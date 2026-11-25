# CI, releases and the public API baseline

How the GitHub workflows validate and release the repository, and the rules for the public API baseline and the release version. `AGENTS.md` (§ CI and releases, § Public API and release version) states the rules every agent applies and points here for the full statements. `ContinuousIntegrationPolicyTests`, `PublicApiBaselineTests`, `HostApiContractTests` and `ReleaseVersionSourceTests` pin what is checkable.

## Continuous integration and releases

- `.github/workflows/validate.yml` is automatic for pull requests and pushes to
  `main`, and can also be dispatched manually. Its stable required-check names
  are `.NET validation` and `Lean validation`; both invoke the `validate-all.ps1` phase boundary
  ([testing-and-validation.md](testing-and-validation.md) § Commands) rather than duplicating commands in YAML. It runs BOTH phases on every
  such event regardless of which files changed — the .NET + Lean backstop
  behind the risk-based local levels ([testing-and-validation.md](testing-and-validation.md) § Validation), its .NET phase at the
  fast tier (`-Tier Fast`, § Test tiers there) — and local execution is opt-in as described in `AGENTS.md` § Validation.
- `.github/workflows/slow-tier-nightly.yml` (job `slow-tier`, 60 minutes) runs
  the slow tier (`validate-all.ps1 -Phase DotNet -Tier Slow`) on `main` every
  night and on manual dispatch, never on pull requests or pushes, and uploads
  its diagnostics with `if: ${{ always() }}`; a failure fails that run visibly.
  `release.yml` validates the release commit with the full tier
  (`-Tier Full`). `ContinuousIntegrationPolicyTests` pins all three tiers.
- `validate-all.ps1` writes a command/exit-code/environment record, one TRX per
  test project, a failure summary and the GC-isolated allocation logs to a fresh
  git-ignored `artifacts/validation/validate-all-*` directory (a temporary
  directory if that path is not ignored). `validate.yml` uploads it with
  `if: always()`; the job result remains the validation result. On Windows a
  detached run survives losing its console: when PowerShell's console host fails
  to restore the console title or mode around a native command with Win32 error
  0xE9 ("No process is on the other end of the pipe."), the script records
  `console host lost`, keeps the completed command's real exit code (or starts a
  command that never ran), and runs every later native command in a hidden
  console of its own; any other failure is rethrown unchanged.
- Both phases build and test in the default Debug configuration, but stack
  frame sizes are configuration-sensitive: the S3 `AstWalker` overflow and the
  Batch 1 F1 deferred-compile overflow appeared only (or far earlier) in
  Release. The third `validate.yml` job, `Release stack suites (x64)`
  (`release-stack-suites`, 30 minutes), is the Release backstop the Debug jobs
  cannot be: `scripts/validate-stack-suites.ps1` builds
  `dotnet/tests/KatLang.Tests` with `-c Release` and runs only the listed
  `SubprocessProbe` process-death stack suites plus the in-process
  `AsyncStackDepthTests` and `PlannedLoopFrameNestingTests` in Release. A test
  class that launches a `SubprocessProbe` child is either
  listed there or excluded with a reason in `ContinuousIntegrationPolicyTests`
  (`EveryProcessProbeClass_IsInTheReleaseStackSuite_OrExcludedWithAReason`). It fails on a build or test failure, a zero-test filter, or a listed
  class that executed nothing, and writes its logs and TRX to a fresh ignored
  `artifacts/validation/stack-suites-release-*` directory (uploaded with
  `if: always()`). It is a CI backstop, not a validation level, and does not
  change the `validate-all.ps1` phase contract. `release.yml` runs the same job
  and gates every build on it. `[Conditional("DEBUG")]` / `#if DEBUG`
  invariant checks are compiled out of Release, so the Debug jobs remain their
  only coverage. ARM64 is not covered per pull request: no ARM64-specific frame
  gap has been measured, so it waits on measuring frame sizes on
  `ubuntu-24.04-arm` and would be a second `arch` matrix leg, not a new job;
  until then ARM64 has only the release build-and-smoke check. The job runs on
  Linux x64 only, while the S3 and F1 frame measurements were taken on Windows
  x64 (whose Release frames and stack-probe behaviour differ), so it cannot
  guarantee detection of a Windows x64-only Release stack regression; a
  Windows x64 matrix leg is the open follow-up.
- `dotnet/KatLang.slnx` deliberately omits the standalone tool projects (today only the
  SharpFuzz harness `dotnet/fuzz/KatLang.ParserFuzz`), so the .NET phase never compiles
  them. The fourth `validate.yml` job, `Standalone tool build`
  (`standalone-tool-build`, 15 minutes), runs
  `scripts/build-standalone-tools.ps1`, which compiles each of them in Debug and
  Release and fails on a build failure or when its project list differs from the
  tracked projects outside the solution. It is build-only (no tool or test runs),
  not a validation level, does not change the `validate-all.ps1` phase contract,
  and writes its logs to a fresh ignored
  `artifacts/validation/standalone-tools-build-*` directory (uploaded with
  `if: always()`). `release.yml` does not run it.
- `.github/workflows/semantic-nightly.yml` (job `semantic-sweeps`, 90 minutes)
  runs nightly and on manual dispatch only, never on pull requests or pushes:
  `scripts/run-semantic-sweeps.ps1` builds `dotnet/fuzz/KatLang.ParserFuzz` (Debug)
  and runs `semantic-campaign --exhaustive` over every finite recipe
  (`SemanticCorpus.FiniteRecipes`, 40-minute budget per recipe). A failure or
  an incomplete sweep fails the job. On failure or cancellation the upload step
  attempts to preserve `artifacts/validation/semantic-sweeps-*`. This CI backstop
  runs separately from the validation levels and the build-only standalone-tool
  job. `ContinuousIntegrationPolicyTests` covers its workflow policies
  (dotnet/fuzz/README.md § Nightly sweeps).
- `.github/workflows/release.yml` is manual-only. Dispatch it from `main` with
  the version already present in `KatLangVersion.props`. A push, merge, or tag
  never publishes a release automatically.
- The release workflow validates the exact dispatched commit, builds and runs
  the NativeAOT CLI on native Windows/Linux/macOS x64 and ARM64 runners,
  packages the tested executable with the root `LICENSE`, `NOTICE`, and
  `PATENTS` files plus the exact restored RID-specific .NET runtime pack's MIT
  license and third-party notices, collects all six archives, produces
  `SHA256SUMS`, and only then creates the tag and publishes the GitHub Release.
  Runtime/ILCompiler pack identities and versions come from the publish output's
  `project.assets.json`, never from the machine-wide SDK root. The shipped
  projects currently have no external `PackageReference`; adding one requires
  explicit release-notice review and an update to the pinned CI policy. Unix
  archives store the CLI as mode `0755` and every text document as mode `0644`.
- `KatLangVersion.props` remains authoritative. Workflow code must never pass
  an MSBuild version override, create/move an existing version tag, or replace
  an existing release.
- Normal jobs have `contents: read`. Only the final publication job has
  `contents: write`; workflows use no user-managed secrets. External actions
  are pinned to immutable commit SHAs and `.github/dependabot.yml` proposes
  reviewable GitHub Actions pin updates.
- Every .NET job installs its SDK through the local action
  `.github/actions/setup-baseline-dotnet`, which passes the exact `global.json`
  `sdk.version` to `setup-dotnet`; that action's own `global-json-file` input
  maps `rollForward: latestMajor` to the LTS channel, which can be older than
  the baseline. A local action's directory must be listed in
  `.github/dependabot.yml`, whose `/` covers only the workflows.


## Public API baseline and release version

- `dotnet/tests/KatLang.Formatting.PublicApi.Tests/PublicApiBaseline.txt` is the checked-in, deterministic rendering of the COMPILED public surface of the `KatLang` assembly — the one assembly the NuGet package ships — reflected by `PublicApiSurfaceRenderer` in that deliberately non-friend test project: every exported type plus consumer-reachable protected nested types, with base/interfaces, generics and constraints; every consumer-visible member with parameter names, modifiers, defaults, nullable annotations and nullable-flow attributes; and every public enum member with its exact numeric value. `PublicApiBaselineTests` compares exactly and never rewrites; a difference is a NuGet surface change. Record an intentional change by regenerating it ([testing-and-validation.md](testing-and-validation.md) § Regenerating generated artifacts) and review the diff as the compatibility review. Regenerating the baseline never changes the release version; the focused hand-written contracts in that project (`PublicElaborationSurfaceTests`, `PublicFormatterExtensionTests`, `HostApiContractTests`) stay beside it.
- The public surface is LAYERED and deliberate (September 2026 public API audit): the primary host API (`KatLangEngine`, `RunOptions`, `RunResult`, `Result`, `KatLangError`/`KatLangErrorCode`), host extensibility (`HostOperation`/`HostOperations`, `OutputFormatter`/`BoundedOutputWriter`), analysis (`Parser`, `Lexer`/`Token`, `Semantics`), host tooling (`KatLang.CodeLink` with its library-produced `CodeLinkEncoding`/`CodeLinkDecoding` results: KatLang's own katlang.org code-link format, `docs/design/code-link-format.md` — C#-only, no language semantics, its coder and model internal; the format, its primer and its fixtures are FROZEN, and a new format version is the owner's decision, never part of a language change), and the low-level `Evaluator` over the Lean-shaped AST — which evaluates a host-built `Expr` as-is and is never a source runner. Implementation machinery stays internal and is pinned so by name in `HostApiContractTests` (a baseline regeneration cannot bless re-exposing it): the signature and binding planners (`Signatures/`), the evaluator's value views on `Result` (spread/structure/selection/value-count views, `Normalize`, the UNBOUNDED atom projections — hosts use the bounded `RunResult.Success.Atoms` / `Evaluator.RunFlat`), `SemanticModel` construction, message builders, and compatibility shims. Source, evaluator, and configuration entry points validate their direct CLR arguments (host-built AST payloads remain an advanced caller contract) (`ArgumentNullException`, never a `NullReferenceException`); async entry points deliver every exception through the returned task; each `Evaluator` entry family has exactly one overload per arity (no positional-`null` ambiguity). `RunResult` variants and `ParseResult` are library-produced records with internal constructors and get-only payloads; hosts read/deconstruct them and construct `Result` values for host callbacks. `RunFlat`/`RunFlatAsync` accept host operations through the same bounded projection as their ordinary forms. The package ships its XML documentation — any documentation diagnostic that means a comment is wrong (unresolvable or ambiguous cref, bad param/paramref) is a build error, so docs cannot name a removed API — and is `IsAotCompatible` (trim/AOT analyzers on every build).
- `KatLangVersion.props` is the ONE place the release version is written. `dotnet/src/KatLang/KatLang.csproj` (package and assembly version), `dotnet/src/KatLang.CLI/KatLang.CLI.csproj` (which builds against the KatLang PROJECT, so it cannot lag onto a previously published package) and `dotnet/tests/KatLang.CLI.Tests` (which bakes the value in as `IntendedKatLangVersion` assembly metadata — build intent, never read from the KatLang assembly under test) derive from it. `ReleaseVersionSourceTests` rejects any other version literal in an MSBuild file and any in-repository `PackageReference` to KatLang; the CLI version tests compare the loaded runtime, the CLI assembly and `--version` against the intended metadata, so a stale or mismatched artifact fails rather than passing against itself.
