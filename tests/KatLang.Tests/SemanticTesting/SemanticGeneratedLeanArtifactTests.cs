using System.Globalization;
using System.Text;
using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// SEM-2C (first step): generates and pins <c>lean/CoreTests/SemanticGeneratedCases.lean</c>, the third
/// generated Lean/C# differential corpus. It gives every VALID SEM-2B generated case
/// (<see cref="SemanticCorpus.All"/>, kinds <see cref="SemanticCaseKind.ValidSuccess"/> and
/// <see cref="SemanticCaseKind.ValidRuntimeFailure"/>) a Lean guard.
///
/// <para><b>The identity-prelude member.</b> Most generated programs call the host operations
/// <c>trace(x)</c> and <c>wait(x)</c>, which Lean does not model and <see cref="LeanAstEncoder"/>
/// refuses (they are <c>Expr.NativeCall</c> wrappers). Both operations return their argument, so for
/// each case this test builds a Lean-comparable member: the base source with
/// <see cref="IdentityPrelude"/> (<c>trace(x) = x</c>, <c>wait(x) = x</c>) prepended. It parses without
/// any host operation, so its REAL elaborated AST is what both evaluators run. The member is built only
/// here — it is not a <see cref="SemanticCase.Members"/> entry, so SEM-2B descriptors and replay are
/// unchanged.</para>
///
/// <para><b>Claim.</b> Lean is checked on the identity-prelude member of each included case against the
/// generator's constructed expectation (C# checks the member against that expectation here, then the
/// Lean guard pins the same neutral text). The relation between the member and the host-operation BASE
/// program is C# evidence only (the SEM-2B profiles plus this test's member check). Host events, async
/// suspension and cancellation, and optimizer paths are not observed by these guards.</para>
///
/// Regenerate with:
///   $env:KATLANG_REGENERATE_SEMANTIC_GENERATED = "1"
///   dotnet test ./tests/KatLang.Tests/KatLang.Tests.csproj --filter SemanticGeneratedLeanArtifact
/// That run writes the artifact and then fails by design (see <see cref="ArtifactRegeneration"/>);
/// review the diff, clear the flag, rerun, and run <c>lake build CoreTests</c>.
/// </summary>
public class SemanticGeneratedLeanArtifactTests
{
    internal const string ArtifactRelativePath = "lean/CoreTests/SemanticGeneratedCases.lean";

    /// <summary>The two identity definitions standing in for the SEM-2B host operations.</summary>
    internal const string IdentityPrelude = "trace(x) = x\nwait(x) = x\n";

    /// <summary>
    /// Valid cases excluded by exact id, each with a non-blank reason. Only an exclusion caused by the
    /// identity assumption itself (for example a non-number host-operation argument) belongs here; any
    /// other disagreement is a finding. Empty: every valid case is included.
    /// </summary>
    internal static readonly IReadOnlyDictionary<string, string> ExcludedById =
        new Dictionary<string, string>(StringComparer.Ordinal);

    /// <summary>Invalid front-end cases of the fixed corpus, excluded by kind (Lean has no surface front end).</summary>
    private const int ExpectedInvalidFrontEndCases = 9;

    /// <summary>Coverage ratchet: may only be raised, or lowered in a reviewed diff that removes cases.</summary>
    private const int MinimumIncludedCases = 264;

    /// <summary>
    /// Lean build-cost caps (SEM-2C measurement, 2026-11-09: 230 cases, 234,301 bytes, cold module build
    /// 17 s on the 16-processor development host, about 0.07 s per case). Raising a cap requires a new measurement of the
    /// module's cold build time and of the Lean CI job.
    /// </summary>
    private const int MaximumIncludedCases = 300;

    private const int MaximumArtifactBytes = 350_000;

    [Fact]
    public void GeneratedLeanArtifact_MatchesCurrentCSharpObservations()
    {
        var expected = GenerateArtifact();
        var path = Path.Combine(RepoRoot.Find(), ArtifactRelativePath);
        var flag = RegenerationFlags.SemanticGenerated;

        ArtifactRegeneration.VerifyOrRegenerate(
            flag,
            ArtifactRelativePath,
            regenerate: () => expected,
            verify: () =>
            {
                Assert.True(File.Exists(path),
                    $"{ArtifactRelativePath} is missing. Set {flag}=1 and rerun this test to generate it (that run fails by design).");
                var actual = File.ReadAllText(path).ReplaceLineEndings("\n");
                Assert.True(expected == actual,
                    $"{ArtifactRelativePath} is out of date with the SEM-2B corpus or the current C# observations. " +
                    $"Set {flag}=1 and rerun this test to regenerate it (that run fails by design), review the diff, and run " +
                    "`lake build CoreTests` to check the Lean side. " +
                    SemanticExplorerLeanArtifactTests.DescribeFirstDifference(expected, actual));
            },
            afterRegenerating: "run `lake build CoreTests` to check the Lean side");
    }

    [Fact]
    public void GeneratedModule_IsImportedByTheCanonicalCoreTestsTarget()
    {
        var root = File.ReadAllText(Path.Combine(RepoRoot.Find(), "lean/CoreTests.lean")).ReplaceLineEndings("\n");
        Assert.Contains("\nimport CoreTests.SemanticGeneratedCases\n", root.EndsWith('\n') ? root : root + "\n", StringComparison.Ordinal);
    }

    /// <summary>
    /// The partition is exact: included + excluded by kind + excluded by id = corpus size; the
    /// by-kind exclusion is exactly the invalid front-end cases; every by-id exclusion names a valid
    /// case and has a reason; every family with a valid case keeps at least one included case.
    /// </summary>
    [Fact]
    public void Partition_IsExact_AndEveryFamilyKeepsIncludedCases()
    {
        var all = SemanticCorpus.All();
        var included = IncludedCases(all);
        var byKind = all.Where(c => c.Kind == SemanticCaseKind.InvalidFrontEnd).ToList();
        var byId = all.Where(c => IsValid(c) && ExcludedById.ContainsKey(c.CaseId)).ToList();

        Assert.Equal(ExpectedInvalidFrontEndCases, byKind.Count);
        Assert.Equal(all.Count, included.Count + byKind.Count + byId.Count);
        Assert.Equal(ExcludedById.Count, byId.Count);
        Assert.All(ExcludedById, pair => Assert.False(string.IsNullOrWhiteSpace(pair.Value), pair.Key));
        Assert.True(ExcludedById.Count <= 5, "More than five valid cases excluded by id: this needs an owner review, not more exclusions.");

        foreach (var family in all.Where(IsValid).SelectMany(c => c.Families).Distinct(StringComparer.Ordinal))
        {
            Assert.True(included.Any(c => c.Families.Contains(family)),
                $"Every valid case of family '{family}' is excluded from the Lean corpus.");
        }

        // The emitted id list is exactly the included partition, in corpus order.
        Assert.Equal(included.Select(c => c.CaseId), EmittedCaseIds(ReadArtifact()));
    }

    /// <summary>Coverage ratchet plus the Lean build-cost caps (cases and bytes).</summary>
    [Fact]
    public void Ratchet_IncludedCoverageCannotShrink_AndTheArtifactStaysInsideItsBuildBudget()
    {
        var included = IncludedCases(SemanticCorpus.All());
        Assert.True(included.Count >= MinimumIncludedCases,
            $"Included SEM-2B Lean coverage shrank below {MinimumIncludedCases} (actual {included.Count}).");
        Assert.True(included.Count <= MaximumIncludedCases,
            $"Included cases ({included.Count}) exceed the measured cap {MaximumIncludedCases}; raising it requires a new Lean build measurement.");
        var bytes = Encoding.UTF8.GetByteCount(GenerateArtifact());
        Assert.True(bytes <= MaximumArtifactBytes,
            $"The generated artifact ({bytes} bytes) exceeds the measured cap {MaximumArtifactBytes}; raising it requires a new Lean build measurement.");
    }

    /// <summary>The Lean name mangling is deterministic and injective over the corpus, and round-trips.</summary>
    [Fact]
    public void LeanNames_AreInjective_AndDecodeToTheirCaseIds()
    {
        var ids = SemanticCorpus.All().Select(c => c.CaseId).ToList();
        var names = ids.Select(LeanName).ToList();
        Assert.Equal(ids.Count, names.Distinct(StringComparer.Ordinal).Count());
        Assert.All(names, n => Assert.Matches("^case_[A-Za-z0-9_]+$", n));
        Assert.Equal(ids, names.Select(DecodeLeanName));

        // Characters a hand-written mangling would plausibly conflate stay distinct.
        string[] lookalikes = ["a/b", "a_b", "a-b", "a+b", "a_2Fb", "a.b"];
        Assert.Equal(lookalikes.Length, lookalikes.Select(LeanName).Distinct(StringComparer.Ordinal).Count());
        Assert.All(lookalikes, id => Assert.Equal(id, DecodeLeanName(LeanName(id))));
    }

    /// <summary>The host fixture is exactly the two identity-compatible operations the prelude replaces.</summary>
    [Fact]
    public void HostFixture_IsExactlyTraceAndWait()
        => Assert.Equal(["trace", "wait"], MetamorphicHostFixture.OperationNames);

    /// <summary>A member whose identity prelude is missing fails loudly and names the case.</summary>
    [Fact]
    public void Generation_NamesTheCase_WhenAMemberDoesNotParse()
    {
        var sample = IncludedCases(SemanticCorpus.All()).First(c => c.Source.Contains("trace(", StringComparison.Ordinal));
        var ex = Assert.Throws<InvalidOperationException>(() => ObserveMember(sample, sample.Source));
        Assert.Contains(sample.CaseId, ex.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("{ trace(x) = x\n0 }")]
    [InlineData("Box = { wait(x) = x\n0 }\n0")]
    [InlineData("F(0) = { trace(x) = x\n0 }\nF(x) = 0\n0")]
    [InlineData("Box = { wait(x) = x\ncount }\n0")]
    [InlineData("Box = { open { trace(x) = x }\n0 }\n0")]
    [InlineData("Id(x) = x\nId({ trace(x) = x\n0 })")]
    [InlineData("[{ wait(x) = x\n0 }]")]
    [InlineData("F(trace) = 0\n0")]
    [InlineData("F(wait, 0) = 0\nF(x, y) = 0\n0")]
    public void Generation_RejectsHostOperationDeclarations_InEveryNestedPosition(string source)
    {
        var sample = IncludedCases(SemanticCorpus.All())[0];
        var member = IdentityPrelude + source;
        SourceProvenance.ParseValid(member);

        var ex = Assert.Throws<InvalidOperationException>(() => ObserveMember(sample, member));
        Assert.Contains(sample.CaseId, ex.Message, StringComparison.Ordinal);
        Assert.Contains("declares a host-operation name itself", ex.Message, StringComparison.Ordinal);
    }

    internal static bool IsValid(SemanticCase c)
        => c.Kind is SemanticCaseKind.ValidSuccess or SemanticCaseKind.ValidRuntimeFailure;

    internal static List<SemanticCase> IncludedCases(IReadOnlyList<SemanticCase> all)
        => all.Where(c => IsValid(c) && !ExcludedById.ContainsKey(c.CaseId)).ToList();

    internal static string BuildMember(SemanticCase c) => IdentityPrelude + c.Source;

    /// <summary>
    /// Injective Lean identifier for a case id: ASCII letters and digits are kept, every other
    /// character (including <c>_</c>) becomes <c>_</c> plus two upper-case hex digits.
    /// </summary>
    internal static string LeanName(string caseId)
    {
        var builder = new StringBuilder("case_");
        foreach (var ch in caseId)
        {
            if (ch > 0x7E || ch < 0x20)
                throw new InvalidOperationException($"Case id '{caseId}' contains a non-printable-ASCII character.");
            if (char.IsAsciiLetterOrDigit(ch))
                builder.Append(ch);
            else
                builder.Append('_').Append(((int)ch).ToString("X2", CultureInfo.InvariantCulture));
        }

        return builder.ToString();
    }

    internal static string DecodeLeanName(string name)
    {
        var body = name["case_".Length..];
        var builder = new StringBuilder();
        for (var i = 0; i < body.Length; i++)
        {
            if (body[i] == '_')
            {
                builder.Append((char)int.Parse(body.AsSpan(i + 1, 2), NumberStyles.HexNumber, CultureInfo.InvariantCulture));
                i += 2;
            }
            else
            {
                builder.Append(body[i]);
            }
        }

        return builder.ToString();
    }

    /// <summary>
    /// Parses and checks one member against the case's constructed expectation, returning the parsed
    /// root and the shared neutral observation. Throws (naming the case) on any disagreement.
    /// </summary>
    internal static (Algorithm Root, ExplorerObservation Observation) ObserveMember(SemanticCase c, string member)
    {
        var parsed = Parser.Parse(member);
        if (parsed.HasErrors)
        {
            var first = parsed.Diagnostics.First(d => d.Severity == DiagnosticSeverity.Error);
            throw new InvalidOperationException(
                $"Identity-prelude member of '{c.CaseId}' does not parse cleanly: {first.Code} {first.Message}");
        }

        RequireSingleIdentityDeclarations(c, parsed.Root);

        var counted = Evaluator.RunCounted(new Expr.AlgorithmExpr(parsed.Root));
        var expected = c.Expected;
        if (c.Kind == SemanticCaseKind.ValidSuccess)
        {
            if (counted.IsError)
            {
                throw new InvalidOperationException(
                    $"Identity-prelude member of '{c.CaseId}' failed ({MetamorphicValue.ErrorCategory(counted.Error)}) but the constructed expectation is {expected}.");
            }

            if (!Result.ValueComparer.Equals(counted.Value.Value, expected.Value!)
                || counted.Value.EmittedCount != expected.EmittedCount)
            {
                throw new InvalidOperationException(
                    $"Identity-prelude member of '{c.CaseId}' observed {SemanticExplorerHarness.Neutral(counted.Value.Value)} n={counted.Value.EmittedCount} " +
                    $"but the constructed expectation is {SemanticExplorerHarness.Neutral(expected.Value!)} n={expected.EmittedCount}.");
            }
        }
        else
        {
            if (!counted.IsError)
            {
                throw new InvalidOperationException(
                    $"Identity-prelude member of '{c.CaseId}' succeeded ({SemanticExplorerHarness.Neutral(counted.Value.Value)}) but the constructed expectation is {expected}.");
            }

            var category = MetamorphicValue.ErrorCategory(counted.Error);
            if (category != expected.ErrorCategory)
            {
                throw new InvalidOperationException(
                    $"Identity-prelude member of '{c.CaseId}' failed with {category} but the constructed expectation is {expected.ErrorCategory}.");
            }
        }

        var observation = SemanticExplorerHarness.Observe(c.CaseId, member);
        var expectedOutcome = c.Kind == SemanticCaseKind.ValidSuccess ? "ok" : "err";
        if (observation.Outcome != expectedOutcome)
        {
            throw new InvalidOperationException(
                $"Shared observation of '{c.CaseId}' is '{observation.Neutral}', expected outcome {expectedOutcome}.");
        }

        if (c.Kind == SemanticCaseKind.ValidSuccess)
        {
            var expectedNeutral = $"ok raw={SemanticExplorerHarness.Neutral(expected.Value!)} n={expected.EmittedCount}";
            if (observation.Neutral != expectedNeutral)
            {
                throw new InvalidOperationException(
                    $"Shared observation of '{c.CaseId}' is '{observation.Neutral}', expected '{expectedNeutral}'.");
            }
        }

        return (parsed.Root, observation);
    }

    /// <summary>
    /// The prelude's two definitions must be the ONLY declarations of <c>trace</c> and <c>wait</c>
    /// anywhere in the member: a base source that declared either name itself would change what the
    /// identity member means.
    /// </summary>
    private static void RequireSingleIdentityDeclarations(SemanticCase c, Algorithm root)
    {
        if (!MetamorphicHostFixture.OperationNames.SequenceEqual(["trace", "wait"]))
        {
            throw new InvalidOperationException(
                $"The SEM-2B host fixture is [{string.Join(", ", MetamorphicHostFixture.OperationNames)}], not exactly [trace, wait]; the identity prelude no longer covers it.");
        }

        var counts = new Dictionary<string, int>(StringComparer.Ordinal) { ["trace"] = 0, ["wait"] = 0 };
        new IdentityDeclarationCounter(counts).VisitAlgorithm(root);
        if (counts["trace"] != 1 || counts["wait"] != 1)
        {
            throw new InvalidOperationException(
                $"The base source of '{c.CaseId}' declares a host-operation name itself (trace x{counts["trace"]}, wait x{counts["wait"]} in the member).");
        }
    }

    private sealed class IdentityDeclarationCounter(Dictionary<string, int> counts) : AstWalker
    {
        private readonly HashSet<Algorithm> _visited = new(ReferenceEqualityComparer.Instance);

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            if (_visited.Add(algorithm))
                base.VisitAlgorithm(algorithm);
        }

        protected override void VisitProperty(Property property)
        {
            Count(property.Name);
            base.VisitProperty(property);
        }

        protected override void VisitExplicitParameterDeclaration(Algorithm algorithm, ParameterDeclaration declaration)
            => Count(declaration.Name);

        protected override void VisitConditionalBinderDeclaration(Pattern.Bind pattern, SourceSpan span)
            => Count(pattern.Name);

        private void Count(string name)
        {
            if (counts.ContainsKey(name))
                counts[name]++;
        }
    }

    private static string ReadArtifact()
        => File.ReadAllText(Path.Combine(RepoRoot.Find(), ArtifactRelativePath)).ReplaceLineEndings("\n");

    private static List<string> EmittedCaseIds(string artifact)
    {
        var start = artifact.IndexOf("def includedCaseIds : List String := [\n", StringComparison.Ordinal);
        Assert.True(start >= 0, "The artifact has no includedCaseIds list.");
        var end = artifact.IndexOf("\n]\n", start, StringComparison.Ordinal);
        return artifact[start..end].Split('\n').Skip(1)
            .Select(line => line.Trim().TrimEnd(',').Trim('"'))
            .ToList();
    }

    internal static string GenerateArtifact()
    {
        var all = SemanticCorpus.All();
        var included = IncludedCases(all);
        var byKind = all.Count(c => c.Kind == SemanticCaseKind.InvalidFrontEnd);
        var byId = all.Count(c => IsValid(c) && ExcludedById.ContainsKey(c.CaseId));
        var successes = included.Count(c => c.Kind == SemanticCaseKind.ValidSuccess);

        var builder = new StringBuilder();
        builder.Append($"""
            import KatLang

            /-!
            GENERATED FILE - DO NOT EDIT BY HAND.

            SEM-2C: Lean/C# differential corpus of the SEM-2B generated cases
            (fuzz/KatLang.ParserFuzz/Semantic/SemanticCorpus.cs). For every valid case the program below is
            `LeanAstEncoder`'s encoding of the parsed IDENTITY-PRELUDE MEMBER: the case's base source with
            `trace(x) = x` and `wait(x) = x` prepended in place of the SEM-2B host operations, which Lean
            does not model. C# checked each member against the generator's constructed expectation (value
            and emitted count, or error kind); each `#guard` pins the member's C# neutral observation. A
            failing guard is a Lean/C# divergence on that case.

            Not checked here: the host-operation base program itself, host events, async suspension and
            cancellation, and optimizer paths (all C# evidence of the SEM-2B profiles).

            Partition (machine-checked by the `includedCaseIds.length` guard below):
            - corpus cases: {all.Count}
            - excluded by kind (invalid front-end programs; Lean has no surface front end): {byKind}
            - excluded by exact id: {byId}
            - included cases: {included.Count} ({successes} success, {included.Count - successes} runtime failure)

            Regenerate from the repo root with:
              $env:KATLANG_REGENERATE_SEMANTIC_GENERATED = "1"
              dotnet test ./tests/KatLang.Tests/KatLang.Tests.csproj --filter SemanticGeneratedLeanArtifact
            -/

            namespace SemanticGeneratedCases
            open KatLang

            """.ReplaceLineEndings("\n"));
        builder.Append('\n');
        builder.Append(LeanObsTemplate.SharedDefinitions.ReplaceLineEndings("\n"));
        builder.Append("\n\n");

        var ids = new List<string>();
        foreach (var c in included)
        {
            if (c.CaseId.Contains('"') || c.CaseId.Contains('\\'))
                throw new InvalidOperationException($"Case id '{c.CaseId}' cannot be listed as a plain Lean string.");

            var member = BuildMember(c);
            var (root, observation) = ObserveMember(c, member);
            string program;
            try
            {
                program = LeanAstEncoder.EncodeProgram(root);
            }
            catch (NotSupportedException ex)
            {
                throw new InvalidOperationException(
                    $"Identity-prelude member of '{c.CaseId}' is not Lean-encodable: {ex.Message}", ex);
            }

            var name = LeanName(c.CaseId);
            var sourceComment = c.Source.ReplaceLineEndings("\n").Replace("\n", " \\n ");
            builder.Append($"-- {c.CaseId}: {sourceComment}\n");
            builder.Append($"def {name} : Expr :=\n  {program}\n");
            builder.Append($"#guard obs {name} == {LeanAstEncoder.QuoteString(observation.Neutral)}\n");
            LeanObsTemplate.AppendErrorGuard(builder, name, observation.ErrorPayload);
            builder.Append('\n');
            ids.Add(c.CaseId);
        }

        SemanticExplorerLeanArtifactTests.AppendCountGuard(builder, "includedCaseIds", ids, included.Count,
            "Machine-checked included partition count: the id list is built by the same loop that emits\n" +
            "the guards above, while the expected total is computed independently from the corpus\n" +
            "partition, so a generation bug fails `lake build`.");

        builder.Append($"-- {ids.Count} differential cases.\n");
        builder.Append("end SemanticGeneratedCases\n");
        return builder.ToString();
    }
}
