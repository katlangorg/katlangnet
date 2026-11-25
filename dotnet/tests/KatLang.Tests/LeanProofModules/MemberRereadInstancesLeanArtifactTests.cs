using System.Globalization;
using System.Text;

namespace KatLang.Tests.LeanProofModules;

/// <summary>
/// Generates and pins <c>lean/KatLangArityLaws/MemberRereadInstances.lean</c> (E-18 step 1, M1): the general
/// re-read theorem <c>NavigationSettled.member_bridge_of_probe</c> APPLIED to source programs, one namespace
/// per receiver class and bundle kind.
///
/// <para>The module is GENERATED text. Every instance is one of three templates filled from a table row:
/// <see cref="ReusedRootTemplate"/> and <see cref="ReusedParameterTemplate"/> re-use the definitions and
/// reachability chain of a <c>MemberBridgeSource*</c> namespace, and <see cref="NewRootTemplate"/> carries its
/// own. To add, change or remove an instance — or to follow a change to a statement the instances mention,
/// such as the <c>aliasCells</c> write of <see cref="WroteAlias"/> — edit the table or the template HERE,
/// regenerate, and build the Lean target: the proofs are checked by Lean, not by this test.</para>
///
/// <para>This generator replaces a Python script that existed only in an ignored scratch folder of one
/// machine. On the day it was ported (2026-11-16) both produced the tracked module byte for byte.</para>
///
/// Regenerate with:
///   $env:KATLANG_REGENERATE_MEMBER_REREAD_INSTANCES = "1"
///   dotnet test ./dotnet/tests/KatLang.Tests/KatLang.Tests.csproj --filter MemberRereadInstancesLeanArtifact
/// That run writes the module and then fails by design (see <see cref="ArtifactRegeneration"/>); review the
/// diff, clear the flag, rerun, and run <c>lake build KatLangArityLaws</c>.
/// </summary>
public class MemberRereadInstancesLeanArtifactTests
{
    internal const string ArtifactRelativePath = "lean/KatLangArityLaws/MemberRereadInstances.lean";

    [Fact]
    public void GeneratedLeanModule_IsItsGeneratorsOutput()
        => LeanProofModuleArtifact.VerifyOrRegenerate(
            RegenerationFlags.MemberRereadInstances, ArtifactRelativePath, GenerateArtifact());

    /// <summary>
    /// Every table row opens its own Lean namespace, and the module header's table of receiver classes names
    /// it: a row added without its header entry, or two rows under one name, is a generator mistake that Lean
    /// would report late (a duplicate declaration) or not at all (an undocumented instance).
    /// </summary>
    [Fact]
    public void EveryInstance_OpensItsOwnNamespace_NamedInTheModuleHeader()
    {
        var namespaces = InstanceNamespaces().ToList();

        Assert.NotEmpty(namespaces);
        Assert.Equal(namespaces.Count, namespaces.Distinct(StringComparer.Ordinal).Count());
        Assert.All(namespaces, name => Assert.Contains($"`{name}`", Header, StringComparison.Ordinal));

        var generated = GenerateArtifact();
        Assert.All(namespaces, name =>
        {
            Assert.Equal(1, LeanProofModuleArtifact.CountOccurrences(generated, $"\nnamespace {name}\n"));
            Assert.Equal(1, LeanProofModuleArtifact.CountOccurrences(generated, $"\nend {name}\n"));
        });
    }

    private static IEnumerable<string> InstanceNamespaces()
        => ReusedRootInstances.Select(static instance => instance.Namespace)
            .Concat(ReusedParameterInstances.Select(static instance => instance.Namespace))
            .Concat(NewRootInstances.Select(static instance => instance.Namespace));

    /// <summary>The module's whole text: the header, the instances in table order, the footer.</summary>
    internal static string GenerateArtifact()
    {
        var fuel = NavigationFuel.ToString(CultureInfo.InvariantCulture);
        var builder = new StringBuilder(Header);

        foreach (var instance in ReusedRootInstances)
        {
            builder.Append(LeanProofModuleArtifact.Fill(
                ReusedRootTemplate,
                ("NS", instance.Namespace), ("TEXT", instance.Text), ("KIND", instance.Kind), ("FUEL", fuel)));
        }

        foreach (var instance in ReusedParameterInstances)
        {
            builder.Append(LeanProofModuleArtifact.Fill(
                ReusedParameterTemplate,
                ("NS", instance.Namespace), ("TEXT", instance.Text), ("KIND", instance.Kind), ("FUEL", fuel)));
        }

        foreach (var instance in NewRootInstances)
        {
            builder.Append(LeanProofModuleArtifact.Fill(
                NewRootTemplate,
                ("NS", instance.Namespace), ("TEXT", instance.Text), ("KIND", instance.Kind), ("FUEL", fuel),
                ("DOC", instance.Doc), ("TARGET", instance.Target), ("MEMBER", instance.Member), ("ARGS", instance.Args),
                ("VALUE", instance.Value), ("VALUEDOC", instance.ValueDoc),
                ("WROTE", instance.Wrote), ("WROTEDOC", instance.WroteDoc)));
        }

        builder.Append(Footer);
        return builder.ToString().ReplaceLineEndings("\n");
    }

    // ── The instance tables ─────────────────────────────────────────────────────────────────────

    /// <summary>The explicit fuel every instance's navigation run is evaluated at (<c>navFuel</c>).</summary>
    private const int NavigationFuel = 64;

    /// <summary>
    /// An instance whose definitions and reachability chain a <c>MemberBridgeSource*</c> module already has
    /// under the same namespace: the written call <paramref name="Text"/> and what it is an instance of.
    /// </summary>
    private sealed record ReusedInstance(string Namespace, string Text, string Kind);

    /// <summary>
    /// An instance new in this module, with its own definitions and reachability chain. The Lean fields:
    /// the receiver expression, the member name, the argument bundle, the statement of the call's outcome and
    /// the statement of what the probe wrote.
    /// </summary>
    private sealed record NewInstance(
        string Namespace,
        string Text,
        string Kind,
        string Doc,
        string Target,
        string Member,
        string Args,
        string Value,
        string ValueDoc,
        string Wrote,
        string WroteDoc);

    private const string SpreadNone = "[.sequenceSpread (.emptySequence 0)]";
    private const string SpreadOne = "[.sequenceSpread (.listLiteral [.num 5])]";
    private const string SpreadFails = "[.sequenceSpread (.binary .div (.num 1) (.num 0))]";

    /// <summary>The outcome of the plan's ordinary call from <c>entry</c>, the subject of each outcome statement.</summary>
    private const string OrdinaryOutcome = "((ordinaryCall productionPlanRoute 0 shape .call).runState entry).1";

    /// <summary>A runtime-target alias: the receiver's first navigation records the alias's binding cell.</summary>
    private const string WroteAlias = "probed.aliasCells.length = entry.aliasCells.length + 1";

    /// <summary>A static reference: the probe leaves the state as it found it.</summary>
    private const string WroteNothing = "probed = entry";

    private const string Rtc = ".resolve \"RTC\"";
    private const string Rta = ".resolve \"RTA\"";
    private const string Als = ".resolve \"ALS\"";

    private const string RtcDoc = "`RTC = Capture(FM(0)).Algorithm`: a runtime-target alias.";
    private const string RtaDoc = "`RTA = RC.Algorithm`, `RC = Capture(FM(0))`: a runtime-target alias over a static receiver.";
    private const string AlsDoc = "`ALS = Lib.Sub`: the reference's own row is a member path.";

    private const string SpreadFailsDoc = "The supply formation FAILS (the spread divides by zero): both sides fail alike.";
    private const string WroteAliasDoc = "The first navigation WRITES: the alias's binding cell is recorded.";
    private const string WroteNothingDoc = "A static reference: the probe writes nothing.";

    /// <summary>Instances of <c>MemberBridgeSource*</c> in the ROOT context.</summary>
    private static readonly ReusedInstance[] ReusedRootInstances =
    [
        new("RuntimeEmpty", "RTC.Pair()", "a RUNTIME-TARGET alias, empty bundle"),
        new("RuntimeSpreadOne", "RTC.G([5]*)", "a runtime-target alias, a spread forming one cell"),
        new("RuntimeNamedOrdinary", "RTA.G(2)", "a runtime-target alias over the STATIC receiver `RC`, ordinary bundle"),
        new("PathRefEmpty", "ALS.K()", "a transparent reference to a MEMBER PATH, empty bundle"),
        new("RefEmpty", "AB.V()", "a transparent reference, empty bundle"),
        new("RefSpreadNone", "AB.V(()*)", "a transparent reference, a spread forming no cell"),
        new("RefSpreadOne", "AB.G([5]*)", "a transparent reference, a spread forming one cell"),
        new("RefSpreadFails", "AB.G((1 / 0)*)", "a transparent reference, a FAILING spread"),
        new("RefOrdinary", "AB.G(2)", "a transparent reference, ordinary bundle"),
        new("OpenEmpty", "OBox.V()", "an OPENED name, empty bundle"),
        new("OpenSpreadNone", "OBox.V(()*)", "an opened name, a spread forming no cell"),
        new("NestedEmpty", "Lib.Sub.K()", "a NESTED member path, empty bundle"),
        new("NestedSpreadOne", "Lib.Sub.H([5]*)", "a nested member path, a spread forming one cell"),
        new("NestedSpreadFails", "Lib.Sub.H((1 / 0)*)", "a nested member path, a FAILING spread"),
    ];

    /// <summary>Instances of <c>MemberBridgeSourceParameters</c>: the plan is written in a parameter owner's body.</summary>
    private static readonly ReusedInstance[] ReusedParameterInstances =
    [
        new("ParamEmpty", "b.V()", "a PARAMETER receiver, empty bundle"),
        new("ParamRefSpreadNone", "b.V(()*)", "a parameter bound to a transparent reference, a spread forming no cell"),
        new("ParamSpreadFails", "b.G((1 / 0)*)", "a parameter receiver, a FAILING spread"),
        new("ParamPathEmpty", "b.Sub.K()", "a PARAMETER-ROOTED member path, empty bundle"),
    ];

    /// <summary>Instances new in this module, in the ROOT context.</summary>
    private static readonly NewInstance[] NewRootInstances =
    [
        new(
            Namespace: "RuntimeSpreadNone",
            Text: "RTC.Pair(()*)",
            Kind: "a RUNTIME-TARGET alias, a spread forming no cell",
            Doc: RtcDoc,
            Target: Rtc,
            Member: "Pair",
            Args: SpreadNone,
            Value: OrdinaryOutcome + " = .ok (.sequenceValue [.atom 7, .atom 8], 1)",
            ValueDoc: "The call's value: the member `Pair` of the projected callable.",
            Wrote: WroteAlias,
            WroteDoc: WroteAliasDoc),
        new(
            Namespace: "RuntimeSpreadFails",
            Text: "RTC.G((1 / 0)*)",
            Kind: "a RUNTIME-TARGET alias, a FAILING spread",
            Doc: RtcDoc,
            Target: Rtc,
            Member: "G",
            Args: SpreadFails,
            Value: OrdinaryOutcome + ".toOption = none",
            ValueDoc: SpreadFailsDoc,
            Wrote: WroteAlias,
            WroteDoc: WroteAliasDoc),
        new(
            Namespace: "RuntimeNamedSpreadOne",
            Text: "RTA.G([5]*)",
            Kind: "a runtime-target alias over the STATIC receiver `RC`, a spread forming one cell",
            Doc: RtaDoc,
            Target: Rta,
            Member: "G",
            Args: SpreadOne,
            Value: OrdinaryOutcome + " = .ok (.atom 5, 1)",
            ValueDoc: "The call's value: `G(5) = 5`.",
            Wrote: WroteAlias,
            WroteDoc: WroteAliasDoc),
        new(
            Namespace: "RuntimeNamedSpreadFails",
            Text: "RTA.G((1 / 0)*)",
            Kind: "a runtime-target alias over the STATIC receiver `RC`, a FAILING spread",
            Doc: RtaDoc,
            Target: Rta,
            Member: "G",
            Args: SpreadFails,
            Value: OrdinaryOutcome + ".toOption = none",
            ValueDoc: SpreadFailsDoc,
            Wrote: WroteAlias,
            WroteDoc: WroteAliasDoc),
        new(
            Namespace: "PathRefSpreadNone",
            Text: "ALS.K(()*)",
            Kind: "a transparent reference to a MEMBER PATH, a spread forming no cell",
            Doc: AlsDoc,
            Target: Als,
            Member: "K",
            Args: SpreadNone,
            Value: OrdinaryOutcome + " = .ok (.atom 3, 1)",
            ValueDoc: "The call's value.",
            Wrote: WroteNothing,
            WroteDoc: WroteNothingDoc),
        new(
            Namespace: "PathRefSpreadOne",
            Text: "ALS.H([5]*)",
            Kind: "a transparent reference to a member path, a spread forming one cell",
            Doc: AlsDoc,
            Target: Als,
            Member: "H",
            Args: SpreadOne,
            Value: OrdinaryOutcome + " = .ok (.atom 6, 1)",
            ValueDoc: "The call's value: `H(5) = 6`.",
            Wrote: WroteNothing,
            WroteDoc: WroteNothingDoc),
        new(
            Namespace: "PathRefSpreadFails",
            Text: "ALS.H((1 / 0)*)",
            Kind: "a transparent reference to a member path, a FAILING spread",
            Doc: AlsDoc,
            Target: Als,
            Member: "H",
            Args: SpreadFails,
            Value: OrdinaryOutcome + ".toOption = none",
            ValueDoc: SpreadFailsDoc,
            Wrote: WroteNothing,
            WroteDoc: WroteNothingDoc),
        new(
            Namespace: "PathRefOrdinary",
            Text: "ALS.H(2)",
            Kind: "a transparent reference to a member path, ordinary bundle",
            Doc: AlsDoc,
            Target: Als,
            Member: "H",
            Args: "[.num 2]",
            Value: OrdinaryOutcome + " = .ok (.atom 3, 1)",
            ValueDoc: "The call's value: `H(2) = 3`.",
            Wrote: WroteNothing,
            WroteDoc: WroteNothingDoc),
    ];

    // ── The module text ─────────────────────────────────────────────────────────────────────────
    //
    // Lean text, verbatim. A placeholder is @NAME@ (LeanProofModuleArtifact.Fill).

    /// <summary>Imports, the module documentation, the opened namespaces and the evaluation options.</summary>
    private const string Header = """
        import KatLangArityLaws.StoredCallableNormal
        import KatLangArityLaws.MemberBridgeSourceAliases
        import KatLangArityLaws.MemberBridgeSourcePaths
        import KatLangArityLaws.MemberBridgeSourceParameters

        /-!
        # The member bridge FROM THE PROBE, applied to source programs (E-18 step 1, M1)

        `NavigationSettled.member_bridge_of_probe` is the member bridge for every bundle with the production
        probe as its only navigation premise. This module APPLIES it — one theorem, every receiver class —
        from the state BEFORE the plan's classification (`entry`, the state the VALUE shell runs the plan
        from):

        | namespace | receiver | what the probe's navigation does |
        | --- | --- | --- |
        | `RuntimeEmpty`, `RuntimeSpreadNone`, `RuntimeSpreadOne`, `RuntimeSpreadFails` | `RTC = Capture(FM(0)).Algorithm` | RUNTIME-TARGET ALIAS: route decision, binding cell recorded, its CALLABLE projected (a flight that evaluates the receiver) |
        | `RuntimeNamedOrdinary`, `RuntimeNamedSpreadOne`, `RuntimeNamedSpreadFails` | `RTA = RC.Algorithm` | runtime-target alias over a STATIC receiver `RC` |
        | `PathRefEmpty`, `PathRefSpreadNone`, `PathRefSpreadOne`, `PathRefSpreadFails`, `PathRefOrdinary` | `ALS = Lib.Sub` | transparent reference whose row is a MEMBER PATH |
        | `RefEmpty`, `RefSpreadNone`, `RefSpreadOne`, `RefSpreadFails`, `RefOrdinary` | `AB = Box` | transparent reference, name row |
        | `OpenEmpty`, `OpenSpreadNone` | `OBox`, through `open OLib` | opened name |
        | `NestedEmpty`, `NestedSpreadOne`, `NestedSpreadFails` | `Lib.Sub` | nested member path (`probe_member`) |
        | `ParamEmpty`, `ParamRefSpreadNone`, `ParamSpreadFails` | `b` | parameter: first projection of its cell |
        | `ParamPathEmpty` | `b.Sub` | PARAMETER-ROOTED member path |

        Bundles: empty, a spread forming no cell, a spread forming one cell, a FAILING spread, an ordinary
        list.

        Per instance, the premises of `member_bridge_of_probe` and where each is proved:

        * `nav_run` — `NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed)`: the
          navigation core completes the probe from `entry` (`navFuel` at an explicit fuel, by `cbv`); it is
          the production probe (`NavRuns.production`, `probe_entry`);
        * `no_mint` — the probe advanced no runtime-declaration identity;
        * `select` — production's own dot decision selects the DECLARED member;
        * `head_normal` (parameter heads) — the CALLABLE the parameter's cell projects is structure-normal:
          DERIVED by `StoredCallableNormal.param_head_normal` from two facts of the reached heap (the
          parameter's cell awaits its first projection, and was supplied with a written name);
        * `production_entry` — production completes from `entry`.
        * `input_free` — the plan's context is outside every retained cell's computation (ledger R-1), so
          no member access of the route notes an input record; of the re-used instance, or stated here.

        `nav_settled` is the DERIVED `NavSettled` (over every navigation extension of the probe's exit) and
        `bridge_of_probe` the theorem applied. Nothing here assumes settledness, an alias-key fact or an
        activation fact.

        The namespaces of `MemberBridgeSource*` are re-used with their definitions and reachability chain
        (`captured`, `program_run`, `plan_cell`, `flight`, `demand_passes`); the namespaces new here
        (`RuntimeSpreadNone`, `RuntimeSpreadFails`, `RuntimeNamedSpreadOne`, `RuntimeNamedSpreadFails`, `PathRefSpreadNone`,
        `PathRefSpreadOne`, `PathRefSpreadFails`, `PathRefOrdinary`) carry their own.

        NOT here, and why: the EMPTY bundle over the named runtime-target alias (`RTA.Pair()`): the receiver
        `RC` is a cached property, and the zero-supply call's CACHE-PUB-1 publication compares its
        `reprStr`-built cache key with `RC`'s — a comparison of two printed keys of different owners, which
        no Lean proof decides (`Std.Format.pretty` is opaque). `RTC.Pair()` (`RuntimeEmpty`) is the empty
        bundle of the class; `RTA` has the ordinary, spread-first and failing-spread bundles.

        NOT here: a reference CHAIN of two steps (`AB2 = AB`). The theorem covers it without any key
        premise, but the instance's run facts cannot be proved by any Lean proof: the chase compares the
        second step's `reprStr`-built key with the first's, and `Std.Format.pretty` is opaque
        (`NavigationRereadGuards` checks that run by execution instead).

        GENERATED text, never edited by hand. The generator — this header, the instance templates and the
        instance tables — is
        `dotnet/tests/KatLang.Tests/LeanProofModules/MemberRereadInstancesLeanArtifactTests.cs`. To change an
        instance or a statement, edit it there and regenerate from the repo root with
          $env:KATLANG_REGENERATE_MEMBER_REREAD_INSTANCES = "1"
          dotnet test ./dotnet/tests/KatLang.Tests/KatLang.Tests.csproj --filter MemberRereadInstancesLeanArtifact
        (that run writes this file and then fails by design), then run `lake build KatLangArityLaws`: the
        generator writes the text, and only Lean checks the proofs.
        -/

        open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
        open KatLang.NavigationReread KatLang.NavigationSettled KatLang.StoredCallableNormal
        open KatLang.MemberStabilityInstances
        open KatLang.PlanAlgorithmBridgeInstances (completeB complete_of_B)
        open KatLang.PlanAlgorithmBridgeInstances.Source (demand_passes_flight)

        namespace KatLang.MemberRereadInstances

        set_option maxRecDepth 100000
        set_option maxHeartbeats 4000000
        set_option cbv.maxSteps 20000000

        """;

    private const string Footer = "\nend KatLang.MemberRereadInstances\n";

    /// <summary>An instance of <c>MemberBridgeSource*</c> in the ROOT context: definitions and reachability re-used.</summary>
    private const string ReusedRootTemplate = """

        /-! ## `@NS@`: `@TEXT@` — @KIND@ -/

        namespace @NS@
        open KatLang.MemberStabilityInstances.@NS@

        theorem rfacts :
            ((navFuel @FUEL@ (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
            (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
            (completeB ((evalCounted src ctx []).runState entry).1 = true) := by
          cbv
          all_goals (repeat' (first | rfl | constructor))

        /-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
        theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
          have h := rfacts.1
          rw [probe_owner] at h
          exact ⟨@FUEL@, h, nofun⟩

        theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

        theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry := complete_of_B rfacts.2.2

        theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
          have h := selected
          rw [probe_owner] at h
          exact h

        /-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
            navigation extension — derived from the probe. -/
        theorem nav_settled : NavSettled target ctx owner probed :=
          navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)
            input_free

        /-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
        theorem bridge_of_probe :
            (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
              (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
          member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
            (fun _ _ _ hx => nomatch hx) production_entry input_free

        end @NS@

        """;

    /// <summary>An instance of <c>MemberBridgeSourceParameters</c>: the plan is written in a parameter owner's body.</summary>
    private const string ReusedParameterTemplate = """

        /-! ## `@NS@`: `@TEXT@` — @KIND@ -/

        namespace @NS@
        open KatLang.MemberStabilityInstances.@NS@

        /-- The cell the head parameter `b` holds at `entry`. -/
        def cellB : Nat := (parameterAddressIn entry.lexicalActivations "b" ctxIn).getD 0

        theorem rfacts :
            ((navFuel @FUEL@ (.resolveDotReceiver? target ctxIn)).runState entry = (.ok alg?, probed)) ∧
            (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
            (completeB ((evalCounted src ctxIn envIn).runState entry).1 = true) ∧
            (parameterAddressIn entry.lexicalActivations "b" ctxIn = some cellB) ∧
            (staticUnprojected entry cellB = true) := by
          cbv
          all_goals (repeat' (first | rfl | constructor))

        /-- The probe's own run over recorded data: the navigation core completes it from `entry` — the
            parameter's captured activation is recorded (`NavigationReread.anchored`). -/
        theorem nav_run : NavRuns (.resolveDotReceiver? target ctxIn) entry (.ok (some owner), probed) := by
          have h := rfacts.1
          rw [probe_owner] at h
          exact ⟨@FUEL@, h, nofun⟩

        theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration := rfacts.2.1

        theorem production_entry : ProductionCompletes (evalCounted src ctxIn envIn) entry := complete_of_B rfacts.2.2.1

        theorem select : selectDotEdge ctxIn target N (some owner) = .ok (.member owner p) := by
          have h := selected
          rw [probe_owner] at h
          exact h

        /-- The parameter's cell at `entry`, and its state: awaiting its FIRST projection, supplied with a
            written name (`StoredCallableNormal.staticUnprojected`). -/
        theorem head_cell : parameterAddressIn entry.lexicalActivations "b" ctxIn = some cellB := rfacts.2.2.2.1

        theorem head_unprojected : staticUnprojected entry cellB = true := rfacts.2.2.2.2

        /-- **`param_head_normal` APPLIED**: the CALLABLE the head parameter's cell projects is
            structure-normal — DERIVED from the cell's own suspension, not assumed. -/
        theorem head_normal : ∀ x o v, headParam? target = some x →
            (projectParameterCallable x ctxIn).runState entry = (.ok (some o), v) → structureNormal o = true := by
          intro x o v hx hrun
          have hb : headParam? target = some "b" := rfl
          rw [hb] at hx
          cases hx
          exact param_head_normal "b" ctxIn entry cellB head_cell head_unprojected o v hrun

        /-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
            navigation extension — derived from the probe. -/
        theorem nav_settled : NavSettled target ctxIn owner probed :=
          navSettled_of_navRuns target ctxIn entry probed owner rfl nav_run no_mint head_normal input_free

        /-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
        theorem bridge_of_probe :
            (ordinaryCall productionPlanRoute k shape .call).runState entry =
              (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState entry :=
          member_bridge_of_probe k target N (.resolve N) args ctxIn envIn entry probed owner p rfl nav_run no_mint select
            head_normal production_entry input_free

        end @NS@

        """;

    /// <summary>A NEW instance in the ROOT context, with its own reachability chain.</summary>
    private const string NewRootTemplate = """

        /-! ## `@NS@`: `@TEXT@` — @KIND@ -/

        namespace @NS@

        /-- @DOC@ -/
        def target : Expr := @TARGET@
        def N : Ident := "@MEMBER@"
        def args : OutputBundle := @ARGS@
        def path : Expr := .dotMember target N (.resolve N) none
        /-- The plan's written source `@TEXT@`. -/
        def src : Expr := .dotMember target N (.resolve N) (some args)
        /-- THE SOURCE PROGRAM's one row: `Capture(@TEXT@)`. -/
        def row : Expr := MemberStabilityInstances.capture src
        def ctx : EvalCtx := MemberStabilityInstances.ctxOf [row]
        def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩
        /-- The plan's context is outside every retained cell's computation (ledger R-1): no member access
            of its route notes an input record. -/
        theorem input_free : ctx.inputRecord = none := rfl

        def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
        def entry : EvalState := withState 0 .evaluating fin
        def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
        /-- The receiver's identity as production's probe answers it. -/
        def alg? : Option Algorithm :=
          match ((resolveDotReceiver? target ctx).runState entry).1 with
          | .ok a => a
          | .error _ => none
        /-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
        def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
        def owner : Algorithm := alg?.getD (alg [] [] [] [])
        def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
        /-- The plan's flight on the member (`.call`) route. -/
        def x : EvalState := withRoute 0 .call probed

        /-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`). -/
        theorem rfacts :
            ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
            ((evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
            (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
            (entry.needs[0]? = some entryCell) ∧
            ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
            (alg? = some owner) ∧
            (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
            ((probed.needs[0]?).bind NeedCell.route = none) ∧
            (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
            ((navFuel @FUEL@ (.resolveDotReceiver? target ctx)).runState entry = (.ok alg?, probed)) ∧
            (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
            (completeB ((evalCounted src ctx []).runState entry).1 = true) ∧
            (@VALUE@) ∧
            (@WROTE@) := by
          cbv
          all_goals (repeat' (first | rfl | constructor))

        /-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
            written invocation: the reference to cell 0. -/
        theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) := rfacts.1

        theorem program_run :
            (evalProgramOutput (wireToCaller MemberStabilityInstances.base (MemberStabilityInstances.rootOf [row])) MemberStabilityInstances.base []).runState EvalState.empty =
              (.ok (.callRef 0), fin) := rfacts.2.1

        /-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
        theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } := rfacts.2.2.1

        theorem entry_cell : entry.needs[0]? = some entryCell := rfacts.2.2.2.1

        /-- The production probe from `entry`. -/
        theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) := rfacts.2.2.2.2.1

        theorem probe_owner : alg? = some owner := rfacts.2.2.2.2.2.1

        /-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
        theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) := rfacts.2.2.2.2.2.2.1

        theorem route_free : (probed.needs[0]?).bind NeedCell.route = none := rfacts.2.2.2.2.2.2.2.1

        /-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
            probe and the dot decision, recorded as the `.call` route. -/
        theorem flight :
            (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
              (.ok .call, x) :=
          MemberStabilityInstances.flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
            selected route_free input_free

        theorem demand_done :
            ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
          rfacts.2.2.2.2.2.2.2.2.1

        /-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
        theorem demand_passes :
            (demandNeed 0).runState fin =
              (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
               (res.1, withState 0 (.completed res.1) res.2)) :=
          demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

        /-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
        theorem nav_run : NavRuns (.resolveDotReceiver? target ctx) entry (.ok (some owner), probed) := by
          have h := rfacts.2.2.2.2.2.2.2.2.2.1
          rw [probe_owner] at h
          exact ⟨@FUEL@, h, nofun⟩

        theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration :=
          rfacts.2.2.2.2.2.2.2.2.2.2.1

        theorem production_entry : ProductionCompletes (evalCounted src ctx []) entry :=
          complete_of_B rfacts.2.2.2.2.2.2.2.2.2.2.2.1

        theorem select : selectDotEdge ctx target N (some owner) = .ok (.member owner p) := by
          have h := selected
          rw [probe_owner] at h
          exact h

        /-- @VALUEDOC@ -/
        theorem outcome : @VALUE@ := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.1

        /-- @WROTEDOC@ -/
        theorem probe_effect : @WROTE@ := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2

        /-- **`navSettled_of_navRuns` APPLIED**: settled navigation at the probe's exit, over EVERY
            navigation extension — derived from the probe. -/
        theorem nav_settled : NavSettled target ctx owner probed :=
          navSettled_of_navRuns target ctx entry probed owner rfl nav_run no_mint (fun _ _ _ hx => nomatch hx)
            input_free

        /-- **`member_bridge_of_probe` APPLIED** from the state before the classification. -/
        theorem bridge_of_probe :
            (ordinaryCall productionPlanRoute 0 shape .call).runState entry =
              (reCountValueBoundary <$> evalCounted src ctx []).runState entry :=
          member_bridge_of_probe 0 target N (.resolve N) args ctx [] entry probed owner p rfl nav_run no_mint select
            (fun _ _ _ hx => nomatch hx) production_entry input_free

        end @NS@

        """;
}
