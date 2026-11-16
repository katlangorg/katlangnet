using System.Text;

namespace KatLang.Tests.LeanProofModules;

/// <summary>
/// Generates and pins <c>lean/KatLangArityLaws/PublishedCallableInstances.lean</c> (E-18 step 1, M1 —
/// instances): <c>PublishedCallableNormal.member_bridge_of_probe_reached</c> APPLIED to source programs whose
/// head parameter is bound to an intrinsic <c>.Algorithm</c> link.
///
/// <para>The module is GENERATED text: <see cref="Header"/> (the documentation and the source program's
/// declarations, written by hand HERE) followed by <see cref="InstanceTemplate"/> filled once per row of
/// <see cref="Instances"/>. To add or change an instance, or to follow a change to a statement the instances
/// mention, edit the table or the template here, regenerate, and build the Lean target: the proofs are
/// checked by Lean, not by this test.</para>
///
/// <para>This generator replaces a Python script that existed only in an ignored scratch folder of one
/// machine. On the day it was ported (2026-11-16) both produced the tracked module byte for byte.</para>
///
/// Regenerate with:
///   $env:KATLANG_REGENERATE_PUBLISHED_CALLABLE_INSTANCES = "1"
///   dotnet test ./tests/KatLang.Tests/KatLang.Tests.csproj --filter PublishedCallableInstancesLeanArtifact
/// That run writes the module and then fails by design (see <see cref="ArtifactRegeneration"/>); review the
/// diff, clear the flag, rerun, and run <c>lake build KatLangArityLaws</c>.
/// </summary>
public class PublishedCallableInstancesLeanArtifactTests
{
    internal const string ArtifactRelativePath = "lean/KatLangArityLaws/PublishedCallableInstances.lean";

    [Fact]
    public void GeneratedLeanModule_IsItsGeneratorsOutput()
        => LeanProofModuleArtifact.VerifyOrRegenerate(
            RegenerationFlags.PublishedCallableInstances, ArtifactRelativePath, GenerateArtifact());

    /// <summary>
    /// Every table row opens its own Lean namespace, and the module header's instance table names it: a row
    /// added without its header entry, or two rows under one name, is a generator mistake that Lean would
    /// report late (a duplicate declaration) or not at all (an undocumented instance).
    /// </summary>
    [Fact]
    public void EveryInstance_OpensItsOwnNamespace_NamedInTheModuleHeader()
    {
        var namespaces = Instances.Select(static instance => instance.Name).ToList();

        Assert.NotEmpty(namespaces);
        Assert.Equal(namespaces.Count, namespaces.Distinct(StringComparer.Ordinal).Count());
        Assert.All(namespaces, name => Assert.Contains($"| `{name}` |", Header, StringComparison.Ordinal));

        var generated = GenerateArtifact();
        Assert.All(namespaces, name =>
        {
            Assert.Equal(1, LeanProofModuleArtifact.CountOccurrences(generated, $"\nnamespace {name}\n"));
            Assert.Equal(1, LeanProofModuleArtifact.CountOccurrences(generated, $"\nend {name}\n"));
        });
    }

    /// <summary>The module's whole text: the header, the instances in table order, the footer.</summary>
    internal static string GenerateArtifact()
    {
        var builder = new StringBuilder(Header);

        foreach (var instance in Instances)
        {
            builder.Append(LeanProofModuleArtifact.Fill(
                InstanceTemplate,
                ("NAME", instance.Name), ("TITLE", instance.Title),
                ("TARGETDOC", instance.TargetDoc), ("TARGET", instance.Target),
                ("MEMBER", instance.Member), ("HEAD", instance.Head),
                ("ROWDOC", instance.RowDoc), ("ROW", instance.Row),
                ("VALUE", instance.Value),
                ("CAPTURED", instance.Captured), ("CAPTUREDDOC", instance.CapturedDoc),
                ("NEWCELLS", instance.NewCells)));
        }

        builder.Append(Footer);
        return builder.ToString().ReplaceLineEndings("\n");
    }

    // ── The instance table ──────────────────────────────────────────────────────────────────────

    /// <summary>
    /// One instance. The Lean fields: the receiver expression (<paramref name="Target"/>), the member name,
    /// the head parameter, the program row, the call's value (a Lean numeral), whether the head parameter is
    /// read through a captured ancestor activation (a Lean <c>Bool</c>), and the number of cells the receiver
    /// probe allocates (a Lean numeral).
    /// </summary>
    private sealed record Instance(
        string Name,
        string Title,
        string TargetDoc,
        string Target,
        string Member,
        string Head,
        string RowDoc,
        string Row,
        string Value,
        string Captured,
        string CapturedDoc,
        string NewCells);

    private static readonly Instance[] Instances =
    [
        new(
            Name: "LinkParam",
            Title: "`b.G(5)` inside `PG(b)`, called as `PG(RC.Algorithm)` — a parameter bound to an intrinsic `.Algorithm` link",
            TargetDoc: "The receiver is the parameter `b`, bound to the link `RC.Algorithm`.",
            Target: ".param \"b\"",
            Member: "G",
            Head: "b",
            RowDoc: "`PG(RC.Algorithm)`, with `PG(b) = Capture(b.G(5))` and `RC = Capture(FM(0))`",
            Row: "callN \"PG\" [dot (.resolve \"RC\") \"Algorithm\" none]",
            Value: "5",
            Captured: "false",
            CapturedDoc: "`b` is a parameter of the plan's own site, read from the context's tier.",
            NewCells: "4"),
        new(
            Name: "LinkAncestor",
            Title: "`c.G(5)` inside `Inner(z)` of `PA(c)`, called as `PA(RC.Algorithm)` — a CAPTURED-ANCESTOR parameter bound to a link",
            TargetDoc: "The receiver is the ancestor parameter `c` of the enclosing `PA`, bound to the link `RC.Algorithm`.",
            Target: ".param \"c\"",
            Member: "G",
            Head: "c",
            RowDoc: "`PA(RC.Algorithm)`, with `PA(c) = { Inner(z) = Capture(c.G(5)) ⏎ Inner(0) }`",
            Row: "callN \"PA\" [dot (.resolve \"RC\") \"Algorithm\" none]",
            Value: "5",
            Captured: "true",
            CapturedDoc: "`c` belongs to the enclosing `PA`: it is read through the RECORDED activation of its owner (`capturedId?` is `some`).",
            NewCells: "4"),
        new(
            Name: "LinkForwardedPath",
            Title: "`b.Sub.H(5)` inside `PH(b)`, reached as `PN(RS.Algorithm)` with `PN(c) = PH(c)` — FORWARDING and a parameter-rooted member path",
            TargetDoc: "The receiver is the member path `b.Sub` over the parameter `b`, which transports `PN`'s parameter `c`, bound to the link `RS.Algorithm`.",
            Target: ".dotMember (.param \"b\") \"Sub\" (.resolve \"Sub\") none",
            Member: "H",
            Head: "b",
            RowDoc: "`PN(RS.Algorithm)`, with `PN(c) = PH(c)`, `PH(b) = Capture(b.Sub.H(5))` and `RS = Capture(FS(0))`",
            Row: "callN \"PN\" [dot (.resolve \"RS\") \"Algorithm\" none]",
            Value: "6",
            Captured: "false",
            CapturedDoc: "`b` is a parameter of the plan's own site; its cell IS the cell `PN` received (NEED-01 transport).",
            NewCells: "4"),
    ];

    // ── The module text ─────────────────────────────────────────────────────────────────────────
    //
    // Lean text, verbatim. A placeholder is @NAME@ (LeanProofModuleArtifact.Fill).

    /// <summary>
    /// Imports, the module documentation, the opened namespaces, the evaluation options and the SOURCE PROGRAM
    /// every instance runs in (its declarations, root and context). Hand-written.
    /// </summary>
    private const string Header = """
        import KatLangArityLaws.PublishedCallableNormal
        import KatLangArityLaws.MemberBridgeSourceParameters

        /-!
        # The member bridge on REACHED states, structure-normality discharged (E-18 step 1, M1 — instances)

        `PublishedCallableNormal.member_bridge_of_probe_reached` is the member bridge whose premise on the
        parameter head's CALLABLE is the whole-run invariant `Publications.NormalHeap` instead of a fact
        about one cell. These instances APPLY it on source programs where the earlier premise
        (`StoredCallableNormal.param_head_normal`: the cell awaits its first projection and was supplied
        with a written name, block or dot expression that is no link) does NOT hold — the parameter is
        bound to an INTRINSIC `.Algorithm` LINK, whose CALLABLE is another cell's outcome (the captured
        call's callee cell):

        | instance | program row | what it adds |
        | --- | --- | --- |
        | `LinkParam` | `PG(RC.Algorithm)`, `PG(b) = Capture(b.G(5))` | a parameter bound to a link |
        | `LinkAncestor` | `PA(RC.Algorithm)`, `PA(c) = { Inner(z) = Capture(c.G(5)) ⏎ Inner(0) }` | the same through a CAPTURED-ANCESTOR context: the plan is written in a nested body, and the head parameter is read through the recorded activation of its owner (`captured_ancestor`: `capturedId?` is `some`, and the read is anchored) |
        | `LinkForwardedPath` | `PN(RS.Algorithm)`, `PN(c) = PH(c)`, `PH(b) = Capture(b.Sub.H(5))` | FORWARDING (the inner parameter transports the outer one's cell) and a parameter-rooted member PATH |

        In each: `head_is_link` (the earlier premise is false here), `heap_normal` — **`NormalHeap` of the
        entry state from REACHABILITY alone**: the state is production's evaluation of the row from the
        empty state (`production_normalHeap`) followed by the VALUE shell's mark (`normalHeap_modify`); it is
        not decided by evaluating the heap — `head_projection_normal`, `nav_settled`
        (`navSettled_of_navRuns_reached`) and `bridge` (`member_bridge_of_probe_reached`).

        Method, reachability chain and the meaning of "reached" are those of `MemberBridgeSourceInstances`
        (`captured`, `program_run`, `plan_cell`, `flight`, `demand_passes`); every run equation is one
        proof-producing evaluation (`cbv`) per namespace. The bundles are ordinary (`G(5)`, `H(5)`): the
        receiver read publishes the cached property `RC` / `RS`, and a zero-supply member call would compare
        its cache key with that entry's — two printed keys of different owners, which no Lean proof decides.

        The navigation run (`nav_run`) is still established by evaluating the navigation core: `NavRuns`
        from the production probe alone is NOT a theorem (captured-activation validity is not yet a
        whole-run invariant).

        GENERATED text, never edited by hand. The generator — this header, the instance template and the
        instance table — is
        `tests/KatLang.Tests/LeanProofModules/PublishedCallableInstancesLeanArtifactTests.cs`. To change an
        instance or a statement, edit it there and regenerate from the repo root with
          $env:KATLANG_REGENERATE_PUBLISHED_CALLABLE_INSTANCES = "1"
          dotnet test ./tests/KatLang.Tests/KatLang.Tests.csproj --filter PublishedCallableInstancesLeanArtifact
        (that run writes this file and then fails by design), then run `lake build KatLangArityLaws`: the
        generator writes the text, and only Lean checks the proofs.
        -/

        open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
        open KatLang.NavigationReread KatLang.NavigationSettled KatLang.StoredCallableNormal
        open KatLang.Publications KatLang.PublishedCallableNormal
        open KatLang.MemberStabilityInstances (metaParam callN dot add fm base flight_member)
        open KatLang.PlanAlgorithmBridgeInstances (completeB complete_of_B)
        open KatLang.PlanAlgorithmBridgeInstances.Source (demand_passes_flight)

        namespace KatLang.PublishedCallableInstances

        set_option maxRecDepth 100000
        set_option maxHeartbeats 4000000
        set_option cbv.maxSteps 20000000

        /-! ## The source program -/

        /-- `Capture(e)`. -/
        def cap (e : Expr) : Expr := callN "Capture" [e]

        /-- `FS(x) = { Sub = { H(y) = y + 1 ⏎ K = 3 } ⏎ x }`: a callable whose member declares members. -/
        def fs : Algorithm :=
          algPrivate ["x"] []
            [("Sub", algPrivate [] [] [("H", alg ["y"] [] [] [add (.param "y") (.num 1)]), ("K", alg [] [] [] [.num 3])] [])]
            [.param "x"]

        /-- `PA(c) = { Inner(z) = Capture(c.G(5)) ⏎ Inner(0) }`: the plan is written in a nested body that
            captures the ancestor parameter `c` (`Inner` is local to `PA`'s activation). -/
        def pa : Algorithm :=
          Algorithm.mk none (Algorithm.normalParameters ["c"]) []
            [privateLocalProp "Inner" (.localCapturedAncestorParams ["c"])
              (alg ["z"] [] [] [cap (dot (.param "c") "G" (some [.num 5]))])]
            [callN "Inner" [.num 0]]

        /-- `Capture(meta op) = op`; `FM` (members `V`, `G`, `Pair`); `FS` (member `Sub`);
            `RC = Capture(FM(0))`, `RS = Capture(FS(0))` (captured calls);
            `PG(b) = Capture(b.G(5))`; `PA` (above); `PH(b) = Capture(b.Sub.H(5))`; `PN(c) = PH(c)`. -/
        def decls : List (Ident × Algorithm) :=
          [("Capture", algWithParameters [metaParam "op"] [] [] [.param "op"]),
           ("FM", fm),
           ("FS", fs),
           ("RC", alg [] [] [] [cap (callN "FM" [.num 0])]),
           ("RS", alg [] [] [] [cap (callN "FS" [.num 0])]),
           ("PG", alg ["b"] [] [] [cap (dot (.param "b") "G" (some [.num 5]))]),
           ("PH", alg ["b"] [] [] [cap (dot (dot (.param "b") "Sub" none) "H" (some [.num 5]))]),
           ("PN", alg ["c"] [] [] [callN "PH" [.param "c"]])]

        /-- The program's root algorithm with the declaration identities `runResultM` assigns. -/
        def rootOf (rows : List Expr) : Algorithm :=
          match (identifyPropertyExpr (.algorithmExpr
              (Algorithm.mk none [] [] (propsPrivate decls ++ [privateProp "PA" pa]) rows))).run' 0 with
          | .algorithmExpr a => a
          | _ => alg [] [] [] []

        /-- The context a program's root rows are evaluated in (`runResultM`'s wiring). -/
        def ctxOf (rows : List Expr) : EvalCtx := base.push (wireToCaller base (rootOf rows))


        """;

    private const string Footer = "end KatLang.PublishedCallableInstances\n";

    /// <summary>One instance: its definitions, its evaluated facts in one proof-producing evaluation, and the theorems read off them.</summary>
    private const string InstanceTemplate = """
        /-! ## `@NAME@`: @TITLE@ -/

        namespace @NAME@

        /-- @TARGETDOC@ -/
        def target : Expr := @TARGET@
        def N : Ident := "@MEMBER@"
        def args : OutputBundle := [.num 5]
        def path : Expr := .dotMember target N (.resolve N) none
        /-- The plan's written source. -/
        def src : Expr := .dotMember target N (.resolve N) (some args)
        /-- THE SOURCE PROGRAM's one row: @ROWDOC@. -/
        def row : Expr := @ROW@
        def ctx : EvalCtx := ctxOf [row]

        def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
        /-- The plan cell: the cell the program's result names. -/
        def k : Nat := match ((evalCounted row ctx []).runState EvalState.empty).1 with | .ok (.callRef a, _) => a | _ => 0
        /-- THE GENUINE CONTEXT of the plan: the context the source binders built, read off the plan cell. -/
        def ctxIn : EvalCtx := match fin.needs[k]? with | some { suspension := .expression _ c _, .. } => c | _ => ctx
        def envIn : ValEnv := match fin.needs[k]? with | some { suspension := .expression _ _ v, .. } => v | _ => []
        def shape : NeedPlan.CallShape := ⟨path, args, ctxIn, envIn, .dot target N (.resolve N)⟩

        /-- The state the VALUE shell runs the plan from. -/
        def entry : EvalState := withState k .evaluating fin
        def entryCell : NeedCell := { suspension := .expression src ctxIn envIn, state := .evaluating }
        /-- The cell the head parameter `@HEAD@` holds at `entry`. -/
        def cellB : Nat := (parameterAddressIn entry.lexicalActivations "@HEAD@" ctxIn).getD 0
        /-- The receiver's identity as production's probe answers it. -/
        def alg? : Option Algorithm :=
          match ((resolveDotReceiver? target ctxIn).runState entry).1 with
          | .ok a => a
          | .error _ => none
        /-- The probe's exit state: the head parameter's FIRST CALLABLE projection — a link's — ran. -/
        def probed : EvalState := ((resolveDotReceiver? target ctxIn).runState entry).2
        def owner : Algorithm := alg?.getD (alg [] [] [] [])
        def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
        /-- The plan's flight on the member (`.call`) route. -/
        def x : EvalState := withRoute k .call probed

        /-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`). -/
        theorem rfacts :
            ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin)) ∧
            ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef k), fin)) ∧
            (fin.needs[k]? = some { suspension := .expression src ctxIn envIn }) ∧
            (entry.needs[k]? = some entryCell) ∧
            ((resolveDotReceiver? target ctxIn).runState entry = (.ok alg?, probed)) ∧
            (alg? = some owner) ∧
            (selectDotEdge ctxIn target N alg? = .ok (.member owner p)) ∧
            ((probed.needs[k]?).bind NeedCell.route = none) ∧
            (((NeedPlan.executeAlong productionPlanRoute k shape .call).runState x).1.isIncomplete = false) ∧
            ((navFuel 64 (.resolveDotReceiver? target ctxIn)).runState entry = (.ok alg?, probed)) ∧
            (probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration) ∧
            (completeB ((evalCounted src ctxIn envIn).runState entry).1 = true) ∧
            (((ordinaryCall productionPlanRoute k shape .call).runState entry).1 = .ok (.atom @VALUE@, 1)) ∧
            (parameterAddressIn entry.lexicalActivations "@HEAD@" ctxIn = some cellB) ∧
            (staticUnprojected entry cellB = false) ∧
            ((entry.needs[cellB]?.map fun c => match c.suspension with
                | .expression source _ _ => (linkEdge? source).isSome
                | _ => false) = some true) ∧
            ((capturedId? "@HEAD@" ctxIn).isSome = @CAPTURED@) ∧
            (anchored "@HEAD@" ctxIn entry = true) ∧
            (probed.needs.size = entry.needs.size + @NEWCELLS@) := by
          cbv
          all_goals (repeat' (first | rfl | constructor))

        /-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
            written invocation: the reference to cell `k`. -/
        theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin) := rfacts.1

        theorem program_run :
            (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
              (.ok (.callRef k), fin) := rfacts.2.1

        /-- **REACHED (2).** Cell `k` is THE PLAN, suspended in the context the program's binders built. -/
        theorem plan_cell : fin.needs[k]? = some { suspension := .expression src ctxIn envIn } := rfacts.2.2.1

        theorem entry_cell : entry.needs[k]? = some entryCell := rfacts.2.2.2.1

        /-- The production probe from `entry`. -/
        theorem probe_entry : (resolveDotReceiver? target ctxIn).runState entry = (.ok alg?, probed) := rfacts.2.2.2.2.1

        theorem probe_owner : alg? = some owner := rfacts.2.2.2.2.2.1

        /-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
        theorem selected : selectDotEdge ctxIn target N alg? = .ok (.member owner p) := rfacts.2.2.2.2.2.2.1

        theorem route_free : (probed.needs[k]?).bind NeedCell.route = none := rfacts.2.2.2.2.2.2.2.1

        /-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
            probe and the dot decision, recorded as the `.call` route. -/
        theorem flight :
            (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify k shape)).runState entry =
              (.ok .call, x) :=
          flight_member k target N (.resolve N) args ctxIn envIn entry probed entryCell alg? _ entry_cell rfl probe_entry
            selected route_free

        theorem demand_done :
            ((NeedPlan.executeAlong productionPlanRoute k shape .call).runState x).1.isIncomplete = false :=
          rfacts.2.2.2.2.2.2.2.2.1

        /-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
        theorem demand_passes :
            (demandNeed k).runState fin =
              (let res := (NeedPlan.executeAlong productionPlanRoute k shape .call).runState x
               (res.1, withState k (.completed res.1) res.2)) :=
          demand_passes_flight k fin x _ src ctxIn envIn shape .call plan_cell rfl rfl rfl flight nofun demand_done

        /-- The probe's own run over recorded data: the navigation core completes it from `entry`. -/
        theorem nav_run : NavRuns (.resolveDotReceiver? target ctxIn) entry (.ok (some owner), probed) := by
          have h := rfacts.2.2.2.2.2.2.2.2.2.1
          rw [probe_owner] at h
          exact ⟨64, h, nofun⟩

        theorem no_mint : probed.nextRuntimeDeclaration = entry.nextRuntimeDeclaration :=
          rfacts.2.2.2.2.2.2.2.2.2.2.1

        theorem production_entry : ProductionCompletes (evalCounted src ctxIn envIn) entry :=
          complete_of_B rfacts.2.2.2.2.2.2.2.2.2.2.2.1

        theorem select : selectDotEdge ctxIn target N (some owner) = .ok (.member owner p) := by
          have h := selected
          rw [probe_owner] at h
          exact h

        /-- The call's value. -/
        theorem outcome : ((ordinaryCall productionPlanRoute k shape .call).runState entry).1 = .ok (.atom @VALUE@, 1) :=
          rfacts.2.2.2.2.2.2.2.2.2.2.2.2.1

        theorem head_cell : parameterAddressIn entry.lexicalActivations "@HEAD@" ctxIn = some cellB :=
          rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

        /-- **The earlier premise does NOT hold here**: the head parameter's cell was supplied with an
            `.Algorithm` LINK (`head_link`), so `StoredCallableNormal.staticUnprojected` is false and
            `param_head_normal` does not apply. -/
        theorem head_is_link : staticUnprojected entry cellB = false := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

        theorem head_link : (entry.needs[cellB]?.map fun c => match c.suspension with
            | .expression source _ _ => (linkEdge? source).isSome
            | _ => false) = some true := rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

        /-- How the head parameter is found: @CAPTUREDDOC@ In either case the read is ANCHORED. -/
        theorem captured_ancestor : (capturedId? "@HEAD@" ctxIn).isSome = @CAPTURED@ ∧ anchored "@HEAD@" ctxIn entry = true :=
          ⟨rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

        /-- The probe's flight is a RUNTIME projection: it allocates four cells (the link's receiver cell and
            what that receiver's VALUE and the captured call's callee read supply) before it publishes. -/
        theorem probe_effect : probed.needs.size = entry.needs.size + @NEWCELLS@ :=
          rfacts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

        /-- **THE ENTRY HEAP IS NORMAL — FROM REACHABILITY.** `entry` is production's evaluation of the
            source row from the empty state, then the VALUE shell's mark on the plan cell: every production
            operation keeps a normal heap normal (`production_normalHeap`) and the mark keeps every CALLABLE
            field (`normalHeap_modify`). Nothing about the heap's contents is evaluated. -/
        theorem heap_normal : NormalHeap entry.needs :=
          normalHeap_modify (h := fin.needs)
            (production_normalHeap (.evalCounted row ctx []) EvalState.empty empty_normalHeap) k _ (fun _ => rfl)

        /-- **`param_head_normal_reached` APPLIED**: the identity the head parameter projects — a link's
            CALLABLE, the captured call's callee — is structure-normal, by the whole-run invariant. -/
        theorem head_projection_normal : ∀ o v,
            (projectParameterCallable "@HEAD@" ctxIn).runState entry = (.ok (some o), v) → structureNormal o = true :=
          param_head_normal_reached ctxIn entry heap_normal "@HEAD@"

        /-- **`navSettled_of_navRuns_reached` APPLIED**: settled navigation at the probe's exit, over EVERY
            navigation extension, with no premise on the head's CALLABLE. -/
        theorem nav_settled : NavSettled target ctxIn owner probed :=
          navSettled_of_navRuns_reached target ctxIn entry probed owner rfl nav_run no_mint heap_normal

        /-- **`member_bridge_of_probe_reached` APPLIED** from the state before the classification. -/
        theorem bridge :
            (ordinaryCall productionPlanRoute k shape .call).runState entry =
              (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState entry :=
          member_bridge_of_probe_reached k target N (.resolve N) args ctxIn envIn entry probed owner p rfl nav_run no_mint
            select heap_normal production_entry

        end @NAME@


        """;
}
