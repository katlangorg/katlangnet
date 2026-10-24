using System.Collections.ObjectModel;

namespace KatLang.Tests;

/// <summary>
/// One host-built AST differential case (HOST-DIFF-1). The program is CONSTRUCTED directly as a C#
/// AST, typically carrying PRE-WIRED <see cref="ScopeCtx"/> parent chains (a shape no source
/// program produces). The SAME object graph is evaluated by the C# evaluator
/// (<see cref="HostParentDifferentialHarness"/>) and encoded for Lean by <see cref="LeanAstEncoder"/>;
/// the generated <c>lean/CoreTests/HostParentDifferential.lean</c> then guards Lean's observation of
/// that encoding against the recorded C# one.
/// </summary>
/// <param name="Id">Stable case id (<c>HP-NNx</c>); the generated Lean name is derived from it.</param>
/// <param name="Description">What the case pins.</param>
/// <param name="Program">The ONE immutable program graph both sides consume.</param>
/// <param name="WatchedProperties">Property names whose published zero-argument cache entries are
/// compared (C# published entries per binding name vs Lean <c>zeroArgPropertyCache</c> entries).</param>
/// <param name="Divergence">Non-null exactly for a KNOWN Lean/C# model divergence (HOST-LEAN-O6):
/// the case is excluded from the comparable partition, and both sides' differing observations are
/// pinned instead (C# by <c>HostParentDifferentialTests</c>, Lean by a generated guard).</param>
public sealed record HostParentCase(
    string Id,
    string Description,
    Expr Program,
    IReadOnlyList<string> WatchedProperties,
    HostParentDivergence? Divergence = null)
{
    /// <summary>The Lean definition name of the case (<c>HP-01a</c> → <c>hp_01a</c>).</summary>
    public string LeanName => Id.Replace("-", "_", StringComparison.Ordinal).ToLowerInvariant();
}

/// <summary>
/// A reviewed, machine-checked model divergence: the exact C# neutral observation, the exact Lean
/// neutral observation of the encoded program, and the named reason (an owner-level decision, not
/// an encoder gap). Both observations are hand-reviewed constants, never regenerated from a run.
/// </summary>
public sealed record HostParentDivergence(string Reason, string CSharpNeutral, string LeanNeutral);

/// <summary>
/// The host-parent differential corpus: the HP-01..HP-14 matrix of HOST-DIFF-1 plus the discovered
/// shapes (record-equal / shared / reused host objects, parent-replacing wiring routes, alias and
/// family variants). Pure, Lean-representable ASTs only: no host operations, integer numbers.
/// A raw host chain has no implicit prelude level; the module controls pin this boundary too.
/// </summary>
public static class HostParentDifferentialCorpus
{
    // ── AST vocabulary ───────────────────────────────────────────────────────────────────────

    private static ReadOnlyCollection<T> L<T>(params T[] items) => Array.AsReadOnly(items);
    private static Expr R(string name) => new Expr.Resolve(name);
    private static Expr X(string name) => new Expr.Param(name);
    private static Expr N(int value) => new Expr.Num(value);
    private static Expr Add(Expr a, Expr b) => new Expr.Binary(BinaryOp.Add, a, b);
    private static Expr Sub(Expr a, Expr b) => new Expr.Binary(BinaryOp.Sub, a, b);
    private static Expr Mul(Expr a, Expr b) => new Expr.Binary(BinaryOp.Mul, a, b);
    private static Expr Call(string name, params Expr[] args) => new Expr.Call(R(name), new OutputBundle(args));
    private static Expr Call(Expr callee, params Expr[] args) => new Expr.Call(callee, new OutputBundle(args));
    private static Expr Dot(Expr target, string name) => new Expr.DotCall(target, name, null);
    private static Expr Block(Algorithm algorithm) => new Expr.AlgorithmExpr(algorithm);

    private static Algorithm.User Body(params Expr[] rows) => new(null, L<ParameterPattern>(), L<Expr>(), L<Property>(), new OutputBundle(rows));
    private static Algorithm.User BodyWith(Property[] properties, params Expr[] rows)
        => new(null, L<ParameterPattern>(), L<Expr>(), L(properties), new OutputBundle(rows));
    private static Algorithm.User Fn(string[] parameters, params Expr[] rows)
        => new(null, L(parameters.Select(p => (ParameterPattern)new CaptureParameterPattern(p)).ToArray()), L<Expr>(), L<Property>(), new OutputBundle(rows));
    private static Algorithm.User FnWith(string[] parameters, Property[] properties, params Expr[] rows)
        => new(null, L(parameters.Select(p => (ParameterPattern)new CaptureParameterPattern(p)).ToArray()), L<Expr>(), L(properties), new OutputBundle(rows));
    private static Algorithm.User Namespace(params Property[] members)
        => new(null, L<ParameterPattern>(), L<Expr>(), L(members), OutputBundle.Empty);

    private static Property Prop(string name, Algorithm value, bool isPublic = false) => new(name, value, isPublic);
    private static Property Public(string name, Algorithm value) => new(name, value, IsPublic: true);
    private static Property Local(string name, Algorithm value, params string[] required)
        => new(name, value, IsPublic: false, PropertyExposure.LocalOnlyCapturedAncestorParameters) { RequiredAncestorParameters = L(required) };

    private static ScopeCtx Scope(ScopeCtx? parent, params Property[] properties)
        => new(parent, L<Expr>(), L(properties));
    private static ScopeCtx ScopeOpening(ScopeCtx? parent, Expr[] opens, params Property[] properties)
        => new(parent, L(opens), L(properties));

    /// <summary>An opened inline block whose PRE-WIRED parent is <paramref name="parent"/> (the route that keeps it).</summary>
    private static Expr OpenBlock(ScopeCtx parent, Expr[] opens, params Property[] members)
        => Block(new Algorithm.User(parent, L<ParameterPattern>(), L(opens), L(members), OutputBundle.Empty));

    /// <summary>The root program: <c>open</c> the targets, declare <paramref name="properties"/>, emit <paramref name="rows"/>.</summary>
    private static Expr Program(Expr[] opens, Property[] properties, params Expr[] rows)
        => Block(new Algorithm.User(null, L<ParameterPattern>(), L(opens), L(properties), new OutputBundle(rows)));

    /// <summary>The established host pattern: <c>open { public Run = rows; members }</c> whose parent is <paramref name="scope"/>; output <c>Run</c>.</summary>
    private static Expr OpenedThrough(ScopeCtx scope, Expr[] rows, params Property[] members)
        => Program([OpenBlock(scope, [], [Public("Run", Body(rows)), .. members])], [], R("Run"));

    /// <summary>Two opened blocks: <c>RunA = rowA</c> under <paramref name="a"/>, <c>RunB = rowB</c> under <paramref name="b"/>, each with its own <c>G(x) = P</c>; output <c>RunA, RunB</c>.</summary>
    private static Expr OpenedTwo(ScopeCtx a, Expr rowA, ScopeCtx b, Expr rowB, Func<Property[]>? members = null)
        => Program(
            [OpenBlock(a, [], [Public("RunA", Body(rowA)), .. members?.Invoke() ?? [GReader()]]),
             OpenBlock(b, [], [Public("RunB", Body(rowB)), .. members?.Invoke() ?? [GReader()]])],
            [], R("RunA"), R("RunB"));

    /// <summary><c>P = x</c>: reads the parameter <c>x</c> it does not bind from its caller, so a cache hit returns the FIRST caller's <c>x</c>.</summary>
    private static Property PDyn() => Prop("P", Body(X("x")));
    /// <summary><c>public G(x) = P</c>.</summary>
    private static Property GReader() => Public("G", Fn(["x"], R("P")));

    /// <summary><c>F(*xs) = 7</c>: a callable that declares parameterized structure (an alias target).</summary>
    private static Property FCollecting()
        => Prop("F", new Algorithm.User(null, L<ParameterPattern>(new CaptureParameterPattern("xs", Kind: ParameterKind.Collecting)),
            L<Expr>(), L<Property>(), new OutputBundle([N(7)])));

    /// <summary>Opens <c>{ public FA = F }</c> under <paramref name="first"/> and <c>{ public FB = F }</c> under <paramref name="second"/> (static aliases); the root's <c>P(f, f) = 0</c> evaluates <c>P(FA, FB)</c>.</summary>
    private static Expr Need04(ScopeCtx first, ScopeCtx second)
    {
        static Property AliasF(string name) => Public(name, new Algorithm.Alias(null, L<Expr>(), L<Property>(), R("F")));
        return Program([OpenBlock(first, [], AliasF("FA")), OpenBlock(second, [], AliasF("FB"))],
            [Prop("P", Fn(["f", "f"], N(0)))], Call("P", R("FA"), R("FB")));
    }

    // ── Corpus ───────────────────────────────────────────────────────────────────────────────

    private static readonly Lazy<IReadOnlyList<HostParentCase>> s_cases = new(Build);

    /// <summary>Every case, in stable order. The graphs are built once and never mutated.</summary>
    public static IReadOnlyList<HostParentCase> AllCases() => s_cases.Value;

    private static ReadOnlyCollection<HostParentCase> Build()
    {
        var cases = new List<HostParentCase>();
        void Case(string id, string description, Expr program, params string[] watched)
            => cases.Add(new(id, description, program, L(watched)));
        void Divergent(string id, string description, Expr program, HostParentDivergence divergence, params string[] watched)
            => cases.Add(new(id, description, program, L(watched), divergence));

        // HP-01: a host parent's property read through an opened inline block — one declaring binding.
        Case("HP-01a", "host parent property read through an opened block", OpenedThrough(Scope(null, Prop("P", Body(N(7)))), [R("P")]), "P");
        Case("HP-01b", "three reads of one host property share ONE entry", OpenedThrough(Scope(null, Prop("P", Body(N(7)))), [Add(Add(R("P"), R("P")), R("P"))]), "P");
        Case("HP-01c", "a dynamically reading host property is cached once per run (first caller's x)",
            OpenedThrough(Scope(null, PDyn()), [Call("G", N(1)), Call("G", N(2))], GReader()), "P");
        Case("HP-01d", "a public host property is read by the block like a private one",
            OpenedThrough(Scope(null, Public("P", Body(N(3)))), [Mul(R("P"), N(2))]), "P");

        // HP-02: grandparent lookup and ownership-first resolution.
        {
            var grand = Scope(null, Prop("V", Body(N(1))));
            Case("HP-02a", "a grandparent host level is reached through its parent level",
                OpenedThrough(Scope(grand, Prop("W", Body(N(2)))), [Add(Mul(R("V"), N(10)), R("W"))]), "V", "W");
            Case("HP-02b", "the nearest declaring level wins (parent V shadows grandparent V)",
                OpenedThrough(Scope(Scope(null, Prop("V", Body(N(1)))), Prop("V", Body(N(2)))), [R("V")]), "V");
            Case("HP-02c", "a host level's own property beats its opened provider (ownership before opens)",
                OpenedThrough(ScopeOpening(null, [Block(Namespace(Public("V", Body(N(5)))))], Prop("V", Body(N(2)))), [R("V")]), "V");
            Case("HP-02d", "a grandparent's property beats the parent level's open (the whole owner walk first)",
                OpenedThrough(ScopeOpening(Scope(null, Prop("V", Body(N(1)))), [Block(Namespace(Public("V", Body(N(5)))))]), [R("V")]), "V");
            Case("HP-02e", "a name no level declares falls back to a host level's open provider",
                OpenedThrough(ScopeOpening(Scope(null, Prop("V", Body(N(1)))), [Block(Namespace(Public("U", Body(N(5)))))]), [Add(R("U"), R("V"))]), "U", "V");
            Case("HP-02f", "an undeclared name under a host chain is an unknown name",
                OpenedThrough(Scope(Scope(null, Prop("V", Body(N(1)))), Prop("W", Body(N(2)))), [R("Z")]));
        }

        // HP-03: public open member success, private refusal, structural dot access.
        {
            ScopeCtx Lib() => Scope(null, Prop("M", Namespace(Public("A", Body(N(1))), Prop("B", Body(N(2))))));
            Case("HP-03a", "a block opens a host-declared namespace and reads its PUBLIC member",
                Program([OpenBlock(Lib(), [R("M")], Public("Run", Body(R("A"))))], [], R("Run")), "A");
            Case("HP-03b", "a PRIVATE member is not open-provided (structured refusal)",
                Program([OpenBlock(Lib(), [R("M")], Public("Run", Body(R("B"))))], [], R("Run")));
            Case("HP-03c", "structural dot access selects the declared PRIVATE member of a host namespace",
                OpenedThrough(Lib(), [Add(Dot(R("M"), "B"), Dot(R("M"), "A"))]), "A", "B");
            Case("HP-03d", "a dotted open step through a private member is refused",
                Program([OpenBlock(Scope(null, Prop("M", Namespace(Prop("N", Namespace(Public("K", Body(N(4)))))))), [Dot(R("M"), "N")],
                    Public("Run", Body(R("K"))))], [], R("Run")));
            Case("HP-03e", "a dotted open step through a public member is open-provided",
                Program([OpenBlock(Scope(null, Prop("M", Namespace(Public("N", Namespace(Public("K", Body(N(4)))))))), [Dot(R("M"), "N")],
                    Public("Run", Body(R("K"))))], [], R("Run")), "K");
        }

        // HP-04: shadowing — a block-local property wins over host ancestors and opens.
        Case("HP-04a", "a block property shadows the host parent's property of the same name",
            OpenedThrough(Scope(null, Prop("V", Body(N(1)))), [R("V")], Prop("V", Body(N(3)))), "V");
        Case("HP-04b", "a block property shadows a host level's open provider",
            OpenedThrough(ScopeOpening(null, [Block(Namespace(Public("V", Body(N(9)))))]), [R("V")], Prop("V", Body(N(3)))), "V");
        Case("HP-04c", "a property of the reading body shadows both block and host declarations",
            Program([OpenBlock(Scope(null, Prop("V", Body(N(1)))), [], Public("Run", BodyWith([Prop("V", Body(N(4)))], R("V"))), Prop("V", Body(N(3))))], [], R("Run")),
            "V");

        // HP-05: ScopeCtx.Parameters and a local-only captured member.
        {
            ScopeCtx Captured() => new(null, L<Expr>(), L(Local("P", Body(X("x")), "x")), L("x"));
            Case("HP-05a", "an unactivated local-only host property keys on the ACCESS context: one entry per G call",
                OpenedThrough(Captured(), [Call("G", N(1)), Call("G", N(2))], GReader()), "P");
            Case("HP-05b", "two reads within ONE access context share the local-only entry",
                OpenedThrough(Captured(), [Call("G2", N(3))], Public("G2", Fn(["x"], Add(R("P"), R("P"))))), "P");
            Case("HP-05c", "a host level's Parameters take no part in property lookup (the name stays unknown)",
                OpenedThrough(new ScopeCtx(null, L<Expr>(), L<Property>(), L("x")), [R("x")]));

            // Accessibility (K1-08) of a local-only member whose required input `x` a HOST level
            // names in its Parameters (the nearest-owner walk stops there, at an unactivated level)
            // versus the same member with no level naming `x` (the walk finds no owner), through
            // structural dot access and through `open`, by name and by explicit owner depth.
            static ScopeCtx Requiring(bool hostNamesX, Property member)
                => new(null, L<Expr>(), L(Prop("M", Namespace(member))), hostNamesX ? L("x") : L<string>());
            static Property LocalL() => new("L", Body(X("x")), IsPublic: true, PropertyExposure.LocalOnlyCapturedAncestorParameters)
                { RequiredAncestorParameters = L("x") };
            static Property DepthL() => LocalL() with { CaptureRequirements = L(new CapturedParameterRequirement("x", 1)) };
            foreach (var (suffix, hostNamesX, member, description) in new[]
            {
                ("d", true, (Func<Property>)LocalL, "named by the host level's Parameters"),
                ("e", false, (Func<Property>)LocalL, "named by no level"),
                ("f", true, (Func<Property>)DepthL, "required at owner depth 1, the host level naming it"),
                ("g", false, (Func<Property>)DepthL, "required at owner depth 1, the host level NOT naming it"),
            })
            {
                Case($"HP-05{suffix}", $"structural access M.L to a local-only member whose input x is {description}",
                    OpenedThrough(Requiring(hostNamesX, member()), [Call("G", N(1))], Public("G", Fn(["x"], Dot(R("M"), "L")))));
            }

            Case("HP-05h", "open access to a local-only member whose input x is named by the host level's Parameters",
                Program([OpenBlock(Requiring(true, LocalL()), [R("M")], Public("Run", Body(Call("G", N(1)))), Public("G", Fn(["x"], R("L"))))], [], R("Run")));
            Case("HP-05i", "open access to a local-only member whose input x is named by no level",
                Program([OpenBlock(Requiring(false, LocalL()), [R("M")], Public("Run", Body(Call("G", N(1)))), Public("G", Fn(["x"], R("L"))))], [], R("Run")));
        }

        // HP-06: repeated reads, P() then P — Q-37 / CACHE-PUB-1 key agreement.
        {
            Case("HP-06a", "CACHE-PUB-1: H(x) = P() establishes the empty entry; the later read reuses it",
                OpenedThrough(Scope(null, PDyn()), [Call("H", N(1)), Call("G", N(2))], Public("H", Fn(["x"], Call("P"))), GReader()), "P");
            Case("HP-06b", "an established entry is never replaced by a later fresh P()",
                OpenedThrough(Scope(null, PDyn()), [Call("G", N(1)), Call("H", N(2)), Call("G", N(3))], Public("H", Fn(["x"], Call("P"))), GReader()), "P");
            // Q-37 through a host binding: P = K(x); K(0) = 1; K(n) = G(n - 1) + 100; G(x) = P. G(1)'s
            // read owns P's key, the nested G(0) read is re-entrant (1, unpublished), the owner
            // publishes 101, which G(5) reuses.
            var family = new Algorithm.Conditional(null, L<Expr>(), L(
                new CondBranch(new Pattern.LitInt(0), Body(N(1))),
                new CondBranch(new Pattern.Bind("n"), Body(Add(Call("G", Sub(X("n"), N(1))), N(100))))));
            ScopeCtx Recursive() => Scope(null, Prop("P", Body(Call("K", X("x")))), Prop("K", family), GReader());
            Case("HP-06c", "Q-37: the outermost read owns the entry, the re-entrant read publishes nothing",
                OpenedThrough(Recursive(), [Call("G", N(1)), Call("G", N(5))]), "P");
            Case("HP-06d", "Q-37 with the owning access an explicit P() (CACHE-PUB-1)",
                OpenedThrough(Recursive(), [Call("H", N(1)), Call("G", N(5))], Public("H", Fn(["x"], Call("P")))), "P");
        }

        // HP-07: activation-local results of two independent enclosing calls (D1/D2 controls).
        {
            ScopeCtx Activations() => Scope(null, Public("F", FnWith(["x"],
                [Local("L", Body(Mul(X("x"), N(10))), "x"), Local("M", Body(Add(R("L"), N(1))), "x")], R("M"))));
            Case("HP-07a", "two calls of a host-declared F keep their own local-only L and M entries",
                OpenedThrough(Activations(), [Call("F", N(1)), Call("F", N(2))]), "L", "M");
            Case("HP-07b", "repeated calls with one argument still bind fresh activations (D2)",
                OpenedThrough(Activations(), [Add(Call("F", N(1)), Call("F", N(1)))]), "L", "M");
        }

        // HP-08: separately created host levels never alias, however their content is shared.
        {
            Case("HP-08a", "two fresh equal host levels, each with its own P: two owners",
                OpenedTwo(Scope(null, PDyn()), Call("G", N(1)), Scope(null, PDyn()), Call("G", N(2))), "P");
            var shared = PDyn();
            Case("HP-08b", "ONE Property object declared by two distinct host levels: two owners (former 5b shape)",
                OpenedTwo(Scope(null, shared), Call("G", N(1)), Scope(null, shared), Call("G", N(2))), "P");
            var list = L(PDyn());
            Case("HP-08c", "two distinct host levels sharing ONE property list: two owners",
                OpenedTwo(new ScopeCtx(null, L<Expr>(), list), Call("G", N(1)), new ScopeCtx(null, L<Expr>(), list), Call("G", N(2))), "P");
            var original = Scope(null, PDyn());
            Case("HP-08d", "a record `with` copy of a host level is another owner",
                OpenedTwo(original, Call("G", N(1)), original with { }, Call("G", N(2))), "P");
            var grand = Scope(null, PDyn());
            Case("HP-08e", "distinct parent objects over record-equal grandparents (copies) keep two owners",
                OpenedTwo(Scope(grand), Call("G", N(1)), Scope(grand with { }), Call("G", N(2))), "P");
            Case("HP-08f", "two distinct host levels with distinct declarations of different values",
                OpenedTwo(Scope(null, Prop("P", Body(N(10)))), Call("G", N(1)), Scope(null, Prop("P", Body(N(20)))), Call("G", N(2))), "P");

            // NEED-04 beyond the cache (O6-17): P(f, f) = 0 binds ONE callable, so P(FA, FB) over the
            // aliases FA/FB of a host-declared F(*xs) accepts only when both reach ONE host declaring
            // scope; distinct host objects are distinct callables whatever their content.
            var fShared = FCollecting();
            var fList = L(FCollecting());
            var fOriginal = Scope(null, FCollecting());
            Case("HP-08g", "NEED-04: F from two fresh equal host levels is two callables", Need04(Scope(null, FCollecting()), Scope(null, FCollecting())));
            Case("HP-08h", "NEED-04: one F Property in two distinct host levels is two callables", Need04(Scope(null, fShared), Scope(null, fShared)));
            Case("HP-08i", "NEED-04: one property list in two distinct host levels is two callables",
                Need04(new ScopeCtx(null, L<Expr>(), fList), new ScopeCtx(null, L<Expr>(), fList)));
            Case("HP-08j", "NEED-04: a record `with` copy of the host level is another callable scope", Need04(fOriginal, fOriginal with { }));

            // O6-10: ONE property list declared by an ownerless host level AND by an evaluator-owned
            // open block. RunA reads G (and so P) through the host level; the root's G(2) reaches the
            // owned block's G. Two declaring owners, two entries.
            var both = L(PDyn(), GReader());
            Case("HP-08k", "a host level and an evaluator-owned block declaring ONE property list are two owners",
                Program([OpenBlock(new ScopeCtx(null, L<Expr>(), both), [], Public("RunA", Body(Call("G", N(1))))),
                         Block(new Algorithm.User(null, L<ParameterPattern>(), L<Expr>(), both, OutputBundle.Empty))],
                    [], R("RunA"), Call("G", N(2))), "P");
        }

        // HP-09: the SAME host level object opened from two places is one owner.
        {
            var same = Scope(null, PDyn());
            Case("HP-09a", "one host level object opened by two blocks: one owner, one entry",
                OpenedTwo(same, Call("G", N(1)), same, Call("G", N(2))), "P");
            var grand = Scope(null, PDyn());
            Case("HP-09b", "one grandparent object reached through two distinct children: one owner",
                OpenedTwo(Scope(grand, Prop("W", Body(N(1)))), Call("G", N(1)), Scope(grand, Prop("W", Body(N(2)))), Call("G", N(2))), "P");
            var block = OpenBlock(Scope(null, PDyn()), [], Public("Run", Body(Call("G", N(1)), Call("G", N(2)))), GReader());
            Case("HP-09c", "one opened block object listed twice in one open list is one provider",
                Program([block, block], [], R("Run")), "P");
            var one = Scope(null, FCollecting());
            Case("HP-09d", "NEED-04: F reached through ONE host level object twice is one callable", Need04(one, one));
        }

        // HP-10: nested parents, nested open providers, structural/dot lookup.
        {
            var lib = Scope(null, Prop("Lib", Namespace(Public("N", Namespace(Public("K", Body(N(4))))))));
            Case("HP-10a", "a block opens a dotted path into a host-declared namespace",
                Program([OpenBlock(lib, [Dot(R("Lib"), "N")], Public("Run", Body(R("K"))))], [], R("Run")), "K");
            var inner = OpenBlock(Scope(null, Prop("Z", Body(N(5)))), [], Public("Z2", Body(Add(R("Z"), N(1)))));
            Case("HP-10b", "a block's own open target is another block with ITS OWN pre-wired parent",
                Program([OpenBlock(Scope(null, Prop("Y", Body(N(100)))), [inner], Public("Run", Body(Add(R("Z2"), R("Y")))))], [], R("Run")), "Z", "Z2", "Y");
            Case("HP-10c", "structural member access into a host-declared object",
                OpenedThrough(Scope(null, Prop("Obj", Namespace(Public("A", Body(N(2))), Prop("B", Body(N(3)))))), [Add(Dot(R("Obj"), "A"), Dot(R("Obj"), "B"))]), "A", "B");
            Case("HP-10d", "a host level's own open target supplies a name to the block",
                OpenedThrough(ScopeOpening(null, [Block(Namespace(Public("Q", Body(N(8)))))]), [R("Q")]), "Q");
            Case("HP-10e", "a member of a member through a two-level host chain",
                OpenedThrough(Scope(Scope(null, Prop("Outer", Namespace(Public("Mid", Namespace(Public("Leaf", Body(N(6)))))))), Prop("W", Body(N(1)))),
                    [Add(Dot(Dot(R("Outer"), "Mid"), "Leaf"), R("W"))]), "Leaf", "W");
            Expr diamond = N(1);
            for (var i = 0; i < 12; i++) diamond = Add(diamond, diamond);
            Case("HP-10f", "a shared expression diamond in a host parent uses compact Lean let terms",
                OpenedThrough(Scope(null, Prop("P", Body(diamond))), [R("P")]), "P");
            // The large shared body activates compact printing. The SAME dynamic P body in two
            // scopes must still resolve/cache under each context; term sharing cannot merge owners.
            var dynamic = PDyn();
            var unused = Prop("Large", Body(diamond));
            Case("HP-10g", "compact terms keep the declaring contexts of shared host properties distinct",
                OpenedTwo(Scope(null, dynamic, unused), Call("G", N(1)),
                    Scope(null, dynamic, unused), Call("G", N(2))), "P", "Large");
            Expr spreadSpine = N(1);
            Expr joinSpine = N(1);
            for (var i = 0; i <= EvaluationLimits.MaxSupportedAstDepth; i++)
            {
                spreadSpine = new Expr.SequenceSpread(spreadSpine);
                joinSpine = new Expr.SequenceConstruct(joinSpine, new Expr.EmptySequence(0));
            }
            Case("HP-10h", "an evaluator-accepted spread spine beyond recursive depth uses iterative compact printing",
                OpenedThrough(Scope(null, Prop("P", Body(spreadSpine))), [R("P")]), "P");
            Case("HP-10i", "an evaluator-accepted join spine preserves the non-spread empty-leaf rule",
                OpenedThrough(Scope(null, Prop("P", Body(joinSpine))), [R("P")]), "P");
        }

        // HP-11: host-built static aliases and alias chains resolve in their DECLARING namespace.
        {
            static Property Inc(int delta) => Prop("Inc", Fn(["x"], Add(X("x"), N(delta))));
            static Property AliasOf(string name, string target) => Prop(name, new Algorithm.Alias(null, L<Expr>(), L<Property>(), R(target)));
            Case("HP-11a", "a host-declared static alias calls its target", OpenedThrough(Scope(null, Inc(1), AliasOf("A", "Inc")), [Call("A", N(5))]));
            Case("HP-11b", "a host alias chain B -> A -> Inc", OpenedThrough(Scope(null, Inc(1), AliasOf("A", "Inc"), AliasOf("B", "A")), [Call("B", N(5))]));
            Case("HP-11c", "a host alias resolves its target in the HOST scope, never the block's shadowing Inc",
                OpenedThrough(Scope(null, Inc(1), AliasOf("A", "Inc")), [Add(Call("A", N(5)), Call("Inc", N(5)))], Inc(100)));
            Case("HP-11d", "a block alias over a host-declared target", OpenedThrough(Scope(null, Inc(1)), [Call("A2", N(5))], AliasOf("A2", "Inc")));
            Case("HP-11e", "an alias in a grandparent level through a member path", OpenedThrough(
                Scope(Scope(null, Prop("M", Namespace(Public("Twice", Fn(["x"], Mul(X("x"), N(2))))))), Prop("T", new Algorithm.Alias(null, L<Expr>(), L<Property>(), Dot(R("M"), "Twice")))),
                [Call("T", N(21))]));
        }

        // HP-12: runtime callable-projection aliases `A = R.Algorithm` declared in a host parent.
        {
            static Property[] Members(bool parameterized) =>
            [
                Prop("F", parameterized ? Fn(["v"], Add(X("v"), N(1))) : Body(N(7))),
                Prop("Capture", new Algorithm.User(null, L<ParameterPattern>(new CaptureParameterPattern("op", Kind: ParameterKind.Meta)), L<Expr>(), L<Property>(), new OutputBundle([X("op")]))),
                Prop("R", Body(parameterized ? Call("Capture", Call("F", N(1))) : Call("Capture", Call("F")))),
                Prop("A", new Algorithm.Alias(null, L<Expr>(), L<Property>(), Dot(R("R"), "Algorithm")) { HasRuntimeTarget = true }),
            ];
            Case("HP-12a", "D4 terminal fallback: a zero-parameter target keeps ordinary-property semantics (A, A(), A, A())",
                OpenedThrough(Scope(null, Members(parameterized: false)), [R("A"), Call("A"), R("A"), Call("A")]), "A", "R", "F");
            Case("HP-12b", "D3 parameterized forwarding: A(args) is a fresh call of the projected F",
                OpenedThrough(Scope(null, Members(parameterized: true)), [Call("A", N(5)), Call("A", N(10))]), "A", "R");
            var list = L(Members(parameterized: false));
            var one = new ScopeCtx(null, L<Expr>(), list);
            Case("HP-12c", "one host object opened twice shares the alias's declaring namespace (HOST-ALIAS-R14)",
                OpenedTwo(one, R("A"), one, Call("A"), static () => []), "A", "R", "F");
            Case("HP-12d", "record-equal host objects sharing the member list keep one namespace each (HOST-ALIAS-R14)",
                OpenedTwo(one, R("A"), new ScopeCtx(null, L<Expr>(), list), Call("A"), static () => []), "A", "R", "F");
        }

        // HP-13: user / conditional / alias algorithms carrying pre-wired parents on every route.
        {
            var decoy = Scope(null, Prop("V", Body(N(99))), Prop("Inc", Fn(["x"], Add(X("x"), N(100)))));
            var host = Scope(null, Prop("V", Body(N(1))), Prop("Inc", Fn(["x"], Add(X("x"), N(1)))));
            var family = new Algorithm.Conditional(decoy, L<Expr>(), L(new CondBranch(new Pattern.LitInt(0), Body(R("V"))),
                new CondBranch(new Pattern.Bind("n"), Body(Add(X("n"), R("V"))))));
            Case("HP-13a", "a host property whose CONDITIONAL value carries its own parent: lookup wiring replaces it",
                OpenedThrough(new ScopeCtx(null, L<Expr>(), L([.. host.Properties, Prop("K", family)])), [Call("K", N(0)), Call("K", N(5))]), "V");
            var alias = new Algorithm.Alias(decoy, L<Expr>(), L<Property>(), R("Inc"));
            Case("HP-13b", "a host property whose ALIAS value carries its own parent: lookup wiring replaces it",
                OpenedThrough(new ScopeCtx(null, L<Expr>(), L([.. host.Properties, Prop("A", alias)])), [Call("A", N(1))]));
            Case("HP-13c", "a pre-wired CONDITIONAL as an open target is refused when a lookup reaches it",
                Program([Block(new Algorithm.Conditional(host, L<Expr>(), L(new CondBranch(new Pattern.LitInt(0), Body(N(1))))))], [], R("Z")));
            Case("HP-13d", "a pre-wired ALIAS as an open target is refused when a lookup reaches it",
                Program([Block(new Algorithm.Alias(host, L<Expr>(), L<Property>(), R("Inc")))], [], R("Z")));
            Case("HP-13e", "a pre-wired PROGRAM ROOT is wired under the prelude: its host parent is replaced",
                Block(new Algorithm.User(host, L<ParameterPattern>(), L<Expr>(), L<Property>(), new OutputBundle([R("V")]))));
            Case("HP-13f", "a pre-wired inline block in VALUE position is wired to its caller",
                OpenedThrough(host, [Block(new Algorithm.User(decoy, L<ParameterPattern>(), L<Expr>(), L<Property>(), new OutputBundle([R("V")])))]), "V");
            Case("HP-13g", "a pre-wired inline CALLEE is wired to its caller",
                OpenedThrough(host, [Call(Block(new Algorithm.User(decoy, L<ParameterPattern>(new CaptureParameterPattern("y")), L<Expr>(), L<Property>(),
                    new OutputBundle([Add(X("y"), R("V"))]))), N(3))]), "V");
            Case("HP-13h", "a pre-wired inline CONDITIONAL callee is wired to its caller",
                OpenedThrough(host, [Call(Block(family), N(0))]), "V");
            Case("HP-13i", "a pre-wired inline ALIAS callee resolves its target from the caller",
                OpenedThrough(host, [Call(Block(alias), N(2))]));
            Case("HP-13j", "a pre-wired property value of the BLOCK itself is replaced by the block's wiring",
                OpenedThrough(host, [R("U")], Prop("U", new Algorithm.User(decoy, L<ParameterPattern>(), L<Expr>(), L<Property>(), new OutputBundle([R("V")])))), "U", "V");
            Case("HP-13k", "a structural receiver block with a pre-wired parent is wired to its caller",
                OpenedThrough(host, [Dot(Block(new Algorithm.User(decoy, L<ParameterPattern>(), L<Expr>(), L(Public("W", Body(R("V")))), OutputBundle.Empty)), "W")]), "W", "V");
            var module = new Algorithm.User(decoy, L<ParameterPattern>(), L<Expr>(),
                L(Public("Run", Body(R("V")))), OutputBundle.Empty) { IsModuleElaborated = true };
            Case("HP-13l", "an explicitly wired module open preserves its host root instead of taking the caller's V",
                Program([Block(module)], [Prop("V", Body(N(1)))], R("Run")));
            var preludeModule = new Algorithm.User(Scope(null, Prop("count", Fn(["x"], N(99)))),
                L<ParameterPattern>(), L<Expr>(), L<Property>(), new OutputBundle([Call("count", new Expr.ListLiteral([]))]))
                { IsModuleElaborated = true };
            Case("HP-13m", "a module property roots at the supplied host chain, which has no implicit prelude count",
                OpenedThrough(Scope(null, Prop("M", preludeModule)), [R("M")]), "M");
        }

        // HP-14: the residual HOST-LEAN-O6 shapes. Comparable controls first, then the two known
        // divergences, which are excluded from the comparable partition and pinned on BOTH sides.
        {
            var member = Public("F", Body(N(7)));
            var provider = new Algorithm.User(Scope(null), L<ParameterPattern>(), L<Expr>(), L(member), OutputBundle.Empty);
            var empty = Scope(null);
            Case("HP-14a", "control: one declaration opened twice under ONE empty host level object is one provider",
                Program([Block(provider with { Parent = empty }), Block(provider with { Parent = empty })], [], R("F")), "F");
            Divergent("HP-14b", "one declaration opened twice under two DISTINCT empty host level objects",
                Program([Block(provider with { Parent = Scope(null) }), Block(provider with { Parent = Scope(null) })], [], R("F")),
                new HostParentDivergence(
                    "HOST-LEAN-O6 O6-18 (Q-19 open-provider identity over EMPTY host levels): C# compares host levels by object " +
                    "reference, Lean by content, and an empty level has no PropDef to carry a per-object identity; a faithful " +
                    "encoding needs a Lean host-level token (deferred design E, owner decision OD-1).",
                    CSharpNeutral: "err ambiguousOpen",
                    LeanNeutral: "ok raw=7 n=1"));

            // O6-11x: an evaluator-owned Q nested under two record-equal host levels sharing ONE list.
            static Property[] Nested() => [Prop("S", Body(X("x"))), Prop("P", Namespace(Public("Q", Body(R("S")))))];
            static Property[] Reader() => [Public("G", Fn(["x"], R("S"), Dot(R("P"), "Q")))];
            Case("HP-14c", "control: fresh host levels with their own nested declarations keep (S, P.Q) per level",
                OpenedTwo(Scope(null, Nested()), Call("G", N(1)), Scope(null, Nested()), Call("G", N(2)), Reader), "S", "Q");
            var sharedList = L(Nested());
            Divergent("HP-14d", "an owned Q nested under two record-equal host levels that share ONE property list",
                OpenedTwo(new ScopeCtx(null, L<Expr>(), sharedList), Call("G", N(1)), new ScopeCtx(null, L<Expr>(), sharedList), Call("G", N(2)), Reader),
                new HostParentDivergence(
                    "HOST-LEAN-O6 O6-11x (C# pass-through policy): C# keys the host DECLARING level by reference but a host level " +
                    "PASSED THROUGH by structure, so the second level's P.Q reuses the first level's entry; the per-object encoding " +
                    "keeps Lean's two levels distinct. Which policy is the contract awaits owner decision OD-1.",
                    CSharpNeutral: "ok raw=S[S[1, 1], S[2, 1]] n=2",
                    LeanNeutral: "ok raw=S[S[1, 1], S[2, 2]] n=2"),
                "S", "Q");
        }

        return cases.AsReadOnly();
    }
}
