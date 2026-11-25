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
/// compared (C# published entries per binding name vs Lean <c>zeroArgPropertyCache</c> entries), on
/// success and failure alike (KL-06).</param>
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

    /// <summary>The expected number of executed ticks when the case also pins effects.</summary>
    public int? ExpectedTickCount { get; init; }
}

/// <summary>
/// A reviewed, machine-checked model divergence: the exact C# neutral observation, the exact Lean
/// neutral observation of the encoded program, and the named reason (an owner-level decision, not
/// an encoder gap). Both observations are hand-reviewed constants, never regenerated from a run.
/// </summary>
public sealed record HostParentDivergence(string Reason, string CSharpNeutral, string LeanNeutral);

/// <summary>
/// The host-parent differential corpus: the HP-01..HP-14 matrix of HOST-DIFF-1 (and DECON-CACHE-2's HP-15,
/// KL-06's failed-run publications HP-16, KL-07's neutral-text collision HP-17, EXPORTED-DETACHED's HP-18
/// and R-1's retained runtime-alias cells HP-19, with their open qualification HP-20) plus the discovered
/// shapes (record-equal / shared / reused host objects, parent-replacing wiring routes, alias and
/// family variants). Pure, Lean-representable ASTs only: no host operations, integer numbers.
/// A raw host chain has no implicit prelude level; the module controls pin this boundary too.
/// </summary>
public static class HostParentDifferentialCorpus
{
    internal const string EscapedAliasCall = """
        Cap(meta r) = r
        Inc(x) = x + 1
        Dbl(x) = x * 2
        Sel(k) = if(k + tick() == 2, Cap(Inc(0)), Cap(Dbl(0)))
        F(y) = {
          A = Sel(y).Algorithm
          P = [A(5)]
          P[0]
        }
        F(1)
        """;

    // ── AST vocabulary ───────────────────────────────────────────────────────────────────────

    private static ReadOnlyCollection<T> L<T>(params T[] items) => Array.AsReadOnly(items);
    private static Expr R(string name) => new Expr.Resolve(name);
    private static Expr X(string name) => new Expr.Param(name);
    private static Expr N(int value) => new Expr.Num(value);
    /// <summary>A HOST-BUILT string literal: unlike a source literal, it may hold the quote character.</summary>
    private static Expr Str(string value) => new Expr.StringLiteral(value);
    private static Expr ListOf(params Expr[] items) => new Expr.ListLiteral(new OutputBundle(items));
    private static Expr Add(Expr a, Expr b) => new Expr.Binary(BinaryOp.Add, a, b);
    private static Expr Sub(Expr a, Expr b) => new Expr.Binary(BinaryOp.Sub, a, b);
    private static Expr Mul(Expr a, Expr b) => new Expr.Binary(BinaryOp.Mul, a, b);
    private static Expr Div(Expr a, Expr b) => new Expr.Binary(BinaryOp.Div, a, b);
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

    /// <summary>
    /// <c>tick()</c>, called as the builtin itself: a raw host chain has no prelude level, so no name
    /// reaches it. The one inline builtin <see cref="LeanAstEncoder"/> encodes.
    /// </summary>
    private static Expr Tick() => Call(Block(new Algorithm.Builtin(BuiltinId.tick)));

    /// <summary>
    /// <c>P = tick()</c>: THE EVALUATION WITNESS. Each evaluation of <c>P</c> returns the run's next
    /// tick, so a cache hit returns the first evaluation's <c>1</c> and a second owner returns
    /// <c>2</c>: the values say how many owners a run has. <c>P</c> is self-contained, as an exported
    /// property must be. (Until EXPORTED-DETACHED, November 2026, the witness was <c>P = x</c>, read
    /// dynamically from whichever caller came first; an exported property is now evaluated DETACHED and
    /// that read is refused — HP-18a. The readers' arguments 1 and 2 used to BE those values, so the
    /// reviewed observations are the same wherever the rows are <c>G(1), G(2)</c>.)
    /// </summary>
    private static Property PDyn() => Prop("P", Body(Tick()));
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

    /// <summary>
    /// A parsed program with each property named by a dotted declaration path (<c>"F.P"</c>) forced to
    /// <see cref="PropertyExposure.Exported"/>: the tree a wrong exposure analysis, or a host, would hand the
    /// evaluators. The front end's own verdict on it must be local-only.
    /// </summary>
    private static Expr MisExposedSource(string source, params string[] paths)
    {
        Algorithm root = SourceProvenance.ParseValid(source).Root;
        foreach (var path in paths)
            root = ExportedAt(root, path.Split('.'), 0);
        return new Expr.AlgorithmExpr(root);
    }

    private static Algorithm ExportedAt(Algorithm algorithm, string[] path, int depth)
    {
        var owner = (Algorithm.User)algorithm;
        var properties = owner.Properties.ToList();
        var index = properties.FindIndex(property => property.Name == path[depth]);
        var selected = properties[index];
        properties[index] = depth < path.Length - 1
            ? selected with { Value = ExportedAt(selected.Value, path, depth + 1) }
            : selected.Exposure == PropertyExposure.LocalOnlyCapturedAncestorParameters
                ? selected with { Exposure = PropertyExposure.Exported, RequiredAncestorParameters = [], CaptureRequirements = null }
                : throw new InvalidOperationException($"{string.Join('.', path)} is not local-only");
        return owner with { Properties = properties };
    }

    // ── Corpus ───────────────────────────────────────────────────────────────────────────────

    private static readonly Lazy<IReadOnlyList<HostParentCase>> s_cases = new(Build);

    /// <summary>Every case, in stable order. The graphs are built once and never mutated.</summary>
    public static IReadOnlyList<HostParentCase> AllCases() => s_cases.Value;

    private static ReadOnlyCollection<HostParentCase> Build()
    {
        var cases = new List<HostParentCase>();
        // Every case is comparable since HOST-LEAN-O6. A future reviewed model divergence is added with its
        // HostParentDivergence (`cases.Add(new(id, description, program, watched, divergence))`) and named in
        // HostParentDifferentialTests' exact partition guard.
        void Case(string id, string description, Expr program, params string[] watched)
            => cases.Add(new(id, description, program, L(watched)));

        // HP-01: a host parent's property read through an opened inline block — one declaring binding.
        Case("HP-01a", "host parent property read through an opened block", OpenedThrough(Scope(null, Prop("P", Body(N(7)))), [R("P")]), "P");
        Case("HP-01b", "three reads of one host property share ONE entry", OpenedThrough(Scope(null, Prop("P", Body(N(7)))), [Add(Add(R("P"), R("P")), R("P"))]), "P");
        Case("HP-01c", "an exported host property is evaluated once per run (both readers get the first evaluation)",
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
            ScopeCtx Captured() => new(null, L<Expr>(), L(Local("P", Body(Tick()), "x")), L("x"));
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

            // KL-04: ABSENT exact-owner metadata versus an explicitly EMPTY list on one member that names
            // an input no level binds. Absent, access falls back to the names' nearest owners and is
            // refused; an empty list requires no owner and accepts. The encoding must keep them apart.
            static Property Unowned(IReadOnlyList<CapturedParameterRequirement>? owners)
                => new("L", Body(N(7)), IsPublic: true, PropertyExposure.LocalOnlyCapturedAncestorParameters)
                    { RequiredAncestorParameters = L("absent"), CaptureRequirements = owners };
            Case("HP-05j", "structural access Box.L to a local-only member naming an unbound input, exact owners ABSENT",
                Program([], [Prop("Box", Namespace(Unowned(null)))], Dot(R("Box"), "L")));
            Case("HP-05k", "structural access Box.L to a local-only member naming an unbound input, exact owners EMPTY",
                Program([], [Prop("Box", Namespace(Unowned(L<CapturedParameterRequirement>())))], Dot(R("Box"), "L")));
        }

        // HP-06: repeated reads, P() then P — Q-37 / CACHE-PUB-1 key agreement.
        {
            Case("HP-06a", "CACHE-PUB-1: H(x) = P() establishes the empty entry; the later read reuses it",
                OpenedThrough(Scope(null, PDyn()), [Call("H", N(1)), Call("G", N(2))], Public("H", Fn(["x"], Call("P"))), GReader()), "P");
            Case("HP-06b", "an established entry is never replaced by a later fresh P()",
                OpenedThrough(Scope(null, PDyn()), [Call("G", N(1)), Call("H", N(2)), Call("G", N(3))], Public("H", Fn(["x"], Call("P"))), GReader()), "P");
            // Q-37 through a host binding: P = K(tick()); K(1) = G(0) + 100; K(n) = 1; G(x) = P. G(1)'s
            // read owns P's key (tick 1), the nested G(0) read is re-entrant (tick 2: 1, unpublished),
            // the owner publishes 101, which G(5) reuses.
            var family = new Algorithm.Conditional(null, L<Expr>(), L(
                new CondBranch(new Pattern.LitInt(1), Body(Add(Call("G", N(0)), N(100)))),
                new CondBranch(new Pattern.Bind("n"), Body(N(1)))));
            ScopeCtx Recursive() => Scope(null, Prop("P", Body(Call("K", Tick()))), Prop("K", family), GReader());
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
            // The large shared body activates compact printing. The SAME witness P body in two
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

        // HP-14: the HOST-LEAN-O6 shapes. HP-14b was the one known divergence (O6-18: an EMPTY host level has
        // no declaration to carry a per-object identity) until HOST-LEAN-O6 gave every host level its object's
        // Lean host-scope token; HP-14d was one until HOST-NESTED-1 (OD-1(a)) made C# key host ANCESTORS by
        // reference too. Both are ordinary comparable cases now.
        {
            var member = Public("F", Body(N(7)));
            var provider = new Algorithm.User(Scope(null), L<ParameterPattern>(), L<Expr>(), L(member), OutputBundle.Empty);
            var empty = Scope(null);
            Case("HP-14a", "control: one declaration opened twice under ONE empty host level object is one provider",
                Program([Block(provider with { Parent = empty }), Block(provider with { Parent = empty })], [], R("F")), "F");
            Case("HP-14b", "Q-19: one declaration opened twice under two DISTINCT empty host level objects is two providers",
                Program([Block(provider with { Parent = Scope(null) }), Block(provider with { Parent = Scope(null) })], [], R("F")), "F");

            // O6-11x: an evaluator-owned Q nested under two record-equal host levels sharing ONE list.
            static Property[] Nested() => [Prop("S", Body(Tick())), Prop("P", Namespace(Public("Q", Body(R("S")))))];
            static Property[] Reader() => [Public("G", Fn(["x"], R("S"), Dot(R("P"), "Q")))];
            Case("HP-14c", "control: fresh host levels with their own nested declarations keep (S, P.Q) per level",
                OpenedTwo(Scope(null, Nested()), Call("G", N(1)), Scope(null, Nested()), Call("G", N(2)), Reader), "S", "Q");
            // HOST-NESTED-1: C# formerly keyed this passed-through host level structurally and observed
            // S[S[1, 1], S[2, 1]]; with every host ancestor keyed by reference it agrees with the
            // per-object encoding.
            var sharedList = L(Nested());
            Case("HP-14d", "an owned Q nested under two record-equal host levels that share ONE property list keeps (S, P.Q) per level",
                OpenedTwo(new ScopeCtx(null, L<Expr>(), sharedList), Call("G", N(1)), new ScopeCtx(null, L<Expr>(), sharedList), Call("G", N(2)), Reader),
                "S", "Q");

            // HOST-LEAN-O6: identity that ONLY an empty host ANCESTOR distinguishes. One evaluator-owned
            // declaration (`with` copies of one block) is pre-wired under two empty host levels, each opened
            // by its own wrapper namespace (so no name is ambiguous). The owners, callables and alias cells
            // under the two levels differ only in that ancestor's object identity — no property, list or
            // declaration tells them apart in C#. The encoder also qualifies owned property ids by
            // host ancestry; the direct Lean guards isolate omission of the ancestor token itself.
            static Expr Wrapper(Algorithm.User block, ScopeCtx parent, params Property[] members)
                => Block(new Algorithm.User(null, L<ParameterPattern>(), L(Block(block with { Parent = parent })), L(members), OutputBundle.Empty));
            var dynamicBlock = Namespace(PDyn(), GReader());
            Expr Cache(ScopeCtx first, ScopeCtx second)
                => Program([Wrapper(dynamicBlock, first, Public("RunA", Body(Call("G", N(1))))),
                            Wrapper(dynamicBlock, second, Public("RunB", Body(Call("G", N(2)))))], [], R("RunA"), R("RunB"));
            Case("HP-14e", "an owned P under two DISTINCT empty host ancestors is two cache owners (one evaluation per owner)",
                Cache(Scope(null), Scope(null)), "P");
            var oneEmpty = Scope(null);
            Case("HP-14f", "control: the owned P under ONE empty host ancestor object reached twice is one cache owner",
                Cache(oneEmpty, oneEmpty), "P");

            var callableBlock = Namespace(FCollecting() with { IsPublic = true });
            static Property AliasTo(string name, string target) => Public(name, new Algorithm.Alias(null, L<Expr>(), L<Property>(), R(target)));
            Expr Need04Ancestors(ScopeCtx first, ScopeCtx second)
                => Program([Wrapper(callableBlock, first, AliasTo("FA", "F")), Wrapper(callableBlock, second, AliasTo("FB", "F"))],
                    [Prop("P", Fn(["f", "f"], N(0)))], Call("P", R("FA"), R("FB")));
            Case("HP-14g", "NEED-04: one F declaration under two DISTINCT empty host ancestors is two callables",
                Need04Ancestors(Scope(null), Scope(null)));
            Case("HP-14h", "NEED-04 control: one F declaration under ONE empty host ancestor object is one callable",
                Need04Ancestors(oneEmpty, oneEmpty));

            // A runtime alias `A = R.Algorithm` projects F through its BINDING CELL, keyed by the alias's
            // declaring chain. Distinct empty ancestors keep two cells, so FA and FB project two callables
            // (NEED-04 refuses P(FA, FB)); a cell shared across the two ancestors would project the first
            // ancestor's F twice and accept.
            var projectingBlock = Namespace(
                Prop("F", Fn(["v"], Add(X("v"), N(1)))),
                Prop("Capture", new Algorithm.User(null, L<ParameterPattern>(new CaptureParameterPattern("op", Kind: ParameterKind.Meta)), L<Expr>(), L<Property>(), new OutputBundle([X("op")]))),
                Prop("R", Body(Call("Capture", Call("F", N(1))))),
                Public("A", new Algorithm.Alias(null, L<Expr>(), L<Property>(), Dot(R("R"), "Algorithm")) { HasRuntimeTarget = true }));
            Expr AliasAncestors(ScopeCtx first, ScopeCtx second)
                => Program([Wrapper(projectingBlock, first, AliasTo("FA", "A")), Wrapper(projectingBlock, second, AliasTo("FB", "A"))],
                    [Prop("P", Fn(["f", "f"], N(0)))], Call("P", R("FA"), R("FB")));
            Case("HP-14i", "runtime alias cells under two DISTINCT empty host ancestors project two callables (NEED-04 refuses)",
                AliasAncestors(Scope(null), Scope(null)));
            Case("HP-14j", "control: runtime alias cells under ONE empty host ancestor object project one callable",
                AliasAncestors(oneEmpty, oneEmpty));

            // One evaluator-owned declaration can have several host-built views. C# compares each
            // nonempty opens/property list by reference, and separately allocated empty lists as
            // equivalent. Neither equal printed lists nor a shared declaration can replace that fact.
            Expr Need04Views(Algorithm.User first, Algorithm.User second)
                => Program([Wrapper(first, oneEmpty, AliasTo("FA", "F")), Wrapper(second, oneEmpty, AliasTo("FB", "F"))],
                    [Prop("P", Fn(["f", "f"], N(0)))], Call("P", R("FA"), R("FB")));
            Case("HP-14k", "NEED-04: owned views with distinct nonempty property lists are distinct declaring scopes",
                Need04Views(callableBlock, callableBlock with { Properties = L(callableBlock.Properties.ToArray()) }));
            var open = Block(Namespace(Public("Unused", Body(N(3)))));
            var withOpen = callableBlock with { Opens = L(open) };
            Case("HP-14l", "NEED-04: owned views with distinct nonempty opens lists are distinct declaring scopes",
                Need04Views(withOpen, withOpen with { Opens = L(open) }));
            Case("HP-14m", "NEED-04 control: copied empty opens lists keep equivalent owned scopes",
                Need04Views(callableBlock, callableBlock with { Opens = L<Expr>() }));
            var replacedProperties = callableBlock with { Properties = L(callableBlock.Properties.ToArray()) };
            Case("HP-14n", "NEED-04: replacing a callable's OWN lists preserves its declaration identity",
                Program([], [Prop("P", Fn(["f", "f"], N(0)))],
                    Call("P", Block(callableBlock), Block(replacedProperties))));
            var holder = Namespace(Public("Lib", Namespace(Public("F", Body(N(7)))))) with { Parent = oneEmpty };
            Expr Providers(Algorithm.User second)
                => Program([Dot(R("A"), "Lib"), Dot(R("B"), "Lib")],
                    [Prop("A", holder), Prop("B", second)], R("F"));
            Case("HP-14o", "Q-19: provider declarations under owned views with different nonempty lists stay distinct",
                Providers(holder with { Properties = L(holder.Properties.ToArray()) }));
            Case("HP-14p", "Q-19 control: providers under equivalent owned reconstructions share identity",
                Providers(holder with { }));

            Expr LiteralAliases(bool sameComponents)
            {
                var host = Scope(null, Prop("F", Body(N(7))),
                    Prop("Capture", new Algorithm.User(null, L<ParameterPattern>(new CaptureParameterPattern("op", Kind: ParameterKind.Meta)),
                        L<Expr>(), L<Property>(), new OutputBundle([X("op")]))),
                    Prop("R", Body(Call("Capture", Call("F")))));
                var literal = new Algorithm.Alias(null, L<Expr>(), L<Property>(), Dot(R("R"), "Algorithm")) { HasRuntimeTarget = true };
                var opens = L(Block(Namespace(Public("Unused", Body(N(3))))));
                // Distinct declarations, no properties in either owned parent: a shared literal's
                // alias key must retain the opens-list identity directly, without a binding id.
                var first = new Algorithm.User(host, L<ParameterPattern>(), opens, L<Property>(), new OutputBundle([Block(literal)]));
                var second = new Algorithm.User(host, L<ParameterPattern>(), sameComponents ? opens : L(opens.ToArray()),
                    L<Property>(), new OutputBundle([Block(literal)]));
                // Value-position blocks wire to their caller. Supply the target through that
                // caller too; the pre-wired host edge remains part of the encoded input graph.
                return Program([], host.Properties.ToArray(), Block(first), Block(second));
            }
            Case("HP-14q", "shared runtime alias literal under property-free owned parents with distinct opens lists",
                LiteralAliases(false), "R", "F");
            Case("HP-14r", "control: shared runtime alias literal under owned parents sharing their opens list",
                LiteralAliases(true), "R", "F");

            // FG-I1: one declaration under an identified and under an anonymous level. One block object
            // is an inline `open` target (wired under the root's anonymous level) and a property
            // (wired under the identified root), so the two reaches of `F` are one declaration, equal
            // block levels, and a MIXED parent pair: the outside of Lean's provenance domain.
            Expr SharedAcrossPresence()
            {
                var block = Namespace(Public("F", Fn(["x"], X("x"))));
                return Program([Block(block)], [Public("N", block), Prop("P", Fn(["f", "f", "f"], N(0)))],
                    Call("P", R("F"), Dot(R("N"), "F"), R("F")));
            }
            Case("HP-14s", "NEED-04: one shared block as an open target and a property is two callables",
                SharedAcrossPresence());

            // FG-I1: the same block pre-wired under two ownerless host levels and left unwired once: three
            // chains of EQUAL depth, so activations cannot refuse the pair. In Lean only the printed
            // fallback separates the identified from the anonymous outer level (`equalDepthFork`).
            Expr EqualDepthFork()
            {
                var block = Namespace(Public("F", Fn(["x"], X("x"))));
                static Property Opener(string name, Algorithm opened) => Public(name, new Algorithm.User(null,
                    L<ParameterPattern>(), L(Block(opened)),
                    L(Public("G", new Algorithm.Alias(null, L<Expr>(), L<Property>(), R("F")))), OutputBundle.Empty));
                return Program([],
                    [Opener("P", block with { Parent = Scope(null) }), Opener("Q", block),
                     Opener("R", block with { Parent = Scope(null) }), Prop("Same", Fn(["f", "f", "f"], N(0)))],
                    Call("Same", Dot(R("P"), "G"), Dot(R("Q"), "G"), Dot(R("R"), "G")));
            }
            Case("HP-14t", "NEED-04: one block under two host levels and the prelude, at one depth, is three callables",
                EqualDepthFork());

            // Q-19 under the runtime declaration index (November 2026): ONE declaration reached under two
            // DISTINCT empty host levels, interleaved with another declaration and a repeat of the first
            // level. Only reaches of one declaration are compared; the repeat is the first reach's provider,
            // while the second level's reach stays its own, so F is ambiguous. Under ONE level object the
            // three reaches are one provider beside G's.
            Expr Interleaved(ScopeCtx first, ScopeCtx second)
                => Program([Block(provider with { Parent = first }), Block(Namespace(Public("G", Body(N(9))))),
                            Block(provider with { Parent = second }), Block(provider with { Parent = first })],
                    [], Add(R("F"), R("G")));
            Case("HP-14u", "Q-19: one declaration under two DISTINCT empty host levels, interleaved with another provider and a repeat, stays two providers",
                Interleaved(Scope(null), Scope(null)));
            Case("HP-14v", "Q-19 control: the same interleaving under ONE empty host level object is one provider of F",
                Interleaved(oneEmpty, oneEmpty), "F", "G");
        }

        // HP-15: DECON-CACHE-2 — parsed assignment deconstructions transformed with public record copies
        // (no pre-wired parents). The C# routes run the shared-bind memo, which Lean does not have, so
        // agreement pins that the memo serves exactly the ordinary helper's value: a target helper copied
        // over ANOTHER argument (H04/H05), a copy whose unpacking pattern CHANGED under its retained group
        // token (V05/V06), and a copy reading a LOCALLY shadowing source (V07). Both read orders.
        Case("HP-15a", "a deconstruction helper copied over another argument, copy read first (H04)",
            DeconstructionMemoEligibilityTests.HostWitness("H04"), "a", "c");
        Case("HP-15b", "a deconstruction helper copied over another argument, original read first (H05)",
            DeconstructionMemoEligibilityTests.HostWitness("H05"), "a", "c");
        Case("HP-15c", "a deconstruction helper copy with a changed unpacking pattern, copy read first (V05)",
            DeconstructionMemoEligibilityTests.HostWitness("V05"), "a", "c");
        Case("HP-15d", "a deconstruction helper copy with a changed unpacking pattern, original read first (V06)",
            DeconstructionMemoEligibilityTests.HostWitness("V06"), "a", "c");
        Case("HP-15e", "a deconstruction target body copied with a local shadowing source (V07)",
            DeconstructionMemoEligibilityTests.HostWitness("V07"), "a", "c");

        // HP-16: KL-06 — what a FAILED run leaves published. A failure keeps every entry a successful owner
        // published before it, and a failed owner publishes nothing; the generated guards compare both
        // sides' published entries on failing cases too. The root failure after a published X (the KL-06
        // witness), a failing owner chain under a host level, and a failed owner whose host dependency
        // stays published.
        Case("HP-16a", "a run that fails after X = 7 was published keeps the entry (rows X, 1 / 0)",
            Program([], [Prop("X", Body(N(7)))], R("X"), Div(N(1), N(0))), "X");
        Case("HP-16b", "a failing host property and the failing owner reading it publish nothing",
            OpenedThrough(Scope(null, Prop("P", Body(Div(N(1), N(0))))), [R("P")]), "P", "Run");
        Case("HP-16c", "a failed owner publishes nothing while its host dependency P stays published",
            OpenedThrough(Scope(null, Prop("P", Body(N(7)))), [R("P"), Div(N(1), N(0))]), "P", "Run");

        // HP-17: KL-07 — a host property holding a list of host-built strings, read through an opened block.
        // The neutral text writes strings between unescaped quotes, so the two-string list and the
        // one-string list (a host-built string holding the quote, which no source literal can) both read
        // L['a', 'b']; only their kl-struct-v1 identities tell them apart (NeutralCollisionPairs).
        Case("HP-17a", "KL-07: a host property holding the list of the two strings a and b",
            OpenedThrough(Scope(null, Prop("P", Body(ListOf(Str("a"), Str("b"))))), [R("P")]), "P");
        Case("HP-17b", "KL-07: a host property holding the list of the ONE host-built string a', 'b",
            OpenedThrough(Scope(null, Prop("P", Body(ListOf(Str("a', 'b"))))), [R("P")]), "P");

        // HP-18: EXPORTED-DETACHED (November 2026) — MIS-EXPOSED host-built trees. The evaluator enforces
        // the exposure flag: an exported zero-argument property is evaluated DETACHED from the
        // activations that exist when its evaluation starts, and a captured parameter read is
        // lexical-only. Each case hands both evaluators a tree whose `Exported` flag is FALSE — the
        // property reads an input of the call around it — and both refuse it, where a value used to be
        // shared across calls or read from whichever caller was live. The watched properties compare
        // what the failed runs published: nothing under the falsely exported key.
        {
            // (a)/(b) The former evaluation witness: a body reading a name it does not bind, exported,
            // on a host level and on the evaluator-owned block. Formerly S[1, 1], the first caller's x.
            static Property Unbound() => Prop("P", Body(X("x")));
            Case("HP-18a", "an exported host property reading a name it does not bind is refused, whoever reads it",
                OpenedThrough(Scope(null, Unbound()), [Call("G", N(1)), Call("G", N(2))], GReader()), "P");
            Case("HP-18b", "the same exported property declared by the evaluator-owned block is refused",
                OpenedThrough(Scope(null), [Call("G", N(1)), Call("G", N(2))], GReader(), Unbound()), "P");
            // (c) A host level that lists x among its Parameters is x's lexical owner, and no call
            // activates a host level: the local-only read finds no binding. Formerly S[1, 2], each
            // caller's own x.
            Case("HP-18c", "a local-only host property reading a parameter its unactivated host level names is refused",
                OpenedThrough(new ScopeCtx(null, L<Expr>(), L(Local("P", Body(X("x")), "x")), L("x")),
                    [Call("G", N(1)), Call("G", N(2))], GReader()), "P");

            // (d)–(i) F(y) declared by a host level, with ONE member falsely exported.
            static ScopeCtx Owner(Property[] members, params Expr[] rows) => Scope(null, Public("F", FnWith(["y"], members, rows)));
            static Property MisExposed(string name, params Expr[] rows) => Prop(name, Body(rows));
            Case("HP-18d", "a falsely exported P = y * 10 is refused in ONE call (formerly 10)",
                OpenedThrough(Owner([MisExposed("P", Mul(X("y"), N(10)))], R("P")), [Call("F", N(1))]), "P");
            Case("HP-18e", "the same P is refused in TWO calls (formerly S[10, 10]: the first call's value twice)",
                OpenedThrough(Owner([MisExposed("P", Mul(X("y"), N(10)))], R("P")), [Call("F", N(1)), Call("F", N(2))]), "P");
            Case("HP-18f", "an explicit P() of the falsely exported P is refused (formerly it published the first call's value)",
                OpenedThrough(Owner([MisExposed("P", Mul(X("y"), N(10)))], Add(Call("P"), R("P"))), [Call("F", N(1)), Call("F", N(2))]), "P");
            // A falsely exported P navigating the correctly local-only Box.Q, in both row orders.
            static Property[] Navigating() =>
                [Prop("Box", Namespace(new Property("Q", Body(Mul(X("y"), N(10))), IsPublic: true, PropertyExposure.LocalOnlyCapturedAncestorParameters)
                    { RequiredAncestorParameters = L("y") })),
                 MisExposed("P", Add(Dot(R("Box"), "Q"), N(0)))];
            Case("HP-18g", "a falsely exported P navigating a local-only member is refused when the owner's call comes first (formerly S[10, 10])",
                OpenedThrough(Owner(Navigating(), R("P")), [Call("F", N(1)), Dot(R("F"), "P")]), "P", "Q");
            Case("HP-18h", "the same navigation is refused when the outside read comes first",
                OpenedThrough(Owner(Navigating(), R("P")), [Dot(R("F"), "P"), Call("F", N(1))]), "P", "Q");
            // A falsely exported P reading the correctly local-only L, whose entry the row already
            // established: the refusal runs before the cache is consulted, so the hit is refused too.
            Case("HP-18i", "a falsely exported P reading an ESTABLISHED local-only entry is refused (formerly S[21, 31])",
                OpenedThrough(Owner([Local("L", Body(Mul(X("y"), N(10))), "y"), MisExposed("P", Add(R("L"), N(1)))], Add(R("L"), R("P"))),
                    [Call("F", N(1)), Call("F", N(2))]), "L", "P");
            // The correctly classified twins: detachment changes nothing.
            Case("HP-18j", "control: the same P declared local-only keeps one value per call",
                OpenedThrough(Owner([Local("P", Body(Mul(X("y"), N(10))), "y")], R("P")), [Call("F", N(1)), Call("F", N(2))]), "P");
            Case("HP-18k", "control: a self-contained exported member of a called owner is evaluated once in each call of the owner",
                OpenedThrough(Owner([Prop("T", Body(Tick()))], Add(R("T"), X("y"))), [Call("F", N(1)), Call("F", N(2))]), "T");

            // (l)–(q) THE OTHER EXECUTED OPERATIONS on an unavailable parameter. The VALUE read is not
            // the only operation on a written parameter: it is refused with unknownName where it is
            // INVOKED (its CALLABLE projection — never the missing-callable report of a usable value)
            // and where it is TRANSPORTED as a supplied argument (while the supply is formed, although
            // the callee never demands it). Each mutant has its correctly classified control.
            static Property IncMember() => Public("Inc", Fn(["n"], Add(X("n"), N(1))));
            static Property IgnoreMember() => Public("Ignore", Fn(["z"], N(42)));
            static ScopeCtx OwnerBeside(Property helper, Property[] members, params Expr[] rows)
                => Scope(null, helper, Public("F", FnWith(["y"], members, rows)));
            static Expr Invoking() => Add(Call(X("y"), N(5)), N(0));
            static Expr Transporting() => Add(Call("Ignore", X("y")), N(0));
            Case("HP-18l", "a falsely exported P = y(5) + 0 is refused where the parameter is INVOKED (formerly notAnAlgorithm)",
                OpenedThrough(OwnerBeside(IncMember(), [MisExposed("P", Invoking())], R("P")), [Call("F", R("Inc"))]), "P");
            Case("HP-18m", "control: the same P declared local-only invokes the supplied callable",
                OpenedThrough(OwnerBeside(IncMember(), [Local("P", Body(Invoking()), "y")], R("P")), [Call("F", R("Inc"))]), "P");
            Case("HP-18n", "a falsely exported P = Ignore(y) + 0 is refused where the parameter is TRANSPORTED, although the callee ignores it (formerly 42)",
                OpenedThrough(OwnerBeside(IgnoreMember(), [MisExposed("P", Transporting())], R("P")), [Call("F", N(7))]), "P");
            Case("HP-18o", "control: the same P declared local-only transports the parameter and the callee ignores it",
                OpenedThrough(OwnerBeside(IgnoreMember(), [Local("P", Body(Transporting()), "y")], R("P")), [Call("F", N(7))]), "P");
            // A STATIC owner: G is never called, so inside the navigated member G.F the owner's `y` is
            // lexically owned and unavailable. No exported evaluation is involved, and H's own `y` —
            // the same name, dynamically live — never answers.
            static ScopeCtx StaticOwner(Property helper, Expr body) => Scope(null, helper,
                Public("G", FnWith(["y"], [Public("F", Fn(["n"], body))], N(0))),
                Public("H", Fn(["y"], Call(Dot(R("G"), "F"), N(1)))));
            Case("HP-18p", "a static owner's parameter is refused where a navigated member INVOKES it, never the caller's same-named callable (formerly 2)",
                OpenedThrough(StaticOwner(IncMember(), Call(X("y"), X("n"))), [Call("H", R("Inc"))]));
            Case("HP-18q", "a static owner's parameter is refused where a navigated member TRANSPORTS it (formerly 43)",
                OpenedThrough(StaticOwner(IgnoreMember(), Add(Call("Ignore", X("y")), X("n"))), [Call("H", N(7))]));

            // (r)–(u) The same refusal through two more routes: the dot-only `string` intrinsic's
            // receiver read, and a SPREAD operand of a supply.
            static Expr StringReceiver() => Dot(X("y"), "string");
            static Expr SpreadOperand() => Add(Call("Inc", new Expr.SequenceSpread(X("y"))), N(0));
            Case("HP-18r", "a falsely exported P = y.string is refused at the intrinsic's receiver",
                OpenedThrough(Owner([MisExposed("P", StringReceiver())], R("P")), [Call("F", N(7))]), "P");
            Case("HP-18s", "control: the same P declared local-only reads the receiver's text",
                OpenedThrough(Owner([Local("P", Body(StringReceiver()), "y")], R("P")), [Call("F", N(7))]), "P");
            Case("HP-18t", "a falsely exported P = Inc(y*) + 0 is refused at the spread operand",
                OpenedThrough(OwnerBeside(IncMember(), [MisExposed("P", SpreadOperand())], R("P")), [Call("F", N(7))]), "P");
            Case("HP-18u", "control: the same P declared local-only spreads the parameter",
                OpenedThrough(OwnerBeside(IncMember(), [Local("P", Body(SpreadOperand()), "y")], R("P")), [Call("F", N(7))]), "P");
        }

        // HP-19: RETAINED RUNTIME-ALIAS CELLS (ledger R-1, November 2026). A retained binding cell records
        // the input reads of its computation, and an exported (detached) evaluation that reuses a cell known
        // to have read an input of an activation detached in it is refused with the alias's own
        // localOnlyProperty before the channel runs, whichever row established the cell; a read the cell's
        // computation makes while such an evaluation is served is refused where it happens, with its own
        // refusal. Parsed programs with members forced exported (the front end classifies them local-only);
        // the controls keep their values.
        {
            const string Selector = "Cap(meta r) = r\nInc(n) = n + 1\nDbl(n) = n * 2\nSel(k) = if(k == 1, Cap(Inc(0)), Cap(Dbl(0)))\n";
            const string Witness = Selector + "F(y) = {\n  A = Sel(y).Algorithm\n  P = A(5) + 0\n  {0}\n}\nF(1), F(2)\n";
            static Expr Classified(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
            static string With(string template, string rows) => template.Replace("{0}", rows, StringComparison.Ordinal);
            Case("HP-19a", "R-1: a falsely exported sibling reusing the call's established alias cell is refused with the alias's localOnlyProperty (formerly S[S[6, 6], S[10, 10]], unrefused)",
                MisExposedSource(With(Witness, "A(5), P"), "F.P"), "P");
            Case("HP-19b", "R-1: the same sibling establishing the cell itself is refused at the written y, the direct read's unknownName (the other row order)",
                MisExposedSource(With(Witness, "P, A(5)"), "F.P"), "P");
            Case("HP-19c", "R-1: a falsely exported bare read of a parameter-rooted path alias after an attached read is refused (the value route)",
                MisExposedSource("G(v) = v + 1\nF(y) = {\n  A = y.G\n  P = A + 0\n  A + 0, P\n}\nF(1), F(2)\n", "F.P"), "P");
            Case("HP-19d", "R-1: a local-only HIT inside the cell's computation is recorded, so the reuse is refused",
                MisExposedSource(Selector + "F(y) = {\n  L = Sel(y)\n  A = L.Algorithm\n  P = A(5) + 0\n  L.Algorithm(5), A(5), P\n}\nF(1), F(2)\n", "F.P"), "P");
            Case("HP-19e", "R-1: a cell whose computation reuses another retained cell takes its read, so the reuse is refused",
                MisExposedSource(Selector + "F(y) = {\n  B = Sel(y).Algorithm\n  A = Cap(B(0)).Algorithm\n  P = A(5) + 0\n  B(5), A(5), P\n}\nF(1), F(2)\n", "F.P"), "P");
            Case("HP-19f", "R-1 control: an INDEPENDENT local-only alias cell is shared with the falsely exported sibling",
                MisExposedSource("Cap(meta r) = r\nInc(n) = n + 1\nDbl(n) = n * 2\nF(y) = {\n  A = if(true, Cap(Inc(0)), Cap(Dbl(y))).Algorithm\n  P = A(5) + 0\n  A(5), P\n}\nF(1), F(2)\n", "F.P"), "P");
            Case("HP-19g", "R-1 control: the witness correctly classified keeps S[S[6, 6], S[10, 10]]",
                Classified(With(Witness, "A(5), P")), "P");

            // DEFERRED READS: the cell's VALUE is a lazy list built in its own computation, whose positions read
            // y only when read. THE DEMAND DECIDES (owner decision 2026-11-24): the read is refused while a
            // detached evaluation that detaches y's activation is served, and is the row's own otherwise.
            const string Lazy = "Cap(meta r) = r\nF(y) = {\n  Mk(v) = {\n    Z(*xs) = [1, 2].map{ n + y }\n    Cap(Z())\n  }\n  A = Mk(5).Algorithm\n  P = {0}\n  Q = P[0] + 0\n  {1}\n}\nF(1), F(2)\n";
            static string Rows(string template, string p, string rows)
                => template.Replace("{0}", p, StringComparison.Ordinal).Replace("{1}", rows, StringComparison.Ordinal);
            Case("HP-19h", "R-1: a falsely exported sibling reading a lazy position of a reused cell is refused at the deferred read (formerly S[S[2, 2], S[2, 3]], unrefused)",
                MisExposedSource(Rows(Lazy, "A[0] + 0", "A.count, P"), "F.P"), "P");
            Case("HP-19i", "R-1: the same sibling establishing the cell itself is refused at the same deferred read (the other row order)",
                MisExposedSource(Rows(Lazy, "A[0] + 0", "P, A.count"), "F.P"), "P");
            Case("HP-19j", "R-1 (owner decision): after the sibling read only the count, the attached row's later read of a position uses the row's own input",
                MisExposedSource(Rows(Lazy, "A.count + 0", "A.count, P, A[1]"), "F.P"), "P");
            Case("HP-19k", "R-1: a lazy value carried out of the sibling unread and read by the ROW is the row's own read",
                MisExposedSource(Rows(Lazy, "A.take(2)", "A.count, P[0]"), "F.P"), "P");
            Case("HP-19l", "R-1: a cell whose VALUE is another cell's lazy value is refused at the deferred read",
                MisExposedSource("Cap(meta r) = r\nF(y) = {\n  Mk(v) = {\n    Z(*xs) = [1, 2].map{ n + y }\n    Cap(Z())\n  }\n  B = Mk(5).Algorithm\n  Mk2(v) = {\n    W(*xs) = B\n    Cap(W())\n  }\n  A = Mk2(0).Algorithm\n  P = A[0] + 0\n  B.count, A.count, P\n}\nF(1), F(2)\n", "F.P"), "P");
            Case("HP-19m", "R-1 control: an INDEPENDENT lazy value is shared with the falsely exported sibling",
                MisExposedSource("Cap(meta r) = r\nDbl(n) = n * 2\nZ0(*xs) = [1, 2].map{ n + 1 }\nF(y) = {\n  A = if(true, Cap(Z0()), Cap(Dbl(y))).Algorithm\n  P = A[0] + 0\n  A.count, P\n}\nF(1), F(2)\n", "F.P"), "P");
            Case("HP-19n", "R-1 control: the lazy witness correctly classified keeps S[S[2, 2], S[2, 3]]",
                Classified(Rows(Lazy, "A[0] + 0", "A.count, P")), "P");
            Case("HP-19o", "R-1 (owner decision): the count-only sibling FIRST establishes the cell at the call's own watermark, and the row's later position read uses the row's own input",
                MisExposedSource(Rows(Lazy, "A.count + 0", "P, A.count, A[1]"), "F.P"), "P");
            Case("HP-19p", "R-1: a warm cell still enforces the reader's access — the sibling demands a position the row already read, and its reuse is refused",
                MisExposedSource(Rows(Lazy, "A[1] + 0", "A.count, A[1], P"), "F.P"), "P");
            Case("HP-19q", "R-1: a second falsely exported sibling that demands the escaped position is refused at the deferred read",
                MisExposedSource(Rows(Lazy, "A.take(2)", "A.count, Q"), "F.P", "F.Q"), "P", "Q");

            // A CORRECTLY CLASSIFIED program (review 050804fe, finding 1): the activation supplying z is recorded
            // inside B's own computation, so forwarding B's list through A keeps that input B's own.
            const string Forwarded = "Cap(meta r) = r\nBuild(z) = {\n  Z(*xs) = [1, 2].map{ n + z }\n  Cap(Z())\n}\nB = Build(5).Algorithm\nBuild2(v) = {\n  W(*xs) = B\n  Cap(W())\n}\nA = Build2(0).Algorithm\nObserve = A.count + 0\n{0}\n";
            Case("HP-19r", "R-1 control (correctly classified): a list forwarded through a second root alias keeps its freshly owned input",
                Classified(With(Forwarded, "B.count, A.count, Observe, A[0]")), "Observe");
            Case("HP-19s", "R-1 control (correctly classified): the same with the count reads in the other order",
                Classified(With(Forwarded, "A.count, B.count, Observe, A[0]")), "Observe");
            Case("HP-19t", "R-1 control (correctly classified): the same with the exported reader establishing the second alias",
                Classified(With(Forwarded, "B.count, Observe, A[0]")), "Observe");

            // AN ADMITTED LOCAL-ONLY MEMBER ACCESS is an input read (finding 2): the member's accessibility uses
            // the enclosing activation although the selected branch never reads y.
            const string Member = "Cap(meta r) = r\nF(y) = {\n  Box = {\n    public G(x) = if(true, x + 1, y + 0)\n  }\n  A = Cap(Box.G(0)).Algorithm\n  P = A(5) + 0\n  {0}\n}\nF(1)\n";
            const string MemberCall = "Cap(meta r) = r\nInc(x) = x + 1\nF(y) = {\n  Box = { public Mk(k) = if(true, Cap(Inc(0)), y + 0) }\n  A = Box.Mk(0).Algorithm\n  P = A(5) + 0\n  {0}\n}\nF(1)\n";
            Case("HP-19u", "R-1: an admitted access of a local-only member is the cell's input read, so the sibling's reuse is refused although the member's body never reads y",
                MisExposedSource(With(Member, "A(5), P"), "F.P"), "P");
            Case("HP-19v", "R-1: the same sibling establishing the cell is refused at the member access (the other row order)",
                MisExposedSource(With(Member, "P, A(5)"), "F.P"), "P");
            Case("HP-19w", "R-1 control: the member witness correctly classified keeps S[6, 6]",
                Classified(With(Member, "A(5), P")), "P");
            Case("HP-19x", "R-1: the same through a CALL of the local-only member as the cell's receiver",
                MisExposedSource(With(MemberCall, "A(5), P"), "F.P"), "P");
            Case("HP-19y", "R-1: the member call with the sibling first is refused at the member access",
                MisExposedSource(With(MemberCall, "P, A(5)"), "F.P"), "P");

            // A KNOWN DEPENDENT CELL IS REFUSED BEFORE ITS CHANNEL RUNS (finding 3): Same(A, A) warms the CALLABLE,
            // which reads y; the sibling's VALUE request is refused without running the channel's effect.
            Case("HP-19z", "R-1: a cold VALUE channel of a cell known to depend on y is refused before it runs",
                MisExposedSource("Cap(meta r) = r\nEffect(*xs) = tick()\nSel(k) = if(k == 1, Cap(Effect()), Cap(Effect()))\nSame(f, f) = 0\nF(y) = {\n  A = Sel(y).Algorithm\n  P = A + 0\n  Same(A, A), P\n}\nF(1)\n", "F.P"), "P");

            // OPEN QUALIFICATION (pinned residual): an `open`-provided local-only member's admission is resolved by
            // the lexical lookup, a state-free judgment of the model, and is not recorded on the cell — the reuse
            // is not refused in either row order.
            const string Opened = "Cap(meta r) = r\nF(y) = {\n  open Box\n  Box = {\n    public G(x) = if(true, x + 1, y + 0)\n  }\n  A = Cap(G(0)).Algorithm\n  P = A(5) + 0\n  {0}\n}\nF(1)\n";
            Case("HP-20a", "R-1 open qualification: an open-provided local-only member's admitted access is not recorded — the sibling's reuse is not refused (attached read first)",
                MisExposedSource(With(Opened, "A(5), P"), "F.P"), "P");
            Case("HP-20b", "R-1 open qualification: the same with the sibling first",
                MisExposedSource(With(Opened, "P, A(5)"), "F.P"), "P");

            cases.Add(new("HP-21a", "the escaped element projects its alias under the element's detached watermark and refuses y before tick",
                MisExposedSource(EscapedAliasCall, "F.P"), L("P")) { ExpectedTickCount = 0 });
        }

        return cases.AsReadOnly();
    }

    /// <summary>
    /// KL-07: pairs of comparable cases whose successful values share their neutral text but are
    /// different values. The generated artifact pins each case's <c>kl-struct-v1</c> identity and
    /// also guards that neither case's Lean value has the OTHER case's identity, so substituting
    /// one list for the other fails the structural guard while the neutral guard still passes.
    /// </summary>
    public static IReadOnlyList<(string Left, string Right)> NeutralCollisionPairs { get; } = [("HP-17a", "HP-17b")];
}
