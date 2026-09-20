using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;
using ValEnv = System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Result Value)>;

namespace KatLang.Tests;

/// <summary>
/// The evaluator's declaration, activation, and scope-owner state lives ON the runtime
/// model (September 2026, invalid-state audit §3.1) — no process-global side table:
/// <list type="bullet">
///   <item><b>Declaration identity</b> is <see cref="Algorithm.Declaration"/>: a token minted
///   by the constructor of every <see cref="Algorithm.User"/>/<see cref="Algorithm.Conditional"/>
///   and carried by every <c>with</c> copy (a copy is a VIEW of the same written declaration),
///   stored in a private equality-transparent slot so structural record equality is untouched.</item>
///   <item><b>Activation identity</b> is a <see cref="ParameterActivation"/> — one fresh object
///   per call of a parameterized body or clause family, compared by reference — carried on the
///   activated <see cref="ScopeCtx"/> (<see cref="ScopeCtx.Activation"/>): the entered body's
///   head scope (<see cref="Evaluator.EvalCtx.HeadScope"/>) or the family scope a branch body
///   is wired under.</item>
///   <item><b>Scope ownership</b> is <see cref="ScopeCtx.Owner"/>, set by the two evaluator
///   scope construction paths; a host-built scope has none and identifies only itself;
///   parent-chain lookup through it has no cache owner, exactly as before.</item>
/// </list>
/// The behavioural tests run the sync generic, sync optimized, and genuinely suspending
/// async paths, and each is sensitive to a specific wrong representation named in its
/// comment (a mutation that was applied and observed to fail it during the change).
/// </summary>
public class EvaluatorIdentityStateTests
{
    // ── A. Declaration identity representation ──────────────────────────────

    [Fact]
    public void SeparateConstructions_AreDistinctDeclarations_AndCopiesShareTheirs()
    {
        var first = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var second = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        Assert.NotNull(first.Declaration);
        Assert.NotSame(first.Declaration, second.Declaration);

        // A `with` copy — parent wiring, a parameter-list replacement, a copy of a copy — is a
        // view of the same declaration, with no registration step.
        var scope = new ScopeCtx(null, [], []);
        Assert.Same(first.Declaration, (first with { Parent = scope }).Declaration);
        Assert.Same(first.Declaration, (first with { }).Declaration);
        Assert.Same(first.Declaration, first.WithParameters([new ParameterDeclaration("x")]).Declaration);
        Assert.Same(first.Declaration, first.WithParams(["a", "b"]).Declaration);
        Assert.Same(first.Declaration, ((first with { Parent = scope }) with { Output = [new Expr.Num(2)] }).Declaration);

        var branch = new CondBranch(new Pattern.Bind("x"), new Algorithm.User(null, [], [], [], [new Expr.Num(1)]));
        var family = new Algorithm.Conditional(null, [], [branch]);
        var otherFamily = new Algorithm.Conditional(null, [], [branch]);
        Assert.NotNull(family.Declaration);
        Assert.NotSame(family.Declaration, otherFamily.Declaration);
        Assert.Same(family.Declaration, (family with { Parent = scope }).Declaration);
        Assert.NotSame(family.Declaration, branch.Body.Declaration);

        Assert.Null(new Algorithm.Builtin(BuiltinId.count).Declaration);
    }

    [Fact]
    public void DeclarationToken_IsTransparentToStructuralEquality()
    {
        // Two separately constructed algorithms over the SAME component instances (record
        // equality compares the list members by reference) were equal before the token existed
        // and remain equal, hash alike, and print alike; a copy equals its source.
        IReadOnlyList<ParameterPattern> patterns = [new CaptureParameterPattern("x")];
        IReadOnlyList<Expr> opens = [];
        IReadOnlyList<Property> properties = [];
        OutputBundle output = [new Expr.Param("x")];
        var first = new Algorithm.User(null, patterns, opens, properties, output);
        var second = new Algorithm.User(null, patterns, opens, properties, output);
        Assert.NotSame(first.Declaration, second.Declaration);
        Assert.Equal(first, second);
        Assert.Equal(first.GetHashCode(), second.GetHashCode());
        Assert.Equal(first.ToString(), second.ToString());
        Assert.DoesNotContain("declaration#", first.ToString());
        Assert.Equal(first, first with { });

        IReadOnlyList<CondBranch> branches = [new CondBranch(new Pattern.Bind("x"), first)];
        var family = new Algorithm.Conditional(null, opens, branches);
        var otherFamily = new Algorithm.Conditional(null, opens, branches);
        Assert.NotSame(family.Declaration, otherFamily.Declaration);
        Assert.Equal(family, otherFamily);
        Assert.Equal(family.GetHashCode(), otherFamily.GetHashCode());
        Assert.Equal(family.ToString(), otherFamily.ToString());

        // Semantic tokens must also be safe in ordinary equality-based collections.
        // Only Algorithm's inaccessible storage slot ignores its contents for equality.
        var token = new DeclarationIdentity();
        var other = new DeclarationIdentity();
        Assert.False(ReferenceEquals(token, other));
        Assert.False(token.Equals(other));
        Assert.False(token.Equals((object)other));
        Assert.False(EqualityComparer<DeclarationIdentity>.Default.Equals(token, other));
        Assert.Equal(2, new HashSet<DeclarationIdentity> { token, other, token }.Count);
        Assert.Equal(2, new[] { token, other, token }.Distinct().Count());
        Assert.Single(new HashSet<Algorithm> { first, second, first with { } });
        Assert.Single(new HashSet<Algorithm> { family, otherFamily, family with { } });
    }

    [Fact]
    public void ScopeOwnership_IsExcludedFromScopeEquality()
    {
        var owner = new Algorithm.User(null, [new CaptureParameterPattern("n")], [], [], [new Expr.Param("n")]);
        IReadOnlyList<Expr> opens = [];
        IReadOnlyList<Property> properties = [new Property("P", new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))];
        IReadOnlyList<string> parameters = ["n"];
        var plain = new ScopeCtx(null, opens, properties, parameters);
        var ownedStatic = new ScopeCtx(null, opens, properties, parameters) { Owner = owner };
        var ownedActive = new ScopeCtx(null, opens, properties, parameters)
        {
            Owner = owner,
            Activation = ParameterActivation.Capture(["n"], Evaluator.EvalCtx.Empty, [("n", new Result.Atom(1))]),
        };
        var otherActivation = ownedActive with
        {
            Activation = ParameterActivation.Capture(["n"], Evaluator.EvalCtx.Empty, [("n", new Result.Atom(2))]),
        };

        Assert.Equal(plain, ownedStatic);
        Assert.Equal(plain, ownedActive);
        Assert.Equal(ownedActive, otherActivation);
        Assert.Equal(plain.GetHashCode(), ownedActive.GetHashCode());
        Assert.NotSame(ownedActive.Activation, otherActivation.Activation);
        Assert.Same(owner, ownedActive.Owner);
        Assert.Same(owner.Declaration, ownedActive.Declaration);
        Assert.Null(plain.Owner);
        Assert.Null(plain.Declaration);
        Assert.Null(plain.Activation);
        Assert.DoesNotContain("Owner", plain.ToString());
        Assert.DoesNotContain("Activation", ownedActive.ToString());

        // Every positional component still distinguishes scopes.
        Assert.NotEqual(plain, plain with { Parent = new ScopeCtx(null, [], []) });
        Assert.NotEqual(plain, plain with { Opens = [new Expr.Resolve("Lib")] });
        Assert.NotEqual(plain, plain with { Properties = [] });
        Assert.NotEqual(plain, plain with { Parameters = ["m"] });
        Assert.Equal(plain, plain with { Parent = null });
    }

    [Fact]
    public void ParsedSiblings_WithIdenticalBodies_AreDistinctDeclarations()
    {
        var root = SourceProvenance.ParseValid("A = { public X = 1 }\nB = { public X = 1 }\nA.X + B.X").Root;
        var a = Assert.Single(root.Properties, property => property.Name == "A").Value;
        var b = Assert.Single(root.Properties, property => property.Name == "B").Value;
        Assert.NotSame(a.Declaration, b.Declaration);
        Assert.NotSame(a.Declaration, root.Declaration);
        Assert.NotSame(a.Declaration, Assert.Single(a.Properties).Value.Declaration);
    }

    // ── B. Behaviour on every execution path ────────────────────────────────

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public async Task SelfNavigation_ReachesTheActiveDeclaration(int path)
    {
        // `Outer.Inner.X` written inside Outer's own body navigates a FRESH copy of Outer's
        // declaration; it must find the currently active level of that declaration (same
        // token, compatible activations) so X is accessible and reads THIS call's n.
        // Sensitive to: a copy minting a fresh declaration token; a wired scope without an
        // owner (no declaration to compare); the head scope losing its activation.
        const string source = "Outer(n) = {\n  Inner = { public X = n }\n  Outer.Inner.X\n}\nOuter(5), Outer(6)";
        Assert.Equal([5m, 6m], await Atoms(source, path));
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public async Task RepeatedAndNestedActivations_ReadTheirOwnCapturedValues(int path)
    {
        // Every call is its own activation: a nested parameterized body reads the enclosing
        // call's binding, and two calls of one declaration never see each other's.
        // Sensitive to: an activation reused across calls of one declaration.
        const string nested = "Outer(n) = {\n  Mid(m) = {\n    Inner = { public X = n * 100 + m }\n    Inner.X\n  }\n  Mid(1) + Mid(2)\n}\nOuter(5), Outer(7)";
        Assert.Equal([1003m, 1403m], await Atoms(nested, path));

        // Recursion: each level's local-only Peek captures that level's n.
        const string recursion = "Down(n) = {\n  Peek = { n }\n  if(n == 0, Peek, Peek + Down(n - 1))\n}\nDown(3)";
        Assert.Equal([6m], await Atoms(recursion, path));
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public async Task ConditionalCall_PublishesItsBinderActivationOnTheFamilyScope(int path)
    {
        // The selected branch body is wired under the family scope carrying the matched
        // binders AND their activation; a nested member capturing a binder is accessible
        // inside the branch and reads that call's binding.
        // Sensitive to: the family scope created without its activation.
        const string source = "F(0) = 0\nF(n) = {\n  Inner = { public X = n }\n  Inner.X\n}\nF(5), F(6), F(0)";
        Assert.Equal([5m, 6m, 0m], await Atoms(source, path));
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public async Task ProviderCapturingAnotherFamilysBinder_IsRefusedInsideThisFamily(int path)
    {
        // Two clause families of identical shape (no opens, no properties, one binder `n`):
        // a provider capturing F's binder, handed through a common parameterized parent into
        // G's activation, cannot be read there — the required owner is F's family activation,
        // which is not on G's lexical chain. Sensitive to: a family scope created without its
        // own activation, or an activation compared by anything but reference.
        const string source = "H(f, k) = {\n  F(0) = 0\n  F(n) = H({ public X = n }, 0)\n  G(0) = 0\n  G(n) = f.X\n  if(k != 0, F(k), G(7))\n}\nH({ public X = 0 }, 5)";
        var result = await Run(source, path);
        Assert.True(result.IsError);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, KatLangError.FromEvalError(result.Error).Code);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public async Task ProviderCapturingAnotherActivationOfTheSameDeclaration_IsRefused(int path)
    {
        // Made is H's own member capturing n; the first activation hands its Made into a
        // second activation of the SAME declaration, whose Read finds the same declaring
        // scope on its chain — but a different activation. Activation identity is by
        // reference, so the access is refused; the same-activation read (the control) works.
        // Sensitive to: an activation compared by presence or by declaration instead of by
        // reference (CompatibleActivations).
        const string transfer = "H(f, n) = {\n  Made = { public X = n }\n  Read(g) = g.X\n  if(n != 0, H(Made, 0), Read(f))\n}\nH({ public X = 0 }, 5)";
        var refused = await Run(transfer, path);
        Assert.True(refused.IsError);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, KatLangError.FromEvalError(refused.Error).Code);

        const string control = "H(n) = {\n  Made = { public X = n }\n  Apply(g) = g.X\n  Apply(Made)\n}\nH(5), H(6)";
        Assert.Equal([5m, 6m], await Atoms(control, path));
    }

    [Fact]
    public void SharedComponents_DistinguishConstructedDeclarations_ButNotCopies()
    {
        // Declaration identity is the ONLY thing that separates two scopes whose components
        // (opens, properties, parameters, parent) are the same instances. Two separately
        // CONSTRUCTED declarations over shared components stay distinct: navigating G from
        // inside F's activation must not find F's active level, so G's captured member is
        // refused. A host `with` COPY, by contrast, is one declaration at two sites (the same
        // rule that keeps the evaluator's own wiring copies identified), so the navigation
        // finds F's activation and the member reads its n.
        // Sensitive to: comparing scopes by their components instead of their declaration
        // token, and to a copy minting a fresh token.
        var member = new Property("X", new Algorithm.User(null, [], [], [], [new Expr.Param("n")]), true,
            PropertyExposure.LocalOnlyCapturedAncestorParameters) { RequiredAncestorParameters = ["n"] };
        IReadOnlyList<ParameterPattern> patterns = [new CaptureParameterPattern("n")];
        IReadOnlyList<Expr> opens = [];
        IReadOnlyList<Property> properties = [member];
        OutputBundle output = [new Expr.DotCall(new Expr.Resolve("G"), "X")];
        var f = new Algorithm.User(null, patterns, opens, properties, output);

        var constructed = new Algorithm.User(null, patterns, opens, properties, output);
        Assert.Equal(f, constructed);
        var refused = Evaluator.Run(new Expr.AlgorithmExpr(Root(f, constructed)));
        Assert.True(refused.IsError);
        Assert.IsType<EvalError.LocalOnlyProperty>(Innermost(refused.Error));

        var copied = f with { };
        var admitted = Evaluator.Run(new Expr.AlgorithmExpr(Root(f, copied)));
        Assert.False(admitted.IsError, admitted.IsError ? admitted.Error.ToString() : null);
        Assert.Equal(new Result.Atom(5), admitted.Value);

        static Algorithm.User Root(Algorithm f, Algorithm g)
            => new(null, [], [], [new Property("F", f), new Property("G", g)],
                [new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(5)])]);

        static EvalError Innermost(EvalError error)
        {
            while (error is EvalError.WithContext context) error = context.Inner;
            return error;
        }
    }

    [Fact]
    public void ParentChainPropertyRead_IsCachedByItsOwningScope()
    {
        // A property found on the parent chain is keyed by the declaring scope the lookup
        // level owns (Lean rebuilds the owner from the level): the root read of Inner and the
        // first read of A store one entry each, and the two further reads of A inside Inner
        // hit A's. Sensitive to: a scope wired without its owner (its members go uncached,
        // so A would be requested once and evaluated three times).
        const string source = "A = 1\nInner = { A + A + A }\nInner";
        var cache = new RunScopedZeroArgPropertyResultCache();
        var result = Evaluator.Run(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache, enableLoopOptimization: true);
        Assert.False(result.IsError);
        Assert.Equal(new Result.Atom(3), result.Value);
        var lexical = cache.GetSnapshot().GetAccessKind(ZeroArgPropertyAccessKind.CountedLexical);
        Assert.Equal(4, lexical.Requests);
        Assert.Equal(2, lexical.Stores);
        Assert.Equal(2, lexical.Hits);
    }

    // ── C. Activation and head-scope representation ─────────────────────────

    [Fact]
    public void EnterAlgorithmBody_CarriesTheActivatedHeadScope()
    {
        var body = new Algorithm.User(null, [new CaptureParameterPattern("x"), new CaptureParameterPattern("f")], [], [],
            [new Expr.Param("x")]);
        var ctx = Evaluator.EvalCtx.Empty.Push(new Algorithm.User(null, [], [], [], []));
        var callee = new Algorithm.User(null, [], [], [], [new Expr.Num(9)]);
        var callerCtx = ctx.WithAlgEnv([("f", callee, null), ("f", new Algorithm.Builtin(BuiltinId.count), null), ("g", callee, null)]);
        ValEnv values = [("x", new Result.Atom(1)), ("y", new Result.Atom(2)), ("x", new Result.Atom(3))];

        var entered = Evaluator.EnterAlgorithmBody(body, callerCtx, values);
        Assert.Same(body, entered.Head);
        var head = Assert.IsType<ScopeCtx>(entered.HeadScope);
        Assert.Same(body, head.Owner);
        Assert.Same(body.Declaration, head.Declaration);
        Assert.Equal(["x", "f"], head.Parameters);
        Assert.Same(body.Opens, head.Opens);
        Assert.Same(body.Properties, head.Properties);
        Assert.Null(head.Parent);

        // The activation keeps the FIRST binding of each owned name on every tier, and
        // nothing else; a second entry is a distinct activation.
        var activation = Assert.IsType<ParameterActivation>(head.Activation);
        Assert.Equal([("x", new Result.Atom(1))], activation.Values);
        Assert.Equal([("f", callee, (EvalError?)null)], activation.Algorithms);
        Assert.Empty(activation.Counted);
        Assert.NotSame(activation, Evaluator.EnterAlgorithmBody(body, callerCtx, values).HeadScope!.Activation);

        // A parameterless body and every plain push carry no head scope.
        Assert.Null(Evaluator.EnterAlgorithmBody(callee, callerCtx, values).HeadScope);
        Assert.Null(entered.Push(callee).HeadScope);
        Assert.Same(head, entered.WithAlgEnv([]).HeadScope);
        Assert.Same(head, entered.WithCountedParamEnv([]).HeadScope);
        Assert.Same(head, entered.WithZeroArgPropertyResultCache(new RunScopedZeroArgPropertyResultCache()).HeadScope);
    }

    [Fact]
    public void ParameterActivation_CapturesFirstBindingPerOwnedName_OnEveryTier()
    {
        var wide = Enumerable.Range(0, 12).Select(index => $"p{index}").ToArray();
        ValEnv values = [("p3", new Result.Atom(3)), ("q", new Result.Atom(0)), ("p3", new Result.Atom(30)), ("p11", new Result.Atom(11))];
        var counted = Evaluator.EvalCtx.Empty.WithCountedParamEnv(
            [("p0", new Evaluator.CountedResult(new Result.Atom(7), 1)), ("zz", new Evaluator.CountedResult(new Result.Atom(8), 1))]);

        var activation = ParameterActivation.Capture(wide, counted, values);
        Assert.Equal([("p3", new Result.Atom(3)), ("p11", new Result.Atom(11))], activation.Values);
        Assert.Empty(activation.Algorithms);
        Assert.Equal(["p0"], activation.Counted.Select(binding => binding.Name));

        Assert.Empty(ParameterActivation.Capture([], counted, values).Values);
        Assert.Empty(ParameterActivation.Capture(["none"], counted, values).Values);
    }

    // ── D. Traversal: ownership is a back-reference, not an AST edge ────────

    [Fact]
    public void StructuralPreflight_NeverFollowsScopeOwnership()
    {
        // A scope whose owner points back at the scope's own subtree (as every evaluator-wired
        // scope's owner does through Parent) is neither a cycle nor extra depth to the
        // preflight, which enumerates exactly Parent, Opens, and Properties.
        var parent = new ScopeCtx(null, [], []);
        var owner = new Algorithm.User(parent, [new CaptureParameterPattern("n")], [], [], [new Expr.Param("n")]);
        var scope = new ScopeCtx(parent, [], [new Property("P", owner)], ["n"])
        {
            Owner = owner,
            Activation = ParameterActivation.Capture(["n"], Evaluator.EvalCtx.Empty, [("n", new Result.Atom(1))]),
        };
        var cyclicOwner = owner with { Parent = scope };
        var selfOwned = scope with { Owner = cyclicOwner };

        var children = new List<object>();
        for (var index = 0; AstStructuralPreflight.TryGetChild(selfOwned, index, out var child); index++)
            children.Add(child);
        Assert.Equal([parent, owner], children);

        var wired = owner with { Parent = selfOwned };
        Assert.Null(AstStructuralPreflight.Check(wired, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines));
        Assert.False(Evaluator.Run(new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("W", wired)],
            [new Expr.Call(new Expr.Resolve("W"), [new Expr.Num(4)])]))).IsError);
    }

    // ── E. Lifetime: a completed run roots nothing ──────────────────────────

    [Fact]
    public void CompletedRun_LeavesItsAlgorithmsAndScopesCollectible()
    {
        var (root, scope, activation) = RunAndForget();
        for (var attempt = 0; attempt < 5 && (root.IsAlive || scope.IsAlive || activation.IsAlive); attempt++)
        {
            GC.Collect();
            GC.WaitForPendingFinalizers();
            GC.Collect();
        }

        Assert.False(root.IsAlive, "the evaluated root algorithm stayed reachable after the run");
        Assert.False(scope.IsAlive, "an evaluator-wired scope stayed reachable after the run");
        Assert.False(activation.IsAlive, "a parameter activation stayed reachable after the run");
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (WeakReference Root, WeakReference Scope, WeakReference Activation) RunAndForget()
    {
        const string source = "Outer(n) = {\n  Inner = { public X = n }\n  Outer.Inner.X\n}\nOuter(5)";
        var root = SourceProvenance.ParseValid(source).Root;
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.Equal(new Result.Atom(5), result.Value);

        // A scope and activation exactly as the evaluator mints them for Outer(5).
        var outer = Assert.Single(root.Properties).Value;
        var entered = Evaluator.EnterAlgorithmBody(outer, Evaluator.EvalCtx.Empty.Push(root), [("n", new Result.Atom(5))]);
        var scope = entered.HeadScope!;
        return (new WeakReference(root), new WeakReference(scope), new WeakReference(scope.Activation));
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    private static async Task<IReadOnlyList<Decimal128>> Atoms(string source, int path)
    {
        var result = await Run(source, path);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        return result.Value.Value.ToAtoms();
    }

    /// <summary>0: synchronous generic; 1: synchronous optimized; 2: genuinely suspending async twin.</summary>
    private static async Task<EvalResult<Evaluator.CountedResult>> Run(string source, int path)
    {
        var ast = AsyncEvaluationHarness.Ast(source);
        if (path != 2)
            return Evaluator.RunCountedObserved(ast, enableOptimizations: path == 1).Result;

        // An async cache forces the twin family; a program with property reads suspends at
        // each one, and the sync seam member must never be consulted.
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var (result, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache));
        Assert.Equal(0, cache.SyncAccesses);
        return result;
    }
}
