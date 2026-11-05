using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// B3-5★ review regressions (independent review, checkpoint 2, 2026-11-03): each pins a defect the review found in the
/// first selection candidate, in the shape it was found, plus the independent oracle the review asked for — rule G6
/// applied to a whole equation system at once, against the selector's components, local pass and joint regions.
/// </summary>
public sealed class SignatureSelectionReviewRegressionTests
{
    private const string Host = "modules.example";

    private static Algorithm.User Block(IReadOnlyList<Property> properties, params Expr[] rows)
        => new(null, [], [], properties, new OutputBundle(rows));

    // ── Closed bare forwarding rewrites the block it forwards into ──────────────────────────────────

    /// <summary>
    /// <c>F(x) = { public G(x) = H + 0 }.G</c> forwards F's <c>x</c> to the block's member: the block is REWRITTEN first,
    /// so the member reads <c>H(x) + 0</c> — never the written <c>H + 0</c>, whose zero-argument demand is H's arity error.
    /// </summary>
    [Fact]
    public async Task ClosedBareForwarding_RewritesTheBlockItForwardsInto()
    {
        const string Source = "H = x + 1\nF(x) = { public G(x) = H + 0 }.G\n";
        var observation = await SixRouteAgreement.OnEveryRouteAsync(Source + "F(4)");
        Assert.True(observation is { Kind: "ok", Value: "5" }, observation.ToString());

        var f = Assert.Single(SourceProvenance.ParseValid(Source + "0").Root.Properties, property => property.Name == "F").Value;
        var block = FindBlock(Assert.Single(f.Output));
        var member = Assert.Single(block.Properties, property => property.Name == "G").Value;
        var row = Assert.IsType<Expr.Binary>(Assert.Single(member.Output));
        var call = Assert.IsType<Expr.Call>(row.Left);
        Assert.Equal("H", Assert.IsType<Expr.Resolve>(call.Function).Name);
        Assert.Equal("x", Assert.IsType<Expr.Param>(Assert.Single(call.Args)).Name);

        static Algorithm FindBlock(Expr expr)
        {
            var pending = new Stack<object>([expr]);
            while (pending.TryPop(out var node))
            {
                if (node is Expr.AlgorithmExpr found)
                    return found.Algorithm;
                for (var i = 0; AstStructuralPreflight.TryGetChild(node, i, out var child); i++)
                    pending.Push(child);
            }

            throw new InvalidOperationException("The forwarding row has no block.");
        }
    }

    // ── A region served from another context's processing completes what is below it ─────────────

    /// <summary>
    /// ONE host-built body <c>Shared = { public Q = Need + 0 ⏎ 0 }</c> under two declaring contexts (<c>Left.S</c>,
    /// <c>Right.S</c>): the resolver processes it once and serves <c>Right.S</c> from that processing, so
    /// <c>R = Right.S.Q</c> — whose target lies below the served context — gets a completed target, a completed structure
    /// cell and completed contextual facts, through the region's counterpart: never a pending publication, and never one
    /// publication per path of the shared graph.
    /// </summary>
    [Fact]
    public void ARegionServedFromAnotherContext_CompletesTheTargetsAndFactsBelowIt()
    {
        var need = new Algorithm.User(null, [new CaptureParameterPattern("p")], [], [], new OutputBundle([new Expr.Param("p")]))
        {
            HasExplicitParameterList = true,
        };
        var shared = Block([new Property("Q", Block([], new Expr.Binary(BinaryOp.Add, new Expr.Resolve("Need"), new Expr.Num(0))), IsPublic: true)],
            new Expr.Num(0));
        var right = Block([new Property("S", shared, IsPublic: true)], new Expr.Num(0));
        var root = Block(
            [
                new Property("Need", need),
                new Property("Left", Block([new Property("S", shared, IsPublic: true)], new Expr.Num(0))),
                new Property("Right", right),
                new Property("R", Block([], new Expr.DotCall(new Expr.DotCall(new Expr.Resolve("Right"), "S"), "Q"))),
            ],
            new Expr.Call(new Expr.Resolve("R"), new OutputBundle([new Expr.Num(5)])));

        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root, diagnostics: diagnostics);
        Assert.Equal(0, diagnostics.ReportedCount);

        var r = Assert.IsType<Algorithm.Alias>(Assert.Single(resolved.Properties, property => property.Name == "R").Value);
        Assert.True(r.IsReference);
        Assert.NotNull(r.ResolvedTarget);
        Assert.False(r.ResolvedTargetCell?.IsPending ?? false, "R's target is pending on a context below a served region.");
        Assert.False(r.ResolvedStructureCell?.IsPending ?? false, "R's structure is pending on a context below a served region.");
        Assert.Equal(["p"], r.ResolvedTarget!.Signature.Signature!.ParameterNames);
        var processedQ = Assert.IsType<Algorithm.User>(r.ResolvedTarget.Algorithm);
        Assert.Equal(["p"], processedQ.Params);

        var publication = resolved.CompletedStructure!;
        var graph = publication.Facts;
        var rKey = graph.Child(publication.Entry!, r)!;
        var receiver = graph.Facts(rKey)!.Receiver;
        Assert.Equal(StaticFactKind.Structure, receiver.Kind);
        Assert.Same(processedQ, graph.Facts(receiver.Target!)!.Body);

        var rightKey = graph.Child(publication.Entry!, Assert.Single(resolved.Properties, property => property.Name == "Right").Value)!;
        var leftKey = graph.Child(publication.Entry!, Assert.Single(resolved.Properties, property => property.Name == "Left").Value)!;
        var rightS = graph.Member(rightKey, "S")!;
        var leftS = graph.Member(leftKey, "S")!;
        Assert.Same(Assert.Single(resolved.Properties, property => property.Name == "Left").Value.Properties.Single().Value,
            Assert.Single(resolved.Properties, property => property.Name == "Right").Value.Properties.Single().Value);
        var rightQ = graph.Member(rightS, "Q")!;
        var leftQ = graph.Member(leftS, "Q")!;
        Assert.Same(rightQ, receiver.Target);
        Assert.Same(processedQ, graph.Facts(rightQ)!.Body);
        Assert.Same(processedQ, graph.Facts(leftQ)!.Body);

        // Review checkpoint 3: the served context's facts are its OWN — the processed body is shared, its contextual
        // selections and declaring identity are not.
        Assert.NotSame(leftQ, rightQ);
        Assert.Same(rightQ, graph.Facts(rightQ)!.Open.Target);
        Assert.Same(leftQ, graph.Facts(leftQ)!.Open.Target);
        Assert.Same(rightQ, graph.Facts(rightQ)!.Receiver.Target);
        Assert.NotEqual(graph.Facts(leftQ)!.Open.Identity, graph.Facts(rightQ)!.Open.Identity);
        Assert.Equal(receiver.Identity, graph.Facts(rightQ)!.Open.Identity);

        var value = Evaluator.RunFlat(new Expr.AlgorithmExpr(resolved));
        Assert.False(value.IsError, value.IsError ? value.Error.ToString() : "");
        Assert.Equal([(Decimal128)5], value.Value);
    }

    /// <summary>
    /// Review checkpoint 3: a deferred unit reads an EARLIER unit's completion below a region that unit served from
    /// another context — even once the unit has registered the context itself (every new key gets an empty slot).
    /// </summary>
    [Fact]
    public void AFrozenServedRegion_GivesTheForkTheEarlierView_OnceTheForkRegistersTheContext()
    {
        var limits = new StaticQueryLimits(1_000_000, 4, 200_000, 4_000_000);
        var parsed = (Algorithm.User)SourceProvenance.ParseSyntaxValidRoot(
            "Left = {\n    public S = {\n        public Q = 7\n        0\n    }\n    0\n}\nRight = {\n    public S = 0\n    0\n}\nF(x) = x\n0");
        var left = parsed.Properties.Single(property => property.Name == "Left").Value;
        var shared = left.Properties.Single().Value;
        var q = shared.Properties.Single().Value;
        var rightWritten = (Algorithm.User)parsed.Properties.Single(property => property.Name == "Right").Value;
        var right = rightWritten with { Properties = [rightWritten.Properties.Single() with { Value = shared }] };
        var root = parsed with { Properties = [.. parsed.Properties.Select(property => property.Name == "Right" ? property with { Value = right } : property)] };

        var operation = new StaticStructureOperation(root, limits);
        var leftKey = operation.ContextOf(operation.Root, left);
        var leftS = operation.ContextOf(leftKey, shared);
        var leftQ = operation.ContextOf(leftS, q);
        var rightKey = operation.ContextOf(operation.Root, right);
        var rightS = operation.ContextOf(rightKey, shared);
        foreach (var (key, body) in new (StaticScopeKey, Algorithm)[] { (leftKey, left), (leftS, shared), (leftQ, q), (rightKey, right), (rightS, shared) })
        {
            operation.Publish(key, StaticPublicationStage.Detected, body);
            operation.Publish(key, StaticPublicationStage.Resolved, body);
        }

        operation.AliasResolvedRegion(rightS, leftS);
        operation.Publish(operation.Root, StaticPublicationStage.Detected, root);
        operation.Publish(operation.Root, StaticPublicationStage.Resolved, root);
        var fork = operation.Freeze().Materialize(operation.Root, parsed.Properties.Single(property => property.Name == "F").Value,
            new Pattern.Bind("x"), limits);

        var rightQ = fork.ContextOf(rightS, q);
        Assert.NotSame(leftQ, rightQ);
        Assert.Same(q, fork.EarlierResolvedView(rightQ));
        Assert.Same(q, fork.ResolvedView(rightQ));
        Assert.Null(fork.Published(rightQ, StaticPublicationStage.Resolved));
    }

    // ── Every context below a served region has completed facts of its own (review checkpoint 3b) ─────

    /// <summary>
    /// A host-built root through detection (or, <paramref name="nameResolved"/>, the name-resolved host admission), resolution
    /// and exposure, which seals its completed facts.
    /// </summary>
    private static Algorithm Elaborate(Algorithm.User root, bool nameResolved = false)
    {
        var diagnostics = new DiagnosticBag();
        var resolved = nameResolved
            ? ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root, diagnostics: diagnostics)
            : ImplicitArgumentResolver.ResolvePrevalidated(ParameterDetector.DetectPrevalidated(root, diagnostics: diagnostics));
        Assert.Equal(0, diagnostics.ReportedCount);
        var exposed = PropertyExposureResolver.Resolve(resolved, observations: null);
        Assert.True(exposed.CompletedStructure!.Facts.IsSealed);
        return exposed;
    }

    /// <summary>The completed keys of the members <paramref name="names"/>, one inside the other, from <paramref name="owner"/>.</summary>
    private static StaticScopeKey[] MemberPath(CompletedStaticStructures graph, StaticScopeKey owner, params string[] names)
    {
        var keys = new StaticScopeKey[names.Length];
        for (var i = 0; i < names.Length; i++)
            owner = keys[i] = graph.Member(owner, names[i]) ?? throw new InvalidOperationException($"No completed member '{names[i]}' at depth {i}.");
        return keys;
    }

    /// <summary>The bodies of the members <paramref name="names"/>, one inside the other, from <paramref name="owner"/>.</summary>
    private static Algorithm[] WrittenPath(Algorithm owner, params string[] names)
    {
        var bodies = new Algorithm[names.Length];
        for (var i = 0; i < names.Length; i++)
            owner = bodies[i] = owner.Properties.Single(property => property.Name == names[i]).Value;
        return bodies;
    }

    private static Expr MemberRead(string head, params string[] members)
        => members.Aggregate((Expr)new Expr.Resolve(head), (receiver, member) => new Expr.DotCall(receiver, member));

    /// <summary>The branch body's key, then its members' keys along <paramref name="names"/>.</summary>
    private static StaticScopeKey[] BranchPath(CompletedStructurePublication publication, CondBranch branch, params string[] names)
    {
        var body = publication.Facts.Child(publication.Entry!, branch.Body, branch.Pattern)
            ?? throw new InvalidOperationException("The branch body has no completed context.");
        return [body, .. MemberPath(publication.Facts, body, names)];
    }

    /// <summary>
    /// Review checkpoint 3b: ONE host-built, name-resolved body <c>S = { public Q = { public V = { public W = 1 ⏎ public T =
    /// Top ⏎ 0 } ⏎ public U = V ⏎ 0 } ⏎ 0 }</c> under <c>Left</c> and <c>Right</c>. Resolution processes it once and serves
    /// <c>Right.S</c> from that processing, while exposure copies <c>Right.S</c>'s subtree; every context below
    /// <c>Right.S</c>, however deep, still has completed facts of its OWN: one key per context by every route (a key another
    /// unit or a consumer constructs reads the same facts), the copy the exposed tree holds there, its own declaring identity,
    /// and its selections re-based onto it — a target inside the region is this occurrence's context, one outside it
    /// (<c>Top</c>) the same declaration from both occurrences.
    /// </summary>
    [Fact]
    public void EveryContextBelowAServedRegion_HasCompletedFactsOfItsOwn()
    {
        var v = Block([new Property("W", Block([], new Expr.Num(1)), IsPublic: true), new Property("T", Block([], new Expr.Resolve("Top")), IsPublic: true)],
            new Expr.Num(0));
        var q = Block([new Property("V", v, IsPublic: true), new Property("U", Block([], new Expr.Resolve("V")), IsPublic: true)], new Expr.Num(0));
        var shared = Block([new Property("Q", q, IsPublic: true)], new Expr.Num(0));
        var right = Block([new Property("S", shared, IsPublic: true)], new Expr.Num(0));
        var root = Block(
            [
                new Property("Top", Block([new Property("K", Block([], new Expr.Num(2)), IsPublic: true)], new Expr.Num(0))),
                new Property("Left", Block([new Property("S", shared, IsPublic: true)], new Expr.Num(0))),
                new Property("Right", right),
            ],
            MemberRead("Right", "S", "Q", "V", "T", "K"), MemberRead("Right", "S", "Q", "U", "W"));

        var exposed = Elaborate(root, nameResolved: true);
        var publication = exposed.CompletedStructure!;
        var graph = publication.Facts;
        string[] path = ["S", "Q", "V", "W"];
        var leftKey = graph.Member(publication.Entry!, "Left")!;
        var rightKey = graph.Member(publication.Entry!, "Right")!;
        var leftKeys = MemberPath(graph, leftKey, path);
        var rightKeys = MemberPath(graph, rightKey, path);
        Assert.True(graph.IsReach(rightKeys[0]), "Right.S is not served from Left.S's processing, so nothing below it is projected.");
        var leftBodies = WrittenPath(exposed.Properties.Single(property => property.Name == "Left").Value, path);
        var rightBodies = WrittenPath(exposed.Properties.Single(property => property.Name == "Right").Value, path);
        Assert.NotSame(leftBodies[1], rightBodies[1]);
        var owners = DeclaringOwners.Root.Inside(root).Inside(right);
        for (var depth = 0; depth < path.Length; depth++)
        {
            var leftFacts = graph.Facts(leftKeys[depth])!;
            var rightFacts = graph.Facts(rightKeys[depth])!;
            Assert.NotSame(leftKeys[depth], rightKeys[depth]);
            Assert.Same(leftBodies[depth], leftFacts.Body);
            Assert.Same(rightBodies[depth], rightFacts.Body);
            // Each occurrence's copy has a context of its own in the context-free body index.
            Assert.Same(leftKeys[depth], graph.ExactContext(leftBodies[depth])!.Key);
            Assert.Same(rightKeys[depth], graph.ExactContext(rightBodies[depth])!.Key);
            Assert.Same(rightKeys[depth], graph.Child(depth == 0 ? rightKey : rightKeys[depth - 1], rightBodies[depth]));
            Assert.Same(rightKeys[depth], rightFacts.Open.Target);
            Assert.Same(rightKeys[depth], rightFacts.Receiver.Target);
            Assert.Equal(OpenProviderIdentity.DeclaredIn(rightBodies[depth], owners), rightFacts.Open.Identity);
            Assert.NotEqual(leftFacts.Open.Identity, rightFacts.Open.Identity);
            owners = owners.Inside(rightBodies[depth]);
        }

        // A selection outside the region is the same declaration from both occurrences; one inside it is the occurrence's own.
        var top = graph.Member(publication.Entry!, "Top")!;
        var leftT = graph.Facts(graph.Member(leftKeys[2], "T")!)!;
        var rightT = graph.Facts(graph.Member(rightKeys[2], "T")!)!;
        Assert.Same(top, leftT.Receiver.Target);
        Assert.Same(top, rightT.Receiver.Target);
        Assert.Equal(leftT.Receiver.Identity, rightT.Receiver.Identity);
        Assert.Same(leftKeys[2], graph.Facts(graph.Member(leftKeys[1], "U")!)!.Receiver.Target);
        Assert.Same(rightKeys[2], graph.Facts(graph.Member(rightKeys[1], "U")!)!.Receiver.Target);

        // Keys this table did not create (another unit's table, a consumer's own construction) name the same contexts.
        var namedQ = new StaticScopeKey(rightKeys[0], rightKeys[1].Declaration);
        var namedV = new StaticScopeKey(namedQ, rightKeys[2].Declaration);
        Assert.Same(graph.Facts(rightKeys[2]), graph.Facts(namedV));
        Assert.Same(rightKeys[3], graph.Member(namedV, "W"));
        Assert.Same(rightKeys[3], graph.Child(namedV, rightBodies[3]));

        var value = Evaluator.RunFlat(new Expr.AlgorithmExpr(exposed));
        Assert.False(value.IsError, value.IsError ? value.Error.ToString() : "");
        Assert.Equal([(Decimal128)2, (Decimal128)1], value.Value);
    }

    /// <summary>
    /// Review checkpoint 3b, in the review's own shape: a host-built family whose literal branches share ONE body
    /// <c>B = { public Q = { public V = { public W = 1 ⏎ 0 } ⏎ public M = Module ⏎ 0 } ⏎ 0 }</c>. Each branch occurrence has
    /// completed facts at every depth under keys of its own; the branch region distinguishes the contexts, never their
    /// declaring identities. Review checkpoint 4: the loaded module <c>M</c> is ONE context wherever it is held — its member
    /// key below a projected <c>Q</c> is the module's own key by every route, never a projected copy.
    /// </summary>
    [Fact]
    public void BranchesSharingOneBody_HaveCompletedFactsAtEveryDepthOfEachOccurrence()
    {
        var module = new Algorithm.User(null, [], [], [new Property("K", Block([], new Expr.Num(7)), IsPublic: true)], new OutputBundle([new Expr.Num(0)]))
        {
            IsModuleElaborated = true,
        };
        var v = Block([new Property("W", Block([], new Expr.Num(1)), IsPublic: true)], new Expr.Num(0));
        var q = Block([new Property("V", v, IsPublic: true), new Property("M", module, IsPublic: true)], new Expr.Num(0));
        var shared = Block([new Property("Q", q, IsPublic: true)], new Expr.Num(0));
        var root = Block(
            [new Property("F", new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(0), shared), new CondBranch(new Pattern.LitInt(1), shared)]))],
            new Expr.Num(0));

        var exposed = Elaborate(root);
        var publication = exposed.CompletedStructure!;
        var graph = publication.Facts;
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(exposed.Properties).Value);
        string[] names = ["Q", "V", "W"];
        var occurrences = family.Branches.Select(branch => BranchPath(publication, branch, names)).ToArray();
        Assert.True(graph.IsReach(occurrences[1][0]), "F(1) is not served from F(0)'s processing, so nothing below it is projected.");
        var owners = DeclaringOwners.Root.Inside(root);
        for (var depth = 0; depth < occurrences[0].Length; depth++)
        {
            Assert.NotSame(occurrences[0][depth], occurrences[1][depth]);
            for (var branch = 0; branch < family.Branches.Count; branch++)
            {
                var body = depth == 0 ? family.Branches[branch].Body : WrittenPath(family.Branches[branch].Body, names[..depth])[^1];
                var facts = graph.Facts(occurrences[branch][depth])!;
                Assert.Same(body, facts.Body);
                Assert.Same(occurrences[branch][depth], facts.Open.Target);
                Assert.Equal(OpenProviderIdentity.DeclaredIn(body, owners), facts.Open.Identity);
                if (depth > 0) Assert.Same(occurrences[branch][depth], graph.Child(occurrences[branch][depth - 1], body));
            }

            owners = owners.Inside(graph.Facts(occurrences[0][depth])!.Body!);
        }

        var moduleKeys = occurrences.Select(keys => graph.Member(keys[1], "M")!).ToArray();
        Assert.Same(moduleKeys[0], moduleKeys[1]);
        Assert.Same(graph.PreludeKey, moduleKeys[0].Parent);
        for (var branch = 0; branch < family.Branches.Count; branch++)
        {
            var exposedModule = WrittenPath(family.Branches[branch].Body, "Q", "M")[^1];
            Assert.Same(moduleKeys[0], graph.Child(occurrences[branch][1], exposedModule));
        }
    }

    /// <summary>
    /// Review checkpoint 4: one family whose many literal branches share ONE body serves every later branch from the first;
    /// each occurrence still has completed facts under its own keys, and the shared body names no unique context.
    /// </summary>
    [Fact]
    public void ManyBranchesSharingOneBody_EachHaveTheirOwnCompletedFacts()
    {
        const int Branches = 64;
        var shared = Block([new Property("Q", Block([new Property("V", Block([], new Expr.Num(1)), IsPublic: true)], new Expr.Num(0)), IsPublic: true)],
            new Expr.Num(0));
        var root = Block(
            [new Property("F", new Algorithm.Conditional(null, [], [.. Enumerable.Range(0, Branches).Select(branch => new CondBranch(new Pattern.LitInt(branch), shared))]))],
            new Expr.Num(0));

        var exposed = Elaborate(root);
        var publication = exposed.CompletedStructure!;
        var graph = publication.Facts;
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(exposed.Properties).Value);
        var occurrences = family.Branches.Select(branch => BranchPath(publication, branch, "Q", "V")).ToArray();
        Assert.Equal(Branches - 1, occurrences.Count(keys => graph.IsReach(keys[0])));
        for (var depth = 0; depth < 3; depth++)
        {
            Assert.Equal(Branches, occurrences.Select(keys => keys[depth]).Distinct(ReferenceEqualityComparer.Instance).Count());
            Assert.All(occurrences, keys => Assert.NotNull(graph.Facts(keys[depth])?.Body));
        }

        Assert.Throws<ArgumentException>(() => graph.ExactContext(graph.Facts(occurrences[0][1])!.Body!));
    }

    /// <summary>
    /// Review checkpoint 4: two DEFINITIONS sharing one declaration (<c>B = A with { … }</c>) as <c>Q.A</c> and <c>Q.B</c> of a
    /// name-resolved body served from another context. Each keeps a context of its own below the served occurrence — its own
    /// key by every route and the copy exposure gave that occurrence — and neither is mistaken for the other's.
    /// </summary>
    [Fact]
    public void DefinitionsSharingADeclaration_BelowAServedRegion_KeepTheirOwnContexts()
    {
        var a = Block([new Property("X", Block([], new Expr.Num(1)), IsPublic: true)], new Expr.Num(1));
        var b = a with { Output = new OutputBundle([new Expr.Num(2)]) };
        Assert.Same(OpenProviderIdentity.DeclarationOf(a), OpenProviderIdentity.DeclarationOf(b));
        var shared = Block([new Property("Q", Block([new Property("A", a, IsPublic: true), new Property("B", b, IsPublic: true)], new Expr.Num(0)), IsPublic: true)],
            new Expr.Num(0));
        var root = Block(
            [
                new Property("Left", Block([new Property("S", shared, IsPublic: true)], new Expr.Num(0))),
                new Property("Right", Block([new Property("S", shared, IsPublic: true)], new Expr.Num(0))),
            ],
            MemberRead("Right", "S", "Q", "A"), MemberRead("Right", "S", "Q", "B"));

        var exposed = Elaborate(root, nameResolved: true);
        var publication = exposed.CompletedStructure!;
        var graph = publication.Facts;
        foreach (var side in new[] { "Left", "Right" })
        {
            var owner = graph.Member(publication.Entry!, side)!;
            var keys = MemberPath(graph, owner, "S", "Q");
            Assert.Equal(side == "Right", graph.IsReach(keys[0]));
            var exposedQ = WrittenPath(exposed.Properties.Single(property => property.Name == side).Value, "S", "Q")[^1];
            var definitions = new[] { "A", "B" }.Select(name => (Key: graph.Member(keys[1], name)!, Body: WrittenPath(exposedQ, name)[^1])).ToArray();
            Assert.NotSame(definitions[0].Key, definitions[1].Key);
            foreach (var (key, body) in definitions)
            {
                Assert.Same(body, graph.Facts(key)!.Body);
                Assert.Same(key, graph.Child(keys[1], body));
                Assert.Same(key, graph.ExactContext(body)!.Key);
                Assert.Same(key, graph.Facts(key)!.Open.Target);
            }
        }

        var value = Evaluator.RunFlat(new Expr.AlgorithmExpr(exposed));
        Assert.False(value.IsError, value.IsError ? value.Error.ToString() : "");
        Assert.Equal([(Decimal128)1, (Decimal128)2], value.Value);
    }

    /// <summary>
    /// Review checkpoint 4b: the same two definitions written as INLINE blocks of <c>Q</c>'s output — no member name to go by —
    /// keep their own contexts on both sides too: retargeting matches each exposed copy through the view it was copied from.
    /// </summary>
    [Fact]
    public void InlineDefinitionsSharingADeclaration_BelowAServedRegion_KeepTheirOwnContexts()
    {
        var a = Block([new Property("X", Block([], new Expr.Num(1)), IsPublic: true)], new Expr.Num(1));
        var b = a with { Output = new OutputBundle([new Expr.Num(2)]) };
        AssertInlineDefinitionsKeepTheirOwnContexts(Block([], new Expr.AlgorithmExpr(a), new Expr.AlgorithmExpr(b), new Expr.Num(0)),
            q => q.Output.Take(2));
    }

    /// <summary>
    /// Review checkpoint 4c: the same inline definitions in <c>Q</c>'s hoisted deconstruction right-hand side — rows detection,
    /// resolution and exposure treat as rows of <c>Q</c> itself — keep their own contexts, in the processed branch and the
    /// branch served from it alike. (The name-resolved host admission cannot elaborate such rows at all, before B3-5★ as
    /// now: it has no detected view for their blocks; so this runs the detection pipeline.)
    /// </summary>
    [Fact]
    public void DeconstructionRowDefinitionsSharingADeclaration_BelowAServedRegion_KeepTheirOwnContexts()
    {
        const string Source = "$deconstruct$0";
        var a = Block([new Property("X", Block([], new Expr.Num(1)), IsPublic: true)], new Expr.Num(1));
        var b = a with { Output = new OutputBundle([new Expr.Num(2)]) };
        var rows = Block([], new Expr.AlgorithmExpr(a), new Expr.AlgorithmExpr(b)) with { AssignmentDeconstructionRowIndex = 0 };
        var shared = Block([new Property("Q", Block([new Property(Source, rows)], new Expr.Num(0)), IsPublic: true)], new Expr.Num(0));
        var root = Block(
            [new Property("F", new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(0), shared), new CondBranch(new Pattern.LitInt(1), shared)]))],
            new Expr.Num(0));

        var exposed = Elaborate(root);
        var publication = exposed.CompletedStructure!;
        var graph = publication.Facts;
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(exposed.Properties).Value);
        var contexts = new List<StaticScopeKey>();
        foreach (var branch in family.Branches)
        {
            var keys = BranchPath(publication, branch, "Q");
            var exposedQ = WrittenPath(branch.Body, "Q")[^1];
            foreach (var row in exposedQ.Properties.Single(property => property.Name == Source).Value.Output)
            {
                var block = Assert.IsType<Expr.AlgorithmExpr>(row).Algorithm;
                var key = graph.Child(keys[1], block);
                Assert.NotNull(key);
                Assert.Same(block, graph.Facts(key)!.Body);
                contexts.Add(key);
            }
        }

        Assert.True(graph.IsReach(BranchPath(publication, family.Branches[1])[0]));
        Assert.Equal(4, contexts.Distinct(ReferenceEqualityComparer.Instance).Count());
    }

    /// <summary>
    /// <paramref name="q"/> as <c>Q</c> of ONE name-resolved body shared by <c>Left.S</c> and <c>Right.S</c>: on both sides, each
    /// inline block <paramref name="blocksOf"/> finds in the exposed <c>Q</c> has a context of its own, by <c>Child</c> and
    /// <c>ExactContext</c> alike, with that exposed block as its body.
    /// </summary>
    private static void AssertInlineDefinitionsKeepTheirOwnContexts(Algorithm.User q, Func<Algorithm, IEnumerable<Expr>> blocksOf)
    {
        var shared = Block([new Property("Q", q, IsPublic: true)], new Expr.Num(0));
        var root = Block(
            [
                new Property("Left", Block([new Property("S", shared, IsPublic: true)], new Expr.Num(0))),
                new Property("Right", Block([new Property("S", shared, IsPublic: true)], new Expr.Num(0))),
            ],
            new Expr.Num(0));

        var exposed = Elaborate(root, nameResolved: true);
        var publication = exposed.CompletedStructure!;
        var graph = publication.Facts;
        var contexts = new List<StaticScopeKey>();
        foreach (var side in new[] { "Left", "Right" })
        {
            var keys = MemberPath(graph, graph.Member(publication.Entry!, side)!, "S", "Q");
            Assert.Equal(side == "Right", graph.IsReach(keys[0]));
            var exposedQ = WrittenPath(exposed.Properties.Single(property => property.Name == side).Value, "S", "Q")[^1];
            foreach (var row in blocksOf(exposedQ))
            {
                var block = Assert.IsType<Expr.AlgorithmExpr>(row).Algorithm;
                var key = graph.Child(keys[1], block);
                Assert.NotNull(key);
                Assert.Same(block, graph.Facts(key)!.Body);
                Assert.Same(key, graph.ExactContext(block)!.Key);
                contexts.Add(key);
            }
        }

        Assert.Equal(4, contexts.Distinct(ReferenceEqualityComparer.Instance).Count());
    }

    /// <summary>
    /// Review checkpoint 4c: a projected context whose providers all lie outside the served region (inline open targets are
    /// rooted at the prelude) shares its counterpart's very provider array — never one copy per occurrence.
    /// </summary>
    [Fact]
    public void ProvidersOutsideTheServedRegion_AreSharedByEveryProjectedOccurrence()
    {
        static Expr Provider(string name, int value)
            => new Expr.AlgorithmExpr(Block([new Property(name, Block([], new Expr.Num(value)), IsPublic: true)], new Expr.Num(0)));
        var q = new Algorithm.User(null, [], [Provider("P1", 1), Provider("P2", 2)], [], new OutputBundle([new Expr.Num(0)]));
        var shared = Block([new Property("Q", q, IsPublic: true)], new Expr.Num(0));
        var root = Block(
            [new Property("F", new Algorithm.Conditional(null, [], [.. Enumerable.Range(0, 8).Select(branch => new CondBranch(new Pattern.LitInt(branch), shared))]))],
            new Expr.Num(0));

        var exposed = Elaborate(root);
        var publication = exposed.CompletedStructure!;
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(exposed.Properties).Value);
        var providers = family.Branches.Select(branch => publication.Facts.Facts(BranchPath(publication, branch, "Q")[1])!.Providers).ToArray();
        Assert.Equal(2, providers[0].Length);
        Assert.All(providers[0], provider => Assert.Equal(StaticFactKind.Structure, provider.Kind));
        var array = System.Runtime.InteropServices.ImmutableCollectionsMarshal.AsArray(providers[0]);
        Assert.All(providers, each => Assert.Same(array, System.Runtime.InteropServices.ImmutableCollectionsMarshal.AsArray(each)));
    }

    /// <summary>
    /// Review checkpoint 4b: many aliases of ONE projected context with many members (<c>R_i = Right.S.Q</c>). Completing their
    /// eligibility reads that context's projected facts again only when what it is projected from changed — never once per
    /// revision of anything else (formerly every revision rebuilt them: Θ(aliases × members)).
    /// </summary>
    [Fact]
    public void ManyAliasesOfOneProjectedContext_ReadItsFactsWithoutRebuildingThemPerRevision()
    {
        const int Members = 50;
        const int Aliases = 50;
        var q = Block([.. Enumerable.Range(0, Members).Select(index => new Property($"M{index}", Block([], new Expr.Num(index)), IsPublic: true))],
            new Expr.Num(0));
        var shared = Block([new Property("Q", q, IsPublic: true)], new Expr.Num(0));
        var root = Block(
            [
                new Property("Left", Block([new Property("S", shared, IsPublic: true)], new Expr.Num(0))),
                new Property("Right", Block([new Property("S", shared, IsPublic: true)], new Expr.Num(0))),
                .. Enumerable.Range(0, Aliases).Select(index => new Property($"R{index}", Block([], MemberRead("Right", "S", "Q")))),
            ],
            new Expr.Num(0));

        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root, diagnostics: diagnostics);
        Assert.Equal(0, diagnostics.ReportedCount);
        var publication = resolved.CompletedStructure!;
        var graph = publication.Facts;
        var rightQ = MemberPath(graph, graph.Member(publication.Entry!, "Right")!, "S", "Q")[1];
        Assert.True(graph.IsReach(rightQ.Parent!));
        var builds = graph.ProjectedFactsBuilds;
        Assert.All(Enumerable.Range(0, Aliases), index =>
            Assert.Same(rightQ, graph.Facts(graph.Member(publication.Entry!, $"R{index}")!)!.Receiver.Target));
        Assert.InRange(builds, 1, 4);
    }

    /// <summary>
    /// Review checkpoint 3b: sealed facts serve parallel readers. Readers racing to the first projection of each context below
    /// a served branch all receive the same key and the same facts at every depth.
    /// </summary>
    [Fact]
    public void ParallelReadersBelowAServedRegion_ReceiveTheSameKeysAndFacts()
    {
        const int Depth = 6;
        const int Readers = 8;
        Algorithm body = Block([], new Expr.Num(1));
        var names = Enumerable.Range(1, Depth).Select(level => $"Q{level}").ToArray();
        for (var level = Depth - 1; level >= 0; level--)
            body = Block([new Property(names[level], body, IsPublic: true)], new Expr.Num(0));
        var root = Block(
            [new Property("F", new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(0), body), new CondBranch(new Pattern.LitInt(1), body)]))],
            new Expr.Num(0));
        var exposed = Elaborate(root);
        var publication = exposed.CompletedStructure!;
        var graph = publication.Facts;
        var served = Assert.IsType<Algorithm.Conditional>(Assert.Single(exposed.Properties).Value).Branches[1];

        var results = new (StaticScopeKey[] Keys, CompletedStaticStructures.BodyFacts[] Facts)[Readers];
        var failures = new Exception?[Readers];
        using var start = new Barrier(Readers);
        var threads = Enumerable.Range(0, Readers).Select(reader => new Thread(() =>
        {
            try
            {
                start.SignalAndWait();
                var keys = BranchPath(publication, served, names);
                results[reader] = (keys, keys.Select(key => graph.Facts(key)!).ToArray());
            }
            catch (Exception exception)
            {
                failures[reader] = exception;
            }
        })).ToArray();
        foreach (var thread in threads) thread.Start();
        foreach (var thread in threads) thread.Join();

        Assert.All(failures, failure => Assert.Null(failure));
        Assert.True(graph.IsReach(results[0].Keys[0]));
        for (var reader = 1; reader < Readers; reader++)
            for (var depth = 0; depth <= Depth; depth++)
            {
                Assert.Same(results[0].Keys[depth], results[reader].Keys[depth]);
                Assert.Same(results[0].Facts[depth], results[reader].Facts[depth]);
            }
    }

    /// <summary>
    /// Review checkpoint 3b, at the table itself: a later unit inherits an earlier unit's reach and projects below it under its
    /// own keys, while the earlier unit's keys read the same contexts' facts there; reading a sealed table's projections never
    /// changes what a later unit inherits and is charged for.
    /// </summary>
    [Fact]
    public void ALaterUnit_ProjectsBelowAnEarlierUnitsReach_AndEarlierKeysReadItsFacts()
    {
        var v = Block([], new Expr.Num(1));
        var q = Block([new Property("V", v, IsPublic: true)], new Expr.Num(0));
        var s = Block([new Property("Q", q, IsPublic: true)], new Expr.Num(0));
        var left = Block([new Property("S", s, IsPublic: true)], new Expr.Num(0));
        var right = Block([new Property("S", s, IsPublic: true)], new Expr.Num(0));
        var prelude = new StaticScopeKey(null, OpenProviderIdentity.RootLevelDeclaration);
        var leftKey = new StaticScopeKey(prelude, OpenProviderIdentity.DeclarationOf(left));
        var leftS = new StaticScopeKey(leftKey, OpenProviderIdentity.DeclarationOf(s));
        var leftQ = new StaticScopeKey(leftS, OpenProviderIdentity.DeclarationOf(q));
        var leftV = new StaticScopeKey(leftQ, OpenProviderIdentity.DeclarationOf(v));
        var rightKey = new StaticScopeKey(prelude, OpenProviderIdentity.DeclarationOf(right));
        var rightS = new StaticScopeKey(rightKey, OpenProviderIdentity.DeclarationOf(s));
        var rightQ = new StaticScopeKey(rightS, OpenProviderIdentity.DeclarationOf(q));
        CompletedStaticStructures.BodyFacts Facts(StaticScopeKey key, Algorithm body, DeclaringOwners owners, StaticScopeKey? member = null)
        {
            var self = new CompletedStaticStructures.Selection(StaticFactKind.Structure, key, OpenProviderIdentity.DeclaredIn(body, owners));
            var members = member is null ? new Dictionary<string, StaticScopeKey>() : new() { [body.Properties.Single().Name] = member };
            return new(body, self, self, members, new HashSet<string>(), []);
        }

        var earlier = new CompletedStaticStructures(prelude);
        var leftOwners = DeclaringOwners.Root.Inside(left);
        var rightOwners = DeclaringOwners.Root.Inside(right);
        earlier.Add(leftKey, Facts(leftKey, left, DeclaringOwners.Root, leftS));
        earlier.Add(leftS, Facts(leftS, s, leftOwners, leftQ));
        earlier.Add(leftQ, Facts(leftQ, q, leftOwners.Inside(s), leftV));
        earlier.Add(leftV, Facts(leftV, v, leftOwners.Inside(s).Inside(q)));
        earlier.SuspendProjection();
        earlier.AddReach(rightS, leftS, OpenProviderIdentity.DeclaredIn(s, rightOwners), OpenProviderIdentity.DeclaredIn(s, leftOwners));
        earlier.Add(rightKey, Facts(rightKey, right, DeclaringOwners.Root, rightS));
        earlier.Add(rightS, Facts(rightS, s, rightOwners, rightQ));
        earlier.AdoptBelowReaches([(rightQ, leftQ)]);
        earlier.Seal();
        var retained = earlier.RetainedStorageUnits;

        var earlierV = earlier.Member(rightQ, "V")!;
        Assert.Same(v, earlier.Facts(earlierV)!.Body);
        Assert.Same(earlierV, earlier.Facts(earlierV)!.Open.Target);
        Assert.Equal(OpenProviderIdentity.DeclaredIn(v, rightOwners.Inside(s).Inside(q)), earlier.Facts(earlierV)!.Open.Identity);
        Assert.Equal(retained, earlier.RetainedStorageUnits);

        var later = new CompletedStaticStructures(prelude, earlier);
        later.Seal();
        Assert.Same(q, later.Facts(rightQ)!.Body);
        var laterV = later.Member(rightQ, "V")!;
        Assert.Same(laterV, later.Child(rightQ, v));
        Assert.Same(later.Facts(laterV), later.Facts(earlierV));
        Assert.Same(laterV, later.Facts(laterV)!.Open.Target);
        Assert.Equal(earlier.Facts(earlierV)!.Open.Identity, later.Facts(laterV)!.Open.Identity);
        Assert.Equal(retained, later.RetainedStorageUnits);
    }

    /// <summary>
    /// Review checkpoint 4e, at the table itself: a reach retains both declaring chains (counted for a later unit by their
    /// length), and the body index's below-a-reach check walks each owner once per build — W contexts under one D-owner
    /// stem that no processing context encloses cost about W + D charged steps, never W × D (nor nothing).
    /// </summary>
    [Fact]
    public void ReachChainsAndTheBodyIndexWalk_AreChargedByTheirLength()
    {
        const int Depth = 64;
        const int Width = 64;
        var budget = new StaticQueryResourceBudget(new(10_000_000, 8, MaxStorageUnits: 10_000_000));
        var prelude = new StaticScopeKey(null, OpenProviderIdentity.RootLevelDeclaration);
        var table = new CompletedStaticStructures(prelude, resources: budget);
        CompletedStaticStructures.BodyFacts Facts(StaticScopeKey key, Algorithm body)
        {
            var self = new CompletedStaticStructures.Selection(StaticFactKind.Structure, key);
            return new(body, self, self, new Dictionary<string, StaticScopeKey>(), new HashSet<string>(), []);
        }

        var shared = Block([], new Expr.Num(0));
        var processed = new StaticScopeKey(prelude, OpenProviderIdentity.DeclarationOf(shared), new Pattern.LitInt(0));
        var reach = new StaticScopeKey(prelude, OpenProviderIdentity.DeclarationOf(shared), new Pattern.LitInt(1));
        table.Add(processed, Facts(processed, shared));
        table.Add(reach, Facts(reach, shared));
        // A stem of Depth owners below the prelude, then Width leaves below its last owner.
        var owner = prelude;
        Algorithm? leaf = null;
        for (var level = 0; level < Depth + Width; level++)
        {
            var body = Block([], new Expr.Num(level));
            var key = new StaticScopeKey(owner, OpenProviderIdentity.DeclarationOf(body));
            table.Add(key, Facts(key, body));
            if (level < Depth) owner = key;
            leaf = body;
        }

        // A 72-declaration chain (the provider, 70 owners, the root level) and a 2-declaration one: 6 + ⌈74 / 8⌉ units.
        var owners = DeclaringOwners.Root;
        for (var level = 0; level < 70; level++) owners = owners.InsideIdentity(new object());
        var retained = table.RetainedStorageUnits;
        table.AddReach(reach, processed, OpenProviderIdentity.DeclaredIn(shared, owners), OpenProviderIdentity.DeclaredIn(shared, DeclaringOwners.Root));
        Assert.Equal(6 + (72 + 2 + 7) / 8, table.RetainedStorageUnits - retained);

        var before = budget.AdapterWork;
        Assert.NotNull(table.ExactContext(leaf!));
        Assert.InRange(budget.AdapterWork - before, Width, 4L * (Width + Depth));
    }

    /// <summary>
    /// Review checkpoint 4f: reaches served one from another chain their projections (the context below the last one is
    /// projected through every earlier one). A read of that context, even with every entry current, validates the whole
    /// chain — and charges each hop, read after read, before the table is sealed.
    /// </summary>
    [Fact]
    public void WarmReadsThroughANestedProjectionChain_ChargeEveryCounterpartHop()
    {
        const int Depth = 16;
        const int Reads = 32;
        var budget = new StaticQueryResourceBudget(new(10_000_000, 8, MaxStorageUnits: 10_000_000));
        var prelude = new StaticScopeKey(null, OpenProviderIdentity.RootLevelDeclaration);
        var table = new CompletedStaticStructures(prelude, resources: budget);
        var child = Block([], new Expr.Num(1));
        var body = Block([new Property("C", child, IsPublic: true)], new Expr.Num(0));
        CompletedStaticStructures.BodyFacts Facts(StaticScopeKey key, Algorithm view, StaticScopeKey? member = null)
        {
            var self = new CompletedStaticStructures.Selection(StaticFactKind.Structure, key);
            var members = member is null ? new Dictionary<string, StaticScopeKey>() : new() { ["C"] = member };
            return new(view, self, self, members, new HashSet<string>(), []);
        }

        // Branch occurrences of one body; occurrence k is served from occurrence k - 1, and each one's C below it.
        var occurrences = Enumerable.Range(0, Depth + 1)
            .Select(index => new StaticScopeKey(prelude, OpenProviderIdentity.DeclarationOf(body), new Pattern.LitInt(index))).ToArray();
        var children = occurrences.Select(occurrence => new StaticScopeKey(occurrence, OpenProviderIdentity.DeclarationOf(child))).ToArray();
        table.Add(children[0], Facts(children[0], child));
        for (var index = 0; index <= Depth; index++)
            table.Add(occurrences[index], Facts(occurrences[index], body, children[index]));
        table.SuspendProjection();
        var identity = OpenProviderIdentity.DeclaredIn(body, DeclaringOwners.Root);
        for (var index = 1; index <= Depth; index++)
            table.AddReach(occurrences[index], occurrences[index - 1], identity, identity);
        table.AdoptBelowReaches([.. Enumerable.Range(1, Depth).Select(index => (children[index], children[index - 1]))]);

        Assert.Same(child, table.Facts(children[Depth])!.Body);
        Assert.Same(children[Depth], table.Facts(children[Depth])!.Open.Target);
        var before = budget.AdapterWork;
        for (var read = 0; read < Reads; read++)
            Assert.Same(child, table.Facts(children[Depth])!.Body);
        Assert.True(budget.AdapterWork - before >= (long)Reads * Depth, $"{budget.AdapterWork - before} charged steps");
    }

    // ── Refusal regions are linear, and report each failure as what it is ──────────────────────────

    private static SignatureSelector.Selection SelectChain(int readers, out int[] refusedAt)
    {
        // E0 reads itself and does not settle; E1..En each read the one before.
        var identities = Enumerable.Range(0, readers + 1).Select(_ => new object()).ToArray();
        var references = Enumerable.Range(0, readers + 1)
            .Select(i => (IReadOnlyList<SignatureEquationReference>)[new SignatureEquationReference(i == 0 ? 0 : i - 1, null, identities[i == 0 ? 0 : i - 1], -1, new Expr.Resolve("r"), "r")])
            .ToArray();
        var closed = new SignatureFact([], null, isLifted: false, composition: null, new CallableSignature("", []));
        SignatureFact Compose(int equation, IReadOnlyList<(int Reference, CallableSignature Signature)> lifted)
        {
            // E0 alternates between two signatures: its completion repeats with period two.
            IReadOnlyList<ParameterPattern> patterns = equation == 0
                ? [new CaptureParameterPattern(lifted.Count > 0 && lifted[0].Signature.ParameterNames[0] == "x" ? "y" : "x")]
                : lifted.Count > 0 ? [new CaptureParameterPattern("x")] : [];
            return new SignatureFact(patterns, null, lifted.Count > 0, null, CallableSignature.FromInferredPatterns($"E{equation}", patterns));
        }

        var selection = new SignatureSelector(references, new bool[readers + 1], Compose, static (_, settled, _) => settled, closed,
            new StaticQueryResourceBudget(StaticQueryLimits.Default), CancellationToken.None).Solve();
        refusedAt = [.. selection.Refusals.SelectMany(static refusal => refusal.Equations)];
        return selection;
    }

    /// <summary>
    /// Review checkpoint 3: a cycle that does not settle, read by a long chain of readers — every reader fails only through it — forms
    /// its joint region in work linear in the chain (formerly one reader closure per failed component, Θ(n²) and
    /// uncharged), and is reported once, at the cycle; the readers are not reported again.
    /// </summary>
    [Fact]
    public void ARefusalRegion_IsFormedInLinearWork_AndReportedAtTheCycleOnly()
    {
        var small = SelectChain(400, out var smallRefused);
        var large = SelectChain(800, out var largeRefused);
        Assert.Equal([0], smallRefused);
        Assert.Equal([0], largeRefused);
        Assert.Equal(SignatureSelectionOutcome.NonSettling, Assert.Single(large.Refusals).Outcome);
        Assert.True(small.RegionVisits > 400, $"Only {small.RegionVisits} region visits were observed.");
        var ratio = (double)large.RegionVisits / small.RegionVisits;
        Assert.True(ratio < 2.6, $"Doubling the readers grew the region work {ratio:F2}x ({small.RegionVisits} -> {large.RegionVisits}).");
    }

    /// <summary>
    /// Review checkpoint 3: two cycles that do not settle, whose cones merely meet (both read <c>X</c>), are one joint region,
    /// but each is reported as what it is, with its own members, never as one group.
    /// </summary>
    [Fact]
    public void IndependentCycles_AreReportedSeparately()
    {
        var parsed = Parser.Parse("X(x) = x\nY(y) = y\nA = B + X\nB = A + Y\nC = D + X\nD = C + Y\n0");
        Assert.Equal(4, parsed.Diagnostics.Count);
        Assert.All(parsed.Diagnostics, diagnostic => Assert.Equal(DiagnosticCode.SelfDependentInferredParameters, diagnostic.Code));
        Assert.Equal(2, parsed.Diagnostics.Count(diagnostic => diagnostic.Message.Contains("'A' and 'B' use one another by name", StringComparison.Ordinal)));
        Assert.Equal(2, parsed.Diagnostics.Count(diagnostic => diagnostic.Message.Contains("'C' and 'D' use one another by name", StringComparison.Ordinal)));
    }

    private const string Oscillator = "X(x) = x\nY(y) = y\nF = G + X\nG = F + Y\n0";

    // ── A refusal inside a loaded module is positioned at its import site ──────────────────────────

    private static RunOptions ModuleOptions(IReadOnlyDictionary<string, string> modules)
        => new()
        {
            AllowedHosts = [Host],
            DownloadCode = (url, _) => ValueTask.FromResult(modules[url]),
        };

    /// <summary>
    /// A module's own cycle that does not settle is reported in the loading document's coordinates: at the
    /// declaration that imports it — never unpositioned, never at the module's own coordinates.
    /// </summary>
    [Theory]
    [InlineData("M = load('https://modules.example/u.kat')\n0", 1, 1, 1, 2)]
    [InlineData("X = 1\nN = 2\n  M = load('https://modules.example/u.kat')\n0", 3, 3, 3, 4)]
    public async Task ASelectionRefusalInAModule_IsReportedAtItsImportSite(string source, int line, int column, int endLine, int endColumn)
    {
        var parsed = await Parser.ParseAsync(source, ModuleOptions(new Dictionary<string, string>
        {
            ["https://modules.example/u.kat"] = "\n\n\n" + Oscillator,
        }));
        Assert.Equal(2, parsed.Diagnostics.Count);
        Assert.All(parsed.Diagnostics, refusal =>
        {
            Assert.Equal(DiagnosticCode.SelfDependentInferredParameters, refusal.Code);
            Assert.Equal(new SourceSpan(line, column, endLine, endColumn), refusal.Span);
        });
    }

    // ── One deferred region, evaluated again ────────────────────────────────────────────────────

    private const string GoodModule = "A(x) = x\nR = { public Q = A + 0 }.Q\n0";

    private static Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlat(Algorithm root, CancellationToken cancellationToken = default)
        => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), limits: null, cancellationToken);

    /// <summary>
    /// The SAME parsed program, evaluated again: a deferred unit whose selection refuses (its module's cycle does not settle) is
    /// refused the same way every time it is selected, publishes nothing, and leaves the other branch's unit — selected
    /// in the same tree afterwards — to select and evaluate normally.
    /// </summary>
    [Fact]
    public async Task ARefusedDeferredUnit_IsRefusedAgain_AndAnotherBranchOfTheSameTreeSucceeds()
    {
        var options = ModuleOptions(new Dictionary<string, string>
        {
            ["https://modules.example/bad.kat"] = Oscillator,
            ["https://modules.example/good.kat"] = GoodModule,
        });
        var parsed = await Parser.ParseAsync(
            "G(0) = {\n    M = load('https://modules.example/bad.kat')\n    M.F(1)\n}\n"
            + "G(n) = {\n    N = load('https://modules.example/good.kat')\n    N.R(n)\n}\nG(Pick)\nPick = 0",
            options);
        Assert.False(parsed.HasErrors, string.Join('\n', parsed.Diagnostics.Select(d => d.Message)));

        for (var attempt = 0; attempt < 2; attempt++)
        {
            var refused = await RunFlat(parsed.Root);
            Assert.True(refused.IsError);
            Assert.Equal(KatLangErrorCode.SelfDependentInferredParameters, refused.Error.Code);
        }

        var other = parsed.Root with
        {
            Properties = parsed.Root.Properties.Select(property => property.Name == "Pick"
                ? property with { Value = Block([], new Expr.Num(4)) }
                : property).ToArray(),
        };
        var selected = await RunFlat(other);
        Assert.False(selected.IsError, selected.IsError ? selected.Error.ToString() : "");
        Assert.Equal([(Decimal128)4], selected.Value);
    }

    /// <summary>
    /// The SAME parsed program, evaluated again after its first evaluation was cancelled while its deferred unit was
    /// being fetched: however far that unit's preparation got before the cancellation was observed, the same tree's
    /// retry selects and evaluates it.
    /// </summary>
    [Fact]
    public async Task ACancelledEvaluation_LeavesTheSameTreesDeferredUnitUsable()
    {
        using var cancellation = new CancellationTokenSource();
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = [Host],
            DownloadCode = (url, _) =>
            {
                if (++downloads == 1)
                    cancellation.Cancel();
                return ValueTask.FromResult(GoodModule);
            },
        };
        var parsed = await Parser.ParseAsync(
            "G(0) = 0\nG(n) = {\n    N = load('https://modules.example/good.kat')\n    N.R(n)\n}\nG(4)",
            options);
        Assert.False(parsed.HasErrors, string.Join('\n', parsed.Diagnostics.Select(d => d.Message)));
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties, property => property.Name == "G").Value);
        var region = Assert.Single(family.Branches, branch => branch.Body.DeferredRegion is not null).Body.DeferredRegion!;

        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => RunFlat(parsed.Root, cancellation.Token));
        var materializedBefore = region.IsMaterialized;

        var retry = await RunFlat(parsed.Root);
        Assert.False(retry.IsError, retry.IsError ? retry.Error.ToString() : "");
        Assert.Equal([(Decimal128)4], retry.Value);
        Assert.True(region.IsMaterialized);
        Assert.Equal(materializedBefore ? 1 : 2, region.MaterializationAttempts);
    }

    /// <summary>
    /// A selection observes its operation's cancellation at every charge: a cancelled selection throws the cancellation,
    /// fails its ledger (nothing that ledger admitted is usable afterwards) and returns nothing to publish.
    /// </summary>
    [Fact]
    public void ACancelledSelection_ThrowsAndPublishesNothing()
    {
        var closed = new SignatureFact([], null, isLifted: false, composition: null, new CallableSignature("", []));
        IReadOnlyList<SignatureEquationReference>[] references = [[], []];
        var ledger = new StaticQueryResourceBudget(StaticQueryLimits.Default);
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var selector = new SignatureSelector(references, [false, false],
            (equation, _) => new SignatureFact([], null, false, null, new CallableSignature($"E{equation}", [])), static (_, settled, _) => settled, closed, ledger, cancellation.Token);
        Assert.ThrowsAny<OperationCanceledException>(() => selector.Solve());
        Assert.True(ledger.IsFailed);
    }

    // ── A reader resolves an ambiguous lower component (research W14u) ──────────────────────────

    private const string Prelude = "Cap(meta op) = op\nId(v) = v\nC(a, *p) = a\nA0 = C + 0\nB(p) = p\nDc(*w) = count(w)\n";

    private static readonly string[] W14uDeclarations =
    [
        "Lx1 = Cap(Id(Hx1 + 0)).Algorithm",
        "Hx1 = Ln1.repeat(A0) + B",
        "Ln1 = Cap(Id(Hn1 + 0)).Algorithm",
        "Hn1 = Lx1.repeat(A0) + B",
        "Lf1 = Cap(Id(Hf1 + 0)).Algorithm",
        "Hf1 = Lf1.repeat(A0) + Lx1.repeat(A0) + B",
    ];

    private static IEnumerable<string[]> Permutations(string[] items)
    {
        if (items.Length <= 1)
        {
            yield return items;
            yield break;
        }

        for (var i = 0; i < items.Length; i++)
        {
            foreach (var rest in Permutations([.. items.Where((_, j) => j != i)]))
                yield return [items[i], .. rest];
        }
    }

    /// <summary>
    /// W14u: the pair {Lx1, Hx1, Ln1, Hn1} alone has two grounded classifications (Lx1 or Ln1 a calculation), and its
    /// reader {Lf1, Hf1} refutes one of them (with Ln1 a calculation, Hf1 would need Lf1 to be one too, which it never
    /// is). Rule G6 over the whole table selects Lx1 — jointly, never by the pair on its own — in every declaration order:
    /// Lx1(p), Hx1(p), Hn1(*p), Hf1(*p), and Ln1, Lf1 runtime references.
    /// </summary>
    [Fact]
    public void AReader_ResolvesAnAmbiguousLowerComponent_InEveryOrder()
    {
        var order = 0;
        foreach (var declarations in Permutations(W14uDeclarations))
        {
            // Every sixth of the 720 orders: each declaration first in some of them.
            if (order++ % 6 != 0)
                continue;
            var root = SourceProvenance.ParseValid(Prelude + "Outer(a) = {\n    " + string.Join("\n    ", declarations) + "\n    0\n}\n0").Root;
            var outer = Assert.Single(root.Properties, property => property.Name == "Outer").Value;
            Algorithm Member(string name) => Assert.Single(outer.Properties, property => property.Name == name).Value;
            var context = string.Join(" | ", declarations);
            Assert.True(Member("Lx1") is Algorithm.User { Params: ["p"] }, context);
            Assert.True(Member("Hx1") is Algorithm.User { Params: ["p"] }, context);
            Assert.True(Member("Hn1") is Algorithm.User { Params: ["p"] }, context);
            Assert.True(Member("Hf1") is Algorithm.User { Params: ["p"] }, context);
            Assert.True(Member("Ln1") is Algorithm.Alias { HasRuntimeTarget: true }, context);
            Assert.True(Member("Lf1") is Algorithm.Alias { HasRuntimeTarget: true }, context);
            Assert.Equal(ParameterKind.Collecting, Assert.Single(Member("Hn1").ParameterPatterns.OfType<CaptureParameterPattern>()).Kind);
        }

        Assert.Equal(720, order);
    }

    /// <summary>
    /// A completed cycle inside a joint cone is read by the local pass and again by the joint solve. Both readings must end
    /// in one list per fact, or a reader's selected composition and the rewrite would disagree by reference (independent
    /// review, checkpoint 1). The added <c>p</c> changes no signature, only what the region reads.
    /// </summary>
    [Fact]
    public void ACompletedCycleInAJointCone_IsOneList()
    {
        string[] added = ["P(p) = p", "Q(p) = p", "R = S + P", "S = R + Q"];
        var declarations = W14uDeclarations.Select(static row => row.StartsWith("Hf1", StringComparison.Ordinal) ? row + " + R" : row).Concat(added).ToArray();
        foreach (var order in new[] { declarations, [.. declarations.Reverse()] })
        {
            var root = SourceProvenance.ParseValid(Prelude + "Outer(a) = {\n    " + string.Join("\n    ", order) + "\n    0\n}\n0").Root;
            var outer = Assert.Single(root.Properties, property => property.Name == "Outer").Value;
            var hf1 = ParameterPattern.FlattenCaptures(Assert.Single(outer.Properties, property => property.Name == "Hf1").Value.ParameterPatterns);
            Assert.NotNull(Assert.Single(hf1, static capture => capture.Name == "p"));
        }
    }

    // ── The independent oracle: rule G6 over a whole system ────────────────────────────────────

    /// <summary>A reference of a synthetic equation: an equation target or an external signature, maybe guarded.</summary>
    private sealed record SyntheticReference(int Target, int External, int Guard);

    private sealed record SyntheticSystem(string[][] Own, SyntheticReference[][] References, bool[] IsLink)
    {
        public int Count => Own.Length;

        public override string ToString()
            => string.Join("; ", Enumerable.Range(0, Count).Select(i =>
                $"{(IsLink[i] ? "L" : "E")}{i}({string.Join(",", Own[i])}) = "
                + string.Join(" ", References[i].Select(r => (r.Target >= 0 ? $"E{r.Target}" : $"X{r.External}") + (r.Guard >= 0 ? $"?L{r.Guard}" : "")))));
    }

    // External signatures: X0 accepts zero arguments (never lifted), X1 and X2 require one each.
    private static readonly string[][] Externals = [[], ["e1"], ["e2"]];

    private static SyntheticSystem RandomSystem(Random random)
    {
        var count = random.Next(1, 7);
        var isLink = new bool[count];
        var links = new List<int>();
        for (var i = 0; i < count; i++)
        {
            if (links.Count < 4 && random.NextDouble() < 0.4)
            {
                isLink[i] = true;
                links.Add(i);
            }
        }

        var own = new string[count][];
        var references = new SyntheticReference[count][];
        for (var i = 0; i < count; i++)
        {
            own[i] = random.NextDouble() < 0.4 ? [$"o{i}"] : [];
            references[i] = new SyntheticReference[random.Next(0, 4)];
            for (var r = 0; r < references[i].Length; r++)
            {
                var guard = links.Count > 0 && random.NextDouble() < 0.4 ? links[random.Next(links.Count)] : -1;
                references[i][r] = random.NextDouble() < 0.7
                    ? new SyntheticReference(random.Next(count), -1, guard)
                    : new SyntheticReference(-1, random.Next(Externals.Length), guard);
            }
        }

        return new SyntheticSystem(own, references, isLink);
    }

    /// <summary>One equation's composed parameter names: its own, then each first active requiring callee's, by name.</summary>
    private static string[] ComposeNames(SyntheticSystem system, int equation, IReadOnlySet<int> open, Func<int, string[]> read)
    {
        var names = new List<string>(system.Own[equation]);
        var seen = new HashSet<(bool, int)>();
        foreach (var reference in system.References[equation])
        {
            if (reference.Guard >= 0 && !open.Contains(reference.Guard))
                continue;
            var callee = reference.Target >= 0 ? read(reference.Target) : Externals[reference.External];
            if (callee.Length == 0 || !seen.Add((reference.Target >= 0, reference.Target >= 0 ? reference.Target : reference.External)))
                continue;
            foreach (var name in callee)
            {
                if (!names.Contains(name))
                    names.Add(name);
            }
        }

        return [.. names];
    }

    /// <summary>
    /// The reading of the WHOLE system under the calculation links <paramref name="open"/>: components of the active read
    /// graph dependency-first, a cyclic one by the closed gate and then simultaneous rounds over this oracle's own
    /// composition and its own record of every state; null for an equation with no meaning.
    /// </summary>
    private static string[]?[] EvaluateWhole(SyntheticSystem system, IReadOnlySet<int> open, bool guardBlindRounds = false)
    {
        bool Active(SyntheticReference reference) => reference.Target >= 0 && (reference.Guard < 0 || open.Contains(reference.Guard));
        var facts = new string[]?[system.Count];
        var meaningless = new bool[system.Count];
        foreach (var component in StronglyConnectedCalleesFirst(system.Count,
                     key => system.References[key].Where(Active).Select(reference => reference.Target)))
        {
            var members = component.ToHashSet();
            if (component.Any(key => system.References[key].Any(reference => Active(reference) && !members.Contains(reference.Target) && meaningless[reference.Target])))
            {
                foreach (var key in component)
                    meaningless[key] = true;
                continue;
            }

            var cyclic = component.Count > 1 || system.References[component[0]].Any(reference => Active(reference) && reference.Target == component[0]);
            if (!cyclic)
            {
                facts[component[0]] = ComposeNames(system, component[0], open, target => facts[target]!);
                continue;
            }

            var closed = component.ToDictionary(key => key, key => ComposeNames(system, key, open, target => members.Contains(target) ? [] : facts[target]!));
            var reached = closed;
            if (component.Any(key => system.References[key].Any(reference => Active(reference) && members.Contains(reference.Target) && closed[reference.Target].Length > 0)))
            {
                reached = Rounds(system, component, members, guardBlindRounds ? AllEquations(system) : open, closed, target => facts[target] ?? []);
                if (reached is null)
                {
                    foreach (var key in component)
                        meaningless[key] = true;
                    continue;
                }
            }

            foreach (var (key, names) in reached)
                facts[key] = names;
        }

        return facts;
    }

    private static HashSet<int> AllEquations(SyntheticSystem system) => [.. Enumerable.Range(0, system.Count)];

    /// <summary>Simultaneous rounds with every state remembered: successive equality settles, any other repeat is non-settling.</summary>
    private static Dictionary<int, string[]>? Rounds(SyntheticSystem system, List<int> component, HashSet<int> members, IReadOnlySet<int> open,
        Dictionary<int, string[]> closed, Func<int, string[]> lower)
    {
        string State(Dictionary<int, string[]> round) => string.Join(";", component.Order().Select(key => string.Join(",", round[key])));
        var seen = new HashSet<string> { State(closed) };
        var previous = closed;
        while (true)
        {
            var read = previous;
            var next = component.ToDictionary(key => key, key => ComposeNames(system, key, open, target => members.Contains(target) ? read[target] : lower(target)));
            if (State(next) == State(previous))
                return next;
            if (!seen.Add(State(next)))
                return null;
            previous = next;
        }
    }

    /// <summary>Tarjan's components, each emitted after every component it reaches: callees first.</summary>
    private static List<List<int>> StronglyConnectedCalleesFirst(int count, Func<int, IEnumerable<int>> successors)
    {
        var index = new int[count];
        var low = new int[count];
        var onStack = new bool[count];
        Array.Fill(index, -1);
        var stack = new Stack<int>();
        var result = new List<List<int>>();
        var next = 0;

        void Visit(int key)
        {
            index[key] = low[key] = next++;
            stack.Push(key);
            onStack[key] = true;
            foreach (var successor in successors(key))
            {
                if (index[successor] < 0)
                {
                    Visit(successor);
                    low[key] = Math.Min(low[key], low[successor]);
                }
                else if (onStack[successor])
                {
                    low[key] = Math.Min(low[key], index[successor]);
                }
            }

            if (low[key] != index[key])
                return;
            var component = new List<int>();
            int popped;
            do
            {
                popped = stack.Pop();
                onStack[popped] = false;
                component.Add(popped);
            }
            while (popped != key);
            result.Add(component);
        }

        for (var key = 0; key < count; key++)
        {
            if (index[key] < 0)
                Visit(key);
        }

        return result;
    }

    private static IEnumerable<HashSet<int>> AllSubsets(IReadOnlyList<int> items)
    {
        for (var mask = 0; mask < 1 << items.Count; mask++)
            yield return [.. items.Where((_, position) => (mask & (1 << position)) != 0)];
    }

    /// <summary>Rule G6 over every classification of every link of the whole system: the selected facts, or null.</summary>
    private static string[][]? GlobalRuleG6(SyntheticSystem system, bool guardBlindRounds = false)
    {
        var links = Enumerable.Range(0, system.Count).Where(key => system.IsLink[key]).ToArray();
        string[][]? grounded = null;
        int groundedCount = 0;
        var undetermined = false;
        foreach (var gamma in AllSubsets(links))
        {
            var facts = EvaluateWhole(system, gamma, guardBlindRounds);
            if (links.Any(link => facts[link] is { } fact && fact.Length > 0 != gamma.Contains(link)))
                continue;
            if (facts.Any(fact => fact is null))
                continue;

            var verdict = "grounded";
            foreach (var support in AllSubsets([.. gamma.Order()]))
            {
                if (support.Count == 0)
                    continue;
                var counterfactual = EvaluateWhole(system, gamma.Except(support).ToHashSet(), guardBlindRounds);
                if (support.Any(link => counterfactual[link] is { Length: > 0 }))
                    continue;
                if (support.All(link => counterfactual[link] is not null))
                {
                    verdict = "ungrounded";
                    break;
                }

                verdict = "undetermined";
            }

            if (verdict == "grounded")
            {
                groundedCount++;
                grounded ??= [.. facts.Select(fact => fact!)];
            }
            else if (verdict == "undetermined")
            {
                undetermined = true;
            }
        }

        return groundedCount == 1 && !undetermined ? grounded : null;
    }

    /// <summary>
    /// THE INDEPENDENT ORACLE: the selector — components, a dependency-first local pass, joint regions over dependency
    /// cones, alternative-carrying tables — must select exactly when rule G6 applied to the whole system at once selects,
    /// and must select the same facts, on random systems of up to six equations and four links (guarded reads, cycles,
    /// self reads, links read by their own guards, deduplicated callees).
    /// </summary>
    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(4)]
    [InlineData(5)]
    [InlineData(6)]
    public void TheSelector_AgreesWithRuleG6OverTheWholeSystem(int seed)
    {
        var random = new Random(seed);
        var closed = new SignatureFact([], null, isLifted: false, composition: null, new CallableSignature("", []));
        var selected = 0;
        for (var trial = 0; trial < 500; trial++)
        {
            var system = RandomSystem(random);
            var internalIdentities = Enumerable.Range(0, system.Count).Select(_ => new object()).ToArray();
            var externalIdentities = Externals.Select(_ => new object()).ToArray();
            var externalSignatures = Externals
                .Select((names, k) => CallableSignature.FromInferredPatterns($"X{k}", [.. names.Select(name => (ParameterPattern)new CaptureParameterPattern(name))]))
                .ToArray();
            var references = system.References
                .Select(list => (IReadOnlyList<SignatureEquationReference>)list.Select(reference => reference.Target >= 0
                    ? new SignatureEquationReference(reference.Target, null, internalIdentities[reference.Target], reference.Guard, new Expr.Resolve("r"), "r")
                    : new SignatureEquationReference(-1, externalSignatures[reference.External], externalIdentities[reference.External], reference.Guard, new Expr.Resolve("r"), "r"))
                    .ToList())
                .ToArray();
            SignatureFact Compose(int equation, IReadOnlyList<(int Reference, CallableSignature Signature)> lifted)
            {
                var names = new List<string>(system.Own[equation]);
                foreach (var (_, signature) in lifted)
                {
                    foreach (var name in signature.ParameterNames)
                    {
                        if (!names.Contains(name))
                            names.Add(name);
                    }
                }

                IReadOnlyList<ParameterPattern> patterns = [.. names.Select(name => (ParameterPattern)new CaptureParameterPattern(name))];
                return new SignatureFact(patterns, null, lifted.Count > 0, null, CallableSignature.FromInferredPatterns($"E{equation}", patterns));
            }

            var selection = new SignatureSelector(references, system.IsLink, Compose, static (_, settled, _) => settled, closed,
                new StaticQueryResourceBudget(StaticQueryLimits.Default), CancellationToken.None).Solve();
            var oracle = GlobalRuleG6(system);
            Assert.True(oracle is not null == selection.Succeeded,
                $"seed {seed}, trial {trial}: rule G6 over the whole system {(oracle is null ? "selects nothing" : "selects")}, "
                + $"the selector {(selection.Succeeded ? "selected" : "refused")}: {system}");
            if (oracle is null)
                continue;
            selected++;
            for (var key = 0; key < system.Count; key++)
            {
                Assert.True(oracle[key].SequenceEqual(selection.Facts[key].Signature.ParameterNames),
                    $"seed {seed}, trial {trial}, E{key}: rule G6 gives ({string.Join(",", oracle[key])}), the selector "
                    + $"({string.Join(",", selection.Facts[key].Signature.ParameterNames)}): {system}");
            }
        }

        // The random systems exercise both outcomes; recursive completion selects most of them.
        Assert.InRange(selected, 50, 499);
    }

    /// <summary>A control of the comparison: rounds that ignore their guards answer differently on some system.</summary>
    [Fact]
    public void GuardBlindRounds_AreExposedByRuleG6()
    {
        var random = new Random(77);
        for (var trial = 0; trial < 20000; trial++)
        {
            var system = RandomSystem(random);
            var (correct, blind) = (GlobalRuleG6(system), GlobalRuleG6(system, guardBlindRounds: true));
            if (correct is null != blind is null
                || (correct is not null && !correct.Zip(blind!).All(static pair => pair.First.SequenceEqual(pair.Second))))
                return;
        }

        Assert.Fail("Guard-blind rounds went unnoticed.");
    }
}
