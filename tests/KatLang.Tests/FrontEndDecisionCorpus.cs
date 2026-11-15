using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>Where a classified name stands.</summary>
internal enum FrontEndSite
{
    /// <summary>A bare name written in a row.</summary>
    BareName,

    /// <summary>The lexical-fallback name of a dot edge (rewritten by the same rule as a bare callee name).</summary>
    DotFallback,

    /// <summary>The head name of a static <c>open</c> target.</summary>
    OpenHead,
}

/// <summary>
/// One scope level of a program as parameter detection left it: the names it binds by NAME RESOLUTION
/// (written and inferred parameters, or a branch body's pattern binders), the properties it declares,
/// and — filled in after implicit-argument resolution — the parameters automatic forwarding added.
/// </summary>
internal sealed class FrontEndLevel(
    int index,
    FrontEndLevel? parent,
    StaticScopeKey key,
    IReadOnlyList<string> parameters,
    IReadOnlyList<string> properties,
    bool isNeverCalledRoot)
{
    public int Index { get; } = index;
    public FrontEndLevel? Parent { get; } = parent;
    public StaticScopeKey Key { get; } = key;
    public IReadOnlyList<string> Parameters { get; } = parameters;
    public IReadOnlyList<string> Properties { get; } = properties;

    /// <summary>The program root: never called, so its inferred signature binds nothing a call could supply.</summary>
    public bool IsNeverCalledRoot { get; } = isNeverCalledRoot;

    public IReadOnlyList<string> Forwarded { get; set; } = [];

    /// <summary>Whether an open head is classified at this level (so its callable chain is emitted).</summary>
    public bool HasOpenHead { get; set; }
}

/// <summary>
/// One classified name: C#'s owner-walk selection (the production binding fact, as a Lean
/// <c>OwnedDeclaration</c> term) and the node the detector elaborated it to.
/// </summary>
internal sealed record FrontEndOccurrence(FrontEndLevel Level, FrontEndSite Site, string Name, bool IsParameter, string Owned);

/// <summary>One clause family: its heads as Lean patterns and C#'s derived lifting signature as a Lean term.</summary>
internal sealed record FrontEndFamily(string Name, string? LeanHeads, string? Expected, string? SkipReason);

/// <summary>Why a corpus program contributes no front-end decisions.</summary>
internal enum FrontEndSkip
{
    /// <summary>The parser rejected the source: no elaboration decision is made on a recovery syntax tree here.</summary>
    SyntaxError,

    /// <summary>
    /// The source writes a <c>load</c> directive. Module elaboration is async-only, so without a downloader the tree is
    /// elaborated provisionally and its decisions depend on members the missing module would supply.
    /// </summary>
    UnresolvedLoad,

    /// <summary>Parameter inference was refused as circular: the signatures the owner walk reads are undecided.</summary>
    UndecidedInference,

    /// <summary>A reviewed Lean/C# disagreement, excluded by exact id (<see cref="FrontEndDecisionCorpus.ReviewedDriftById"/>).</summary>
    ReviewedDrift,
}

/// <summary>One reviewed disagreement: its class, and the smallest program that shows it.</summary>
internal sealed record FrontEndDrift(string Class, string Witness);

internal sealed record FrontEndProgram(
    string Corpus,
    string Id,
    string Source,
    FrontEndSkip? Skip,
    IReadOnlyList<FrontEndLevel> Levels,
    IReadOnlyList<FrontEndOccurrence> Occurrences,
    IReadOnlyList<FrontEndFamily> Families,
    FinalTreeConfirmation FinalTree);

/// <summary>
/// How the classified names of one program compare with the complete pipeline's tree: confirmed there as the same
/// node, without a source span to match by (a name the parser synthesized, such as the plumbing of an assignment
/// deconstruction), or with no node of that span and name left there (a later pass rewrote the occurrence).
/// </summary>
internal readonly record struct FinalTreeConfirmation(int Confirmed, int NoSpan, int NoCounterpart);

/// <summary>
/// Collects, for every corpus program, the C# front end's per-occurrence decisions and the inputs the Lean
/// front-end specification functions read (<c>lean/KatLang.lean</c>: <c>selectOwnedDeclaration</c>,
/// <c>elaboratesToParameter</c>, <c>elaborateOpenHead</c>, <c>familyLiftingSignature?</c>).
///
/// <para><b>What is C#'s decision.</b> The program is run through the real front-end stages, one at a time:
/// the raw parse, then <see cref="ParameterDetector.DetectPrevalidated"/> (name resolution), then
/// <see cref="ImplicitArgumentResolver.ResolvePrevalidated(DetectedProgram, FrontEndTraversalObservations?, DiagnosticBag?)"/>
/// (automatic parameter forwarding) on that same detection. A name's verdict is read twice: the NODE the detector
/// left in its output tree (<see cref="Expr.Param"/> or <see cref="Expr.Resolve"/>), and the BINDING FACT the
/// detection's own static-structure operation answers for that name in that scope
/// (<see cref="StaticStructureOperation.Binding"/>: parameter or declaration, with the owning scope), which is the
/// query the detector's rewrite and <see cref="ElaboratedScopeLookup.SelectOwnedDeclaration"/> both read. The two
/// must agree, or collection throws.</para>
///
/// <para><b>What is the input.</b> The owner chain is rebuilt from the DETECTED TREE's own nesting — each
/// enclosing body's stored parameter patterns and property names, a branch body's pattern binders — never from the
/// verdicts, so a guard cannot be satisfied by construction. Its shape is cross-checked against the operation's
/// scope keys: each level's key must have the enclosing level's key as its parent. Automatic forwarding runs after
/// detection, so a detected body's parameters are name-resolution parameters only; what forwarding added is the
/// resolved view's signature minus the detected one.</para>
///
/// <para>Shapes the walk does not understand throw instead of being approximated.</para>
/// </summary>
internal static class FrontEndDecisionCorpus
{
    public const string ExplorerCorpus = "explorer";
    public const string LanguageSpecCorpus = "spec";

    /// <summary>
    /// Programs on which a Lean specification function and the C# front end are KNOWN to disagree, by exact
    /// <c>corpus/id</c>, each with its classified reason and a minimal witness program. Such a program is left out
    /// of the guards and counted in the artifact's partition. A disagreement is an owner decision: neither
    /// production nor the specification is changed to remove an entry, and an entry is never added to make a
    /// failing guard pass without that review. Empty: every guard of both corpora holds.
    /// </summary>
    internal static readonly IReadOnlyDictionary<string, FrontEndDrift> ReviewedDriftById = new Dictionary<string, FrontEndDrift>();

    private static readonly Lazy<IReadOnlyList<FrontEndProgram>> LazyPrograms = new(CollectAll);

    /// <summary>Every program of both differential corpora, in corpus order: the explorer's, then the specification's.</summary>
    public static IReadOnlyList<FrontEndProgram> Programs => LazyPrograms.Value;

    private static readonly Lazy<IReadOnlyList<string>> LazyPrelude = new(static () =>
    {
        var operation = StaticStructureAdmission.Create(new Algorithm.User(null, [], [], [], []), hostOperations: null).Operation;
        return PropertyNames(operation.SourceOf(operation.Queries.Keys.Root));
    });

    /// <summary>
    /// The outermost level of every chain: the property names of C#'s semantic prelude (no host operations
    /// configured), in declaration order. Every program's own prelude level is checked to be this one.
    /// </summary>
    public static IReadOnlyList<string> PreludeProperties() => LazyPrelude.Value;

    private static IReadOnlyList<FrontEndProgram> CollectAll()
    {
        var programs = new List<FrontEndProgram>();
        foreach (var explorerCase in SemanticExplorerCorpus.AllCases())
            programs.Add(Collect(ExplorerCorpus, explorerCase.Id, explorerCase.Source));
        foreach (var specCase in LanguageSpec.LanguageSpecCorpus.AllCases())
            programs.Add(Collect(LanguageSpecCorpus, specCase.Id, specCase.Source));
        return programs.AsReadOnly();
    }

    public static FrontEndProgram Collect(string corpus, string id, string source)
    {
        FrontEndProgram Skipped(FrontEndSkip reason) => new(corpus, id, source, reason, [], [], [], default);

        if (ReviewedDriftById.ContainsKey($"{corpus}/{id}"))
            return Skipped(FrontEndSkip.ReviewedDrift);

        var parsed = Parser.ParseSyntax(source);
        if (parsed.HasErrors)
            return Skipped(FrontEndSkip.SyntaxError);
        if (LoadElaborationGuard.TryFindFirstUnresolvedLoad(parsed.Root, out _))
            return Skipped(FrontEndSkip.UnresolvedLoad);

        var detected = ParameterDetector.DetectPrevalidated(parsed.Root);
        if (detected.Diagnostics.HasReported(DiagnosticCode.SelfDependentInferredParameters))
            return Skipped(FrontEndSkip.UndecidedInference);

        var operation = detected.Operation
            ?? throw new InvalidOperationException($"{corpus}/{id}: detection returned no static-structure operation.");
        try
        {
            var walk = new Walk(operation);
            walk.Program(detected.Root);

            // Automatic parameter forwarding, on the SAME detection: the resolved view of each scope key.
            ImplicitArgumentResolver.ResolvePrevalidated(detected);
            if (detected.Diagnostics.HasReported(DiagnosticCode.SelfDependentInferredParameters))
                return Skipped(FrontEndSkip.UndecidedInference);
            foreach (var level in walk.Levels)
            {
                if (operation.ResolvedView(level.Key) is Algorithm.User resolved)
                    level.Forwarded = ParameterNames(resolved).Where(name => !level.Parameters.Contains(name)).ToArray();
            }

            return new(corpus, id, source, null, walk.Levels, walk.Occurrences, walk.Families,
                ConfirmAgainstFinalTree(source, walk.WrittenNodes));
        }
        catch (Exception error) when (error is InvalidOperationException or NotSupportedException)
        {
            throw new InvalidOperationException($"{corpus}/{id}: {error.Message}{Environment.NewLine}Source:{Environment.NewLine}{source}", error);
        }
    }

    /// <summary>
    /// Q-04: a name's detected verdict is final. Every WRITTEN occurrence the complete pipeline's tree still holds —
    /// matched by its source span and name — must be the node kind detection gave it, or collection throws. A
    /// synthetic name with no span, and a written occurrence a later pass rewrote, has no counterpart to compare;
    /// both are counted.
    /// </summary>
    private static FinalTreeConfirmation ConfirmAgainstFinalTree(
        string source, IReadOnlyList<(Expr Node, bool IsParameter, SourceSpan? Span)> written)
    {
        var final = new Dictionary<(SourceSpan Span, string Name), (bool Parameter, bool Lexical)>();
        var collector = new NameNodes(final);
        collector.VisitAlgorithm(SourceProvenance.ParseAllowingDiagnostics(source).Root);

        var (confirmed, noSpan, noCounterpart) = (0, 0, 0);
        foreach (var (node, isParameter, writtenAt) in written)
        {
            if (writtenAt is not { } span)
            {
                noSpan++;
                continue;
            }

            var name = node is Expr.Param parameter ? parameter.Name : ((Expr.Resolve)node).Name;
            if (!final.TryGetValue((span, name), out var kinds))
            {
                noCounterpart++;
                continue;
            }

            if (isParameter ? !kinds.Parameter : !kinds.Lexical)
            {
                throw new InvalidOperationException(
                    $"the written name '{name}' at {span} was detected as {(isParameter ? "a parameter" : "a lexical reference")} " +
                    "but the complete pipeline's tree holds the other node there: a later pass re-selected a binding (Q-04).");
            }

            confirmed++;
        }

        return new(confirmed, noSpan, noCounterpart);
    }

    private sealed class NameNodes(Dictionary<(SourceSpan Span, string Name), (bool Parameter, bool Lexical)> nodes) : AstWalker
    {
        public override void VisitExpr(Expr expression)
        {
            Record(expression, expression.Span);
            if (expression is Expr.DotCall edge)
                Record(edge.EffectiveLexicalFallback, edge.EffectiveLexicalFallback.Span ?? edge.MemberSpan);
            base.VisitExpr(expression);
        }

        private void Record(Expr expression, SourceSpan? at)
        {
            if (at is not { } span)
                return;
            var (name, isParameter) = expression switch
            {
                Expr.Param(var parameter) => (parameter, true),
                Expr.Resolve(var reference) => (reference, false),
                _ => (null, false),
            };
            if (name is null)
                return;
            nodes.TryGetValue((span, name), out var kinds);
            nodes[(span, name)] = isParameter ? (true, kinds.Lexical) : (kinds.Parameter, true);
        }
    }

    private static IReadOnlyList<string> ParameterNames(Algorithm.User body)
        => body.Parameters.Select(static parameter => parameter.Name).Distinct(StringComparer.Ordinal).ToArray();

    private static IReadOnlyList<string> PropertyNames(Algorithm body)
        => body.Properties.Select(static property => property.Name
            ?? throw new NotSupportedException("a property without a name has no owner-level entry.")).ToArray();

    private sealed class Walk(StaticStructureOperation operation)
    {
        private readonly StaticScopeKey _preludeKey = operation.Queries.Keys.Root;
        private FrontEndLevel? _prelude;

        public List<FrontEndLevel> Levels { get; } = [];
        public List<FrontEndOccurrence> Occurrences { get; } = [];
        public List<FrontEndFamily> Families { get; } = [];
        /// <summary>Every classified node with the span it was written at (a dot edge's fallback name: its member token's).</summary>
        public List<(Expr Node, bool IsParameter, SourceSpan? Span)> WrittenNodes { get; } = [];

        public void Program(Algorithm root)
        {
            if (root is not Algorithm.User user)
                throw new NotSupportedException($"the detected program root is a {root.GetType().Name}.");
            if (!ReferenceEquals(operation.Root.Parent, _preludeKey))
                throw new NotSupportedException("the program root is not declared directly under the prelude.");

            // The prelude is the chain's outermost property level. It is index -1: every program shares its one
            // Lean definition, so it is never emitted per program.
            _prelude = new FrontEndLevel(-1, null, _preludeKey, [], PropertyNames(operation.SourceOf(_preludeKey)), isNeverCalledRoot: false);
            if (!_prelude.Properties.SequenceEqual(PreludeProperties(), StringComparer.Ordinal))
                throw new InvalidOperationException("this program's prelude level is not the shared semantic prelude.");
            Body(user, _prelude, branchPattern: null, operation.Root, isProgramRoot: true);
        }

        private void Nested(Algorithm algorithm, string name, FrontEndLevel parent)
        {
            switch (algorithm)
            {
                case Algorithm.Builtin:
                    break;

                case Algorithm.Conditional family:
                    Family(family, name, parent);
                    break;

                case Algorithm.User user:
                    Body(user, parent, branchPattern: null, operation.ContextOf(parent.Key, user), isProgramRoot: false);
                    break;

                default:
                    throw new NotSupportedException($"a detected tree holds a {algorithm.GetType().Name}.");
            }
        }

        private void Family(Algorithm.Conditional family, string name, FrontEndLevel parent)
        {
            // A parsed family owns no opens, so it adds no level of its own: its branch bodies stand directly under
            // the level that declares the family (ParameterDetector.ProcessConditionalProperty).
            if (family.Opens.Count > 0)
                throw new NotSupportedException("a clause family with its own open list (host-built only).");

            Families.Add(DescribeFamily(name, family));
            foreach (var branch in family.Branches)
            {
                if (branch.Body is not Algorithm.User body)
                    throw new NotSupportedException($"a clause body that is a {branch.Body.GetType().Name} (host-built only).");
                if (body.DeferredRegion is not null)
                    throw new NotSupportedException("a deferred module region.");
                Body(body, parent, branch.Pattern, operation.ContextOf(parent.Key, body, branch.Pattern), isProgramRoot: false);
            }
        }

        private static FrontEndFamily DescribeFamily(string name, Algorithm.Conditional family)
        {
            // Lean `Pattern.bind` carries no parameter kind, and C# gives a collecting or META binder (and the
            // parser's recovery placeholder) no vote: such a head has no faithful Lean spelling.
            static bool Unrepresentable(Pattern pattern) => pattern switch
            {
                Pattern.Bind bind => bind.ParameterKind != ParameterKind.Normal || bind.IsRecoveryPlaceholder,
                Pattern.SequenceValue(var items) => items.Any(Unrepresentable),
                Pattern.ListValue(var items) => items.Any(Unrepresentable),
                _ => false,
            };

            if (family.Branches.Any(branch => Unrepresentable(branch.Pattern)))
                return new(name, null, null, "a clause head binds a collecting, META or recovery-placeholder name");

            string heads;
            try
            {
                heads = string.Join(", ", family.Branches.Select(branch => $"clause ({LeanAstEncoder.EncodePattern(branch.Pattern)})"));
            }
            catch (NotSupportedException)
            {
                // The encoder refuses what the Lean core cannot spell (a fractional or quantum-bearing number, a
                // control character): the same fail-loud boundary the evaluation corpora exclude such cases at.
                return new(name, null, null, "a clause head holds a literal the Lean core cannot spell");
            }

            var derived = ImplicitArgumentResolver.DeriveFamilyLiftingSignature(name, family);
            var expected = derived.Signature is { } signature
                ? $"some [{string.Join(", ", signature.Parameters.Select(parameter => $".capture {{ name := {LeanAstEncoder.QuoteString(parameter.Name)} }}"))}]"
                : "none";
            return new(name, heads, expected, null);
        }

        private void Body(Algorithm.User body, FrontEndLevel parent, Pattern? branchPattern, StaticScopeKey key, bool isProgramRoot)
        {
            if (body.IsModuleElaborated || body.IsModuleRoot)
                throw new NotSupportedException("a loaded module body.");
            if (!ReferenceEquals(key.Parent, parent.Key))
                throw new InvalidOperationException("a body's scope key is not declared under the enclosing level's key: the lexical chain and C#'s scope chain differ.");

            IReadOnlyList<string> parameters = ParameterNames(body);
            if (branchPattern is not null)
            {
                // A branch body's inputs are its clause head's binders, owned by the body's own level.
                if (parameters.Count > 0)
                    throw new NotSupportedException("a clause body with parameter patterns of its own.");
                parameters = branchPattern.BoundNamesExpandingSharedNodesOnce().Distinct(StringComparer.Ordinal).ToArray();
            }

            var level = new FrontEndLevel(Levels.Count, parent, key, parameters, PropertyNames(body), isProgramRoot);
            Levels.Add(level);

            foreach (var open in body.Opens)
                Open(open, level);

            foreach (var property in body.Properties)
            {
                // A hoisted deconstruction right-hand side is written by THIS body: its rows are collected and
                // rewritten with this body's rows, never as a nested scope of its own.
                if (property.Value is Algorithm.User { IsAssignmentDeconstructionSource: true } source)
                {
                    foreach (var row in source.Output)
                        Row(row, level);
                }
                else
                {
                    Nested(property.Value, property.Name!, level);
                }
            }

            foreach (var row in body.Output)
                Row(row, level);
        }

        private void Open(Expr open, FrontEndLevel level)
        {
            var head = open.OpenTargetHead();
            if (head is Expr.Resolve or Expr.Param)
            {
                level.HasOpenHead = true;
                Name(head, level, FrontEndSite.OpenHead);
            }

            OpenInterior(open);
        }

        /// <summary>
        /// An open target is a static path: only its head is a lexical name. An inline block anywhere inside it is its
        /// own owner region rooted at the prelude (ParameterDetector.ProcessSharedOpenAlgorithm), whatever opened it.
        /// </summary>
        private void OpenInterior(Expr expression)
        {
            if (expression is Expr.AlgorithmExpr block)
            {
                Nested(block.Algorithm, "<anonymous>", _prelude!);
                return;
            }

            foreach (var child in Children(expression))
                OpenInterior(child);
        }

        private void Row(Expr expression, FrontEndLevel level)
        {
            switch (expression)
            {
                case Expr.Resolve or Expr.Param:
                    Name(expression, level, FrontEndSite.BareName);
                    return;

                case Expr.AlgorithmExpr block:
                    Nested(block.Algorithm, "<anonymous>", level);
                    return;

                case Expr.Grace:
                    throw new NotSupportedException("a Grace marker survived parameter detection.");

                case Expr.DotCall edge:
                    Row(edge.Target, level);
                    Name(edge.EffectiveLexicalFallback, level, FrontEndSite.DotFallback, edge.MemberSpan);
                    if (edge.Args is { } arguments)
                    {
                        foreach (var argument in arguments)
                            Row(argument, level);
                    }

                    return;
            }

            foreach (var child in Children(expression))
                Row(child, level);
        }

        /// <summary>The written child expressions of a scope-less node, in reading order.</summary>
        private static IEnumerable<Expr> Children(Expr expression) => expression switch
        {
            Expr.Capture(var rows) => rows,
            Expr.ListLiteral(var items) => items,
            Expr.SequenceSpread(var operand) => [operand],
            Expr.SequenceConstruct(var left, var right) => [left, right],
            Expr.Unary(_, var operand) => [operand],
            Expr.Binary(_, var left, var right) => [left, right],
            Expr.Comparison(var first, var links) => [first, .. links.Select(static link => link.Operand)],
            Expr.Index(var target, var selectors) => [target, .. selectors],
            Expr.Call(var function, var arguments) => [function, .. arguments],
            Expr.DotCall edge => [edge.Target, .. edge.Args ?? OutputBundle.Empty],
            Expr.Grace(var inner, _) => [inner],
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence
                or Expr.NativeCall or Expr.AlgorithmExpr => [],
        };

        private void Name(Expr node, FrontEndLevel level, FrontEndSite site, SourceSpan? writtenAt = null)
        {
            var (name, isParameter) = node switch
            {
                Expr.Param(var parameter) => (parameter, true),
                Expr.Resolve(var reference) => (reference, false),
                _ => throw new NotSupportedException($"a {site} that is a {node.GetType().Name}, not a name."),
            };

            // An open head is owned by CALLABLE bindings only: the never-called root's signature takes no part.
            var owned = operation.Binding(level.Key, name,
                site == FrontEndSite.OpenHead ? StaticQueryProjection.OpenHeadBinding : StaticQueryProjection.OwnedBinding);
            if ((owned.Kind == StaticFactKind.Parameter) != isParameter)
            {
                throw new InvalidOperationException(
                    $"the {site} '{name}' elaborated to {(isParameter ? "Expr.Param" : "Expr.Resolve")} but its owned binding fact is {owned.Kind}.");
            }

            if (site != FrontEndSite.OpenHead && (operation.Binding(level.Key, name).Kind == StaticFactKind.Parameter) != isParameter)
            {
                throw new InvalidOperationException(
                    $"the {site} '{name}' elaborated to {(isParameter ? "Expr.Param" : "Expr.Resolve")} against its own binding fact.");
            }

            var term = owned.Kind switch
            {
                StaticFactKind.Parameter => $".parameter {Depth(level, owned.Scope, name)}",
                StaticFactKind.Declaration => $".property {Depth(level, owned.Scope, name)}",
                StaticFactKind.Missing => ".none",
                _ => throw new NotSupportedException(
                    $"the {site} '{name}' has owned-binding fact {owned.Kind}, which has no Lean OwnedDeclaration encoding."),
            };
            Occurrences.Add(new(level, site, name, isParameter, term));
            WrittenNodes.Add((node, isParameter, node.Span ?? writtenAt));
        }

        /// <summary>The position of the deciding level in the occurrence's chain (0 = its own body), by scope key.</summary>
        private static int Depth(FrontEndLevel level, StaticScopeKey? owner, string name)
        {
            var depth = 0;
            for (var current = level; current is not null; current = current.Parent, depth++)
            {
                if (ReferenceEquals(current.Key, owner))
                    return depth;
            }

            throw new InvalidOperationException($"the level that owns '{name}' is not an enclosing level of its occurrence.");
        }
    }
}
