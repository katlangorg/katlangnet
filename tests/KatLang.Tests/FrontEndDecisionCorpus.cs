using KatLang.ParserFuzz;
using KatLang.Tests.LanguageSpec;
using KatLang.Tests.SemanticTesting;

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
/// How parameter detection treated one CANDIDATE name of an inferring level — a name written in the level's own rows
/// (<c>StaticStructureQueries.CandidateNames</c>): the promotion question of Lean's <c>shouldTreatAsImplicitParam</c>.
/// </summary>
internal enum FrontEndPromotionClass
{
    /// <summary>Promoted: the name is an inferred input of the level (<c>IsInput</c> is Yes). Lean's probe must say true.</summary>
    Promoted,

    /// <summary>
    /// Not promoted because lexical lookup finds a declaration: the level's own property, an enclosing level's, a
    /// prelude member, or a public member an open provides (the inference binding is a declaration). Lean's probe
    /// must say false.
    /// </summary>
    Resolves,

    /// <summary>
    /// Not asked: an established PARAMETER binding owns the name (an enclosing level's written or inferred parameter,
    /// a branch binder). Lean's caller excludes such a name before the probe; FD-1 checks the binding itself.
    /// </summary>
    EnclosingParameter,

    /// <summary>
    /// Not asked: nothing binds the name, yet it is not an input, because no reading of it participates — a dot
    /// fallback no receiver can select, or the OD-B exemption of a parameter-rooted path row. Lean models no
    /// participation, so its probe is not this decision.
    /// </summary>
    NotParticipating,

    /// <summary>
    /// Not asked: the name resolves to a member of C#'s semantic prelude that Lean's <c>preludeAlg</c> does not model
    /// (the <c>Math</c> members and <c>load</c>). The artifact pins Lean's prelude to exactly the builtins.
    /// </summary>
    PreludeOnly,

    /// <summary>The lookup reaches two opened providers (C#'s static <c>AmbiguousOpen</c> rejection).</summary>
    AmbiguousOpen,
}

/// <summary>One candidate name's promotion verdict; <paramref name="ThroughOpen"/>: its declaration was found by an open.</summary>
internal sealed record FrontEndPromotion(string Name, FrontEndPromotionClass Class, bool ThroughOpen)
{
    /// <summary>Whether this is promotion's own question, which the Lean probe answers.</summary>
    public bool IsAsked => Class is FrontEndPromotionClass.Promoted or FrontEndPromotionClass.Resolves or FrontEndPromotionClass.AmbiguousOpen;
}

/// <summary>Where automatic forwarding took one argument binding (Lean <c>ForwardingSource</c>).</summary>
internal enum FrontEndForwardingKind
{
    /// <summary>The referencing level's own name-resolution parameter (Lean <c>ownParameter</c>).</summary>
    Own,

    /// <summary>An enclosing level's parameter binding, at <see cref="FrontEndForwarding.Level"/> (Lean <c>capturedParameter</c>).</summary>
    Captured,

    /// <summary>A parameter forwarding added to the referencing level (Lean <c>forwardedParameter</c>).</summary>
    Forwarded,

    /// <summary>A closed body's value operand stayed bare and its callee requires exactly this binding.</summary>
    Unavailable,
}

/// <summary>One forwarded binding of a level, by name, with C#'s source and, when captured, the chain level it reads.</summary>
internal sealed record FrontEndForwarding(string Name, FrontEndForwardingKind Kind, int Level, string? Requested = null);

/// <summary>One lexical step to a property body, or to a numbered branch of a property family.</summary>
internal sealed record FrontEndPathStep(string Property, int? Branch = null);

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
    bool isNeverCalledRoot,
    IReadOnlyList<Property>? declared = null,
    bool infers = false,
    bool ownOpens = false,
    IReadOnlyList<FrontEndPathStep>? path = null)
{
    public int Index { get; } = index;
    public FrontEndLevel? Parent { get; } = parent;
    public StaticScopeKey Key { get; } = key;
    public IReadOnlyList<string> Parameters { get; } = parameters;
    public IReadOnlyList<string> Properties { get; } = properties;

    /// <summary>The detected property declarations, in <see cref="Properties"/> order (their spans locate collisions).</summary>
    public IReadOnlyList<Property> Declared { get; } = declared ?? [];

    /// <summary>The program root: never called, so its inferred signature binds nothing a call could supply.</summary>
    public bool IsNeverCalledRoot { get; } = isNeverCalledRoot;

    /// <summary>Whether the level infers its parameters: an ordinary body with no written parameter list (C# <c>BodyContext.Infers</c>).</summary>
    public bool Infers { get; } = infers;

    /// <summary>Whether this level or an enclosing one writes an <c>open</c> (C# <c>BodyContext.HasOpens</c>).</summary>
    public bool HasOpens { get; } = ownOpens || parent?.HasOpens == true;

    /// <summary>
    /// The property or clause-branch steps from the root. An anonymous block has no such address.
    /// </summary>
    public IReadOnlyList<FrontEndPathStep>? Path { get; } = path;

    public IReadOnlyList<string> Forwarded { get; set; } = [];

    /// <summary>Whether an open head is classified at this level (so its callable chain is emitted).</summary>
    public bool HasOpenHead { get; set; }

    /// <summary>Whether another level is declared directly under this one.</summary>
    public bool HasChildLevel { get; set; }

    /// <summary>The promotion verdict of every candidate name, in the order C# lists them.</summary>
    public List<FrontEndPromotion> Promotions { get; } = [];

    /// <summary>The properties of this level C#'s collision validator reported, in <see cref="Properties"/> order.</summary>
    public IReadOnlyList<string> Conflicts { get; set; } = [];

    /// <summary>The source of each forwarded capture occurrence and each attributable refusal.</summary>
    public List<FrontEndForwarding> Forwardings { get; } = [];
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

/// <summary>
/// The lifted references of one program the complete pipeline's tree holds: attributed to the level that wrote the
/// reference, and those whose written occurrence could not be found among the classified names.
/// </summary>
internal readonly record struct FrontEndLifts(int Attributed, int Unattributed);

internal sealed record FrontEndProgram(
    string Corpus,
    string Id,
    string Source,
    FrontEndSkip? Skip,
    IReadOnlyList<FrontEndLevel> Levels,
    IReadOnlyList<FrontEndOccurrence> Occurrences,
    IReadOnlyList<FrontEndFamily> Families,
    FinalTreeConfirmation FinalTree,
    FrontEndLifts Lifts = default,
    string? Tree = null,
    string? TreeSkipReason = null);

/// <summary>
/// How the classified names of one program compare with the complete pipeline's tree: confirmed there as the same
/// node, without a source span to match by (a name the parser synthesized, such as the plumbing of an assignment
/// deconstruction), or with no node of that span and name left there (a later pass rewrote the occurrence).
/// </summary>
internal readonly record struct FinalTreeConfirmation(int Confirmed, int NoSpan, int NoCounterpart);

/// <summary>
/// Collects, for every corpus program, the C# front end's per-occurrence decisions and the inputs the Lean
/// front-end specification functions read (<c>lean/KatLang.lean</c>: <c>selectOwnedDeclaration</c>,
/// <c>elaboratesToParameter</c>, <c>elaborateOpenHead</c>, <c>familyLiftingSignature?</c>,
/// <c>shouldTreatAsImplicitParam</c>, <c>forwardingSource</c>, <c>conflictingOwnedNames</c>).
///
/// <para><b>What is C#'s decision.</b> The program is run through the real front-end stages, one at a time:
/// the raw parse, then <see cref="ParameterDetector.DetectPrevalidated"/> (name resolution), then
/// <see cref="ImplicitArgumentResolver.ResolvePrevalidated(DetectedProgram, FrontEndTraversalObservations?, DiagnosticBag?)"/>
/// (automatic parameter forwarding) on that same detection, and — once more, as a whole — the complete pipeline
/// (<see cref="Parser.Parse(string)"/>). A name's verdict is read twice: the NODE the detector
/// left in its output tree (<see cref="Expr.Param"/> or <see cref="Expr.Resolve"/>), and the BINDING FACT the
/// detection's own static-structure operation answers for that name in that scope
/// (<see cref="StaticStructureOperation.Binding"/>: parameter or declaration, with the owning scope), which is the
/// query the detector's rewrite and <see cref="ElaboratedScopeLookup.SelectOwnedDeclaration"/> both read. The two
/// must agree, or collection throws. The other decisions are read where production makes them:</para>
/// <list type="bullet">
/// <item>PROMOTION — for every candidate name of an inferring level (the names its rows write,
/// <c>StaticStructureQueries.CandidateNames</c>), the same operation's <c>IsInput</c> verdict, the query
/// <c>ParameterDetector</c>'s free-name collection reads, and its <c>InferenceBinding</c> fact (the availability
/// <c>IsInput</c> reads: the owner walk without the level's own inference, then opens), which says why a name was not
/// promoted (<see cref="FrontEndPromotionClass"/>). An inferred input must be among the level's detected parameters
/// and nothing else may be, or collection throws.</item>
/// <item>FORWARDING SOURCES — the complete pipeline's tree: a reference the resolver lifted is a call at the
/// reference's own span whose arguments are the synthesized, spanless parameter reads of one shared bundle. Each
/// argument binding is C#'s forwarding source: a parameter forwarding added to the level (the resolved signature
/// minus the detected one), the level's own parameter, or else the nearest enclosing level whose completed signature
/// binds the name. Each argument is checked against the callee's selected signature. At a closed value operand a
/// bare reference to a callee with one required binding identifies an unavailable source.</item>
/// <item>COLLISIONS — the complete pipeline's <see cref="DiagnosticCode.ParameterPropertyCollision"/> diagnostics,
/// each matched to the detected property declared at its span.</item>
/// </list>
///
/// <para><b>What is the input.</b> The owner chain is rebuilt from the DETECTED TREE's own nesting — each
/// enclosing body's stored parameter patterns and property names, a branch body's pattern binders — never from the
/// verdicts, so a guard cannot be satisfied by construction. Its shape is cross-checked against the operation's
/// scope keys: each level's key must have the enclosing level's key as its parent. Automatic forwarding runs after
/// detection, so a detected body's parameters are name-resolution parameters only; what forwarding added is the
/// resolved view's signature minus the detected one. A level whose chain writes an <c>open</c> asks promotion over
/// the resolved tree before exposure classification instead (<c>treeSite</c>), reached from the root by property names.</para>
///
/// <para>Shapes the walk does not understand throw instead of being approximated.</para>
/// </summary>
internal static class FrontEndDecisionCorpus
{
    public const string ExplorerCorpus = "explorer";
    public const string LanguageSpecCorpus = "spec";
    public const string SemanticGeneratedCorpus = "sem2b";
    public const string TutorialCorpusName = "tutorial";
    internal const string InvalidOpenTarget = "the program has an invalid open target";
    internal const string UnspellableLiteral = "the program holds a literal the Lean core cannot spell";

    /// <summary>
    /// Programs on which a Lean specification function and the C# front end are KNOWN to disagree, by exact
    /// <c>corpus/id</c>, each with its classified reason and a minimal witness program. Such a program is left out
    /// of the guards and counted in the artifact's partition. A disagreement is an owner decision: neither
    /// production nor the specification is changed to remove an entry, and an entry is never added to make a
    /// failing guard pass without that review. Empty: every program stays in the differential unless it meets a structural skip reason.
    /// </summary>
    internal static readonly IReadOnlyDictionary<string, FrontEndDrift> ReviewedDriftById = new Dictionary<string, FrontEndDrift>();

    private static readonly Lazy<IReadOnlyList<FrontEndProgram>> LazyPrograms = new(CollectAll);

    /// <summary>
    /// Every program of the four differential corpora, in corpus order: the explorer's, the specification's, the
    /// SEM-2B generated corpus's identity-prelude members, and the tutorial's source fences.
    /// </summary>
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

    /// <summary>
    /// The members of Lean's <c>preludeAlg</c>: the builtins, by name, in <see cref="BuiltinId"/> order. The artifact
    /// guards Lean's prelude to be exactly this list; a C# prelude member outside it is not modeled by Lean.
    /// </summary>
    public static IReadOnlyList<string> LeanPreludeNames { get; } = Enum.GetValues<BuiltinId>().Select(static builtin => builtin.ToString()).ToArray();

    private static readonly HashSet<string> LeanPrelude = new(LeanPreludeNames, StringComparer.Ordinal);

    /// <summary>The id of a tutorial source fence: its ordinal among the tutorial's source fences.</summary>
    internal static string TutorialId(TutorialExample example) => $"fence-{example.Index:D3}";

    private static IReadOnlyList<FrontEndProgram> CollectAll()
    {
        var programs = new List<FrontEndProgram>();
        foreach (var explorerCase in SemanticExplorerCorpus.AllCases())
            programs.Add(Collect(ExplorerCorpus, explorerCase.Id, explorerCase.Source));
        foreach (var specCase in LanguageSpec.LanguageSpecCorpus.AllCases())
            programs.Add(Collect(LanguageSpecCorpus, specCase.Id, specCase.Source));
        foreach (var semanticCase in SemanticCorpus.All())
        {
            foreach (var member in semanticCase.Members)
            {
                var id = member.Role == SemanticMember.BaseRole ? semanticCase.CaseId : $"{semanticCase.CaseId}/{member.Role}";
                programs.Add(Collect(SemanticGeneratedCorpus, id, SemanticGeneratedLeanArtifactTests.IdentityPrelude + member.Source));
            }
        }
        foreach (var example in TutorialCorpus.Examples)
            programs.Add(Collect(TutorialCorpusName, TutorialId(example), example.Source));
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

            // A free name is left out of the promotion question only where no reading of it participates: a dot edge's
            // fallback no receiver can select. A bare name written in the level always participates.
            foreach (var occurrence in walk.Occurrences.Where(static occurrence => occurrence.Site == FrontEndSite.BareName))
            {
                if (occurrence.Level.Promotions.Any(promotion => promotion.Name == occurrence.Name && promotion.Class == FrontEndPromotionClass.NotParticipating))
                    throw new InvalidOperationException($"'{occurrence.Name}' is written as a bare name of its level, yet no reading of it participates in inference.");
            }

            // Automatic parameter forwarding, on the SAME detection: the resolved view of each scope key.
            var observations = new FrontEndTraversalObservations();
            var beforeExposure = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations);
            if (detected.Diagnostics.HasReported(DiagnosticCode.SelfDependentInferredParameters))
                return Skipped(FrontEndSkip.UndecidedInference);
            foreach (var level in walk.Levels)
            {
                if (operation.ResolvedView(level.Key) is Algorithm.User resolved)
                    level.Forwarded = ParameterNames(resolved).Where(name => !level.Parameters.Contains(name)).ToArray();
            }

            // The complete pipeline, once: its tree confirms the detected verdicts and holds the lifted calls forwarding
            // built, and its diagnostics are the collision validator's verdicts.
            var complete = SourceProvenance.ParseAllowingDiagnostics(source);
            var finalTree = ConfirmAgainstFinalTree(complete.Root, walk.WrittenNodes);
            AttributeCollisions(complete.Diagnostics, walk.Levels);
            var lifts = AttributeForwarding(complete.Root, walk, operation);
            if (lifts.Attributed + lifts.Unattributed != observations.ImplicitCallsSynthesized)
                throw new InvalidOperationException($"Found {lifts.Attributed + lifts.Unattributed} lifted calls, but the resolver synthesized {observations.ImplicitCallsSynthesized}.");
            var (tree, treeSkip) = EncodeForPromotion(beforeExposure, complete, walk.Levels);

            return new(corpus, id, source, null, walk.Levels, walk.Occurrences, walk.Families, finalTree, lifts, tree, treeSkip);
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
    private static FinalTreeConfirmation ConfirmAgainstFinalTree(Algorithm finalRoot, IReadOnlyList<WrittenName> written)
    {
        var final = new Dictionary<(SourceSpan Span, string Name), (bool Parameter, bool Lexical)>();
        var collector = new NameNodes(final);
        collector.VisitAlgorithm(finalRoot);

        var (confirmed, noSpan, noCounterpart) = (0, 0, 0);
        foreach (var occurrence in written)
        {
            if (occurrence.Span is not { } span)
            {
                noSpan++;
                continue;
            }

            if (!final.TryGetValue((span, occurrence.Name), out var kinds))
            {
                noCounterpart++;
                continue;
            }

            if (occurrence.IsParameter ? !kinds.Parameter : !kinds.Lexical)
            {
                throw new InvalidOperationException(
                    $"the written name '{occurrence.Name}' at {span} was detected as {(occurrence.IsParameter ? "a parameter" : "a lexical reference")} " +
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

    /// <summary>
    /// The collision validator's verdicts: each <see cref="DiagnosticCode.ParameterPropertyCollision"/> the complete
    /// pipeline reported is located at a declaration span of exactly one detected property, which conflicts at its
    /// level. A reported span no detected declaration carries throws.
    /// </summary>
    private static void AttributeCollisions(IReadOnlyList<Diagnostic> diagnostics, IReadOnlyList<FrontEndLevel> levels)
    {
        var reported = new HashSet<SourceSpan>();
        foreach (var diagnostic in diagnostics.Where(static diagnostic => diagnostic.Code == DiagnosticCode.ParameterPropertyCollision))
        {
            var span = diagnostic.Span ?? throw new InvalidOperationException("a parameter/property collision was reported without a span.");
            if (!reported.Add(span))
                throw new InvalidOperationException($"the collision at {span} was reported twice.");
        }

        var attributed = new HashSet<SourceSpan>();
        foreach (var level in levels)
        {
            List<string>? conflicts = null;
            foreach (var property in level.Declared)
            {
                var hits = property.DeclarationSpans.Where(reported.Contains).ToList();
                if (hits.Count == 0)
                    continue;
                if (hits.Count != property.DeclarationSpans.Count)
                    throw new InvalidOperationException($"property '{property.Name}' has a collision at only some of its written declarations.");
                if (!attributed.Add(hits[0]) || hits.Skip(1).Any(span => !attributed.Add(span)))
                    throw new InvalidOperationException($"the collision at {hits[0]} is declared by two detected properties.");
                (conflicts ??= []).Add(property.Name!);
            }

            level.Conflicts = conflicts ?? (IReadOnlyList<string>)[];
        }

        if (!reported.SetEquals(attributed))
        {
            throw new InvalidOperationException(
                $"a parameter/property collision was reported at {string.Join(", ", reported.Except(attributed))}, where no detected level declares a property.");
        }
    }

    /// <summary>
    /// The forwarding sources C# chose, read from the lifted calls of the complete pipeline's tree (see the class
    /// documentation). Every added parameter must occur in a synthesized argument at that level.
    /// </summary>
    private static FrontEndLifts AttributeForwarding(Algorithm finalRoot, Walk walk, StaticStructureOperation operation)
    {
        var written = new Dictionary<(SourceSpan Span, string Name), WrittenName?>();
        foreach (var occurrence in walk.WrittenNodes)
        {
            if (occurrence.Span is not { } span)
                continue;
            // A span written twice in two levels (a shared node) has no one level: it is marked, never guessed.
            var key = (span, occurrence.Name);
            written[key] = written.TryGetValue(key, out var known) && !ReferenceEquals(known?.Level, occurrence.Level)
                ? null
                : occurrence;
        }

        var collector = new LiftedCalls();
        collector.VisitAlgorithm(finalRoot);

        var (attributed, unattributed) = (0, 0);
        var seen = new HashSet<(SourceSpan, string)>();
        foreach (var (span, name, arguments) in collector.Found)
        {
            if (!seen.Add((span, name)))
                continue;
            if (!written.TryGetValue((span, name), out var found) || found is not { } occurrence)
            {
                unattributed++;
                continue;
            }

            attributed++;
            var signature = CalleeSignature(occurrence, operation)
                ?? throw new InvalidOperationException($"No lifting signature for '{name}' at {span}.");
            var actual = ArgumentBindings(arguments);
            var level = occurrence.Level;
            var source = (Algorithm.User)operation.SourceOf(level.Key);
            var bareForwarding = !level.Infers && source.Output.Count == 1
                && ReferenceEquals(source.Output[0], operation.WrittenExpression(level.Key, occurrence.Reference));
            // A closed bare row may omit an unbound top-level collector. Every other callee capture has
            // one synthesized read in declaration order, even for repeated names and structural patterns.
            var patterns = signature.ParameterPatterns.Where(pattern => !(bareForwarding
                && pattern is CaptureParameterPattern { Kind: ParameterKind.Collecting } collector
                && operation.Binding(level.Key, collector.Name, StaticQueryProjection.OwnedBinding).Kind != StaticFactKind.Parameter));
            var expected = ParameterPattern.FlattenCaptures(patterns).Select(capture => capture.Name).ToArray();
            if (expected.SequenceEqual(actual, StringComparer.Ordinal))
            {
                foreach (var bound in actual)
                    RecordForwarding(level, bound);
            }
            else if (!bareForwarding && source.ParameterPatterns is [CaptureParameterPattern { Kind: ParameterKind.Collecting } caller]
                && signature.ParameterPatterns is [var group]
                && ParameterPattern.StructuralItems(group) is [CaptureParameterPattern { Kind: ParameterKind.Collecting } requested]
                && actual is [var supplied] && supplied == caller.Name)
            {
                // Forwarding by shape may supply a different name. Ask Lean about the CALLEE's name and
                // retain the actual argument for the disagreement report.
                level.Forwardings.Add(new(supplied, FrontEndForwardingKind.Own, 0, requested.Name));
            }
            else
            {
                throw new InvalidOperationException($"'{name}' at {span} requests [{string.Join(", ", expected)}] but forwards [{string.Join(", ", actual)}].");
            }
        }

        // With just one required binding at a definite value operand the absence of a lift distinguishes
        // its unavailable source. A multi-name refusal alone cannot identify which input was missing.
        foreach (var (key, found) in written)
        {
            if (seen.Contains(key) || found is not { ValueOperand: true, IsParameter: false } occurrence || occurrence.Level.Infers)
                continue;
            var signature = CalleeSignature(occurrence, operation);
            if (signature is { AcceptsZeroSuppliedArguments: false }
                && signature.Parameters.Select(parameter => parameter.Name).Distinct(StringComparer.Ordinal).ToArray() is [var missing])
                occurrence.Level.Forwardings.Add(new(missing, FrontEndForwardingKind.Unavailable, 0));
        }

        foreach (var level in walk.Levels)
        {
            foreach (var name in level.Forwarded)
                if (!level.Forwardings.Any(source => source.Name == name))
                    throw new InvalidOperationException($"level {level.Index} acquired '{name}' without a matching synthesized read.");
        }

        return new(attributed, unattributed);
    }

    /// <summary>The selected callee's requested bindings, independent of the arguments found in its call.</summary>
    private static CallableSignature? CalleeSignature(WrittenName occurrence, StaticStructureOperation operation)
    {
        var scope = occurrence.Level.Key;
        StaticScopeKey? callee;
        if (occurrence.Reference is Expr.DotCall edge)
        {
            if (edge.Args is not null)
                return null;
            var member = operation.Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, scope, StaticQueryProjection.MemberSelection,
                node: operation.WrittenExpression(scope, edge)));
            callee = member.Kind == StaticFactKind.Structure ? member.Scope : null;
        }
        else
        {
            var binding = operation.Binding(scope, occurrence.Name);
            callee = binding.Kind == StaticFactKind.Declaration ? operation.ContextOf(binding.Scope!, binding.Property!.Value) : null;
        }

        if (callee is null)
            return null;
        var endpoint = operation.Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, callee, StaticQueryProjection.InvocationTarget));
        if (endpoint.Scope is not { } target || endpoint.Kind != StaticFactKind.Structure)
            return null;
        var algorithm = operation.ResolvedView(target) ?? operation.SourceOf(target);
        return algorithm is Algorithm.Conditional family
            ? ImplicitArgumentResolver.DeriveFamilyLiftingSignature(occurrence.Name, family).Signature
            : CallableSignature.FromAlgorithm(occurrence.Name, algorithm);
    }

    private static void RecordForwarding(FrontEndLevel level, string name)
    {
        if (level.Forwarded.Contains(name))
        {
            level.Forwardings.Add(new(name, FrontEndForwardingKind.Forwarded, 0));
            return;
        }

        if (level.Parameters.Contains(name))
        {
            level.Forwardings.Add(new(name, FrontEndForwardingKind.Own, 0));
            return;
        }

        // The argument is a parameter READ: at run time it reads the nearest enclosing activation that binds the name,
        // whose completed signature holds a forwarded parameter as well as the name-resolution ones.
        var depth = 1;
        for (var current = level.Parent; current is { Index: >= 0 }; current = current.Parent, depth++)
        {
            if (current.Parameters.Contains(name) || current.Forwarded.Contains(name))
            {
                level.Forwardings.Add(new(name, FrontEndForwardingKind.Captured, depth));
                return;
            }
        }

        throw new InvalidOperationException($"forwarding supplied '{name}' from a level where no parameter binds it.");
    }

    /// <summary>The ordered parameter reads of one synthesized bundle, including repeated captures.</summary>
    private static IReadOnlyList<string> ArgumentBindings(IEnumerable<Expr> arguments)
    {
        var names = new List<string>();
        var pending = new Stack<Expr>(arguments.Reverse());
        while (pending.TryPop(out var expression))
        {
            if (expression is Expr.Param(var name))
            {
                names.Add(name);
                continue;
            }

            if (expression is Expr.Resolve or Expr.AlgorithmExpr)
                throw new NotSupportedException($"a synthesized forwarding argument holds a {expression.GetType().Name}.");
            foreach (var child in Children(expression).Reverse())
                pending.Push(child);
        }

        return names;
    }

    /// <summary>
    /// Every lifted reference of a tree: a call at its callee name's own span, or a dot edge given arguments, whose
    /// arguments are all synthesized (no node of them carries a span) — the shape the resolver gives a lifted reference
    /// and a completed bare-forwarding row (a written call's callee span is never the call's, and a written argument
    /// has a span).
    /// </summary>
    private sealed class LiftedCalls : AstWalker
    {
        public List<(SourceSpan Span, string Name, IReadOnlyList<Expr> Arguments)> Found { get; } = [];

        public override void VisitExpr(Expr expression)
        {
            switch (expression)
            {
                case Expr.Call(Expr.Resolve callee, var arguments)
                    when callee.Span is { } span && expression.Span == span && arguments.Count > 0 && arguments.All(Synthesized):
                    Found.Add((span, callee.Name, arguments));
                    break;

                case Expr.DotCall { Args: { Count: > 0 } arguments } edge
                    when arguments.All(Synthesized) && (edge.EffectiveLexicalFallback.Span ?? edge.MemberSpan) is { } member:
                    Found.Add((member, NameOf(edge.EffectiveLexicalFallback), arguments));
                    break;
            }

            base.VisitExpr(expression);
        }

        private static bool Synthesized(Expr expression)
            => expression.Span is null && Children(expression).All(Synthesized);
    }

    /// <summary>
    /// Lean needs the providers' resolved reference shapes for open lookup. Exposure is decided later and is
    /// absent at detection. Programs with invalid targets or an unrepresentable literal carry a counted skip reason.
    /// </summary>
    private static (string? Tree, string? SkipReason) EncodeForPromotion(Algorithm beforeExposure, SourceProvenance complete, IReadOnlyList<FrontEndLevel> levels)
    {
        if (!levels.Any(static level => level.HasOpens && level.Promotions.Any(static promotion => promotion.IsAsked)))
            return (null, null);
        // The probe requires valid open targets. Other diagnostics (including an ambiguous *use* of valid opens)
        // leave that premise intact. Use the resolved providers of the detected tree, before exposure classification.
        if (complete.Diagnostics.Any(diagnostic => diagnostic.Code is DiagnosticCode.BadOpenForm or DiagnosticCode.OpenTargetIsParameter
                or DiagnosticCode.IllegalInOpen or DiagnosticCode.UnresolvedOpenTarget))
            return (null, InvalidOpenTarget);

        try
        {
            return (LeanAstEncoder.EncodeProgram(beforeExposure), null);
        }
        catch (NotSupportedException error) when (error.Message.StartsWith("LeanAstEncoder cannot encode the non-integer or non-finite number", StringComparison.Ordinal))
        {
            return (null, UnspellableLiteral);
        }
    }

    private static IReadOnlyList<string> ParameterNames(Algorithm.User body)
        => body.Parameters.Select(static parameter => parameter.Name).Distinct(StringComparer.Ordinal).ToArray();

    private static IReadOnlyList<string> PropertyNames(Algorithm body)
        => body.Properties.Select(static property => property.Name
            ?? throw new NotSupportedException("a property without a name has no owner-level entry.")).ToArray();

    private static string NameOf(Expr node) => node switch
    {
        Expr.Param(var parameter) => parameter,
        Expr.Resolve(var reference) => reference,
        _ => throw new NotSupportedException($"a {node.GetType().Name}, not a name."),
    };

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

    /// <summary>A classified name with the span it was written at (a dot edge's fallback name: its member token's) and its level.</summary>
    internal readonly record struct WrittenName(string Name, bool IsParameter, SourceSpan? Span, FrontEndLevel Level,
        Expr Reference, bool ValueOperand);

    private sealed class Walk(StaticStructureOperation operation)
    {
        private readonly StaticScopeKey _preludeKey = operation.Queries.Keys.Root;
        private FrontEndLevel? _prelude;

        public List<FrontEndLevel> Levels { get; } = [];
        public List<FrontEndOccurrence> Occurrences { get; } = [];
        public List<FrontEndFamily> Families { get; } = [];
        /// <summary>Every classified name with the span it was written at (a dot edge's fallback name: its member token's).</summary>
        public List<WrittenName> WrittenNodes { get; } = [];

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
            Body(user, _prelude, branchPattern: null, operation.Root, isProgramRoot: true, path: []);
        }

        private void Nested(Algorithm algorithm, string name, FrontEndLevel parent, IReadOnlyList<FrontEndPathStep>? path)
        {
            switch (algorithm)
            {
                case Algorithm.Builtin:
                    break;

                case Algorithm.Conditional family:
                    Family(family, name, parent, path);
                    break;

                case Algorithm.User user:
                    Body(user, parent, branchPattern: null, operation.ContextOf(parent.Key, user), isProgramRoot: false, path);
                    break;

                default:
                    throw new NotSupportedException($"a detected tree holds a {algorithm.GetType().Name}.");
            }
        }

        private void Family(Algorithm.Conditional family, string name, FrontEndLevel parent, IReadOnlyList<FrontEndPathStep>? path)
        {
            // A parsed family owns no opens, so it adds no level of its own: its branch bodies stand directly under
            // the level that declares the family (ParameterDetector.ProcessConditionalProperty).
            if (family.Opens.Count > 0)
                throw new NotSupportedException("a clause family with its own open list (host-built only).");

            Families.Add(DescribeFamily(name, family));
            for (var index = 0; index < family.Branches.Count; index++)
            {
                var branch = family.Branches[index];
                if (branch.Body is not Algorithm.User body)
                    throw new NotSupportedException($"a clause body that is a {branch.Body.GetType().Name} (host-built only).");
                if (body.DeferredRegion is not null)
                    throw new NotSupportedException("a deferred module region.");
                Body(body, parent, branch.Pattern, operation.ContextOf(parent.Key, body, branch.Pattern), isProgramRoot: false,
                    path is null ? null : [.. parent.Path!, new(name, index)]);
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

        private void Body(Algorithm.User body, FrontEndLevel parent, Pattern? branchPattern, StaticScopeKey key, bool isProgramRoot,
            IReadOnlyList<FrontEndPathStep>? path)
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

            // C#'s BodyContext.Infers for a raw-source detection: an ordinary body with no written parameter list.
            var infers = branchPattern is null && !body.HasExplicitParameterList;
            var level = new FrontEndLevel(Levels.Count, parent, key, parameters, PropertyNames(body), isProgramRoot,
                body.Properties, infers, body.Opens.Count > 0, path);
            parent.HasChildLevel = true;
            Levels.Add(level);
            Promote(level);

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
                    Nested(property.Value, property.Name!, level, path is null ? null : [.. path, new(property.Name!)]);
                }
            }

            foreach (var row in body.Output)
                Row(row, level);
        }

        /// <summary>
        /// Promotion, for every candidate name of the level: the detection operation's <c>IsInput</c> verdict and, for
        /// a name it did not promote, the inference binding that says why (see <see cref="FrontEndPromotionClass"/>).
        /// </summary>
        private void Promote(FrontEndLevel level)
        {
            var candidates = operation.Queries.CandidateNames(level.Key);
            if (!level.Infers)
            {
                if (candidates.Count > 0)
                    throw new InvalidOperationException("a level with closed inputs has inference candidates.");
                return;
            }

            StaticInputGraph? graph = null;
            foreach (var name in candidates)
            {
                var input = operation.Read(StaticQueryKey.IsInput(level.Key, name));
                var binding = operation.Binding(level.Key, name, StaticQueryProjection.InferenceBinding);
                if (input.Kind == StaticFactKind.Yes)
                {
                    if (!level.Parameters.Contains(name))
                        throw new InvalidOperationException($"'{name}' is an inferred input of its level but not among the detected parameters.");
                    if (binding.Kind == StaticFactKind.Parameter)
                        throw new InvalidOperationException($"'{name}' was promoted despite an established parameter binding, which bypasses Lean's promotion probe.");
                    level.Promotions.Add(new(name, FrontEndPromotionClass.Promoted, ThroughOpen: false));
                    continue;
                }

                if (input.Kind != StaticFactKind.No)
                    throw new InvalidOperationException($"the promotion of '{name}' is undecided ({input.Kind}).");
                if (level.Parameters.Contains(name))
                    throw new InvalidOperationException($"'{name}' is a detected parameter of an inferring level but not an inferred input.");

                if (binding.Kind == StaticFactKind.Missing)
                {
                    var raw = (Algorithm.User)operation.SourceOf(level.Key);
                    graph ??= new StaticInputGraph(AstHelpers.WrittenRows(raw));
                    var uses = operation.Read(StaticQueryKey.Project(StaticQueryKind.IsInput, level.Key,
                        StaticQueryProjection.InputUses, name, length: graph.Uses[name].Count));
                    if (uses.Kind != StaticFactKind.No && !IsParameterRootedReference(raw, level))
                        throw new InvalidOperationException($"'{name}' has a participating use, no binding and no inferred parameter.");
                }
                var throughOpen = binding.Kind == StaticFactKind.Declaration && !OnChain(level, binding.Scope);
                if (throughOpen && !level.HasOpens)
                    throw new InvalidOperationException($"'{name}' resolves to a declaration off its chain, which writes no open.");
                level.Promotions.Add(binding.Kind switch
                {
                    StaticFactKind.Parameter => new(name, FrontEndPromotionClass.EnclosingParameter, ThroughOpen: false),
                    StaticFactKind.Declaration when ReferenceEquals(binding.Scope, _preludeKey) && !LeanPrelude.Contains(name)
                        => new(name, FrontEndPromotionClass.PreludeOnly, ThroughOpen: false),
                    StaticFactKind.Declaration => new(name, FrontEndPromotionClass.Resolves, throughOpen),
                    StaticFactKind.Missing => new(name, FrontEndPromotionClass.NotParticipating, ThroughOpen: false),
                    StaticFactKind.Ambiguous => new(name, FrontEndPromotionClass.AmbiguousOpen, ThroughOpen: true),
                    _ => throw new InvalidOperationException($"'{name}' has inference binding {binding.Kind}, which no promotion class describes."),
                });
            }

            if (level.Parameters.Any(parameter => level.Promotions.All(promotion => promotion.Name != parameter)))
                throw new InvalidOperationException("an inferring level has a detected parameter that is no candidate name.");
        }

        // OD-B can suppress an otherwise participating fallback on a single parameter-rooted path.
        private bool IsParameterRootedReference(Algorithm.User raw, FrontEndLevel level)
        {
            if (level.IsNeverCalledRoot || AstHelpers.WrittenRows(raw) is not [Expr.DotCall { Args: null } path])
                return false;
            Expr head = path;
            while (head is Expr.DotCall { Args: null } step)
                head = step.Target;
            return head is Expr.Param || head is Expr.Resolve(var name)
                && operation.Binding(level.Key, name, StaticQueryProjection.InferenceBinding).Kind == StaticFactKind.Parameter;
        }

        private static bool OnChain(FrontEndLevel level, StaticScopeKey? scope)
        {
            for (FrontEndLevel? current = level; current is not null; current = current.Parent)
            {
                if (ReferenceEquals(current.Key, scope))
                    return true;
            }

            return false;
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
                Nested(block.Algorithm, "<anonymous>", _prelude!, path: null);
                return;
            }

            foreach (var child in Children(expression))
                OpenInterior(child);
        }

        private void Row(Expr expression, FrontEndLevel level, bool valueOperand = false)
        {
            switch (expression)
            {
                case Expr.Resolve or Expr.Param:
                    Name(expression, level, FrontEndSite.BareName, valueOperand: valueOperand);
                    return;

                case Expr.AlgorithmExpr block:
                    Nested(block.Algorithm, "<anonymous>", level, path: null);
                    return;

                case Expr.Grace:
                    throw new NotSupportedException("a Grace marker survived parameter detection.");

                case Expr.DotCall edge:
                    Row(edge.Target, level);
                    Name(edge.EffectiveLexicalFallback, level, FrontEndSite.DotFallback, edge.MemberSpan, edge, valueOperand);
                    if (edge.Args is { } arguments)
                    {
                        foreach (var argument in arguments)
                            Row(argument, level);
                    }

                    return;
            }

            foreach (var child in Children(expression))
                Row(child, level, valueOperand: expression is Expr.Unary or Expr.Binary or Expr.Comparison or Expr.Index
                    or Expr.Capture or Expr.ListLiteral or Expr.SequenceSpread or Expr.SequenceConstruct);
        }

        private void Name(Expr node, FrontEndLevel level, FrontEndSite site, SourceSpan? writtenAt = null, Expr? callee = null, bool valueOperand = false)
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
            WrittenNodes.Add(new(name, isParameter, node.Span ?? writtenAt, level, callee ?? node, valueOperand));
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
