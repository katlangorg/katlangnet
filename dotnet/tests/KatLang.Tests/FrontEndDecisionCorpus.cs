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

    /// <summary>
    /// A REFUSED forward that names this binding (Lean <c>unavailable</c>): a closed body's value operand stayed bare and
    /// this is the one name its callee requests that no parameter binds there, or bare forwarding reported this
    /// parameter as unforwardable.
    /// </summary>
    Unavailable,
}

/// <summary>One forwarded binding of a level, by name, with C#'s source and, when captured, the chain level it reads.</summary>
internal sealed record FrontEndForwarding(string Name, FrontEndForwardingKind Kind, int Level, string? Requested = null)
{
    /// <summary>
    /// For a by-shape supply (<see cref="Requested"/> is the callee's own name for the binding): the source forwarding BY
    /// NAME has for that name at the level, as a Lean <c>ForwardingSource</c> term, read from the detection's
    /// owned-binding fact. It is what <c>forwardingSource</c> must answer for the requested name, since that function
    /// decides by name only.
    /// </summary>
    public string? ByName { get; init; }
}

/// <summary>
/// What the pipeline's OUTPUT shows about the role formula lifting gave one supplied slot of a written call. Lifting
/// can change the tree at a bare name or an argumentless member path whose
/// invocation endpoint has a nameable lifting signature that requires supplied arguments. In a VALUE role such a
/// reference becomes a synthesized call; in a CALLABLE role it stays as written. An unnameable family at a value
/// slot of an inferring body carries a diagnostic at that reference.
/// </summary>
internal enum FrontEndSlotOutcome
{
    /// <summary>The reference was lifted there: the slot's role was VALUE.</summary>
    ShownValue,

    /// <summary>The resolver reported an unnameable family at this reference when it tried to lift it as a value.</summary>
    ReportedValue,

    /// <summary>
    /// The reference stayed bare where nothing could have refused its lift (an inferring level, or a closed level in
    /// which every requested name has a parameter binding or the by-shape supply applies): the slot's role was CALLABLE.
    /// </summary>
    ShownCallable,

    /// <summary>
    /// The reference stayed bare in a closed level that leaves a requested name unbound: a callable role and a refused
    /// lift (PAR-04) leave the same tree, so the output shows neither.
    /// </summary>
    RefusedOrCallable,

    /// <summary>
    /// This position supplies no evidence of its role from a lift or diagnostic: a literal, a parameter, a compound expression (its own
    /// children take THEIR consumers' roles), a name with no static endpoint, a callable that accepts zero supplied
    /// arguments, or a clause family with no lifting signature or diagnostic at this position.
    /// </summary>
    NoRoleSensitiveReference,

    /// <summary>
    /// A slot of a call whose callee kind the collector cannot read, such as an unstamped dot edge.
    /// </summary>
    CalleeNotRead,

    /// <summary>A dot receiver is an argument position only when the edge selects the extension fallback.</summary>
    ReceiverOutsideSupply,

    /// <summary>
    /// A slot after a spread DECLARATION-LEVEL OUTPUT SPREADING inserted (a marked call, or a marked reference formula
    /// lifting called). Whether such a slot's position still counts as known is that rule's own decision — a lift only
    /// signature selection decides leaves it known and is reported instead (<c>OutputSpreadReferenceNeedsCall</c>) — and
    /// the tree does not say which, so the position, and with it the role's table entry, is not read.
    /// </summary>
    PositionNotRead,

    /// <summary>
    /// A slot of a call the PARSER synthesized (the plumbing of an assignment deconstruction): it carries no source span
    /// to find its counterpart in the complete pipeline's tree by, and no written reference fills it.
    /// </summary>
    SynthesizedCall,

    /// <summary>A slot of a written call the complete pipeline's tree no longer holds at its span with the same slots.</summary>
    NoFinalCounterpart,
}

/// <summary>
/// One supplied slot whose role the output shows (<see cref="FrontEndSlotOutcome.ShownValue"/>,
/// <see cref="FrontEndSlotOutcome.ReportedValue"/> or
/// <see cref="FrontEndSlotOutcome.ShownCallable"/>): the written callee, its kind as read from its invocation endpoint
/// (never from the resolver's private classification), the supplied position with whether a spread slot precedes it in
/// the complete pipeline's call, and the role shown.
/// </summary>
internal sealed record FrontEndSlotRole(
    FrontEndLevel Level,
    string Callee,
    LiftingCallee Kind,
    int Position,
    bool PositionKnown,
    LiftingRole Role,
    string Reference);

/// <summary>
/// One closed lone row bare forwarding refused (<see cref="DiagnosticCode.UnforwardableParameter"/>): the
/// report count and the names of the unbound fixed captures identified in those reports.
/// </summary>
internal sealed record FrontEndBareRefusal(FrontEndLevel Level, string Callee, int Reports, IReadOnlyList<string> Attributed);

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

    /// <summary>The source of each forwarded capture occurrence and of each refused forward that names one binding.</summary>
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
internal readonly record struct FrontEndLifts(int Attributed, int Unattributed)
{
    /// <summary>
    /// Closed value operands left bare whose callee requests two or more names no parameter binds: the one observation
    /// (no lift) cannot be divided among them, so no source is recorded for any.
    /// </summary>
    public int MultiNameRefusals { get; init; }

    /// <summary>The unbound names of <see cref="MultiNameRefusals"/>.</summary>
    public int MultiNameRefusalNames { get; init; }
}

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
    string? TreeSkipReason = null)
{
    /// <summary>The supplied slots whose role the output shows, in written order.</summary>
    public IReadOnlyList<FrontEndSlotRole> SlotRoles { get; init; } = [];

    /// <summary>Every supplied slot of every written call, by what the output shows about it.</summary>
    public IReadOnlyDictionary<FrontEndSlotOutcome, int> SlotOutcomes { get; init; } = new Dictionary<FrontEndSlotOutcome, int>();

    /// <summary>The written calls and argument-carrying dot edges.</summary>
    public int WrittenCalls { get; init; }

    /// <summary>Argument slots and dot receivers, counted on the detected calls before classifying any position.</summary>
    public int WrittenPositions { get; init; }

    /// <summary>The closed lone rows bare forwarding refused.</summary>
    public IReadOnlyList<FrontEndBareRefusal> BareRefusals { get; init; } = [];
}

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
/// <c>shouldTreatAsImplicitParam</c>, <c>forwardingSource</c>, <c>conflictingOwnedNames</c>, <c>liftingSlotRole</c>).
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
/// binds the name. Each argument is checked against the callee's selected signature. A REFUSED forward is an
/// unavailable source where the refusal names one binding (<see cref="AttributeForwarding"/>,
/// <see cref="AttributeBareRefusals"/>), and the by-shape supply is recorded with both names
/// (<see cref="FrontEndForwarding.Requested"/>).</item>
/// <item>SLOT ROLES — the complete pipeline's tree again: a written slot that holds a role-sensitive reference shows
/// the role lifting gave it, by the lift it holds or by the lift it does not hold where nothing could have refused
/// one, or by an unliftable-family diagnostic at the reference (<see cref="AttributeSlotRoles"/>). Callee classification is private to the
/// pass, and nothing is added to it.</item>
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
    public const string WitnessCorpus = "witness";
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
    /// Every program of the four differential corpora, in corpus order — the explorer's, the specification's, the
    /// SEM-2B generated corpus's identity-prelude members, and the tutorial's source fences — and then the members of
    /// the front-end witnesses (<see cref="FrontEndWitnesses"/>).
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
        foreach (var witness in FrontEndWitnesses.All)
        {
            foreach (var member in witness.Members)
                programs.Add(Collect(WitnessCorpus, member.Id, member.Source));
        }

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
            var lifted = new LiftedCalls();
            lifted.VisitAlgorithm(complete.Root);
            var lifts = AttributeForwarding(lifted.Found, walk, operation);
            if (lifts.Attributed + lifts.Unattributed != observations.ImplicitCallsSynthesized)
                throw new InvalidOperationException($"Found {lifts.Attributed + lifts.Unattributed} lifted calls, but the resolver synthesized {observations.ImplicitCallsSynthesized}.");
            var (slotRoles, slotOutcomes) = AttributeSlotRoles(complete, walk, operation);
            var bareRefusals = AttributeBareRefusals(complete.Diagnostics, walk, operation);
            var (tree, treeSkip) = EncodeForPromotion(beforeExposure, complete, walk.Levels);

            return new(corpus, id, source, null, walk.Levels, walk.Occurrences, walk.Families, finalTree, lifts, tree, treeSkip)
            {
                SlotRoles = slotRoles,
                SlotOutcomes = slotOutcomes,
                WrittenCalls = walk.Calls.Count,
                WrittenPositions = walk.Calls.Sum(static call => call.Slots.Count),
                BareRefusals = bareRefusals,
            };
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
    private static FrontEndLifts AttributeForwarding(
        IReadOnlyList<(SourceSpan Span, string Name, IReadOnlyList<Expr> Arguments)> liftedCalls, Walk walk, StaticStructureOperation operation)
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

        var (attributed, unattributed) = (0, 0);
        var seen = new HashSet<(SourceSpan, string)>();
        foreach (var (span, name, arguments) in liftedCalls)
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
            else if (!bareForwarding && ByShapeSupply(source, signature) is (var caller, var requested)
                && actual is [var supplied] && supplied == caller)
            {
                // THE BY-SHAPE RULE (KatLang.lean, "Implicit argument resolution"; ownership-and-lookup.md): a caller whose
                // whole written list is one collector re-supplies a callee whose whole list is one group holding a lone
                // collector, whatever the two are named. The read is the caller's own collector; the callee's name is
                // kept beside it, because `forwardingSource` decides by NAME and has no arm for this rule.
                level.Forwardings.Add(new(supplied, FrontEndForwardingKind.Own, 0, requested) { ByName = ByNameSource(level, requested, operation) });
            }
            else
            {
                throw new InvalidOperationException($"'{name}' at {span} requests [{string.Join(", ", expected)}] but forwards [{string.Join(", ", actual)}].");
            }
        }

        // A REFUSED forward leaves ONE observation: a reference that stayed bare at a definite value operand of a closed
        // body, although its callee requires supplied arguments. It names one binding exactly when one requested name
        // has no parameter binding at that level (the detector's own owned-binding fact, FD-1): every other requested
        // name was available, so the refusal is that name's. Two or more unbound names share the one observation, and it
        // cannot be divided among them: no source is recorded for any, and the occurrence is counted.
        var (multiNameRefusals, multiNameRefusalNames) = (0, 0);
        foreach (var (key, found) in written)
        {
            if (seen.Contains(key) || found is not { ValueOperand: true } occurrence || occurrence.Level.Infers
                || occurrence.IsParameter && occurrence.Reference is not Expr.DotCall)
                continue;
            var signature = CalleeSignature(occurrence, operation);
            if (signature is not { AcceptsZeroSuppliedArguments: false })
                continue;
            var level = occurrence.Level;
            if (ByShapeSupply((Algorithm.User)operation.SourceOf(level.Key), signature) is not null)
                throw new InvalidOperationException($"'{occurrence.Name}' at {key.Span} stayed bare at a value operand although the by-shape supply applies.");
            switch (UnboundRequestedNames(level, signature, operation))
            {
                case []:
                    throw new InvalidOperationException(
                        $"'{occurrence.Name}' at {key.Span} stayed bare at a value operand of a closed body although a parameter binds every name it requests.");

                case [var missing]:
                    level.Forwardings.Add(new(missing, FrontEndForwardingKind.Unavailable, 0));
                    break;

                case var several:
                    multiNameRefusals++;
                    multiNameRefusalNames += several.Count;
                    break;
            }
        }

        foreach (var level in walk.Levels)
        {
            foreach (var name in level.Forwarded)
                if (!level.Forwardings.Any(source => source.Name == name))
                    throw new InvalidOperationException($"level {level.Index} acquired '{name}' without a matching synthesized read.");
        }

        return new(attributed, unattributed) { MultiNameRefusals = multiNameRefusals, MultiNameRefusalNames = multiNameRefusalNames };
    }

    /// <summary>
    /// The premise of the by-shape rule, read from the two written signatures alone (C#
    /// <c>ImplicitArgumentResolver.TryGetSingleCollectingForwarding</c>, the reference kernel's <c>canForwardStream</c>):
    /// the caller's whole written list is one top-level collector and the callee's whole list is one structural group
    /// holding a lone collector. The caller's and the callee's collector names, or null.
    /// </summary>
    private static (string Caller, string Requested)? ByShapeSupply(Algorithm.User caller, CallableSignature callee)
        => caller.ParameterPatterns is [CaptureParameterPattern { Kind: ParameterKind.Collecting } own]
            && callee.ParameterPatterns is [var group]
            && ParameterPattern.StructuralItems(group) is [CaptureParameterPattern { Kind: ParameterKind.Collecting } requested]
                ? (own.Name, requested.Name)
                : null;

    /// <summary>
    /// The source forwarding BY NAME has for <paramref name="name"/> at <paramref name="level"/>, as a Lean
    /// <c>ForwardingSource</c> term: the parameter binding the detection's owned-binding fact selects there, else a new
    /// forwarded parameter of an inferring body, else nothing.
    /// </summary>
    private static string ByNameSource(FrontEndLevel level, string name, StaticStructureOperation operation)
    {
        var binding = operation.Binding(level.Key, name, StaticQueryProjection.OwnedBinding);
        if (binding.Kind != StaticFactKind.Parameter)
            return level.Infers ? ".forwardedParameter" : ".unavailable";
        var depth = Walk.Depth(level, binding.Scope, name);
        return depth == 0 ? ".ownParameter" : $".capturedParameter {depth}";
    }

    /// <summary>
    /// The names a callee requests that no parameter binding supplies at <paramref name="level"/>, in the callee's
    /// declaration order: the detection's own owned-binding fact for each name there is not a parameter.
    /// </summary>
    private static IReadOnlyList<string> UnboundRequestedNames(FrontEndLevel level, CallableSignature signature, StaticStructureOperation operation)
        => signature.Parameters.Select(static parameter => parameter.Name).Distinct(StringComparer.Ordinal)
            .Where(name => operation.Binding(level.Key, name, StaticQueryProjection.OwnedBinding).Kind != StaticFactKind.Parameter)
            .ToArray();

    /// <summary>
    /// SLOT ROLES, as far as the pipeline's output shows them (see <see cref="FrontEndSlotOutcome"/>). Every supplied slot
    /// of every written call and argument-carrying dot edge is classified; a slot whose role is shown is recorded with
    /// the callee's kind, and that kind's row of C#'s own role table must give the role shown, or collection throws.
    ///
    /// <para>The callee's KIND is read from its Q3 invocation endpoint through the detection's static-structure
    /// operation — the same endpoint the forwarding check reads a callee's signature from — never from
    /// <c>ImplicitArgumentResolver.StaticCalleeKindOf</c>, which is private to the pass: a written block is a user
    /// callee; a parameter, an unresolved or ambiguous name and a name whose endpoint is no structure are dynamic; a
    /// declaration is its endpoint's kind. A dot edge is read by the verdict the COMPLETE pipeline's edge carries
    /// (<see cref="Expr.DotCall.ElaboratedMissSelection"/>): a selected fallback is the call of its fallback name with
    /// the receiver at position 0, and an edge the runtime decides gives its arguments a dynamic callee.</para>
    ///
    /// <para>A position is KNOWN unless a WRITTEN spread slot precedes it. After a spread the front end inserted for a
    /// marked declaration the position is not read (<see cref="FrontEndSlotOutcome.PositionNotRead"/>).</para>
    /// </summary>
    private static (IReadOnlyList<FrontEndSlotRole> Roles, IReadOnlyDictionary<FrontEndSlotOutcome, int> Outcomes) AttributeSlotRoles(
        SourceProvenance complete,
        Walk walk,
        StaticStructureOperation operation)
    {
        var outcomes = new Dictionary<FrontEndSlotOutcome, int>();
        if (walk.Calls.Count == 0)
            return ([], outcomes);

        void Count(FrontEndSlotOutcome outcome, int slots = 1)
            => outcomes[outcome] = outcomes.GetValueOrDefault(outcome) + slots;

        var refusedFamilies = complete.Diagnostics.Where(static diagnostic => diagnostic.Code == DiagnosticCode.UnliftableClauseFamily)
            .Select(static diagnostic => diagnostic.Span ?? throw new InvalidOperationException("an unliftable family was reported without a span."))
            .ToHashSet();
        // A node written in two levels (a shared node) has no one level: it is marked, never guessed.
        var byNode = new Dictionary<Expr, WrittenName?>(ReferenceEqualityComparer.Instance);
        foreach (var occurrence in walk.WrittenNodes)
            byNode[occurrence.Reference] = byNode.TryGetValue(occurrence.Reference, out var known) && !ReferenceEquals(known?.Level, occurrence.Level) ? null : occurrence;

        var final = new FinalCalls();
        final.VisitAlgorithm(complete.Root);

        var roles = new List<FrontEndSlotRole>();
        foreach (var call in walk.Calls)
        {
            if (ReadCall(call, final, operation) is not (var callee, var kind, var positions))
            {
                Count(final.Counterpart(call) is not null ? FrontEndSlotOutcome.CalleeNotRead
                    : call.Node is Expr.Call { Span: null } or Expr.DotCall { MemberSpan: null } ? FrontEndSlotOutcome.SynthesizedCall
                    : FrontEndSlotOutcome.NoFinalCounterpart, call.Slots.Count);
                continue;
            }

            // The receiver of an edge the runtime decides is no slot of a call: its role is the edge's, not a callee's.
            Count(FrontEndSlotOutcome.ReceiverOutsideSupply, call.Slots.Count - positions.Count);
            foreach (var (slot, rewritten, position, known) in positions)
            {
                if (known is not { } positionKnown)
                {
                    Count(FrontEndSlotOutcome.PositionNotRead);
                    continue;
                }

                var outcome = SlotOutcome(slot, rewritten, call.Level, byNode, refusedFamilies, operation);
                Count(outcome);
                if (outcome is not (FrontEndSlotOutcome.ShownValue or FrontEndSlotOutcome.ReportedValue or FrontEndSlotOutcome.ShownCallable))
                    continue;

                var shown = outcome == FrontEndSlotOutcome.ShownCallable ? LiftingRole.Callable : LiftingRole.Value;
                var table = FormulaLiftingRoles.SlotRole(kind, position, positionKnown);
                if (table != shown)
                {
                    throw new InvalidOperationException(
                        $"the call of '{callee}' gives position {position} ({(positionKnown ? "known" : "after a spread")}) the role {shown} in the pipeline's output, "
                        + $"but its endpoint's kind {kind.Kind} has the role {table} there: the callee kind read here is not the resolver's.");
                }

                roles.Add(new(call.Level, callee, kind, position, positionKnown, shown, byNode[slot]!.Value.Name));
            }
        }

        return (roles, outcomes);
    }

    /// <summary>What the output shows about the role of <paramref name="slot"/> (<see cref="FrontEndSlotOutcome"/>).</summary>
    private static FrontEndSlotOutcome SlotOutcome(
        Expr slot, Expr rewritten, FrontEndLevel level, Dictionary<Expr, WrittenName?> byNode,
        HashSet<SourceSpan> refusedFamilies, StaticStructureOperation operation)
    {
        if (!byNode.TryGetValue(slot, out var found) || found is not { Span: { } span } reference
            || reference.IsParameter && slot is not Expr.DotCall)
            return FrontEndSlotOutcome.NoRoleSensitiveReference;
        var result = rewritten is Expr.SequenceSpread { InsertedFor: not null } inserted ? inserted.Operand : rewritten;
        if (LiftedCalls.Read(result) is { } lift && lift.Name == reference.Name && lift.Span == span)
            return FrontEndSlotOutcome.ShownValue;
        if (slot is not (Expr.Resolve or Expr.DotCall { Args: null }))
            return FrontEndSlotOutcome.NoRoleSensitiveReference;
        var sameReference = result switch
        {
            Expr.Resolve(var name) => slot is Expr.Resolve && name == reference.Name && result.Span == span,
            Expr.DotCall { Args: null } edge => slot is Expr.DotCall && edge.Name == reference.Name && edge.MemberSpan == span,
            _ => false,
        };
        if (!sameReference)
            return FrontEndSlotOutcome.NoFinalCounterpart;
        if (reference.Reference.Span is { } extent && refusedFamilies.Contains(extent))
            return FrontEndSlotOutcome.ReportedValue;
        if (CalleeSignature(reference, operation) is not { AcceptsZeroSuppliedArguments: false } signature)
            return FrontEndSlotOutcome.NoRoleSensitiveReference;
        // Nothing could have refused the lift: the body infers its inputs, the by-shape supply applies, or a parameter
        // binds every requested name. So the reference stayed bare because its slot kept its callable identity.
        return level.Infers
            || ByShapeSupply((Algorithm.User)operation.SourceOf(level.Key), signature) is not null
            || UnboundRequestedNames(level, signature, operation).Count == 0
                ? FrontEndSlotOutcome.ShownCallable
                : FrontEndSlotOutcome.RefusedOrCallable;
    }

    /// <summary>
    /// One written call as this collector reads it: its callee's written name, its kind, and each supplied slot with its
    /// position and whether that position is known (null: not read, <see cref="FrontEndSlotOutcome.PositionNotRead"/>).
    /// Null when the callee kind is not read or the complete pipeline's tree holds no counterpart of the call.
    /// </summary>
    private static (string Callee, LiftingCallee Kind, IReadOnlyList<(Expr Slot, Expr Rewritten, int Position, bool? PositionKnown)> Positions)? ReadCall(
        WrittenCall call, FinalCalls final, StaticStructureOperation operation)
    {
        if (final.Counterpart(call) is not { } counterpart)
            return null;

        // The slots of the counterpart, in the written call's order (a dot edge's receiver first).
        IReadOnlyList<Expr> finalSlots = counterpart is Expr.DotCall { Args: { } finalArguments } finalEdge
            ? [finalEdge.Target, .. finalArguments]
            : [.. ((Expr.Call)counterpart).Args];
        var positions = new List<(Expr, Expr, int, bool?)>(call.Slots.Count);

        // A written spread ends the known positions; a spread only the complete pipeline holds was inserted for a marked
        // declaration, and what follows it is not read.
        void Add(int first, int leadingSlots)
        {
            bool? known = true;
            for (var index = first; index < call.Slots.Count; index++)
            {
                positions.Add((call.Slots[index], finalSlots[index], index - first + leadingSlots, known));
                if (call.Slots[index] is Expr.SequenceSpread)
                    known = known is null ? null : false;
                else if (finalSlots[index] is Expr.SequenceSpread)
                    known = null;
            }
        }

        if (call.Node is Expr.Call(var function, _))
        {
            if (CalleeKind(function, call.Level, operation) is not (var name, var kind))
                return null;
            Add(first: 0, leadingSlots: 0);
            return (name, kind, positions);
        }

        var edge = (Expr.DotCall)counterpart;
        if (edge.ElaboratedMissSelection is not { } selection)
            return null;
        switch (FormulaLiftingRoles.EdgeKind(edge, selection))
        {
            case DotEdgeKind.StructuralMember:
            {
                if (CalleeKind(call.Node, call.Level, operation) is not (var name, var kind))
                    return null;
                Add(first: 1, leadingSlots: 0);
                return (name, kind, positions);
            }

            case DotEdgeKind.Fallback:
            {
                // `R.F(args)` is the call `F(R, args)`: the receiver is slot 0.
                if (CalleeKind(((Expr.DotCall)call.Node).EffectiveLexicalFallback, call.Level, operation) is not (var name, var kind))
                    return null;
                Add(first: 0, leadingSlots: 0);
                return (name, kind, positions);
            }

            default:
                // The runtime decides the route, or the edge is an intrinsic: nothing is statically called, and the
                // arguments are classified as a dynamic callee's own slots (the receiver is not one of them).
                Add(first: 1, leadingSlots: 0);
                return ($".{edge.Name}", LiftingCallee.Dynamic, positions);
        }
    }

    /// <summary>
    /// The kind of a written callee, from its Q3 invocation endpoint (see <see cref="AttributeSlotRoles"/>); null for a
    /// callee outside the supported forms. A function of C#'s prelude that is no builtin (a Math member) is a
    /// strict-value callee: Lean models that kind, though not the member.
    /// </summary>
    private static (string Name, LiftingCallee Kind)? CalleeKind(Expr callee, FrontEndLevel level, StaticStructureOperation operation)
    {
        string name;
        StaticScopeKey target;
        switch (callee)
        {
            case Expr.AlgorithmExpr:
                return ("<block>", LiftingCallee.User);

            case Expr.Param(var parameter):
                return (parameter, LiftingCallee.Dynamic);

            case Expr.Resolve(var resolved):
            {
                name = resolved;
                var binding = operation.Binding(level.Key, name);
                if (binding.Kind != StaticFactKind.Declaration)
                    return (name, LiftingCallee.Dynamic);
                target = operation.ContextOf(binding.Scope!, binding.Property!.Value);
                break;
            }
            case Expr.DotCall member:
            {
                name = "." + member.Name;
                // Q3 selects the declaration from the written receiver and member, independently of the arguments.
                var selection = operation.Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, level.Key,
                    StaticQueryProjection.MemberSelection, stratum: StaticCycleCheck.Formation, node: operation.WrittenExpression(level.Key, member)));
                if (selection.Kind != StaticFactKind.Structure || selection.Scope is not { } selected)
                    return member.Args is null ? (name, LiftingCallee.Dynamic) : null;
                target = selected;
                break;
            }

            default:
                return null;
        }

        var endpoint = operation.Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, target, StaticQueryProjection.InvocationTarget));
        if (endpoint.Kind != StaticFactKind.Structure || endpoint.Scope is not { } scope)
            return (name, LiftingCallee.Dynamic);
        var algorithm = operation.SourceOf(scope);
        return algorithm switch
        {
            Algorithm.Builtin(var builtin) => (name, LiftingCallee.OfBuiltin(builtin)),
            Algorithm.Conditional => (name, LiftingCallee.Family),
            Algorithm.User => (name, ImplicitArgumentResolver.PreludeContext.For(hostOperations: null).IsStrictValue(algorithm)
                ? LiftingCallee.StrictValue : LiftingCallee.User),
            var other => throw new NotSupportedException($"the invocation endpoint of '{name}' is a {other.GetType().Name}."),
        };
    }

    /// <summary>
    /// The complete pipeline's written calls, by span: a call that is no lifted reference (a lifted reference's call
    /// stands at its callee name's own span), and an argument-carrying dot edge by its member token.
    /// </summary>
    private sealed class FinalCalls : AstWalker
    {
        private readonly Dictionary<SourceSpan, Expr?> _calls = [];
        private readonly Dictionary<SourceSpan, Expr?> _edges = [];

        public override void VisitExpr(Expr expression)
        {
            switch (expression)
            {
                case Expr.Call { Span: { } span } call when call.Function.Span != span:
                    Record(_calls, span, call);
                    break;

                case Expr.DotCall { Args: not null, MemberSpan: { } member } edge:
                    Record(_edges, member, edge);
                    break;
            }

            base.VisitExpr(expression);
        }

        // Two different nodes at one span have no one counterpart: marked, never guessed.
        private static void Record(Dictionary<SourceSpan, Expr?> nodes, SourceSpan span, Expr node)
            => nodes[span] = nodes.TryGetValue(span, out var known) && !ReferenceEquals(known, node) ? null : node;

        /// <summary>The node the complete pipeline holds for a written call: the same kind, at the same span, with the same slots.</summary>
        public Expr? Counterpart(WrittenCall call)
            => call.Node switch
            {
                Expr.Call written when written.Span is { } span && _calls.GetValueOrDefault(span) is Expr.Call found
                    && found.Args.Count == written.Args.Count => found,
                Expr.DotCall { MemberSpan: { } member, Args: { } arguments } when _edges.GetValueOrDefault(member) is Expr.DotCall { Args: { } found } edge
                    && found.Count == arguments.Count => edge,
                _ => null,
            };
    }

    /// <summary>
    /// BARE-FORWARDING REFUSALS. A closed body whose one row is a bare callee forwards by name (FWD-02), and a callee
    /// parameter no existing binding supplies is <see cref="DiagnosticCode.UnforwardableParameter"/>, reported ONCE PER
    /// PARAMETER at the row. Match the reported parameter against the callee's signature, since several reports can
    /// share a span. A missing fixed binding has an unavailable by-name source. A structural mismatch, including a
    /// name bound inside a different pattern, concerns the pattern form. Both can occur on the same row.
    /// </summary>
    private static IReadOnlyList<FrontEndBareRefusal> AttributeBareRefusals(IReadOnlyList<Diagnostic> diagnostics, Walk walk, StaticStructureOperation operation)
    {
        var reports = diagnostics.Where(static diagnostic => diagnostic.Code == DiagnosticCode.UnforwardableParameter)
            .ToLookup(static diagnostic => diagnostic.Span ?? throw new InvalidOperationException("an unforwardable parameter was reported without a span."));
        if (reports.Count == 0)
            return [];

        var refusals = new List<FrontEndBareRefusal>();
        var located = new HashSet<SourceSpan>();
        foreach (var occurrence in walk.WrittenNodes)
        {
            var level = occurrence.Level;
            if (level.Infers || occurrence.IsParameter && occurrence.Reference is not Expr.DotCall)
                continue;
            var body = (Algorithm.User)operation.SourceOf(level.Key);
            if (body.Output is not [var row] || row.Span is not { } span || !reports.Contains(span)
                || !ReferenceEquals(row, operation.WrittenExpression(level.Key, occurrence.Reference)))
                continue;
            if (!located.Add(span))
                throw new InvalidOperationException($"the unforwardable parameters at {span} belong to two written rows.");
            var signature = CalleeSignature(occurrence, operation)
                ?? throw new InvalidOperationException($"'{occurrence.Name}' at {span} has unforwardable parameters but no forwarding contract.");

            var parameters = signature.ParameterPatterns.Distinct(ParameterPattern.ContractComparer).ToArray();
            var reported = new HashSet<ParameterPattern>(ParameterPattern.ContractComparer);
            var names = new List<string>();
            foreach (var diagnostic in reports[span])
            {
                // The diagnostic exposes the parameter only in its message. Read its subject, never the proposed repair.
                var parameter = parameters.SingleOrDefault(pattern => diagnostic.Message.Contains(
                    $"its parameter '{ExprNameRenderer.BoundName(pattern.DisplayName)}'", StringComparison.Ordinal));
                if (parameter is null || !reported.Add(parameter))
                    throw new InvalidOperationException($"missing, ambiguous or duplicate parameter in the refusal at {span}: {diagnostic.Message}");
                if (parameter is CaptureParameterPattern { Kind: not ParameterKind.Collecting } capture
                    && operation.Binding(level.Key, capture.Name, StaticQueryProjection.OwnedBinding).Kind != StaticFactKind.Parameter)
                {
                    names.Add(capture.Name);
                    level.Forwardings.Add(new(capture.Name, FrontEndForwardingKind.Unavailable, 0));
                }
            }

            refusals.Add(new(level, occurrence.Name, reported.Count, names));
        }

        if (located.Count != reports.Count)
            throw new InvalidOperationException("an unforwardable parameter was reported at a span that is no closed body's lone bare row.");
        return refusals;
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
            if (Read(expression) is { } lifted)
                Found.Add(lifted);
            base.VisitExpr(expression);
        }

        internal static (SourceSpan Span, string Name, IReadOnlyList<Expr> Arguments)? Read(Expr expression) => expression switch
        {
            Expr.Call(Expr.Resolve callee, var arguments)
                when callee.Span is { } span && expression.Span == span && arguments.Count > 0 && arguments.All(Synthesized)
                => (span, callee.Name, arguments),
            Expr.DotCall { Args: { Count: > 0 } arguments } edge
                when arguments.All(Synthesized) && (edge.EffectiveLexicalFallback.Span ?? edge.MemberSpan) is { } member
                => (member, NameOf(edge.EffectiveLexicalFallback), arguments),
            _ => null,
        };

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

    /// <summary>
    /// A written call or argument-carrying dot edge of the detected tree, with its supplied slots in order (a dot edge's
    /// receiver first: <c>R.F(args)</c> supplies <c>R</c> before <c>args</c> when its fallback is selected).
    /// </summary>
    internal sealed record WrittenCall(FrontEndLevel Level, Expr Node, IReadOnlyList<Expr> Slots);

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

        /// <summary>Every written call and argument-carrying dot edge, in reading order.</summary>
        public List<WrittenCall> Calls { get; } = [];

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
            // Lean `Pattern.bind` carries a binder's collecting flag (Q-47: `.bind name true`) and no META kind, and
            // C# gives a META binder (and the parser's recovery placeholder) no vote: such a head has no faithful Lean
            // spelling. A collecting binder is spelled, and names no argument position in either engine.
            static bool Unrepresentable(Pattern pattern) => pattern switch
            {
                Pattern.Bind bind => bind.ParameterKind == ParameterKind.Meta || bind.IsRecoveryPlaceholder,
                Pattern.SequenceValue(var items) => items.Any(Unrepresentable),
                Pattern.ListValue(var items) => items.Any(Unrepresentable),
                _ => false,
            };

            if (family.Branches.Any(branch => Unrepresentable(branch.Pattern)))
                return new(name, null, null, "a clause head binds a META or recovery-placeholder name");

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
                        Calls.Add(new(level, edge, [edge.Target, .. arguments]));
                        foreach (var argument in arguments)
                            Row(argument, level);
                    }

                    return;
            }

            if (expression is Expr.Call call)
                Calls.Add(new(level, call, [.. call.Args]));

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
        internal static int Depth(FrontEndLevel level, StaticScopeKey? owner, string name)
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
