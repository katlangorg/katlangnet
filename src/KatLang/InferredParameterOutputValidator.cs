namespace KatLang;

/// <summary>
/// The output rule over COMPLETED signatures (X-07): an algorithm that has parameters must define an
/// output. The parser enforces it on every WRITTEN parameter list of the raw syntax tree
/// (<see cref="AlgorithmValidation.FindExplicitParameterOutputViolations"/>) and the evaluator's
/// pre-evaluation gate on every tree it is handed, but an OPEN body's parameter list is final only
/// after inference — the names parameter detection infers from what its definition uses, and the
/// parameters formula lifting forwards to the callables it uses — so a parameterized, output-less
/// body whose parameters were all inferred used to reach the evaluator and fail there, unpositioned,
/// as a run-time error of the whole program. This pass runs once implicit-argument resolution has
/// completed every signature and applies the gate's own test (a stored parameter-pattern list that is
/// not empty, and no output row) to every algorithm whose parameters were INFERRED — a written list
/// was reported at parse time and is never reported twice — reporting the same error kind
/// (<see cref="DiagnosticCode.ExplicitParametersRequireOutput"/>) before evaluation, positioned where
/// the source explains it (<see cref="AnchorOf"/>) and worded for inferred parameters
/// (<see cref="AlgorithmValidation.InferredParametersRequireOutputMessage"/>). A violation with no
/// position at all (a host-built tree) is left to the evaluator's gate, which reports the same kind.
/// Lean: <c>validateExplicitParamOutputInvariant</c>, which <c>runResultM</c> runs before
/// evaluation; the phase, the position and the wording are C#-only.
/// </summary>
internal sealed class InferredParameterOutputValidator : AstWalker
{
    private readonly DiagnosticBag _diagnostics;
    private readonly Algorithm? _programRoot;
    // A node shared by several parents is validated once (its verdict is node-local): the first
    // reach positions its report, like every front-end validator's per-node reporting.
    private readonly HashSet<object> _visited = new(ReferenceEqualityComparer.Instance);
    private readonly NestedReachIndex _nestedAlgorithms = new();
    // The import site of the module content the walk is inside (see ImportSite): where an imported
    // violation — which has no span of its own — is reported. Starts at the site a deferred region
    // recorded for its body.
    private SourceSpan? _importSite;
    // The written definition of the algorithm about to be visited: the declaring property's name when
    // it is a property's direct value, the block literal when it is one.
    private SourceSpan? _definition;

    private InferredParameterOutputValidator(DiagnosticBag diagnostics, Algorithm? programRoot, SourceSpan? importSite)
    {
        _diagnostics = diagnostics;
        _programRoot = programRoot;
        _importSite = importSite;
    }

    protected override bool VisitsExplicitParameterDeclarations => false;

    /// <summary>Validates a completed program tree; <paramref name="programRoot"/> is its root.</summary>
    internal static void ValidateProgram(Algorithm programRoot, DiagnosticBag diagnostics)
        => new InferredParameterOutputValidator(diagnostics, programRoot, importSite: null).VisitAlgorithm(programRoot);

    /// <summary>
    /// Validates a materialized deferred branch body, starting from the import site the region
    /// recorded for the body.
    /// </summary>
    internal static void ValidateDeferredBody(Algorithm body, DiagnosticBag diagnostics, SourceSpan? importSite)
        => new InferredParameterOutputValidator(diagnostics, programRoot: null, importSite).VisitAlgorithm(body);

    public override void VisitAlgorithm(Algorithm algorithm)
    {
        // A deferred region's provisional body is validated when it materializes.
        if (algorithm.DeferredRegion is not null || !_visited.Add(algorithm))
            return;

        base.VisitAlgorithm(algorithm);
    }

    protected override void VisitUserAlgorithm(Algorithm.User algorithm)
    {
        // The definition belongs to this algorithm only: what it holds is defined by its own
        // properties and blocks.
        var definition = _definition;
        _definition = null;
        if (!algorithm.HasExplicitParameterList
            && algorithm.ParameterPatterns.Count > 0
            && algorithm.Output.Count == 0
            && AnchorOf(algorithm, definition) is { } anchor)
        {
            _diagnostics.Report(
                DiagnosticCode.ExplicitParametersRequireOutput,
                anchor,
                algorithm.ParameterPatterns,
                static parameters => AlgorithmValidation.InferredParametersRequireOutputMessage(parameters));
        }

        try { base.VisitUserAlgorithm(algorithm); }
        finally { _definition = definition; }
    }

    protected override void VisitProperty(Property property)
    {
        var savedSite = _importSite;
        var savedDefinition = _definition;
        if (ImportSite.OfProperty(property) is { } site)
            _importSite = site;
        _definition = property.FirstDeclarationSpan;
        try { VisitAlgorithm(property.Value); }
        finally
        {
            _importSite = savedSite;
            _definition = savedDefinition;
        }
    }

    public override void VisitExpr(Expr expr)
    {
        // Only a nested algorithm can hold a violation: a subtree that reaches none is not walked.
        if (!_nestedAlgorithms.Reaches(expr) || !_visited.Add(expr))
            return;

        var savedSite = _importSite;
        var savedDefinition = _definition;
        if (expr is Expr.AlgorithmExpr block)
        {
            if (ImportSite.OfBlock(block) is { } site)
                _importSite = site;
            _definition = block.Span;
        }

        try { base.VisitExpr(expr); }
        finally
        {
            _importSite = savedSite;
            _definition = savedDefinition;
        }
    }

    // A call argument bundle shared by several call nodes (FE-2) is visited once, like a shared node —
    // and not at all when it reaches no algorithm.
    private protected override void VisitCallArguments(OutputBundle arguments)
    {
        if (_nestedAlgorithms.Reaches(arguments) && _visited.Add(arguments))
            base.VisitCallArguments(arguments);
    }

    /// <summary>
    /// Where an output-less algorithm with inferred parameters is reported: the first source
    /// occurrence of its first parameter that parameter detection inferred from a name its definition
    /// uses (in signature order, so the parameter a call would bind first — the written list's
    /// convention); else its written definition, the declaring property or the block literal (a
    /// parameter formula lifting forwarded to a callable it uses has no occurrence of its own); else,
    /// for the program root, which no definition writes, the first row it writes; else the import
    /// site of the module content it lies in. Null for a host-built tree that carries none of these.
    /// </summary>
    private SourceSpan? AnchorOf(Algorithm.User algorithm, SourceSpan? definition)
    {
        var ownCount = algorithm.ForwardingParameterStart ?? algorithm.ParameterPatterns.Count;
        for (var index = 0; index < ownCount; index++)
        {
            foreach (var capture in ParameterPattern.EnumerateCaptures([algorithm.ParameterPatterns[index]]))
            {
                if (capture.InferredProvenance?.Span is { } occurrence)
                    return occurrence;
            }
        }

        if (definition is { } written)
            return written;

        if (ReferenceEquals(algorithm, _programRoot))
        {
            foreach (var row in AstHelpers.WrittenRows(algorithm))
            {
                if (row.Span is { } rowSpan)
                    return rowSpan;
            }
        }

        return _importSite;
    }
}
