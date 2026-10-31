namespace KatLang;

/// <summary>
/// Explicit KatLang front-end boundary.
/// Starts from raw syntax and produces an elaborated program ready for
/// evaluator-facing and semantic-model consumers.
/// </summary>
internal static class FrontEndPipeline
{
    internal static FrontEndResult Process(string source)
    {
        var budget = new SourceProcessingBudget(null);
        if (TryRejectMainSource(source, budget, out var rejected))
            return rejected;

        return ProcessWithoutModuleElaboration(
            ElaborationInput.Parse(source, budget.CreateDiagnosticBag()), hostOperations: null, budget.Limits, CancellationToken.None);
    }

    /// <summary>
    /// Synchronous options-configured front end. Module elaboration is ASYNC-ONLY
    /// (obtaining source text for <c>load</c> awaits <see cref="RunOptions.DownloadCode"/>),
    /// so a downloader-configured options object is rejected here before any parsing —
    /// there is no synchronous module-fetching pipeline to fall back to, and no blocking
    /// bridge is ever taken. Downloader-less options keep full synchronous processing:
    /// parsing and every elaboration pass are CPU work, and <c>load</c> syntax without a
    /// downloader keeps its established unavailability diagnostic.
    /// </summary>
    /// <exception cref="InvalidOperationException">
    /// <see cref="RunOptions.DownloadCode"/> is configured; use the asynchronous pipeline
    /// (<see cref="ProcessAsync(string, RunOptions?)"/> via <see cref="KatLangEngine.RunAsync"/> or
    /// <see cref="Parser.ParseAsync"/>).
    /// </exception>
    internal static FrontEndResult Process(string source, RunOptions? options)
        => Process(source, options, comparisonObservations: null);

    /// <summary>
    /// <see cref="Process(string, RunOptions?)"/> with a passive clause-family duplicate-detection
    /// observer (null in production; see <see cref="PatternComparisonObservations"/>). Test entry.
    /// </summary>
    internal static FrontEndResult Process(string source, RunOptions? options, PatternComparisonObservations? comparisonObservations)
    {
        // Validation only: no loader exists on the synchronous path, but a nonsensical
        // allow-list fails loudly at every options boundary, not just the loading one.
        _ = NormalizeAllowedHosts(options?.AllowedHosts);
        ThrowIfSynchronousEntryWithDownloader(options);

        var cancellationToken = options?.SourceProcessingCancellationToken ?? CancellationToken.None;
        cancellationToken.ThrowIfCancellationRequested();

        var budget = new SourceProcessingBudget(options?.SourceProcessingLimits);
        if (TryRejectMainSource(source, budget, out var rejected))
            return rejected;

        // The operation's ONE bounded diagnostic list: the parse opens it and every later
        // stage reports into it (see DiagnosticBag). The parse observes the configured token
        // inside clause-family duplicate detection (SEC-03).
        var input = ElaborationInput.Parse(source, budget.CreateDiagnosticBag(), comparisonObservations, cancellationToken);
        cancellationToken.ThrowIfCancellationRequested();

        return ProcessWithoutModuleElaboration(input, options?.HostOperations, budget.Limits, cancellationToken);
    }

    /// <summary>
    /// Asynchronous options-configured front end — the canonical path when
    /// <see cref="RunOptions.DownloadCode"/> is configured. Parsing, parameter detection,
    /// implicit-argument resolution, and exposure resolution remain synchronous CPU work;
    /// only module acquisition awaits, inside <see cref="ModuleLoader.ElaborateAsync"/>.
    /// With no downloader configured (or a downloader whose ValueTasks complete
    /// synchronously) the returned task completes synchronously on the calling thread —
    /// no work is scheduled elsewhere and nothing yields artificially.
    /// </summary>
    internal static ValueTask<FrontEndResult> ProcessAsync(string source, RunOptions? options)
        => ProcessAsync(source, options, comparisonObservations: null);

    /// <summary>
    /// <see cref="ProcessAsync(string, RunOptions?)"/> with a passive clause-family
    /// duplicate-detection observer shared by the main parse and every module parse (null in
    /// production; see <see cref="PatternComparisonObservations"/>). Test entry.
    /// </summary>
    internal static async ValueTask<FrontEndResult> ProcessAsync(
        string source,
        RunOptions? options,
        PatternComparisonObservations? comparisonObservations)
    {
        // MIRROR OF Process(string, RunOptions?) — keep in lock-step; only module
        // elaboration is awaited.
        var allowedHosts = NormalizeAllowedHosts(options?.AllowedHosts);

        var cancellationToken = options?.SourceProcessingCancellationToken ?? CancellationToken.None;
        cancellationToken.ThrowIfCancellationRequested();

        var budget = new SourceProcessingBudget(options?.SourceProcessingLimits);
        if (TryRejectMainSource(source, budget, out var rejected))
            return rejected;

        // The operation's ONE bounded diagnostic list: the parse, the module loader (every
        // module and nested module), and every elaboration pass report into it. The parse
        // observes the configured token inside clause-family duplicate detection (SEC-03).
        var input = ElaborationInput.Parse(source, budget.CreateDiagnosticBag(), comparisonObservations, cancellationToken);
        cancellationToken.ThrowIfCancellationRequested();

        if (options?.DownloadCode is not null)
            return await ProcessWithModuleElaborationAsync(
                input,
                options.DownloadCode,
                allowedHosts,
                budget,
                options.HostOperations,
                comparisonObservations,
                cancellationToken).ConfigureAwait(false);

        return ProcessWithoutModuleElaboration(input, options?.HostOperations, budget.Limits, cancellationToken);
    }

    /// <summary>
    /// The one enforcement point for the async-only source-loading contract on
    /// synchronous entry paths (<see cref="KatLangEngine.Run"/>,
    /// <see cref="Parser.Parse(string, RunOptions?)"/>): module downloading awaits, so a
    /// synchronous entry cannot honor a downloader-configured options object and fails
    /// fast instead of blocking a thread or silently ignoring the configuration.
    /// </summary>
    private static void ThrowIfSynchronousEntryWithDownloader(RunOptions? options)
    {
        if (options?.DownloadCode is not null)
        {
            throw new InvalidOperationException(
                "RunOptions.DownloadCode is configured, but module loading is asynchronous; use " +
                "KatLangEngine.RunAsync (or an async convenience entry point) or Parser.ParseAsync, " +
                "or omit the downloader for source without load directives.");
        }
    }

    /// <summary>
    /// Validates and normalizes <see cref="RunOptions.AllowedHosts"/> at the options boundary —
    /// the synchronous AND the asynchronous front end, so a nonsensical allow-list fails loudly
    /// wherever it is supplied, matching the <see cref="EvaluationLimits"/> /
    /// <see cref="SourceProcessingLimits"/> convention. A null set keeps the loader's default;
    /// every entry is trimmed; a null, empty, or whitespace-only entry is rejected with
    /// <see cref="ArgumentException"/> BEFORE any parsing or loader exists, because an empty
    /// entry under the exact-or-subdomain rule once collapsed into the suffix <c>"."</c> and
    /// admitted every root-anchored host name (bug-hunt B5a; the canonical allow-list itself —
    /// <see cref="ModuleLoadTarget.AllowedHosts"/> — refuses blank entries as well, so an
    /// internally constructed loader can never fail open either). The exact-or-subdomain rule
    /// itself (<see cref="ModuleLoadTarget"/>): <c>sub.ex.com</c> is admitted under
    /// <c>ex.com</c>, <c>ex.com.evil.net</c> is not, and both sides compare in canonical IDNA form.
    /// </summary>
    /// <exception cref="ArgumentException">An entry is null, empty, or whitespace-only.</exception>
    internal static IReadOnlyList<string>? NormalizeAllowedHosts(IEnumerable<string>? allowedHosts)
    {
        if (allowedHosts is null)
            return null;

        var normalized = new List<string>();
        var index = 0;
        foreach (var entry in allowedHosts)
        {
            if (string.IsNullOrWhiteSpace(entry))
            {
                throw new ArgumentException(
                    $"RunOptions.AllowedHosts entry {index} is {(entry is null ? "null" : "blank")}; " +
                    "every allowed host must be a non-blank host name.",
                    nameof(RunOptions.AllowedHosts));
            }

            normalized.Add(entry.Trim());
            index++;
        }

        return normalized;
    }

    /// <summary>
    /// Enforces the configured per-source length ceiling on the MAIN program before parsing and
    /// reserves it against the run-wide aggregate. A rejected source produces one structured
    /// <see cref="SourceProcessingDiagnostics.SourceLengthExceeded"/> diagnostic and no parse.
    /// </summary>
    private static bool TryRejectMainSource(string source, SourceProcessingBudget budget, out FrontEndResult rejected)
    {
        if (!budget.SourceLengthWithinLimit(source.Length))
        {
            rejected = new FrontEndResult(
                new Algorithm.User(null, [], [], [], []),
                [SourceProcessingDiagnostics.SourceLengthExceeded(source.Length, budget.MaxSourceLength)]);
            return true;
        }

        // Reserve the main program against the run-wide aggregate before any module is loaded, so
        // modules are charged on top of it. By default the per-source ceiling never exceeds the
        // aggregate ceiling, so this fits; a caller that configured the aggregate below its own
        // program source is rejected here rather than silently proceeding.
        if (!budget.TryReserveAggregate(source.Length))
        {
            rejected = new FrontEndResult(
                new Algorithm.User(null, [], [], [], []),
                [SourceProcessingDiagnostics.AggregateSourceLengthExceededByProgram(source.Length, budget.MaxAggregateSourceLength)]);
            return true;
        }

        rejected = null!;
        return false;
    }

    /// <summary>
    /// The front end without module elaboration. Every <c>load</c> directive is then
    /// UNAVAILABLE: it is reported once per site (<see cref="DiagnosticCode.LoadElaborationUnavailable"/>,
    /// which blocks evaluation), kept in place, and the program around it is elaborated
    /// PROVISIONALLY (see <see cref="FinalizeElaboration"/>), so the published root is an
    /// elaborated tree whatever the configuration.
    /// </summary>
    private static FrontEndResult ProcessWithoutModuleElaboration(
        ElaborationInput input,
        HostOperations? hostOperations,
        SourceProcessingLimits sourceProcessingLimits,
        CancellationToken cancellationToken)
    {
        var modulesUnavailable = ReportUnavailableLoads(input);

        return FinalizeElaboration(
            input,
            hostOperations: hostOperations,
            provisional: modulesUnavailable,
            sourceProcessingLimits: sourceProcessingLimits,
            cancellationToken: cancellationToken);
    }

    private static bool ReportUnavailableLoads(ElaborationInput input)
        => LoadElaborationGuard.ReportUnavailable(input.Current, input.Diagnostics);

    private static async ValueTask<FrontEndResult> ProcessWithModuleElaborationAsync(
        ElaborationInput input,
        Func<string, CancellationToken, ValueTask<string>> downloadCode,
        IEnumerable<string>? allowedHosts,
        SourceProcessingBudget budget,
        HostOperations? hostOperations,
        PatternComparisonObservations? comparisonObservations,
        CancellationToken cancellationToken)
    {
        var loader = new ModuleLoader(
            input.Diagnostics,
            downloadCode,
            allowedHosts,
            budget,
            cancellationToken)
        {
            ComparisonObservations = comparisonObservations,
        };
        input.Put(await loader.ElaborateAsync(input.Take()).ConfigureAwait(false));
        cancellationToken.ThrowIfCancellationRequested();

        if (RejectOverDeepComposition(input) is { } rejected)
            return rejected;

        var modulesMissing = ReportMissingModules(input, loader);

        return FinalizeElaboration(
            input,
            hostOperations: hostOperations,
            hasDeferredModuleRegions: loader.DeferredRegionCount > 0,
            provisional: modulesMissing,
            modules: loader.ModuleUnits.BeginOperation(),
            sourceProcessingLimits: budget.Limits,
            cancellationToken: cancellationToken);
    }

    /// <summary>
    /// Module elaboration splices independently parsed module trees (each already structurally
    /// checked by ParseSyntax) into the host tree, so the COMPOSED root can be deeper than any
    /// single parse. Re-check it at the raw-syntax cap before the recursive load-invariant walk;
    /// a rejected composition returns the same placeholder-root convention ParseSyntax uses, so
    /// no downstream consumer ever walks the unsafe tree. (FinalizeElaboration then applies the
    /// lower elaboration gate shared with the non-module path.)
    /// </summary>
    private static FrontEndResult? RejectOverDeepComposition(ElaborationInput input)
    {
        if (AstStructuralPreflight.Check(
                input.Current,
                AstStructuralPreflight.RawSyntaxMaxAstDepth,
                AstConsumerProfile.FullyRecursive) is not { } structuralRejection)
            return null;

        input.Diagnostics.Add(AstStructuralPreflight.ToParseDiagnostic(
            structuralRejection, AstStructuralPreflight.RawSyntaxMaxAstDepth));
        return new FrontEndResult(new Algorithm.User(null, [], [], [], []), input.Diagnostics);
    }

    /// <summary>
    /// An unresolved load directive left outside deferred regions means a module is MISSING:
    /// either the loader REFUSED it — reported why at its site and kept the written directive
    /// in place, never a stand-in value (ModuleLoader.RefuseLoad) — or its traversal never
    /// reached it, an internal failure of module elaboration and the only kind this reports.
    /// Either way the tree is published as a PROVISIONAL elaboration (see FinalizeElaboration),
    /// exactly like a program parsed without a downloader, so no consumer of a parse result
    /// ever receives raw syntax or a tree that pretends a module was something it was not.
    /// </summary>
    private static bool ReportMissingModules(ElaborationInput input, ModuleLoader loader)
    {
        var root = input.Current;
        var modulesMissing = LoadElaborationGuard.TryFindFirstUnresolvedLoad(root, out _);
        if (modulesMissing && LoadElaborationGuard.TryFindFirstUnresolvedLoad(root, loader.RefusedLoads, out _))
            input.Diagnostics.Add(LoadElaborationGuard.CreatePostElaborationInvariantDiagnostic(root, loader.RefusedLoads));
        return modulesMissing;
    }

    /// <summary>
    /// The complete elaboration of a load-elaborated root: the structural gate, parameter
    /// detection (name resolution), implicit-argument resolution (automatic parameter forwarding),
    /// the declaration and open validators, and exposure resolution. Every parse result's root is produced here (or is
    /// the empty placeholder root of a rejected source), so a published root is ALWAYS an
    /// elaborated tree — never raw syntax.
    /// <para>
    /// A <paramref name="provisional"/> elaboration is the one for a program that still carries
    /// unresolved <c>load</c> directives outside deferred regions — a MISSING module: unavailable
    /// (the parse had no downloader) or refused by module elaboration (a failed fetch, a refused
    /// target, a cycle, a budget limit, invalid module source) — and it is the whole-document
    /// instance of a deferred module region's eager provisional elaboration: the same passes
    /// build the same tree, the load directives stay in place as the source constructs they are,
    /// and the passes' diagnostics are WITHHELD, because any of them may depend on members the
    /// missing modules would have supplied (an undeclared name an <c>open</c> would provide, a
    /// root parameter inferred for it, an open path through a module, a refused forwarding to a
    /// module callable) and a module's reach is not confined to its load site: an <c>open</c>
    /// covers every nested scope and a dot path can navigate into a module property from
    /// anywhere. (A deferred materialization whose loads fail likewise runs no pass at all.) The
    /// operation's own diagnostics — why each module is missing
    /// (<see cref="DiagnosticCode.LoadElaborationUnavailable"/>, <see cref="DiagnosticCode.LoadFetchFailed"/>,
    /// …), syntax errors, and the structural gate below — are reported as always and keep the
    /// result unevaluable, while editor tooling models the tree with module-dependent names
    /// indeterminate (<see cref="Semantics.IdentifierClassification.DeferredModuleReference"/>).
    /// </para>
    /// </summary>
    private static FrontEndResult FinalizeElaboration(
        ElaborationInput input,
        HostOperations? hostOperations = null,
        bool hasDeferredModuleRegions = false,
        bool provisional = false,
        ModuleUnits? modules = null,
        SourceProcessingLimits? sourceProcessingLimits = null,
        CancellationToken cancellationToken = default)
    {
        cancellationToken.ThrowIfCancellationRequested();

        // The elaboration passes below (parameter detection's rewriting walk,
        // implicit-argument and exposure resolution) recurse with evaluation-class
        // frame sizes — a ~500-626-node composed tree overflows a 1 MiB thread inside
        // ParameterDetector.RewriteParams — so trees between the raw-syntax cap and
        // the evaluation ceiling are rejected HERE, on both the module and non-module
        // paths, with one structured diagnostic instead of being walked at
        // machine-dependent risk. Anything this gate passes is also within the
        // evaluator's own structural ceiling. This is the pipeline's ONE common gate:
        // the passes below run through their prevalidated cores, so the modest
        // depth growth elaboration itself adds (parameter lifting wraps calls) is
        // absorbed by the ceiling's measured ≥2x margin rather than re-gated
        // mid-pipeline.
        if (RejectOverDeepElaboration(input) is { } rejected)
            return rejected;

        var diagnostics = input.Diagnostics;

        // Every pass below reports into `passDiagnostics`: the operation's bag, or — for a
        // provisional elaboration — a bag of the same capacity that nothing ever commits (see
        // the summary). The passes themselves run identically either way, so the provisional
        // tree is exactly the tree the same program elaborates to without its modules.
        var passDiagnostics = provisional ? diagnostics.CreateStage() : diagnostics;

        // Host-operation names resolve during parameter detection (through the
        // configuration's extended semantic prelude), so referencing one never turns
        // it into an implicit parameter — the front-end half of the same name-level
        // agreement the built-in Math module relies on.
        // NAME RESOLUTION and AUTOMATIC PARAMETER FORWARDING are two separate operations
        // (Q-04, decided September 28 2026): detection decides what every written name
        // denotes, and implicit-argument resolution then forwards, to each referenced callee,
        // the parameter bindings those decisions established — adding a forwarded parameter
        // only where none exists. Forwarding never feeds back into name resolution: a
        // parameter it adds is never what a written name refers to, so no binding is
        // re-selected once signatures are complete (the former ownership-completion pass
        // re-selected them, which is how adding a reference could rebind a written name).
        // Every loaded module is ONE unit of the program (Q-31 H-P + Q-32 I-U): each pass elaborates
        // it once, rooted at the prelude, wherever it is spliced (see ModuleUnitRegistry).
        modules ??= new ModuleUnits();
        StaticStructureOperation? operation = null;
        try
        {
            operation = StaticStructureAdmission.Create(input.Current, hostOperations, sourceProcessingLimits, cancellationToken: cancellationToken).Operation;
            DetectParameters(input, hostOperations, passDiagnostics, modules, operation);
            if (operation is not null && passDiagnostics.HasReported(DiagnosticCode.SelfDependentInferredParameters))
            {
                operation.CompleteLookups(input.Current);
                input.Current.CompletedStructure!.Facts.Seal(cancellationToken);
                // A1 recovery (F4): the unit is rejected and never forwarded, validated by the
                // open-provider and output rules, exposure-settled or published — those read
                // signatures and targets the undecided inputs leave open. Only the collision rule,
                // which is monotone in the parameters a signature holds, runs, over the detected
                // tree (see ParameterPropertyCollisionValidator.ValidateAfterSelfDependentInference).
                cancellationToken.ThrowIfCancellationRequested();
                ValidateCollisionsAfterSelfDependentInference(input, passDiagnostics);
                return new(ElaboratedUserRoot(input.Take()), diagnostics, hasDeferredModuleRegions);
            }
        }
        catch (StaticQueryLimitExceededException error)
        {
            diagnostics.Add(StaticStructureAdmission.Rejection(error));
            return new(new Algorithm.User(null, [], [], [], []), diagnostics);
        }

        cancellationToken.ThrowIfCancellationRequested();

        // Implicit-argument resolution also REPORTS the forwarding it had to refuse: a
        // registry-proven value-demanding position whose referenced callable needs implicit
        // parameters the enclosing CLOSED explicit list cannot supply can never be satisfied
        // by any call of that algorithm, so it is a static well-formedness failure of the
        // closed interface — the same rule parameter detection applies to a directly written
        // undeclared identifier, one indirection further out.
        try { ResolveImplicitArguments(input, passDiagnostics, hostOperations, modules, operation); }
        catch (StaticQueryLimitExceededException error)
        {
            diagnostics.Add(StaticStructureAdmission.Rejection(error));
            return new(new Algorithm.User(null, [], [], [], []), diagnostics);
        }

        // The parameter/property collision rule, the open PROVIDER rule, and the output rule
        // need completed signatures (an inferred parameter list is final only now) and nothing
        // from exposure, so they run here: an algorithm with inferred parameters and no output is
        // this front end's error, never the evaluator's (X-07; a written list was reported at
        // parse time).
        ValidateCompletedSignatures(input, passDiagnostics, hostOperations);

        try
        {
            cancellationToken.ThrowIfCancellationRequested();
            ResolveExposure(input, hostOperations, modules, cancellationToken);
            cancellationToken.ThrowIfCancellationRequested();

            // The program's later operations (deferred materializations) receive these module units —
            // the very declarations this tree holds — when this elaboration is the evaluable one.
            if (!provisional && !diagnostics.HasReportedErrors)
                modules.Publish(operation is not null && hasDeferredModuleRegions ? operation.Freeze(cancellationToken) : null);
        }
        catch (StaticQueryLimitExceededException error)
        {
            diagnostics.Add(StaticStructureAdmission.Rejection(error));
            return new(new Algorithm.User(null, [], [], [], []), diagnostics);
        }

        // B2c: a tree with deferred module regions is evaluated by the async evaluation
        // family only (materializing a selected branch awaits the module downloader). The
        // placeholders the tree carries are what route it there and what make the synchronous
        // entry points reject it (DeferredModuleRegion.RequiresAsyncEvaluation walks the tree
        // itself), so no root has to be marked — and no copy of one can lose a mark.
        return new FrontEndResult(ElaboratedUserRoot(input.Take()), diagnostics, hasDeferredModuleRegions);
    }

    // ── One frame per pass (SEC-S1) ────────────────────────────────────────────
    // Each helper takes its pass's input out of the hand-off and puts the output back, so the
    // input is referenced only from the helper's own frame and becomes unreachable when the pass
    // returns (apart from what the output shares with it). The pipeline methods above never hold
    // a tree in a local, a parameter, or an argument temporary: unoptimized (tier-0) code reports
    // those live for the whole method, which kept the raw syntax tree, the detected tree, and a
    // finished validator's memo alive through every later pass.

    private static FrontEndResult? RejectOverDeepElaboration(ElaborationInput input)
    {
        if (AstStructuralPreflight.Check(
                input.Current,
                EvaluationLimits.MaxSupportedAstDepth,
                AstConsumerProfile.FullyRecursive) is not { } elaborationRejection)
            return null;

        input.Diagnostics.Add(AstStructuralPreflight.ToParseDiagnostic(
            elaborationRejection, EvaluationLimits.MaxSupportedAstDepth));
        return new FrontEndResult(new Algorithm.User(null, [], [], [], []), input.Diagnostics);
    }

    private static void DetectParameters(
        ElaborationInput input, HostOperations? hostOperations, DiagnosticBag passDiagnostics, ModuleUnits modules, StaticStructureOperation? operation)
    {
        var (parameterizedRoot, _) = ParameterDetector.DetectPrevalidated(
            input.Take(), hostOperations, diagnostics: passDiagnostics, modules: modules, structuralOperation: operation);
        input.Put(parameterizedRoot);
    }

    private static void ResolveImplicitArguments(
        ElaborationInput input, DiagnosticBag passDiagnostics, HostOperations? hostOperations, ModuleUnits modules, StaticStructureOperation? operation)
        => input.Put(ImplicitArgumentResolver.ResolvePrevalidated(
            input.Take(), observations: null, passDiagnostics, hostOperations, modules, operation));

    // One frame per validator as well, so one validator's memo is gone before the next runs.
    private static void ValidateCompletedSignatures(
        ElaborationInput input, DiagnosticBag passDiagnostics, HostOperations? hostOperations)
    {
        ValidateParameterPropertyCollisions(input, passDiagnostics);
        ValidateOpenProviders(input, passDiagnostics, hostOperations);
        ValidateInferredParameterOutputs(input, passDiagnostics);
    }

    private static void ValidateParameterPropertyCollisions(ElaborationInput input, DiagnosticBag passDiagnostics)
    {
        var root = input.Current;
        new ParameterPropertyCollisionValidator(passDiagnostics, programRoot: root).VisitAlgorithm(root);
    }

    private static void ValidateCollisionsAfterSelfDependentInference(ElaborationInput input, DiagnosticBag passDiagnostics)
    {
        var root = input.Current;
        ParameterPropertyCollisionValidator.ValidateAfterSelfDependentInference(
            root, passDiagnostics, enclosingParameters: null, programRoot: root, importSite: null);
    }

    private static void ValidateOpenProviders(ElaborationInput input, DiagnosticBag passDiagnostics, HostOperations? hostOperations)
        => OpenProviderValidator.Validate(input.Current, passDiagnostics, hostOperations);

    private static void ValidateInferredParameterOutputs(ElaborationInput input, DiagnosticBag passDiagnostics)
        => InferredParameterOutputValidator.ValidateProgram(input.Current, passDiagnostics);

    private static void ResolveExposure(ElaborationInput input, HostOperations? hostOperations, ModuleUnits modules, CancellationToken cancellationToken)
        => input.Put(PropertyExposureResolver.Resolve(input.Take(), observations: null, hostOperations, modules, cancellationToken));

    /// <summary>
    /// The tree and diagnostic list of ONE elaboration, handed from pass to pass (see the pass
    /// helpers above): the current tree is held here and nowhere else in the pipeline's frames.
    /// Built from the raw parse inside <see cref="Parse(string, DiagnosticBag)"/>, so not even the
    /// parse result record outlives the call that produced it.
    /// </summary>
    private sealed class ElaborationInput
    {
        private Algorithm? _current;

        private ElaborationInput(SyntaxParseResult syntax)
        {
            _current = syntax.SyntaxRoot;
            Diagnostics = syntax.Diagnostics;
        }

        public DiagnosticBag Diagnostics { get; }

        /// <summary>The current tree, left in place (a read-only check or validation).</summary>
        public Algorithm Current
            => _current ?? throw new InvalidOperationException("Internal error: the elaboration tree was taken and not replaced.");

        /// <summary>The current tree, removed: the caller's pass owns it until it <see cref="Put"/>s its output.</summary>
        public Algorithm Take()
        {
            var current = Current;
            _current = null;
            return current;
        }

        public void Put(Algorithm next) => _current = next;

        public static ElaborationInput Parse(string source, DiagnosticBag diagnostics)
            => new(Parser.ParseSyntax(source, diagnostics));

        public static ElaborationInput Parse(
            string source,
            DiagnosticBag diagnostics,
            PatternComparisonObservations? comparisonObservations,
            CancellationToken cancellationToken)
            => new(Parser.ParseSyntax(
                source,
                initialNestingDebt: 0,
                diagnostics,
                comparisonObservations,
                cancellationToken,
                CancellationToken.None));
    }

    /// <summary>
    /// The program root after elaboration, as the <see cref="Algorithm.User"/> it is by
    /// construction: the parser's root is a user algorithm and every pass (module loading,
    /// parameter detection, implicit-argument resolution, exposure resolution) returns the variant it was given — a builtin as itself, a family as a
    /// family, a user algorithm as a user algorithm. The passes are total over the hierarchy
    /// for the NESTED algorithms they rewrite, so their entry points are base-typed and the
    /// type system states the root invariant here, once, with a fail-loud guard for the
    /// variant-changing pass that must never exist (pinned by <c>AlgorithmOwnershipTests</c>).
    /// </summary>
    private static Algorithm.User ElaboratedUserRoot(Algorithm elaboratedRoot)
        => elaboratedRoot as Algorithm.User
            ?? throw new InvalidOperationException(
                "Internal error: a front-end elaboration pass changed the variant of the program root " +
                $"to {elaboratedRoot.GetType().Name}.");
}

/// <summary>
/// Raw syntax result produced directly by the recursive-descent parser.
/// No front-end elaboration passes have run yet. <see cref="Diagnostics"/> is the operation's
/// bag the parse reported into; the front end keeps reporting into the same bag.
/// </summary>
internal sealed record SyntaxParseResult(Algorithm.User Root, DiagnosticBag Diagnostics)
{
    public Algorithm.User SyntaxRoot => Root;

    /// <summary>Whether the parse REPORTED an error — stored or dropped by the diagnostic budget.</summary>
    public bool HasErrors => Diagnostics.HasReportedErrors;
}

/// <summary>
/// Internal front-end result after load elaboration, parameter detection,
/// implicit argument resolution, and property exposure analysis.
/// </summary>
internal sealed record FrontEndResult(
    Algorithm.User ElaboratedRoot,
    IReadOnlyList<Diagnostic> Diagnostics,
    bool HasDeferredModuleRegions = false)
{
    public bool HasErrors => Diagnostics.Any(d => d.Severity == DiagnosticSeverity.Error);

    /// <summary>
    /// The public parse result, carrying the host operations the elaboration resolved names
    /// against. Its diagnostics are a read-only snapshot: the pipeline's working list never
    /// escapes, so no consumer can change a published result through a cast.
    /// </summary>
    public ParseResult ToParseResult(HostOperations? hostOperations = null)
        => new(ElaboratedRoot, Array.AsReadOnly(Diagnostics.ToArray())) { HostOperations = hostOperations };
}
