using System.Collections;
using System.Collections.ObjectModel;
using System.Numerics;
using KatLang.Semantics;

namespace KatLang.Formatting.PublicApi.Tests;

/// <summary>
/// READ-ONLY VIEWS NEVER HAND OUT THEIR STORAGE (November 2026), pinned from a NON-friend consumer.
/// <see cref="Result.ListValue.Items"/> and <see cref="Result.SequenceValue.Items"/> were
/// <c>Array.AsReadOnly(array)</c>, whose non-generic <see cref="ICollection.SyncRoot"/> is the
/// array itself: <c>(Result[])((ICollection)list.Items).SyncRoot</c> gave any host — and any host
/// operation, in the middle of a run — the writable storage of a value the engine treats as
/// immutable. Every other published list had the same hole, the process-wide catalogs included.
/// These tests perform that attack through the public API alone; the reflection sweep over every
/// public collection member is <see cref="PublicCollectionStorageSweepTests"/>.
/// </summary>
public class ReadOnlyViewStorageContractTests
{
    private static readonly Result Planted = new Result.Atom(99);

    public static TheoryData<string, bool> ArgumentValues
    {
        get
        {
            var data = new TheoryData<string, bool>();
            foreach (var declaration in new[] { "V = [1, 2, 3]", "V = (1, 2, 3)", "V = range(1, 5)", "V = [[1, 2], (3, 4)]" })
            {
                data.Add(declaration, false);
                data.Add(declaration, true);
            }

            return data;
        }
    }

    /// <summary>
    /// The attack inside a run: a host operation receives the VALUE of a cached property, reaches
    /// for its storage through <c>Items.SyncRoot</c> at every level, and writes when it gets an
    /// array. The same run then reads the property twice more. The value must be what a run whose
    /// operation attacks nothing produces, and what a second attacked run produces.
    /// </summary>
    [Theory]
    [MemberData(nameof(ArgumentValues))]
    public async Task HostOperation_CannotChangeItsArgumentThroughSyncRoot(string declaration, bool asynchronous)
    {
        var source = declaration + "\npoke(V), V, V";
        var attempts = 0;
        var openRoutes = new List<string>();
        Result Attack(IReadOnlyList<Result> arguments)
        {
            attempts++;
            openRoutes.AddRange(WriteThroughEveryRoute(arguments, "the argument list"));
            foreach (var argument in arguments)
                openRoutes.AddRange(AttackValue(argument));
            return new Result.Atom(0);
        }

        var attacked = await RunAsync(source, Operation(Attack, asynchronous), asynchronous);
        var again = await RunAsync(source, Operation(Attack, asynchronous), asynchronous);
        var clean = await RunAsync(source, Operation(static _ => new Result.Atom(0), asynchronous), asynchronous);

        Assert.Equal(2, attempts);
        Assert.Empty(openRoutes);
        Assert.Equal(clean.Value, attacked.Value, Result.ValueComparer);
        Assert.Equal(again.Value, attacked.Value, Result.ValueComparer);
        Assert.Equal(clean.ToDisplayString(), attacked.ToDisplayString());
        Assert.Equal(clean.Atoms, attacked.Atoms);

        // The two later reads are the cached property's value, untouched: both rows are one value,
        // equal to what a fresh evaluation of the declaration alone yields.
        var rows = attacked.OutputRows;
        Assert.Equal(3, rows.Count);
        Assert.Same(rows[1], rows[2]);
        var alone = Assert.IsType<RunResult.Success>(KatLangEngine.Run(declaration + "\nV, 0"));
        Assert.Equal(alone.OutputRows[0], rows[1], Result.ValueComparer);
        Assert.DoesNotContain(Planted, Flatten(attacked.Value), Result.ValueComparer);
    }

    /// <summary>The documented snippet, verbatim, against a value a host built and values the engine produced.</summary>
    [Fact]
    public void TheCastAndWriteSnippet_FailsForBuiltAndProducedValues()
    {
        var built = new Result.ListValue([new Result.Atom(1), new Result.Atom(2)]);
        Assert.Throws<InvalidCastException>(() =>
        {
            var storage = (Result[])((ICollection)built.Items).SyncRoot;
            storage[0] = Planted;
        });
        Assert.Equal(new Result.Atom(1), built.Items[0]);

        var builtSequence = new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]);
        Assert.Throws<InvalidCastException>(() => _ = (Result[])((ICollection)builtSequence.Items).SyncRoot);

        foreach (var source in new[] { "[1, 2, 3]", "(1, 2, 3)", "range(1, 5)", "[[1, 2], (3, 4)]", "[]", "()" })
        {
            var value = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).Value;
            var before = Flatten(value).ToArray();
            Assert.Empty(AttackValue(value));
            Assert.Equal(before, Flatten(value), Result.ValueComparer);
            foreach (var view in ViewsOf(value))
            {
                PublishedCollection.AssertHandsOutNoStorage(view, source);
                Assert.IsAssignableFrom<ReadOnlyCollection<Result>>(view);
            }
        }
    }

    /// <summary>
    /// A value's view is still ONE object: record equality reads it by reference, a <c>with</c>
    /// copy shares it, two empty values share the one empty view, and its debug text is the plain
    /// collection's.
    /// </summary>
    [Fact]
    public void ValueViews_KeepTheirIdentityEqualityAndText()
    {
        var list = new Result.ListValue([new Result.Atom(1)]);
        Assert.Same(list.Items, list.Items);
        var copy = list with { };
        Assert.Same(list.Items, copy.Items);
        Assert.Equal(list, copy);
        Assert.Equal(list.GetHashCode(), copy.GetHashCode());
        Assert.NotEqual(list, new Result.ListValue([new Result.Atom(1)]));
        Assert.Equal(list, new Result.ListValue([new Result.Atom(1)]), Result.ValueComparer);
        list.Deconstruct(out var deconstructed);
        Assert.Same(list.Items, deconstructed);
        Assert.Equal("ListValue { Items = System.Collections.ObjectModel.ReadOnlyCollection`1[KatLang.Result] }", list.ToString());

        var sequence = new Result.SequenceValue([new Result.Atom(1)]);
        Assert.Same(sequence.Items, (sequence with { }).Items);
        Assert.Equal("SequenceValue { Items = System.Collections.ObjectModel.ReadOnlyCollection`1[KatLang.Result] }", sequence.ToString());

        Assert.Same(new Result.ListValue([]).Items, new Result.ListValue([]).Items);
        Assert.Equal(new Result.ListValue([]), new Result.ListValue([]));
        Assert.Same(((ICollection)new Result.ListValue([]).Items).SyncRoot, ((ICollection)new Result.SequenceValue([]).Items).SyncRoot);
        Assert.IsNotType<Result[]>(((ICollection)new Result.ListValue([]).Items).SyncRoot);
    }

    /// <summary>Public construction still snapshots: the caller keeps no alias, and the view is not the caller's list.</summary>
    [Fact]
    public void PublicConstruction_StillSnapshotsItsInput()
    {
        var input = new List<Result> { new Result.Atom(1), new Result.Atom(2) };
        var value = new Result.ListValue(input);
        input[0] = Planted;
        input.Add(Planted);
        Assert.Equal([new Result.Atom(1), new Result.Atom(2)], value.Items);
        Assert.NotSame(input, ((ICollection)value.Items).SyncRoot);
        var error = Assert.Throws<ArgumentException>(() => new Result.SequenceValue([new Result.Atom(1), null!]));
        Assert.Equal("items", error.ParamName);
    }

    // A host implementation can keep any destination passed to CopyTo. Refuse that call here
    // so the test checks ownership without retaining or mutating a library buffer.
    private sealed class HostList<T>(params T[] items) : List<T>(items), ICollection<T>
    {
        void ICollection<T>.CopyTo(T[] array, int arrayIndex)
            => throw new InvalidOperationException("The host received a snapshot buffer.");
    }

    [Fact]
    public void HostSnapshots_ReadItemsWithoutHandingTheSourceTheirStorage()
    {
        var items = new HostList<Result>(new Result.Atom(1), new Result.Atom(2));
        var list = new Result.ListValue(items);
        var sequence = new Result.SequenceValue(items.Concat(items));
        items.Clear();
        Assert.Equal([new Result.Atom(1), new Result.Atom(2)], list.Items);
        Assert.Equal(list.Items.Concat(list.Items), sequence.Items);

        var names = new HostList<string>("a", "b");
        var options = new RunOptions { AllowedHosts = names };
        var branch = new ConditionalBranchInfo("F(a, b)", null, names);
        var parameters = new HostList<PropertyParameterInfo>(new PropertyParameterInfo("a", PropertyParameterKind.Explicit, null));
        var signature = new PropertySignatureInfo(PropertyCallStyle.Plain, "F(a)", parameters);
        var property = new PropertyInfo("F", null, PropertyShape.Ordinary, true, PropertyExposure.Exported,
            parameters, new HostList<ConditionalBranchInfo>(branch)) { Signatures = new HostList<PropertySignatureInfo>(signature) };
        var symbol = new VisibleSymbol("a", IdentifierClassification.Builtin, null, null);
        var symbols = new HostList<VisibleSymbol>(symbol);
        var container = new VisibleSymbol("F", IdentifierClassification.PropertyReference, null, property, symbols);
        var scope = new ScopeVisibility(null, symbols);
        var errors = new HostList<KatLangError>(Assert.Single(Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("1 +")).Errors));
        var exception = new KatLangException(errors);
        names.Clear();
        parameters.Clear();
        symbols.Clear();
        errors.Clear();
        Assert.Equal(["a", "b"], options.AllowedHosts!);
        Assert.Equal(["a", "b"], Assert.Single(property.ConditionalBranches).BinderNames);
        Assert.Equal("a", Assert.Single(property.Parameters).Name);
        Assert.Equal("a", Assert.Single(Assert.Single(property.Signatures).Parameters).Name);
        Assert.Same(symbol, Assert.Single(container.Members));
        Assert.Same(symbol, Assert.Single(scope.Symbols));
        Assert.Single(exception.Errors);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(8)]
    [InlineData(65)]
    public void UnknownLengthHostInput_IsReadOnceAndKeepsItsOrder(int count)
    {
        var reads = 0;
        IEnumerable<Result> Items()
        {
            Assert.Equal(1, ++reads);
            for (var index = 0; index < count; index++)
                yield return new Result.Atom(index);
        }

        var value = new Result.ListValue(Items());
        Assert.Equal(1, reads);
        Assert.Equal(count, value.Items.Count);
        for (var index = 0; index < count; index++)
            Assert.Equal(new Result.Atom(index), value.Items[index]);
    }

    // A caller-defined list that is ONLY an IReadOnlyList<T>: no ICollection<T>, no IList, no
    // CopyTo. Its count and its indexer both work, so a snapshot that read it by position would
    // never start an enumeration, and would never meet a failure the enumeration raises.
    private sealed class ReadOnlyListOnly<T>(T[] items, int failAt = -1) : IReadOnlyList<T>
    {
        public int Enumerations { get; private set; }

        public int IndexerReads { get; private set; }

        public InvalidOperationException Failure { get; } = new("The host list failed while it was being enumerated.");

        public int Count => items.Length;

        public T this[int index]
        {
            get
            {
                IndexerReads++;
                return items[index];
            }
        }

        // Counted here, not inside the iterator: an iterator body only starts at its first MoveNext.
        public IEnumerator<T> GetEnumerator()
        {
            Enumerations++;
            return Enumerate();
        }

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

        private IEnumerator<T> Enumerate()
        {
            for (var index = 0; index < items.Length; index++)
            {
                if (index == failAt)
                    throw Failure;
                yield return items[index];
            }
        }
    }

    /// <summary>
    /// <see cref="RunOptions.AllowedHosts"/> documents that the caller's sequence is ENUMERATED
    /// once, at initialization. A caller-defined read-only list is no exception: its elements
    /// come from its enumeration, in the enumeration's order, and never from its count and
    /// indexer. The sizes cross the snapshot's inline buffer (8) and its rented growth.
    /// </summary>
    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(3)]
    [InlineData(8)]
    [InlineData(9)]
    [InlineData(65)]
    public void AllowedHosts_EnumeratesACallerDefinedReadOnlyListOnce_AndKeepsItsOrder(int count)
    {
        // Deliberately not in name order: the snapshot's order is the enumeration's and nothing else's.
        var names = Enumerable.Range(0, count).Select(index => $"h{(count - index) * 7 % 10}-{index}.example").ToArray();
        var source = new ReadOnlyListOnly<string>(names);

        var options = new RunOptions { AllowedHosts = source };

        Assert.Equal(1, source.Enumerations);
        Assert.Equal(0, source.IndexerReads);
        var snapshot = Assert.IsAssignableFrom<IReadOnlyList<string>>(options.AllowedHosts);
        Assert.Equal(names, snapshot);
        for (var index = 0; index < count; index++)
            Assert.Same(names[index], snapshot[index]);

        // A snapshot: reading the option again, and running with it, never returns to the caller's list.
        Assert.Same(snapshot, options.AllowedHosts);
        Assert.IsType<RunResult.Success>(KatLangEngine.Run("1", options));
        Assert.Equal(1, source.Enumerations);
        Assert.Equal(0, source.IndexerReads);
        Assert.NotSame(source, snapshot);
        PublishedCollection.AssertHandsOutNoStorage(snapshot, "RunOptions.AllowedHosts");
    }

    /// <summary>
    /// "Enumeration exceptions escape the initializer" (<see cref="RunOptions.AllowedHosts"/>): a
    /// failure raised partway through the caller's enumeration reaches the caller unchanged, also
    /// when the list's count and indexer would have answered without it.
    /// </summary>
    [Fact]
    public void AllowedHosts_AFailureInACallerDefinedReadOnlyListsEnumeration_EscapesTheInitializer()
    {
        var source = new ReadOnlyListOnly<string>(["a.example", "b.example", "c.example"], failAt: 1);

        var thrown = Assert.Throws<InvalidOperationException>(() => new RunOptions { AllowedHosts = source });

        Assert.Same(source.Failure, thrown);
        Assert.Equal(1, source.Enumerations);
        Assert.Equal(0, source.IndexerReads);

        // The count and the indexer succeed for every position, the failing one included.
        Assert.Equal(3, source.Count);
        Assert.Equal("b.example", source[1]);
    }

    /// <summary>
    /// The other public constructors that snapshot a caller's collection read it the same way:
    /// one enumeration supplies the elements, and its failure is the constructor's failure.
    /// </summary>
    [Fact]
    public void HostSnapshots_EnumerateACallerDefinedReadOnlyListOnce()
    {
        Result[] atoms = [new Result.Atom(3), new Result.Atom(1), new Result.Atom(2)];
        var listSource = new ReadOnlyListOnly<Result>(atoms);
        var list = new Result.ListValue(listSource);
        Assert.Equal((1, 0), (listSource.Enumerations, listSource.IndexerReads));
        Assert.Equal(atoms, list.Items);

        var sequenceSource = new ReadOnlyListOnly<Result>(atoms);
        var sequence = new Result.SequenceValue(sequenceSource);
        Assert.Equal((1, 0), (sequenceSource.Enumerations, sequenceSource.IndexerReads));
        Assert.Equal(atoms, sequence.Items);

        var failing = new ReadOnlyListOnly<Result>(atoms, failAt: 2);
        Assert.Same(failing.Failure, Assert.Throws<InvalidOperationException>(() => new Result.ListValue(failing)));
        Assert.Equal((1, 0), (failing.Enumerations, failing.IndexerReads));

        var error = Assert.Single(Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("1 +")).Errors);
        var errorSource = new ReadOnlyListOnly<KatLangError>([error]);
        var exception = new KatLangException(errorSource);
        Assert.Equal((1, 0), (errorSource.Enumerations, errorSource.IndexerReads));
        Assert.Same(error, Assert.Single(exception.Errors));

        var failingErrors = new ReadOnlyListOnly<KatLangError>([error], failAt: 0);
        Assert.Same(failingErrors.Failure, Assert.Throws<InvalidOperationException>(() => new KatLangException(failingErrors)));
        Assert.Equal((1, 0), (failingErrors.Enumerations, failingErrors.IndexerReads));
    }

    // ── Every published site ────────────────────────────────────────────────────────────

    private static readonly Lazy<IReadOnlyDictionary<string, Func<object>>> SiteTable = new(BuildSites);

    public static TheoryData<string> Sites
    {
        get
        {
            var data = new TheoryData<string>();
            foreach (var site in SiteTable.Value.Keys.Order(StringComparer.Ordinal))
                data.Add(site);
            return data;
        }
    }

    /// <summary>
    /// Each engine-owned or snapshot list KatLang publishes, by name: the object is not writable
    /// storage, its <c>SyncRoot</c> is one stable object that is not storage either, every
    /// mutation member throws, and the content is unchanged. Non-empty, so nothing passes on an
    /// empty array.
    /// </summary>
    [Theory]
    [MemberData(nameof(Sites))]
    public void PublishedList_RejectsTheCastAndWriteAttack(string site)
    {
        var collection = SiteTable.Value[site]();
        Assert.NotEmpty((IEnumerable)collection);
        PublishedCollection.AssertHandsOutNoStorage(collection, site);
    }

    private const string Program = """
        V = [1, 2, 3]
        Outer(n) = {
            Inner = n + 1
            Inner
        }
        Pick(0) = 0
        Pick(k) = k + 1
        V, Outer(1), Pick(2)
        """;

    private static IReadOnlyDictionary<string, Func<object>> BuildSites()
    {
        var sites = new Dictionary<string, Func<object>>(StringComparer.Ordinal);
        var operation = HostOperation.Create("poke", static (_, _) => new Result.Atom(0), "x", "y");
        var operations = HostOperations.Create(operation);
        var options = new RunOptions { HostOperations = operations, AllowedHosts = ["katlang.org", "example.org"] };
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(Program, options));
        var single = Assert.IsType<RunResult.Success>(KatLangEngine.Run("[1, 2, 3]"));
        var parseFailure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("1 +\n2 +"));
        var parsed = Parser.Parse(Program, options);
        Assert.False(parsed.HasErrors);
        var model = SemanticModelBuilder.Build(parsed);
        var math = PreludeCatalog.Symbols.Single(static symbol => symbol.Name == "Math");
        var (tokens, lexical) = Lexer.Tokenize("A @= 1\nA");

        // Values and results.
        sites["Result.ListValue.Items (engine)"] = () => ((Result.ListValue)success.OutputRows[0]).Items;
        sites["Result.SequenceValue.Items (engine)"] = () => ((Result.SequenceValue)success.Value).Items;
        sites["Result.ListValue.Items (host-built)"] = () => new Result.ListValue([new Result.Atom(1)]).Items;
        sites["Result.SequenceValue.Items (host-built)"] = () => new Result.SequenceValue([new Result.Atom(1)]).Items;
        sites["RunResult.Success.Atoms"] = () => success.Atoms;
        sites["RunResult.Success.OutputRows (many rows)"] = () => success.OutputRows;
        sites["RunResult.Success.OutputRows (one row)"] = () => single.OutputRows;
        sites["RunResult.ParseFailure.Errors"] = () => parseFailure.Errors;
        sites["RunResult.EvalFailure.Errors"] = () => EvalFailure("1 / 0").Errors;
        sites["KatLangException.Errors"] = () => new KatLangException([.. parseFailure.Errors]).Errors;
        sites["KatLangException.Errors (thrown)"] = () => Assert.Throws<KatLangException>(() => KatLangEngine.EvaluateToAtoms("1 +")).Errors;
        sites["KatLangEngine.EvaluateToAtoms"] = () => KatLangEngine.EvaluateToAtoms("1, [2, 3]");
        sites["Evaluator.RunFlat"] = () => Evaluator.RunFlat(new Expr.AlgorithmExpr(parsed.Root)).Value!;
        sites["ParseResult.Diagnostics"] = () => Parser.Parse("1 +").Diagnostics;
        sites["Lexer.Tokenize tokens"] = () => tokens;
        sites["Lexer.Tokenize diagnostics"] = () => lexical;

        // Error payloads.
        sites["EvalError.AmbiguousOpen.Providers"] = () => AmbiguousOpenError().Providers;
        sites["EvalError.LocalOnlyProperty.RequiredParameters"] = () => Innermost<EvalError.LocalOnlyProperty>(
            Failure("Outer(n) = {\n    Inner = n + 1\n    Inner\n}\nOuter.Inner")).RequiredParameters!;
        sites["EvalError.UnresolvedImplicitParams.ParamNames"] = () => Innermost<EvalError.UnresolvedImplicitParams>(
            Failure("Add(acc, item) = acc + item\nreduce([1, 2], Add, Add)")).ParamNames;
        sites["ImplicitParameterContext.ParamNames"] = () => Context<ImplicitParameterContext>(
            Failure("Add(acc, item) = acc + item\nreduce([1, 2], Add, Add)")).ParamNames;
        sites["DeconstructionBindingContext.TargetDisplayNames"] = () => Context<DeconstructionBindingContext>(
            Failure("x, y = 1, 2, 3\nx")).TargetDisplayNames;
        sites["LoopStateBindingContext.StepParameterNames"] = () => Context<LoopStateBindingContext>(
            Failure("Step(a, b) = a, b\nrepeat(Step(1, 2, 3), 1)")).StepParameterNames;
        sites["VariadicLoopStateBindingContext.StepParameterNames"] = () => Context<VariadicLoopStateBindingContext>(
            Failure("Step(a, *r) = a\nrepeat(Step(), 1)")).StepParameterNames;
        sites["ReduceInitialAccumulatorContext.RequiredParameterNames"] = () => Context<ReduceInitialAccumulatorContext>(
            Failure("Inc(x) = x + 1\nAdd(e, a) = e + a\nProbe(unused) = reduce([1, 2], Add, Inc)\nProbe(0)")).RequiredParameterNames;

        // Hosting configuration and process-wide catalogs.
        sites["HostOperations.Operations"] = () => operations.Operations;
        sites["HostOperation.ParameterNames"] = () => operation.ParameterNames;
        sites["RunOptions.AllowedHosts"] = () => options.AllowedHosts!;
        sites["OutputFormatters.All"] = () => OutputFormatters.All;
        sites["Lexer.KeywordNames"] = () => Lexer.KeywordNames;
        sites["PreludeCatalog.KeywordNames"] = () => PreludeCatalog.KeywordNames;
        sites["PreludeCatalog.Symbols"] = () => PreludeCatalog.Symbols;
        sites["PreludeCatalog.DotIntrinsicSymbols"] = () => PreludeCatalog.DotIntrinsicSymbols;
        sites["PreludeCatalog Math.Members"] = () => math.Members;
        sites["PreludeCatalog map.Property.Signatures"] = () => PreludeCatalog.Symbols.Single(static symbol => symbol.Name == "map").Property!.Signatures;
        sites["PreludeCatalog map.Property.Parameters"] = () => PreludeCatalog.Symbols.Single(static symbol => symbol.Name == "map").Property!.Parameters;

        // Shared elaboration data.
        sites["Property.RequiredAncestorParameters"] = () =>
            ((Algorithm.User)parsed.Root.Properties.Single(static property => property.Name == "Outer").Value)
                .Properties.Single(static property => property.Name == "Inner").RequiredAncestorParameters;

        // The semantic model.
        var outer = model.PropertyInfos.Single(static property => property.Name == "Outer");
        var pick = model.PropertyInfos.Single(static property => property.Name == "Pick");
        sites["SemanticModel.IdentifierOccurrences"] = () => model.IdentifierOccurrences;
        sites["SemanticModel.Declarations"] = () => model.Declarations;
        sites["SemanticModel.IdentifierResolutions"] = () => model.IdentifierResolutions;
        sites["SemanticModel.PropertyInfos"] = () => model.PropertyInfos;
        sites["SemanticModel.ScopeVisibilities"] = () => model.ScopeVisibilities;
        sites["SemanticModel.FindDeclarations"] = () => model.FindDeclarations("V");
        sites["SemanticModel.FindResolutions"] = () => model.FindResolutions("V");
        sites["SemanticModel.FindProperties"] = () => model.FindProperties("V");
        sites["SemanticModel.GetVisibleSymbolsAt"] = () => model.GetVisibleSymbolsAt(new SourcePosition(3, 5));
        sites["ScopeVisibility.Symbols (model)"] = () => model.ScopeVisibilities[0].Symbols;
        sites["ScopeVisibility.Symbols (host-built)"] = () => new ScopeVisibility(null, [.. model.ScopeVisibilities[0].Symbols]).Symbols;
        sites["VisibleSymbol.Members (host-built)"] = () => new VisibleSymbol(
            "Host", IdentifierClassification.PropertyReference, null, null, [.. math.Members]).Members;
        sites["PropertyInfo.Parameters"] = () => outer.Parameters;
        sites["PropertyInfo.Signatures"] = () => outer.Signatures;
        sites["PropertySignatureInfo.Parameters"] = () => outer.Signatures[0].Parameters;
        sites["PropertyInfo.GetParameters"] = () => outer.GetParameters(PropertyCallStyle.Plain);
        sites["PropertyInfo.ConditionalBranches"] = () => pick.ConditionalBranches;
        sites["ConditionalBranchInfo.BinderNames"] = () => pick.ConditionalBranches.First(static branch => branch.BinderNames.Count > 0).BinderNames;
        return sites;
    }

    // ── Attack helpers ──────────────────────────────────────────────────────────────────

    /// <summary>
    /// Tries to write to every list view of <paramref name="value"/>, children included, and names
    /// the routes that let the write through.
    /// </summary>
    private static List<string> AttackValue(Result value)
    {
        var open = new List<string>();
        foreach (var view in ViewsOf(value))
            open.AddRange(WriteThroughEveryRoute(view, value.GetType().Name + ".Items"));
        return open;
    }

    /// <summary>
    /// The casts a host can write: the view or its <c>SyncRoot</c> as an array or a list. A route
    /// that throws <see cref="NotSupportedException"/> or does not exist is closed.
    /// </summary>
    private static List<string> WriteThroughEveryRoute(IReadOnlyList<Result> view, string what)
    {
        var open = new List<string>();
        var candidates = new List<(string Name, object Target)> { ("the view", view) };
        if (view is ICollection untyped)
            candidates.Add(("SyncRoot", untyped.SyncRoot));

        foreach (var (name, target) in candidates)
        {
            if (target is Result[] { Length: > 0 } storage)
            {
                storage[0] = Planted;
                open.Add($"{what}: {name} is the Result[] storage");
            }

            if (target is List<Result> list)
            {
                list.Add(Planted);
                open.Add($"{what}: {name} is the List<Result> storage");
            }

            if (target is IList<Result> { Count: > 0 } generic && Writes(() => generic[0] = Planted))
                open.Add($"{what}: {name} accepts IList<Result>.set_Item");
            if (target is IList { Count: > 0 } nonGeneric && Writes(() => nonGeneric[0] = Planted))
                open.Add($"{what}: {name} accepts IList.set_Item");
            if (target is ICollection<Result> collection && Writes(() => collection.Add(Planted)))
                open.Add($"{what}: {name} accepts ICollection<Result>.Add");
        }

        return open;
    }

    private static bool Writes(Action write)
    {
        try
        {
            write();
            return true;
        }
        catch (NotSupportedException)
        {
            return false;
        }
    }

    /// <summary>Every item view reachable from <paramref name="value"/>, outermost first.</summary>
    private static List<IReadOnlyList<Result>> ViewsOf(Result value)
    {
        var views = new List<IReadOnlyList<Result>>();
        var pending = new Stack<Result>([value]);
        while (pending.TryPop(out var current))
        {
            var items = current switch
            {
                Result.ListValue list => list.Items,
                Result.SequenceValue sequence => sequence.Items,
                _ => null,
            };
            if (items is null)
                continue;
            views.Add(items);
            foreach (var item in items)
                pending.Push(item);
        }

        return views;
    }

    private static List<Result> Flatten(Result value)
    {
        var leaves = new List<Result>();
        var pending = new Stack<Result>([value]);
        while (pending.TryPop(out var current))
        {
            switch (current)
            {
                case Result.ListValue list:
                    foreach (var item in list.Items.Reverse()) pending.Push(item);
                    break;
                case Result.SequenceValue sequence:
                    foreach (var item in sequence.Items.Reverse()) pending.Push(item);
                    break;
                default:
                    leaves.Add(current);
                    break;
            }
        }

        return leaves;
    }

    private static HostOperations Operation(Func<IReadOnlyList<Result>, Result> body, bool asynchronous)
        => HostOperations.Create(asynchronous
            ? HostOperation.CreateAsync("poke", async (arguments, _) =>
            {
                await Task.Yield();
                return body(arguments);
            }, "x")
            : HostOperation.Create("poke", (arguments, _) => body(arguments), "x"));

    private static async Task<RunResult.Success> RunAsync(string source, HostOperations operations, bool asynchronous)
    {
        var options = new RunOptions { HostOperations = operations };
        var run = asynchronous ? await KatLangEngine.RunAsync(source, options) : KatLangEngine.Run(source, options);
        return Assert.IsType<RunResult.Success>(run);
    }

    private static RunResult.EvalFailure EvalFailure(string source)
        => Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));

    private static EvalError Failure(string source)
        => Assert.Single(EvalFailure(source).Errors).Source!;

    /// <summary>
    /// An open ambiguity in a host-built tree exercises the evaluator's provider list.
    /// </summary>
    internal static EvalError.AmbiguousOpen AmbiguousOpenError()
    {
        static Property Provider(string name, int value)
        {
            var number = new Algorithm.User(null, [], [], [], [new Expr.Num(value)]);
            var member = new Property("Test", number, IsPublic: true);
            return new Property(name, new Algorithm.User(null, [], [], [member], []));
        }

        var root = new Algorithm.User(null, [], [new Expr.Resolve("A"), new Expr.Resolve("B")],
            [Provider("A", 1), Provider("B", 2)], [new Expr.Resolve("Test")]);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.True(result.IsError);
        return Innermost<EvalError.AmbiguousOpen>(result.Error);
    }

    private static T Innermost<T>(EvalError error)
        where T : EvalError
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return Assert.IsType<T>(error);
    }

    private static T Context<T>(EvalError error)
        where T : ErrorContext
    {
        for (var current = error; current is EvalError.WithContext context; current = context.Inner)
        {
            if (context.ErrorContext is T found)
                return found;
        }

        throw new Xunit.Sdk.XunitException($"No {typeof(T).Name} frame on {error}.");
    }
}
