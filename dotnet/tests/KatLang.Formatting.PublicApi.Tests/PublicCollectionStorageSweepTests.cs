using System.Collections;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text;
using KatLang.Semantics;
using Xunit.Abstractions;

namespace KatLang.Formatting.PublicApi.Tests;

/// <summary>
/// The sweep behind <see cref="ReadOnlyViewStorageContractTests"/>: instead of naming sites, it
/// walks every public property and parameterless method of the objects KatLang produces and
/// attacks every collection it finds (<see cref="PublishedCollection.AssertHandsOutNoStorage"/>).
/// A public collection member that the walk never reached with a non-empty value, and that is not
/// listed below with a reason, fails — so a new member is covered when it is added, not when
/// someone remembers this file. A public member whose DECLARED type exposes storage
/// (an array, <see cref="ArraySegment{T}"/>, <see cref="Memory{T}"/>, a mutable collection type)
/// fails too.
/// </summary>
public class PublicCollectionStorageSweepTests(ITestOutputHelper output)
{
    private static readonly Assembly KatLang = typeof(KatLangEngine).Assembly;

    [Fact]
    public async Task DeferredMaterialization_PreservesReadOnlyDiagnostics()
    {
        const string source = """
            F(0) = 0
            F(n) = { open 'https://modules.example/unused.kat'
                A = { open { public X = 1 }.Nope
                    X }
                A(5) }
            F(1)
            """;
        var options = new RunOptions
        {
            AllowedHosts = ["modules.example"],
            DownloadCode = static (_, _) => ValueTask.FromResult("public Unused = 1"),
        };
        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source, options));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.UnresolvedOpenTarget, error.Code);
        PublishedCollection.AssertHandsOutNoStorage(failure.Errors, "deferred RunResult.EvalFailure.Errors");

        var cause = error.Source;
        while (cause is EvalError.WithContext frame)
            cause = frame.Inner;
        Assert.NotNull(cause);
        // The retained error variant is internal. Discover its public payload exactly as the
        // sweep discovers a public property, then probe the view through ordinary interfaces.
        var property = cause.GetType().GetProperty("Diagnostics", BindingFlags.Public | BindingFlags.Instance);
        Assert.NotNull(property);
        var diagnostics = Assert.IsAssignableFrom<IReadOnlyList<Diagnostic>>(property.GetValue(cause));
        Assert.Contains(diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.UnresolvedOpenTarget);
        PublishedCollection.AssertHandsOutNoStorage(diagnostics, "deferred materialization diagnostics");
    }

    private const string HostSuppliedAst =
        "AST list: the parser and the elaborator store the list they built, and a host-built node stores the host's list "
        + "(storage the host supplied and still owns); the AST's immutability contract is a separate owner question";

    private const string AstProjection =
        "AST projection: computed from the node's own lists, which are outside this guarantee (see the AST lists)";

    private const string AlwaysEmpty = "always empty: the shared bundle of no items has nothing to write";

    /// <summary>
    /// Public collection members the sweep does NOT attack, each with its reason. Exact: an entry
    /// that names no public member, or whose every value the corpus reaches already passes the
    /// attack, fails <see cref="TheExemptionList_IsExact"/>.
    /// </summary>
    private static readonly IReadOnlyDictionary<string, string> Exempt = new Dictionary<string, string>(StringComparer.Ordinal)
    {
        ["KatLang.Algorithm.Alias.Opens"] = HostSuppliedAst,
        ["KatLang.Algorithm.Alias.Properties"] = HostSuppliedAst,
        ["KatLang.Algorithm.Conditional.Branches"] = HostSuppliedAst,
        ["KatLang.Algorithm.Conditional.Opens"] = HostSuppliedAst,
        ["KatLang.Algorithm.User.Opens"] = HostSuppliedAst,
        ["KatLang.Algorithm.User.ParameterPatterns"] = HostSuppliedAst,
        ["KatLang.Algorithm.User.Parameters"] = AstProjection,
        ["KatLang.Algorithm.User.Params"] = AstProjection,
        ["KatLang.Algorithm.User.Properties"] = HostSuppliedAst,
        ["KatLang.Expr.Comparison.Links"] = HostSuppliedAst,
        ["KatLang.Expr.NativeCall.ArgNames"] = HostSuppliedAst,
        ["KatLang.ListValueParameterPattern.Captures"] = AstProjection,
        ["KatLang.ListValueParameterPattern.Items"] = HostSuppliedAst,
        ["KatLang.OutputBundle.Empty"] = AlwaysEmpty,
        ["KatLang.ParameterPattern.Captures"] = AstProjection,
        ["KatLang.Pattern.BoundNames()"] = AstProjection,
        ["KatLang.Pattern.TryGetOrdinaryClauseParams()"] = AstProjection,
        ["KatLang.Pattern.ListValue.Items"] = HostSuppliedAst,
        ["KatLang.Pattern.SequenceValue.Items"] = HostSuppliedAst,
        ["KatLang.Property.DeclarationSpans"] = HostSuppliedAst,
        ["KatLang.ScopeCtx.Opens"] = HostSuppliedAst,
        ["KatLang.ScopeCtx.Parameters"] = HostSuppliedAst,
        ["KatLang.ScopeCtx.Properties"] = HostSuppliedAst,
        ["KatLang.SequenceValueParameterPattern.Captures"] = AstProjection,
        ["KatLang.SequenceValueParameterPattern.Items"] = HostSuppliedAst,
        ["KatLang.UnpackingParameterPattern.Captures"] = AstProjection,
        ["KatLang.UnpackingParameterPattern.Items"] = HostSuppliedAst,
    };

    [Fact]
    public void EveryPublishedCollectionOfTheCorpus_HandsOutNoStorage()
    {
        var census = Census.Current.Value;
        var failures = new List<string>();
        foreach (var observation in census.Observations)
        {
            if (observation.Member is { } member && Exempt.ContainsKey(member))
                continue;
            try
            {
                PublishedCollection.AssertHandsOutNoStorage(observation.Value, observation.Path);
            }
            catch (Xunit.Sdk.XunitException failure)
            {
                failures.Add($"{observation.Member ?? "(element)"} at {observation.Path}: {FirstLine(failure.Message)}");
            }
        }

        output.WriteLine(census.Render(Exempt));
        Assert.True(census.Observations.Count > 200, $"The walk found only {census.Observations.Count} collections; the corpus is broken.");
        Assert.True(failures.Count == 0,
            $"{failures.Count} published collection(s) hand out writable storage:\n"
            + string.Join("\n", failures.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).Take(60)));
    }

    /// <summary>
    /// Coverage: every public collection-typed property and parameterless method of an exported
    /// type was reached with a NON-EMPTY value and attacked above, or is exempt with a reason.
    /// </summary>
    [Fact]
    public void EveryPublicCollectionMember_IsAttackedOrExempt()
    {
        var census = Census.Current.Value;
        var nonEmpty = census.Observations
            .Where(static observation => observation.Member is not null && ((IEnumerable)observation.Value).Cast<object?>().Any())
            .Select(static observation => observation.Member!)
            .ToHashSet(StringComparer.Ordinal);
        var uncovered = DeclaredCollectionMembers()
            .Where(member => !Exempt.ContainsKey(member) && !nonEmpty.Contains(member))
            .Order(StringComparer.Ordinal)
            .ToList();

        Assert.True(uncovered.Count == 0,
            "Public collection members the corpus never reached with a non-empty value. Extend the corpus of "
            + nameof(PublicCollectionStorageSweepTests) + " so the member is attacked, or exempt it with a reason:\n"
            + string.Join("\n", uncovered));
    }

    [Fact]
    public void TheExemptionList_IsExact()
    {
        var declared = DeclaredCollectionMembers().ToHashSet(StringComparer.Ordinal);
        Assert.Equal([], Exempt.Keys.Where(member => !declared.Contains(member)).Order(StringComparer.Ordinal));
        Assert.All(Exempt.Values, static reason => Assert.False(string.IsNullOrWhiteSpace(reason)));

        // An exemption is for a member that publishes storage this guarantee does not cover. A member the
        // corpus reaches only with values that pass the attack needs none: remove it, so it stays attacked.
        var census = Census.Current.Value;
        var unneeded = Exempt.Keys.Where(member =>
        {
            var reached = census.Observations
                .Where(observation => observation.Member == member && ((IEnumerable)observation.Value).Cast<object?>().Any())
                .ToList();
            return reached.Count > 0 && reached.All(static observation => PublishedCollection.FindStorage(observation.Value, observation.Path) is null);
        });
        Assert.Equal([], unneeded.Order(StringComparer.Ordinal));

        // RequiredAncestorParameters is the one AST list inside the guarantee: shared elaboration data.
        Assert.DoesNotContain("KatLang.Property.RequiredAncestorParameters", Exempt.Keys);
        Assert.Contains("KatLang.Property.RequiredAncestorParameters", declared);
    }

    /// <summary>
    /// No public member DECLARES a type through which engine-owned storage could leave: an array,
    /// a span or memory over one, or a mutable collection type. Inputs a host supplies are not
    /// outputs; the parameters of a callback the engine invokes are.
    /// </summary>
    [Fact]
    public void NoPublicMemberDeclaresAStorageExposingType()
    {
        var reviewed = new Dictionary<string, string>(StringComparer.Ordinal);
        var exposures = DeclaredStorageExposures(KatLang.GetExportedTypes()).Order(StringComparer.Ordinal).ToList();

        Assert.True(exposures.Except(reviewed.Keys).Count() == 0,
            "Public members whose declared type can hand out storage (review each; convert it to a read-only view, "
            + "or list it here with the reason it exposes no engine-owned storage):\n"
            + string.Join("\n", exposures.Except(reviewed.Keys)));
        Assert.Equal([], reviewed.Keys.Except(exposures).Order(StringComparer.Ordinal));
    }

    [Fact]
    public void TheDeclaredTypeScan_FlagsEveryStorageShape_AndNoReadOnlyOne()
    {
        Type[] exposing =
        [
            typeof(int[]), typeof(ArraySegment<int>), typeof(Memory<int>), typeof(ReadOnlyMemory<int>), typeof(Span<int>),
            typeof(List<int>), typeof(IList<int>), typeof(ICollection<int>), typeof(Dictionary<int, int>),
            typeof(IDictionary<int, int>), typeof(IReadOnlyDictionary<int, int>), typeof(HashSet<int>), typeof(ISet<int>),
            typeof(IReadOnlyList<int[]>), typeof(Task<Memory<int>>), typeof((int, List<int>)), typeof(EvalResult<int[]>),
            typeof(IList), typeof(ICollection), typeof(Array), typeof(DerivedList),
        ];
        Assert.All(exposing, static type => Assert.True(ExposesStorage(type), type.ToString()));

        Type[] readOnly =
        [
            typeof(IReadOnlyList<int>), typeof(IReadOnlyCollection<int>), typeof(IEnumerable<int>), typeof(string),
            typeof(ReadOnlySpan<int>), typeof(Task<IReadOnlyList<int>>), typeof((IReadOnlyList<int>, IReadOnlyList<string>)),
            typeof(EvalResult<IReadOnlyList<int>>), typeof(Result), typeof(int),
        ];
        Assert.All(readOnly, static type => Assert.False(ExposesStorage(type), type.ToString()));
    }

    private sealed class DerivedList : List<int> { }

    /// <summary>The member scan reads every output position of a type, and no input position.</summary>
    [Fact]
    public void TheDeclaredMemberScan_FlagsEveryOutputPosition_AndNoInput()
    {
        string[] expected =
        [
            "ExposureFixture.Callback() callback parameter items : System.Collections.Generic.IList`1[System.Int32]",
            "ExposureFixture.Field : System.Collections.Generic.List`1[System.Int32]",
            "ExposureFixture.Out() by-reference parameter items : System.Int32[]&",
            "ExposureFixture.Protected : System.Int32[]",
            "ExposureFixture.Raw : System.Int32[]",
            "ExposureFixture.Register() delegate argument callback(obj) : System.Int32[]",
            "ExposureFixture.Returned() returns System.Memory`1[System.Int32]",
            "ExposureFixture.op_Implicit() returns System.Int32[]",
        ];
        var found = DeclaredStorageExposures([typeof(ExposureFixture)])
            .Select(static exposure => exposure[(exposure.IndexOf(nameof(ExposureFixture), StringComparison.Ordinal))..]);
        Assert.Equal(expected, found.Order(StringComparer.Ordinal));
    }

    /// <summary>Output positions that expose storage beside inputs and read-only outputs that do not; only scanned.</summary>
    private class ExposureFixture
    {
        public List<int> Field = [];

        public int[] Raw => [];

        protected int[] Protected => [];

        internal int[] Internal => [];

        public IReadOnlyList<int> ReadOnly => [];

        public Memory<int> Returned() => default;

        public IEnumerable<int> ReturnedReadOnly() => [];

        public void Out(out int[] items) => items = [];

        public void Input(int[] items, List<int> more)
        {
        }

        public virtual void Callback(IList<int> items)
        {
        }

        public void Register(Action<int[]> callback, Func<int[]> supplier)
        {
        }

        public static implicit operator int[](ExposureFixture fixture) => fixture.Raw;

        public static implicit operator ExposureFixture(int[] items) => new();
    }

    /// <summary>The compiler's collection-expression lists the corpus can reach are read-only too.</summary>
    [Fact]
    public void CompilerSynthesizedLists_ReachedByTheCorpus_HandOutNoStorage()
    {
        var synthesized = Census.Current.Value.Observations
            .Where(static observation => observation.Value.GetType().Name.StartsWith("<>z__", StringComparison.Ordinal))
            .ToList();
        foreach (var observation in synthesized)
            PublishedCollection.AssertHandsOutNoStorage(observation.Value, observation.Path);
        output.WriteLine($"compiler-synthesized collection objects reached: {synthesized.Count} "
            + $"({string.Join(", ", synthesized.Select(static observation => observation.Value.GetType().Name).Distinct())})");
    }

    // ── Declared surface ────────────────────────────────────────────────────────────────

    private const BindingFlags Declared =
        BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static | BindingFlags.DeclaredOnly;

    /// <summary>Every public collection-typed property and parameterless method of an exported type.</summary>
    private static IEnumerable<string> DeclaredCollectionMembers()
    {
        foreach (var type in KatLang.GetExportedTypes())
        {
            foreach (var property in type.GetProperties(Declared))
            {
                if (property.GetMethod is { IsPublic: true } && property.GetIndexParameters().Length == 0 && IsCollectionType(property.PropertyType))
                    yield return MemberKey(property);
            }

            foreach (var method in type.GetMethods(Declared))
            {
                if (IsWalkedMethod(method))
                    yield return MemberKey(method);
            }
        }
    }

    private static bool IsWalkedMethod(MethodInfo method)
        => method is { IsPublic: true, IsSpecialName: false, IsGenericMethodDefinition: false }
            && method.GetParameters().Length == 0
            && IsCollectionType(method.ReturnType);

    private static bool IsCollectionType(Type type)
        => type != typeof(string) && typeof(IEnumerable).IsAssignableFrom(type);

    private static string MemberKey(MemberInfo member)
    {
        // A closed generic type's full name spells out its arguments' assemblies; its definition's does not.
        var declaring = member.DeclaringType!;
        if (declaring.IsGenericType)
            declaring = declaring.GetGenericTypeDefinition();
        return declaring.FullName!.Replace('+', '.') + "." + member.Name + (member is MethodInfo ? "()" : "");
    }

    /// <summary>
    /// Every public or protected member of an exported type whose declared output type exposes
    /// storage: property and field types, return types, by-reference parameters, and the parameters
    /// of the callbacks the engine invokes (virtual members a host overrides and delegate parameters).
    /// </summary>
    private static IEnumerable<string> DeclaredStorageExposures(IEnumerable<Type> types)
    {
        foreach (var type in types)
        {
            if (type.IsEnum || typeof(Delegate).IsAssignableFrom(type))
                continue;

            foreach (var property in type.GetProperties(Declared))
            {
                if (IsConsumerVisible(property.GetMethod) && ExposesStorage(property.PropertyType))
                    yield return $"{MemberKey(property)} : {property.PropertyType}";
            }

            foreach (var field in type.GetFields(Declared))
            {
                if ((field.IsPublic || field.IsFamily || field.IsFamilyOrAssembly) && ExposesStorage(field.FieldType))
                    yield return $"{MemberKey(field)} : {field.FieldType}";
            }

            foreach (var method in type.GetMethods(Declared))
            {
                // A property's accessors are read as the property; an operator is an ordinary method here.
                if (!IsConsumerVisible(method) || (method.IsSpecialName && !method.Name.StartsWith("op_", StringComparison.Ordinal)))
                    continue;
                if (ExposesStorage(method.ReturnType))
                    yield return $"{MemberKey(method)} returns {method.ReturnType}";

                var invokedByTheEngine = method.IsVirtual && !method.IsFinal && !type.IsSealed;
                foreach (var parameter in method.GetParameters())
                {
                    var parameterType = parameter.ParameterType;
                    if (parameterType.IsByRef && ExposesStorage(parameterType.GetElementType()!))
                        yield return $"{MemberKey(method)} by-reference parameter {parameter.Name} : {parameterType}";
                    else if (invokedByTheEngine && ExposesStorage(parameterType))
                        yield return $"{MemberKey(method)} callback parameter {parameter.Name} : {parameterType}";

                    if (typeof(Delegate).IsAssignableFrom(parameterType) && parameterType.GetMethod("Invoke") is { } invoke)
                    {
                        foreach (var argument in invoke.GetParameters())
                        {
                            if (ExposesStorage(argument.ParameterType))
                                yield return $"{MemberKey(method)} delegate argument {parameter.Name}({argument.Name}) : {argument.ParameterType}";
                        }
                    }
                }
            }
        }
    }

    private static bool IsConsumerVisible(MethodBase? method)
        => method is not null && (method.IsPublic || method.IsFamily || method.IsFamilyOrAssembly);

    private static readonly HashSet<Type> StorageShapes =
    [
        typeof(Array), typeof(IList), typeof(ICollection), typeof(IDictionary),
        typeof(ArraySegment<>), typeof(Memory<>), typeof(ReadOnlyMemory<>), typeof(Span<>),
        typeof(List<>), typeof(IList<>), typeof(ICollection<>), typeof(LinkedList<>), typeof(Queue<>), typeof(Stack<>),
        typeof(Dictionary<,>), typeof(IDictionary<,>), typeof(IReadOnlyDictionary<,>), typeof(SortedDictionary<,>), typeof(SortedList<,>),
        typeof(HashSet<>), typeof(SortedSet<>), typeof(ISet<>), typeof(IReadOnlySet<>),
        typeof(System.Collections.ObjectModel.Collection<>), typeof(System.Collections.ObjectModel.ReadOnlyCollection<>),
        typeof(System.Collections.ObjectModel.ReadOnlyDictionary<,>),
    ];

    /// <summary>
    /// Whether <paramref name="type"/> is, or carries in a generic argument, a type that can hand
    /// out storage: an array, a span or memory, or a collection type other than the three read-only
    /// sequence interfaces. A dictionary or set type is flagged even when read-only, because the
    /// sweep's attack only understands lists; such a member needs its own review.
    /// </summary>
    private static bool ExposesStorage(Type type)
    {
        if (type.IsByRef || type.IsPointer)
            return ExposesStorage(type.GetElementType()!);
        if (type.IsArray)
            return true;
        if (StorageShapes.Contains(type) || type.GetInterfaces().Any(contract =>
            StorageShapes.Contains(contract.IsGenericType ? contract.GetGenericTypeDefinition() : contract)))
            return true;
        if (!type.IsGenericType)
            return false;
        return StorageShapes.Contains(type.GetGenericTypeDefinition()) || type.GetGenericArguments().Any(ExposesStorage);
    }

    private static string FirstLine(string text)
    {
        var end = text.IndexOf('\n');
        return (end < 0 ? text : text[..end]).TrimEnd('\r');
    }

    // ── The corpus and its walk ─────────────────────────────────────────────────────────

    /// <summary>One collection the walk found: the member that returned it (null for an element), and where.</summary>
    private sealed record Observation(string? Member, object Value, string Path);

    /// <summary>The result of a member the walk cannot invoke itself: a static, a callback argument, or a method that takes arguments.</summary>
    private sealed record MemberResult(string Member, object? Value);

    private sealed class Census
    {
        public static readonly Lazy<Census> Current = new(Build);

        public List<Observation> Observations { get; } = [];

        private readonly HashSet<object> _visited = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<object, HashSet<string>> _credited = new(ReferenceEqualityComparer.Instance);
        private readonly Stack<(object Value, string Path, int Depth)> _pending = new();

        private const int MaximumVisits = 2_000_000;
        private const int MaximumValueTypeDepth = 64;

        private Census()
        {
        }

        private static Census Build()
        {
            var census = new Census();
            foreach (var (label, root) in StaticRoots().Concat(Corpus()))
                census.Walk(root, label);
            return census;
        }

        private void Walk(object? root, string label)
        {
            if (root is MemberResult result)
                Push(result.Value, label, result.Member, depth: 0);
            else
                Push(root, label, member: null, depth: 0);

            var visits = 0;
            while (_pending.TryPop(out var frame))
            {
                Assert.True(++visits <= MaximumVisits, $"The walk from {label} did not end after {MaximumVisits} objects.");
                var (value, path, depth) = frame;
                var type = value.GetType();

                if (value is ITuple tuple)
                {
                    for (var index = 0; index < tuple.Length; index++)
                        Push(tuple[index], $"{path}.Item{index + 1}", member: null, depth + 1);
                    continue;
                }

                if (value is IEnumerable sequence)
                {
                    var index = 0;
                    foreach (var element in sequence)
                        Push(element, $"{path}[{index++}]", member: null, depth + 1);
                }

                if (type.Assembly != KatLang)
                    continue;

                foreach (var property in type.GetProperties(BindingFlags.Public | BindingFlags.Instance))
                {
                    if (property.GetMethod is not { IsPublic: true } || property.GetIndexParameters().Length != 0 || !IsPublicKatLangMember(property))
                        continue;
                    if (TryRead(() => property.GetValue(value), out var read))
                        Push(read, $"{path}.{property.Name}", MemberKey(property), depth + 1);
                }

                foreach (var method in type.GetMethods(BindingFlags.Public | BindingFlags.Instance))
                {
                    if (!IsWalkedMethod(method) || !IsPublicKatLangMember(method))
                        continue;
                    if (TryRead(() => method.Invoke(value, null), out var returned))
                        Push(returned, $"{path}.{method.Name}()", MemberKey(method), depth + 1);
                }
            }
        }

        /// <summary>A member a consumer can name: declared by a publicly visible KatLang type.</summary>
        private static bool IsPublicKatLangMember(MemberInfo member)
            => member.DeclaringType is { IsVisible: true } declaring && declaring.Assembly == KatLang;

        private static bool TryRead(Func<object?> read, out object? value)
        {
            try
            {
                value = read();
                return true;
            }
            catch (TargetInvocationException)
            {
                // A member that refuses in this state (EvalResult.Value of an error) publishes nothing.
                value = null;
                return false;
            }
        }

        private void Push(object? value, string path, string? member, int depth)
        {
            if (value is null or string)
                return;
            var type = value.GetType();
            if (type.IsPrimitive || type.IsEnum)
                return;

            // One observation per collection object and member that returned it (an element has no member).
            if (value is IEnumerable && (type.IsValueType || CreditedMembers(value).Add(member ?? "")))
                Observations.Add(new Observation(member, value, path));

            if (type.IsValueType)
            {
                // A boxed struct has no identity to remember; the depth bounds the walk instead.
                if (depth > MaximumValueTypeDepth || (type.Assembly != KatLang && value is not ITuple and not IEnumerable))
                    return;
            }
            else if (!_visited.Add(value))
            {
                return;
            }

            _pending.Push((value, path, depth));
        }

        private HashSet<string> CreditedMembers(object collection)
        {
            if (!_credited.TryGetValue(collection, out var members))
                _credited.Add(collection, members = new HashSet<string>(StringComparer.Ordinal));
            return members;
        }

        public string Render(IReadOnlyDictionary<string, string> exempt)
        {
            var text = new StringBuilder();
            text.AppendLine($"collections observed: {Observations.Count}");
            foreach (var group in Observations.Where(static observation => observation.Member is not null)
                .GroupBy(static observation => observation.Member!, StringComparer.Ordinal).OrderBy(static group => group.Key, StringComparer.Ordinal))
            {
                var types = group.Select(static observation => observation.Value.GetType().ToString()).Distinct().Order(StringComparer.Ordinal);
                var nonEmpty = group.Count(static observation => ((IEnumerable)observation.Value).Cast<object?>().Any());
                text.AppendLine($"{(exempt.ContainsKey(group.Key) ? "exempt" : "attack")} {group.Key}: {group.Count()} seen, {nonEmpty} non-empty; {string.Join(" | ", types)}");
            }

            var elements = Observations.Where(static observation => observation.Member is null)
                .Select(static observation => observation.Value.GetType().ToString()).Distinct().Order(StringComparer.Ordinal);
            text.AppendLine($"attack (elements and roots): {string.Join(" | ", elements)}");
            return text.ToString();
        }

        /// <summary>Every public static property, and static parameterless collection method, of an exported type.</summary>
        private static IEnumerable<(string Label, object? Root)> StaticRoots()
        {
            foreach (var type in KatLang.GetExportedTypes())
            {
                if (type.ContainsGenericParameters)
                    continue;

                foreach (var property in type.GetProperties(BindingFlags.Public | BindingFlags.Static | BindingFlags.DeclaredOnly))
                {
                    if (property.GetMethod is { IsPublic: true } && property.GetIndexParameters().Length == 0)
                        yield return (MemberKey(property), new MemberResult(MemberKey(property), property.GetValue(null)));
                }

                foreach (var method in type.GetMethods(BindingFlags.Public | BindingFlags.Static | BindingFlags.DeclaredOnly))
                {
                    if (IsWalkedMethod(method))
                        yield return (MemberKey(method), new MemberResult(MemberKey(method), method.Invoke(null, null)));
                }
            }
        }

        /// <summary>The objects KatLang hands to a host, built through the public API alone.</summary>
        private static IEnumerable<(string Label, object? Root)> Corpus()
        {
            const string program = """
                V = [1, 2, 3]
                Outer(n) = {
                    Inner = n + 1
                    Inner
                }
                Pick(0) = 0
                Pick(k) = k + 1
                Pair((p, q)) = p + q
                Head([h, t]) = h
                Size([]) = 0
                Size([a, b]) = 2
                Swap((0, b)) = b
                Swap((a, b)) = a
                Spread(first, *rest) = first
                Implicit = z + 1
                Twin = Outer
                x, y = (7, 8)
                Small = 1 < 2 < 3
                V, (4, 5), range(1, 5), [[1, 2], (3, 4)], Outer(1), Pick(2), Pair((1, 2)), Head([1, 2]), Size([1, 2]), Swap((1, 2))
                Spread(1, 2, 3), Implicit(1), Twin(2), x + y, Small, V.take(2), V[0], poke(V, 1)
                """;

            var hostArguments = new List<IReadOnlyList<Result>>();
            var operation = HostOperation.Create("poke", (arguments, _) =>
            {
                hostArguments.Add(arguments);
                return new Result.ListValue([arguments[0], new Result.Str("s")]);
            }, "value", "other");
            var asynchronous = HostOperation.CreateAsync("pokeLater", async (arguments, _) =>
            {
                await Task.Yield();
                hostArguments.Add(arguments);
                return arguments[0];
            }, "value");
            var operations = HostOperations.Create(operation);
            var asynchronousOperations = HostOperations.Create(operation, asynchronous);
            var options = new RunOptions
            {
                HostOperations = operations,
                AllowedHosts = ["katlang.org", "example.org"],
                ObservePropertyValues = true,
            };

            yield return ("HostOperations", operations);
            yield return ("HostOperations (asynchronous)", asynchronousOperations);
            yield return ("RunOptions", options);

            var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(program, options));
            yield return ("RunResult.Success", success);
            yield return ("RunResult.Success.WithHostDecimalPlaces", success.WithHostDecimalPlaces(null, 2));
            yield return ("RunResult.Success (async)", Assert.IsType<RunResult.Success>(
                KatLangEngine.RunAsync("V = [1, 2]\npokeLater(V), V", new RunOptions { HostOperations = asynchronousOperations })
                    .GetAwaiter().GetResult()));
            yield return ("RunResult.Success (one row)", KatLangEngine.Run("[1, 2, 3]"));
            yield return ("RunResult.NoProgramOutput", KatLangEngine.Run("A = 1"));
            yield return ("RunResult.ParseFailure", KatLangEngine.Run("1 +\n2 +"));
            Assert.Equal(2, hostArguments.Count);
            foreach (var arguments in hostArguments)
                yield return ("host operation arguments", new MemberResult("(callback) HostOperation implementation arguments", arguments));

            string[] failing =
            [
                "1 / 0",
                "Outer(n) = {\n    Inner = n + 1\n    Inner\n}\nOuter.Inner",
                "Add(acc, item) = acc + item\nreduce([1, 2], Add, Add)",
                "x, y = 1, 2, 3\nx",
                "Step(a, b) = a, b\nrepeat(Step(1, 2, 3), 1)",
                "Step(a, *r) = a\nrepeat(Step(), 1)",
                "Inc(x) = x + 1\nAdd(e, a) = e + a\nProbe(unused) = reduce([1, 2], Add, Inc)\nProbe(0)",
            ];
            foreach (var source in failing)
                yield return ($"RunResult.EvalFailure: {source.ReplaceLineEndings(" | ")}", Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)));

            var ambiguous = Parser.Parse("open A, B\nA = {\n    public Test = 1\n}\nB = {\n    public Test = 2\n}\nTest");
            yield return ("ParseResult (diagnostics)", ambiguous);
            Assert.Equal(DiagnosticCode.AmbiguousOpen, Assert.Single(ambiguous.Diagnostics).Code);
            yield return ("Evaluator.Run error", ReadOnlyViewStorageContractTests.AmbiguousOpenError());

            var parsed = Parser.Parse(program, options);
            Assert.False(parsed.HasErrors);
            yield return ("ParseResult", parsed);
            var flatParse = Parser.Parse("[1, 2], (3, 4)");
            Assert.False(flatParse.HasErrors);
            var flat = flatParse.Root;
            yield return ("Evaluator.Run", Evaluator.Run(new Expr.AlgorithmExpr(flat)));
            yield return ("Evaluator.RunFlat", Evaluator.RunFlat(new Expr.AlgorithmExpr(flat)));
            yield return ("KatLangEngine.EvaluateToAtoms", new MemberResult("KatLang.KatLangEngine.EvaluateToAtoms(…)", KatLangEngine.EvaluateToAtoms("1, [2, 3]")));
            yield return ("KatLangException", new KatLangException([.. Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("1 +")).Errors]));
            yield return ("KatLangException (thrown)", Assert.Throws<KatLangException>(() => KatLangEngine.EvaluateToAtoms("1 +")));
            yield return ("Lexer.Tokenize", Lexer.Tokenize("A @= 1\nA"));

            var model = SemanticModelBuilder.Build(parsed);
            yield return ("SemanticModel", model);
            yield return ("SemanticModel.FindDeclarations", new MemberResult("KatLang.Semantics.SemanticModel.FindDeclarations(…)", model.FindDeclarations("V")));
            yield return ("SemanticModel.FindResolutions", new MemberResult("KatLang.Semantics.SemanticModel.FindResolutions(…)", model.FindResolutions("V")));
            yield return ("SemanticModel.FindProperties", new MemberResult("KatLang.Semantics.SemanticModel.FindProperties(…)", model.FindProperties("V")));
            yield return ("SemanticModel.GetVisibleSymbolsAt", new MemberResult("KatLang.Semantics.SemanticModel.GetVisibleSymbolsAt(…)", model.GetVisibleSymbolsAt(new SourcePosition(3, 5))));
            yield return ("SemanticModel.FindScopeAt", model.FindScopeAt(new SourcePosition(3, 5)));
            yield return ("SemanticModel (host AST)", SemanticModelBuilder.Build(ambiguous.Root));
            foreach (var property in model.PropertyInfos)
            {
                foreach (var style in new[] { PropertyCallStyle.Plain, PropertyCallStyle.Dot })
                {
                    yield return ($"PropertyInfo.GetParameters({property.Name}, {style})",
                        new MemberResult("KatLang.Semantics.PropertyInfo.GetParameters(…)", property.GetParameters(style)));
                }
            }

            var formatter = new CapturingFormatter();
            _ = formatter.Format(success);
            _ = formatter.Format(Assert.IsType<RunResult.Success>(KatLangEngine.Run("[1, 2, 3]")));
            Assert.Equal(2, formatter.Rows.Count);
            foreach (var rows in formatter.Rows)
                yield return ("OutputFormatter rows", new MemberResult("(callback) OutputFormatter.WriteSuccessOutput outputRows", rows));
        }
    }

    private sealed class CapturingFormatter : OutputFormatter
    {
        public List<IReadOnlyList<Result>> Rows { get; } = [];

        public override string Id => "capturing";

        protected override bool WriteSuccessOutput(IReadOnlyList<Result> outputRows, OutputFormattingOptions options, BoundedOutputWriter writer)
        {
            Rows.Add(outputRows);
            return true;
        }
    }
}
