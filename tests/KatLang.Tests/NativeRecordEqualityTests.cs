using System.Numerics;
using System.Reflection;
using System.Runtime.CompilerServices;
using KatLang.Tests.LanguageSpec;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// NATIVE RECORD EQUALITY AND HASHING ON HOST-BUILT ASTS
/// (docs/design/language-rules/evaluator-and-hosting.md § Shared-DAG guarantee, NATIVE RECORD
/// EQUALITY). The records whose compiler-generated equality followed a record-valued field —
/// every <see cref="Expr"/> variant with an expression or algorithm child, the three scope-owning
/// <see cref="Algorithm"/> variants and <see cref="ScopeCtx"/> — now compare and hash on an explicit
/// stack with a call-local memo. This class pins what that rewrite must not change and what it
/// promises:
/// <list type="bullet">
///   <item>PARITY: <see cref="GeneratedRecordContract"/> is the compiler's record-synthesis
///   algorithm written over reflection (never the implementation under test). Every verdict and
///   every hash value of a bounded, diverse corpus — hand-built variants, generated trees and
///   shared DAGs, <c>with</c> copies, every field mutated in turn, and every node the parser
///   produces for the shared corpora — equals the contract's.</item>
///   <item>INVENTORY: the set of AST records with hand-written equality is exact, and no AST
///   record with a record-valued field on a cycle keeps recursive generated equality.</item>
///   <item>DEPTH: 200,000 levels through every recursive field (also run on a 1 MiB thread in a
///   child process by <see cref="AstStructuralDepthProcessTests"/>).</item>
///   <item>DAG WORK: a shared node's fields are compared and hashed once per distinct node (pair),
///   counted through host-defined collections; nothing is retained between operations.</item>
/// </list>
/// </summary>
public class NativeRecordEqualityTests(ITestOutputHelper output)
{
    // ── The compiler-generated record contract, over reflection (the oracle) ─

    /// <summary>
    /// What the C# compiler synthesizes for a record class, computed from metadata: equality is
    /// reference identity, else the same <c>EqualityContract</c> and every instance field, base
    /// first, in declaration order, each through <c>EqualityComparer&lt;TField&gt;.Default</c>;
    /// the hash folds the contract and the same fields with the multiplier -1521134295. A field
    /// whose type is an AST record is expanded by this oracle itself, so no hand-written
    /// <c>Equals</c>/<c>GetHashCode</c> of the library is ever its own judge. <see cref="ScopeCtx"/>
    /// never had generated equality: its legacy hand-written contract is restated here.
    /// </summary>
    internal static class GeneratedRecordContract
    {
        private const BindingFlags DeclaredInstance =
            BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly;

        internal static readonly Type[] Families =
        [
            typeof(Expr), typeof(Algorithm), typeof(ScopeCtx), typeof(Property), typeof(CondBranch),
            typeof(ComparisonLink), typeof(InterpolationLink), typeof(Pattern), typeof(ParameterPattern),
            typeof(ParameterDeclaration),
        ];

        private static readonly Dictionary<Type, FieldInfo[]> FieldCache = [];
        private static readonly Dictionary<Type, (object Comparer, MethodInfo EqualsMethod, MethodInfo HashMethod)> Comparers = [];

        internal static bool IsRecordClass(Type type)
            => type.IsClass && type.GetMethod("<Clone>$", BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic) is not null;

        /// <summary>Whether <paramref name="type"/> is an AST record the oracle expands instead of asking.</summary>
        internal static bool IsModeled(Type type)
            => type.Assembly == typeof(Expr).Assembly && IsRecordClass(type) && Families.Any(family => family.IsAssignableFrom(type));

        /// <summary>Every instance field of <paramref name="type"/>, base record first, in declaration order.</summary>
        internal static FieldInfo[] Fields(Type type)
        {
            lock (FieldCache)
            {
                if (FieldCache.TryGetValue(type, out var known))
                    return known;
                var levels = new Stack<Type>();
                for (var level = type; level is not null && level != typeof(object); level = level.BaseType)
                    levels.Push(level);
                return FieldCache[type] = levels.SelectMany(static level => level.GetFields(DeclaredInstance)).ToArray();
            }
        }

        private static Type EqualityContract(object record)
            => (Type)record.GetType()
                .GetProperty("EqualityContract", BindingFlags.Instance | BindingFlags.NonPublic)!
                .GetValue(record)!;

        private static (object Comparer, MethodInfo EqualsMethod, MethodInfo HashMethod) DefaultComparer(Type type)
        {
            lock (Comparers)
            {
                if (Comparers.TryGetValue(type, out var known))
                    return known;
                var comparerType = typeof(EqualityComparer<>).MakeGenericType(type);
                var comparer = comparerType.GetProperty("Default", BindingFlags.Public | BindingFlags.Static)!.GetValue(null)!;
                return Comparers[type] = (
                    comparer,
                    comparerType.GetMethod("Equals", [type, type])!,
                    comparerType.GetMethod("GetHashCode", [type])!);
            }
        }

        /// <summary><c>EqualityComparer&lt;declared&gt;.Default.Equals(left, right)</c> as the generated code calls it.</summary>
        internal static bool Equals(Type declared, object? left, object? right)
        {
            if (!IsModeled(declared))
            {
                var (comparer, equals, _) = DefaultComparer(declared);
                return (bool)equals.Invoke(comparer, [left, right])!;
            }

            // The default comparer of an IEquatable reference type: nulls, then left.Equals(right),
            // which a sealed record answers for `right as TLeft`.
            if (left is null || right is null)
                return left is null && right is null;
            if (left.GetType() != right.GetType())
                return false;
            if (ReferenceEquals(left, right))
                return true;

            if (left is ScopeCtx leftScope)
            {
                var rightScope = (ScopeCtx)right;
                return Equals(typeof(ScopeCtx), leftScope.Parent, rightScope.Parent)
                    && Equals(typeof(IReadOnlyList<Expr>), leftScope.Opens, rightScope.Opens)
                    && Equals(typeof(IReadOnlyList<Property>), leftScope.Properties, rightScope.Properties)
                    && Equals(typeof(IReadOnlyList<string>), leftScope.Parameters, rightScope.Parameters);
            }

            if (EqualityContract(left) != EqualityContract(right))
                return false;
            foreach (var field in Fields(left.GetType()))
            {
                if (!Equals(field.FieldType, field.GetValue(left), field.GetValue(right)))
                    return false;
            }

            return true;
        }

        /// <summary><c>EqualityComparer&lt;declared&gt;.Default.GetHashCode(value)</c> as the generated code calls it.</summary>
        internal static int Hash(Type declared, object? value)
        {
            if (!IsModeled(declared))
            {
                var (comparer, _, hasher) = DefaultComparer(declared);
                return (int)hasher.Invoke(comparer, [value])!;
            }

            if (value is null)
                return 0;
            if (value is ScopeCtx scope)
            {
                // Legacy: HashCode.Combine(Parent, Opens, Properties, Parameters). Combine reads its
                // first component as `Parent?.GetHashCode() ?? 0`, and an int hashes to itself.
                return HashCode.Combine(Hash(typeof(ScopeCtx), scope.Parent), scope.Opens, scope.Properties, scope.Parameters);
            }

            var hash = EqualityComparer<Type>.Default.GetHashCode(EqualityContract(value));
            foreach (var field in Fields(value.GetType()))
                hash = unchecked(hash * -1521134295 + Hash(field.FieldType, field.GetValue(value)));
            return hash;
        }
    }

    /// <summary>The static type the library declares a record of this family as (the comparer the generated code picks).</summary>
    private static Type FamilyOf(object record) => record switch
    {
        Expr => typeof(Expr),
        Algorithm => typeof(Algorithm),
        Pattern => typeof(Pattern),
        ParameterPattern => typeof(ParameterPattern),
        _ => record.GetType(),
    };

    // Every native route to equality for one ordered pair, against the contract. Messages name
    // types only: a record's generated text is not part of this subject.
    private static bool AssertPairParity(object left, object right)
    {
        var expected = GeneratedRecordContract.Equals(FamilyOf(left), left, right);
        var where = $"{left.GetType().Name} vs {right.GetType().Name}, expected {expected}";
        Assert.True(expected == left.Equals(right), "Equals(object): " + where);
        Assert.True(expected == Equals(left, right), "object.Equals(a, b): " + where);
        switch (left, right)
        {
            case (Expr a, Expr b):
                Assert.True(expected == a.Equals(b), "Equals(Expr): " + where);
                Assert.True(expected == (a == b), "==: " + where);
                Assert.True(expected != (a != b), "!=: " + where);
                Assert.True(expected == EqualityComparer<Expr>.Default.Equals(a, b), "default comparer: " + where);
                break;
            case (Algorithm a, Algorithm b):
                Assert.True(expected == a.Equals(b), "Equals(Algorithm): " + where);
                Assert.True(expected == (a == b), "==: " + where);
                Assert.True(expected != (a != b), "!=: " + where);
                Assert.True(expected == EqualityComparer<Algorithm>.Default.Equals(a, b), "default comparer: " + where);
                break;
            case (ScopeCtx a, ScopeCtx b):
                Assert.True(expected == a.Equals(b), "Equals(ScopeCtx): " + where);
                Assert.True(expected == (a == b), "==: " + where);
                Assert.True(expected != (a != b), "!=: " + where);
                Assert.True(expected == EqualityComparer<ScopeCtx>.Default.Equals(a, b), "default comparer: " + where);
                break;
        }

        if (left.GetType() == right.GetType())
        {
            // The strongly typed members of the concrete record: Equals(T), operator ==, operator !=.
            var type = left.GetType();
            object?[] pair = [left, right];
            Assert.True(expected == (bool)type.GetMethod("Equals", [type])!.Invoke(left, [right])!, "Equals(T): " + where);
            Assert.True(expected == (bool)type.GetMethod("op_Equality", [type, type])!.Invoke(null, pair)!, "T ==: " + where);
            Assert.True(expected != (bool)type.GetMethod("op_Inequality", [type, type])!.Invoke(null, pair)!, "T !=: " + where);
        }

        if (expected)
            Assert.True(left.GetHashCode() == right.GetHashCode(), "equal records hash alike: " + where);
        return expected;
    }

    private static void AssertHashParity(object record)
    {
        var expected = GeneratedRecordContract.Hash(FamilyOf(record), record);
        Assert.True(expected == record.GetHashCode(), $"GetHashCode of {record.GetType().Name}");
        Assert.True(expected == record.GetHashCode(), $"repeated GetHashCode of {record.GetType().Name}");
        switch (record)
        {
            case Expr expr:
                Assert.True(expected == EqualityComparer<Expr>.Default.GetHashCode(expr), "default comparer hash");
                break;
            case Algorithm algorithm:
                Assert.True(expected == EqualityComparer<Algorithm>.Default.GetHashCode(algorithm), "default comparer hash");
                break;
            case ScopeCtx scope:
                Assert.True(expected == EqualityComparer<ScopeCtx>.Default.GetHashCode(scope), "default comparer hash");
                break;
        }
    }

    // ── Corpus construction ──────────────────────────────────────────────────

    private static readonly SourceSpan SpanA = new(1, 2, 1, 6);
    private static readonly SourceSpan SpanB = new(3, 1, 3, 9);

    /// <summary>
    /// Deterministic generator of records over a small pool of REFERENCE-COMPARED parts (bundles and
    /// lists): two records built over the same part instance can be equal, two over equal-content
    /// instances cannot — exactly the generated contract's distinction.
    /// </summary>
    private sealed class RecordGenerator
    {
        private readonly Random _random;
        private readonly List<Expr> _exprs = [];
        private readonly List<Algorithm> _algorithms = [];
        private readonly List<ScopeCtx> _scopes = [];

        // Index 1 and 2 of each kind have equal content and different identities.
        private readonly OutputBundle[] _bundles =
        [
            OutputBundle.Empty, new([new Expr.Num(1)]), new([new Expr.Num(1)]), new([new Expr.Resolve("a"), new Expr.Num(2)]),
        ];

        private readonly IReadOnlyList<ComparisonLink>[] _links =
        [
            Array.Empty<ComparisonLink>(),
            new[] { new ComparisonLink(ComparisonOp.Lt, new Expr.Num(3)) },
            new List<ComparisonLink> { new(ComparisonOp.Lt, new Expr.Num(3)) },
        ];

        private readonly IReadOnlyList<InterpolationLink>[] _interpolations =
        [
            Array.Empty<InterpolationLink>(),
            new[] { new InterpolationLink(new Expr.Resolve("h"), "t") },
            new[] { new InterpolationLink(new Expr.Resolve("h"), "t") },
        ];

        private readonly IReadOnlyList<Expr>[] _opens = [Array.Empty<Expr>(), new Expr[] { new Expr.Resolve("M") }, new Expr[] { new Expr.Resolve("M") }];
        private readonly IReadOnlyList<Property>[] _properties;
        private readonly IReadOnlyList<ParameterPattern>[] _patterns =
        [
            Array.Empty<ParameterPattern>(),
            new ParameterPattern[] { new CaptureParameterPattern("x") },
            new ParameterPattern[] { new CaptureParameterPattern("x") },
        ];

        private readonly IReadOnlyList<string>[] _names = [Array.Empty<string>(), new[] { "x" }, new[] { "x" }];
        private readonly IReadOnlyList<CondBranch>[] _branches;

        public RecordGenerator(int seed)
        {
            _random = new Random(seed);
            var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
            _properties = [Array.Empty<Property>(), new[] { new Property("P", body) }, new[] { new Property("P", body) }];
            _branches =
            [
                Array.Empty<CondBranch>(),
                new[] { new CondBranch(new Pattern.LitInt(0), body) },
                new[] { new CondBranch(new Pattern.LitInt(0), body) },
            ];
        }

        public IReadOnlyList<Expr> Exprs => _exprs;

        public IReadOnlyList<Algorithm> Algorithms => _algorithms;

        public IReadOnlyList<ScopeCtx> Scopes => _scopes;

        private T Pick<T>(IReadOnlyList<T> options) => options[_random.Next(options.Count)];

        private SourceSpan? Span() => _random.Next(4) switch { 0 => SpanA, 1 => SpanB, _ => null };

        public ScopeCtx? Scope(int depth)
        {
            if (_scopes.Count > 0 && _random.Next(3) == 0)
                return Pick(_scopes);
            if (depth <= 0 || _random.Next(3) == 0)
                return null;
            var scope = new ScopeCtx(Scope(depth - 1), Pick(_opens), Pick(_properties), Pick(_names));
            _scopes.Add(scope);
            return scope;
        }

        public Algorithm Algorithm(int depth)
        {
            if (_algorithms.Count > 0 && _random.Next(4) == 0)
                return Pick(_algorithms);
            Algorithm algorithm = _random.Next(depth <= 0 ? 2 : 5) switch
            {
                0 => new Algorithm.Builtin(_random.Next(2) == 0 ? BuiltinId.sum : BuiltinId.count),
                1 => new Algorithm.User(Scope(2), Pick(_patterns), Pick(_opens), Pick(_properties), Pick(_bundles))
                {
                    HasExplicitParameterList = _random.Next(2) == 0,
                },
                2 => new Algorithm.Conditional(Scope(2), Pick(_opens), Pick(_branches)),
                3 => new Algorithm.Alias(Scope(2), Pick(_opens), Pick(_properties), Expr(depth - 1)) { IsReference = _random.Next(2) == 0 },
                _ => new Algorithm.User(Scope(3), Pick(_patterns), Pick(_opens), Pick(_properties), Pick(_bundles)),
            };
            _algorithms.Add(algorithm);
            return algorithm;
        }

        private Expr Leaf() => _random.Next(10) switch
        {
            0 => new Expr.Num(_random.Next(3)),
            1 => new Expr.Param(_random.Next(2) == 0 ? "p" : "q"),
            2 => new Expr.Resolve(_random.Next(2) == 0 ? "a" : "b"),
            3 => new Expr.StringLiteral(_random.Next(2) == 0 ? "s" : "t"),
            4 => new Expr.BoolLiteral(_random.Next(2) == 0),
            5 => new Expr.EmptySequence(_random.Next(2)),
            6 => new Expr.ListLiteral(Pick(_bundles)),
            7 => new Expr.Capture(Pick(_bundles)),
            8 => new Expr.NativeCall("Sin", Pick(_names)),
            _ => new Expr.InterpolatedString("head", Pick(_interpolations)),
        };

        public Expr Expr(int depth)
        {
            // Sharing: an existing node becomes a child of several parents.
            if (_exprs.Count > 0 && _random.Next(4) == 0)
                return Pick(_exprs);
            Expr expr;
            if (depth <= 0 || _random.Next(5) == 0)
            {
                expr = Leaf();
            }
            else
            {
                expr = _random.Next(11) switch
                {
                    0 => new Expr.Unary(_random.Next(2) == 0 ? UnaryOp.Minus : UnaryOp.Not, Expr(depth - 1)),
                    1 => new Expr.Binary(_random.Next(2) == 0 ? BinaryOp.Add : BinaryOp.Mul, Expr(depth - 1), Expr(depth - 1)),
                    2 => new Expr.Comparison(Expr(depth - 1), Pick(_links)),
                    3 => new Expr.Index(Expr(depth - 1), Pick(_bundles)),
                    4 => new Expr.SequenceConstruct(Expr(depth - 1), Expr(depth - 1)),
                    5 => new Expr.SequenceSpread(Expr(depth - 1)) { SpreadMarkerSpan = Span() },
                    6 => new Expr.DotCall(Expr(depth - 1), _random.Next(2) == 0 ? "m" : "n", _random.Next(3) == 0 ? null : Pick(_bundles))
                    {
                        MemberSpan = Span(),
                        LexicalFallback = _random.Next(2) == 0 ? null : Expr(depth - 1),
                    },
                    7 => new Expr.Grace(Expr(depth - 1), _random.Next(2) == 0 ? 1 : -1),
                    8 => new Expr.AlgorithmExpr(Algorithm(depth - 1)),
                    9 => new Expr.Call(Expr(depth - 1), Pick(_bundles)),
                    _ => new Expr.DotCall(Expr(depth - 1), "m"),
                };
            }

            if (_random.Next(3) == 0)
                expr = expr with { Span = Span() };
            _exprs.Add(expr);
            return expr;
        }
    }

    /// <summary>
    /// An independently allocated copy of <paramref name="expr"/> made of <c>with</c> copies: every
    /// record on the way down is a new object, every reference-compared part is the original one,
    /// so the generated contract calls the copy equal.
    /// </summary>
    private static Expr Rebuild(Expr expr, int depth = 0) => expr switch
    {
        Expr.Unary unary => unary with { Operand = Rebuild(unary.Operand, depth + 1) },
        Expr.Binary binary => binary with { Left = Rebuild(binary.Left, depth + 1), Right = Rebuild(binary.Right, depth + 1) },
        Expr.Comparison comparison => comparison with { First = Rebuild(comparison.First, depth + 1) },
        Expr.Index index => index with { Target = Rebuild(index.Target, depth + 1) },
        Expr.SequenceConstruct sequence => sequence with { Left = Rebuild(sequence.Left, depth + 1), Right = Rebuild(sequence.Right, depth + 1) },
        Expr.SequenceSpread spread => spread with { Operand = Rebuild(spread.Operand, depth + 1) },
        Expr.DotCall dot => dot with
        {
            Target = Rebuild(dot.Target, depth + 1),
            LexicalFallback = dot.LexicalFallback is { } fallback ? Rebuild(fallback, depth + 1) : null,
        },
        Expr.Grace grace => grace with { Inner = Rebuild(grace.Inner, depth + 1) },
        Expr.AlgorithmExpr algorithm => algorithm with { Algorithm = Rebuild(algorithm.Algorithm, depth + 1) },
        Expr.Call call => call with { Function = Rebuild(call.Function, depth + 1) },
        Expr.Param param => param with { },
        Expr.Num number => number with { },
        Expr.StringLiteral text => text with { },
        Expr.InterpolatedString interpolated => interpolated with { },
        Expr.BoolLiteral flag => flag with { },
        Expr.EmptySequence empty => empty with { },
        Expr.ListLiteral list => list with { },
        Expr.Resolve resolve => resolve with { },
        Expr.Capture capture => capture with { },
        Expr.NativeCall native => native with { },
    };

    private static Algorithm Rebuild(Algorithm algorithm, int depth) => algorithm switch
    {
        Algorithm.User user => user with { Parent = Rebuild(user.Parent) },
        Algorithm.Conditional family => family with { Parent = Rebuild(family.Parent) },
        Algorithm.Alias alias => alias with { Parent = Rebuild(alias.Parent), Target = Rebuild(alias.Target, depth + 1) },
        Algorithm.Builtin builtin => builtin with { },
    };

    private static ScopeCtx? Rebuild(ScopeCtx? scope)
    {
        if (scope is null)
            return null;
        var chain = new Stack<ScopeCtx>();
        for (var level = scope; level is not null; level = level.Parent)
            chain.Push(level);
        ScopeCtx? rebuilt = null;
        while (chain.TryPop(out var level))
            rebuilt = level with { Parent = rebuilt };
        return rebuilt;
    }

    // ── B. Shallow compatibility differential ────────────────────────────────

    [Theory]
    [InlineData(20261111)]
    [InlineData(7)]
    [InlineData(424242)]
    public void GeneratedTreesAndSharedDags_EqualAndHashLikeTheGeneratedContract(int seed)
    {
        var generator = new RecordGenerator(seed);
        for (var index = 0; index < 60; index++)
            generator.Expr(6);
        for (var index = 0; index < 12; index++)
        {
            generator.Algorithm(4);
            generator.Scope(5);
        }

        // The pool: every generated node, plus an independently allocated copy of some of them.
        var pool = new List<object>();
        pool.AddRange(generator.Exprs);
        pool.AddRange(generator.Exprs.Where(static (_, index) => index % 3 == 0).Select(static expr => Rebuild(expr)));
        pool.AddRange(generator.Algorithms);
        pool.AddRange(generator.Algorithms.Select(static algorithm => Rebuild(algorithm, 0)));
        pool.AddRange(generator.Scopes);
        pool.AddRange(generator.Scopes.Select(static scope => Rebuild(scope)!));

        var equal = 0;
        var unequal = 0;
        var equalDistinctObjects = 0;
        foreach (var record in pool)
            AssertHashParity(record);
        foreach (var left in pool)
        {
            foreach (var right in pool)
            {
                if (AssertPairParity(left, right))
                {
                    equal++;
                    equalDistinctObjects += ReferenceEquals(left, right) ? 0 : 1;
                }
                else
                {
                    unequal++;
                }
            }
        }

        output.WriteLine($"seed {seed}: {pool.Count} records, {equal} equal ordered pairs ({equalDistinctObjects} between distinct objects), {unequal} unequal");
        Assert.True(pool.Count > 150, $"too few records: {pool.Count}");
        Assert.True(equalDistinctObjects > 100, $"too few equal pairs of distinct objects: {equalDistinctObjects}");
        Assert.True(unequal > 10_000, $"too few unequal pairs: {unequal}");
    }

    [Fact]
    public void EveryRecordVariant_KeepsTheGeneratedContract_FieldByField()
    {
        // One hand-built representative of every AST record kind whose equality reaches a record,
        // and of the unchanged kinds that only enter one.
        var bundle = new OutputBundle([new Expr.Num(1)]);
        IReadOnlyList<ComparisonLink> links = [new ComparisonLink(ComparisonOp.Eq, new Expr.Num(2))];
        IReadOnlyList<Expr> opens = [new Expr.Resolve("M")];
        var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        IReadOnlyList<Property> properties = [new Property("P", body)];
        var scope = new ScopeCtx(new ScopeCtx(null, opens, properties, ["a"]), [], properties, ["b"]);
        var leaf = new Expr.Resolve("x") { Span = SpanA };

        object[] representatives =
        [
            new Expr.Unary(UnaryOp.Minus, leaf) { Span = SpanB },
            new Expr.Binary(BinaryOp.Sub, leaf, new Expr.Num(4)),
            new Expr.Comparison(leaf, links),
            new Expr.Index(leaf, bundle),
            new Expr.SequenceConstruct(leaf, new Expr.EmptySequence(0)),
            new Expr.SequenceSpread(leaf) { SpreadMarkerSpan = SpanA },
            new Expr.DotCall(leaf, "member", bundle) { MemberSpan = SpanB, LexicalFallback = new Expr.Param("member") },
            new Expr.DotCall(leaf, "member"),
            new Expr.Grace(leaf, 1),
            new Expr.AlgorithmExpr(body),
            new Expr.Call(leaf, bundle),
            new Algorithm.User(scope, [new CaptureParameterPattern("x")], opens, properties, bundle) { HasExplicitParameterList = true },
            new Algorithm.Conditional(scope, opens, [new CondBranch(new Pattern.LitInt(0), body)]),
            new Algorithm.Alias(scope, opens, properties, leaf) { IsReference = false },
            scope,
            new ComparisonLink(ComparisonOp.Ne, leaf),
            new InterpolationLink(leaf, "text"),
            new Property("Q", new Algorithm.Alias(null, [], [], leaf), IsPublic: true),
            new CondBranch(new Pattern.Bind("n"), new Algorithm.Alias(null, [], [], leaf)),
        ];

        var mutations = 0;
        var transparent = 0;
        foreach (var record in representatives)
        {
            AssertHashParity(record);
            Assert.True(AssertPairParity(record, record));
            var copy = Clone(record);
            Assert.True(AssertPairParity(record, copy), $"a `with` copy of {record.GetType().Name} equals its source");
            Assert.True(AssertPairParity(copy, record));
            AssertHashParity(copy);

            // Every instance field in turn: the only difference between the two records.
            foreach (var field in GeneratedRecordContract.Fields(record.GetType()))
            {
                if (record is ScopeCtx && field.Name is "<Owner>k__BackingField" or "<Activation>k__BackingField")
                    continue; // Runtime ownership never took part in ScopeCtx equality (pinned by its own tests).
                var mutated = Clone(record);
                field.SetValue(mutated, Mutate(field, field.GetValue(record)));
                var stillEqual = AssertPairParity(record, mutated);
                Assert.True(stillEqual == AssertPairParity(mutated, record), "symmetry");
                AssertHashParity(mutated);
                var isSlot = field.FieldType.IsGenericType && field.FieldType.GetGenericTypeDefinition() == typeof(RuntimeStateSlot<>);
                Assert.True(isSlot == stillEqual, $"{record.GetType().Name}.{field.Name}: a state slot is transparent, every other field is compared");
                mutations++;
                transparent += isSlot ? 1 : 0;
            }
        }

        output.WriteLine($"{representatives.Length} representatives, {mutations} single-field mutations ({transparent} equality-transparent slots)");
        Assert.True(mutations >= 90, $"too few field mutations: {mutations}");
        Assert.True(transparent > 15, $"too few slot mutations: {transparent}");
    }

    private static object Clone(object record)
        => record.GetType().GetMethod("<Clone>$", BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)!.Invoke(record, null)!;

    // A value of the field's type that differs from the current one. A field type this table does
    // not know fails the test: a new field of a hand-written record must be decided here.
    private static object? Mutate(FieldInfo field, object? current)
    {
        var type = field.FieldType;
        if (type.IsGenericType && type.GetGenericTypeDefinition() == typeof(RuntimeStateSlot<>))
        {
            var payloadType = type.GetGenericArguments()[0];
            var payload = Nullable.GetUnderlyingType(payloadType) is { } underlying
                ? Different(underlying, null)
                : payloadType.IsValueType ? Different(payloadType, null) : RuntimeHelpers.GetUninitializedObject(payloadType);
            return Activator.CreateInstance(type, BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic, null, [payload], null);
        }

        return Different(Nullable.GetUnderlyingType(type) ?? type, current)
            ?? throw new InvalidOperationException($"No mutation is known for field {field.DeclaringType!.Name}.{field.Name} of type {type}.");
    }

    private static object? Different(Type type, object? current)
    {
        if (type == typeof(bool)) return current is not true;
        if (type == typeof(int)) return (current as int? ?? 0) + 1;
        if (type == typeof(string)) return (current as string) + "'";
        if (type == typeof(SourceSpan)) return current is SourceSpan span && span == SpanA ? SpanB : SpanA;
        if (type.IsEnum)
        {
            var values = Enum.GetValues(type);
            return Equals(values.GetValue(0), current) ? values.GetValue(1) : values.GetValue(0);
        }

        if (type == typeof(Expr)) return new Expr.Num(987_654);
        if (type == typeof(Algorithm)) return new Algorithm.Builtin(BuiltinId.atoms);
        if (type == typeof(Pattern)) return new Pattern.LitString("mutated");
        if (type == typeof(ScopeCtx)) return new ScopeCtx(null, [], [], ["mutated"]);
        if (type == typeof(OutputBundle)) return new OutputBundle([new Expr.Num(987_654)]);
        if (type == typeof(object)) return new object();
        if (type.IsGenericType && type.GetGenericTypeDefinition() == typeof(IReadOnlyList<>))
            return Activator.CreateInstance(typeof(List<>).MakeGenericType(type.GetGenericArguments()[0]));
        return null;
    }

    [Fact]
    public void ReferenceComparedParts_StayReferenceCompared()
    {
        // Same content, different list or bundle identity: unequal, as generated equality always was.
        var first = new Expr.Num(1);
        Assert.False(new Expr.Call(first, new OutputBundle([new Expr.Num(1)])).Equals(new Expr.Call(first, new OutputBundle([new Expr.Num(1)]))));
        Assert.False(new Expr.Index(first, new OutputBundle([first])).Equals(new Expr.Index(first, new OutputBundle([first]))));
        Assert.False(new Expr.Comparison(first, new List<ComparisonLink>()).Equals(new Expr.Comparison(first, new List<ComparisonLink>())));
        Assert.False(new Expr.DotCall(first, "m", new OutputBundle([first])).Equals(new Expr.DotCall(first, "m", new OutputBundle([first]))));
        Assert.False(new Expr.DotCall(first, "m").Equals(new Expr.DotCall(first, "m", OutputBundle.Empty)));
        Assert.False(new Algorithm.Alias(null, new List<Expr>(), [], first).Equals(new Algorithm.Alias(null, new List<Expr>(), [], first)));
        Assert.False(new Algorithm.User(null, new List<ParameterPattern>(), [], [], []).Equals(new Algorithm.User(null, new List<ParameterPattern>(), [], [], [])));
        Assert.False(new ScopeCtx(null, new List<Expr>(), [], []).Equals(new ScopeCtx(null, new List<Expr>(), [], [])));

        // One shared instance: equal, with equal hashes, whatever objects surround it.
        var bundle = new OutputBundle([first]);
        var links = new List<ComparisonLink>();
        Assert.True(new Expr.Call(new Expr.Num(1), bundle).Equals(new Expr.Call(new Expr.Num(1), bundle)));
        Assert.True(new Expr.Comparison(new Expr.Num(1), links).Equals(new Expr.Comparison(new Expr.Num(1), links)));
        Assert.Equal(new Expr.Comparison(new Expr.Num(1), links).GetHashCode(), new Expr.Comparison(new Expr.Num(1), links).GetHashCode());

        // Different derived records with the same components are different records.
        Assert.False(((Expr)new Expr.Binary(BinaryOp.Add, first, first)).Equals(new Expr.SequenceConstruct(first, first)));
        Assert.False(((Expr)new Expr.Unary(UnaryOp.Minus, first)).Equals(new Expr.SequenceSpread(first)));
        Assert.False(((Expr)new Expr.Call(first, bundle)).Equals(new Expr.Index(first, bundle)));
        Assert.False(((Algorithm)new Algorithm.Alias(null, [], [], first)).Equals(new Algorithm.User(null, [], [], [], [])));

        // Null: the typed members, the object member and the operators.
        var unary = new Expr.Unary(UnaryOp.Minus, first);
        Assert.False(unary.Equals((Expr.Unary?)null));
        Assert.False(unary.Equals((Expr?)null));
        Assert.False(unary.Equals((object?)null));
        Assert.False(unary == null);
        Assert.True(unary != null);
        Assert.True((Expr.Unary?)null == (Expr.Unary?)null);
        Assert.False(new ScopeCtx(null, [], [], []).Equals(null));
        Assert.False(new Algorithm.Alias(null, [], [], first).Equals((Algorithm?)null));

        // Source metadata is compared; runtime state is not.
        Assert.False(unary.Equals(unary with { Span = SpanA }));
        Assert.True((unary with { Span = SpanA }).Equals(unary with { Span = SpanA }));
        var declaredTwice = new Algorithm.Alias(null, [], [], first);
        Assert.True(declaredTwice.Equals(new Algorithm.Alias(null, [], [], first)));
        Assert.NotSame(declaredTwice.Declaration, new Algorithm.Alias(null, [], [], first).Declaration);
        var owned = new ScopeCtx(null, [], [], []) { Owner = declaredTwice };
        Assert.True(owned.Equals(new ScopeCtx(null, [], [], [])));
        Assert.Equal(owned.GetHashCode(), new ScopeCtx(null, [], [], []).GetHashCode());
    }

    [Fact]
    public void MalformedHostRecords_KeepTheGeneratedAnswers()
    {
        // What no parser writes and a host can still construct: a null where the type promises a
        // record or a collection. Generated equality compared nulls like any other field value and
        // hashed them to 0; nothing here became an exception or a different verdict.
        var leaf = new Expr.Num(1);
        object[] malformed =
        [
            new Expr.Unary(UnaryOp.Minus, null!),
            new Expr.Unary(UnaryOp.Minus, null!),
            new Expr.Unary(UnaryOp.Minus, leaf),
            new Expr.Binary(BinaryOp.Add, null!, leaf),
            new Expr.Binary(BinaryOp.Add, leaf, null!),
            new Expr.Binary(BinaryOp.Add, null!, null!),
            new Expr.Comparison(null!, null!),
            new Expr.Comparison(leaf, null!),
            new Expr.Index(null!, null!),
            new Expr.Call(null!, null!),
            new Expr.Call(leaf, null!),
            new Expr.DotCall(null!, null!),
            new Expr.DotCall(leaf, null!, null),
            new Expr.AlgorithmExpr(null!),
            new Expr.AlgorithmExpr(null!),
            new Expr.Grace(null!, 0),
            new Expr.SequenceSpread(null!),
            new Expr.SequenceConstruct(null!, null!),
            new Algorithm.Alias(null, null!, null!, null!),
            new Algorithm.Alias(null, null!, null!, leaf),
            new Algorithm.User(null, null!, null!, null!, null!),
            new Algorithm.User(null, null!, null!, null!, null!),
            new Algorithm.Conditional(null, null!, null!),
            new ScopeCtx(null, null!, null!, null!),
            new ScopeCtx(new ScopeCtx(null, null!, null!, null!), null!, null!, null!),
        ];

        var equalDistinct = 0;
        foreach (var record in malformed)
            AssertHashParity(record);
        foreach (var left in malformed)
        {
            foreach (var right in malformed)
                equalDistinct += AssertPairParity(left, right) && !ReferenceEquals(left, right) ? 1 : 0;
        }

        // The repeated shapes above are equal pairs of distinct objects, in both directions.
        Assert.True(equalDistinct >= 6, $"too few equal malformed pairs: {equalDistinct}");
    }

    [Fact]
    public void ParserCorpus_EveryExpressionAndAlgorithm_EqualsAndHashesLikeTheGeneratedContract()
    {
        var expressions = 0;
        var algorithms = 0;
        var interior = 0;
        var rebuiltEqual = 0;
        var neighbourPairs = 0;
        var programs = 0;
        foreach (var root in ParsedCorpus())
        {
            var collected = new RecordCollector();
            collected.VisitAlgorithm(root);
            // A bounded sample of each program keeps the whole corpus within a few seconds.
            var sample = collected.Exprs.Where(static (_, index) => index % 4 == 0).Take(60).ToList();
            programs++;
            Expr? previous = null;
            foreach (var expr in sample)
            {
                expressions++;
                interior += expr is Expr.Unary or Expr.Binary or Expr.Comparison or Expr.Index or Expr.SequenceConstruct
                    or Expr.SequenceSpread or Expr.DotCall or Expr.Grace or Expr.AlgorithmExpr or Expr.Call ? 1 : 0;
                AssertHashParity(expr);
                var rebuilt = Rebuild(expr);
                rebuiltEqual += AssertPairParity(expr, rebuilt) ? 1 : 0;
                AssertPairParity(rebuilt, expr);
                AssertHashParity(rebuilt);
                if (previous is not null)
                {
                    AssertPairParity(previous, expr);
                    AssertPairParity(expr, previous);
                    neighbourPairs++;
                }

                previous = expr;
            }

            foreach (var algorithm in collected.Algorithms.Take(20))
            {
                algorithms++;
                AssertHashParity(algorithm);
                Assert.True(AssertPairParity(algorithm, Rebuild(algorithm, 0)));
            }
        }

        output.WriteLine(
            $"{programs} programs: {expressions} expressions ({interior} with record children), {rebuiltEqual} equal to their rebuilt copy, "
            + $"{neighbourPairs} neighbour pairs, {algorithms} algorithms");
        Assert.True(expressions > 5000, $"too few expressions: {expressions}");
        Assert.True(interior > 2000, $"too few expressions with record children: {interior}");
        Assert.True(rebuiltEqual == expressions, "a rebuilt copy shares every reference-compared part, so it is equal");
        Assert.True(algorithms > 1000, $"too few algorithms: {algorithms}");
    }

    private static readonly Lazy<IReadOnlyList<Algorithm.User>> Corpus = new(BuildCorpus);

    private static IReadOnlyList<Algorithm.User> ParsedCorpus() => Corpus.Value;

    // Every program of the three shared corpora, elaborated; an erroneous program contributes its
    // recovered tree, which the parser built as well (the subject is every record the parser
    // produces, and no evaluator outcome is read from these trees).
    private static IReadOnlyList<Algorithm.User> BuildCorpus()
    {
        var sources = new List<string>();
        foreach (var specCase in LanguageSpecCorpus.AllCases())
        {
            sources.Add(specCase.Source);
            sources.AddRange(specCase.Probes.Select(static probe => probe.Probe));
        }

        sources.AddRange(SemanticExplorerCorpus.AllCases().Select(static explorerCase => explorerCase.Source));
        sources.AddRange(TutorialCorpus.Examples.Select(static example => example.Source));
        return sources.Distinct(StringComparer.Ordinal)
            .Select(static source => SourceProvenance.ParseAllowingDiagnostics(source).Root)
            .ToList();
    }

    private sealed class RecordCollector : AstWalker
    {
        public List<Expr> Exprs { get; } = [];

        public List<Algorithm> Algorithms { get; } = [];

        public override void VisitExpr(Expr expr)
        {
            Exprs.Add(expr);
            base.VisitExpr(expr);
        }

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            Algorithms.Add(algorithm);
            base.VisitAlgorithm(algorithm);
        }
    }

    // ── Inventory pins ───────────────────────────────────────────────────────

    private static IEnumerable<Type> AstRecordTypes()
        => typeof(Expr).Assembly.GetTypes().Where(GeneratedRecordContract.IsModeled);

    private static bool HasHandWrittenEquality(Type record)
    {
        var typed = record.GetMethod("Equals", BindingFlags.Instance | BindingFlags.Public | BindingFlags.DeclaredOnly, [record]);
        return typed is not null && !typed.IsDefined(typeof(CompilerGeneratedAttribute), inherit: false);
    }

    [Fact]
    public void HandWrittenRecordEquality_IsExactlyTheRecursiveRecords()
    {
        // The records listed here are the whole hand-written surface the differential above must
        // cover; adding one without extending that coverage fails here.
        string[] expected =
        [
            "KatLang.Algorithm+Alias", "KatLang.Algorithm+Conditional", "KatLang.Algorithm+User",
            "KatLang.Expr+AlgorithmExpr", "KatLang.Expr+Binary", "KatLang.Expr+Call", "KatLang.Expr+Comparison",
            "KatLang.Expr+DotCall", "KatLang.Expr+Grace", "KatLang.Expr+Index", "KatLang.Expr+SequenceConstruct",
            "KatLang.Expr+SequenceSpread", "KatLang.Expr+Unary", "KatLang.ScopeCtx",
        ];
        var actual = AstRecordTypes().Where(HasHandWrittenEquality).Select(static type => type.FullName!)
            .OrderBy(static name => name, StringComparer.Ordinal).ToArray();
        Assert.Equal(expected, actual);

        // Each of them also writes GetHashCode itself.
        foreach (var type in AstRecordTypes().Where(HasHandWrittenEquality))
        {
            var hash = type.GetMethod("GetHashCode", BindingFlags.Instance | BindingFlags.Public | BindingFlags.DeclaredOnly, Type.EmptyTypes);
            Assert.True(hash is not null && !hash.IsDefined(typeof(CompilerGeneratedAttribute), inherit: false), type.FullName);
        }
    }

    [Fact]
    public void NoAstRecordOnARecordValuedCycle_KeepsGeneratedEquality()
    {
        // Generated equality recurses once per record-valued field it follows. That is unbounded
        // exactly for a record that can reach its own kind again through such fields; every other
        // record adds a bounded number of frames before it enters one that is iterative. Equality
        // transparent slots are never followed, and neither is a list or a bundle.
        var records = AstRecordTypes().ToArray();
        IEnumerable<Type> Followed(Type record)
        {
            if (record == typeof(ScopeCtx))
                return [typeof(ScopeCtx)]; // Its hand-written contract follows Parent only.
            return GeneratedRecordContract.Fields(record)
                .Select(static field => field.FieldType)
                .Where(GeneratedRecordContract.IsModeled)
                .SelectMany(fieldType => records.Where(candidate => fieldType.IsAssignableFrom(candidate) && !candidate.IsAbstract))
                .Distinct();
        }

        var onCycle = new List<string>();
        foreach (var record in records.Where(static record => record.IsSealed))
        {
            var seen = new HashSet<Type>();
            var pending = new Stack<Type>(Followed(record));
            while (pending.TryPop(out var reached))
            {
                if (reached == record)
                {
                    onCycle.Add(record.FullName!);
                    break;
                }

                if (seen.Add(reached))
                {
                    foreach (var next in Followed(reached))
                        pending.Push(next);
                }
            }
        }

        onCycle.Sort(StringComparer.Ordinal);
        output.WriteLine("records on a record-valued cycle: " + string.Join(", ", onCycle));
        // User and Conditional reach only the ScopeCtx chain; they are hand-written so that one
        // operation's memo also covers the scopes many algorithms share.
        string[] expected =
        [
            "KatLang.Algorithm+Alias", "KatLang.Expr+AlgorithmExpr", "KatLang.Expr+Binary", "KatLang.Expr+Call",
            "KatLang.Expr+Comparison", "KatLang.Expr+DotCall", "KatLang.Expr+Grace", "KatLang.Expr+Index",
            "KatLang.Expr+SequenceConstruct", "KatLang.Expr+SequenceSpread", "KatLang.Expr+Unary", "KatLang.ScopeCtx",
        ];
        Assert.Equal(expected, onCycle);
        Assert.All(onCycle, name => Assert.True(HasHandWrittenEquality(typeof(Expr).Assembly.GetType(name)!), name));
    }

    // ── A. Depth ─────────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(DeepRecordGraphs.ShapeData), MemberType = typeof(DeepRecordGraphs))]
    public void TwoHundredThousandLevels_EqualAndHashWithoutRecursion(string shape)
        => DeepRecordGraphs.AssertExpressionShape(shape, DeepRecordGraphs.Depth);

    [Fact]
    public void TwoHundredThousandLevels_OfSharedDiamonds_EqualAndHash()
        => DeepRecordGraphs.AssertSharedDiamonds(DeepRecordGraphs.Depth);

    [Fact]
    public void TwoHundredThousandScopeLevels_EqualAndHash_AloneAndUnderEveryAlgorithmKind()
        => DeepRecordGraphs.AssertScopeChains(DeepRecordGraphs.Depth);

    [Fact]
    public void RecordsThatOnlyEnterADeepExpression_AreStackSafeWithIt()
        => DeepRecordGraphs.AssertEntryRecords(DeepRecordGraphs.Depth);

    [Fact]
    public void PatternsParameterPatternsAndValues_NeverRecursed_TheirItemListsCompareByReference()
        => DeepRecordGraphs.AssertReferenceComparedHierarchies(DeepRecordGraphs.Depth);

    // ── C. Work on shared DAGs ───────────────────────────────────────────────

    /// <summary>
    /// A host-defined links list that counts how often record equality and hashing ask it — once
    /// per comparison or hash of the record that holds it — and fails the test instead of hanging
    /// when a walk expands shared paths.
    /// </summary>
    private sealed class CountingLinks(WorkBudget budget) : List<ComparisonLink>
    {
        public int EqualsCalls;
        public int HashCalls;

        public override bool Equals(object? obj)
        {
            EqualsCalls++;
            budget.Charge();
            return ReferenceEquals(this, obj);
        }

        public override int GetHashCode()
        {
            HashCalls++;
            budget.Charge();
            return RuntimeHelpers.GetHashCode(this);
        }
    }

    private sealed class WorkBudget(long limit)
    {
        public long Spent;

        public void Charge()
        {
            if (++Spent > limit)
                throw new InvalidOperationException("Native record equality expanded shared paths.");
        }
    }

    // level(i) = Binary(node(i), node(i)) over node(i) = Comparison(level(i - 1), counter(i)):
    // 2 * depth + 1 distinct records, 2^depth root-to-leaf paths, one counter per shared node.
    private static Expr CountingDiamond(IReadOnlyList<CountingLinks> counters, Expr leaf)
    {
        var level = leaf;
        foreach (var counter in counters)
        {
            var node = new Expr.Comparison(level, counter);
            level = new Expr.Binary(BinaryOp.Add, node, node);
        }

        return level;
    }

    [Theory]
    [InlineData(10)]
    [InlineData(20)]
    [InlineData(40)]
    [InlineData(80)]
    [InlineData(5000)]
    public void Equality_ComparesEachDistinctPairOfASharedDagOnce(int depth)
    {
        var budget = new WorkBudget(8L * depth);
        var counters = Enumerable.Range(0, depth).Select(_ => new CountingLinks(budget)).ToList();
        var left = CountingDiamond(counters, new Expr.Num(1));
        var right = CountingDiamond(counters, new Expr.Num(1));
        var different = CountingDiamond(counters, new Expr.Num(2));

        Assert.True(left.Equals(right));
        output.WriteLine($"depth {depth}: {2 * depth + 1} distinct records per side, field comparisons = {budget.Spent}");
        // One comparison of each shared node pair, exactly: the second edge finds the pair proven.
        Assert.Equal(depth, budget.Spent);
        Assert.All(counters, static counter => Assert.Equal(1, counter.EqualsCalls));

        // Nothing was attached to the records: asking again does the same work again.
        Assert.True(left == right);
        Assert.Equal(2L * depth, budget.Spent);

        // A difference at the deepest leaf is found before any shared node's own fields are compared.
        Assert.False(left.Equals(different));
        Assert.Equal(2L * depth, budget.Spent);
        Assert.True(left.Equals(left));
        Assert.Equal(2L * depth, budget.Spent);
    }

    [Theory]
    [InlineData(10)]
    [InlineData(20)]
    [InlineData(40)]
    [InlineData(80)]
    [InlineData(5000)]
    public void Hashing_HashesEachDistinctNodeOfASharedDagOnce(int depth)
    {
        var budget = new WorkBudget(8L * depth);
        var counters = Enumerable.Range(0, depth).Select(_ => new CountingLinks(budget)).ToList();
        var dag = CountingDiamond(counters, new Expr.Num(1));
        var twin = CountingDiamond(counters, new Expr.Num(1));

        var hash = dag.GetHashCode();
        output.WriteLine($"depth {depth}: {2 * depth + 1} distinct records, field hashes = {budget.Spent}");
        Assert.Equal(depth, budget.Spent);
        Assert.All(counters, static counter => Assert.Equal(1, counter.HashCalls));

        // Call-local: the next operation hashes every node again, with the same result.
        Assert.Equal(hash, dag.GetHashCode());
        Assert.Equal(2L * depth, budget.Spent);
        Assert.Equal(hash, twin.GetHashCode());
        Assert.Equal(3L * depth, budget.Spent);
    }

    [Theory]
    [InlineData(4)]
    [InlineData(8)]
    [InlineData(12)]
    public void ASharedDag_EqualsTheTreeItDenotes_AtTheCostOfTheirDistinctPairs(int depth)
    {
        // The same logical tree, once as a diamond DAG and once fully expanded: the generated
        // contract calls them equal, and every (shared node, tree node) pair is a distinct pair.
        var budget = new WorkBudget(long.MaxValue);
        var counters = Enumerable.Range(0, depth).Select(_ => new CountingLinks(budget)).ToList();
        var dag = CountingDiamond(counters, new Expr.Num(1));
        var tree = ExpandedTree(counters, depth);

        Assert.True(dag.Equals(tree));
        Assert.True(tree.Equals(dag));
        Assert.Equal(dag.GetHashCode(), tree.GetHashCode());
        // The tree holds 2^(depth - i) copies of the shared node at height i: one comparison per
        // distinct (shared node, copy) pair, in each of the two directions asked above.
        var treeNodes = (2L << depth) - 2;
        for (var height = 0; height < depth; height++)
            Assert.Equal(2 * (1 << (depth - height)), counters[height].EqualsCalls);
        output.WriteLine($"depth {depth}: {treeNodes} comparison nodes in the tree, field comparisons = {counters.Sum(static counter => (long)counter.EqualsCalls)}");

        static Expr ExpandedTree(IReadOnlyList<CountingLinks> counters, int height)
            => height == 0
                ? new Expr.Num(1)
                : new Expr.Binary(
                    BinaryOp.Add,
                    new Expr.Comparison(ExpandedTree(counters, height - 1), counters[height - 1]),
                    new Expr.Comparison(ExpandedTree(counters, height - 1), counters[height - 1]));
    }

    [Theory]
    [InlineData(50, 2000)]
    [InlineData(400, 2000)]
    public void ManyAlgorithmsOverOneDeepScopeChain_WalkTheChainOncePerOperation(int algorithms, int chain)
    {
        // The scope chain is shared by every algorithm of the expression: its levels are compared
        // and hashed once per operation, not once per algorithm.
        var budget = new WorkBudget(8L * (algorithms + chain));
        var levels = Enumerable.Range(0, chain).Select(_ => new CountingNames(budget)).ToList();
        ScopeCtx Chain()
        {
            ScopeCtx? scope = null;
            foreach (var names in levels)
                scope = new ScopeCtx(scope, [], [], names);
            return scope!;
        }

        Expr Program(ScopeCtx scope)
        {
            Expr program = new Expr.Num(0);
            for (var index = 0; index < algorithms; index++)
                program = new Expr.Binary(BinaryOp.Add, program, new Expr.AlgorithmExpr(new Algorithm.Conditional(scope, [], [])));
            return program;
        }

        var left = Program(Chain());
        var right = Program(Chain());
        Assert.True(left.Equals(right));
        Assert.Equal(chain, budget.Spent);
        Assert.Equal(left.GetHashCode(), right.GetHashCode());
        Assert.Equal(3L * chain, budget.Spent);
        output.WriteLine($"{algorithms} algorithms over {chain} scope levels: scope field reads = {chain} per operation");
    }

    private sealed class CountingNames(WorkBudget budget) : List<string>
    {
        public override bool Equals(object? obj)
        {
            budget.Charge();
            return ReferenceEquals(this, obj);
        }

        public override int GetHashCode()
        {
            budget.Charge();
            return RuntimeHelpers.GetHashCode(this);
        }
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(128)]
    public void SharedLeafRecords_AreComparedAndHashedOncePerOperation(int depth)
    {
        // NativeCall's argument-name list is a shallow, reference-compared field. A shared leaf
        // must be memoized just like a recursive node, including a leaf read before the first
        // recursive descent. Depth zero also pins reuse without allocating a traversal table.
        var budget = new WorkBudget(8);
        var names = new CountingNames(budget);
        Expr Graph()
        {
            var leaf = new Expr.NativeCall("f", names);
            Expr graph = new Expr.Binary(BinaryOp.Add, leaf, leaf);
            for (var level = 0; level < depth; level++)
                graph = new Expr.Binary(BinaryOp.Add, leaf, graph);
            return graph;
        }

        var left = Graph();
        var right = Graph();
        Assert.True(left.Equals(right));
        Assert.Equal(1, budget.Spent);
        var hash = left.GetHashCode();
        Assert.Equal(2, budget.Spent);
        Assert.Equal(hash, right.GetHashCode());
        Assert.Equal(3, budget.Spent);
        Assert.True(left.Equals(right));
        Assert.Equal(4, budget.Spent);
    }

    // ── D. Collections ───────────────────────────────────────────────────────

    [Fact]
    public void HashSetsAndDictionaries_TreatEqualDeepKeysAsOneKey()
    {
        const int depth = 20_000;
        Expr Deep(int leaf)
        {
            Expr expr = new Expr.Num(leaf);
            for (var level = 0; level < depth; level++)
                expr = level % 2 == 0 ? new Expr.Unary(UnaryOp.Minus, expr) : new Expr.Binary(BinaryOp.Add, expr, expr);
            return expr;
        }

        var key = Deep(1);
        var equalKey = Deep(1);
        var otherKey = Deep(2);

        // Membership is asserted as a Boolean throughout: a failed collection assertion would
        // print its items, and a deep record's generated text is recursive.
        var set = new HashSet<Expr> { key };
        Assert.True(set.Contains(equalKey), "an equal key is found");
        Assert.False(set.Add(equalKey));
        Assert.True(set.Add(otherKey));
        Assert.Equal(2, set.Count);
        Assert.True(set.Remove(Deep(2)));
        Assert.True(set.Count == 1, "one key is left");

        var map = new Dictionary<Expr, string> { [key] = "one" };
        Assert.Equal("one", map[equalKey]);
        Assert.False(map.ContainsKey(otherKey));
        map[equalKey] = "replaced";
        Assert.True(map.Count == 1, "an equal key replaces, never adds");
        Assert.Equal("replaced", map[key]);

        // The other record families that own a recursive field, as keys.
        var (namesX, namesY) = (DeepRecordGraphs.NamesX, DeepRecordGraphs.NamesY);
        var scopes = new HashSet<ScopeCtx> { DeepRecordGraphs.Scope(depth, namesX) };
        Assert.True(scopes.Contains(DeepRecordGraphs.Scope(depth, namesX)), "an equal scope is found");
        Assert.False(scopes.Contains(DeepRecordGraphs.Scope(depth, namesY)), "an unequal scope is not");
        var algorithms = new Dictionary<Algorithm, int> { [new Algorithm.Alias(DeepRecordGraphs.Scope(depth, namesX), [], [], key)] = 7 };
        Assert.Equal(7, algorithms[new Algorithm.Alias(DeepRecordGraphs.Scope(depth, namesX), [], [], equalKey)]);
        Assert.False(algorithms.ContainsKey(new Algorithm.Alias(DeepRecordGraphs.Scope(depth, namesX), [], [], otherKey)));
        Assert.False(algorithms.ContainsKey(new Algorithm.Alias(DeepRecordGraphs.Scope(depth, namesY), [], [], equalKey)));

        // Records that hold one: a tuple key and a link.
        var pairs = new HashSet<(Expr, int)> { (key, 1) };
        Assert.True(pairs.Contains((equalKey, 1)), "a tuple over an equal key is found");
        Assert.False(pairs.Contains((otherKey, 1)), "a tuple over an unequal key is not");
        Assert.True(new HashSet<ComparisonLink> { new(ComparisonOp.Lt, key) }.Contains(new ComparisonLink(ComparisonOp.Lt, equalKey)), "a link over an equal key is found");

        // Repeated hashing is stable, and an equal key hashes alike.
        Assert.Equal(key.GetHashCode(), key.GetHashCode());
        Assert.Equal(key.GetHashCode(), equalKey.GetHashCode());
    }

    /// <summary>A host list with CONTENT equality: the one way a caller-owned collection changes a record's equality.</summary>
    private sealed class ContentComparedLinks : List<ComparisonLink>
    {
        public int Reads;

        public override bool Equals(object? obj)
        {
            Reads++;
            return obj is ContentComparedLinks other && this.SequenceEqual(other);
        }

        public override int GetHashCode()
        {
            Reads++;
            var hash = new HashCode();
            foreach (var link in this)
                hash.Add(link);
            return hash.ToHashCode();
        }
    }

    [Fact]
    public void CallerOwnedCollections_AreReadAfreshByEveryOperation()
    {
        // No hash or verdict is cached on a record: a host that edits a collection it owns sees the
        // edit in the next operation, through any number of enclosing records.
        var leftLinks = new ContentComparedLinks();
        var rightLinks = new ContentComparedLinks();
        // (The enclosing records hold the comparison once each. A record that holds one child in
        // two fields folds that child's hash in twice, and the synthesized multiplier plus one is
        // even: about 32 such levels cancel the child out of the hash altogether. That is the
        // generated formula, kept as it is; it costs collisions, never equality.)
        Expr Wrap(Expr inner)
        {
            for (var level = 0; level < 64; level++)
                inner = new Expr.Unary(UnaryOp.Minus, new Expr.Binary(BinaryOp.Add, inner, new Expr.Num(level)));
            return inner;
        }

        var left = Wrap(new Expr.Comparison(new Expr.Num(1), leftLinks));
        var right = Wrap(new Expr.Comparison(new Expr.Num(1), rightLinks));
        Assert.True(left.Equals(right));
        var emptyHash = left.GetHashCode();
        Assert.Equal(emptyHash, right.GetHashCode());

        leftLinks.Add(new ComparisonLink(ComparisonOp.Lt, new Expr.Num(2)));
        Assert.False(left.Equals(right));
        Assert.NotEqual(emptyHash, left.GetHashCode());
        Assert.Equal(GeneratedRecordContract.Hash(typeof(Expr), left), left.GetHashCode());
        var set = new HashSet<Expr> { left };
        Assert.False(set.Contains(right), "the edited record is another key");

        rightLinks.Add(new ComparisonLink(ComparisonOp.Lt, new Expr.Num(2)));
        Assert.True(left.Equals(right));
        Assert.Equal(left.GetHashCode(), right.GetHashCode());
        Assert.True(set.Contains(right), "equal again after the same edit");

        var reads = leftLinks.Reads;
        _ = left.GetHashCode();
        _ = left.GetHashCode();
        Assert.Equal(reads + 2, leftLinks.Reads);
    }

    // ── Reference cycles ─────────────────────────────────────────────────────

    [Fact]
    public void AForgedRecordCycle_IsRefused_NeverWalkedForever()
    {
        // No public construction makes a record reach itself through a record-valued field: such a
        // field is set from an existing record. (Host cycles run through caller-owned lists, which
        // record equality compares by reference and never enters.) Only reflection can forge one;
        // it used to overflow the stack, and is now refused.
        Expr.Unary Forged(int length, int leaf)
        {
            var bottom = new Expr.Unary(UnaryOp.Minus, new Expr.Num(leaf));
            Expr top = bottom;
            for (var index = 1; index < length; index++)
                top = new Expr.Unary(UnaryOp.Minus, top);
            typeof(Expr.Unary).GetField("<Operand>k__BackingField", BindingFlags.Instance | BindingFlags.NonPublic)!.SetValue(bottom, top);
            return (Expr.Unary)top;
        }

        var cycle = Forged(5, 1);
        var hashFailure = Assert.Throws<InvalidOperationException>(() => cycle.GetHashCode());
        Assert.Contains("cycle", hashFailure.Message, StringComparison.OrdinalIgnoreCase);
        var equalsFailure = Assert.Throws<InvalidOperationException>(() => cycle.Equals(Forged(5, 1)));
        Assert.Contains("cycle", equalsFailure.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Throws<InvalidOperationException>(() => cycle.Equals(Forged(3, 1)));
        // A record that is its own child, and a cycle met below an acyclic prefix.
        var selfLoop = Forged(1, 1);
        Assert.Throws<InvalidOperationException>(() => selfLoop.GetHashCode());
        Assert.Throws<InvalidOperationException>(() => selfLoop.Equals(Forged(1, 1)));
        Assert.Throws<InvalidOperationException>(() => new Expr.Binary(BinaryOp.Add, new Expr.Num(1), cycle).GetHashCode());
        Assert.Throws<InvalidOperationException>(() => new Expr.Grace(cycle, 1).Equals(new Expr.Grace(Forged(5, 1), 1)));
        Assert.Throws<InvalidOperationException>(() => new HashSet<Expr> { cycle });
        Assert.True(cycle.Equals(cycle));

        // A cycle through a caller-owned list is no cycle of the record graph: it stays shallow.
        var links = new List<ComparisonLink>();
        var comparison = new Expr.Comparison(new Expr.Num(1), links);
        links.Add(new ComparisonLink(ComparisonOp.Eq, comparison));
        Assert.True(comparison.Equals(new Expr.Comparison(new Expr.Num(1), links)));
        Assert.Equal(comparison.GetHashCode(), new Expr.Comparison(new Expr.Num(1), links).GetHashCode());
    }

    // ── Ordinary workload ────────────────────────────────────────────────────

    [Fact]
    public void SmallExpressions_AllocateNothingOrLittle()
    {
        // Coarse bounds only (a strict zero would need a GC-isolated child): a record whose record
        // children are leaves is compared and hashed without any traversal state; a small tree
        // allocates an explicit stack and a memo per operation (about 5 KB for one comparison plus
        // one hash of the 19 nested records below, measured November 2026).
        const int rounds = 2000;
        var bundle = new OutputBundle([new Expr.Num(1)]);
        Expr Flat() => new Expr.Binary(BinaryOp.Add, new Expr.Resolve("a"), new Expr.Num(2));
        Expr Small()
        {
            Expr expr = new Expr.Call(new Expr.Resolve("F"), bundle);
            for (var level = 0; level < 6; level++)
                expr = new Expr.Binary(BinaryOp.Mul, new Expr.Unary(UnaryOp.Minus, expr), new Expr.DotCall(new Expr.Resolve("r"), "m"));
            return expr;
        }

        var (flatLeft, flatRight, smallLeft, smallRight) = (Flat(), Flat(), Small(), Small());
        long Measure(Expr left, Expr right)
        {
            var sink = 0;
            for (var warm = 0; warm < 200; warm++)
                sink += left.Equals(right) ? left.GetHashCode() : 0;
            var before = GC.GetAllocatedBytesForCurrentThread();
            for (var round = 0; round < rounds; round++)
                sink += left.Equals(right) ? left.GetHashCode() : 0;
            var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
            GC.KeepAlive(sink);
            return allocated;
        }

        var flat = Measure(flatLeft, flatRight);
        var small = Measure(smallLeft, smallRight);
        output.WriteLine($"equality + hash, {rounds} rounds: flat {flat} bytes ({flat / (double)rounds:0.0} per round), 19-record tree {small} bytes ({small / (double)rounds:0.0} per round)");
        Assert.True(flat < 64 * 1024, $"a record over leaf children allocated {flat} bytes in {rounds} rounds");
        Assert.True(small < rounds * 8192L, $"a small tree allocated {small} bytes in {rounds} rounds");
    }
}

/// <summary>
/// The deep host-built record graphs of <see cref="NativeRecordEqualityTests"/>, shared with the
/// child-process probe in <see cref="AstStructuralDepthProcessTests"/>. Assertion messages are
/// constants: a deep record's generated text is itself recursive and is not this subject.
/// </summary>
internal static class DeepRecordGraphs
{
    internal const int Depth = 200_000;

    internal static readonly string[] Shapes =
    [
        "unary", "binaryLeft", "binaryRight", "sequenceLeft", "sequenceRight", "spread", "grace", "call", "index",
        "dotTarget", "dotFallback", "comparison", "alias", "mixed",
    ];

    public static TheoryData<string> ShapeData()
    {
        var data = new TheoryData<string>();
        foreach (var shape in Shapes)
            data.Add(shape);
        return data;
    }

    // The reference-compared parts every graph of one test shares, so that independently built
    // graphs can be equal.
    private static readonly OutputBundle Arguments = new([new Expr.Num(7)]);
    private static readonly IReadOnlyList<ComparisonLink> Links = [new ComparisonLink(ComparisonOp.Lt, new Expr.Num(7))];
    private static readonly IReadOnlyList<Expr> NoOpens = [];
    private static readonly IReadOnlyList<Property> NoProperties = [];
    private static readonly IReadOnlyList<ParameterPattern> NoPatterns = [];

    /// <summary>Root parameter lists: a list is compared by reference, so equal scopes share one.</summary>
    internal static readonly IReadOnlyList<string> NamesX = ["x"];
    internal static readonly IReadOnlyList<string> NamesY = ["y"];

    private static Expr Wrap(string shape, int level, Expr inner) => shape switch
    {
        "unary" => new Expr.Unary(UnaryOp.Minus, inner),
        "binaryLeft" => new Expr.Binary(BinaryOp.Add, inner, new Expr.Num(2)),
        "binaryRight" => new Expr.Binary(BinaryOp.Add, new Expr.Num(2), inner),
        "sequenceLeft" => new Expr.SequenceConstruct(inner, new Expr.Num(2)),
        "sequenceRight" => new Expr.SequenceConstruct(new Expr.Num(2), inner),
        "spread" => new Expr.SequenceSpread(inner),
        "grace" => new Expr.Grace(inner, 1),
        "call" => new Expr.Call(inner, Arguments),
        "index" => new Expr.Index(inner, Arguments),
        "dotTarget" => new Expr.DotCall(inner, "member", Arguments),
        "dotFallback" => new Expr.DotCall(new Expr.Resolve("receiver"), "member") { LexicalFallback = inner },
        "comparison" => new Expr.Comparison(inner, Links),
        "alias" => new Expr.AlgorithmExpr(new Algorithm.Alias(null, NoOpens, NoProperties, new Expr.DotCall(inner, "member"))),
        "mixed" => Wrap(Shapes[level % (Shapes.Length - 1)], level, inner),
        _ => throw new ArgumentOutOfRangeException(nameof(shape), shape, null),
    };

    internal static Expr Chain(string shape, int depth, Expr leaf, int firstLevel = 0)
    {
        var expr = leaf;
        for (var level = firstLevel; level < firstLevel + depth; level++)
            expr = Wrap(shape, level, expr);
        return expr;
    }

    internal static ScopeCtx Scope(int depth, IReadOnlyList<string> rootParameters)
    {
        var scope = new ScopeCtx(null, NoOpens, NoProperties, rootParameters);
        for (var level = 1; level < depth; level++)
            scope = new ScopeCtx(scope, NoOpens, NoProperties, []);
        return scope;
    }

    /// <summary>Every native route, for an equal pair and for a pair that differs at the deepest leaf.</summary>
    internal static void AssertExpressionShape(string shape, int depth)
    {
        var left = Chain(shape, depth, new Expr.Num(1));
        var equal = Chain(shape, depth, new Expr.Num(1));
        var different = Chain(shape, depth, new Expr.Num(2));
        AssertEverything(left, equal, different);

        // With a shared subtree: the two graphs are distinct above one shared deep half.
        var shared = Chain(shape, depth / 2, new Expr.Num(1));
        var overShared = Chain(shape, depth / 2, shared, firstLevel: depth / 2);
        Assert.True(overShared.Equals(Chain(shape, depth / 2, shared, firstLevel: depth / 2)), "equal above a shared subtree");
        Assert.True(overShared.Equals(left), "a graph over a shared subtree equals the unshared graph it denotes");
        Assert.True(overShared.GetHashCode() == left.GetHashCode(), "and hashes alike");
        Assert.False(overShared.Equals(different), "unequal below a shared subtree");
    }

    private static void AssertEverything(Expr left, Expr equal, Expr different)
    {
        Assert.True(left.Equals(equal), "Equals(Expr), equal");
        Assert.True(equal.Equals(left), "Equals(Expr), symmetric");
        Assert.True(left.Equals((object)equal), "Equals(object), equal");
        Assert.True(left == equal, "==, equal");
        Assert.False(left != equal, "!=, equal");
        Assert.True(TypedEquals(left, equal), "Equals(T) and the typed operators, equal");
        Assert.True(EqualityComparer<Expr>.Default.Equals(left, equal), "default comparer, equal");

        Assert.False(left.Equals(different), "Equals(Expr), deepest leaf differs");
        Assert.False(different.Equals(left), "Equals(Expr), symmetric difference");
        Assert.False(left.Equals((object)different), "Equals(object), deepest leaf differs");
        Assert.False(left == different, "==, deepest leaf differs");
        Assert.True(left != different, "!=, deepest leaf differs");
        Assert.False(TypedEquals(left, different), "Equals(T) and the typed operators, deepest leaf differs");
        Assert.False(EqualityComparer<Expr>.Default.Equals(left, different), "default comparer, deepest leaf differs");

        var hash = left.GetHashCode();
        Assert.True(hash == left.GetHashCode(), "repeated hash");
        Assert.True(hash == equal.GetHashCode(), "equal records hash alike");
        Assert.True(hash == EqualityComparer<Expr>.Default.GetHashCode(equal), "default comparer hash");
        _ = different.GetHashCode();

        var set = new HashSet<Expr> { left };
        Assert.True(set.Contains(equal), "HashSet finds an equal key");
        Assert.False(set.Add(equal), "HashSet keeps one of two equal keys");
        Assert.True(set.Add(different), "HashSet keeps an unequal key apart");
        var map = new Dictionary<Expr, int> { [left] = 1 };
        Assert.True(map.TryGetValue(equal, out var value) && value == 1, "Dictionary lookup through an equal key");
        Assert.False(map.ContainsKey(different), "Dictionary misses an unequal key");
    }

    // The strongly typed Equals and operators of the concrete record (the route a host holding
    // the concrete type takes).
    private static bool TypedEquals(Expr left, Expr right) => (left, right) switch
    {
        (Expr.Unary a, Expr.Unary b) => Agree(a.Equals(b), a == b, a != b),
        (Expr.Binary a, Expr.Binary b) => Agree(a.Equals(b), a == b, a != b),
        (Expr.SequenceConstruct a, Expr.SequenceConstruct b) => Agree(a.Equals(b), a == b, a != b),
        (Expr.SequenceSpread a, Expr.SequenceSpread b) => Agree(a.Equals(b), a == b, a != b),
        (Expr.Grace a, Expr.Grace b) => Agree(a.Equals(b), a == b, a != b),
        (Expr.Call a, Expr.Call b) => Agree(a.Equals(b), a == b, a != b),
        (Expr.Index a, Expr.Index b) => Agree(a.Equals(b), a == b, a != b),
        (Expr.DotCall a, Expr.DotCall b) => Agree(a.Equals(b), a == b, a != b),
        (Expr.Comparison a, Expr.Comparison b) => Agree(a.Equals(b), a == b, a != b),
        (Expr.AlgorithmExpr a, Expr.AlgorithmExpr b) => Agree(a.Equals(b), a == b, a != b),
        _ => throw new InvalidOperationException("The deep graphs are built from records with record children."),
    };

    private static bool Agree(bool equals, bool same, bool different)
    {
        Assert.True(equals == same && equals != different, "Equals(T), == and != agree");
        return equals;
    }

    /// <summary>A diamond at every level: 2^depth root-to-leaf paths over depth + 1 distinct records.</summary>
    internal static void AssertSharedDiamonds(int depth)
    {
        static Expr Diamonds(int depth, Expr leaf)
        {
            var expr = leaf;
            for (var level = 0; level < depth; level++)
                expr = level % 2 == 0 ? new Expr.Binary(BinaryOp.Add, expr, expr) : new Expr.SequenceConstruct(expr, expr);
            return expr;
        }

        AssertEverything(Diamonds(depth, new Expr.Num(1)), Diamonds(depth, new Expr.Num(1)), Diamonds(depth, new Expr.Num(2)));
    }

    internal static void AssertScopeChains(int depth)
    {
        var scope = Scope(depth, NamesX);
        var equal = Scope(depth, NamesX);
        var different = Scope(depth, NamesY); // Differs at the outermost ancestor only.

        Assert.True(scope.Equals(equal), "ScopeCtx.Equals, equal");
        Assert.True(scope.Equals((object)equal), "ScopeCtx.Equals(object), equal");
        Assert.True(scope == equal, "ScopeCtx ==");
        Assert.False(scope != equal, "ScopeCtx !=");
        Assert.False(scope.Equals(different), "ScopeCtx.Equals, outermost ancestor differs");
        Assert.True(scope != different, "ScopeCtx !=, outermost ancestor differs");
        Assert.True(scope.GetHashCode() == equal.GetHashCode(), "equal scopes hash alike");
        Assert.True(new HashSet<ScopeCtx> { scope }.Contains(equal), "HashSet finds an equal scope");

        // Every algorithm kind that carries a parent scope.
        (Algorithm Left, Algorithm Equal, Algorithm Different)[] algorithms =
        [
            (new Algorithm.User(scope, NoPatterns, NoOpens, NoProperties, Arguments),
                new Algorithm.User(equal, NoPatterns, NoOpens, NoProperties, Arguments),
                new Algorithm.User(different, NoPatterns, NoOpens, NoProperties, Arguments)),
            (new Algorithm.Conditional(scope, NoOpens, []),
                new Algorithm.Conditional(equal, NoOpens, Array.Empty<CondBranch>()),
                new Algorithm.Conditional(different, NoOpens, Array.Empty<CondBranch>())),
            (new Algorithm.Alias(scope, NoOpens, NoProperties, new Expr.Resolve("target")),
                new Algorithm.Alias(equal, NoOpens, NoProperties, new Expr.Resolve("target")),
                new Algorithm.Alias(different, NoOpens, NoProperties, new Expr.Resolve("target"))),
        ];
        foreach (var (left, same, other) in algorithms)
        {
            Assert.True(left.Equals(same), "Algorithm.Equals over a deep parent, equal");
            Assert.True(left.Equals((object)same), "Algorithm.Equals(object) over a deep parent");
            Assert.True(left == same, "Algorithm == over a deep parent");
            Assert.False(left.Equals(other), "Algorithm.Equals over a deep parent, outermost ancestor differs");
            Assert.True(left != other, "Algorithm != over a deep parent");
            Assert.True(left.GetHashCode() == same.GetHashCode(), "equal algorithms hash alike");
            Assert.True(new Dictionary<Algorithm, int> { [left] = 1 }.ContainsKey(same), "Dictionary lookup through an equal algorithm");

            // And the expression that carries the algorithm.
            Assert.True(new Expr.AlgorithmExpr(left).Equals(new Expr.AlgorithmExpr(same)), "AlgorithmExpr over a deep parent, equal");
            Assert.False(new Expr.AlgorithmExpr(left).Equals(new Expr.AlgorithmExpr(other)), "AlgorithmExpr over a deep parent, different");
            Assert.True(new Expr.AlgorithmExpr(left).GetHashCode() == new Expr.AlgorithmExpr(same).GetHashCode(), "AlgorithmExpr hash");
        }
    }

    /// <summary>The unchanged records that hold an expression or an algorithm: one generated frame, then the iterative walk.</summary>
    internal static void AssertEntryRecords(int depth)
    {
        var left = Chain("mixed", depth, new Expr.Num(1));
        var equal = Chain("mixed", depth, new Expr.Num(1));
        var different = Chain("mixed", depth, new Expr.Num(2));

        Assert.True(new ComparisonLink(ComparisonOp.Lt, left).Equals(new ComparisonLink(ComparisonOp.Lt, equal)), "ComparisonLink, equal");
        Assert.False(new ComparisonLink(ComparisonOp.Lt, left).Equals(new ComparisonLink(ComparisonOp.Lt, different)), "ComparisonLink, different");
        Assert.True(new ComparisonLink(ComparisonOp.Lt, left).GetHashCode() == new ComparisonLink(ComparisonOp.Lt, equal).GetHashCode(), "ComparisonLink hash");
        Assert.True(new InterpolationLink(left, "t") == new InterpolationLink(equal, "t"), "InterpolationLink ==");
        Assert.True(new InterpolationLink(left, "t") != new InterpolationLink(different, "t"), "InterpolationLink !=");
        Assert.True(new InterpolationLink(left, "t").GetHashCode() == new InterpolationLink(equal, "t").GetHashCode(), "InterpolationLink hash");

        Algorithm Alias(Expr target) => new Algorithm.Alias(null, NoOpens, NoProperties, target);
        Assert.True(new Property("P", Alias(left)).Equals(new Property("P", Alias(equal))), "Property, equal");
        Assert.False(new Property("P", Alias(left)).Equals(new Property("P", Alias(different))), "Property, different");
        Assert.True(new Property("P", Alias(left)).GetHashCode() == new Property("P", Alias(equal)).GetHashCode(), "Property hash");
        var head = new Pattern.Bind("n");
        Assert.True(new CondBranch(head, Alias(left)).Equals(new CondBranch(head, Alias(equal))), "CondBranch, equal");
        Assert.False(new CondBranch(head, Alias(left)).Equals(new CondBranch(head, Alias(different))), "CondBranch, different");
        Assert.True(new CondBranch(head, Alias(left)).GetHashCode() == new CondBranch(head, Alias(equal)).GetHashCode(), "CondBranch hash");
    }

    /// <summary>
    /// The hierarchies whose structural children sit in LISTS: generated equality compares the list
    /// reference and never an element, so depth never mattered and independently built structures
    /// are unequal.
    /// </summary>
    internal static void AssertReferenceComparedHierarchies(int depth)
    {
        ParameterPattern parameters = new CaptureParameterPattern("x"), otherParameters = new CaptureParameterPattern("x");
        Pattern head = new Pattern.Bind("x"), otherHead = new Pattern.Bind("x");
        Result value = new Result.Atom(1), otherValue = new Result.Atom(1);
        for (var level = 0; level < depth; level++)
        {
            parameters = level % 2 == 0 ? new SequenceValueParameterPattern([parameters]) : new ListValueParameterPattern([parameters]);
            otherParameters = level % 2 == 0 ? new SequenceValueParameterPattern([otherParameters]) : new ListValueParameterPattern([otherParameters]);
            head = level % 2 == 0 ? new Pattern.SequenceValue([head]) : new Pattern.ListValue([head]);
            otherHead = level % 2 == 0 ? new Pattern.SequenceValue([otherHead]) : new Pattern.ListValue([otherHead]);
            value = level % 2 == 0 ? new Result.ListValue([value]) : new Result.SequenceValue([value, value]);
            otherValue = level % 2 == 0 ? new Result.ListValue([otherValue]) : new Result.SequenceValue([otherValue, otherValue]);
        }

        Assert.True(parameters.Equals(parameters) && !parameters.Equals(otherParameters) && parameters != otherParameters, "parameter patterns compare their item list by reference");
        Assert.True(parameters.GetHashCode() == parameters.GetHashCode(), "parameter pattern hash");
        Assert.True(head.Equals(head) && !head.Equals(otherHead) && head != otherHead, "clause patterns compare their item list by reference");
        Assert.True(head.GetHashCode() == head.GetHashCode(), "clause pattern hash");
        Assert.True(value.Equals(value) && !value.Equals(otherValue) && value != otherValue, "values compare their item list by reference");
        Assert.True(value.GetHashCode() == value.GetHashCode(), "value hash");

        // Records that hold them stay shallow as well.
        var body = new Algorithm.User(null, NoPatterns, NoOpens, NoProperties, Arguments);
        Assert.True(new CondBranch(head, body).Equals(new CondBranch(head, body)), "CondBranch over a deep head");
        Assert.False(new CondBranch(head, body).Equals(new CondBranch(otherHead, body)), "CondBranch over another deep head");
        _ = new CondBranch(head, body).GetHashCode();
        Assert.True(Result.ValueComparer.Equals(value, otherValue), "language equality is the separate, structural comparer");
    }

    /// <summary>Everything above, as the child-process probe runs it.</summary>
    internal static void AssertAll(int depth)
    {
        foreach (var shape in Shapes)
            AssertExpressionShape(shape, depth);
        AssertSharedDiamonds(depth);
        AssertScopeChains(depth);
        AssertEntryRecords(depth);
        AssertReferenceComparedHierarchies(depth);
    }
}
