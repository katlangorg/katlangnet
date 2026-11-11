using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text;

namespace KatLang.Tests;

/// <summary>
/// RAW RECORD TEXT ON HOST-BUILT RECORDS (docs/design/language-rules/evaluator-and-hosting.md
/// § Shared-DAG guarantee, RAW RECORD TEXT). The records whose synthesized <c>ToString</c> followed
/// a record-valued member — the AST records of <see cref="NativeRecordEqualityTests"/> and
/// <see cref="EvalError.WithContext"/> — write their members with an explicit stack. This class pins
/// the layout (the compiler's, restated over reflection), the inventory, the refusal of a forged
/// cycle and the deep renderings (also run on a 1 MiB thread in a child process by
/// <see cref="AstStructuralDepthProcessTests"/>).
/// </summary>
public class NativeRecordTextTests
{
    private const BindingFlags DeclaredInstance =
        BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly;

    private static readonly SourceSpan Span = new(1, 2, 1, 4);

    [Fact]
    public void ShallowRecords_PreserveSynthesizedMemberOrderAndValues()
    {
        var leaf = new Expr.Resolve("x") { Span = Span };
        var args = new OutputBundle([leaf]);
        var unary = new Expr.Unary(UnaryOp.Minus, leaf);
        var scope = new ScopeCtx(new ScopeCtx(null, [], [], ["root"]), [], [], ["child"]);
        var user = new Algorithm.User(scope, [new CaptureParameterPattern(new ParameterDeclaration("x"))], [], [], args)
        {
            HasExplicitParameterList = true,
        };
        var fallback = new Expr.DotCall(unary, "m", args) { MemberSpan = Span, LexicalFallback = unary };
        object[] samples =
        [
            unary,
            new Expr.Binary(BinaryOp.Add, unary, unary),
            new Expr.Comparison(unary, [new ComparisonLink(ComparisonOp.Lt, leaf)]),
            new Expr.Index(unary, args),
            new Expr.SequenceConstruct(leaf, unary),
            new Expr.SequenceSpread(unary) { SpreadMarkerSpan = Span },
            new Expr.DotCall(unary, "m") { MemberSpan = Span },
            fallback,
            new Expr.Grace(unary, 2),
            new Expr.Grace(leaf, -1) { Span = Span },
            new Expr.AlgorithmExpr(user),
            new Expr.AlgorithmExpr(new Algorithm.Builtin(BuiltinId.count)),
            new Expr.Call(unary, args),
            new Expr.Unary(UnaryOp.Minus, null!),
            user,
            new Algorithm.User(null, [], [], [], OutputBundle.Empty),
            new Algorithm.Conditional(scope, [], [new CondBranch(new Pattern.Bind("x"), user)]),
            new Algorithm.Alias(scope, [], [], fallback) { IsReference = false },
            new Algorithm.Alias(null, [], [], leaf),
            scope,
            new EvalError.WithContext(new CallContext("f"),
                new EvalError.WithContext("frame", new EvalError.EvaluationStepLimitExceeded(20))) { Span = Span },
            new EvalError.WithContext(new PropertyEvaluationContext("P"), new EvalError.UnknownName("x")),
        ];

        foreach (var sample in samples)
            Assert.Equal(GeneratedText(sample), sample.ToString());
    }

    [Theory]
    [InlineData(13)]
    [InlineData(39)]
    public void NestedRecordsOfEveryKind_PrintLikeTheSynthesizedLayout(int depth)
    {
        // Every recursive member of every expression kind, nested in one another: each record's
        // remaining members must follow a child of any size (Binary.Right after a deep Left, a
        // dot edge's three record-valued members, an alias target below an algorithm expression).
        // The fallback edge prints its child twice (LexicalFallback and EffectiveLexicalFallback),
        // so the text doubles there; the depths keep it small.
        var leaf = new Expr.Num(1) { Span = Span };
        var mixed = DeepRecordGraphs.Chain("mixed", depth, leaf);
        var text = mixed.ToString();
        Assert.Equal(GeneratedText(mixed), text);

        // The records that only ENTER one: a synthesized frame around the writer.
        Assert.Equal(GeneratedText(new ComparisonLink(ComparisonOp.Lt, mixed)), new ComparisonLink(ComparisonOp.Lt, mixed).ToString());
        Assert.Equal($"InterpolationLink {{ Hole = {text}, Text = t }}", new InterpolationLink(mixed, "t").ToString());

        // A shared child is written at each occurrence.
        var twice = new Expr.Binary(BinaryOp.Add, mixed, mixed).ToString();
        Assert.Equal($"Binary {{ Span = , Op = Add, Left = {text}, Right = {text} }}", twice);
    }

    /// <summary>
    /// The compiler's record text restated over reflection: the type's name, then every public
    /// readable instance property, base record first, in declaration order, as
    /// <c>Name = value</c>. A member holding one of the records under test is expanded by this
    /// oracle itself, so no hand-written <c>PrintMembers</c> is its own judge; any other value
    /// prints through its own <c>ToString</c> (these records declare no public field). Recursive:
    /// for shallow fixtures only.
    /// </summary>
    private static string? GeneratedText(object? value)
    {
        if (value is not (Expr.Unary or Expr.Binary or Expr.Comparison or Expr.Index or Expr.SequenceConstruct
            or Expr.SequenceSpread or Expr.DotCall or Expr.Grace or Expr.AlgorithmExpr or Expr.Call
            or Algorithm.User or Algorithm.Conditional or Algorithm.Alias or ScopeCtx or EvalError.WithContext
            or ComparisonLink))
            return value?.ToString();

        var type = value.GetType();
        var levels = new Stack<Type>();
        for (var level = type; level is not null && level != typeof(object); level = level.BaseType)
            levels.Push(level);
        var members = levels.SelectMany(static level => level.GetProperties(
                BindingFlags.Public | BindingFlags.Instance | BindingFlags.DeclaredOnly))
            .Where(static member => member.GetMethod is { IsPublic: true })
            .Select(member => $"{member.Name} = {GeneratedText(member.GetValue(value))}");
        return $"{type.Name} {{ {string.Join(", ", members)} }}";
    }

    [Fact]
    public void HandWrittenRecordText_IsExactlyTheRecordsWithHandWrittenEquality()
    {
        // One inventory, two walks: a record whose equality follows a record-valued field prints
        // that field too. AstRecordText decides by the equality classification which members it
        // writes itself, so a record on one list and not on the other would print wrongly (or
        // recurse again) only for the hosts that nest it.
        static bool IsHandWritten(MethodInfo? method)
            => method is not null && !method.IsDefined(typeof(CompilerGeneratedAttribute), inherit: false);

        var records = typeof(Expr).Assembly.GetTypes().Where(NativeRecordEqualityTests.GeneratedRecordContract.IsModeled).ToArray();
        string[] Names(Func<Type, bool> selected)
            => records.Where(selected).Select(static type => type.FullName!).OrderBy(static name => name, StringComparer.Ordinal).ToArray();

        var equality = Names(static type => IsHandWritten(type.GetMethod("Equals", DeclaredInstance, [type])));
        var text = Names(static type => IsHandWritten(type.GetMethod("PrintMembers", DeclaredInstance, [typeof(StringBuilder)])));
        Assert.Equal(14, equality.Length);
        Assert.Equal(equality, text);

        // The one error record that holds an error writes all three members itself.
        var frame = typeof(EvalError.WithContext);
        Assert.True(IsHandWritten(frame.GetMethod("PrintMembers", DeclaredInstance, [typeof(StringBuilder)])), "WithContext.PrintMembers");
        Assert.True(IsHandWritten(frame.GetMethod("Equals", DeclaredInstance, [frame])), "WithContext.Equals");
        Assert.True(IsHandWritten(frame.GetMethod("GetHashCode", DeclaredInstance, Type.EmptyTypes)), "WithContext.GetHashCode");
    }

    [Fact]
    public void AForgedRecordCycle_HasNoText_AndIsRefused()
    {
        // No public construction makes a record reach itself through a printed member; only
        // reflection can forge one. Its synthesized text never ended (the compiler's stack guard
        // threw); the iterative writer refuses it instead of writing forever.
        var operand = typeof(Expr.Unary).GetField("<Operand>k__BackingField", BindingFlags.Instance | BindingFlags.NonPublic)!;
        var bottom = new Expr.Unary(UnaryOp.Minus, new Expr.Num(1));
        var top = new Expr.Unary(UnaryOp.Minus, new Expr.Grace(bottom, 1));
        operand.SetValue(bottom, top);
        var selfLoop = new Expr.Unary(UnaryOp.Minus, new Expr.Num(1));
        operand.SetValue(selfLoop, selfLoop);

        var failure = Assert.Throws<InvalidOperationException>(() => top.ToString());
        Assert.Contains("cycle", failure.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Throws<InvalidOperationException>(() => selfLoop.ToString());
        // Below an acyclic prefix, and through a record that only enters the writer.
        Assert.Throws<InvalidOperationException>(() => new Expr.Binary(BinaryOp.Add, new Expr.Num(1), top).ToString());
        Assert.Throws<InvalidOperationException>(() => new ComparisonLink(ComparisonOp.Lt, top).ToString());

        // A cycle through a caller-owned list is no cycle of printed members: a list prints as
        // itself and is never entered.
        var links = new List<ComparisonLink>();
        var comparison = new Expr.Comparison(new Expr.Num(1), links);
        links.Add(new ComparisonLink(ComparisonOp.Eq, comparison));
        Assert.EndsWith($", Links = {links} }}", comparison.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void FiftyThousandLevels_RenderWithoutRecursion() => AssertDeepText();

    // Run only in the child process. Losing the entry check can terminate the process
    // before either assertion returns.
    internal static void AssertReentrantHostFormatting()
    {
        ScopeCtx scope = null!;
        scope = new ScopeCtx(null, new ReenteringList<Expr>(() => scope.ToString()), [], []);
        Assert.Throws<InsufficientExecutionStackException>(() => scope.ToString());

        EvalError error = null!;
        var names = new ReenteringList<string>(() => error.ToString());
        error = new EvalError.WithContext(new ImplicitParameterContext(names, 0), new EvalError.BadArity());
        Assert.Throws<InsufficientExecutionStackException>(() => error.ToString());
    }

    private sealed class ReenteringList<T>(Func<string> format) : IReadOnlyList<T>
    {
        public override string ToString() => format();

        // ImplicitParameterContext reaches the host through Count.
        public int Count => format().Length;

        public T this[int index] => throw new NotSupportedException();

        public IEnumerator<T> GetEnumerator() => throw new NotSupportedException();

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    /// <summary>
    /// Deep chains through an expression member, a scope parent and an error's inner error. The
    /// synthesized text recursed once per level (the compiler's stack guard threw long before this
    /// depth) and copied every nested text once per enclosing level. Assertion messages are
    /// constants: a failure must not print the text it is about.
    /// </summary>
    internal static void AssertDeepText()
    {
        const int depth = 50_000;
        var leaf = new Expr.Resolve("deep leaf");
        var unary = DeepRecordGraphs.Chain("unary", depth, leaf);
        var scope = DeepRecordGraphs.Scope(depth + 1, DeepRecordGraphs.NamesX);
        var rootScope = DeepRecordGraphs.Scope(1, DeepRecordGraphs.NamesX);
        var inner = new EvalError.EvaluationStepLimitExceeded(100);
        EvalError error = inner;
        for (var level = 0; level < depth; level++)
            error = new EvalError.WithContext("frame", error);

        AssertRepeatedLayout(unary.ToString(), "Unary { Span = , Op = Minus, Operand = ", leaf.ToString(), " }", depth);
        AssertRepeatedLayout(scope.ToString(), "ScopeCtx { Parent = ", rootScope.ToString(),
            $", Opens = {scope.Opens}, Properties = {scope.Properties}, Parameters = {scope.Parameters} }}", depth);
        // An algorithm over the deep scope chain, below an expression: three record kinds deep.
        var user = new Algorithm.User(scope, [], [], [], OutputBundle.Empty);
        var body = new Expr.AlgorithmExpr(user).ToString();
        Assert.True(body.StartsWith("AlgorithmExpr { Span = , Algorithm = User { Parent = ScopeCtx { Parent = ScopeCtx { ", StringComparison.Ordinal), "algorithm prefix");
        Assert.True(body.EndsWith(", HasExplicitParameterList = False } }", StringComparison.Ordinal), "algorithm suffix");

        Assert.True(error.IsResourceLimit);
        Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, error.Code);
        AssertRepeatedLayout(error.ToString(),
            "WithContext { Span = , IsResourceLimit = True, Code = EvaluationStepLimitExceeded, ErrorContext = frame, Inner = ",
            inner.ToString(), ", Context = frame }", depth);
    }

    private static void AssertRepeatedLayout(string text, string prefix, string leaf, string suffix, int depth)
    {
        Assert.True(text.Length == (long)depth * (prefix.Length + suffix.Length) + leaf.Length, "rendered length");
        var remainder = text.AsSpan();
        for (var level = 0; level < depth; level++)
        {
            Assert.True(remainder.StartsWith(prefix, StringComparison.Ordinal), "record prefix");
            Assert.True(remainder.EndsWith(suffix, StringComparison.Ordinal), "record suffix");
            remainder = remainder[prefix.Length..^suffix.Length];
        }

        Assert.True(remainder.SequenceEqual(leaf), "deepest record");
    }
}
