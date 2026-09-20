namespace KatLang.Tests;

/// <summary>
/// The ONE test-side enumeration of the concrete <see cref="Expr"/> variants.
///
/// <para><see cref="Expr"/> is a C# <c>closed</c> hierarchy, so a production switch
/// expression that names every variant is proven exhaustive by the compiler and a
/// new variant fails the build at every such dispatch (<c>CS8509</c> is an error in
/// <c>src/KatLang</c>). No test therefore re-proves that a dispatch covers every
/// variant. What the compiler does NOT prove is per-variant BEHAVIOR — that a
/// composite variant's children are actually walked, that a load inside it is
/// elaborated, that its children route through the async seam — and it cannot help
/// the few statement-form traversals (side-effect visitors and collectors) that keep a
/// runtime guard. The behavioral tables pinning those properties are ratcheted against
/// this catalog, so a newly added variant fails a test until it has a row instead of
/// silently staying untested.</para>
/// </summary>
internal static class ExprVariantCatalog
{
    // The copy constructor permits non-nested descendants in the declaring assembly.
    // Discover the whole compiler-known set, then pin our nested/sealed convention below.
    internal static IReadOnlyList<Type> DirectVariants { get; } = typeof(Expr).Assembly.GetTypes()
        .Where(type => type.BaseType == typeof(Expr))
        .ToList();

    /// <summary>Every concrete variant, by declaration name, in ordinal order.</summary>
    public static IReadOnlyList<string> DeclaredVariantNames { get; } = DirectVariants
        .Select(type => type.Name)
        .OrderBy(name => name, StringComparer.Ordinal)
        .ToList();

    /// <summary>
    /// Variants whose public shape holds an expression, algorithm, or bundle child —
    /// derived from the actual record shape so a composite variant can never be
    /// mistaken for a leaf by a child-free sample.
    /// </summary>
    public static IReadOnlyList<string> StructurallyCompositeVariantNames { get; } = DirectVariants
        .Where(HasStructuralExprChildren)
        .Select(type => type.Name)
        .OrderBy(name => name, StringComparer.Ordinal)
        .ToList();

    /// <summary>
    /// One embeddable, evaluable sample per variant. Samples are immutable records
    /// and are freely shared across embedding positions; each evaluates through the
    /// evaluator entry points to an ordinary outcome (ok or a structured error).
    /// </summary>
    public static IReadOnlyDictionary<string, Expr> Samples { get; } = BuildSamples();

    private static IReadOnlyDictionary<string, Expr> BuildSamples()
    {
        var leaf = new Expr.Num(1);
        return new Dictionary<string, Expr>(StringComparer.Ordinal)
        {
            [nameof(Expr.Param)] = new Expr.Param("p"),
            [nameof(Expr.Num)] = leaf,
            [nameof(Expr.StringLiteral)] = new Expr.StringLiteral("s"),
            [nameof(Expr.BoolLiteral)] = new Expr.BoolLiteral(true),
            [nameof(Expr.Unary)] = new Expr.Unary(UnaryOp.Minus, leaf),
            [nameof(Expr.Binary)] = new Expr.Binary(BinaryOp.Add, leaf, leaf),
            [nameof(Expr.Index)] = new Expr.Index(new Expr.Capture([leaf, leaf]), new Expr.Num(0)),
            [nameof(Expr.SequenceConstruct)] = new Expr.SequenceConstruct(leaf, leaf),
            [nameof(Expr.EmptySequence)] = new Expr.EmptySequence(0),
            [nameof(Expr.SequenceSpread)] = new Expr.SequenceSpread(new Expr.Capture([leaf, leaf])),
            [nameof(Expr.ListLiteral)] = new Expr.ListLiteral([leaf, leaf]),
            [nameof(Expr.Resolve)] = new Expr.Resolve("R"),
            [nameof(Expr.DotCall)] = new Expr.DotCall(new Expr.Capture([leaf, leaf]), "count"),
            [nameof(Expr.Grace)] = new Expr.Grace(leaf, 1),
            [nameof(Expr.AlgorithmExpr)] = new Expr.AlgorithmExpr(
                new Algorithm.User(Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: [leaf])),
            [nameof(Expr.Capture)] = new Expr.Capture([leaf, leaf]),
            [nameof(Expr.Call)] = new Expr.Call(new Expr.Resolve("F"), new OutputBundle([leaf])),
            [nameof(Expr.NativeCall)] = new Expr.NativeCall("Abs", ["x"]),
        };
    }

    /// <summary>xUnit member data over every variant name.</summary>
    public static TheoryData<string> VariantNames()
    {
        var data = new TheoryData<string>();
        foreach (var name in DeclaredVariantNames)
            data.Add(name);
        return data;
    }

    /// <summary>
    /// Asserts that a hand-written per-variant table names every declared variant and
    /// nothing else — the ratchet that turns "new <see cref="Expr"/> variant" into a
    /// failing test for a behavioral table the compiler cannot complete.
    /// </summary>
    public static void AssertCoversEveryVariant(IEnumerable<string> tableVariantNames, string tableDescription)
    {
        var covered = tableVariantNames.Distinct(StringComparer.Ordinal).OrderBy(name => name, StringComparer.Ordinal).ToList();
        var missing = DeclaredVariantNames.Except(covered, StringComparer.Ordinal).ToList();
        var stale = covered.Except(DeclaredVariantNames, StringComparer.Ordinal).ToList();
        Assert.True(
            missing.Count == 0 && stale.Count == 0,
            $"{tableDescription} must have exactly one row per Expr variant. "
            + $"Missing: [{string.Join(", ", missing)}]; stale: [{string.Join(", ", stale)}].");
    }

    /// <summary>
    /// Asserts that a behavioral table covers every structurally composite variant
    /// except the ones it deliberately excludes (each exclusion must itself be a real
    /// composite variant, so an exclusion cannot go stale silently).
    /// </summary>
    public static void AssertCoversEveryCompositeVariant(
        IEnumerable<string> tableVariantNames,
        string tableDescription,
        params string[] deliberatelyExcluded)
    {
        foreach (var excluded in deliberatelyExcluded)
        {
            Assert.Contains(excluded, StructurallyCompositeVariantNames);
        }

        var expected = StructurallyCompositeVariantNames.Except(deliberatelyExcluded, StringComparer.Ordinal).ToList();
        var covered = tableVariantNames.Distinct(StringComparer.Ordinal).OrderBy(name => name, StringComparer.Ordinal).ToList();
        Assert.True(
            expected.SequenceEqual(covered, StringComparer.Ordinal),
            $"{tableDescription} must cover every structurally composite Expr variant"
            + (deliberatelyExcluded.Length == 0 ? "" : $" except [{string.Join(", ", deliberatelyExcluded)}]")
            + $". Expected: [{string.Join(", ", expected)}]; covered: [{string.Join(", ", covered)}].");
    }

    private static bool HasStructuralExprChildren(Type variantType)
        => variantType
            .GetProperties(System.Reflection.BindingFlags.Public
                | System.Reflection.BindingFlags.Instance
                | System.Reflection.BindingFlags.DeclaredOnly)
            .Any(property =>
                typeof(Expr).IsAssignableFrom(property.PropertyType)
                || typeof(Algorithm).IsAssignableFrom(property.PropertyType)
                || typeof(OutputBundle).IsAssignableFrom(property.PropertyType)
                || typeof(IEnumerable<Expr>).IsAssignableFrom(property.PropertyType));
}

/// <summary>The catalog's own consistency: its sample table is complete and every sample is the variant it claims.</summary>
public class ExprVariantCatalogTests
{
    [Fact]
    public void DirectVariants_ArePublicSealedNestedRecords()
    {
        Assert.NotEmpty(ExprVariantCatalog.DirectVariants);
        Assert.All(ExprVariantCatalog.DirectVariants, type =>
        {
            Assert.Equal(typeof(Expr), type.DeclaringType);
            Assert.True(type.IsNestedPublic);
            Assert.True(type.IsSealed);
        });
    }

    [Fact]
    public void Samples_HaveExactlyOneRowPerVariant()
    {
        ExprVariantCatalog.AssertCoversEveryVariant(ExprVariantCatalog.Samples.Keys, "ExprVariantCatalog.Samples");
        foreach (var (name, sample) in ExprVariantCatalog.Samples)
            Assert.Equal(name, sample.GetType().Name);
    }

    [Fact]
    public void CompositeVariants_AreExactlyTheVariantsWithExpressionChildren()
    {
        Assert.Equal(
            new[]
            {
                nameof(Expr.AlgorithmExpr), nameof(Expr.Binary), nameof(Expr.Call), nameof(Expr.Capture),
                nameof(Expr.DotCall), nameof(Expr.Grace), nameof(Expr.Index), nameof(Expr.ListLiteral),
                nameof(Expr.SequenceConstruct), nameof(Expr.SequenceSpread), nameof(Expr.Unary),
            },
            ExprVariantCatalog.StructurallyCompositeVariantNames);
    }
}
