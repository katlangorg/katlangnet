using System.Globalization;
using System.Reflection;
using System.Runtime.CompilerServices;

namespace KatLang.Formatting.PublicApi.Tests;

/// <summary>
/// The checked-in public API baseline of the KatLang NuGet package.
///
/// <para><c>PublicApiBaseline.txt</c> is the deterministic rendering
/// (<see cref="PublicApiSurfaceRenderer"/>) of the COMPILED <c>KatLang</c>
/// assembly — the one assembly the package ships — so any change to the
/// surface a consumer binds against (a removed or added member, a changed
/// signature, a moved enum value, a narrowed accessor) fails this suite before
/// a downstream consumer discovers it. The normal run only compares; an
/// intentional surface change is recorded by regenerating the baseline in a
/// targeted run that writes it and then fails by design
/// (<see cref="ArtifactRegeneration"/>):
///   $env:KATLANG_REGENERATE_PUBLIC_API = "1"
///   dotnet test .\KatLang.slnx --filter PublicApiBaseline
/// then review the diff (it IS the NuGet compatibility review), clear the flag,
/// and rerun. Regenerating the baseline never changes the release version; that
/// decision stays explicit in KatLangVersion.props.</para>
/// </summary>
public class PublicApiBaselineTests
{
    internal const string BaselineRelativePath = "tests/KatLang.Formatting.PublicApi.Tests/PublicApiBaseline.txt";

    private static readonly Assembly PackageAssembly = typeof(KatLangEngine).Assembly;

    /// <summary>
    /// What the baseline means depends on this: the reflected assembly is the
    /// packaged one, and this project sees it exactly as a consumer does.
    /// </summary>
    [Fact]
    public void Baseline_ReflectsThePackagedKatLangAssembly_AsANonFriendConsumerSeesIt()
    {
        Assert.Equal("KatLang", PackageAssembly.GetName().Name);
        Assert.DoesNotContain(
            PackageAssembly.GetCustomAttributes<InternalsVisibleToAttribute>(),
            attribute => attribute.AssemblyName.StartsWith(
                typeof(PublicApiBaselineTests).Assembly.GetName().Name!, StringComparison.Ordinal));
    }

    [Fact]
    public void PublicApiSurface_MatchesTheCheckedInBaseline()
    {
        var rendered = PublicApiSurfaceRenderer.Render(PackageAssembly);
        var flag = RegenerationFlags.PublicApi;

        ArtifactRegeneration.VerifyOrRegenerate(
            flag,
            BaselineRelativePath,
            regenerate: () => rendered,
            verify: () =>
            {
                var path = Path.Combine(RepoRoot.Find(), BaselineRelativePath);
                Assert.True(File.Exists(path),
                    $"{BaselineRelativePath} is missing. Set {flag}=1 and rerun this test to create it " +
                    "(that run fails by design); review the file, clear the flag, and rerun.");

                var checkedIn = File.ReadAllText(path).ReplaceLineEndings("\n");
                if (checkedIn == rendered)
                    return;

                Assert.Fail(
                    $"The compiled public API of {PackageAssembly.GetName().Name} differs from {BaselineRelativePath}. " +
                    "This is a NuGet surface change. If it is unintended, revert it. If it is intended, review its " +
                    "compatibility impact and the release version, then record it: set " +
                    $"{flag}=1, rerun this test (it rewrites the baseline and then fails by design), review the diff, " +
                    "clear the flag, and rerun. " + FirstDifference(checkedIn, rendered));
            },
            afterRegenerating: "treat that diff as the NuGet compatibility review");
    }

    [Fact]
    public void Baseline_HasIntegrity()
    {
        var path = Path.Combine(RepoRoot.Find(), BaselineRelativePath);
        Assert.True(File.Exists(path), $"{BaselineRelativePath} is missing.");

        var lines = File.ReadAllText(path).ReplaceLineEndings("\n").Split('\n');
        Assert.True(lines.Length > 10, "baseline is empty or truncated");
        Assert.StartsWith("# Public API surface of assembly KatLang.", lines[0], StringComparison.Ordinal);
        Assert.Equal("", lines[^1]); // ends with a newline

        // Type headings (unindented, non-comment, non-blank lines) are unique.
        var headings = lines.Where(line => line.Length > 0 && line[0] != ' ' && line[0] != '#').ToList();
        Assert.NotEmpty(headings);
        Assert.Equal(headings.Count, headings.Distinct(StringComparer.Ordinal).Count());
        Assert.DoesNotContain(lines, line => line.EndsWith(' ') || line.EndsWith('\t'));
    }

    [Fact]
    public void Renderer_EmitsExactlyOneBlockPerConsumerVisibleType()
    {
        var rendered = PublicApiSurfaceRenderer.Render(PackageAssembly);
        var headings = rendered.Split('\n')
            .Where(line => line.Length > 0 && line[0] != ' ' && line[0] != '#')
            .ToHashSet(StringComparer.Ordinal);

        var expected = PublicApiSurfaceRenderer.ConsumerVisibleTypes(PackageAssembly)
            .Select(PublicApiSurfaceRenderer.TypeHeading)
            .ToHashSet(StringComparer.Ordinal);

        Assert.Equal(expected.Count, headings.Count);
        foreach (var heading in expected)
            Assert.Contains(headings, line => line.EndsWith(" " + heading, StringComparison.Ordinal) || line.Contains(" " + heading + " ", StringComparison.Ordinal) || line.Contains(" " + heading + "(", StringComparison.Ordinal));
    }

    [Fact]
    public void Renderer_IsIndependentOfReflectionOrder_AndCarriesNoRuntimeIdentityNoise()
    {
        var types = PublicApiSurfaceRenderer.ConsumerVisibleTypes(PackageAssembly);
        var forward = PublicApiSurfaceRenderer.Render("KatLang", types);
        var reversed = PublicApiSurfaceRenderer.Render("KatLang", types.Reverse());
        Assert.Equal(forward, reversed);

        // Canonical names only: no generic arity ticks, by-ref ampersands, or
        // assembly/version/culture qualification, which is what keeps the
        // baseline identical across runtimes and releases. String constants and
        // attribute messages may contain anything, so those checks skip lines
        // that carry quoted text.
        Assert.DoesNotContain("Version=", forward, StringComparison.Ordinal);
        Assert.DoesNotContain("PublicKeyToken", forward, StringComparison.Ordinal);
        Assert.DoesNotContain("Culture=", forward, StringComparison.Ordinal);
        Assert.DoesNotContain("\r", forward, StringComparison.Ordinal);
        Assert.DoesNotMatch("`[0-9]", forward);
        foreach (var line in forward.Split('\n').Where(line => !line.Contains('"')))
        {
            Assert.DoesNotContain("`", line, StringComparison.Ordinal);
            Assert.DoesNotContain("&", line, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Renderer_IsCultureInvariant()
    {
        var expected = PublicApiSurfaceRenderer.Render(PackageAssembly);
        var previousCulture = CultureInfo.CurrentCulture;
        var previousUiCulture = CultureInfo.CurrentUICulture;
        try
        {
            CultureInfo.CurrentCulture = CultureInfo.GetCultureInfo("lv-LV");
            CultureInfo.CurrentUICulture = CultureInfo.GetCultureInfo("lv-LV");
            Assert.Equal(expected, PublicApiSurfaceRenderer.Render(PackageAssembly));
        }
        finally
        {
            CultureInfo.CurrentCulture = previousCulture;
            CultureInfo.CurrentUICulture = previousUiCulture;
        }
    }

    /// <summary>
    /// The renderer's format, pinned on a purpose-built fixture so every rendered
    /// construct is reviewable in one place: enum values with negative and
    /// unsigned extremes, public/protected nested and nested-generic types,
    /// variance and constraints, defaults, nullable and flow-nullability
    /// annotations, long tuple names, ref/ref-readonly signatures, decimal
    /// constants, operators and conversions, indexers, required/init/protected
    /// accessors, record surfaces, delegates, extension/params parameters and
    /// the rendered attributes. The expected text is a manually reviewed
    /// constant.
    /// </summary>
    [Fact]
    public void RendererFixture_RendersTheDocumentedFormat()
    {
        var fixtureNamespace = typeof(RendererFixture.Shape).Namespace!;
        var types = PublicApiSurfaceRenderer.ConsumerVisibleTypes(typeof(RendererFixture.Shape).Assembly)
            .Where(type => type.Namespace == fixtureNamespace);

        var rendered = PublicApiSurfaceRenderer.Render("Fixture", types);
        var body = rendered[PublicApiSurfaceRenderer.Header("Fixture").Length..];
        Assert.Equal(ExpectedFixtureRendering, body);
    }

    private const string ExpectedFixtureRendering = """

        public class KatLang.Formatting.PublicApi.Tests.RendererFixture.ConstraintCases<TClass, TNullableClass, TNotNull, TStruct, TUnmanaged, TNew>
          where TClass : class
          where TNullableClass : class?
          where TNotNull : notnull
          where TStruct : struct
          where TUnmanaged : unmanaged
          where TNew : new()
          ctor     public ConstraintCases()

        [Experimental("KATFIX001")] public class KatLang.Formatting.PublicApi.Tests.RendererFixture.ExperimentalType
          ctor     public ExperimentalType()

        public class KatLang.Formatting.PublicApi.Tests.RendererFixture.GenericOuter<TOuter>
          where TOuter : notnull
          ctor     public GenericOuter()
          property public TOuter OuterValue { get; set; }

        public class KatLang.Formatting.PublicApi.Tests.RendererFixture.GenericOuter<TOuter>.Inner<TInner>
          where TOuter : notnull
          where TInner : unmanaged
          ctor     public Inner()
          property public TInner InnerValue { get; set; }

        protected internal class KatLang.Formatting.PublicApi.Tests.RendererFixture.GenericOuter<TOuter>.ProtectedInternalNested
          where TOuter : notnull
          ctor     public ProtectedInternalNested()

        protected class KatLang.Formatting.PublicApi.Tests.RendererFixture.GenericOuter<TOuter>.ProtectedNested
          where TOuter : notnull
          ctor     public ProtectedNested()
          method   protected virtual void Hook()

        public interface KatLang.Formatting.PublicApi.Tests.RendererFixture.IShape<out T>
          where T : class
          property public T Value { get; }
          method   public string Describe(bool verbose)

        public class KatLang.Formatting.PublicApi.Tests.RendererFixture.Outer
          ctor     public Outer()

        public sealed class KatLang.Formatting.PublicApi.Tests.RendererFixture.Outer.Inner
          ctor     public Inner()

        public enum KatLang.Formatting.PublicApi.Tests.RendererFixture.Outer.Kind : ulong
          Big = 18446744073709551615

        [Flags] public enum KatLang.Formatting.PublicApi.Tests.RendererFixture.Permissions : byte
          None = 0
          Read = 1
          Write = 2
          All = 3

        public sealed record KatLang.Formatting.PublicApi.Tests.RendererFixture.Point : System.IEquatable<KatLang.Formatting.PublicApi.Tests.RendererFixture.Point>
          ctor     public Point(int X, int Y)
          property public int X { get; init; }
          property public int Y { get; init; }
          method   public KatLang.Formatting.PublicApi.Tests.RendererFixture.Point <Clone>$()
          method   public void Deconstruct(out int X, out int Y)
          method   public double Distance(KatLang.Formatting.PublicApi.Tests.RendererFixture.Point? other = null)
          method   public bool Equals(KatLang.Formatting.PublicApi.Tests.RendererFixture.Point? other)
          method   public override bool Equals(object? obj)
          method   public override int GetHashCode()
          method   public override string ToString()
          operator public static bool op_Equality(KatLang.Formatting.PublicApi.Tests.RendererFixture.Point? left, KatLang.Formatting.PublicApi.Tests.RendererFixture.Point? right)
          operator public static bool op_Inequality(KatLang.Formatting.PublicApi.Tests.RendererFixture.Point? left, KatLang.Formatting.PublicApi.Tests.RendererFixture.Point? right)

        public delegate ref readonly int KatLang.Formatting.PublicApi.Tests.RendererFixture.RefReader()

        public class KatLang.Formatting.PublicApi.Tests.RendererFixture.RequiredOwner
          field    public required string Name
          ctor     [SetsRequiredMembers] public RequiredOwner()

        public abstract class KatLang.Formatting.PublicApi.Tests.RendererFixture.Shape : KatLang.Formatting.PublicApi.Tests.RendererFixture.IShape<string>
          const    public const string Kind = "poly\"gon\n"
          const    public const int MaxSides = 12
          const    public const decimal Ratio = 1.25
          field    public static readonly KatLang.Formatting.PublicApi.Tests.RendererFixture.Shape? Empty
          field    protected readonly int seed
          ctor     protected Shape(string name, int sides = 4, string? label = null, KatLang.Formatting.PublicApi.Tests.RendererFixture.Speed speed = KatLang.Formatting.PublicApi.Tests.RendererFixture.Speed.Fast, System.Threading.CancellationToken token = default)
          property public abstract double Area { get; }
          property public static int Count { get; }
          property [AllowNull] public string Label { get; set; }
          property [MaybeNull] public string? MaybeLabel { get; }
          property public string Name { get; protected set; }
          property [DisallowNull] public string? NullableLabel { get; set; }
          property public ref readonly int ReadOnlyRefValue { get; }
          property public ref int RefValue { get; }
          property public required int Sides { get; init; }
          property public string Value { get; }
          indexer  public virtual int this[int index] { get; }
          event    public System.EventHandler<string>? Changed
          method   public (int width, int height) Bounds(System.ReadOnlySpan<char> label)
          method   public static void Consume([NotNull] ref string? value)
          method   public static TResult? Convert<TResult>(KatLang.Formatting.PublicApi.Tests.RendererFixture.Shape shape, System.Func<KatLang.Formatting.PublicApi.Tests.RendererFixture.Shape, TResult?> selector) where TResult : struct
          method   public static void Defaults(decimal ratio = 1.25, double nan = NaN, char slash = '\\', string text = "line\n")
          method   public virtual string Describe(bool verbose = false)
          method   public static [NotNullIfNotNull("value")] string? Echo(string? value)
          method   [MemberNotNullWhen(true, "_label")] public bool EnsureLabel()
          method   [DoesNotReturn] public static void Fail()
          method   [MemberNotNull("_label")] public void InitializeLabel()
          method   [EditorBrowsable(Never)] [Obsolete("Removed.", error: true)] public void Legacy()
          method   public (int one, int two, int three, int four, int five, int six, int seven, int eight) LongBounds()
          method   public abstract double Measure(in double scale, out string? unit)
          method   public int Observe(ref readonly string? text)
          method   public T Pick<T>(System.Collections.Generic.IReadOnlyList<T?> items, ref int index) where T : class, System.IComparable<T>, new()
          method   public ref readonly int ReadOnlyRefAt()
          method   public ref int RefAt()
          method   protected internal virtual void Reset()
          method   public static void Stop([DoesNotReturnIf(true)] bool condition)
          method   [Obsolete("Use Describe instead.")] public string Summary()
          method   public override string ToString()
          method   public static bool TryMaybe([MaybeNullWhen(false)] out string? name)
          method   public static bool TryName([NotNullWhen(true)] out string? name)
          method   protected abstract void Validate()
          operator public static KatLang.Formatting.PublicApi.Tests.RendererFixture.Shape op_Addition(KatLang.Formatting.PublicApi.Tests.RendererFixture.Shape left, KatLang.Formatting.PublicApi.Tests.RendererFixture.Shape right)
          operator public static string op_Implicit(KatLang.Formatting.PublicApi.Tests.RendererFixture.Shape shape)

        public static class KatLang.Formatting.PublicApi.Tests.RendererFixture.ShapeExtensions
          method   public static int CountAll(this System.Collections.Generic.IEnumerable<KatLang.Formatting.PublicApi.Tests.RendererFixture.Shape> shapes, params System.ReadOnlySpan<int> weights)

        public delegate bool KatLang.Formatting.PublicApi.Tests.RendererFixture.ShapeFilter<in TShape>(TShape shape, params object[] tags)
          where TShape : KatLang.Formatting.PublicApi.Tests.RendererFixture.Shape

        public readonly record struct KatLang.Formatting.PublicApi.Tests.RendererFixture.Size : System.IEquatable<KatLang.Formatting.PublicApi.Tests.RendererFixture.Size>
          ctor     public Size(double Width, double Height)
          property public double Height { get; init; }
          property public double Width { get; init; }
          method   public void Deconstruct(out double Width, out double Height)
          method   public bool Equals(KatLang.Formatting.PublicApi.Tests.RendererFixture.Size other)
          method   public override bool Equals(object obj)
          method   public override int GetHashCode()
          method   public override string ToString()
          operator public static bool op_Equality(KatLang.Formatting.PublicApi.Tests.RendererFixture.Size left, KatLang.Formatting.PublicApi.Tests.RendererFixture.Size right)
          operator public static bool op_Inequality(KatLang.Formatting.PublicApi.Tests.RendererFixture.Size left, KatLang.Formatting.PublicApi.Tests.RendererFixture.Size right)

        public enum KatLang.Formatting.PublicApi.Tests.RendererFixture.Speed : long
          Reverse = -1
          Slow = 2
          Fast = 10

        """;

    private static string FirstDifference(string checkedIn, string rendered)
    {
        var expectedLines = checkedIn.Split('\n');
        var actualLines = rendered.Split('\n');
        var shared = Math.Min(expectedLines.Length, actualLines.Length);
        var index = 0;
        while (index < shared && expectedLines[index] == actualLines[index])
            index++;

        var baseline = index < expectedLines.Length ? expectedLines[index] : "<end of file>";
        var compiled = index < actualLines.Length ? actualLines[index] : "<end of file>";
        return $"First difference at line {index + 1}:{Environment.NewLine}" +
               $"baseline: {baseline}{Environment.NewLine}compiled: {compiled}";
    }
}
