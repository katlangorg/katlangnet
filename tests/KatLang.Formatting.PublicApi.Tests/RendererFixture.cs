using System.ComponentModel;
using System.Diagnostics.CodeAnalysis;

// The renderer format fixture: a small, purpose-built public surface that
// exercises every construct PublicApiSurfaceRenderer renders (enum values and
// underlying types, public/protected nested types, nested generics, generic
// variance and constraints (including class?, notnull and unmanaged), optional
// defaults, nullable and flow-nullability annotations, tuple names, ref returns,
// operators and conversions, indexers, events, decimal constants,
// required/init/protected accessors, records, delegates, extension and params
// parameters, and the rendered attributes). Its golden
// rendering in PublicApiBaselineTests pins the FORMAT independently of the
// KatLang surface, and it is the safe target for renderer mutation testing.
namespace KatLang.Formatting.PublicApi.Tests.RendererFixture;

[Flags]
public enum Permissions : byte
{
    None = 0,
    Read = 1,
    Write = 2,
    All = Read | Write,
}

public enum Speed : long
{
    Slow = 2,
    Fast = 10,
    Reverse = -1,
}

public interface IShape<out T> where T : class
{
    T Value { get; }

    string Describe(bool verbose);
}

public abstract class Shape : IShape<string>
{
    public const int MaxSides = 12;
    public const decimal Ratio = 1.25m;
    public const string Kind = "poly\"gon\n";
    public static readonly Shape? Empty;
    protected readonly int seed;
    private int _value;
    private string? _label;

    protected Shape(string name, int sides = 4, string? label = null, Speed speed = Speed.Fast, CancellationToken token = default)
    {
        Name = name;
        Value = label ?? name;
        seed = sides;
        Changed = null;
    }

    public string Value { get; }

    public string Name { get; protected set; }

    public required int Sides { get; init; }

    public abstract double Area { get; }

    public virtual int this[int index] => index;

    public static int Count { get; private set; }

    public ref int RefValue => ref _value;

    public ref readonly int ReadOnlyRefValue => ref _value;

    [AllowNull]
    public string Label
    {
        get => _label ?? Name;
        set => _label = value;
    }

    [MaybeNull]
    public string MaybeLabel => null!;

    [DisallowNull]
    public string? NullableLabel { get; set; }

    public event EventHandler<string>? Changed;

    public abstract double Measure(in double scale, out string? unit);

    public virtual string Describe(bool verbose = false) => Name;

    public override string ToString() => Name;

    [Obsolete("Use Describe instead.")]
    public string Summary() => Name;

    [Obsolete("Removed.", true)]
    [EditorBrowsable(EditorBrowsableState.Never)]
    public void Legacy() => Count++;

    public static TResult? Convert<TResult>(Shape shape, Func<Shape, TResult?> selector) where TResult : struct
        => selector(shape);

    public T Pick<T>(IReadOnlyList<T?> items, ref int index) where T : class, IComparable<T>, new()
        => items[index] ?? new T();

    public (int width, int height) Bounds(ReadOnlySpan<char> label) => (label.Length, seed);

    public (int one, int two, int three, int four, int five, int six, int seven, int eight) LongBounds()
        => (1, 2, 3, 4, 5, 6, 7, 8);

    public ref int RefAt() => ref _value;

    public ref readonly int ReadOnlyRefAt() => ref _value;

    public int Observe(ref readonly string? text) => text?.Length ?? 0;

    public static bool TryName([NotNullWhen(true)] out string? name)
    {
        name = "shape";
        return true;
    }

    public static bool TryMaybe([MaybeNullWhen(false)] out string name)
    {
        name = null!;
        return false;
    }

    public static void Consume([NotNull] ref string? value)
    {
        value ??= "value";
    }

    public static void Stop([DoesNotReturnIf(true)] bool condition)
    {
        if (condition)
            throw new InvalidOperationException();
    }

    [return: NotNullIfNotNull(nameof(value))]
    public static string? Echo(string? value) => value;

    [MemberNotNull(nameof(_label))]
    public void InitializeLabel() => _label = Name;

    [MemberNotNullWhen(true, nameof(_label))]
    public bool EnsureLabel()
    {
        _label ??= Name;
        return true;
    }

    [DoesNotReturn]
    public static void Fail() => throw new InvalidOperationException();

    public static void Defaults(
        decimal ratio = 1.25m,
        double nan = double.NaN,
        char slash = '\\',
        string text = "line\n")
    {
    }

    public static Shape operator +(Shape left, Shape right) => left;

    public static implicit operator string(Shape shape) => shape.Name;

    protected internal virtual void Reset() => Changed?.Invoke(this, Name);

    protected abstract void Validate();

    internal void NotSurface() => Validate();
}

public sealed record Point(int X, int Y)
{
    public double Distance(Point? other = null) => other is null ? 0 : X - other.X;
}

public readonly record struct Size(double Width, double Height);

public delegate bool ShapeFilter<in TShape>(TShape shape, params object[] tags) where TShape : Shape;

public delegate ref readonly int RefReader();

public static class ShapeExtensions
{
    public static int CountAll(this IEnumerable<Shape> shapes, params ReadOnlySpan<int> weights)
        => shapes.Count() + weights.Length;
}

public class Outer
{
    public sealed class Inner
    {
        public Inner()
        {
        }
    }

    public enum Kind : ulong
    {
        Big = 18446744073709551615,
    }
}

public class GenericOuter<TOuter> where TOuter : notnull
{
    public TOuter OuterValue { get; set; } = default!;

    public class Inner<TInner> where TInner : unmanaged
    {
        public TInner InnerValue { get; set; }
    }

    protected class ProtectedNested
    {
        protected virtual void Hook()
        {
        }
    }

    protected internal class ProtectedInternalNested
    {
    }

    private protected class PrivateProtectedNested
    {
    }
}

public class ConstraintCases<TClass, TNullableClass, TNotNull, TStruct, TUnmanaged, TNew>
    where TClass : class
    where TNullableClass : class?
    where TNotNull : notnull
    where TStruct : struct
    where TUnmanaged : unmanaged
    where TNew : new()
{
}

[Experimental("KATFIX001")]
public class ExperimentalType
{
}

public class RequiredOwner
{
    public required string Name;

    [SetsRequiredMembers]
    public RequiredOwner()
    {
        Name = "ready";
    }
}
