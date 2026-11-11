using System.Reflection;
using Contract = KatLang.Tests.NativeRecordEqualityTests.GeneratedRecordContract;

namespace KatLang.Tests;

/// <summary>
/// NATIVE RECORD EQUALITY AND HASHING OF ERROR CONTEXT FRAMES
/// (docs/design/language-rules/evaluator-and-hosting.md § The evaluation-error taxonomy, C# RECORD
/// OPERATIONS ON CONTEXT FRAMES). <see cref="EvalError.WithContext"/> is the one error record that
/// holds an error; its synthesized <c>Equals</c> and <c>GetHashCode</c> followed
/// <see cref="EvalError.WithContext.Inner"/> once per frame, and are now loops. This class holds
/// them to the synthesized contract — restated over reflection, never the members under test —
/// on every native route, pins the inventory, and runs a 200,000-frame chain (also on a 1 MiB
/// thread in a child process by <see cref="AstStructuralDepthProcessTests"/>).
/// </summary>
public class EvalErrorRecordEqualityTests
{
    private const BindingFlags DeclaredInstance =
        BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly;

    private static readonly SourceSpan SpanA = new(1, 2, 1, 3);
    private static readonly SourceSpan SpanB = new(2, 1, 2, 2);

    // ── The synthesized contract of a frame, over reflection (the oracle) ────

    // Reference identity, else the same record kind and every instance field, base record first,
    // in declaration order, each through its default comparer. The inner error is expanded here,
    // so the hand-written members of a frame are never their own judge; every other error kind
    // answers for itself (those members are still synthesized, or shallow).
    private static bool GeneratedEquals(EvalError? left, EvalError? right)
    {
        if (left is null || right is null)
            return left is null && right is null;
        if (ReferenceEquals(left, right))
            return true;
        if (left.GetType() != right.GetType())
            return false;
        if (left is not EvalError.WithContext)
            return left.Equals(right);

        foreach (var field in Contract.Fields(typeof(EvalError.WithContext)))
        {
            var (leftValue, rightValue) = (field.GetValue(left), field.GetValue(right));
            var equal = field.FieldType == typeof(EvalError)
                ? GeneratedEquals((EvalError?)leftValue, (EvalError?)rightValue)
                : Contract.Equals(field.FieldType, leftValue, rightValue);
            if (!equal)
                return false;
        }

        return true;
    }

    // The equality contract's hash, then every field folded in with the synthesized multiplier.
    private static int GeneratedHash(EvalError? error)
    {
        if (error is not EvalError.WithContext frame)
            return error?.GetHashCode() ?? 0;

        var hash = EqualityComparer<Type>.Default.GetHashCode(typeof(EvalError.WithContext));
        foreach (var field in Contract.Fields(typeof(EvalError.WithContext)))
        {
            var value = field.GetValue(frame);
            var fieldHash = field.FieldType == typeof(EvalError)
                ? GeneratedHash((EvalError?)value)
                : Contract.Hash(field.FieldType, value);
            hash = unchecked(hash * -1521134295 + fieldHash);
        }

        return hash;
    }

    private static EvalError[] Samples()
    {
        var unknown = new EvalError.UnknownName("x");
        var inner = new EvalError.WithContext(new CallContext("inner"), unknown);
        var outer = new EvalError.WithContext(new CallContext("outer"), inner) { Span = SpanA };
        return
        [
            unknown,
            new EvalError.UnknownName("x"),
            new EvalError.UnknownName("y"),
            inner,
            inner with { },
            outer,
            outer with { }, // Shares its inner frame by reference.
            new EvalError.WithContext(new CallContext("outer"), inner with { IsProjectionFailure = true })
            {
                Span = SpanA,
                IsProjectionFailure = true, // The runtime slot is equality-transparent.
            },
            outer with { Span = null },
            outer with { Span = SpanB },
            new EvalError.WithContext(outer.Context, inner) { Span = SpanA }, // Another context KIND with the same text.
            new EvalError.WithContext(new CallContext("other"), inner) { Span = SpanA },
            outer.WithInner(inner with { Span = SpanB }),
            outer.WithInner(unknown), // A shorter chain.
            outer.WithInner(new EvalError.WithContext(new CallContext("inner"), new EvalError.UnknownName("y"))),
            outer.WithInner(new EvalError.WithContext(new CallContext("inner"), new EvalError.WithContext("deeper", unknown))),
            // Host-built frames no evaluation produces: a null inner error, a null context.
            new EvalError.WithContext("empty", null!),
            new EvalError.WithContext("empty", null!),
            new EvalError.WithContext(new CallContext("outer"), new EvalError.WithContext("empty", null!)) { Span = SpanA },
            new EvalError.WithContext((ErrorContext)null!, unknown),
            new EvalError.WithContext((ErrorContext)null!, new EvalError.UnknownName("x")),
        ];
    }

    [Fact]
    public void WithContext_KeepsTheSynthesizedContract_OnEveryNativeRoute()
    {
        // Messages name positions only: the text of a frame around a null inner error is itself
        // an exception, and a record's text is not this subject.
        var samples = Samples();
        var equalPairs = 0;
        for (var i = 0; i < samples.Length; i++)
        {
            var left = samples[i];
            var hash = GeneratedHash(left);
            Assert.True(hash == left.GetHashCode(), $"GetHashCode of samples[{i}]");
            Assert.True(hash == EqualityComparer<EvalError>.Default.GetHashCode(left), $"default comparer hash of samples[{i}]");
            Assert.False(left.Equals((EvalError?)null), $"samples[{i}] equals no null");
            Assert.False(left.Equals((object?)null), $"samples[{i}] equals no null object");
            if (left is EvalError.WithContext nullCheck)
                Assert.False(nullCheck.Equals((EvalError.WithContext?)null), $"samples[{i}] equals no null frame");

            for (var j = 0; j < samples.Length; j++)
            {
                var right = samples[j];
                var expected = GeneratedEquals(left, right);
                var where = $"samples[{i}] vs samples[{j}], expected {expected}";
                Assert.True(expected == left.Equals(right), "Equals(EvalError): " + where);
                Assert.True(expected == left.Equals((object)right), "Equals(object): " + where);
                Assert.True(expected == Equals(left, right), "object.Equals(a, b): " + where);
                Assert.True(expected == (left == right), "==: " + where);
                Assert.True(expected != (left != right), "!=: " + where);
                Assert.True(expected == EqualityComparer<EvalError>.Default.Equals(left, right), "default comparer: " + where);
                if (left is EvalError.WithContext leftFrame && right is EvalError.WithContext rightFrame)
                {
                    Assert.True(expected == leftFrame.Equals(rightFrame), "Equals(WithContext): " + where);
                    Assert.True(expected == (leftFrame == rightFrame), "WithContext ==: " + where);
                    Assert.True(expected != (leftFrame != rightFrame), "WithContext !=: " + where);
                }

                if (expected)
                {
                    Assert.True(left.GetHashCode() == right.GetHashCode(), "equal errors hash alike: " + where);
                    if (i != j)
                        equalPairs++;
                }
            }
        }

        // The oracle is not vacuous: the corpus holds equal pairs of distinct objects and unequal ones.
        Assert.True(equalPairs >= 8, $"{equalPairs} equal ordered pairs of distinct samples");
        Assert.True(equalPairs < samples.Length * (samples.Length - 1) / 4, "most pairs differ");
    }

    [Fact]
    public void WithContext_ComparesTheFieldsTheCompilerCompared()
    {
        // The verdicts a reader expects, stated outright (the differential above derives them).
        var inner = new EvalError.WithContext(new CallContext("inner"), new EvalError.UnknownName("x"));
        var left = new EvalError.WithContext(new CallContext("outer"), inner) { Span = SpanA };
        var equal = new EvalError.WithContext(new CallContext("outer"), inner with { IsProjectionFailure = true })
        {
            Span = left.Span,
            IsProjectionFailure = true,
        };
        var nullInner = new EvalError.WithContext("empty", null!);

        Assert.True(left.Equals(equal) && equal.Equals(left) && left.GetHashCode() == equal.GetHashCode(), "a runtime slot is transparent");
        Assert.False(left.Equals(left with { Span = null }), "the frame's span is compared");
        Assert.False(left.Equals(new EvalError.WithContext(left.Context, inner) { Span = left.Span }), "the context is compared as a record, not as text");
        Assert.False(left.Equals(left.WithInner(inner with { Span = SpanB })), "an inner frame's span is compared");
        Assert.False(left.Equals(left.WithInner(new EvalError.UnknownName("x"))), "a shorter chain differs");
        Assert.False(left.Equals(left.WithInner(new EvalError.WithContext(new CallContext("inner"), inner))), "a longer chain differs");
        Assert.True(nullInner.Equals(nullInner with { }), "two null inner errors are equal");
        Assert.False(nullInner.Equals(left) || left.Equals(nullInner), "a null inner error equals no error");
        Assert.True(new HashSet<EvalError> { left }.Contains(equal), "a hash set finds an equal frame");
    }

    [Fact]
    public void WithContext_IsTheOnlyErrorRecordThatHoldsAnErrorOrAContext()
    {
        // Synthesized equality, hashing and text recurse through a field whose type is a record
        // of the same family. Among the error and context records that is one field; a second
        // one would bring the recursion back (or need the same treatment) and must fail here.
        Type[] families = [typeof(EvalError), typeof(ErrorContext)];
        var holders = typeof(EvalError).Assembly.GetTypes()
            .Where(type => families.Any(family => family.IsAssignableFrom(type)))
            .SelectMany(static type => type.GetFields(DeclaredInstance).Select(field => (Type: type, Field: field)))
            .Where(member => families.Any(family => family.IsAssignableFrom(member.Field.FieldType)))
            .Select(static member => $"{member.Type.FullName}.{member.Field.Name}")
            .OrderBy(static name => name, StringComparer.Ordinal)
            .ToArray();
        string[] expected =
        [
            "KatLang.EvalError+WithContext.<ErrorContext>k__BackingField",
            "KatLang.EvalError+WithContext.<Inner>k__BackingField",
        ];
        Assert.Equal(expected, holders);

        // And the frame's own fields are exactly the two its hand-written members read after the
        // base record's part (the differential's hash would also move with a third).
        string[] ownFields = ["<ErrorContext>k__BackingField", "<Inner>k__BackingField"];
        Assert.Equal(ownFields, typeof(EvalError.WithContext).GetFields(DeclaredInstance).Select(static field => field.Name).ToArray());
    }

    [Fact]
    public void TwoHundredThousandFrames_EqualAndHashWithoutRecursion() => AssertDeepEqualityAndHashing();

    /// <summary>
    /// Every native route over 200,000 frames: an equal chain, one that differs at the terminal
    /// error, and one above a shared deep half. Assertion messages are constants.
    /// </summary>
    internal static void AssertDeepEqualityAndHashing()
    {
        const int depth = 200_000;
        var left = Chain(new EvalError.UnknownName("x"), depth);
        var equal = Chain(new EvalError.UnknownName("x"), depth);
        var different = Chain(new EvalError.UnknownName("y"), depth);
        EvalError baseTyped = left;
        Assert.True(left.Equals(equal) && equal.Equals(left), "Equals(WithContext), equal");
        Assert.True(left == equal && !(left != equal), "operators, equal");
        Assert.True(baseTyped.Equals(equal) && baseTyped.Equals((object)equal), "Equals(EvalError) and Equals(object), equal");
        Assert.True(EqualityComparer<EvalError>.Default.Equals(left, equal), "default comparer, equal");
        Assert.False(left.Equals(different), "the terminal error differs");
        Assert.True(left != different && !baseTyped.Equals(different), "operators and Equals(EvalError), different");

        var hash = left.GetHashCode();
        Assert.True(hash == left.GetHashCode(), "repeated hash");
        Assert.True(hash == EqualityComparer<EvalError>.Default.GetHashCode(equal), "equal chains hash alike");
        _ = different.GetHashCode();
        Assert.True(new HashSet<EvalError> { left }.Contains(equal), "HashSet finds an equal deep key");
        var map = new Dictionary<EvalError, int> { [left] = 1 };
        Assert.True(map.ContainsKey(equal), "Dictionary lookup through an equal deep key");
        Assert.False(map.ContainsKey(different), "Dictionary misses an unequal deep key");

        // Two chains over ONE shared deep half: equal to each other (the walk stops at the shared
        // frame) and to the unshared chain they denote.
        var shared = Chain(new EvalError.UnknownName("x"), depth / 2);
        var overShared = Chain(shared, depth / 2);
        Assert.True(overShared.Equals(Chain(shared, depth / 2)), "equal above a shared half");
        Assert.True(overShared.Equals(left) && overShared.GetHashCode() == hash, "a chain over a shared half is the chain it denotes");
        Assert.False(overShared.Equals(different), "unequal below a shared half");

        // The classifications every frame reports are the terminal error's.
        Assert.True(left.Code == KatLangErrorCode.UnknownName && !left.IsResourceLimit, "classification through 200,000 frames");

        static EvalError.WithContext Chain(EvalError leaf, int frames)
        {
            var frame = new EvalError.WithContext("frame", leaf);
            for (var level = 1; level < frames; level++)
                frame = new EvalError.WithContext("frame", frame);
            return frame;
        }
    }
}
