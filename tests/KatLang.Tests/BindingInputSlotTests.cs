using System.Reflection;
using KatLang.Runtime;

namespace KatLang.Tests;

public class BindingInputSlotTests
{
    [Fact]
    public void FromUserCallItem_ValueOnlySlot_PreservesValue()
    {
        var value = Atom(10m);

        var slot = BindingInputSlot.FromUserCallItem(value, algorithm: null, valueError: null);

        Assert.Same(value, slot.Value);
        Assert.Null(slot.Algorithm);
        Assert.Null(slot.ValueError);
    }

    [Fact]
    public void FromUserCallItem_ValueAndAlgorithmSlot_PreservesAlgorithm()
    {
        var value = Atom(20m);
        var algorithm = SimpleAlgorithm();

        var slot = BindingInputSlot.FromUserCallItem(value, algorithm, valueError: null);

        Assert.Same(value, slot.Value);
        Assert.Same(algorithm, slot.Algorithm);
        Assert.Null(slot.ValueError);
    }

    [Fact]
    public void FromUserCallItem_AlgorithmAndValueErrorSlot_PreservesChannels()
    {
        var algorithm = SimpleAlgorithm();
        var error = new EvalError.UnknownName("missing");

        var slot = BindingInputSlot.FromUserCallItem(value: null, algorithm, error);

        Assert.Null(slot.Value);
        Assert.Same(algorithm, slot.Algorithm);
        Assert.Same(error, slot.ValueError);
    }

    [Fact]
    public void FromUserCallItem_ErrorOnlySlot_IsRepresentable()
    {
        var error = new EvalError.DivByZero();

        var slot = BindingInputSlot.FromUserCallItem(value: null, algorithm: null, error);

        Assert.Null(slot.Value);
        Assert.Null(slot.Algorithm);
        Assert.Same(error, slot.ValueError);
    }

    [Fact]
    public void FromEvaluatedValue_LoopEvaluatedSlot_IsValueOnly()
    {
        var value = Atom(30m);

        var slot = BindingInputSlot.FromEvaluatedValue(value);

        Assert.Same(value, slot.Value);
        Assert.Null(slot.Algorithm);
        Assert.Null(slot.ValueError);
    }

    [Fact]
    public void BindingInputSlot_DoesNotDeclareBehaviorLikePublicInstanceMethods()
    {
        string[] behaviorVerbs = ["Bind", "Apply", "Dispatch", "Resolve", "Evaluate", "Validate", "Match"];
        var declaredPublicInstanceMethods = typeof(BindingInputSlot).GetMethods(
            BindingFlags.Public | BindingFlags.Instance | BindingFlags.DeclaredOnly);

        var behaviorMethods = declaredPublicInstanceMethods
            .Where(method => behaviorVerbs.Any(verb =>
                method.Name.StartsWith(verb, StringComparison.Ordinal)
                || method.Name.Contains(verb, StringComparison.Ordinal)))
            .Select(static method => method.Name)
            .ToArray();

        Assert.Empty(behaviorMethods);
    }

    [Fact]
    public void ValueOnlySlots_CanRepresentPrefixVariadicSuffixShape()
    {
        List<BindingInputSlot> slots =
        [
            BindingInputSlot.FromEvaluatedValue(Atom(10m)),
            BindingInputSlot.FromEvaluatedValue(Atom(20m)),
            BindingInputSlot.FromEvaluatedValue(Atom(30m)),
            BindingInputSlot.FromEvaluatedValue(Atom(40m)),
        ];

        Assert.Equal(4, slots.Count);
        Assert.All(slots, AssertValueOnly);
        Assert.Equal([10m, 20m, 30m, 40m], AtomValues(slots));
    }

    [Fact]
    public void ValueOnlySlots_CanRepresentCountedCaptureInputsWithoutCountedResult()
    {
        List<BindingInputSlot> slots =
        [
            BindingInputSlot.FromEvaluatedValue(Atom(7m)),
            BindingInputSlot.FromEvaluatedValue(Atom(8m)),
            BindingInputSlot.FromEvaluatedValue(Atom(9m)),
        ];

        Assert.Equal(3, slots.Count);
        Assert.All(slots, AssertValueOnly);
        Assert.Equal([7m, 8m, 9m], AtomValues(slots));
    }

    private static Result.Atom Atom(decimal value) => new(value);

    private static Algorithm SimpleAlgorithm()
        => new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: [new Expr.Num(1m)]);

    private static void AssertValueOnly(BindingInputSlot slot)
    {
        Assert.NotNull(slot.Value);
        Assert.Null(slot.Algorithm);
        Assert.Null(slot.ValueError);
    }

    private static decimal[] AtomValues(IEnumerable<BindingInputSlot> slots)
        => slots
            .Select(static slot => Assert.IsType<Result.Atom>(slot.Value).Value)
            .ToArray();
}