namespace KatLang;

/// <summary>
/// The ONE storage shape for state a record CARRIES without it being part of the
/// record's structure: an algorithm's declaration token and deferred module region
/// (<see cref="Algorithm.Declaration"/>, <see cref="Algorithm.DeferredRegion"/>) and
/// the diagnostic provenance notes of inferred parameters
/// (<see cref="ParameterDeclaration.InferredProvenance"/>,
/// <see cref="CaptureParameterPattern.InferredProvenance"/>,
/// <see cref="Expr.DotCall.InferredFallbackProvenance"/>,
/// <see cref="EvalError.ArityMismatch.InferredImplicitParameters"/>,
/// <see cref="EvalError.UnresolvedImplicitParams.InferredImplicitParameters"/>).
/// <para>Declared as a private field of the carrying record and exposed through an
/// internal init-only property. The record's SYNTHESIZED copy constructor copies
/// the one reference like any other field, so every <c>with</c> copy is a view of
/// the same state object with no registration step and no hand-written copy
/// constructor to keep in step — a carrier never declares one. Only the SLOT is
/// equality-transparent (every slot equals every other and hashes to 0), so the
/// synthesized record equality, hashing, and printing stay exactly the structural
/// identity; the value exposed through it keeps its own ordinary semantics
/// (reference identity for a token or a note, whatever <c>Equals</c> it defines).
/// Keeping the exclusion here also leaves the compiler responsible for comparing
/// and copying every structural field of the carrier, including any added later.
/// A default slot carries <c>default(T)</c> — null for every reference payload.</para>
/// </summary>
internal readonly struct RuntimeStateSlot<T>(T value) : IEquatable<RuntimeStateSlot<T>>
{
    internal T Value { get; } = value;

    public bool Equals(RuntimeStateSlot<T> other) => true;

    public override bool Equals(object? obj) => obj is RuntimeStateSlot<T>;

    public override int GetHashCode() => 0;
}
