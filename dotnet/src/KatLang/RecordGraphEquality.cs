using System.Runtime.InteropServices;

namespace KatLang;

/// <summary>
/// STACK-SAFE NATIVE RECORD EQUALITY AND HASHING. The C# compiler synthesizes a
/// record's <c>Equals</c> and <c>GetHashCode</c> as one call per field through
/// <c>EqualityComparer&lt;TField&gt;.Default</c>, so a field whose type is itself a record recurses on
/// the caller's stack: once per level of an expression chain, of a scope's parent chain, or of an
/// alias target. A host may build such a chain far deeper than any stack (the evaluator's
/// structural gate applies to a RUN, not to a record), and a <see cref="StackOverflowException"/>
/// cannot be caught. The records with such a field — every <see cref="Expr"/> variant that holds an
/// expression or an algorithm, the three scope-owning <see cref="Algorithm"/> variants and
/// <see cref="ScopeCtx"/> — therefore declare <c>Equals(T)</c> and <c>GetHashCode()</c> themselves
/// and delegate to this walk. Every other native route (<c>Equals(object)</c>, the base-typed
/// <c>Equals</c>, <c>==</c>, <c>!=</c>, the default comparer, hash sets and dictionaries) is still
/// synthesized and ends in those two members.
///
/// <para><b>The contract is the generated one, unchanged.</b> A record describes itself as the
/// compiler would compare it: its record-valued fields in declaration order
/// (<c>RecordChildCount</c>, <c>RecordChild</c>) and, between them, its remaining fields in
/// declaration order (<c>RecordFieldsEqual</c> per segment; <c>RecordHashStart</c> and
/// <c>RecordHashAfterChild</c> for the hash), each through <see cref="FieldEquals{T}"/> and
/// <see cref="Combine{T}"/> — the very <c>EqualityComparer&lt;TField&gt;.Default</c> calls and the
/// very multiplier of the synthesized members — with the base record's part left to the compiler
/// (<c>base.Equals</c>, <c>base.GetHashCode</c>). So equality is still reference identity, else the
/// same record kind and every field: source spans and metadata compared, lists and bundles by
/// their own equality (reference identity unless a host type defines another), state slots
/// transparent; and a record's hash is the value the synthesized member returned. This is NOT
/// language equality: <see cref="Result.ValueComparer"/>, <c>ParameterPattern.ContractComparer</c>
/// and the pattern match-equivalence index are separate and untouched. Field comparisons and
/// hashing run in the generated order, including calls to a host collection's own methods.</para>
///
/// <para><b>Shared nodes.</b> A host graph may reach one record through many parents. Within ONE
/// top-level operation each ordered pair of record references is compared at most once and each
/// record is hashed at most once: a pair met again is already proven equal (an unequal pair ends
/// the operation), and a record met again has its hash. The work is therefore proportional to the
/// distinct records (pairs) and their fields, never to the paths that reach them; the generated
/// members did the same work once per path. The memo is keyed by reference identity, allocated
/// with the explicit stack at the first descent below the root's own children — a record whose
/// record-valued fields hold only leaves or nulls needs neither, and a one-child root can use
/// the same leaf walk for its child when it has that shape — and discarded with the call.
/// Equality also skips identical child references; hashing must still traverse their descendants.
/// Nothing is stored on a record, so a caller-owned collection edited between two
/// operations is read afresh by the second.</para>
///
/// <para><b>Cycles.</b> A record-valued field is assigned from an existing record, so no public
/// construction makes a record reach itself through such fields; host reference cycles run through
/// caller-owned lists, which records compare as lists and never enter. A cycle forged by
/// reflection had no answer before (it overflowed the stack) and is refused here with an
/// <see cref="InvalidOperationException"/> instead of being walked forever.</para>
/// </summary>
internal static class RecordGraphEquality
{
    /// <summary>The multiplier of compiler-synthesized record hashing.</summary>
    private const int HashMultiplier = -1521134295;

    // Small first allocations: an ordinary expression is a few records deep, and a memo sized for it
    // is one table instead of the three a growing dictionary would allocate on the way there.
    private const int InitialStackCapacity = 8;

    private const int InitialMemoCapacity = 16;

    /// <summary>One field as synthesized record equality compares it.</summary>
    internal static bool FieldEquals<T>(T left, T right) => EqualityComparer<T>.Default.Equals(left, right);

    /// <summary>One field folded into a hash as synthesized record hashing folds it (a null field hashes to 0).</summary>
    internal static int Combine<T>(int hash, T field)
        => unchecked(hash * HashMultiplier + EqualityComparer<T>.Default.GetHashCode(field!));

    /// <summary>A record-valued field's completed hash folded in at that field's position (0 for a null field).</summary>
    internal static int CombineChild(int hash, int childHash) => unchecked(hash * HashMultiplier + childHash);

    /// <summary>
    /// Whether two records of the SAME kind, neither null nor one object, are equal under the
    /// generated record contract. Called by a record's own <c>Equals(T)</c> after its reference
    /// test.
    /// </summary>
    internal static bool AreEqual(object left, object right)
    {
        EqualityFrame[]? stack = null;
        var depth = 0;
        // false: the pair is being compared (it is on the stack); true: proven equal.
        Dictionary<ReferencePair, bool>? pairs = null;
        // A root has at most two record children. Keep its first shallow pair inline, both to
        // reuse a shared leaf without allocating and to seed the memo if the next child descends.
        object? shallowLeft = null;
        object? shallowRight = null;
        var segment = 0;
        var childCount = ChildCount(left);
        while (true)
        {
            if (!FieldsEqual(left, right, segment))
                return false;

            if (segment < childCount)
            {
                var leftChild = Child(left, segment);
                var rightChild = Child(right, segment);
                segment++;
                // EqualityComparer<T>.Default over a record: nulls first, then the left record's
                // Equals, which starts with the reference test and answers only for its own kind.
                if (ReferenceEquals(leftChild, rightChild))
                    continue;
                if (leftChild is null || rightChild is null || leftChild.GetType() != rightChild.GetType())
                    return false;

                var nested = ChildCount(leftChild);
                if (nested == 0)
                {
                    // Shallow records still belong to the DAG: a host-defined collection can
                    // make their equality expensive, so memoize them too once the walk has state.
                    var pair = new ReferencePair(leftChild, rightChild);
                    if (pairs is not null ? pairs.ContainsKey(pair)
                        : ReferenceEquals(leftChild, shallowLeft) && ReferenceEquals(rightChild, shallowRight))
                        continue;
                    if (!leftChild.Equals(rightChild))
                        return false;
                    if (pairs is not null)
                        pairs.Add(pair, true);
                    else
                        (shallowLeft, shallowRight) = (leftChild, rightChild);
                    continue;
                }

                if (pairs is null)
                {
                    // The first descent is always from the root pair. A root with ONE record-valued
                    // field over a record whose own children are leaves or nulls needs no state:
                    // that child's members are the leaf walk above (one bounded native call, never
                    // a descent: an unequal kind on the right ends it), and the root has no second
                    // edge that could meet one of the child's pairs again.
                    if (childCount == 1 && ChildrenAreLeaves(leftChild, nested))
                        return leftChild.Equals(rightChild) && FieldsEqual(left, right, segment);

                    pairs = new Dictionary<ReferencePair, bool>(InitialMemoCapacity) { [new ReferencePair(left, right)] = false };
                    if (shallowLeft is not null)
                        pairs.Add(new ReferencePair(shallowLeft, shallowRight!), true);
                    stack = new EqualityFrame[InitialStackCapacity];
                }

                ref var proven = ref CollectionsMarshal.GetValueRefOrAddDefault(pairs, new ReferencePair(leftChild, rightChild), out var met);
                if (met)
                {
                    if (proven)
                        continue;
                    throw CycleRefused();
                }

                if (depth == stack!.Length)
                    Array.Resize(ref stack, depth * 2);
                stack[depth++] = new EqualityFrame(left, right, segment, childCount);
                (left, right, segment, childCount) = (leftChild, rightChild, 0, nested);
                continue;
            }

            if (depth == 0)
                return true;

            pairs![new ReferencePair(left, right)] = true;
            ref var frame = ref stack![--depth];
            (left, right, segment, childCount) = (frame.Left, frame.Right, frame.Segment, frame.ChildCount);
            frame = default;
        }
    }

    /// <summary>
    /// The hash the generated record contract gives <paramref name="node"/>. Called by a record's
    /// own <c>GetHashCode()</c>.
    /// </summary>
    internal static int HashOf(object node)
    {
        HashFrame[]? stack = null;
        var depth = 0;
        // null: the record is being hashed (it is on the stack); otherwise its completed hash.
        Dictionary<object, int?>? hashes = null;
        object? shallowNode = null;
        var shallowHash = 0;
        var index = 0;
        var childCount = ChildCount(node);
        var hash = HashStart(node);
        while (true)
        {
            if (index < childCount)
            {
                var child = Child(node, index);
                int childHash;
                if (child is null)
                {
                    childHash = 0;
                }
                else
                {
                    var nested = ChildCount(child);
                    if (nested == 0)
                    {
                        if (hashes is not null)
                        {
                            ref var knownLeaf = ref CollectionsMarshal.GetValueRefOrAddDefault(hashes, child, out _);
                            knownLeaf ??= child.GetHashCode();
                            childHash = knownLeaf.Value;
                        }
                        else if (ReferenceEquals(child, shallowNode))
                        {
                            childHash = shallowHash;
                        }
                        else
                        {
                            childHash = child.GetHashCode();
                            (shallowNode, shallowHash) = (child, childHash);
                        }
                    }
                    else
                    {
                        if (hashes is null)
                        {
                            // The first descent is always from the root. As in AreEqual: a one-child
                            // root over a record with only leaf children folds that child's own
                            // (stateless) hash and the fields after it, and is done.
                            if (childCount == 1 && ChildrenAreLeaves(child, nested))
                                return HashAfterChild(node, index, hash, child.GetHashCode());

                            hashes = new Dictionary<object, int?>(InitialMemoCapacity, ReferenceEqualityComparer.Instance) { [node] = null };
                            if (shallowNode is not null)
                                hashes.Add(shallowNode, shallowHash);
                            stack = new HashFrame[InitialStackCapacity];
                        }

                        ref var known = ref CollectionsMarshal.GetValueRefOrAddDefault(hashes, child, out var met);
                        if (!met)
                        {
                            if (depth == stack!.Length)
                                Array.Resize(ref stack, depth * 2);
                            stack[depth++] = new HashFrame(node, index, childCount, hash);
                            (node, index, childCount, hash) = (child, 0, nested, HashStart(child));
                            continue;
                        }

                        childHash = known ?? throw CycleRefused();
                    }
                }

                hash = HashAfterChild(node, index, hash, childHash);
                index++;
                continue;
            }

            if (depth == 0)
                return hash;

            hashes![node] = hash;
            var completed = hash;
            ref var frame = ref stack![--depth];
            (node, index, childCount, hash) = (frame.Node, frame.Index, frame.ChildCount, frame.Hash);
            frame = default;
            hash = HashAfterChild(node, index, hash, completed);
            index++;
        }
    }

    // The three record families whose equality follows a record-valued field. They share no base
    // type, so the walk dispatches on the family here; within a family the variant decides.

    private static int ChildCount(object node) => node switch
    {
        Expr expr => expr.RecordChildCount(),
        Algorithm algorithm => algorithm.RecordChildCount(),
        ScopeCtx => ScopeCtx.RecordChildCount,
        _ => throw NotARecordNode(node),
    };

    private static object? Child(object node, int index) => node switch
    {
        Expr expr => expr.RecordChild(index),
        Algorithm algorithm => algorithm.RecordChild(index),
        ScopeCtx scope => scope.Parent,
        _ => throw NotARecordNode(node),
    };

    // Whether every record-valued field of `node` holds a leaf record or null, read from the stored
    // references alone (no field is compared or hashed here). Such a record's own Equals and
    // GetHashCode run this walk without a stack or a memo, keep the generated field order and reuse
    // a leaf that both of its fields hold. A leaf has no record-valued field, so no cycle hides here.
    private static bool ChildrenAreLeaves(object node, int childCount)
    {
        for (var index = 0; index < childCount; index++)
        {
            if (Child(node, index) is { } child && ChildCount(child) != 0)
                return false;
        }

        return true;
    }

    private static bool FieldsEqual(object left, object right, int segment) => left switch
    {
        Expr expr => expr.RecordFieldsEqual((Expr)right, segment),
        Algorithm algorithm => algorithm.RecordFieldsEqual((Algorithm)right, segment),
        ScopeCtx scope => scope.RecordFieldsEqual((ScopeCtx)right, segment),
        _ => throw NotARecordNode(left),
    };

    private static int HashStart(object node) => node switch
    {
        Expr expr => expr.RecordHashStart(),
        Algorithm algorithm => algorithm.RecordHashStart(),
        ScopeCtx => 0,
        _ => throw NotARecordNode(node),
    };

    private static int HashAfterChild(object node, int index, int hash, int childHash) => node switch
    {
        Expr expr => expr.RecordHashAfterChild(index, hash, childHash),
        Algorithm algorithm => algorithm.RecordHashAfterChild(index, hash, childHash),
        ScopeCtx scope => scope.RecordHashAfterParent(childHash),
        _ => throw NotARecordNode(node),
    };

    /// <summary>The failure of a record that declares no record-valued field and was asked for one.</summary>
    internal static InvalidOperationException NoRecordChildren(object node)
        => new($"{node.GetType().Name} has no record-valued field for record equality to follow.");

    private static InvalidOperationException NotARecordNode(object node)
        => new($"{node.GetType().Name} is not a record whose equality follows record-valued fields.");

    private static InvalidOperationException CycleRefused()
        => new("A record reaches itself through its own record-valued fields (a reference cycle). "
            + "Record equality and hashing are defined for acyclic record graphs only.");

    private readonly struct EqualityFrame(object left, object right, int segment, int childCount)
    {
        public readonly object Left = left;
        public readonly object Right = right;
        public readonly int Segment = segment;
        public readonly int ChildCount = childCount;
    }

    private readonly struct HashFrame(object node, int index, int childCount, int hash)
    {
        public readonly object Node = node;
        public readonly int Index = index;
        public readonly int ChildCount = childCount;
        public readonly int Hash = hash;
    }

    // Reference identity of both members: a record's own equality is the question being answered.
    private readonly struct ReferencePair(object left, object right) : IEquatable<ReferencePair>
    {
        private readonly object _left = left;
        private readonly object _right = right;

        public bool Equals(ReferencePair other)
            => ReferenceEquals(_left, other._left) && ReferenceEquals(_right, other._right);

        public override bool Equals(object? obj) => obj is ReferencePair other && Equals(other);

        public override int GetHashCode()
            => HashCode.Combine(
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(_left),
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(_right));
    }
}
