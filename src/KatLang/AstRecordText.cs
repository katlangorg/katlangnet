using System.Runtime.CompilerServices;
using System.Text;

namespace KatLang;

/// <summary>
/// STACK-SAFE RECORD TEXT. The compiler synthesizes a record's <c>ToString</c> as a
/// <c>PrintMembers</c> call that appends every public member through that member's own
/// <c>ToString</c>, so a member whose type is itself a record recursed on the caller's stack, once
/// per level of a host-built chain, and built one intermediate string per level. The records with
/// such a member are the ones <see cref="RecordGraphEquality"/> walks — every <see cref="Expr"/>
/// variant that holds an expression or an algorithm, the three scope-owning
/// <see cref="Algorithm"/> variants and <see cref="ScopeCtx"/> — and each declares
/// <c>PrintMembers</c> itself and delegates here. <c>ToString</c> is still synthesized: it writes the
/// root's name and braces around this call.
///
/// <para><b>The layout is the generated one, unchanged.</b> Members appear in the synthesized
/// order — the base record's public members, then the record's own in declaration order, computed
/// properties such as <see cref="Expr.DotCall.EffectiveLexicalFallback"/> and the parameter
/// projections of <see cref="Algorithm.User"/> included — each as <c>Name = value</c> through the
/// member's own <c>ToString</c> (a null member prints as empty text). A collection prints as that
/// collection prints itself and is never entered.</para>
///
/// <para><b>Shared nodes and cycles.</b> Text is per occurrence by definition: a child reached
/// through two members is written twice, so the work is the size of the text. A record that
/// reaches itself through the record-valued members this writer follows (a reflection-forged
/// cycle) is refused instead of being written forever.</para>
/// </summary>
internal static class AstRecordText
{
    /// <summary>
    /// Appends the members of <paramref name="node"/> as its synthesized <c>PrintMembers</c> would,
    /// writing nested records into the same builder with an explicit stack of (record, next
    /// segment) continuations.
    /// </summary>
    internal static bool PrintMembers(StringBuilder builder, object node)
    {
        // Caller-owned collections can re-enter ToString from their own formatter. Retain
        // the compiler's stack check at entry even though the record walk itself is iterative.
        RuntimeHelpers.EnsureSufficientExecutionStack();

        Stack<(object Node, int Segment)>? parents = null;
        // The records being written, root first: a child already on this path is a cycle.
        HashSet<object>? active = null;
        var segment = 0;

        while (true)
        {
            var child = PrintSegment(builder, node, segment);
            if (child is not null)
            {
                segment++;
                if (WritesMembersHere(child))
                {
                    parents ??= new();
                    active ??= new HashSet<object>(ReferenceEqualityComparer.Instance) { node };
                    if (!active.Add(child))
                        throw CycleRefused();

                    parents.Push((node, segment));
                    // What the child's synthesized ToString writes around its members.
                    builder.Append(child.GetType().Name).Append(" { ");
                    (node, segment) = (child, 0);
                }
                else
                {
                    builder.Append(child);
                }

                continue;
            }

            if (parents is null || !parents.TryPop(out var parent))
                return true;

            active!.Remove(node);
            builder.Append(" }");
            (node, segment) = parent;
        }
    }

    // Exactly the records whose PrintMembers delegates to this writer: the ones with a
    // record-valued field for equality. Any other member value is written by its own ToString.
    private static bool WritesMembersHere(object value) => value switch
    {
        Expr expr => expr.RecordChildCount() != 0,
        Algorithm algorithm => algorithm.RecordChildCount() != 0,
        ScopeCtx => true,
        _ => false,
    };

    // One segment: the members in declaration order up to and including the label of the next
    // record-valued member, whose value is returned for the caller to write (the empty string for
    // a null member, which prints as nothing). Null means every member of the record is written.
    private static object? PrintSegment(StringBuilder builder, object node, int segment)
    {
        if (segment == 0 && node is Expr expr)
            Member(builder, "Span = ", expr.Span);

        switch (node, segment)
        {
            case (Expr.Unary unary, 0):
                Member(builder, ", Op = ", unary.Op);
                return Child(builder, ", Operand = ", unary.Operand);
            case (Expr.Binary binary, 0):
                Member(builder, ", Op = ", binary.Op);
                return Child(builder, ", Left = ", binary.Left);
            case (Expr.Binary binary, 1):
                return Child(builder, ", Right = ", binary.Right);
            case (Expr.Comparison comparison, 0):
                return Child(builder, ", First = ", comparison.First);
            case (Expr.Comparison comparison, 1):
                Member(builder, ", Links = ", comparison.Links);
                break;
            case (Expr.Index index, 0):
                return Child(builder, ", Target = ", index.Target);
            case (Expr.Index index, 1):
                Member(builder, ", Selectors = ", index.Selectors);
                break;
            case (Expr.SequenceConstruct sequence, 0):
                return Child(builder, ", Left = ", sequence.Left);
            case (Expr.SequenceConstruct sequence, 1):
                return Child(builder, ", Right = ", sequence.Right);
            case (Expr.SequenceSpread spread, 0):
                return Child(builder, ", Operand = ", spread.Operand);
            case (Expr.SequenceSpread spread, 1):
                Member(builder, ", SpreadMarkerSpan = ", spread.SpreadMarkerSpan);
                break;
            case (Expr.DotCall dot, 0):
                return Child(builder, ", Target = ", dot.Target);
            case (Expr.DotCall dot, 1):
                Member(builder, ", Name = ", dot.Name);
                Member(builder, ", Args = ", dot.Args);
                Member(builder, ", MemberSpan = ", dot.MemberSpan);
                return Child(builder, ", LexicalFallback = ", dot.LexicalFallback);
            case (Expr.DotCall dot, 2):
                return Child(builder, ", EffectiveLexicalFallback = ", dot.EffectiveLexicalFallback);
            case (Expr.Grace grace, 0):
                return Child(builder, ", Inner = ", grace.Inner);
            case (Expr.Grace grace, 1):
                Member(builder, ", Weight = ", grace.Weight);
                break;
            case (Expr.AlgorithmExpr algorithm, 0):
                return Child(builder, ", Algorithm = ", algorithm.Algorithm);
            case (Expr.Call call, 0):
                return Child(builder, ", Function = ", call.Function);
            case (Expr.Call call, 1):
                Member(builder, ", Args = ", call.Args);
                break;
            case (Algorithm.User user, 0):
                return Child(builder, "Parent = ", user.Parent);
            case (Algorithm.User user, 1):
                Member(builder, ", ParameterPatterns = ", user.ParameterPatterns);
                Member(builder, ", Parameters = ", user.Parameters);
                Member(builder, ", Params = ", user.Params);
                Member(builder, ", Opens = ", user.Opens);
                Member(builder, ", Properties = ", user.Properties);
                Member(builder, ", Output = ", user.Output);
                Member(builder, ", HasExplicitParameterList = ", user.HasExplicitParameterList);
                break;
            case (Algorithm.Conditional conditional, 0):
                return Child(builder, "Parent = ", conditional.Parent);
            case (Algorithm.Conditional conditional, 1):
                Member(builder, ", Opens = ", conditional.Opens);
                Member(builder, ", Branches = ", conditional.Branches);
                break;
            case (Algorithm.Alias alias, 0):
                Member(builder, "IsReference = ", alias.IsReference);
                return Child(builder, ", Parent = ", alias.Parent);
            case (Algorithm.Alias alias, 1):
                Member(builder, ", Opens = ", alias.Opens);
                Member(builder, ", Properties = ", alias.Properties);
                return Child(builder, ", Target = ", alias.Target);
            case (ScopeCtx scope, 0):
                return Child(builder, "Parent = ", scope.Parent);
            case (ScopeCtx scope, 1):
                Member(builder, ", Opens = ", scope.Opens);
                Member(builder, ", Properties = ", scope.Properties);
                Member(builder, ", Parameters = ", scope.Parameters);
                break;
            default:
                // A record above has a case for segment 0 and ends at its first segment without
                // one. A record with no case at all is one this writer was never taught: it must
                // not print as an empty member list.
                if (segment == 0)
                    throw NotAPrintedRecord(node);
                break;
        }

        return null;
    }

    private static void Member(StringBuilder builder, string label, object? value)
        => builder.Append(label).Append(value);

    private static object Child(StringBuilder builder, string label, object? child)
    {
        builder.Append(label);
        return child ?? string.Empty;
    }

    private static InvalidOperationException NotAPrintedRecord(object node)
        => new($"{node.GetType().Name} is not a record whose members this writer prints.");

    private static InvalidOperationException CycleRefused()
        => new("A record reaches itself through its own printed members (a reference cycle). "
            + "Record text is defined for acyclic record graphs only.");
}
