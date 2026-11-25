using System.Numerics;

namespace KatLang;

/// <summary>
/// The Grace movement law (PAR-06; X-49, decided 2026-10-08): how an owner's summed Grace weights
/// reorder its OWN inferred parameters. A weight is a request for adjacent exchanges — each postfix
/// <c>~</c> one exchange toward the end of the list, each prefix <c>~</c> one toward the front — and
/// the parameters make their requests one at a time:
/// <list type="number">
/// <item>every parameter with a POSITIVE weight, from the last-occurring to the first-occurring;</item>
/// <item>then every parameter with a NEGATIVE weight, from the first-occurring to the last-occurring.</item>
/// </list>
/// Rightward movers go first, and in reverse first-occurrence order, so that the mover nearer the
/// end it heads for always moves before the one behind it, so no movement is lost because a
/// same-direction blocker had not had its turn. Equal accumulated weights preserve relative order;
/// a contiguous equal-weight run moves as a unit when every parameter outside that run has zero
/// weight. Other movers can split the run. Leftward movers are taken from the
/// front for the same reason. A rightward mover and a leftward mover can meet only when the
/// rightward one is written first, so running the rightward pass first resolves every such meeting
/// in first-occurrence order.
/// <para>In its one turn a parameter exchanges with its neighbour on the side its weight points to,
/// one unit per exchange, until its remaining weight is zero, it reaches the end of the own list, or
/// the neighbour moves the same way with at least as much REMAINING weight (the patent's strict
/// comparison of current remaining weights). A parameter that is passed keeps its remaining weight,
/// and weight a parameter cannot use — at an end or against such a neighbour — stays with it and
/// keeps blocking a parameter that later pushes the same way no harder (<c>a~~ + b~</c> is
/// <c>(b, a)</c>; <c>~a + b + ~~c</c> is <c>(a, c, b)</c>).</para>
/// <para>The list holds the owner's own names only: forwarded names are appended after it later
/// (PAR-05, PAR-07), so nothing moves across the own/lifted boundary. The turn order comes from the
/// first-occurrence identities and their initial weights, never from spellings, current positions
/// or dictionary enumeration. Each turn makes at most n − 1 exchanges, so a list of n names is
/// settled after at most n(n − 1) exchanges whatever the size of the weights.</para>
/// </summary>
internal static class GraceMovement
{
    /// <summary>
    /// Reorders <paramref name="ownOrder"/> in place — the detector's entry point. See
    /// <see cref="Settle"/> for the arguments.
    /// </summary>
    internal static void Apply(List<string> ownOrder, IReadOnlyDictionary<string, BigInteger> weights)
    {
        if (ownOrder.Count < 2 || weights.Count == 0)
            return;

        var settled = Settle(ownOrder, weights);
        for (var place = 0; place < settled.Order.Length; place++)
            ownOrder[place] = settled.Order[place];
    }

    /// <summary>
    /// Settles <paramref name="ownOrder"/> — the owner's OWN inferred parameters in first semantic
    /// occurrence (PAR-05), each name once — under <paramref name="weights"/>, each name's exact
    /// summed weight (prefix −1, postfix +1 per marker, opposite markers already cancelled; a missing
    /// name weighs zero). Returns the final order and, aligned with it, each name's remaining weight:
    /// the part of its weight it could not use.
    /// </summary>
    internal static Settlement Settle(IReadOnlyList<string> ownOrder, IReadOnlyDictionary<string, BigInteger> weights)
    {
        var count = ownOrder.Count;

        // Identities are first-occurrence indices. `at` maps a position to the identity standing
        // there and `position` maps an identity to its place, so each exchange is O(1).
        var names = new string[count];
        var remaining = new BigInteger[count];
        var at = new int[count];
        var position = new int[count];
        var rightward = 0;
        var leftward = 0;
        for (var identity = 0; identity < count; identity++)
        {
            names[identity] = ownOrder[identity];
            var weight = weights.TryGetValue(names[identity], out var summed) ? summed : BigInteger.Zero;
            remaining[identity] = weight;
            at[identity] = identity;
            position[identity] = identity;
            if (weight.Sign > 0)
                rightward++;
            else if (weight.Sign < 0)
                leftward++;
        }

        // The schedule is fixed by the initial weights before anything moves.
        var turns = new int[rightward + leftward];
        var next = 0;
        for (var identity = count - 1; identity >= 0; identity--)
        {
            if (remaining[identity].Sign > 0)
                turns[next++] = identity;
        }

        for (var identity = 0; identity < count; identity++)
        {
            if (remaining[identity].Sign < 0)
                turns[next++] = identity;
        }

        foreach (var mover in turns)
        {
            var step = remaining[mover].Sign;
            while (!remaining[mover].IsZero)
            {
                var from = position[mover];
                var to = from + step;
                if (to < 0 || to >= count)
                    break;

                // A neighbour moving the same way with at least as much remaining weight blocks; an
                // unmarked neighbour or one moving the other way never does. The mover keeps
                // whatever it could not use.
                var neighbour = at[to];
                var blocked = step > 0
                    ? remaining[neighbour] >= remaining[mover]
                    : remaining[neighbour] <= remaining[mover];
                if (blocked)
                    break;

                at[from] = neighbour;
                position[neighbour] = from;
                at[to] = mover;
                position[mover] = to;
                remaining[mover] -= step;
            }
        }

        var order = new string[count];
        var leftover = new BigInteger[count];
        for (var place = 0; place < count; place++)
        {
            order[place] = names[at[place]];
            leftover[place] = remaining[at[place]];
        }

        return new Settlement(order, leftover);
    }

    /// <summary>
    /// A settled own list: <see cref="Order"/> is the final order and <see cref="Remaining"/>, aligned
    /// with it, each name's unused weight.
    /// </summary>
    internal readonly record struct Settlement(string[] Order, BigInteger[] Remaining);
}
