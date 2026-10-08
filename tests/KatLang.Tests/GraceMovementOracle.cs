using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// Two reference formulations of the PAR-06 Grace movement law (X-49), written without any code
/// shared with <c>GraceMovement</c>. Identities are first-occurrence indices.
/// <list type="bullet">
/// <item><see cref="TwoPass"/> — the NORMATIVE statement transcribed literally (list scans, no
/// position map): positive weights take turns from the last-occurring, then negative weights from
/// the first-occurring.</item>
/// <item><see cref="SourceOrderWithYielding"/> — a different algorithm: identities take turns in
/// first-occurrence order, and a mover blocked by a same-direction neighbour that has not had its
/// turn lets that neighbour move first, then tries again.</item>
/// </list>
/// The X-49 investigation found the two equal on 208,196 states (empirical, not a proof); the tests
/// re-check that on their own domains and use the yielding formulation as the oracle for the real
/// front end. Both report each identity's remaining weight, indexed by identity.
/// </summary>
internal static class GraceMovementOracle
{
    internal readonly record struct Run(int[] Order, BigInteger[] Remaining);

    internal static Run TwoPass(IReadOnlyList<BigInteger> weights)
    {
        var count = weights.Count;
        var order = Enumerable.Range(0, count).ToList();
        var remaining = weights.ToArray();

        var rightward = Enumerable.Range(0, count).Reverse().Where(p => weights[p].Sign > 0);
        var leftward = Enumerable.Range(0, count).Where(p => weights[p].Sign < 0);
        foreach (var mover in rightward.Concat(leftward).ToList())
        {
            while (!remaining[mover].IsZero)
            {
                var here = order.IndexOf(mover);
                var there = here + remaining[mover].Sign;
                if (there < 0 || there >= count)
                    break;

                var neighbour = order[there];
                var passes = remaining[mover].Sign > 0
                    ? remaining[neighbour] < remaining[mover]
                    : remaining[neighbour] > remaining[mover];
                if (!passes)
                    break;

                order[here] = neighbour;
                order[there] = mover;
                remaining[mover] -= remaining[mover].Sign;
            }
        }

        return new Run([.. order], remaining);
    }

    internal static Run SourceOrderWithYielding(IReadOnlyList<BigInteger> weights)
    {
        var count = weights.Count;
        var order = Enumerable.Range(0, count).ToList();
        var remaining = weights.ToArray();
        var started = new bool[count];

        for (var identity = 0; identity < count; identity++)
        {
            if (!started[identity] && !remaining[identity].IsZero)
                Turn(identity);
        }

        return new Run([.. order], remaining);

        void Turn(int mover)
        {
            started[mover] = true;
            while (!remaining[mover].IsZero)
            {
                var direction = remaining[mover].Sign;
                var here = order.IndexOf(mover);
                var there = here + direction;
                if (there < 0 || there >= count)
                    return;

                var neighbour = order[there];
                var passes = direction > 0
                    ? remaining[neighbour] < remaining[mover]
                    : remaining[neighbour] > remaining[mover];
                if (!passes)
                {
                    // A same-direction blocker that has not moved yet goes first; any other block
                    // ends the turn.
                    if (!started[neighbour] && remaining[neighbour].Sign == direction)
                    {
                        Turn(neighbour);
                        continue;
                    }

                    return;
                }

                order[here] = neighbour;
                order[there] = mover;
                remaining[mover] -= direction;
            }
        }
    }

    internal static int[] Order(IReadOnlyList<int> weights)
        => SourceOrderWithYielding([.. weights.Select(static w => new BigInteger(w))]).Order;
}
