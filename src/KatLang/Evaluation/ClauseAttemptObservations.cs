namespace KatLang;

/// <summary>How one observed conditional-clause attempt ended (<see cref="ClauseAttemptObservations"/>).</summary>
internal enum ClauseAttemptOutcome : byte
{
    /// <summary>The attempt began and has not ended — still running, or abandoned by an exception (cancellation).</summary>
    Pending,

    /// <summary>The clause's head bound the supply: the clause is selected and no later clause is attempted.</summary>
    Matched,

    /// <summary>An ordinary non-match: the dispatch continues with the next clause.</summary>
    NonMatch,

    /// <summary>The attempt returned an error, which ends the dispatch.</summary>
    Error,
}

/// <summary>
/// One observed clause attempt: the dispatch it belongs to (numbered from 1 in the order the run's
/// family dispatches made their first attempt), the family, the clause's index in written order, and
/// its outcome.
/// </summary>
internal readonly record struct ClauseAttempt(int Dispatch, Algorithm Family, int Clause, ClauseAttemptOutcome Outcome);

/// <summary>
/// Passive record of the conditional-clause attempts of one observed run (SEC-02-FU2), carried by
/// <see cref="EvaluationObservations.ClauseAttempts"/>. An attempt is recorded when a family dispatch
/// begins binding a cardinality-eligible clause — immediately before the binder that may demand the
/// clause's supplied values — and its outcome when that binder returns. The family-level duplicate
/// and cardinality decisions, the skip of a clause whose head refuses the supply count, and the
/// activation of a matched clause are not attempts. So a dispatch that wrongly continued past a
/// terminal error to a later clause is visible here even when the run's retained terminal error
/// (Q-02) stops that clause before its first demand.
///
/// <para>Internal, test-only C# implementation instrumentation, never language semantics and never
/// compared against Lean. Created only by a test that asks for it: an ordinary run, or an observed
/// run without it, records nothing and allocates nothing. Recording never influences evaluation —
/// no demand, checkpoint, or effect is added — and one instance belongs to one run; it is
/// synchronized so a run's asynchronous continuations may record from any thread.</para>
/// </summary>
internal sealed class ClauseAttemptObservations
{
    private readonly Lock gate = new();
    private readonly List<ClauseAttempt> attempts = [];
    private readonly Stack<Dispatch> active = new();
    private int dispatches;

    // Bookkeeping belongs to the opt-in observer, not the recursive evaluator frames. In
    // particular, a disabled observer adds no dispatch/attempt locals to either family driver.
    private sealed class Dispatch(Algorithm family)
    {
        internal readonly Algorithm Family = family;
        internal int Number;
        internal int Attempt;
    }

    /// <summary>Every attempt so far, in the order the attempts began.</summary>
    public IReadOnlyList<ClauseAttempt> Attempts
    {
        get
        {
            lock (gate)
                return [.. attempts];
        }
    }

    /// <summary>The attempted clause indices, in the order the attempts began.</summary>
    public IReadOnlyList<int> AttemptedClauses
    {
        get
        {
            lock (gate)
                return [.. attempts.Select(static attempt => attempt.Clause)];
        }
    }

    /// <summary>
    /// Begins one nested dispatch. Its number is assigned only when it makes its first attempt.
    /// </summary>
    internal void BeginDispatch(Algorithm family)
    {
        lock (gate)
            active.Push(new Dispatch(family));
    }

    /// <summary>Records that the current dispatch begins binding the specified clause.</summary>
    internal void RecordAttempt(int clause)
    {
        lock (gate)
        {
            var dispatch = active.Peek();
            if (dispatch.Number == 0)
                dispatch.Number = ++dispatches;
            dispatch.Attempt = attempts.Count;
            attempts.Add(new ClauseAttempt(dispatch.Number, dispatch.Family, clause, ClauseAttemptOutcome.Pending));
        }
    }

    /// <summary>
    /// Completes the current attempt and, for a match or error, its dispatch. An exception leaves
    /// its attempt pending and the run ends; this run's collector is never reused for another run.
    /// </summary>
    internal void RecordOutcome(ClauseAttemptOutcome outcome)
    {
        lock (gate)
        {
            var dispatch = active.Peek();
            attempts[dispatch.Attempt] = attempts[dispatch.Attempt] with { Outcome = outcome };
            if (outcome is not ClauseAttemptOutcome.NonMatch)
                active.Pop();
        }
    }

    /// <summary>Ends a dispatch that exhausted its clauses without a match.</summary>
    internal void EndUnmatchedDispatch()
    {
        lock (gate)
            active.Pop();
    }
}
