namespace KatLang;

/// <summary>
/// Allocation-free LIFO ownership for the parser, loop memo, and loader state scopes.
/// Store this mutable tracker in a private, non-readonly owner field; only tickets are
/// copied. A ticket is unique for that owner's lifetime, so a copied disposable cannot
/// release a newer scope at the same depth. Rejection changes no state.
/// </summary>
internal struct StateScopeStack
{
    private long _lastId;
    private long _currentId;

    internal readonly record struct Ticket(long Id, long ParentId);

    public Ticket Enter()
    {
        var id = checked(_lastId + 1);
        var ticket = new Ticket(id, _currentId);
        _lastId = _currentId = id;
        return ticket;
    }

    public void Exit(Ticket ticket)
    {
        if (ticket.Id == 0 || _currentId != ticket.Id)
            throw new InvalidOperationException("State scopes must be disposed once, in reverse entry order.");

        _currentId = ticket.ParentId;
    }
}
