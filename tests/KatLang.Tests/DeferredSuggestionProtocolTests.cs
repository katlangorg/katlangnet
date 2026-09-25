using System.Collections.Frozen;

namespace KatLang.Tests;

/// <summary>
/// FE-1: a provenance note captures its suggestion's candidate context at promotion and computes the
/// suggestion on first read. The value read must be exactly what eager computation followed by the
/// finalizer's in-place operations produced — the confirmed receivers applied in order, a dropped
/// suggestion gone for good — whenever the read happens, including before finalization, and
/// concurrent first readers must agree.
/// </summary>
public class DeferredSuggestionProtocolTests
{
    private sealed class CountingQuery(NameSuggestion? result) : SuggestionQuery
    {
        private int _evaluations;

        public int Evaluations => Volatile.Read(ref _evaluations);

        public override NameSuggestion? Evaluate()
        {
            Interlocked.Increment(ref _evaluations);
            return result;
        }
    }

    private static FrozenSet<string> Receiver(params string[] members)
        => members.ToFrozenSet(StringComparer.Ordinal);

    [Fact]
    public void NothingIsEvaluatedUntilTheFirstRead_AndTheReadIsCached()
    {
        var query = new CountingQuery(new NameSuggestion("Alpha"));
        var note = new ImplicitParameterProvenance("Alpah", span: null, query);

        Assert.Equal(0, query.Evaluations);
        Assert.False(note.IsSuggestionEvaluated);
        Assert.Equal("Alpha", note.SuggestedName);
        Assert.Equal("Alpha", note.SuggestedName);
        Assert.Equal(1, query.Evaluations);
        Assert.True(note.IsSuggestionEvaluated);
    }

    [Fact]
    public void ConfirmedReceivers_ApplyInOrder_EvenAfterAnEarlierRead()
    {
        var query = new CountingQuery(new NameSuggestion("Double", "Lib", isReceiverMember: true));
        var note = new ImplicitParameterProvenance("Duoble", span: null, query);

        Assert.Equal("Lib.Double", note.SuggestedName);

        // A receiver that declares the member keeps the suggestion; one that does not drops it,
        // and a later confirmation cannot revive it.
        note.ConfirmDotMemberReceiver(Receiver("Double", "Half"));
        Assert.Equal("Lib.Double", note.SuggestedName);
        note.ConfirmDotMemberReceiver(Receiver("Half"));
        Assert.Null(note.SuggestedName);
        note.ConfirmDotMemberReceiver(Receiver("Double"));
        Assert.Null(note.SuggestedName);
    }

    [Fact]
    public void LexicalSuggestion_SurvivesOnlyAMemberlessConfirmedReceiver()
    {
        var kept = new ImplicitParameterProvenance("cnt", span: null, new CountingQuery(new NameSuggestion("count")));
        kept.ConfirmDotMemberReceiver(Receiver());
        Assert.Equal("count", kept.SuggestedName);

        var dropped = new ImplicitParameterProvenance("cnt", span: null, new CountingQuery(new NameSuggestion("count")));
        dropped.ConfirmDotMemberReceiver(Receiver("Anything"));
        Assert.Null(dropped.SuggestedName);
    }

    [Fact]
    public void ForgottenOrigin_DropsTheSuggestion_WhateverWasReadBefore()
    {
        var note = new ImplicitParameterProvenance(
            "Duoble", span: null, new CountingQuery(new NameSuggestion("Double", "Lib", isReceiverMember: true)), new DotMemberFallbackOrigin("Lib"));

        Assert.Equal("Lib.Double", note.SuggestedName);
        note.ForgetDotMemberOrigin();

        Assert.Null(note.SuggestedName);
        Assert.Null(note.DotMemberOrigin);
        note.ConfirmDotMemberReceiver(Receiver("Double"));
        Assert.Null(note.SuggestedName);
    }

    [Fact]
    public void NoQuery_MeansNoSuggestion()
    {
        var note = new ImplicitParameterProvenance("x", span: null, suggestion: null);
        Assert.Null(note.SuggestedName);
        Assert.True(note.IsSuggestionEvaluated);
    }

    [Fact]
    public async Task ConcurrentFirstReads_AgreeOnOneValue()
    {
        for (var round = 0; round < 50; round++)
        {
            var query = new CountingQuery(new NameSuggestion("Alpha"));
            var note = new ImplicitParameterProvenance("Alpah", span: null, query);
            using var start = new ManualResetEventSlim();
            var readers = Enumerable.Range(0, 8)
                .Select(_ => Task.Run(() =>
                {
                    start.Wait();
                    return note.SuggestedName;
                }))
                .ToArray();

            start.Set();
            var values = await Task.WhenAll(readers);

            Assert.All(values, value => Assert.Equal("Alpha", value));
            Assert.InRange(query.Evaluations, 1, readers.Length);
            Assert.Equal("Alpha", note.SuggestedName);
        }
    }
}
