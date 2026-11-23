using System.Collections.Immutable;
using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>
/// Depth-first walk of a recipe's CHOICE TREE (exhaustive campaigns). It replays a prefix of
/// values and takes the FIRST alternative of every later decision, recording each decision's
/// alternatives. A pick of <c>n</c> has the alternatives <c>0..n-1</c>; a <c>p</c> % chance has two —
/// it holds (recorded <c>0</c>) or it does not (recorded <c>p</c>) — and one when <c>p</c> is 0 or 100,
/// so a chance that only selects a branch is not walked a hundred times. The recorded values are the
/// program's CANONICAL choice sequence: <see cref="ReplayingChooser"/> (and so every recording
/// chooser) replays them to the same program, since a chance draws a pick of 100.
/// </summary>
internal sealed class ChoiceTreeChooser(IReadOnlyList<int> prefix) : SemanticChooser
{
    private readonly List<(int Count, int Percent, int Value)> _decisions = [];

    /// <summary>The first prefix value outside its dimension (it was replaced by the first alternative), or <c>null</c>.</summary>
    public string? Problem { get; private set; }

    /// <summary>Every decision of the generation so far.</summary>
    public int Consumed => _decisions.Count;

    /// <summary>The canonical choice sequence of the generation.</summary>
    public ImmutableArray<int> Values => [.. _decisions.Select(static d => d.Value)];

    public override int Pick(string dimension, int count)
    {
        if (count <= 0) throw new ArgumentOutOfRangeException(nameof(count));
        return Decide(dimension, count, -1);
    }

    public override bool Chance(string dimension, int percent) => Decide(dimension, 100, Math.Clamp(percent, 0, 100)) < percent;

    private int Decide(string dimension, int count, int percent)
    {
        var at = _decisions.Count;
        var value = 0;
        if (at < prefix.Count)
        {
            value = prefix[at];
            if (!Allowed(count, percent, value))
            {
                Problem ??= string.Create(CultureInfo.InvariantCulture,
                    $"choice {at} ({dimension}) is {value}, outside its alternatives ({(percent < 0 ? $"0..{count - 1}" : percent is > 0 and < 100 ? $"0 or {percent}" : "0")})");
                value = 0;
            }
        }

        _decisions.Add((count, percent, value));
        return value;
    }

    private static bool Allowed(int count, int percent, int value)
        => percent < 0 ? value >= 0 && value < count : value == 0 || (value == percent && percent is > 0 and < 100);

    private static int? Successor(int count, int percent, int value)
        => percent < 0 ? (value + 1 < count ? value + 1 : null) : (value == 0 && percent is > 0 and < 100 ? percent : null);

    /// <summary>The prefix of the next sequence in depth-first order; <c>false</c> after the last one.</summary>
    public bool TryNext(out ImmutableArray<int> next)
    {
        for (var i = _decisions.Count - 1; i >= 0; i--)
        {
            var (count, percent, value) = _decisions[i];
            if (Successor(count, percent, value) is { } successor)
            {
                next = [.. _decisions.Take(i).Select(static d => d.Value), successor];
                return true;
            }
        }

        next = [];
        return false;
    }
}

/// <summary>
/// Exhaustive enumeration of a FINITE recipe (<see cref="SemanticCorpus.FiniteRecipes"/>): every
/// choice sequence of its tree in depth-first order, each generated once, deduplicated by base
/// source. Each distinct program is identified by <c>sem2b/v2/&lt;recipe&gt;/all/&lt;choices&gt;</c>
/// (<see cref="SemanticCorpus.ExhaustiveLocalId"/>), which replay, export and reduction rebuild from
/// the id alone. Enumerating GENERATES only; nothing is evaluated.
/// </summary>
internal static class SemanticExhaustive
{
    /// <summary>A recipe whose tree exceeds this many sequences is refused as not finite in practice.</summary>
    internal const int MaxSequences = 1 << 20;

    /// <summary>One distinct enumerated program: its canonical choices and its durable id.</summary>
    internal sealed record EnumeratedProgram(ImmutableArray<int> Choices, string CaseId);

    /// <summary>
    /// The whole enumeration: how many choice sequences the tree has and the distinct programs, in
    /// depth-first order. <see cref="Sequences"/> exceeds <c>Programs.Length</c> only when two
    /// sequences render the same base source (with the same expectation).
    /// </summary>
    internal sealed record Enumeration(string Recipe, int Sequences, ImmutableArray<EnumeratedProgram> Programs);

    /// <summary>Enumerates every program of a finite recipe. Throws for any other recipe or a tree beyond <see cref="MaxSequences"/>.</summary>
    internal static Enumeration Enumerate(string recipe)
    {
        var body = SemanticCorpus.FiniteBody(recipe)
            ?? throw new ArgumentException($"'{recipe}' is not a finite recipe; only {string.Join(", ", SemanticCorpus.FiniteRecipes)} enumerate.", nameof(recipe));
        var programs = ImmutableArray.CreateBuilder<EnumeratedProgram>();
        var seen = new Dictionary<string, string>(StringComparer.Ordinal);
        var prefix = ImmutableArray<int>.Empty;
        var sequences = 0;
        while (true)
        {
            if (++sequences > MaxSequences)
                throw new InvalidOperationException($"the {recipe} choice tree exceeds {MaxSequences.ToString(CultureInfo.InvariantCulture)} sequences; it is not enumerable");
            var chooser = new ChoiceTreeChooser(prefix);
            var built = body(new SemanticGrammar.Gen(chooser), "enumeration", SemanticCorpus.ExhaustiveTier, null, null).Case;
            if (chooser.Problem is { } problem)
                throw new InvalidOperationException($"{recipe} enumeration replayed an invalid prefix: {problem}");
            var meaning = Meaning(built);
            if (seen.TryGetValue(built.Source, out var earlier))
            {
                if (earlier != meaning)
                    throw new InvalidOperationException($"two {recipe} choice sequences render one source with different expectations:\n{built.Source}");
            }
            else
            {
                seen.Add(built.Source, meaning);
                var choices = chooser.Values;
                programs.Add(new EnumeratedProgram(choices, SemanticRecipe.CasePrefix + SemanticCorpus.ExhaustiveLocalId(recipe, choices)));
            }

            if (!chooser.TryNext(out prefix)) break;
        }

        return new Enumeration(recipe, sequences, programs.ToImmutable());
    }

    /// <summary>
    /// Whether <paramref name="choices"/> is the canonical sequence of one program of a finite
    /// recipe: one generation consumes exactly these values, each inside its dimension.
    /// </summary>
    internal static bool IsCanonical(string recipe, IReadOnlyList<int> choices, out string problem)
    {
        if (SemanticCorpus.FiniteBody(recipe) is not { } body)
        {
            problem = "not a finite recipe";
            return false;
        }

        var chooser = new ChoiceTreeChooser(choices);
        try
        {
            body(new SemanticGrammar.Gen(chooser), "canonical-check", SemanticCorpus.ExhaustiveTier, null, null);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            problem = "its generation failed (" + exception.GetType().Name + ": " + exception.Message + ")";
            return false;
        }

        problem = chooser.Problem
            ?? (chooser.Consumed != choices.Count
                ? string.Create(CultureInfo.InvariantCulture, $"the program takes {chooser.Consumed} choices, the id lists {choices.Count}")
                : "");
        return problem.Length == 0;
    }

    /// <summary>What a run is judged against: kind, outcome, events and profiles.</summary>
    private static string Meaning(SemanticCase c)
        => string.Join("|", c.Kind, c.Expected.ValueIdentity, c.Expected.ErrorCategory, c.Expected.Diagnostic, c.Expected.DiagnosticPhase,
            string.Join(",", c.Expected.Events), string.Join(",", c.Profiles), string.Join(",", c.Members.Select(static m => m.Fingerprint)));
}
