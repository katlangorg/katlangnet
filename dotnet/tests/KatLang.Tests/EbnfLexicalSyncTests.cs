using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>
/// Mechanically pins the lexical terminal claims of <c>KatLang.ebnf</c> to the
/// shipped lexer, so the grammar can no longer drift from the implementation by
/// convention alone (it documented ASCII-only identifiers for over a year while
/// the lexer accepted letters of any script).
///
/// <para>The architecture is deliberately not a string search: the identifier
/// productions' Unicode-category claims and reserved-word list are EXTRACTED
/// from the grammar text and then compared against the lexer's actual behavior
/// (a full basic-multilingual-plane sweep of the identifier character
/// predicates, and the authoritative <see cref="Lexer.KeywordNames"/> table).
/// The identifier production SHAPE is checked semantically, rather than pinning
/// whitespace or alternative order. Whole-string and end-to-end identifier
/// behavior is pinned in <c>LexerTests</c>; UTF-16 code-unit edge
/// behavior (surrogates, combining marks, non-ASCII digits, strings, comments)
/// in <c>Utf16LexerContractTests</c>.</para>
/// </summary>
public class EbnfLexicalSyncTests
{
    private static string Grammar { get; } =
        File.ReadAllText(Path.Combine(RepoRoot.Find(), "KatLang.ebnf"));

    // ── The identifier character claim, verified over the whole BMP ─────────

    [Fact]
    public void EbnfIdentifierProduction_IsStartFollowedByZeroOrMoreParts()
    {
        var rhs = ProductionRhs("Identifier");
        Assert.Matches(@"^IdentifierStart\s*\{\s*IdentifierPart\s*\}$", rhs);
    }

    [Fact]
    public void EbnfIdentifierCharacterClaims_MatchTheShippedLexer_OverTheWholeBmp()
    {
        var (startLiterals, startCategories) = CharacterClassClaim("IdentifierStart");
        var (partLiterals, partCategories) = CharacterClassClaim("IdentifierPart");

        var failures = new List<string>();
        for (var value = 0; value <= 0xFFFF && failures.Count < 12; value++)
        {
            var c = (char)value;
            var category = CharUnicodeInfo.GetUnicodeCategory(c);
            var claimedStart = startLiterals.Contains(c) || startCategories.Contains(category);
            var claimedPart = partLiterals.Contains(c) || partCategories.Contains(category);

            if (Lexer.IsIdentifierStartChar(c) != claimedStart)
                failures.Add(
                    $"U+{value:X4} ({category}): the KatLang.ebnf identifier-START claim says " +
                    $"{Word(claimedStart)}, the shipped lexer says {Word(!claimedStart)}.");

            if (Lexer.IsIdentifierPartChar(c) != claimedPart)
                failures.Add(
                    $"U+{value:X4} ({category}): the KatLang.ebnf identifier-CONTINUATION claim says " +
                    $"{Word(claimedPart)}, the shipped lexer says {Word(!claimedPart)}.");
        }

        Assert.True(
            failures.Count == 0,
            "KatLang.ebnf's identifier terminal claims drifted from the shipped lexer contract " +
            "(underscore plus per-UTF-16-code-unit char.IsLetter for start; additionally Unicode " +
            "decimal digits for continuation). Update the grammar and the lexer TOGETHER:" +
            Environment.NewLine + string.Join(Environment.NewLine, failures));

        static string Word(bool identifierCharacter)
            => identifierCharacter ? "identifier character" : "not an identifier character";
    }

    /// <summary>
    /// Interprets an EBNF character-class production as the union of its quoted
    /// single-character terminals and the Unicode categories stated by the
    /// <c>UnicodeLetter</c>/<c>UnicodeDigit</c> productions it references, so the
    /// sweep above tests what the grammar ACTUALLY claims. A production this
    /// cannot interpret (say, reverted to an ASCII regex) fails loudly.
    /// </summary>
    private static (IReadOnlySet<char> Literals, IReadOnlySet<UnicodeCategory> Categories) CharacterClassClaim(
        string productionName,
        string? grammar = null)
    {
        var rhs = ProductionRhs(productionName, grammar);
        var literals = new HashSet<char>();
        var categories = new HashSet<UnicodeCategory>();

        foreach (var alternative in SplitAlternatives(rhs))
        {
            var term = alternative.Trim();
            var literal = Regex.Match(term, "^\"(.)\"$");
            if (literal.Success)
            {
                literals.Add(literal.Groups[1].Value[0]);
                continue;
            }

            if (term is "UnicodeLetter" or "UnicodeDigit")
            {
                categories.UnionWith(CategoryClaim(term, grammar));
                continue;
            }

            Assert.Fail(
                $"KatLang.ebnf production '{productionName} = {rhs}' contains the unrecognized " +
                $"character-class alternative '{term}'. The sync test must interpret every " +
                "alternative rather than silently ignoring a new grammar claim.");
        }

        Assert.True(
            literals.Count > 0 || categories.Count > 0,
            $"KatLang.ebnf production '{productionName} = {rhs}' no longer reads as a character " +
            "class made of quoted single-character terminals and UnicodeLetter/UnicodeDigit " +
            "references, so its claim cannot be checked against the lexer. If the identifier " +
            "grammar was deliberately restructured, update EbnfLexicalSyncTests with it.");

        return (literals, categories);
    }

    /// <summary>Extracts the Unicode general-category codes (Lu, Nd, ...) stated by a
    /// category-bearing terminal production such as <c>UnicodeLetter</c>.</summary>
    private static IReadOnlySet<UnicodeCategory> CategoryClaim(string productionName, string? grammar = null)
    {
        var rhs = ProductionRhs(productionName, grammar);
        Assert.Matches(@"^\?.*\?$", rhs);

        var categories = new HashSet<UnicodeCategory>();
        foreach (Match match in Regex.Matches(rhs, @"\b[A-Z][a-z]\b"))
        {
            var code = match.Value;
            Assert.True(
                KnownCategoryCodes.TryGetValue(code, out var category),
                $"KatLang.ebnf production '{productionName} = {rhs}' names unknown Unicode " +
                $"general-category code '{code}'. Update the independent test interpreter deliberately.");
            categories.Add(category);
        }

        Assert.True(
            categories.Count > 0,
            $"KatLang.ebnf production '{productionName} = {rhs}' no longer states any Unicode " +
            "general-category codes — did the identifier charset claim revert to an ASCII regex? " +
            "The shipped lexer accepts letters of any script (per UTF-16 code unit).");

        return categories;
    }

    private static readonly IReadOnlyDictionary<string, UnicodeCategory> KnownCategoryCodes =
        new Dictionary<string, UnicodeCategory>(StringComparer.Ordinal)
        {
            ["Lu"] = UnicodeCategory.UppercaseLetter,
            ["Ll"] = UnicodeCategory.LowercaseLetter,
            ["Lt"] = UnicodeCategory.TitlecaseLetter,
            ["Lm"] = UnicodeCategory.ModifierLetter,
            ["Lo"] = UnicodeCategory.OtherLetter,
            ["Nl"] = UnicodeCategory.LetterNumber,
            ["Nd"] = UnicodeCategory.DecimalDigitNumber,
            ["No"] = UnicodeCategory.OtherNumber,
            ["Mn"] = UnicodeCategory.NonSpacingMark,
            ["Mc"] = UnicodeCategory.SpacingCombiningMark,
            ["Me"] = UnicodeCategory.EnclosingMark,
            ["Pc"] = UnicodeCategory.ConnectorPunctuation,
            ["Pd"] = UnicodeCategory.DashPunctuation,
            ["Po"] = UnicodeCategory.OtherPunctuation,
            ["Sm"] = UnicodeCategory.MathSymbol,
            ["Sc"] = UnicodeCategory.CurrencySymbol,
            ["Sk"] = UnicodeCategory.ModifierSymbol,
            ["So"] = UnicodeCategory.OtherSymbol,
            ["Cf"] = UnicodeCategory.Format,
            ["Cs"] = UnicodeCategory.Surrogate,
            ["Co"] = UnicodeCategory.PrivateUse,
            ["Cn"] = UnicodeCategory.OtherNotAssigned,
            ["Cc"] = UnicodeCategory.Control,
            ["Zs"] = UnicodeCategory.SpaceSeparator,
            ["Zl"] = UnicodeCategory.LineSeparator,
            ["Zp"] = UnicodeCategory.ParagraphSeparator,
            ["Ps"] = UnicodeCategory.OpenPunctuation,
            ["Pe"] = UnicodeCategory.ClosePunctuation,
            ["Pi"] = UnicodeCategory.InitialQuotePunctuation,
            ["Pf"] = UnicodeCategory.FinalQuotePunctuation,
        };

    // ── The reserved-word claim, verified against the one keyword table ──────

    [Fact]
    public void EbnfReservedWordList_MatchesTheLexerKeywordTable()
    {
        var claimed = Regex.Matches(ProductionRhs("ReservedWord"), "\"([^\"]+)\"")
            .Select(static match => match.Groups[1].Value)
            .ToList();

        var duplicates = claimed
            .GroupBy(static word => word, StringComparer.Ordinal)
            .Where(static group => group.Count() > 1)
            .Select(static group => group.Key)
            .OrderBy(static word => word, StringComparer.Ordinal)
            .ToList();

        var missing = Lexer.KeywordNames.Except(claimed, StringComparer.Ordinal).Order(StringComparer.Ordinal).ToList();
        var extra = claimed.Except(Lexer.KeywordNames, StringComparer.Ordinal).Order(StringComparer.Ordinal).ToList();
        Assert.True(
            missing.Count == 0 && extra.Count == 0 && duplicates.Count == 0,
            "KatLang.ebnf's ReservedWord production drifted from the lexer's keyword table " +
            "(Lexer.KeywordNames, derived from the one keyword-definition table). " +
            (missing.Count > 0 ? $"Reserved by the lexer but not listed in the grammar: {string.Join(", ", missing)}. " : "") +
            (extra.Count > 0 ? $"Listed in the grammar but not reserved by the lexer: {string.Join(", ", extra)}. " : "") +
            (duplicates.Count > 0 ? $"Listed more than once in the grammar: {string.Join(", ", duplicates)}. " : "") +
            "Update the lexer, KatLang.ebnf, and the keyword pins in LexerTests together.");

        // And the behavioral half of the claim: every word the grammar lists as
        // reserved must actually be refused as an identifier by the lexer.
        foreach (var word in claimed)
        {
            Assert.False(
                Lexer.IsValidIdentifier(word),
                $"KatLang.ebnf lists '{word}' as a ReservedWord, but Lexer.IsValidIdentifier accepts it.");
        }
    }

    // ── Grammar extraction and harmless-formatting tolerance ─────────────────

    [Fact]
    public void CharacterClassInterpreter_AllowsWrappingAndReorderedAlternatives()
    {
        const string grammar = """
              IdentifierStart =
                    UnicodeLetter
                  | "_" ;
              UnicodeLetter = ? Unicode category Lo, Lm, Lt, Ll, or Lu ? ;
            """;

        var (literals, categories) = CharacterClassClaim("IdentifierStart", grammar);
        Assert.True(literals.SetEquals(['_']));
        Assert.True(
            categories.SetEquals(
            [
                UnicodeCategory.UppercaseLetter,
                UnicodeCategory.LowercaseLetter,
                UnicodeCategory.TitlecaseLetter,
                UnicodeCategory.ModifierLetter,
                UnicodeCategory.OtherLetter,
            ]));
    }

    [Fact]
    public void ProductionExtractor_IgnoresSemicolonsInsideDelimitedFormsAndComments()
    {
        const string grammar = """
              Probe = "a;\"b" | /a\/;b/ | ? prose ; still special ?
                      (* adjacent comment ; *) | "z" ;
              After = "not part of Probe" ;
            """;

        Assert.Equal(
            "\"a;\\\"b\" | /a\\/;b/ | ? prose ; still special ? | \"z\"",
            ProductionRhs("Probe", grammar));
    }

    // ── Grammar extraction ───────────────────────────────────────────────────

    /// <summary>
    /// The whitespace-normalized right-hand side of a production,
    /// with <c>(* ... *)</c> comments dropped. The terminating <c>;</c> is found
    /// respecting quoted terminals, <c>/.../</c> regex terminals, and
    /// <c>? ... ?</c> special sequences, so semicolons inside comments or
    /// terminals never end a production early.
    /// </summary>
    private static string ProductionRhs(string productionName, string? grammar = null)
    {
        grammar ??= Grammar;
        var header = Regex.Match(
            grammar,
            $@"^[ \t]*{Regex.Escape(productionName)}[ \t]*=",
            RegexOptions.Multiline);
        Assert.True(
            header.Success,
            $"KatLang.ebnf no longer declares the production '{productionName}'. The lexical sync " +
            "tests pin it against the shipped lexer; if the grammar was deliberately restructured, " +
            "update EbnfLexicalSyncTests in the same change.");

        var rhs = new StringBuilder();
        var i = header.Index + header.Length;
        var terminated = false;
        while (i < grammar.Length)
        {
            if (grammar[i] == '(' && i + 1 < grammar.Length && grammar[i + 1] == '*')
            {
                var end = grammar.IndexOf("*)", i + 2, StringComparison.Ordinal);
                Assert.True(end >= 0, $"KatLang.ebnf: unterminated comment inside production '{productionName}'.");
                i = end + 2;
                rhs.Append(' ');
                continue;
            }

            var c = grammar[i];
            if (c == ';')
            {
                terminated = true;
                break;
            }

            if (c is '"' or '/' or '?')
            {
                var close = FindDelimitedEnd(grammar, i, c);
                Assert.True(
                    close >= 0,
                    $"KatLang.ebnf: unterminated '{c}'-delimited terminal inside production '{productionName}'.");
                rhs.Append(grammar, i, close - i + 1);
                i = close + 1;
                continue;
            }

            rhs.Append(c);
            i++;
        }

        Assert.True(terminated, $"KatLang.ebnf: production '{productionName}' has no terminating ';'.");
        return Regex.Replace(rhs.ToString(), @"\s+", " ").Trim();
    }

    private static int FindDelimitedEnd(string grammar, int open, char delimiter)
    {
        for (var i = open + 1; i < grammar.Length; i++)
        {
            if (delimiter is '"' or '/' && grammar[i] == '\\' && i + 1 < grammar.Length)
            {
                i++;
                continue;
            }

            if (grammar[i] == delimiter)
                return i;
        }

        return -1;
    }

    private static IReadOnlyList<string> SplitAlternatives(string rhs)
    {
        var alternatives = new List<string>();
        var start = 0;
        for (var i = 0; i < rhs.Length; i++)
        {
            if (rhs[i] is '"' or '/' or '?')
            {
                var close = FindDelimitedEnd(rhs, i, rhs[i]);
                Assert.True(close >= 0, $"Unterminated '{rhs[i]}'-delimited form in '{rhs}'.");
                i = close;
                continue;
            }

            if (rhs[i] != '|')
                continue;

            alternatives.Add(rhs[start..i]);
            start = i + 1;
        }

        alternatives.Add(rhs[start..]);
        return alternatives;
    }
}
