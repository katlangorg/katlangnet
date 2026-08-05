using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>
/// The <see cref="StringDelimiterMode.Never"/> contract for the <c>concise</c>
/// formatter: the mode suppresses added string quote delimiters ONLY — it does
/// not disable structural delimiter removal. Concise decides elision per
/// concrete value from the exact raw token representation: safe raw labels
/// (<c>neto</c>, <c>net_salary</c>) still participate, while ambiguous raw
/// strings conservatively keep the containing sequence's canonical
/// parentheses and separators. The suite also pins the SPREAD salary program
/// end to end under the acceptance preset (width 100, indent 2, "\n", zero
/// root spacing, Never): spread discards the outer salary structure, so every
/// row formats independently and flat — the natural structured program is
/// pinned separately in <see cref="NaturalStructureLayoutTests"/>.
/// </summary>
public class ConciseNeverModeTests
{
    /// <summary>The acceptance options preset (KatLangWeb-compatible).</summary>
    private static OutputFormattingOptions Preset(
        int width = 100,
        int indent = 2,
        int spacing = 0,
        int? maxDisplayLength = null)
        => new()
        {
            PreferredLineWidth = width,
            IndentSize = indent,
            NewLine = "\n",
            RootOutputSpacing = spacing,
            StringDelimiters = StringDelimiterMode.Never,
            MaxDisplayLength = maxDisplayLength,
        };

    private static string Concise(string source, OutputFormattingOptions? options = null)
        => OutputFormatters.Concise.Format(KatLangEngine.Run(source), options ?? Preset());

    private const string SpreadSalarySource = """
        # Salary calculations for Latvia using 2026 tax rates.

        Round = Math.Round(x, 2)
        NonTaxMin = 550
        DependentPersonTaxRelief = 250
        PersonalIncomeTaxRate = 0.255
        EmployeeSocContributionRate = 0.105
        EmployerSocContributionRate = 0.2359
        BusinessRiskStateDutyAmount = 0.36

        SalaryExpenses(grossSalary, hasTaxBook, numberOfChildren) = {
            SocTax = (grossSalary * EmployeeSocContributionRate).Round
            ChildCredit = numberOfChildren * DependentPersonTaxRelief
            TaxableIncome = grossSalary - SocTax - ChildCredit - hasTaxBook * NonTaxMin
            IncomeTax = (TaxableIncome * PersonalIncomeTaxRate).Round
            NetSalary = grossSalary - SocTax - IncomeTax
            EmployeeTax = SocTax + IncomeTax
            EmployerSocTax = (grossSalary * EmployerSocContributionRate).Round

            ('neto' NetSalary)
            ('taxes' EmployeeTax + EmployerSocTax + BusinessRiskStateDutyAmount)
            ('social' SocTax + EmployerSocTax
            'income' IncomeTax
            'risk' BusinessRiskStateDutyAmount)
            ('total' grossSalary + EmployerSocTax + BusinessRiskStateDutyAmount)
        }

        SalaryExpenses(2000, 1, 0)*
        ''
        SalaryExpenses(502, 0, 0)*
        """;

    private const string SpreadSalaryCanonical =
        "(neto, 1473.80)\n" +
        "(taxes, 998.36)\n" +
        "(social, 681.80, income, 316.20, risk, 0.36)\n" +
        "(total, 2472.16)\n" +
        "\n" +
        "(neto, 334.72)\n" +
        "(taxes, 286.06)\n" +
        "(social, 171.13, income, 114.57, risk, 0.36)\n" +
        "(total, 620.78)";

    private const string SpreadSalaryConcise =
        "neto 1473.80\n" +
        "taxes 998.36\n" +
        "social 681.80 income 316.20 risk 0.36\n" +
        "total 2472.16\n" +
        "\n" +
        "neto 334.72\n" +
        "taxes 286.06\n" +
        "social 171.13 income 114.57 risk 0.36\n" +
        "total 620.78";

    // ── The SPREAD salary program under the acceptance preset ───────────────

    [Fact]
    public void SpreadSalary_Exact_RemainsCanonicalAndIgnoresThePreset()
    {
        var run = KatLangEngine.Run(SpreadSalarySource);
        Assert.Equal(run.ToDisplayString(), OutputFormatters.Exact.Format(run, Preset()));
        Assert.Equal(SpreadSalaryCanonical, run.ToDisplayString().ReplaceLineEndings("\n"));
    }

    [Fact]
    public void SpreadSalary_Readable_KeepsEveryDelimiterWithoutAddedQuotesOrSpacing()
    {
        var text = OutputFormatters.Readable.Format(KatLangEngine.Run(SpreadSalarySource), Preset());

        // No added quotes, no automatic blank rows; the single blank line is
        // the explicit empty-string output row.
        Assert.Equal(SpreadSalaryCanonical, text);
        Assert.DoesNotContain("'", text, StringComparison.Ordinal);
        Assert.Equal(1, text.Split('\n').Count(line => line.Length == 0));
    }

    [Fact]
    public void SpreadSalary_Concise_FormatsEachFlattenedRowIndependently()
    {
        var text = OutputFormatters.Concise.Format(KatLangEngine.Run(SpreadSalarySource), Preset());

        Assert.Equal(SpreadSalaryConcise, text);
        Assert.DoesNotContain("''", text, StringComparison.Ordinal);
        Assert.DoesNotContain(":", text, StringComparison.Ordinal);
        Assert.DoesNotContain("(", text, StringComparison.Ordinal);
        Assert.Equal(1, text.Split('\n').Count(line => line.Length == 0));
        Assert.Contains("net", text, StringComparison.Ordinal);
        Assert.Equal(text, text.ToLowerInvariant());
    }

    // ── Safe raw labels stay eligible for delimiter removal ─────────────────

    [Theory]
    [InlineData("('neto', 1473.8)", "neto 1473.8")]
    [InlineData("('net_salary', 1473.8)", "net_salary 1473.8")]
    [InlineData("('a_b_c', 1)", "a_b_c 1")]
    [InlineData("('_leading', 2)", "_leading 2")]
    [InlineData("('trailing_', 3)", "trailing_ 3")]
    [InlineData("(1, 2, 3)", "1 2 3")]
    [InlineData("('neto:', 1473.8)", "neto: 1473.8")]
    public void SafeRawTokens_SpaceJoinUnderNever(string source, string expected)
        => Assert.Equal(expected, Concise(source));

    // ── Ambiguous raw strings retain the containing sequence ────────────────

    [Theory]
    [InlineData("('', 1)", "(, 1)")]
    [InlineData("('net salary', 1473.8)", "(net salary, 1473.8)")]
    [InlineData("(' leading', 1)", "( leading, 1)")]
    [InlineData("('trailing ', 1)", "(trailing , 1)")]
    [InlineData("('a,b', 1)", "(a,b, 1)")]
    [InlineData("('a(b)', 1)", "(a(b), 1)")]
    [InlineData("('a[b]', 1)", "(a[b], 1)")]
    [InlineData("('123', 4)", "(123, 4)")]
    [InlineData("('-2', 1)", "(-2, 1)")]
    [InlineData("('+7', 1)", "(+7, 1)")]
    [InlineData("('1.5', 1)", "(1.5, 1)")]
    [InlineData("('1e5', 1)", "(1e5, 1)")]
    [InlineData("('()', 1)", "((), 1)")]
    [InlineData("('[1, 2]', 1)", "([1, 2], 1)")]
    public void AmbiguousRawStrings_RetainCanonicalSequencePunctuation(string source, string expected)
    {
        var text = Concise(source);
        Assert.Equal(expected, text);

        // Never forbids added delimiters: content stays verbatim, unquoted.
        Assert.DoesNotContain("'", text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("a\tb")]
    [InlineData("a\rb")]
    [InlineData("a\nb")]
    [InlineData("can't")]
    public void HostOnlyUnsafeStrings_RetainPunctuationAndContent(string raw)
    {
        var value = new Result.SequenceValue([new Result.Str(raw), new Result.Atom(1)]);
        var success = new RunResult.Success(new Algorithm.User(null, [], [], [], []), value, []);

        var text = OutputFormatters.Concise.Format(success, Preset());

        Assert.Equal($"({raw}, 1)", text);
        Assert.Contains(raw, text, StringComparison.Ordinal);
    }

    // ── Nested structures under Never ───────────────────────────────────────

    [Fact]
    public void SequenceInsideList_KeepsParenthesesUnderNever()
        => Assert.Equal("[(1, 2), 3]", Concise("[(1, 2), 3]"));

    [Fact]
    public void ListInsideSequence_AtZeroSpacing_KeepsInlineParentheses()
        => Assert.Equal("(1, [2, 3])", Concise("(1, [2, 3])"));

    [Fact]
    public void ListInsideSequence_WithSpacing_FormsABlockUnderNever()
        => Assert.Equal("1\n[2, 3]", Concise("(1, [2, 3])", Preset(spacing: 1)));

    [Fact]
    public void SafeFlatChildSequence_JoinsInsideABlockUnderNever()
        => Assert.Equal("1 2\n3", Concise("((1, 2), 3)", Preset(spacing: 1)));

    [Fact]
    public void SalaryShapedBlock_WithPairLines_WorksUnderNever()
        => Assert.Equal(
            "neto 1473.8\n" +
            "taxes 998.36\n" +
            "  social 681.8\n" +
            "  income 316.2\n" +
            "  risk 0.36\n" +
            "total 2472.16",
            Concise(
                "(('neto', 1473.8), ('taxes', 998.36), ('social', 681.8, 'income', 316.2, 'risk', 0.36), ('total', 2472.16))",
                Preset(width: 20, spacing: 1)));

    [Fact]
    public void AdjacentBlockShapedSiblings_KeepParenthesesUnderNever()
        => Assert.Equal(
            "(\n  100,\n  200,\n  300\n)\n(\n  400,\n  500,\n  600\n)",
            Concise("((100, 200, 300), (400, 500, 600))", Preset(width: 8, spacing: 1)));

    [Fact]
    public void NestedSequenceAsFirstItem_KeepsParenthesesUnderNever()
        => Assert.Equal(
            "(\n  100,\n  200,\n  300\n)\n1\n2",
            Concise("((100, 200, 300), 1, 2)", Preset(width: 8, spacing: 1)));

    [Fact]
    public void NestedSequenceAsMiddleItem_BecomesASubBlockUnderNever()
        => Assert.Equal(
            "1\n  100\n  200\n  300\n2",
            Concise("(1, (100, 200, 300), 2)", Preset(width: 8, spacing: 1)));

    [Fact]
    public void NestedSequenceAsFinalItem_BecomesASubBlockUnderNever()
        => Assert.Equal(
            "1\n2\n  100\n  200\n  300",
            Concise("(1, 2, (100, 200, 300))", Preset(width: 8, spacing: 1)));

    [Fact]
    public void EmptyChildren_StayVisibleUnderNever()
    {
        Assert.Equal("1\n()\n2", Concise("(1, (), 2)", Preset(spacing: 1)));
        Assert.Equal("1\n[]\n2", Concise("(1, [], 2)", Preset(spacing: 1)));
    }

    // ── Root-output boundaries with zero root spacing ───────────────────────

    [Fact]
    public void SeveralRootRows_AndOneRootSequence_StayDistinctUnderThePreset()
    {
        var twoRows = Concise("A = 1\nB = 2\nA()\nB()");
        var oneSequence = Concise("(A() B())\nA = 1\nB = 2");

        Assert.Equal("1\n2", twoRows);
        Assert.Equal("1 2", oneSequence);
        Assert.NotEqual(twoRows, oneSequence);
    }

    [Fact]
    public void MultilineRootSequence_KeepsParenthesesAtZeroSpacing()
    {
        var oneNestedRoot = Concise("((1, 2), (3, 4))", Preset(width: 9));
        var twoRootRows = Concise("(1, 2), (3, 4)", Preset(width: 9));

        Assert.Equal("(\n  (1, 2),\n  (3, 4)\n)", oneNestedRoot);
        Assert.Equal("1 2\n3 4", twoRootRows);
        Assert.NotEqual(oneNestedRoot, twoRootRows);
    }

    [Fact]
    public void RootSequenceOfSequences_KeepsParenthesesAtZeroSpacing()
    {
        // Structural complexity now breaks this root into multiline layout even
        // though its flat text fits the width — but with no nested pair block
        // to anchor a paren-hidden root block at zero root spacing, the
        // parentheses stay, so one root sequence still cannot be confused with
        // two independent root rows ("1 2\n3 4").
        Assert.Equal("(\n  (1, 2),\n  (3, 4)\n)", Concise("((1, 2), (3, 4))"));
        Assert.Equal("1 2\n3 4", Concise("(1, 2), (3, 4)"));
    }

    [Fact]
    public void ExplicitEmptyStringRow_IsExactlyOneBlankLineAtZeroSpacing()
        => Assert.Equal("a 1\n\nb 2", Concise("('a', 1)\n''\n('b', 2)"));

    // ── Zero indentation ────────────────────────────────────────────────────

    [Fact]
    public void ZeroIndent_RetainsChildParenthesesUnderNever()
        => Assert.Equal(
            "1\n(\n100,\n200,\n300\n)\n2",
            Concise("(1, (100, 200, 300), 2)", Preset(width: 8, indent: 0, spacing: 1)));

    // ── Policy comparison on one value ──────────────────────────────────────

    [Fact]
    public void DelimiterModes_ChangeQuotingButNotStructuralSafetyRules()
    {
        static string With(string source, StringDelimiterMode mode)
            => OutputFormatters.Concise.Format(
                KatLangEngine.Run(source),
                new OutputFormattingOptions { NewLine = "\n", RootOutputSpacing = 0, StringDelimiters = mode });

        // A safe label joins under every mode; only the quoting differs.
        Assert.Equal("neto 1", With("('neto', 1)", StringDelimiterMode.Never));
        Assert.Equal("neto 1", With("('neto', 1)", StringDelimiterMode.WhenNeeded));
        Assert.Equal("'neto' 1", With("('neto', 1)", StringDelimiterMode.Always));

        // A numeric-looking string is only safe once quoting makes it
        // self-bounding; raw rendering conservatively retains the sequence.
        Assert.Equal("(123, 5)", With("('123', 5)", StringDelimiterMode.Never));
        Assert.Equal("'123' 5", With("('123', 5)", StringDelimiterMode.WhenNeeded));
        Assert.Equal("'123' 5", With("('123', 5)", StringDelimiterMode.Always));

        // Atom-only sequences join under every mode.
        Assert.Equal("1 2", With("(1, 2)", StringDelimiterMode.Never));
        Assert.Equal("1 2", With("(1, 2)", StringDelimiterMode.Always));
    }

    // ── Exact and Readable regressions under the preset ─────────────────────

    [Fact]
    public void Exact_EqualsToDisplayString_ForEveryPresetCase()
    {
        foreach (var source in new[]
        {
            SpreadSalarySource,
            "('neto', 1473.8)", "('net_salary', 1473.8)", "(1, 2, 3)",
            "('', 1)", "('net salary', 1473.8)", "('123', 4)", "('a,b', 1)",
            "[(1, 2), 3]", "(1, [2, 3])", "((1, 2), (3, 4))",
        })
        {
            var run = KatLangEngine.Run(source);
            Assert.Equal(run.ToDisplayString(), OutputFormatters.Exact.Format(run, Preset()));
        }
    }

    [Fact]
    public void Readable_RetainsAllDelimitersUnderThePreset()
    {
        Assert.Equal("(neto, 1473.8)", OutputFormatters.Readable.Format(KatLangEngine.Run("('neto', 1473.8)"), Preset()));
        Assert.Equal("[(1, 2), 3]", OutputFormatters.Readable.Format(KatLangEngine.Run("[(1, 2), 3]"), Preset()));
        Assert.Equal("1\n2", OutputFormatters.Readable.Format(KatLangEngine.Run("1, 2"), Preset()));
    }

    // ── Display limits around joined and retained punctuation ───────────────

    private static string OverflowResponse(int limit)
    {
        var message = KatLangError.FromEvalError(new EvalError.DisplayLengthLimitExceeded(limit)).Message;
        if (message.Length <= limit) return message;
        return limit >= 1 ? "…" : string.Empty;
    }

    [Theory]
    [InlineData("('neto', 1473.8)", "neto 1473.8")]   // removed punctuation, spaces replacing commas
    [InlineData("('123', 5)", "(123, 5)")]            // retained punctuation
    [InlineData("1\n''\n2", "1\n\n2")]                // explicit blank row
    public void PresetOutputs_SweepTheDisplayLimitAllOrNothing(string source, string natural)
    {
        var run = KatLangEngine.Run(source);
        Assert.Equal(natural, OutputFormatters.Concise.Format(run, Preset()));

        for (var limit = 0; limit <= natural.Length + 2; limit++)
        {
            var text = OutputFormatters.Concise.Format(run, Preset(maxDisplayLength: limit));
            Assert.True(text.Length <= limit, $"limit {limit} returned {text.Length} units.");
            Assert.Equal(limit >= natural.Length ? natural : OverflowResponse(limit), text);
        }
    }

    [Fact]
    public void CustomNewLine_IsChargedExactlyUnderThePreset()
    {
        var run = KatLangEngine.Run("1\n''\n2");
        var options = new OutputFormattingOptions
        {
            NewLine = "\r\n",
            RootOutputSpacing = 0,
            StringDelimiters = StringDelimiterMode.Never,
            MaxDisplayLength = 6,
        };

        Assert.Equal("1\r\n\r\n2", OutputFormatters.Concise.Format(run, options));
        Assert.Equal(
            OverflowResponse(5),
            OutputFormatters.Concise.Format(run, options with { MaxDisplayLength = 5 }));
    }

    // ── Robustness with large raw strings ───────────────────────────────────

    private static RunResult.Success SequenceWithString(string raw)
        => new(
            new Algorithm.User(null, [], [], [], []),
            new Result.SequenceValue([new Result.Str(raw), new Result.Atom(1)]),
            []);

    [Fact]
    public void LargeSafeString_RendersFullyWithoutJoining()
    {
        var raw = new string('a', 200_000);
        var text = OutputFormatters.Concise.Format(SequenceWithString(raw), Preset());

        // Far too wide for any join or inline line, so the multiline
        // parenthesized form is used: "(\n  " + raw + ",\n  1\n)".
        Assert.Equal(raw.Length + 11, text.Length);
        Assert.StartsWith("(\n  a", text, StringComparison.Ordinal);
        Assert.EndsWith(",\n  1\n)", text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(true)]   // unsafe character first: safety scan exits immediately
    [InlineData(false)]  // unsafe character last: one full scan at most
    public void LargeUnsafeStrings_RetainPunctuationBounded(bool unsafeFirst)
    {
        var body = new string('a', 200_000);
        var raw = unsafeFirst ? "," + body : body + ",";
        var text = OutputFormatters.Concise.Format(SequenceWithString(raw), Preset());

        Assert.Equal(raw.Length + 11, text.Length);
        Assert.StartsWith("(", text, StringComparison.Ordinal);

        var bounded = OutputFormatters.Concise.Format(SequenceWithString(raw), Preset(maxDisplayLength: 1_000));
        Assert.True(bounded.Length <= 1_000);
        Assert.StartsWith("Display output limit of", bounded, StringComparison.Ordinal);
    }

    [Fact]
    public void LargeUnsafeString_UnderTinyLimit_StaysAllocationBounded()
    {
        var success = SequenceWithString("," + new string('a', 200_000));
        var options = Preset(maxDisplayLength: 16);

        _ = OutputFormatters.Concise.Format(success, options);
        _ = OutputFormatters.Concise.Format(success, options);

        var before = GC.GetAllocatedBytesForCurrentThread();
        var text = OutputFormatters.Concise.Format(success, options);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.True(text.Length <= 16);
        Assert.True(
            allocated < 64_000,
            $"tiny-limit formatting of a large unsafe string allocated {allocated} bytes");
    }

    [Fact]
    public void FittingUnsafeString_IsScannedOnceAndRetainsPunctuation()
    {
        // Fits the (large) width, so the safety scan actually runs and must
        // find the late unsafe character in one early-exit pass; the row then
        // falls back to the canonical inline form "(" + raw + ", 1)".
        var raw = new string('a', 5_000) + ",";
        var text = OutputFormatters.Concise.Format(
            SequenceWithString(raw),
            Preset(width: OutputFormattingOptions.MaxSupportedPreferredLineWidth, spacing: 1));

        Assert.Equal(raw.Length + 5, text.Length);
        Assert.StartsWith("(", text, StringComparison.Ordinal);
    }

    [Fact]
    public void WideAndDeepAndSharedValues_StayBoundedUnderThePreset()
    {
        var wideItems = new Result[100_000];
        for (var i = 0; i < wideItems.Length; i++)
            wideItems[i] = new Result.Atom(i % 10);
        var wide = new RunResult.Success(
            new Algorithm.User(null, [], [], [], []),
            Result.SequenceValue.TakeOwnership(wideItems),
            []);
        Assert.True(OutputFormatters.Concise.Format(wide, Preset(maxDisplayLength: 1_000)).Length <= 1_000);

        Result deep = new Result.Atom(1);
        for (var i = 0; i < 10_000; i++)
        {
            deep = i % 2 == 0
                ? Result.ListValue.TakeOwnership([deep])
                : Result.SequenceValue.TakeOwnership([deep]);
        }

        var deepSuccess = new RunResult.Success(new Algorithm.User(null, [], [], [], []), deep, []);
        Assert.True(OutputFormatters.Concise.Format(deepSuccess, Preset(width: 1, maxDisplayLength: 500)).Length <= 500);

        Result shared = new Result.Atom(1);
        for (var i = 0; i < 30; i++)
            shared = Result.ListValue.TakeOwnership([shared, shared]);
        var sharedSuccess = new RunResult.Success(new Algorithm.User(null, [], [], [], []), shared, []);
        Assert.True(OutputFormatters.Concise.Format(sharedSuccess, Preset(maxDisplayLength: 10_000)).Length <= 10_000);
    }
}
