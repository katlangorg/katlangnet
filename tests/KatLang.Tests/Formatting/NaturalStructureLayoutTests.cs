using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>
/// Structural-complexity layout: width alone no longer decides between inline
/// and structured rendering. The natural, UNSPREAD salary program — whose
/// canonical flat text fits inside the preferred width — must expose its
/// nested value structure in Readable (all delimiters kept, multiline) and
/// Concise (safe delimiters replaced by lines and indentation), while Exact
/// stays canonical. The spread variant deliberately discards that structure,
/// and the formatters must not reconstruct it.
/// </summary>
public class NaturalStructureLayoutTests
{
    /// <summary>The acceptance options preset (KatLangWeb-compatible).</summary>
    private static OutputFormattingOptions Acceptance(
        int width = 100,
        int indent = 2,
        int spacing = 0)
        => new()
        {
            PreferredLineWidth = width,
            IndentSize = indent,
            NewLine = "\n",
            RootOutputSpacing = spacing,
            StringDelimiters = StringDelimiterMode.Never,
        };

    private const string SalaryDefinitions = """
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

        """;

    /// <summary>The primary acceptance program: natural structured results, NO spread operators.</summary>
    private const string NaturalSource = SalaryDefinitions + """
        SalaryExpenses(2000, 1, 0)
        ''
        SalaryExpenses(502, 0, 0)
        """;

    /// <summary>The secondary comparison program: spread deliberately discards the outer structure.</summary>
    private const string SpreadSource = SalaryDefinitions + """
        SalaryExpenses(2000, 1, 0)*
        ''
        SalaryExpenses(502, 0, 0)*
        """;

    private const string NaturalCanonical =
        "((neto, 1473.80), (taxes, 998.36), (social, 681.80, income, 316.20, risk, 0.36), (total, 2472.16))\n" +
        "\n" +
        "((neto, 334.72), (taxes, 286.06), (social, 171.13, income, 114.57, risk, 0.36), (total, 620.78))";

    private const string NaturalReadable =
        "(\n" +
        "  (neto, 1473.80),\n" +
        "  (taxes, 998.36),\n" +
        "  (\n" +
        "    social, 681.80,\n" +
        "    income, 316.20,\n" +
        "    risk, 0.36\n" +
        "  ),\n" +
        "  (total, 2472.16)\n" +
        ")\n" +
        "\n" +
        "(\n" +
        "  (neto, 334.72),\n" +
        "  (taxes, 286.06),\n" +
        "  (\n" +
        "    social, 171.13,\n" +
        "    income, 114.57,\n" +
        "    risk, 0.36\n" +
        "  ),\n" +
        "  (total, 620.78)\n" +
        ")";

    private const string NaturalConcise =
        "neto 1473.80\n" +
        "taxes 998.36\n" +
        "  social 681.80\n" +
        "  income 316.20\n" +
        "  risk 0.36\n" +
        "total 2472.16\n" +
        "\n" +
        "neto 334.72\n" +
        "taxes 286.06\n" +
        "  social 171.13\n" +
        "  income 114.57\n" +
        "  risk 0.36\n" +
        "total 620.78";

    // ── The natural program's value structure ────────────────────────────────

    [Fact]
    public void NaturalProgram_ProducesThreeRowsWithIntactNestedStructure()
    {
        // No spread operator anywhere in the primary program (`*` appears only
        // as multiplication inside the definitions); the spread variant is the
        // separate comparison program.
        Assert.DoesNotContain(")*", NaturalSource, StringComparison.Ordinal);
        Assert.Contains(")*", SpreadSource, StringComparison.Ordinal);

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(NaturalSource));
        Assert.Equal(3, success.OutputRows.Count);

        foreach (var rowIndex in new[] { 0, 2 })
        {
            var salary = Assert.IsType<Result.SequenceValue>(success.OutputRows[rowIndex]);
            Assert.Equal(4, salary.Items.Count);
            Assert.Equal(2, Assert.IsType<Result.SequenceValue>(salary.Items[0]).Items.Count);
            Assert.Equal(2, Assert.IsType<Result.SequenceValue>(salary.Items[1]).Items.Count);

            // The social/income/risk child stays one nested six-item sequence.
            var social = Assert.IsType<Result.SequenceValue>(salary.Items[2]);
            Assert.Equal(6, social.Items.Count);
            Assert.Equal(new Result.Str("social"), social.Items[0]);
            Assert.Equal(new Result.Str("income"), social.Items[2]);
            Assert.Equal(new Result.Str("risk"), social.Items[4]);

            Assert.Equal(2, Assert.IsType<Result.SequenceValue>(salary.Items[3]).Items.Count);
        }

        Assert.Equal(new Result.Str(string.Empty), success.OutputRows[1]);
    }

    // ── Exact stays canonical ────────────────────────────────────────────────

    [Fact]
    public void NaturalProgram_Exact_IsCanonicalAndIgnoresTheOptions()
    {
        var run = KatLangEngine.Run(NaturalSource);
        Assert.Equal(run.ToDisplayString(), OutputFormatters.Exact.Format(run, Acceptance()));
        Assert.Equal(NaturalCanonical, run.ToDisplayString().ReplaceLineEndings("\n"));
    }

    // ── Readable exposes the structure while keeping every delimiter ─────────

    [Fact]
    public void NaturalProgram_Readable_IsStructuredMultilineWithAllDelimiters()
    {
        var run = KatLangEngine.Run(NaturalSource);
        var text = OutputFormatters.Readable.Format(run, Acceptance());

        Assert.Equal(NaturalReadable, text);
        Assert.NotEqual(run.ToDisplayString().ReplaceLineEndings("\n"), text);

        // Delimiter preservation: same parenthesis count as canonical output.
        Assert.Equal(NaturalCanonical.Count(c => c == '('), text.Count(c => c == '('));
        Assert.Equal(NaturalCanonical.Count(c => c == ')'), text.Count(c => c == ')'));
        Assert.DoesNotContain("'", text, StringComparison.Ordinal);
    }

    // ── Concise renders blocks with an indented nested pair block ────────────

    [Fact]
    public void NaturalProgram_Concise_UsesIndentedStructureInsteadOfDelimiters()
    {
        var text = OutputFormatters.Concise.Format(KatLangEngine.Run(NaturalSource), Acceptance());

        Assert.Equal(NaturalConcise, text);
        Assert.DoesNotContain("(", text, StringComparison.Ordinal);
        Assert.DoesNotContain(":", text, StringComparison.Ordinal);
        Assert.DoesNotContain("=", text, StringComparison.Ordinal);
        Assert.DoesNotContain("-", text, StringComparison.Ordinal);
        Assert.Equal(text, text.ToLowerInvariant());
    }

    // ── The explicit empty-string row ────────────────────────────────────────

    [Fact]
    public void NaturalProgram_ExplicitEmptyString_IsExactlyOneBlankLine()
    {
        foreach (var formatter in OutputFormatters.All)
        {
            var text = formatter.Format(KatLangEngine.Run(NaturalSource), Acceptance())
                .ReplaceLineEndings("\n");
            Assert.Equal(1, text.Split('\n').Count(line => line.Length == 0));
            Assert.DoesNotContain("''", text, StringComparison.Ordinal);
        }
    }

    // ── Spread comparison: discarded structure is not reconstructed ──────────

    [Fact]
    public void SpreadProgram_StaysFlat_WithoutReconstructedNesting()
    {
        var spreadConcise = OutputFormatters.Concise.Format(KatLangEngine.Run(SpreadSource), Acceptance());

        // Each spread row is an independent root row: the social row joins on
        // ONE unindented line, because the parent grouping no longer exists in
        // the evaluated value and the formatter must not guess it back.
        Assert.Contains("\nsocial 681.80 income 316.20 risk 0.36\n", "\n" + spreadConcise + "\n", StringComparison.Ordinal);
        Assert.DoesNotContain("  social", spreadConcise, StringComparison.Ordinal);
        Assert.NotEqual(NaturalConcise, spreadConcise);

        // Readable likewise renders the flattened rows flat (each row is a
        // structurally simple pair sequence).
        var spreadReadable = OutputFormatters.Readable.Format(KatLangEngine.Run(SpreadSource), Acceptance());
        Assert.Contains("(social, 681.80, income, 316.20, risk, 0.36)", spreadReadable, StringComparison.Ordinal);
        Assert.DoesNotContain("  social", spreadReadable, StringComparison.Ordinal);
    }

    // ── Generic structured examples (no business meaning) ────────────────────

    [Fact]
    public void SimpleRootPair_StaysInlineAndJoins()
    {
        Assert.Equal("(name, Alice)", OutputFormatters.Readable.Format(KatLangEngine.Run("('name', 'Alice')"), Acceptance()));
        Assert.Equal("name Alice", OutputFormatters.Concise.Format(KatLangEngine.Run("('name', 'Alice')"), Acceptance()));
    }

    [Fact]
    public void RootPairSequence_MayStayFlat()
    {
        // A flat multi-pair sequence at ROOT may stay inline/joined; only as a
        // child of a larger structured parent does it become a pair block.
        Assert.Equal(
            "(city, Riga, country, Latvia)",
            OutputFormatters.Readable.Format(KatLangEngine.Run("('city', 'Riga', 'country', 'Latvia')"), Acceptance()));
        Assert.Equal(
            "city Riga country Latvia",
            OutputFormatters.Concise.Format(KatLangEngine.Run("('city', 'Riga', 'country', 'Latvia')"), Acceptance()));
    }

    [Fact]
    public void StructuredParentWithOnePairChildren()
    {
        const string source = "(('name', 'Alice'), ('total', 10))";

        Assert.Equal(
            "(\n  (name, Alice),\n  (total, 10)\n)",
            OutputFormatters.Readable.Format(KatLangEngine.Run(source), Acceptance()));

        // With root spacing, blocks are unambiguous and the parent block forms.
        Assert.Equal(
            "name Alice\ntotal 10",
            OutputFormatters.Concise.Format(KatLangEngine.Run(source), Acceptance(spacing: 1)));

        // At zero root spacing there is no indented pair block to anchor the
        // paren-hidden root block, so Concise conservatively keeps the
        // parentheses (structure still exposed multiline).
        Assert.Equal(
            "(\n  (name, Alice),\n  (total, 10)\n)",
            OutputFormatters.Concise.Format(KatLangEngine.Run(source), Acceptance()));
    }

    [Fact]
    public void StructuredParentWithNestedMultiPairChild()
    {
        const string source = "(('name', 'Alice'), ('city', 'Riga', 'country', 'Latvia'), ('total', 10))";

        Assert.Equal(
            "(\n" +
            "  (name, Alice),\n" +
            "  (\n" +
            "    city, Riga,\n" +
            "    country, Latvia\n" +
            "  ),\n" +
            "  (total, 10)\n" +
            ")",
            OutputFormatters.Readable.Format(KatLangEngine.Run(source), Acceptance()));

        // The nested pair block anchors the root block even at zero spacing.
        Assert.Equal(
            "name Alice\n  city Riga\n  country Latvia\ntotal 10",
            OutputFormatters.Concise.Format(KatLangEngine.Run(source), Acceptance()));
    }

    [Fact]
    public void UnsafeNestedPairChild_RetainsSequencePunctuation()
    {
        // 'net salary' is not a safe raw token under Never, so the nested pair
        // child keeps canonical parentheses and separators.
        const string source = "(('id', 1), ('net salary', 1473.8, 'tax', 500))";
        var text = OutputFormatters.Concise.Format(KatLangEngine.Run(source), Acceptance(spacing: 1));

        Assert.Equal("id 1\n(\n  net salary, 1473.8,\n  tax, 500\n)", text);
        Assert.DoesNotContain("'", text, StringComparison.Ordinal);
    }

    [Fact]
    public void MultiPairSequenceInsideList_KeepsElementBoundaries()
    {
        const string source = "[('city', 'Riga', 'country', 'Latvia'), 3]";

        // Inline: the list stays bracketed and the sequence keeps parentheses.
        Assert.Equal(
            "[(city, Riga, country, Latvia), 3]",
            OutputFormatters.Concise.Format(KatLangEngine.Run(source), Acceptance()));

        // Multiline: the sequence element still keeps its parentheses inside
        // the bracketed list, so the list can never appear to gain elements.
        Assert.Equal(
            "[\n  (\n    city, Riga,\n    country, Latvia\n  ),\n  3\n]",
            OutputFormatters.Concise.Format(KatLangEngine.Run(source), Acceptance(width: 20)));
    }

    // ── Safety cases around structural layout ────────────────────────────────────

    [Fact]
    public void ZeroIndent_RetainsDelimitedStructureForTheSalaryBlock()
    {
        const string source = SalaryDefinitions + "SalaryExpenses(2000, 1, 0)";
        var text = OutputFormatters.Concise.Format(KatLangEngine.Run(source), Acceptance(indent: 0));

        // Indentation cannot carry nesting, so every parenthesis stays and the
        // structure is exposed through delimited multiline layout instead.
        Assert.Equal(
            "(\n(neto, 1473.80),\n(taxes, 998.36),\n(\nsocial, 681.80,\nincome, 316.20,\nrisk, 0.36\n),\n(total, 2472.16)\n)",
            text);
    }

    [Fact]
    public void AdjacentMultiPairChildren_NeverMergeIntoOneBlock()
    {
        const string source = "(('a', 1), ('b', 1, 'c', 2), ('d', 3, 'e', 4))";
        var text = OutputFormatters.Concise.Format(KatLangEngine.Run(source), Acceptance(spacing: 1));

        // The earlier of two adjacent pair-block candidates falls back to a
        // joined line; only the later becomes an indented block, so two
        // paren-less blocks can never sit side by side.
        Assert.Equal("a 1\nb 1 c 2\n  d 3\n  e 4", text);
    }

    [Fact]
    public void ListInsidePairValue_KeepsBracketsAndParentheses()
        => Assert.Equal(
            "(scores, [1, 2])",
            OutputFormatters.Concise.Format(KatLangEngine.Run("('scores', [1, 2])"), Acceptance()));

    [Fact]
    public void StructuredValues_DoNotMasqueradeAsScalarPairs()
    {
        const string source = "('name', ('Alice', 'Bob'), 'ages', [20, 30])";
        const string expected = "(\n  name,\n  (Alice, Bob),\n  ages,\n  [20, 30]\n)";

        Assert.Equal(expected, OutputFormatters.Readable.Format(KatLangEngine.Run(source), Acceptance()));
        Assert.Equal(expected, OutputFormatters.Concise.Format(KatLangEngine.Run(source), Acceptance()));
    }

    [Fact]
    public void PairBlockAtTheFirstOrLastPosition_KeepsDistinctChildBoundaries()
    {
        Assert.Equal(
            "a 1 b 2\ntotal 3",
            OutputFormatters.Concise.Format(
                KatLangEngine.Run("(('a', 1, 'b', 2), ('total', 3))"),
                Acceptance(spacing: 1)));
        Assert.Equal(
            "name x\n  a 1\n  b 2",
            OutputFormatters.Concise.Format(
                KatLangEngine.Run("(('name', 'x'), ('a', 1, 'b', 2))"),
                Acceptance(spacing: 1)));
    }

    [Fact]
    public void UnderscoreLabels_FlowThroughPairBlocks()
        => Assert.Equal(
            "net_salary 1473.8\n  social_tax 1\n  income_tax 2\n  risk_duty 3",
            OutputFormatters.Concise.Format(
                KatLangEngine.Run("(('net_salary', 1473.8), ('social_tax', 1, 'income_tax', 2, 'risk_duty', 3))"),
                Acceptance()));

    [Fact]
    public void RootRowsAndRootSequence_StayDistinctAtZeroSpacing()
    {
        var rows = OutputFormatters.Concise.Format(KatLangEngine.Run("A = 1\nB = 2\nA()\nB()"), Acceptance());
        var sequence = OutputFormatters.Concise.Format(KatLangEngine.Run("(A() B())\nA = 1\nB = 2"), Acceptance());

        Assert.Equal("1\n2", rows);
        Assert.Equal("1 2", sequence);
        Assert.NotEqual(rows, sequence);
    }

    [Fact]
    public void EmptyValues_RemainVisibleUnderTheNewRules()
    {
        Assert.Equal("()", OutputFormatters.Concise.Format(KatLangEngine.Run("()"), Acceptance()));
        Assert.Equal("[]", OutputFormatters.Concise.Format(KatLangEngine.Run("[]"), Acceptance()));
        Assert.Equal(
            "(\n  (1, 2),\n  ()\n)",
            OutputFormatters.Readable.Format(KatLangEngine.Run("((1, 2), ())"), Acceptance()));
    }

    [Fact]
    public void ExistingColonInContent_IsNotConfusedWithInventedPunctuation()
        => Assert.Equal(
            "note: 5\n  a: 1\n  b: 2",
            OutputFormatters.Concise.Format(
                KatLangEngine.Run("(('note:', 5), ('a:', 1, 'b:', 2))"),
                Acceptance()));

    // ── Custom newline through the structured layout ─────────────────────────

    [Fact]
    public void CustomMultiCharacterNewLine_FlowsThroughBlocksAndPairBlocks()
    {
        var options = new OutputFormattingOptions
        {
            PreferredLineWidth = 100,
            IndentSize = 2,
            NewLine = "\r\n",
            RootOutputSpacing = 0,
            StringDelimiters = StringDelimiterMode.Never,
        };

        Assert.Equal(
            "name Alice\r\n  city Riga\r\n  country Latvia\r\ntotal 10",
            OutputFormatters.Concise.Format(
                KatLangEngine.Run("(('name', 'Alice'), ('city', 'Riga', 'country', 'Latvia'), ('total', 10))"),
                options));
    }

    // ── Robustness of the new structural paths ───────────────────────────────

    private static RunResult.Success SuccessOf(Result value)
        => new(new Algorithm.User(null, [], [], [], []), value, []);

    [Fact]
    public void DeeplyNestedBlocks_StayIterativeAndBounded()
    {
        Result value = new Result.SequenceValue(
            [new Result.Str("a"), new Result.Atom(1), new Result.Str("b"), new Result.Atom(2)]);
        for (var i = 0; i < 2_000; i++)
            value = new Result.SequenceValue([new Result.Str("k"), new Result.Atom(i), value]);

        var options = Acceptance(spacing: 1) with { MaxDisplayLength = 50_000 };
        var text = OutputFormatters.Concise.Format(SuccessOf(value), options);
        Assert.True(text.Length <= 50_000);
    }

    [Fact]
    public void WideParentWithManyOnePairChildren_StaysBounded()
    {
        var children = new Result[10_000];
        for (var i = 0; i < children.Length; i++)
            children[i] = new Result.SequenceValue([new Result.Str("k"), new Result.Atom(i)]);
        var value = Result.SequenceValue.TakeOwnership(children);

        var bounded = OutputFormatters.Concise.Format(
            SuccessOf(value), Acceptance(spacing: 1) with { MaxDisplayLength = 2_000 });
        Assert.True(bounded.Length <= 2_000);
        Assert.StartsWith("Display output limit of", bounded, StringComparison.Ordinal);
    }

    [Fact]
    public void LargeNestedMultiPairChild_RendersAsABoundedPairBlock()
    {
        var pairItems = new Result[4_000];
        for (var i = 0; i < pairItems.Length; i += 2)
        {
            pairItems[i] = new Result.Str("k" + i);
            pairItems[i + 1] = new Result.Atom(i);
        }

        var value = new Result.SequenceValue(
            [new Result.SequenceValue([new Result.Str("head"), new Result.Atom(1)]), Result.SequenceValue.TakeOwnership(pairItems)]);

        var text = OutputFormatters.Concise.Format(
            SuccessOf(value), Acceptance(spacing: 1) with { MaxDisplayLength = 500_000 });

        Assert.StartsWith("head 1\n  k0 0\n  k2 2", text, StringComparison.Ordinal);
        Assert.True(text.Length <= 500_000);
    }

    [Fact]
    public void DagSharedPairStructure_RendersDeterministicallyBounded()
    {
        var shared = new Result.SequenceValue(
            [new Result.Str("x"), new Result.Atom(1), new Result.Str("y"), new Result.Atom(2)]);
        var value = new Result.SequenceValue(
            [new Result.Str("a"), new Result.Atom(0), shared, new Result.Str("b"), new Result.Atom(9), shared]);

        var text = OutputFormatters.Concise.Format(SuccessOf(value), Acceptance(spacing: 1));

        // The shared pair run renders identically at both sites, each hanging
        // off its preceding line.
        Assert.Equal("a\n0\n  x 1\n  y 2\nb\n9\n  x 1\n  y 2", text);
        Assert.Equal(text, OutputFormatters.Concise.Format(SuccessOf(value), Acceptance(spacing: 1)));
    }

    [Fact]
    public void TinyWidthAndTinyLimits_StayAllOrNothingBounded()
    {
        var run = KatLangEngine.Run(NaturalSource);
        foreach (var formatter in OutputFormatters.All)
        {
            var text = formatter.Format(run, Acceptance(width: 1) with { MaxDisplayLength = 300 });
            Assert.True(text.Length <= 300, $"{formatter.Id}: {text.Length}");
        }
    }

    [Fact]
    public void AcceptanceOutputs_SweepTheDisplayLimitAllOrNothing()
    {
        var run = KatLangEngine.Run(NaturalSource);
        var natural = OutputFormatters.Concise.Format(run, Acceptance());
        Assert.Equal(NaturalConcise, natural);

        foreach (var limit in new[] { 0, 1, 10, natural.Length - 1, natural.Length, natural.Length + 1 })
        {
            var text = OutputFormatters.Concise.Format(run, Acceptance() with { MaxDisplayLength = limit });
            Assert.True(text.Length <= limit, $"limit {limit} returned {text.Length} units.");
            if (limit >= natural.Length)
                Assert.Equal(natural, text);
            else
                Assert.NotEqual(natural, text);
        }
    }
}
