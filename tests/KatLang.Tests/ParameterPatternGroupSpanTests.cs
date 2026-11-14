using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// A written sequence or list pattern group keeps its own exact extent, delimiters included, through parsing,
/// elaboration, recovery and lifting; the capture spans stay the captures' own; and nothing that no parser wrote
/// claims a location. The location is metadata: identity, equality, display, binding and evaluation never read it.
/// The extent reaches two consumers that refer to a whole group: a signature's structural slot in the semantic model,
/// and the pre-evaluation refusal of a one-item sequence pattern.
/// </summary>
public class ParameterPatternGroupSpanTests
{
    private const string Example = "F((x, y), [a, b]) = x + y + a + b\n0";
    private const string Lib = "https://katlang.org/lib.kat";

    private static readonly SourceSpan ExampleSequence = new(1, 3, 1, 9);
    private static readonly SourceSpan ExampleList = new(1, 11, 1, 17);

    private static Algorithm Member(ParseResult parse, string name)
        => Assert.Single(parse.Root.Properties, property => property.Name == name).Value;

    private static IReadOnlyList<ParameterPattern> Patterns(ParseResult parse, string name)
        => Assert.IsType<Algorithm.User>(Member(parse, name)).ParameterPatterns;

    private static IReadOnlyList<ParameterPattern> Patterns(string source, string name) => Patterns(Parser.Parse(source), name);

    private static SourceSpan? Written(ParameterPattern pattern) => ParameterPattern.GroupSource(pattern)?.WrittenSpan;

    private static IReadOnlyList<ParameterPattern> Items(ParameterPattern pattern) => ParameterPattern.StructuralItems(pattern)!;

    private static PropertySignatureInfo PlainSignature(ParseResult parse, string name)
        => Assert.Single(SemanticModelBuilder.Build(parse).FindProperties(name)).Signatures[0];

    private static RunOptions Options(string moduleSource) => new()
    {
        DownloadCode = (_, _) => ValueTask.FromResult(moduleSource),
    };

    // ── Exact extents ────────────────────────────────────────────────────────────────────────

    [Fact]
    public void TheElaboratedPatterns_KeepEachGroupsExtent_AndTheCapturesTheirOwn()
    {
        var patterns = Patterns(Example, "F");
        var sequence = Assert.IsType<SequenceValueParameterPattern>(patterns[0]);
        var list = Assert.IsType<ListValueParameterPattern>(patterns[1]);

        Assert.Equal(ExampleSequence, sequence.Source?.WrittenSpan);
        Assert.Equal(ExampleList, list.Source?.WrittenSpan);
        Assert.Equal(new SourceSpan(1, 4, 1, 5), Assert.IsType<CaptureParameterPattern>(sequence.Items[0]).Span);
        Assert.Equal(new SourceSpan(1, 7, 1, 8), Assert.IsType<CaptureParameterPattern>(sequence.Items[1]).Span);
        Assert.Equal(new SourceSpan(1, 12, 1, 13), Assert.IsType<CaptureParameterPattern>(list.Items[0]).Span);
        Assert.Equal(new SourceSpan(1, 15, 1, 16), Assert.IsType<CaptureParameterPattern>(list.Items[1]).Span);
    }

    [Fact]
    public void TheParsedClausePatterns_KeepEachGroupsExtent_AndTheArgumentListClaimsNone()
    {
        var family = Parser.Parse("F((x, y), [a, b]) = x\nF((1, 2), [3]) = 0\n0");
        var branches = Assert.IsType<Algorithm.Conditional>(Member(family, "F")).Branches;

        var head = Assert.IsType<Pattern.SequenceValue>(branches[0].Pattern);
        Assert.Null(head.Span);
        Assert.Equal(ExampleSequence, Assert.IsType<Pattern.SequenceValue>(head.Items[0]).Span);
        Assert.Equal(ExampleList, Assert.IsType<Pattern.ListValue>(head.Items[1]).Span);

        var literals = Assert.IsType<Pattern.SequenceValue>(branches[1].Pattern);
        Assert.Equal(new SourceSpan(2, 3, 2, 9), Assert.IsType<Pattern.SequenceValue>(literals.Items[0]).Span);
        Assert.Equal(new SourceSpan(2, 11, 2, 14), Assert.IsType<Pattern.ListValue>(literals.Items[1]).Span);
    }

    [Fact]
    public void ALoneGroupHead_LocatesTheGroup_NeverTheHeadsOwnParentheses()
    {
        var pattern = Assert.Single(Patterns("F((x, y)) = x + y\n0", "F"));
        Assert.Equal(new SourceSpan(1, 3, 1, 9), Written(pattern));
    }

    [Fact]
    public void EmptyGroups_AreLocated_WithNoCaptureToApproximateThem()
    {
        var patterns = Patterns("F((), [ ]) = 1\n0", "F");
        Assert.Equal(new SourceSpan(1, 3, 1, 5), Written(patterns[0]));
        Assert.Equal(new SourceSpan(1, 7, 1, 10), Written(patterns[1]));
        Assert.Empty(Items(patterns[0]));
        Assert.Empty(Items(patterns[1]));
    }

    [Fact]
    public void NestedGroups_KeepInnerAndOuterExtentsApart()
    {
        var outer = Patterns("F(((a, b), [c, (d, e)]), z) = a\n0", "F")[0];
        Assert.Equal(new SourceSpan(1, 3, 1, 24), Written(outer));

        var inner = Items(outer);
        Assert.Equal(new SourceSpan(1, 4, 1, 10), Written(inner[0]));
        Assert.Equal(new SourceSpan(1, 12, 1, 23), Written(inner[1]));
        Assert.Equal(new SourceSpan(1, 16, 1, 22), Written(Items(inner[1])[1]));
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void AMultilineGroup_SpansFromOpenerToCloser_InTheLexersCoordinates(string newline)
    {
        var source = $"F((x,{newline}    y),{newline}  [  a,{newline} b ]) = x + y + a + b{newline}0";
        var patterns = Patterns(source, "F");
        Assert.Equal(new SourceSpan(1, 3, 2, 7), Written(patterns[0]));
        Assert.Equal(new SourceSpan(3, 3, 4, 5), Written(patterns[1]));
    }

    // ── Recovery ─────────────────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("F((*a, *b), z) = a\n0", 3, 11)]
    [InlineData("F([*a, *b], z) = a\n0", 3, 11)]
    public void ACollectorRecoveryRewrite_IsTheSameWrittenGroup(string source, int start, int end)
    {
        var parse = Parser.Parse(source);
        Assert.Contains(parse.Diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.InvalidCollectingBinding);
        var group = Patterns(parse, "F")[0];
        Assert.Equal(new SourceSpan(1, start, 1, end), Written(group));
        Assert.Single(Items(group), static item => item is CaptureParameterPattern { Kind: ParameterKind.Collecting });
    }

    [Fact]
    public void AMetaRecoveryRewrite_IsTheSameWrittenGroup()
    {
        var parse = Parser.Parse("F((meta a, b), z) = a\n0");
        Assert.Contains(parse.Diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.InvalidMetaParameter);
        var group = Patterns(parse, "F")[0];
        Assert.Equal(new SourceSpan(1, 3, 1, 14), Written(group));
        Assert.DoesNotContain(Items(group), static item => item is CaptureParameterPattern { Kind: ParameterKind.Meta });
    }

    [Theory]
    [InlineData("F((x = 1), z) = x\n0")]
    [InlineData("F([x = 1], z) = x\n0")]
    public void AGroupWithNoRealCloser_ClaimsNoExtent(string source)
    {
        var parse = Parser.Parse(source);
        Assert.True(parse.HasErrors);
        Assert.Null(Written(Patterns(parse, "F")[0]));
    }

    [Fact]
    public void AGroupWithAMalformedItem_KeepsItsRealDelimiters()
    {
        var parse = Parser.Parse("F((x, @), z) = x\n0");
        Assert.True(parse.HasErrors);
        Assert.Equal(new SourceSpan(1, 3, 1, 9), Written(Patterns(parse, "F")[0]));
    }

    [Fact]
    public void AnImmediateSingletonDiagnostic_StaysAtTheRealDelimiters()
    {
        var diagnostic = Assert.Single(Parser.Parse("F((x)) = x\nF(7)").Diagnostics,
            static diagnostic => diagnostic.Code == DiagnosticCode.SingletonSequencePattern);
        Assert.Equal(new SourceSpan(1, 3, 1, 6), diagnostic.Span);
    }

    // ── Structural rewrites keep provenance ──────────────────────────────────────────────────

    [Fact]
    public void WithStructuralItems_AndFreezing_KeepTheWrittenGroup()
    {
        var source = new PatternGroupSource(ExampleSequence);
        var inner = new ListValueParameterPattern([new CaptureParameterPattern("a")]) { Source = new(ExampleList) };
        var group = new SequenceValueParameterPattern([inner, new CaptureParameterPattern("b")]) { Source = source };

        Assert.Equal(source, ParameterPattern.GroupSource(ParameterPattern.WithStructuralItems(group, [inner])));

        var frozen = new ImplicitSignatureTemplateInterner(observations: null, resources: null, CancellationToken.None).Freeze(group);
        Assert.NotSame(group, frozen);
        Assert.Equal(source, ParameterPattern.GroupSource(frozen));
        Assert.Equal(ExampleList, Written(Items(frozen)[0]));
    }

    [Fact]
    public void TheCollectorRecoveryOfAParameterPattern_KeepsTheWrittenGroup()
    {
        var group = new ListValueParameterPattern(
            [new CaptureParameterPattern("a", Kind: ParameterKind.Collecting), new CaptureParameterPattern("b", Kind: ParameterKind.Collecting)])
        {
            Source = new(ExampleList),
        };

        var recovered = Assert.Single(ParameterPattern.KeepFirstCollectingCapturePerLevel([group]));
        Assert.NotSame(group, recovered);
        Assert.Equal(ExampleList, Written(recovered));
    }

    [Fact]
    public void ALiftedGroup_IsTheCalleesOwnRecord_ReadByEveryOwnerAtOneLocation()
    {
        var parse = Parser.Parse("F((x, y), [a]) = x + y + a\nG = F + 1\nH = F + 2\n0");
        var callee = Patterns(parse, "F")[0];
        var first = Patterns(parse, "G")[0];
        var second = Patterns(parse, "H")[0];

        Assert.Equal(ExampleSequence, Written(callee));
        Assert.Equal(ExampleSequence, Written(first));
        Assert.Equal(ExampleSequence, Written(second));
        Assert.Same(first, second);
    }

    [Fact]
    public void AFilteredLift_KeepsItsOrigin_ButNotAWrittenLocation_AndCaptureSpansStayExact()
    {
        const string Source = "P(x, [x, a]) = x + a\nQ = P + 1\n0";
        var patterns = Patterns(Source, "Q");
        var capture = Assert.IsType<CaptureParameterPattern>(patterns[0]);
        var list = Assert.IsType<ListValueParameterPattern>(patterns[1]);

        Assert.Equal(new SourceSpan(1, 3, 1, 4), capture.Span);
        Assert.Equal("[a]", list.DisplayName);
        Assert.Null(list.Source?.WrittenSpan);
        Assert.Equal(new PatternGroupSource(new SourceSpan(1, 6, 1, 12), IsFiltered: true), list.Source);
        Assert.Equal(new SourceSpan(1, 10, 1, 11), Assert.IsType<CaptureParameterPattern>(Assert.Single(list.Items)).Span);
    }

    [Fact]
    public void ASequenceGroupNormalizedAway_LeavesTheSurvivingCaptureItsOwnSpan()
    {
        var patterns = Patterns("P(x, (x, a)) = x + a\nQ = P + 1\n0", "Q");
        Assert.Equal(["x", "a"], patterns.Select(static pattern => pattern.DisplayName));
        Assert.Equal(new SourceSpan(1, 10, 1, 11), Assert.IsType<CaptureParameterPattern>(patterns[1]).Span);
    }

    [Fact]
    public void ABranchBinderView_OfAGroupHoldingALiteral_IsFiltered()
    {
        var head = Assert.IsType<Algorithm.Conditional>(Member(Parser.Parse("F((0, y), [z]) = y\nF(a, b) = a\n0"), "F")).Branches[0].Pattern;
        var patterns = ImplicitArgumentResolver.BranchBinderParameterPatterns(head);

        Assert.Equal(new PatternGroupSource(new SourceSpan(1, 3, 1, 9), IsFiltered: true), ParameterPattern.GroupSource(patterns[0]));
        Assert.Equal(new SourceSpan(1, 11, 1, 14), Written(patterns[1]));
    }

    // ── Generated, host-built and imported patterns claim nothing ────────────────────────────

    [Fact]
    public void AnUnpackingReceiver_HasNoDelimitersToLocate()
    {
        var target = Assert.IsType<Algorithm.User>(Member(Parser.Parse("a, b = 1, 2\na + b"), "a"));
        var call = Assert.IsType<Expr.Call>(Assert.Single(target.Output));
        var helper = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(call.Function).Algorithm);

        var receiver = Assert.IsType<UnpackingParameterPattern>(Assert.Single(helper.ParameterPatterns));
        Assert.Null(ParameterPattern.GroupSource(receiver));
        Assert.Null(ParameterPattern.GroupSource(ParameterPattern.WithFilteredStructuralItems(receiver, receiver.Items)));
    }

    [Fact]
    public void HostBuiltPatterns_HaveNoLocation()
    {
        Assert.Null(ParameterPattern.GroupSource(new SequenceValueParameterPattern([])));
        Assert.Null(ParameterPattern.GroupSource(new ListValueParameterPattern([])));
        Assert.Null(ParameterPattern.GroupSource(new CaptureParameterPattern("x", new SourceSpan(1, 1, 1, 2))));
        Assert.Null(new Pattern.SequenceValue([]).Span);
        Assert.Null(new Pattern.ListValue([]).Span);
    }

    [Fact]
    public async Task AnImportedGroup_CarriesNoModuleCoordinate_EvenWithNoLocatedItem()
    {
        // `()`, `[]` and literal-only groups hold nothing else a rewrite would have to strip.
        const string Module = "\n\npublic F((x, y), [a], (), []) = x + y + a\npublic G((1, 2), ()) = 3\npublic G((3, 4), ()) = 4";
        var parse = await Parser.ParseAsync("open '" + Lib + "'\nZ = F\n0", Options(Module));
        Assert.False(parse.HasErrors);
        var module = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(parse.Root.Opens)).Algorithm);

        var signature = Assert.IsType<Algorithm.User>(Assert.Single(module.Properties, static property => property.Name == "F").Value);
        Assert.Equal(4, signature.ParameterPatterns.Count);
        Assert.All(signature.ParameterPatterns, static pattern => Assert.Null(ParameterPattern.GroupSource(pattern)));

        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(module.Properties, static property => property.Name == "G").Value);
        Assert.All(family.Branches, static branch =>
        {
            var head = Assert.IsType<Pattern.SequenceValue>(branch.Pattern);
            Assert.All(head.Items, static item => Assert.Null(Assert.IsType<Pattern.SequenceValue>(item).Span));
        });

        var parameters = PlainSignature(parse, "Z").Parameters;
        Assert.Equal(4, parameters.Count);
        Assert.All(parameters, static parameter =>
        {
            Assert.Null(parameter.Span);
            Assert.Empty(parameter.OriginSpans);
        });
    }

    // ── Metadata stays metadata ──────────────────────────────────────────────────────────────

    [Fact]
    public void GroupLocations_AreTransparentToParameterPatternIdentity()
    {
        IReadOnlyList<ParameterPattern> items = [new CaptureParameterPattern("x")];
        ParameterPattern[] pairs =
        [
            new SequenceValueParameterPattern(items),
            new SequenceValueParameterPattern(items) { Source = new(ExampleSequence) },
            new ListValueParameterPattern(items),
            new ListValueParameterPattern(items) { Source = new(ExampleList, IsFiltered: true) },
        ];

        foreach (var (plain, located) in new[] { (pairs[0], pairs[1]), (pairs[2], pairs[3]) })
        {
            Assert.Equal(plain, located);
            Assert.Equal(plain.GetHashCode(), located.GetHashCode());
            Assert.Equal(plain.ToString(), located.ToString());
            Assert.Equal(plain.DisplayName, located.DisplayName);
            Assert.True(ParameterPattern.ContractComparer.Equals(plain, located));
            Assert.Equal(ParameterPattern.ContractComparer.GetHashCode(plain), ParameterPattern.ContractComparer.GetHashCode(located));
        }
    }

    [Fact]
    public void GroupLocations_AreTransparentToPatternIdentity()
    {
        IReadOnlyList<Pattern> items = [new Pattern.Bind("x")];
        Pattern[][] pairs =
        [
            [new Pattern.SequenceValue(items), new Pattern.SequenceValue(items) { Span = ExampleSequence }],
            [new Pattern.ListValue(items), new Pattern.ListValue(items) { Span = ExampleList }],
        ];

        foreach (var pair in pairs)
        {
            Assert.Equal(pair[0], pair[1]);
            Assert.Equal(pair[0].GetHashCode(), pair[1].GetHashCode());
            Assert.Equal(pair[0].ToString(), pair[1].ToString());
        }
    }

    [Fact]
    public void ARecordCopy_KeepsTheLocation_AndTheDeconstructionContractIsUnchanged()
    {
        var sequence = new Pattern.SequenceValue([]) { Span = ExampleSequence };
        Assert.Equal(ExampleSequence, (sequence with { }).Span);
        sequence.Deconstruct(out var items);
        Assert.Same(sequence.Items, items);
    }

    [Fact]
    public async Task EvaluationAndCallFailures_ReadNoGroupLocation()
    {
        const string Definition = "public F((x, y), [a, b]) = x + y + a + b";
        var local = KatLangEngine.Run(Definition + "\nF((1, 2), [3, 4])");
        var imported = await KatLangEngine.RunAsync("open '" + Lib + "'\nF((1, 2), [3, 4])", Options(Definition));
        Assert.Equal(Assert.IsType<RunResult.Success>(local).Value, Assert.IsType<RunResult.Success>(imported).Value);

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(Definition + "\nF(1, [3, 4])"));
        Assert.Equal(2, Assert.Single(failure.Errors).Span?.Start.Line);
    }

    // ── Consumers ────────────────────────────────────────────────────────────────────────────

    [Fact]
    public void TheEditorSignature_LocatesEachStructuralSlotAtItsWrittenGroup()
    {
        var parameters = PlainSignature(Parser.Parse(Example), "F").Parameters;
        Assert.Equal(["(x, y)", "[a, b]"], parameters.Select(static parameter => parameter.DisplayName));
        Assert.Equal([ExampleSequence, ExampleList], parameters.Select(static parameter => parameter.Span!.Value));
        Assert.All(parameters, static parameter => Assert.Empty(parameter.OriginSpans));
    }

    [Fact]
    public void TheEditorSignature_LeavesACaptureSlotBesideAGroupUnchanged()
    {
        var parameters = PlainSignature(Parser.Parse("F(a, (x, y)) = a + x + y\n0"), "F").Parameters;
        Assert.Null(parameters[0].Span);
        Assert.Equal(new SourceSpan(1, 6, 1, 12), parameters[1].Span);
    }

    [Fact]
    public void TheEditorSignature_OfAFamily_LocatesAStructuralSlotInItsFirstHead()
    {
        var parameters = PlainSignature(Parser.Parse("F((x, y), [a]) = x\nF(b, c) = b\n0"), "F").Parameters;
        Assert.Equal(new SourceSpan(1, 3, 1, 9), parameters[0].Span);
        Assert.Equal(new SourceSpan(1, 11, 1, 14), parameters[1].Span);
    }

    [Fact]
    public void AnInferredStructuralSlot_NamesItsWrittenGroupAsAnOrigin_NotAsItsDeclaration()
    {
        var parameters = PlainSignature(Parser.Parse("F((x, y), [a]) = x + y + a\nG = F + 1\n0"), "G").Parameters;
        Assert.Equal(PropertyParameterKind.Implicit, parameters[0].Kind);
        Assert.Null(parameters[0].Span);
        Assert.Equal(new SourceSpan(1, 3, 1, 9), Assert.Single(parameters[0].OriginSpans));
        Assert.Equal(new SourceSpan(1, 11, 1, 14), Assert.Single(parameters[1].OriginSpans));
    }

    [Fact]
    public void AnInferredFilteredSlot_NamesTheGroupItCameFrom()
    {
        var parameters = PlainSignature(Parser.Parse("P(x, [x, a]) = x + a\nQ = P + 1\n0"), "Q").Parameters;
        var filtered = Assert.Single(parameters, static parameter => parameter.DisplayName == "[a]");
        Assert.Null(filtered.Span);
        Assert.Equal(new SourceSpan(1, 6, 1, 12), Assert.Single(filtered.OriginSpans));
    }

    [Fact]
    public void AGroupLiftedIntoARecursiveGroup_KeepsItsLocation()
    {
        const string Source = "F((p, q)) = p + q\nA = F + B\nB = A + 1\n0";
        var parameter = PlainSignature(Parser.Parse(Source), "A").Parameters[0];
        Assert.Equal("(p, q)", parameter.DisplayName);
        Assert.Equal(new SourceSpan(1, 3, 1, 9), Assert.Single(parameter.OriginSpans));
    }

    [Fact]
    public void TheModelsOfOneDocument_HaveEqualStructuralSlots()
    {
        var first = PlainSignature(Parser.Parse(Example), "F").Parameters[0];
        var second = PlainSignature(Parser.Parse(Example), "F").Parameters[0];
        Assert.Equal(first, second);

        var inferred = "F((x, y)) = x + y\nG = F + 1\n0";
        Assert.Equal(PlainSignature(Parser.Parse(inferred), "G").Parameters[0], PlainSignature(Parser.Parse(inferred), "G").Parameters[0]);
    }

    [Theory]
    [InlineData("F((x)) = x\nF(7)", 1, 3, 1, 6)]
    [InlineData("F(a, [(  x  )]) = x\nF(7)", 1, 7, 1, 14)]
    [InlineData("G(0) = 0\nG((x)) = x\nG(7)", 2, 3, 2, 6)]
    public async Task ARefusedRecoveredSingleton_IsReportedAtItsWrittenGroup(string source, int line, int column, int endLine, int endColumn)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseAllowingDiagnostics(source).Root);
        var expected = new EvalError.IllegalInEval(Parser.SingletonSequencePatternDiagnostic) { Span = new SourceSpan(line, column, endLine, endColumn) };
        Assert.Equal(expected, Evaluator.Run(program).Error);
        Assert.Equal(expected, (await Evaluator.RunAsync(program)).Error);
    }

    [Fact]
    public void ARefusedHostBuiltSingleton_FallsBackToNoLocation()
    {
        var bad = new Algorithm.User(null, [new SequenceValueParameterPattern([new CaptureParameterPattern("x")])], [], [],
            OutputBundle.From([new Expr.Param("x")]));
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("Bad", bad)], OutputBundle.From([new Expr.Num(1)])));

        Assert.Equal(new EvalError.IllegalInEval(Parser.SingletonSequencePatternDiagnostic), Evaluator.Run(program).Error);
    }
}
