using System.Globalization;
using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// Direct golden tests of <see cref="LeanAstEncoder"/>. Both differential
/// corpora now DERIVE their Lean programs through the encoder, so the encoder
/// itself is the fidelity-bearing artifact: every expected string here is a
/// manually reviewed constant (never produced by the encoder at authoring
/// time), organized around the semantics-bearing metadata whose silent loss
/// was the Track 9 failure mode — parameter shape, exposure, opens, patterns,
/// elaboration-produced structure — plus the fail-loud contract for
/// everything the encoder deliberately does not model.
/// </summary>
public class LeanAstEncoderTests
{
    private static string EncodeSource(string source)
        => LeanAstEncoder.EncodeProgram(SourceProvenance.ParseValid(source).Root);

    // ----- parameter channel: the three constructor spellings -----------------

    [Fact]
    public void FixedParameters_EncodeAsPlainAlg()
    {
        Assert.Equal(
            ".algorithmExpr (alg [] [] "
            + "[privateProp \"F\" (alg [\"a\", \"b\"] [] [] [(.binary .add (.param \"a\") (.param \"b\"))])] "
            + "[(.call (.resolve \"F\") [.num 1, .num 2])])",
            EncodeSource("F(a, b) = a + b\nF(1, 2)"));
    }

    [Fact]
    public void CollectingParameter_EncodesAsAlgWithParameters()
    {
        Assert.Equal(
            ".algorithmExpr (alg [] [] "
            + "[privateProp \"F\" (algWithParameters [{ name := \"a\", kind := .collecting }] [] [] [.param \"a\"])] "
            + "[(.call (.resolve \"F\") [.num 1, .num 2])])",
            EncodeSource("F(*a) = a\nF(1, 2)"));
    }

    [Fact]
    public void MixedCollectingParameterList_PreservesPositionAndKinds()
    {
        Assert.Equal(
            ".algorithmExpr (alg [] [] "
            + "[privateProp \"F\" (algWithParameters [{ name := \"h\" }, { name := \"t\", kind := .collecting }, "
            + "{ name := \"z\" }] [] [] [.param \"t\"])] "
            + "[(.call (.resolve \"F\") [.num 1, .num 2, .num 3])])",
            EncodeSource("F(h, *t, z) = t\nF(1, 2, 3)"));
    }

    [Fact]
    public void CollectingParameter_PreservesFrontAndEndPositions()
    {
        Assert.Equal(
            ".algorithmExpr (alg [] [] [privateProp \"F\" (algWithParameters "
            + "[{ name := \"head\", kind := .collecting }, { name := \"last\" }] [] [] [.param \"head\"])] "
            + "[(.call (.resolve \"F\") [.num 1, .num 2])])",
            EncodeSource("F(*head, last) = head\nF(1, 2)"));

        Assert.Equal(
            ".algorithmExpr (alg [] [] [privateProp \"F\" (algWithParameters "
            + "[{ name := \"first\" }, { name := \"tail\", kind := .collecting }] [] [] [.param \"tail\"])] "
            + "[(.call (.resolve \"F\") [.num 1, .num 2])])",
            EncodeSource("F(first, *tail) = tail\nF(1, 2)"));
    }

    /// <summary>
    /// Pattern SHAPE is load-bearing: <c>F((x))</c> is a singleton
    /// sequence-value pattern, a DIFFERENT program from flat <c>F(x)</c>, and
    /// the flattened parameter list cannot distinguish the two — the original
    /// Track 9 erase-the-pattern failure mode.
    /// </summary>
    [Fact]
    public void SequenceValueParameterPattern_EncodesAsAlgWithParameterPatterns()
    {
        Assert.Equal(
            ".algorithmExpr (alg [] [] "
            + "[privateProp \"PairSum\" (algWithParameterPatterns [.sequenceValue [.capture { name := \"x\" }, "
            + ".capture { name := \"y\" }]] [] [] [(.binary .add (.param \"x\") (.param \"y\"))])] "
            + "[(.call (.resolve \"PairSum\") [(.capture [.num 1, .num 2])])])",
            EncodeSource("PairSum((x, y)) = x + y\nPairSum((1, 2))"));
    }

    [Fact]
    public void NestedCollectingPattern_KeepsKindInsideThePattern()
    {
        Assert.Equal(
            ".algorithmExpr (alg [] [] "
            + "[privateProp \"Collect\" (algWithParameterPatterns [.sequenceValue [.capture { name := \"h\" }, "
            + ".capture { name := \"t\", kind := .collecting }]] [] [] [.param \"t\"])] "
            + "[(.call (.resolve \"Collect\") [(.capture [.num 1, .num 2, .num 3])])])",
            EncodeSource("Collect((h, *t)) = t\nCollect((1, 2, 3))"));
    }

    [Fact]
    public void ParameterPatternShape_PreservesSingletonNestedMixedAndDuplicateCaptures()
    {
        static Algorithm.User AlgorithmWith(params ParameterPattern[] patterns) => new(
            Parent: null,
            Parameters: ParameterPattern.FlattenCaptures(patterns),
            Opens: [],
            Properties: [],
            Output: [new Expr.Num(1)])
        {
            ParameterPatterns = patterns,
        };

        Assert.Equal(
            "(algWithParameterPatterns [.sequenceValue [.capture { name := \"x\" }]] [] [] [.num 1])",
            LeanAstEncoder.EncodeAlgorithm(AlgorithmWith(
                new SequenceValueParameterPattern([new CaptureParameterPattern("x")]))));

        Assert.Equal(
            "(algWithParameterPatterns [.capture { name := \"head\" }, .sequenceValue "
            + "[.sequenceValue [.capture { name := \"x\" }, .capture { name := \"middle\", kind := .collecting }], "
            + ".capture { name := \"tail\" }]] [] [] [.num 1])",
            LeanAstEncoder.EncodeAlgorithm(AlgorithmWith(
                new CaptureParameterPattern("head"),
                new SequenceValueParameterPattern(
                [
                    new SequenceValueParameterPattern(
                    [
                        new CaptureParameterPattern("x"),
                        new CaptureParameterPattern("middle", Kind: ParameterKind.Collecting),
                    ]),
                    new CaptureParameterPattern("tail"),
                ]))));

        Assert.Equal(
            "(alg [\"x\", \"x\"] [] [] [.num 1])",
            LeanAstEncoder.EncodeAlgorithm(AlgorithmWith(
                new CaptureParameterPattern("x"),
                new CaptureParameterPattern("x"))));
    }

    /// <summary>
    /// Assignment deconstruction encodes the REAL parser elaboration: the RHS
    /// hoisted into one synthesized shared property (<c>$deconstruct$N</c>) and
    /// one helper-call property per WRITTEN target — never a hand-simplified
    /// shape with invented names or omitted sibling targets.
    /// </summary>
    [Fact]
    public void AssignmentDeconstruction_EncodesTheRealElaboration()
    {
        Assert.Equal(
            ".algorithmExpr (alg [] [] ["
            + "privateProp \"$deconstruct$0\" (alg [] [] [] [(.capture [.num 1, .num 2])]), "
            + "privateProp \"x\" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns "
            + "[.sequenceValue [.capture { name := \"x\" }, .capture { name := \"y\" }]] [] [] [.param \"x\"])) "
            + "[.resolve \"$deconstruct$0\"])]), "
            + "privateProp \"y\" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns "
            + "[.sequenceValue [.capture { name := \"x\" }, .capture { name := \"y\" }]] [] [] [.param \"y\"])) "
            + "[.resolve \"$deconstruct$0\"])])"
            + "] [.resolve \"x\"])",
            EncodeSource("x, y = (1, 2)\nx"));
    }

    [Fact]
    public void MultipleDeconstructions_UseDeterministicDistinctGeneratedNames()
    {
        var encoded = EncodeSource("a, b = 1, 2\nc, d = 3, 4\na, d");

        Assert.Contains("privateProp \"$deconstruct$0\"", encoded, StringComparison.Ordinal);
        Assert.Contains("privateProp \"$deconstruct$1\"", encoded, StringComparison.Ordinal);
        Assert.Equal(1, encoded.Split("privateProp \"a\"", StringSplitOptions.None).Length - 1);
        Assert.Equal(1, encoded.Split("privateProp \"b\"", StringSplitOptions.None).Length - 1);
        Assert.Equal(1, encoded.Split("privateProp \"c\"", StringSplitOptions.None).Length - 1);
        Assert.Equal(1, encoded.Split("privateProp \"d\"", StringSplitOptions.None).Length - 1);
    }

    // ----- property metadata: visibility and exposure -------------------------

    [Fact]
    public void PropertyVisibilityAndExposure_AreEncodedDistinctly()
    {
        // `A = { X = 1 }` elaborates X as PRIVATE; `public` flips only the
        // visibility bit; a public member capturing an ancestor parameter is
        // public but NOT exported. All three must stay distinguishable.
        Assert.Equal(
            ".algorithmExpr (alg [] [] "
            + "[privateProp \"A\" (alg [] [] [privateProp \"X\" (alg [] [] [] [.num 1])] [])] "
            + "[(.dotCall (.resolve \"A\") \"X\" none)])",
            EncodeSource("A = {\n    X = 1\n}\nA.X"));

        Assert.Equal(
            ".algorithmExpr (alg [] [] "
            + "[privateProp \"A\" (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 1])] [])] "
            + "[(.dotCall (.resolve \"A\") \"X\" none)])",
            EncodeSource("A = {\n    public X = 1\n}\nA.X"));

        Assert.Equal(
            ".algorithmExpr (alg [] [] "
            + "[privateProp \"Lib\" (alg [\"p\"] [] [publicLocalProp \"X\" .localCapturedAncestorParams "
            + "(alg [] [] [] [(.binary .add (.param \"p\") (.num 1))])] [.resolve \"X\"])] "
            + "[(.call (.resolve \"Lib\") [.num 7])])",
            EncodeSource("Lib(p) = {\n    public X = p + 1\n    X\n}\nLib(7)"));
    }

    // ----- conditional algorithms ---------------------------------------------

    [Fact]
    public void MultiClauseFamily_EncodesAsConditionalWithOrderedBranches()
    {
        Assert.Equal(
            ".algorithmExpr (alg [] [] "
            + "[privateProp \"F\" (.conditional none [] "
            + "[⟨.litInt 0, (alg [] [] [] [.num 100])⟩, ⟨.bind \"n\", (alg [] [] [] [.param \"n\"])⟩])] "
            + "[(.call (.resolve \"F\") [.num 7])])",
            EncodeSource("F(0) = 100\nF(n) = n\nF(7)"));
    }

    [Fact]
    public void ElaboratedPropertyCollectionOrder_IsEncodedWithoutReconstruction()
    {
        // Clause-family properties are appended after plain properties by the
        // authoritative parser even when written first.
        Assert.Equal(
            ".algorithmExpr (alg [] [] [privateProp \"x\" (alg [] [] [] [.num 1]), "
            + "privateProp \"I\" (alg [\"a\"] [] [] [.param \"a\"])] "
            + "[(.call (.resolve \"I\") [.resolve \"x\"])])",
            EncodeSource("I(a) = a\nx = 1\nI(x)"));
    }

    // ----- expression forms added for corpus coverage -------------------------

    [Fact]
    public void IndexAndStringAndList_EncodeCanonically()
    {
        Assert.Equal(
            ".algorithmExpr (alg [] [] [privateProp \"x\" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] "
            + "[(.index (.resolve \"x\") (.num 0))])",
            EncodeSource("x = [1, 2]\nx:0"));

        Assert.Equal(
            ".algorithmExpr (alg [] [] [] [(.binary .eq (.stringLiteral \"ab\") (.stringLiteral \"ab\"))])",
            EncodeSource("'ab' == 'ab'"));
    }

    [Fact]
    public void InternalSequenceConstruct_EncodesFromTheConstructedAst()
    {
        // Internal node: no source form exists; the internal-node differential
        // cases derive their Lean text from the same hand-built AST.
        var node = new Expr.SequenceConstruct(new Expr.EmptySequence(0), new Expr.Num(1));
        Assert.Equal("(.sequenceConstruct (.emptySequence 0) (.num 1))", LeanAstEncoder.EncodeExpr(node));
    }

    [Fact]
    public void OpensEncodeInDeclaredOrder_IncludingDuplicates()
    {
        // Dedup is an EVALUATION rule (Lean resolveAllOpens), not an encoding
        // rule: the written duplicate target must survive encoding so both
        // sides decide dedup themselves.
        Assert.Equal(
            ".algorithmExpr (alg [] [] ["
            + "privateProp \"Lib\" (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 1])] []), "
            + "privateProp \"A\" (alg [] [.resolve \"Lib\", .resolve \"Lib\"] [] [.resolve \"X\"])"
            + "] [.resolve \"A\"])",
            EncodeSource("Lib = {\n    public X = 1\n}\nA = {\n    open Lib, Lib\n    X\n}\nA"));
    }

    // ----- fail-loud contract -------------------------------------------------

    [Fact]
    public void IntegerNumbers_AreEncodedByValue_NotBySourceSpellingOrGeneralFormat()
    {
        Assert.Equal(".algorithmExpr (alg [] [] [] [.num 1000])", EncodeSource("1e3"));
        Assert.Equal(
            ".num " + "1" + new string('0', 100),
            LeanAstEncoder.EncodeExpr(new Expr.Num(
                Decimal128.Parse("1e100", CultureInfo.InvariantCulture))));
        Assert.Equal(
            ".num (-42)",
            LeanAstEncoder.EncodeExpr(new Expr.Num(
                Decimal128.Parse("-42", CultureInfo.InvariantCulture))));
    }

    [Fact]
    public void NonIntegerNonFiniteAndNegativeZeroNumbers_AreRefusedNotApproximated()
    {
        // The Lean core models Int; a fractional literal must not silently
        // print as invalid (or rounded) Lean.
        var fractional = new Expr.Num(SourceProvenance.ParseValid("0.5").Root.Output[0] is Expr.Num n
            ? n.Value
            : throw new InvalidOperationException("expected a numeric literal"));
        var ex = Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeExpr(fractional));
        Assert.Contains("0.5", ex.Message);

        Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeExpr(
            new Expr.Num(Decimal128.Parse("0.1", CultureInfo.InvariantCulture))));
        Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeExpr(new Expr.Num(Decimal128.PositiveInfinity)));
        Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeExpr(new Expr.Num(Decimal128.NegativeInfinity)));
        Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeExpr(new Expr.Num(Decimal128.NaN)));

        var negativeZero = Decimal128.Parse("-0", CultureInfo.InvariantCulture);
        var zero = Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeExpr(new Expr.Num(negativeZero)));
        Assert.Contains("negative zero", zero.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void StringEscaping_IsLeanFaithful_AndControlCharactersAreRefused()
    {
        Assert.Equal(
            ".stringLiteral \"say \\\"hi\\\" and a back\\\\slash\"",
            LeanAstEncoder.EncodeExpr(new Expr.StringLiteral("say \"hi\" and a back\\slash")));
        Assert.Throws<NotSupportedException>(
            () => LeanAstEncoder.EncodeExpr(new Expr.StringLiteral("line\nbreak")));

        Assert.Equal(".stringLiteral \"\"", LeanAstEncoder.EncodeExpr(new Expr.StringLiteral("")));
        Assert.Equal(".stringLiteral \"café\"", LeanAstEncoder.EncodeExpr(new Expr.StringLiteral("café")));
        Assert.Equal(".stringLiteral \"e\u0301\"", LeanAstEncoder.EncodeExpr(new Expr.StringLiteral("e\u0301")));
        Assert.Equal(".stringLiteral \"😺\"", LeanAstEncoder.EncodeExpr(new Expr.StringLiteral("😺")));

        foreach (var control in new[] { '\t', '\r', '\n', '\u0000', '\u001f', '\u007f' })
        {
            var ex = Assert.Throws<NotSupportedException>(
                () => LeanAstEncoder.EncodeExpr(new Expr.StringLiteral("a" + control + "b")));
            Assert.Contains($"U+{(int)control:X4}", ex.Message);
        }

        Assert.Throws<NotSupportedException>(
            () => LeanAstEncoder.EncodeExpr(new Expr.StringLiteral("\uD800")));
        Assert.Throws<NotSupportedException>(
            () => LeanAstEncoder.EncodeExpr(new Expr.StringLiteral("\uDC00")));
    }

    [Fact]
    public void UnicodeAstNames_EncodeAsLeanStrings_IndependentlyOfCallableValidation()
    {
        var value = new Algorithm.User(null, [], [], [], [new Expr.Num(3)]);
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("π", value)],
            Output: [new Expr.Resolve("π")]);

        var encodedRoot = LeanAstEncoder.EncodeProgram(root);
        Assert.Contains("privateProp \"π\"", encodedRoot, StringComparison.Ordinal);
        Assert.Contains(".resolve \"π\"", encodedRoot, StringComparison.Ordinal);

        // Parameter names are representable by the same string field too. Lean's
        // ASCII-only callableParameterNameIsIdentifierLike becomes observable
        // only if evaluation reaches that validator; encoding itself is faithful.
        var callable = new Algorithm.User(
            Parent: null,
            Parameters: [new ParameterDeclaration("π")],
            Opens: [],
            Properties: [],
            Output: [new Expr.Param("π")]);
        Assert.Contains("(alg [\"π\"]", LeanAstEncoder.EncodeAlgorithm(callable), StringComparison.Ordinal);
    }

    [Fact]
    public void HostOnlyFieldsWithoutAFaithfulLeanValue_AreRefused()
    {
        Assert.Throws<NotSupportedException>(() =>
            LeanAstEncoder.EncodeExpr(new Expr.EmptySequence(-1)));

        var parent = new ScopeCtx(Parent: null, Opens: [], Properties: []);
        var wired = new Algorithm.User(
            Parent: parent, Parameters: [], Opens: [], Properties: [], Output: [new Expr.Num(1)]);
        var ex = Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeAlgorithm(wired));
        Assert.Contains("Parent", ex.Message);
    }

    /// <summary>
    /// The Lean model derives the flattened parameter list from the pattern
    /// list, so a host tree whose two channels disagree has NO faithful single
    /// spelling — encoding either channel alone would assert a different
    /// program. Refuse, never approximate.
    /// </summary>
    [Fact]
    public void DivergentParameterChannels_AreRefused()
    {
        var divergent = new Algorithm.User(
            Parent: null,
            Parameters: [new ParameterDeclaration("a")],
            Opens: [],
            Properties: [],
            Output: [new Expr.Param("a")])
        {
            ParameterPatterns = [new CaptureParameterPattern("b")],
        };
        var ex = Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeAlgorithm(divergent));
        Assert.Contains("disagree", ex.Message);
    }

    /// <summary>
    /// The complete deliberate-exclusion inventory: every <see cref="Expr"/>
    /// variant is either encodable or refused with a diagnostic, and the
    /// refused set is exactly {Grace, NativeCall} — Grace because elaboration
    /// consumes and strips it, NativeCall because it exists only inside
    /// prelude/host wrapper bodies and the Lean core deliberately does not
    /// model natives. A NEW Expr variant added to the AST fails this
    /// reflection sweep until it is classified here and in the encoder.
    /// </summary>
    [Fact]
    public void EveryExprVariant_IsEitherEncodableOrDeliberatelyRefused()
    {
        string[] deliberatelyUnsupported = [nameof(Expr.Grace), nameof(Expr.NativeCall)];
        var variants = typeof(Expr).GetNestedTypes()
            .Where(t => t.IsAssignableTo(typeof(Expr)) && !t.IsAbstract)
            .Select(t => t.Name)
            .OrderBy(n => n, StringComparer.Ordinal)
            .ToList();

        // Reflection-complete sample table: one constructible instance per variant.
        var samples = new Dictionary<string, Expr>(StringComparer.Ordinal)
        {
            [nameof(Expr.Param)] = new Expr.Param("a"),
            [nameof(Expr.Num)] = new Expr.Num(1),
            [nameof(Expr.StringLiteral)] = new Expr.StringLiteral("s"),
            [nameof(Expr.Unary)] = new Expr.Unary(UnaryOp.Minus, new Expr.Num(1)),
            [nameof(Expr.Binary)] = new Expr.Binary(BinaryOp.Add, new Expr.Num(1), new Expr.Num(2)),
            [nameof(Expr.Index)] = new Expr.Index(new Expr.Resolve("x"), new Expr.Num(0)),
            [nameof(Expr.SequenceConstruct)] = new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2)),
            [nameof(Expr.EmptySequence)] = new Expr.EmptySequence(0),
            [nameof(Expr.SequenceSpread)] = new Expr.SequenceSpread(new Expr.Resolve("x")),
            [nameof(Expr.ListLiteral)] = new Expr.ListLiteral([new Expr.Num(1)]),
            [nameof(Expr.Resolve)] = new Expr.Resolve("x"),
            [nameof(Expr.DotCall)] = new Expr.DotCall(new Expr.Resolve("x"), "m"),
            [nameof(Expr.Grace)] = new Expr.Grace(new Expr.Resolve("x"), -1),
            [nameof(Expr.AlgorithmExpr)] = new Expr.AlgorithmExpr(
                new Algorithm.User(Parent: null, Parameters: [], Opens: [], Properties: [], Output: [new Expr.Num(1)])),
            [nameof(Expr.Capture)] = new Expr.Capture(new OutputBundle([new Expr.Num(1)])),
            [nameof(Expr.Call)] = new Expr.Call(new Expr.Resolve("f"), [new Expr.Num(1)]),
            [nameof(Expr.NativeCall)] = new Expr.NativeCall("abs", ["value"]),
        };

        foreach (var variant in variants)
        {
            Assert.True(samples.ContainsKey(variant),
                $"Expr variant '{variant}' has no sample here; classify it as encodable or deliberately unsupported.");

            if (deliberatelyUnsupported.Contains(variant))
            {
                var ex = Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeExpr(samples[variant]));
                Assert.Contains(variant, ex.Message);
            }
            else
            {
                var encoded = LeanAstEncoder.EncodeExpr(samples[variant]);
                Assert.False(string.IsNullOrWhiteSpace(encoded), $"'{variant}' encoded to empty text.");
            }
        }

        // No stale sample rows for variants that no longer exist.
        Assert.Equal(variants.Count, samples.Count);
    }

    [Fact]
    public void EveryAlgorithmVariant_IsEitherEncodableOrDeliberatelyRefused()
    {
        var variants = typeof(Algorithm).GetNestedTypes()
            .Where(t => t.IsAssignableTo(typeof(Algorithm)) && !t.IsAbstract)
            .Select(t => t.Name)
            .OrderBy(n => n, StringComparer.Ordinal)
            .ToList();
        var samples = new Dictionary<string, Algorithm>(StringComparer.Ordinal)
        {
            [nameof(Algorithm.User)] = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]),
            [nameof(Algorithm.Conditional)] = new Algorithm.Conditional(null, [], []),
            [nameof(Algorithm.Builtin)] = new Algorithm.Builtin(BuiltinId.count),
        };

        Assert.Equal(variants.OrderBy(n => n, StringComparer.Ordinal), samples.Keys.OrderBy(n => n, StringComparer.Ordinal));
        foreach (var variant in variants)
        {
            if (variant == nameof(Algorithm.Builtin))
                Assert.Throws<NotSupportedException>(() => LeanAstEncoder.EncodeAlgorithm(samples[variant]));
            else
                Assert.False(string.IsNullOrWhiteSpace(LeanAstEncoder.EncodeAlgorithm(samples[variant])));
        }
    }

    [Fact]
    public void EveryPatternAndParameterPatternVariant_HasAnIndependentConstructorPin()
    {
        var patternVariants = typeof(Pattern).GetNestedTypes()
            .Where(t => t.IsAssignableTo(typeof(Pattern)) && !t.IsAbstract)
            .Select(t => t.Name)
            .OrderBy(n => n, StringComparer.Ordinal)
            .ToList();
        var patterns = new Dictionary<string, (Pattern Value, string Expected)>(StringComparer.Ordinal)
        {
            [nameof(Pattern.Bind)] = (new Pattern.Bind("x"), ".bind \"x\""),
            [nameof(Pattern.LitInt)] = (new Pattern.LitInt(7), ".litInt 7"),
            [nameof(Pattern.LitString)] = (new Pattern.LitString("s"), ".litString \"s\""),
            [nameof(Pattern.SequenceValue)] = (
                new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.LitInt(2)]),
                ".sequenceValue [.bind \"x\", .litInt 2]"),
        };
        Assert.Equal(patternVariants.OrderBy(n => n, StringComparer.Ordinal), patterns.Keys.OrderBy(n => n, StringComparer.Ordinal));
        foreach (var variant in patternVariants)
            Assert.Equal(patterns[variant].Expected, LeanAstEncoder.EncodePattern(patterns[variant].Value));

        var parameterPatternVariants = typeof(ParameterPattern).Assembly.GetTypes()
            .Where(t => t.IsAssignableTo(typeof(ParameterPattern)) && !t.IsAbstract)
            .Select(t => t.Name)
            .OrderBy(n => n, StringComparer.Ordinal)
            .ToList();
        Assert.Equal(
            new[] { nameof(CaptureParameterPattern), nameof(SequenceValueParameterPattern) }.OrderBy(n => n, StringComparer.Ordinal),
            parameterPatternVariants);
    }

    [Fact]
    public void EveryOperatorParameterKindAndExposureValue_IsMappedFailLoud()
    {
        var binaryNames = new Dictionary<BinaryOp, string>
        {
            [BinaryOp.Add] = "add", [BinaryOp.Sub] = "sub", [BinaryOp.Mul] = "mul",
            [BinaryOp.Div] = "div", [BinaryOp.IDiv] = "idiv", [BinaryOp.Mod] = "mod",
            [BinaryOp.Pow] = "pow", [BinaryOp.Lt] = "lt", [BinaryOp.Gt] = "gt",
            [BinaryOp.Le] = "le", [BinaryOp.Ge] = "ge", [BinaryOp.Eq] = "eq",
            [BinaryOp.Ne] = "ne", [BinaryOp.And] = "and", [BinaryOp.Or] = "or",
            [BinaryOp.Xor] = "xor",
        };
        Assert.Equal(Enum.GetValues<BinaryOp>(), binaryNames.Keys.OrderBy(v => (int)v));
        foreach (var (op, leanName) in binaryNames)
        {
            Assert.Equal(
                $"(.binary .{leanName} (.num 1) (.num 2))",
                LeanAstEncoder.EncodeExpr(new Expr.Binary(op, new Expr.Num(1), new Expr.Num(2))));
        }

        var unaryNames = new Dictionary<UnaryOp, string>
        {
            [UnaryOp.Minus] = "minus",
            [UnaryOp.Not] = "not",
        };
        Assert.Equal(Enum.GetValues<UnaryOp>(), unaryNames.Keys.OrderBy(v => (int)v));
        foreach (var (op, leanName) in unaryNames)
        {
            Assert.Equal(
                $"(.unary .{leanName} (.num 1))",
                LeanAstEncoder.EncodeExpr(new Expr.Unary(op, new Expr.Num(1))));
        }

        Assert.Equal(new[] { ParameterKind.Normal, ParameterKind.Collecting }, Enum.GetValues<ParameterKind>());

        var value = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var exposures = new Dictionary<PropertyExposure, string>
        {
            [PropertyExposure.Exported] = "publicProp \"X\" (alg [] [] [] [.num 1])",
            [PropertyExposure.LocalOnlyCapturedAncestorParameters] =
                "publicLocalProp \"X\" .localCapturedAncestorParams (alg [] [] [] [.num 1])",
            [PropertyExposure.LocalOnlyConditionalAlgorithm] =
                "publicLocalProp \"X\" .localConditional (alg [] [] [] [.num 1])",
        };
        Assert.Equal(Enum.GetValues<PropertyExposure>(), exposures.Keys.OrderBy(v => (int)v));
        foreach (var (exposure, expected) in exposures)
            Assert.Equal(expected, LeanAstEncoder.EncodeProperty(
                new Property("X", value, IsPublic: true, Exposure: exposure)));
    }
}
