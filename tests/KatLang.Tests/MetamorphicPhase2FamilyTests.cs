using System.Collections.Immutable;
using System.Globalization;
using KatLang.ParserFuzz;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>
/// Deterministic coverage for the Phase 2 metamorphic relation families: dotted collection
/// builtins, user-defined extension calls, bounded dotted chains, and builtin-callback versus
/// user-wrapper equivalence.
///
/// <para>Phase 2's full Cartesian product is in the millions and mostly redundant, so the
/// sweeps here are STRATIFIED (each family's own dimensions crossed exhaustively under the
/// default policy, then every execution policy crossed against representative points) — while
/// the Phase 1 family stays exhaustive because it is the payload compatibility surface.</para>
/// </summary>
public class MetamorphicPhase2FamilyTests
{
    private static string SeedDirectory =>
        Path.Combine(RepoRoot.Find(), "fuzz", "KatLang.ParserFuzz", "MetamorphicTestcases");

    private static List<MetamorphicParameters> Stratified { get; } =
        MetamorphicTemplates.EnumerateStratifiedParameters().ToList();

    private static IEnumerable<MetamorphicParameters> OfFamily(MetamorphicFamily family)
        => Stratified.Where(parameters => parameters.Family == family);

    /// <summary>
    /// The families this file is about: Phase 1 plus Phase 2's four.
    ///
    /// <para>Phase 3 appended families whose two members are deliberately the SAME source under
    /// different execution policies, and one whose source deliberately does not parse. Sweeps that
    /// assert "the two members are different programs" or "every generated source parses" are
    /// statements about the DOTTED-REWRITE families, so they are scoped here rather than weakened;
    /// <c>MetamorphicPhase3FamilyTests</c> owns the equivalent statements for its own families.</para>
    /// </summary>
    private static readonly MetamorphicFamily[] RewriteFamilies =
    [
        MetamorphicFamily.DottedCollectionCall,
        MetamorphicFamily.DottedCollectionBuiltin,
        MetamorphicFamily.UserExtensionCall,
        MetamorphicFamily.DottedChain,
        MetamorphicFamily.BuiltinCallbackWrapper,
    ];

    private static IEnumerable<MetamorphicParameters> RewritePoints
        => Stratified.Where(parameters => RewriteFamilies.Contains(parameters.Family));

    /// <summary>The one committed chain measured to FUSE: <c>filter &gt; count</c>.</summary>
    private static byte FusibleChainIndex { get; } = (byte)MetamorphicChainTemplate.Chains
        .Select(static (chain, index) => (Names: chain.Select(static link => link.Builtin).ToArray(), index))
        .First(static entry => entry.Names.SequenceEqual(["filter", "count"]))
        .index;

    /// <summary>The exact-list receiver <c>[1, 2, 3]</c>.</summary>
    private static byte ListReceiverIndex { get; } = (byte)MetamorphicTables.ReceiverShapes
        .Select(static (shape, index) => (shape, index))
        .First(static entry => entry.shape.Id == "list")
        .index;

    /// <summary>The generated pair of the fusible chain under the default policy.</summary>
    private static (string Ordinary, string Dotted) FusibleChainPair()
    {
        var testCase = MetamorphicTemplates.Build(MetamorphicDecoder.Decode(
            [0x03, 0, 0, 1, 1, 0, FusibleChainIndex, ListReceiverIndex]));
        return (testCase.LeftSource, testCase.RightSource);
    }

    // ── Frozen Phase 1 tables ────────────────────────────────────────────────

    /// <summary>
    /// The LITERAL contents of every table a version-zero (six-byte) payload indexes into.
    ///
    /// <para>The index-level oracle below cannot see a reordering: swapping two entries of
    /// <c>RangeStopTable</c> changes what every existing Phase 1 payload MEANS while leaving all
    /// five decoded indices identical. These expectations are therefore written out by hand and
    /// deliberately not derived from the decoder or the registry — if a frozen table is reordered
    /// or edited, this test is what fails.</para>
    /// </summary>
    [Fact]
    public void FrozenPhase1Tables_StillHoldTheirExactValuesInTheirExactOrder()
    {
        Assert.Equal(
            new[] { 1, 0, 2, 3, 5, 8, -1, -3, 16, 33, 64, 100 },
            MetamorphicDecoder.RangeStopTable.ToArray());

        Assert.Equal(new[] { -1, 0, 1, 4 }, MetamorphicDecoder.OffsetTable.ToArray());

        Assert.Equal(
            new[]
            {
                MetamorphicLimitMode.Default,
                MetamorphicLimitMode.CumulativeItems,
                MetamorphicLimitMode.PerCollectionItems,
                MetamorphicLimitMode.Both,
            },
            MetamorphicFamilyRegistry.Get(MetamorphicFamily.DottedCollectionCall).SupportedLimitModes.ToArray());

        // Byte 0 resolves through the family table, whose first entry is the version-zero family.
        Assert.Equal(MetamorphicFamily.DottedCollectionCall, MetamorphicDecoder.FamilyTable[0]);
        Assert.Equal("dotted-collection-call", MetamorphicFamilyRegistry.All[0].Id);

        // The version-zero prefix length itself, and the Phase 1 cardinality bound.
        Assert.Equal(6, MetamorphicParameters.CommonPayloadLength);
        Assert.Equal(128, MetamorphicDecoder.MaxPhase1Cardinality);

        // Byte 5: index 0 means optimizations ON, index 1 means OFF.
        Assert.True(MetamorphicDecoder.Decode([0, 0, 0, 1, 1, 0]).EnableOptimizations);
        Assert.False(MetamorphicDecoder.Decode([0, 0, 0, 1, 1, 1]).EnableOptimizations);

        // The canonical index an unused offset collapses to is the one whose OFFSET IS ZERO.
        Assert.Equal(0, MetamorphicDecoder.OffsetTable[1]);

        // Which mode consumes which offset byte — reversing these would silently repoint the
        // limit an existing payload configures.
        Assert.False(MetamorphicDecoder.UsesPrimaryOffset(MetamorphicLimitMode.Default));
        Assert.False(MetamorphicDecoder.UsesSecondaryOffset(MetamorphicLimitMode.Default));
        Assert.True(MetamorphicDecoder.UsesPrimaryOffset(MetamorphicLimitMode.CumulativeItems));
        Assert.False(MetamorphicDecoder.UsesSecondaryOffset(MetamorphicLimitMode.CumulativeItems));
        Assert.False(MetamorphicDecoder.UsesPrimaryOffset(MetamorphicLimitMode.PerCollectionItems));
        Assert.True(MetamorphicDecoder.UsesSecondaryOffset(MetamorphicLimitMode.PerCollectionItems));
        Assert.True(MetamorphicDecoder.UsesPrimaryOffset(MetamorphicLimitMode.Both));
        Assert.True(MetamorphicDecoder.UsesSecondaryOffset(MetamorphicLimitMode.Both));
    }

    /// <summary>
    /// What a frozen Phase 1 payload MEANS: the two programs it generates and the limits it
    /// places on them. Hand-written end-to-end expectations, so a table reorder, a changed offset
    /// placement, or a changed optimizer encoding all fail here even though the decoded indices
    /// would still round-trip.
    /// </summary>
    [Theory]
    // payload,             left,                            right,                          limits,                                        optimizer
    [InlineData("00 00 00 01 01 00", "count(range(1, 1))", "range(1, 1).count", "default", true)]
    [InlineData("00 01 00 01 01 00", "count(range(1, 0))", "range(1, 0).count", "default", true)]
    [InlineData("00 04 00 01 01 00", "count(range(1, 5))", "range(1, 5).count", "default", true)]
    [InlineData("00 04 01 00 01 00", "count(range(1, 5))", "range(1, 5).count", "maxMaterializedItems=4", true)]
    [InlineData("00 04 01 01 01 00", "count(range(1, 5))", "range(1, 5).count", "maxMaterializedItems=5", true)]
    [InlineData("00 04 01 02 01 00", "count(range(1, 5))", "range(1, 5).count", "maxMaterializedItems=6", true)]
    [InlineData("00 04 02 01 00 00", "count(range(1, 5))", "range(1, 5).count", "maxCollectionItems=4", true)]
    [InlineData("00 05 03 01 03 00", "count(range(1, 8))", "range(1, 8).count", "maxMaterializedItems=8,maxCollectionItems=12", true)]
    [InlineData("00 07 01 00 01 00", "count(range(1, -3))", "range(1, -3).count", "maxMaterializedItems=4", true)]
    [InlineData("00 0b 03 01 01 01", "count(range(1, 100))", "range(1, 100).count", "maxMaterializedItems=100,maxCollectionItems=100", false)]
    public void FrozenPhase1Payloads_StillGenerateExactlyTheirOriginalProgramsAndLimits(
        string payloadHex, string leftExpression, string rightExpression, string limits, bool optimizations)
    {
        var testCase = MetamorphicTemplates.Build(MetamorphicDecoder.Decode(ParseHex(payloadHex)));

        Assert.Equal(MetamorphicFamily.DottedCollectionCall, testCase.Family);
        Assert.Equal(leftExpression, testCase.LeftSource);
        Assert.Equal(rightExpression, testCase.RightSource);
        Assert.Equal(limits, testCase.LimitsText);
        Assert.Equal(optimizations, testCase.EnableOptimizations);
        Assert.Equal(MetamorphicOperationalRelation.ExactMaterializationEqual, testCase.OperationalRelation);

        // And it still re-encodes to exactly the six bytes it was written as.
        Assert.Equal(payloadHex, testCase.Parameters.ToHex());
    }

    // ── Payload backward compatibility ───────────────────────────────────────

    /// <summary>The Phase 1 decoder, reimplemented here as the compatibility ORACLE.</summary>
    private static (int Stop, int Mode, int Primary, int Secondary, int Optimize) LegacyDecode(byte[] payload)
    {
        static int At(byte[] bytes, int index, int count) => (index < bytes.Length ? bytes[index] : 0) % count;

        var stop = At(payload, 1, 12);
        var mode = At(payload, 2, 4);
        var primary = At(payload, 3, 4);
        var secondary = At(payload, 4, 4);
        var optimize = At(payload, 5, 2);

        // Phase 1 normalization: offsets the mode does not use collapse to index 1 (offset 0).
        if (mode is 0 or 2) primary = 1;
        if (mode is 0 or 1) secondary = 1;
        return (stop, mode, primary, secondary, optimize);
    }

    [Fact]
    public void EverySixBytePayload_StillDecodesExactlyAsPhase1Did()
    {
        // Exhaustive over every byte position: one position varies across all 256 values while
        // the rest hold a fixed non-zero pattern, plus the all-values sweep of byte 0 (the byte
        // that would otherwise start selecting a Phase 2 family).
        var patterns = new List<byte[]>();
        for (var position = 0; position < MetamorphicParameters.CommonPayloadLength; position++)
        {
            for (var value = 0; value <= byte.MaxValue; value++)
            {
                var payload = new byte[] { 0x11, 0x22, 0x33, 0x02, 0x01, 0x01 };
                payload[position] = (byte)value;
                patterns.Add(payload);
            }
        }

        foreach (var payload in patterns)
        {
            var decoded = MetamorphicDecoder.Decode(payload);
            var expected = LegacyDecode(payload);

            Assert.Equal(MetamorphicFamily.DottedCollectionCall, decoded.Family);
            Assert.Equal(expected.Stop, decoded.LegacyRangeStopIndex);
            Assert.Equal(expected.Mode, decoded.LimitModeIndex);
            Assert.Equal(expected.Primary, decoded.PrimaryOffsetIndex);
            Assert.Equal(expected.Secondary, decoded.SecondaryOffsetIndex);
            Assert.Equal(expected.Optimize, decoded.OptimizeIndex);
            Assert.Equal(0, decoded.Extra0 + decoded.Extra1 + decoded.Extra2 + decoded.Extra3);
        }
    }

    [Fact]
    public void ShortPayloads_NeverSelectAPhase2Family()
    {
        for (var length = 0; length <= MetamorphicParameters.CommonPayloadLength; length++)
        {
            for (var value = 0; value <= byte.MaxValue; value++)
            {
                var payload = new byte[length];
                for (var i = 0; i < length; i++) payload[i] = (byte)value;
                Assert.Equal(MetamorphicFamily.DottedCollectionCall, MetamorphicDecoder.Decode(payload).Family);
            }
        }
    }

    [Fact]
    public void EveryTrackedPhase1Seed_DecodesToTheSameLegacyCaseAndStillReplays()
    {
        var seeds = LoadSeeds().Where(seed => seed.DeclaredFamily == MetamorphicFamily.DottedCollectionCall).ToList();
        Assert.NotEmpty(seeds);

        foreach (var seed in seeds)
        {
            Assert.Equal(MetamorphicParameters.CommonPayloadLength, seed.Payload.Length);

            var decoded = MetamorphicDecoder.Decode(seed.Payload);
            var expected = LegacyDecode(seed.Payload);

            Assert.Equal(MetamorphicFamily.DottedCollectionCall, decoded.Family);
            Assert.Equal(expected.Stop, decoded.LegacyRangeStopIndex);
            Assert.Equal(expected.Mode, decoded.LimitModeIndex);
            Assert.Equal(expected.Primary, decoded.PrimaryOffsetIndex);
            Assert.Equal(expected.Secondary, decoded.SecondaryOffsetIndex);
            Assert.Equal(expected.Optimize, decoded.OptimizeIndex);

            // Still a six-byte canonical encoding, and still relation-clean.
            Assert.Equal(seed.Payload, decoded.Encode());
            Assert.Null(MetamorphicInvariants.Run(seed.Payload).Mismatch);
        }
    }

    [Fact]
    public void ExtendedPayloads_RoundTripAndStayBounded()
    {
        foreach (var parameters in Stratified)
        {
            var encoded = parameters.Encode();
            Assert.Equal(parameters.EncodedLength, encoded.Length);
            Assert.InRange(encoded.Length, MetamorphicParameters.CommonPayloadLength, MetamorphicDecoder.MaxPayloadLength);
            Assert.Equal(parameters, MetamorphicDecoder.Decode(encoded));
        }
    }

    [Fact]
    public void EveryBytePosition_StaysInsideItsFamilyTable()
    {
        for (var familyIndex = 0; familyIndex < MetamorphicDecoder.FamilyTable.Length; familyIndex++)
        {
            var definition = MetamorphicFamilyRegistry.Get(MetamorphicDecoder.FamilyTable[familyIndex]);
            for (var position = 0; position < MetamorphicDecoder.MaxPayloadLength; position++)
            {
                for (var value = 0; value <= byte.MaxValue; value += 7)
                {
                    var payload = new byte[MetamorphicDecoder.MaxPayloadLength];
                    payload[0] = (byte)familyIndex;
                    payload[position] = position == 0 ? (byte)familyIndex : (byte)value;

                    var decoded = MetamorphicDecoder.Decode(payload);
                    Assert.InRange(decoded.LimitModeIndex, 0, definition.SupportedLimitModes.Length - 1);
                    Assert.InRange(decoded.PrimaryOffsetIndex, 0, MetamorphicDecoder.OffsetTable.Length - 1);
                    Assert.InRange(decoded.SecondaryOffsetIndex, 0, MetamorphicDecoder.OffsetTable.Length - 1);
                    Assert.InRange(decoded.OptimizeIndex, 0, 1);
                    for (var extra = 0; extra < definition.ExtraDimensionCount; extra++)
                        Assert.InRange(decoded.Extra(extra), 0, definition.ExtraDimensionSizes[extra] - 1);

                    // Nothing beyond the family's own dimensions is ever set.
                    for (var extra = definition.ExtraDimensionCount; extra < MetamorphicParameters.MaxExtraDimensions; extra++)
                        Assert.Equal(0, decoded.Extra(extra));
                }
            }
        }
    }

    // ── Registry ─────────────────────────────────────────────────────────────

    [Fact]
    public void EveryRegisteredFamily_IsCompletelyDeclared()
    {
        Assert.Equal(MetamorphicFamily.DottedCollectionCall, MetamorphicFamilyRegistry.All[0].Family);

        var ids = new HashSet<string>(StringComparer.Ordinal);
        foreach (var definition in MetamorphicFamilyRegistry.All)
        {
            Assert.True(ids.Add(definition.Id), $"duplicate family id '{definition.Id}'");
            Assert.NotEmpty(definition.Id);
            Assert.NotEmpty(definition.Group);
            Assert.NotEmpty(definition.Description);
            Assert.NotEmpty(definition.SupportedLimitModes);
            Assert.NotNull(definition.Normalize);
            Assert.NotNull(definition.ValidatePreconditions);
            Assert.NotNull(definition.Build);
            Assert.InRange(definition.ExtraDimensionCount, 0, MetamorphicParameters.MaxExtraDimensions);
            Assert.Equal(definition, MetamorphicFamilyRegistry.Get(definition.Family));
            Assert.True(MetamorphicFamilyRegistry.TryGetById(definition.Id, out var byId));
            Assert.Equal(definition, byId);
        }
    }

    [Fact]
    public void UnregisteredFamily_FailsClearly()
    {
        Assert.Throws<ArgumentOutOfRangeException>(
            () => MetamorphicFamilyRegistry.Get((MetamorphicFamily)999));
        Assert.False(MetamorphicFamilyRegistry.TryGetById("no-such-family", out _));
        Assert.False(MetamorphicCase.TryParseFamilyId("no-such-family", out _));
    }

    [Fact]
    public void BuiltinTableArity_MatchesTheProductionBuiltinRegistry()
    {
        // Pre-campaign audit: a wrong suffix kind here would silently generate calls with the
        // wrong number of arguments and turn ordinary arity errors into "equivalence" evidence.
        foreach (var builtin in MetamorphicTables.Builtins)
        {
            Assert.True(Enum.TryParse<KatLang.BuiltinId>(builtin.Name, out var id), builtin.Name);
            var descriptor = KatLang.BuiltinRegistry.GetBuiltin(id);

            var declaredSuffixCount = builtin.SuffixKind switch
            {
                MetamorphicSuffixKind.None => 0,
                MetamorphicSuffixKind.WholeNumber => 1,
                MetamorphicSuffixKind.Value => 1,
                MetamorphicSuffixKind.Callback1 => 1,
                MetamorphicSuffixKind.Callback2Initial => 2,
                _ => -1,
            };

            // Receiver + declared suffixes must be exactly the builtin's fixed arity.
            Assert.Equal(1 + declaredSuffixCount, descriptor.FixedArity);
            Assert.True(descriptor.AcceptsArity(1 + declaredSuffixCount));
            Assert.False(descriptor.AcceptsArity(2 + declaredSuffixCount));

            // Callback eligibility: a builtin may serve as a callback of arity N only if its
            // fixed arity IS N. Zero means "excluded by policy" — the higher-order builtins,
            // which take a callback themselves, are not used as callbacks.
            var higherOrder = builtin.SuffixKind is MetamorphicSuffixKind.Callback1 or MetamorphicSuffixKind.Callback2Initial;
            if (higherOrder) Assert.Equal(0, builtin.CallbackArity);
            else Assert.Equal(descriptor.FixedArity, builtin.CallbackArity);

            // Collection builtins expose the receiver as their first parameter.
            if (descriptor.SequenceMetadata is { } metadata)
            {
                Assert.Equal(declaredSuffixCount, metadata.SuffixArgs.Count);
                Assert.Equal("collection", metadata.Parameters[0].DisplayName);
            }
        }

        // Control-flow and scalar-bound builtins are deliberately absent.
        foreach (var excluded in new[] { "if", "while", "repeat", "range" })
            Assert.DoesNotContain(MetamorphicTables.Builtins, b => b.Name == excluded);
    }

    [Fact]
    public void EveryTableEntry_ResolvesToTheExpectedRuntimeCallableOrShape()
    {
        // Builtin names must be real prelude callables, not strings that merely look right.
        foreach (var builtin in MetamorphicTables.Builtins)
        {
            var probe = $"MmR = [1, 2, 3]\n{builtin.Name}";
            Assert.False(Parser.Parse(probe).HasErrors, probe);
            Assert.Contains(builtin.Name, KatLang.BuiltinRegistry.BuiltinNames);
        }

        // Declared collection-view sizes must match what the runtime actually reports.
        foreach (var shape in MetamorphicTables.ReceiverShapes.Concat(MetamorphicTables.CallbackInputShapes))
        {
            var source = $"MmR = {shape.Source}\nMmR.count";
            Assert.True(MetamorphicExecutor.TryObserve(source, null, true, out var observation, out var reason), reason);
            Assert.Equal("ok", observation.Semantic.Outcome);
            Assert.Equal(
                shape.CollectionItemCount.ToString(CultureInfo.InvariantCulture),
                observation.Semantic.Structure);
        }
    }

    // ── Generated sources: shape, boundaries, and resolution path ────────────

    [Fact]
    public void EveryGeneratedPair_ParsesAndNeverUsesStructuralMemberSyntax()
    {
        foreach (var parameters in RewritePoints)
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            foreach (var source in new[] { testCase.LeftSource, testCase.RightSource })
            {
                Assert.False(Parser.Parse(source).HasErrors, source);

                // Structural member access is a DIFFERENT construct and out of scope: no
                // template may declare an algorithm with exposed members and dot into it.
                Assert.DoesNotContain("public ", source, StringComparison.Ordinal);
            }

            Assert.NotEqual(testCase.LeftSource, testCase.RightSource);
        }
    }

    [Fact]
    public void DottedForms_IntroduceNoImplicitSpreadAndKeepSuffixBoundaries()
    {
        foreach (var parameters in Stratified)
        {
            var testCase = MetamorphicTemplates.Build(parameters);

            // The rewrite lives in the CALL, so that is where the spread rule applies:
            // `A.F(B, C)` is `F(A, B, C)`, never `F(A*, B, C)`, so the dotted call may not add
            // or drop a spread marker relative to the ordinary call. (A rejected
            // collecting-projection wrapper legitimately writes a collecting parameter in its
            // DEFINITION; that is the very thing its precondition rejects, and it is never
            // compared.) These families never write a multiplication in an output expression,
            // so every `*` counted here is the postfix spread marker.
            if (testCase.Family is MetamorphicFamily.DottedCollectionBuiltin
                or MetamorphicFamily.UserExtensionCall
                or MetamorphicFamily.DottedChain
                or MetamorphicFamily.DottedCollectionCall)
            {
                Assert.Equal(
                    CountOccurrences(OutputExpression(testCase.LeftSource), "*"),
                    CountOccurrences(OutputExpression(testCase.RightSource), "*"));
            }

            // Both members write the receiver expression exactly once.
            if (testCase.Family is MetamorphicFamily.DottedCollectionBuiltin
                or MetamorphicFamily.UserExtensionCall
                or MetamorphicFamily.DottedChain)
            {
                Assert.Equal(1, CountOccurrences(OutputLine(testCase.LeftSource), MetamorphicTables.ReceiverProperty));
                Assert.Equal(1, CountOccurrences(OutputLine(testCase.RightSource), MetamorphicTables.ReceiverProperty));
            }
        }
    }

    [Fact]
    public void GeneratedNames_CannotCollideWithBuiltinsOrTemplateLocals()
    {
        var generated = new[]
        {
            MetamorphicTables.ReceiverProperty, MetamorphicTables.RowsProperty,
            MetamorphicTables.ExtensionFunction, MetamorphicTables.WrapperFunction,
            MetamorphicTables.DoubleCallback, MetamorphicTables.BigCallback, MetamorphicTables.AddCallback,
        };

        foreach (var name in generated)
        {
            Assert.StartsWith(MetamorphicTables.NamePrefix, name, StringComparison.Ordinal);
            Assert.DoesNotContain(name, KatLang.BuiltinRegistry.BuiltinNames);
            Assert.DoesNotContain(name, KatLang.BuiltinRegistry.MathMemberNames);
        }

        Assert.Equal(generated.Length, generated.Distinct(StringComparer.Ordinal).Count());
    }

    [Fact]
    public void DottedReceiverAlwaysEvaluatesToAValue_SoTheMemberResolvesAsAnExtensionCall()
    {
        // A block-valued receiver would make `.F` STRUCTURAL member access. Every receiver in
        // the tables evaluates to an ordinary Result value, which is what makes the dotted form
        // an extension-style call rather than a member lookup.
        foreach (var shape in MetamorphicTables.ReceiverShapes)
        {
            var parsed = Parser.Parse($"{shape.Source}");
            Assert.False(parsed.HasErrors, shape.Source);
            var evaluated = Evaluator.RunCounted(new Expr.AlgorithmExpr(parsed.Root));
            Assert.False(evaluated.IsError, shape.Source);
            Assert.True(
                evaluated.Value.Value is Result.Atom or Result.Str or Result.SequenceValue or Result.ListValue,
                $"receiver '{shape.Id}' is not a plain value");
        }
    }

    /// <summary>
    /// Every generated Group A dotted form resolves through the EXTENSION-CALL path, not through
    /// structural member access. Two independent discriminators, both tied to real behaviour:
    ///
    /// <list type="number">
    ///   <item><b>Elaborated shape.</b> The right member's output is an <c>Expr.DotCall</c> whose
    ///   target is the receiver PROPERTY and whose member names a prelude builtin — and the
    ///   program declares no exposed member at all, so structural lookup has nothing to find.</item>
    ///   <item><b>Receiver injection.</b> Structural member access does not supply the receiver as
    ///   an argument, so under that resolution <c>MmR.take(2)</c> would be <c>take(2)</c> — an
    ///   arity error against the fixed <c>take(collection, count)</c> signature. Every dotted form
    ///   instead agrees with the ordinary call that passes the receiver explicitly, which only
    ///   receiver injection can produce.</item>
    /// </list>
    ///
    /// <para>The contrast case pins the discriminator itself: an algorithm with an exposed member
    /// really does resolve structurally, and it is a shape no template can build.</para>
    /// </summary>
    [Fact]
    public void GeneratedDottedForms_ResolveThroughTheExtensionCallPath_NotStructuralMemberAccess()
    {
        var checkedPoints = 0;
        var receiverInjectionWitnesses = 0;

        foreach (var parameters in OfFamily(MetamorphicFamily.DottedCollectionBuiltin))
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            if (!testCase.Precondition.Satisfied) continue;

            var builtin = MetamorphicDottedBuiltinTemplate.BuiltinOf(parameters);
            var dotCall = Assert.IsType<Expr.DotCall>(OutputExpressionOf(testCase.RightSource));

            // The member is a prelude builtin applied to the receiver PROPERTY reference.
            Assert.Equal(builtin.Name, dotCall.Name);
            Assert.Contains(builtin.Name, KatLang.BuiltinRegistry.BuiltinNames);
            Assert.Equal(MetamorphicTables.ReceiverProperty, Assert.IsType<Expr.Resolve>(dotCall.Target).Name);

            // Nothing in either program exposes a member, so structural lookup cannot resolve it.
            Assert.Empty(ExposedMemberNames(testCase.RightSource));
            Assert.Empty(ExposedMemberNames(testCase.LeftSource));

            // Receiver injection: the dotted form matches the ordinary call that passes the
            // receiver explicitly. Structural access would drop it and change the arity.
            var execution = MetamorphicExecutor.Execute(testCase);
            Assert.True(execution.Accepted);
            Assert.Equal(execution.Left!.Semantic, execution.Right!.Semantic);

            // A suffix-carrying builtin makes the injection observable as an arity difference.
            if (builtin.SuffixKind != MetamorphicSuffixKind.None) receiverInjectionWitnesses++;
            checkedPoints++;
        }

        Assert.True(checkedPoints > 0, "no dotted-builtin point was checked");
        Assert.True(receiverInjectionWitnesses > 0, "no suffix-carrying builtin exercised receiver injection");

        // Dropping the receiver really is an arity error, so the agreement above is evidence.
        Assert.True(MetamorphicExecutor.TryObserve("MmR = [1, 2, 3]\ntake(2)", null, true, out var dropped, out _));
        Assert.Equal("err", dropped.Semantic.Outcome);

        // The contrast: an exposed member DOES resolve structurally, and no template builds one.
        const string structural = "MmObject = {\n    public MmValue = 7\n}\nMmObject.MmValue";
        var structuralParse = Parser.Parse(structural);
        Assert.False(structuralParse.HasErrors);
        Assert.Contains("MmValue", ExposedMemberNames(structural));
        Assert.True(MetamorphicExecutor.TryObserve(structural, null, true, out var member, out _));
        Assert.Equal("7", member.Semantic.Structure);

        foreach (var parameters in RewritePoints)
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            Assert.Empty(ExposedMemberNames(testCase.RightSource));
            Assert.Empty(ExposedMemberNames(testCase.LeftSource));
        }
    }

    [Fact]
    public void ChainTemplate_BuildsTheOrdinaryEquivalentStructurallyFromTheSameLinkList()
    {
        foreach (var parameters in OfFamily(MetamorphicFamily.DottedChain))
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            var chain = MetamorphicChainTemplate.ChainOf(parameters);
            Assert.InRange(chain.Length, 2, MetamorphicChainTemplate.MaxChainLength);

            // The dotted form applies the links left to right,
            var expectedDotted = MetamorphicTables.ReceiverProperty + string.Concat(chain.Select(link => link.Dotted));
            Assert.Equal(expectedDotted, OutputExpression(testCase.RightSource));

            // and... the ordinary form wraps the same links in the same order.
            var expectedOrdinary = MetamorphicTables.ReceiverProperty;
            foreach (var link in chain) expectedOrdinary = link.Ordinary(expectedOrdinary);
            Assert.Equal(expectedOrdinary, OutputExpression(testCase.LeftSource));

            foreach (var link in chain)
                Assert.Contains(MetamorphicTables.Builtins, builtin => builtin.Name == link.Builtin);
        }
    }

    [Fact]
    public void UserExtensionTemplate_PreservesSuffixArityAndSpreadPlacement()
    {
        foreach (var parameters in OfFamily(MetamorphicFamily.UserExtensionCall))
        {
            var body = MetamorphicUserExtensionTemplate.BodyOf(parameters);
            var testCase = MetamorphicTemplates.Build(parameters);
            var left = OutputExpression(testCase.LeftSource);
            var right = OutputExpression(testCase.RightSource);

            if (body.SuffixIsSpread)
            {
                // The spread sits in the SUFFIX on BOTH sides — never on the receiver, which has
                // no dotted spelling at all.
                Assert.Contains("MmS*", left, StringComparison.Ordinal);
                Assert.Contains("MmS*", right, StringComparison.Ordinal);
                Assert.DoesNotContain($"{MetamorphicTables.ReceiverProperty}*", left, StringComparison.Ordinal);
                Assert.DoesNotContain($"{MetamorphicTables.ReceiverProperty}*", right, StringComparison.Ordinal);
            }

            if (body.SuffixArity == 0)
            {
                Assert.Equal($"{MetamorphicTables.ExtensionFunction}({MetamorphicTables.ReceiverProperty})", left);
                Assert.Equal($"{MetamorphicTables.ReceiverProperty}.{MetamorphicTables.ExtensionFunction}", right);
            }
            else
            {
                Assert.StartsWith($"{MetamorphicTables.ExtensionFunction}({MetamorphicTables.ReceiverProperty}, ", left, StringComparison.Ordinal);
                Assert.StartsWith($"{MetamorphicTables.ReceiverProperty}.{MetamorphicTables.ExtensionFunction}(", right, StringComparison.Ordinal);
            }
        }
    }

    /// <summary>
    /// A dimension the selected body IGNORES must collapse to one canonical index. The
    /// spread-suffix body writes the same generated <c>MmS*</c> whatever the suffix variant
    /// says, so all six variants are one case — not six payloads building byte-identical pairs
    /// under six distinct fingerprints.
    /// </summary>
    [Fact]
    public void IgnoredSuffixVariants_CollapseToOneCanonicalParameterPoint()
    {
        for (var body = 0; body < MetamorphicUserExtensionTemplate.BodyCount; body++)
        {
            var shape = MetamorphicUserExtensionTemplate.Bodies[body];
            var ignoresSuffix = MetamorphicUserExtensionTemplate.SuffixVariantCount(shape) == 1;
            var points = new HashSet<MetamorphicParameters>();
            var pairs = new HashSet<(string, string)>();

            for (var suffix = 0; suffix <= byte.MaxValue; suffix++)
            {
                var parameters = MetamorphicDecoder.Decode(
                    [0x02, 0, 0, 1, 1, 0, (byte)body, ListReceiverIndex, (byte)suffix]);

                // Idempotent normalization: the canonical form re-encodes and re-decodes to itself.
                Assert.Equal(parameters, MetamorphicDecoder.Decode(parameters.Encode()));

                if (!points.Add(parameters)) continue;
                var testCase = MetamorphicTemplates.Build(parameters);
                pairs.Add((testCase.LeftSource, testCase.RightSource));
            }

            // One generated pair per canonical point, in both directions.
            Assert.Equal(points.Count, pairs.Count);
            if (ignoresSuffix) Assert.Single(points);
            else Assert.Equal(MetamorphicUserExtensionTemplate.SuffixVariantCount(shape), points.Count);
        }

        // The spread body is the one this normalization was added for.
        Assert.Contains(MetamorphicUserExtensionTemplate.Bodies, body => body.SuffixIsSpread);
        foreach (var body in MetamorphicUserExtensionTemplate.Bodies.Where(b => b.SuffixIsSpread))
            Assert.Equal(1, MetamorphicUserExtensionTemplate.SuffixVariantCount(body));
    }

    /// <summary>
    /// Over the COMPLETE normalized parameter space of every Phase 2 family: encoding round-trips,
    /// and no two distinct canonical points share the fingerprint features derived from them.
    /// Decoding is pure, so this can cover the whole space rather than a stratum.
    /// </summary>
    [Fact]
    public void CompleteNormalizedPhase2Space_RoundTripsAndProducesDistinctFingerprintFeatures()
    {
        for (var familyIndex = 1; familyIndex < MetamorphicDecoder.FamilyTable.Length; familyIndex++)
        {
            var definition = MetamorphicFamilyRegistry.Get(MetamorphicDecoder.FamilyTable[familyIndex]);
            var canonical = new HashSet<MetamorphicParameters>();
            var features = new Dictionary<string, MetamorphicParameters>(StringComparer.Ordinal);

            foreach (var extras in CrossDimensions(definition.ExtraDimensionSizes.ToArray()))
                for (var mode = 0; mode < definition.SupportedLimitModes.Length; mode++)
                    for (var primary = 0; primary < MetamorphicDecoder.OffsetTable.Length; primary++)
                        for (var secondary = 0; secondary < MetamorphicDecoder.OffsetTable.Length; secondary++)
                            for (var optimize = 0; optimize < 2; optimize++)
                            {
                                var payload = new byte[MetamorphicParameters.CommonPayloadLength + extras.Length];
                                payload[0] = (byte)familyIndex;
                                payload[2] = (byte)mode;
                                payload[3] = (byte)primary;
                                payload[4] = (byte)secondary;
                                payload[5] = (byte)optimize;
                                for (var i = 0; i < extras.Length; i++)
                                    payload[MetamorphicParameters.CommonPayloadLength + i] = (byte)extras[i];

                                var parameters = MetamorphicDecoder.Decode(payload);
                                if (!canonical.Add(parameters)) continue;

                                Assert.Equal(parameters, MetamorphicDecoder.Decode(parameters.Encode()));

                                // The parameter-derived half of the fingerprint must separate distinct points.
                                var feature = $"{definition.Id}|{definition.DescribeVariant(parameters)}|{parameters.LimitMode}|" +
                                              $"{parameters.PrimaryOffset}|{parameters.SecondaryOffset}|{parameters.EnableOptimizations}";
                                if (!features.TryAdd(feature, parameters))
                                {
                                    Assert.Fail(
                                        $"two canonical points share fingerprint features:\n  {parameters}\n  {features[feature]}");
                                }
                            }

            Assert.NotEmpty(canonical);
        }
    }

    private static IEnumerable<int[]> CrossDimensions(int[] sizes)
    {
        if (sizes.Length == 0)
        {
            yield return [];
            yield break;
        }

        var indices = new int[sizes.Length];
        while (true)
        {
            yield return (int[])indices.Clone();

            var position = sizes.Length - 1;
            while (position >= 0)
            {
                indices[position]++;
                if (indices[position] < sizes[position]) break;
                indices[position] = 0;
                position--;
            }

            if (position < 0) yield break;
        }
    }

    [Fact]
    public void UserExtensionTemplate_EvaluatesTheReceiverExactlyOnce()
    {
        // A receiver whose construction materializes item slots: evaluating it twice would show
        // up as doubled materialization, which the exact-work relation forbids.
        const string once = "MmF(r) = r.count\nMmR = range(1, 10)\nMmF(MmR)";
        const string dotted = "MmF(r) = r.count\nMmR = range(1, 10)\nMmR.MmF";

        Assert.True(MetamorphicExecutor.TryObserve(once, null, true, out var a, out _));
        Assert.True(MetamorphicExecutor.TryObserve(dotted, null, true, out var b, out _));
        Assert.Equal(10, a.MaterializedItems);
        Assert.Equal(a.MaterializedItems, b.MaterializedItems);
        Assert.Equal(a.EvaluationSteps, b.EvaluationSteps);
        Assert.Equal(a.PeakDynamicDepth, b.PeakDynamicDepth);
    }

    // ── Callback projection ──────────────────────────────────────────────────

    [Fact]
    public void TrustedCallbackProjections_AreAcceptedAndInvalidOnesAreRejectedByName()
    {
        var acceptedProjections = new HashSet<MetamorphicWrapperProjection>();
        var rejectedReasons = new Dictionary<MetamorphicWrapperProjection, string>();

        foreach (var parameters in OfFamily(MetamorphicFamily.BuiltinCallbackWrapper))
        {
            var projection = MetamorphicCallbackWrapperTemplate.ProjectionOf(parameters);
            var precondition = MetamorphicTemplates.Build(parameters).Precondition;

            if (precondition.Satisfied) acceptedProjections.Add(projection);
            else rejectedReasons[projection] = precondition.Reason;
        }

        Assert.Contains(MetamorphicWrapperProjection.DottedFixed, acceptedProjections);
        Assert.Contains(MetamorphicWrapperProjection.OrdinaryFixed, acceptedProjections);
        Assert.DoesNotContain(MetamorphicWrapperProjection.Collecting, acceptedProjections);
        Assert.DoesNotContain(MetamorphicWrapperProjection.ArityMismatched, acceptedProjections);

        Assert.Equal(
            "collecting-projection-collects-a-list-not-the-supplied-value",
            rejectedReasons[MetamorphicWrapperProjection.Collecting]);
        Assert.Equal(
            "wrapper-arity-does-not-match-callback-projection",
            rejectedReasons[MetamorphicWrapperProjection.ArityMismatched]);
    }

    [Fact]
    public void CollectingProjection_IsGenuinelyNotEquivalent_WhichIsWhyItIsRejected()
    {
        // Evidence for the precondition: a collecting parameter COLLECTS the supplied
        // slot into a list, so the wrapper sees [element] where the direct builtin sees element.
        const string direct = "MmRows = [[1, 2], [3]]\nMmRows.map(count)";
        const string collectingWrapper = "MmWrap(*xs) = count(xs)\nMmRows = [[1, 2], [3]]\nMmRows.map(MmWrap)";

        Assert.True(MetamorphicExecutor.TryObserve(direct, null, true, out var a, out _));
        Assert.True(MetamorphicExecutor.TryObserve(collectingWrapper, null, true, out var b, out _));
        Assert.Equal("L[2, 1]", a.Semantic.Structure);
        Assert.Equal("L[1, 1]", b.Semantic.Structure);
        Assert.NotEqual(a.Semantic, b.Semantic);
    }

    [Fact]
    public void ArityMismatchedProjection_IsGenuinelyNotEquivalent()
    {
        const string direct = "MmRows = [1, 2, 3]\nMmRows.map(count)";
        const string twoParam = "MmWrap(a, b) = count(a)\nMmRows = [1, 2, 3]\nMmRows.map(MmWrap)";

        Assert.True(MetamorphicExecutor.TryObserve(direct, null, true, out var a, out _));
        Assert.True(MetamorphicExecutor.TryObserve(twoParam, null, true, out var b, out _));
        Assert.Equal("ok", a.Semantic.Outcome);
        Assert.Equal("err", b.Semantic.Outcome);
    }

    /// <summary>
    /// The rejected projections are a UNIVERSAL precondition over a generated family, so one
    /// worked example is not the claim. This sweeps the COMPLETE normalized callback-wrapper
    /// space — every consumer, every eligible callback builtin, every input shape, both rejected
    /// projections — and for each point checks that
    ///
    /// <list type="bullet">
    ///   <item>the rejection carries its documented reason;</item>
    ///   <item>the case never reaches the comparator as an accepted equivalence;</item>
    ///   <item>the wrapper really is written in the shape the reason names.</item>
    /// </list>
    ///
    /// <para>The semantic reason is then discharged per (projection x callback arity), by RUNNING
    /// the direct form against the wrapper form. Note what the sweep shows and a single example
    /// would hide: these projections are not observably different at EVERY point. A collecting wrapper
    /// binds <c>[element]</c> where the builtin binds <c>element</c>, and for several
    /// builtin/element combinations the two are indistinguishable (<c>count</c> of a scalar and
    /// of a one-element list are both 1); an empty input never invokes the callback at all, so
    /// every projection agrees there. That is exactly why the precondition must be STRUCTURAL — a
    /// property of how the wrapper binds — rather than a per-case measurement, which would
    /// quietly admit those coincidences as evidence of equivalence.</para>
    /// </summary>
    [Fact]
    public void EveryRejectedCallbackProjection_IsRejectedByNameAndNeverReachesTheComparator()
    {
        var expected = new Dictionary<MetamorphicWrapperProjection, string>
        {
            [MetamorphicWrapperProjection.Collecting] = "collecting-projection-collects-a-list-not-the-supplied-value",
            [MetamorphicWrapperProjection.ArityMismatched] = "wrapper-arity-does-not-match-callback-projection",
        };

        var visited = new HashSet<MetamorphicParameters>();
        var coveredConsumers = new HashSet<string>(StringComparer.Ordinal);
        var coveredCallbacks = new HashSet<(MetamorphicWrapperProjection, int, string)>();
        var coveredInputs = new HashSet<(MetamorphicWrapperProjection, int, string)>();
        var disagreements = new HashSet<(MetamorphicWrapperProjection, int)>();
        var emptyInputAgreements = 0;
        var rejectedPoints = 0;

        for (var consumer = 0; consumer < MetamorphicTables.CallbackConsumers.Length; consumer++)
            for (var callback = 0; callback < MetamorphicTables.Builtins.Length; callback++)
                for (var input = 0; input < MetamorphicTables.CallbackInputShapes.Length; input++)
                    for (var projection = 0; projection < MetamorphicTables.WrapperProjections.Length; projection++)
                    {
                        var parameters = MetamorphicDecoder.Decode(
                            [0x04, 0, 0, 1, 1, 0, (byte)consumer, (byte)callback, (byte)input, (byte)projection]);
                        var kind = MetamorphicCallbackWrapperTemplate.ProjectionOf(parameters);
                        if (!expected.TryGetValue(kind, out var reason)) continue;
                        if (!visited.Add(parameters)) continue;

                        var testCase = MetamorphicTemplates.Build(parameters);
                        var consumerName = MetamorphicCallbackWrapperTemplate.ConsumerOf(parameters);
                        var arity = MetamorphicTables.CallbackArityOf(consumerName);
                        var callbackName = MetamorphicCallbackWrapperTemplate.CallbackOf(parameters).Name;
                        var inputShape = MetamorphicCallbackWrapperTemplate.InputOf(parameters);

                        // Normalize maps the callback dimension onto the builtins this consumer's arity can
                        // accept, so a decoded point never names an impossible callback.
                        Assert.True(
                            MetamorphicCallbackWrapperTemplate.CallbackOf(parameters).IsCallbackOfArity(arity),
                            $"decoded point names a callback the consumer cannot supply: {parameters}");

                        rejectedPoints++;
                        coveredConsumers.Add(consumerName);
                        coveredCallbacks.Add((kind, arity, callbackName));
                        coveredInputs.Add((kind, arity, inputShape.Id));

                        // Rejected by NAME, and never compared: execution stops at the precondition.
                        Assert.False(testCase.Precondition.Satisfied);
                        Assert.Equal(reason, testCase.Precondition.Reason);

                        var execution = MetamorphicExecutor.Execute(testCase);
                        Assert.False(execution.Accepted);
                        Assert.Equal(reason, execution.RejectionReason);
                        Assert.Null(execution.Left);
                        Assert.Null(execution.Right);

                        var report = MetamorphicInvariants.Run(parameters.Encode());
                        Assert.False(report.Accepted);
                        Assert.Null(report.Mismatch);

                        // The wrapper really is written in the shape its rejection reason names.
                        var wrapperLine = testCase.RightSource.Split('\n')[0];
                        var expectedWrapper = kind == MetamorphicWrapperProjection.Collecting
                            ? $"{MetamorphicTables.WrapperFunction}(*xs) = "
                            : $"{MetamorphicTables.WrapperFunction}({(arity == 1 ? "a, b" : "a")}) = ";
                        Assert.StartsWith(expectedWrapper, wrapperLine, StringComparison.Ordinal);

                        // Evidence: run both forms and record where they genuinely disagree.
                        Assert.True(MetamorphicExecutor.TryObserve(testCase.LeftSource, null, true, out var direct, out _));
                        Assert.True(MetamorphicExecutor.TryObserve(testCase.RightSource, null, true, out var wrapped, out _));

                        if (!Equals(direct.Semantic, wrapped.Semantic)) disagreements.Add((kind, arity));

                        // An EMPTY input never invokes the callback, so no projection can be distinguished
                        // there. That is a positive, falsifiable claim — and the clearest demonstration that
                        // the precondition has to be structural: measuring these points would report a
                        // rejected projection as equivalent.
                        if (inputShape.CollectionItemCount == 0)
                        {
                            Assert.Equal(direct.Semantic, wrapped.Semantic);
                            emptyInputAgreements++;
                        }
                    }

        // The complete space really was covered: both consumer arities, all three consumers,
        // every eligible callback builtin, and every input shape, for BOTH rejected projections.
        Assert.True(rejectedPoints > 0, "no rejected callback-projection point was generated");
        Assert.Equal(MetamorphicTables.CallbackConsumers.Length, coveredConsumers.Count);
        foreach (var kind in expected.Keys)
            foreach (var arity in new[] { 1, 2 })
            {
                var callbacks = MetamorphicTables.Builtins.Where(b => b.IsCallbackOfArity(arity)).Select(b => b.Name);
                Assert.Equal(
                    callbacks.Order().ToArray(),
                    coveredCallbacks.Where(e => e.Item1 == kind && e.Item2 == arity).Select(e => e.Item3).Order().ToArray());
                Assert.Equal(
                    MetamorphicTables.CallbackInputShapes.Select(s => s.Id).Order().ToArray(),
                    coveredInputs.Where(e => e.Item1 == kind && e.Item2 == arity).Select(e => e.Item3).Order().ToArray());

                // And each (projection, arity) has at least one point where the difference IS visible.
                Assert.Contains((kind, arity), disagreements);
            }

        Assert.True(emptyInputAgreements > 0, "the empty-input coincidence was never exercised");
    }

    [Fact]
    public void CallbackArguments_StayInTheCallableAlgorithmChannel()
    {
        // Both members name the callback rather than reifying it, so the builtin's algorithm
        // channel is used on both sides and a higher-order argument stays lazy.
        foreach (var parameters in OfFamily(MetamorphicFamily.BuiltinCallbackWrapper))
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            if (!testCase.Precondition.Satisfied) continue;

            var callback = MetamorphicCallbackWrapperTemplate.CallbackOf(parameters);
            var consumer = MetamorphicCallbackWrapperTemplate.ConsumerOf(parameters);
            Assert.Contains($"{consumer}({callback.Name}", OutputExpression(testCase.LeftSource), StringComparison.Ordinal);
            Assert.Contains($"{consumer}({MetamorphicTables.WrapperFunction}", OutputExpression(testCase.RightSource), StringComparison.Ordinal);
        }

        // A callable receiver keeps its algorithm meaning through the dotted rewrite.
        Assert.True(MetamorphicExecutor.TryObserve(
            "MmApply(g, v) = g(v)\nMmDouble(x) = x * 2\nMmDouble.MmApply(7)", null, true, out var dotted, out _));
        Assert.True(MetamorphicExecutor.TryObserve(
            "MmApply(g, v) = g(v)\nMmDouble(x) = x * 2\nMmApply(MmDouble, 7)", null, true, out var ordinary, out _));
        Assert.Equal(ordinary.Semantic, dotted.Semantic);
        Assert.Equal("14", dotted.Semantic.Structure);
    }

    // ── The declared relations, over the whole stratified space ──────────────

    [Fact]
    public void EveryStratifiedParameterPoint_SatisfiesItsDeclaredRelations()
    {
        var accepted = new Dictionary<string, int>(StringComparer.Ordinal);
        var rejected = new Dictionary<string, int>(StringComparer.Ordinal);

        foreach (var parameters in Stratified)
        {
            // Exactly what the fuzz callback does, including its harness self-checks.
            MetamorphicInvariants.Check(parameters.Encode());

            var report = MetamorphicInvariants.Run(parameters.Encode());
            Assert.Null(report.Mismatch);

            var family = report.Execution.Case.FamilyId;
            if (report.Accepted) accepted[family] = accepted.GetValueOrDefault(family) + 1;
            else rejected[$"{family}/{report.RejectionReason}"] = rejected.GetValueOrDefault($"{family}/{report.RejectionReason}") + 1;
        }

        // Every family contributes accepted cases — including the Phase 3 ones, which this sweep
        // still executes in full even though the rejection inventory below is scoped.
        foreach (var definition in MetamorphicFamilyRegistry.All)
            Assert.True(accepted.GetValueOrDefault(definition.Id) > 0, $"family '{definition.Id}' produced no accepted case");

        // Every rejection must be one of the reasons the templates document, so a high
        // rejection rate can never hide behind unexplained coverage loss. The inventory is scoped
        // to the REWRITE families this file owns; Phase 3's own reasons are enumerated by
        // MetamorphicPhase3FamilyTests.EveryPhase3Rejection_IsOneOfTheDocumentedReasons.
        string[] expectedRejections =
        [
            // Callback projections that are provably NOT equivalent (see the template docs).
            "builtin-callback-wrapper/collecting-projection-collects-a-list-not-the-supplied-value",
            "builtin-callback-wrapper/wrapper-arity-does-not-match-callback-projection",
        ];

        var rewriteIds = RewriteFamilies.Select(MetamorphicCase.FamilyIdOf).ToHashSet(StringComparer.Ordinal);
        var rewriteRejected = rejected
            .Where(entry => rewriteIds.Contains(entry.Key[..entry.Key.IndexOf('/', StringComparison.Ordinal)]))
            .ToList();

        foreach (var entry in rewriteRejected)
            Assert.Contains(entry.Key, expectedRejections);

        // Rejection stays a bounded, explainable share rather than silent coverage loss.
        var rewriteAccepted = accepted.Where(entry => rewriteIds.Contains(entry.Key)).Sum(entry => entry.Value);
        var rewriteRejectedCount = rewriteRejected.Sum(entry => entry.Value);
        Assert.InRange(
            (double)rewriteRejectedCount / (rewriteAccepted + rewriteRejectedCount), 0.0, 0.35);
    }

    [Fact]
    public void OperationalRelations_AreDeclaredAtTheStrengthTheRepositoryEstablishes()
    {
        Assert.Equal(
            MetamorphicOperationalRelation.ExactObservedWorkEqual,
            MetamorphicFamilyRegistry.Get(MetamorphicFamily.UserExtensionCall).OperationalRelation);

        foreach (var family in new[]
        {
            MetamorphicFamily.DottedCollectionCall, MetamorphicFamily.DottedCollectionBuiltin,
            MetamorphicFamily.DottedChain, MetamorphicFamily.BuiltinCallbackWrapper,
        })
        {
            Assert.Equal(
                MetamorphicOperationalRelation.ExactMaterializationEqual,
                MetamorphicFamilyRegistry.Get(family).OperationalRelation);
        }
    }

    [Fact]
    public void ExactMaterializationAndBoundaryEquality_HoldForRepresentativeCases()
    {
        var exact = 0;
        var directional = 0;
        var fusionWitnesses = 0;

        foreach (var parameters in RewritePoints.Where(p => p.LimitMode == MetamorphicLimitMode.Default))
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            var execution = MetamorphicExecutor.Execute(testCase);
            if (!execution.Accepted) continue;

            Assert.Equal(execution.Left!.Semantic.IsResourceLimit, execution.Right!.Semantic.IsResourceLimit);

            if (testCase.OperationalRelation == MetamorphicOperationalRelation.MaterializationNeverIncreases)
            {
                // The right member is the fusion-eligible spelling: it may charge less, never more.
                Assert.True(execution.Right.MaterializedItems <= execution.Left.MaterializedItems);
                Assert.True(execution.Right.MaterializedStringChars <= execution.Left.MaterializedStringChars);
                directional++;
                if (execution.Right.MaterializedItems < execution.Left.MaterializedItems) fusionWitnesses++;
                continue;
            }

            Assert.Equal(execution.Left.MaterializedItems, execution.Right.MaterializedItems);
            Assert.Equal(execution.Left.MaterializedStringChars, execution.Right.MaterializedStringChars);
            exact++;
        }

        Assert.True(exact > 0 && directional > 0, "both relation strengths must be exercised");

        // The directional relation must be earned by a real optimization difference, not merely
        // declared: at least one fusion-eligible pair charges strictly less on the dotted side.
        // Without this the test would pass unchanged if the optimizer stopped fusing entirely.
        Assert.True(fusionWitnesses > 0, "no fusion-eligible pair actually materialized less");
    }

    [Fact]
    public void BothSidesCrossEveryCumulativeBoundaryTogether()
    {
        var probes = new (string Left, string Right)[]
        {
            ("MmR = range(1, 6)\ntake(MmR, 3)", "MmR = range(1, 6)\nMmR.take(3)"),
            ("MmF(r, a) = take(r, a)\nMmR = range(1, 6)\nMmF(MmR, 3)",
             "MmF(r, a) = take(r, a)\nMmR = range(1, 6)\nMmR.MmF(3)"),
            ("MmDouble(x) = x * 2\nMmR = range(1, 6)\ncount(map(MmR, MmDouble))",
             "MmDouble(x) = x * 2\nMmR = range(1, 6)\nMmR.map(MmDouble).count"),
            ("MmRows = [[1, 2], [3]]\nMmRows.map(count)",
             "MmWrap(a) = a.count\nMmRows = [[1, 2], [3]]\nMmRows.map(MmWrap)"),
            ("MmR = ['abc', 'de']\ndistinct(MmR)", "MmR = ['abc', 'de']\nMmR.distinct"),
        };

        foreach (var (left, right) in probes)
        {
            for (var budget = 1L; budget <= 20; budget++)
            {
                AssertSameBoundary(left, right, new EvaluationLimits { MaxMaterializedItems = budget });
                AssertSameBoundary(left, right, new EvaluationLimits { MaxCollectionItems = (int)budget });
            }

            for (var budget = 0L; budget <= 10; budget++)
            {
                AssertSameBoundary(left, right, new EvaluationLimits { MaxMaterializedStringChars = budget });
                AssertSameBoundary(left, right, new EvaluationLimits { MaxStringLength = (int)budget });
            }
        }

        static void AssertSameBoundary(string left, string right, EvaluationLimits limits)
        {
            Assert.True(MetamorphicExecutor.TryObserve(left, limits, true, out var a, out _));
            Assert.True(MetamorphicExecutor.TryObserve(right, limits, true, out var b, out _));
            Assert.Equal(a.Semantic, b.Semantic);
        }
    }

    /// <summary>
    /// The exact contract every operational relation carries: counters are compared only when
    /// BOTH executions complete. All three cases in one place —
    ///
    /// <list type="number">
    ///   <item>successful runs compare counters;</item>
    ///   <item>ordinary, non-resource semantic failures compare counters too;</item>
    ///   <item>a run stopped by a resource limit still compares its structured resource outcome,
    ///   but not its partial work counters.</item>
    /// </list>
    /// </summary>
    [Fact]
    public void OperationalCounters_AreComparedUnlessAResourceLimitAbortedARun()
    {
        var testCase = MetamorphicTemplates.Build(MetamorphicDecoder.Decode([0x01, 0, 0, 1, 1, 0, 0, 0, 0]));

        // (1) Two SUCCESSFUL runs: comparable, and a difference is reported.
        Assert.True(MetamorphicComparator.WorkIsComparable(Observation(items: 4), Observation(items: 4)));
        Assert.Equal(
            MetamorphicMismatchKind.MaterializedItems,
            MetamorphicComparator.Compare(testCase, Observation(items: 4), Observation(items: 9))!.Kind);

        // (2) An ordinary, NON-resource semantic failure is not exempt: both sides agree on the
        // error kind and payload, so the comparison reaches the counters and reports them.
        var leftError = Failed("TypeMismatch", isResourceLimit: false, items: 4);
        var rightError = Failed("TypeMismatch", isResourceLimit: false, items: 9);
        Assert.True(MetamorphicComparator.WorkIsComparable(leftError, rightError));
        var errorMismatch = MetamorphicComparator.Compare(testCase, leftError, rightError);
        Assert.Equal(MetamorphicMismatchKind.MaterializedItems, errorMismatch!.Kind);
        Assert.Equal(MetamorphicMismatchClass.Operational, errorMismatch.Class);

        // A real pair that fails this way is compared, not skipped: `sum` over strings.
        Assert.True(MetamorphicExecutor.TryObserve("MmR = ['ab', 'cd']\nsum(MmR)", null, true, out var realLeft, out _));
        Assert.True(MetamorphicExecutor.TryObserve("MmR = ['ab', 'cd']\nMmR.sum", null, true, out var realRight, out _));
        Assert.Equal("err", realLeft.Semantic.Outcome);
        Assert.False(realLeft.Semantic.IsResourceLimit);
        Assert.True(MetamorphicComparator.WorkIsComparable(realLeft, realRight));
        Assert.Equal(realLeft.MaterializedItems, realRight.MaterializedItems);

        // (3) A RESOURCE abort. Minimized campaign reproducer (payload 01 00 04 00 01 01 10 01 02):
        // both forms stop on the SAME string-budget error with the SAME payload, but the ordinary
        // call materialized its initial accumulator before forcing the receiver while the dotted
        // call prepares the receiver first — so the counters captured at the abort differ (2 vs 0).
        const string ordinary = "MmR = 'ab'\nreduce(MmR, contains, [1, 2])";
        const string dotted = "MmR = 'ab'\nMmR.reduce(contains, [1, 2])";
        var limits = new EvaluationLimits { MaxMaterializedStringChars = 1 };

        Assert.True(MetamorphicExecutor.TryObserve(ordinary, limits, false, out var left, out _));
        Assert.True(MetamorphicExecutor.TryObserve(dotted, limits, false, out var right, out _));

        // The structured resource outcome IS still compared
        Assert.Equal(left.Semantic, right.Semantic);
        Assert.True(left.Semantic.IsResourceLimit);
        Assert.Equal("StringMaterializationLimitExceeded", left.Semantic.ErrorCategory);
        Assert.Equal(
            MetamorphicMismatchKind.SemanticErrorPayload,
            MetamorphicComparator.Compare(
                testCase,
                Failed("StringMaterializationLimitExceeded", isResourceLimit: true, items: 0, payload: "limit=1"),
                Failed("StringMaterializationLimitExceeded", isResourceLimit: true, items: 0, payload: "limit=2"))!.Kind);

        // but... the partial counters are not.
        Assert.NotEqual(left.MaterializedItems, right.MaterializedItems);
        Assert.False(MetamorphicComparator.WorkIsComparable(left, right));
        Assert.Null(MetamorphicComparator.Compare(
            MetamorphicTemplates.Build(MetamorphicDecoder.Decode([0x01, 0, 4, 0, 1, 1, 0x10, 1, 2])), left, right));

        // The gate is scoped to aborted runs only: the same two programs run to completion are
        // compared exactly.
        Assert.True(MetamorphicExecutor.TryObserve(ordinary, null, false, out var wholeLeft, out _));
        Assert.True(MetamorphicExecutor.TryObserve(dotted, null, false, out var wholeRight, out _));
        Assert.True(MetamorphicComparator.WorkIsComparable(wholeLeft, wholeRight));
        Assert.Equal(wholeLeft.MaterializedItems, wholeRight.MaterializedItems);
        Assert.Equal(wholeLeft.MaterializedStringChars, wholeRight.MaterializedStringChars);
    }

    [Fact]
    public void NoObservableOutcomeEverDiffersBetweenOrdinaryAndDottedFormsUnderAnyBudgetPair()
    {
        // The evidence behind the gate above: across every trusted builtin, every receiver, and
        // the whole (item budget x string budget) grid, the two spellings always agree on what a
        // program can observe. Only the partial counters of an aborted run ever differ.
        var builtins = MetamorphicTables.Builtins
            .Where(b => b.SuffixKind is MetamorphicSuffixKind.None)
            .Select(b => (Ordinary: $"{b.Name}(MmR)", Dotted: $"MmR.{b.Name}"))
            .Append(("reduce(MmR, contains, [1, 2])", "MmR.reduce(contains, [1, 2])"))
            .ToList();

        foreach (var receiver in new[] { "'ab'", "['ab', 'cd']", "[1, 2, 3]", "7", "()" })
            foreach (var (ordinary, dotted) in builtins)
            {
                var left = $"MmR = {receiver}\n{ordinary}";
                var right = $"MmR = {receiver}\n{dotted}";

                for (var strings = 0L; strings <= 3; strings++)
                    for (var items = 1L; items <= 5; items++)
                    {
                        var limits = new EvaluationLimits { MaxMaterializedStringChars = strings, MaxMaterializedItems = items };
                        Assert.True(MetamorphicExecutor.TryObserve(left, limits, false, out var a, out _));
                        Assert.True(MetamorphicExecutor.TryObserve(right, limits, false, out var b, out _));
                        Assert.Equal(a.Semantic, b.Semantic);
                    }
            }
    }

    [Fact]
    public void GenerousLimits_BehaveExactlyLikeTheDefaultPolicy()
    {
        // BOTH members, and every counter — not just the left one's item total. The left member
        // of a chain is the non-fusible spelling, so observing only it would miss exactly the
        // failure this test exists to catch: a "generous" budget that silently changes optimizer
        // eligibility shows up on the RIGHT member first.
        var checkedCases = 0;
        foreach (var parameters in RewritePoints.Where(p => p.LimitMode == MetamorphicLimitMode.Generous))
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            if (!testCase.Precondition.Satisfied) continue;

            Assert.Null(testCase.Limits!.MaxMaterializedStringChars);
            Assert.Null(testCase.Limits.MaxStringLength);
            Assert.Null(testCase.Limits.MaxSteps);

            foreach (var source in new[] { testCase.LeftSource, testCase.RightSource })
            {
                Assert.True(MetamorphicExecutor.TryObserve(source, testCase.Limits, testCase.EnableOptimizations, out var bounded, out _));
                Assert.True(MetamorphicExecutor.TryObserve(source, null, testCase.EnableOptimizations, out var free, out _));
                Assert.Equal(free, bounded);
            }

            checkedCases++;
        }

        Assert.True(checkedCases > 0, "the generous policy produced no comparable case");
    }

    // ── Chain fusion policy: the relation must match the EFFECTIVE optimizer ──

    /// <summary>
    /// The harness's fusion-eligibility helper must agree with the runtime's own gate, measured
    /// on a chain that demonstrably fuses. Configuring either string budget, the cumulative
    /// item budget, or a step budget switches the sequence-pipeline optimizer off however
    /// generous the value is, so an eligibility rule that reads only the optimizer flag
    /// would be wrong here.
    /// </summary>
    [Fact]
    public void EffectiveFusionEligibility_MatchesWhatTheRuntimeActuallyDoes()
    {
        var (ordinary, dotted) = FusibleChainPair();

        (EvaluationLimits? Limits, bool Optimize)[] policies =
        [
            (null, true),
            (null, false),
            (new EvaluationLimits { MaxCollectionItems = 1_000 }, true),
            (new EvaluationLimits { MaxMaterializedItems = 1_000, MaxCollectionItems = 1_000 }, true),
            (new EvaluationLimits { MaxMaterializedStringChars = 1_000 }, true),
            (new EvaluationLimits { MaxStringLength = 1_000 }, true),
            (new EvaluationLimits { MaxSteps = 1_000_000 }, true),
            (new EvaluationLimits { MaxMaterializedItems = 1_000, MaxStringLength = 1_000 }, true),
        ];

        foreach (var (limits, optimize) in policies)
        {
            Assert.True(MetamorphicExecutor.TryObserve(ordinary, limits, optimize, out var left, out _));
            Assert.True(MetamorphicExecutor.TryObserve(dotted, limits, optimize, out var right, out _));

            var eligible = MetamorphicLimitPolicy.SequencePipelineFusionCanApply(optimize, limits);
            var describe = $"limits={MetamorphicCase.DescribeLimits(limits)} optimize={optimize}";

            if (eligible)
            {
                // The helper claimed fusion is possible, and on THIS chain it really happens.
                Assert.True(right.MaterializedItems < left.MaterializedItems, $"expected fusion: {describe}");
            }
            else
            {
                // The helper claimed fusion is impossible, so the two spellings agree exactly.
                Assert.Equal(left.MaterializedItems, right.MaterializedItems);
                Assert.Equal(left.MaterializedStringChars, right.MaterializedStringChars);
            }
        }
    }

    /// <summary>
    /// The directional relation is declared exactly where fusion can apply, and the observed
    /// counters prove the directional branch is a real optimization difference rather than an
    /// enum choice: the ordinary form materializes strictly more.
    /// </summary>
    [Fact]
    public void ChainRelation_IsDirectionalOnlyWhereFusionCanApply_AndTheDifferenceIsReal()
    {
        var definition = MetamorphicFamilyRegistry.Get(MetamorphicFamily.DottedChain);
        var directionalWitnesses = 0;
        var exactUnderStringLimits = 0;
        var exactUnderOptimizerOff = 0;

        for (var mode = 0; mode < definition.SupportedLimitModes.Length; mode++)
            for (var optimize = 0; optimize < 2; optimize++)
            {
                // The one chain measured to fuse (filter > count) on an exact-list receiver.
                var testCase = MetamorphicTemplates.Build(MetamorphicDecoder.Decode(
                    [0x03, 0, (byte)mode, 0, 0, (byte)optimize, FusibleChainIndex, ListReceiverIndex]));
                if (!testCase.Precondition.Satisfied) continue;

                var fusionCanApply = MetamorphicLimitPolicy.SequencePipelineFusionCanApply(
                    testCase.EnableOptimizations, testCase.Limits);

                Assert.Equal(
                    fusionCanApply
                        ? MetamorphicOperationalRelation.MaterializationNeverIncreases
                        : MetamorphicOperationalRelation.ExactMaterializationEqual,
                    testCase.OperationalRelation);

                var execution = MetamorphicExecutor.Execute(testCase);
                Assert.True(execution.Accepted);
                Assert.Null(MetamorphicComparator.Compare(testCase, execution.Left!, execution.Right!));

                if (fusionCanApply)
                {
                    // The dotted spelling really does less work here; the left one is not fusible.
                    Assert.True(execution.Right!.MaterializedItems < execution.Left!.MaterializedItems);
                    directionalWitnesses++;
                    continue;
                }

                Assert.Equal(execution.Left!.MaterializedItems, execution.Right!.MaterializedItems);
                if (testCase.Limits is { } limits && (limits.MaxStringLength is not null || limits.MaxMaterializedStringChars is not null))
                    exactUnderStringLimits++;
                else if (!testCase.EnableOptimizations)
                    exactUnderOptimizerOff++;
            }

        // All three regimes must actually be exercised, so the test fails if the chain stops
        // fusing, if the string-limit modes stop reaching the exact relation, or if the
        // optimizer-off policy disappears.
        Assert.True(directionalWitnesses > 0, "no fusion-eligible chain point charged less");
        Assert.True(exactUnderStringLimits > 0, "no configured-string-budget point reached the exact relation");
        Assert.True(exactUnderOptimizerOff > 0, "no optimizer-off point reached the exact relation");
    }

    /// <summary>
    /// Every accepted chain point satisfies the relation the new selector chose for it, over the
    /// whole chain x receiver x policy space rather than a sample.
    /// </summary>
    [Fact]
    public void EveryAcceptedChainPoint_SatisfiesItsSelectedRelation()
    {
        var definition = MetamorphicFamilyRegistry.Get(MetamorphicFamily.DottedChain);
        var accepted = 0;

        for (var chain = 0; chain < MetamorphicChainTemplate.ChainCount; chain++)
            for (var receiver = 0; receiver < MetamorphicTables.ReceiverShapes.Length; receiver++)
                for (var mode = 0; mode < definition.SupportedLimitModes.Length; mode++)
                    for (var optimize = 0; optimize < 2; optimize++)
                    {
                        var testCase = MetamorphicTemplates.Build(MetamorphicDecoder.Decode(
                            [0x03, 0, (byte)mode, 1, 1, (byte)optimize, (byte)chain, (byte)receiver]));
                        if (!testCase.Precondition.Satisfied) continue;

                        var execution = MetamorphicExecutor.Execute(testCase);
                        if (!execution.Accepted) continue;
                        accepted++;

                        Assert.Null(MetamorphicComparator.Compare(testCase, execution.Left!, execution.Right!));

                        // Where the exact relation was selected it must genuinely hold, not merely pass the
                        // weaker inequality the directional relation would have applied.
                        if (testCase.OperationalRelation == MetamorphicOperationalRelation.ExactMaterializationEqual
                            && MetamorphicComparator.WorkIsComparable(execution.Left!, execution.Right!))
                        {
                            Assert.Equal(execution.Left!.MaterializedItems, execution.Right!.MaterializedItems);
                            Assert.Equal(execution.Left.MaterializedStringChars, execution.Right.MaterializedStringChars);
                        }
                    }

        Assert.True(accepted > 0, "the chain family produced no accepted case");
    }

    /// <summary>
    /// A configured cumulative-item budget forces the generic sequence paths, so the
    /// cumulative-item modes are ACCEPTED (the former
    /// "fused-chain-does-not-share-the-cumulative-item-budget" rejection guarded a
    /// divergence that is structurally impossible now), fusion eligibility is off for
    /// them, and the two spellings agree exactly on the charged budget.
    /// </summary>
    [Fact]
    public void ChainCumulativeModes_AreAcceptedWhenTheirBudgetDisablesFusion()
    {
        var definition = MetamorphicFamilyRegistry.Get(MetamorphicFamily.DottedChain);
        var cumulativePointsExercised = 0;

        for (var mode = 0; mode < definition.SupportedLimitModes.Length; mode++)
            for (var optimize = 0; optimize < 2; optimize++)
            {
                var cumulative = definition.SupportedLimitModes[mode]
                    is MetamorphicLimitMode.CumulativeItems or MetamorphicLimitMode.Both;

                var testCase = MetamorphicTemplates.Build(MetamorphicDecoder.Decode(
                    [0x03, 0, (byte)mode, 1, 1, (byte)optimize, FusibleChainIndex, ListReceiverIndex]));

                // No mode is rejected for the retired cumulative-budget reason anymore.
                Assert.True(
                    testCase.Precondition.Satisfied
                        || testCase.Precondition.Reason != "fused-chain-does-not-share-the-cumulative-item-budget");
                if (!testCase.Precondition.Satisfied) continue;

                if (!cumulative) continue;
                cumulativePointsExercised++;

                // The harness eligibility mirror and the runtime gate agree: a configured
                // cumulative budget disables fusion however generous the value is…
                Assert.False(MetamorphicLimitPolicy.SequencePipelineFusionCanApply(
                    testCase.EnableOptimizations, testCase.Limits));

                // …so both spellings run generic and charge the SAME cumulative budget.
                var execution = MetamorphicExecutor.Execute(testCase);
                Assert.True(execution.Accepted);
                Assert.Null(MetamorphicComparator.Compare(testCase, execution.Left!, execution.Right!));
                if (MetamorphicComparator.WorkIsComparable(execution.Left!, execution.Right!))
                    Assert.Equal(execution.Left!.MaterializedItems, execution.Right!.MaterializedItems);
            }

        Assert.True(cumulativePointsExercised > 0, "no cumulative-item chain point was exercised");
    }

    /// <summary>The exhaustive Group B claim the family's ExactObservedWorkEqual relation rests on.</summary>
    [Fact]
    public void UserExtensionCall_AgreesOnExactWorkAtEveryParameterPoint()
    {
        var accepted = 0;
        foreach (var parameters in OfFamily(MetamorphicFamily.UserExtensionCall))
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            Assert.Equal(MetamorphicOperationalRelation.ExactObservedWorkEqual, testCase.OperationalRelation);

            var execution = MetamorphicExecutor.Execute(testCase);
            if (!execution.Accepted) continue;
            accepted++;

            Assert.Null(MetamorphicComparator.Compare(testCase, execution.Left!, execution.Right!));
            if (!MetamorphicComparator.WorkIsComparable(execution.Left!, execution.Right!)) continue;

            // Exact WORK: materialization plus steps and peak depth.
            Assert.Equal(execution.Left!.MaterializedItems, execution.Right!.MaterializedItems);
            Assert.Equal(execution.Left.MaterializedStringChars, execution.Right.MaterializedStringChars);
            Assert.Equal(execution.Left.EvaluationSteps, execution.Right.EvaluationSteps);
            Assert.Equal(execution.Left.PeakDynamicDepth, execution.Right.PeakDynamicDepth);
        }

        Assert.True(accepted > 0, "the user-extension family produced no accepted case");
    }

    /// <summary>
    /// The fluent spread form lowers to the same call AST as its explicit
    /// counterpart, so every accepted stratified point must agree on value or
    /// structured error, resource classification, evaluation steps,
    /// materialization, and peak call depth.
    /// </summary>
    [Fact]
    public void SpreadSpellingParity_AgreesOnSemanticsAndDeclaredWorkAtEveryParameterPoint()
    {
        var accepted = 0;
        var exactWork = 0;
        foreach (var parameters in OfFamily(MetamorphicFamily.SpreadSpellingParity))
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            var execution = MetamorphicExecutor.Execute(testCase);
            if (!execution.Accepted) continue;
            accepted++;

            Assert.Null(MetamorphicComparator.Compare(testCase, execution.Left!, execution.Right!));
            if (testCase.OperationalRelation != MetamorphicOperationalRelation.ExactObservedWorkEqual
                || !MetamorphicComparator.WorkIsComparable(execution.Left!, execution.Right!))
            {
                continue;
            }

            exactWork++;
            Assert.Equal(execution.Left!.MaterializedItems, execution.Right!.MaterializedItems);
            Assert.Equal(execution.Left.MaterializedStringChars, execution.Right.MaterializedStringChars);
            Assert.Equal(execution.Left.EvaluationSteps, execution.Right.EvaluationSteps);
            Assert.Equal(execution.Left.PeakDynamicDepth, execution.Right.PeakDynamicDepth);
        }

        Assert.True(accepted > 0, "the spread-spelling family produced no accepted case");
        Assert.True(exactWork > 0, "the fluent spread contexts produced no exact-work witness");
    }

    // ── Comparator ───────────────────────────────────────────────────────────

    [Fact]
    public void Comparator_ReportsExactWorkMismatchesOnlyForExactWorkFamilies()
    {
        var exactWork = MetamorphicTemplates.Build(
            MetamorphicDecoder.Decode([0x02, 0, 0, 1, 1, 0, 0, 0, 0]));
        Assert.Equal(MetamorphicOperationalRelation.ExactObservedWorkEqual, exactWork.OperationalRelation);

        var steps = MetamorphicComparator.Compare(exactWork, Observation(items: 4, steps: 3), Observation(items: 4, steps: 5));
        Assert.Equal(MetamorphicMismatchKind.EvaluationSteps, steps!.Kind);
        Assert.Equal(MetamorphicMismatchClass.Operational, steps.Class);

        var depth = MetamorphicComparator.Compare(exactWork, Observation(items: 4, depth: 1), Observation(items: 4, depth: 2));
        Assert.Equal(MetamorphicMismatchKind.PeakDynamicDepth, depth!.Kind);

        // A materialization-only family tolerates the very same step difference.
        var materializationOnly = MetamorphicTemplates.Build(
            MetamorphicDecoder.Decode([0x01, 0, 0, 1, 1, 0, 0, 0, 0]));
        Assert.Equal(MetamorphicOperationalRelation.ExactMaterializationEqual, materializationOnly.OperationalRelation);
        Assert.Null(MetamorphicComparator.Compare(materializationOnly, Observation(items: 4, steps: 3), Observation(items: 4, steps: 5)));
    }

    [Fact]
    public void Comparator_StillReportsEveryPhase1MismatchClass()
    {
        var testCase = MetamorphicTemplates.Build(MetamorphicDecoder.Decode([0x01, 0, 0, 1, 1, 0, 0, 0, 0]));

        Assert.Equal(
            MetamorphicMismatchKind.MaterializedItems,
            MetamorphicComparator.Compare(testCase, Observation(items: 4), Observation(items: 5))!.Kind);
        Assert.Equal(
            MetamorphicMismatchKind.MaterializedStringChars,
            MetamorphicComparator.Compare(testCase, Observation(items: 4, strings: 1), Observation(items: 4, strings: 2))!.Kind);
        Assert.Equal(
            MetamorphicMismatchKind.EmittedCount,
            MetamorphicComparator.Compare(testCase, Observation(items: 4, emitted: 1), Observation(items: 4, emitted: 2))!.Kind);
        Assert.Equal(
            MetamorphicMismatchKind.SemanticStructure,
            MetamorphicComparator.Compare(testCase, Observation(items: 4, structure: "1"), Observation(items: 4, structure: "2"))!.Kind);
    }

    // ── Fingerprints ─────────────────────────────────────────────────────────

    [Fact]
    public void Fingerprints_AreStableAndDistinguishMateriallyDifferentTemplates()
    {
        var seen = new Dictionary<string, MetamorphicParameters>(StringComparer.Ordinal);
        foreach (var parameters in Stratified)
        {
            var execution = MetamorphicExecutor.Execute(MetamorphicTemplates.Build(parameters));
            var fingerprint = MetamorphicFingerprint.Describe(execution, null);

            Assert.Equal(fingerprint, MetamorphicFingerprint.Describe(execution, null));
            Assert.DoesNotContain("System.", fingerprint, StringComparison.Ordinal);
            Assert.DoesNotContain("count(range(", fingerprint, StringComparison.Ordinal);   // never source text
            Assert.False(
                seen.ContainsKey(fingerprint),
                $"fingerprint collision:\n  {parameters}\n  {seen.GetValueOrDefault(fingerprint)}");
            seen[fingerprint] = parameters;
        }

        // Every declared field must be present on EVERY fingerprint, not just a sample: a field
        // that only appears for some cases cannot be counted on in a campaign summary.
        string[] fields =
        [
            "family=", "group=", "status=", "rejection=", "precondition=", "itemTotal=", "stringTotal=",
            "limitMode=", "primaryOffset=", "secondaryOffset=", "optimizer=", "relation=",
            "left=", "right=", "work=", "semanticMismatch=", "resourceMismatch=", "operationalMismatch=",
        ];

        foreach (var fingerprint in seen.Keys)
            foreach (var field in fields)
                Assert.Contains(field, fingerprint, StringComparison.Ordinal);
    }

    /// <summary>
    /// <c>work=</c> records which side of the resource-abort gate a case landed on, so a campaign
    /// summary can show how much of its coverage reached the work comparison. All three states
    /// must be reachable and correctly reported.
    /// </summary>
    [Fact]
    public void Fingerprint_RecordsWhetherOperationalCountersWereActuallyCompared()
    {
        var states = new Dictionary<string, MetamorphicParameters>(StringComparer.Ordinal);

        foreach (var parameters in Stratified)
        {
            var execution = MetamorphicExecutor.Execute(MetamorphicTemplates.Build(parameters));
            var fingerprint = MetamorphicFingerprint.Describe(execution, null);

            var expected = execution switch
            {
                { Left: { } left, Right: { } right } =>
                    MetamorphicComparator.WorkIsComparable(left, right) ? "compared" : "partial",
                _ => "absent",
            };

            Assert.Contains($"|work={expected}|", fingerprint, StringComparison.Ordinal);
            states.TryAdd(expected, parameters);
        }

        // A rejected case has no observations at all; an aborted pair is compared only
        // semantically; a completed pair reaches the counters.
        Assert.Equal(["absent", "compared", "partial"], states.Keys.Order().ToArray());
    }

    // ── Isolation ────────────────────────────────────────────────────────────

    [Fact]
    public void EveryFamilyGroup_IsIsolatedAndOrderIndependent()
    {
        foreach (var definition in MetamorphicFamilyRegistry.All)
        {
            var parameters = OfFamily(definition.Family).First(p => MetamorphicTemplates.Build(p).Precondition.Satisfied);
            var testCase = MetamorphicTemplates.Build(parameters);

            // A / unrelated B / A — the two A observations must be identical.
            MetamorphicExecutor.AssertIsolated(testCase.LeftSource, testCase.Limits, testCase.EnableOptimizations);
            MetamorphicExecutor.AssertIsolated(testCase.RightSource, testCase.Limits, testCase.EnableOptimizations);

            // Comparison order must not affect either observation.
            Assert.True(MetamorphicExecutor.TryObserve(testCase.LeftSource, testCase.Limits, testCase.EnableOptimizations, out var leftFirst, out _));
            Assert.True(MetamorphicExecutor.TryObserve(testCase.RightSource, testCase.Limits, testCase.EnableOptimizations, out var rightSecond, out _));
            Assert.True(MetamorphicExecutor.TryObserve(testCase.RightSource, testCase.Limits, testCase.EnableOptimizations, out var rightFirst, out _));
            Assert.True(MetamorphicExecutor.TryObserve(testCase.LeftSource, testCase.Limits, testCase.EnableOptimizations, out var leftSecond, out _));

            Assert.Equal(leftFirst, leftSecond);
            Assert.Equal(rightFirst, rightSecond);
        }
    }

    // ── Replay and seeds ─────────────────────────────────────────────────────

    [Fact]
    public void AllTrackedSeeds_ReplayCleanly()
        => Assert.Equal(0, MetamorphicReplay.RunReplay(["metamorphic-replay", SeedDirectory]));

    [Fact]
    public void TrackedSeeds_CoverEveryRegisteredFamily()
    {
        var seeds = LoadSeeds();
        foreach (var definition in MetamorphicFamilyRegistry.All)
        {
            Assert.Contains(seeds, seed => seed.DeclaredFamily == definition.Family);
        }

        Assert.All(seeds, seed => Assert.NotEqual("", seed.Description));
        Assert.All(seeds, seed => Assert.InRange(
            seed.Payload.Length, MetamorphicParameters.CommonPayloadLength, MetamorphicDecoder.MaxPayloadLength));
    }

    [Fact]
    public void TrackedSeeds_CoverTheRequiredPhase2Situations()
    {
        var cases = LoadSeeds()
            .Select(seed => MetamorphicTemplates.Build(MetamorphicDecoder.Decode(seed.Payload)))
            .ToList();

        var dottedBuiltin = cases.Where(c => c.Family == MetamorphicFamily.DottedCollectionBuiltin).ToList();
        Assert.Contains(dottedBuiltin, c => Parameters(c, MetamorphicDottedBuiltinTemplate.BuiltinOf).SuffixKind == MetamorphicSuffixKind.None);
        Assert.Contains(dottedBuiltin, c => Parameters(c, MetamorphicDottedBuiltinTemplate.BuiltinOf).SuffixKind == MetamorphicSuffixKind.WholeNumber);
        Assert.Contains(dottedBuiltin, c => Parameters(c, MetamorphicDottedBuiltinTemplate.BuiltinOf).ResultKind == MetamorphicResultKind.Collection);
        Assert.Contains(dottedBuiltin, c => Parameters(c, MetamorphicDottedBuiltinTemplate.BuiltinOf).SuffixKind == MetamorphicSuffixKind.Callback1);
        Assert.Contains(dottedBuiltin, c => c.ExpectedStringTotal > 0);
        Assert.Contains(dottedBuiltin, c => c.ExpectedItemTotal == 0);
        Assert.Contains(dottedBuiltin, c => c.Limits?.MaxMaterializedItems is not null);

        var userCalls = cases.Where(c => c.Family == MetamorphicFamily.UserExtensionCall).ToList();
        Assert.Contains(userCalls, c => Parameters(c, MetamorphicUserExtensionTemplate.BodyOf).SuffixArity == 0);
        Assert.Contains(userCalls, c => Parameters(c, MetamorphicUserExtensionTemplate.BodyOf).SuffixArity >= 2);
        Assert.Contains(userCalls, c => Parameters(c, MetamorphicUserExtensionTemplate.BodyOf).SuffixIsSpread);
        Assert.Contains(userCalls, c => Parameters(c, MetamorphicUserExtensionTemplate.BodyOf).Id == "multipleOutputs");

        var chains = cases.Where(c => c.Family == MetamorphicFamily.DottedChain).ToList();
        Assert.Contains(chains, c => MetamorphicChainTemplate.ChainOf(c.Parameters).Length == 2);
        Assert.Contains(chains, c => MetamorphicChainTemplate.ChainOf(c.Parameters).Length == 3);
        Assert.Contains(chains, c => MetamorphicChainTemplate.ChainOf(c.Parameters).Any(link => link.Suffix.Length > 0));

        var callbacks = cases.Where(c => c.Family == MetamorphicFamily.BuiltinCallbackWrapper).ToList();
        foreach (var consumer in MetamorphicTables.CallbackConsumers)
            Assert.Contains(callbacks, c => MetamorphicCallbackWrapperTemplate.ConsumerOf(c.Parameters) == consumer);
        Assert.Contains(callbacks, c => c.ExpectedStringTotal > 0);
        Assert.Contains(callbacks, c => !c.Precondition.Satisfied);
    }

    [Fact]
    public void ReplayRemainsDeterministicForEveryTrackedSeed()
    {
        foreach (var seed in LoadSeeds())
        {
            var first = MetamorphicInvariants.Run(seed.Payload);
            var second = MetamorphicInvariants.Run(seed.Payload);
            Assert.Equal(first.Fingerprint, second.Fingerprint);
            Assert.Equal(first.Execution.Left, second.Execution.Left);
            Assert.Equal(first.Execution.Right, second.Execution.Right);
        }
    }

    // ── Helpers ──────────────────────────────────────────────────────────────

    private static List<MetamorphicSeed> LoadSeeds()
    {
        var problems = new List<string>();
        var seeds = MetamorphicSeedFile.Load(Path.Combine(SeedDirectory, "seeds.txt"), problems).ToList();
        Assert.Empty(problems);
        return seeds;
    }

    private static byte[] ParseHex(string text)
        => [.. text.Split(' ').Select(part => Convert.ToByte(part, 16))];

    /// <summary>The elaborated expression behind a generated program's single output row.</summary>
    private static Expr OutputExpressionOf(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, source);
        return Assert.Single(parsed.Root.Output);
    }

    /// <summary>Every name a program exposes as a structural member, at any nesting depth.</summary>
    private static List<string> ExposedMemberNames(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, source);

        var names = new List<string>();
        Collect(parsed.Root);
        return names;

        void Collect(Algorithm algorithm)
        {
            foreach (var property in algorithm.Properties)
            {
                if (property.IsPublic) names.Add(property.Name);
                Collect(property.Value);
            }
        }
    }

    private static T Parameters<T>(MetamorphicCase testCase, Func<MetamorphicParameters, T> selector)
        => selector(testCase.Parameters);

    // The templates emit their output row as the final non-empty line of the
    // generated program (bare expression row; preparation definitions precede it).
    private static string OutputLine(string source)
        => source.Split('\n').Last(line => line.Length > 0);

    private static string OutputExpression(string source) => OutputLine(source);

    private static int CountOccurrences(string text, string needle)
    {
        var count = 0;
        var index = text.IndexOf(needle, StringComparison.Ordinal);
        while (index >= 0)
        {
            count++;
            index = text.IndexOf(needle, index + needle.Length, StringComparison.Ordinal);
        }

        return count;
    }

    private static MetamorphicOperationalObservation Observation(
        long items, long strings = 0, long steps = 0, int depth = 0, int emitted = 1, string structure = "1")
        => new(MetamorphicSemanticObservation.Success(structure, emitted), steps, items, strings, depth, "on");

    private static MetamorphicOperationalObservation Failed(
        string category, bool isResourceLimit, long items, string? payload = null)
        => new(MetamorphicSemanticObservation.Failure(category, payload, isResourceLimit), 0, items, 0, 0, "on");
}
