using System.Collections.Concurrent;

namespace KatLang.Tests;

/// <summary>
/// FE-4a: K properties can LOGICALLY require the same W ancestor inputs — K × W memberships of the
/// relation "property P requires input A of owner O" — without the representation PHYSICALLY repeating
/// the W-wide set per property. Every property whose final requirement summary is equal holds a
/// reference to ONE immutable output list (<see cref="Property.RequiredAncestorParameters"/> and the
/// internal <see cref="Property.CaptureRequirements"/>), and properties that each add a few inputs to
/// one wide set hold persistent lists sharing that set's structure. The canonical hostile shape (one
/// owner of W parameters, a <c>Base</c> reading all W, K properties reading <c>Base</c>) formerly
/// retained (K + 1) × W entries per list; it now retains W.
///
/// <para>The pins separate the four quantities: LOGICAL memberships (the sum of list counts over
/// properties), the distinct BACKING lists, the PHYSICAL entries those backings store, and the
/// representation WORK the pass performs (<see cref="FrontEndTraversalObservations"/>'s
/// <c>RequiredAncestor*</c> and <c>SummaryMember*</c> counters). Exact identity is pinned
/// separately: same-named parameters of different owners stay different requirements, and an
/// independent slow oracle recomputes the relation for generated dependency graphs.</para>
/// </summary>
public class RequiredAncestorRepresentationTests
{
    private static object Backing(object list)
        => list switch
        {
            RequiredAncestorList<string> names => names.Backing,
            RequiredAncestorList<CapturedParameterRequirement> captures => captures.Backing,
            _ => list,
        };

    private static void AssertSameBacking(object? first, object? second)
        => Assert.Same(first is null ? null : Backing(first), second is null ? null : Backing(second));
    private static string Names(string prefix, int count, string separator = ", ")
        => string.Join(separator, Enumerable.Range(0, count).Select(i => $"{prefix}{i}"));

    private static string Arguments(int count, int start = 1)
        => string.Join(", ", Enumerable.Range(start, count));

    /// <summary>The exact FE-3 review shape: one owner of W parameters, Base reads all W, K properties read Base.</summary>
    private static string Canonical(int properties, int width)
        => $"O({Names("v", width)}) = {{\n    Base = {Names("v", width)}\n"
            + string.Concat(Enumerable.Range(0, properties).Select(i => $"    P{i} = Base\n"))
            + "    Base\n}\n1";

    private static Algorithm.User Exposed(string source, FrontEndTraversalObservations observations)
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var (detected, detectionDiagnostics) = ParameterDetector.DetectPrevalidated(syntax);
        Assert.Empty(detectionDiagnostics);
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations: null, diagnostics);
        Assert.Empty(diagnostics);
        return (Algorithm.User)PropertyExposureResolver.Resolve(resolved, observations);
    }

    private static IEnumerable<Property> AllProperties(Algorithm root)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (!seen.Add(node))
                continue;
            switch (node)
            {
                case Algorithm.User user:
                    foreach (var open in user.Opens) pending.Push(open);
                    foreach (var property in user.Properties) pending.Push(property);
                    foreach (var row in user.Output) pending.Push(row);
                    break;
                case Algorithm.Conditional conditional:
                    foreach (var branch in conditional.Branches) pending.Push(branch.Body);
                    break;
                case Property property:
                    yield return property;
                    pending.Push(property.Value);
                    break;
                case Expr.AlgorithmExpr(var nested):
                    pending.Push(nested);
                    break;
                case Expr.Call(var function, var args):
                    pending.Push(function);
                    foreach (var argument in args) pending.Push(argument);
                    break;
                case Expr.Capture(var body):
                    foreach (var row in body) pending.Push(row);
                    break;
            }
        }
    }

    private static Property Member(Algorithm owner, params string[] path)
    {
        var current = owner;
        Property? property = null;
        foreach (var name in path)
        {
            property = Assert.Single(current.Properties, p => p.Name == name);
            current = property.Value;
        }

        return property!;
    }

    /// <summary>Logical memberships, distinct backings, and the entries those backings store.</summary>
    private readonly record struct Census(long Logical, int Backings, long Physical, long CaptureLogical, int CaptureBackings, long CapturePhysical);

    private static Census Count(IEnumerable<Property> properties)
    {
        var names = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var captures = new HashSet<object>(ReferenceEqualityComparer.Instance);
        long logical = 0, physical = 0, captureLogical = 0, capturePhysical = 0;
        foreach (var property in properties)
        {
            logical += property.RequiredAncestorParameters.Count;
            if (property.RequiredAncestorParameters.Count > 0 && names.Add(Backing(property.RequiredAncestorParameters)))
                physical += property.RequiredAncestorParameters.Count;
            var capture = property.CaptureRequirements ?? [];
            captureLogical += capture.Count;
            if (capture.Count > 0 && captures.Add(Backing(capture)))
                capturePhysical += capture.Count;
        }

        return new Census(logical, names.Count, physical, captureLogical, captures.Count, capturePhysical);
    }

    // ── The canonical structural law ──────────────────────────────────────────

    /// <summary>
    /// K + 1 properties (Base and K readers) each logically require the W parameters — (K + 1) × W
    /// memberships — while ONE W-entry list backs every one of them, for the public names and the
    /// internal capture requirements alike, and every property holds that same list. The work is
    /// O(K + W): the W requirements are canonicalized once, each of the K + 2 level equations (the
    /// root's one property, the owner's K + 1) is evaluated once, the summary channel expands only
    /// Base (every reader shares its seed), and exactly two W-entry lists are materialized.
    /// </summary>
    [Theory]
    [InlineData(16, 16)]
    [InlineData(32, 32)]
    [InlineData(64, 64)]
    [InlineData(128, 128)]
    [InlineData(256, 256)]
    [InlineData(64, 32)]
    [InlineData(64, 128)]
    [InlineData(64, 512)]
    [InlineData(32, 64)]
    [InlineData(128, 64)]
    [InlineData(256, 64)]
    public void IdenticalRequirementSets_ShareOneBackingList(int width, int properties)
    {
        var observations = new FrontEndTraversalObservations();
        var root = Exposed(Canonical(properties, width), observations);
        var owner = Member(root, "O").Value;
        var census = Count(owner.Properties);

        Assert.Equal((long)(properties + 1) * width, census.Logical);
        Assert.Equal(1, census.Backings);
        Assert.Equal(width, census.Physical);
        Assert.Equal((long)(properties + 1) * width, census.CaptureLogical);
        Assert.Equal(1, census.CaptureBackings);
        Assert.Equal(width, census.CapturePhysical);

        var shared = Member(owner, "Base").RequiredAncestorParameters;
        Assert.All(owner.Properties, property => AssertSameBacking(shared, property.RequiredAncestorParameters));
        Assert.All(owner.Properties, property => AssertSameBacking(Member(owner, "Base").CaptureRequirements, property.CaptureRequirements));

        Assert.Equal(width, observations.RequiredAncestorElementsCanonicalized);
        Assert.Equal(properties + 2, observations.RequiredAncestorLevelEvaluations);
        Assert.Equal(2, observations.RequiredAncestorListsMaterialized);
        Assert.Equal(2L * width, observations.RequiredAncestorListEntriesMaterialized);
        Assert.Equal(properties + 1, observations.SummaryMemberEvaluations);
        Assert.Equal(1, observations.SummaryMemberExpansions);
    }

    /// <summary>The public result carries the same shared representation as the direct pass.</summary>
    [Fact]
    public void PublicParseResult_SharesTheBackingList()
    {
        var root = SourceProvenance.ParseValid(Canonical(40, 24)).Root;
        var owner = Member(root, "O").Value;
        var census = Count(owner.Properties);
        Assert.Equal(41L * 24, census.Logical);
        Assert.Equal(1, census.Backings);
        Assert.Equal(24, census.Physical);
    }

    // ── Transitive, diamond, and cyclic dependencies ──────────────────────────

    public static TheoryData<string, int> SharedShapes() => new()
    {
        // Forward chain: P0 = Base, P(i) = P(i-1).
        { "chain", 0 },
        // Reverse chain: the dependency of every property is declared AFTER it.
        { "reverse-chain", 0 },
        // Diamonds: L and R read Base, every P reads both.
        { "diamond", 2 },
        // A sibling cycle through Base: P(i) = P(i+1), Base; Base reads P0.
        { "cycle", 0 },
    };

    private static string SharedShape(string shape, int properties, int width)
    {
        var header = $"O({Names("v", width)}) = {{\n";
        return shape switch
        {
            "chain" => header + $"    Base = {Names("v", width)}\n"
                + string.Concat(Enumerable.Range(0, properties).Select(i => $"    P{i} = {(i == 0 ? "Base" : $"P{i - 1}")}\n"))
                + "    Base\n}\n1",
            "reverse-chain" => header
                + string.Concat(Enumerable.Range(0, properties).Select(i => $"    P{i} = {(i == properties - 1 ? "Base" : $"P{i + 1}")}\n"))
                + $"    Base = {Names("v", width)}\n    Base\n}}\n1",
            "diamond" => header + $"    Base = {Names("v", width)}\n    L = Base\n    R = Base\n"
                + string.Concat(Enumerable.Range(0, properties).Select(i => $"    P{i} = L, R\n"))
                + "    Base\n}\n1",
            "cycle" => header + $"    Base = {Names("v", width)}, P0\n"
                + string.Concat(Enumerable.Range(0, properties).Select(i => $"    P{i} = P{(i + 1) % properties}, Base\n"))
                + "    1\n}\n1",
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
    }

    /// <summary>
    /// Transitive chains in either declaration order, diamonds, and cycles all end with every property
    /// requiring the same W inputs: one backing list, and O(K + W) representation work — a chain is
    /// solved in O(K) evaluations whichever way it is declared (the former round-by-round solve
    /// needed K rounds of all K, allocating K² × W), and a cycle's members share one seed.
    /// </summary>
    [Theory]
    [MemberData(nameof(SharedShapes))]
    public void TransitiveDiamondAndCyclicDependencies_ShareOneBackingList(string shape, int extraProperties)
    {
        foreach (var (properties, width) in new[] { (32, 32), (128, 128) })
        {
            var observations = new FrontEndTraversalObservations();
            var root = Exposed(SharedShape(shape, properties, width), observations);
            var owner = Member(root, "O").Value;
            var census = Count(owner.Properties);
            var expected = Names("v", width).Split(", ").Order(StringComparer.Ordinal).ToArray();

            Assert.All(owner.Properties, property => Assert.Equal(expected, property.RequiredAncestorParameters));
            Assert.Equal((long)(properties + 1 + extraProperties) * width, census.Logical);
            Assert.Equal(1, census.Backings);
            Assert.Equal(width, census.Physical);
            Assert.Equal(1, census.CaptureBackings);

            var equations = properties + 2 + extraProperties;
            Assert.InRange(observations.RequiredAncestorLevelEvaluations, equations, 2 * equations);
            Assert.InRange(observations.SummaryMemberEvaluations, 1, 2 * equations);
            Assert.InRange(observations.SummaryMemberExpansions, 0, 2);
            Assert.Equal(width, observations.RequiredAncestorElementsCanonicalized);
            Assert.Equal(2L * width, observations.RequiredAncestorListEntriesMaterialized);
        }
    }

    /// <summary>
    /// A cycle whose every member ALSO adds its own parameter (<c>P(i) = P(i+1), x(i)</c>): each member
    /// logically requires every x — K × K memberships — yet the members form one strongly connected
    /// component solved as ONE unit, so the work stays linear and every member holds one list. The
    /// former round-by-round solve propagated each x around the cycle, one step per round.
    /// </summary>
    [Theory]
    [InlineData(64)]
    [InlineData(256)]
    public void CycleOfMembersAddingTheirOwnInputs_IsSolvedAsOneComponent(int properties)
    {
        var source = $"O({Names("x", properties)}) = {{\n"
            + string.Concat(Enumerable.Range(0, properties).Select(i => $"    P{i} = P{(i + 1) % properties}, x{i}\n"))
            + "    1\n}\n1";
        var observations = new FrontEndTraversalObservations();
        var owner = Member(Exposed(source, observations), "O").Value;
        var expected = Names("x", properties).Split(", ").Order(StringComparer.Ordinal).ToArray();

        Assert.All(owner.Properties, property => Assert.Equal(expected, property.RequiredAncestorParameters));
        var census = Count(owner.Properties);
        Assert.Equal((long)properties * properties, census.Logical);
        Assert.Equal(1, census.Backings);
        Assert.Equal(properties, census.Physical);
        Assert.InRange(observations.RequiredAncestorLevelEvaluations, properties, 3L * properties);
        Assert.Equal(1, observations.SummaryMemberEvaluations);
        Assert.Equal(0, observations.SummaryMemberExpansions);
    }

    /// <summary>
    /// K properties reading one OPENED member, or one member PATH, whose requirement is the owner's W
    /// parameters: the level settles that one reference ONCE (every reader reuses the validated
    /// settlement), the summary channel expands it once, and every reader shares one W-entry list —
    /// the former solve re-resolved the provided member's W-wide seed per property per round.
    /// </summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void OpenedOrNavigatedMember_IsSettledOncePerLevel(bool throughOpen)
    {
        const int width = 64;
        const int properties = 96;
        var source = $"O({Names("v", width)}) = {{\n" + (throughOpen ? "    open Lib\n" : "")
            + $"    Lib = {{\n        public Base = {Names("v", width)}\n        1\n    }}\n"
            + string.Concat(Enumerable.Range(0, properties).Select(i => $"    P{i} = {(throughOpen ? "Base" : "Lib.Base")}\n"))
            + "    1\n}\n1";
        var observations = new FrontEndTraversalObservations();
        var owner = Member(Exposed(source, observations), "O").Value;
        var expected = Names("v", width).Split(", ").Order(StringComparer.Ordinal).ToArray();

        var shared = Member(owner, "P0").RequiredAncestorParameters;
        Assert.Equal(expected, shared);
        for (var i = 0; i < properties; i++)
            AssertSameBacking(shared, Member(owner, $"P{i}").RequiredAncestorParameters);
        Assert.Equal(expected.Select(name => new CapturedParameterRequirement(name, 1)), Member(owner, "Lib", "Base").CaptureRequirements!);
        var census = Count(owner.Properties);
        Assert.Equal((long)properties * width, census.Logical);
        Assert.Equal(1, census.Backings);
        Assert.Equal(width, census.Physical);

        Assert.Equal(1, observations.RequiredAncestorResolutionComputations);
        Assert.Equal(3, observations.SummaryMemberExpansions);
        Assert.Equal(3L * width, observations.RequiredAncestorListEntriesMaterialized);
    }

    /// <summary>
    /// A design-independent guard over the public parse path: doubling K = W roughly doubles the
    /// allocation for identical, transitive, partially overlapping, and cyclic requirement shapes. A
    /// representation or solve that copies a W-wide set per property, or runs a round per chain
    /// step, quadruples it or worse (the former solve allocated K² × W on the chain).
    /// </summary>
    [Theory]
    [InlineData("canonical")]
    [InlineData("reverse-chain")]
    [InlineData("overlap")]
    [InlineData("cycle-with-own-inputs")]
    public void PublicParse_AllocationGrowsLinearly(string shape)
    {
        static string Source(string shape, int n) => shape switch
        {
            "canonical" => Canonical(n, n),
            "reverse-chain" => SharedShape("reverse-chain", n, n),
            "overlap" => $"O({Names("v", n)}, {Names("x", n)}) = {{\n    Base = {Names("v", n)}\n"
                + string.Concat(Enumerable.Range(0, n).Select(i => $"    P{i} = Base, x{i}\n")) + "    Base\n}\n1",
            "cycle-with-own-inputs" => $"O({Names("x", n)}) = {{\n"
                + string.Concat(Enumerable.Range(0, n).Select(i => $"    P{i} = P{(i + 1) % n}, x{i}\n")) + "    1\n}\n1",
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };

        static long Allocation(string source)
        {
            void Parse() => Assert.Empty(SourceProvenance.ParseValid(source).Diagnostics);
            Parse();
            var before = GC.GetAllocatedBytesForCurrentThread();
            Parse();
            return GC.GetAllocatedBytesForCurrentThread() - before;
        }

        var small = Allocation(Source(shape, 256));
        var large = Allocation(Source(shape, 512));
        var ratio = (double)large / small;
        Assert.True(ratio < 2.6, $"Doubling K = W grew the allocation {ratio:F2}x ({small} -> {large} bytes).");
    }

    // ── Partial overlap: persistent structural sharing ────────────────────────

    /// <summary>
    /// K properties each add ONE own parameter to a shared W-wide base (<c>P(i) = Base, x(i)</c>):
    /// K distinct sets of W + 1 inputs, K × (W + 1) logical memberships. The base's lists are
    /// materialized once; each property's list is DERIVED from them by its one-element difference
    /// (a persistent list sharing the base's structure), in either declaration order — never K flat
    /// W-entry copies. Contents stay exact: sorted, distinct names, and name-then-depth captures.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PartiallyOverlappingSets_DeriveFromTheSharedBase(bool baseDeclaredLast)
    {
        const int width = 64;
        const int properties = 96;
        var header = $"O({Names("v", width)}, {Names("x", properties)}) = {{\n";
        var baseLine = $"    Base = {Names("v", width)}\n";
        var readers = string.Concat(Enumerable.Range(0, properties).Select(i => $"    P{i} = Base, x{i}\n"));
        var source = header + (baseDeclaredLast ? readers + baseLine : baseLine + readers) + "    Base\n}\n1";
        var observations = new FrontEndTraversalObservations();
        var owner = Member(Exposed(source, observations), "O").Value;

        var baseNames = Names("v", width).Split(", ");
        for (var i = 0; i < properties; i++)
        {
            var property = Member(owner, $"P{i}");
            Assert.Equal(baseNames.Append($"x{i}").Order(StringComparer.Ordinal), property.RequiredAncestorParameters);
            Assert.Equal(
                baseNames.Append($"x{i}").Order(StringComparer.Ordinal).Select(name => new CapturedParameterRequirement(name, 0)),
                property.CaptureRequirements!);
            Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, property.Exposure);
        }

        // Base's two lists (W each) are materialized flat, the persistent bases are built from them
        // once, and every reader stores only its one-element difference, per list.
        Assert.Equal(2L * width, observations.RequiredAncestorListEntriesMaterialized);
        Assert.Equal(2, observations.RequiredAncestorPersistentBases);
        Assert.Equal(2L * properties, observations.RequiredAncestorListsDerived);
        Assert.Equal(2L * properties, observations.RequiredAncestorDerivedEntries);
    }

    /// <summary>
    /// Below the derivation threshold a set is materialized flat whatever its derivation: at the
    /// boundary a base of <see cref="RequiredAncestorOutputs.MinimumDerivationBase"/> − 1 inputs is
    /// never extended, while one of exactly that size is.
    /// </summary>
    [Theory]
    [InlineData(RequiredAncestorOutputs.MinimumDerivationBase - 1, false)]
    [InlineData(RequiredAncestorOutputs.MinimumDerivationBase, true)]
    [InlineData(RequiredAncestorOutputs.MinimumDerivationBase + 1, true)]
    public void DerivationThreshold_IsTheMinimumBaseSize(int width, bool derived)
    {
        var source = $"O({Names("v", width)}, x0, x1) = {{\n    Base = {Names("v", width)}\n    P0 = Base, x0\n    P1 = Base, x1\n    Base\n}}\n1";
        var observations = new FrontEndTraversalObservations();
        var owner = Member(Exposed(source, observations), "O").Value;

        Assert.Equal(Names("v", width).Split(", ").Append("x1").Order(StringComparer.Ordinal), Member(owner, "P1").RequiredAncestorParameters);
        Assert.Equal(derived ? 4 : 0, observations.RequiredAncestorListsDerived);
    }

    /// <summary>
    /// Empty, singleton, and small sets around every size up to the derivation threshold: content,
    /// order, and exposure are exact, an exported property carries the shared empty list, and equal
    /// sets share one list whatever their size.
    /// </summary>
    [Fact]
    public void EmptySingletonAndSmallSets_AreExactAndShared()
    {
        for (var width = 0; width <= RequiredAncestorOutputs.MinimumDerivationBase + 1; width++)
        {
            var parameters = width == 0 ? "z" : Names("v", width);
            var body = width == 0 ? "1" : Names("v", width);
            var root = SourceProvenance.ParseValid($"O({parameters}) = {{\n    Base = {body}\n    P = Base\n    Q = Base\n    Base\n}}\n1").Root;
            var owner = Member(root, "O").Value;
            var expected = width == 0 ? [] : Names("v", width).Split(", ").Order(StringComparer.Ordinal).ToArray();
            foreach (var name in new[] { "Base", "P", "Q" })
            {
                var property = Member(owner, name);
                Assert.Equal(expected, property.RequiredAncestorParameters);
                Assert.Equal(width == 0 ? PropertyExposure.Exported : PropertyExposure.LocalOnlyCapturedAncestorParameters, property.Exposure);
            }

            AssertSameBacking(Member(owner, "P").RequiredAncestorParameters, Member(owner, "Q").RequiredAncestorParameters);
            Assert.Empty(Member(root, "O").RequiredAncestorParameters);
        }
    }

    // ── Exact identity: owners, shadowing, ordering ───────────────────────────

    /// <summary>
    /// The SAME names at two owner levels are different requirements: a property reading Outer's
    /// <c>x</c> (through <c>B</c>) captures depth 1, one reading Middle's <c>x</c> captures depth 0, and
    /// one reading both captures BOTH — never collapsed by spelling. The public names lists are equal
    /// (names are all they say), and the evaluator's accessibility law resolves each capture from the
    /// property's own scope.
    /// </summary>
    [Fact]
    public void SameNamedParametersOfDifferentOwners_StayDifferentRequirements()
    {
        const string source = "Outer(x) = {\n    B = x\n    Middle(x) = {\n        XB = x\n        P = B\n        Q = XB\n        R = B + XB\n        P, Q, R\n    }\n    Middle(10)\n}\nOuter(1)";
        var root = SourceProvenance.ParseValid(source).Root;
        var middle = Member(root, "Outer", "Middle").Value;

        Assert.Equal([new CapturedParameterRequirement("x", 1)], Member(middle, "P").CaptureRequirements!);
        Assert.Equal([new CapturedParameterRequirement("x", 0)], Member(middle, "Q").CaptureRequirements!);
        Assert.Equal([new CapturedParameterRequirement("x", 0), new CapturedParameterRequirement("x", 1)], Member(middle, "R").CaptureRequirements!);
        Assert.All(["P", "Q", "R"], name => Assert.Equal(["x"], Member(middle, name).RequiredAncestorParameters));
        Assert.Equal("(1, 10, 11)", KatLangEngine.Run(source).ToDisplayString());
    }

    /// <summary>
    /// Two owners whose members capture same-named parameters at the same relative depth share one
    /// capture list by CONTENT (depths are owner-relative, so equal content is equal meaning), yet
    /// remain two declarations evaluated in their own activations.
    /// </summary>
    [Fact]
    public void EqualRelativeRequirementsOfDifferentOwners_ShareContentNotDeclarations()
    {
        const string source = "Outer1(x) = {\n    A = x\n    B = A\n    B\n}\nOuter2(x) = {\n    A = x\n    B = A\n    B * 10\n}\nOuter1(1), Outer2(2)";
        var root = SourceProvenance.ParseValid(source).Root;
        var first = Member(root, "Outer1", "B");
        var second = Member(root, "Outer2", "B");

        AssertSameBacking(first.CaptureRequirements, second.CaptureRequirements);
        AssertSameBacking(first.RequiredAncestorParameters, second.RequiredAncestorParameters);
        Assert.NotSame(Member(root, "Outer1").Value, Member(root, "Outer2").Value);
        Assert.Equal("1\n20", KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    /// <summary>The public names keep their established ORDINAL order (not declaration order, not natural numeric order).</summary>
    [Fact]
    public void RequiredNames_KeepOrdinalOrder()
    {
        var root = SourceProvenance.ParseValid($"O({Names("v", 12)}, Zeta, alpha) = {{\n    Base = alpha, Zeta, {Names("v", 12)}\n    P = Base\n    P\n}}\n1").Root;
        var names = Member(root, "O", "P").RequiredAncestorParameters;
        Assert.Equal(["Zeta", "alpha", "v0", "v1", "v10", "v11", "v2", "v3", "v4", "v5", "v6", "v7", "v8", "v9"], names);
        Assert.Equal(names.Order(StringComparer.Ordinal), names);

        // Unions of sets canonicalized in the order z…, a… (the requirement sets' own key order): the
        // public list is still ordinal, for a flat list (P: two equally wide halves) and for one
        // derived from a wide base (Q: Z plus one input).
        var union = SourceProvenance.ParseValid($"O({Names("a", 20)}, {Names("z", 20)}) = {{\n    Z = {Names("z", 20)}\n    A = {Names("a", 20)}\n    P = Z, A\n    Q = Z, a1\n    P, Q\n}}\n1").Root;
        var expected = Names("a", 20).Split(", ").Concat(Names("z", 20).Split(", ")).Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(expected, Member(union, "O", "P").RequiredAncestorParameters);
        Assert.Equal(expected.Select(name => new CapturedParameterRequirement(name, 0)), Member(union, "O", "P").CaptureRequirements!);
        var derived = Names("z", 20).Split(", ").Append("a1").Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(derived, Member(union, "O", "Q").RequiredAncestorParameters);
        Assert.Equal(derived.Select(name => new CapturedParameterRequirement(name, 0)), Member(union, "O", "Q").CaptureRequirements!);
    }

    /// <summary>
    /// Sharing by content is decided by EXACT element equality, never by the hash: under an element
    /// comparer whose every hash collides, lists of equal length and different content are still
    /// different (one differing final entry, or the same elements in another order), while equal
    /// contents built separately are equal.
    /// </summary>
    [Fact]
    public void ContentSharing_ProvesEqualityElementByElement()
    {
        var colliding = EqualityComparer<string>.Create(StringComparer.Ordinal.Equals, _ => 0);
        var comparer = new RequiredAncestorOutputs.ExactSequenceComparer<string>(colliding);
        string[] names = ["a", "b", "c"];
        Assert.True(comparer.Equals(names, ["a", "b", "c"]));
        Assert.Equal(comparer.GetHashCode(names), comparer.GetHashCode(["a", "b", "d"]));
        Assert.False(comparer.Equals(names, ["a", "b", "d"]));
        Assert.False(comparer.Equals(names, ["c", "b", "a"]));
        Assert.False(comparer.Equals(names, ["a", "b"]));

        var collidingCaptures = EqualityComparer<CapturedParameterRequirement>.Create((x, y) => x.Equals(y), _ => 0);
        var captures = new RequiredAncestorOutputs.ExactSequenceComparer<CapturedParameterRequirement>(collidingCaptures);
        CapturedParameterRequirement[] outer = [new("x", 1)];
        Assert.False(captures.Equals(outer, [new("x", 0)]));
        Assert.True(captures.Equals(outer, [new("x", 1)]));
    }

    // ── Immutability, retention, and concurrency ──────────────────────────────

    /// <summary>
    /// A list shared by K properties cannot be changed through any of them: it is not a mutable array
    /// or list, and every mutating interface route throws. The same holds for derived persistent lists.
    /// </summary>
    [Fact]
    public void SharedLists_HaveNoMutationRoute()
    {
        var source = $"O({Names("v", 20)}, x0) = {{\n    Base = {Names("v", 20)}\n    P = Base\n    Q = Base, x0\n    Base\n}}\n1";
        var owner = Member(SourceProvenance.ParseValid(source).Root, "O").Value;
        foreach (var name in new[] { "P", "Q" })
        {
            var names = Member(owner, name).RequiredAncestorParameters;
            var before = names.ToArray();
            Assert.False(names is string[] or List<string>);
            if (names is IList<string> list)
            {
                Assert.True(list.IsReadOnly);
                Assert.Throws<NotSupportedException>(() => list[0] = "hijacked");
                Assert.Throws<NotSupportedException>(() => list.Add("hijacked"));
                Assert.Throws<NotSupportedException>(() => list.RemoveAt(0));
                Assert.Throws<NotSupportedException>(list.Clear);
            }

            if (names is ISet<string> set)
                Assert.Throws<NotSupportedException>(() => set.Add("hijacked"));

            Assert.Equal(before, names);
            var captures = Member(owner, name).CaptureRequirements!;
            Assert.False(captures is CapturedParameterRequirement[] or List<CapturedParameterRequirement>);
        }

        AssertSameBacking(Member(owner, "Base").RequiredAncestorParameters, Member(owner, "P").RequiredAncestorParameters);
    }

    /// <summary>
    /// A retained list references nothing but its elements: no requirement set, interner, summary
    /// scope, lexical scope, or AST node is reachable from it, so retaining a parse result never
    /// retains the analysis that built its lists. Two parses build independent lists (no process-wide
    /// cache shares lists across runs).
    /// </summary>
    [Fact]
    public void RetainedLists_ReachNoAnalysisState_AndAreNotSharedAcrossRuns()
    {
        var source = $"O({Names("v", 24)}, x0) = {{\n    Base = {Names("v", 24)}\n    P = Base\n    Q = Base, x0\n    Base\n}}\n1";
        var first = Member(SourceProvenance.ParseValid(source).Root, "O").Value;
        foreach (var property in first.Properties)
        {
            AssertReachesOnlyValues(property.RequiredAncestorParameters);
            AssertReachesOnlyValues(property.CaptureRequirements!);
        }

        var second = Member(SourceProvenance.ParseValid(source).Root, "O").Value;
        Assert.NotSame(Member(first, "P").RequiredAncestorParameters, Member(second, "P").RequiredAncestorParameters);
        Assert.Equal(Member(first, "Q").RequiredAncestorParameters, Member(second, "Q").RequiredAncestorParameters);
    }

    private static void AssertReachesOnlyValues(object list)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(list);
        while (pending.TryPop(out var node))
        {
            var type = node.GetType();
            if (type == typeof(string) || type.IsPrimitive || !seen.Add(node))
                continue;
            if (node is Array array)
            {
                foreach (var element in array)
                    if (element is not null) pending.Push(element);
                continue;
            }

            Assert.False(type.Assembly == typeof(Property).Assembly && type != typeof(CapturedParameterRequirement) && !(type.IsGenericType && type.GetGenericTypeDefinition() == typeof(RequiredAncestorList<>)),
                $"A retained requirement list reaches {type.FullName}.");

            for (var current = type; current is not null; current = current.BaseType)
            {
                foreach (var field in current.GetFields(System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.DeclaredOnly))
                {
                    if (field.GetValue(node) is { } value && !field.FieldType.IsPointer)
                        pending.Push(value);
                }
            }
        }
    }

    /// <summary>Many threads reading one shared list observe identical contents in identical order.</summary>
    [Fact]
    public void SharedList_ReadConcurrently_IsStable()
    {
        var owner = Member(SourceProvenance.ParseValid(Canonical(64, 200)).Root, "O").Value;
        var shared = Member(owner, "P7").RequiredAncestorParameters;
        var expected = shared.ToArray();
        var failures = new ConcurrentBag<string>();
        Parallel.For(0, 32, new ParallelOptions { MaxDegreeOfParallelism = 16 }, worker =>
        {
            for (var round = 0; round < 200; round++)
            {
                var property = owner.Properties[(worker + round) % owner.Properties.Count];
                var list = property.RequiredAncestorParameters;
                if (!ReferenceEquals(Backing(list), Backing(shared)) || !list.SequenceEqual(expected) || list[round % list.Count] != expected[round % expected.Length])
                    failures.Add($"{worker}/{round}");
            }
        });
        Assert.Empty(failures);
    }

    // ── Fixed-point safety ────────────────────────────────────────────────────

    /// <summary>
    /// A property reading an OPENED member whose own requirement arrives through a sibling declared
    /// later: its settlement first sees that sibling's summary still empty, and must be recomputed
    /// once the sibling's summary grows — a settlement cached before the fixed point is final would
    /// classify <c>P</c> exported and hand every activation the first one's value.
    /// </summary>
    [Fact]
    public void SettlementReadingALaterSibling_IsRecomputedWhenTheSiblingGrows()
    {
        const string source = "O(x) = {\n    open L\n    P = V\n    L = {\n        public V = Q\n        1\n    }\n    Q = x\n    P\n}\nO(1), O(2)";
        var owner = Member(SourceProvenance.ParseValid(source).Root, "O").Value;

        Assert.Equal(["x"], Member(owner, "P").RequiredAncestorParameters);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, Member(owner, "P").Exposure);
        Assert.Equal("1\n2", KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    /// <summary>
    /// A requirement set that grows AFTER its first sharing — P shares Base's early summary, then Base
    /// grows once the sibling its opened member reads (<c>Late</c>, a read no static edge announces)
    /// is solved — is re-shared, never left at the early set.
    /// </summary>
    [Fact]
    public void ReaderOfAGrowingSummary_FollowsItToTheFixedPoint()
    {
        const string source = "O(x, y) = {\n    open L\n    P = Base\n    Base = x, V\n    L = {\n        public V = Late\n        1\n    }\n    Late = y\n    P\n}\nO(1, 2)";
        var owner = Member(SourceProvenance.ParseValid(source).Root, "O").Value;
        Assert.Equal(["x", "y"], Member(owner, "P").RequiredAncestorParameters);
        AssertSameBacking(Member(owner, "Base").RequiredAncestorParameters, Member(owner, "P").RequiredAncestorParameters);
        Assert.Equal("(1, 2)", KatLangEngine.Run(source).ToDisplayString());
    }

    /// <summary>
    /// The summary channel's twin of the stale-settlement hazard: inside block <c>O</c>, member <c>A</c>
    /// reads an opened member whose requirement arrives through <c>Late</c>, solved after <c>A</c>. A
    /// reused expansion of <c>A</c> must be validated against the member seeds it read, or <c>O</c>'s
    /// value would lose Outer's <c>y</c>: <c>O</c> would be classified exported and the run-scoped cache
    /// would hand the first activation's value to the second call.
    /// </summary>
    [Fact]
    public void MemberExpansionReadingALaterMember_IsRecomputedWhenTheMemberGrows()
    {
        const string source = "Outer(y) = {\n    O = {\n        open L\n        A = V\n        L = {\n            public V = Late\n            1\n        }\n        Late = y\n        A\n    }\n    O\n}\nOuter(5), Outer(6)";
        var root = SourceProvenance.ParseValid(source).Root;
        Assert.Equal(["y"], Member(root, "Outer", "O").RequiredAncestorParameters);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, Member(root, "Outer", "O").Exposure);
        Assert.Equal("5\n6", KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    /// <summary>
    /// Several declarations of one name keep the former last-write-wins map: every same-named
    /// declaration, and every reader of the name, receives the LAST declaration's summary.
    /// </summary>
    [Fact]
    public void SameNamedDeclarations_ShareTheLastDeclarationsSummary()
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics("O(x, y) = {\n    A = x\n    A = y\n    R = A\n    R\n}\n1");
        Assert.True(parsed.HasFrontEndErrors);
        var owner = Member(parsed.Root, "O").Value;
        Assert.All(owner.Properties.Where(p => p.Name == "A"), property => Assert.Equal(["y"], property.RequiredAncestorParameters));
        Assert.Equal(["y"], Member(owner, "R").RequiredAncestorParameters);
    }

    // ── Modules and deferred regions ──────────────────────────────────────────

    private const string ModuleUrl = "https://katlang.org/fe4a/lib.kat";

    private static RunOptions ModuleOptions(string moduleSource, Action? onDownload = null)
        => new()
        {
            DownloadCode = (url, _) =>
            {
                onDownload?.Invoke();
                return url == ModuleUrl ? ValueTask.FromResult(moduleSource) : throw new InvalidOperationException($"404: {url}");
            },
        };

    /// <summary>
    /// One module imported in two importer contexts is classified in each (its owners are different
    /// scopes there), and its members' lists are equal in content — and, having equal content, shared.
    /// </summary>
    [Fact]
    public async Task ModuleImportedInTwoContexts_HasEqualListsInEach()
    {
        const string module = "public Model(a, b) = {\n    Base = a + b\n    P1 = Base\n    P2 = Base\n    public R = P2 + a\n    R\n}";
        const string source = $"P = {{\n    open '{ModuleUrl}'\n    Model(1, 2)\n}}\nQ(k) = {{\n    open '{ModuleUrl}'\n    Model(k, k)\n}}\nP + Q(5)";
        var root = (await SourceProvenance.ParseValidAsync(source, ModuleOptions(module))).Root;

        Algorithm Model(string importer)
        {
            var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(Member(root, importer).Value.Opens));
            return Member(block.Algorithm, "Model").Value;
        }

        var inP = Model("P");
        var inQ = Model("Q");
        foreach (var name in new[] { "Base", "P1", "P2", "R" })
        {
            Assert.Equal(["a", "b"], Member(inP, name).RequiredAncestorParameters);
            Assert.Equal([new CapturedParameterRequirement("a", 0), new CapturedParameterRequirement("b", 0)], Member(inQ, name).CaptureRequirements!);
            AssertSameBacking(Member(inP, name).RequiredAncestorParameters, Member(inQ, name).RequiredAncestorParameters);
        }

        Assert.Equal("19", (await KatLangEngine.RunAsync(source, ModuleOptions(module))).ToDisplayString());
    }

    /// <summary>
    /// A deferred module region is classified only when evaluation selects it: the unselected branch
    /// downloads and materializes nothing. Selected, its demand-time run reads the EAGER run's summary
    /// of the enclosing <c>Base</c> (another interner's set, adopted by its elements), and every one of
    /// its K readers holds one shared list with the depth the branch body's chain gives the owner.
    /// </summary>
    [Fact]
    public async Task DeferredRegion_IsClassifiedOnlyWhenSelected_AgainstTheEagerSummaries()
    {
        const int width = 20;
        const int readers = 12;
        var downloads = 0;
        var options = ModuleOptions("public Two = 2", () => Interlocked.Increment(ref downloads));
        string Program(int selected)
            => $"Outer({Names("v", width)}) = {{\n    Base = {Names("v", width, " + ")}\n    F(0) = {{\n        open '{ModuleUrl}'\n"
                + string.Concat(Enumerable.Range(0, readers).Select(i => $"        P{i} = Base\n"))
                + $"        P{readers - 1} + Two\n    }}\n    F(n) = n\n    F({selected})\n}}\nOuter({Arguments(width)})";

        var unselected = await SourceProvenance.ParseValidAsync(Program(1), options);
        var unselectedRegion = Assert.IsType<Algorithm.Conditional>(Member(unselected.Root, "Outer", "F").Value).Branches[0].Body.DeferredRegion!;
        var run = await Evaluator.RunCountedAsync(new Expr.AlgorithmExpr(unselected.Root), new AsyncEvaluation.PassThroughAsyncZeroArgPropertyResultCache());
        Assert.False(run.IsError);
        Assert.Equal([1m], run.Value.Value.ToAtoms());
        Assert.False(unselectedRegion.IsMaterialized);
        Assert.Equal(0, downloads);

        var selected = await SourceProvenance.ParseValidAsync(Program(0), options);
        var region = Assert.IsType<Algorithm.Conditional>(Member(selected.Root, "Outer", "F").Value).Branches[0].Body.DeferredRegion!;
        var materialized = await region.MaterializeAsync(CancellationToken.None);
        Assert.False(materialized.IsError);
        var body = materialized.Value;
        Assert.Same(body, (await region.MaterializeAsync(CancellationToken.None)).Value);
        var expected = Names("v", width).Split(", ").Order(StringComparer.Ordinal).ToArray();
        var shared = Member(body, "P0").RequiredAncestorParameters;
        Assert.Equal(expected, shared);
        for (var i = 0; i < readers; i++)
        {
            var property = Member(body, $"P{i}");
            AssertSameBacking(shared, property.RequiredAncestorParameters);
            Assert.Equal(expected.Select(name => new CapturedParameterRequirement(name, 2)), property.CaptureRequirements!);
        }

        Assert.Equal(1, downloads);
        Assert.Equal("212", (await KatLangEngine.RunAsync(Program(0), options)).ToDisplayString());
        var independent = await SourceProvenance.ParseValidAsync(Program(0), options);
        var independentRegion = Assert.IsType<Algorithm.Conditional>(Member(independent.Root, "Outer", "F").Value).Branches[0].Body.DeferredRegion!;
        var independentBody = (await independentRegion.MaterializeAsync(CancellationToken.None)).Value;
        Assert.Equal(shared, Member(independentBody, "P0").RequiredAncestorParameters);
        Assert.NotSame(Backing(shared), Backing(Member(independentBody, "P0").RequiredAncestorParameters));
    }

    // ── Independent oracle over generated dependency graphs ───────────────────

    /// <summary>
    /// Random owner-with-nested-owner programs — chains, diamonds, shared dependencies, cycles,
    /// partial overlaps, and same-named parameters at both owner levels — checked against a slow,
    /// independent recomputation of the relation with plain sets and naive round-by-round iteration:
    /// the exposure, the sorted required names, and the name-then-depth captures of every property.
    /// </summary>
    [Fact]
    public void GeneratedDependencyGraphs_MatchTheSlowOracle()
    {
        var random = new Random(4_000_2026);
        for (var program = 0; program < 250; program++)
        {
            var generated = GenerateProgram(random);
            var root = SourceProvenance.ParseValid(generated.Source).Root;
            var expected = Oracle(generated);
            var outer = Member(root, "O").Value;
            foreach (var (path, requirements) in expected)
            {
                var property = path.Length == 1 ? Member(outer, path[0]) : Member(outer, path[0], path[1]);
                var names = requirements.Select(r => r.Name).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
                var declaredInMiddle = path.Length == 2;
                var captures = requirements
                    .Select(r => new CapturedParameterRequirement(r.Name, declaredInMiddle && r.Owner == "O" ? 1 : 0))
                    .OrderBy(c => c.Name, StringComparer.Ordinal).ThenBy(c => c.OwnerDepth).ToArray();
                var context = $"program {program}, property {string.Join('.', path)}:\n{generated.Source}";
                Assert.True(names.SequenceEqual(property.RequiredAncestorParameters), context);
                Assert.True(captures.SequenceEqual(property.CaptureRequirements!), context);
                Assert.True((requirements.Count > 0) == (property.Exposure == PropertyExposure.LocalOnlyCapturedAncestorParameters), context);
            }
        }
    }

    private sealed record GeneratedProperty(string Name, string[] Parameters, string[] Properties);

    private sealed record GeneratedProgram(
        string Source,
        string[] OuterParameters,
        GeneratedProperty[] OuterProperties,
        string[] MiddleParameters,
        GeneratedProperty[] MiddleProperties,
        string[] MiddleOutput);

    private static GeneratedProgram GenerateProgram(Random random)
    {
        var outerParameters = Enumerable.Range(0, random.Next(1, 6)).Select(i => $"x{i}").ToArray();
        // Middle binds some of the SAME names (shadowing) and some of its own.
        var middleParameters = outerParameters.Where(_ => random.Next(3) == 0).Concat(Enumerable.Range(0, random.Next(0, 3)).Select(i => $"y{i}")).ToArray();
        if (middleParameters.Length == 0)
            middleParameters = ["y0"];

        var outerCount = random.Next(1, 8);
        var outer = Enumerable.Range(0, outerCount).Select(i => new GeneratedProperty(
            $"P{i}",
            Pick(random, outerParameters, 3),
            Pick(random, Enumerable.Range(0, outerCount).Select(j => $"P{j}").ToArray(), 3))).ToArray();
        var middleCount = random.Next(1, 7);
        var visibleToMiddle = middleParameters.Union(outerParameters).ToArray();
        var middle = Enumerable.Range(0, middleCount).Select(i => new GeneratedProperty(
            $"Q{i}",
            Pick(random, visibleToMiddle, 3),
            Pick(random, Enumerable.Range(0, middleCount).Select(j => $"Q{j}").Concat(outer.Select(p => p.Name)).ToArray(), 3))).ToArray();
        var middleOutput = Pick(random, middle.Select(q => q.Name).ToArray(), 2);

        static string Row(GeneratedProperty property)
        {
            var items = property.Parameters.Concat(property.Properties).ToArray();
            return items.Length == 0 ? "1" : string.Join(", ", items);
        }

        var source = new System.Text.StringBuilder();
        source.Append("O(").Append(string.Join(", ", outerParameters)).Append(") = {\n");
        foreach (var property in outer)
            source.Append("    ").Append(property.Name).Append(" = ").Append(Row(property)).Append('\n');
        source.Append("    M(").Append(string.Join(", ", middleParameters)).Append(") = {\n");
        foreach (var property in middle)
            source.Append("        ").Append(property.Name).Append(" = ").Append(Row(property)).Append('\n');
        source.Append("        ").Append(middleOutput.Length == 0 ? "1" : string.Join(", ", middleOutput)).Append("\n    }\n    1\n}\n1");
        return new GeneratedProgram(source.ToString(), outerParameters, outer, middleParameters, middle, middleOutput);
    }

    private static string[] Pick(Random random, string[] from, int max)
        => from.Length == 0 ? [] : from.OrderBy(_ => random.Next()).Take(random.Next(0, Math.Min(max, from.Length) + 1)).ToArray();

    /// <summary>
    /// The slow reference: requirements are (name, owner) pairs — "O" or "M" — with the nearest owner
    /// binding each written parameter; a property requires its own parameters plus everything the
    /// properties it reads require, iterated round by round with plain sets until nothing changes; M's
    /// value requires what its output rows require minus what M itself binds.
    /// </summary>
    private static Dictionary<string[], HashSet<(string Name, string Owner)>> Oracle(GeneratedProgram program)
    {
        var outer = program.OuterProperties.ToDictionary(p => p.Name, _ => new HashSet<(string, string)>());
        var middle = program.MiddleProperties.ToDictionary(p => p.Name, _ => new HashSet<(string, string)>());
        var middleValue = new HashSet<(string, string)>();
        bool changed;
        do
        {
            changed = false;
            foreach (var property in program.OuterProperties)
            {
                var next = new HashSet<(string, string)>(property.Parameters.Select(name => (name, "O")));
                foreach (var read in property.Properties)
                    next.UnionWith(outer[read]);
                changed |= !next.SetEquals(outer[property.Name]);
                outer[property.Name] = next;
            }

            foreach (var property in program.MiddleProperties)
            {
                var next = new HashSet<(string, string)>(property.Parameters.Select(name => (name, program.MiddleParameters.Contains(name) ? "M" : "O")));
                foreach (var read in property.Properties)
                    next.UnionWith(read.StartsWith('Q') ? middle[read] : outer[read]);
                changed |= !next.SetEquals(middle[property.Name]);
                middle[property.Name] = next;
            }

            var value = new HashSet<(string, string)>(program.MiddleOutput.SelectMany(read => middle[read]).Where(r => r.Item2 != "M"));
            changed |= !value.SetEquals(middleValue);
            middleValue = value;
        }
        while (changed);

        var expected = new Dictionary<string[], HashSet<(string Name, string Owner)>>();
        foreach (var (name, requirements) in outer)
            expected.Add([name], requirements);
        foreach (var (name, requirements) in middle)
            expected.Add(["M", name], requirements);
        expected.Add(["M"], middleValue);
        return expected;
    }
}
