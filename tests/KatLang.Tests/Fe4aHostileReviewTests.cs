using System.Collections;
using System.Reflection;
using Requirement = KatLang.PropertyExposureResolver.Requirement;

namespace KatLang.Tests;

public class Fe4aHostileReviewTests
{
    [Fact]
    public void CaptureWrappers_PreserveRecordEqualityAndSharedBacking()
    {
        var root = SourceProvenance.ParseValid("O(x) = {\nP = x\nQ = x\n1\n}\n1").Root;
        var properties = Assert.IsType<Algorithm.User>(root.Properties.Single().Value).Properties;
        var p = properties[0];
        var q = p with { CaptureRequirements = properties[1].CaptureRequirements };
        Assert.False(p == q);
        Assert.True(p == (p with { }));
        Assert.Equal(p.GetHashCode(), (p with { }).GetHashCode());
        Assert.Same(Assert.IsType<RequiredAncestorList<CapturedParameterRequirement>>(p.CaptureRequirements).Backing,
            Assert.IsType<RequiredAncestorList<CapturedParameterRequirement>>(q.CaptureRequirements).Backing);
    }

    [Fact]
    public void RepeatedOpenCondition_PreservesAmbiguityShadowingAndBoundOwners()
    {
        var owner = new Algorithm.User(null, [new CaptureParameterPattern(new ParameterDeclaration("x"))], [], [], OutputBundle.Empty);
        var captured = new PropertyDependencyGraphBuilder.SummarySeed(ownerQualifiedParameters: [new("x", owner)]);
        PendingReference Lookup(string head, OpenCandidate[] candidates, bool bound = false)
            => new(head, [], candidates, bound ? [owner] : []);
        var single = Lookup("V", [new ResolvedOpenCandidate(captured, 0)]);
        var ambiguous = Lookup("V", [new ResolvedOpenCandidate(captured, 0), new ResolvedOpenCandidate(captured, 0)]);
        var unresolved = Lookup("V", [new UnresolvedOpenCandidate("L", [], 0), new ResolvedOpenCandidate(captured, 1)]);
        PropertyDependencyGraphBuilder.SummarySeed Reduce(PendingReference pending)
            => new PropertyDependencyGraphBuilder.SummarySeed(pendingReferences: [pending]).UnderMissingLexicalHead("V");
        Assert.Empty(Reduce(single).PendingReferences);
        Assert.Equal([new OwnerQualifiedParameter("x", owner)], Reduce(single).OwnerQualifiedParameters);
        Assert.True(Reduce(ambiguous).IsEmpty);
        Assert.Single(Reduce(unresolved).PendingReferences);
        Assert.Single(Reduce(Lookup("Other", [new ResolvedOpenCandidate(captured, 0)])).PendingReferences);
        Assert.True(Reduce(Lookup("V", [new ResolvedOpenCandidate(captured, 0)], bound: true)).IsEmpty);
        // Reduction is conditional: it never changes the original seed that lexical shadowing may select instead.
        Assert.Single(single.Candidates);
        Assert.Single(captured.OwnerQualifiedParameters);
    }

    private sealed record Element(int Value);

    [Fact]
    public void AwkwardNames_UseOrdinalOrderForNamesAndCaptures()
    {
        var root = SourceProvenance.ParseValid("O(ā, a2, a10, a1, a, A) = {\nP = ā, a2, a10, a1, a, A\nP\n}\n1").Root;
        var property = Assert.IsType<Algorithm.User>(root.Properties.Single().Value).Properties.Single();
        string[] expected = ["A", "a", "a1", "a10", "a2", "ā"];
        Assert.Equal(expected, property.RequiredAncestorParameters);
        Assert.Equal(expected.Select(n => new CapturedParameterRequirement(n, 0)), property.CaptureRequirements!);
    }
    private sealed class TestInterner<T>(IEqualityComparer<T> comparer) : CanonicalSetInterner<T>(comparer) where T : notnull
    {
        internal Node? From(IEnumerable<T> elements) => WithElements(null, elements);
        internal Node? Union(Node? a, Node? b) => UnionRoots(a, b);
        internal Node? Except(Node? a, Node? b) => ExceptRoots(a, b);
        internal bool Contains(Node? a, T element) => ContainsElement(a, element);
    }

    [Fact]
    public void GenericInterner_UsesExactSuppliedComparerUnderCollisions()
    {
        var objects = Enumerable.Range(0, 40).Select(i => new Element(i / 2)).ToArray();
        foreach (var identity in new[] { false, true })
        {
            var comparer = EqualityComparer<Element>.Create(
                (a, b) => identity ? ReferenceEquals(a, b) : a == b, _ => 0);
            var interner = new TestInterner<Element>(comparer);
            var all = interner.From(objects);
            Assert.Equal(identity ? 40 : 20, all!.Count);
            Assert.Same(all, interner.From(objects.Reverse().Concat(objects)));
            Assert.True(interner.Contains(all, objects[0]));
            Assert.Equal(!identity, interner.Contains(all, new Element(0)));
            var random = new Random(401);
            for (var i = 0; i < 100; i++)
            {
                var a = objects.Where(_ => random.Next(2) == 0).ToHashSet(comparer);
                var b = objects.Where(_ => random.Next(2) == 0).ToHashSet(comparer);
                var left = interner.From(a);
                var right = interner.From(b);
                Assert.Same(interner.From(a.Union(b, comparer)), interner.Union(left, right));
                Assert.Same(interner.From(a.Except(b, comparer)), interner.Except(left, right));
                Assert.Same(left, interner.Union(left, left));
                Assert.Null(interner.Except(left, left));
            }
        }
    }

    [Fact]
    public void ForeignSets_AreAdoptedByElements_AndCaptureDepthsArePartOfTheKey()
    {
        var owner = ElaboratedScopeLookup.CreateScope(new Algorithm.User(null, [], [], [], OutputBundle.Empty));
        var first = new RequirementSetInterner(null);
        var set = first.From([new Requirement("x", owner)]);
        var second = new RequirementSetInterner(null);
        _ = second.From([new Requirement("other", null)]); // Deliberately collide dense keys across runs.
        var adopted = second.Adopt(set);
        Assert.NotSame(set.Root, adopted.Root);
        Assert.Same(adopted.Root, second.From(set.Elements).Root);
        var outputs = new RequiredAncestorOutputs(second, null);
        Assert.Equal([new CapturedParameterRequirement("x", 0)], outputs.Captures(adopted, _ => 0));
        Assert.Equal([new CapturedParameterRequirement("x", 2)], outputs.Captures(adopted, _ => 2));
        Assert.NotSame(outputs.Captures(adopted, _ => 0), outputs.Captures(adopted, _ => 2));
    }

    [Theory]
    [InlineData(15, 0)] [InlineData(15, 1)] [InlineData(15, 3)] [InlineData(15, 4)]
    [InlineData(16, 0)] [InlineData(16, 1)] [InlineData(16, 4)] [InlineData(16, 5)]
    [InlineData(17, 0)] [InlineData(17, 1)] [InlineData(17, 4)] [InlineData(17, 5)]
    public void ProjectionThresholds_PreserveAllCollectionOperations(int width, int delta)
    {
        var sets = new RequirementSetInterner(null);
        var outputs = new RequiredAncestorOutputs(sets, null);
        var source = Enumerable.Range(0, width).Select(i => $"z{i}").ToArray();
        var added = Enumerable.Range(0, delta).Select(i => $"A{i}").ToArray();
        var set = sets.Union(sets.From(source.Select(n => new Requirement(n, null))), sets.From(added.Select(n => new Requirement(n, null))));
        var names = outputs.Names(set);
        var captures = outputs.Captures(set, _ => 1);
        var expected = source.Concat(added).Order(StringComparer.Ordinal).ToArray();
        Check(names, expected);
        Check(captures, expected.Select(n => new CapturedParameterRequirement(n, 1)).ToArray());
    }

    private static void Check<T>(IReadOnlyList<T> values, T[] expected)
    {
        Assert.Equal(expected.Length, values.Count);
        Assert.Equal(expected, values);
        for (var i = 0; i < values.Count; i++) Assert.Equal(expected[i], values[i]);
        if (values is ICollection<T> collection)
        {
            var copy = new T[values.Count + 1];
            collection.CopyTo(copy, 1);
            Assert.Equal(expected, copy.Skip(1));
            Assert.True(collection.Contains(expected[0]));
            Assert.Throws<NotSupportedException>(() => collection.Add(expected[0]));
            Assert.Throws<NotSupportedException>(() => collection.Remove(expected[0]));
            Assert.Throws<NotSupportedException>(collection.Clear);
        }
        if (values is IList<T> list)
        {
            Assert.Throws<NotSupportedException>(() => list[0] = expected[0]);
            Assert.Throws<NotSupportedException>(() => list.Insert(0, expected[0]));
            Assert.Throws<NotSupportedException>(() => list.RemoveAt(0));
        }
        if (values is IList untyped)
        {
            Assert.Throws<NotSupportedException>(() => untyped[0] = expected[0]);
            Assert.Throws<NotSupportedException>(() => untyped.Add(expected[0]));
            Assert.Throws<NotSupportedException>(() => untyped.Remove(expected[0]));
            Assert.Throws<NotSupportedException>(() => untyped.Insert(0, expected[0]));
            Assert.Throws<NotSupportedException>(() => untyped.RemoveAt(0));
            Assert.Throws<NotSupportedException>(untyped.Clear);
        }
    }

    [Fact]
    public void RetainedProjection_DoesNotRetainInterner()
    {
        var (weak, list) = MakeRetainedProjection();
        for (var i = 0; i < 3; i++) { GC.Collect(); GC.WaitForPendingFinalizers(); GC.Collect(); }
        Assert.False(weak.IsAlive);
        Assert.Equal(32, list.Count);
        GC.KeepAlive(list);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static (WeakReference, IReadOnlyList<string>) MakeRetainedProjection()
    {
        var sets = new RequirementSetInterner(null);
        var outputs = new RequiredAncestorOutputs(sets, null);
        var list = outputs.Names(sets.From(Enumerable.Range(0, 32).Select(i => new Requirement($"x{i}", null))));
        return (new WeakReference(sets), RequiredAncestorList<string>.ForProperty(list));
    }

    [Fact]
    public void GeneratedOpenedAndNavigatedCycles_MatchIndependentOracleInBothOrders()
    {
        var random = new Random(4042026);
        for (var sample = 0; sample < 100; sample++)
        {
            const int n = 5;
            var reads = Enumerable.Range(0, n).Select(_ => Enumerable.Range(0, n).Where(_ => random.Next(3) == 0).ToArray()).ToArray();
            var inputs = Enumerable.Range(0, n).Select(_ => Enumerable.Range(0, 3).Where(_ => random.Next(3) == 0).ToArray()).ToArray();
            foreach (var shadow in new[] { false, true })
            {
                var expected = Enumerable.Range(0, n).Select(i => inputs[i].Select(p => $"x{p}").ToHashSet(StringComparer.Ordinal)).ToArray();
                bool changed;
                do
                {
                    var next = expected.Select(s => new HashSet<string>(s, StringComparer.Ordinal)).ToArray();
                    for (var i = 0; i < n; i++) foreach (var dep in reads[i]) if (!shadow || (i + dep) % 2 == 0) next[i].UnionWith(expected[dep]);
                    changed = Enumerable.Range(0, n).Any(i => !next[i].SetEquals(expected[i]));
                    expected = next;
                } while (changed);
                foreach (var reverse in new[] { false, true })
                {
                    var declarations = Enumerable.Range(0, n).SelectMany(i => new[]
                    {
                        $"L{i} = {{ public V = P{i}\n1 }}",
                        $"P{i} = " + string.Join(", ", inputs[i].Select(p => $"x{p}").Concat(reads[i].Select(j =>
                            (i + j) % 2 == 0 ? $"L{j}.V" : $"{{ open L{j}\nV }}")).DefaultIfEmpty("1"))
                    }).ToArray();
                    if (reverse) Array.Reverse(declarations);
                    var source = (shadow ? "V = 7\n" : "") + "O(x0, x1, x2) = {\n" + string.Join("\n", declarations) + "\n1\n}\n1";
                    var root = SourceProvenance.ParseValid(source).Root;
                    var owner = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "O").Value);
                    for (var i = 0; i < n; i++)
                    {
                        var property = owner.Properties.Single(p => p.Name == $"P{i}");
                        Assert.True(expected[i].Order(StringComparer.Ordinal).SequenceEqual(property.RequiredAncestorParameters), source);
                        Assert.Equal(expected[i].Order(StringComparer.Ordinal).Select(name => new CapturedParameterRequirement(name, 0)), property.CaptureRequirements!);
                    }
                }
            }
        }
    }

    [Fact]
    public void UnionOfTwoLargeBasesAndSmallVariants_RetainsSharedStructure()
    {
        const int width = 64, count = 96;
        var sets = new RequirementSetInterner(null);
        var observations = new FrontEndTraversalObservations();
        var outputs = new RequiredAncestorOutputs(sets, observations);
        var left = sets.From(Enumerable.Range(0, width).Select(i => new Requirement($"a{i}", null)));
        var right = sets.From(Enumerable.Range(0, width).Select(i => new Requirement($"z{i}", null)));
        var lists = new List<object>();
        for (var i = 0; i < count; i++)
        {
            var variant = sets.Union(left, sets.From([new Requirement($"x{i}", null)]));
            var combined = sets.Union(variant, right);
            var names = outputs.Names(combined);
            var captures = outputs.Captures(combined, _ => -1);
            Assert.Equal(left.Elements.Concat(right.Elements).Select(r => r.Name).Append($"x{i}").Order(StringComparer.Ordinal), names);
            Assert.Equal(names.Select(n => new CapturedParameterRequirement(n, -1)), captures);
            lists.Add(names);
            lists.Add(captures);
        }
        Assert.InRange(observations.RequiredAncestorListEntriesMaterialized, 0, 4 * width);
        Assert.InRange(PhysicalEntries(lists), 1, 2 * (2 * width + count * 20));
    }

    [Fact]
    public void SourceCombiningLargeBasesWithVariants_RetainsDeltas()
    {
        const int width = 64, count = 96;
        string Names(string prefix, int n) => string.Join(", ", Enumerable.Range(0, n).Select(i => prefix + i));
        var source = $"O({Names("a", width)}, {Names("z", width)}, {Names("x", count)}) = {{\nA = {Names("a", width)}\nZ = {Names("z", width)}\n"
            + string.Concat(Enumerable.Range(0, count).Select(i => $"L{i} = A, x{i}\nP{i} = L{i}, Z\n")) + "1\n}\n1";
        var owner = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid(source).Root.Properties.Single().Value);
        var properties = owner.Properties.Where(p => p.Name.StartsWith('P')).ToArray();
        Assert.All(properties, p => Assert.Equal(2 * width + 1, p.RequiredAncestorParameters.Count));
        Assert.InRange(PhysicalEntries(properties.SelectMany(p => new object[] { p.RequiredAncestorParameters, p.CaptureRequirements! })),
            1, 2 * (2 * width + count * 20));
    }

    // Count actual arrays and persistent element-bearing nodes, deduplicating by object identity.
    internal static long PhysicalEntries(IEnumerable<object> roots)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>(roots);
        long entries = 0;
        while (pending.TryPop(out var current))
        {
            if (current is string || current.GetType().IsValueType || !seen.Add(current)) continue;
            if (current is Array array)
            {
                if (array is string[] or CapturedParameterRequirement[]) entries += array.Length;
                else foreach (var item in array) if (item is not null) pending.Push(item);
                continue;
            }
            if (current is IComparer<string> or IEqualityComparer<string>) continue;
            foreach (var field in current.GetType().GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic))
            {
                var value = field.GetValue(current);
                if (value is string or CapturedParameterRequirement) entries++;
                else if (value is not null && !value.GetType().IsValueType) pending.Push(value);
            }
        }
        return entries;
    }
}
