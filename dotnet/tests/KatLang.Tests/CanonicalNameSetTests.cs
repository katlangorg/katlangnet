namespace KatLang.Tests;

/// <summary>
/// <see cref="NameSetInterner"/> (FE-1): a canonical name set is the SAME node — and carries the same
/// id — for equal content, whatever order or grouping built it, and distinct content never shares an
/// id. That exactness is what lets the front end's semantic-region memos key a wide context by one
/// integer without turning content identity into derivation identity or a probabilistic hash.
/// </summary>
public class CanonicalNameSetTests
{
    [Fact]
    public void EmptySet_HasIdZero_AndAddingNothingKeepsIt()
    {
        var interner = new NameSetInterner();
        Assert.Equal(0, NameSetInterner.Empty.Id);
        Assert.Equal(NameSetInterner.Empty, interner.With(NameSetInterner.Empty, []));
        Assert.False(interner.Contains(NameSetInterner.Empty, "a"));
    }

    [Fact]
    public void EqualContent_IsOneNode_WhateverTheOrderAndGrouping()
    {
        var interner = new NameSetInterner();
        var names = Enumerable.Range(0, 300).Select(i => $"n{i}").ToArray();

        var bulk = interner.With(NameSetInterner.Empty, names);
        var reversedOneByOne = Enumerable.Reverse(names).Aggregate(NameSetInterner.Empty, (set, name) => interner.With(set, [name]));
        var chunked = names.Chunk(7).Aggregate(NameSetInterner.Empty, (set, chunk) => interner.With(set, chunk));
        var withDuplicates = interner.With(interner.With(NameSetInterner.Empty, names.Take(150)), names.Concat(names));

        Assert.NotEqual(0, bulk.Id);
        Assert.Equal(bulk, reversedOneByOne);
        Assert.Equal(bulk, chunked);
        Assert.Equal(bulk, withDuplicates);
        Assert.Equal(bulk.Id, chunked.Id);
    }

    [Fact]
    public void AddingPresentNames_ReturnsTheSameSet()
    {
        var interner = new NameSetInterner();
        var set = interner.With(NameSetInterner.Empty, ["a", "b", "c"]);
        Assert.Equal(set, interner.With(set, ["b", "a"]));
        Assert.Equal(set, interner.With(set, ["c", "c", "a"]));
    }

    [Theory]
    [InlineData(1)]
    [InlineData(7)]
    [InlineData(42)]
    public void RandomDerivations_AgreeWithReferenceSets_AndIdsMatchContentExactly(int seed)
    {
        var random = new Random(seed);
        var interner = new NameSetInterner();
        var universe = Enumerable.Range(0, 64).Select(i => i % 3 == 0 ? $"v{i}" : i % 3 == 1 ? $"name_{i}" : $"{(char)('a' + i % 26)}{i}").ToArray();
        var sets = new List<(CanonicalNameSet Set, HashSet<string> Reference)>();

        for (var trial = 0; trial < 400; trial++)
        {
            // Extend a previous set (or the empty one) by a random batch: the same content arises
            // through many different derivations.
            var (baseSet, baseReference) = sets.Count == 0 || random.Next(4) == 0
                ? (NameSetInterner.Empty, new HashSet<string>(StringComparer.Ordinal))
                : sets[random.Next(sets.Count)];
            var batch = Enumerable.Range(0, random.Next(0, 6)).Select(_ => universe[random.Next(universe.Length)]).ToArray();
            var set = interner.With(baseSet, batch);
            var reference = new HashSet<string>(baseReference, StringComparer.Ordinal);
            reference.UnionWith(batch);

            foreach (var name in universe)
                Assert.Equal(reference.Contains(name), interner.Contains(set, name));

            sets.Add((set, reference));
        }

        // Exactness in both directions: equal content ⇔ equal id.
        foreach (var (left, leftReference) in sets)
        {
            foreach (var (right, rightReference) in sets)
                Assert.Equal(leftReference.SetEquals(rightReference), left.Id == right.Id);
        }
    }

    [Fact]
    public void SetsFromDifferentInterners_AreNotComparedByTheCaller_ButEachIsCanonicalWithinItsOwn()
    {
        var first = new NameSetInterner();
        var second = new NameSetInterner();
        // Different interning orders assign different keys; each interner is canonical on its own.
        var a1 = first.With(NameSetInterner.Empty, ["x", "y"]);
        var a2 = first.With(first.With(NameSetInterner.Empty, ["y"]), ["x"]);
        var b1 = second.With(NameSetInterner.Empty, ["y", "z", "x"]);
        var b2 = second.With(second.With(NameSetInterner.Empty, ["z"]), ["x", "y"]);
        Assert.Equal(a1, a2);
        Assert.Equal(b1, b2);
        Assert.True(first.Contains(a1, "x") && first.Contains(a1, "y") && !first.Contains(a1, "z"));
    }

    /// <summary>
    /// Union, difference, count, and enumeration agree with reference sets over random derivations,
    /// and their results are canonical too: a union or difference equals — as the SAME node — the
    /// set built directly from its content.
    /// </summary>
    [Theory]
    [InlineData(3)]
    [InlineData(11)]
    [InlineData(29)]
    public void UnionExceptCountAndNames_AgreeWithReferenceSets_AndStayCanonical(int seed)
    {
        var random = new Random(seed);
        var interner = new NameSetInterner();
        var universe = Enumerable.Range(0, 96).Select(i => $"n{i}").ToArray();
        var sets = new List<(CanonicalNameSet Set, HashSet<string> Reference)> { (NameSetInterner.Empty, new HashSet<string>(StringComparer.Ordinal)) };

        for (var trial = 0; trial < 300; trial++)
        {
            var (left, leftReference) = sets[random.Next(sets.Count)];
            var (right, rightReference) = sets[random.Next(sets.Count)];
            var batch = Enumerable.Range(0, random.Next(0, 12)).Select(_ => universe[random.Next(universe.Length)]).ToArray();

            var (set, reference) = random.Next(3) switch
            {
                0 => (interner.Union(left, right), new HashSet<string>(leftReference.Union(rightReference), StringComparer.Ordinal)),
                1 => (interner.Except(left, right), new HashSet<string>(leftReference.Except(rightReference), StringComparer.Ordinal)),
                _ => (interner.With(left, batch), new HashSet<string>(leftReference.Union(batch), StringComparer.Ordinal)),
            };

            Assert.Equal(reference.Count, set.Count);
            Assert.True(reference.SetEquals(set.Names), $"trial {trial}: enumeration differs from the reference");
            Assert.Equal(set.Count, set.Names.Count());
            Assert.Equal(interner.With(NameSetInterner.Empty, reference), set);
            sets.Add((set, reference));
        }
    }

    [Fact]
    public void UnionAndExcept_Identities()
    {
        var interner = new NameSetInterner();
        var a = interner.With(NameSetInterner.Empty, ["a", "b", "c", "d"]);
        var b = interner.With(NameSetInterner.Empty, ["c", "d", "e"]);

        Assert.Equal(a, interner.Union(a, NameSetInterner.Empty));
        Assert.Equal(a, interner.Union(a, a));
        Assert.Equal(interner.Union(a, b), interner.Union(b, a));
        Assert.Equal(NameSetInterner.Empty, interner.Except(a, a));
        Assert.Equal(a, interner.Except(a, NameSetInterner.Empty));
        Assert.Equal(NameSetInterner.Empty, interner.Except(NameSetInterner.Empty, a));
        Assert.Equal(interner.With(NameSetInterner.Empty, ["a", "b"]), interner.Except(a, b));
        Assert.Equal(0, NameSetInterner.Empty.Count);
        Assert.Empty(NameSetInterner.Empty.Names);
    }

    /// <summary>
    /// Combining a wide set with sets that each differ from an already combined one by a single
    /// name walks only that name's path: the memo answers every unchanged branch pair. The two wide
    /// sets INTERLEAVE their keys, so combining them merges at every branch — without the memo each
    /// variant would re-merge all of it — and removing the other set from a variant likewise.
    /// </summary>
    [Fact]
    public void UnionAndExceptMemo_CombiningSmallVariantsOfWideSets_CostTheirOwnPaths()
    {
        var observations = new FrontEndTraversalObservations();
        var interner = new NameSetInterner(observations);
        // Keys follow first canonicalization: n0, n1, n2, … alternate between the two sets.
        _ = interner.With(NameSetInterner.Empty, Enumerable.Range(0, 8000).Select(i => $"n{i}"));
        var even = interner.With(NameSetInterner.Empty, Enumerable.Range(0, 4000).Select(i => $"n{2 * i}"));
        var odd = interner.With(NameSetInterner.Empty, Enumerable.Range(0, 4000).Select(i => $"n{2 * i + 1}"));
        var all = interner.Union(even, odd);
        _ = interner.Except(all, odd);
        var firstMerge = observations.NameSetOperationSteps;
        Assert.True(firstMerge >= 4000, $"interleaved sets merged in only {firstMerge} steps");

        for (var i = 0; i < 500; i++)
        {
            var variant = interner.With(even, [$"x{i}"]);
            Assert.Equal(8001, interner.Union(variant, odd).Count);
            Assert.Equal(4001, interner.Except(interner.With(all, [$"x{i}"]), odd).Count);
        }

        var perVariant = (observations.NameSetOperationSteps - firstMerge) / 500.0;
        Assert.True(perVariant <= 64, $"each single-name variant took {perVariant:F1} union and difference steps on average");
    }

    [Fact]
    public void ExtendingAWideSet_CanonicalizesOnlyTheAddedNames()
    {
        var observations = new FrontEndTraversalObservations();
        var interner = new NameSetInterner(observations);
        const int width = 5000;
        var wide = interner.With(NameSetInterner.Empty, Enumerable.Range(0, width).Select(i => $"v{i}"));
        Assert.Equal(width, observations.ContextNamesCanonicalized);

        // 1000 sibling extensions by one name each: 1000 more names examined, never 1000 × width.
        var children = Enumerable.Range(0, 1000).Select(i => interner.With(wide, [$"local{i % 10}"])).ToArray();
        Assert.Equal(width + 1000, observations.ContextNamesCanonicalized);
        Assert.Equal(10, children.Select(child => child.Id).Distinct().Count());
        Assert.All(children, child => Assert.True(interner.Contains(child, "v4999")));
    }
}
