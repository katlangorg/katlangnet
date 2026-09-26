using System.Collections;
using System.Collections.ObjectModel;
using KatLang.Semantics;

namespace KatLang.Formatting.PublicApi.Tests;

public class ScopeVisibilityPublicContractTests
{
    private static SemanticModel Model()
    {
        var parsed = Parser.Parse("Lib = { public X = 1\n1 }\nA = { Q = 2\nQ }\nB = { Q = 3\nQ }\nA + B");
        Assert.Empty(parsed.Diagnostics);
        return SemanticModelBuilder.Build(parsed);
    }

    [Fact]
    public void EnumeratorState_MatchesThePreviousArrayBackedPublicList()
    {
        var model = Model();
        foreach (var list in new[] { model.ScopeVisibilities[0].Symbols, model.GetVisibleSymbolsAt(new SourcePosition(1, 1)) })
        {
            var expected = ((IEnumerable)Array.AsReadOnly(list.ToArray())).GetEnumerator();
            var actual = ((IEnumerable)list).GetEnumerator();
            Assert.Equal(ReadError(expected), ReadError(actual));
            while (expected.MoveNext())
            {
                Assert.True(actual.MoveNext());
                Assert.Same(expected.Current, actual.Current);
            }
            Assert.False(actual.MoveNext());
            Assert.Equal(ReadError(expected), ReadError(actual));
            expected.Reset();
            actual.Reset();
            Assert.Equal(ReadError(expected), ReadError(actual));
            Assert.True(actual.MoveNext());
            Assert.Same(list[0], actual.Current);
        }
    }

    private static Type? ReadError(IEnumerator enumerator)
        => Record.Exception(() => _ = enumerator.Current)?.GetType();

    [Fact]
    public void SharedSymbols_HaveAnExplicitModelLocalEqualityContract()
    {
        var model = Model();
        var symbols = model.ScopeVisibilities.Select(scope => Assert.Single(scope.Symbols, s => s.Name == "Lib")).ToArray();
        Assert.True(symbols.Length > 2);
        Assert.NotEmpty(symbols[0].Members);
        foreach (var symbol in symbols)
        {
            Assert.Same(symbols[0], symbol);
            Assert.True(symbols[0] == symbol);
            Assert.Equal(symbols[0].GetHashCode(), symbol.GetHashCode());
            Assert.Same(symbols[0].Members, symbol.Members);
            Assert.Contains(symbol, new HashSet<VisibleSymbol> { symbols[0] });
        }
        var shadows = model.ScopeVisibilities.SelectMany(s => s.Symbols).Where(s => s.Name == "Q").Distinct().ToArray();
        Assert.Equal(2, shadows.Length);
        Assert.NotSame(shadows[0].Declaration, shadows[1].Declaration);
        Assert.NotEqual(shadows[0], shadows[1]);
        Assert.NotSame(symbols[0], Model().ScopeVisibilities[0].Symbols.Single(s => s.Name == "Lib"));
    }

    [Fact]
    public void ListsKeepTheirTypeEqualityAndMutationContracts()
    {
        var model = Model();
        foreach (var scope in model.ScopeVisibilities)
        {
            Assert.IsType<ReadOnlyCollection<VisibleSymbol>>(scope.Symbols);
            Assert.Equal(scope, scope with { });
            Assert.Equal(scope.GetHashCode(), (scope with { }).GetHashCode());
            Assert.NotEqual(scope, new ScopeVisibility(scope.Span, scope.Symbols, scope.NestingDepth));
            Assert.Equal(scope.ToString(), new ScopeVisibility(scope.Span, scope.Symbols, scope.NestingDepth).ToString());
            var items = scope.Symbols.ToArray();
            var generic = Assert.IsAssignableFrom<IList<VisibleSymbol>>(scope.Symbols);
            var nonGeneric = Assert.IsAssignableFrom<IList>(scope.Symbols);
            Assert.True(generic.IsReadOnly);
            Assert.True(nonGeneric.IsFixedSize);
            Assert.Throws<NotSupportedException>(() => generic[0] = items[0]);
            Assert.Throws<NotSupportedException>(() => generic.Add(items[0]));
            Assert.Throws<NotSupportedException>(() => generic.Insert(0, items[0]));
            Assert.Throws<NotSupportedException>(() => generic.Remove(items[0]));
            Assert.Throws<NotSupportedException>(() => generic.RemoveAt(0));
            Assert.Throws<NotSupportedException>(generic.Clear);
            Assert.Throws<NotSupportedException>(() => nonGeneric[0] = items[0]);
            Assert.Throws<NotSupportedException>(() => nonGeneric.Add(items[0]));
            Assert.Throws<NotSupportedException>(() => nonGeneric.Insert(0, items[0]));
            Assert.Throws<NotSupportedException>(() => nonGeneric.Remove(items[0]));
            Assert.Throws<NotSupportedException>(() => nonGeneric.RemoveAt(0));
            Assert.Throws<NotSupportedException>(nonGeneric.Clear);
            Assert.Same(((ICollection)scope.Symbols).SyncRoot, ((ICollection)scope.Symbols).SyncRoot);
            Assert.False(((ICollection)scope.Symbols).IsSynchronized);
            var copied = new object[items.Length + 1];
            ((ICollection)scope.Symbols).CopyTo(copied, 1);
            Assert.Equal(items, copied.Skip(1));
            foreach (var symbol in items.Where(s => s.Members.Count > 0))
                Assert.Throws<NotSupportedException>(() => ((IList<VisibleSymbol>)symbol.Members).Clear());
            Assert.Equal(items, scope.Symbols);
        }
        var empty = SemanticModelBuilder.Build(Parser.Parse("1")).ScopeVisibilities.Single();
        Assert.Same(Array.Empty<VisibleSymbol>(), empty.Symbols);
        Assert.Equal(new ScopeVisibility(null, []), empty);
    }
}
