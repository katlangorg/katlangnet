using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// The OutputBundle ownership contract: an <see cref="OutputBundle"/> SNAPSHOTS
/// its ordered expression membership at construction and never exposes mutable
/// backing storage, so <c>Count</c>, indexing, and enumeration order are
/// stable for the bundle's lifetime. Every test here failed (or was
/// expressible as a failure) against the earlier aliasing implementation:
/// mutating a caller-owned source collection used to mutate the bundle —
/// including the Output bundle of an already-elaborated algorithm, silently
/// invalidating completed front-end analysis.
/// </summary>
public class OutputBundleOwnershipTests
{
    private static readonly Expr A = new Expr.Num(1);
    private static readonly Expr B = new Expr.Num(2);

    // ── 9.1 / 9.2 source-List mutation ──────────────────────────────────────

    [Fact]
    public void FromList_SnapshotsMembership_AddDoesNotGrowTheBundle()
    {
        var input = new List<Expr> { A };
        var bundle = OutputBundle.From(input);

        input.Add(B);

        Assert.Same(A, bundle[0]);
        Assert.Same(A, Assert.Single(bundle));
    }

    [Fact]
    public void FromList_SnapshotsMembership_ClearRemoveReplaceDoNotChangeTheBundle()
    {
        var input = new List<Expr> { A, B };
        var bundle = OutputBundle.From(input);

        input[0] = B;
        input.RemoveAt(1);
        input.Clear();

        Assert.Equal(2, bundle.Count);
        Assert.Same(A, bundle[0]);
        Assert.Same(B, bundle[1]);
        Assert.Equal(new[] { A, B }, bundle.ToArray());
    }

    [Fact]
    public void Constructor_SnapshotsListMembership()
    {
        var input = new List<Expr> { A };
        var bundle = new OutputBundle(input);

        input.Add(B);
        input[0] = B;

        Assert.Same(A, Assert.Single(bundle));
    }

    // ── 9.3 source-array mutation ───────────────────────────────────────────

    [Fact]
    public void FromArray_SnapshotsMembership_ElementReplacementDoesNotChangeTheBundle()
    {
        var input = new Expr[] { A };
        var bundle = OutputBundle.From(input);

        input[0] = B;

        Assert.Same(A, bundle[0]);
    }

    // ── 9.4 implicit conversions ────────────────────────────────────────────

    [Fact]
    public void ImplicitListConversion_Snapshots()
    {
        var input = new List<Expr> { A };
        OutputBundle bundle = input;

        input.Add(B);
        input[0] = B;

        Assert.Same(A, Assert.Single(bundle));
    }

    [Fact]
    public void ImplicitArrayConversion_Snapshots()
    {
        var input = new Expr[] { A };
        OutputBundle bundle = input;

        input[0] = B;

        Assert.Same(A, Assert.Single(bundle));
    }

    [Fact]
    public void CollectionExpression_Snapshots()
    {
        // Collection expressions route through Create(ReadOnlySpan<Expr>),
        // which copies the span into bundle-owned storage.
        OutputBundle bundle = [A, B];
        Assert.Equal(2, bundle.Count);
        Assert.Same(A, bundle[0]);
        Assert.Same(B, bundle[1]);
    }

    // ── 9.5 backing-storage escape ──────────────────────────────────────────

    [Fact]
    public void PublicApi_ExposesNoMutableViewOfBundleMembership()
    {
        var sourceList = new List<Expr> { A };
        var sourceArray = new Expr[] { A };
        foreach (var bundle in new[]
        {
            OutputBundle.From(sourceList),
            OutputBundle.From(sourceArray),
            new OutputBundle(sourceList),
            (OutputBundle)sourceArray,
        })
        {
            // The bundle itself must not be downcastable to mutable storage.
            // (OutputBundle is sealed and implements only IReadOnlyList<Expr>,
            // so the IList cast is impossible even statically; assert through
            // object to keep the runtime pin.)
            Assert.Null((object)bundle as IList<Expr>);
            Assert.Null((object)bundle as List<Expr>);
            Assert.Null((object)bundle as Expr[]);

            // No public instance member may return a type that carries the
            // bundle's Expr membership mutably (List<Expr>, Expr[], IList<Expr>,
            // ICollection<Expr>, ...). This is a behavioral surface assertion,
            // not a private-field peek: it fails if anyone reintroduces an
            // Items-style property that leaks the backing store.
            foreach (var property in typeof(OutputBundle).GetProperties(
                System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.Instance))
            {
                var type = property.PropertyType;
                Assert.False(
                    type.IsAssignableTo(typeof(IList<Expr>)) || type == typeof(Expr[]),
                    $"OutputBundle.{property.Name} exposes mutable membership storage ({type.Name}).");
            }

            foreach (var method in typeof(OutputBundle).GetMethods(
                System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.Instance))
            {
                var type = method.ReturnType;
                Assert.False(
                    type.IsAssignableTo(typeof(IList<Expr>)) || type == typeof(Expr[]),
                    $"OutputBundle.{method.Name}() returns mutable membership storage ({type.Name}).");
            }
        }
    }

    // ── 9.6 existing-bundle reuse ───────────────────────────────────────────

    [Fact]
    public void FromExistingBundle_ReturnsTheSameInstance_NoCopy()
    {
        OutputBundle bundle = [A, B];
        Assert.Same(bundle, OutputBundle.From(bundle));

        // The snapshot constructor may share the already-stable storage of a
        // bundle input; membership must be identical either way.
        var rewrapped = new OutputBundle(bundle);
        Assert.Equal(bundle.ToArray(), rewrapped.ToArray());
    }

    // ── 9.7 Empty ───────────────────────────────────────────────────────────

    [Fact]
    public void Empty_IsSharedAndStable()
    {
        Assert.Same(OutputBundle.Empty, OutputBundle.From(new List<Expr>()));
        Assert.Same(OutputBundle.Empty, OutputBundle.From(Array.Empty<Expr>()));
        Assert.Same(OutputBundle.Empty, (OutputBundle)Array.Empty<Expr>());
        OutputBundle viaCollectionExpression = [];
        Assert.Same(OutputBundle.Empty, viaCollectionExpression);
        Assert.Empty(OutputBundle.Empty);
    }

    // ── 9.8 post-elaboration stability ──────────────────────────────────────

    [Fact]
    public void ElaboratedAlgorithmOutput_CannotBeChangedBehindTheFrontEndsBack()
    {
        // Host-built equivalent of the aliasing hazard the gate review
        // demonstrated: the caller keeps its mutable output list, hands the
        // algorithm to the front end (which completes parameter analysis for
        // exactly that membership), then mutates its list. Before A.1 the
        // bundle aliased the list, so Root.Params stayed stale while the
        // evaluator saw a newly inserted unresolved expression. Now the
        // bundle snapshots: the analyzed AST is immune to the mutation, the
        // analysis stays consistent, and evaluation is unchanged.
        var callerOwnedOutput = new List<Expr>
        {
            new Expr.Binary(BinaryOp.Add, new Expr.Resolve("x"), new Expr.Num(1)),
        };
        var hostRoot = new Algorithm.User(null, [], [], [], callerOwnedOutput);

        var (detected, diagnostics) = ParameterDetector.Detect(hostRoot);
        Assert.Empty(diagnostics);
        Assert.Equal(["x"], detected.Params);
        var analyzedRowCount = detected.Output.Count;

        // The caller mutates its retained collection AFTER analysis completed.
        callerOwnedOutput.Add(new Expr.Resolve("neverAnalyzed"));
        callerOwnedOutput.Clear();

        // The analyzed AST's bundle membership is unchanged...
        Assert.Equal(analyzedRowCount, detected.Output.Count);
        Assert.IsType<Expr.Binary>(Assert.Single(hostRoot.Output));

        // ...the established analysis stays consistent with what evaluation
        // sees: calling the detected root with x = 41 evaluates the analyzed
        // row and nothing else.
        var resolved = ImplicitArgumentResolver.Resolve(detected);
        var program = new Algorithm.User(
            null,
            [],
            [],
            [new Property("F", resolved)],
            [new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(41)])]);
        var run = Evaluator.RunFlat(new Expr.AlgorithmExpr(program));
        Assert.False(run.IsError, run.IsError ? run.Error.ToString() : null);
        Assert.Equal(new Decimal128[] { 42m }, run.Value);
    }

    [Fact]
    public void ParsedAlgorithmOutput_IsStableAgainstEveryPubliclyReachableCollection()
    {
        // Parsed roots never expose the parser's internal row lists, and every
        // bundle in the elaborated tree is snapshot-owned; spot-check that a
        // parsed program's bundles enumerate identically before and after
        // evaluation (no shared mutable state with the evaluator either).
        var root = SourceProvenance.ParseValid("A = 1, 2\nA.count").Root;
        var before = root.Output.ToArray();

        var run = Evaluator.RunFlat(new Expr.AlgorithmExpr(root));
        Assert.False(run.IsError);
        Assert.Equal(new Decimal128[] { 2m }, run.Value);

        Assert.Equal(before, root.Output.ToArray());
    }
}
