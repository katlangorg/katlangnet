namespace KatLang.Tests;

/// <summary>
/// The parser's declaration-start relation is encoded ONCE,
/// <c>Parser.ClassifyDeclarationStartAt</c>: the algorithm body loop dispatches a row on its
/// verdict, and every boundary consumer (the slot boundary, semicolon, open-target and operand
/// recovery, the star classifier) stops at <c>Parser.StartsDeclaration</c>, which is exactly that
/// verdict other than <see cref="Parser.DeclarationStart.None"/>. The two used to be hand-kept
/// copies. These pins check their agreement over every declaration-start shape, recovery shapes
/// included, from three sides: the classifier's verdict; what the body loop dispatches the row
/// as; and where operand recovery, the one boundary consumer reached at every token kind
/// (`public` and the collect-marker star included), stops.
/// <para>A disagreement either loses a following declaration into an operand or makes the body
/// loop re-admit a head that the operand parse refused, without consuming it, and then the parse
/// never ends: a dispatch that skipped the binding-pattern arm at a collect-marker star looped
/// forever on <c>Z = 1 +</c> newline <c>*items = 1, 2</c>. The parsing checks therefore run in a
/// terminable child (<see cref="AgreementProbe"/>), so such a regression fails with its source
/// instead of hanging the suite. The classifier check runs in process: it lexes and then performs
/// only bounded forward scans.</para>
/// </summary>
public class DeclarationStartClassifierTests
{
    private const string DeclarationBoundaryMessage =
        "The next line begins a declaration, which never continues an expression.";
    private const string PublicOpenMessage = "'public' cannot be applied to open declarations.";
    private const string MisplacedOpenMessage =
        "'open' declaration must appear before any properties or output expressions.";
    private const string ReservedLiteralFragment = "is the reserved Boolean literal, not a name";

    /// <summary>
    /// A first line ending in a dangling operator: the next line's first token is where operand
    /// recovery consults the declaration-start relation. It adds exactly one line and declares
    /// <c>Z</c>, so every position on the shape's lines moves down one line.
    /// </summary>
    private const string OperandRecoveryPrefix = "Z = 1 +\n";

    private static readonly (string Source, Parser.DeclarationStart Kind, string[] Names)[] Shapes =
    [
        // open
        ("open A", Parser.DeclarationStart.Open, []),
        ("open A, B", Parser.DeclarationStart.Open, []),
        ("open A B", Parser.DeclarationStart.Open, []),                          // missing-comma recovery

        // public open (reported, then the open is parsed)
        ("public open A", Parser.DeclarationStart.PublicOpen, []),

        // public Name = …
        ("public A = 1", Parser.DeclarationStart.PublicPropertyDefinition, ["A"]),
        ("public A* = 1", Parser.DeclarationStart.PublicPropertyDefinition, ["A"]),
        ("public A * = 1", Parser.DeclarationStart.PublicPropertyDefinition, ["A"]),   // detached marker
        ("public A** = 1", Parser.DeclarationStart.PublicPropertyDefinition, ["A"]),   // repeated marker
        ("public A =\n1", Parser.DeclarationStart.PublicPropertyDefinition, ["A"]),    // body on the next line

        // public Name(pattern) = …
        ("public F(x) = x", Parser.DeclarationStart.PublicClauseDefinition, ["F"]),
        ("public F(x)* = x", Parser.DeclarationStart.PublicClauseDefinition, ["F"]),
        ("public F(a,\nb) = a", Parser.DeclarationStart.PublicClauseDefinition, ["F"]), // pattern list spans lines

        // reserved Boolean literal heads (reported, head skipped)
        ("true = 1", Parser.DeclarationStart.ReservedLiteralHead, []),
        ("false(x) = x", Parser.DeclarationStart.ReservedLiteralHead, []),
        ("public true = 1", Parser.DeclarationStart.ReservedLiteralHead, []),
        ("public false(x) = x", Parser.DeclarationStart.ReservedLiteralHead, []),
        ("true* = 1", Parser.DeclarationStart.ReservedLiteralHead, []),

        // invalid grace on a property name (reported, then the property is parsed)
        ("~A = 1", Parser.DeclarationStart.GracedPropertyDefinition, ["A"]),
        ("~~A = 1", Parser.DeclarationStart.GracedPropertyDefinition, ["A"]),
        ("~ A = 1", Parser.DeclarationStart.GracedPropertyDefinition, ["A"]),
        ("~public A = 1", Parser.DeclarationStart.GracedPropertyDefinition, ["A"]),

        // Name = …
        ("A = 1", Parser.DeclarationStart.PropertyDefinition, ["A"]),
        ("A* = 1", Parser.DeclarationStart.PropertyDefinition, ["A"]),
        ("A * = 1", Parser.DeclarationStart.PropertyDefinition, ["A"]),          // detached marker
        ("A** = 1", Parser.DeclarationStart.PropertyDefinition, ["A"]),          // repeated marker
        ("A @= 1", Parser.DeclarationStart.PropertyDefinition, ["A"]),           // reported character is transparent
        ("A =\n1", Parser.DeclarationStart.PropertyDefinition, ["A"]),           // body on the next line
        ("A =", Parser.DeclarationStart.PropertyDefinition, ["A"]),              // missing body

        // deconstruction binding patterns
        ("x, y = 1, 2", Parser.DeclarationStart.BindingPattern, ["x", "y"]),
        ("x, *rest = 1, 2, 3", Parser.DeclarationStart.BindingPattern, ["x", "rest"]),
        ("*items = 1, 2", Parser.DeclarationStart.BindingPattern, ["items"]),
        ("* items = 1, 2", Parser.DeclarationStart.BindingPattern, ["items"]),     // detached collect marker
        ("**items = 1, 2", Parser.DeclarationStart.BindingPattern, ["items"]),     // repeated collect marker
        ("a*, b = 1, 2", Parser.DeclarationStart.BindingPattern, ["a", "b"]),      // output marker on a target
        ("x, y* = 1, 2", Parser.DeclarationStart.BindingPattern, ["x", "y"]),

        // Name(pattern) = …
        ("F(x) = x", Parser.DeclarationStart.ClauseDefinition, ["F"]),
        ("F(0) = 1", Parser.DeclarationStart.ClauseDefinition, ["F"]),
        ("F(x)* = x", Parser.DeclarationStart.ClauseDefinition, ["F"]),
        ("F(x) * = x", Parser.DeclarationStart.ClauseDefinition, ["F"]),         // detached marker
        ("F(a,\nb) = a", Parser.DeclarationStart.ClauseDefinition, ["F"]),       // pattern list spans lines
        ("F(x, ) = x", Parser.DeclarationStart.ClauseDefinition, ["F"]),         // recovered head

        // no declaration starts here
        ("A", Parser.DeclarationStart.None, []),
        ("1 + 2", Parser.DeclarationStart.None, []),
        ("A == 1", Parser.DeclarationStart.None, []),
        ("A\n= 1", Parser.DeclarationStart.None, []),                            // heads never span a newline
        ("A*\n= 1", Parser.DeclarationStart.None, []),
        ("Foo\n(x) = 1", Parser.DeclarationStart.None, []),
        ("Foo(x)\n= 1", Parser.DeclarationStart.None, []),
        ("x, y\n= 1, 2", Parser.DeclarationStart.None, []),
        ("F(x]) = 1", Parser.DeclarationStart.None, []),                         // the head does not close in itself
        ("public", Parser.DeclarationStart.None, []),
        ("public A", Parser.DeclarationStart.None, []),
        ("public 1 = 2", Parser.DeclarationStart.None, []),
        ("true", Parser.DeclarationStart.None, []),
        ("true + 1", Parser.DeclarationStart.None, []),
        ("~A", Parser.DeclarationStart.None, []),
        ("~A* = 1", Parser.DeclarationStart.None, []),                           // the grace scan admits no marker
        ("*items", Parser.DeclarationStart.None, []),
        ("* 2", Parser.DeclarationStart.None, []),
        ("x, 1 = 2", Parser.DeclarationStart.None, []),
        ("[A = 1]", Parser.DeclarationStart.None, []),
        ("(A = 1)", Parser.DeclarationStart.None, []),
    ];

    public static TheoryData<string> ShapeSources => new(Shapes.Select(shape => shape.Source).ToArray());

    [Fact]
    public void EveryDeclarationStartKind_HasShapes()
    {
        foreach (var kind in Enum.GetValues<Parser.DeclarationStart>())
            Assert.Contains(Shapes, shape => shape.Kind == kind);
        Assert.Equal(Shapes.Length, Shapes.Select(shape => shape.Source).Distinct(StringComparer.Ordinal).Count());
    }

    /// <summary>
    /// The classifier's verdict, and its consumer-position gate: excluding the comma-spanning
    /// arm (open-target recovery's first target) refuses exactly the binding patterns and
    /// changes no other verdict.
    /// </summary>
    [Theory]
    [MemberData(nameof(ShapeSources))]
    public void Classifier_ReturnsTheShapesKind(string source)
    {
        var kind = Assert.Single(Shapes, shape => shape.Source == source).Kind;

        Assert.Equal(kind, Parser.ClassifyDeclarationStartOf(source, includeCommaSpanningBindingPatterns: true));
        Assert.Equal(
            kind == Parser.DeclarationStart.BindingPattern ? Parser.DeclarationStart.None : kind,
            Parser.ClassifyDeclarationStartOf(source, includeCommaSpanningBindingPatterns: false));
    }

    /// <summary>
    /// For every shape, in a terminable child: the body loop dispatches the row as the declaration
    /// the classifier names (<see cref="AssertDispatchedAs"/>), and operand recovery stops exactly
    /// at the dispatched heads (<see cref="AssertOperandRecoveryAgrees"/>).
    /// </summary>
    [Fact]
    public void BodyLoopDispatchAndOperandRecovery_AgreeOnEveryShape()
        => TerminationProbe.RunAndAssert(
            typeof(AgreementProbe), nameof(AgreementProbe.Sweep), Shapes.Length, TerminationProbe.ParserStallWindow);

    /// <summary>
    /// The parsing sweep of <see cref="BodyLoopDispatchAndOperandRecovery_AgreeOnEveryShape"/>, one
    /// work item per shape with its assertions, as one explicitly named probe; not a discovered test.
    /// </summary>
    public sealed class AgreementProbe
    {
        public void Sweep()
        {
            using var progress = TerminationProgress.Start();
            for (var i = 0; i < Shapes.Length; i++)
            {
                var (source, kind, names) = Shapes[i];
                progress.Begin(i + 1, "dispatch", source);
                try
                {
                    AssertDispatchedAs(source, kind, names);
                    progress.Enter("operand-recovery");
                    AssertOperandRecoveryAgrees(source, kind);
                }
                catch (Exception) when (progress.ReportFailure())
                {
                    throw; // Unreachable: the filter only reports the failing source and never catches.
                }
                progress.Complete();
            }
            progress.Finish($"shapes={Shapes.Length}");
        }
    }

    /// <summary>The body loop dispatches the row as the declaration <paramref name="kind"/> names.</summary>
    private static void AssertDispatchedAs(string source, Parser.DeclarationStart kind, string[] names)
    {
        var raw = Parser.ParseSyntax(source);
        var root = raw.Root;
        var diagnostics = raw.Diagnostics.ToList();
        var properties = root.Properties;

        switch (kind)
        {
            case Parser.DeclarationStart.Open:
                Assert.NotEmpty(root.Opens);
                Assert.Empty(properties);
                Assert.DoesNotContain(diagnostics, d => d.Message == PublicOpenMessage);
                break;
            case Parser.DeclarationStart.PublicOpen:
                Assert.NotEmpty(root.Opens);
                Assert.Empty(properties);
                Assert.Single(diagnostics, d => d.Code == DiagnosticCode.InvalidOpenDeclaration && d.Message == PublicOpenMessage);
                break;
            case Parser.DeclarationStart.PublicPropertyDefinition:
                AssertDeclares(properties, names, isPublic: true, clause: false);
                break;
            case Parser.DeclarationStart.PublicClauseDefinition:
                AssertDeclares(properties, names, isPublic: true, clause: true);
                break;
            case Parser.DeclarationStart.ReservedLiteralHead:
                Assert.Empty(properties);
                Assert.Single(diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken
                    && d.Message.Contains(ReservedLiteralFragment, StringComparison.Ordinal));
                break;
            case Parser.DeclarationStart.GracedPropertyDefinition:
                Assert.Single(diagnostics, d => d.Code == DiagnosticCode.InvalidGraceMarker);
                AssertDeclares(properties, names, isPublic: source.Contains("public", StringComparison.Ordinal), clause: false);
                break;
            case Parser.DeclarationStart.PropertyDefinition:
                AssertDeclares(properties, names, isPublic: false, clause: false);
                break;
            case Parser.DeclarationStart.BindingPattern:
                // The deconstruction's hoisted right-hand side, then one private property per
                // target: a property-path recovery of `items = …` declares only the target.
                Assert.Equal(["$deconstruct$0", .. names], properties.Select(p => p.Name));
                Assert.All(properties, p => Assert.False(p.IsPublic));
                break;
            case Parser.DeclarationStart.ClauseDefinition:
                AssertDeclares(properties, names, isPublic: false, clause: true);
                break;
            case Parser.DeclarationStart.None:
                Assert.Empty(properties);
                Assert.Empty(root.Opens);
                Assert.DoesNotContain(diagnostics, d => d.Message == PublicOpenMessage
                    || d.Code == DiagnosticCode.InvalidGraceMarker
                    || d.Message.Contains(ReservedLiteralFragment, StringComparison.Ordinal));
                break;
            default:
                Assert.Fail($"No dispatch observation for {kind}.");
                break;
        }
    }

    /// <summary>
    /// Operand recovery refuses EXACTLY the heads the body loop dispatches as declarations: after
    /// a dangling operator it reports the declaration boundary iff the shape starts a declaration,
    /// and the refused head then parses exactly as it does alone — the same declarations, opens and
    /// rows, and the same diagnostics one line down (beside the boundary report and, for an
    /// <c>open</c>, the misplaced-open report the earlier <c>Z</c> causes). A shape that starts no
    /// declaration is taken as the operand instead.
    /// </summary>
    private static void AssertOperandRecoveryAgrees(string source, Parser.DeclarationStart kind)
    {
        var alone = Parser.ParseSyntax(source);
        var afterDanglingOperator = Parser.ParseSyntax(OperandRecoveryPrefix + source);
        var diagnostics = afterDanglingOperator.Diagnostics.ToList();

        var boundaryReports = diagnostics.Where(d => d.Message.EndsWith(DeclarationBoundaryMessage, StringComparison.Ordinal)).ToList();
        if (kind == Parser.DeclarationStart.None)
        {
            Assert.Empty(boundaryReports);
            return;
        }

        var boundary = Assert.Single(boundaryReports);
        Assert.Equal(DiagnosticCode.UnexpectedToken, boundary.Code);
        Assert.Equal(new SourceSpan(1, 7, 1, 8), boundary.Span);   // the dangling `+`

        var rest = diagnostics.Where(d => !ReferenceEquals(d, boundary)).ToList();
        if (kind is Parser.DeclarationStart.Open or Parser.DeclarationStart.PublicOpen)
            Assert.True(rest.Remove(Assert.Single(rest, d => d.Message == MisplacedOpenMessage)));

        Assert.Equal(
            alone.Diagnostics.Select(d => (d.Code, d.Message, Span: OneLineDown(d.Span))),
            rest.Select(d => (d.Code, d.Message, d.Span)));
        Assert.Equal(
            ["Z", .. alone.Root.Properties.Select(p => p.Name)],
            afterDanglingOperator.Root.Properties.Select(p => p.Name));
        Assert.Equal(
            [false, .. alone.Root.Properties.Select(p => p.IsPublic)],
            afterDanglingOperator.Root.Properties.Select(p => p.IsPublic));
        Assert.Equal(alone.Root.Opens.Count, afterDanglingOperator.Root.Opens.Count);
        Assert.Equal(alone.Root.Output.Count, afterDanglingOperator.Root.Output.Count);
    }

    private static void AssertDeclares(IReadOnlyList<Property> properties, string[] names, bool isPublic, bool clause)
    {
        var property = Assert.Single(properties);
        Assert.Equal(Assert.Single(names), property.Name);
        Assert.Equal(isPublic, property.IsPublic);
        Assert.Equal(clause, IsClause(property.Value));
    }

    // A clause family elaborates to a conditional algorithm, or (one clause with a capture
    // head) an ordinary algorithm with explicit parameters; a property body has neither.
    private static bool IsClause(Algorithm value)
        => value is Algorithm.Conditional || value is Algorithm.User { ParameterPatterns.Count: > 0 };

    private static SourceSpan? OneLineDown(SourceSpan? span)
        => span is { } s
            ? new SourceSpan(s.Start.Line + 1, s.Start.Column, s.End.Line + 1, s.End.Column)
            : null;
}
