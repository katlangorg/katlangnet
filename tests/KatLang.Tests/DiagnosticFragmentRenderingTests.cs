namespace KatLang.Tests;

public class DiagnosticFragmentRenderingTests
{
    private static string RenderFragment(string fragment)
        => fragment.Replace("\r", "<CR>", StringComparison.Ordinal).Replace("\n", "<LF>", StringComparison.Ordinal);

    [Fact]
    public void FrontEndLayout_SeparatesRawLineBreaksFromTheStructuralSeparator()
    {
        var text = DiagnosticMessage.JoinLines("first\nFORGED", "repair\r\nFORGED");
        var diagnostic = new Diagnostic(text, DiagnosticSeverity.Error, null) { Code = DiagnosticCode.UnforwardableParameter };
        var original = new Diagnostic(diagnostic.Message, diagnostic.Severity, diagnostic.Span) { Code = diagnostic.Code };
        var error = KatLangError.FromDiagnostic(diagnostic);

        Assert.Equal("first<LF>FORGED" + Environment.NewLine + "repair<CR><LF>FORGED", error.RenderDiagnostic(RenderFragment));
        Assert.Equal(text.Text, error.Message);
        Assert.Equal(diagnostic, original);
        Assert.Equal(diagnostic.GetHashCode(), original.GetHashCode());
        Assert.Equal(diagnostic.ToString(), original.ToString());
        Assert.Equal(RenderFragment(original.Message), KatLangError.FromDiagnostic(original).RenderDiagnostic(RenderFragment));
        Assert.Equal(KatLangErrorCode.UnforwardableParameter, error.Code);
        Assert.Null(error.Source);
    }

    [Fact]
    public void FrontEndLayout_TracksEveryStructuralSeparator()
    {
        var diagnostic = new Diagnostic(DiagnosticMessage.JoinLines(["first\nFORGED", "repair\nFORGED", "suggestion\nFORGED"]),
            DiagnosticSeverity.Error, null);

        Assert.Equal(string.Join(Environment.NewLine, "first<LF>FORGED", "repair<LF>FORGED", "suggestion<LF>FORGED"),
            KatLangError.FromDiagnostic(diagnostic).RenderDiagnostic(RenderFragment));
    }

    [Fact]
    public void StructuredMessages_AreNotFormattedAfterTheDiagnosticBudgetIsExhausted()
    {
        var bag = new DiagnosticBag(1);
        var formatted = 0;
        for (var i = 0; i < 3; i++)
        {
            bag.Report(DiagnosticCode.UndeclaredIdentifier, null, i, value =>
            {
                formatted++;
                return DiagnosticMessage.JoinLines($"error {value}", "repair");
            });
        }

        Assert.Equal(1, formatted);
        Assert.Equal(2, bag.Count);
        Assert.Equal(DiagnosticCode.DiagnosticCountExceeded, bag[1].Code);
        Assert.Equal("error 0" + Environment.NewLine + "repair",
            KatLangError.FromDiagnostic(bag[0]).RenderDiagnostic(RenderFragment));
    }

    [Theory]
    [InlineData(4093)]
    [InlineData(4094)]
    [InlineData(4095)]
    [InlineData(4096)]
    [InlineData(5000)]
    public void BoundedFrontEndMessages_KeepOnlyACompleteStructuralSeparator(int firstLineLength)
    {
        var first = "raw\nFORGED" + new string('x', firstLineLength - "raw\nFORGED".Length);
        var diagnostic = new Diagnostic(DiagnosticMessage.JoinLines(first, new string('y', 5000)), DiagnosticSeverity.Error, null);
        var bag = new DiagnosticBag(1);
        bag.Add(diagnostic);
        var stored = Assert.Single(bag);
        Assert.True(stored.Message.Length <= DiagnosticBag.MaxRetainedMessageLength + ExprNameRenderer.TruncationMarker.Length);
        var retainedSeparator = stored.Message.Length >= first.Length + Environment.NewLine.Length
            && stored.Message.AsSpan(first.Length, Environment.NewLine.Length).SequenceEqual(Environment.NewLine);

        var rendered = KatLangError.FromDiagnostic(stored).RenderDiagnostic(RenderFragment);

        Assert.StartsWith("raw<LF>FORGED", rendered);
        Assert.Equal(retainedSeparator ? 1 : 0, rendered.Count(ch => ch == '\n'));
        Assert.Equal(stored.Message, KatLangError.FromDiagnostic(stored).Message);
    }

    [Fact]
    public void DeferredModuleLayout_PreservesOnlyDiagnosticAndExplanationSeparators()
    {
        var primary = new Diagnostic(DiagnosticMessage.JoinLines("first\nFORGED", "repair\nFORGED"), DiagnosticSeverity.Error, null)
        {
            Code = DiagnosticCode.UnforwardableParameter,
        };
        var secondary = new Diagnostic("second\nFORGED", DiagnosticSeverity.Error, null) { Code = DiagnosticCode.InvalidLoadUrl };
        var warning = new Diagnostic("not an error", DiagnosticSeverity.Warning, null);
        var source = EvalError.ModuleRegionMaterializationFailed.From([warning, primary, primary, secondary]);
        var error = KatLangError.FromEvalError(source);
        var original = error.Message;

        Assert.Equal("first<LF>FORGED" + Environment.NewLine + "repair<LF>FORGED" + Environment.NewLine + "second<LF>FORGED",
            error.RenderDiagnostic(RenderFragment));
        Assert.Equal(original, error.Message);
        Assert.Same(source, error.Source);
        Assert.Equal(KatLangErrorCode.UnforwardableParameter, error.Code);
    }
}
