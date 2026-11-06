namespace KatLang.Tests;

/// <summary>
/// A signature-only prelude placeholder is no open provider (MOD-03 with MOD-07; constitution audit
/// neighbouring finding). The semantic prelude declares <c>load</c> only so that detection never infers the
/// directive's name; the runtime prelude has no such binding, so an open target's direct lookup finds
/// nothing there. An open that reaches the placeholder is therefore the ordinary
/// <see cref="KatLangErrorCode.UnresolvedOpenTarget"/>, exactly as for any other name only an open provides,
/// and never <see cref="KatLangErrorCode.IllegalInOpen"/> over a parameter no source wrote. The placeholder set
/// is read from the registry, so a future signature-only name is covered without a spelling here.
/// </summary>
public class OpenSignatureOnlyPlaceholderTests
{
    public static TheoryData<string> PlaceholderNames
    {
        get
        {
            var names = new TheoryData<string>();
            foreach (var name in BuiltinRegistry.SemanticPreludeExtraNames.Where(BuiltinRegistry.IsSemanticPreludeOnlyName))
                names.Add(name);
            return names;
        }
    }

    private static KatLangError SingleFrontEndError(string source)
    {
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        return Assert.Single(failure.Errors);
    }

    private static void AssertNoPhantomParameter(KatLangError error)
    {
        Assert.DoesNotContain("(found:", error.Message, StringComparison.Ordinal);
        foreach (var parameter in BuiltinRegistry.LoadParameterNames)
            Assert.DoesNotContain($"'{parameter}'", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void TheRegistryDeclaresAPlaceholder()
        => Assert.Contains("load", BuiltinRegistry.SemanticPreludeExtraNames.Where(BuiltinRegistry.IsSemanticPreludeOnlyName));

    [Theory]
    [MemberData(nameof(PlaceholderNames))]
    public void ReferenceToThePlaceholder_IsAnUnresolvedOpenTarget(string name)
    {
        var error = SingleFrontEndError($"open A, B\nA = {{ public {name} = 1 }}\nB = {name}\n1");
        Assert.Equal(KatLangErrorCode.UnresolvedOpenTarget, error.Code);
        AssertNoPhantomParameter(error);
        Assert.Contains("'B'", error.Message, StringComparison.Ordinal);
        var span = Assert.NotNull(error.Span);
        Assert.Equal((1, 9), (span.Start.Line, span.Start.Column));
    }

    [Fact]
    public void TheWitnessMatchesAnOrdinaryNameOnlyAnOpenProvides()
    {
        static string Shape(string message, string name) => message.Replace($"'{name}'", "'_'");
        var placeholder = SingleFrontEndError("open A, B\nA = { public load = 1 }\nB = load\n1");
        var ordinary = SingleFrontEndError("open A, B\nA = { public Foo = 1 }\nB = Foo\n1");
        Assert.Equal(ordinary.Code, placeholder.Code);
        Assert.Equal(Shape(ordinary.Message, "Foo"), Shape(placeholder.Message, "load"));
        Assert.Equal(ordinary.Span, placeholder.Span);
    }

    [Theory]
    [MemberData(nameof(PlaceholderNames))]
    public void ThePlaceholderWrittenAsTheTarget_IsAnUnresolvedOpenTarget(string name)
    {
        foreach (var source in new[] { $"open {name}\n1", $"open {name}.X\n1", $"open A, {name}\nA = {{ public {name} = 1 }}\n1" })
        {
            var error = SingleFrontEndError(source);
            Assert.Equal(KatLangErrorCode.UnresolvedOpenTarget, error.Code);
            AssertNoPhantomParameter(error);
        }
    }

    [Fact]
    public void AnUnboundBareReferenceBehindAnOpen_KeepsItsOwnDiagnostic()
    {
        var error = SingleFrontEndError("open B\nB = load\n1");
        Assert.Equal(KatLangErrorCode.UnboundLoadReference, error.Code);
        Assert.Equal(ParameterDetector.UnboundLoadReferenceMessage, error.Message);
    }

    [Theory]
    // A real declaration of the spelling is an ordinary provider, in the head and in the reference.
    [InlineData("open load\nload = { public X = 1 }\nX", "1")]
    [InlineData("open B\nload = { public X = 1 }\nB = load\nX", "1")]
    // An opened public member named `load` keeps binding the bare name.
    [InlineData("open A\nA = { public load = 1 }\nload", "1")]
    [InlineData("open A\nA = { public load = 1 }\nB = load\nB", "1")]
    public void ARealBinding_StaysOrdinary(string source, string expected)
        => Assert.Equal(expected, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());

    [Theory]
    // Genuinely illegal targets keep their category, and a WRITTEN parameter is still named.
    [InlineData("open B\nB(x) = x\n1", KatLangErrorCode.IllegalInOpen, "(found: x)")]
    [InlineData("open count\n1", KatLangErrorCode.IllegalInOpen, "builtin")]
    [InlineData("open B\nB = count\n1", KatLangErrorCode.IllegalInOpen, "builtin")]
    [InlineData("open Nope\n1", KatLangErrorCode.UnresolvedOpenTarget, "'Nope'")]
    [InlineData("open A, B\nA = { public Foo = 1 }\nB = Foo\n1", KatLangErrorCode.UnresolvedOpenTarget, "'B'")]
    public void OtherOpenRefusals_AreUnchanged(string source, KatLangErrorCode code, string fragment)
    {
        var error = SingleFrontEndError(source);
        Assert.Equal(code, error.Code);
        Assert.Contains(fragment, error.Message, StringComparison.Ordinal);
    }
}
