using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorOpenVisibilityTests
{
    private static void AssertEvalAllPublicFails(string source)
    {
        var result = EvalAllPublic(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: [{string.Join(", ", result.Value)}]");
    }

    /// <summary>
    /// ERROR-TOLERANT: evaluates a source the FRONT END has already rejected,
    /// to confirm the parser's recovery tree does not accidentally produce a
    /// value. Callers must have asserted the front-end diagnostic first — the
    /// parse failure is the real coverage; this is only a belt-and-braces check
    /// that recovery does not fabricate a result.
    ///
    /// <para>
    /// Deliberately separate from the STRICT-SOURCE helpers (Track 13): those
    /// now refuse to evaluate parse-invalid source precisely so a test cannot
    /// claim evaluator coverage it does not have.
    /// </para>
    /// </summary>
    private static void AssertFrontEndRejectedAndRecoveryTreeAlsoFails(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.True(parsed.HasErrors, $"Expected a front-end diagnostic for:{Environment.NewLine}{source}");

        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(MakeAllPublic(parsed.Root)));
        if (result.IsOk)
            Assert.Fail($"Recovery tree unexpectedly evaluated to: [{string.Join(", ", result.Value)}]");
    }

    // â”€â”€ Open resolution â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Open_MathPi()
    {
        var source = """
            open Math
            Pi
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_MathExp()
    {
        var source = """
            open Math
            Exp(1)
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(Decimal128.Exp(Decimal128.One), result.Value[0]);
    }

    [Fact]
    public void Eval_Open_MathInExpression()
    {
        var source = """
            open Math
            Pi * 2
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi * 2, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_UserDefinedModule()
    {
        var source = """
            open M
            M = { public X = 42
            X }
            X
            """;
        AssertEvalAllPublic(source, 42);
    }

    [Fact]
    public void Eval_Open_TripleDotSpellingFails()
    {
        // There is no ellipsis token: `A...B` lexes as dot tokens, so the
        // dotted open target is ordinary invalid syntax and the parse fails
        // before evaluation ever runs.
        var source = """
            A = { public X = 1
            X }
            B = { public Y = 2
            Y }
            open A...B
            X + Y
            """;
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);

        AssertFrontEndRejectedAndRecoveryTreeAlsoFails(source);
    }

    [Fact]
    public void Eval_Open_SpreadExpressionTargetFails()
    {
        // A spread expression is not an open form: the parser rejects
        // it before evaluation ever runs.
        var source = """
            A = { public X = 1
            X }
            open A*
            X
            """;
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);
        Assert.Contains(
            parseResult.Diagnostics,
            d => d.Message.Contains("Invalid open form: 'spread' is not allowed in open declarations"));

        AssertFrontEndRejectedAndRecoveryTreeAlsoFails(source);
    }

    [Fact]
    public void Eval_Open_MissingProperty_Fails()
    {
        var source = """
            open Math
            Foo
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Open_InPropertyBody()
    {
        var source = """
            open Math
            Circumference = Pi * 2 * r
            Circumference(5)
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi * 2 * 5, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_DirectFunctionOpen()
    {
        var source = """
            open Lib
            Lib = { public F = x + 1 }
            F(10)
            """;
        AssertEvalAllPublic(source, 11);
    }

    [Fact]
    public void Eval_Open_PublicMemberBodyCanCallBuiltinIf()
    {
        var source = """
            open Vec
            Vec = {
                public Test = if(x > 0, 1, 0)
            }
            Test(35)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Open_PublicMemberBodyCanCallBuiltinMath()
    {
        var source = """
            open Vec
            Vec = {
                public Magnitude = Math.Sqrt(x * x + y * y)
            }
            Magnitude(3, 4)
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_Open_PublicMemberBodyCanCallBuiltinSum()
    {
        var source = """
            open Vec
            Vec = {
                public SumPair = (x, y).sum
            }
            SumPair(3, 4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_Open_PublicMemberCallMatchesOwnerQualifiedCall()
    {
        var source = """
            open Vec
            Vec = {
                public Test = if(x > 0, 1, 0)
            }
            Direct = Vec.Test(35)
            Opened = Test(35)
            Direct == Opened
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Open_PublicZeroArgMemberBodyCanCallBuiltinIf()
    {
        var source = """
            open Vec
            Vec = {
                public Test = if(1 > 0, 10, 20)
            }
            Test
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Open_PublicMemberSeesDefinitionSiteSibling()
    {
        var source = """
            open Vec
            Vec = {
                Helper = 10
                public Test = Helper + x
            }
            Test(5)
            """;
        AssertEval(source, 15);
    }

    [Fact]
    public void Eval_Open_PublicMemberDoesNotSeeOpenerLocalShadow()
    {
        var source = """
            A = 10
            Vec = {
                public Test = A + x
            }
            Scope = {
                open Vec
                A = 100
                Test(5)
            }
            Scope
            """;
        AssertEval(source, 15);
    }

    [Fact]
    public void Eval_Open_PrivateMemberRemainsHidden()
    {
        var source = """
            open Vec
            Vec = {
                Hidden = 10
                public Test = 1
            }
            Hidden
            """;
        var result = Eval(source);
        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_Open_PublicMemberAmbiguityRemainsAnError()
    {
        var source = """
            open A, B
            A = {
                public Test = 1
            }
            B = {
                public Test = 2
            }
            Test
            """;
        var result = Eval(source);
        Assert.True(result.IsError);
        Assert.IsType<EvalError.AmbiguousOpen>(Innermost(result.Error));
    }

    [Fact]
    public void Eval_Open_DotAccess_NestedResolve()
    {
        var source = """
            Lib = { Helper = x + 1
              UseHelper = Helper(x)
            }
            Lib.UseHelper(10)
            """;
        AssertEval(source, 11);
    }


    [Fact]
    public void Eval_Open_LibraryOpenWithNestedResolve()
    {
        var source = """
            open Lib
            Lib = { public Helper = x + 1
              public UseHelper = Helper(x)
            }
            UseHelper(10)
            """;
        AssertEvalAllPublic(source, 11);
    }

    [Fact]
    public void Eval_Open_LibraryIsolatedFromOpenerScope()
    {
        // In the Opens model, libraries are isolated: they do NOT get access
        // to the opener's scope. Fn lives in Wrapper but is not visible to Lib.
        var source = """
            Lib = { Apply = Fn(x) }
            Wrapper = {
              open Lib
              Fn = x * 2
              Apply(5)
            }
            Wrapper
            """;
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_LibraryCannotAccessOpenerProperty()
    {
        // Library's property references a name that only exists in the opening scope.
        // Opens are isolated â€” Factor is not visible to Lib.
        var source = """
            Lib = { Calc = x * Factor }
            Main = {
              open Lib
              Factor = 3
              Calc(5)
            }
            Main
            """;
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_LibraryWithOwnDependencies()
    {
        // A library can reference its own properties (sibling resolution works).
        var source = """
            open Lib
            Lib = {
              public Helper = x + 1
              public UseHelper = Helper(x)
            }
            UseHelper(10)
            """;
        AssertEvalAllPublic(source, 11);
    }

    // â”€â”€ Open-specific tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Open_MultipleOpens()
    {
        var source = """
            open A, B
            A = { public X = 1 }
            B = { public Y = 2 }
            X + Y
            """;
        AssertEvalAllPublic(source, 3);
    }

    [Fact]
    public void Eval_Open_UnbracketedCommaList_ResolvesFromSecondLib()
    {
        // open Lib2, Lib3 → two separate opens; Val3 resolves from Lib3
        var source = """
            open Lib2, Lib3
            Lib2 = { public Val2 = 20 }
            Lib3 = { public Val3 = 30 }
            Val3
            """;
        AssertEvalAllPublic(source, 30);
    }

    [Fact]
    public void Eval_Open_AmbiguityFails()
    {
        // Both A and B provide X â†’ ambiguity â†’ should fail
        var source = """
            open A, B
            A = { public X = 1 }
            B = { public X = 2 }
            X
            """;
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_LocalOverridesOpen()
    {
        // Local property takes priority over imported name
        var source = """
            open Lib
            Lib = { public X = 99 }
            X = 1
            X
            """;
        AssertEvalAllPublic(source, 1);
    }

    [Fact]
    public void Eval_Open_TripleDotSpellingDoesNotMergeLibraries()
    {
        // Libraries are opened through one comma-separated open declaration
        // (semicolon is not an open-target separator); there is no ellipsis
        // token, so an `A...B` spelling lexes as dot tokens and is a parse
        // error, not a merged open.
        var source = """
            A = { public X = 1 }
            B = { public Y = 2 }
            open A...B
            X + Y
            """;
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);

        AssertFrontEndRejectedAndRecoveryTreeAlsoFails(source);
    }

    [Fact]
    public void Eval_Open_CommaList_OpensBothLibraries()
        // Comma is the open-target separator: one open declaration with a
        // comma-separated list opens both libraries, so X + Y = 3.
        // (`open` must precede the definitions it targets; a lexically visible
        // head defined later in the same body is explicitly supported.)
        => AssertEvalAllPublic("open A, B\nA = { public X = 1 }\nB = { public Y = 2 }\nX + Y", 3);

    [Theory]
    [InlineData("open A, B, C\nA = { public X = 1 }\nB = { public Y = 2 }\nC = { public Z = 4 }\nX + Y + Z")]
    [InlineData("open A,\nB,\nC\nA = { public X = 1 }\nB = { public Y = 2 }\nC = { public Z = 4 }\nX + Y + Z")]
    [InlineData("open A\n, B\n, C\nA = { public X = 1 }\nB = { public Y = 2 }\nC = { public Z = 4 }\nX + Y + Z")]
    public void Eval_Open_CommaContinuationAcrossLines_OpensAllTargets(string source)
        // Trailing- and leading-comma continuation are equivalent to the
        // single-line list: all three libraries open, so X + Y + Z = 7.
        => AssertEvalAllPublic(source, 7);

    [Theory]
    [InlineData("open Lib.Sub\nLib = { public Sub = { public V = 7 } }\nV")]
    [InlineData("open Lib\n.Sub\nLib = { public Sub = { public V = 7 } }\nV")]
    public void Eval_Open_DottedTargetWithLeadingDotContinuation_OpensSameTarget(string source)
        // A leading '.' continues the dotted open target across the line,
        // so both spellings open Lib.Sub and V resolves to 7.
        => AssertEvalAllPublic(source, 7);

    [Theory]
    [InlineData("A = { public X = 1 }\nB = { public Y = 2 }\nopen A ; B\nX + Y")]
    [InlineData("A = { public X = 1 }\nB = { public Y = 2 }\nopen A B\nX + Y")]
    public void Eval_Open_NonCommaSeparator_IsParseErrorNotTwoOpens(string source)
    {
        // ';' and same-line adjacency are not open-target separators: the
        // parse reports the separator mistake, and B is never opened.
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);

        AssertFrontEndRejectedAndRecoveryTreeAlsoFails(source);
    }

    [Fact]
    public void Eval_Open_NotTransitive()
    {
        // Lib1's opens should not be visible to the opener
        var source = """
            open Lib1
            Inner = { public Z = 42 }
            Lib1 = {
                open Inner
                W = Z
            }
            Z
            """;
        // Z is not transitively visible â†’ fail
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_SelfNameInOpenExpression_Fails()
    {
        // "self" is no longer a keyword — it's now just an identifier.
        // Using it in open position fails because there's no algorithm named "self".
        var source = """
            open self.HiddenLib
            HiddenLib = { X = 42 }
            X
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Open_ChildResolvesFromParentOpens()
    {
        // Lean test: parent-open visibility.
        // Parent opens Lib; Child does NOT open it.
        // Child resolves "X" via parent chain â†’ parent opens â†’ Lib.
        var source = """
            Lib = { public X = 42 }
            Main = {
                open Lib
                Child = (X)
                Child
            }
            Main
            """;
        AssertEvalAllPublic(source, 42);
    }

    [Fact]
    public void Eval_Open_StructuralOwnershipTakesPrecedenceOverOpens()
    {
        // Ownership-first model: structural properties in the parent chain
        // always take precedence over opened namespaces.
        //
        // Wrapper resolves "Val" via:
        //   1. Local props â†’ none
        //   2. Parent structural: Main â†’ no Val; Root â†’ Val = 0 found!
        //   3. Opens never consulted (structural wins)
        //
        // Even though Main opens Lib which has Val = 42, the root's
        // structural Val = 0 takes precedence.
        var source = """
            Val = 0
            Main = {
                open Lib
                Lib = { public Val = 42 }
                Wrapper = (
                    Val
                )
                Wrapper
            }
            Main
            """;
        AssertEvalAllPublic(source, 0);
    }

    // â”€â”€ Property visibility tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Visibility_OpenCanSeePublicButNotPrivate()
    {
        // Library with one public and one private property.
        // Open should see the public one but not the private one.
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            open Lib
            public Lib = { public X = 42
            Y = 99 }
            X
            """;
        AssertEval(source, 42);

        // Now try Y (private) â€” should fail
        var sourceY = """
            open Lib
            public Lib = { public X = 42
            Y = 99 }
            Y
            """;
        AssertEvalFails(sourceY);
    }

    [Fact]
    public void Eval_Visibility_NotPublicPropertyOnPrivateIntermediate()
    {
        // open Lib.Sub where Sub exists but is private → NotPublicProperty.
        // Lib doesn't need public (it's in the ownership chain), but Sub must
        // be public because it's an intermediate on the open path.
        //
        // Track 12: this test previously used a source with `open` written AFTER
        // a property, which the PARSER rejects. `EvalFull` ignores parser
        // diagnostics, so the test passed on an unrelated recovery-AST failure
        // and never reached the branch it names. It also needs the second,
        // valid provider: without a name that falls through to the opens, open
        // resolution never runs at all, and the obvious `X` reference is turned
        // into an implicit parameter before evaluation. See
        // OpenPathResolutionBranchTests for the full pre-emption story.
        var source = """
            Pub = { public Y = 7 }
            Lib = { Sub = { public X = 42 } }
            A = {
                open Lib.Sub, Pub
                Y
            }
            A
            """;

        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected NotPublicProperty but got: {result.Value}");

        var notPublic = Assert.IsType<EvalError.NotPublicProperty>(Innermost(result.Error));
        Assert.Equal("Lib", notPublic.ObjectDesc);
        Assert.Equal("Sub", notPublic.PropertyName);
    }

    // â”€â”€ Open normalization acceptance tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Open_PropPathInOpen_Works()
    {
        // Acceptance A: Lib.Sub in open â†’ prop-path resolves correctly
        var source = """
            open Lib.Sub
            public Lib = { public Sub = { public X = 1 } }
            X
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Open_DotCallWithArgs_Fails()
    {
        // Acceptance B: Lib.Sub() â†’ call-like dot syntax in open â†’ parse error
        var source = """
            public Lib = { public Sub = { public X = 1 } }
            open Lib.Sub()
            X
            """;
        // Parser emits diagnostic for invalid open form
        var result = KatLang.Parser.Parse(source);
        Assert.True(result.HasErrors);
    }

    [Fact]
    public void Eval_Open_MultipleOpensCommaForm_Works()
    {
        // Acceptance C: multiple opens with comma-separated form
        var source = """
            open Lib2, Lib3
            public Lib2 = { public Val = 2 }
            public Lib3 = { public Val2 = 3 }
            Val2
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Open_PrivateIntermediate_Fails()
    {
        // Acceptance D: private intermediate on open path
        var source = """
            open Lib.Sub
            Lib = { Sub = { public X = 1 } }
            X
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Visibility_OwnershipFirstShadowingBeatsOpens()
    {
        // Structural property in parent chain beats opened property,
        // even when the structural property is private.
        // Opens enforce public-only, but structural always wins first.
        var source = """
            Val = 0
            Main = {
                open Lib
                Lib = { Val = 42 }
                Wrapper = (
                    Val
                )
                Wrapper
            }
            Main
            """;
        // Make Lib and its Val public so the open path works
        AssertEvalAllPublic(source, 0);
    }

    [Fact]
    public void Eval_Visibility_AmbiguousOpenWithTwoPublicProviders()
    {
        // Two opens provide the same public name â†’ AmbiguousOpen error
        var source = """
            open A, B
            A = { public X = 1 }
            B = { public X = 2 }
            X
            """;
        AssertEvalAllPublicFails(source);

        // Verify it's specifically an AmbiguousOpen error
        var ast = ParseValidRoot(source);
        var publicAst = MakeAllPublic(ast);
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(publicAst));
        Assert.True(result.IsError);
        // Unwrap WithContext if present
        var err = result.Error;
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        Assert.IsType<EvalError.AmbiguousOpen>(err);
    }

    [Fact]
    public void Eval_Visibility_AllParsedPropertiesPrivateByDefault()
    {
        // Parsed properties are private by default.
        // Opening a user-defined library with default visibility should
        // not expose any properties through opens.
        var source = """
            open Lib
            Lib = { X = 42 }
            X
            """;
        // Without MakeAllPublic, X should NOT be visible through opens
        AssertEvalFails(source);
    }

    // â”€â”€ Public keyword syntax tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_PublicKeyword_OpenCanSeePublicProperty()
    {
        var source = """
            open Lib
            Lib = { public Val = 42 }
            Val
            """;
        // Lib itself must also be public for open resolution to find it
        AssertEvalAllPublic(source, 42);
    }

    [Fact]
    public void Eval_PublicKeyword_EndToEnd()
    {
        // Full end-to-end: public keyword makes property visible through opens.
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            open Lib
            public Lib = { public Val = 42 }
            Val
            """;
        AssertEval(source, 42);
    }

    [Fact]
    public void Eval_PublicKeyword_PrivateNotVisible()
    {
        // Library with one public and one private property
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            open Lib
            public Lib = { public X = 1
            Y = 2 }
            X
            """;
        AssertEval(source, 1);

        // Y is private, should fail
        var sourceY = """
            open Lib
            public Lib = { public X = 1
            Y = 2 }
            Y
            """;
        AssertEvalFails(sourceY);
    }

    [Fact]
    public void Eval_PublicKeyword_InBlock()
    {
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            open Lib
            public Lib = {public Val = 42}
            Val
            """;
        AssertEval(source, 42);
    }

    // â”€â”€ Opens-aware parameter detection (Lean: shouldTreatAsImplicitParam) â”€â”€

    [Fact]
    public void Eval_Open_LowercasePublicProperty_ResolvesViaOpen()
    {
        // Lowercase public property visible through opens should NOT become a param.
        // Lean: shouldTreatAsImplicitParam uses lookupLexical which includes opens.
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            open Lib
            public Lib = { public val = 42 }
            val
            """;
        AssertEval(source, 42);
    }

    [Fact]
    public void Eval_Open_LowercasePublicFunction_CanBeCalled()
    {
        // Opened lowercase function name: should stay as Resolve, not become param.
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            open Lib
            public Lib = { public inc = x + 1 }
            inc(5)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_Open_PropertyBodySeesOpenedNames()
    {
        // "val" in F's body is visible through parent's opens (not a param of F).
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            open Lib
            public Lib = { public val = 42 }
            F = val + 1
            F
            """;
        AssertEval(source, 43);
    }

    // -- open visibility: container does not need to be public ----------------
    // Rule: open never requires the opened algorithm itself to be public.
    //       It only requires the algorithm to be available in the current context.
    //       open imports only public members of that algorithm.

    [Fact]
    public void Eval_Open_LocalNonPublicAlgorithm_CanBeOpened()
    {
        // open never requires the opened algorithm itself to be public.
        // It only requires the algorithm to be available in the current context.
        // open imports only public members of that algorithm.
        var source = """
            open Lib
            Lib = {
                public Pi = 3
            }
            Pi
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Open_LocalPublicAlgorithm_CanStillBeOpened()
    {
        // Public open target also works (public is not required, but not harmful).
        var source = """
            open Lib
            public Lib = {
                public Pi = 3
            }
            Pi
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Open_NonPublicMember_NotImported()
    {
        // open imports only public members. Non-public members must not be visible.
        var source = """
            open Lib
            Lib = {
                Pi = 3
            }
            Pi
            """;
        var result = Eval(source);
        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_Open_QualifiedAccess_StillWorks()
    {
        // Qualified dot-access should keep current intended behavior.
        var source = """
            Lib = {
                public Pi = 3
            }
            Lib.Pi
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Open_NestedLocalOpen_Works()
    {
        // open inside a nested algorithm body can open a sibling definition.
        var source = """
            A = {
                open Lib
                Lib = {
                    public Pi = 3
                }
                Pi
            }
            A
            """;
        AssertEval(source, 3);
    }
}
