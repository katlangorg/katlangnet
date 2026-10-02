namespace KatLang.Tests;

/// <summary>
/// Algorithm results are calculation values. Supplied inputs may expose VALUE and CALLABLE
/// capabilities, but no result construction — a returned parameter, an <c>if</c> or clause
/// selection, a collection, a selection, a multi-row output, a spread of a result, a
/// property holding a call — exports callable identity, and an undersupplied call is an
/// arity failure, never a partially applied callable. Every case runs on all six routes.
/// </summary>
public class ResultValueBoundaryTests
{
    private const string Inc = "Inc(x)=x+1\n";
    private const string Dec = "Dec(x)=x-1\n";
    private const string Apply = "Apply(f,x)=f(x)\n";
    private const string ReturnF = "ReturnF(f)=f\n";
    private const string Choose = "Choose(true,a,b)=a\nChoose(false,a,b)=b\n";

    public static TheoryData<string, KatLangErrorCode> CallableInputsLeaveResultsAsValues => new()
    {
        // A returned parameter is VALUE-demanded; the call result has no callable identity.
        { Inc + ReturnF + "ReturnF(Inc)", KatLangErrorCode.ArityMismatch },
        { Inc + ReturnF + Apply + "Apply(ReturnF(Inc),3)", KatLangErrorCode.NotAnAlgorithm },
        { Inc + "ReturnF(f)=(f)\n" + Apply + "Apply(ReturnF(Inc),3)", KatLangErrorCode.NotAnAlgorithm },
        { Inc + "A=Inc\n" + ReturnF + Apply + "Apply(ReturnF(A),3)", KatLangErrorCode.NotAnAlgorithm },
        { Inc + ReturnF + "R=ReturnF\n" + Apply + "T(z)=Apply(R(Inc),z)\nT(3)", KatLangErrorCode.NotAnAlgorithm },
        { Inc + ReturnF + "T(z)=ReturnF(Inc)==z\nT(1)", KatLangErrorCode.ArityMismatch },
        // Clause-family and builtin `if` selection produce the selected VALUE.
        { Inc + Dec + Choose + Apply + "T(f,g,z)=Apply(Choose(true,f,g),z)\nT(Inc,Dec,3)", KatLangErrorCode.NotAnAlgorithm },
        { Inc + Dec + Apply + "T(f,g,z)=Apply(if(true,f,g),z)\nT(Inc,Dec,3)", KatLangErrorCode.NotAnAlgorithm },
        { Inc + Dec + Choose + "T(f,g)=Choose(true,f,g)\nT(Inc,Dec)", KatLangErrorCode.ArityMismatch },
        { Inc + Dec + "T(f,g)=if(true,f,g)\nT(Inc,Dec)", KatLangErrorCode.ArityMismatch },
        { Inc + "A=Inc\n" + Choose + Apply + "T(z)=Apply(Choose(true,A,A),z)\nT(3)", KatLangErrorCode.NotAnAlgorithm },
        // Collections, selections and collector elements hold values, never callables.
        { Inc + "T(f)=[f]\nT(Inc)", KatLangErrorCode.ArityMismatch },
        { Inc + "T(f)=(f,1)\nT(Inc)", KatLangErrorCode.ArityMismatch },
        { Inc + Apply + "T(f,z)=Apply([f]:0,z)\nT(Inc,3)", KatLangErrorCode.NotAnAlgorithm },
        { Inc + Apply + "T(f,z)=Apply(first((f,1)),z)\nT(Inc,3)", KatLangErrorCode.NotAnAlgorithm },
        { Inc + Apply + "T(*fs)=Apply(fs:0,3)\nT(Inc)", KatLangErrorCode.NotAnAlgorithm },
        { Inc + "T(*fs)=fs\nT(Inc)", KatLangErrorCode.ArityMismatch },
        // Every output row of a multi-row result is a value, and a spread result opens values.
        { Inc + "Two(f,v)=f,v\nTwo(Inc,1)", KatLangErrorCode.ArityMismatch },
        { Inc + "Two(f,v)=v,f\nTwo(Inc,1)", KatLangErrorCode.ArityMismatch },
        { Inc + "Two(f,v)=f,v\n" + Apply + "T(g)=Apply(Two(g,3)*)\nT(Inc)", KatLangErrorCode.ArityMismatch },
        // A property holding a call result is an ordinary zero-parameter property.
        { Inc + ReturnF + "G=ReturnF(Inc)\nG(3)", KatLangErrorCode.ArityMismatch },
        { "Z=7\n" + ReturnF + "Apply0(f)=f()\nApply0(ReturnF(Z))", KatLangErrorCode.NotAnAlgorithm },
        { "V=[1,2,3]\nApply0(f)=f()\nApply0(V.sum)", KatLangErrorCode.NotAnAlgorithm },
        // A loop's final state is materialized as values.
        { Inc + "Step(s)=s\nT(f)=repeat(Step,1,f)\nT(Inc)", KatLangErrorCode.ArityMismatch },
        { Inc + "Step(s)=s\nT(f)=repeat(Step,0,f)\nT(Inc)", KatLangErrorCode.ArityMismatch },
        // A bare callable at the root is its own zero-supply demand.
        { Inc + "Inc", KatLangErrorCode.ArityMismatch },
        { Inc + "A=Inc\nA", KatLangErrorCode.ArityMismatch },
    };

    [Theory]
    [MemberData(nameof(CallableInputsLeaveResultsAsValues))]
    public async Task CallableInputsLeaveResultsAsValues_OnEveryRoute(string source, KatLangErrorCode expected)
    {
        for (var route = 0; route < 6; route++)
        {
            var observation = await ModelCProductionTests.Observe(source, route);
            Assert.True(observation.Error == expected, $"route {route}: expected {expected}, got {observation.Error?.ToString() ?? observation.Value}");
        }
    }

    public static TheoryData<string, KatLangErrorCode> UndersuppliedCallsAreArityFailures => new()
    {
        { "Add(x,y)=x+y\nAdd(10)", KatLangErrorCode.ArityMismatch },
        { "F(0,y)=y\nF(x,y)=x+y\nF(1)", KatLangErrorCode.ArityMismatch },
        { "Add(x,y)=x+y\nA=Add\nA(10)", KatLangErrorCode.ArityMismatch },
        { "take((1,2,3))", KatLangErrorCode.ArityMismatch },
        { "Math.Pow(2)", KatLangErrorCode.ArityMismatch },
        { "trace()", KatLangErrorCode.ArityMismatch },
        { "H(x,*rest)=x\nH()", KatLangErrorCode.ArityMismatch },
        { "I=if\nT(z)=I(true,z)\nT(1)", KatLangErrorCode.ArityMismatch },
        { "Add(x,y)=x+y\nT(z)=if(true,Add(10),z)\nT(1)", KatLangErrorCode.ArityMismatch },
        { "F(0,y)=y\nF(x,y)=x+y\n" + Apply + "Apply(F,3)", KatLangErrorCode.ArityMismatch },
        { Apply + "Apply(take,[1,2])", KatLangErrorCode.ArityMismatch },
        { Apply + "Apply(Math.Pow,2)", KatLangErrorCode.ArityMismatch },
        { "H(x,y,*rest)=x\n" + Apply + "Apply(H,2)", KatLangErrorCode.ArityMismatch },
        // The undersupplied call is a computation, never a callable to apply later.
        { "Add(x,y)=x+y\n" + Apply + "Apply(Add(10),3)", KatLangErrorCode.NotAnAlgorithm },
    };

    [Theory]
    [MemberData(nameof(UndersuppliedCallsAreArityFailures))]
    public async Task UndersuppliedCallsAreArityFailures_OnEveryRoute(string source, KatLangErrorCode expected)
    {
        for (var route = 0; route < 6; route++)
        {
            var observation = await ModelCProductionTests.Observe(source, route);
            Assert.True(observation.Error == expected, $"route {route}: expected {expected}, got {observation.Error?.ToString() ?? observation.Value}");
        }
    }

    [Theory]
    [InlineData(Inc + Apply + "Apply(Inc,3)", "4")]
    [InlineData(Inc + "A=Inc\n" + Apply + "Apply(A,3), A(3)", "(4, 4)")]
    [InlineData(Inc + Apply + "Pass(f)=Apply(f,3)\nPass(Inc)", "4")]
    [InlineData("Target(x)=x*2\nWrapper(x)=Target\nWrapper(5)", "10")]
    [InlineData("Target(x)=x*2\nWrapper(x)=Target\n" + Apply + "Apply(Wrapper,5)", "10")]
    [InlineData(Inc + Apply + "W(f,x)=Apply\nW(Inc,3)", "4")]
    [InlineData(Inc + Apply + "T(*fs)=Apply(fs*,3)\nT(Inc)", "4")]
    [InlineData("Lib={ Inc(x)=x+1 }\n" + Apply + "Apply(Lib.Inc,3)", "4")]
    [InlineData("Lib={ Inc(x)=x+1 }\n" + Apply + "T(m,z)=Apply(m.Inc,z)\nT(Lib,3)", "4")]
    [InlineData("Scale(factor,values)=values.map{ x*factor }\nScale(3,[1,2])", "[3, 6]")]
    [InlineData(Inc + "T(f)=[1,2].map{ f(x) }\nT(Inc)", "[2, 3]")]
    [InlineData("Mk(k)={\nInner={ Add(x)=x+k\nAdd }\nInner(3)\n}\nMk(10)", "13")]
    [InlineData(Inc + "T(f,v)=if(false,f,v)\nT(Inc,5)", "5")]
    [InlineData(Inc + Choose + "T(f,v)=Choose(false,f,v)\nT(Inc,5)", "5")]
    [InlineData("Add(x,y)=x+y\nK(u)=5\nK(Add(10))", "5")]
    [InlineData("Z=7\nApply0(f)=f()\nZ2=Z\nApply0(Z), Z, Z2", "(7, 7, 7)")]
    public async Task HigherOrderInputsForwardingAndLocalCapturesStillWork(string source, string expected)
    {
        for (var route = 0; route < 6; route++)
        {
            var observation = await ModelCProductionTests.Observe(source, route);
            Assert.True(observation.Error is null, $"route {route}: {observation.Error}");
            Assert.Equal(expected, observation.Value);
        }
    }

    /// <summary>
    /// A bare nested callable in a closed body is bare forwarding — an invocation that must be
    /// supplied — never a way to return the nested algorithm to the caller.
    /// </summary>
    [Theory]
    [InlineData("Make(k)={ Add(x)=x+k\nAdd }\nMake(10)")]
    [InlineData("Mk(k)={\nInner={ Add(x)=x+k\nAdd }\nInner\n}\nMk(10)")]
    public void NestedCallablesCannotEscapeThroughAResult(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.Contains(parsed.Diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.UnforwardableParameter);
    }
}
