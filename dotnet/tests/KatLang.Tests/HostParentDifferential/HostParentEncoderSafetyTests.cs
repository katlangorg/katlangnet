namespace KatLang.Tests;

public class HostParentEncoderSafetyTests
{
    [Theory]
    [InlineData(12)]
    [InlineData(24)]
    public void SharedExpressionInHostParent_IsPrintedWithoutExpandingEveryPath(int depth)
    {
        Expr diamond = new Expr.Num(1);
        for (var i = 0; i < depth; i++)
            diamond = new Expr.Binary(BinaryOp.Add, diamond, diamond);
        var host = new ScopeCtx(null, [], [new Property("P", new Algorithm.User(null, [], [], [], [diamond]))]);
        var program = new Algorithm.User(host, [], [], [], [new Expr.Num(1)]);
        Assert.Null(AstStructuralPreflight.Check(program, EvaluationLimits.MaxSupportedAstDepth,
            AstConsumerProfile.EvaluatorIterativeJoinSpines));
        var encoded = LeanAstEncoder.EncodeAlgorithm(program);
        Assert.True(encoded.Length < 20_000, $"{depth} shared links produced {encoded.Length} characters.");
        Assert.Contains("let ", encoded, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EvaluatorAcceptedJoinSpineInsideHostParent_IsEncodedIteratively(bool spread)
    {
        Expr spine = new Expr.Num(1);
        for (var i = 0; i < 20_000; i++)
            spine = spread ? new Expr.SequenceSpread(spine) : new Expr.SequenceConstruct(spine, new Expr.Num(1));
        var host = new ScopeCtx(null, [], [new Property("P", new Algorithm.User(null, [], [], [], [spine]))]);
        var program = new Algorithm.User(host, [], [], [], [new Expr.Num(1)]);
        Assert.Null(AstStructuralPreflight.Check(program, EvaluationLimits.MaxSupportedAstDepth,
            AstConsumerProfile.EvaluatorIterativeJoinSpines));
        var encoded = LeanAstEncoder.EncodeAlgorithm(program);
        Assert.Contains(spread ? ".sequenceSpread " : ".sequenceConstruct ", encoded, StringComparison.Ordinal);
        Assert.True(encoded.Length < 4_000_000);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SharedParentScopeDiamond_IsPrintedOncePerObject(bool componentProvenance)
    {
        ScopeCtx scope = new(null, [], []);
        for (var i = 0; i < 16; i++)
        {
            var block = new Expr.AlgorithmExpr(new Algorithm.User(scope, [], [], [], []));
            scope = new ScopeCtx(null, [block, block], []);
        }
        var alias = new Algorithm.Alias(null, [], [], new Expr.Num(1)) { HasRuntimeTarget = true };
        var program = new Algorithm.User(scope, [], [], [], componentProvenance
            ? new OutputBundle([new Expr.AlgorithmExpr(alias), new Expr.AlgorithmExpr(alias)])
            : new OutputBundle([new Expr.Num(1)]));
        Assert.Null(AstStructuralPreflight.Check(program, EvaluationLimits.MaxSupportedAstDepth,
            AstConsumerProfile.EvaluatorIterativeJoinSpines));
        var encoded = LeanAstEncoder.EncodeAlgorithm(program);
        Assert.True(encoded.Length < 20_000, $"16 shared parent links produced {encoded.Length} characters.");
        Assert.Contains("let ", encoded, StringComparison.Ordinal);
    }
}
