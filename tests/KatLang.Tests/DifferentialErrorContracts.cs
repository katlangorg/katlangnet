namespace KatLang.Tests;

// Independent constructor-projection goldens, NOT translations of source programs.
// Some errors are unreachable from validated source. These check the projections even
// when the evaluator corpus has no witness of that constructor. Expectations are handwritten.
internal static class DifferentialErrorContracts
{
    internal sealed record Contract(EvalError Error, string LeanError, ErrorComparison Policy, SharedErrorPayload? Expected);

    internal static readonly IReadOnlyList<Contract> All = Array.AsReadOnly<Contract>([
        new(new EvalError.ArityMismatch(2, 1), "(.arityMismatch 2 1)", ErrorComparison.Comparable, new("arity", [], [2, 1])),
        new(new EvalError.VariadicArityMismatch("F", 2, 1), "(.arityMismatch 2 1)", ErrorComparison.Partial, new("arity", [], [2, 1])),
        new(new EvalError.BadArity(), ".badArity", ErrorComparison.Comparable, new("badArity", [], [])),
        new(new EvalError.BranchArityMismatch("F", 2, 1), "(.branchArityMismatch \"F\" 2 1)", ErrorComparison.Partial, new("branchArity", [], [2, 1])),
        new(new EvalError.BranchOutputArityMismatch("F", 3, 2), "(.branchOutputArityMismatch \"F\" 3 2)", ErrorComparison.Partial, new("branchOutputArity", [], [3, 2])),
        new(new EvalError.UnknownName("x"), "(.unknownName \"x\")", ErrorComparison.Comparable, new("unknownName", ["x"], [])),
        new(new EvalError.UnknownProperty("object", "x"), "(.unknownProperty \"object\" \"x\")", ErrorComparison.Partial, new("unknownProperty", ["x"], [])),
        new(new EvalError.NotPublicProperty("object", "x"), "(.notPublicProperty \"object\" \"x\")", ErrorComparison.Partial, new("notPublicProperty", ["x"], [])),
        new(new EvalError.LocalOnlyProperty("object", "x", PropertyExposure.Exported), "(.localOnlyProperty \"object\" \"x\" .exported)", ErrorComparison.Partial, new("localOnlyProperty", ["x", "exported"], [])),
        new(new EvalError.LocalOnlyProperty("object", "x", PropertyExposure.LocalOnlyConditionalAlgorithm), "(.localOnlyProperty \"object\" \"x\" .localConditional)", ErrorComparison.Partial, new("localOnlyProperty", ["x", "conditional"], [])),
        new(new EvalError.LocalOnlyProperty("object", "x", PropertyExposure.LocalOnlyCapturedAncestorParameters) { RequiredParameters = ["a"] }, "(.localOnlyProperty \"object\" \"x\" (.localCapturedAncestorParams [\"a\"]))", ErrorComparison.Partial, new("localOnlyProperty", ["x", "captured"], [])),
        new(new EvalError.AmbiguousOpen("x", ["M", "N"]), "(.ambiguousOpen \"x\" [\"M\", \"N\"])", ErrorComparison.Partial, new("ambiguousOpen", ["x"], [])),
        new(new EvalError.DuplicateProperty("x"), "(.duplicateProperty \"x\")", ErrorComparison.Comparable, new("duplicateProperty", ["x"], [])),
        new(new EvalError.UnresolvedImplicitParams(["z", "a"]), "(.unresolvedImplicitParams [\"z\", \"a\"])", ErrorComparison.Comparable, new("unresolvedImplicitParams", ["z", "a"], [])),
        new(new EvalError.BadIndex(), ".badIndex", ErrorComparison.Comparable, new("index", [], [])),
        new(new EvalError.DivByZero(), ".divByZero", ErrorComparison.Comparable, new("div0", [], [])),
        new(new EvalError.DemandCycle(), ".demandCycle", ErrorComparison.Comparable, new("demandCycle", [], [])),
        new(new EvalError.DuplicateBranchPattern(), ".duplicateBranchPattern", ErrorComparison.Comparable, new("duplicateBranchPattern", [], [])),
        new(new EvalError.ExplicitParametersRequireOutput(), ".explicitParamsRequireOutput", ErrorComparison.Comparable, new("explicitParamsRequireOutput", [], [])),
        new(new EvalError.MissingOutput(), "(.missingOutput .own)", ErrorComparison.Comparable, new("missingOutput", [], [])),
        new(new EvalError.SpreadMissingOutput(), ".spreadMissingOutput", ErrorComparison.Comparable, new("spreadMissingOutput", [], [])),
        new(new EvalError.TypeMismatch("message"), "(.typeMismatch \"message\")", ErrorComparison.CategoryOnly, null),
        new(new EvalError.NoMatchingBranch("F"), "(.noMatchingBranch \"F\")", ErrorComparison.CategoryOnly, null),
        new(new EvalError.NotAnAlgorithm("description"), "(.notAnAlgorithm \"description\")", ErrorComparison.CategoryOnly, null),
        new(new EvalError.IllegalInOpen("reason"), "(.illegalInOpen \"reason\")", ErrorComparison.CategoryOnly, null),
        new(new EvalError.BadOpenForm("reason"), "(.badOpenForm \"reason\")", ErrorComparison.CategoryOnly, null),
        new(new EvalError.IllegalInEval("reason"), "(.illegalInEval \"reason\")", ErrorComparison.CategoryOnly, null),
        new(new EvalError.WithContext("context", new EvalError.ArityMismatch(2, 1)), "(.withContext \"context\" (.arityMismatch 2 1))", ErrorComparison.Comparable, new("arity", [], [2, 1])),
    ]);
}
