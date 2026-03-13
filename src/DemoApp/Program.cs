using KatLang;

var source = """
    2/999999999999999999999999999999
    """;

Console.WriteLine("=== KatLang Parser Demo ===");
Console.WriteLine(source);
Console.WriteLine();

// Parse
var result = Parser.Parse(source, null);

if (result.HasErrors)
{
    Console.WriteLine("Diagnostics:");
    foreach (var diag in result.Diagnostics)
        Console.WriteLine($"  [{diag.Severity}] at {diag.Span.StartLineNumber}:{diag.Span.StartColumn}: {diag.Message}");
    Console.WriteLine();
}

var ast = result.Root;

Console.WriteLine("=== AST ===");
PrintAlgorithm(ast, indent: 0);

// Evaluate
Console.WriteLine();
Console.WriteLine("=== Evaluation ===");
var evalResult = Evaluator.Run(new Expr.Block(ast));
if (evalResult.IsOk)
{
    var output = ResultToString(evalResult.Value);
    Console.WriteLine(output);
}
else
{
    var err = evalResult.Error;
    if (err.Span is { } span)
        Console.WriteLine($"Evaluation failed at {span.StartLineNumber}:{span.StartColumn}-{span.EndLineNumber}:{span.EndColumn}: {err}");
    else
        Console.WriteLine($"Evaluation failed: {err}");
}

static void TestEval(string source, string expected)
{
    var ast = Parser.Parse(source).Root;
    var evalResult = Evaluator.Run(new Expr.Block(ast));
    var actual = evalResult.IsOk ? $"[{string.Join(", ", evalResult.Value.ToAtoms())}]" : $"failed: {evalResult.Error}";
    var status = actual == expected ? "OK" : "FAIL";
    Console.WriteLine($"{status}: {source.Replace("\n", "\\n")} => {actual} (expected {expected})");
}

// ── Pretty-printer ──────────────────────────────────────────────────────────

static void PrintAlgorithm(Algorithm alg, int indent)
{
    var pad = new string(' ', indent);

    if (alg is Algorithm.Builtin(var id))
    {
        Console.WriteLine($"{pad}Builtin({id})");
        return;
    }

    if (alg.Params.Count > 0)
        Console.WriteLine($"{pad}Params: [{string.Join(", ", alg.Params)}]");

    if (alg.Opens.Count > 0)
    {
        for (var i = 0; i < alg.Opens.Count; i++)
        {
            Console.Write($"{pad}Open[{i}]: ");
            PrintExpr(alg.Opens[i], indent + 2);
            Console.WriteLine();
        }
    }

    foreach (var prop in alg.Properties)
    {
        Console.WriteLine($"{pad}{prop.Name} =");
        PrintAlgorithm(prop.Value, indent + 2);
    }

    for (var i = 0; i < alg.Output.Count; i++)
    {
        Console.Write($"{pad}Output[{i}]: ");
        PrintExpr(alg.Output[i], indent + 2);
        Console.WriteLine();
    }
}

static void PrintExpr(Expr expr, int indent)
{
    switch (expr)
    {
        case Expr.Num(var v):
            Console.Write($"Num({v})");
            break;

        case Expr.Param(var n):
            Console.Write($"Param(\"{n}\")");
            break;

        case Expr.Resolve(var n):
            Console.Write($"Resolve(\"{n}\")");
            break;

        case Expr.StringLiteral(var s):
            Console.Write($"StringLiteral(\"{s}\")");
            break;

        case Expr.Unary(var op, var operand):
            Console.Write($"Unary({op}, ");
            PrintExpr(operand, indent);
            Console.Write(')');
            break;

        case Expr.Binary(var op, var left, var right):
            Console.Write($"Binary({op}, ");
            PrintExpr(left, indent);
            Console.Write(", ");
            PrintExpr(right, indent);
            Console.Write(')');
            break;

        case Expr.Index(var target, var selector):
            Console.Write("Index(");
            PrintExpr(target, indent);
            Console.Write(", ");
            PrintExpr(selector, indent);
            Console.Write(')');
            break;

        case Expr.Combine(var left, var right):
            Console.Write("Combine(");
            PrintExpr(left, indent);
            Console.Write(", ");
            PrintExpr(right, indent);
            Console.Write(')');
            break;

        case Expr.DotCall(var target, var name, var dotArgs):
            Console.Write("DotCall(");
            PrintExpr(target, indent);
            Console.Write($", \"{name}\"");
            if (dotArgs is not null)
            {
                Console.Write(", ");
                PrintAlgorithm(dotArgs, indent);
            }
            Console.Write(')');
            break;

        case Expr.Grace(var inner, var weight):
            Console.Write($"Grace({weight}, ");
            PrintExpr(inner, indent);
            Console.Write(')');
            break;

        case Expr.Block(var alg):
            Console.WriteLine("Block(");
            PrintAlgorithm(alg, indent + 2);
            Console.Write($"{new string(' ', indent)})");
            break;

        case Expr.Call(var func, var args):
            Console.Write("Call(");
            PrintExpr(func, indent);
            Console.WriteLine(", Args(");
            PrintAlgorithm(args, indent + 2);
            Console.Write($"{new string(' ', indent)}))");
            break;

        case Expr.NativeCall(var fnName, var argNames):
            Console.Write($"NativeCall(\"{fnName}\", [{string.Join(", ", argNames)}])");
            break;
    }
}

static string ResultToString(Result result)
{
    if (result is Result.Atom val)
    {
        return val.Value.ToString();
    }
    if (result is Result.Group group)
    {
        var text = new System.Text.StringBuilder();
        foreach (var item in group.Items)
        {
            text.Append(InlineResultToString(item));
            text.Append("\n");
        }

        return text.ToString();
    }

    return string.Empty;
}

static string InlineResultToString(Result result)
{
    if (result is Result.Atom atom)
        return atom.Value.ToString();

    if (result is Result.Group group)
        return string.Join(",", group.Items.Select(InlineResultToString));

    return string.Empty;
}

static string GroupToString(Result.Group group)
{
    var text = new System.Text.StringBuilder();
    text.Append("(");
    foreach (var item in group.Items)
    {
        if (item is Result.Atom atom)
        {
            text.Append(atom.Value);
        }
        if (item is Result.Group subGroup)
        {
            text.Append(GroupToString(subGroup));
        }
        text.Append(",");
    }
    if (group.Items.Count() > 0)
    {
        text.Remove(text.Length - 1, 1);
    }
    text.Append(")");

    return text.ToString();
}
