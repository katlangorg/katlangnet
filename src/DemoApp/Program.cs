using KatLang;

var source = """
    TomatoPrice = 1.20
    ApplePrice = 0.80
    CucumberPrice = 0.60

    Expense when (1, qty) = TomatoPrice * qty
    Expense when (2, a, qty) = ~a * qty //error should be in this line
    Expense when (3, qty) = CucumberPrice * qty //but it is shown in this line

    Expense(1, 0.80, 3)
    """;

switch (KatLangEngine.Run(source))
{
    case RunResult.Success s:
        Console.WriteLine(s.ToDisplayString());
        break;

    case RunResult.ParseFailure p:
        foreach (var error in p.Errors)
            Console.WriteLine(error);
        break;

    case RunResult.EvalFailure e:
        foreach (var error in e.Errors)
            Console.WriteLine(error);
        break;
}

// ── Pretty-printer ──────────────────────────────────────────────────────────

static void PrintAst(RunResult result)
{
    switch (result)
    {
        case RunResult.Success s:
            Console.WriteLine("=== AST ===");
            PrintAlgorithm(s.Root, indent: 0);
            break;
        case RunResult.EvalFailure p:
            Console.WriteLine("=== AST ===");
            PrintAlgorithm(p.Root, indent: 0);
            break;
    }
}

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
