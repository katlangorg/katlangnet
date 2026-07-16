using KatLang;

var source = """
    sum(1,2,3,4,5)
    """;

switch (KatLangEngine.Run(source, new RunOptions { DownloadCode = DownloadCode }))
{
    case RunResult.Success s:
        Console.WriteLine(s.ToDisplayString());
        break;

    case RunResult.NoProgramOutput n:
        Console.WriteLine(n.ToDisplayString());
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
        case RunResult.NoProgramOutput n:
            Console.WriteLine("=== AST ===");
            PrintAlgorithm(n.Root, indent: 0);
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

        case Expr.SequenceConstruct(var joinLeft, var joinRight):
            Console.Write("SequenceConstruct(");
            PrintExpr(joinLeft, indent);
            Console.Write(", ");
            PrintExpr(joinRight, indent);
            Console.Write(')');
            break;

        case Expr.SequenceSpread(var operand):
            Console.Write("SequenceSpread(");
            PrintExpr(operand, indent);
            Console.Write(')');
            break;

        case Expr.ListLiteral(var listItems):
            Console.Write("ListLiteral(");
            for (var i = 0; i < listItems.Count; i++)
            {
                if (i > 0)
                    Console.Write(", ");
                PrintExpr(listItems[i], indent);
            }
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
    if (result is Result.SequenceValue sequenceValue)
    {
        var text = new System.Text.StringBuilder();
        foreach (var item in sequenceValue.Items)
        {
            text.Append(InlineResultToString(item));
            text.Append("\n");
        }

        return text.ToString();
    }
    if (result is Result.ListValue listValue)
    {
        return ListValueToString(listValue);
    }

    return string.Empty;
}

static string InlineResultToString(Result result)
{
    if (result is Result.Atom atom)
        return atom.Value.ToString();

    if (result is Result.SequenceValue sequenceValue)
        return string.Join(",", sequenceValue.Items.Select(InlineResultToString));

    if (result is Result.ListValue listValue)
        return ListValueToString(listValue);

    return string.Empty;
}

static string ListValueToString(Result.ListValue listValue)
{
    var text = new System.Text.StringBuilder();
    text.Append("[");
    for (var i = 0; i < listValue.Items.Count; i++)
    {
        if (i > 0)
            text.Append(", ");

        text.Append(listValue.Items[i] switch
        {
            Result.Atom atom => atom.Value.ToString(),
            Result.SequenceValue nested => SequenceValueToString(nested),
            Result.ListValue nested => ListValueToString(nested),
            var other => InlineResultToString(other),
        });
    }
    text.Append("]");

    return text.ToString();
}

static string SequenceValueToString(Result.SequenceValue sequenceValue)
{
    var text = new System.Text.StringBuilder();
    text.Append("(");
    foreach (var item in sequenceValue.Items)
    {
        if (item is Result.Atom atom)
        {
            text.Append(atom.Value);
        }
        if (item is Result.SequenceValue nestedSequenceValue)
        {
            text.Append(SequenceValueToString(nestedSequenceValue));
        }
        if (item is Result.ListValue nestedListValue)
        {
            text.Append(ListValueToString(nestedListValue));
        }
        text.Append(",");
    }
    if (sequenceValue.Items.Count() > 0)
    {
        text.Remove(text.Length - 1, 1);
    }
    text.Append(")");

    return text.ToString();
}
static string DownloadCode(string url)
{
    using var client = new HttpClient { Timeout = TimeSpan.FromSeconds(10) };
    return client.GetStringAsync(url).GetAwaiter().GetResult();
}
