using KatLang;

string source = @"
U = 4
I = 0.5
R = U / I
R
";

var result = Parser.Parse(source);
if (result.Errors.Count == 0)
{
    Console.WriteLine(result.Expression);
}
else
{
    foreach (var error in result.Errors)
    {
        Console.WriteLine($"{error.Message} StartLine: {error.StartLine}; StartColumn: {error.StartColumn}; EndLine: {error.EndLine}; EndColumn: {error.EndColumn}");
    }
}