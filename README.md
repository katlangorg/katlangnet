# Kat
KatLang - Language for calculations. To learn more read the [KatLang tutorial](http://katlang.org/tutorial) or play with [KatLang online](http://katlang.org).
## KatLang scanner and parser .net library
Nuget package: https://www.nuget.org/packages/KatLang
### Use of KatLang parser library
```c#
using KatLang;

string katCode = @"
U = 4
I = 0.5
R = U / I
R
";

var result = Parser.Parse(katCode);
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
```

## Roadmap
Improve KatLang type system.
Performance improvements.
Do some research on possible syntax improvements.

## Feedback
Contact Mikus Vanags: mikus.vanags@logicsresearchcentre.com