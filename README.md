# KatLang — Language for Calculations

You write formulas, give them names and build larger calculations from them, and KatLang works out the results in decimal arithmetic.

To learn more, read the [introduction][about] and the [tutorial][tutorial], or play with [KatLang online][playground].

## A first look

```
Data = [2, 4, 4, 4, 5, 5, 7, 9]

Mean = Data.avg
Variance = Data.map{(x - Mean) ^ 2}.avg
Deviation = Variance.sqrt

Mean, Variance, Deviation
```

It outputs `5`, `4` and `2`: the mean, the variance and the standard deviation of the data. Each `Name = …` line defines a calculation, and any other line, here the last, produces output. `Data.avg` is another way to write `avg(Data)`, and inside the braces `x`, which nothing defines, stands for each element of the list in turn.

## Why KatLang

- **Inferred parameters.** In `Speed = distance / time`, the names that nothing defines become parameters in order of appearance, so `Speed(100, 8)` is `12.5`.
- **Decimal arithmetic.** Numbers are decimals with 34 significant digits, so `0.1 + 0.2` is `0.3` and `19.99 * 3` is `59.97`.
- **One idea for functions and modules.** Every calculation is an *algorithm* that can have parameters, named parts and output, and algorithms can be passed to other algorithms.
- **Formally specified.** The core semantics are defined in the Lean 4 theorem prover, with machine-checked proofs of key properties.
- **Made to be embedded.** A program cannot reach files or the network unless its host allows it, and the host can limit and cancel its work.

## Try it

- **In your browser:** try KatLang in the [online playground][playground], with nothing to install.
- **On the command line:** download the archive for Windows, Linux or macOS from the [latest release][releases], extract `katlang` and put it on your `PATH`. It is a single executable and needs no .NET installation.

  ```text
  katlang eval "2 + 3 * 4"
  katlang run program.kat
  ```

  The first prints `14`. The second runs a program file; save the example from *A first look* as `program.kat` to try it. The [command-line guide][cli] covers every command and option, including running and sharing programs as links.

## Use KatLang from .NET

The [KatLang NuGet package][nuget] parses and runs KatLang programs in .NET 11 applications (`dotnet add package KatLang`):

```c#
using KatLang;

var result = await KatLangEngine.RunAsync("""
    Speed = distance / time
    Speed(100, 8)
    """);
Console.WriteLine(result.ToDisplayString());   // 12.5
```

A run returns a structured result instead of throwing for a mistake in the program. The [.NET guide][dotnet] shows how to inspect it and handle errors safely, set resource limits, add your own operations, format output and load modules.

## Specification and proofs

KatLang's semantics are defined in [`KatLang.lean`][spec], an executable model written in the Lean 4 theorem prover. Within the limits listed below, it is the single source of truth for how programs evaluate, and independent implementations should conform to it. The surface syntax is defined by [`KatLang.ebnf`][ebnf] together with the reference parser in this repository.

To check a new implementation, run the programs in the [portable conformance fixture][conformance] and compare its results and diagnostics with the expected values.

Machine-checked Lean proofs establish core properties of that model — for example, how arguments, including spreads, are distributed among parameters; that `x.Add(1)` gives the same value as `Add(x, 1)` once checking `x` finds no member named `Add`; and that a value, once computed for an argument or cached for a property, never changes. The Lean work has limits:

- The proofs are about the Lean model, not the C# code. No proof connects the two, so this implementation is checked against the model by running the same test programs through both.
- The Lean model's numbers are integers and it has no `Math` functions, so decimal arithmetic (IEEE 754 Decimal128) and functions such as `sqrt` are tested in C# only.
- Lean's evaluator starts from the program after the C# front end has parsed it, resolved its names and inferred its parameters: parsing has no Lean model, and parts of name resolution and parameter inference are checked against Lean specification functions on test corpora.
- Host features have no Lean counterpart: resource limits, cancellation, async evaluation, module downloads, seeded randomness and output formatting.
- Some theorems hold only under stated premises, and some properties are still open. The [proof ledger][ledger] lists every claim with its premises and status.

## License

This project is released under the MIT License with an additional patent grant provided by Logics Research Centre SIA. See [LICENSE][license], [PATENTS][patents] and [NOTICE][notice], which the NuGet package also contains. Contributors, please read [CONTRIBUTING.md][contributing] and [CODE_OF_CONDUCT.md][coc].

The patent grant covers use and distribution of KatLang, derivative works, and independent reimplementations of the KatLang language that conform to the KatLang specification ([`KatLang.lean`][spec]). If you are building such an implementation, you are already covered — no permission needed. For uses of the patented techniques outside the scope of KatLang, you are welcome to reach out — Logics Research Centre SIA is open to discussing licensing arrangements. Don't hesitate to get in touch: mikus.vanags@logicsresearchcentre.com

> "Ask and it will be given to you; seek and you will find; knock and the door will be opened to you."
> Matthew 7:7

## Roadmap

- Research possible syntax improvements.
- Improve the KatLang type system.
- Improve performance.

If you have ideas for improving or extending the KatLang language — new constructs, better semantics, or clearer language rules — you are warmly welcome to open a discussion or reach out directly. Good ideas are always worth a conversation.

## Co-funded by the European Union

1.1.1.9 Research application No 1.1.1.9/LZP/3/25/353 of the Activity "Post-doctoral Research" "KatLang: Enhancing a Higher-Order Domain-Specific Language for Problem Solving and Educational Assessment in Mathematics and Physics".

## Authorship and Contributions

KatLang is created and authored by Mikus Vanags and published by Logics Research Centre SIA. Copyright is held by Logics Research Centre SIA and Contributors: contributors keep the copyright in their contributions and license them under the MIT License, with no Contributor License Agreement required (see CONTRIBUTING.md). Contributions from the community are very welcome — whether through ideas, discussions, bug reports, documentation improvements, or code. The full list of contributors is at https://github.com/katlangorg/katlangnet/graphs/contributors.

## Feedback
Contact Mikus Vanags: mikus.vanags@logicsresearchcentre.com

---

> "So whether you eat or drink or whatever you do, do it all for the glory of God."
> 1 Corinthians 10:31

Jesus is Lord.

[about]: https://katlang.org/about
[tutorial]: https://katlang.org/tutorial
[playground]: https://katlang.org
[releases]: https://github.com/katlangorg/katlangnet/releases/latest
[nuget]: https://www.nuget.org/packages/KatLang
[cli]: https://github.com/katlangorg/katlangnet/blob/main/docs/cli.md
[dotnet]: https://github.com/katlangorg/katlangnet/blob/main/docs/dotnet.md
[spec]: https://github.com/katlangorg/katlangnet/blob/main/lean/KatLang.lean
[ebnf]: https://github.com/katlangorg/katlangnet/blob/main/KatLang.ebnf
[conformance]: https://github.com/katlangorg/katlangnet/blob/main/conformance/README.md
[ledger]: https://github.com/katlangorg/katlangnet/blob/main/docs/design/formal-correspondence-ledger.md
[license]: https://github.com/katlangorg/katlangnet/blob/main/LICENSE
[patents]: https://github.com/katlangorg/katlangnet/blob/main/PATENTS
[notice]: https://github.com/katlangorg/katlangnet/blob/main/NOTICE
[coc]: https://github.com/katlangorg/katlangnet/blob/main/CODE_OF_CONDUCT.md
[contributing]: https://github.com/katlangorg/katlangnet/blob/main/CONTRIBUTING.md
