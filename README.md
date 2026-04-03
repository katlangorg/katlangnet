# KatLang — Language for Calculations
To learn more read the [KatLang tutorial](http://katlang.org/tutorial) or play with [KatLang online](http://katlang.org).

## Language Specification
The authoritative KatLang specification is defined in [`KatLang.lean`](KatLang.lean) using the Lean theorem prover. It is the single source of truth for KatLang's syntax, semantics, and language rules. Independent implementations should conform to this specification.

If you have ideas for improving or extending the KatLang language — new constructs, better semantics, or clearer language rules — you are warmly welcome to open a discussion or reach out directly. Good ideas are always worth a conversation.

## Use of KatLang .NET parsing and evaluation library
```c#
using KatLang;

var source = """
    NetSalary = {
        SocTax = grossSalary * 0.105
        ChildCredit = numberOfChildren * 250
        NonTaxMin = 550
        TaxableIncome = grossSalary - SocTax - ChildCredit - NonTaxMin
        IncomeTax = TaxableIncome * 0.255
        grossSalary - SocTax - IncomeTax
    }
    NetSalary(1600, 2)
    """;

switch (KatLangEngine.Run(source))
{
    case RunResult.Success s:
        foreach (var atom in s.Atoms)
            Console.WriteLine(atom);
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
```

## Nuget package
https://www.nuget.org/packages/KatLang

License and patent grant details are included in the repository and package files (`LICENSE`, `PATENTS`).

## Licensing

This project is released under the MIT License with an additional patent grant provided by Logics Research Centre SIA.

Please see:
- LICENSE
- PATENTS
- NOTICE
- CODE_OF_CONDUCT.md
- CONTRIBUTING.md

The patent grant covers use and distribution of KatLang, derivative works, and independent reimplementations of the KatLang language that conform to the KatLang specification (`KatLang.lean`). If you are building such an implementation, you are already covered — no permission needed. For uses of the patented techniques outside the scope of KatLang, you are welcome to reach out — Logics Research Centre SIA is open to discussing licensing arrangements. Don't hesitate to get in touch: mikus.vanags@logicsresearchcentre.com

> "Ask and it will be given to you; seek and you will find; knock and the door will be opened to you."
> Matthew 7:7

## Roadmap
Research on possible syntax improvements.
Improve KatLang type system.
Performance improvements.

## Co-funded by the European Union

1.1.1.9 Research application No 1.1.1.9/LZP/3/25/353 of the Activity "Post-doctoral Research" "KatLang: Enhancing a Higher-Order Domain-Specific Language for Problem Solving and Educational Assessment in Mathematics and Physics".

## Authorship and Contributions

KatLang is created and authored by Mikus Vanags and published by Logics Research Centre SIA. Contributions from the community are very welcome — whether through ideas, discussions, bug reports, documentation improvements, or code.

## Feedback
Contact Mikus Vanags: mikus.vanags@logicsresearchcentre.com

---

> "So whether you eat or drink or whatever you do, do it all for the glory of God."
> 1 Corinthians 10:31

Jesus is Lord.