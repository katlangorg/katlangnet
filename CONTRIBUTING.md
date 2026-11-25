# Contributing

Thank you for your interest in contributing to the KatLang project.

The KatLang project is released under the MIT License with an
additional patent grant. By contributing, you help improve the
project for everyone.

## Build Prerequisites

Install a stable .NET SDK version 11.0.100 or later. [global.json](global.json)
selects the highest eligible SDK installed on your machine. CI and release
workflows provision the baseline SDK from the same file. The projects target
`net11.0`, and running the framework-dependent builds or tests requires the
.NET 11 runtime.

Open [the .NET solution](dotnet/KatLang.slnx) in your IDE, or build it from the
repository root with `dotnet build ./dotnet/KatLang.slnx`.

## Changing the language

Start with the [Lean model](lean/KatLang.lean) and the [rules for the affected subsystem](docs/design/language-rules/README.md). The [.NET alignment guide](dotnet/src/KatLang/SEMANTIC-ALIGNMENT.md) identifies which changes also need a Lean update. Update the [grammar](KatLang.ebnf) for syntax changes and the [tutorial](tutorial.md) when a change affects users.

Add a regression case to the appropriate [shared feature file](conformance/README.md) with a stable ID and hand-written expectations. The .NET suite reads those files directly, and the [Lean differential checks](docs/design/executable-language-spec.md) use the same expectations for the cases the model covers. Use the [validation guide](docs/testing-and-validation.md) to select the checks and regenerate affected artifacts.

Update the [Semantic Constitution](docs/constitution/constitution.md) and its affected companion records in the same change. When a current rule depends on a review finding, record the finding and link to a tracked regression case or Lean declaration so another contributor can verify it from a fresh clone.

## License of Contributions

By submitting a contribution (including but not limited to code,
documentation, tests, or examples), you agree that your contribution
is provided under the MIT License.

You represent that you have the right to submit the contribution and
that it does not infringe the rights of any third party.

All accepted contributions must be licensed under the MIT License.
Contributions submitted under alternative license terms or with
additional restrictions cannot be accepted.

This project does not require a Contributor License Agreement (CLA).

## No Additional Requirements

Contributors are not required to agree with or endorse any belief,
statement, or dedication expressed elsewhere in this project.

Contributions are welcome from individuals of any background.

## Creating Additional KatLang Libraries

Contributors are welcome to experiment with and develop additional
libraries, tools, or implementations related to KatLang.

If you are interested in creating a new KatLang library, official
implementation, or reusable component intended for broader adoption,
you are encouraged to contact Logics Research Centre SIA to discuss
coordination, naming, and potential reuse of patented technology.

This is not a requirement for personal or experimental work, but
helps ensure clarity, compatibility, and long-term sustainability
of the KatLang project.

## Code of Conduct

Please be respectful and constructive when participating in the
project. See [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md) for details.
