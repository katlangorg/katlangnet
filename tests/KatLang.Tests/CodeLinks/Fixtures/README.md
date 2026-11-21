# Code-link fixtures

Expectations for KatLang code links (`KatLang.CodeLink` in `src/KatLang/CodeLinks/`), made with the
reference implementation of code-link format 1, so the tests need no Node.js. A code link is
`https://katlang.org/#<format>/<payload>`, and its payload is KatLang's own format, specified in
[`docs/design/code-link-format.md`](../../../../docs/design/code-link-format.md). The KatLang tests
(`tests/KatLang.Tests/CodeLinks/`) read all three files; the CLI tests read the first two through the
same loader (`CodeLinkFixtures.cs`, linked as source) to check what `--code-link` and `katlang source`
write for the same programs.

The format is frozen: a link already shared must keep opening, so every payload here is exact. A change
to the encoder that alters one of them is a new format, which only the owner decides. Never regenerate
these files to make a failing test pass.

## Encoding

- `code-link-vectors.json`: the documented example (`100 - 3 * 5 ^ 2`) and ten programs, the sources
  of katlangweb's earlier Playground vectors, with their payloads and links.
- `code-link-cases.json`: 707 sources with the reference encoder's verdict (`status`: `ok`, `empty`,
  `sourceTooLong` or `payloadTooLong`) and the payload, also for a program whose payload is over the
  limit; a program over the source limit is never encoded. The sources are the tutorial's programs,
  with LF, CRLF, CR and mixed line breaks, tabs and trailing spaces; Latvian and other non-ASCII text;
  control characters; emoji and other surrogate pairs, and unpaired surrogates; repetitions and seeded
  random text; and sources at the limits: payloads of exactly 1,970 and 1,971 characters (random text,
  and comment-only programs the CLI tests can run), sources of 20,000 and 20,001 code units, and the
  empty program. Its `schema` field describes the three ways a case gives its source.

## Decoding

`code-link-decode-cases.json` is the decoder oracle: 2,404 inputs with the reference decoder's
verdict, a refusal (named as `CodeLinkRefusal` names it) or a program.

- **Truncations** (1,418): proper prefixes of the payloads of 31 bases (short and long, ASCII and not,
  unpaired surrogates, both limits); all of them for short payloads, a sample for long ones. The
  reference decoder refused every sampled prefix.
- **Mutations** (537): one character replaced or deleted at the start, the middle and the end of the
  same payloads. Each is refused: as damaged, as over the source limit, or as a payload that decodes
  but is not its program's own.
- **Cases** (449): payload lengths around the limit; characters outside the alphabet, inside and
  appended; format numbers this KatLang does not read; wrong and missing check values; extra digits;
  invalid and non-canonical WTF-8 (overlong forms, a surrogate pair written as two surrogates, code
  points above U+10FFFF); programs at and over the source limit, and length fields beyond any program;
  300 random payloads; and links for `TryGetPayload` and `DecodeLink` (other origins, a path, a query,
  no fragment, format numbers that are malformed, too long or unknown, a letter before the number,
  the earlier `#code/` format, another fragment, an empty payload, a second `#`).

The file's `schema` field describes its forms.

## Regenerating

All three files are expectations, not observations of this repository's code: never regenerate them
from the C# encoder or decoder. They were made outside this repository, which has no JavaScript, with
the reference implementation and its generator (`codelink.js` and `generate.js`, deterministic and
seeded), over the frozen primer `src/KatLang/CodeLinks/code-link-primer-1.txt`:

```
node generate.js <output directory>
```

A future format gets fixtures of its own; these stay, so that format-1 links keep opening.
