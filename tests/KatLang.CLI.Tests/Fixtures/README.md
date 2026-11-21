# Code-link fixtures

Expected payloads for `katlang --code-link` (`src/KatLang.CLI/CodeLink.cs`, `LzString.cs`), made by
katlang.org's own encoder, so the tests need no Node.js. A code link is
`https://katlang.org/#code/<payload>` with `payload = LZString.compressToEncodedURIComponent(source)`
from lz-string 1.5.0; the contract is katlangweb's `docs/code-links.md`.

- `code-link-vectors.json` is a byte-for-byte copy of katlangweb's
  `KatLangWeb.Tests/Fixtures/code-link-vectors.json` at katlangweb commit `9d9bce7` (2026-11-21), the
  test vectors the Playground's own codec is tested against.
- `code-link-cases.json` holds 707 more sources, encoded once on 2026-11-21 with katlangweb's
  `KatLangWeb/wwwroot/js/katlang-code-link.js` over its vendored
  `KatLangWeb/wwwroot/lib/lz-string/1.5.0/lz-string.js` (the codec of the reference encoder
  `tools/katlang-code-link/katlang-code-link.js`), with a sample also run through that encoder. The
  sources are the tutorial's programs, with LF, CRLF, CR and mixed line breaks, tabs and trailing
  spaces; Latvian and other non-ASCII text; code units around U+00FF and U+0100, where the encoding
  switches from 8-bit to 16-bit literals; emoji and other surrogate pairs, and unpaired surrogates;
  `__proto__` and other names JavaScript objects treat specially; repetitions and seeded random text
  across the code-width steps; and sources at the limits: payloads of 8,192 and 8,193 characters,
  sources of 50,000 and 50,001 code units, and the empty program. Each case records the reference
  encoder's verdict (`status`: `ok`, `empty` or `tooLong`) and the payload, also for a source that has
  no link. Its `schema` field describes the three ways a case gives its source.

Both files are expectations, not observations of this repository's code: never regenerate them from
the C# encoder. To add cases, encode them with the reference encoder and review the diff.
