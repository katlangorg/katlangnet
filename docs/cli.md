# The `katlang` command-line tool

`katlang` runs KatLang programs from a terminal: a program in a file, a program written on the command line, or the program of a link. It is one self-contained executable for Windows, Linux and macOS, on x64 and Arm64, and needs no .NET installation. The language itself is taught in the [tutorial](https://katlang.org/tutorial); to run KatLang from your own .NET code, see the [.NET guide](dotnet.md).

## Contents

1. [Installing](#installing)
2. [Commands](#commands)
3. [Options](#options)
4. [Output and exit status](#output-and-exit-status)
5. [Loading modules](#loading-modules)
6. [Code links and program links](#code-links-and-program-links)
7. [Reproducible randomness](#reproducible-randomness)
8. [Decimal places](#decimal-places)

## Installing

Download the archive for your system from the [latest release](https://github.com/katlangorg/katlangnet/releases/latest): `katlang-cli-<version>-<platform>.zip` for Windows and `katlang-cli-<version>-<platform>.tar.gz` for Linux and macOS, where the platform is `win-x64`, `win-arm64`, `linux-x64`, `linux-arm64`, `osx-x64` or `osx-arm64`. Extract `katlang` (`katlang.exe` on Windows) and put it on your `PATH`. The release's `SHA256SUMS` file lists the SHA-256 checksum of every archive.

## Commands

| Command | What it does |
| --- | --- |
| `katlang run <file\|link>` | Run the program in a file, or the program of a [link](#running-a-program-link). |
| `katlang eval <source>` | Run the program written as the argument. |
| `katlang check <file\|link>` | Check a program for errors without running it. |
| `katlang source <link>` | Write the program of a [link](#reading-a-program-link) to stdout, and run nothing. |
| `katlang --help` | Show the usage and every option. |
| `katlang --version` | Show the KatLang version. |

```text
katlang eval "2 + 3 * 4"
katlang run program.kat
katlang check program.kat
```

KatLang text is written in single quotes only (`'text'`); double-quoted strings and string interpolation are not KatLang syntax. On the command line, wrap a program that contains strings in the shell's double quotes: `katlang eval "'pass', 2 + 3"`.

## Options

| Option | Commands | What it does |
| --- | --- | --- |
| `--allow-loading` | `run`, `eval`, `check` | Let the program download and run modules. Off by default. See [Loading modules](#loading-modules). |
| `--random-seed <integer>` | `run`, `eval` | Reproduce the same random values. See [Reproducible randomness](#reproducible-randomness). |
| `--min-decimal-places <integer>` | `run`, `eval` | Show at least this many digits after the decimal point. See [Decimal places](#decimal-places). |
| `--max-decimal-places <integer>` | `run`, `eval` | Show at most this many digits after the decimal point. See [Decimal places](#decimal-places). |
| `--code-link` | `run`, `eval`, `check` | After the output, write a link that opens the program in the playground. See [Code links and program links](#code-links-and-program-links). |

Each option may be written once, anywhere before a bare `--`. A bare `--` ends the options, so a file or source argument that itself begins with two dashes is written after it (`katlang eval -- "--1"`). `source` takes no options.

## Output and exit status

A program's output goes to stdout and its diagnostics to stderr. The exit status is 0 when the command succeeds and 1 for every failure: a usage error, a file or link that cannot be read, an error in the program, or output over the display limit.

The CLI's `run` and `eval` commands render before writing program output. Display overflow returns exit code 1, writes the complete limit notice once to stderr, and leaves stdout empty. Genuine notice-shaped output remains successful stdout output with exit code 0. Ordinary output keeps its terminating newline; programs with no output rows succeed silently. `check` validates source without executing or rendering it, so valid source that would overflow on execution still passes silently.

`check` also writes warnings to stderr, in the same `[line:column] message` form as errors, and a program whose only diagnostics are warnings passes with exit status 0. KatLang has one warning: a clause written after a catch-all clause of the same conditional algorithm (`F(x) = …` followed by `F(0) = …`), which no call can select. `run` and `eval` run such a program as written and report no warning.

The CLI's `run` and `check` commands enforce KatLang's per-source ceiling (`SourceProcessingLimits.MaxSupportedSourceLength`, 2,097,152 UTF-16 code units) while reading the file, never after reading it whole: the file is decoded incrementally exactly as `File.ReadAllTextAsync` decodes it (UTF-8, or the encoding a byte-order mark names), and as soon as the decoded text exceeds the ceiling the read stops, nothing is parsed, and the command fails with exit code 1 and `Source length exceeds the maximum of 2097152 UTF-16 code units.` on stderr. The limit counts decoded code units, not bytes, and trusts no file metadata, so a growing file, a pipe, or a device is bounded the same way. This is the CLI's own file acquisition; `eval` source and text supplied by other hosts or module downloads are measured by KatLang's front end as before.

## Loading modules

The `katlang` CLI's `--allow-loading` flag is off by default: without it, source that uses `load` or `open 'url'` is rejected with a diagnostic and nothing is fetched, so a plain run never contacts a host that a program names. With it, a module may come from **any public HTTPS host** (the CLI sets `RunOptions.AllowAnyHost`): KatLang hands a load target to the CLI's downloader after its own checks pass — an HTTPS URL without user information whose host is a valid DNS name or IP literal — and the downloader decides the rest. The CLI registers no host operations, so a loaded module can compute but reach nothing outside the program.

The CLI runs inside AI agents, where a link can be pasted or injected by someone else, and such a link must not reach the user's own machine or network. So everything the CLI downloads — a module, or the program a URL operand names (below) — goes through one downloader with one set of guardrails. They belong to the shipped CLI, not to the KatLang package, whose host-supplied downloader contract is unchanged:

- **HTTPS only.** An `http://` address is refused, never upgraded: code is not fetched unprotected in transit, and plain-HTTP internal services, such as the cloud metadata address `169.254.169.254`, stay out of reach.
- **No user information** in the address (`user@`, `user:password@`).
- **Public addresses only.** The CLI resolves the host name itself and refuses every address that is not on the public internet, IP literals included: loopback, private (RFC 1918), carrier-grade NAT, link-local, unique-local IPv6, unspecified, multicast and reserved addresses, and the IPv4-mapped, NAT64 and 6to4 forms of them. It then connects only to an address that passed, so a DNS answer cannot change between the check and the connection. Because the address a proxy would connect to cannot be checked, the system proxy settings are not used: every connection is direct.
- HTTP redirects are refused rather than followed.
- Only a `200 OK` response carries source; every other status, including `204 No Content` and `206 Partial Content`, is a failed download reported in the CLI's own words.
- No cookies, credentials, or other ambient state are sent, and no decompression is negotiated. Every request is HTTP/1.1 with the fixed `User-Agent` `katlang-cli/<version>`.
- Each download is limited to **1 MiB (1,048,576 content bytes)**. This is a fixed CLI transport policy, independent of and intentionally stricter than the library's decoded-source limit: valid source that fits the library limit can still be refused by the CLI. Non-ASCII and non-UTF-8 sources consume the content bytes their encoding requires, including any byte-order mark. An excessive declared `Content-Length` is refused before buffering; a chunked or unknown-length body is refused when a buffer write would exceed the ceiling. The ceiling counts content bytes exposed by `HttpContent`, excluding HTTP headers and chunk framing. No decompression is negotiated or performed. Network read-ahead and the HTTP client's bounded disposal drain are separate from accepted buffer contents.
- Each complete download has one absolute **15-second cancellation deadline** starting before the request and remaining active through name resolution, the connection, headers and body acquisition. Incoming bytes do not restart it, so both stalled and trickling responses are cancelled. Cancellation is cooperative; bounded synchronous text decoding is not preemptible.

These bounds apply per download. KatLang's `SourceProcessingLimits` (decoded per-module source length, aggregate source, module count, import depth) still apply separately to the text the downloader returns. A refused or timed-out module download is reported as an ordinary `load: failed to fetch '<url>': <reason>` diagnostic with exit code 1, where the reason is the CLI's own sentence, for example `its host is not at a public address (127.0.0.1).`, `the server responded with a redirect (HTTP status 302), and redirects are not allowed.` or `the download did not complete within 15 seconds.`

## Code links and program links

With `--code-link`, `run`, `eval` and `check` end with a link to the program they read. After the command's usual output (rows on stdout, diagnostics on stderr), the CLI flushes stdout and writes one last line to stderr:

```
katlang-link: https://katlang.org/#1/<payload>
```

Opening the link shows the program in the KatLang Playground on katlang.org and runs it there. The payload is KatLang's code-link format (see [Code links](dotnet.md#code-links) in the .NET guide), computed by the KatLang library (`CodeLink.Encode`) in the same process as the run. The source is the program text exactly as the command evaluates it — the `eval` argument, the file's text after the one leading byte order mark the CLI drops, or the program a link gave (below) — as UTF-16 code units, with line breaks, tabs, trailing spaces and a final line break kept as written; the payload is never percent-encoded.

- The line is written whatever the program does once the CLI has its source: success, a KatLang error at any stage, output over the display limit, even a cancellation. A usage error, or a file or link that cannot be read, stops the command before it has the source and writes no link line.
- A program that cannot be a code link gets `katlang-link: none: <reason>` instead: an empty program, one longer than 20,000 UTF-16 code units, or one whose payload would be longer than 1,970 characters.
- The option changes neither stdout nor the exit status; without it the CLI computes and writes nothing extra. Like every option, it may be written once, anywhere before a bare `--`.
- The link carries the program's source and nothing else (no results, settings or identity), so anyone who has it can read the program.

For example, `katlang eval --code-link "100 - 3 * 5 ^ 2"` prints `25` on stdout and `katlang-link: https://katlang.org/#1/4MWjDBlNE4PH` on stderr.

### Running a program link

`run`, `check` and `source` take a **program link** wherever they take a file or a link. For `run` and `check`, an operand that starts with `https://` or `http://` (in any letter case) is a link, and every other operand is a file path as before, also after a bare `--`; a file whose path really starts that way can still be named as `./https:…`. `source` reads every operand as a link. There are two kinds of link, told apart from the address, and only the way the program text is obtained differs. Once the text is read, the command does exactly what it does for a file that holds the same text — options, output rows, diagnostics, exit status, limits and cancellation — and `--code-link` writes the link of the text that was read.

**A code link** carries the program in the address itself: a link with a `#<format>/<payload>` fragment, whatever origin, path or query comes before the `#`. The CLI decodes it (`CodeLink.DecodeLink`) and never touches the network.

```
katlang run "https://katlang.org/#1/4MWjDBlNE4PH"
```

prints `25`, and with `--code-link` also writes `katlang-link: https://katlang.org/#1/4MWjDBlNE4PH`, the link's canonical form, to stderr.

- The program runs exactly as the link carries it, as UTF-16 code units. Nothing is stripped: every line break stays, and so does a leading U+FEFF, which a file would drop. This is how the Playground runs it.
- A link that carries no program fails with exit status 1, nothing on stdout, and `katlang: invalid code link: <reason>` on stderr (the reasons are listed under `source`, below). There is no usage hint, and no `katlang-link:` line even with `--code-link`, because no source was read, exactly as for a missing file.
- A link with a `#` is never downloaded. A fragment never reaches a server, so it can only mean a program carried in the link: a fragment that starts no code link, such as one in the earlier `#code/` format, is an invalid code link (`it has no #<format>/<payload> fragment.`), not a download of the address before it.
- A code link can carry an unpaired surrogate, which UTF-8 cannot represent. `run` and `check` evaluate such a program as it is. A string value that holds one is written to stdout with U+FFFD, the replacement character, in its place, and a diagnostic shows it as a visible `\uXXXX` escape or names its code point, so neither stream ever carries one.

**A program URL** is any other link: the program is downloaded as text from it. Downloading the program that the operand names is the request the command makes, so it needs no option; `--allow-loading` stays the opt-in for the modules that a program names.

```
katlang run "https://katlang.org/a/019ead4b-d41d-7564-ba11-c177f917a0fe"
katlang run "https://raw.githubusercontent.com/<user>/<repository>/main/program.kat"
```

- The download passes the guardrails of [Loading modules](#loading-modules): HTTPS only, no user information, a public address only, no redirects, only `200 OK`, 1 MiB and 15 seconds.
- Only KatLang source text runs. The response must be `text/plain`, in any character set, or `application/octet-stream`, which many servers send for an unknown extension such as `.kat`. Anything else — `text/html`, `application/json`, an image, or no `Content-Type` at all — is refused from the response headers, before anything runs. The text is decoded as the response states (its character set, else a byte order mark, else UTF-8), and one leading byte order mark is dropped, as for a file. A `text/plain` body that is not valid KatLang is a program with errors: it is reported with KatLang's own diagnostics, exactly as for a file.
- A program shared from the Playground has a page, `https://katlang.org/a/<id>`, which is HTML, and a raw-code address, `https://katlang.org/api/a/<id>`, which is the same program as text. Given the page, on katlang.org or a subdomain of it, the CLI downloads the raw-code address on the same host; a query and a trailing `/` are dropped, and the id is a GUID in either letter case. On any other host `/a/…` is an ordinary path, downloaded as given.
- With `--code-link`, a program URL gets a code link of the downloaded text: a snapshot, which later edits to the shared program do not change.
- A link that gives no program fails with exit status 1, nothing on stdout, no usage hint and no `katlang-link:` line, and one line on stderr. The line quotes the link as given, except that user information is shown as `<redacted>`:
  - `katlang: not found: '<link>'.` for a `404`. For a shared program that means private, unshared or unknown.
  - `katlang: not KatLang source: '<link>' returned text/html.` for a response that is not source text. It names what came back: the media type, `no Content-Type`, or `a Content-Type that cannot be read`.
  - `katlang: cannot download '<link>': <reason>` for everything else, where the reason is one of these sentences:
    - `it is not a valid address.`
    - `only HTTPS addresses are downloaded.`
    - `it contains user information ('user@' or 'user:password@').`
    - `its host is not at a public address (<address>).`
    - `its host name could not be resolved.`
    - `the connection failed.`
    - `a secure connection could not be established.`
    - `the request failed.`
    - `the server responded with a redirect (HTTP status <status>), and redirects are not allowed.`
    - `the server responded with HTTP status <status>; only 200 (OK) is accepted.`
    - `the declared Content-Length of <bytes> bytes exceeds the 1048576-byte limit.`
    - `the response body exceeds the 1048576-byte limit.`
    - `the download did not complete within 15 seconds.`
    - `the response names a character set that is not supported.`

A module download that fails reports the same sentence in its diagnostic, `load: failed to fetch '<url>': <reason>`.

### Reading a program link

`katlang source <link>` writes the program of a link of either kind to stdout, and runs nothing.

```
katlang source "https://katlang.org/#1/4MWjDBlNE4PH"
katlang source "https://katlang.org/a/019ead4b-d41d-7564-ba11-c177f917a0fe"
katlang source "<link>" > program.kat
```

- stdout receives the program exactly as it was read. No line break is added, and control characters are written raw, as `cat` writes a file, so redirecting stdout reproduces the program byte for byte as UTF-8. (Windows PowerShell 5.1 re-encodes what any native program writes to a redirected stdout, as UTF-16; use PowerShell 7.4 or later, `cmd` or a POSIX shell.) Look at a program from a link you do not trust in a file or an editor rather than on a terminal. To run the program, give the link to `run` instead of saving it: the program then runs exactly as the link has it, with no file and no shell in between.
- A code link is read exactly as given, with nothing trimmed or decoded, and by its fragment alone: any origin, path and query may come before the `#`. It gets the checks above (`CodeLink.DecodeLink`). An operand that is neither a web address nor a code link is refused as an invalid code link.
- A program URL is downloaded under the rules above, and fails with the same three lines.
- A code link that carries no program is refused: exit status 1, nothing on stdout, and one line on stderr, `katlang: invalid code link: <reason>`. The reason is one of these sentences:
  - `it has no #<format>/<payload> fragment.`
  - `its format is not one this KatLang reads; a newer KatLang may read it.`
  - `its payload is empty.`
  - `its payload is longer than 1,970 characters.`
  - `its payload has a character that code links do not use.`
  - `its payload is damaged or cut short.`
  - `its program is longer than 20,000 UTF-16 code units.`
  - `its payload does not re-encode to itself, so it was changed.`
- A code link can carry an unpaired surrogate, which UTF-8 cannot represent. `source` does not print such a program, because the file would not be the program: it fails in the same way, with `katlang: cannot print the program: it contains an unpaired surrogate, which UTF-8 cannot represent.` (`run` and `check` evaluate such a program, as described above.)
- `source` takes exactly one argument and no option: it has no program to load modules for, evaluate, display or link, so each command option is a usage error for it (`option '--code-link' is not valid for 'source': source reads a link and runs nothing.`).

## Reproducible randomness

Without a seed, KatLang's random operations (`Math.Random`, `random`, `Math.RandomInt` and `randomInt`) may give different values on every run. With `--random-seed`, `run` and `eval` reproduce the same random values for the same program, seed and KatLang version:

```
katlang run <file> --random-seed <integer>
katlang eval <source> --random-seed <integer>
```

`--random-seed` takes any signed 64-bit integer as the next token (`--random-seed -5` and `--random-seed +5` are different seeds; `--random-seed=5` is not accepted) and is refused by `check`, which does not evaluate. KatLang randomness is not cryptographically secure. The [.NET guide](dotnet.md#reproducible-randomness) describes exactly what a seed reproduces.

## Decimal places

`run` and `eval` take two display settings, the fewest and the most digits shown after the decimal point, each an integer from 0 through 99:

```
katlang eval --max-decimal-places 3 "1 / 7"
katlang eval --min-decimal-places 2 --max-decimal-places 2 "19.99 * 3"
katlang run --max-decimal-places 6 program.kat
```

They change only how numbers are displayed, never a value or a calculation. Each one is combined with the program's own `MinDecimalPlaces` or `MaxDecimalPlaces` property, and when both are set the smaller count applies. A minimum above the maximum is an error, and two options that contradict each other are a usage error. The [.NET guide](dotnet.md#decimal-places-minimum-maximum-source-and-host) gives the full rules.

Like `--random-seed`, each decimal-places option takes its value as the next token (`--max-decimal-places=2` is not accepted, and a leading sign or zeros such as `+2` or `02` spell the same integer), may be written at most once, and is refused by `check`, which validates the source's syntax and front-end semantics but does not evaluate — so it never runs the engine's reads either.
