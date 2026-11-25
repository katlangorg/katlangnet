# KatLang code-link format

A code link carries a KatLang program in a URL: `https://katlang.org/#<format>/<payload>`, for
example `https://katlang.org/#1/4MWjDBlNE4PH` for `100 - 3 * 5 ^ 2`. This document specifies the
link and its format 1 completely enough to implement them again. The implementation is
`dotnet/src/KatLang/CodeLinks/` (`KatLang.CodeLink`); the fixtures in
`dotnet/tests/KatLang.Tests/CodeLinks/Fixtures/` were made with an independent reference implementation of
this text and pin its results exactly.

## Versions

A link names the format of its payload by number, before the payload. Format 1 is the only one so
far.

A format is frozen once released: a link already shared must keep opening, so a format never
changes, not even to follow a language change. In particular the primer (§ The primer) is never
edited. A new format is introduced only by the owner's decision: it gets the next number, the
encoder writes it from then on, and readers keep reading every earlier format. A reader refuses a
link whose number names no format it reads (`UnsupportedVersion`): a link made by a newer KatLang,
or a changed one.

Format 1 replaced the lz-string links of `#code/<payload>` (November 2026, before any release that
promised them); those are not read.

## The link

- A link's **fragment** is everything after its first `#`. A code link's fragment is the **format
  number** (one to nine ASCII decimal digits, the first not `0`), a `/`, and the **payload**, the rest of
  the fragment exactly as written: nothing is trimmed and nothing is percent-decoded. Any other
  fragment is not a code link (`NotACodeLink`): no number, a leading zero, a tenth digit, a sign or
  a letter before the number (the earlier `#code/` links among them). Only the fragment is read;
  the origin, path and query are the host's own route policy.
- The canonical link is `https://katlang.org/#`, the format number, `/` and the payload.
- A payload is **digits** of base64url (RFC 4648 § 5): `A`–`Z` are 0–25, `a`–`z` 26–51, `0`–`9`
  52–61, `-` 62 and `_` 63. URL fragments allow all of them as they are, so a payload is never
  percent-encoded.
- Format 1: the payload is the digits of one arithmetic-coded stream (§ The stream).

## Limits

- A program is 1 to 20,000 UTF-16 code units long.
- A payload is at most 1,970 characters long (the format number and its `/` not counted), so a
  canonical link is at most 1,993 characters: under 2,000, the length beyond which some browsers,
  mail and chat programs cut links short or refuse them, with a small reserve.
- A program's bytes (§ Bytes) number at most 60,000, three per code unit.

## Bytes

The stream carries a program's **WTF-8** bytes: its UTF-16 code units are read as code points (a
high surrogate followed by a low surrogate is one supplementary code point; every other surrogate
is a code point of its own, U+D800 to U+DFFF), and each code point is written as UTF-8 writes it,
surrogate code points in three bytes (`ED A0..BF 80..BF`). Every UTF-16 string, unpaired surrogates
included, has exactly one byte form.

A reader takes the bytes strictly: no overlong form, no code point above U+10FFFF, no stray
continuation byte, nothing missing at the end. A surrogate pair written as two three-byte sequences
reads as the pair; its own bytes are the four-byte form, so its payload is not canonical (§ Reading
a link).

## The stream

The stream is a sequence of bits, each coded with a probability that it is 1, in 1 to 4095 of 4096:

1. **The length** n ≥ 1, the number of bytes, in Elias gamma code: ⌊log₂ n⌋ zero bits, then the
   ⌊log₂ n⌋ + 1 binary digits of n, the most significant first (which is 1). Each bit has
   probability 2048.
2. **The bytes**, each as its 8 bits from the most significant, each bit with the probability the
   model gives (§ The model), which then learns that bit.
3. **The check value**: the low 12 bits of the CRC-32 of the bytes, the most significant first, each
   with probability 2048. The CRC is ISO-HDLC, the CRC of zlib and PNG: polynomial `0xEDB88320`
   reflected, initial value and final XOR `0xFFFFFFFF` (CRC-32 of `123456789` is `0xCBF43926`).

### The arithmetic coder

A carryless binary coder on a 30-bit interval, writing base64url digits. All quantities are
non-negative integers.

- The state is `low = 0`, `high = 2^30 − 1`.
- To code a bit b with probability p (of b = 1, in 4096ths):
  `mid = low + ⌊(high − low) × p / 4096⌋`; if b = 1 then `high = mid`, else `low = mid + 1`. Then,
  while `⌊low / 2^24⌋ = ⌊high / 2^24⌋`: write the digit `⌊high / 2^24⌋`, and set
  `low = (low × 64) mod 2^30`, `high = (high × 64) mod 2^30 + 63`.
- To finish: for k = 0, 1, …, 5, let `u = 64^(5 − k)` and `v = ⌈low / u⌉ × u`; at the first k with
  `v ≤ high`, write the k most significant of v's five digits (digit i, from 0, is
  `⌊v / 2^(24 − 6i)⌋ mod 64`), and stop.

A **decoder** keeps the same `low` and `high` and a value x, the first five digits of the stream as
a 30-bit number, a digit past the stream's end counting as 0. To read a bit with probability p it
computes `mid` as above, takes b = 1 if x ≤ mid and b = 0 otherwise, updates `low` and `high` as the
encoder does, and at each shift also sets `x = (x × 64) mod 2^30 + d`, d the next digit. A canonical
stream has at least as many digits as the coder shifts, so a decoder refuses the payload as
`Damaged` as soon as it would shift more times than the stream has digits.

## The model

The model predicts each bit of the bytes. It mixes seven context models and a match model in the
logistic domain. Every quantity is an integer, every hash is unsigned 32-bit arithmetic modulo 2^32,
and a shift of a negative number rounds towards −∞.

### Logistic functions

- The **stretch domain** is ln(p / (1 − p)) × 256, from −2047 to 2047.
- `squash(d)`, a probability in 1..4095 of 4096: clamp d to −2047..2047, let `e = d + 2048`,
  `j = e >> 6`, `w = e & 63`, and take `(P[j] × (64 − w) + P[j + 1] × w + 32) >> 6`, clamped to
  1..4095, where P is these 65 numbers, `round(4096 / (1 + e^(−(i − 32) / 4)))` clamped to 1..4095
  for i = 0..64:

  ```
  1, 2, 2, 3, 4, 5, 6, 8, 10, 13, 17, 21, 27, 35, 45, 58, 74, 94, 120, 153, 194, 246, 311, 391,
  488, 606, 747, 912, 1102, 1314, 1546, 1793, 2048, 2303, 2550, 2782, 2994, 3184, 3349, 3490,
  3608, 3705, 3785, 3850, 3902, 3943, 3976, 4002, 4022, 4038, 4051, 4061, 4069, 4075, 4079,
  4083, 4086, 4088, 4090, 4091, 4092, 4093, 4094, 4094, 4095
  ```

- `stretch(p)` for p = 0..4095 is a table: for d from −2047 to 2047 in order, every p not yet set
  with p ≤ squash(d) is set to d; every p left is 2047.

### Hashing

- `mix(x)`, the MurmurHash3 finalizer: `x ^= x >> 16; x *= 0x85EBCA6B; x ^= x >> 13;
  x *= 0xC2B2AE35; x ^= x >> 16`.
- `step(h, c, k) = mix(h + (c + 1) × 0x9E3779B1 + k × 2^20)`.

### State

- **Seven context tables** of 2^17 slots each; a slot holds a probability P (16 bits, of the bit
  being 1, in 65536ths; initially 32768) and a count N (initially 0).
- **Weights**: 48 sets of 9 integers (16 fractional bits), each initially 19661.
- **Match probabilities**: 64 slots, P initially 49152 and N initially 0.
- **A match table** of 2^16 positions, initially 0; the history of every byte so far (the primer's,
  then the program's); the match pointer and length (initially 0).
- The **partial byte** c0 (1 at a byte's start, then 1 followed by the bits read so far), the bit
  index (0 to 7), and the word hash (initially 0).
- The **adaptation rate** of a count n is `R[n] = ⌊65536 / (2n + 3)⌋`, applied as a fraction of
  32768.

### Contexts

At the start and after each byte, with c1 the latest byte, c2 the one before it and so on (a byte
before the history's start counts as 0):

- h0 = 0; h1 = step(0, c1, 1); h2 = step(h1, c2, 2); h3 = step(h2, c3, 3); h4 = step(h3, c4, 4);
  h5 = step(step(h4, c5, 5), c6, 6);
- h6 = step(0x7777, c1, 7) when the word hash is 0, and step(word, 0, 8) otherwise.

### Predicting a bit

1. For each context i = 0..6: its slot is `mix(h_i XOR (c0 × 0x27D4EB2F)) >> 15` in table i, and its
   input is `stretch(P >> 4)` of that slot. The **order** is the largest i in 1..5 whose slot has
   N > 0, or 0.
2. **The match input** is 0, unless the match length is positive and the expected byte (the history
   byte at the match pointer) agrees with c0 on the bits read so far
   (`((expected | 256) >> (8 − bit index)) = c0`). Then the expected bit is
   `(expected >> (7 − bit index)) & 1`, the match context is `min(length, 63)`, and the input is
   `stretch(P >> 4)` of that match slot, negated when the expected bit is 0. When the length is
   positive but the bits disagree, the length becomes 0.
3. **The bias input** is 256.
4. The weight set is `(order × 8 + bit index)`. The prediction is
   `p = squash((Σ weight_i × input_i) >> 16)` over the nine inputs.

### Learning a bit b

1. With `err = b × 4096 − p`, each weight of the set becomes
   `clamp(weight + ((input × err) >> 10), −2^22, 2^22)`.
2. Each context slot: `P += ((b ? 65535 : 0) − P) × R[N] >> 15`; then N increases by 1 up to 60.
3. If there was an expected bit: the match slot learns whether it was right, in the same way with
   N up to 255, and if it was wrong the match length becomes 0.
4. `c0 = c0 × 2 + b`, and the bit index increases. After the eighth bit, the byte `c0 & 255` ends:

### Ending a byte

1. The byte is appended to the history; c0 = 1 and the bit index is 0.
2. If the match length is positive, the match pointer and the length increase by 1 (the length up
   to 65535).
3. If the history holds at least 5 bytes: `m = step(…step(step(0, c1, 17), c2, 18)…, c5, 21) >> 16`.
   If the match length is 0 and the match table's entry m is a position q > 0, count L, the bytes
   that agree going back from q − 1 and from the latest byte, up to 32 (and not before the history's
   start); if L ≥ 5, the match length is L and the pointer q. Then the entry m becomes the history's
   length.
4. The word hash becomes `((word XOR byte) × 0x01000193) | 1` when the byte is `0`–`9`, `A`–`Z`,
   `a`–`z`, `_` or 128 or above, and 0 otherwise.
5. The contexts are computed again.

### The primer

Before a stream is coded, the model reads the 15,102 bytes of `code-link-primer-1.txt` (embedded in
the KatLang assembly; SHA-256 `71cf25503940d337838bc2e4d58c21880eb27e22e8a14335bb95b165fa489fdf`):
every bit is predicted and then learned exactly as a coded bit is, and the state it leaves is where
every stream of format 1 starts. The primer is a header line, a vocabulary of KatLang's builtins,
Math members, keywords and idioms, and the KatLang examples of the tutorial as of 2026-11-21, so a
short program is cheap from its first byte. It is part of the format and never edited.

## Encoding

`CodeLink.Encode` makes these checks in order: an empty program has no link; a program longer than
20,000 code units has none and is never encoded; otherwise its payload is made, and a payload longer
than 1,970 characters is no link either.

## Reading a link

A reader makes these checks in order, and the first that fails is the refusal
(`CodeLinkRefusal`):

1. The link has a code-link fragment, `<format>/<payload>` (`NotACodeLink`; a link reader only).
2. The format number names a format the reader reads (`UnsupportedVersion`).
3. The payload is not empty (`EmptyPayload`) and at most 1,970 characters long (`PayloadTooLong`).
4. Every character is a digit (`InvalidCharacter`).
5. Read the stream in order. The 16th leading zero in the length field gives `SourceTooLong`
   immediately, as does a completed length above 60,000 bytes. An invalid WTF-8 byte gives
   `Damaged`, and a byte that takes the text past 20,000 code units gives `SourceTooLong`.
   An incomplete final code point or a checksum mismatch gives `Damaged`. At any bit, the
   decoder returns `Damaged` if it needs to shift more times than the payload has digits.
6. Re-encode the program in the format the link names. Its payload must match the
   input exactly (`NotCanonical`). This checks extra digits, a longer flush, and a surrogate pair
   written as two surrogate code points.

The checksum and canonical encoding detect many edits. An edit that produces a canonical payload
for a different program passes both checks.

The work is linear in the announced length, at most 60,000 bytes, and reading stops at the first
byte that cannot belong to a link.
