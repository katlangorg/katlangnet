import Std.Data.HashMap
import KatLang

/-!
# `kl-struct-v1` exporter (test-side; KL-07 pilot)

Renders a COMPLETED Lean `Result` as `kl-struct-v1` text, byte-identical to the C# encoder
`MetamorphicStructuralIdentity.Encode`
(`fuzz/KatLang.ParserFuzz/Metamorphic/MetamorphicStructuralIdentity.cs`) on the values both
engines can represent. This is maintained TEST code: `KatLang.lean` does not use it, and the format
belongs to the C# encoder (`docs/design/differential-observations.md`); a mismatch is fixed
here, never by changing the format.

Format: `kl-struct-v1:<n>:` followed by exactly `n` node definitions. A node id is the
definition's zero-based position, and the root is the last definition. Each definition is one of:

- `n<len>:<number>`: an atom in its canonical Decimal128 equality class. A Lean atom is an
  `Int`, so the class text is `0`, or `[-]<coefficient>e<exponent>` with the coefficient's
  trailing zeros moved into the exponent. Lean `1200` reads `12e2`, as C# `1200` and `1200.00` do.
- `b0` / `b1`: a Boolean.
- `t<len>:<text>`: a string of `len` UTF-16 code units. A Lean string is a sequence of Unicode
  scalar values, so a scalar outside the BMP contributes its surrogate pair (two units).
  Printable ASCII is written as itself except `\` (written `\\`), and every other unit is
  written `\uXXXX` (uppercase hex).
- `s<count>:<id>,...;` / `l<count>:<id>,...;`: a sequence / exact list over earlier ids, each id
  followed by `,` and the whole terminated by `;` (`s0:;` is `()`, `l0:;` is `[]`).

The table is canonical: ids are assigned in left-to-right post-order of first completion, and
each definition is interned once by its text. A shared subtree and two independently built
equal subtrees therefore give the same text.

COVERAGE: equal text means structurally equal completed values that both engines can represent.
It does NOT cover:
- Decimal128 representation (the spelling `1.0` against `1.00`): the neutral text and C#-side
  checks keep that;
- unpaired UTF-16 surrogates: a Lean `String` cannot hold them, and `LeanAstEncoder` refuses
  them at the Lean string boundary;
- host-visible object identity (KL-01): equal subtrees give equal text, whatever their CLR identity.

A value holding a call reference or argument view never leaves a run (`Result.containsCallRef`)
and has no identity (`none`), just as the C# encoder refuses one.
-/

namespace StructuralIdentity
open KatLang

/-- The format identifier every encoding starts with (C#: `MetamorphicStructuralIdentity.Version`). -/
def version : String := "kl-struct-v1"

/-- The canonical class text of an integer atom: `0`, or `[-]<c>e<k>` where `c` has no trailing
    zero (C#: `CanonicalNumber` on an integral Decimal128). -/
def canonicalInt (n : Int) : String :=
  if n == 0 then "0"
  else
    let digits := Nat.toDigits 10 n.natAbs
    let coefficient := (digits.reverse.dropWhile (· == '0')).reverse
    let exponent := digits.length - coefficient.length
    (if n < 0 then "-" else "") ++ String.ofList coefficient ++ "e" ++ toString exponent

/-- The UTF-16 code units of one Unicode scalar value: itself in the BMP, otherwise its
    surrogate pair. -/
def utf16Units (c : Char) : List Nat :=
  let v := c.toNat
  if v < 0x10000 then [v]
  else
    let w := v - 0x10000
    [0xD800 + w / 0x400, 0xDC00 + w % 0x400]

/-- One uppercase hexadecimal digit. -/
def hexDigit (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (55 + d)

/-- Four uppercase hexadecimal digits of one code unit. -/
def hex4 (u : Nat) : String :=
  String.ofList [hexDigit (u / 4096 % 16), hexDigit (u / 256 % 16), hexDigit (u / 16 % 16), hexDigit (u % 16)]

/-- One escaped UTF-16 code unit. -/
def escapeUnit (u : Nat) : String :=
  if u == 0x5C then "\\\\"
  else if 0x20 ≤ u ∧ u ≤ 0x7E then String.singleton (Char.ofNat u)
  else "\\u" ++ hex4 u

/-- A string definition `t<len>:<escaped>` (C#: `QuoteText`), framed in UTF-16 code units. -/
def quoteText (s : String) : String :=
  let units := s.toList.flatMap utf16Units
  "t" ++ toString units.length ++ ":" ++ String.join (units.map escapeUnit)

/-- A number definition `n<len>:<class>`. -/
def numberDefinition (n : Int) : String :=
  let text := canonicalInt n
  "n" ++ toString text.length ++ ":" ++ text

/-- A structure definition `s`/`l` `<count>:<id>,...;` over earlier ids. -/
def structureDefinition (tag : String) (ids : Array Nat) : String :=
  tag ++ toString ids.size ++ ":" ++ ids.foldl (fun text id => text ++ toString id ++ ",") "" ++ ";"

/-- The interned definition table of one encoding. -/
structure Table where
  definitions : Array String := #[]
  ids : Std.HashMap String Nat := {}

/-- The id of `definition`: its existing id, or the next id when it is new. -/
def Table.intern (table : Table) (definition : String) : Table × Nat :=
  match table.ids[definition]? with
  | some id => (table, id)
  | none =>
      let id := table.definitions.size
      ({ definitions := table.definitions.push definition, ids := table.ids.insert definition id }, id)

mutual
  /-- Post-order walk: the children left to right, then the node's own definition. -/
  def walk : Result → Table → Table × Nat
    | .atom n, table => table.intern (numberDefinition n)
    | .bool b, table => table.intern (if b then "b1" else "b0")
    | .str s, table => table.intern (quoteText s)
    | .sequenceValue items, table =>
        let (table, ids) := walkItems items table #[]
        table.intern (structureDefinition "s" ids)
    | .listValue items, table =>
        let (table, ids) := walkItems items table #[]
        table.intern (structureDefinition "l" ids)
    -- Unreachable from `encode`, which refuses a value holding either.
    | .callRef _, table => (table, 0)
    | .argView _, table => (table, 0)
    -- A lazy list form (issue #204) is run-internal too: `encode` refuses it.
    | .deferred _, table => (table, 0)
    | .pendingList _, table => (table, 0)

  /-- The ids of the items, in order. -/
  def walkItems : List Result → Table → Array Nat → Table × Array Nat
    | [], table, ids => (table, ids)
    | item :: rest, table, ids =>
        let (table, id) := walk item table
        walkItems rest table (ids.push id)
end

/-- The `kl-struct-v1` text of a completed value; `none` for a value holding a call reference or
    argument view. The root is the last definition, as C#'s `Render` requires. -/
def encode (value : Result) : Option String :=
  if value.containsCallRef || value.isLazy then none
  else
    let (table, rootId) := walk value {}
    if rootId + 1 == table.definitions.size then
      some (version ++ ":" ++ toString table.definitions.size ++ ":" ++ String.join table.definitions.toList)
    else none

/-! ## Hand-reviewed examples

Each expected text below was written by hand from the format rules above and reviewed against
them; it is not observed output. `StructuralIdentityExporterTests` checks that each one is also the
C# encoder's text of the same value. The generated `HostParentDifferential.lean` cross-checks the
exporter against the C# encoder on C#-built examples and on every successful host-parent case. -/

-- Number classes. Lean atoms are integers: zero, negatives, and trailing decimal zeros moved into
-- the exponent (Lean 1200, like C# 1200 and 1200.00, is the class `12e2`). C# checks the fractional
-- class (`1.5` and `1.50` read `15e-1`); Lean has no fractional atom.
#guard canonicalInt 0 == "0"
#guard canonicalInt 7 == "7e0"
#guard canonicalInt 10 == "1e1"
#guard canonicalInt 1200 == "12e2"
#guard canonicalInt (-5) == "-5e0"
#guard canonicalInt (-120) == "-12e1"
#guard canonicalInt 1000000000000000000000000000000000000000 == "1e39"
#guard encode (.atom 0) == some "kl-struct-v1:1:n1:0"
#guard encode (.atom 7) == some "kl-struct-v1:1:n3:7e0"
#guard encode (.atom 1200) == some "kl-struct-v1:1:n4:12e2"
#guard encode (.atom (-5)) == some "kl-struct-v1:1:n4:-5e0"
#guard encode (.atom (-120)) == some "kl-struct-v1:1:n5:-12e1"

-- KL-07: both lists have the neutral text `L['a', 'b']`; their identities differ.
#guard encode (.listValue [.str "a", .str "b"]) == some "kl-struct-v1:3:t1:at1:bl2:0,1,;"
#guard encode (.listValue [.str "a', 'b"]) == some "kl-struct-v1:2:t6:a', 'bl1:0,;"

-- `()` against `[]`, and Booleans against numbers and strings.
#guard encode (.sequenceValue []) == some "kl-struct-v1:1:s0:;"
#guard encode (.listValue []) == some "kl-struct-v1:1:l0:;"
#guard encode (.listValue [.bool true, .bool false]) == some "kl-struct-v1:3:b1b0l2:0,1,;"
#guard encode (.listValue [.atom 1, .str "1", .bool true]) == some "kl-struct-v1:4:n3:1e0t1:1b1l3:0,1,2,;"

-- Strings: a backslash is doubled; a quote, a space and `~` are printable ASCII; a line feed and a
-- tab are escaped; `é` is one BMP unit; U+1F600 and U+10437 are surrogate pairs, and the length
-- counts UTF-16 units.
#guard encode (.str "a\\b") == some "kl-struct-v1:1:t3:a\\\\b"
#guard encode (.str "\"q\" ~") == some "kl-struct-v1:1:t5:\"q\" ~"
#guard encode (.str "a\nb\t") == some "kl-struct-v1:1:t4:a\\u000Ab\\u0009"
#guard encode (.str "😀") == some "kl-struct-v1:1:t2:\\uD83D\\uDE00"
#guard encode (.str "é𐐷x") == some "kl-struct-v1:1:t4:\\u00E9\\uD801\\uDC37x"

-- Unit boundaries, checked on the exporter's helpers only: `LeanAstEncoder` has no reviewed Lean
-- spelling for a control character other than a line feed or a tab, so no C#-built example
-- carries DEL or U+001F. The printable range is exactly U+0020..U+007E, and the BMP ends at U+FFFF.
#guard escapeUnit 0x1F == "\\u001F"
#guard escapeUnit 0x20 == " "
#guard escapeUnit 0x7E == "~"
#guard escapeUnit 0x7F == "\\u007F"
#guard escapeUnit 0x5C == "\\\\"
#guard escapeUnit 0xFFFF == "\\uFFFF"
#guard utf16Units (Char.ofNat 0xFFFF) == [0xFFFF]
#guard utf16Units (Char.ofNat 0x10000) == [0xD800, 0xDC00]
#guard utf16Units (Char.ofNat 0x10FFFF) == [0xDBFF, 0xDFFF]
#guard quoteText "a\x7F" == "t2:a\\u007F"

-- Nested lists and sequences, in post-order.
#guard encode (.sequenceValue [.atom 1, .listValue [.atom 2, .sequenceValue []], .listValue []])
  == some "kl-struct-v1:6:n3:1e0n3:2e0s0:;l2:1,2,;l0:;s3:0,3,4,;"

-- Equal subtrees built with different sharing give one text, and a repeated value is defined once,
-- also across levels.
def sharedPair : Result :=
  let pair := Result.listValue [.atom 1, .str "a"]
  .sequenceValue [pair, pair]
def independentPair : Result :=
  .sequenceValue [.listValue [.atom 1, .str "a"], .listValue [.atom 1, .str "a"]]
#guard encode sharedPair == some "kl-struct-v1:4:n3:1e0t1:al2:0,1,;s2:2,2,;"
#guard encode independentPair == some "kl-struct-v1:4:n3:1e0t1:al2:0,1,;s2:2,2,;"
#guard encode (.listValue [.atom 7, .atom 7]) == some "kl-struct-v1:2:n3:7e0l2:0,0,;"
#guard encode (.listValue [.listValue [.atom 1], .atom 1]) == some "kl-struct-v1:3:n3:1e0l1:0,;l2:1,0,;"

-- Multi-digit ids, counts and string lengths.
#guard encode (.listValue ((List.range 11).map fun i => .atom (Int.ofNat i)))
  == some "kl-struct-v1:12:n1:0n3:1e0n3:2e0n3:3e0n3:4e0n3:5e0n3:6e0n3:7e0n3:8e0n3:9e0n3:1e1l11:0,1,2,3,4,5,6,7,8,9,10,;"
#guard encode (.str "hello, world") == some "kl-struct-v1:1:t12:hello, world"

-- A call reference or argument view never leaves a run: no identity.
#guard encode (.listValue [.atom 1, .callRef 0]) == none
#guard encode (.argView 3) == none

-- A deferred list item or a pending list is materialized before a value leaves its run: no identity.
#guard encode (.listValue [.atom 1, .deferred 0]) == none
#guard encode (.pendingList [(0, 1)]) == none

end StructuralIdentity
