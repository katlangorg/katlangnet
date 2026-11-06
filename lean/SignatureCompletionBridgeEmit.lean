import KatLangArityLaws.SignatureCompletionBridgeCases
import KatLangArityLaws.SignatureCompletionOutcomes

/-!
Writes the Lean model's outcomes of the bridge corpus to standard output. THE ONLY WRITER of
`tests/KatLang.Tests/SignatureCompletion/lean-model-outcomes.txt`: no native answer is an input here.

    Push-Location lean
    lake build KatLangArityLaws.SignatureCompletionBridgeCases KatLangArityLaws.SignatureCompletionOutcomes
    if ($LASTEXITCODE -ne 0) { throw 'Lean bridge build failed.' }
    $scOutcomeLines = lake env lean --run SignatureCompletionBridgeEmit.lean
    if ($LASTEXITCODE -ne 0) { throw 'Lean outcome emission failed.' }
    $scOutcomePath = Join-Path (Get-Location) '../tests/KatLang.Tests/SignatureCompletion/lean-model-outcomes.txt'
    [IO.File]::WriteAllText($scOutcomePath, ($scOutcomeLines -join "`n") + "`n", [Text.UTF8Encoding]::new($false))
    Pop-Location

The writer preserves LF separators and UTF-8 without a BOM. `Set-Content -NoNewline` would concatenate the native
process's separate output lines and corrupt the receipt.

This file is not part of a library target; `#guard renderCorpus bridgeCases == committedOutcomes` in `SignatureCompletionGuards.lean` makes
`lake build KatLangArityLaws` fail when the committed file is not what the model computes.
-/

def main : IO Unit :=
  IO.print (KatLang.SignatureCompletion.Bridge.renderCorpus KatLang.SignatureCompletion.Bridge.bridgeCases)
