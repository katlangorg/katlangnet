import KatLangArityLaws.SignatureCompletion

/-! The rendering of the bridge corpus: one `id<TAB>outcome` line per case, computed by the model alone. -/

namespace KatLang.SignatureCompletion.Bridge

/-- A bound far above any corpus component's rounds: the bridge compares no exhausted outcome. -/
def bridgeFuel : Nat := 4096

def renderCorpus (cases : List (String × System)) : String :=
  String.join (cases.map fun (id, sys) => s!"{id}\t{renderOutcome sys (select sys bridgeFuel)}\n")

end KatLang.SignatureCompletion.Bridge
