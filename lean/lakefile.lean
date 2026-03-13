import Lake
open Lake DSL

package «katlang»

@[default_target]
lean_lib «KatLang» where
  srcDir := "."

lean_lib «CoreTests» where
  srcDir := "."

lean_lib «AstDemo» where
  srcDir := "."
