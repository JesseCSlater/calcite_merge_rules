import Lake
open Lake DSL

package calciteMergeRules {
  -- add package configuration options here
}

lean_lib CalciteMergeRules

require std from git
  "https://github.com/leanprover/std4/" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

require aesop from git "https://github.com/JLimperg/aesop" @ "master"

@[default_target]
lean_exe calciteMergeRules {
  root := `Table
}
