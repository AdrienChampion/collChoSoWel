import Lake
open Lake DSL

package choice {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib Choice {
  -- add library configuration options here
}

@[default_target]
lean_exe ChoiceBin {
  root := `Main
}
