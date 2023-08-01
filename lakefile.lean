import Lake
open Lake DSL

package choice {
  -- add package configuration options here
}

lean_lib Choice {
  -- add library configuration options here
}

@[default_target]
lean_exe ChoiceBin {
  root := `Main
}
