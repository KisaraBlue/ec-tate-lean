import Lake
open Lake DSL

package ECTate {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[defaultTarget]
lean_lib ECTate {
  roots := #[`ECTate],
  globs := #[.one `ECTate, .andSubmodules `ECTate]

  -- add any library configuration options here
}
