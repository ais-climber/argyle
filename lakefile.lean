import Lake
open Lake DSL

package «argyle» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require Graph from git
  "https://github.com/PeterKementzey/graph-library-for-lean4.git"

@[default_target]
lean_lib «Argyle» {
  -- add any library configuration options here
}
