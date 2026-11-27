import Lake
open Lake DSL

package «opn-euler-steuerwald-lean» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

@[default_target]
lean_lib «Opn» where
  -- add library configuration options here
