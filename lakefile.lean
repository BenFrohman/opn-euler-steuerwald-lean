import Lake
open Lake DSL

package «opn-euler-steuerwald-lean» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

@[default_target]
lean_lib «Opn» where
