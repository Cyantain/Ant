import Lake
open Lake DSL

package "Ant" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib" @ "git#v4.17.0"

@[default_target]
lean_lib «Ant» where
  -- add any library configuration options here
