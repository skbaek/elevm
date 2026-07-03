import Lake
open Lake DSL

package «elevm» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "10061bf49d6d842b2099878901410ef3b6a393c2"

@[default_target]
lean_lib «Elevm» where
lean_exe «elevm» where
  root := `Main
