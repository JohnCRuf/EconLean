import Lake
open Lake DSL

set_option autoImplicit false

package «econlean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require "leanprover-community" / "mathlib"

lean_lib «EconLean» where
  -- add library configuration options here

@[default_target]
lean_exe «econlean» where
  root := `Main
