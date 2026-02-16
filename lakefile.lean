import Lake
open Lake DSL

package «econlean» where
  -- add package configuration options here

lean_lib «EconLean» where
  -- add library configuration options here

@[default_target]
lean_exe «econlean» where
  root := `Main
