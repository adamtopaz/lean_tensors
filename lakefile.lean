import Lake
open Lake DSL

package «lean_tensors» where
  -- add package configuration options here

lean_lib «LeanTensors» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «lean_tensors» where
  root := `Main
