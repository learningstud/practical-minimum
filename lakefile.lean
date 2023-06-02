import Lake
open Lake DSL

package «practical-minimum»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib PracticalMinimum

lean_lib ApostolCalculus
lean_lib Kip
lean_lib Cmd
lean_lib Cpp

@[default_target]
lean_exe cmd {
  root := `Cmd
  -- exeName
}