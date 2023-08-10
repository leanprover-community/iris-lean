import Lake
open Lake DSL

package iris where
  srcDir := "./src/"

require std from git "https://github.com/leanprover/std4" @ "main"

@[default_target]
lean_lib iris
