import Lake
open Lake DSL

package iris where
  srcDir := "./src/"

require "leanprover-community" / "Qq" @ git "v4.15.0"

@[default_target]
lean_lib Iris
