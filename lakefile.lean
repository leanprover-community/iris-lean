import Lake
open Lake DSL

package iris where
  srcDir := "./src/"

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.10.0"
require Qq from git "https://github.com/gebner/quote4" @ "master"

@[default_target]
lean_lib Iris
