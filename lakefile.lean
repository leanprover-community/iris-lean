import Lake
open Lake DSL

package «Iris» where
  srcDir := "./src/"

require std from git "https://github.com/leanprover/std4" @ "main"
require Qq from git "https://github.com/gebner/quote4" @ "master"

@[default_target]
lean_lib «Iris» where
