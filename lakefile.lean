import Lake
open Lake DSL

package iris where
  srcDir := "./src/"

@[default_target]
lean_lib iris
