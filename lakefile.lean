import Lake
open Lake DSL

package iris where
  srcDir := "./src/"

@[defaultTarget]
lean_lib iris
