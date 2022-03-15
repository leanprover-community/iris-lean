import Lake
open Lake DSL

package «iris-lean» {
  defaultFacet := .oleans,
  srcDir := "./src/",
  libRoots := #[ "Iris" ],
  libName := "Iris"
}
