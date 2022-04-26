import Lean.Syntax

namespace Lean.Syntax

def getAtomValFromNode? (s : Syntax) (kind : SyntaxNodeKind) (parse : String → Option α) : Option α := Id.run <| do
  if !(s.isNodeOf kind 1) then
    return none
  let a := s.getArg 0
  if !a.isAtom then
    return none
  return parse <| a.getAtomVal!

end Lean.Syntax
