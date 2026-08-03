module

public import IrisDoNightly.Codec.Basic
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `delta` codec — pure model -/

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

@[expose] public section

def deltaEnc : Int → List Int → List Int
  | _, [] => []
  | prev, c :: cs => (c - prev + 256) % 256 :: deltaEnc c cs

def deltaDec : Int → List Int → List Int
  | _, [] => []
  | prev, d :: ds => (prev + d) % 256 :: deltaDec ((prev + d) % 256) ds

end

end Iris.HeapLang.Ax
