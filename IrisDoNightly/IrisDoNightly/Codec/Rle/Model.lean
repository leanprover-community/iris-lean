module

public import IrisDoNightly.Codec.Basic
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `rle` (run-length) codec — pure model -/

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

@[expose] public section

def rleEncAux : Int → Int → List Int → List Int
  | c, k, [] => [k, c]
  | c, k, x :: xs => if x = c then rleEncAux c (k + 1) xs else k :: c :: rleEncAux x 1 xs

def rleEnc : List Int → List Int
  | [] => []
  | c :: cs => rleEncAux c 1 cs

def replicateApp : Nat → Int → List Int → List Int
  | 0, _, tail => tail
  | n + 1, c, tail => c :: replicateApp n c tail

def rleDec : List Int → List Int
  | [] => []
  | [_] => []
  | k :: c :: rest => replicateApp k.toNat c (rleDec rest)

def GoodCounts : List Int → Prop
  | [] => True
  | [_] => True
  | k :: _ :: rest => 0 ≤ k ∧ GoodCounts rest

end

end Iris.HeapLang.Ax
