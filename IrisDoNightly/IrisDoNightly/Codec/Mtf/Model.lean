module

public import IrisDoNightly.Codec.Basic
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `mtf` (move-to-front) codec — pure model -/

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

@[expose] public section

def idxOf : List Int → Int → Int
  | [], _ => 0
  | x :: xs, c => if x = c then 0 else idxOf xs c + 1

def eraseIdx' : List Int → Int → List Int
  | [], _ => []
  | x :: xs, r => if r = 0 then xs else x :: eraseIdx' xs (r - 1)

def mtfEnc : List Int → List Int → List Int
  | _, [] => []
  | tbl, c :: cs => idxOf tbl c :: mtfEnc (c :: eraseIdx' tbl (idxOf tbl c)) cs

def mtfDec : List Int → List Int → List Int
  | _, [] => []
  | tbl, r :: rs => nthD tbl r :: mtfDec (nthD tbl r :: eraseIdx' tbl r) rs

end

end Iris.HeapLang.Ax
