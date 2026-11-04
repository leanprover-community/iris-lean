module

public import Iris
public import IrisTest.Benchmarking.Timing

namespace IrisTest.ListBenchmarking

open Iris BI ProgramLogic List HeapLang

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def nil : Val := hl_val% none()

def cons : Val := hl_val% λ x, some(ref(x))

def llength : Val := hl_val% λ x, #(0 : Int)

def makeList2 : List Int → (Exp → Exp) → Exp
  | [] => fun cont => cont nil
  | l :: ls => fun cont =>
    makeList2 ls fun e => hl%
    let vls := &e;
    &(cont hl(&cons (#l, vls)))

opaque isList [HeapLangGS hlc GF] (v : Val) (xs : List Int) : IProp GF

axiom isList_nil {v} [HeapLangGS hlc GF] :
  isList (GF := GF) v [] ⊣⊢ iprop(⌜v = hl_val(none())⌝)

axiom isList_cons {v x xs} [HeapLangGS hlc GF] :
  isList (GF := GF) v (x :: xs) ⊣⊢ iprop(∃ l tl, ⌜v = hl_val(some(#(.loc l)))⌝ ∗
    l ↦ some hl_val((#x, &tl)) ∗ isList tl xs)

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

axiom nil_spec (Φ : Val → IProp GF) :
    (∀ v, isList v [] -∗ Φ v) -∗
    WP hl(v(&nil)) {{ Φ }}

axiom cons_spec (x : Int) (l : Val) (ls : List Int) (Φ : Val → IProp GF) :
    isList (GF := GF) l ls -∗
    (∀ v, isList v (x :: ls) -∗ Φ v) -∗
    WP hl(&cons v((#x, &l))) {{ Φ }}

axiom length_spec (l : Val) (ls : List Int) (Φ : Val → IProp GF) :
    isList (GF := GF) l ls -∗
    (∀ v, isList v ls -∗ ⌜v = hl_val(#(ls.length : Int))⌝ -∗ Φ v) -∗
    WP hl(&llength v(&l)) {{ Φ }}

def buildList (l : List Int) : Exp :=
  makeList2 l fun e => hl%
  let v := &e;
  &llength v

syntax "list_bench " num : command

macro_rules
  | `(list_bench $n:num) => do
    let name := Lean.mkIdent (Lean.Name.mkSimple s!"wp_buildList_{n.getNat}")
    let lbl := Lean.Syntax.mkStrLit s!"heaplang_list|cons_loop|{n.getNat}"
    `(theorem $name :
        ⊢@{IProp GF} WP (buildList (replicate $n 1)) {{ fun bv => iprop% ⌜bv = hl_val(# $n)⌝ }} := by
      unfold buildList
      dsimp only [reduceReplicate, makeList2]
      wp_pures
      wp_bind &cons _
      iapply cons_spec
      · unfold nil; iapply isList_nil; itrivial
      itimeN 5 $lbl
        repeat
          iintro %_ _ <;> wp_pures
          wp_bind &cons _
          iapply cons_spec $$ [$]
      iintro %v Hv <;>
      wp_pures <;>
      wp_bind &llength _
      iapply length_spec $$ Hv
      iintro %w Hw %Hlen //)

list_bench 10
list_bench 15
list_bench 20
list_bench 25

end

end ListBenchmarking

end IrisTest
