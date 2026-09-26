/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.HeapLang.TransfiniteProofMode

/-! # Derived prophecy laws for heap_lang in Transfinite Iris

This file ports the prophecy lemmas `wp_resolve_proph`, `swp_resolve_proph`,
`wp_resolve_cmpxchg_suc`, `swp_resolve_cmpxchg_suc`, `wp_resolve_cmpxchg_fail` and
`swp_resolve_cmpxchg_fail` of `theories/heap_lang/lifting.v` of Transfinite Iris.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.HeapLang.Transfinite

open Iris Iris.Transfinite ProgramLogic Iris.BI

variable {GF : BundledGFunctors} [H : HeapLangTGS GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {k : Nat}

instance atomic_unit_beta :
    Language.Atomic Language.Atomicity.StronglyAtomic hl((v(λ _, #())) #()) := by
  constructor
  intro σ _ _ _ _ h
  dsimp only []
  apply prim_step_to_val_always_to_val (κsₐ := []) (σ₁ₐ := σ) (σ₂ₐ := σ) (efsₐ := []) ?h h
  case h =>
    apply ProgramLogic.EctxLanguage.primStep_of_baseStep
    simp only [BaseStep.baseStep, val_to_ofVal]
    constructor
    rfl

/-- Rocq: `wp_resolve_proph`. -/
theorem wp_resolve_proph {p : ProphId} {w : Val} {pvs : List (Val × Val)} :
    ⊢ proph p pvs -∗
      (∀ pvs', ⌜pvs = (hl_val(#()), w) :: pvs'⌝ -∗ proph p pvs' -∗ Φ hl_val(#())) -∗
      Iris.Transfinite.wp s E hl(resolveProph(v(#p), v(&w))) Φ := by
  iintro Hp HΦ
  twp_closure
  iapply wp_resolve (hne := rfl) $$ Hp
  twp_pures
  iintro %pvs' %heq Hp
  iapply HΦ $$ %pvs' %heq Hp

/-- Rocq: `swp_resolve_proph`. -/
theorem swp_resolve_proph {p : ProphId} {w : Val} {pvs : List (Val × Val)} :
    ⊢ proph p pvs -∗
      ▷ (∀ pvs', ⌜pvs = (hl_val(#()), w) :: pvs'⌝ -∗ proph p pvs' -∗ Φ hl_val(#())) -∗
      swp k s E hl(resolve((v(λ _, #())) #(), v(#p), v(&w))) Φ := by
  iintro Hp HΦ
  iapply swp_resolve $$ Hp
  twp_pure
  iintro %pvs' %heq Hp
  iapply HΦ $$ %pvs' %heq Hp

/-- Rocq: `wp_resolve_cmpxchg_suc`. -/
theorem wp_resolve_cmpXchg_suc {l : Loc} {p : ProphId} {pvs : List (Val × Val)} {v1 v2 w : Val}
    (hsafe : v1.compareSafe v1) :
    ⊢ proph p pvs -∗ ▷ l ↦ some v1 -∗
      ((∃ pvs', ⌜pvs = (hl_val((&v1, #true)), w) :: pvs'⌝ ∗ proph p pvs' ∗ l ↦ some v2) -∗
        Φ hl_val((&v1, #true))) -∗
      Iris.Transfinite.wp s E hl(resolve(cmpXchg(#l, &v1, &v2), v(#p), v(&w))) Φ := by
  iintro Hp Hl HΦ
  iapply wp_resolve (hne := rfl) $$ Hp
  iapply wp_cmpXchg_suc rfl hsafe $$ Hl
  iintro Hl %pvs' %heq Hp
  iapply HΦ
  iexists pvs'
  iframe Hp Hl %heq

/-- Rocq: `swp_resolve_cmpxchg_suc`. -/
theorem swp_resolve_cmpXchg_suc {l : Loc} {p : ProphId} {pvs : List (Val × Val)} {v1 v2 w : Val}
    (hsafe : v1.compareSafe v1) :
    ⊢ proph p pvs -∗ ▷ l ↦ some v1 -∗
      ((∃ pvs', ⌜pvs = (hl_val((&v1, #true)), w) :: pvs'⌝ ∗ proph p pvs' ∗ l ↦ some v2) -∗
        Φ hl_val((&v1, #true))) -∗
      swp k s E hl(resolve(cmpXchg(#l, &v1, &v2), v(#p), v(&w))) Φ := by
  iintro Hp Hl HΦ
  iapply swp_resolve $$ Hp
  iapply swp_cmpXchg_suc rfl hsafe $$ Hl
  iintro Hl %pvs' %heq Hp
  iapply HΦ
  iexists pvs'
  iframe Hp Hl %heq

/-- Rocq: `wp_resolve_cmpxchg_fail`. -/
theorem wp_resolve_cmpXchg_fail {l : Loc} {p : ProphId} {pvs : List (Val × Val)} {q}
    {v' v1 v2 w : Val} (hne : v' ≠ v1) (hsafe : v'.compareSafe v1) :
    ⊢ proph p pvs -∗ ▷ l ↦{q} some v' -∗
      ((∃ pvs', ⌜pvs = (hl_val((&v', #false)), w) :: pvs'⌝ ∗ proph p pvs' ∗ l ↦{q} some v') -∗
        Φ hl_val((&v', #false))) -∗
      Iris.Transfinite.wp s E hl(resolve(cmpXchg(#l, &v1, &v2), v(#p), v(&w))) Φ := by
  iintro Hp Hl HΦ
  iapply wp_resolve (hne := rfl) $$ Hp
  iapply wp_cmpXchg_fail hne hsafe $$ Hl
  iintro Hl %pvs' %heq Hp
  iapply HΦ
  iexists pvs'
  iframe Hp Hl %heq

/-- Rocq: `swp_resolve_cmpxchg_fail`. -/
theorem swp_resolve_cmpXchg_fail {l : Loc} {p : ProphId} {pvs : List (Val × Val)} {q}
    {v' v1 v2 w : Val} (hne : v' ≠ v1) (hsafe : v'.compareSafe v1) :
    ⊢ proph p pvs -∗ ▷ l ↦{q} some v' -∗
      ((∃ pvs', ⌜pvs = (hl_val((&v', #false)), w) :: pvs'⌝ ∗ proph p pvs' ∗ l ↦{q} some v') -∗
        Φ hl_val((&v', #false))) -∗
      swp k s E hl(resolve(cmpXchg(#l, &v1, &v2), v(#p), v(&w))) Φ := by
  iintro Hp Hl HΦ
  iapply swp_resolve $$ Hp
  iapply swp_cmpXchg_fail hne hsafe $$ Hl
  iintro Hl %pvs' %heq Hp
  iapply HΦ
  iexists pvs'
  iframe Hp Hl %heq

end Iris.HeapLang.Transfinite
