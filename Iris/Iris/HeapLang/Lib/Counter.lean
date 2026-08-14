/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.Algebra.Auth
public import Iris.Algebra.Lib.FracAuth
public import Iris.Algebra.Numbers
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode
public import Iris.Instances.Lib.Invariants
public import Iris.Std.Namespaces

namespace Iris.HeapLang

open BI Iris ProgramLogic CMRA OFE Auth

@[expose] public section

namespace Counter

@[rocq_alias heap_lang.newcounter]
def newcounter : Val := hl_val%
  λ _, ref(#0)

@[rocq_alias heap_lang.incr]
def incr : Val := hl_val%
  rec incr l :=
    let n := !l;
    if cas(l, n, #1 + n)
      then #()
      else incr l

@[rocq_alias heap_lang.read]
def read : Val := hl_val%
  λ l, !l

/-! ## Monotone counter -/

abbrev MCounterRF : COFE.OFunctorPre := constOF (Auth MaxNat)

@[rocq_alias heap_lang.mcounterG]
class MCounterG (GF : BundledGFunctors) where [elemG : ElemG GF MCounterRF]

attribute [reducible, instance] MCounterG.elemG

#rocq_ignore heap_lang.«mcounterΣ» "Superseded by the `MCounterG` typeclass on `BundledGFunctors`."
#rocq_ignore heap_lang.«subG_mcounterΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

section MonoProof

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [MCounterG GF] (N : Namespace)

@[rocq_alias heap_lang.mcounter_inv]
abbrev mcounterInv (γ : GName) (l : Loc) : IProp GF := iprop(
  ∃ n : Nat, iOwn (F := MCounterRF) γ (● MaxNat.ofNat n) ∗ (l ↦ some hl_val(#n)))

@[rocq_alias heap_lang.mcounter]
def mcounter (l : Loc) (n : Nat) : IProp GF := iprop(
  ∃ γ, inv N (mcounterInv γ l) ∧ iOwn (F := MCounterRF) γ (◯ MaxNat.ofNat n))

@[rocq_alias heap_lang.mcounter_persistent]
instance mcounter_persistent (l : Loc) (n : Nat) : Persistent (mcounter (GF := GF) N l n) := by
  unfold mcounter; exact exists_persistent _ (h := fun _ => inferInstance)

@[rocq_alias heap_lang.newcounter_mono_spec]
theorem newcounter_mono_spec :
    {{ (True : IProp GF) }} hl(&newcounter #()) {{ l, RET hl_val(#l); mcounter N l 0 }} := by
  iintro %Φ _ Hφ
  wp_lam
  wp_alloc l with Hl
  imod iOwn_alloc (F := MCounterRF) (((● MaxNat.ofNat 0) • (◯ MaxNat.ofNat 0)) : Auth MaxNat) with ⟨%γ, H⟩
  · exact auth_both_valid_2 trivial (MaxNat.inc_iff.mpr (by simp))
  icases iOwn_op $$ H with ⟨Hγ, Hγ'⟩
  imod inv_alloc N ⊤ (mcounterInv γ l) $$ [Hl Hγ] with #Hinv
  · iexists 0; iframe
  imodintro
  iapply Hφ
  unfold mcounter
  iexists γ
  iframe Hinv Hγ'

@[rocq_alias heap_lang.incr_mono_spec]
theorem incr_mono_spec (l : Loc) (n : Nat) :
    {{ mcounter (GF := GF) N l n }} hl(&incr #l) {{ RET hl_val(#()); mcounter N l (n + 1) }} := by
  iintro %Φ Hl Hφ
  iloeb as IH
  wp_rec
  unfold mcounter
  icases Hl with ⟨%γ, #Hinv, Hγf⟩
  wp_bind !_
  iinv Hinv with ⟨%c, Hγ, Hl⟩ Hclose
  wp_load
  imod Hclose $$ [Hγ Hl] with -
  · inext; iexists c; iframe
  imodintro
  wp_pures
  wp_bind cmpXchg(_, _, _)
  iinv Hinv with ⟨%c', Hγ, Hl⟩ Hclose
  wp_cmpxchg with hsuc hfail
  · obtain rfl : c = c' := by injection hsuc with h; injection h with h2; exact_mod_cast h2.symm
    icombine Hγ Hγf gives %Hv
    have hle : n ≤ c := by have := (auth_both_valid_discrete.mp Hv).1; grind [MaxNat.inc_iff]
    icombine Hγ Hγf as Hγ
    imod iOwn_update
        (a' := (((● MaxNat.ofNat (c + 1)) • (◯ MaxNat.ofNat (c + 1))) : Auth MaxNat)) $$ Hγ with Hγ
    · exact auth_update (MaxNat.local_update (by grind))
    icases iOwn_op $$ Hγ with ⟨Hγ, Hγf⟩
    imod Hclose $$ [Hγ Hl] with -
    · inext
      iexists (c + 1)
      rw [show ((c + 1 : Nat) : Int) = 1 + (c : Int) by omega]
      iframe
    imodintro
    wp_pures
    iapply Hφ
    imodintro
    iexists γ
    iframe Hinv
    iapply iOwn_mono $$ Hγf
    exact frag_inc_of_inc (MaxNat.inc_iff.mpr (by simp only [MaxNat.le_toNat]; omega))
  · imod Hclose $$ [Hγ Hl] with -
    · inext; iexists c'; iframe
    imodintro
    wp_pures
    iapply IH $$ [Hγf] [$Hφ]
    iexists γ
    iframe Hinv Hγf

@[rocq_alias heap_lang.read_mono_spec]
theorem read_mono_spec (l : Loc) (j : Nat) :
    {{ mcounter (GF := GF) N l j }} hl(&read #l)
    {{ i, RET hl_val(#i); ⌜j ≤ i⌝ ∧ mcounter N l i }} := by
  iintro %Φ Hc Hφ
  unfold mcounter
  icases Hc with ⟨%γ, #Hinv, Hγf⟩
  wp_lam
  iinv Hinv with ⟨%c, Hγ, Hl⟩ Hclose
  wp_load
  icombine Hγ Hγf gives %Hv
  have hle : j ≤ c := by have := (auth_both_valid_discrete.mp Hv).1; grind [MaxNat.inc_iff]
  icombine Hγ Hγf as Hγ
  imod iOwn_update
      (a' := (((● MaxNat.ofNat c) • (◯ MaxNat.ofNat c)) : Auth MaxNat)) $$ Hγ with Hγ
  · exact auth_update (MaxNat.local_update (by simp))
  icases iOwn_op $$ Hγ with ⟨Hγ, Hγf⟩
  imod Hclose $$ [Hγ Hl] with -
  · inext; iexists c; iframe
  imodintro
  iapply Hφ
  isplit
  · ipureintro; exact hle
  · iexists γ
    iframe Hinv Hγf

end MonoProof

/-! ## Counter with contributions -/

abbrev CCounterRF : COFE.OFunctorPre := constOF (FracAuth (A := Nat))

@[rocq_alias heap_lang.ccounterG]
class CCounterG (GF : BundledGFunctors) where [elemG : ElemG GF CCounterRF]

attribute [reducible, instance] CCounterG.elemG

#rocq_ignore heap_lang.«ccounterΣ» "Superseded by the `CCounterG` typeclass on `BundledGFunctors`."
#rocq_ignore heap_lang.«subG_ccounterΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

section ContribProof

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [CCounterG GF] (N : Namespace)

@[rocq_alias heap_lang.ccounter_inv]
abbrev ccounterInv (γ : GName) (l : Loc) : IProp GF := iprop(
  ∃ n : Nat, iOwn (F := CCounterRF) γ (●F n) ∗ (l ↦ some hl_val(#n)))

@[rocq_alias heap_lang.ccounter_ctx]
abbrev ccounterCtx (γ : GName) (l : Loc) : IProp GF := inv N (ccounterInv γ l)

@[rocq_alias heap_lang.ccounter]
def ccounter (γ : GName) (q : Qp) (n : Nat) : IProp GF := iOwn (F := CCounterRF) γ (◯F{q} n)

@[rocq_alias heap_lang.ccounter_op]
theorem ccounter_op (γ : GName) (q1 q2 : Qp) (n1 n2 : Nat) :
    ccounter (GF := GF) γ (q1 + q2) (n1 + n2) ⊣⊢ ccounter γ q1 n1 ∗ ccounter γ q2 n2 := by
  unfold ccounter
  rw [← iOwn_op.to_eq]
  exact (congrArg (iOwn (F := CCounterRF) γ) FracAuth.frag_op).to_bi

@[rocq_alias heap_lang.newcounter_contrib_spec]
theorem newcounter_contrib_spec (R : IProp GF) :
    {{ (True : IProp GF) }} hl(&newcounter #())
    {{ γ l, RET hl_val(#l); ccounterCtx N γ l ∗ ccounter γ 1 0 }} := by
  iintro %Φ _ Hφ
  wp_lam
  wp_alloc l with Hl
  imod iOwn_alloc (F := CCounterRF) (CMRA.op (●F (0 : Nat)) (◯F (0 : Nat))) with ⟨%γ, H⟩
  · exact FracAuth.valid trivial
  icases iOwn_op $$ H with ⟨Hγ, Hγ'⟩
  imod inv_alloc N ⊤ (ccounterInv γ l) $$ [Hl Hγ] with #Hinv
  · iexists 0; iframe
  imodintro
  iapply Hφ
  unfold ccounterCtx ccounter
  iframe Hinv Hγ'

@[rocq_alias heap_lang.incr_contrib_spec]
theorem incr_contrib_spec (γ : GName) (l : Loc) (q : Qp) (n : Nat) :
    {{ ccounterCtx (GF := GF) N γ l ∗ ccounter γ q n }} hl(&incr #l)
    {{ RET hl_val(#()); ccounter γ q (n + 1) }} := by
  iintro %Φ ⟨#Hctx, Hγf⟩ Hφ
  iloeb as IH
  wp_rec
  unfold ccounterCtx ccounter
  wp_bind !_
  iinv Hctx with ⟨%c, Hγ, Hl⟩ Hclose
  wp_load
  imod Hclose $$ [Hγ Hl] with -
  · inext; iexists c; iframe
  imodintro
  wp_pures
  wp_bind cmpXchg(_, _, _)
  iinv Hctx with ⟨%c', Hγ, Hl⟩ Hclose
  wp_cmpxchg with hsuc hfail
  · obtain rfl : c = c' := by injection hsuc with h; injection h with h2; exact_mod_cast h2.symm
    icombine Hγ Hγf as Hγ
    imod iOwn_update (a' := CMRA.op (●F (c + 1)) (◯F{q} (n + 1))) $$ Hγ with Hγ
    · exact FracAuth.update (CommMonoidLike.leftCancelAdd_local_update
        (by show c + (n + 1) = c + 1 + n; omega))
    icases iOwn_op $$ Hγ with ⟨Hγ, Hγf⟩
    imod Hclose $$ [Hγ Hl] with -
    · inext
      iexists (c + 1)
      rw [show ((c + 1 : Nat) : Int) = 1 + (c : Int) by omega]
      iframe
    imodintro
    wp_pures
    iapply Hφ
    imodintro
    iexact Hγf
  · imod Hclose $$ [Hγ Hl] with -
    · inext; iexists c'; iframe
    imodintro
    wp_pures
    iapply IH $$ [$Hγf] [$Hφ]

@[rocq_alias heap_lang.read_contrib_spec]
theorem read_contrib_spec (γ : GName) (l : Loc) (q : Qp) (n : Nat) :
    {{ ccounterCtx (GF := GF) N γ l ∗ ccounter γ q n }} hl(&read #l)
    {{ c, RET hl_val(#c); ⌜n ≤ c⌝ ∧ ccounter γ q n }} := by
  iintro %Φ ⟨#Hctx, Hγf⟩ Hφ
  unfold ccounterCtx ccounter
  wp_lam
  iinv Hctx with ⟨%c, Hγ, Hl⟩ Hclose
  wp_load
  icombine Hγ Hγf gives %Hv
  have hle : n ≤ c := by
    have ⟨z, hz⟩ := CommMonoidLike.included_iff.mp (FracAuth.included_total Hv)
    omega
  imod Hclose $$ [Hγ Hl] with -
  · inext; iexists c; iframe
  imodintro
  iapply Hφ
  isplit
  · ipureintro; exact hle
  · iexact Hγf

@[rocq_alias heap_lang.read_contrib_spec_1]
theorem read_contrib_spec_1 (γ : GName) (l : Loc) (n : Nat) :
    {{ ccounterCtx (GF := GF) N γ l ∗ ccounter γ 1 n }} hl(&read #l)
    {{ RET hl_val(#n); ccounter γ 1 n }} := by
  iintro %Φ ⟨#Hctx, Hγf⟩ Hφ
  unfold ccounterCtx ccounter
  wp_lam
  iinv Hctx with ⟨%c, Hγ, Hl⟩ Hclose
  wp_load
  icombine Hγ Hγf gives %Hv
  obtain rfl : n = c := (FracAuth.agree Hv).symm
  imod Hclose $$ [Hγ Hl] with -
  · inext; iexists n; iframe
  imodintro
  iapply Hφ
  iexact Hγf

end ContribProof

end Counter
end
