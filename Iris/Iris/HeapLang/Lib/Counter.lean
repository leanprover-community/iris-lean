/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
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

@[rocq_alias heap_lang.counter.incr]
def incr : Val := hl_val%
  rec incr l :=
    let n := !l;
    if cas(l, n, #1 + n)
      then #()
      else incr l

@[rocq_alias heap_lang.read]
def read : Val := hl_val%
  λ l, !l

/-! ## Generic counter specifications

Both counters below keep the same invariant — the location holds `n`, and `A n` is authoritative
ghost state tracking it — so their `incr`/`read` proofs differ only in the resource algebra. The
two specifications here do the program reasoning once, taking the ghost-state exchange performed
while the invariant is open as a premise. -/

section CounterProof

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

/-- The shared counter invariant: the location holds `n`, tracked by the ghost state `A n`. -/
abbrev counterInv (A : Nat → IProp GF) (l : Loc) : IProp GF := iprop%
  ∃ n : Nat, A n ∗ l ↦ some hl_val(#n)

private theorem incr_spec {A : Nat → IProp GF} (P : IProp GF) (Q : IProp GF) (l : Loc)
    (hupd : ∀ c : Nat, iprop(A c ∗ P) ⊢ iprop(|==> (A (c + 1) ∗ Q))) :
    {{ inv N (counterInv A l) ∧ P }} hl(&incr #l) {{ RET hl_val(#()); Q }} := by
  iintro %Φ ⟨#Hinv, HP⟩ Hφ
  iloeb as IH
  wp_rec
  wp_bind !_
  iinv Hinv with ⟨%c, HA, Hl⟩ Hclose
  wp_load
  imod Hclose $$ [HA Hl] with -
  · inext; iexists c; iframe
  imodintro
  wp_pures
  wp_bind cmpXchg(_, _, _)
  iinv Hinv with ⟨%c', HA, Hl⟩ Hclose
  wp_cmpxchg with hsuc hfail
  · obtain rfl : c = c' := by grind
    imod hupd c $$ [$HA $HP] with ⟨HA, HQ⟩
    imod Hclose $$ [HA Hl] with -
    · inext; iexists (c + 1); rw [show ((c + 1 : Nat) : Int) = 1 + (c : Int) by omega]; iframe
    imodintro
    wp_pures
    iapply Hφ $$ HQ
  · imod Hclose $$ [HA Hl] with -
    · inext; iexists c'; iframe
    imodintro
    wp_pures
    iapply IH $$ HP Hφ

private theorem read_spec {A : Nat → IProp GF} (P : IProp GF) (Ψ : Nat → IProp GF) (l : Loc)
    (hupd : ∀ c : Nat, iprop(A c ∗ P) ⊢ iprop(|==> (A c ∗ Ψ c))) :
    {{ inv N (counterInv A l) ∧ P }} hl(&read #l) {{ c, RET hl_val(#c); Ψ c }} := by
  iintro %Φ ⟨#Hinv, HP⟩ Hφ
  wp_lam
  iinv Hinv with ⟨%c, HA, Hl⟩ Hclose
  wp_load
  imod hupd c $$ [$HA $HP] with ⟨HA, HΨ⟩
  imod Hclose $$ [HA Hl] with -
  · inext; iexists c; iframe
  imodintro
  iapply Hφ $$ HΨ

end CounterProof

/-! ## Monotone counter -/

abbrev MCounterRF : COFE.OFunctorPre := constOF (Auth MaxNat)

@[rocq_alias heap_lang.mcounterG]
class MCounterG (GF : BundledGFunctors) where [elemG : ElemG GF MCounterRF]

attribute [reducible, instance] MCounterG.elemG

#rocq_ignore heap_lang.«mcounterΣ» "Superseded by the `MCounterG` typeclass on `BundledGFunctors`."
#rocq_ignore heap_lang.«subG_mcounterΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

section MonoProof

variable {GF : BundledGFunctors} [HeapLangGS hlc GF] [MCounterG GF] (N : Namespace)

/-- The authoritative element of the monotone counter. -/
abbrev mcounterAuth (γ : GName) (n : Nat) : IProp GF := iOwn (F := MCounterRF) γ (● MaxNat.ofNat n)

/-- A lower-bound fragment of the monotone counter. -/
abbrev mcounterFrag (γ : GName) (n : Nat) : IProp GF := iOwn (F := MCounterRF) γ (◯ MaxNat.ofNat n)

@[rocq_alias heap_lang.mcounter_inv]
abbrev mcounterInv (γ : GName) (l : Loc) : IProp GF := counterInv (mcounterAuth γ) l

@[reducible, rocq_alias heap_lang.mcounter]
def mcounter (l : Loc) (n : Nat) : IProp GF := iprop%
  ∃ γ, inv N (mcounterInv γ l) ∧ mcounterFrag γ n

@[rocq_alias heap_lang.mcounter_persistent]
instance mcounter_persistent (l : Loc) (n : Nat) : Persistent (mcounter (GF := GF) N l n) :=
  exists_persistent _ (h := fun _ => inferInstance)

@[rocq_alias heap_lang.newcounter_mono_spec]
theorem newcounter_mono_spec :
    {{ (True : IProp GF) }} hl(&newcounter #()) {{ l, RET hl_val(#l); mcounter N l 0 }} := by
  iintro %Φ _ Hφ
  wp_lam
  wp_alloc l with Hl
  imod iOwn_alloc (F := MCounterRF)
    (((● MaxNat.ofNat 0) • (◯ MaxNat.ofNat 0)) : Auth MaxNat) with ⟨%γ, Hγ, Hγ'⟩
  · exact auth_both_valid_2 trivial (MaxNat.inc_iff.mpr (by simp))
  imod inv_alloc N _ (mcounterInv γ l) $$ [Hl Hγ] with #Hinv
  · iexists 0; iframe
  imodintro
  iapply Hφ
  iexists γ
  iframe Hinv Hγ'

@[rocq_alias heap_lang.incr_mono_spec]
theorem incr_mono_spec (l : Loc) (n : Nat) :
    {{ mcounter (GF := GF) N l n }} hl(&incr #l) {{ RET hl_val(#()); mcounter N l (n + 1) }} := by
  iintro %Φ Hc Hφ
  icases Hc with ⟨%γ, #Hinv, Hγf⟩
  iapply incr_spec (mcounterFrag γ n) (mcounterFrag γ (n + 1)) l $$ [$Hinv $Hγf] [Hφ]
  · iintro %c ⟨Hγ, Hγf⟩
    icombine Hγ Hγf gives %Hv
    imod iOwn_update_op
      (a' := (((● MaxNat.ofNat (c + 1)) • (◯ MaxNat.ofNat (c + 1))) : Auth MaxNat)) $$
      [$Hγ $Hγf] with ⟨Hγ, Hγf⟩
    · exact auth_update_of_localUpdate (fun h => h) (MaxNat.local_update (by grind))
    imodintro
    iframe Hγ
    iapply iOwn_mono $$ Hγf
    have hnc := CMRA.inc_of_incExt (auth_both_valid_discrete.mp Hv).1
    refine CMRA.inc_of_incExt (frag_incExt_of_incExt (MaxNat.inc_iff.mpr ?_))
    grind [MaxNat.inc_iff]
  iintro !> Hγf
  iapply Hφ
  iexists γ
  iframe Hinv Hγf

@[rocq_alias heap_lang.read_mono_spec]
theorem read_mono_spec (l : Loc) (j : Nat) :
    {{ mcounter (GF := GF) N l j }} hl(&read #l)
    {{ i, RET hl_val(#i); ⌜j ≤ i⌝ ∧ mcounter N l i }} := by
  iintro %Φ Hc Hφ
  icases Hc with ⟨%γ, #Hinv, Hγf⟩
  iapply read_spec (mcounterFrag γ j) (fun c => iprop% ⌜j ≤ c⌝ ∗ mcounterFrag γ c) l $$ [$Hinv $Hγf] [Hφ]
  · iintro %c ⟨Hγ, Hγf⟩
    icombine Hγ Hγf gives %Hv
    imod iOwn_update_op
      (a' := (((● MaxNat.ofNat c) • (◯ MaxNat.ofNat c)) : Auth MaxNat)) $$ [$Hγ $Hγf] with ⟨Hγ, Hγf⟩
    · exact auth_update_of_localUpdate (fun h => h) (MaxNat.local_update (by simp))
    imodintro
    iframe Hγ Hγf
    ipureintro
    have hjc := CMRA.inc_of_incExt (auth_both_valid_discrete.mp Hv).1
    grind [MaxNat.inc_iff]
  iintro !> %c ⟨%hle, Hγf⟩
  iapply Hφ
  iframe %hle
  iexists γ
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

/-- The authoritative element of the counter with contributions. -/
abbrev ccounterAuth (γ : GName) (n : Nat) : IProp GF := iOwn (F := CCounterRF) γ (●F n)

@[rocq_alias heap_lang.ccounter_inv]
abbrev ccounterInv (γ : GName) (l : Loc) : IProp GF := counterInv (ccounterAuth γ) l

@[rocq_alias heap_lang.ccounter_ctx]
abbrev ccounterCtx (γ : GName) (l : Loc) : IProp GF := inv N (ccounterInv γ l)

@[reducible, rocq_alias heap_lang.ccounter]
def ccounter (γ : GName) (q : Qp) (n : Nat) : IProp GF := iOwn (F := CCounterRF) γ (◯F{q} n)

@[rocq_alias heap_lang.ccounter_op]
theorem ccounter_op (γ : GName) (q1 q2 : Qp) (n1 n2 : Nat) :
    ccounter (GF := GF) γ (q1 + q2) (n1 + n2) ⊣⊢ ccounter γ q1 n1 ∗ ccounter γ q2 n2 := by
  rw [← iOwn_op.to_eq]
  exact (congrArg (iOwn (F := CCounterRF) γ) FracAuth.frag_op).to_bi

@[rocq_alias heap_lang.newcounter_contrib_spec]
theorem newcounter_contrib_spec :
    {{ (True : IProp GF) }} hl(&newcounter #())
    {{ γ l, RET hl_val(#l); ccounterCtx N γ l ∗ ccounter γ 1 0 }} := by
  iintro %Φ _ Hφ
  wp_lam
  wp_alloc l with Hl
  imod iOwn_alloc (F := CCounterRF) (CMRA.op (●F (0 : Nat)) (◯F (0 : Nat))) with ⟨%γ, Hγ, Hγ'⟩
  · exact FracAuth.valid trivial
  imod inv_alloc N ⊤ (ccounterInv γ l) $$ [Hl Hγ] with #Hinv
  · iexists 0; iframe
  imodintro
  iapply Hφ
  iframe Hinv Hγ'

@[rocq_alias heap_lang.incr_contrib_spec]
theorem incr_contrib_spec (γ : GName) (l : Loc) (q : Qp) (n : Nat) :
    {{ ccounterCtx (GF := GF) N γ l ∗ ccounter γ q n }} hl(&incr #l)
    {{ RET hl_val(#()); ccounter γ q (n + 1) }} := by
  iintro %Φ ⟨#Hctx, Hγf⟩ Hφ
  iapply incr_spec (ccounter γ q n) (ccounter γ q (n+1)) l $$ [$Hctx $Hγf] Hφ
  iintro %c ⟨Hγ, Hγf⟩
  imod iOwn_update_op (a' := CMRA.op (●F (c + 1)) (◯F{q} (n + 1))) $$ [$Hγ $Hγf] with ⟨Hγ, Hγf⟩
  · exact FracAuth.update (fun h => h) (CommMonoidLike.leftCancelAdd_local_update (by grind))
  imodintro
  iframe

@[rocq_alias heap_lang.read_contrib_spec]
theorem read_contrib_spec (γ : GName) (l : Loc) (q : Qp) (n : Nat) :
    {{ ccounterCtx (GF := GF) N γ l ∗ ccounter γ q n }} hl(&read #l)
    {{ c, RET hl_val(#c); ⌜n ≤ c⌝ ∧ ccounter γ q n }} := by
  iintro %Φ ⟨#Hctx, Hγf⟩ Hφ
  iapply read_spec (ccounter γ q n) (fun c => iprop% ⌜n ≤ c⌝ ∗ ccounter γ q n) l  $$ [$Hctx $Hγf] [Hφ]
  · iintro %c ⟨Hγ, Hγf⟩
    icombine Hγ Hγf gives %Hv
    iframe Hγ Hγf
    ipureintro
    have ⟨z, hz⟩ := CommMonoidLike.included_iff.mp (FracAuth.included_total Hv)
    omega
  iintro !> %c ⟨%hle, Hγf⟩
  iapply Hφ
  iframe %hle Hγf

@[rocq_alias heap_lang.read_contrib_spec_1]
theorem read_contrib_spec_1 (γ : GName) (l : Loc) (n : Nat) :
    {{ ccounterCtx (GF := GF) N γ l ∗ ccounter γ 1 n }} hl(&read #l)
    {{ RET hl_val(#n); ccounter γ 1 n }} := by
  iintro %Φ ⟨#Hctx, Hγf⟩ Hφ
  iapply read_spec (ccounter γ 1 n) (fun c => iprop% ⌜c = n⌝ ∗ ccounter γ 1 n) l $$ [$Hctx $Hγf] [Hφ]
  · iintro %c ⟨Hγ, Hγf⟩
    icombine Hγ Hγf gives %Hv
    imodintro
    iframe Hγ Hγf
    ipureintro
    exact FracAuth.agree Hv
  iintro !> %c ⟨%heq, Hγf⟩
  subst heq
  iapply Hφ $$ Hγf

end ContribProof

end Counter
end
