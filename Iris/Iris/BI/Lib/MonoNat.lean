/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra.Lib.MonoNat
public import Iris.Algebra.Auth
public import Iris.BI
public import Iris.BI.Lib.Fractional
public import Iris.ProofMode
public import Iris.Instances.IProp

@[expose] public section

namespace Iris
open Auth BI MonoNat

abbrev MonoNatRF : COFE.OFunctorPre :=
  AuthURF (constOF MaxNat)

@[rocq_alias mono_natG]
class MonoNatG (GF : BundledGFunctors) where
  elem : ElemG GF (MonoNatRF)
  name : GName

attribute [reducible, instance] MonoNatG.elem

namespace MonoNat

variable {GF : BundledGFunctors} [MonoNatG GF]
open MonoNatG

@[rocq_alias mono_nat_auth_own]
def auth_own (γ : GName) (dq : DFrac) (n : MaxNat) : IProp GF :=
  iOwn (E := elem) γ (MonoNat.auth dq n)

@[rocq_alias mono_nat_lb_own]
def lb_own (γ : GName) (n : MaxNat) : IProp GF :=
  iOwn (E := elem) γ (MonoNat.lb n)

notation γ " ↪●MN{" dq "} " n => auth_own γ dq n
notation γ " ↪●MN " n => auth_own γ (DFrac.own 1) n
notation γ " ↪●MN□ " n => auth_own γ DFrac.discard n
notation γ " ↪◯MN " n => lb_own γ n

@[rocq_alias mono_nat_auth_own_timeless]
instance : Timeless (PROP := IProp GF) (γ ↪●MN{dq} n) := by
  unfold auth_own
  infer_instance

@[rocq_alias mono_nat_auth_own_persistent]
instance : Persistent (PROP := IProp GF) (γ ↪●MN□ n) := by
  unfold auth_own
  infer_instance

@[rocq_alias mono_nat_lb_own_timeless]
instance : Timeless (PROP := IProp GF) (γ ↪◯MN n) := by
  unfold lb_own
  infer_instance

@[rocq_alias mono_nat_lb_own_persistent]
instance : Persistent (PROP := IProp GF) (γ ↪◯MN n) := by
  unfold lb_own
  infer_instance

instance : IsUnit (◯MN 0 : MonoNat) := by
  infer_instance

@[rocq_alias mono_nat_auth_own_fractional]
instance {γ n} : Fractional (PROP := IProp GF) (fun q : Qp => γ ↪●MN{.own q} n) where
  fractional p q := by
    unfold auth_own
    rw [←iOwn_op.to_eq]
    refine BI.equiv_iff.mp ?_
    exact OFE.Equiv.of_eq (congrArg (iOwn _) (auth_dfrac_op (.own p) (.own q) _))

@[rocq_alias mono_nat_auth_own_agree]
theorem auth_own_agree (γ : GName) (dq1 dq2 : DFrac) (n1 n2 : MaxNat) :
  ⊢@{IProp GF} (γ ↪●MN{dq1} n1) -∗ (γ ↪●MN{dq2} n2) -∗ ⌜✓ (dq1 • dq2) ∧ n1 = n2⌝ := by
  unfold auth_own
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  exact (auth_dfrac_op_valid dq1 dq2 n1 n2).mp Hvalid

@[rocq_alias mono_nat_auth_own_exclusive]
theorem auth_own_exclusive (γ : GName) (n1 n2 : MaxNat) :
  ⊢@{IProp GF} (γ ↪●MN n1) -∗ (γ ↪●MN n2) -∗ False := by
  unfold auth_own
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  exact (auth_op_valid _ _).mp Hvalid

@[rocq_alias mono_nat_auth_lb_own_valid]
theorem auth_lb_own_valid (γ : GName) (dq : DFrac) (n m : MaxNat) :
  ⊢@{IProp GF} (γ ↪●MN{dq} n) -∗ (γ ↪◯MN m) -∗ ⌜✓ dq ∧ m ≤ n⌝ := by
  unfold auth_own lb_own
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  exact (both_dfrac_valid dq n m).mp Hvalid

@[rocq_alias mono_nat_lb_own_get]
theorem lb_own_get (γ : GName) (dq : DFrac) (n : MaxNat) :
  ⊢@{IProp GF} (γ ↪●MN{dq} n) -∗ (γ ↪◯MN n) := by
  unfold auth_own lb_own
  iintro H
  iapply iOwn_mono $$ H
  exact included _ _

@[rocq_alias mono_nat_lb_own_le]
theorem lb_own_le (γ : GName) (n n' : MaxNat) (h : n' ≤ n) :
  ⊢@{IProp GF} (γ ↪◯MN n) -∗ (γ ↪◯MN n') := by
  unfold lb_own
  iintro H
  iapply iOwn_mono $$ H
  exact lb_mono _ _ h

@[rocq_alias mono_nat_lb_own_0]
theorem lb_own_0 {GF : BundledGFunctors} [MonoNatG GF] (γ : GName) :
  ⊢@{IProp GF} |==> (γ ↪◯MN 0) := by
  unfold lb_own
  iapply iOwn_unit

@[rocq_alias mono_nat_own_alloc_strong]
theorem own_alloc_strong (P : Nat → Prop) n
  (hP : ∀ N, ∃ k, N ≤ k ∧ P k) :
  ⊢@{IProp GF} |==> ∃ γ, ⌜P γ⌝ ∗ (γ ↪●MN n) ∗ γ ↪◯MN n := by
  unfold auth_own lb_own
  imod iOwn_alloc_strong (F := MonoNatRF) ((●MN n) • (◯MN n)) P hP with ⟨%γ, ⟨H1, H2⟩⟩
  · simp [both_valid]
  imodintro
  iexists γ
  iframe H1
  icases iOwn_op $$ H2 with ⟨$,$⟩

@[rocq_alias mono_nat_own_alloc]
theorem own_alloc {GF : BundledGFunctors} [MonoNatG GF] (n : MaxNat) :
  ⊢@{IProp GF} |==> (∃ γ, (γ ↪●MN n) ∗ (γ ↪◯MN n)) := by
  imod (own_alloc_strong (λ _ => True) n) with ⟨%γ, ⟨-, H⟩⟩
  · intro n; exists n; simp
  · iexists γ
    imodintro
    iframe

@[rocq_alias mono_nat_own_update]
theorem own_update {GF : BundledGFunctors} [MonoNatG GF] (γ : GName) (n n' : MaxNat) (h : n ≤ n') :
  ⊢@{IProp GF} (γ ↪●MN n) ==∗ (γ ↪●MN n') ∗ (γ ↪◯MN n') := by
  iintro H
  ihave >Hauth : |==> (γ ↪●MN n') $$ [H]
  · unfold auth_own
    iapply iOwn_update $$ H
    exact update _ h
  · imodintro
    ihave #$ := lb_own_get $$ Hauth
    iframe

@[rocq_alias mono_nat_own_persist]
theorem own_persist (γ : GName) (dq : DFrac) (a : MaxNat) :
  ⊢@{IProp GF} (γ ↪●MN{dq} a) ==∗ (γ ↪●MN□ a) := by
  unfold auth_own
  iintro H
  iapply iOwn_update $$ H
  exact auth_persist _ _

@[rocq_alias mono_nat_own_unpersist]
theorem own_unpersist {GF : BundledGFunctors} [MonoNatG GF] (γ : GName) (a : MaxNat) :
  ⊢@{IProp GF} (γ ↪●MN□ a) ==∗ (∃ q, γ ↪●MN{DFrac.own q} a) := by
  unfold auth_own
  iintro H
  imod iOwn_updateP (auth_unpersist _) $$ H with ⟨%a, ⟨%H, H⟩⟩
  obtain ⟨q, Hq⟩ := H
  imodintro
  iexists q
  rw [←Hq]
  iframe

end MonoNat

end Iris
