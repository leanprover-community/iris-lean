/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Init -- shake: keep
public import Iris.BI.Lib.MonoNat

@[expose] public section

/-! # Ghost state for a monotonically increasing non-negative integer -/

namespace Iris
open BI

@[rocq_alias mono_ZG]
class MonoZG (GF : BundledGFunctors) where
  natG : MonoNatG GF

attribute [reducible, instance] MonoZG.natG

#rocq_ignore «mono_ZΣ» "Superseded by the `MonoZG` typeclass on `BundledGFunctors`."

namespace MonoZ

variable {GF : BundledGFunctors} [MonoZG GF]

@[rocq_alias mono_Z_auth_own]
def auth_own (γ : GName) (dq : DFrac) (n : Int) : IProp GF := iprop%
  ⌜0 ≤ n⌝ ∗ (γ ↪●MN{dq} MaxNat.ofNat n.toNat)

#rocq_ignore mono_Z_auth_own_def "`mono_Z_auth_own` is defined directly without `seal`/`unseal`."
#rocq_ignore mono_Z_auth_own_aux "`mono_Z_auth_own` is defined directly without `seal`/`unseal`."
#rocq_ignore mono_Z_auth_own_unseal "`mono_Z_auth_own` is defined directly without `seal`/`unseal`."

@[rocq_alias mono_Z_lb_own]
def lb_own (γ : GName) (n : Int) : IProp GF := iprop%
  ⌜0 ≤ n⌝ ∗ (γ ↪◯MN MaxNat.ofNat n.toNat)

#rocq_ignore mono_Z_lb_own_def "`mono_Z_lb_own` is defined directly without `seal`/`unseal`."
#rocq_ignore mono_Z_lb_own_aux "`mono_Z_lb_own` is defined directly without `seal`/`unseal`."
#rocq_ignore mono_Z_lb_own_unseal "`mono_Z_lb_own` is defined directly without `seal`/`unseal`."

notation γ " ↪●MZ{" dq "} " n => auth_own γ dq n
notation γ " ↪●MZ " n => auth_own γ (DFrac.own 1) n
notation γ " ↪●MZ□ " n => auth_own γ DFrac.discard n
notation γ " ↪◯MZ " n => lb_own γ n

@[rocq_alias mono_Z_auth_own_timeless]
instance : Timeless (PROP := IProp GF) (γ ↪●MZ{dq} n) := by
  unfold auth_own
  infer_instance

@[rocq_alias mono_Z_auth_own_persistent]
instance : Persistent (PROP := IProp GF) (γ ↪●MZ□ n) := by
  unfold auth_own
  infer_instance

@[rocq_alias mono_Z_lb_own_timeless]
instance : Timeless (PROP := IProp GF) (γ ↪◯MZ n) := by
  unfold lb_own
  infer_instance

@[rocq_alias mono_Z_lb_own_persistent]
instance : Persistent (PROP := IProp GF) (γ ↪◯MZ n) := by
  unfold lb_own
  infer_instance

@[rocq_alias mono_Z_auth_own_fractional]
instance {γ n} : Fractional (PROP := IProp GF) (fun q : Qp => γ ↪●MZ{.own q} n) where
  fractional p q := by
    unfold auth_own
    constructor
    · iintro ⟨%Hn, H1, H2⟩
      iframe %Hn H1 H2
    · iintro ⟨⟨%Hn, H1⟩, -, H2⟩
      icombine H1 H2 as $
      iframe %Hn

@[rocq_alias mono_Z_auth_own_as_fractional]
instance {γ n} (q : Qp) : AsFractional (PROP := IProp GF) (γ ↪●MZ{.own q} n) ioΦ
    (fun q : Qp => γ ↪●MZ{.own q} n) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := inferInstance

@[rocq_alias mono_Z_auth_own_agree]
theorem auth_own_agree (γ : GName) (dq1 dq2 : DFrac) (n1 n2 : Int) :
    ⊢@{IProp GF} (γ ↪●MZ{dq1} n1) -∗ (γ ↪●MZ{dq2} n2) -∗ ⌜✓ (dq1 • dq2) ∧ n1 = n2⌝ := by
  unfold auth_own
  iintro ⟨%Hn1, H1⟩ ⟨%Hn2, H2⟩
  icases MonoNat.auth_own_agree $$ H1 H2 with %⟨Hdq, Heq⟩
  ipureintro
  simp only [MaxNat.eq_toNat] at Heq
  exact ⟨Hdq, by omega⟩

@[rocq_alias mono_Z_auth_own_exclusive]
theorem auth_own_exclusive (γ : GName) (n1 n2 : Int) :
    ⊢@{IProp GF} (γ ↪●MZ n1) -∗ (γ ↪●MZ n2) -∗ False := by
  iintro H1 H2
  icases auth_own_agree $$ H1 H2 with %⟨Hdq, -⟩
  ipureintro
  exact DFrac.own_whole_exclusive.exclusive0_l _ Hdq.validN

@[rocq_alias mono_Z_auth_lb_own_valid]
theorem auth_lb_own_valid (γ : GName) (dq : DFrac) (n m : Int) :
    ⊢@{IProp GF} (γ ↪●MZ{dq} n) -∗ (γ ↪◯MZ m) -∗ ⌜✓ dq ∧ m ≤ n⌝ := by
  unfold auth_own lb_own
  iintro ⟨%Hn, Hauth⟩ ⟨%Hm, Hlb⟩
  icases MonoNat.auth_lb_own_valid $$ Hauth Hlb with %⟨Hdq, Hle⟩
  ipureintro
  simp only [MaxNat.le_toNat] at Hle
  exact ⟨Hdq, by omega⟩

@[rocq_alias mono_Z_lb_own_get]
theorem lb_own_get (γ : GName) (dq : DFrac) (n : Int) :
    ⊢@{IProp GF} (γ ↪●MZ{dq} n) -∗ (γ ↪◯MZ n) := by
  unfold auth_own lb_own
  iintro ⟨$, H⟩
  iapply MonoNat.lb_own_get $$ H

@[rocq_alias mono_Z_lb_own_le]
theorem lb_own_le (γ : GName) (n n' : Int) (h : n' ≤ n) (h0 : 0 ≤ n') :
    ⊢@{IProp GF} (γ ↪◯MZ n) -∗ (γ ↪◯MZ n') := by
  unfold lb_own
  iintro ⟨-, H⟩
  iframe %h0
  iapply MonoNat.lb_own_le (h := by simp only [MaxNat.le_toNat]; omega) $$ H

@[rocq_alias mono_Z_lb_own_0]
theorem lb_own_0 (γ : GName) : ⊢@{IProp GF} |==> (γ ↪◯MZ 0) := by
  unfold lb_own
  simp only [Int.toNat_zero]
  imod MonoNat.lb_own_0 with H
  imodintro
  iframe H
  ipureintro
  omega

@[rocq_alias mono_Z_own_alloc]
theorem own_alloc (n : Int) (h : 0 ≤ n) :
    ⊢@{IProp GF} |==> (∃ γ, (γ ↪●MZ n) ∗ (γ ↪◯MZ n)) := by
  unfold auth_own lb_own
  imod (MonoNat.own_alloc (MaxNat.ofNat n.toNat)) with ⟨%γ, H1, H2⟩
  imodintro
  iexists γ
  iframe %h H1 H2

@[rocq_alias mono_Z_own_update]
theorem own_update (γ : GName) (n n' : Int) (h : n ≤ n') :
    ⊢@{IProp GF} (γ ↪●MZ n) ==∗ (γ ↪●MZ n') ∗ (γ ↪◯MZ n') := by
  iintro H
  ihave >Hauth : |==> (γ ↪●MZ n') $$ [H]
  · unfold auth_own
    icases H with ⟨%Hn, H⟩
    imod MonoNat.own_update (n' := MaxNat.ofNat n'.toNat)
      (h := by simp only [MaxNat.le_toNat]; omega) $$ H with ⟨H, -⟩
    imodintro
    iframe H
    ipureintro
    omega
  · imodintro
    ihave #$ := lb_own_get $$ Hauth
    iframe

@[rocq_alias mono_Z_own_persist]
theorem own_persist (γ : GName) (dq : DFrac) (a : Int) :
    ⊢@{IProp GF} (γ ↪●MZ{dq} a) ==∗ (γ ↪●MZ□ a) := by
  unfold auth_own
  iintro ⟨$, H⟩
  iapply MonoNat.own_persist $$ H

@[rocq_alias mono_Z_own_unpersist]
theorem own_unpersist (γ : GName) (a : Int) :
    ⊢@{IProp GF} (γ ↪●MZ□ a) ==∗ (∃ q, γ ↪●MZ{DFrac.own q} a) := by
  unfold auth_own
  iintro ⟨%Ha, H⟩
  imod MonoNat.own_unpersist $$ H with ⟨%q, H⟩
  imodintro
  iexists q
  iframe %Ha H

end MonoZ

end Iris
