/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Algebra.CMRA
import Iris.Algebra.Updates
import Iris.Algebra.LocalUpdates
import Iris.Std.RocqAlias

namespace Iris

inductive Csum (α β : Type _) where
  | inl : α → Csum α β
  | inr : β → Csum α β
  | invalid : Csum α β

open Csum OFE CMRA

/-! ## OFE -/

@[simp] protected def Csum.Equiv [OFE α] [OFE β] : Csum α β → Csum α β → Prop
  | inl a, inl a' => a ≡ a'
  | inr b, inr b' => b ≡ b'
  | invalid, invalid => True
  | _, _ => False

@[simp] protected def Csum.Dist [OFE α] [OFE β] (n : Nat) : Csum α β → Csum α β → Prop
  | inl a, inl a' => a ≡{n}≡ a'
  | inr b, inr b' => b ≡{n}≡ b'
  | invalid, invalid => True
  | _, _ => False

theorem Csum.dist_eqv [OFE α] [OFE β] {n} : Equivalence (Csum.Dist (α := α) (β := β) n) where
  refl {x} := by cases x with
    | inl => exact Dist.rfl
    | inr => exact Dist.rfl
    | invalid => trivial
  symm {x y} h := by
    cases x with
    | inl => cases y with
      | inl => exact Dist.symm h
      | _ => exact h
    | inr => cases y with
      | inr => exact Dist.symm h
      | _ => exact h
    | invalid => cases y with
      | invalid => trivial
      | _ => exact h
  trans {x y z} h₁ h₂ := by
    cases x with
    | inl => cases y with
      | inl => cases z with
        | inl => exact Dist.trans h₁ h₂
        | _ => exact h₂.elim
      | _ => exact h₁.elim
    | inr => cases y with
      | inr => cases z with
        | inr => exact Dist.trans h₁ h₂
        | _ => exact h₂.elim
      | _ => exact h₁.elim
    | invalid => cases y with
      | invalid => cases z with
        | invalid => trivial
        | _ => exact h₂.elim
      | _ => exact h₁.elim

instance [OFE α] [OFE β] : OFE (Csum α β) where
  Equiv := Csum.Equiv
  Dist := Csum.Dist
  dist_eqv := Csum.dist_eqv
  equiv_dist {x y} := by
    constructor
    · intro h n
      cases x with
      | inl => cases y with
        | inl => exact Equiv.dist h
        | _ => exact h
      | inr => cases y with
        | inr => exact Equiv.dist h
        | _ => exact h
      | invalid => cases y with
        | invalid => trivial
        | _ => exact h
    · intro h
      cases x with
      | inl => cases y with
        | inl => exact equiv_dist.mpr h
        | _ => exact (h 0).elim
      | inr => cases y with
        | inr => exact equiv_dist.mpr h
        | _ => exact (h 0).elim
      | invalid => cases y with
        | invalid => trivial
        | _ => exact (h 0).elim
  dist_lt {n x y m} hn hlt := by
    cases x with
    | inl => cases y with
      | inl => exact Dist.lt hn hlt
      | _ => exact hn.elim
    | inr => cases y with
      | inr => exact Dist.lt hn hlt
      | _ => exact hn.elim
    | invalid => cases y with
      | invalid => trivial
      | _ => exact hn.elim

instance [OFE α] [OFE β] : NonExpansive (inl (α := α) (β := β)) where
  ne _ _ _ h := h

instance [OFE α] [OFE β] : NonExpansive (inr (α := α) (β := β)) where
  ne _ _ _ h := h

@[rocq_alias Cinl_inj]
theorem Csum.inl_inj [OFE α] [OFE β] {a a' : α} (h : (inl (β := β) a) ≡ inl a') : a ≡ a' := h

@[rocq_alias Cinl_inj_dist]
theorem Csum.inl_injN [OFE α] [OFE β] {a a' : α} (h : (inl (β := β) a) ≡{n}≡ inl a') :
    a ≡{n}≡ a' := h

@[rocq_alias Cinr_inj]
theorem Csum.inr_inj [OFE α] [OFE β] {b b' : β} (h : (inr (α := α) b) ≡ inr b') : b ≡ b' := h

@[rocq_alias Cinr_inj_dist]
theorem Csum.inr_injN [OFE α] [OFE β] {b b' : β} (h : (inr (α := α) b) ≡{n}≡ inr b') :
    b ≡{n}≡ b' := h

instance [OFE α] [OFE β] [OFE.Discrete α] [OFE.Discrete β] : OFE.Discrete (Csum α β) where
  discrete_0 {x y} h := by
    cases x with
    | inl => cases y with
      | inl => exact discrete_0 (α := α) h
      | _ => exact h
    | inr => cases y with
      | inr => exact discrete_0 (α := β) h
      | _ => exact h
    | invalid => cases y with
      | invalid => trivial
      | _ => exact h

instance [OFE α] [OFE β] [OFE.Leibniz α] [OFE.Leibniz β] : OFE.Leibniz (Csum α β) where
  eq_of_eqv {x y} h := by
    cases x with
    | inl => cases y with
      | inl => exact congrArg _ (eq_of_eqv h)
      | _ => exact h.elim
    | inr => cases y with
      | inr => exact congrArg _ (eq_of_eqv h)
      | _ => exact h.elim
    | invalid => cases y with
      | invalid => rfl
      | _ => exact h.elim

instance [OFE α] [OFE β] {a : α} [DiscreteE a] : DiscreteE (inl (β := β) a) where
  discrete {x} h := by
    cases x with
    | inl => exact DiscreteE.discrete (x := a) h
    | _ => exact h

instance [OFE α] [OFE β] {b : β} [DiscreteE b] : DiscreteE (inr (α := α) b) where
  discrete {x} h := by
    cases x with
    | inr => exact DiscreteE.discrete (x := b) h
    | _ => exact h

instance [OFE α] [OFE β] : DiscreteE (@invalid α β) where
  discrete {x} h := by cases x with | _ => exact h

/-! ## COFE -/

@[simp] def Csum.getInlD (x : Csum α β) (dflt : α) : α :=
  match x with
  | inl a => a
  | _ => dflt

@[simp] def Csum.getInrD (x : Csum α β) (dflt : β) : β :=
  match x with
  | inr b => b
  | _ => dflt

@[rocq_alias csum_chain_l]
def csumChainL [OFE α] [OFE β] (c : Chain (Csum α β)) (a : α) : Chain α where
  chain n := (c n).getInlD a
  cauchy {n i} h := by
    simp only [Csum.getInlD]
    have hc := c.cauchy h
    revert hc
    cases c.chain i
    all_goals cases c.chain n
    all_goals simp [OFE.Dist]

@[rocq_alias csum_chain_r]
def csumChainR [OFE α] [OFE β] (c : Chain (Csum α β)) (b : β) : Chain β where
  chain n := (c n).getInrD b
  cauchy {n i} h := by
    simp only [Csum.getInrD]
    have hc := c.cauchy h
    revert hc
    cases c.chain i
    all_goals cases c.chain n
    all_goals simp [OFE.Dist]

instance [OFE α] [OFE β] [IsCOFE α] [IsCOFE β] : IsCOFE (Csum α β) where
  compl c :=
    match c 0 with
    | inl a => inl (IsCOFE.compl (csumChainL c a))
    | inr b => inr (IsCOFE.compl (csumChainR c b))
    | invalid => invalid
  conv_compl {n c} := by
    have h0n := c.cauchy (Nat.zero_le n)
    revert h0n
    rcases e0 : c.chain 0 with a | b | _
    · rcases en : c.chain n with a' | b' | _
      · intro h0n
        show IsCOFE.compl (csumChainL c a) ≡{n}≡ a'
        refine Dist.trans COFE.conv_compl ?_
        simp [csumChainL, en]
      · exact id
      · exact id
    · rcases en : c.chain n with a' | b' | _
      · exact id
      · intro h0n
        show IsCOFE.compl (csumChainR c b) ≡{n}≡ b'
        refine Dist.trans COFE.conv_compl ?_
        simp [csumChainR, en]
      · exact id
    · rcases en : c.chain n with a' | b' | _
      · exact id
      · exact id
      · intro
        trivial

/-! ## CMRA -/

@[simp] abbrev Csum.valid [CMRA α] [CMRA β] : Csum α β → Prop
  | inl a => ✓ a
  | inr b => ✓ b
  | invalid => False

@[simp] abbrev Csum.validN [CMRA α] [CMRA β] (n : Nat) : Csum α β → Prop
  | inl a => ✓{n} a
  | inr b => ✓{n} b
  | invalid => False

abbrev Csum.pcore [CMRA α] [CMRA β] : Csum α β → Option (Csum α β)
  | inl a => (CMRA.pcore a).map inl
  | inr b => (CMRA.pcore b).map inr
  | invalid => some invalid

abbrev Csum.op [CMRA α] [CMRA β] : Csum α β → Csum α β → Csum α β
  | inl a, inl a' => inl (a • a')
  | inr b, inr b' => inr (b • b')
  | _, _ => invalid

@[rocq_alias Cinl_op]
theorem Csum.inl_op [CMRA α] [CMRA β] (a a' : α) :
    inl (β := β) (a • a') = Csum.op (inl a) (inl a') := rfl

@[rocq_alias Cinr_op]
theorem Csum.inr_op [CMRA α] [CMRA β] (b b' : β) :
    inr (α := α) (b • b') = Csum.op (inr b) (inr b') := rfl

private theorem pcore_map_inl_eq [CMRA α] {a : α} {cx : Csum α β}
    (h : (CMRA.pcore a).map Csum.inl = some cx) :
    ∃ ca, CMRA.pcore a = some ca ∧ cx = inl ca := by
  cases hpa : CMRA.pcore a with
  | none => simp_all
  | some => simp_all

private theorem pcore_map_inr_eq [CMRA β] {b : β} {cx : Csum α β}
    (h : (CMRA.pcore b).map Csum.inr = some cx) :
    ∃ cb, CMRA.pcore b = some cb ∧ cx = inr cb := by
  cases hpb : CMRA.pcore b with
  | none => simp_all
  | some => simp_all

instance [CMRA α] [CMRA β] : CMRA (Csum α β) where
  pcore := Csum.pcore
  op := Csum.op
  Valid := Csum.valid
  ValidN := Csum.validN
  op_ne {x} := ⟨fun {n y₁ y₂} hy => by
    cases x with
    | inl a => cases y₁ with
      | inl => cases y₂ with
        | inl => exact Dist.op_r hy
        | _ => exact hy
      | _ => cases y₂ with
        | _ => trivial
    | inr b => cases y₁ with
      | inr => cases y₂ with
        | inr => exact Dist.op_r hy
        | _ => exact hy
      | _ => cases y₂ with
        | _ => trivial
    | invalid => cases y₁ with
      | _ => cases y₂ with
        | _ => trivial⟩
  pcore_ne {n x y cx} hxy hpx := by
    cases x with
    | inl a => cases y with
      | inl a' =>
        obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq hpx
        obtain ⟨cy, hcy, ecy⟩ := CMRA.pcore_ne hxy hpa
        exact ⟨inl cy, by simp [Csum.pcore, hcy], ecy⟩
      | inr => exact hxy.elim
      | invalid => exact hxy.elim
    | inr b => cases y with
      | inr b' =>
        obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq hpx
        obtain ⟨cy, hcy, ecy⟩ := CMRA.pcore_ne hxy hpb
        exact ⟨inr cy, by simp [Csum.pcore, hcy], ecy⟩
      | inl => exact hxy.elim
      | invalid => exact hxy.elim
    | invalid => cases y with
      | invalid =>
        simp [Csum.pcore] at hpx
        subst hpx
        exact ⟨invalid, rfl, trivial⟩
      | inl => exact hxy.elim
      | inr => exact hxy.elim
  validN_ne {n x y} h hv := by
    cases x with
    | inl => cases y with
      | inl => exact CMRA.validN_ne h hv
      | _ => exact h.elim
    | inr => cases y with
      | inr => exact CMRA.validN_ne h hv
      | _ => exact h.elim
    | invalid => cases y with
      | invalid => trivial
      | _ => exact h.elim
  valid_iff_validN {x} := by
    cases x with
    | inl => simp [CMRA.valid_iff_validN]
    | inr => simp [CMRA.valid_iff_validN]
    | invalid => simp
  validN_succ := by
    intro x _ h
    show Csum.validN _ x
    cases x with
    | inl => exact CMRA.validN_succ h
    | inr => exact CMRA.validN_succ h
    | invalid => exact h
  assoc {x y z} := by
    cases x with
    | inl => cases y with
      | inl => cases z with
        | inl => exact CMRA.assoc
        | _ => trivial
      | _ => cases z with
        | _ => trivial
    | inr => cases y with
      | inr => cases z with
        | inr => exact CMRA.assoc
        | _ => trivial
      | _ => cases z with
        | _ => trivial
    | invalid => cases y with
      | _ => cases z with
        | _ => trivial
  comm {x y} := by
    cases x with
    | inl => cases y with
      | inl => exact CMRA.comm
      | _ => trivial
    | inr => cases y with
      | inr => exact CMRA.comm
      | _ => trivial
    | invalid => cases y with
      | _ => trivial
  pcore_op_left {x cx} hpx := by
    cases x with
    | inl a =>
      obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq hpx
      exact CMRA.pcore_op_left hpa
    | inr b =>
      obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq hpx
      exact CMRA.pcore_op_left hpb
    | invalid =>
      simp [Csum.pcore] at hpx
      subst hpx
      trivial
  pcore_idem {x cx} hpx := by
    cases x with
    | inl a =>
      obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq hpx
      exact Option.map_forall₂ inl (CMRA.pcore_idem hpa)
    | inr b =>
      obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq hpx
      exact Option.map_forall₂ inr (CMRA.pcore_idem hpb)
    | invalid =>
      simp [Csum.pcore] at hpx
      subst hpx
      simp [Csum.pcore]
  pcore_op_mono {x cx} hpx y := by
    cases x with
    | inl a => cases y with
      | inl a' =>
        obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq hpx
        obtain ⟨cy, hcy⟩ := CMRA.pcore_op_mono hpa a'
        exact ⟨inl cy, Option.map_forall₂ inl hcy⟩
      | inr =>
        obtain ⟨ca, _, rfl⟩ := pcore_map_inl_eq hpx
        exact ⟨invalid, trivial⟩
      | invalid =>
        obtain ⟨ca, _, rfl⟩ := pcore_map_inl_eq hpx
        exact ⟨invalid, trivial⟩
    | inr b => cases y with
      | inr b' =>
        obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq hpx
        obtain ⟨cy, hcy⟩ := CMRA.pcore_op_mono hpb b'
        exact ⟨inr cy, Option.map_forall₂ inr hcy⟩
      | inl =>
        obtain ⟨cb, _, rfl⟩ := pcore_map_inr_eq hpx
        exact ⟨invalid, trivial⟩
      | invalid =>
        obtain ⟨cb, _, rfl⟩ := pcore_map_inr_eq hpx
        exact ⟨invalid, trivial⟩
    | invalid =>
      simp [Csum.pcore] at hpx
      subst hpx
      exact ⟨invalid, trivial⟩
  validN_op_left {n x y} h := by
    cases x with
    | inl => cases y with
      | inl => exact CMRA.validN_op_left h
      | _ => exact h.elim
    | inr => cases y with
      | inr => exact CMRA.validN_op_left h
      | _ => exact h.elim
    | invalid => exact h.elim
  extend {n x y₁ y₂} hv he := by
    cases x with
    | inl a => cases y₁ with
      | inl => cases y₂ with
        | inl =>
          obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := CMRA.extend hv he
          exact ⟨inl z₁, inl z₂, hz, hz₁, hz₂⟩
        | _ => exact he.elim
      | _ => cases y₂ with
        | _ => exact he.elim
    | inr b => cases y₁ with
      | inr => cases y₂ with
        | inr =>
          obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := CMRA.extend hv he
          exact ⟨inr z₁, inr z₂, hz, hz₁, hz₂⟩
        | _ => exact he.elim
      | _ => cases y₂ with
        | _ => exact he.elim
    | invalid => cases y₁ with
      | _ => cases y₂ with
        | _ => exact hv.elim

@[rocq_alias Cinl_valid]
theorem Csum.inl_valid [CMRA α] [CMRA β] {a : α} : ✓ (inl (β := β) a) ↔ ✓ a := .rfl

@[rocq_alias Cinr_valid]
theorem Csum.inr_valid [CMRA α] [CMRA β] {b : β} : ✓ (inr (α := α) b) ↔ ✓ b := .rfl

/-! ## CMRA Discrete -/

instance [CMRA α] [CMRA β] [CMRA.Discrete α] [CMRA.Discrete β] :
    CMRA.Discrete (Csum α β) where
  discrete_valid {x} hv := by
    cases x with
    | inl a =>
      show ✓ a
      exact CMRA.discrete_valid hv
    | inr b =>
      show ✓ b
      exact CMRA.discrete_valid hv
    | invalid => exact hv

/-! ## CoreId -/

instance [CMRA α] [CMRA β] {a : α} [CoreId a] : CoreId (inl (β := β) a) where
  core_id := Option.map_forall₂ inl core_id

instance [CMRA α] [CMRA β] {b : β} [CoreId b] : CoreId (inr (α := α) b) where
  core_id := Option.map_forall₂ inr core_id

/-! ## Exclusive -/

instance [CMRA α] [CMRA β] {a : α} [Exclusive a] : Exclusive (inl (β := β) a) where
  exclusive0_l y h := by
    cases y with
    | inl a' => exact Exclusive.exclusive0_l (x := a) a' h
    | inr => exact h
    | invalid => exact h

instance [CMRA α] [CMRA β] {b : β} [Exclusive b] : Exclusive (inr (α := α) b) where
  exclusive0_l y h := by
    cases y with
    | inr b' => exact Exclusive.exclusive0_l (x := b) b' h
    | inl => exact h
    | invalid => exact h

/-! ## Cancelable -/

instance [CMRA α] [CMRA β] {a : α} [Cancelable a] : Cancelable (inl (β := β) a) where
  cancelableN {n y z} hv he := by
    cases y with
    | inl => cases z with
      | inl => exact cancelableN (x := a) hv he
      | _ => exact he
    | _ => cases z with
      | _ => trivial

instance [CMRA α] [CMRA β] {b : β} [Cancelable b] : Cancelable (inr (α := α) b) where
  cancelableN {n y z} hv he := by
    cases y with
    | inr => cases z with
      | inr => exact cancelableN (x := b) hv he
      | _ => exact he
    | _ => cases z with
      | _ => trivial

/-! ## IdFree -/

instance [CMRA α] [CMRA β] {a : α} [IdFree a] : IdFree (inl (β := β) a) where
  id_free0_r y hv he := by
    cases y with
    | inl a' => exact id_free0_r (x := a) _ hv he
    | _ => trivial

instance [CMRA α] [CMRA β] {b : β} [IdFree b] : IdFree (inr (α := α) b) where
  id_free0_r y hv he := by
    cases y with
    | inr b' => exact id_free0_r (x := b) _ hv he
    | _ => trivial

/-! ## Included -/

@[rocq_alias csum_included]
theorem csum_included [CMRA α] [CMRA β] {x y : Csum α β} :
    x ≼ y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ a ≼ a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ b ≼ b') := by
  constructor
  · rintro ⟨z, hz⟩
    cases x with
    | inl a => cases z with
      | inl c => cases y with
        | inl a' =>
          right
          left
          exact ⟨a, a', rfl, rfl, c, hz⟩
        | inr => exact hz.elim
        | invalid => exact hz.elim
      | inr =>
        left
        cases y with | invalid => rfl | _ => exact hz.elim
      | invalid =>
        left
        cases y with | invalid => rfl | _ => exact hz.elim
    | inr b => cases z with
      | inr c => cases y with
        | inr b' =>
          right
          right
          exact ⟨b, b', rfl, rfl, c, hz⟩
        | inl => exact hz.elim
        | invalid => exact hz.elim
      | inl =>
        left
        cases y with | invalid => rfl | _ => exact hz.elim
      | invalid =>
        left
        cases y with | invalid => rfl | _ => exact hz.elim
    | invalid => cases z with
      | _ =>
        left
        cases y with | invalid => rfl | _ => exact hz.elim
  · rintro (rfl | ⟨a, a', rfl, rfl, c, hc⟩ | ⟨b, b', rfl, rfl, c, hc⟩)
    · exact ⟨invalid, by cases x with
        | inl => rfl | inr => rfl | invalid => rfl⟩
    · exact ⟨inl c, hc⟩
    · exact ⟨inr c, hc⟩

@[rocq_alias Cinl_included]
theorem Csum.inl_included [CMRA α] [CMRA β] {a a' : α} :
    (inl (β := β) a) ≼ inl a' ↔ a ≼ a' := by
  constructor
  · rintro ⟨z, hz⟩
    cases z with
    | inl c => exact ⟨c, hz⟩
    | inr => exact hz.elim
    | invalid => exact hz.elim
  · rintro ⟨c, hc⟩
    exact ⟨inl c, hc⟩

@[rocq_alias Cinr_included]
theorem Csum.inr_included [CMRA α] [CMRA β] {b b' : β} :
    (inr (α := α) b) ≼ inr b' ↔ b ≼ b' := by
  constructor
  · rintro ⟨z, hz⟩
    cases z with
    | inr c => exact ⟨c, hz⟩
    | inl => exact hz.elim
    | invalid => exact hz.elim
  · rintro ⟨c, hc⟩
    exact ⟨inr c, hc⟩

@[rocq_alias CsumInvalid_included]
theorem Csum.invalid_included [CMRA α] [CMRA β] (x : Csum α β) : x ≼ invalid :=
  ⟨invalid, by cases x with | inl => rfl | inr => rfl | invalid => rfl⟩

@[rocq_alias csum_includedN]
theorem csum_includedN [CMRA α] [CMRA β] {n} {x y : Csum α β} :
    x ≼{n} y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ a ≼{n} a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ b ≼{n} b') := by
  constructor
  · rintro ⟨z, hz⟩
    cases x with
    | inl a => cases z with
      | inl c => cases y with
        | inl a' =>
          right
          left
          exact ⟨a, a', rfl, rfl, c, hz⟩
        | inr => exact hz.elim
        | invalid => exact hz.elim
      | inr =>
        left
        cases y with | invalid => rfl | _ => exact hz.elim
      | invalid =>
        left
        cases y with | invalid => rfl | _ => exact hz.elim
    | inr b => cases z with
      | inr c => cases y with
        | inr b' =>
          right
          right
          exact ⟨b, b', rfl, rfl, c, hz⟩
        | inl => exact hz.elim
        | invalid => exact hz.elim
      | inl =>
        left
        cases y with | invalid => rfl | _ => exact hz.elim
      | invalid =>
        left
        cases y with | invalid => rfl | _ => exact hz.elim
    | invalid => cases z with
      | _ =>
        left
        cases y with | invalid => rfl | _ => exact hz.elim
  · rintro (rfl | ⟨a, a', rfl, rfl, c, hc⟩ | ⟨b, b', rfl, rfl, c, hc⟩)
    · exact ⟨invalid, by cases x with
        | inl => exact Dist.rfl
        | inr => exact Dist.rfl
        | invalid => exact Dist.rfl⟩
    · exact ⟨inl c, hc⟩
    · exact ⟨inr c, hc⟩

/-! ## Updates -/

@[rocq_alias csum_update_l]
theorem csum_update_l [CMRA α] [CMRA β] {a₁ a₂ : α}
    (h : a₁ ~~> a₂) : (inl (β := β) a₁) ~~> inl a₂ := by
  intro n mz hv
  cases mz with
  | none => exact h n none hv
  | some z => cases z with
    | inl a' => exact h n (some a') hv
    | inr => exact hv.elim
    | invalid => exact hv.elim

@[rocq_alias csum_update_r]
theorem csum_update_r [CMRA α] [CMRA β] {b₁ b₂ : β}
    (h : b₁ ~~> b₂) : (inr (α := α) b₁) ~~> inr b₂ := by
  intro n mz hv
  cases mz with
  | none => exact h n none hv
  | some z => cases z with
    | inl => exact hv.elim
    | inr b' => exact h n (some b') hv
    | invalid => exact hv.elim

@[rocq_alias csum_updateP_l]
theorem csum_updateP_l [CMRA α] [CMRA β] {P : α → Prop} {Q : Csum α β → Prop} {a : α}
    (h : a ~~>: P) (hPQ : ∀ a', P a' → Q (inl a')) : (inl (β := β) a) ~~>: Q := by
  intro n mz hv
  cases mz with
  | none =>
    obtain ⟨c, hc, hvc⟩ := h n none hv
    exact ⟨inl c, hPQ c hc, hvc⟩
  | some z => cases z with
    | inl a' =>
      obtain ⟨c, hc, hvc⟩ := h n (some a') hv
      exact ⟨inl c, hPQ c hc, hvc⟩
    | inr => exact hv.elim
    | invalid => exact hv.elim

@[rocq_alias csum_updateP_r]
theorem csum_updateP_r [CMRA α] [CMRA β] {P : β → Prop} {Q : Csum α β → Prop} {b : β}
    (h : b ~~>: P) (hPQ : ∀ b', P b' → Q (inr b')) : (inr (α := α) b) ~~>: Q := by
  intro n mz hv
  cases mz with
  | none =>
    obtain ⟨c, hc, hvc⟩ := h n none hv
    exact ⟨inr c, hPQ c hc, hvc⟩
  | some z => cases z with
    | inl => exact hv.elim
    | inr b' =>
      obtain ⟨c, hc, hvc⟩ := h n (some b') hv
      exact ⟨inr c, hPQ c hc, hvc⟩
    | invalid => exact hv.elim

@[rocq_alias csum_updateP'_l]
theorem csum_updateP'_l [CMRA α] [CMRA β] {P : α → Prop} {a : α}
    (h : a ~~>: P) : (inl (β := β) a) ~~>: fun m' => ∃ a', m' = inl a' ∧ P a' :=
  csum_updateP_l h fun a' ha' => ⟨a', rfl, ha'⟩

@[rocq_alias csum_updateP'_r]
theorem csum_updateP'_r [CMRA α] [CMRA β] {P : β → Prop} {b : β}
    (h : b ~~>: P) : (inr (α := α) b) ~~>: fun m' => ∃ b', m' = inr b' ∧ P b' :=
  csum_updateP_r h fun b' hb' => ⟨b', rfl, hb'⟩

/-! ## Local Updates -/

@[rocq_alias csum_local_update_l]
theorem csum_local_update_l [CMRA α] [CMRA β] {a₁ a₂ a₁' a₂' : α}
    (h : (a₁, a₂) ~l~> (a₁', a₂')) :
    ((inl (β := β) a₁, inl a₂) ~l~> (inl a₁', inl a₂')) := by
  intro n mf hv he
  cases mf with
  | none => exact h n none hv he
  | some z => cases z with
    | inl a' => exact h n (some a') hv he
    | inr => exact he.elim
    | invalid => exact he.elim

@[rocq_alias csum_local_update_r]
theorem csum_local_update_r [CMRA α] [CMRA β] {b₁ b₂ b₁' b₂' : β}
    (h : (b₁, b₂) ~l~> (b₁', b₂')) :
    ((inr (α := α) b₁, inr b₂) ~l~> (inr b₁', inr b₂')) := by
  intro n mf hv he
  cases mf with
  | none => exact h n none hv he
  | some z => cases z with
    | inr b' => exact h n (some b') hv he
    | inl => exact he.elim
    | invalid => exact he.elim

/-! ## Functor -/

@[simp, rocq_alias csum_map]
def Csum.map (f : α → α') (g : β → β') : Csum α β → Csum α' β'
  | inl a => inl (f a)
  | inr b => inr (g b)
  | invalid => invalid

@[rocq_alias csum_map_id]
theorem csum_map_id {x : Csum α β} : Csum.map id id x = x := by
  cases x with
  | inl => simp
  | inr => simp
  | invalid => simp

@[rocq_alias csum_map_compose]
theorem csum_map_compose (f : α → α') (f' : α' → α'') (g : β → β') (g' : β' → β'')
    (x : Csum α β) : Csum.map (f' ∘ f) (g' ∘ g) x = Csum.map f' g' (Csum.map f g x) := by
  cases x with
  | inl => simp
  | inr => simp
  | invalid => simp

@[rocq_alias csum_map_ext]
theorem csum_map_ext [OFE α] [OFE α'] [OFE β] [OFE β'] (f f' : α → α') (g g' : β → β')
    (hf : ∀ x, f x ≡ f' x) (hg : ∀ x, g x ≡ g' x) (x : Csum α β) :
    Csum.map f g x ≡ Csum.map f' g' x := by
  cases x with
  | inl a =>
    simp [Csum.map]
    exact hf _
  | inr b =>
    simp [Csum.map]
    exact hg _
  | invalid => trivial

@[rocq_alias csum_map_cmra_ne]
theorem csum_map_ne [OFE α] [OFE α'] [OFE β] [OFE β'] {n}
    {f f' : α → α'} (hf : ∀ ⦃x₁ x₂⦄, x₁ ≡{n}≡ x₂ → f x₁ ≡{n}≡ f' x₂)
    {g g' : β → β'} (hg : ∀ ⦃x₁ x₂⦄, x₁ ≡{n}≡ x₂ → g x₁ ≡{n}≡ g' x₂)
    {x y : Csum α β} (hxy : x ≡{n}≡ y) :
    Csum.map f g x ≡{n}≡ Csum.map f' g' y := by
  cases x with
  | inl => cases y with
    | inl =>
      simp [Csum.map]
      exact hf hxy
    | _ => exact hxy
  | inr => cases y with
    | inr =>
      simp [Csum.map]
      exact hg hxy
    | _ => exact hxy
  | invalid => cases y with
    | invalid => trivial
    | _ => exact hxy

@[rocq_alias csumO_map]
def csumO_map [OFE α] [OFE α'] [OFE β] [OFE β'] (f : α -n> α') (g : β -n> β') :
    Csum α β -n> Csum α' β' where
  f := Csum.map f g
  ne := ⟨fun {_n} {_x₁} {_x₂} hxy =>
    csum_map_ne (fun _ _ h => f.ne.1 h) (fun _ _ h => g.ne.1 h) hxy⟩

@[rocq_alias csumO_map_ne]
theorem csumO_map_ne [OFE α] [OFE α'] [OFE β] [OFE β'] :
    NonExpansive₂ (csumO_map (α := α) (α' := α') (β := β) (β' := β')) where
  ne _ _ _ hf _ _ hg x := by
    cases x with
    | inl a =>
      simp [csumO_map, Csum.map]
      exact hf _
    | inr b =>
      simp [csumO_map, Csum.map]
      exact hg _
    | invalid => trivial

@[rocq_alias csumRF]
abbrev CsumOF (Fa Fb : COFE.OFunctorPre) : COFE.OFunctorPre :=
  fun A B _ _ => Csum (Fa A B) (Fb A B)

private def csumC_map [CMRA α] [CMRA α'] [CMRA β] [CMRA β']
    (fa : α -C> α') (fb : β -C> β') : Csum α β -C> Csum α' β' where
  f := Csum.map fa fb
  ne := (csumO_map fa.toHom fb.toHom).ne
  validN {n x} hv := by cases x with
    | inl a => exact fa.validN hv
    | inr b => exact fb.validN hv
    | invalid => exact hv
  pcore x := by
    cases x with
    | inl a =>
      show ((CMRA.pcore a).map inl).map (Csum.map fa fb) ≡ (CMRA.pcore (fa a)).map inl
      rw [Option.map_map]
      show (CMRA.pcore a).map (inl ∘ ⇑fa) ≡ _
      rw [show (CMRA.pcore a).map (inl ∘ ⇑fa) = ((CMRA.pcore a).map fa).map inl from
        (Option.map_map ..).symm]
      exact Option.map_forall₂ inl (fa.pcore a)
    | inr b =>
      show ((CMRA.pcore b).map inr).map (Csum.map fa fb) ≡ (CMRA.pcore (fb b)).map inr
      rw [Option.map_map]
      show (CMRA.pcore b).map (inr ∘ ⇑fb) ≡ _
      rw [show (CMRA.pcore b).map (inr ∘ ⇑fb) = ((CMRA.pcore b).map fb).map inr from
        (Option.map_map ..).symm]
      exact Option.map_forall₂ inr (fb.pcore b)
    | invalid => trivial
  op x y := by
    cases x with
    | inl => cases y with
      | inl => exact fa.op _ _
      | _ => trivial
    | inr => cases y with
      | inr => exact fb.op _ _
      | _ => trivial
    | invalid => cases y with
      | _ => trivial

instance {Fa Fb} [RFunctor Fa] [RFunctor Fb] : RFunctor (CsumOF Fa Fb) where
  map f g := csumC_map (RFunctor.map f g) (RFunctor.map f g)
  map_ne.ne _ _ _ hf _ _ hg x := by
    cases x with
    | inl =>
      simp [csumC_map, Csum.map]
      exact RFunctor.map_ne.ne hf hg _
    | inr =>
      simp [csumC_map, Csum.map]
      exact RFunctor.map_ne.ne hf hg _
    | invalid => trivial
  map_id x := by
    cases x with
    | inl =>
      simp [csumC_map, Csum.map]
      exact RFunctor.map_id _
    | inr =>
      simp [csumC_map, Csum.map]
      exact RFunctor.map_id _
    | invalid => simp [csumC_map, Csum.map]
  map_comp f g f' g' x := by
    cases x with
    | inl =>
      simp [csumC_map, Csum.map]
      exact RFunctor.map_comp f g f' g' _
    | inr =>
      simp [csumC_map, Csum.map]
      exact RFunctor.map_comp f g f' g' _
    | invalid => simp [csumC_map, Csum.map]

instance {Fa Fb} [RFunctorContractive Fa] [RFunctorContractive Fb] :
    RFunctorContractive (CsumOF Fa Fb) where
  map_contractive.1 {n x y} hKL z := by
    cases z with
    | inl a => exact RFunctorContractive.map_contractive.1 hKL _
    | inr b => exact RFunctorContractive.map_contractive.1 hKL _
    | invalid => trivial

end Iris
