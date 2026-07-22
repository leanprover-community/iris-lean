/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.Updates
public import Iris.Algebra.LocalUpdates
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

@[rocq_alias csum]
inductive Csum (α β : Type _) where
  | inl : α → Csum α β
  | inr : β → Csum α β
  | invalid : Csum α β

open Csum OFE CMRA

namespace Csum

/-! ## OFE -/

@[simp, rocq_alias csum_equiv] def Equiv [OFE α] [OFE β] : Csum α β → Csum α β → Prop
  | inl a, inl a' => a ≡ a'
  | inr b, inr b' => b ≡ b'
  | invalid, invalid => True
  | _, _ => False

@[simp, rocq_alias csum_dist] def Dist [OFE α] [OFE β] (n : Nat) : Csum α β → Csum α β → Prop
  | inl a, inl a' => a ≡{n}≡ a'
  | inr b, inr b' => b ≡{n}≡ b'
  | invalid, invalid => True
  | _, _ => False

theorem dist_eqv [OFE α] [OFE β] {n} : Equivalence (Csum.Dist (α := α) (β := β) n) where
  refl {x} := by cases x with
    | inl => exact Dist.rfl
    | inr => exact Dist.rfl
    | invalid => trivial
  symm {x y} h := by cases x <;> cases y <;> first | trivial | exact h.symm | exact h
  trans {x y z} h₁ h₂ := by
    cases x <;> cases y <;> cases z <;>
      first | trivial | exact h₁.trans h₂ | exact h₂.elim | exact h₁.elim

@[rocq_alias csumO]
instance [OFE α] [OFE β] : OFE (Csum α β) where
  Dist := Csum.Dist
  dist_eqv := dist_eqv
  eq_dist {x y} := by
    cases x <;> cases y <;> simp [Csum.Dist, eq_dist]
  dist_lt {n x y m} hn hlt := by
    cases x <;> cases y <;> first | exact OFE.Dist.lt hn hlt | exact hn.elim | trivial

#rocq_ignore csum_ofe_mixin "Not needed"

@[rocq_alias Cinl_ne]
instance [OFE α] [OFE β] : NonExpansive (inl (α := α) (β := β)) where
  ne _ _ _ := id

#rocq_ignore Cinl_proper "Derivable using NonExpansive.eqv"

@[rocq_alias Cinr_ne]
instance [OFE α] [OFE β] : NonExpansive (inr (α := α) (β := β)) where
  ne _ _ _ := id

#rocq_ignore Cinr_proper "Derivable using NonExpansive.eqv"

@[rocq_alias Cinl_inj]
theorem inl_inj [OFE α] [OFE β] {a a' : α} (h : (inl (β := β) a) ≡ inl a') : a ≡ a' := h

@[rocq_alias Cinl_inj_dist]
theorem inl_injN [OFE α] [OFE β] {a a' : α} (h : inl (β := β) a ≡{n}≡ inl a') : a ≡{n}≡ a' := h

@[rocq_alias Cinr_inj]
theorem inr_inj [OFE α] [OFE β] {b b' : β} (h : (inr (α := α) b) ≡ inr b') : b ≡ b' := h

@[rocq_alias Cinr_inj_dist]
theorem inr_injN [OFE α] [OFE β] {b b' : β} (h : inr (α := α) b ≡{n}≡ inr b') : b ≡{n}≡ b' := h

@[rocq_alias csum_ofe_discrete]
instance [OFE α] [OFE β] [OFE.Discrete α] [OFE.Discrete β] : OFE.Discrete (Csum α β) where
  discrete_0 {x y} h := by cases x <;> cases y <;>
    first
      | exact congrArg inl (discrete_0 (α := α) h)
      | exact congrArg inr (discrete_0 (α := β) h)
      | exact h.elim | trivial

@[rocq_alias Cinl_discrete]
instance [OFE α] [OFE β] {a : α} [DiscreteE a] : DiscreteE (inl (β := β) a) where
  discrete {x} h := by
    cases x with
    | inl => exact congrArg inl (DiscreteE.discrete (x := a) h)
    | inr => exact h.elim
    | invalid => exact h.elim

@[rocq_alias Cinr_discrete]
instance [OFE α] [OFE β] {b : β} [DiscreteE b] : DiscreteE (inr (α := α) b) where
  discrete {x} h := by
    cases x with
    | inl => exact h.elim
    | inr => exact congrArg inr (DiscreteE.discrete (x := b) h)
    | invalid => exact h.elim

instance [OFE α] [OFE β] : DiscreteE (@invalid α β) where
  discrete {x} h := by
    cases x with
    | inl => exact h.elim
    | inr => exact h.elim
    | invalid => exact rfl

/-! ## COFE -/

@[simp] def getInlD (x : Csum α β) (d : α) : α :=
  match x with | inl a => a | _ => d

@[simp] def getInrD (x : Csum α β) (d : β) : β :=
  match x with | inr b => b | _ => d

@[rocq_alias csum_chain_l]
def chainL [OFE α] [OFE β] (c : Chain (Csum α β)) (a : α) : Chain α where
  chain n := (c n).getInlD a
  cauchy {n i} h := by
    have hc := c.cauchy h; revert hc
    cases c.chain i <;> cases c.chain n <;> simp [OFE.Dist]

@[rocq_alias csum_chain_r]
def chainR [OFE α] [OFE β] (c : Chain (Csum α β)) (b : β) : Chain β where
  chain n := (c n).getInrD b
  cauchy {n i} h := by
    have hc := c.cauchy h; revert hc
    cases c.chain i <;> cases c.chain n <;> simp [OFE.Dist]

@[rocq_alias csum_cofe]
instance [OFE α] [OFE β] [IsCOFE α] [IsCOFE β] : IsCOFE (Csum α β) where
  compl c :=
    match c 0 with
    | inl a => inl (IsCOFE.compl (chainL c a))
    | inr b => inr (IsCOFE.compl (chainR c b))
    | invalid => invalid
  conv_compl {n c} := by
    have h0n := c.cauchy (Nat.zero_le n)
    revert h0n
    rcases e0 : c.chain 0 with a|b|_ <;> rcases en : c.chain n with a'|b'|_ <;> try (· exact id)
    · intro _
      show IsCOFE.compl (chainL c a) ≡{n}≡ a'
      refine OFE.Dist.trans COFE.conv_compl ?_
      simp [chainL, en]
    · intro _
      show IsCOFE.compl (chainR c b) ≡{n}≡ b'
      refine OFE.Dist.trans COFE.conv_compl ?_
      simp [chainR, en]

#rocq_ignore csum_compl "Included in IsCOFE instance"

/-! ## CMRA -/

@[simp] abbrev valid [CMRA α] [CMRA β] : Csum α β → Prop
  | inl a => ✓ a
  | inr b => ✓ b
  | invalid => False

@[simp] abbrev validN [CMRA α] [CMRA β] (n : Nat) : Csum α β → Prop
  | inl a => ✓{n} a
  | inr b => ✓{n} b
  | invalid => False

abbrev pcore [CMRA α] [CMRA β] : Csum α β → Option (Csum α β)
  | inl a => (CMRA.pcore a).map inl
  | inr b => (CMRA.pcore b).map inr
  | invalid => some invalid

abbrev op [CMRA α] [CMRA β] : Csum α β → Csum α β → Csum α β
  | inl a, inl a' => inl (a • a')
  | inr b, inr b' => inr (b • b')
  | _, _ => invalid

@[rocq_alias Cinl_op]
theorem inl_op [CMRA α] [CMRA β] (a a' : α) :
    inl (β := β) (a • a') = Csum.op (inl a) (inl a') := rfl

@[rocq_alias Cinr_op]
theorem inr_op [CMRA α] [CMRA β] (b b' : β) :
    inr (α := α) (b • b') = Csum.op (inr b) (inr b') := rfl

private theorem pcore_map_inl_eq [CMRA α] {a : α} {cx : Csum α β}
    (h : (CMRA.pcore a).map inl = some cx) :
    ∃ ca, CMRA.pcore a = some ca ∧ cx = inl ca := by
  cases _ : CMRA.pcore a <;> simp_all

private theorem pcore_map_inr_eq [CMRA β] {b : β} {cx : Csum α β}
    (h : (CMRA.pcore b).map inr = some cx) :
    ∃ cb, CMRA.pcore b = some cb ∧ cx = inr cb := by
  cases _ : CMRA.pcore b <;> simp_all

@[rocq_alias csum_cmra_mixin]
instance [CMRA α] [CMRA β] : CMRA (Csum α β) where
  pcore := Csum.pcore
  op := Csum.op
  Valid := Csum.valid
  ValidN := Csum.validN
  op_ne {x} := ⟨fun {n y₁ y₂} hy => by cases x <;> cases y₁ <;> cases y₂ <;>
    first | exact OFE.Dist.op_r hy | exact hy | trivial⟩
  pcore_ne {n x y cx} hxy hpx := by
    cases x <;> cases y <;> try exact hxy.elim
    · obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq hpx
      obtain ⟨cy, hcy, ecy⟩ := CMRA.pcore_ne hxy hpa
      exact ⟨inl cy, by simp [Csum.pcore, hcy], ecy⟩
    · obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq hpx
      obtain ⟨cy, hcy, ecy⟩ := CMRA.pcore_ne hxy hpb
      exact ⟨inr cy, by simp [Csum.pcore, hcy], ecy⟩
    · simp only [Csum.pcore, Option.some.injEq] at hpx
      exact ⟨invalid, rfl, hpx ▸ .rfl⟩
  validN_ne {n x y} h hv := by
    cases x <;> cases y <;> first | exact CMRA.validN_ne h hv | exact h.elim | trivial
  valid_iff_validN {x} := by cases x <;> simp [CMRA.valid_iff_validN]
  validN_succ {x _} h := by
    cases x with | inl | inr => exact CMRA.validN_succ h | invalid => exact h
  assoc {x y z} := by cases x <;> cases y <;> cases z <;> first | trivial | exact CMRA.assoc
  comm {x y} := by cases x <;> cases y <;> first | trivial | exact CMRA.comm
  pcore_op_left {x cx} hpx := by cases x with
    | inl a => obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq hpx; exact CMRA.pcore_op_left hpa
    | inr b => obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq hpx; exact CMRA.pcore_op_left hpb
    | invalid => simp only [Csum.pcore, Option.some.injEq] at hpx; exact hpx ▸ .rfl
  pcore_idem {x cx} hpx := by cases x with
    | inl a =>
      obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq hpx
      exact Equiv.of_eq (Option.map_forall₂ inl (CMRA.pcore_idem hpa).to_eq)
    | inr b =>
      obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq hpx
      exact Equiv.of_eq (Option.map_forall₂ inr (CMRA.pcore_idem hpb).to_eq)
    | invalid => simp only [Csum.pcore, Option.some.injEq] at hpx; exact hpx ▸ .rfl
  pcore_op_mono {x cx} hpx y := by cases x with
    | inl a =>
      obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq hpx; cases y with
      | inl a' =>
        obtain ⟨cy, hcy⟩ := CMRA.pcore_op_mono hpa a'
        exact ⟨inl cy, Equiv.of_eq (Option.map_forall₂ inl hcy.to_eq)⟩
      | _ => exact ⟨invalid, .rfl⟩
    | inr b =>
      obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq hpx; cases y with
      | inr b' =>
        obtain ⟨cy, hcy⟩ := CMRA.pcore_op_mono hpb b'
        exact ⟨inr cy, Equiv.of_eq (Option.map_forall₂ inr hcy.to_eq)⟩
      | _ => exact ⟨invalid, .rfl⟩
    | invalid =>
      simp only [Csum.pcore, Option.some.injEq] at hpx; exact hpx ▸ ⟨invalid, .rfl⟩
  validN_op_left {n x y} h := by
    cases x <;> cases y <;> first | exact CMRA.validN_op_left h | exact h.elim
  extend {n x y₁ y₂} hv he := by
    cases x <;> cases y₁ <;> cases y₂ <;> first
      | exact he.elim
      | exact hv.elim
      | (obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := CMRA.extend hv he
         exact ⟨inl z₁, inl z₂, hz, hz₁, hz₂⟩)
      | (obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := CMRA.extend hv he
         exact ⟨inr z₁, inr z₂, hz, hz₁, hz₂⟩)

#rocq_ignore csumR "Use Csum type with typeclass inference"
#rocq_ignore csum_op_instance "Use CMRA instance"
#rocq_ignore csum_pcore_instance "Use CMRA instance"
#rocq_ignore csum_validN_instance "Use CMRA instance"
#rocq_ignore csum_valid_instance "Use CMRA instance"

@[rocq_alias Cinl_valid]
theorem inl_valid [CMRA α] [CMRA β] {a : α} : ✓ (inl (β := β) a) ↔ ✓ a := .rfl

@[rocq_alias Cinr_valid]
theorem inr_valid [CMRA α] [CMRA β] {b : β} : ✓ (inr (α := α) b) ↔ ✓ b := .rfl

/-! ## CMRA Discrete -/

@[rocq_alias csum_cmra_discrete]
instance [CMRA α] [CMRA β] [CMRA.Discrete α] [CMRA.Discrete β] : CMRA.Discrete (Csum α β) where
  discrete_valid {x} hv :=
    match x with
    | inl a => CMRA.discrete_valid (x := a) hv
    | inr b => CMRA.discrete_valid (x := b) hv
    | invalid => hv

/-! ## CoreId -/

@[rocq_alias Cinl_core_id]
instance [CMRA α] [CMRA β] {a : α} [CoreId a] : CoreId (inl (β := β) a) where
  core_id := Equiv.of_eq (Option.map_forall₂ inl core_id.to_eq)

@[rocq_alias Cinr_core_id]
instance [CMRA α] [CMRA β] {b : β} [CoreId b] : CoreId (inr (α := α) b) where
  core_id := Equiv.of_eq (Option.map_forall₂ inr core_id.to_eq)

/-! ## Exclusive -/

@[rocq_alias Cinl_exclusive]
instance [CMRA α] [CMRA β] {a : α} [Exclusive a] : Exclusive (inl (β := β) a) where
  exclusive0_l | inl a' => Exclusive.exclusive0_l a' | inr _ | invalid => id

@[rocq_alias Cinr_exclusive]
instance [CMRA α] [CMRA β] {b : β} [Exclusive b] : Exclusive (inr (α := α) b) where
  exclusive0_l | inr b' => Exclusive.exclusive0_l b' | inl _ | invalid => id

/-! ## Cancelable -/

@[rocq_alias Cinl_cancelable]
instance [CMRA α] [CMRA β] {a : α} [Cancelable a] : Cancelable (inl (β := β) a) where
  cancelableN {n y z} hv he := by
    cases y with
    | inl => cases z with | inl => exact cancelableN (x := a) hv he | _ => exact he
    | _ => trivial

@[rocq_alias Cinr_cancelable]
instance [CMRA α] [CMRA β] {b : β} [Cancelable b] : Cancelable (inr (α := α) b) where
  cancelableN {n y z} hv he := by
    cases y with
    | inr => cases z with | inr => exact cancelableN (x := b) hv he | _ => exact he
    | _ => trivial

/-! ## IdFree -/

@[rocq_alias Cinl_id_free]
instance [CMRA α] [CMRA β] {a : α} [IdFree a] : IdFree (inl (β := β) a) where
  id_free0_r y hv he := by cases y with | inl a' => exact id_free0_r (x := a) _ hv he | _ => trivial

@[rocq_alias Cinr_id_free]
instance [CMRA α] [CMRA β] {b : β} [IdFree b] : IdFree (inr (α := α) b) where
  id_free0_r y hv he := by cases y with | inr b' => exact id_free0_r (x := b) _ hv he | _ => trivial

/-! ## Included -/

@[rocq_alias csum_included]
theorem included [CMRA α] [CMRA β] {x y : Csum α β} :
    x ≼ y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ a ≼ a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ b ≼ b') := by
  constructor
  · rintro ⟨z, hz⟩; cases x <;> cases z <;> cases y <;>
      first
      | exact Or.inl rfl
      | exact hz.elim | exact (hz 0).elim
      | exact Or.inr (Or.inl ⟨_, _, rfl, rfl, _, hz⟩)
      | exact Or.inr (Or.inr ⟨_, _, rfl, rfl, _, hz⟩)
  · rintro (rfl | ⟨a, a', rfl, rfl, c, hc⟩ | ⟨b, b', rfl, rfl, c, hc⟩)
    · exact ⟨invalid, by cases x <;> rfl⟩
    · exact ⟨inl c, hc⟩
    · exact ⟨inr c, hc⟩

@[rocq_alias Cinl_included]
theorem inl_included [CMRA α] [CMRA β] {a a' : α} :
    (inl (β := β) a) ≼ inl a' ↔ a ≼ a' := by
  constructor
  · rintro ⟨z, hz⟩; cases z <;> first | exact ⟨_, hz⟩ | exact hz.elim | exact (hz 0).elim
  · rintro ⟨c, hc⟩; exact ⟨inl c, hc⟩

@[rocq_alias Cinr_included]
theorem inr_included [CMRA α] [CMRA β] {b b' : β} :
    (inr (α := α) b) ≼ inr b' ↔ b ≼ b' := by
  constructor
  · rintro ⟨z, hz⟩; cases z <;> first | exact ⟨_, hz⟩ | exact hz.elim | exact (hz 0).elim
  · rintro ⟨c, hc⟩; exact ⟨inr c, hc⟩

@[rocq_alias CsumInvalid_included]
theorem invalid_included [CMRA α] [CMRA β] (x : Csum α β) : x ≼ invalid :=
  ⟨invalid, by cases x <;> rfl⟩

@[rocq_alias csum_includedN]
theorem includedN [CMRA α] [CMRA β] {n} {x y : Csum α β} :
    x ≼{n} y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ a ≼{n} a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ b ≼{n} b') := by
  constructor
  · rintro ⟨z, hz⟩; cases x <;> cases z <;> cases y <;>
      first
      | exact Or.inl rfl
      | exact hz.elim | exact (hz 0).elim
      | exact Or.inr (Or.inl ⟨_, _, rfl, rfl, _, hz⟩)
      | exact Or.inr (Or.inr ⟨_, _, rfl, rfl, _, hz⟩)
  · rintro (rfl | ⟨a, a', rfl, rfl, c, hc⟩ | ⟨b, b', rfl, rfl, c, hc⟩)
    · exact ⟨invalid, by cases x <;> exact Dist.rfl⟩
    · exact ⟨inl c, hc⟩
    · exact ⟨inr c, hc⟩

@[rocq_alias Some_csum_included]
theorem some_included [CMRA α] [CMRA β] {x y : Csum α β} :
    some x ≼ some y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ some a ≼ some a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ some b ≼ some b') := by
  constructor
  · intro h; rcases Option.some_inc_some_iff.mp h with heq | hinc
    · cases x <;> cases y <;>
        first
        | exact .inl rfl
        | exact heq.elim | exact (heq 0).elim
        | exact .inr (Or.inl ⟨_, _, rfl, rfl, Option.some_inc_some_iff.mpr (.inl heq)⟩)
        | exact .inr (Or.inr ⟨_, _, rfl, rfl, Option.some_inc_some_iff.mpr (.inl heq)⟩)
    · rcases included.mp hinc with rfl | ⟨a, a', rfl, rfl, ha⟩ | ⟨b, b', rfl, rfl, hb⟩
      · exact .inl rfl
      · exact .inr (Or.inl ⟨a, a', rfl, rfl, Option.some_inc_some_iff.mpr (.inr ha)⟩)
      · exact .inr (Or.inr ⟨b, b', rfl, rfl, Option.some_inc_some_iff.mpr (.inr hb)⟩)
  · rintro (rfl | ⟨a, a', rfl, rfl, mz, hmz⟩ | ⟨b, b', rfl, rfl, mz, hmz⟩)
    · exact ⟨some invalid, by cases x <;> rfl⟩
    · exact ⟨mz.map inl, by cases mz <;> exact hmz⟩
    · exact ⟨mz.map inr, by cases mz <;> exact hmz⟩

@[rocq_alias Some_csum_includedN]
theorem some_includedN [CMRA α] [CMRA β] {n} {x y : Csum α β} :
    some x ≼{n} some y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ some a ≼{n} some a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ some b ≼{n} some b') := by
  constructor
  · intro h; rcases Option.some_incN_some_iff.mp h with heq | hinc
    · cases x <;> cases y <;>
        first
        | exact .inl rfl
        | exact heq.elim | exact (heq 0).elim
        | exact .inr (Or.inl ⟨_, _, rfl, rfl, Option.some_incN_some_iff.mpr (.inl heq)⟩)
        | exact .inr (Or.inr ⟨_, _, rfl, rfl, Option.some_incN_some_iff.mpr (.inl heq)⟩)
    · rcases includedN.mp hinc with rfl | ⟨a, a', rfl, rfl, ha⟩ | ⟨b, b', rfl, rfl, hb⟩
      · exact .inl rfl
      · exact .inr (Or.inl ⟨a, a', rfl, rfl, Option.some_incN_some_iff.mpr (.inr ha)⟩)
      · exact .inr (Or.inr ⟨b, b', rfl, rfl, Option.some_incN_some_iff.mpr (.inr hb)⟩)
  · rintro (rfl | ⟨a, a', rfl, rfl, mz, hmz⟩ | ⟨b, b', rfl, rfl, mz, hmz⟩)
    · exact ⟨some invalid, by cases x <;> exact Dist.rfl⟩
    · exact ⟨mz.map inl, by cases mz <;> exact hmz⟩
    · exact ⟨mz.map inr, by cases mz <;> exact hmz⟩

/-! ## Updates -/

@[rocq_alias csum_update_l]
theorem update_l [CMRA α] [CMRA β] {a₁ a₂ : α}
    (h : a₁ ~~> a₂) : (inl (β := β) a₁) ~~> inl a₂ := by
  intro n mz hv; cases mz with
  | none => exact h n none hv
  | some z => cases z with | inl a' => exact h n (some a') hv | _ => exact hv.elim

@[rocq_alias csum_update_r]
theorem update_r [CMRA α] [CMRA β] {b₁ b₂ : β}
    (h : b₁ ~~> b₂) : (inr (α := α) b₁) ~~> inr b₂ := by
  intro n mz hv; cases mz with
  | none => exact h n none hv
  | some z => cases z with | inr b' => exact h n (some b') hv | _ => exact hv.elim

@[rocq_alias csum_updateP_l]
theorem updateP_l [CMRA α] [CMRA β] {P : α → Prop} {Q : Csum α β → Prop} {a : α}
    (h : a ~~>: P) (hPQ : ∀ a', P a' → Q (inl a')) : (inl (β := β) a) ~~>: Q := by
  intro n mz hv; cases mz with
  | none => obtain ⟨c, hc, hvc⟩ := h n none hv; exact ⟨inl c, hPQ c hc, hvc⟩
  | some z => cases z with
    | inl a' => obtain ⟨c, hc, hvc⟩ := h n (some a') hv; exact ⟨inl c, hPQ c hc, hvc⟩
    | _ => exact hv.elim

@[rocq_alias csum_updateP_r]
theorem updateP_r [CMRA α] [CMRA β] {P : β → Prop} {Q : Csum α β → Prop} {b : β}
    (h : b ~~>: P) (hPQ : ∀ b', P b' → Q (inr b')) : (inr (α := α) b) ~~>: Q := by
  intro n mz hv; cases mz with
  | none => obtain ⟨c, hc, hvc⟩ := h n none hv; exact ⟨inr c, hPQ c hc, hvc⟩
  | some z => cases z with
    | inr b' => obtain ⟨c, hc, hvc⟩ := h n (some b') hv; exact ⟨inr c, hPQ c hc, hvc⟩
    | _ => exact hv.elim

@[rocq_alias csum_updateP'_l]
theorem updateP'_l [CMRA α] [CMRA β] {P : α → Prop} {a : α}
    (h : a ~~>: P) : (inl (β := β) a) ~~>: fun m' => ∃ a', m' = inl a' ∧ P a' :=
  updateP_l h fun a' ha' => ⟨a', rfl, ha'⟩

@[rocq_alias csum_updateP'_r]
theorem updateP'_r [CMRA α] [CMRA β] {P : β → Prop} {b : β}
    (h : b ~~>: P) : (inr (α := α) b) ~~>: fun m' => ∃ b', m' = inr b' ∧ P b' :=
  updateP_r h fun b' hb' => ⟨b', rfl, hb'⟩

/-! ## Local Updates -/

@[rocq_alias csum_local_update_l]
theorem local_update_l [CMRA α] [CMRA β] {a₁ a₂ a₁' a₂' : α}
    (h : (a₁, a₂) ~l~> (a₁', a₂')) :
    ((inl (β := β) a₁, inl a₂) ~l~> (inl a₁', inl a₂')) := by
  intro n mf hv he; cases mf with
  | none => exact h n none hv he
  | some z => cases z with | inl a' => exact h n (some a') hv he | _ => exact he.elim

@[rocq_alias csum_local_update_r]
theorem local_update_r [CMRA α] [CMRA β] {b₁ b₂ b₁' b₂' : β}
    (h : (b₁, b₂) ~l~> (b₁', b₂')) :
    ((inr (α := α) b₁, inr b₂) ~l~> (inr b₁', inr b₂')) := by
  intro n mf hv he; cases mf with
  | none => exact h n none hv he
  | some z => cases z with | inr b' => exact h n (some b') hv he | _ => exact he.elim

/-! ## Functor -/

@[simp, rocq_alias csum_map]
def map (f : α → α') (g : β → β') : Csum α β → Csum α' β'
  | inl a => inl (f a)
  | inr b => inr (g b)
  | invalid => invalid

@[rocq_alias csum_map_id]
theorem map_id {x : Csum α β} : map id id x = x := by cases x <;> simp

@[rocq_alias csum_map_compose]
theorem map_compose (f : α → α') (f' : α' → α'') (g : β → β') (g' : β' → β'')
    (x : Csum α β) : map (f' ∘ f) (g' ∘ g) x = map f' g' (map f g x) := by
  cases x <;> simp

@[rocq_alias csum_map_ext]
theorem map_ext [OFE α] [OFE α'] [OFE β] [OFE β'] (f f' : α → α') (g g' : β → β')
    (hf : ∀ x, f x ≡ f' x) (hg : ∀ x, g x ≡ g' x) (x : Csum α β) :
    map f g x ≡ map f' g' x := by
  cases x with
  | inl a => simp [map]; exact hf _
  | inr b => simp [map]; exact hg _
  | invalid => trivial

@[rocq_alias csum_map_cmra_ne]
theorem map_ne [OFE α] [OFE α'] [OFE β] [OFE β'] {n}
    {f f' : α → α'} (hf : ∀ ⦃x₁ x₂⦄, x₁ ≡{n}≡ x₂ → f x₁ ≡{n}≡ f' x₂)
    {g g' : β → β'} (hg : ∀ ⦃x₁ x₂⦄, x₁ ≡{n}≡ x₂ → g x₁ ≡{n}≡ g' x₂)
    {x y : Csum α β} (hxy : x ≡{n}≡ y) :
    map f g x ≡{n}≡ map f' g' y := by
  cases x with
  | inl => cases y with | inl => simp [map]; exact hf hxy | _ => exact hxy
  | inr => cases y with | inr => simp [map]; exact hg hxy | _ => exact hxy
  | invalid => cases y with | invalid => trivial | _ => exact hxy

@[rocq_alias csumO_map]
def oMap [OFE α] [OFE α'] [OFE β] [OFE β'] (f : α -n> α') (g : β -n> β') :
    Csum α β -n> Csum α' β' where
  f := map f g
  ne := ⟨fun {_n} {_x₁} {_x₂} hxy =>
    map_ne (fun _ _ h => f.ne.1 h) (fun _ _ h => g.ne.1 h) hxy⟩

@[rocq_alias csumO_map_ne]
theorem oMap_ne [OFE α] [OFE α'] [OFE β] [OFE β'] :
    NonExpansive₂ (oMap (α := α) (α' := α') (β := β) (β' := β')) where
  ne _ _ _ hf _ _ hg x := by
    cases x with
    | inl => simp [oMap, map]; exact hf _
    | inr => simp [oMap, map]; exact hg _
    | invalid => trivial

@[rocq_alias csumRF]
abbrev OF (Fa Fb : COFE.OFunctorPre) : COFE.OFunctorPre :=
  fun A B _ _ => Csum (Fa A B) (Fb A B)

@[rocq_alias csum_map_cmra_morphism]
def cMap [CMRA α] [CMRA α'] [CMRA β] [CMRA β']
    (fa : α -C> α') (fb : β -C> β') : Csum α β -C> Csum α' β' where
  f := map fa fb
  ne := (oMap fa.toHom fb.toHom).ne
  validN {n x} hv := by cases x with
    | inl a => exact fa.validN hv
    | inr b => exact fb.validN hv
    | invalid => exact hv
  pcore x := by
    cases x with
    | inl a =>
      show ((CMRA.pcore a).map inl).map (map fa fb) ≡ (CMRA.pcore (fa a)).map inl
      rw [Option.map_map]
      show (CMRA.pcore a).map (inl ∘ ⇑fa) ≡ _
      rw [show (CMRA.pcore a).map (inl ∘ ⇑fa) = ((CMRA.pcore a).map fa).map inl from
        (Option.map_map ..).symm]
      exact Equiv.of_eq (Option.map_forall₂ inl (fa.pcore a).to_eq)
    | inr b =>
      show ((CMRA.pcore b).map inr).map (map fa fb) ≡ (CMRA.pcore (fb b)).map inr
      rw [Option.map_map]
      show (CMRA.pcore b).map (inr ∘ ⇑fb) ≡ _
      rw [show (CMRA.pcore b).map (inr ∘ ⇑fb) = ((CMRA.pcore b).map fb).map inr from
        (Option.map_map ..).symm]
      exact Equiv.of_eq (Option.map_forall₂ inr (fb.pcore b).to_eq)
    | invalid => trivial
  op x y := by cases x <;> cases y <;> first | exact fa.op _ _ | exact fb.op _ _ | trivial

instance {Fa Fb} [RFunctor Fa] [RFunctor Fb] : RFunctor (OF Fa Fb) where
  map f g := cMap (RFunctor.map f g) (RFunctor.map f g)
  map_ne.ne _ _ _ hf _ _ hg x := by
    cases x <;> simp [cMap, map] <;> exact RFunctor.map_ne.ne hf hg _
  map_id x := by cases x <;> simp [cMap, map] <;> exact RFunctor.map_id _
  map_comp f g f' g' x := by
    cases x <;> simp [cMap, map] <;> exact RFunctor.map_comp f g f' g' _

@[rocq_alias csumRF_contractive]
instance {Fa Fb} [RFunctorContractive Fa] [RFunctorContractive Fb] :
    RFunctorContractive (OF Fa Fb) where
  map_contractive.1 {n x y} hKL z := by
    cases z <;> first | exact RFunctorContractive.map_contractive.1 hKL _ | trivial

end Csum

end Iris
