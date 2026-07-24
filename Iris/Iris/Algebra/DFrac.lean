/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Mario Carneiro
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.Frac
public import Iris.Algebra.Updates
public import Iris.Algebra.LocalUpdates
public import Iris.Algebra.IsOp
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

/-- Knowledge about a discardable fraction. -/
@[rocq_alias dfrac]
inductive DFrac where
/-- Ownership of `F` plus knowledge that no fraction has been discarded. -/
| own (f : Qp) : DFrac
/-- Knowledge that a fraction has been discarded. -/
| discard : DFrac
/-- Ownership of `F` plus knowledge that a fraction has been discarded. -/
| ownDiscard (f : Qp) : DFrac

#rocq_ignore DfracOwn_inj "Not needed"
#rocq_ignore DfracBoth_inj "Not needed"

@[simp] instance : COFE DFrac := COFE.ofDiscrete _
instance : OFE.Discrete DFrac := ⟨fun h => h⟩
#rocq_ignore dfracO "Use DFrac type with typeclass inference"

namespace DFrac

open DFrac OFE.Discrete IsOp

@[rocq_alias dfrac_inhabited]
instance : Inhabited DFrac := ⟨discard⟩

def valid : DFrac → Prop
  | .own f        => f.val ≤ 1
  | .discard      => True
  | .ownDiscard f => f.val < 1

def pcore : DFrac → Option DFrac
  | own _        => none
  | .discard     => some discard
  | ownDiscard _ => some discard

def op : DFrac → DFrac → DFrac
  | .discard, .discard => discard
  | own f, .discard
  | ownDiscard f, .discard
  | .discard, own f
  | .discard, ownDiscard f => ownDiscard f
  | own f, own f' => own (f + f')
  | own f, ownDiscard f'
  | ownDiscard f, own f'
  | ownDiscard f, ownDiscard f' => ownDiscard (f + f')

#rocq_ignore dfrac_op_instance "Use CMRA instance"
#rocq_ignore dfrac_pcore_instance "Use CMRA instance"
#rocq_ignore dfrac_valid_instance "Use CMRA instance"
#rocq_ignore dfrac_ra_mixin "Not needed"

@[rocq_alias dfracR]
instance instCMRADFrac : CMRA DFrac where
  pcore := pcore
  op := op
  Valid := valid
  ValidN _ := valid
  op_ne := { ne _ _ _ := congrArg (op _) }
  pcore_ne {_} := by rintro ⟨⟩ ⟨⟩ <;> simp [pcore] <;> nofun
  validN_ne H := H ▸ id
  valid_iff_validN := ⟨fun x _ => x, fun x => x 0⟩
  validN_succ := id
  validN_op_left {_} := by rintro ⟨⟩ ⟨⟩ <;> simp [valid, op] <;> grind
  assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> grind [op]
  comm := by rintro ⟨⟩ ⟨⟩ <;> grind [op]
  pcore_op_left := by rintro ⟨⟩ ⟨⟩ <;> simp [op, pcore]
  pcore_idem := by rintro ⟨⟩ ⟨⟩ <;> simp [pcore]
  pcore_op_mono := by
    rintro ⟨⟩ ⟨⟩ <;> simp [pcore] <;>
    · intro z
      exists discard
      rcases z with z|_|z <;> simp [op]
  extend _ Hxyz := ⟨_, _, discrete Hxyz, .rfl, .rfl⟩

@[rocq_alias dfrac_full_exclusive]
instance own_whole_exclusive : CMRA.Exclusive (α := DFrac) (own 1) where
  exclusive0_l := by
    rintro (y|_|y) <;>
    simp only [CMRA.ValidN, valid, CMRA.op, op] <;>
    grind

instance one_exclusive_left [CMRA V] {v : V} : CMRA.Exclusive (own (One.one : Qp), v) where
  exclusive0_l := by
    refine fun ⟨y1, _⟩ ⟨Hv1, _⟩ => ?_
    have h1 : (One.one : Qp).val = 1 := rfl
    rcases y1 with (y|_|y) <;>
      simp only [CMRA.ValidN, CMRA.op, op, valid] at Hv1 <;>
      grind

instance one_exclusive_right [CMRA V] {v : V} : CMRA.Exclusive (v, own (One.one : Qp)) where
  exclusive0_l := by
    refine fun ⟨_, y2⟩ ⟨_, Hv2⟩ => ?_
    have h1 : (One.one : Qp).val = 1 := rfl
    rcases y2 with (y|_|y) <;>
      simp only [CMRA.ValidN, CMRA.op, op, valid] at Hv2 <;>
      grind

@[rocq_alias dfrac_cancelable]
instance {f : Qp} : CMRA.Cancelable (own f) where
  cancelableN {_} := by
    rintro (a|_|a) (b|_|b) <;> simp [CMRA.ValidN, CMRA.op, op] <;> intro H Hxyz
    any_goals have Hxyz' := discrete Hxyz <;> simp at Hxyz'
    · exact congrArg own (Subtype.ext (by grind))
    · exact absurd Hxyz' (by have := b.2; grind)
    · exact absurd Hxyz' (by have := a.2; grind)
    · exact congrArg ownDiscard (Subtype.ext (by grind))

@[rocq_alias dfrac_own_id_free]
instance {f : Qp} : CMRA.IdFree (own f) where
  id_free0_r := by
    rintro (y|_|y) <;>
      simp [CMRA.ValidN, CMRA.op, op] <;>
      intro H Hxyz <;>
      any_goals have Hxyz' := discrete Hxyz <;>
      simp at Hxyz'
    exact absurd Hxyz' (by have := y.2; grind)

@[rocq_alias dfrac_valid_own_1]
theorem valid_own_one : ✓ own (1 : Qp) := by show (1 : Qp).val ≤ 1; grind

@[rocq_alias dfrac_valid_own_r]
theorem valid_op_own {dq : DFrac} {q : Qp} : ✓ dq • own q → q.val < 1 := by
  obtain y|_|y := dq <;>
    simp only [CMRA.Valid, CMRA.op, op, valid] <;>
    grind

@[rocq_alias dfrac_valid_own_l]
theorem valid_own_op {dq : DFrac} {q : Qp} : ✓ own q • dq → q.val < 1 :=
  fun h => valid_op_own (CMRA.comm' (y := dq) ▸ h)

@[rocq_alias dfrac_valid_discarded]
theorem valid_discard : ✓ (discard : DFrac) := by simp [CMRA.Valid, valid]

@[rocq_alias dfrac_valid_own_discarded]
theorem valid_own_op_discard {q : Qp} : ✓ own q • discard ↔ q.val < 1 := by
  simp [CMRA.op, op, CMRA.Valid, valid]

@[rocq_alias dfrac_cmra_discrete]
instance : CMRA.Discrete DFrac where
  discrete_valid {x} := by simp [CMRA.Valid, CMRA.ValidN]

theorem is_discrete {q : DFrac} : OFE.DiscreteE q := ⟨fun h => h⟩

@[rocq_alias dfrac_discarded_core_id]
instance : CMRA.CoreId (DFrac.discard) where
  core_id := by simp [CMRA.pcore, DFrac.pcore]

@[rocq_alias dfrac_discard_update]
theorem DFrac.update_discard {dq : DFrac} : dq ~~> .discard := by
  intros n q H
  apply (CMRA.valid_iff_validN' n).mp
  have H' := (CMRA.valid_iff_validN' n).mpr H
  simp [CMRA.op?] at H' ⊢
  rcases q with (_|⟨q|_|q⟩) <;>
    simp [CMRA.Valid, valid, CMRA.op, op] <;>
    rcases dq with (f|_|f) <;>
    simp only [CMRA.op?, CMRA.ValidN, CMRA.op, op, valid] at H <;>
    grind

@[rocq_alias dfrac_undiscard_update]
theorem DFrac.update_acquire :
    (.discard : DFrac) ~~>: fun k => ∃ q, k = .own q := by
  apply UpdateP.discrete.mpr
  rintro (_|q)
  · rintro _
    refine ⟨.own 1, ⟨⟨1, rfl⟩, ?_⟩⟩
    simp only [CMRA.op?, CMRA.Valid, valid]
    grind
  rcases q with (q|_|q)
  · intro h
    have hq : q.val < 1 := h
    refine ⟨.own ⟨1 - q.val, by grind⟩, ⟨⟨_, rfl⟩, ?_⟩⟩
    simp only [CMRA.op?, CMRA.Valid, CMRA.op, op, valid, Qp.val_add]
    grind
  · intro _
    refine ⟨.own (Qp.half 1), ⟨⟨_, rfl⟩, ?_⟩⟩
    simp only [CMRA.op?, CMRA.Valid, CMRA.op, op, valid, Qp.val_half]
    grind
  · intro h
    have hq : q.val < 1 := h
    refine ⟨.own ⟨(1 - q.val) / 2, by grind⟩, ⟨⟨_, rfl⟩, ?_⟩⟩
    simp only [CMRA.op?, CMRA.Valid, CMRA.op, op, valid, Qp.val_add]
    grind

@[rocq_alias dfrac_op_own]
theorem op_own {p q : Qp} : own p • own q = own (p + q) := rfl

@[rocq_alias dfrac_op_discarded]
theorem op_discard : (discard : DFrac) • discard = discard := rfl

@[rocq_alias dfrac_valid_own]
theorem valid_own {p : Qp} : ✓ own p ↔ p.val ≤ 1 := .rfl

@[rocq_alias dfrac_valid]
theorem valid_iff {dq : DFrac} : ✓ dq ↔
    match dq with
    | own f => f.val ≤ 1
    | discard => True
    | ownDiscard f => f.val < 1 := by
  cases dq <;> rfl

@[rocq_alias dfrac_discarded_included]
theorem discard_included : (discard : DFrac) ≼ discard := ⟨discard, rfl⟩

@[rocq_alias dfrac_own_included]
theorem own_included {p q : Qp} : own p ≼ own q ↔ ∃ r, q = p + r := by
  refine ⟨fun ⟨z, hz⟩ => ?_, fun ⟨r, hr⟩ => ⟨own r, hr ▸ rfl⟩⟩
  rcases z with (r|_|r) <;> simp [CMRA.op, op] at hz
  exact ⟨r, Qp.ext_iff.mpr hz⟩

@[rocq_alias dfrac_is_op]
instance isOp_dfrac_own {q q1 q2 : Qp} [h : IsOp d q q1 q2] :
    IsOp d (own q) (own q1) (own q2) where
  is_op := by rw [h.is_op]; rfl

end DFrac
