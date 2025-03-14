/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Iris.Algebra.OFE

namespace Iris
open OFE

class CMRA (α : Type _) extends OFE α where
  pcore : α → Option α
  op : α → α → α
  validN : Nat → α → Prop
  valid : α → Prop

  op_ne : NonExpansive (op x)
  pcore_ne : x ≡{n}≡ y → pcore x = some cx →
    ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy
  validN_ne : x ≡{n}≡ y → validN n x → validN n y

  valid_validN : valid x ↔ ∀ n, validN n x
  validN_succ : validN n.succ x → validN n x
  validN_op_l : validN n (op x y) → validN n x

  assoc : op x (op y z) ≡ op (op x y) z
  comm : op x y ≡ op y x

  pcore_l : pcore x = some cx → op cx x ≡ x
  pcore_idem : pcore x = some cx → pcore cx ≡ some cx
  pcore_mono y : pcore x = some cx → ∃ cy, pcore (op x y) = some (op cx cy)

  extend : validN n x → x ≡{n}≡ op y₁ y₂ →
    Σ' z₁ z₂, x ≡ op z₁ z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂

namespace CMRA
variable [CMRA α]

infix:60 " • " => op

def included (x y : α) : Prop := ∃ z, y ≡ x • z
infix:50 " ≼ " => included

def includedN (n : Nat) (x y : α) : Prop := ∃ z, y ≡{n}≡ x • z
notation:50 x "≼{" n "}" y:51 => includedN n x y

def op? [CMRA α] (x : α) : Option α → α
  | some y => x • y
  | none => x
infix:60 " •? " => op?

prefix:50 "✓" => valid
notation:50 "✓{" n "}" x:51 => validN n x

class CoreId (x : α) : Prop where
  core_id : pcore x ≡ some x

class Exclusive (x : α) : Prop where
  exclusive0_l : ¬✓{0} x • y

class Cancelable (x : α) : Prop where
  cancelableN : ✓{n} x • y → x • y ≡{n}≡ x • z → y ≡{n}≡ z

class IdFree (x : α) : Prop where
  id_free0_r : ✓{0} x → ¬x • y ≡{0}≡ x

class IsTotal (α : Type _) [CMRA α] where
  total (x : α) : ∃ cx, pcore x = some cx

def core (x : α) := (pcore x).getD x

class Discrete (α : Type _) [CMRA α] extends OFE.Discrete α where
  discrete_valid {x : α} : ✓{0} x → ✓ x

end CMRA

class UCMRA (α : Type _) extends CMRA α where
  unit : α
  unit_valid : ✓ unit
  unit_left_id : unit • x ≡ x
  pcore_unit : pcore unit ≡ some unit

namespace CRMA
  variable [cmr: CMRA α]

  -- Op
  theorem op_right_equiv (x: α) {y z: α}(e: y ≡ z): x • y ≡ x • z := cmr.op_ne.eqv e

  theorem op_right_dist (x: α) {y z: α}(e: y ≡{n}≡ z): x • y ≡{n}≡ x • z :=
    cmr.op_ne.ne e

  theorem op_commN {x y: α}: x • y ≡{n}≡ y • x := OFE.equiv_dist.mp cmr.comm n

  theorem op_assocN {x y z: α}: x • (y • z) ≡{n}≡ (x • y) • z :=
    OFE.equiv_dist.mp cmr.assoc n

  theorem op_left_dist {x y: α} (z: α)(e: x ≡{n}≡ y): x • z ≡{n}≡ y • z :=
    calc
      x • z ≡{n}≡ z • x := op_commN
      _     ≡{n}≡ z • y := op_right_dist z e
      _     ≡{n}≡ y • z := op_commN

  theorem op_left_equiv {x y: α} (z: α)(e: x ≡ y): x • z ≡ y • z :=
    calc
      x • z ≡ z • x := cmr.comm
      _     ≡ z • y := op_right_equiv z e
      _     ≡ y • z := cmr.comm

  theorem op_opM_assoc (x y: α) (mz: Option α) : (x • y) •? mz ≡ x • (y •? mz) :=
    by unfold CMRA.op?; cases mz <;> simp [cmr.assoc, Equiv.symm]

  -- Validity
  theorem valid_mapN {x y: α} (f: ∀n, ✓{n}x → ✓{n}y): ✓x → ✓y :=
    λv ↦ cmr.valid_validN.mpr (λn ↦ f n (cmr.valid_validN.mp v n))

  theorem validN_equiv {x y: α}: x ≡ y → ✓{n}x → ✓{n}y :=
    λe v ↦ cmr.validN_ne (cmr.equiv_dist.mp e n) v

  theorem valid_equiv {x y: α}: x ≡ y → ✓x → ✓y :=
    λe ↦ valid_mapN (λ_ ↦ validN_equiv e)

  theorem validN_le n n' {x: α} : n' ≤ n → ✓{n} x → ✓{n'} x :=
    λle ↦ le.recOn id (λ _ ih vs ↦ ih (CMRA.validN_succ vs))

  theorem validN_op_r {n} {x y: α} : ✓{n} (x • y) → ✓{n} y :=
    λv ↦ cmr.validN_op_l (validN_equiv cmr.comm v)

  theorem valid_op_r (x y: α) : ✓ (x • y) → ✓ y :=
    valid_mapN (λ_ ↦ validN_op_r)

  theorem valid_op_l {x y: α} : ✓ (x • y) → ✓ x :=
    λv ↦ valid_op_r y x (valid_equiv cmr.comm v)


  -- Core
  theorem pcore_l' {x: α} {cx} (e: cmr.pcore x ≡ some cx): cx • x ≡ x :=
    let ⟨z, pz, ez⟩ := OFE.equiv_some e
    calc
      cx • x ≡ z • x := op_left_equiv _ ez.symm
      _      ≡ x     := cmr.pcore_l pz

  theorem pcore_r {x: α} {cx} (e: cmr.pcore x = some cx): x • cx ≡ x :=
    calc
      x • cx ≡ cx • x := cmr.comm
      _      ≡ x      := cmr.pcore_l e

  theorem pcore_r' {x: α} {cx} (e: cmr.pcore x ≡ some cx): x • cx ≡ x :=
    let ⟨_, pz, ez⟩ := OFE.equiv_some e
    (op_right_equiv x ez).symm.trans (pcore_r pz)

  theorem pcore_idemp' {x: α} {cx} (e: cmr.pcore x ≡ some cx): cmr.pcore cx ≡ some cx :=
    -- Tricky one
    sorry

  theorem pcore_dup (x: α) cx (e: cmr.pcore x = some cx): cx ≡ cx • cx :=
    (pcore_r' (cmr.pcore_idem e)).symm

  theorem pcore_dup' (x: α) cx (e: cmr.pcore x ≡ some cx): cx ≡ cx • cx :=
    let ⟨z, pz, ez⟩ := OFE.equiv_some e
    have : z • z ≡ z := pcore_r' (cmr.pcore_idem pz)
    calc
      cx ≡ z := ez.symm
      _ ≡ z • z := this.symm
      _ ≡ cx • z := op_left_equiv z ez
      _ ≡ cx • cx := op_right_equiv cx ez

  theorem pcore_validN {n} {x: α} {cx} : cmr.pcore x = some cx → ✓{n} x → ✓{n} cx :=
    λe v ↦
      have: ✓{n}x • cx := validN_equiv (pcore_r e).symm v
      validN_op_r this

  theorem pcore_valid (x: α) cx : cmr.pcore x = some cx → ✓ x → ✓ cx :=
    λe ↦ valid_mapN (λ_ ↦ pcore_validN e)

  -- Exclusive elements
  theorem exclusiveN_l n (x: α) [ex: CMRA.Exclusive x] y : ✓{n} (x • y) → False :=
    n.recOn ex.exclusive0_l (λ_ ih ↦ ih ∘ cmr.validN_succ)

  theorem exclusiveN_r n (x: α) [ex: CMRA.Exclusive x] y : ✓{n} (y • x) → False :=
    λv ↦ exclusiveN_l n x y (validN_equiv cmr.comm v)

  theorem exclusive_l  (x: α) [ex: CMRA.Exclusive x] y : ✓ (x • y) → False :=
    λv ↦ ex.exclusive0_l (cmr.valid_validN.mp v 0)

  theorem exclusive_r  (x: α) [ex: CMRA.Exclusive x] y : ✓ (y • x) → False :=
    λv ↦ exclusive_l x y (valid_equiv cmr.comm v)

  theorem exclusiveN_opM n (x: α) [ex: CMRA.Exclusive x] my : ✓{n} (x •? my) → my = none :=
    match my with
    | .none => by simp [CMRA.op?]
    | .some y => by simp [CMRA.op?]; exact exclusiveN_l n x y

  theorem exclusive_includedN n (x: α) [ex: CMRA.Exclusive x] y
      : x ≼{n} y → ✓{n} y → False :=
    λle v ↦
      let ⟨_, hz⟩ := le
      have := cmr.validN_ne hz v
      exclusiveN_l _ _ _ this

  theorem exclusive_included (x: α) [ex: CMRA.Exclusive x] y
      : x ≼ y → ✓ y → False :=
    λle v ↦
      have ⟨z, hz⟩ := le
      have: ✓{0}x • z := validN_equiv hz (cmr.valid_validN.mp v 0)
      ex.exclusive0_l this

  -- Order
  theorem included_includedN n (x y: α) : x ≼ y → x ≼{n} y :=
    λle ↦ le.elim (λz hz ↦ ⟨z, Equiv.dist hz⟩)

  theorem included_trans {x y z: α}(i1: x ≼ y)(i2: y ≼ z): x ≼ z :=
    have ⟨w, (hw : y ≡ x • w)⟩ := i1
    have ⟨t, (ht : z ≡ y • t)⟩ := i2
    suffices h: z ≡ x • (w • t) from ⟨w • t, h⟩
    calc
      z ≡ y • t := ht
      _ ≡ (x • w) • t := op_left_equiv _ hw
      _ ≡ x • (w • t) := cmr.assoc.symm

  theorem includedN_trans {x y z: α}(i1: x ≼{n} y)(i2: y ≼{n} z): x ≼{n} z :=
    have ⟨w, (hw : y ≡{n}≡ x • w)⟩ := i1
    have ⟨t, (ht : z ≡{n}≡ y • t)⟩ := i2
    suffices h: z ≡{n}≡ x • (w • t) from ⟨w • t, h⟩
    calc
      z ≡{n}≡ y • t := ht
      _ ≡{n}≡ (x • w) • t := op_left_dist _ hw
      _ ≡{n}≡ x • (w • t) := op_assocN.symm

  theorem valid_included (x y: α) : x ≼ y → ✓ y → ✓ x :=
    λle v ↦ le.elim (λ_ hz ↦ valid_op_l (valid_equiv hz v))

  theorem validN_includedN n (x y: α) : x ≼{n} y → ✓{n} y → ✓{n} x :=
    λle v ↦ le.elim (λ_ hz ↦ cmr.validN_op_l (CMRA.validN_ne hz v))

  theorem validN_included n (x y: α) : x ≼ y → ✓{n} y → ✓{n} x :=
    λle v ↦ le.elim λz hz ↦
      have : ✓{n}x • z := cmr.validN_ne (equiv_dist.mp hz n) v
      cmr.validN_op_l this

  theorem includedN_le {n n'} {x y: α} : n' ≤ n → x ≼{n} y → x ≼{n'} y :=
    λl1 l2 ↦ l2.elim λz hz ↦ ⟨z, Dist.le hz l1⟩

  theorem includedN_S n (x y: α) : x ≼{n.succ} y → x ≼{n} y :=
    includedN_le (Nat.le_succ n)


  theorem includedN_l n (x y: α) : x ≼{n} x • y := ⟨y, Dist.rfl⟩

  theorem included_l (x y: α) : x ≼ x • y := ⟨y, Equiv.rfl⟩

  theorem included_r (x y: α) : y ≼ x • y := ⟨x, cmr.comm⟩

  theorem includedN_r n (x y: α) : y ≼{n} x • y :=
    (included_r x y).elim (λz hz ↦ ⟨z, Equiv.dist hz⟩)


  theorem pcore_mono' (x y: α) cx :
      x ≼ y → cmr.pcore x ≡ some cx → ∃ cy, cmr.pcore y = some cy ∧ cx ≼ cy :=
    sorry

  theorem pcore_monoN' n (x y: α) cx :
      x ≼{n} y → cmr.pcore x ≡{n}≡ some cx → ∃ cy, cmr.pcore y = some cy ∧ cx ≼{n} cy :=
    sorry

  theorem included_pcore (x: α) cx : cmr.pcore x = some cx → cx ≼ x :=
    λe ↦ ⟨x, (CMRA.pcore_l e).symm⟩


  theorem mono_l (x y z: α) : x ≼ y → z • x ≼ z • y :=
    λle ↦
      let ⟨w, hw⟩ := le
      suffices h: z • y ≡ (z • x) • w from ⟨w, h⟩
      calc
        z • y ≡ z • (x • w) := op_right_equiv z hw
        _     ≡ (z • x) • w := cmr.assoc

  theorem monoN_l n (x y z: α) : x ≼{n} y → z • x ≼{n} z • y :=
    λle ↦
      let ⟨w, hw⟩ := le
      suffices h: z • y ≡{n}≡ (z • x) • w from ⟨w, h⟩
      calc
        z • y ≡{n}≡ z • (x • w) := op_right_dist z hw
        _     ≡{n}≡ (z • x) • w := op_assocN


  theorem monoN_r n (x y z: α) : x ≼{n} y → x • z ≼{n} y • z :=
    λle ↦
      let ⟨w, hw⟩ := le
      suffices h: y • z ≡{n}≡ (x • z) • w from ⟨w, h⟩
      calc
        y • z ≡{n}≡ (x • w) • z := op_left_dist z hw
        _     ≡{n}≡ x • (w • z) := op_assocN.symm
        _     ≡{n}≡ x • (z • w) := op_right_dist x (op_commN)
        _     ≡{n}≡ (x • z) • w := op_assocN

  theorem mono_r (x y z: α) : x ≼ y → x • z ≼ y • z :=
    λle ↦
      let ⟨w, hw⟩ := le
      suffices h: y • z ≡ (x • z) • w from ⟨w, h⟩
      calc
        y • z ≡ (x • w) • z := op_left_equiv z hw
        _     ≡ x • (w • z) := cmr.assoc.symm
        _     ≡ x • (z • w) := op_right_equiv x cmr.comm
        _     ≡ (x • z) • w := cmr.assoc

  theorem monoN n (x1 x2 y1 y2: α) : x1 ≼{n} y1 → x2 ≼{n} y2 → x1 • x2 ≼{n} y1 • y2 :=
    λl1 l2 ↦
      let ⟨w, hw⟩ := l1;  let ⟨t, ht⟩ := l2
      suffices h: y1 • y2 ≡{n}≡ (x1 • x2) • (w • t) from ⟨w • t, h⟩
      calc
        y1 • y2 ≡{n}≡ (x1 • w) • y2 := op_left_dist _ hw
        _       ≡{n}≡ (x1 • w) • (x2 • t) := op_right_dist _ ht
        _       ≡{n}≡ x1 • (w • (x2 • t)) := op_assocN.symm
        _       ≡{n}≡ x1 • ((x2 • t) • w) := op_right_dist _ (op_commN)
        _       ≡{n}≡ (x1 • (x2 • t)) • w := op_assocN
        _       ≡{n}≡ ((x1 • x2) • t) • w := op_left_dist _ (op_assocN)
        _       ≡{n}≡ (x1 • x2) • (t • w) := op_assocN.symm
        _       ≡{n}≡ (x1 • x2) • (w • t) := op_right_dist _ (op_commN)

  theorem mono (x1 x2 y1 y2: α) : x1 ≼ y1 → x2 ≼ y2 → x1 • x2 ≼ y1 • y2 :=
    λl1 l2 ↦
      let ⟨w, hw⟩ := l1;  let ⟨t, ht⟩ := l2
      suffices h: y1 • y2 ≡ (x1 • x2) • (w • t) from ⟨w • t, h⟩
      calc
        y1 • y2 ≡ (x1 • w) • y2 := op_left_equiv _ hw
        _       ≡ (x1 • w) • (x2 • t) := op_right_equiv _ ht
        _       ≡ x1 • (w • (x2 • t)) := cmr.assoc.symm
        _       ≡ x1 • ((x2 • t) • w) := op_right_equiv _ (cmr.comm)
        _       ≡ (x1 • (x2 • t)) • w := cmr.assoc
        _       ≡ ((x1 • x2) • t) • w := op_left_equiv _ cmr.assoc
        _       ≡ (x1 • x2) • (t • w) := cmr.assoc.symm
        _       ≡ (x1 • x2) • (w • t) := op_right_equiv _ (cmr.comm)

end CRMA

instance [c: CMRA α]: Trans c.included c.included c.included where
  trans := CRMA.included_trans

instance [c: CMRA α]: Trans (c.includedN n) (c.includedN n) (c.includedN n) where
  trans := CRMA.includedN_trans
