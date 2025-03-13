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

  valid_iff_validN : valid x ↔ ∀ n, validN n x
  validN_succ : validN n.succ x → validN n x
  validN_op_left : validN n (op x y) → validN n x

  assoc : op x (op y z) ≡ op (op x y) z
  comm : op x y ≡ op y x

  pcore_op_left : pcore x = some cx → op cx x ≡ x
  pcore_idem : pcore x = some cx → pcore cx ≡ some cx
  pcore_op_mono y: pcore x = some cx → ∃ cy, pcore (op x y) = some (op cx cy)

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

instance [cmr: CMRA α]: NonExpansive cmr.pcore where
  ne n x {y} e :=
    suffices h: ∀ox oy, cmr.pcore x = ox → cmr.pcore y = oy → cmr.pcore x ≡{n}≡ cmr.pcore y
    from h (cmr.pcore x) (cmr.pcore y) rfl rfl
    λox oy ex ey ↦
      match ox, oy with
      | .some a, .some b =>
        let ⟨w, hw, ew⟩ := cmr.pcore_ne e ex
        calc
          cmr.pcore x ≡{n}≡ some a      := .of_eq ex
          _           ≡{n}≡ some w      := ew
          _           ≡{n}≡ cmr.pcore y := .of_eq hw.symm
      | .some a, .none =>
        let ⟨w, hw, ew⟩ := cmr.pcore_ne e ex
        Option.noConfusion (hw.symm ▸ ey)
      | .none, .some b =>
        let ⟨w, hw, ew⟩ := cmr.pcore_ne e.symm ey
        Option.noConfusion (hw.symm ▸ ex)
      | .none, .none => by rw[ex, ey]; trivial

namespace CRMA
  variable [cmr: CMRA α]

  -- Op
  theorem op_right_eqv (x: α) {y z: α}(e: y ≡ z): x • y ≡ x • z := cmr.op_ne.eqv e

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

  theorem op_left_eqv {x y: α} (z: α)(e: x ≡ y): x • z ≡ y • z :=
    calc
      x • z ≡ z • x := cmr.comm
      _     ≡ z • y := op_right_eqv z e
      _     ≡ y • z := cmr.comm

  theorem op_opM_assoc (x y: α) (mz: Option α) : (x • y) •? mz ≡ x • (y •? mz) :=
    by unfold CMRA.op?; cases mz <;> simp [cmr.assoc, Equiv.symm]

  -- Validity
  theorem valid_mapN {x y: α} (f: ∀n, ✓{n}x → ✓{n}y): ✓x → ✓y :=
    λv ↦ cmr.valid_iff_validN.mpr (λn ↦ f n (cmr.valid_iff_validN.mp v n))

  theorem validN_of_eqv {x y: α}: x ≡ y → ✓{n}x → ✓{n}y :=
    λe v ↦ cmr.validN_ne (cmr.equiv_dist.mp e n) v

  theorem valid_of_eqv {x y: α}: x ≡ y → ✓x → ✓y :=
    λe ↦ valid_mapN (λ_ ↦ validN_of_eqv e)

  theorem validN_of_le n n' {x: α} : n' ≤ n → ✓{n} x → ✓{n'} x :=
    λle ↦ le.recOn id (λ _ ih vs ↦ ih (CMRA.validN_succ vs))

  theorem validN_op_right {n} {x y: α} : ✓{n} (x • y) → ✓{n} y :=
    λv ↦ cmr.validN_op_left (validN_of_eqv cmr.comm v)

  theorem valid_op_right (x y: α) : ✓ (x • y) → ✓ y :=
    valid_mapN (λ_ ↦ validN_op_right)

  theorem valid_op_left {x y: α} : ✓ (x • y) → ✓ x :=
    λv ↦ valid_op_right y x (valid_of_eqv cmr.comm v)


  -- Core
  theorem pcore_proper {x y: α} (cx: α)(e: x ≡ y)(ps: cmr.pcore x = some cx)
      : ∃cy, cmr.pcore y = some cy ∧ cx ≡ cy := by
    let ⟨cy, hcy, ecy⟩ := cmr.pcore_ne (OFE.equiv_dist.mp e 0) ps
    refine ⟨cy, hcy, ?_⟩
    have (n: Nat): cx ≡{n}≡ cy :=
      let ⟨cy', hcy', ecy'⟩ := cmr.pcore_ne (OFE.equiv_dist.mp e n) ps
      have: cy' = cy := Option.some_inj.mp (hcy' ▸ hcy)
      this ▸ ecy'
    exact equiv_dist.mpr this

  theorem pcore_proper' {x y: α}(e: x ≡ y): cmr.pcore x ≡ cmr.pcore y :=
    NonExpansive.eqv e

  theorem pcore_op_left' {x: α} {cx} (e: cmr.pcore x ≡ some cx): cx • x ≡ x :=
    let ⟨z, pz, ez⟩ := OFE.equiv_some e
    calc
      cx • x ≡ z • x := op_left_eqv _ ez.symm
      _      ≡ x     := cmr.pcore_op_left pz

  theorem pcore_op_right {x: α} {cx} (e: cmr.pcore x = some cx): x • cx ≡ x :=
    calc
      x • cx ≡ cx • x := cmr.comm
      _      ≡ x      := cmr.pcore_op_left e

  theorem pcore_op_right' {x: α} {cx} (e: cmr.pcore x ≡ some cx): x • cx ≡ x :=
    let ⟨_, pz, ez⟩ := OFE.equiv_some e
    (op_right_eqv x ez).symm.trans (pcore_op_right pz)

  theorem pcore_idemp' {x: α} {cx} (e: cmr.pcore x ≡ some cx): cmr.pcore cx ≡ some cx :=
    let ⟨y, py, (ey: y ≡ cx)⟩ := OFE.equiv_some e
    calc
      cmr.pcore cx ≡ cmr.pcore y := pcore_proper' ey.symm
      _            ≡ some y      := cmr.pcore_idem py
      _            ≡ some cx     := ey

  theorem pcore_op_dup {x: α}{cx} (e: cmr.pcore x = some cx): cx ≡ cx • cx :=
    (pcore_op_right' (cmr.pcore_idem e)).symm

  theorem pcore_op_dup' {x: α}{cx} (e: cmr.pcore x ≡ some cx): cx ≡ cx • cx :=
    let ⟨z, pz, ez⟩ := OFE.equiv_some e
    have : z • z ≡ z := pcore_op_right' (cmr.pcore_idem pz)
    calc
      cx ≡ z := ez.symm
      _ ≡ z • z := this.symm
      _ ≡ cx • z := op_left_eqv z ez
      _ ≡ cx • cx := op_right_eqv cx ez

  theorem pcore_validN {n} {x: α} {cx} : cmr.pcore x = some cx → ✓{n} x → ✓{n} cx :=
    λe v ↦
      have: ✓{n}x • cx := validN_of_eqv (pcore_op_right e).symm v
      validN_op_right this

  theorem pcore_valid {x: α} {cx} : cmr.pcore x = some cx → ✓ x → ✓ cx :=
    λe ↦ valid_mapN (λ_ ↦ pcore_validN e)


  -- Exclusive elements
  theorem not_valid_exclN_op_left n (x: α) [ex: CMRA.Exclusive x] y : ✓{n} (x • y) → False :=
    n.recOn ex.exclusive0_l (λ_ ih ↦ ih ∘ cmr.validN_succ)

  theorem not_valid_exclN_op_right n (x: α) [ex: CMRA.Exclusive x] y : ✓{n} (y • x) → False :=
    λv ↦ not_valid_exclN_op_left n x y (validN_of_eqv cmr.comm v)

  theorem not_valid_excl_op_left  (x: α) [ex: CMRA.Exclusive x] y : ✓ (x • y) → False :=
    λv ↦ ex.exclusive0_l (cmr.valid_iff_validN.mp v 0)

  theorem not_excl_op_right  (x: α) [ex: CMRA.Exclusive x] y : ✓ (y • x) → False :=
    λv ↦ not_valid_excl_op_left x y (valid_of_eqv cmr.comm v)

  theorem none_of_excl_valid_op n (x: α) [ex: CMRA.Exclusive x] my : ✓{n} (x •? my) → my = none :=
    match my with
    | .none => by simp [CMRA.op?]
    | .some y => by simp [CMRA.op?]; exact not_valid_exclN_op_left n x y

  theorem not_valid_of_exclN_inc n (x: α) [ex: CMRA.Exclusive x] y
      : x ≼{n} y → ✓{n} y → False :=
    λle v ↦
      let ⟨_, hz⟩ := le
      have := cmr.validN_ne hz v
      not_valid_exclN_op_left _ _ _ this

  theorem not_valid_of_excl_inc (x: α) [ex: CMRA.Exclusive x] y
      : x ≼ y → ✓ y → False :=
    λle v ↦
      have ⟨z, hz⟩ := le
      have: ✓{0}x • z := validN_of_eqv hz (cmr.valid_iff_validN.mp v 0)
      ex.exclusive0_l this


  -- Order
  instance : Trans cmr.Equiv cmr.included cmr.included where
    trans := λe l ↦ l.elim λt et ↦ ⟨t, et.trans (op_left_eqv _ e.symm)⟩

  instance : Trans cmr.included cmr.Equiv cmr.included where
    trans := λl e ↦ l.elim λt et ↦ ⟨t, e.symm.trans et⟩

  instance {n: Nat}: Trans (cmr.includedN n) (cmr.Dist n) (cmr.includedN n) where
    trans := λl e ↦ l.elim λt et ↦ ⟨t, e.symm.trans et⟩

  instance {n: Nat}: Trans (cmr.Dist n) (cmr.includedN n) (cmr.includedN n) where
    trans := λe l ↦ l.elim λt et ↦ ⟨t, et.trans (op_left_dist _ e.symm)⟩

  theorem incN_of_inc n {x y: α} : x ≼ y → x ≼{n} y :=
    λle ↦ le.elim (λz hz ↦ ⟨z, Equiv.dist hz⟩)

  theorem inc_trans {x y z: α}(i1: x ≼ y)(i2: y ≼ z): x ≼ z :=
    have ⟨w, (hw : y ≡ x • w)⟩ := i1
    have ⟨t, (ht : z ≡ y • t)⟩ := i2
    suffices h: z ≡ x • (w • t) from ⟨w • t, h⟩
    calc
      z ≡ y • t := ht
      _ ≡ (x • w) • t := op_left_eqv _ hw
      _ ≡ x • (w • t) := cmr.assoc.symm

  theorem incN_trans {x y z: α}(i1: x ≼{n} y)(i2: y ≼{n} z): x ≼{n} z :=
    have ⟨w, (hw : y ≡{n}≡ x • w)⟩ := i1
    have ⟨t, (ht : z ≡{n}≡ y • t)⟩ := i2
    suffices h: z ≡{n}≡ x • (w • t) from ⟨w • t, h⟩
    calc
      z ≡{n}≡ y • t := ht
      _ ≡{n}≡ (x • w) • t := op_left_dist _ hw
      _ ≡{n}≡ x • (w • t) := op_assocN.symm

  instance : Trans cmr.included cmr.included cmr.included where
    trans := inc_trans

  instance : Trans (cmr.includedN n) (cmr.includedN n) (cmr.includedN n) where
    trans := incN_trans

  theorem valid_of_inc (x y: α) : x ≼ y → ✓ y → ✓ x :=
    λle v ↦ le.elim (λ_ hz ↦ valid_op_left (valid_of_eqv hz v))

  theorem validN_of_incN n (x y: α) : x ≼{n} y → ✓{n} y → ✓{n} x :=
    λle v ↦ le.elim (λ_ hz ↦ cmr.validN_op_left (CMRA.validN_ne hz v))

  theorem validN_of_inc n (x y: α) : x ≼ y → ✓{n} y → ✓{n} x :=
    λle v ↦ le.elim λz hz ↦
      have : ✓{n}x • z := cmr.validN_ne (equiv_dist.mp hz n) v
      cmr.validN_op_left this

  theorem incN_of_incN_le {n n'} {x y: α} : n' ≤ n → x ≼{n} y → x ≼{n'} y :=
    λl1 l2 ↦ l2.elim λz hz ↦ ⟨z, Dist.le hz l1⟩

  theorem incN_of_incN_succ n (x y: α) : x ≼{n.succ} y → x ≼{n} y :=
    incN_of_incN_le (Nat.le_succ n)

  theorem incN_op_left n (x y: α) : x ≼{n} x • y := ⟨y, Dist.rfl⟩

  theorem inc_op_left (x y: α) : x ≼ x • y := ⟨y, Equiv.rfl⟩

  theorem inc_op_right (x y: α) : y ≼ x • y := ⟨x, cmr.comm⟩

  theorem incN_op_right n (x y: α) : y ≼{n} x • y :=
    (inc_op_right x y).elim (λz hz ↦ ⟨z, Equiv.dist hz⟩)

  theorem pcore_mono
    : x ≼ y → cmr.pcore x = some cx → ∃ cy, cmr.pcore y = some cy ∧ cx ≼ cy :=
  λle e ↦
    let ⟨w, hw⟩ := le
    have ⟨z, hz⟩ := cmr.pcore_op_mono _ e
    have h2: cmr.pcore y ≡ cmr.pcore (x • w) := NonExpansive.eqv hw
    let ⟨t, ht, et⟩ := OFE.equiv_some (hz ▸ h2)
    ⟨t, ht, z, et⟩

  theorem pcore_mono' {x y: α} {cx} :
      x ≼ y → cmr.pcore x ≡ some cx → ∃ cy, cmr.pcore y = some cy ∧ cx ≼ cy :=
    λle e ↦
      let ⟨_, hw, ew⟩ := OFE.equiv_some e
      have ⟨t, ht, z, et⟩ := pcore_mono le hw
      ⟨t, ht, z, et.trans (op_left_eqv z ew)⟩

  theorem pcore_monoN' {n} {x y: α} {cx} :
      x ≼{n} y → cmr.pcore x ≡{n}≡ some cx → ∃ cy, cmr.pcore y = some cy ∧ cx ≼{n} cy :=
    λle e ↦
      let ⟨z, hz⟩ := le
      let ⟨w, hw, ew⟩ := OFE.dist_some_right e
      let ⟨t, ht, (et : w ≼ t)⟩ := pcore_mono (inc_op_left x z) hw
      have: cmr.pcore y ≡{n}≡ some t :=
        have: cmr.pcore y ≡{n}≡ cmr.pcore (x • z) := NonExpansive.ne hz
        ht ▸ this
      let ⟨r, hr, er⟩ := OFE.dist_some_right this
      suffices h: cx≼{n}r from ⟨r, hr, h⟩
      calc
        cx ≡{n}≡ w := ew
        w  ≼{n}  t := incN_of_inc n et
        t  ≡{n}≡ r := er

  theorem pcore_inc_self (x: α) cx : cmr.pcore x = some cx → cx ≼ x :=
    λe ↦ ⟨x, (cmr.pcore_op_left e).symm⟩

  theorem op_mono_left (x y z: α) : x ≼ y → z • x ≼ z • y :=
    λle ↦
      let ⟨w, hw⟩ := le
      suffices h: z • y ≡ (z • x) • w from ⟨w, h⟩
      calc
        z • y ≡ z • (x • w) := op_right_eqv z hw
        _     ≡ (z • x) • w := cmr.assoc

  theorem op_monoN_left n (x y z: α) : x ≼{n} y → z • x ≼{n} z • y :=
    λle ↦
      let ⟨w, hw⟩ := le
      suffices h: z • y ≡{n}≡ (z • x) • w from ⟨w, h⟩
      calc
        z • y ≡{n}≡ z • (x • w) := op_right_dist z hw
        _     ≡{n}≡ (z • x) • w := op_assocN


  theorem op_monoN_right n (x y z: α) : x ≼{n} y → x • z ≼{n} y • z :=
    λle ↦
      let ⟨w, hw⟩ := le
      suffices h: y • z ≡{n}≡ (x • z) • w from ⟨w, h⟩
      calc
        y • z ≡{n}≡ (x • w) • z := op_left_dist z hw
        _     ≡{n}≡ x • (w • z) := op_assocN.symm
        _     ≡{n}≡ x • (z • w) := op_right_dist x (op_commN)
        _     ≡{n}≡ (x • z) • w := op_assocN

  theorem op_mono_right (x y z: α) : x ≼ y → x • z ≼ y • z :=
    λle ↦
      let ⟨w, hw⟩ := le
      suffices h: y • z ≡ (x • z) • w from ⟨w, h⟩
      calc
        y • z ≡ (x • w) • z := op_left_eqv z hw
        _     ≡ x • (w • z) := cmr.assoc.symm
        _     ≡ x • (z • w) := op_right_eqv x cmr.comm
        _     ≡ (x • z) • w := cmr.assoc

  theorem op_monoN n (x1 x2 y1 y2: α) : x1 ≼{n} y1 → x2 ≼{n} y2 → x1 • x2 ≼{n} y1 • y2 :=
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

  theorem op_mono (x1 x2 y1 y2: α) : x1 ≼ y1 → x2 ≼ y2 → x1 • x2 ≼ y1 • y2 :=
    λl1 l2 ↦
      let ⟨w, hw⟩ := l1;  let ⟨t, ht⟩ := l2
      suffices h: y1 • y2 ≡ (x1 • x2) • (w • t) from ⟨w • t, h⟩
      calc
        y1 • y2 ≡ (x1 • w) • y2 := op_left_eqv _ hw
        _       ≡ (x1 • w) • (x2 • t) := op_right_eqv _ ht
        _       ≡ x1 • (w • (x2 • t)) := cmr.assoc.symm
        _       ≡ x1 • ((x2 • t) • w) := op_right_eqv _ (cmr.comm)
        _       ≡ (x1 • (x2 • t)) • w := cmr.assoc
        _       ≡ ((x1 • x2) • t) • w := op_left_eqv _ cmr.assoc
        _       ≡ (x1 • x2) • (t • w) := cmr.assoc.symm
        _       ≡ (x1 • x2) • (w • t) := op_right_eqv _ (cmr.comm)

  theorem core_eqv_dup (x: α)[ci: CMRA.CoreId x]: x ≡ x • x := pcore_op_dup' ci.core_id

  theorem op_core_of_included {x y: α}[cx: CMRA.CoreId x](inc: x ≼ y): y ≡ y • x :=
    sorry

  theorem coreId_of_pcore_eq_some {x y: α}(e: cmr.pcore x = some y): CMRA.CoreId y :=
    have := cmr.pcore_idem e
    { core_id := this }

  section total
    variable [tot: CMRA.IsTotal α]

    theorem pcore_eq_core (x: α): cmr.pcore x = some (cmr.core x) := by
      unfold CMRA.core
      have ⟨cx, hcx⟩ := tot.total x
      simp [hcx]

    theorem op_core (x: α): x • cmr.core x ≡ x := pcore_op_right (pcore_eq_core x)

    theorem core_op_core  {x: α}: cmr.core x • cmr.core x ≡ cmr.core x :=
      (pcore_op_dup (pcore_eq_core x)).symm
    theorem validN_core {n}{x: α}(v: ✓{n} x): ✓{n} cmr.core x := pcore_validN (pcore_eq_core x) v
    theorem valid_core {x: α}(v: ✓ x): ✓ cmr.core x := pcore_valid (pcore_eq_core x) v

    theorem coreId_iff_core_eqv_self: CMRA.CoreId x ↔ cmr.core x ≡ x :=
      have left ci: some (CMRA.core x) ≡ some x := (pcore_eq_core x) ▸ ci.core_id
      have right e: CMRA.CoreId x :=
        { core_id := (pcore_eq_core x) ▸ OFE.some_eqv_some_of_eqv e }
      ⟨left, right⟩

    theorem core_eqv_self_of_coreId [ci: CMRA.CoreId x]: cmr.core x ≡ x :=
      coreId_iff_core_eqv_self.mp ci

    theorem core_inc_self {x: α} [ci: CMRA.CoreId x]: cmr.core x ≼ x :=
      suffices h: x ≡ CMRA.core x • x from ⟨x, h⟩
      calc
        x ≡ x • x := core_eqv_dup x
        _ ≡ CMRA.core x • x := op_left_eqv _ (core_eqv_self_of_coreId.symm)

    -- Global Instance cmra_includedN_preorder n : PreOrder (@includedN A _ _ n).
    -- Global Instance cmra_included_preorder : PreOrder (@included A _ _).

    theorem core_incN_core {n} {x y: α} (inc: x ≼{n} y): cmr.core x ≼{n} cmr.core y :=
      have: CMRA.pcore x ≡{n}≡ some (cmr.core x) :=
        by rw [pcore_eq_core x]; exact Dist.of_eq rfl
      let ⟨cy, hcy, icy⟩ := pcore_monoN' inc this
      calc
        cmr.core x ≼{n} cy         := icy
        cy         =    cmr.core y := Eq.symm $ Option.some_inj.mp $ (pcore_eq_core y) ▸ hcy
  end total
end CRMA
