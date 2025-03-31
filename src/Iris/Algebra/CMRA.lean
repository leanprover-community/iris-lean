/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Сухарик (@suhr), Markus de Medeiros
-/
import Iris.Algebra.OFE

namespace Iris
open OFE

class CMRA (α : Type _) extends OFE α where
  pcore : α → Option α
  op : α → α → α
  ValidN : Nat → α → Prop
  Valid : α → Prop

  op_ne : NonExpansive (op x)
  pcore_ne : x ≡{n}≡ y → pcore x = some cx →
    ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy
  validN_ne : x ≡{n}≡ y → ValidN n x → ValidN n y

  valid_iff_validN : Valid x ↔ ∀ n, ValidN n x
  validN_succ : ValidN n.succ x → ValidN n x
  validN_op_left : ValidN n (op x y) → ValidN n x

  assoc : op x (op y z) ≡ op (op x y) z
  comm : op x y ≡ op y x

  pcore_op_left : pcore x = some cx → op cx x ≡ x
  pcore_idem : pcore x = some cx → pcore cx ≡ some cx
  pcore_op_mono y : pcore x = some cx → ∃ cy, pcore (op x y) = some (op cx cy)

  extend : ValidN n x → x ≡{n}≡ op y₁ y₂ →
    Σ' z₁ z₂, x ≡ op z₁ z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂

namespace CMRA
variable [CMRA α]

infix:60 " • " => op

def Included (x y : α) : Prop := ∃ z, y ≡ x • z
infix:50 " ≼ " => Included

def IncludedN (n : Nat) (x y : α) : Prop := ∃ z, y ≡{n}≡ x • z
notation:50 x " ≼{" n "} " y:51 => IncludedN n x y

def op? [CMRA α] (x : α) : Option α → α
  | some y => x • y
  | none => x
infix:60 " •? " => op?

prefix:50 "✓ " => Valid
notation:50 "✓{" n "} " x:51 => ValidN n x

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

namespace CMRA
variable [CMRA α]

instance : NonExpansive (pcore (α := α)) where
  ne n x {y} e := by
    suffices ∀ ox oy, pcore x = ox → pcore y = oy → pcore x ≡{n}≡ pcore y from
      this (pcore x) (pcore y) rfl rfl
    intro ox oy ex ey
    match ox, oy with
    | .some a, .some b =>
      let ⟨w, hw, ew⟩ := pcore_ne e ex
      calc
        pcore x ≡{n}≡ some a  := .of_eq ex
        _       ≡{n}≡ some w  := ew
        _       ≡{n}≡ pcore y := .of_eq hw.symm
    | .some a, .none =>
      let ⟨w, hw, ew⟩ := pcore_ne e ex
      cases hw.symm ▸ ey
    | .none, .some b =>
      let ⟨w, hw, ew⟩ := pcore_ne e.symm ey
      cases hw.symm ▸ ex
    | .none, .none => rw [ex, ey]; trivial

/-! ## Op -/

theorem CoreID_proper (x₁ x₂ : α) (H1 : x₁ ≡ x₂) : CMRA.CoreId x₁ ↔ CMRA.CoreId x₂ :=
  sorry

theorem Exclusive_proper (x₁ x₂ : α) (H1 : x₁ ≡ x₂) : CMRA.Exclusive x₁ ↔ CMRA.Exclusive x₂ :=
  sorry

theorem Cancelable_proper (x₁ x₂ : α) (H1 : x₁ ≡ x₂) : CMRA.Cancelable x₁ ↔ CMRA.Cancelable x₂ :=
  sorry

theorem IdFree_proper (x₁ x₂ : α) (H1 : x₁ ≡ x₂) : CMRA.IdFree x₁ ↔ CMRA.IdFree x₂ :=
  sorry

theorem IdFree_ne (x₁ x₂ : α) n (H1 : x₁ ≡{n}≡ x₂) : CMRA.IdFree x₁ ↔ CMRA.IdFree x₂ :=
  sorry

-- Op

theorem op_right_eqv (x : α) {y z : α} (e : y ≡ z) : x • y ≡ x • z := op_ne.eqv e
theorem _root_.Iris.OFE.Equiv.op_r {x y z : α} : y ≡ z → x • y ≡ x • z := op_right_eqv _

theorem op_right_dist (x : α) {y z : α} (e : y ≡{n}≡ z) : x • y ≡{n}≡ x • z :=
  op_ne.ne e
theorem _root_.Iris.OFE.Dist.op_r {x y z : α} : y ≡{n}≡ z → x • y ≡{n}≡ x • z := op_right_dist _

theorem op_commN {x y : α} : x • y ≡{n}≡ y • x := OFE.equiv_dist.mp comm n

theorem op_assocN {x y z : α} : x • (y • z) ≡{n}≡ (x • y) • z :=
  OFE.equiv_dist.mp assoc n

theorem op_left_eqv {x y : α} (z : α) (e : x ≡ y) : x • z ≡ y • z :=
  comm.trans <| e.op_r.trans comm
theorem _root_.Iris.OFE.Equiv.op_l {x y z : α} : x ≡ y → x • z ≡ y • z := op_left_eqv _

theorem op_left_dist {x y : α} (z : α) (e : x ≡{n}≡ y) : x • z ≡{n}≡ y • z :=
  op_commN.trans <| e.op_r.trans op_commN
theorem _root_.Iris.OFE.Dist.op_l {x y z : α} : x ≡{n}≡ y → x • z ≡{n}≡ y • z := op_left_dist _

theorem op_eqv {x x' y y' : α} (ex : x ≡ x') (ey : y ≡ y') : x • y ≡ x' • y' :=
  ex.op_l.trans ey.op_r
theorem _root_.Iris.OFE.Equiv.op : (x : α) ≡ x' → y ≡ y' → x • y ≡ x' • y' := op_eqv

theorem op_ne2 (x₁ x₂ y₁ y₂ : α) n  (H1 : x₁ ≡{n}≡ x₂) (H2 : y₁ ≡{n}≡ y₂) : x₁ • y₁ ≡{n}≡ x₂ • y₂ :=
  sorry

theorem op_proper2 (x₁ x₂ y₁ y₂ : α) (H1 : x₁ ≡ x₂) (H2 : y₁ ≡ y₂) : x₁ • y₁ ≡ x₂ • y₂ :=
  sorry

theorem opM_ne2 (x₁ x₂ y₁ y₂ : α) n (H1 : x₁ ≡{n}≡ x₂) (H2 : y₁ ≡{n}≡ y₂) : x₁ •? y₁ ≡{n}≡ x₂ •? y₂ :=
  sorry

theorem opM_proper2 (x₁ x₂ y₁ y₂ : α) (H1 : x₁ ≡ x₂) (H2 : y₁ ≡ y₂) : x₁ •? y₁ ≡ x₂ •? y₂ :=
  sorry

-- Validity

theorem op_opM_assoc (x y : α) (mz : Option α) : (x • y) •? mz ≡ x • (y •? mz) := by
  unfold CMRA.op?; cases mz <;> simp [assoc, Equiv.symm]

/-! ## Validity -/

theorem Valid.validN : ✓ (x : α) → ✓{n} x := (valid_iff_validN.1 · _)

theorem valid_mapN {x y : α} (f : ∀ n, ✓{n} x → ✓{n} y) (v : ✓ x) : ✓ y :=
  valid_iff_validN.mpr fun n => f n v.validN

theorem validN_of_eqv {x y : α} : x ≡ y → ✓{n} x → ✓{n} y :=
  fun e v => validN_ne (equiv_dist.mp e n) v

theorem validN_iff {x y : α} (e : x ≡{n}≡ y) : ✓{n} x ↔ ✓{n} y := ⟨validN_ne e, validN_ne e.symm⟩
theorem _root_.Iris.OFE.Dist.validN : (x : α) ≡{n}≡ y → (✓{n} x ↔ ✓{n} y) := validN_iff


theorem valid_of_eqv {x y : α} : x ≡ y → ✓ x → ✓ y :=
  fun e => valid_mapN fun _ => validN_of_eqv e

-- theorem validN_ne (x₁ x₂ : α) n (H : x₁ ≡{n}≡ x₂) : ✓{n} x₁ ↔ ✓{n} x₂ :=
--   sorry

theorem validN_proper (x₁ x₂ : α) n (H : x₁ ≡ x₂) : ✓{n} x₁ ↔ ✓{n} x₂ :=
  sorry

theorem valid_proper (x₁ x₂ : α) (H : x₁ ≡ x₂) : ✓ x₁ ↔ ✓ x₂ :=
  sorry

theorem valid_iff {x y : α} (e : x ≡ y) : ✓ x ↔ ✓ y := ⟨valid_of_eqv e, valid_of_eqv e.symm⟩
theorem _root_.Iris.OFE.Equiv.valid : (x : α) ≡ y → (✓ x ↔ ✓ y) := valid_iff

theorem validN_of_le n n' {x : α} : n' ≤ n → ✓{n} x → ✓{n'} x :=
  fun le => le.recOn id fun  _ ih vs => ih (CMRA.validN_succ vs)

theorem validN_op_right {n} {x y : α} : ✓{n} (x • y) → ✓{n} y :=
  fun v => validN_op_left (validN_of_eqv comm v)

theorem valid_op_right (x y : α) : ✓ (x • y) → ✓ y :=
  valid_mapN fun _ => validN_op_right

theorem valid_op_left {x y : α} : ✓ (x • y) → ✓ x :=
  fun v => valid_op_right y x (valid_of_eqv comm v)

/-! ## Core -/

theorem pcore_proper {x y : α} (cx : α) (e : x ≡ y) (ps : pcore x = some cx)
    : ∃ cy, pcore y = some cy ∧ cx ≡ cy := by
  let ⟨cy, hcy, ecy⟩ := pcore_ne (OFE.equiv_dist.mp e 0) ps
  refine ⟨cy, hcy, ?_⟩
  have (n : Nat) : cx ≡{n}≡ cy :=
    let ⟨cy', hcy', ecy'⟩ := pcore_ne (OFE.equiv_dist.mp e n) ps
    have : cy' = cy := Option.some_inj.mp (hcy' ▸ hcy)
    this ▸ ecy'
  exact equiv_dist.mpr this

theorem pcore_proper' {x y : α} (e : x ≡ y) : pcore x ≡ pcore y :=
  NonExpansive.eqv e

theorem pcore_op_left' {x : α} {cx} (e : pcore x ≡ some cx) : cx • x ≡ x :=
  let ⟨z, pz, ez⟩ := OFE.equiv_some e
  calc
    cx • x ≡ z • x := op_left_eqv _ ez.symm
    _      ≡ x     := pcore_op_left pz

theorem pcore_op_right {x : α} {cx} (e : pcore x = some cx) : x • cx ≡ x :=
  calc
    x • cx ≡ cx • x := comm
    _      ≡ x      := pcore_op_left e

theorem pcore_op_right' {x : α} {cx} (e : pcore x ≡ some cx) : x • cx ≡ x :=
  let ⟨_, pz, ez⟩ := OFE.equiv_some e
  (op_right_eqv x ez).symm.trans (pcore_op_right pz)

theorem pcore_idem' {x : α} {cx} (e : pcore x ≡ some cx) : pcore cx ≡ some cx :=
  let ⟨y, py, (ey : y ≡ cx)⟩ := OFE.equiv_some e
  calc
    pcore cx ≡ pcore y := pcore_proper' ey.symm
    _        ≡ some y  := pcore_idem py
    _        ≡ some cx := ey

theorem pcore_op_self {x : α} {cx} (e : pcore x = some cx) : cx • cx ≡ cx :=
  pcore_op_right' (pcore_idem e)

theorem pcore_op_self' {x : α} {cx} (e : pcore x ≡ some cx) : cx • cx ≡ cx :=
  let ⟨z, pz, ez⟩ := OFE.equiv_some e
  have : z • z ≡ z := pcore_op_right' (pcore_idem pz)
  (ez.op ez).symm.trans (this.trans ez)

theorem pcore_validN {n} {x : α} {cx} (e : pcore x = some cx) (v : ✓{n} x) : ✓{n} cx :=
  validN_op_right (validN_of_eqv (pcore_op_right e).symm v)

theorem pcore_valid {x : α} {cx} (e : pcore x = some cx) : ✓ x → ✓ cx :=
  valid_mapN fun _ => pcore_validN e

/-! ## Exclusive elements -/

theorem not_valid_exclN_op_left {n} {x : α} [Exclusive x] {y} : ¬✓{n} (x • y) :=
  n.recOn Exclusive.exclusive0_l fun _ ih => ih ∘ validN_succ

theorem not_valid_exclN_op_right {n} {x : α} [Exclusive x] {y} : ¬✓{n} (y • x) :=
  fun v => not_valid_exclN_op_left (validN_of_eqv comm v)

theorem not_valid_excl_op_left {x : α} [Exclusive x] {y} : ¬✓ (x • y) :=
  fun v => Exclusive.exclusive0_l v.validN

theorem not_excl_op_right {x : α} [Exclusive x] {y} : ¬✓ (y • x) :=
  fun v => not_valid_excl_op_left (valid_of_eqv comm v)

theorem none_of_excl_valid_op {n} {x : α} [Exclusive x] {my} : ✓{n} (x •? my) → my = none := by
  cases my <;> simp [CMRA.op?, not_valid_exclN_op_left]

theorem not_valid_of_exclN_inc {n} {x : α} [Exclusive x] {y} : x ≼{n} y → ¬✓{n} y
  | ⟨_, hz⟩, v => not_valid_exclN_op_left (validN_ne hz v)

theorem not_valid_of_excl_inc {x : α} [Exclusive x] {y} : x ≼ y → ¬✓ y
  | ⟨_, hz⟩, v => Exclusive.exclusive0_l <| validN_of_eqv hz v.validN

theorem incN_ne2 (x₁ x₂ y₁ y₂ : α) n (H1 : x₁ ≡{n}≡ x₂) (H2 : y₁ ≡{n}≡ y₂) : x₁ ≼{n} y₁ ↔ x₂ ≼{n} y₂ :=
  sorry

theorem incN_proper2 (x₁ x₂ y₁ y₂ : α) n (H1 : x₁ ≡ x₂) (H2 : y₁ ≡ y₂) : x₁ ≼{n} y₁ ↔ x₂ ≼{n} y₂ :=
  sorry

theorem inc_proper2 (x₁ x₂ y₁ y₂ : α) (H1 : x₁ ≡ x₂) (H2 : y₁ ≡ y₂) : x₁ ≼ y₁ ↔ x₂ ≼ y₂ :=
  sorry

/-! ## Order -/

theorem inc_of_eqv_of_inc (e : (a : α) ≡ b) : b ≼ c → a ≼ c
  | ⟨t, et⟩ => ⟨t, et.trans e.symm.op_l⟩

instance : Trans Equiv (Included (α := α)) Included where
  trans := inc_of_eqv_of_inc

theorem inc_of_inc_of_eqv : (a : α) ≼ b → b ≡ c → a ≼ c
  | ⟨t, et⟩, e => ⟨t, e.symm.trans et⟩

instance : Trans (Included (α := α)) Equiv Included where
  trans := inc_of_inc_of_eqv

theorem incN_of_incN_of_dist : (a : α) ≼{n} b → b ≡{n}≡ c → a ≼{n} c
  | ⟨t, et⟩, e => ⟨t, e.symm.trans et⟩

instance {n : Nat} : Trans (IncludedN (α := α) n) (Dist n) (IncludedN n) where
  trans := incN_of_incN_of_dist

theorem incN_of_dist_of_incN (e : (a : α) ≡{n}≡ b) : b ≼{n} c → a ≼{n} c
  | ⟨t, et⟩ => ⟨t, et.trans e.symm.op_l⟩

instance {n : Nat} : Trans (Dist (α := α) n) (IncludedN n) (IncludedN n) where
  trans := incN_of_dist_of_incN

theorem incN_of_inc (n) {x y : α} : x ≼ y → x ≼{n} y
  | ⟨z, hz⟩ => ⟨z, Equiv.dist hz⟩
theorem Included.incN {n} {x y : α} : x ≼ y → x ≼{n} y := incN_of_inc _

theorem inc_iff_left (e : (a : α) ≡ b) : a ≼ c ↔ b ≼ c :=
  ⟨inc_of_eqv_of_inc e.symm, inc_of_eqv_of_inc e⟩
theorem _root_.Iris.OFE.Equiv.inc_l : (a : α) ≡ b → (a ≼ c ↔ b ≼ c) := inc_iff_left

theorem inc_iff_right (e : (b : α) ≡ c) : a ≼ b ↔ a ≼ c :=
  ⟨(inc_of_inc_of_eqv · e), (inc_of_inc_of_eqv · e.symm)⟩
theorem _root_.Iris.OFE.Equiv.inc_r : (b : α) ≡ c → (a ≼ b ↔ a ≼ c) := inc_iff_right

theorem inc_iff (ea : (a : α) ≡ a') (eb : (b : α) ≡ b') : a ≼ b ↔ a' ≼ b' :=
  (inc_iff_left ea).trans (inc_iff_right eb)
theorem _root_.Iris.OFE.Equiv.inc : (a : α) ≡ a' → b ≡ b' → (a ≼ b ↔ a' ≼ b') := inc_iff

theorem incN_iff_left (e : (a : α) ≡{n}≡ b) : a ≼{n} c ↔ b ≼{n} c :=
  ⟨incN_of_dist_of_incN e.symm, incN_of_dist_of_incN e⟩
theorem _root_.Iris.OFE.Dist.incN_l : (a : α) ≡{n}≡ b → (a ≼{n} c ↔ b ≼{n} c) := incN_iff_left

theorem incN_iff_right (e : (b : α) ≡{n}≡ c) : a ≼{n} b ↔ a ≼{n} c :=
  ⟨(incN_of_incN_of_dist · e), (incN_of_incN_of_dist · e.symm)⟩
theorem _root_.Iris.OFE.Dist.incN_r : (b : α) ≡{n}≡ c → (a ≼{n} b ↔ a ≼{n} c) := incN_iff_right

theorem incN_iff (ea : (a : α) ≡{n}≡ a') (eb : (b : α) ≡{n}≡ b') : a ≼{n} b ↔ a' ≼{n} b' :=
  (incN_iff_left ea).trans (incN_iff_right eb)
theorem _root_.Iris.OFE.Dist.incN :
    (a : α) ≡{n}≡ a' → b ≡{n}≡ b' → (a ≼{n} b ↔ a' ≼{n} b') := incN_iff

theorem inc_trans {x y z : α} : x ≼ y → y ≼ z → x ≼ z
  | ⟨w, (hw : y ≡ x • w)⟩, ⟨t, (ht : z ≡ y • t)⟩ =>
    suffices h : z ≡ x • (w • t) from ⟨w • t, h⟩
    calc
      z ≡ y • t := ht
      _ ≡ (x • w) • t := op_left_eqv _ hw
      _ ≡ x • (w • t) := assoc.symm
theorem Included.trans : (x : α) ≼ y → y ≼ z → x ≼ z := inc_trans

instance : Trans (Included (α := α)) Included Included where
  trans := inc_trans

theorem incN_trans {x y z : α} : x ≼{n} y → y ≼{n} z → x ≼{n} z
  | ⟨w, (hw : y ≡{n}≡ x • w)⟩, ⟨t, (ht : z ≡{n}≡ y • t)⟩ =>
    suffices h : z ≡{n}≡ x • (w • t) from ⟨w • t, h⟩
    calc
      z ≡{n}≡ y • t := ht
      _ ≡{n}≡ (x • w) • t := op_left_dist _ hw
      _ ≡{n}≡ x • (w • t) := op_assocN.symm

theorem IncludedN.trans : (x : α) ≼{n} y → y ≼{n} z → x ≼{n} z := incN_trans

instance : Trans (IncludedN (α := α) n) (IncludedN n) (IncludedN n) where
  trans := incN_trans

theorem valid_of_inc {x y : α} : x ≼ y → ✓ y → ✓ x
  | ⟨_, hz⟩, v => valid_op_left (valid_of_eqv hz v)

theorem validN_of_incN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne hz v)

theorem validN_of_inc {n} {x y : α} : x ≼ y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne (equiv_dist.mp hz n) v)

theorem incN_of_incN_le {n n'} {x y : α} (l1 : n' ≤ n) : x ≼{n} y → x ≼{n'} y
  | ⟨z, hz⟩ => ⟨z, Dist.le hz l1⟩

theorem incN_of_incN_succ {n} {x y : α} : x ≼{n.succ} y → x ≼{n} y :=
  incN_of_incN_le (Nat.le_succ n)

theorem incN_op_left (n) (x y : α) : x ≼{n} x • y := ⟨y, Dist.rfl⟩

theorem inc_op_left (x y : α) : x ≼ x • y := ⟨y, Equiv.rfl⟩

theorem inc_op_right (x y : α) : y ≼ x • y := ⟨x, comm⟩

theorem incN_op_right (n) (x y : α) : y ≼{n} x • y :=
  (inc_op_right x y).elim fun z hz => ⟨z, Equiv.dist hz⟩

theorem pcore_mono {x y : α} : x ≼ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ cy
  | ⟨_, hw⟩, e =>
    have ⟨z, hz⟩ := pcore_op_mono _ e
    let ⟨t, ht, et⟩ := OFE.equiv_some (hz ▸ NonExpansive.eqv hw)
    ⟨t, ht, z, et⟩

theorem pcore_mono' {x y : α} {cx} (le : x ≼ y) (e : pcore x ≡ some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼ cy :=
  let ⟨_, hw, ew⟩ := OFE.equiv_some e
  have ⟨t, ht, z, et⟩ := pcore_mono le hw
  ⟨t, ht, z, et.trans ew.op_l⟩

theorem pcore_monoN' {n} {x y : α} {cx} :
    x ≼{n} y → pcore x ≡{n}≡ some cx → ∃ cy, pcore y = some cy ∧ cx ≼{n} cy
  | ⟨z, hz⟩, e =>
    let ⟨w, hw, ew⟩ := OFE.dist_some_right e
    let ⟨t, ht, (et : w ≼ t)⟩ := pcore_mono (inc_op_left x z) hw
    have : pcore y ≡{n}≡ some t :=
      have : pcore y ≡{n}≡ pcore (x • z) := NonExpansive.ne hz
      ht ▸ this
    let ⟨r, hr, er⟩ := OFE.dist_some_right this
    suffices h : cx ≼{n} r from ⟨r, hr, h⟩
    calc
      cx ≡{n}≡ w := ew
      w  ≼{n}  t := incN_of_inc n et
      t  ≡{n}≡ r := er

theorem pcore_inc_self {x : α} {cx} (e : pcore x = some cx) : cx ≼ x :=
  ⟨x, (pcore_op_left e).symm⟩

theorem op_mono_right {x y} (z : α) : x ≼ y → z • x ≼ z • y
  | ⟨w, hw⟩ => ⟨w, hw.op_r.trans assoc⟩

theorem op_monoN_right {n x y} (z : α) : x ≼{n} y → z • x ≼{n} z • y
  | ⟨w, hw⟩ => ⟨w, hw.op_r.trans op_assocN⟩

theorem op_monoN_left {n x y} (z : α) (h : x ≼{n} y) : x • z ≼{n} y • z :=
  (comm.dist.incN comm.dist).1 (op_monoN_right z h)

theorem op_mono_left {x y} (z : α) (h : x ≼ y) : x • z ≼ y • z :=
  (comm.inc comm).1 (op_mono_right z h)

theorem op_monoN {n} {x x' y y' : α} (hx : x ≼{n} x') (hy : y ≼{n} y') : x • y ≼{n} x' • y' :=
  (op_monoN_left _ hx).trans (op_monoN_right _ hy)

theorem op_mono {x x' y y' : α} (hx : x ≼ x') (hy : y ≼ y') : x • y ≼ x' • y' :=
  (op_mono_left _ hx).trans (op_mono_right _ hy)

theorem op_self (x : α) [CoreId x] : x • x ≡ x := pcore_op_self' CoreId.core_id

theorem op_core_right_of_inc {x y : α} [CoreId x] : x ≼ y → x • y ≡ y
  | ⟨_, hz⟩ => hz.op_r.trans <| assoc.trans <| (op_self _).op_l.trans hz.symm

theorem included_dist_l n (x1 x2 x1' : α) : x1 ≼ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ x2' ∧ x2' ≡{n}≡ x2 := by
  sorry

theorem op_core_left_of_inc {x y : α} [CoreId x] (le : x ≼ y) : y • x ≡ y :=
  comm.trans (op_core_right_of_inc le)

theorem CoreId.of_pcore_eq_some {x y : α} (e : pcore x = some y) : CoreId y where
  core_id := pcore_idem e

section total
variable [IsTotal α]

theorem pcore_eq_core (x : α) : pcore x = some (core x) := by
  unfold core
  have ⟨cx, hcx⟩ := IsTotal.total x
  simp [hcx]

theorem op_core (x : α) : x • core x ≡ x := pcore_op_right (pcore_eq_core x)
theorem core_op (x : α) : core x • x ≡ x := comm.trans (op_core x)

theorem core_op_core {x : α} : core x • core x ≡ core x :=
  pcore_op_self (pcore_eq_core x)
theorem validN_core {n} {x : α} (v : ✓{n} x) : ✓{n} core x := pcore_validN (pcore_eq_core x) v
theorem valid_core {x : α} (v : ✓ x) : ✓ core x := pcore_valid (pcore_eq_core x) v

theorem pcore_idemp (x : α) : core (core x) ≡ core x := by
 sorry

theorem tot_core_ne {x₁ x₂ : α} n (H : x₁ ≡{n}≡ x₂) : core x₁ ≡{n}≡ core x₂ := sorry

theorem tot_core_proper {x₁ x₂ : α} (H : x₁ ≡x₂) : core x₁ ≡ core x₂ := sorry

theorem core_eqv_self (x : α) [CoreId x] : core (x : α) ≡ x :=
  show some (core x) ≡ some x from pcore_eq_core x ▸ CoreId.core_id

theorem coreId_iff_core_eqv_self : CoreId (x : α) ↔ core x ≡ x := by
  refine ⟨fun _ => core_eqv_self x, fun e => ?_⟩
  exact { core_id := pcore_eq_core x ▸ OFE.some_eqv_some_of_eqv e }

theorem inc_refl (x : α) : x ≼ x := ⟨core x, (op_core _).symm⟩
theorem incN_refl (x : α) : x ≼{n} x := (inc_refl _).incN

theorem core_inc_self {x : α} [CoreId x] : core x ≼ x :=
  ⟨x, ((core_eqv_self x).op_l.trans (op_self _)).symm⟩

theorem core_incN_core {n} {x y : α} (inc : x ≼{n} y) : core x ≼{n} core y := by
  let ⟨cy, hcy, icy⟩ := pcore_monoN' inc (Dist.of_eq (pcore_eq_core x))
  cases (pcore_eq_core _).symm.trans hcy
  exact icy

theorem cmra_pcore_core_id {x y : α} (H : pcore x = some y) : CMRA.CoreId y :=  by
  sorry

-- instance : CMRA.CoreId (core y) := cmra_pcore_core_id (pcore_eq_core _)

-- What's the best way to port these?
-- Global Instance cmra_includedN_preorder n : PreOrder (@includedN A _ _ n).
-- Global Instance cmra_included_preorder : PreOrder (@included A _ _).

theorem core_mono {x y : α} (Hinc : x ≼ y) : core x ≼ core y := by
  have: CMRA.pcore x ≡ some (core x) :=
    by rw [pcore_eq_core x]; exact Equiv.rfl
  let ⟨cy, hcy, icy⟩ := pcore_mono' Hinc this
  calc
    core x ≼ cy         := icy
    cy         = core y := Eq.symm $ Option.some_inj.mp $ (pcore_eq_core y) ▸ hcy

end total


section discreteElements

variable {α : Type _} [CMRA α]

theorem discrete_inc_l {x y : α} (HD : DiscreteE x) (Hv : ✓{0} y) (Hle : x ≼{0} y) : x ≼ y :=
  sorry
-- Lemma cmra_discrete_included_l x y : Discrete x → ✓{0} y → x ≼{0} y → x ≼ y.
-- Proof.
--   intros ?? [x' ?].
--   destruct (cmra_extend 0 y x x') as (z&z'&Hy&Hz&Hz'); auto; simpl in *.
--   by exists z'; rewrite Hy (discrete_0 x z).
-- Qed.

theorem discrete_inc_r {x y : α} (HD : DiscreteE y) (Hv : ✓{0} y) (Hle : x ≼{0} y) : x ≼ y :=
  sorry
-- Lemma cmra_discrete_included_r x y : Discrete y → x ≼{0} y → x ≼ y.
-- Proof. intros ? [x' ?]. exists x'. by apply (discrete_0 y). Qed.

theorem discrete_op {x y : α} (Hx : DiscreteE x) (Hy : DiscreteE y) : DiscreteE (x • y) := by
  sorry
-- Lemma cmra_op_discrete x1 x2 :
--   ✓{0} (x1 ⋅ x2) → Discrete x1 → Discrete x2 → Discrete (x1 ⋅ x2).
-- Proof.
--   intros ??? z Hz.
--   destruct (cmra_extend 0 z x1 x2) as (y1&y2&Hz'&?&?); auto; simpl in *.
--   { rewrite -?Hz. done. }
--   by rewrite Hz' (discrete_0 x1 y1) // (discrete_0 x2 y2).
-- Qed.

end discreteElements

section discreteCMRA

variable {α : Type _} [CMRA α]

theorem discrete_valid_iff [CMRA.Discrete α] n {x : α} : ✓ x ↔ ✓{n} x := by sorry
-- Lemma cmra_discrete_valid_iff `{!CmraDiscrete A} n x : ✓ x ↔ ✓{n} x.
-- Proof.
--   split; first by rewrite cmra_valid_validN.
--   eauto using cmra_discrete_valid, cmra_validN_le with lia.
-- Qed.

theorem discrete_valid_iff_0 [CMRA.Discrete α] n {x : α} : ✓{0} x ↔ ✓{n} x := by sorry
-- Lemma cmra_discrete_valid_iff_0 `{!CmraDiscrete A} n x : ✓{0} x ↔ ✓{n} x.
-- Proof. by rewrite -!cmra_discrete_valid_iff. Qed.

theorem discrete_included_iff [Discrete α] n {x y : α} : x ≼ y ↔ x ≼{n} y := by sorry
-- Lemma cmra_discrete_included_iff `{!OfeDiscrete A} n x y : x ≼ y ↔ x ≼{n} y.
-- Proof.
--   split; first by apply cmra_included_includedN.
--   intros [z ->%(discrete_iff _ _)]; eauto using cmra_included_l.
-- Qed.

theorem discrete_included_iff_0 [Discrete α] n {x y : α} : x ≼{0} y ↔ x ≼{n} y := by sorry
-- Lemma cmra_discrete_included_iff_0 `{!OfeDiscrete A} n x y : x ≼{0} y ↔ x ≼{n} y.
-- Proof. by rewrite -!cmra_discrete_included_iff. Qed.

end discreteCMRA

section cancelableElements

variable {α : Type _} [CMRA α]

-- Global Instance cancelable_proper : Proper (equiv ==> iff) (@Cancelable A).
-- Proof. unfold Cancelable. intros x x' EQ. by setoid_rewrite EQ. Qed.

theorem cancelable {x y z : α} [CMRA.Cancelable x] : ✓(x • y) → x • y ≡ x • z → y ≡ z :=
  sorry
-- Lemma cancelable x `{!Cancelable x} y z :
-- Proof. rewrite !equiv_dist cmra_valid_validN. intros. by apply (cancelableN x). Qed.


theorem discrete_cancelable {x : α} [CMRA.Discrete α] (H : ∀ {y z : α}, ✓(x • y) → x •  y ≡ x • z → y ≡ z) :
    CMRA.Cancelable x :=
  sorry
-- Lemma discrete_cancelable x `{!CmraDiscrete A}:
--   (∀ y z, ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ≡ z) → Cancelable x.
-- Proof. intros ????. rewrite -!discrete_iff -cmra_discrete_valid_iff. auto. Qed.

instance cancelable_op {x y : α} [CMRA.Cancelable x] [CMRA.Cancelable y] : CMRA.Cancelable (x • y) :=
  sorry
-- Global Instance cancelable_op x y :
--   Cancelable x → Cancelable y → Cancelable (x ⋅ y).
-- Proof.
--   intros ?? n z z' ??. apply (cancelableN y), (cancelableN x).
--   - eapply cmra_validN_op_r. by rewrite assoc.
--   - by rewrite assoc.
--   - by rewrite !assoc.
-- Qed.

instance exclusive_cancelable {x : α} [CMRA.Exclusive x] : CMRA.Cancelable x := by
  sorry
-- Global Instance exclusive_cancelable (x : A) : Exclusive x → Cancelable x.
-- Proof. intros ? n z z' []%(exclusiveN_l _ x). Qed.

end cancelableElements

section idFreeElements

variable {α : Type _} [CMRA α]

-- Global Instance id_free_ne n : Proper (dist n ==> iff) (@IdFree A).
-- Proof.
--   intros x x' EQ%(dist_le _ 0); last lia. rewrite /IdFree.
--   split=> y ?; (rewrite -EQ || rewrite EQ); eauto.
-- Qed.

-- Global Instance id_free_proper : Proper (equiv ==> iff) (@IdFree A).
-- Proof. by move=> P Q /equiv_dist /(_ 0)=> ->. Qed.

theorem id_freeN_r n n' {x : α} [CMRA.IdFree x] {y} : ✓{n}x → ¬ (x • y ≡{n'}≡ x)  := sorry
-- Lemma id_freeN_r n n' x `{!IdFree x} y : ✓{n}x → x ⋅ y ≡{n'}≡ x → False.
-- Proof. eauto using cmra_validN_le, dist_le with lia. Qed.

theorem id_freeN_l n n' {x : α} [CMRA.IdFree x] {y} : ✓{n}x → ¬ (y • x ≡{n'}≡ x)  := sorry
-- Lemma id_freeN_l n n' x `{!IdFree x} y : ✓{n}x → y ⋅ x ≡{n'}≡ x → False.
-- Proof. rewrite comm. eauto using id_freeN_r. Qed.

theorem id_free_r {x : α} [CMRA.IdFree x] {y} : ✓x → ¬ (x • y ≡ x)  := sorry
-- Lemma id_free_r x `{!IdFree x} y : ✓x → x ⋅ y ≡ x → False.
-- Proof. move=> /cmra_valid_validN ? /equiv_dist. eauto. Qed.

theorem id_free_l {x : α} [CMRA.IdFree x] {y} : ✓x → ¬ (y • x ≡ x)  := sorry
-- Lemma id_free_l x `{!IdFree x} y : ✓x → y ⋅ x ≡ x → False.
-- Proof. rewrite comm. eauto using id_free_r. Qed.

theorem discrete_id_free {x : α} [CMRA.Discrete α] (H : ∀ y, ✓ x → x • y ≡ x → False) : CMRA.IdFree x := sorry
-- Lemma discrete_id_free x `{!CmraDiscrete A}:
--   (∀ y, ✓ x → x ⋅ y ≡ x → False) → IdFree x.
-- Proof.
--   intros Hx y ??. apply (Hx y), (discrete_0 _); eauto using cmra_discrete_valid.
-- Qed.

instance id_free_op_r {x y : α} [CMRA.IdFree y] [CMRA.Cancelable x] : CMRA.IdFree (x • y) := sorry
-- Global Instance id_free_op_r x y : IdFree y → Cancelable x → IdFree (x ⋅ y).
-- Proof.
--   intros ?? z ? Hid%symmetry. revert Hid. rewrite -assoc=>/(cancelableN x) ?.
--   eapply (id_free0_r y); [by eapply cmra_validN_op_r |symmetry; eauto].
-- Qed.

instance id_free_op_l {x y : α} [CMRA.IdFree x] [CMRA.Cancelable y] : CMRA.IdFree (x • y) := sorry
-- Global Instance id_free_op_l x y : IdFree x → Cancelable y → IdFree (x ⋅ y).
-- Proof. intros. rewrite comm. apply _. Qed.

instance exclusive_id_Free {x : α} [CMRA.Exclusive x] : CMRA.IdFree x := sorry
-- Global Instance exclusive_id_free x : Exclusive x → IdFree x.
-- Proof. intros ? z ? Hid. apply (exclusiveN_l 0 x z). by rewrite Hid. Qed.

end idFreeElements


section ucmra

variable {α : Type _} [UCMRA α]

theorem unit_validN n : ✓{n} (ε : α) := sorry
--   Lemma ucmra_unit_validN n : ✓{n} (ε:A).
--   Proof. apply cmra_valid_validN, ucmra_unit_valid. Qed.

theorem incN_unit n {x : α} : ε ≼{n} x := sorry
--   Lemma ucmra_unit_leastN n x : ε ≼{n} x.
--   Proof. by exists x; rewrite left_id. Qed.

theorem inc_unit {x : α} : ε ≼ x := sorry
--   Lemma ucmra_unit_least x : ε ≼ x.
--   Proof. by exists x; rewrite left_id. Qed.


theorem unit_right_id (x : α) :  x • unit  ≡ x :=  sorry
--   Global Instance ucmra_unit_right_id : RightId (≡) ε (@op A _).
--   Proof. by intros x; rewrite (comm op) left_id. Qed.

instance unit_CoreId : CMRA.CoreId (ε : α) := sorry
--   Global Instance ucmra_unit_core_id : CoreId (ε:A).
--   Proof. apply ucmra_pcore_unit. Qed.

instance unit_total : CMRA.IsTotal α where
  total := sorry
--   Global Instance cmra_unit_cmra_total : CmraTotal A.
--   Proof.
--     intros x. destruct (cmra_pcore_mono' ε x ε) as (cx&->&?); [..|by eauto].
--     - apply ucmra_unit_least.
--     - apply (core_id _).
--   Qed.

instance empty_cancelable : CMRA.Cancelable (ε : α) := sorry
--   Global Instance empty_cancelable : Cancelable (ε:A).
--   Proof. intros ???. by rewrite !left_id. Qed.


end ucmra


section leibniz

variable {α : Type _} [CMRA α] [Leibniz α]

theorem assoc_L {x y z : α} : x • (y • z) ≡ (x • y) • z := sorry

theorem comm_L {x y : α} : (x • y)  ≡ (y • x) := sorry

theorem pcore_l_L {x cx : α} : CMRA.pcore x = some cx → cx • x = x := sorry
--   Lemma cmra_pcore_l_L x cx : pcore x = Some cx → cx ⋅ x = x.
--   Proof. unfold_leibniz. apply cmra_pcore_l'. Qed.

theorem pcore_idemp_L {x cx : α} : CMRA.pcore x = some cx → CMRA.pcore cx = some cx := sorry
--   Lemma cmra_pcore_idemp_L x cx : pcore x = Some cx → pcore cx = Some cx.
--   Proof. unfold_leibniz. apply cmra_pcore_idemp'. Qed.

theorem op_opM_assoc_L {x y : α} {mz} : (x • y) •? mz = x • (y •? mz) := sorry
--   Lemma cmra_op_opM_assoc_L x y mz : (x ⋅ y) ⋅? mz = x ⋅ (y ⋅? mz).
--   Proof. unfold_leibniz. apply cmra_op_opM_assoc. Qed.

theorem pcore_r_L {x cx : α} : CMRA.pcore x = some cx → x • cx = x := sorry
--   Lemma cmra_pcore_r_L x cx : pcore x = Some cx → x ⋅ cx = x.
--   Proof. unfold_leibniz. apply cmra_pcore_r'. Qed.

theorem pcore_dup_L {x cx : α} : CMRA.pcore x = some cx → cx • cx = cx := sorry
--   Lemma cmra_pcore_dup_L x cx : pcore x = Some cx → cx = cx ⋅ cx.
--   Proof. unfold_leibniz. apply cmra_pcore_dup'. Qed.

theorem core_id_dup_L {x : α} [CMRA.CoreId x] : x = x • x := sorry
--   Lemma core_id_dup_L x `{!CoreId x} : x = x ⋅ x.
--   Proof. unfold_leibniz. by apply core_id_dup. Qed.

theorem core_r_L {x : α} [CMRA.IsTotal α] : x • CMRA.core x = x := sorry
--     Lemma cmra_core_r_L x : x ⋅ core x = x.
--     Proof. unfold_leibniz. apply cmra_core_r. Qed.

theorem core_l_L {x : α} [CMRA.IsTotal α] : CMRA.core x • x = x := sorry
--     Lemma cmra_core_l_L x : core x ⋅ x = x.
--     Proof. unfold_leibniz. apply cmra_core_l. Qed.

theorem core_idemp_L {x : α} [CMRA.IsTotal α] : CMRA.core (CMRA.core x) = CMRA.core x := sorry
--     Lemma cmra_core_idemp_L x : core (core x) = core x.
--     Proof. unfold_leibniz. apply cmra_core_idemp. Qed.

theorem core_dup_L {x : α} [CMRA.IsTotal α] : CMRA.core x = CMRA.core x • CMRA.core x := sorry
--     Lemma cmra_core_dup_L x : core x = core x ⋅ core x.
--     Proof. unfold_leibniz. apply cmra_core_dup. Qed.

theorem core_id_total_L {x : α} [CMRA.IsTotal α] : CMRA.CoreId x ↔ CMRA.core x = x := sorry
--     Lemma core_id_total_L x : CoreId x ↔ core x = x.
--     Proof. unfold_leibniz. apply core_id_total. Qed.

theorem core_id_core_L {x : α} [CMRA.IsTotal α] [CMRA.CoreId x] : CMRA.core x = x := sorry
--     Lemma core_id_core_L x `{!CoreId x} : core x = x.
--     Proof. by apply core_id_total_L. Qed.

end leibniz


section ucmra

variable {α : Type _} [UCMRA α] [Leibniz α]

theorem ucmra_unit_left_id_L {x : α} : ε • x = x := sorry

theorem ucmra_unit_right_id_L {x : α} : x • ε = x := sorry

end ucmra



section CmraMorphism

structure isCmraMor {α β : Type _} [CMRA α] [CMRA β] (f : α -> β) : Prop where
  morphism_validN n x : ✓{n} x -> ✓{n} (f x)
  morphism_pcore x : f <$> CMRA.pcore x ≡ CMRA.pcore (f x)
  morphism_op x y : f (x • y) ≡ f x • f y


/-- A morphism between OFEs, written `α -n> β`, is defined to be a function that is non-expansive. -/
@[ext] structure Hom (α β : Type _) [CMRA α] [CMRA β] extends OFE.Hom α β where
  mor : isCmraMor f

@[inherit_doc]
infixr:25 " -C> " => Hom

instance [CMRA α] [CMRA β] : CoeFun (α -C> β) (fun _ => α → β) := ⟨ fun F => F.f ⟩

protected def Hom.id [CMRA α] : α -C> α where
  toHom := OFE.Hom.id
  mor := ⟨ sorry, sorry, sorry ⟩

protected def Hom.comp [CMRA α] [CMRA β] [CMRA γ] (g : β -C> γ) (f : α -C> β) : α -C> γ where
  toHom := OFE.Hom.comp g.toHom f.toHom
  mor := ⟨ sorry, sorry, sorry ⟩

def morphism_proper [CMRA α] [CMRA β] (f : α -C> β) {x₁ x₂ : α} (X : x₁ ≡ x₂) : f x₁ ≡ f x₂ :=
  sorry

def morphism_core [CMRA α] [CMRA β] (f : α -C> β) {x : α} : CMRA.core (f x) ≡ f (CMRA.core x) :=
  sorry

def morphism_mono [CMRA α] [CMRA β] (f : α -C> β) {x₁ x₂ : α} (H : x₁ ≼ x₂) : f x₁ ≼ f x₂ :=
  sorry

def morphism_monoN [CMRA α] [CMRA β] (f : α -C> β) n {x₁ x₂ : α} (H : x₁ ≼{n} x₂) : f x₁ ≼{n} f x₂ :=
  sorry

def morphism_valid [CMRA α] [CMRA β] (f : α -C> β) {x : α} (H : ✓ x) : ✓ f x :=
  sorry


end CmraMorphism

end CMRA

section rFunctor

class RFunctor (F : Type _ → Type _ → Type _) where
  cmra [COFE α] [COFE β] : CMRA (F α β)
  map [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -n> F α₂ β₂
  map_ne [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFE α] [COFE β] : map (@Hom.id α _) (@Hom.id β _) x ≡ x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x ≡ map g g' (map f f' x)
  mor [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] (f : α₂ -n> α₁) (g : β₁ -n> β₂) :
    CMRA.isCmraMor (map f g)

class RFunctorContractive (F : Type _ → Type _ → Type _) extends RFunctor F where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [instance] RFunctor.cmra

instance RFunctor.toOFunctor [RFunctor F] : COFE.OFunctor F where
  cofe {α β} := (@RFunctor.cmra F _ α β).toOFE
  map f g    := RFunctor.map f g
  map_ne     := RFunctor.map_ne
  map_id     := RFunctor.map_id
  map_comp   := RFunctor.map_comp

instance RFunctorContractive.toOFunctorContractive [RFunctorContractive F] : COFE.OFunctorContractive F where
  toOFunctor      := RFunctor.toOFunctor
  map_contractive := RFunctorContractive.map_contractive

end rFunctor

section urFunctor

class URFunctor (F : Type _ → Type _ → Type _) where
  cmra [COFE α] [COFE β] : UCMRA (F α β)
  map [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -n> F α₂ β₂
  map_ne [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFE α] [COFE β] : map (@Hom.id α _) (@Hom.id β _) x ≡ x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x ≡ map g g' (map f f' x)
  mor [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] (f : α₂ -n> α₁) (g : β₁ -n> β₂) :
    CMRA.isCmraMor (map f g)

class URFunctorContractive (F : Type _ → Type _ → Type _) extends URFunctor F where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [instance] URFunctor.cmra

instance URFunctor.toRFunctor [URFunctor F] : RFunctor F where
  cmra {α β} := (@URFunctor.cmra F _ α β).toCMRA
  map f g    := URFunctor.map f g
  map_ne     := URFunctor.map_ne
  map_id     := URFunctor.map_id
  map_comp   := URFunctor.map_comp
  mor        := URFunctor.mor

instance URFunctorContractive.toRFunctorContractive [URFunctorContractive F] : RFunctorContractive F where
  toRFunctor      := URFunctor.toRFunctor
  map_contractive := URFunctorContractive.map_contractive

end urFunctor

end Iris
