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
  pcore_op_mono y : pcore x = some cx → ∃ cy, pcore (op x y) ≡ some (op cx cy)

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
  exclusive0_l y : ¬✓{0} x • y

class Cancelable (x : α) : Prop where
  cancelableN : ✓{n} x • y → x • y ≡{n}≡ x • z → y ≡{n}≡ z

class IdFree (x : α) : Prop where
  id_free0_r y : ✓{0} x → ¬x • y ≡{0}≡ x

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

theorem CoreID_of_eqv {x₁ x₂ : α} (e : x₁ ≡ x₂) (h : CMRA.CoreId x₁) : CMRA.CoreId x₂ where
  core_id := calc
    pcore x₂ ≡ pcore x₁ := NonExpansive.eqv e.symm
    _        ≡ some x₁  := h.core_id
    _        ≡ some x₂  := e

theorem CoreID_iff {x₁ x₂ : α} (e : x₁ ≡ x₂): CMRA.CoreId x₁ ↔ CMRA.CoreId x₂ :=
  ⟨CoreID_of_eqv e, CoreID_of_eqv e.symm⟩

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

theorem op_ne2 {x₁ x₂ y₁ y₂ : α} {n} (H1 : x₁ ≡{n}≡ x₂) (H2 : y₁ ≡{n}≡ y₂) : x₁ • y₁ ≡{n}≡ x₂ • y₂ :=
  (Dist.op_l H1).trans (op_right_dist x₂ H2)

theorem op_proper2 {x₁ x₂ y₁ y₂ : α} (H1 : x₁ ≡ x₂) (H2 : y₁ ≡ y₂) : x₁ • y₁ ≡ x₂ • y₂ :=
  (Equiv.op_l H1).trans (op_right_eqv x₂ H2)

theorem opM_ne2 {x₁ x₂ y₁ y₂ : α} {n} (H1 : x₁ ≡{n}≡ x₂) (H2 : y₁ ≡{n}≡ y₂) : x₁ •? y₁ ≡{n}≡ x₂ •? y₂ := by
  unfold op?
  simp [op_ne2 H1 H2]

theorem opM_proper2 {x₁ x₂ y₁ y₂ : α} (H1 : x₁ ≡ x₂) (H2 : y₁ ≡ y₂) : x₁ •? y₁ ≡ x₂ •? y₂ := by
  unfold op?
  simp [Equiv.op H1 H2]

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

theorem valid_iff {x y : α} (e : x ≡ y) : ✓ x ↔ ✓ y := ⟨valid_of_eqv e, valid_of_eqv e.symm⟩
theorem _root_.Iris.OFE.Equiv.valid : (x : α) ≡ y → (✓ x ↔ ✓ y) := valid_iff

theorem validN_of_le {n n'} {x : α} : n' ≤ n → ✓{n} x → ✓{n'} x :=
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
  n.recOn (Exclusive.exclusive0_l _) fun _ ih => ih ∘ validN_succ

theorem not_valid_exclN_op_right {n} {x : α} [Exclusive x] {y} : ¬✓{n} (y • x) :=
  fun v => not_valid_exclN_op_left (validN_of_eqv comm v)

theorem not_valid_excl_op_left {x : α} [Exclusive x] {y} : ¬✓ (x • y) :=
  fun v => Exclusive.exclusive0_l _ v.validN

theorem not_excl_op_right {x : α} [Exclusive x] {y} : ¬✓ (y • x) :=
  fun v => not_valid_excl_op_left (valid_of_eqv comm v)

theorem none_of_excl_valid_op {n} {x : α} [Exclusive x] {my} : ✓{n} (x •? my) → my = none := by
  cases my <;> simp [CMRA.op?, not_valid_exclN_op_left]

theorem not_valid_of_exclN_inc {n} {x : α} [Exclusive x] {y} : x ≼{n} y → ¬✓{n} y
  | ⟨_, hz⟩, v => not_valid_exclN_op_left (validN_ne hz v)

theorem not_valid_of_excl_inc {x : α} [Exclusive x] {y} : x ≼ y → ¬✓ y
  | ⟨_, hz⟩, v => Exclusive.exclusive0_l _ <| validN_of_eqv hz v.validN

theorem Exclusive_of_eqv {x₁ x₂ : α} (e : x₁ ≡ x₂) (h : CMRA.Exclusive x₁) : CMRA.Exclusive x₂ where
  exclusive0_l y := (h.exclusive0_l y) ∘ (validN_of_eqv (Equiv.op_l e.symm))

theorem Exclusive_iff {x₁ x₂ : α} (e : x₁ ≡ x₂) : CMRA.Exclusive x₁ ↔ CMRA.Exclusive x₂ :=
  ⟨Exclusive_of_eqv e, Exclusive_of_eqv e.symm⟩

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

theorem incN_ne2 (x₁ x₂ y₁ y₂ : α) n (H1 : x₁ ≡{n}≡ x₂) (H2 : y₁ ≡{n}≡ y₂) : x₁ ≼{n} y₁ → x₂ ≼{n} y₂ :=
  fun inc =>
    calc
      x₂ ≡{n}≡ x₁ := H1.symm
      x₁ ≼{n} y₁ := inc
      y₁ ≡{n}≡ y₂ := H2

theorem incN_proper2 (x₁ x₂ y₁ y₂ : α) n (H1 : x₁ ≡ x₂) (H2 : y₁ ≡ y₂) : x₁ ≼{n} y₁ → x₂ ≼{n} y₂ :=
  fun inc =>
    calc
      x₂ ≡{n}≡ x₁ := H1.dist.symm
      x₁ ≼{n} y₁ := inc
      y₁ ≡{n}≡ y₂ := H2.dist

theorem inc_proper2 (x₁ x₂ y₁ y₂ : α) (H1 : x₁ ≡ x₂) (H2 : y₁ ≡ y₂) : x₁ ≼ y₁ → x₂ ≼ y₂ :=
  fun inc =>
    calc
      x₂ ≡ x₁ := H1.symm
      x₁ ≼ y₁ := inc
      y₁ ≡ y₂ := H2

theorem pcore_mono {x y : α} : x ≼ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ cy
  | ⟨_, hw⟩, e =>
    have ⟨z, hz⟩ := pcore_op_mono _ e
    let ⟨t, ht, et⟩ := OFE.equiv_some ((NonExpansive.eqv hw).trans hz)
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

theorem included_dist_l n (x1 x2 x1' : α) : x1 ≼ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ x2' ∧ x2' ≡{n}≡ x2 :=
  fun ⟨y, hy⟩ e =>
    suffices h : x1' • y ≡{n}≡ x2 from ⟨x1' • y, inc_op_left x1' y, h⟩
    calc
      x1' • y ≡{n}≡ x1 • y := Dist.op_l e
      _       ≡{n}≡ x2 := hy.symm.dist

theorem op_core_left_of_inc {x y : α} [CoreId x] (le : x ≼ y) : y • x ≡ y :=
  comm.trans (op_core_right_of_inc le)

theorem CoreId.of_pcore_eq_some {x y : α} (e : pcore x = some y) : CoreId y where
  core_id := pcore_idem e

theorem cmra_pcore_core_id {x y : α} (H : pcore x = some y) : CMRA.CoreId y where
  core_id := pcore_idem H

-- instance : CMRA.CoreId (core y) := cmra_pcore_core_id (pcore_eq_core _)

-- What's the best way to port these?
-- Global Instance cmra_includedN_preorder n : PreOrder (@includedN A _ _ n).
-- Global Instance cmra_included_preorder : PreOrder (@included A _ _).

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

theorem core_idemp (x : α) : core (core x) ≡ core x := by
  unfold core
  have ⟨cx, e⟩ := IsTotal.total x
  have ⟨z, hz, ez⟩ := OFE.equiv_some (pcore_idem e)
  simp [e, hz, ez]

theorem tot_core_ne {x₁ x₂ : α} n (H : x₁ ≡{n}≡ x₂) : core x₁ ≡{n}≡ core x₂ := by
  show some (core x₁) ≡{n}≡ some (core x₂)
  rw [←pcore_eq_core, ←pcore_eq_core]
  exact NonExpansive.ne H

theorem tot_core_proper {x₁ x₂ : α} (H : x₁ ≡ x₂) : core x₁ ≡ core x₂ := by
  show some (core x₁) ≡ some (core x₂)
  rw [←pcore_eq_core, ←pcore_eq_core]
  exact pcore_proper' H

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
  have ⟨_, hz⟩ := Hle
  let ⟨_, t, wt, wx, _⟩ := extend Hv hz
  ⟨t, wt.trans (Equiv.op_l (HD wx.symm).symm)⟩

theorem discrete_inc_r {x y : α} (HD : DiscreteE y) (_ : ✓{0} y) (Hle : x ≼{0} y) : x ≼ y :=
  have ⟨z, hz⟩ := Hle
  ⟨z, HD hz⟩

theorem discrete_op {x y : α} (Hv : ✓{0} x • y) (Hx : DiscreteE x) (Hy : DiscreteE y)
    : DiscreteE (x • y) :=
  fun {z} h =>
    let ⟨w, t, wt, wx, ty⟩ := CMRA.extend ((Dist.validN h).mp Hv) h.symm
    calc
      x • y ≡ w • y := Equiv.op_l (Hx wx.symm)
      _     ≡ w • t := op_right_eqv w (Hy ty.symm)
      _     ≡ z     := wt.symm

end discreteElements

section discreteCMRA

variable {α : Type _} [CMRA α]

theorem discrete_valid_iff [d: CMRA.Discrete α] n {x : α} : ✓ x ↔ ✓{n} x :=
  ⟨Valid.validN, fun v => d.discrete_valid $ validN_of_le (Nat.zero_le n) v⟩

theorem discrete_valid_iff_0 [d: CMRA.Discrete α] n {x : α} : ✓{0} x ↔ ✓{n} x :=
  ⟨Valid.validN ∘ d.discrete_valid, validN_of_le (Nat.zero_le n)⟩

theorem discrete_included_iff [d: Discrete α] n {x y : α} : x ≼ y ↔ x ≼{n} y :=
  ⟨incN_of_inc _, fun ⟨z, hz⟩ => ⟨z, d.discrete_n hz⟩⟩

theorem discrete_included_iff_0 [d: OFE.Discrete α] n {x y : α} : x ≼{0} y ↔ x ≼{n} y :=
  ⟨fun ⟨z, hz⟩ => ⟨z, (d.discrete_n hz).dist⟩, fun a => incN_of_incN_le (Nat.zero_le n) a⟩

end discreteCMRA

section cancelableElements

variable {α : Type _} [CMRA α]

-- Global Instance cancelable_proper : Proper (equiv ==> iff) (@Cancelable A).
-- Proof. unfold Cancelable. intros x x' EQ. by setoid_rewrite EQ. Qed.

theorem cancelable {x y z : α} [CMRA.Cancelable x] (v : ✓(x • y)) (e : x • y ≡ x • z) : y ≡ z :=
  suffices h: ∀n, y ≡{n}≡ z from equiv_dist.mpr h
  fun n => Cancelable.cancelableN (valid_iff_validN.mp v n) (equiv_dist.mp e n)

theorem discrete_cancelable {x : α} [d: CMRA.Discrete α]
    (H : ∀ {y z : α}, ✓(x • y) → x • y ≡ x • z → y ≡ z) : CMRA.Cancelable x where
  cancelableN {n} {_ _} v e := (H ((discrete_valid_iff n).mpr v) (d.discrete_n e)).dist

instance cancelable_op {x y : α} [cx: CMRA.Cancelable x] [cy: CMRA.Cancelable y] : CMRA.Cancelable (x • y) where
  cancelableN {n w t} v e :=
    have v1: ✓{n} x • (y • w) := validN_ne op_assocN.symm v
    have v2 := validN_op_right v1
    have := calc
      x • (y • w) ≡{n}≡ (x • y) • w := op_assocN
      _           ≡{n}≡ (x • y) • t := e
      _           ≡{n}≡ x • (y • t) := op_assocN.symm
    cy.cancelableN v2 (cx.cancelableN v1 this)

instance exclusive_cancelable {x : α} [CMRA.Exclusive x] : CMRA.Cancelable x where
  cancelableN v _ := absurd v not_valid_exclN_op_left

theorem Cancelable_of_eqv {x₁ x₂ : α} (e : x₁ ≡ x₂) (h : CMRA.Cancelable x₁) : CMRA.Cancelable x₂ where
  cancelableN {n w t} v ee :=
    have v_xw : ✓{n} x₁ • w := validN_of_eqv (Equiv.op_l e.symm) v
    have : x₁ • w ≡{n}≡ x₁ • t := calc
      x₁ • w ≡{n}≡ x₂ • w := Dist.op_l e.dist
      _      ≡{n}≡ x₂ • t := ee
      _      ≡{n}≡ x₁ • t := Dist.op_l e.symm.dist
    h.cancelableN v_xw this

theorem Cancelable_iff {x₁ x₂ : α} (e : x₁ ≡ x₂) : CMRA.Cancelable x₁ ↔ CMRA.Cancelable x₂ :=
  ⟨Cancelable_of_eqv e, Cancelable_of_eqv e.symm⟩

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

theorem IdFree_of_eqv {x₁ x₂ : α} (e : x₁ ≡ x₂) (h : CMRA.IdFree x₁) : CMRA.IdFree x₂ where
  id_free0_r z v := fun h₂ =>
    have := calc
      x₁ • z ≡{0}≡ x₂ • z := op_left_dist z e.dist
      _      ≡{0}≡ x₂ := h₂
      _      ≡{0}≡ x₁ := e.dist.symm
    h.id_free0_r _ ((validN_iff e.dist).mpr v) this

theorem IdFree_iff {x₁ x₂ : α} (e : x₁ ≡ x₂) : CMRA.IdFree x₁ ↔ CMRA.IdFree x₂ :=
  ⟨IdFree_of_eqv e, IdFree_of_eqv e.symm⟩

theorem IdFree_ne {x₁ x₂ : α} {n} (e : x₁ ≡{n}≡ x₂) (h : CMRA.IdFree x₁) : CMRA.IdFree x₂ where
  id_free0_r z v := fun h₂ =>
    have ee := Dist.le e (Nat.zero_le _)
    have := calc
      x₁ • z ≡{0}≡ x₂ • z := op_left_dist z ee
      _      ≡{0}≡ x₂ := h₂
      _      ≡{0}≡ x₁ := ee.symm
    h.id_free0_r _ ((validN_iff ee).mpr v) this

theorem id_freeN_r n n' {x : α} [CMRA.IdFree x] {y} : ✓{n}x → ¬ (x • y ≡{n'}≡ x) :=
  fun v =>
    have : ¬x • y ≡{0}≡ x := IdFree.id_free0_r _ $ validN_of_le (Nat.zero_le _) v
    this ∘ (fun e => Dist.le e (Nat.zero_le _))

theorem id_freeN_l n n' {x : α} [CMRA.IdFree x] {y} : ✓{n}x → ¬ (y • x ≡{n'}≡ x) :=
  fun v => (id_freeN_r n n' v) ∘ comm.dist.trans

theorem id_free_r {x : α} [CMRA.IdFree x] {y} : ✓x → ¬ (x • y ≡ x) :=
  fun v h => IdFree.id_free0_r y (valid_iff_validN.mp v 0) (h.dist)

theorem id_free_l {x : α} [CMRA.IdFree x] {y} : ✓x → ¬ (y • x ≡ x) :=
  fun v => (id_free_r v) ∘ comm.trans

theorem discrete_id_free {x : α} [d : CMRA.Discrete α] (H : ∀ y, ✓ x → x • y ≡ x → False)
    : CMRA.IdFree x where
  id_free0_r y v := fun h => H y (d.discrete_valid v) (d.discrete_0 h)

instance id_free_op_r {x y : α} [iy: CMRA.IdFree y] [cx : CMRA.Cancelable x] : CMRA.IdFree (x • y) where
  id_free0_r z v := fun h =>
    have : ¬y • z ≡{0}≡ y := iy.id_free0_r z (validN_op_right v)
    this (cx.cancelableN v (assoc.dist.trans h).symm).symm

instance id_free_op_l {x y : α} [ix: CMRA.IdFree x] [cy: CMRA.Cancelable y] : CMRA.IdFree (x • y) :=
  IdFree_of_eqv comm (id_free_op_r)

instance exclusive_id_Free {x : α} [ex: CMRA.Exclusive x] : CMRA.IdFree x where
  id_free0_r z v := fun h => ex.exclusive0_l z ((validN_iff h.symm).mp v)

end idFreeElements


section ucmra

variable {α : Type _} [u: UCMRA α]

theorem unit_validN n : ✓{n} u.unit := valid_iff_validN.mp (u.unit_valid) n

theorem incN_unit n {x : α} : u.unit ≼{n} x := ⟨x, (u.unit_left_id (x := x)).symm.dist⟩

theorem inc_unit (x : α) : u.unit ≼ x :=  ⟨x, (u.unit_left_id (x := x)).symm⟩

theorem unit_right_id (x : α) : x • u.unit ≡ x := comm.trans (u.unit_left_id (x := x))

instance unit_CoreId : CMRA.CoreId u.unit where
  core_id := u.pcore_unit

instance unit_total : CMRA.IsTotal α where
  total x :=
    have ⟨y, hy, _⟩ := pcore_mono' (inc_unit x) u.pcore_unit
    ⟨y, hy⟩

instance empty_cancelable : CMRA.Cancelable u.unit where
  cancelableN {n w t} _ e := calc
    w ≡{n}≡ UCMRA.unit • w := u.unit_left_id.dist.symm
    _ ≡{n}≡ UCMRA.unit • t := e
    _ ≡{n}≡ t := u.unit_left_id.dist

theorem dst_incN {n} {x y : α} (H : y ≡{n}≡ x) : x ≼{n} y :=
  ⟨ u.unit, H.trans (equiv_dist.mp (unit_right_id x) n).symm ⟩

end ucmra


section leibniz

variable {α : Type _} [CMRA α] [lei: Leibniz α]

theorem assoc_L {x y z : α} : x • (y • z) = (x • y) • z := lei.leibniz.mp assoc

theorem comm_L {x y : α} : (x • y) = (y • x) := lei.leibniz.mp comm

theorem pcore_l_L {x cx : α} : CMRA.pcore x = some cx → cx • x = x :=
  fun h => lei.leibniz.mp (pcore_op_left h)

theorem pcore_idemp_L {x cx : α} : CMRA.pcore x = some cx → CMRA.pcore cx = some cx :=
  fun h => Leibniz.leibniz.mp (pcore_idem h)

theorem op_opM_assoc_L {x y : α} {mz} : (x • y) •? mz = x • (y •? mz) :=
  lei.leibniz.mp (op_opM_assoc _ _ _)

theorem pcore_r_L {x cx : α} : CMRA.pcore x = some cx → x • cx = x :=
  fun h => lei.leibniz.mp (pcore_op_right h)

theorem pcore_dup_L {x cx : α} : CMRA.pcore x = some cx → cx • cx = cx :=
  fun h => lei.leibniz.mp (pcore_op_self h)

theorem core_id_dup_L {x : α} [CMRA.CoreId x] : x = x • x :=
  lei.leibniz.mp (op_self x).symm

theorem core_r_L {x : α} [CMRA.IsTotal α] : x • CMRA.core x = x :=
  lei.leibniz.mp (op_core x)


theorem core_l_L {x : α} [CMRA.IsTotal α] : CMRA.core x • x = x :=
  lei.leibniz.mp (by exact core_op x)

theorem core_idemp_L {x : α} [CMRA.IsTotal α] : CMRA.core (CMRA.core x) = CMRA.core x :=
  lei.leibniz.mp (by exact core_idemp x)

theorem core_dup_L {x : α} [CMRA.IsTotal α] : CMRA.core x = CMRA.core x • CMRA.core x :=
  lei.leibniz.mp (core_op_core).symm

theorem core_id_total_L {x : α} [CMRA.IsTotal α] : CMRA.CoreId x ↔ CMRA.core x = x := calc
  CoreId x ↔ core x ≡ x := coreId_iff_core_eqv_self
  _        ↔ core x = x := Leibniz.leibniz
theorem core_id_core_L {x : α} [CMRA.IsTotal α] [c: CMRA.CoreId x] : CMRA.core x = x :=
  core_id_total_L.mp c

end leibniz


section ucmra

variable {α : Type _} [u: UCMRA α] [lei: Leibniz α]

theorem ucmra_unit_left_id_L {x : α} : u.unit • x = x := lei.leibniz.mp UCMRA.unit_left_id

theorem ucmra_unit_right_id_L {x : α} : x • u.unit = x := lei.leibniz.mp (unit_right_id x)

end ucmra



section CmraMorphism

structure isCmraMor {α β : Type _} [CMRA α] [CMRA β] (f : α -> β) : Prop where
  morphism_validN {n x} : ✓{n} x -> ✓{n} (f x)
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
  mor :=
    ⟨ fun v => v,
      fun x =>
        match pcore x with
        | none => Equiv.rfl
        | some _ => Equiv.rfl,
      fun _ _ => Equiv.rfl ⟩

protected def Hom.comp [CMRA α] [CMRA β] [CMRA γ] (g : β -C> γ) (f : α -C> β) : α -C> γ where
  toHom := OFE.Hom.comp g.toHom f.toHom
  mor :=
    ⟨ fun v => g.mor.morphism_validN (f.mor.morphism_validN v),
      fun x => sorry,
      fun x y => sorry ⟩

def morphism_proper [CMRA α] [CMRA β] (f : α -C> β) {x₁ x₂ : α} (X : x₁ ≡ x₂) : f x₁ ≡ f x₂ :=
  f.ne.eqv X

def morphism_core [CMRA α] [CMRA β] (f : α -C> β) {x : α} : CMRA.core (f x) ≡ f (CMRA.core x) :=
  suffices h: Option.map f.f (pcore x) ≡ pcore (f.f x) →
    (pcore (f.f x)).getD (f.f x) ≡ f.f ((pcore x).getD x)
  from h (f.mor.morphism_pcore x)
  match pcore x with
  | none => fun h => by simp [OFE.equiv_none h.symm]
  | some cx => fun h => by
    let ⟨s, hs, es⟩ := OFE.equiv_some h.symm
    rw [hs]
    exact es

def morphism_mono [CMRA α] [CMRA β] (f : α -C> β) {x₁ x₂ : α} (H : x₁ ≼ x₂) : f x₁ ≼ f x₂ :=
  have ⟨z, hz⟩ := H
  ⟨f.f z, (morphism_proper f hz).trans (f.mor.morphism_op _ _)⟩

def morphism_monoN [CMRA α] [CMRA β] (f : α -C> β) n {x₁ x₂ : α} (H : x₁ ≼{n} x₂) : f x₁ ≼{n} f x₂ :=
  have ⟨z, hz⟩ := H
  ⟨f.f z, (f.ne.ne hz).trans (f.mor.morphism_op _ _).dist⟩

def morphism_valid [CMRA α] [CMRA β] (f : α -C> β) {x : α} (H : ✓ x) : ✓ f x :=
  valid_iff_validN.mpr (fun _ => f.mor.morphism_validN H.validN)


end CmraMorphism

end CMRA


section rFunctor

class RFunctor (F : COFE.OFunctorPre) where
  -- EXPERIMENT: Replacing COFE in this definition with OFE
  -- https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/OFunctor.20definition
  -- cofe [COFE α] [COFE β] : CMRA (F α β)
  cmra [OFE α] [OFE β] : CMRA (F α β)
  map [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -n> F α₂ β₂
  map_ne [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [OFE α] [OFE β] (x : F α β) : map (@Hom.id α _) (@Hom.id β _) x ≡ x
  map_comp [OFE α₁] [OFE α₂] [OFE α₃] [OFE β₁] [OFE β₂] [OFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x ≡ map g g' (map f f' x)
  mor [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] (f : α₂ -n> α₁) (g : β₁ -n> β₂) :
    CMRA.isCmraMor (map f g)

class RFunctorContractive (F : COFE.OFunctorPre) extends (RFunctor F) where
  map_contractive [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

def RFunctor.ap [RFunctor F] [OFE T] := F T T

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

class URFunctor (F : COFE.OFunctorPre) where
  -- EXPERIMENT: Replacing COFE in this definition with OFE
  -- https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/OFunctor.20definition
  -- cofe [COFE α] [COFE β] : UCMRA (F α β)
  cmra [OFE α] [OFE β] : UCMRA (F α β)
  map [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -n> F α₂ β₂
  map_ne [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [OFE α] [OFE β] (x : F α β) : map (@Hom.id α _) (@Hom.id β _) x ≡ x
  map_comp [OFE α₁] [OFE α₂] [OFE α₃] [OFE β₁] [OFE β₂] [OFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x ≡ map g g' (map f f' x)
  mor [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] (f : α₂ -n> α₁) (g : β₁ -n> β₂) :
    CMRA.isCmraMor (map f g)

class URFunctorContractive (F : COFE.OFunctorPre) extends URFunctor F where
  map_contractive [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
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

/- A dependent function has its range contained in CMRA types -/
class IsUCMRAFun (F : α → Type _) where
  cmra {x : α} : UCMRA (F x)

instance {α β : Type _} [U : UCMRA β] : IsUCMRAFun (fun (_ : α) => β) := ⟨ U ⟩

attribute [instance] IsUCMRAFun.cmra

-- Instance diamond?
instance [IsUCMRAFun F] : IsOFEFun F where
  ofe {x} := (@IsUCMRAFun.cmra _ F _ x).toOFE

section DiscreteFunUCMRA

variable {α : Type _} (β : α → Type _) [IsUCMRAFun β]

instance discrete_fun.CMRA : UCMRA (discrete_fun β) where
  toOFE := discrete_fun.OFE β
  pcore f := some ⟨ fun x => CMRA.core (f x) ⟩
  op f g := ⟨ fun x => f x • g x ⟩
  ValidN n f := ∀ x, ✓{n} (f x)
  Valid f := ∀ x, ✓(f x)
  op_ne := sorry
  pcore_ne := sorry
  validN_ne := sorry
  valid_iff_validN := sorry
  validN_succ := sorry
  validN_op_left := sorry
  assoc := sorry
  comm := sorry
  pcore_op_left := sorry
  pcore_idem := sorry
  pcore_op_mono := sorry
  extend := sorry
  unit := ⟨ fun _ => UCMRA.unit ⟩
  unit_valid := sorry
  unit_left_id := sorry
  pcore_unit := sorry

end DiscreteFunUCMRA


section DiscreteFunURF

-- discrete_fun_OF is the action on objects


-- Ensures there are no instance clashes in the UF definifion
instance {C} (F : C → COFE.OFunctorPre) [HUF : ∀ c, URFunctor (F c)] :
        ∀ A B [OFE A] [OFE B], IsUCMRAFun fun c => F c A B :=
    fun A B _ _ => by
        apply IsUCMRAFun.mk
        intro c
        apply (HUF c).cmra

instance IsOFEFun_UF {C} (F : C → COFE.OFunctorPre) [HURF : ∀ c, URFunctor (F c)] :
     URFunctor (discrete_fun_OF F) where
  cmra {α β _ _ } := discrete_fun.CMRA fun c => F c α β
  map := sorry
  map_ne := sorry
  map_id := sorry
  map_comp := sorry
  mor := sorry

instance IsOFEFun_UFC {C} (F : C → COFE.OFunctorPre) [HURF : ∀ c, URFunctorContractive (F c)] :
     URFunctorContractive (discrete_fun_OF F) where
  map_contractive := sorry

end DiscreteFunURF

section option

variable [CMRA A]

instance : CMRA (OptionO A) where
  pcore f := sorry
  op f g := sorry
  ValidN n f := sorry
  Valid f := sorry
  op_ne := sorry
  pcore_ne := sorry
  validN_ne := sorry
  valid_iff_validN := sorry
  validN_succ := sorry
  validN_op_left := sorry
  assoc := sorry
  comm := sorry
  pcore_op_left := sorry
  pcore_idem := sorry
  pcore_op_mono := sorry
  extend := sorry

instance OptionO_UCMRA [CMRA A] : UCMRA (OptionO A) where
  unit := sorry
  unit_valid := sorry
  unit_left_id := sorry
  pcore_unit := sorry

end option

section optionOF

variable (F : COFE.OFunctorPre)

-- We always get a unital cmra
instance OptionOFisUCMRA [OFE α] [OFE β] [RFunctor F] : UCMRA (OptionOF F α β) := by
  unfold OptionOF
  infer_instance

instance OptionOF_URF [RFunctor F] : URFunctor (OptionOF F) where
  cmra := (OptionOFisUCMRA _)
  map := sorry
  map_ne := sorry
  map_id := sorry
  map_comp := sorry
  mor := sorry

-- instance [RFunctor F] : RFunctor (OptionOF F) :=
--   URFunctor.toRFunctor

instance OptionOF_URFC [RFunctorContractive F] : URFunctorContractive (OptionOF F) where
  map_contractive := sorry

end optionOF

section gen_map

/-
The OFE over gmaps is eqivalent to a non-depdenent discrete function to an `Option` type with a `Leibniz` OFE.
In this setting, the CMRA is always unital, and as a consquence the oFunctors do not require
unitality in order to act as a `URFunctor(Contractive)`.
-/

variable (α β : Type _) [UCMRA β] [Leibniz β]

abbrev gen_map := (α -d> (OptionO β))

-- #synth CMRA (OptionO β)
-- #synth CMRA (α -d> (OptionO β))
-- #synth UCMRA (α -d> (OptionO β))
-- The synthesized UMRA here has unit (fun x => ε) = (fun x => none).
-- For us, this is equivalent to the Rocq-iris unit ∅.

def gen_mapOF (C : Type _) (F : COFE.OFunctorPre) :=
  discrete_fun_OF (fun (_ : C) => OptionOF F)

instance gen_map_UF {C} (F : COFE.OFunctorPre) [HRF : RFunctor F] :
    URFunctor (gen_mapOF C F) where
  cmra := sorry
  map := sorry
  map_ne := sorry
  map_id := sorry
  map_comp := sorry
  mor := sorry

instance gen_map_RF {C} (F : COFE.OFunctorPre) [HRF : RFunctorContractive F] :
     URFunctorContractive (gen_mapOF C F) where
  map_contractive := sorry

end gen_map
