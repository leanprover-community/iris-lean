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
  pcore_op_mono : pcore x = some cx → ∀ y, ∃ cy, pcore (op x y) ≡ some (op cx cy)

  extend : ValidN n x → x ≡{n}≡ op y₁ y₂ →
    Σ' z₁ z₂, x ≡ op z₁ z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂

/-- Reduction of `pcore_op_mono` to regular monotonicity -/
theorem pcore_op_mono_of_core_op_mono [OFE α] (op : α → α → α) (pcore : α → Option α)
    (h : (∀ x cx y : α, (∃ z, y ≡ op x z) → pcore x = some cx →
      ∃ cy, pcore y = some cy ∧ ∃ z, cy ≡ op cx z))
    (x cx) (e : pcore x = some cx) (y) : ∃ cy, pcore (op x y) ≡ some (op cx cy) :=
  have ⟨_, hcy, z, hz⟩ := h x cx (op x y) ⟨y, Equiv.rfl⟩ e
  ⟨z, hcy.symm ▸ hz⟩

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

class CoreId (x : α) where
  core_id : pcore x ≡ some x
export CoreId (core_id)

class Exclusive (x : α) where
  exclusive0_l y : ¬✓{0} x • y
export Exclusive (exclusive0_l)

class Cancelable (x : α) where
  cancelableN : ✓{n} x • y → x • y ≡{n}≡ x • z → y ≡{n}≡ z
export Cancelable (cancelableN)

class IdFree (x : α) where
  id_free0_r y : ✓{0} x → ¬x • y ≡{0}≡ x
export IdFree (id_free0_r)

class IsTotal (α : Type _) [CMRA α] where
  total (x : α) : ∃ cx, pcore x = some cx
export IsTotal (total)

def core (x : α) := (pcore x).getD x

class Discrete (α : Type _) [CMRA α] extends OFE.Discrete α where
  discrete_valid {x : α} : ✓{0} x → ✓ x
export Discrete (discrete_valid)

end CMRA

class UCMRA (α : Type _) extends CMRA α where
  unit : α
  unit_valid : ✓ unit
  unit_left_id : unit • x ≡ x
  pcore_unit : pcore unit ≡ some unit

namespace CMRA
variable [CMRA α]

export UCMRA (unit unit_valid unit_left_id pcore_unit)

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
    | .none, .none => rw [ex, ey]

theorem coreId_of_eqv {x₁ x₂ : α} (e : x₁ ≡ x₂) (h : CoreId x₁) : CoreId x₂ where
  core_id := calc
    pcore x₂ ≡ pcore x₁ := NonExpansive.eqv e.symm
    _        ≡ some x₁  := h.core_id
    _        ≡ some x₂  := e

theorem coreId_iff {x₁ x₂ : α} (e : x₁ ≡ x₂) : CoreId x₁ ↔ CoreId x₂ :=
  ⟨coreId_of_eqv e, coreId_of_eqv e.symm⟩

/-! ## Op -/

theorem op_right_eqv (x : α) {y z : α} (e : y ≡ z) : x • y ≡ x • z := op_ne.eqv e
theorem _root_.Iris.OFE.Equiv.op_r {x y z : α} : y ≡ z → x • y ≡ x • z := op_right_eqv _

theorem op_right_dist (x : α) {y z : α} (e : y ≡{n}≡ z) : x • y ≡{n}≡ x • z :=
  op_ne.ne e
theorem _root_.Iris.OFE.Dist.op_r {x y z : α} : y ≡{n}≡ z → x • y ≡{n}≡ x • z := op_right_dist _

theorem op_commN {x y : α} : x • y ≡{n}≡ y • x := equiv_dist.mp comm n

theorem op_assocN {x y z : α} : x • (y • z) ≡{n}≡ (x • y) • z := equiv_dist.mp assoc n

theorem op_left_eqv {x y : α} (z : α) (e : x ≡ y) : x • z ≡ y • z :=
  comm.trans <| e.op_r.trans comm
theorem _root_.Iris.OFE.Equiv.op_l {x y z : α} : x ≡ y → x • z ≡ y • z := op_left_eqv _

theorem op_left_dist {x y : α} (z : α) (e : x ≡{n}≡ y) : x • z ≡{n}≡ y • z :=
  op_commN.trans <| e.op_r.trans op_commN
theorem _root_.Iris.OFE.Dist.op_l {x y z : α} : x ≡{n}≡ y → x • z ≡{n}≡ y • z := op_left_dist _

theorem _root_.Iris.OFE.Dist.op {x x' y y' : α}
    (ex : x ≡{n}≡ x') (ey : y ≡{n}≡ y') : x • y ≡{n}≡ x' • y' := ex.op_l.trans ey.op_r

theorem op_eqv {x x' y y' : α} (ex : x ≡ x') (ey : y ≡ y') : x • y ≡ x' • y' :=
  ex.op_l.trans ey.op_r
theorem _root_.Iris.OFE.Equiv.op : (x : α) ≡ x' → y ≡ y' → x • y ≡ x' • y' := op_eqv

theorem op_proper2 {x₁ x₂ y₁ y₂ : α} (H1 : x₁ ≡ x₂) (H2 : y₁ ≡ y₂) : x₁ • y₁ ≡ x₂ • y₂ :=
  (Equiv.op_l H1).trans (op_right_eqv x₂ H2)

theorem _root_.Iris.OFE.Dist.opM {x₁ x₂ : α} {y₁ y₂ : Option α}
    (H1 : x₁ ≡{n}≡ x₂) (H2 : y₁ ≡{n}≡ y₂) : x₁ •? y₁ ≡{n}≡ x₂ •? y₂ :=
  match y₁, y₂, H2 with
  | none, none, _ => H1
  | some _, some _, H2 => H1.op H2

theorem _root_.Iris.OFE.Equiv.opM {x₁ x₂ : α} {y₁ y₂ : Option α}
    (H1 : x₁ ≡ x₂) (H2 : y₁ ≡ y₂) : x₁ •? y₁ ≡ x₂ •? y₂ :=
  equiv_dist.2 fun _ => H1.dist.opM H2.dist

theorem opM_left_eqv {x y : α} (z : Option α) (e : x ≡ y) : x •? z ≡ y •? z := e.opM Equiv.rfl
theorem opM_right_eqv (x : α) {y z : Option α} (e : y ≡ z) : x •? y ≡ x •? z := Equiv.rfl.opM e

theorem opM_left_dist {n} {x y : α} (z : Option α) (e : x ≡{n}≡ y) : x •? z ≡{n}≡ y •? z :=
  e.opM Dist.rfl
theorem opM_right_dist {n} (x : α) {y z : Option α} (e : y ≡{n}≡ z) : x •? y ≡{n}≡ x •? z :=
  Dist.rfl.opM e

theorem op_opM_assoc (x y : α) (mz : Option α) : (x • y) •? mz ≡ x • (y •? mz) := by
  unfold op?; cases mz <;> simp [assoc, Equiv.symm]

theorem op_opM_assoc_dist (x y : α) (mz : Option α) : (x • y) •? mz ≡{n}≡ x • (y •? mz) := by
  unfold op?; cases mz <;> simp [assoc.dist, Dist.symm]

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

theorem valid_iff {x y : α} (e : x ≡ y) : ✓ x ↔ ✓ y := ⟨valid_of_eqv e, valid_of_eqv e.symm⟩
theorem _root_.Iris.OFE.Equiv.valid : (x : α) ≡ y → (✓ x ↔ ✓ y) := valid_iff

theorem validN_of_le {n n'} {x : α} : n' ≤ n → ✓{n} x → ✓{n'} x :=
  fun le => le.recOn id fun  _ ih vs => ih (validN_succ vs)

theorem valid0_of_validN {n} {x : α} : ✓{n} x → ✓{0} x := validN_of_le (Nat.zero_le n)

theorem validN_op_right {n} {x y : α} : ✓{n} (x • y) → ✓{n} y :=
  fun v => validN_op_left (validN_of_eqv comm v)

theorem valid_op_right (x y : α) : ✓ (x • y) → ✓ y :=
  valid_mapN fun _ => validN_op_right

theorem valid_op_left {x y : α} : ✓ (x • y) → ✓ x :=
  fun v => valid_op_right y x (valid_of_eqv comm v)

theorem validN_opM {x : α} {my : Option α} : ✓{n} (x •? my) → ✓{n} x :=
  match my with
  | none => id  | some _ => validN_op_left

theorem valid_opM {x : α} {my : Option α} : ✓ (x •? my) → ✓ x :=
  match my with
  | none => id  | some _ => valid_op_left

theorem validN_op_opM_left {mz : Option α} : ✓{n} (x • y : α) •? mz → ✓{n} x •? mz :=
  match mz with
  | .none => validN_op_left
  | .some z => fun h =>
    have := calc
      (x • y) • z ≡{n}≡ x • (y • z) := op_assocN.symm
      _           ≡{n}≡ x • (z • y) := op_right_dist x op_commN
      _           ≡{n}≡ (x • z) • y := op_assocN
    validN_op_left ((Dist.validN this).mp h)

theorem validN_op_opM_right {mz : Option α} (h : ✓{n} (x • y : α) •? mz) : ✓{n} y •? mz :=
  validN_op_opM_left (validN_ne (opM_left_dist mz op_commN) h)

/-! ## Core -/

theorem pcore_proper {x y : α} (cx : α) (e : x ≡ y) (ps : pcore x = some cx)
    : ∃ cy, pcore y = some cy ∧ cx ≡ cy := by
  let ⟨cy, hcy, ecy⟩ := pcore_ne (equiv_dist.mp e 0) ps
  refine ⟨cy, hcy, ?_⟩
  have (n : Nat) : cx ≡{n}≡ cy :=
    let ⟨cy', hcy', ecy'⟩ := pcore_ne (equiv_dist.mp e n) ps
    have : cy' = cy := Option.some_inj.mp (hcy' ▸ hcy)
    this ▸ ecy'
  exact equiv_dist.mpr this

theorem pcore_proper' {x y : α} (e : x ≡ y) : pcore x ≡ pcore y :=
  NonExpansive.eqv e

theorem pcore_op_left' {x : α} {cx} (e : pcore x ≡ some cx) : cx • x ≡ x :=
  let ⟨z, pz, ez⟩ := equiv_some e
  calc
    cx • x ≡ z • x := op_left_eqv _ ez.symm
    _      ≡ x     := pcore_op_left pz

theorem pcore_op_right {x : α} {cx} (e : pcore x = some cx) : x • cx ≡ x :=
  calc
    x • cx ≡ cx • x := comm
    _      ≡ x      := pcore_op_left e

theorem pcore_op_right' {x : α} {cx} (e : pcore x ≡ some cx) : x • cx ≡ x :=
  let ⟨_, pz, ez⟩ := equiv_some e
  (op_right_eqv x ez).symm.trans (pcore_op_right pz)

theorem pcore_idem' {x : α} {cx} (e : pcore x ≡ some cx) : pcore cx ≡ some cx :=
  let ⟨y, py, (ey : y ≡ cx)⟩ := equiv_some e
  calc
    pcore cx ≡ pcore y := pcore_proper' ey.symm
    _        ≡ some y  := pcore_idem py
    _        ≡ some cx := ey

theorem pcore_op_self {x : α} {cx} (e : pcore x = some cx) : cx • cx ≡ cx :=
  pcore_op_right' (pcore_idem e)

theorem pcore_op_self' {x : α} {cx} (e : pcore x ≡ some cx) : cx • cx ≡ cx :=
  let ⟨z, pz, ez⟩ := equiv_some e
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
  cases my <;> simp [op?, not_valid_exclN_op_left]

theorem not_valid_of_exclN_inc {n} {x : α} [Exclusive x] {y} : x ≼{n} y → ¬✓{n} y
  | ⟨_, hz⟩, v => not_valid_exclN_op_left (validN_ne hz v)

theorem not_valid_of_excl_inc {x : α} [Exclusive x] {y} : x ≼ y → ¬✓ y
  | ⟨_, hz⟩, v => Exclusive.exclusive0_l _ <| validN_of_eqv hz v.validN

theorem Exclusive.of_eqv {x₁ x₂ : α} (e : x₁ ≡ x₂) (h : Exclusive x₁) : Exclusive x₂ where
  exclusive0_l y := h.exclusive0_l y ∘ e.op_l.dist.validN.2

theorem exclusive_iff {x₁ x₂ : α} (e : x₁ ≡ x₂) : Exclusive x₁ ↔ Exclusive x₂ :=
  ⟨.of_eqv e, .of_eqv e.symm⟩
theorem _root_.Iris.OFE.Dist.exclusive {x₁ x₂ : α} : x₁ ≡ x₂ → (Exclusive x₁ ↔ Exclusive x₂) :=
  exclusive_iff

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
theorem IncludedN.validN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x := validN_of_incN

theorem validN_of_inc {n} {x y : α} : x ≼ y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne (equiv_dist.mp hz n) v)
theorem Included.validN {n} {x y : α} : x ≼ y → ✓{n} y → ✓{n} x := validN_of_inc

theorem incN_of_incN_le {n n'} {x y : α} (l1 : n' ≤ n) : x ≼{n} y → x ≼{n'} y
  | ⟨z, hz⟩ => ⟨z, Dist.le hz l1⟩
theorem inc0_of_incN {n} {x y : α} : x ≼{n} y → x ≼{0} y := incN_of_incN_le (Nat.zero_le n)
theorem IncludedN.le {n n'} {x y : α} : n' ≤ n → x ≼{n} y → x ≼{n'} y := incN_of_incN_le

theorem incN_of_incN_succ {n} {x y : α} : x ≼{n.succ} y → x ≼{n} y :=
  incN_of_incN_le (Nat.le_succ n)
theorem IncludedN.succ {n} {x y : α} : x ≼{n.succ} y → x ≼{n} y := incN_of_incN_succ

theorem incN_op_left (n) (x y : α) : x ≼{n} x • y := ⟨y, Dist.rfl⟩

theorem inc_op_left (x y : α) : x ≼ x • y := ⟨y, Equiv.rfl⟩

theorem inc_op_right (x y : α) : y ≼ x • y := ⟨x, comm⟩

theorem incN_op_right (n) (x y : α) : y ≼{n} x • y :=
  (inc_op_right x y).elim fun z hz => ⟨z, Equiv.dist hz⟩

theorem pcore_mono {x y : α} : x ≼ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ cy
  | ⟨_, hw⟩, e =>
    have ⟨z, hz⟩ := pcore_op_mono e _
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
    let ⟨w, hw, ew⟩ := OFE.dist_some e
    let ⟨t, ht, (et : w ≼ t)⟩ := pcore_mono (inc_op_left x z) hw
    have : pcore y ≡{n}≡ some t :=
      have : pcore y ≡{n}≡ pcore (x • z) := NonExpansive.ne hz
      ht ▸ this
    let ⟨r, hr, er⟩ := OFE.dist_some this
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

theorem included_dist_l {n} {x1 x2 x1' : α} :
    x1 ≼ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ x2' ∧ x2' ≡{n}≡ x2
  | ⟨y, hy⟩, e => ⟨x1' • y, inc_op_left x1' y, e.op_l.trans hy.symm.dist⟩

theorem op_core_left_of_inc {x y : α} [CoreId x] (le : x ≼ y) : y • x ≡ y :=
  comm.trans (op_core_right_of_inc le)

theorem CoreId.of_pcore_eq_some {x y : α} (e : pcore x = some y) : CoreId y where
  core_id := pcore_idem e

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

theorem op_core_dist (x : α) : x • core x ≡{n}≡ x := (op_core x).dist
theorem core_op_dist (x : α) : core x • x ≡{n}≡ x := (core_op x).dist

theorem core_op_core {x : α} : core x • core x ≡ core x :=
  pcore_op_self (pcore_eq_core x)
theorem validN_core {n} {x : α} (v : ✓{n} x) : ✓{n} core x := pcore_validN (pcore_eq_core x) v
theorem valid_core {x : α} (v : ✓ x) : ✓ core x := pcore_valid (pcore_eq_core x) v

instance (y : α) : CoreId (core y) := CoreId.of_pcore_eq_some (pcore_eq_core _)

theorem core_ne : NonExpansive (core : α → α) where
  ne n x₁ x₂ H := by
    show some (core x₁) ≡{n}≡ some (core x₂)
    rw [← pcore_eq_core, ← pcore_eq_core]
    exact NonExpansive.ne H

theorem _root_.Iris.OFE.Dist.core :
  ∀ {n} {x₁ x₂ : α}, x₁ ≡{n}≡ x₂ → core x₁ ≡{n}≡ core x₂ := @core_ne.ne
theorem _root_.Iris.OFE.Equiv.core : ∀ {x₁ x₂ : α}, x₁ ≡ x₂ → core x₁ ≡ core x₂ := @core_ne.eqv

theorem core_eqv_self (x : α) [CoreId x] : core (x : α) ≡ x :=
  show some (core x) ≡ some x from pcore_eq_core x ▸ CoreId.core_id

theorem coreId_iff_core_eqv_self : CoreId (x : α) ↔ core x ≡ x :=
  ⟨fun _ => core_eqv_self x, fun e => { core_id := pcore_eq_core x ▸ e }⟩

theorem core_idem (x : α) : core (core x) ≡ core x := core_eqv_self _

theorem inc_refl (x : α) : x ≼ x := ⟨core x, (op_core _).symm⟩
@[refl] theorem Included.rfl {x : α} : x ≼ x := inc_refl x

theorem incN_refl (x : α) : x ≼{n} x := (inc_refl _).incN
@[refl] theorem IncludedN.rfl {x : α} : x ≼{n} x := incN_refl x

theorem core_inc_self {x : α} [CoreId x] : core x ≼ x :=
  ⟨x, ((core_eqv_self x).op_l.trans (op_self _)).symm⟩

theorem core_incN_core {n} {x y : α} (inc : x ≼{n} y) : core x ≼{n} core y := by
  let ⟨cy, hcy, icy⟩ := pcore_monoN' inc (Dist.of_eq (pcore_eq_core x))
  cases (pcore_eq_core _).symm.trans hcy
  exact icy

theorem core_op_mono (x y : α) : core x ≼ core (x • y) := by
  have ⟨cy, hcy⟩ := pcore_op_mono (pcore_eq_core x) y
  simp [pcore_eq_core] at hcy
  exact ⟨_, hcy⟩

theorem core_mono {x y : α} (Hinc : x ≼ y) : core x ≼ core y := by
  have ⟨z, hz⟩ := Hinc
  exact hz.core.inc_r.2 (core_op_mono x z)

end total


section discreteElements

variable {α : Type _} [CMRA α]

theorem discrete_inc_l {x y : α} [HD : DiscreteE x] (Hv : ✓{0} y) (Hle : x ≼{0} y) : x ≼ y :=
  have ⟨_, hz⟩ := Hle
  let ⟨_, t, wt, wx, _⟩ := extend Hv hz
  ⟨t, wt.trans (Equiv.op_l (HD.discrete wx.symm).symm)⟩

theorem discrete_inc_r {x y : α} [HD : DiscreteE y] : x ≼{0} y → x ≼ y
  | ⟨z, hz⟩ => ⟨z, HD.discrete hz⟩

instance discrete_op {x y : α} (Hv : ✓{0} x • y) [Hx : DiscreteE x] [Hy : DiscreteE y] :
    DiscreteE (x • y) where
  discrete h :=
    let ⟨_w, _t, wt, wx, ty⟩ := extend ((Dist.validN h).mp Hv) h.symm
    ((Hx.discrete wx.symm).op (Hy.discrete ty.symm)).trans wt.symm

end discreteElements

section discreteCMRA

variable {α : Type _} [CMRA α]

theorem valid_iff_validN' [Discrete α] (n) {x : α} : ✓ x ↔ ✓{n} x :=
  ⟨Valid.validN, fun v => discrete_valid <| validN_of_le (Nat.zero_le n) v⟩

theorem valid_0_iff_validN [Discrete α] (n) {x : α} : ✓{0} x ↔ ✓{n} x :=
  ⟨Valid.validN ∘ discrete_valid, validN_of_le (Nat.zero_le n)⟩

theorem inc_iff_incN [OFE.Discrete α] (n) {x y : α} : x ≼ y ↔ x ≼{n} y :=
  ⟨incN_of_inc _, fun ⟨z, hz⟩ => ⟨z, discrete hz⟩⟩

theorem inc_0_iff_incN [OFE.Discrete α] (n) {x y : α} : x ≼{0} y ↔ x ≼{n} y :=
  ⟨fun ⟨z, hz⟩ => ⟨z, (discrete hz).dist⟩,
   fun a => incN_of_incN_le (Nat.zero_le n) a⟩

end discreteCMRA

section cancelableElements

variable {α : Type _} [CMRA α]

theorem cancelable {x y z : α} [Cancelable x] (v : ✓(x • y)) (e : x • y ≡ x • z) : y ≡ z :=
  equiv_dist.mpr fun _ => cancelableN v.validN e.dist

theorem discrete_cancelable {x : α} [Discrete α]
    (H : ∀ {y z : α}, ✓(x • y) → x • y ≡ x • z → y ≡ z) : Cancelable x where
  cancelableN {n} {_ _} v e := (H ((valid_iff_validN' n).mpr v) (Discrete.discrete e)).dist

instance cancelable_op {x y : α} [Cancelable x] [Cancelable y] : Cancelable (x • y) where
  cancelableN {n w _} v e :=
    have v1 : ✓{n} x • (y • w) := validN_ne op_assocN.symm v
    have v2 := validN_op_right v1
    cancelableN v2 <| cancelableN v1 <| op_assocN.trans <| e.trans op_assocN.symm

instance exclusive_cancelable {x : α} [Exclusive x] : Cancelable x where
  cancelableN v _ := absurd v not_valid_exclN_op_left

theorem Cancelable.of_eqv {x₁ x₂ : α} (e : x₁ ≡ x₂) (h : Cancelable x₁) : Cancelable x₂ where
  cancelableN {n w _} v ee :=
    have v_xw : ✓{n} x₁ • w := e.symm.op_l.dist.validN.1 v
    h.cancelableN v_xw <| e.dist.op_l.trans <| ee.trans e.symm.dist.op_l

theorem cancelable_iff {x₁ x₂ : α} (e : x₁ ≡ x₂) : Cancelable x₁ ↔ Cancelable x₂ :=
  ⟨.of_eqv e, .of_eqv e.symm⟩
theorem _root_.Iris.OFE.Equiv.cancelable {x₁ x₂ : α} : x₁ ≡ x₂ → (Cancelable x₁ ↔ Cancelable x₂) :=
  cancelable_iff

theorem op_opM_cancel_dist {x y z : α} [Cancelable x]
    (vxy : ✓{n} x • y) (h : x • y ≡{n}≡ (x • z) •? mw) : y ≡{n}≡ z •? mw :=
  match mw with
  | none => cancelableN vxy h
  | some _ => cancelableN vxy (h.trans (op_assocN.symm))

end cancelableElements

section idFreeElements

variable {α : Type _} [CMRA α]

-- Global Instance id_free_ne n : Proper (dist n ==> iff) (@IdFree A).
-- Proof.
--   intros x x' EQ%(dist_le _ 0); last lia. rewrite /IdFree.
--   split=> y ?; (rewrite -EQ || rewrite EQ); eauto.
-- Qed.

-- Global Instance id_free_proper : Proper (equiv ==> iff) (@IdFree A).
-- Proof. by move=> P Q /equiv_dist /(_ 0)=> →. Qed.

theorem IdFree.of_dist {x₁ x₂ : α} {n} (e : x₁ ≡{n}≡ x₂) (h : IdFree x₁) : IdFree x₂ where
  id_free0_r z v := fun h₂ =>
    have ee := Dist.le e (Nat.zero_le _)
    have := calc
      x₁ • z ≡{0}≡ x₂ • z := op_left_dist z ee
      _      ≡{0}≡ x₂ := h₂
      _      ≡{0}≡ x₁ := ee.symm
    h.id_free0_r _ ((validN_iff ee).mpr v) this

theorem _root_.Iris.OFE.Dist.idFree {x₁ x₂ : α} (e : x₁ ≡{n}≡ x₂) : IdFree x₁ ↔ IdFree x₂ :=
  ⟨.of_dist e, .of_dist e.symm⟩

theorem IdFree.of_eqv {x₁ x₂ : α} (e : x₁ ≡ x₂) (h : IdFree x₁) : IdFree x₂ :=
  h.of_dist e.dist (n := 0)

theorem idFree_iff {x₁ x₂ : α} (e : x₁ ≡ x₂) : IdFree x₁ ↔ IdFree x₂ :=
  e.dist.idFree (n := 0)
theorem _root_.Iris.OFE.Equiv.idFree {x₁ x₂ : α} : x₁ ≡ x₂ → (IdFree x₁ ↔ IdFree x₂) :=
  idFree_iff

theorem id_freeN_r {n n'} {x : α} [IdFree x] {y} (v : ✓{n} x) : ¬(x • y ≡{n'}≡ x) :=
  id_free0_r _ (validN_of_le (Nat.zero_le _) v) |>.imp (·.le (Nat.zero_le _))

theorem id_freeN_l {n n'} {x : α} [IdFree x] {y} (v : ✓{n} x) : ¬(y • x ≡{n'}≡ x) :=
  id_freeN_r v ∘ comm.dist.trans

theorem id_free_r {x : α} [IdFree x] {y} (v : ✓x) : ¬(x • y ≡ x) :=
  fun h => id_free0_r y (valid_iff_validN.mp v 0) h.dist

theorem id_free_l {x : α} [IdFree x] {y} (v : ✓ x) : ¬(y • x ≡ x) :=
  id_free_r v ∘ comm.trans

theorem discrete_id_free {x : α} [Discrete α] (H : ∀ y, ✓ x → ¬(x • y ≡ x)) : IdFree x where
  id_free0_r y v h := H y (Discrete.discrete_valid v) (Discrete.discrete_0 h)

instance idFree_op_r {x y : α} [IdFree y] [Cancelable x] : IdFree (x • y) where
  id_free0_r z v h :=
    id_free0_r z (validN_op_right v) (cancelableN v (assoc.dist.trans h).symm).symm

instance idFree_op_l {x y : α} [IdFree x] [Cancelable y] : IdFree (x • y) :=
  comm.idFree.1 inferInstance

instance exclusive_idFree {x : α} [Exclusive x] : IdFree x where
  id_free0_r z v h := exclusive0_l z ((validN_iff h.symm).mp v)

end idFreeElements


section ucmra

variable {α : Type _} [UCMRA α]

theorem unit_validN {n} : ✓{n} (unit : α) := valid_iff_validN.mp (unit_valid) n

theorem incN_unit {n} {x : α} : unit ≼{n} x := ⟨x, unit_left_id.symm.dist⟩

theorem inc_unit {x : α} : unit ≼ x := ⟨x, unit_left_id.symm⟩

theorem unit_left_id_dist {n} (x : α) : unit • x ≡{n}≡ x := unit_left_id.dist

theorem unit_right_id {x : α} : x • unit ≡ x := comm.trans unit_left_id

theorem unit_right_id_dist (x : α) : x • unit ≡{n}≡ x := comm.dist.trans (unit_left_id_dist x)

instance unit_CoreId : CoreId (unit : α) where
  core_id := pcore_unit

instance unit_total : IsTotal α where
  total _ :=
    have ⟨y, hy, _⟩ := pcore_mono' inc_unit pcore_unit
    ⟨y, hy⟩

instance empty_cancelable : Cancelable (unit : α) where
  cancelableN {n w t} _ e := calc
    w ≡{n}≡ unit • w := unit_left_id.dist.symm
    _ ≡{n}≡ unit • t := e
    _ ≡{n}≡ t := unit_left_id.dist

theorem _root_.Iris.OFE.Dist.to_incN {n} {x y : α} (H : x ≡{n}≡ y) : x ≼{n} y :=
  ⟨unit, ((equiv_dist.mp unit_right_id n).trans H).symm⟩

end ucmra


section Leibniz
variable [Leibniz α]

theorem assoc_L {x y z : α} : x • (y • z) = (x • y) • z := eq_of_eqv assoc

theorem comm_L {x y : α} : x • y = y • x := eq_of_eqv comm

theorem pcore_op_left_L {x cx : α} (h : pcore x = some cx) : cx • x = x :=
  eq_of_eqv (pcore_op_left h)

theorem pcore_idem_L {x cx : α} (h : pcore x = some cx) : pcore cx = some cx :=
  eq_of_eqv (pcore_idem h)

theorem op_opM_assoc_L {x y : α} {mz} : (x • y) •? mz = x • (y •? mz) :=
  eq_of_eqv (op_opM_assoc ..)

theorem pcore_op_right_L {x cx : α} (h : pcore x = some cx) : x • cx = x :=
  eq_of_eqv (pcore_op_right h)

theorem pcore_op_self_L {x cx : α} (h : pcore x = some cx) : cx • cx = cx :=
  eq_of_eqv (pcore_op_self h)

theorem core_id_dup_L {x : α} [CoreId x] : x • x = x :=
  eq_of_eqv (op_self x)

theorem op_core_L {x : α} [IsTotal α] : x • core x = x :=
  eq_of_eqv (op_core x)

theorem core_op_L {x : α} [IsTotal α] : core x • x = x :=
  eq_of_eqv (core_op x)

theorem core_idem_L {x : α} [IsTotal α] : core (core x) = core x :=
  eq_of_eqv (core_idem x)

theorem core_op_core_L {x : α} [IsTotal α] : core x • core x = core x :=
  eq_of_eqv core_op_core

theorem coreId_iff_core_eq_self {x : α} [IsTotal α] : CoreId x ↔ core x = x := calc
  CoreId x ↔ core x ≡ x := coreId_iff_core_eqv_self
  _        ↔ core x = x := leibniz
theorem core_eq_self {x : α} [IsTotal α] [c : CoreId x] : core x = x :=
  coreId_iff_core_eq_self.mp c

end Leibniz


section UCMRA

variable {α : Type _} [UCMRA α] [Leibniz α]

theorem unit_left_id_L {x : α} : unit • x = x := leibniz.mp unit_left_id

theorem unit_right_id_L {x : α} : x • unit = x := leibniz.mp unit_right_id

end UCMRA

section Hom

-- TODO: Typeclass

/-- A morphism between CMRAs, written `α -C> β`, is defined to be a non-expansive function which
preserves `validN`, `pcore` and `op`. -/
@[ext] structure Hom (α β : Type _) [CMRA α] [CMRA β] extends OFE.Hom α β where
  protected validN {n x} : ✓{n} x → ✓{n} (f x)
  protected pcore x : (pcore x).map f ≡ pcore (f x)
  protected op x y : f (x • y) ≡ f x • f y

@[inherit_doc]
infixr:25 " -C> " => Hom

instance [CMRA β] : CoeFun (α -C> β) (fun _ => α → β) := ⟨fun F => F.f⟩

instance [CMRA β] : OFE (α -C> β) where
  Equiv f g := f.toHom ≡ g.toHom
  Dist n f g := f.toHom ≡{n}≡ g.toHom
  dist_eqv := {
    refl _ := dist_eqv.refl _
    symm h := dist_eqv.symm h
    trans h1 h2 := dist_eqv.trans h1 h2
  }
  equiv_dist := equiv_dist
  dist_lt := dist_lt

protected def Hom.id [CMRA α] : α -C> α where
  toHom := OFE.Hom.id
  validN := id
  pcore x := by dsimp; cases pcore x <;> rfl
  op _ _ := .rfl

-- protected def Hom.comp [CMRA α] [CMRA β] [CMRA γ] (g : β -C> γ) (f : α -C> β) : α -C> γ where
--   toHom := OFE.Hom.comp g.toHom f.toHom
--   hom :=
--     ⟨fun v => g.mor.validN (f.mor.validN v),
--       fun x => sorry,
--       fun x y => sorry⟩

protected theorem Hom.eqv [CMRA β] (f : α -C> β) {x₁ x₂ : α} (X : x₁ ≡ x₂) : f x₁ ≡ f x₂ :=
  f.ne.eqv X

protected theorem Hom.core [CMRA β] (f : α -C> β) {x : α} : core (f x) ≡ f (core x) := by
  suffices (pcore x).map f.f ≡ pcore (f.f x) →
    (pcore (f.f x)).getD (f.f x) ≡ f.f ((pcore x).getD x)
  from this (f.pcore x)
  match pcore x with
  | none => intro h; simp [equiv_none.1 h.symm]
  | some cx =>
    intro h
    let ⟨s, hs, es⟩ := equiv_some h.symm
    rw [hs]; exact es

protected theorem Hom.mono [CMRA β] (f : α -C> β) {x₁ x₂ : α} : x₁ ≼ x₂ → f x₁ ≼ f x₂
  | ⟨z, hz⟩ => ⟨f.f z, (f.eqv hz).trans (f.op ..)⟩

protected theorem Hom.monoN [CMRA β] (f : α -C> β) n {x₁ x₂ : α} : x₁ ≼{n} x₂ → f x₁ ≼{n} f x₂
  | ⟨z, hz⟩ => ⟨f.f z, (f.ne.ne hz).trans (f.op ..).dist⟩

protected theorem Hom.valid [CMRA β] (f : α -C> β) {x : α} (H : ✓ x) : ✓ f x :=
  valid_iff_validN.mpr fun _ => f.validN H.validN

end Hom
end CMRA


section rFunctor

class RFunctor (F : COFE.OFunctorPre) where
  -- EXPERIMENT: Replacing COFE in this definition with OFE
  -- https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/OFunctor.20definition
  -- cofe [COFE α] [COFE β] : CMRA (F α β)
  [cmra [OFE α] [OFE β] : CMRA (F α β)]
  map [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -C> F α₂ β₂
  map_ne [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [OFE α] [OFE β] (x : F α β) : map (@Hom.id α _) (@Hom.id β _) x ≡ x
  map_comp [OFE α₁] [OFE α₂] [OFE α₃] [OFE β₁] [OFE β₂] [OFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x ≡ map g g' (map f f' x)

class RFunctorContractive (F : COFE.OFunctorPre) extends (RFunctor F) where
  map_contractive [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

variable (F T) in
def RFunctor.ap [RFunctor F] [OFE T] := F T T

attribute [instance] RFunctor.cmra


instance RFunctor.toOFunctor [R : RFunctor F] : COFE.OFunctor F where
  cofe       := RFunctor.cmra.toOFE
  map a b    := (RFunctor.map a b).toHom
  map_ne.ne  := RFunctor.map_ne.ne
  map_id     := RFunctor.map_id
  map_comp   := RFunctor.map_comp

instance RFunctorContractive.toOFunctorContractive
    [RFunctorContractive F] : COFE.OFunctorContractive F where
  map_contractive.1 := map_contractive.1

end rFunctor

section urFunctor

class URFunctor (F : COFE.OFunctorPre) where
  -- EXPERIMENT: Replacing COFE in this definition with OFE
  -- https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/OFunctor.20definition
  -- cofe [COFE α] [COFE β] : UCMRA (F α β)
  [cmra [OFE α] [OFE β] : UCMRA (F α β)]
  map [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -C> F α₂ β₂
  map_ne [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [OFE α] [OFE β] (x : F α β) : map (@Hom.id α _) (@Hom.id β _) x ≡ x
  map_comp [OFE α₁] [OFE α₂] [OFE α₃] [OFE β₁] [OFE β₂] [OFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x ≡ map g g' (map f f' x)

class URFunctorContractive (F : COFE.OFunctorPre) extends URFunctor F where
  map_contractive [OFE α₁] [OFE α₂] [OFE β₁] [OFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [instance] URFunctor.cmra

instance URFunctor.toRFunctor [UF : URFunctor F] : RFunctor F where
  cmra     := URFunctor.cmra.toCMRA
  map f g  := URFunctor.map f g
  map_ne   := URFunctor.map_ne
  map_id   := URFunctor.map_id
  map_comp := URFunctor.map_comp

instance URFunctorContractive.toRFunctorContractive
    [URFunctorContractive F] : RFunctorContractive F where
  map_contractive := map_contractive

end urFunctor

section Id

instance COFE.OFunctor.constOF_RFunctor [CMRA B] : RFunctor (constOF B) where
  map f g := by
    refine' { toHom := COFE.OFunctor.map f g, .. }
      <;> intros <;> simp [COFE.OFunctor.map]; trivial
  map_ne.ne := COFE.OFunctor.map_ne.ne
  map_id := COFE.OFunctor.map_id
  map_comp := COFE.OFunctor.map_comp

instance OFunctor.constOF_RFunctorContractive [CMRA B] :
    RFunctorContractive (COFE.constOF B) where
  map_contractive.1 := by simp [Function.uncurry, RFunctor.map, COFE.OFunctor.map]

end Id

section DiscreteFunO
open CMRA

instance cmraDiscreteFunO {α : Type _} (β : α → Type _)
    [∀ x, CMRA (β x)] [∀ x, IsTotal (β x)] : CMRA (∀ x, β x) where
  pcore f := some fun x => core (f x)
  op f g x := f x • g x
  ValidN n f := ∀ x, ✓{n} f x
  Valid f := ∀ x, ✓ f x
  op_ne.ne _ _ _ H y := (H y).op_r
  pcore_ne {n f g _} H := by rintro ⟨⟩; exact ⟨_, rfl, fun x => (H _).core⟩
  validN_ne {n x y} H H1 y := (H y).validN.mp (H1 y)
  valid_iff_validN {g} := by simpa [valid_iff_validN] using forall_comm
  validN_succ H _ := validN_succ (H _)
  validN_op_left H _ := validN_op_left (H _)
  assoc _ := assoc
  comm _ := comm
  pcore_op_left := by rintro f _ ⟨⟩ x; exact core_op (f x)
  pcore_idem := by rintro f _ ⟨⟩ x; exact core_idem (f x)
  pcore_op_mono := by
    rintro f _ ⟨⟩ g
    refine ⟨fun x => core (f x • g x), fun x => ?_⟩
    have ⟨r, hr⟩ := core_op_mono (f x) (g x)
    exact hr.trans (hr.op_r.trans <| assoc.trans core_op_core.op_l).symm
  extend {n f f1 f2} Hv He := by
    let F x := extend (Hv x) (He x)
    exact ⟨fun x => (F x).1, fun x => (F x).2.1,
      fun x => (F x).2.2.1, fun x => (F x).2.2.2.1, fun x => (F x).2.2.2.2⟩

instance ucmraDiscreteFunO {α : Type _} (β : α → Type _) [∀ x, UCMRA (β x)] : UCMRA (∀ x, β x) where
  unit _ := unit
  unit_valid _ := unit_valid
  unit_left_id _ := unit_left_id
  pcore_unit _ := core_eqv_self _

end DiscreteFunO

section DiscreteFunURF

instance urFunctorDiscreteFunOF {C} (F : C → COFE.OFunctorPre) [∀ c, URFunctor (F c)] :
    URFunctor (DiscreteFunOF F) where
  map f g := {
    toHom := COFE.OFunctor.map f g
    validN hv _ := (URFunctor.map f g).validN (hv _)
    pcore _ _ := by simpa [CMRA.pcore_eq_core] using (URFunctor.map f g).pcore _
    op _ _ _ := (URFunctor.map f g).op _ _
  }
  map_ne.ne := COFE.OFunctor.map_ne.ne
  map_id := COFE.OFunctor.map_id
  map_comp := COFE.OFunctor.map_comp

instance DiscreteFunOF_URFC {C} (F : C → COFE.OFunctorPre) [HURF : ∀ c, URFunctorContractive (F c)] :
    URFunctorContractive (DiscreteFunOF F) where
  map_contractive.1 h _ _ := URFunctorContractive.map_contractive.distLater_dist h _

end DiscreteFunURF

section option

variable [CMRA α]

def optionCore (x : Option α) : Option α := x.bind CMRA.pcore

def optionOp (x y : Option α) : Option α :=
  match x, y with
  | some x', some y' => some (CMRA.op x' y')
  | none, _ => y
  | _, none => x

def optionValidN (n : Nat) : Option α → Prop
  | some x => ✓{n} x
  | none => True

def optionValid : Option α → Prop
  | some x => ✓ x
  | none => True

instance cmraOption : CMRA (Option α) where
  pcore x := some (optionCore x)
  op := optionOp
  ValidN := optionValidN
  Valid := optionValid
  op_ne.ne n x1 x2 H := by
    rename_i x
    cases x1 <;> cases x2 <;> cases x <;> simp_all [Dist, Option.Forall₂, optionOp]
    exact CMRA.op_right_dist _ H
  pcore_ne {n} := by
    simp; intro x y cx
    rcases x with _|x <;> rcases y with _|y <;> simp_all [Dist, Option.Forall₂, optionCore]
    cases Hv : CMRA.pcore x <;> cases Hv' : CMRA.pcore y <;> simp
    · cases CMRA.pcore_ne cx.symm Hv'; simp_all
    · cases CMRA.pcore_ne cx Hv; simp_all
    · have ⟨w, Hw1, Hw2⟩ := CMRA.pcore_ne cx.symm Hv'
      cases Hv.symm.trans Hw1; exact Hw2.symm
  validN_ne {n} x y H := by
    cases x <;> cases y <;> simp_all [Dist, Option.Forall₂]
    exact (Dist.validN H).mp
  valid_iff_validN {x} := by
    cases x <;> simp [optionValid, optionValidN]
    exact CMRA.valid_iff_validN
  validN_succ {x n} := by
    cases x <;> simp_all [optionValidN]
    apply CMRA.validN_succ
  validN_op_left {n x y} := by
    cases x <;> cases y <;> simp_all [optionOp, optionValidN]
    apply CMRA.validN_op_left
  assoc {x y z} := by
    cases x <;> cases y <;> cases z <;> simp_all [Equiv, Option.Forall₂, optionOp]
    apply CMRA.assoc
  comm {x y} := by
    cases x <;> cases y <;> simp_all [Equiv, Option.Forall₂, optionOp]
    apply CMRA.comm
  pcore_op_left {x cx} := by
    cases x <;> cases cx <;> simp_all [Equiv, Option.Forall₂, optionCore, optionOp]
    apply CMRA.pcore_op_left
  pcore_idem := by
    simp; rintro (_|x) <;> simp [Equiv, Option.Forall₂, optionCore]
      <;> rcases ex : CMRA.pcore x with _|y <;> simp
    have ⟨z, Hz1, Hz2⟩ := equiv_some (CMRA.pcore_idem ex)
    simp [Hz1, Hz2]
  pcore_op_mono := by
    rintro (_|x) _ ⟨⟩ y <;> simp [optionOp, optionCore]
    · exact ⟨_, .rfl⟩
    cases ex : CMRA.pcore x
    · simp; exact ⟨_, .rfl⟩
    obtain _|y := y <;> simp
    · exists none; simp [ex]
    have ⟨cy, H⟩ := CMRA.pcore_op_mono ex y
    exact ⟨some cy, H⟩
  extend {n} := by
    rintro (_|x) (_|mb1) (_|mb2) <;> simp [optionValidN, optionOp]
      <;> intros Hx Hx' <;> try simp at Hx'
    · exists none, none
    · exists none, some x
    · exists some x, none
    · rcases CMRA.extend Hx Hx' with ⟨mc1, mc2, _, _, _⟩
      exists some mc1, some mc2

instance ucmraOption : UCMRA (Option α) where
  unit := none
  unit_valid := by simp [CMRA.Valid, optionValid]
  unit_left_id := by rintro ⟨⟩ <;> rfl
  pcore_unit := by rfl

theorem CMRA.equiv_of_some_equiv_some {x y : α} (h : some x ≡ some y) : x ≡ y := h

theorem CMRA.dist_of_some_dist_some {n} {x y : α} (h : some x ≡{n}≡ some y) : x ≡{n}≡ y := h

theorem CMRA.op_some_opM_assoc (x y : α) (mz : Option α) : (x • y) •? mz ≡ x •? (some y • mz) :=
  match mz with
  | none   => .rfl
  | some _ => assoc.symm

theorem CMRA.opM_opM_assoc {x : α} {y z : Option α} : (x •? y) •? z ≡ x •? (y • z) := by
  cases y <;> cases z <;> simp [CMRA.op?, CMRA.op, optionOp]
  exact assoc.symm

theorem CMRA.op_some_opM_assoc_dist (x y : α) (mz : Option α) :
    (x • y) •? mz ≡{n}≡ x •? (some y • mz) :=
  match mz with
  | none   => .rfl
  | some _ => assoc.dist.symm

theorem CMRA.some_inc_some_of_dist_opM {x y : α} {mz : Option α} (h : x ≡{n}≡ y •? mz)
    : some y ≼{n} some x :=
  match mz with
  | none   => ⟨none, h⟩
  | some z => ⟨some z, h⟩

theorem CMRA.inc_of_some_inc_some [CMRA.IsTotal α] {x y : α} (h : some y ≼ some x) : y ≼ x :=
  let ⟨mz, hmz⟩ := h
  match mz with
  | none => ⟨core y, (CMRA.equiv_of_some_equiv_some hmz).trans (op_core y).symm⟩
  | some z => ⟨z, hmz⟩

theorem CMRA.incN_of_Option.some_incN_some_iff_some [CMRA.IsTotal α] {x y : α} : some y ≼{n} some x → y ≼{n} x
  | ⟨none, hmz⟩ => ⟨core y, (CMRA.dist_of_some_dist_some hmz).trans (op_core_dist y).symm⟩
  | ⟨some z, hmz⟩ => ⟨z, hmz⟩

theorem CMRA.exists_op_some_eqv_some (x : Option α) (y : α) : ∃z, x • some y ≡ some z :=
  match x with
  | .none => ⟨y, Equiv.rfl⟩
  | .some w => ⟨w • y, Equiv.rfl⟩

theorem CMRA.exists_op_some_dist_some {n} (x : Option α) (y : α) : ∃z, x • some y ≡{n}≡ some z :=
  (CMRA.exists_op_some_eqv_some x y).elim fun z h => ⟨z, h.dist⟩

theorem not_valid_some_exclN_op_left {n} {x : α} [CMRA.Exclusive x] {y : α} :
    ¬✓{n} (some x • some y) := CMRA.not_valid_exclN_op_left (α := α)

theorem validN_op_unit {n} {x : Option α} (vx : ✓{n} x) : ✓{n} x • CMRA.unit := by
  cases x <;> trivial

theorem Option.inc_iff {ma mb : Option α} :
    ma ≼ mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a ≡ b ∨ a ≼ b) := by
  constructor
  · rintro ⟨mc, Hmc⟩
    cases ma <;> cases mb <;> cases mc <;> simp_all [CMRA.op, optionOp]
    · exact .inl Hmc.symm
    · right; rename_i v3; exists v3
  · rintro (H|⟨a, b, Ha, Hb, (H|⟨z, Hz⟩)⟩)
    · subst H; exists mb; simp [CMRA.op, optionOp]
    · subst Ha; subst Hb; exists none; simp [CMRA.op, optionOp]; exact H.symm
    · subst Ha; subst Hb; exists some z

theorem Option.incN_iff {ma mb : Option α} :
    ma ≼{n} mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a ≡{n}≡ b ∨ a ≼{n} b) := by
  constructor
  · rintro ⟨mc, Hmc⟩
    cases ma <;> cases mb <;> cases mc <;> simp_all [CMRA.op, optionOp]
    · exact .inl Hmc.symm
    · right; rename_i v3; exists v3
  · rintro (H|⟨a, b, Ha, Hb, (H|⟨z, Hz⟩)⟩)
    · subst H; exists mb; simp [CMRA.op, optionOp]
    · subst Ha; subst Hb; exists none; simp [CMRA.op, optionOp]; exact H.symm
    · subst Ha; subst Hb; exists some z

theorem Option.inc_iff_isTotal [CMRA.IsTotal α] {ma mb : Option α} :
    ma ≼ mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼ b := by
  apply Option.inc_iff.trans _
  constructor
  · rintro (H|⟨a, b, Ha, Hb, (H|H)⟩)
    · exact .inl H
    · right
      refine ⟨a, b, Ha, Hb, ?_⟩
      exists (CMRA.core a)
      exact H.symm.trans (CMRA.op_core a).symm
    · exact .inr ⟨a, b, Ha, Hb, H⟩
  · rintro (H|⟨a, b, Ha, Hb, H⟩)
    · exact .inl H
    · exact .inr ⟨a, b, Ha, Hb, .inr H⟩

theorem Option.incN_iff_isTotal [CMRA.IsTotal α] {ma mb : Option α} :
    ma ≼{n} mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼{n} b := by
  apply Option.incN_iff.trans _
  constructor
  · rintro (H|⟨a, b, Ha, Hb, (H|H)⟩)
    · exact .inl H
    · right
      refine ⟨a, b, Ha, Hb, ?_⟩
      exists (CMRA.core a)
      apply H.symm.trans (CMRA.op_core_dist a).symm
    · exact .inr ⟨a, b, Ha, Hb, H⟩
  · rintro (H|⟨a, b, Ha, Hb, H⟩)
    · exact .inl H
    · exact .inr ⟨a, b, Ha, Hb, .inr H⟩

theorem Option.some_incN_some_iff {a b : α} : some a ≼{n} some b ↔ a ≡{n}≡ b ∨ a ≼{n} b := by
  apply Option.incN_iff.trans; simp

-- Here
theorem Option.some_inc_some_iff {a b : α} : some a ≼ some b ↔ a ≡ b ∨ a ≼ b := by
  apply Option.inc_iff.trans; simp

theorem Option.eqv_of_inc_exclusive [CMRA.Exclusive (a : α)] {b : α} (H : some a ≼ some b) (Hv : ✓ b) :
     a ≡ b := by
  rcases Option.inc_iff.mp H with (H|⟨a', b', Ha, Hb, H⟩); simp at H
  simp only [Option.some.injEq] at Ha Hb; subst Ha; subst Hb
  rcases H with (H|H); trivial
  exact (CMRA.not_valid_of_excl_inc H Hv).elim

theorem Option.dst_of_inc_exclusive [CMRA.Exclusive (a : α)] {b : α} (H : some a ≼{n} some b) (Hv : ✓{n} b)  :
    a ≡{n}≡ b := by
  rcases Option.incN_iff.mp H with (H|⟨a', b', Ha, Hb, H⟩); simp at H
  simp only [Option.some.injEq] at Ha Hb; subst Ha; subst Hb
  rcases H with (H|H); trivial
  exact (CMRA.not_valid_of_exclN_inc H Hv).elim

theorem Option.some_inc_some_iff_isTotal [CMRA.IsTotal α] {a b : α} : some a ≼ some b ↔ a ≼ b := by
  apply Option.some_inc_some_iff.trans
  refine ⟨?_, .inr⟩
  rintro (H|H)
  · exists (CMRA.core a)
    exact H.symm.trans (CMRA.op_core a).symm
  · exact H

theorem Option.some_incN_some_iff_isTotal [CMRA.IsTotal α] {a b : α} : some a ≼{n} some b ↔ a ≼{n} b := by
  apply Option.some_incN_some_iff.trans
  refine ⟨?_, .inr⟩
  rintro (H|H)
  · exists (CMRA.core a)
    exact H.symm.trans (CMRA.op_core_dist a).symm
  · exact H

instance {a : α} [Hid : CMRA.IdFree a] [Hc : CMRA.Cancelable a] : CMRA.Cancelable (some a) := by
  constructor
  rintro n (_|b) (_|c) _ HE
  · trivial
  · rename_i h
    simp [CMRA.op, optionOp] at HE
    exact Hid.id_free0_r c (CMRA.valid0_of_validN h) (HE.symm.le (n.zero_le))
  · rename_i h
    simp [CMRA.op, optionOp] at HE
    apply Hid.id_free0_r b
    · simp [CMRA.op, optionOp, CMRA.ValidN, optionValidN] at h
      apply CMRA.valid0_of_validN
      exact (Dist.validN HE).mp h
    · apply Dist.le HE (n.zero_le)
  · simp [OFE.Dist, Option.Forall₂]
    apply Hc.cancelableN
    · rename_i h; exact h
    · apply HE

instance (ma : Option α) [Hid : ∀ a : α, CMRA.IdFree a] [Hc : ∀ a : α, CMRA.Cancelable a] :
    CMRA.Cancelable ma := by
  cases ma
  constructor
  · simp [CMRA.op, optionOp]
  · infer_instance

-- Weird that replacing this proof with the #print-ed term doesn't work for some reason
theorem Option.validN_of_incN_validN {a b : α} (Hv : ✓{n} a) (Hinc : some b ≼{n} some a) : ✓{n} b :=  by
  apply CMRA.validN_of_incN Hinc
  apply Hv

-- Same, can't replace with #print-ed term
theorem Option.valid_of_inc_valid {a b : α} (Hv : ✓ a) (Hinc : some b ≼ some a) : ✓ b :=  by
  apply CMRA.valid_of_inc Hinc
  apply Hv

theorem Option.some_inc_some_iff_op? {a b : α} : some a ≼ some b ↔ ∃ mc, b ≡ a •? mc := by
  simp [Option.inc_iff]
  constructor
  · rintro (H|H)
    · exists none; simpa [CMRA.op?] using H.symm
    · rcases H with ⟨mc', H⟩
      exists (some mc')
  · rintro ⟨(_|z), H⟩
    · exact .inl H.symm
    · right; exists z

theorem Option.some_incN_some_iff_op? {a b : α} : some a ≼{n} some b ↔ ∃ mc, b ≡{n}≡ a •? mc := by
  simp [Option.incN_iff]
  constructor
  · rintro (H|H)
    · exists none; simpa [CMRA.op?] using H.symm
    · rcases H with ⟨mc', H⟩
      exists (some mc')
  · rintro ⟨(_|z), H⟩
    · exact .inl H.symm
    · right; exists z

instance [CMRA.Discrete α] : CMRA.Discrete (Option α) where
  discrete_valid {x} := by
    cases x <;> simp [CMRA.Valid, optionValid]
    exact (CMRA.discrete_valid ·)

theorem Option.some_op_op? {a : α} {ma : Option α} : some a • ma = some (a •? ma) := by
  cases ma <;> simp [CMRA.op?, CMRA.op, optionOp]

end option

section unit

instance cmraUnit : CMRA Unit where
  pcore _ := some ()
  op _ _ := ()
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ := id
  pcore_ne _ _ := ⟨(), rfl, .rfl⟩
  validN_ne _ := id
  valid_iff_validN := ⟨fun _ _ => ⟨⟩, fun _ => ⟨⟩⟩
  validN_succ := id
  validN_op_left := id
  assoc := .rfl
  comm := .rfl
  pcore_op_left _ := .rfl
  pcore_idem _ := .rfl
  pcore_op_mono _ _ := ⟨.unit, .rfl⟩
  extend _ _ := ⟨(), (), .rfl, .rfl, .rfl⟩

end unit

namespace Prod

variable {α β : Type _} [CMRA α] [CMRA β]

abbrev pcore (x : α × β) : Option (α × β) :=
  (CMRA.pcore x.fst).bind fun a =>
  (CMRA.pcore x.snd).bind fun b =>
  return (a, b)

abbrev op (x y : α × β) : α × β :=
  (x.1 • y.1, x.2 • y.2)

abbrev ValidN n (x : α × β) := ✓{n} x.fst ∧ ✓{n} x.snd

abbrev Valid (x : α × β) := ✓ x.fst ∧ ✓ x.snd

instance cmraProd : CMRA (α × β) where
  pcore := pcore
  op := op
  ValidN := ValidN
  Valid := Valid
  op_ne {x} :=
    { ne n y z h := dist_prod_ext (Dist.op_r $ dist_fst h) (Dist.op_r $ dist_snd h) }
  pcore_ne {n x y cx} h ph := by
    have ⟨cx₁, hcx₁, this⟩ := Option.bind_eq_some_iff.mp ph
    have ⟨cx₂, hcx₂, hcx⟩ := Option.bind_eq_some_iff.mp this
    have ⟨cy₁, hcy₁, hxy₁⟩ := CMRA.pcore_ne (dist_fst h) hcx₁
    have ⟨cy₂, hcy₂, hxy₂⟩ := CMRA.pcore_ne (dist_snd h) hcx₂
    suffices g : cx ≡{n}≡ (cy₁, cy₂) by simp [hcy₁, hcy₂, g, pcore]
    calc
      cx ≡{n}≡ (cx₁, cx₂) := Dist.of_eq (Option.some.inj hcx).symm
      _  ≡{n}≡ (cy₁, cy₂) := dist_prod_ext hxy₁ hxy₂
  validN_ne {_} x y H := fun ⟨vx1, vx2⟩ => ⟨H.1.validN.mp vx1, H.2.validN.mp vx2⟩
  valid_iff_validN {x} := by
    refine ⟨fun ⟨va, vb⟩ n => ⟨va.validN, vb.validN⟩, fun h => ⟨?_, ?_⟩⟩
    · exact CMRA.valid_iff_validN.mpr fun n => (h n).left
    · exact CMRA.valid_iff_validN.mpr fun n => (h n).right
  validN_succ {x n} := fun ⟨va, vb⟩ => ⟨CMRA.validN_succ va, CMRA.validN_succ vb⟩
  validN_op_left {n x y} := fun ⟨va, vb⟩ => ⟨CMRA.validN_op_left va, CMRA.validN_op_left vb⟩
  assoc {x y z} := ⟨CMRA.assoc, CMRA.assoc⟩
  comm {x y} := ⟨CMRA.comm, CMRA.comm⟩
  pcore_op_left {x cx} h :=
    let ⟨a, ha, ho⟩ := Option.bind_eq_some_iff.mp h
    let ⟨b, hb, hh⟩ := Option.bind_eq_some_iff.mp ho
    (Option.some.inj hh) ▸ OFE.equiv_prod_ext (CMRA.pcore_op_left ha) (CMRA.pcore_op_left hb)
  pcore_idem {x cx} h := by
    have ⟨cx₁, hcx₁, this⟩ := Option.bind_eq_some_iff.mp h
    have ⟨cx₂, hcx₂, hcx⟩ := Option.bind_eq_some_iff.mp this
    have ⟨a, ha, ea⟩ := equiv_some (CMRA.pcore_idem hcx₁)
    have ⟨b, hb, eb⟩ := equiv_some (CMRA.pcore_idem hcx₂)
    have g : (a, b) ≡ (cx₁, cx₂) := ⟨ea, eb⟩
    rw [Option.some.inj hcx.symm]
    simp [ha, hb, g, pcore]
  pcore_op_mono {x cx} h y := by
    have ⟨cx₁, hcx₁, this⟩ := Option.bind_eq_some_iff.mp h
    have ⟨cx₂, hcx₂, hcx⟩ := Option.bind_eq_some_iff.mp this
    have ⟨cy₁, hcy₁⟩ := CMRA.pcore_op_mono hcx₁ y.fst
    have ⟨cy₂, hcy₂⟩ := CMRA.pcore_op_mono hcx₂ y.snd
    have ⟨a, ha, ea⟩ := equiv_some hcy₁
    have ⟨b, hb, eb⟩ := equiv_some hcy₂
    unfold pcore
    rw [Option.some.inj hcx.symm, ha, hb]
    exists (cy₁, cy₂)
  extend {n x y₁ y₂} := fun ⟨vx₁, vx₂⟩ e =>
    let ⟨z₁, w₁, hx₁, hz₁, hw₁⟩ := CMRA.extend vx₁ (OFE.dist_fst e)
    let ⟨z₂, w₂, hx₂, hz₂, hw₂⟩ := CMRA.extend vx₂ (OFE.dist_snd e)
    ⟨(z₁, z₂), (w₁, w₂), ⟨hx₁, hx₂⟩, ⟨hz₁, hz₂⟩, ⟨hw₁, hw₂⟩⟩

theorem valid_fst {x : α × β} (h : ✓ x) : ✓ x.fst := h.left
theorem valid_snd {x : α × β} (h : ✓ x) : ✓ x.snd := h.right

theorem validN_fst {n} {x : α × β} (h : ✓{n} x) : ✓{n} x.fst := h.left
theorem validN_snd {n} {x : α × β} (h : ✓{n} x) : ✓{n} x.snd := h.right

instance [CMRA.Discrete α] [CMRA.Discrete β]: CMRA.Discrete (α × β) where
  discrete_valid := by
    rintro ⟨_, _⟩
    simp [CMRA.ValidN]
    exact (⟨CMRA.discrete_valid ·, CMRA.discrete_valid ·⟩)

end Prod

section optionOF

variable (F : COFE.OFunctorPre)

instance urFunctorOptionOF [RFunctor F] : URFunctor (OptionOF F) where
  cmra {α β} := ucmraOption
  map f g := {
    toHom := COFE.OFunctor.map f g
    validN := by
      simp [COFE.OFunctor.map, CMRA.ValidN, optionMap]
      rintro n (_|x) <;> simp [optionValidN]
      exact (RFunctor.map f g).validN
    pcore := by
      rintro (_|x) <;> simp [optionCore, CMRA.pcore, COFE.OFunctor.map, optionMap]
      have := (RFunctor.map f g).pcore x; revert this
      cases CMRA.pcore x <;> cases CMRA.pcore (RFunctor.map f g x)
        <;> simp [Equiv, Option.Forall₂]
    op := by
      rintro (_|x) (_|y) <;> simp [CMRA.op, COFE.OFunctor.map, optionOp, optionMap]
      exact (RFunctor.map f g).op x y
  }
  map_ne.ne := COFE.OFunctor.map_ne.ne
  map_id := COFE.OFunctor.map_id
  map_comp := COFE.OFunctor.map_comp

instance urFunctorContractiveOptionOF
    [RFunctorContractive F] : URFunctorContractive (OptionOF F) where
  map_contractive.1 := COFE.OFunctorContractive.map_contractive.1

end optionOF

section GenMap

/-
The OFE over gmaps is eqivalent to a non-depdenent discrete function to an `Option` type with a
`Leibniz` OFE.
In this setting, the CMRA is always unital, and as a consquence the oFunctors do not require
unitality in order to act as a `URFunctor(Contractive)`.
-/

variable (α β : Type _) [UCMRA β] [Leibniz β]

abbrev GenMap := α → Option β

-- #synth CMRA (Option β)
-- #synth CMRA (α -d> (Option β))
-- #synth UCMRA (α -d> (Option β))
-- The synthesized UMRA here has unit (fun x => ε) = (fun x => none).
-- For us, this is equivalent to the Rocq-iris unit ∅.

abbrev GenMapOF (C : Type _) (F : COFE.OFunctorPre) :=
  DiscreteFunOF fun (_ : C) => OptionOF F

end GenMap
