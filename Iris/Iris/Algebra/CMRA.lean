/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Сухарик (@suhr), Markus de Medeiros, Puming Liu, Janine Lohse
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.Monoid

@[expose] public section

namespace Iris
open OFE

/-! # Ordered resource algebras

A `CMRA` is a resource algebra (`RABase`) equipped with a step-indexed order `≼{n}` and its
limit `≼` (`OrderN`). The order need neither be reflexive nor contain the extension inclusion
`x ≼ₑ{n} y := ∃ z, y ≡{n}≡ x • z` of frames: reflexivity is the law of unital algebras
(`IncRefl`, part of `UCMRA`), and `≼ₑ ⊆ ≼` is affineness (`CMRA.Affine`). Every classical
resource algebra is a `CMRA` under its extension inclusion, see `CMRA.withExtensionOrder`;
constructions that reason about frames (local updates, views) are stated with `≼ₑ`. -/

/-! ## The components of a resource algebra -/

/-- The composition of a resource algebra, together with its own laws. -/
@[rocq_alias Op]
class Op (α : Type _) [OFE α] where
  op : α → α → α
  op_ne : NonExpansive (op x)
  assoc : op x (op y z) = op (op x y) z
  comm : op x y = op y x

namespace Op

/-- The composition operation. -/
infix:60 " • " => op

variable [OFE α] [Op α]

/-- The composition operation with an optional right argument. -/
@[rocq_alias opM]
def op? (x : α) : Option α → α
  | some y => x • y
  | none => x
@[inherit_doc] infix:60 " •? " => op?

end Op

/-- The partial core of a resource algebra, together with its own laws. -/
@[rocq_alias PCore]
class PCore (α : Type _) [OFE α] where
  pcore : α → Option α
  pcore_ne : x ≡{n}≡ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy
  pcore_idem : pcore x = some cx → pcore cx = some cx

namespace PCore
variable [OFE α] [PCore α]

/-- The total core, returning `x` itself where `pcore` is undefined. -/
@[rocq_alias core]
def core (x : α) := (pcore x).getD x

end PCore

/-- A resource algebra whose core is total. -/
@[rocq_alias CmraTotal]
class CMRA.IsTotal (α : Type _) [OFE α] [PCore α] : Prop where
  total (x : α) : ∃ cx, PCore.pcore x = some cx
#rocq_ignore cmra_total_mixin "Use CMRA + IsTotal"

/-- The validity predicates of a resource algebra, together with their own laws. -/
@[rocq_alias Valid]
class Valid (α : Type _) [OFE α] where
  ValidN : Nat → α → Prop
  Valid : α → Prop
  validN_ne : x ≡{n}≡ y → ValidN n x → ValidN n y
  valid_iff_validN : Valid x ↔ ∀ n, ValidN n x
  validN_succ : ValidN n.succ x → ValidN n x

#rocq_ignore ValidN "Merged into the `Valid` type class"

namespace Valid

/-- Validity. -/
prefix:50 "✓ " => Valid.Valid
/-- Step-indexed validity. -/
notation:50 "✓{" n "} " x:51 => Valid.ValidN n x

end Valid

/-- A step-indexed order `≼{n}` together with its limit `≼`: the step-indexed order is
transitive, respects `≡{n}≡` and is downward closed in `n`; the limit is transitive and is
contained in every `≼{n}`. Neither is required to be reflexive, see `IncRefl`. -/
class OrderN (α : Type _) [OFE α] where
  IncludedN : Nat → α → α → Prop
  Included : α → α → Prop
  incN_ne {n} {x x' y y' : α} :
    x ≡{n}≡ x' → y ≡{n}≡ y' → IncludedN n x y → IncludedN n x' y'
  incN_succ {n} {x y : α} : IncludedN n.succ x y → IncludedN n x y
  incN_trans {n} {x y z : α} : IncludedN n x y → IncludedN n y z → IncludedN n x z
  inc_trans {x y z : α} : Included x y → Included y z → Included x z
  incN_of_inc {x y : α} (n) : Included x y → IncludedN n x y

namespace OrderN

/-- The step-indexed order. -/
notation:50 x " ≼{" n "} " y:51 => IncludedN n x y
/-- The order. -/
infix:50 " ≼ " => Included

variable [OFE α] [OrderN α]

/-- The reflexive closure of the step-indexed order. -/
def IncludedNR (n : Nat) (x y : α) : Prop := x ≡{n}≡ y ∨ x ≼{n} y
@[inherit_doc] notation:50 x " ≼*{" n "} " y:51 => IncludedNR n x y

/-- The reflexive closure of the order. -/
def IncludedR (x y : α) : Prop := x = y ∨ x ≼ y
@[inherit_doc] infix:50 " ≼* " => IncludedR

theorem IncludedN.incNR {n} {x y : α} : x ≼{n} y → x ≼*{n} y := .inr
theorem Included.incR {x y : α} : x ≼ y → x ≼* y := .inr

@[refl] theorem IncludedNR.rfl {n} {x : α} : x ≼*{n} x := .inl .rfl
@[refl] theorem IncludedR.rfl {x : α} : x ≼* x := .inl (Eq.refl x)

theorem IncludedNR.ne {n} {x x' y y' : α} (ex : x ≡{n}≡ x') (ey : y ≡{n}≡ y') :
    x ≼*{n} y → x' ≼*{n} y'
  | .inl e => .inl (ex.symm.trans (e.trans ey))
  | .inr h => .inr (incN_ne ex ey h)

theorem IncludedNR.succ {n} {x y : α} : x ≼*{n.succ} y → x ≼*{n} y
  | .inl e => .inl (e.le (Nat.le_succ n))
  | .inr h => .inr (incN_succ h)

theorem IncludedNR.trans {n} {x y z : α} : x ≼*{n} y → y ≼*{n} z → x ≼*{n} z
  | .inl e₁, .inl e₂ => .inl (e₁.trans e₂)
  | .inl e₁, .inr h₂ => .inr (incN_ne e₁.symm .rfl h₂)
  | .inr h₁, .inl e₂ => .inr (incN_ne .rfl e₂ h₁)
  | .inr h₁, .inr h₂ => .inr (incN_trans h₁ h₂)

theorem IncludedR.trans {x y z : α} : x ≼* y → y ≼* z → x ≼* z
  | .inl e₁, h₂ => e₁ ▸ h₂
  | h₁, .inl e₂ => e₂ ▸ h₁
  | .inr h₁, .inr h₂ => .inr (inc_trans h₁ h₂)

theorem IncludedR.incNR (n) {x y : α} : x ≼* y → x ≼*{n} y
  | .inl e => .inl (e ▸ .rfl)
  | .inr h => .inr (incN_of_inc n h)

end OrderN

/-- Reflexivity of the order: the order law of unital algebras (`UCMRA`), also enjoyed by
total algebras under their extension inclusion. -/
class IncRefl (α : Type _) [OFE α] [OrderN α] : Prop where
  inc_refl (x : α) : x ≼ x

/-- An element `x` is increasing if composing with it never shrinks a resource. Cores and units
are increasing; in an affine algebra every element is. -/
class CMRA.Increasing {α : Type _} [OFE α] [Op α] [OrderN α] (x : α) : Prop where
  increasing (y : α) : y ≼ x • y

/-! ## Resource algebras -/

/-- A resource algebra: composition, core and validity together with the laws relating them. -/
class RABase (α : Type _) extends OFE α, Op α, PCore α, Valid α where
  validN_op_left {n} {x y : α} : ✓{n} (x • y) → ✓{n} x
  pcore_op_left {x cx : α} : pcore x = some cx → cx • x = x
  extend {n} {x y₁ y₂ : α} : ✓{n} x → x ≡{n}≡ y₁ • y₂ →
    Σ' z₁ z₂ : α, x = z₁ • z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂

#rocq_ignore CmraMixin "Use the CMRA type class."
#rocq_ignore cmra_mixin_of' "Not needed."
#rocq_ignore cmra_ofeO "Not needed."
#rocq_ignore RAMixin
  "Bundled record of RA laws; Lean passes them as arguments to `RABase.ofDiscrete`."

namespace CMRA
variable [RABase α]

export Op (op op? op_ne assoc comm)
export PCore (pcore pcore_ne pcore_idem core)
export Valid (Valid ValidN validN_ne valid_iff_validN validN_succ)
export RABase (validN_op_left pcore_op_left extend)
export IsTotal (total)

@[rocq_alias CoreId]
class CoreId (x : α) where
  core_id : pcore x = some x
export CoreId (core_id)

@[rocq_alias Exclusive]
class Exclusive (x : α) where
  exclusive0_l y : ¬✓{0} x • y
export Exclusive (exclusive0_l)

@[rocq_alias Cancelable]
class Cancelable (x : α) where
  cancelableN : ✓{n} x • y → x • y ≡{n}≡ x • z → y ≡{n}≡ z
export Cancelable (cancelableN)
#rocq_ignore Cancelable_proper "Derived from nonexpansivity"

@[rocq_alias IdFree]
class IdFree (x : α) where
  id_free0_r y : ✓{0} x → ¬x • y ≡{0}≡ x
export IdFree (id_free0_r)
#rocq_ignore IdFree_proper "Derived from nonexpansivity"

@[rocq_alias cmra_assoc]
theorem assoc' {x y z : α} : x • (y • z) = (x • y) • z := assoc

@[rocq_alias cmra_comm]
theorem comm' {x y : α} : x • y = y • x := comm

@[rocq_alias cmra_pcore_l]
theorem pcore_l {x cx : α} (e : pcore x = some cx) : cx • x = x := pcore_op_left e

@[rocq_alias cmra_pcore_idemp]
theorem pcore_idemp {x cx : α} (e : pcore x = some cx) : pcore cx = some cx :=
  pcore_idem e

@[rocq_alias cmra_extend]
def extend' {n} {x y₁ y₂ : α} (v : ✓{n} x) (e : x ≡{n}≡ y₁ • y₂) :
    Σ' z₁ z₂, x = (z₁ • z₂ : α) ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ :=
  let ⟨z₁, z₂, hx, hz, hw⟩ := extend (y₁ := y₁) (y₂ := y₂) v e
  ⟨z₁, z₂, hx, hz, hw⟩

@[rocq_alias cmra_validN_op_l]
theorem validN_op_l {n} {x y : α} : ✓{n} (x • y) → ✓{n} x := validN_op_left

@[rocq_alias cmra_valid_validN]
theorem valid_validN {x : α} : ✓ x ↔ ∀ n, ✓{n} x := valid_iff_validN

@[rocq_alias cmra_op_ne]
theorem op_ne' {x : α} : NonExpansive (x • ·) := op_ne

@[rocq_alias cmra_pcore_ne]
theorem pcore_ne' {n} {x y : α} {cx} (h : x ≡{n}≡ y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy := pcore_ne h e

@[rocq_alias cmra_validN_ne]
theorem validN_ne' {n} {x y : α} (h : x ≡{n}≡ y) : ✓{n} x → ✓{n} y := validN_ne h

theorem opM_ne_right {n} {x : α} {y₁ y₂ : Option α} (h : y₁ ≡{n}≡ y₂) : x •? y₁ ≡{n}≡ x •? y₂ :=
  match y₁, y₂, h with
  | none, none, _ => .rfl
  | some _, some _, h => op_ne.ne h

@[rocq_alias cmra_opM_ne]
instance : NonExpansive₂ (op? (α := α)) where
  ne _ x₁ _ e₁ y₁ y₂ e₂ :=
    match y₁, y₂, e₂ with
    | none, none, _ => e₁
    | some _, some y₂, e₂ =>
      ((op_ne (x := x₁)).ne e₂).trans (Dist.of_eq comm |>.trans <|
        ((op_ne (x := y₂)).ne e₁).trans (Dist.of_eq comm))

#rocq_ignore cmra_opM_proper "Derived from nonexpansivity"

@[rocq_alias cmra_pcore_ne']
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

#rocq_ignore CoreId_proper "OFE is Leibniz; use equality"

/-! ## Op -/

theorem op_right_dist (x : α) {y z : α} (e : y ≡{n}≡ z) : x • y ≡{n}≡ x • z :=
  op_ne.ne e
theorem _root_.Iris.OFE.Dist.op_r {x y z : α} : y ≡{n}≡ z → x • y ≡{n}≡ x • z := op_right_dist _

theorem op_commN {x y : α} : x • y ≡{n}≡ y • x := Dist.of_eq comm

theorem op_assocN {x y z : α} : x • (y • z) ≡{n}≡ (x • y) • z := Dist.of_eq assoc

theorem op_left_dist {x y : α} (z : α) (e : x ≡{n}≡ y) : x • z ≡{n}≡ y • z :=
  op_commN.trans <| e.op_r.trans op_commN
theorem _root_.Iris.OFE.Dist.op_l {x y z : α} : x ≡{n}≡ y → x • z ≡{n}≡ y • z := op_left_dist _

theorem _root_.Iris.OFE.Dist.op {x x' y y' : α}
    (ex : x ≡{n}≡ x') (ey : y ≡{n}≡ y') : x • y ≡{n}≡ x' • y' := ex.op_l.trans ey.op_r

#rocq_ignore cmra_op_proper' "OFE is Leibniz; use equality"

theorem _root_.Iris.OFE.Dist.opM {x₁ x₂ : α} {y₁ y₂ : Option α}
    (H1 : x₁ ≡{n}≡ x₂) (H2 : y₁ ≡{n}≡ y₂) : x₁ •? y₁ ≡{n}≡ x₂ •? y₂ :=
  match y₁, y₂, H2 with
  | none, none, _ => H1
  | some _, some _, H2 => H1.op H2

theorem opM_left_dist {n} {x y : α} (z : Option α) (e : x ≡{n}≡ y) : x •? z ≡{n}≡ y •? z :=
  e.opM Dist.rfl
theorem opM_right_dist {n} (x : α) {y z : Option α} (e : y ≡{n}≡ z) : x •? y ≡{n}≡ x •? z :=
  Dist.rfl.opM e

@[rocq_alias cmra_op_opM_assoc]
theorem op_opM_assoc (x y : α) (mz : Option α) : (x • y) •? mz = x • (y •? mz) := by
  unfold op?; cases mz <;> simp [assoc]

theorem op_opM_assoc_dist (x y : α) (mz : Option α) : (x • y) •? mz ≡{n}≡ x • (y •? mz) := by
  unfold op?; cases mz <;> simp [op_assocN, Dist.symm]

/-! ## Validity -/

theorem _root_.Iris.Valid.Valid.validN : ✓ (x : α) → ✓{n} x := (valid_iff_validN.1 · _)
protected theorem Valid.validN : ✓ (x : α) → ✓{n} x := Iris.Valid.Valid.validN

theorem valid_mapN {x y : α} (f : ∀ n, ✓{n} x → ✓{n} y) (v : ✓ x) : ✓ y :=
  valid_iff_validN.mpr fun n => f n v.validN

@[rocq_alias cmra_validN_ne']
theorem validN_dist_iff {x y : α} (e : x ≡{n}≡ y) : ✓{n} x ↔ ✓{n} y := ⟨validN_ne e, validN_ne e.symm⟩
theorem _root_.Iris.OFE.Dist.validN : (x : α) ≡{n}≡ y → (✓{n} x ↔ ✓{n} y) := validN_dist_iff

#rocq_ignore cmra_validN_proper "OFE is Leibniz; use equality"
#rocq_ignore cmra_valid_proper "OFE is Leibniz; use equality"

@[rocq_alias cmra_validN_le]
theorem validN_of_le {n n'} {x : α} (le : n' ≤ n) : ✓{n} x → ✓{n'} x :=
  le.recOn id fun  _ ih vs => ih (validN_succ vs)

@[rocq_alias cmra_validN_lt]
theorem validN_of_lt {n n'} {x : α} (lt : n' < n): ✓{n} x → ✓{n'} x :=
  validN_of_le (Nat.le_of_lt lt)

theorem valid0_of_validN {n} {x : α} : ✓{n} x → ✓{0} x := validN_of_le (Nat.zero_le n)

@[rocq_alias cmra_validN_op_r]
theorem validN_op_right {n} {x y : α} : ✓{n} (x • y) → ✓{n} y :=
  fun v => validN_op_left (comm' (x := x) (y := y) ▸ v)

@[rocq_alias cmra_valid_op_r]
theorem valid_op_right (x y : α) : ✓ (x • y) → ✓ y :=
  valid_mapN fun _ => validN_op_right

@[rocq_alias cmra_valid_op_l]
theorem valid_op_left {x y : α} : ✓ (x • y) → ✓ x :=
  fun v => valid_op_right y x (comm' (x := x) (y := y) ▸ v)

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

#rocq_ignore cmra_pcore_proper "OFE is Leibniz; use equality"

@[rocq_alias cmra_op_ne']
instance cmra_op_ne2 : NonExpansive₂ (op (α := α)) where
  ne _ _ _ e₁ _ _ e₂ := e₁.op e₂

#rocq_ignore cmra_pcore_proper' "OFE is Leibniz; use equality"

@[rocq_alias cmra_pcore_l']
theorem pcore_op_left' {x : α} {cx} (e : pcore x = some cx) : cx • x = x :=
  pcore_l e

@[rocq_alias cmra_pcore_r]
theorem pcore_op_right {x : α} {cx} (e : pcore x = some cx) : x • cx = x :=
  comm'.trans (pcore_l e)

@[rocq_alias cmra_pcore_r']
theorem pcore_op_right' {x : α} {cx} (e : pcore x = some cx) : x • cx = x :=
  pcore_op_right e

@[rocq_alias cmra_pcore_idemp']
theorem pcore_idem' {x : α} {cx} (e : pcore x = some cx) : pcore cx = some cx :=
  pcore_idemp e

@[rocq_alias cmra_pcore_dup]
theorem pcore_op_self {x : α} {cx} (e : pcore x = some cx) : cx • cx = cx :=
  pcore_op_right' (pcore_idem e)

@[rocq_alias cmra_pcore_dup']
theorem pcore_op_self' {x : α} {cx} (e : pcore x = some cx) : cx • cx = cx :=
  pcore_op_self e

@[rocq_alias cmra_pcore_validN]
theorem pcore_validN {n} {x : α} {cx} (e : pcore x = some cx) (v : ✓{n} x) : ✓{n} cx :=
  validN_op_right ((pcore_op_right e).symm ▸ v)

@[rocq_alias cmra_pcore_valid]
theorem pcore_valid {x : α} {cx} (e : pcore x = some cx) : ✓ x → ✓ cx :=
  valid_mapN fun _ => pcore_validN e

@[rocq_alias core_id_dup]
theorem op_self (x : α) [CoreId x] : x • x = x := pcore_op_self' CoreId.core_id

@[rocq_alias cmra_pcore_core_id]
theorem CoreId.of_pcore_eq_some {x y : α} (e : pcore x = some y) : CoreId y where
  core_id := pcore_idem e

/-! ## Exclusive elements -/

@[rocq_alias exclusiveN_l]
theorem not_valid_exclN_op_left {n} {x : α} [Exclusive x] {y} : ¬✓{n} (x • y) :=
  n.recOn (Exclusive.exclusive0_l _) fun _ ih => ih ∘ validN_succ

@[rocq_alias exclusiveN_r]
theorem not_valid_exclN_op_right {n} {x : α} [Exclusive x] {y} : ¬✓{n} (y • x) :=
  fun v => not_valid_exclN_op_left (comm' (x := y) (y := x) ▸ v)

@[rocq_alias exclusive_l]
theorem not_valid_excl_op_left {x : α} [Exclusive x] {y} : ¬✓ (x • y) :=
  fun v => Exclusive.exclusive0_l _ v.validN

@[rocq_alias exclusive_r]
theorem not_excl_op_right {x : α} [Exclusive x] {y} : ¬✓ (y • x) :=
  fun v => not_valid_excl_op_left (comm' (x := y) (y := x) ▸ v)

@[rocq_alias exclusiveN_opM]
theorem none_of_excl_valid_op {n} {x : α} [Exclusive x] {my} : ✓{n} (x •? my) → my = none := by
  cases my <;> simp [op?, not_valid_exclN_op_left]

#rocq_ignore Exclusive_proper "OFE is Leibniz; use equality"

/-! ## Total cores -/

section total
variable [IsTotal α]

@[rocq_alias cmra_pcore_core]
theorem pcore_eq_core (x : α) : pcore x = some (core x) := by
  unfold core
  have ⟨cx, hcx⟩ := IsTotal.total x
  simp [hcx]

@[rocq_alias cmra_core_r]
theorem op_core (x : α) : x • core x = x := pcore_op_right (pcore_eq_core x)
@[rocq_alias cmra_core_l]
theorem core_op (x : α) : core x • x = x := comm'.trans (op_core x)

theorem op_core_dist (x : α) : x • core x ≡{n}≡ x := Dist.of_eq (op_core x)
theorem core_op_dist (x : α) : core x • x ≡{n}≡ x := Dist.of_eq (core_op x)

@[rocq_alias cmra_core_dup]
theorem core_op_core {x : α} : core x • core x = core x :=
  pcore_op_self (pcore_eq_core x)
@[rocq_alias cmra_core_validN]
theorem validN_core {n} {x : α} (v : ✓{n} x) : ✓{n} core x := pcore_validN (pcore_eq_core x) v
@[rocq_alias cmra_core_valid]
theorem valid_core {x : α} (v : ✓ x) : ✓ core x := pcore_valid (pcore_eq_core x) v

@[rocq_alias cmra_core_core_id]
instance (y : α) : CoreId (core y) := CoreId.of_pcore_eq_some (pcore_eq_core _)

@[rocq_alias cmra_core_ne]
theorem core_ne : NonExpansive (core : α → α) where
  ne n x₁ x₂ H := by
    show some (core x₁) ≡{n}≡ some (core x₂)
    rw [← pcore_eq_core, ← pcore_eq_core]
    exact NonExpansive.ne H

#rocq_ignore cmra_core_proper "Derived from core_ne"

theorem _root_.Iris.OFE.Dist.core :
  ∀ {n} {x₁ x₂ : α}, x₁ ≡{n}≡ x₂ → core x₁ ≡{n}≡ core x₂ := @core_ne.ne

@[rocq_alias core_id_core]
theorem core_eqv_self (x : α) [CoreId x] : core (x : α) = x :=
  Option.some.inj ((pcore_eq_core x).symm.trans CoreId.core_id)

@[rocq_alias core_id_total]
theorem coreId_iff_core_eqv_self : CoreId (x : α) ↔ core x = x :=
  ⟨fun _ => core_eqv_self x, fun e => { core_id := (pcore_eq_core x).trans (congrArg some e) }⟩

@[rocq_alias cmra_core_idemp]
theorem core_idem (x : α) : core (core x) = core x := core_eqv_self _

end total

/-! ## Discrete elements -/

@[rocq_alias cmra_op_discrete]
theorem discrete_op {x y : α} (Hv : ✓{0} x • y) [Hx : DiscreteE x] [Hy : DiscreteE y] :
    DiscreteE (x • y) where
  discrete h := by
    obtain ⟨_w, _t, wt, wx, ty⟩ := extend ((Dist.validN h).mp Hv) h.symm
    rw [Hx.discrete wx.symm, Hy.discrete ty.symm, wt]

end CMRA

/-! ## Ordered resource algebras -/

/-- An ordered resource algebra: a resource algebra with a step-indexed order that is respected
by composition, validity and the core. The order is neither required to be reflexive
(`IncRefl`) nor to contain the extension inclusion (`CMRA.Affine`). -/
@[rocq_alias cmra]
class CMRA (α : Type _) extends RABase α, OrderN α where
  op_monoN_left {n} {x y : α} (z : α) : x ≼{n} y → x • z ≼{n} y • z
  op_mono_left {x y : α} (z : α) : x ≼ y → x • z ≼ y • z
  validN_of_incN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x
  pcore_monoN {n} {x y cx : α} : x ≼{n} y → pcore x = some cx →
    ∃ cy, pcore y = some cy ∧ cx ≼{n} cy
  pcore_mono {x y cx : α} : x ≼ y → pcore x = some cx →
    ∃ cy, pcore y = some cy ∧ cx ≼ cy
  pcore_order_op {x cx : α} : pcore x = some cx →
    ∀ y, ∃ cxy, pcore (x • y) = some cxy ∧ cx ≼ cxy
  pcore_increasing {x cx : α} : pcore x = some cx → CMRA.Increasing cx
  increasing_closed {n} {x y : α} : CMRA.Increasing x → x ≼*{n} y → CMRA.Increasing y
  incN_extend {n} {x y : α} : ✓{n} y → x ≼{n} y → ∃ z, z ≼{n.succ} y ∧ z ≡{n}≡ x

namespace CMRA
export OrderN (IncludedN Included incN_ne incN_succ incN_trans inc_trans incN_of_inc)
export IncRefl (inc_refl)
end CMRA

/-! ## The extension inclusion -/

namespace RABase
open CMRA

variable [RABase α]

/-- The step-indexed extension inclusion: `y` is `x` composed with some frame. This is the
inclusion of classical resource algebras (`CMRA.withExtensionOrder` makes it the order), and
the relation frame-based constructions such as local updates and views are stated with. -/
@[rocq_alias includedN]
def IncExtN (n : Nat) (x y : α) : Prop := ∃ z : α, y ≡{n}≡ x • z
@[inherit_doc] notation:50 x " ≼ₑ{" n "} " y:51 => IncExtN n x y

/-- The extension inclusion: `y` is `x` composed with some frame. -/
@[rocq_alias included]
def IncExt (x y : α) : Prop := ∃ z : α, y = x • z
@[inherit_doc] infix:50 " ≼ₑ " => IncExt

theorem incExtN_ne {n} {x x' y y' : α} (ex : x ≡{n}≡ x') (ey : y ≡{n}≡ y') :
    x ≼ₑ{n} y → x' ≼ₑ{n} y'
  | ⟨z, hz⟩ => ⟨z, ey.symm.trans (hz.trans ex.op_l)⟩

theorem incExtN_of_incExtN_of_dist (h : (a : α) ≼ₑ{n} b) (e : b ≡{n}≡ c) : a ≼ₑ{n} c :=
  incExtN_ne .rfl e h

instance {n : Nat} : Trans (IncExtN (α := α) n) (Dist n) (IncExtN n) where
  trans := incExtN_of_incExtN_of_dist

theorem incExtN_of_dist_of_incExtN (e : (a : α) ≡{n}≡ b) (h : b ≼ₑ{n} c) : a ≼ₑ{n} c :=
  incExtN_ne e.symm .rfl h

instance {n : Nat} : Trans (Dist (α := α) n) (IncExtN n) (IncExtN n) where
  trans := incExtN_of_dist_of_incExtN

@[rocq_alias cmra_included_includedN]
theorem incExtN_of_incExt (n) {x y : α} : x ≼ₑ y → x ≼ₑ{n} y
  | ⟨z, hz⟩ => ⟨z, hz.dist⟩
theorem IncExt.incExtN {n} {x y : α} : x ≼ₑ y → x ≼ₑ{n} y := incExtN_of_incExt _

#rocq_ignore cmra_included_proper "OFE is Leibniz; use equality"

theorem incExtN_iff_left (e : (a : α) ≡{n}≡ b) : a ≼ₑ{n} c ↔ b ≼ₑ{n} c :=
  ⟨incExtN_ne e .rfl, incExtN_ne e.symm .rfl⟩

theorem incExtN_iff_right (e : (b : α) ≡{n}≡ c) : a ≼ₑ{n} b ↔ a ≼ₑ{n} c :=
  ⟨incExtN_ne .rfl e, incExtN_ne .rfl e.symm⟩

@[rocq_alias cmra_includedN_ne]
theorem incExtN_dist_iff (ea : (a : α) ≡{n}≡ a') (eb : (b : α) ≡{n}≡ b') :
    a ≼ₑ{n} b ↔ a' ≼ₑ{n} b' :=
  ⟨incExtN_ne ea eb, incExtN_ne ea.symm eb.symm⟩
theorem _root_.Iris.OFE.Dist.incExtN :
    (a : α) ≡{n}≡ a' → b ≡{n}≡ b' → (a ≼ₑ{n} b ↔ a' ≼ₑ{n} b') :=
  incExtN_dist_iff

#rocq_ignore cmra_includedN_proper "OFE is Leibniz; use equality"

@[rocq_alias cmra_included_trans]
theorem incExt_trans {x y z : α} : x ≼ₑ y → y ≼ₑ z → x ≼ₑ z
  | ⟨w, (hw : y = x • w)⟩, ⟨t, (ht : z = y • t)⟩ =>
    suffices h : z = x • (w • t) from ⟨w • t, h⟩
    calc
      z = y • t := ht
      _ = (x • w) • t := congrArg (· • t) hw
      _ = x • (w • t) := assoc.symm
theorem IncExt.trans : (x : α) ≼ₑ y → y ≼ₑ z → x ≼ₑ z := incExt_trans

instance : Trans (IncExt (α := α)) IncExt IncExt where
  trans := incExt_trans

@[rocq_alias cmra_includedN_trans]
theorem incExtN_trans {x y z : α} : x ≼ₑ{n} y → y ≼ₑ{n} z → x ≼ₑ{n} z
  | ⟨w, (hw : y ≡{n}≡ x • w)⟩, ⟨t, (ht : z ≡{n}≡ y • t)⟩ =>
    suffices h : z ≡{n}≡ x • (w • t) from ⟨w • t, h⟩
    calc
      z ≡{n}≡ y • t := ht
      _ ≡{n}≡ (x • w) • t := op_left_dist _ hw
      _ ≡{n}≡ x • (w • t) := op_assocN.symm
theorem IncExtN.trans : (x : α) ≼ₑ{n} y → y ≼ₑ{n} z → x ≼ₑ{n} z := incExtN_trans

instance : Trans (IncExtN (α := α) n) (IncExtN n) (IncExtN n) where
  trans := incExtN_trans

@[rocq_alias cmra_valid_included]
theorem valid_of_incExt {x y : α} : x ≼ₑ y → ✓ y → ✓ x
  | ⟨_, hz⟩, v => valid_op_left (hz ▸ v)

@[rocq_alias cmra_validN_includedN]
theorem validN_of_incExtN {n} {x y : α} : x ≼ₑ{n} y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne hz v)
theorem IncExtN.validN {n} {x y : α} : x ≼ₑ{n} y → ✓{n} y → ✓{n} x := validN_of_incExtN

@[rocq_alias cmra_validN_included]
theorem validN_of_incExt {n} {x y : α} : x ≼ₑ y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne hz.dist v)
theorem IncExt.validN {n} {x y : α} : x ≼ₑ y → ✓{n} y → ✓{n} x := validN_of_incExt

@[rocq_alias cmra_includedN_le]
theorem incExtN_le {n n'} {x y : α} (l1 : n' ≤ n) : x ≼ₑ{n} y → x ≼ₑ{n'} y
  | ⟨z, hz⟩ => ⟨z, Dist.le hz l1⟩
theorem incExt0_of_incExtN {n} {x y : α} : x ≼ₑ{n} y → x ≼ₑ{0} y :=
  incExtN_le (Nat.zero_le n)
theorem IncExtN.le {n n'} {x y : α} : n' ≤ n → x ≼ₑ{n} y → x ≼ₑ{n'} y := incExtN_le

@[rocq_alias cmra.cmra_includedN_S]
theorem incExtN_succ {n} {x y : α} : x ≼ₑ{n.succ} y → x ≼ₑ{n} y :=
  incExtN_le (Nat.le_succ n)
theorem IncExtN.succ {n} {x y : α} : x ≼ₑ{n.succ} y → x ≼ₑ{n} y := incExtN_succ

@[rocq_alias cmra_includedN_l]
theorem incExtN_op_left (n) (x y : α) : x ≼ₑ{n} x • y := ⟨y, Dist.rfl⟩

@[rocq_alias cmra_included_l]
theorem incExt_op_left (x y : α) : x ≼ₑ x • y := ⟨y, rfl⟩

@[rocq_alias cmra_included_r]
theorem incExt_op_right (x y : α) : y ≼ₑ x • y := ⟨x, comm⟩

@[rocq_alias cmra_includedN_r]
theorem incExtN_op_right (n) (x y : α) : y ≼ₑ{n} x • y := ⟨x, op_commN⟩

@[rocq_alias cmra_included_pcore]
theorem pcore_incExt_self {x : α} {cx} (e : pcore x = some cx) : cx ≼ₑ x :=
  ⟨x, (pcore_op_left e).symm⟩

@[rocq_alias cmra_mono_l]
theorem op_mono_right_ext {x y} (z : α) : x ≼ₑ y → z • x ≼ₑ z • y
  | ⟨w, hw⟩ => ⟨w, (congrArg (z • ·) hw).trans assoc⟩

@[rocq_alias cmra_monoN_l]
theorem op_monoN_right_ext {n x y} (z : α) : x ≼ₑ{n} y → z • x ≼ₑ{n} z • y
  | ⟨w, hw⟩ => ⟨w, hw.op_r.trans op_assocN⟩

@[rocq_alias cmra_monoN_r]
theorem op_monoN_left_ext {n x y} (z : α) (h : x ≼ₑ{n} y) : x • z ≼ₑ{n} y • z :=
  (op_commN.incExtN op_commN).1 (op_monoN_right_ext z h)

@[rocq_alias cmra_mono_r]
theorem op_mono_left_ext {x y} (z : α) (h : x ≼ₑ y) : x • z ≼ₑ y • z := by
  rw [comm' (x := x) (y := z), comm' (x := y) (y := z)]; exact op_mono_right_ext z h

@[rocq_alias cmra_monoN]
theorem op_monoN_ext {n} {x x' y y' : α} (hx : x ≼ₑ{n} x') (hy : y ≼ₑ{n} y') :
    x • y ≼ₑ{n} x' • y' :=
  (op_monoN_left_ext _ hx).trans (op_monoN_right_ext _ hy)

#rocq_ignore cmra_monoN' "Use cmra_monoN"

@[rocq_alias cmra_mono]
theorem op_mono_ext {x x' y y' : α} (hx : x ≼ₑ x') (hy : y ≼ₑ y') :
    x • y ≼ₑ x' • y' :=
  (op_mono_left_ext _ hx).trans (op_mono_right_ext _ hy)

#rocq_ignore cmra_mono' "Use cmra_mono"

@[rocq_alias core_id_extract]
theorem op_core_right_of_incExt {x y : α} [CoreId x] : x ≼ₑ y → x • y = y
  | ⟨z, hz⟩ =>
    calc x • y = x • (x • z) := congrArg (x • ·) hz
    _ = (x • x) • z := assoc'
    _ = x • z := congrArg (· • z) (op_self x)
    _ = y := hz.symm

theorem op_core_left_of_incExt {x y : α} [CoreId x] (le : x ≼ₑ y) : y • x = y :=
  comm'.trans (op_core_right_of_incExt le)

@[rocq_alias cmra_included_dist_l]
theorem incExt_dist_l {n} {x1 x2 x1' : α} :
    x1 ≼ₑ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ₑ x2' ∧ x2' ≡{n}≡ x2
  | ⟨y, hy⟩, e => ⟨x1' • y, incExt_op_left x1' y, e.op_l.trans hy.symm.dist⟩

@[rocq_alias exclusive_includedN]
theorem not_valid_of_exclN_incExt {n} {x : α} [Exclusive x] {y} : x ≼ₑ{n} y → ¬✓{n} y
  | ⟨_, hz⟩, v => not_valid_exclN_op_left (validN_ne hz v)

@[rocq_alias exclusive_included]
theorem not_valid_of_excl_incExt {x : α} [Exclusive x] {y} : x ≼ₑ y → ¬✓ y
  | ⟨_, hz⟩, v => Exclusive.exclusive0_l _ <| hz ▸ v.validN

/-- Extension along the step index: `CMRA.incN_extend` for the extension inclusion. -/
theorem incExtN_extend {n} {x y : α} (v : ✓{n} y) :
    x ≼ₑ{n} y → ∃ z, z ≼ₑ{n.succ} y ∧ z ≡{n}≡ x
  | ⟨_, hw⟩ =>
    let ⟨z₁, z₂, hy, hz₁, _⟩ := extend v hw
    ⟨z₁, ⟨z₂, hy.dist⟩, hz₁⟩

/-- A non-expansive function commuting with composition preserves the extension inclusion. -/
theorem incExtN_map {β : Type _} [RABase β] (f : α → β) [NonExpansive f]
    (hop : ∀ x y, f (x • y) = f x • f y) {n} {x y : α} : x ≼ₑ{n} y → f x ≼ₑ{n} f y
  | ⟨z, hz⟩ => ⟨f z, (NonExpansive.ne hz).trans (hop x z).dist⟩

theorem incExt_map {β : Type _} [RABase β] (f : α → β)
    (hop : ∀ x y, f (x • y) = f x • f y) {x y : α} : x ≼ₑ y → f x ≼ₑ f y
  | ⟨z, hz⟩ => ⟨f z, (congrArg f hz).trans (hop x z)⟩

section total
variable [IsTotal α]

theorem incExt_refl (x : α) : x ≼ₑ x := ⟨core x, (op_core x).symm⟩
@[refl] theorem IncExt.rfl {x : α} : x ≼ₑ x := incExt_refl x

theorem incExtN_refl (x : α) : x ≼ₑ{n} x := (incExt_refl _).incExtN
@[refl] theorem IncExtN.rfl {x : α} : x ≼ₑ{n} x := incExtN_refl x

#rocq_ignore cmra_included_preorder
  "Reflexivity is incExt_refl; transitivity is the Trans instance"
#rocq_ignore cmra_includedN_preorder
  "Reflexivity is incExtN_refl; transitivity is the Trans instance"

theorem incExtN_of_dist {n} {x y : α} (h : x ≡{n}≡ y) : x ≼ₑ{n} y :=
  incExtN_ne .rfl h (incExtN_refl x)
theorem _root_.Iris.OFE.Dist.to_incExtN {n} {x y : α} : x ≡{n}≡ y → x ≼ₑ{n} y :=
  incExtN_of_dist

@[rocq_alias cmra_included_core]
theorem core_incExt_self {x : α} : core x ≼ₑ x := ⟨x, (core_op x).symm⟩

end total

section discrete

@[rocq_alias cmra_discrete_included_iff]
theorem incExt_iff_incExtN [OFE.Discrete α] (n) {x y : α} : x ≼ₑ y ↔ x ≼ₑ{n} y :=
  ⟨incExtN_of_incExt _, fun ⟨z, hz⟩ => ⟨z, discrete hz⟩⟩

@[rocq_alias cmra_discrete_included_iff_0]
theorem incExt_0_iff_incExtN [OFE.Discrete α] (n) {x y : α} : x ≼ₑ{0} y ↔ x ≼ₑ{n} y :=
  ⟨fun ⟨z, hz⟩ => ⟨z, (discrete hz).dist⟩, incExt0_of_incExtN⟩

/-- The `discrete_inc` law of `CMRA.Discrete` for a discrete algebra with the extension order. -/
theorem incExt_of_incExt0 [OFE.Discrete α] {x y : α} : x ≼ₑ{0} y → x ≼ₑ y :=
  (incExt_iff_incExtN 0).mpr

@[rocq_alias cmra_discrete_included_l]
theorem discrete_incExt_l {x y : α} [HD : DiscreteE x] (Hv : ✓{0} y) (Hle : x ≼ₑ{0} y) :
    x ≼ₑ y :=
  have ⟨_, hz⟩ := Hle
  let ⟨_, t, wt, wx, _⟩ := extend Hv hz
  ⟨t, wt.trans (congrArg (· • t) (HD.discrete wx.symm).symm)⟩

@[rocq_alias cmra_discrete_included_r]
theorem discrete_incExt_r {x y : α} [HD : DiscreteE y] : x ≼ₑ{0} y → x ≼ₑ y
  | ⟨z, hz⟩ => ⟨z, HD.discrete hz⟩

end discrete

/-- The extension inclusion as a step-indexed order. -/
@[reducible] def extOrderN : OrderN α where
  IncludedN := IncExtN
  Included := IncExt
  incN_ne := incExtN_ne
  incN_succ := incExtN_succ
  incN_trans := incExtN_trans
  inc_trans := incExt_trans
  incN_of_inc n h := incExtN_of_incExt n h

/-- The one law of a classical resource algebra that is specific to the extension inclusion:
the partial core is monotone along frames. Instantiated by such algebras only; it is the input
of the smart constructors `CMRA.withExtensionOrder` and `UCMRA.withExtensionOrder`, and only
the monotonicity of the core along `≼ₑ` (`pcore_mono_ext` and its relatives) is stated over
it. -/
class ExtensionLaws (α : Type _) [RABase α] : Prop where
  pcore_op_mono {x cx : α} :
    pcore x = some cx → ∀ y, ∃ cy : α, pcore (x • y) = some (cx • cy)
export ExtensionLaws (pcore_op_mono)

/-- The extension laws follow from monotonicity of the partial core along the extension
inclusion, the form of the law in Iris-Rocq (`cmra_pcore_mono`). -/
theorem ExtensionLaws.ofPCoreMono
    (h : ∀ {x y cx : α}, x ≼ₑ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ₑ cy) :
    ExtensionLaws α where
  pcore_op_mono e y :=
    let ⟨_, hcy, z, hz⟩ := h (incExt_op_left _ y) e
    ⟨z, hcy.trans (congrArg some hz)⟩

/-- For a total core, monotonicity of `core` along the extension inclusion suffices. -/
theorem ExtensionLaws.ofCoreMono [IsTotal α] (h : ∀ x y : α, x ≼ₑ y → core x ≼ₑ core y) :
    ExtensionLaws α :=
  .ofPCoreMono fun {x y cx} hxy e =>
    have hcx : cx = core x := Option.some.inj (e.symm.trans (pcore_eq_core x))
    ⟨core y, pcore_eq_core y, hcx ▸ h x y hxy⟩

section extensionLaws
variable [ExtensionLaws α]

@[rocq_alias cmra_pcore_mono]
theorem pcore_mono_ext {x y : α} :
    x ≼ₑ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ₑ cy
  | ⟨_, hw⟩, e =>
    have ⟨z, hz⟩ := pcore_op_mono e _
    let ⟨t, ht, et⟩ := OFE.equiv_some ((congrArg pcore hw).trans hz)
    ⟨t, ht, z, et⟩

@[rocq_alias cmra_pcore_mono']
theorem pcore_mono_ext' {x y : α} {cx} (le : x ≼ₑ y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼ₑ cy :=
  pcore_mono_ext le e

@[rocq_alias cmra_pcore_monoN']
theorem pcore_monoN_ext' {n} {x y : α} {cx} :
    x ≼ₑ{n} y → pcore x ≡{n}≡ some cx → ∃ cy, pcore y = some cy ∧ cx ≼ₑ{n} cy
  | ⟨z, hz⟩, e =>
    let ⟨w, hw, ew⟩ := OFE.dist_some e
    let ⟨t, ht, (et : w ≼ₑ t)⟩ := pcore_mono_ext (incExt_op_left x z) hw
    have : pcore y ≡{n}≡ some t :=
      have : pcore y ≡{n}≡ pcore (x • z) := NonExpansive.ne hz
      ht ▸ this
    let ⟨r, hr, er⟩ := OFE.dist_some this
    suffices h : cx ≼ₑ{n} r from ⟨r, hr, h⟩
    calc
      cx ≡{n}≡ w := ew
      w  ≼ₑ{n}  t := incExtN_of_incExt n et
      t  ≡{n}≡ r := er

theorem pcore_monoN_ext {n} {x y : α} {cx} (h : x ≼ₑ{n} y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼ₑ{n} cy :=
  pcore_monoN_ext' h (Dist.of_eq e)

section total
variable [IsTotal α]

@[rocq_alias cmra_core_monoN]
theorem core_incExtN_core {n} {x y : α} (inc : x ≼ₑ{n} y) : core x ≼ₑ{n} core y := by
  let ⟨cy, hcy, icy⟩ := pcore_monoN_ext' inc (Dist.of_eq (pcore_eq_core x))
  cases (pcore_eq_core _).symm.trans hcy
  exact icy

theorem core_op_mono_ext (x y : α) : core x ≼ₑ core (x • y) := by
  have ⟨cy, hcy⟩ := pcore_op_mono (pcore_eq_core x) y
  simp [pcore_eq_core] at hcy
  exact ⟨_, hcy⟩

@[rocq_alias cmra_core_mono]
theorem core_mono_ext {x y : α} (Hinc : x ≼ₑ y) : core x ≼ₑ core y := by
  have ⟨z, hz⟩ := Hinc
  rw [hz]; exact core_op_mono_ext x z

end total
end extensionLaws

section extOrder
attribute [local instance] extOrderN

/-- Under the extension order, the order is the extension inclusion. -/
theorem incExt_iff_inc {x y : α} : x ≼ₑ y ↔ x ≼ y := .rfl

/-- Under the extension order, the step-indexed order is the extension inclusion. -/
theorem incExtN_iff_incN {n} {x y : α} : x ≼ₑ{n} y ↔ x ≼{n} y := .rfl

/-- Every element is increasing for the extension inclusion. -/
theorem increasing_ext (x : α) : Increasing x where
  increasing y := incExt_op_right x y

instance [IsTotal α] : IncRefl α where
  inc_refl := incExt_refl

variable [ExtensionLaws α]

/-- Every classical resource algebra is an ordered resource algebra under its extension
inclusion. -/
@[reducible] def _root_.Iris.CMRA.withExtensionOrder : CMRA α where
  toOrderN := extOrderN
  op_monoN_left := op_monoN_left_ext
  op_mono_left := op_mono_left_ext
  validN_of_incN := validN_of_incExtN
  pcore_monoN := pcore_monoN_ext
  pcore_mono := pcore_mono_ext
  pcore_order_op {_ cx} e y :=
    let ⟨cy, hcy⟩ := pcore_op_mono e y
    ⟨cx • cy, hcy, incExt_op_left cx cy⟩
  pcore_increasing _ := increasing_ext _
  increasing_closed _ _ := increasing_ext _
  incN_extend := incExtN_extend

end extOrder
end RABase

/-! ## Discrete and affine algebras -/

namespace CMRA
variable [CMRA α]

@[rocq_alias CmraDiscrete]
class Discrete (α : Type _) [CMRA α] extends OFE.Discrete α where
  discrete_valid {x : α} : ✓{0} x → ✓ x
  discrete_inc {x y : α} : x ≼{0} y → x ≼ y
export Discrete (discrete_valid discrete_inc)
#rocq_ignore discrete_validN_instance "Use CMRA instance"

/-- An affine algebra: every element is increasing, i.e. the extension inclusion is contained
in the order. Classical resource algebras are affine (`RABase.affine_withExtensionOrder`), and
`UPred M` is a `BIAffine` exactly when `M` is affine. -/
class Affine (α : Type _) [CMRA α] : Prop where
  increasing (x : α) : Increasing x

instance [Affine α] (x : α) : Increasing x := Affine.increasing x

end CMRA

instance RABase.affine_withExtensionOrder [RABase α] [RABase.ExtensionLaws α] :
    @CMRA.Affine α CMRA.withExtensionOrder :=
  letI := CMRA.withExtensionOrder (α := α)
  { increasing := RABase.increasing_ext }

/-! ## Unital algebras -/

/-- The unit of a classical unital resource algebra; the input of `UCMRA.withExtensionOrder`. -/
class Unital (α : Type _) extends RABase α where
  unit : α
  unit_valid : ✓ unit
  unit_left_id : unit • x = x
  pcore_unit : pcore unit = some unit

/-- A unital ordered resource algebra: an ordered resource algebra with a unit, whose order is
reflexive. -/
@[rocq_alias ucmra]
class UCMRA (α : Type _) extends CMRA α, Unital α, IncRefl α

#rocq_ignore Unit "Lean uses the UCMRA.unit field; no separate class needed."
#rocq_ignore UcmraMixin "Lean uses the UCMRA type class directly; mixin/bundle separation is unnecessary."
#rocq_ignore ucmra_cmraR "Folded into Lean's UCMRA extends CMRA."
#rocq_ignore ucmra_ofeO "Folded into Lean's UCMRA → OFE."

/-- Every classical unital resource algebra is a unital ordered resource algebra under its
extension inclusion. -/
@[reducible] def UCMRA.withExtensionOrder [Unital α] [RABase.ExtensionLaws α] : UCMRA α where
  toCMRA := CMRA.withExtensionOrder
  unit := Unital.unit
  unit_valid := Unital.unit_valid
  unit_left_id := Unital.unit_left_id
  pcore_unit := Unital.pcore_unit
  inc_refl _ := ⟨Unital.unit, (Op.comm.trans Unital.unit_left_id).symm⟩

/-- An element that behaves as a unit: valid, a left identity, and its own core. The
element-level counterpart of `Unital`; `UCMRA.unit` satisfies it. -/
class IsUnit [RABase α] (ε : α) : Prop where
  unit_valid : ✓ ε
  unit_left_id : ε • x = x
  pcore_unit : CMRA.pcore ε = some ε

instance [UCMRA α] : IsUnit (UCMRA.unit : α) where
  unit_valid := UCMRA.unit_valid
  unit_left_id := UCMRA.unit_left_id
  pcore_unit := UCMRA.pcore_unit

namespace CMRA
variable [CMRA α]

export UCMRA (unit unit_valid unit_left_id pcore_unit)

/-! ## Order -/

section orderN
omit [CMRA α]
variable [OFE α] [OrderN α]

theorem incN_of_incN_of_dist (h : (a : α) ≼{n} b) (e : b ≡{n}≡ c) : a ≼{n} c :=
  incN_ne .rfl e h

instance {n : Nat} : Trans (IncludedN (α := α) n) (Dist n) (IncludedN n) where
  trans := incN_of_incN_of_dist

theorem incN_of_dist_of_incN (e : (a : α) ≡{n}≡ b) (h : b ≼{n} c) : a ≼{n} c :=
  incN_ne e.symm .rfl h

instance {n : Nat} : Trans (Dist (α := α) n) (IncludedN n) (IncludedN n) where
  trans := incN_of_dist_of_incN

theorem _root_.Iris.OrderN.Included.incN {n} {x y : α} : x ≼ y → x ≼{n} y := incN_of_inc _

theorem incN_iff_left (e : (a : α) ≡{n}≡ b) : a ≼{n} c ↔ b ≼{n} c :=
  ⟨incN_ne e .rfl, incN_ne e.symm .rfl⟩
theorem _root_.Iris.OFE.Dist.incN_l : (a : α) ≡{n}≡ b → (a ≼{n} c ↔ b ≼{n} c) := incN_iff_left

theorem incN_iff_right (e : (b : α) ≡{n}≡ c) : a ≼{n} b ↔ a ≼{n} c :=
  ⟨incN_ne .rfl e, incN_ne .rfl e.symm⟩
theorem _root_.Iris.OFE.Dist.incN_r : (b : α) ≡{n}≡ c → (a ≼{n} b ↔ a ≼{n} c) := incN_iff_right

theorem incN_dist_iff (ea : (a : α) ≡{n}≡ a') (eb : (b : α) ≡{n}≡ b') : a ≼{n} b ↔ a' ≼{n} b' :=
  ⟨incN_ne ea eb, incN_ne ea.symm eb.symm⟩
theorem _root_.Iris.OFE.Dist.incN :
    (a : α) ≡{n}≡ a' → b ≡{n}≡ b' → (a ≼{n} b ↔ a' ≼{n} b') := incN_dist_iff

theorem _root_.Iris.OrderN.Included.trans : (x : α) ≼ y → y ≼ z → x ≼ z := inc_trans

instance : Trans (Included (α := α)) Included Included where
  trans := inc_trans

theorem _root_.Iris.OrderN.IncludedN.trans : (x : α) ≼{n} y → y ≼{n} z → x ≼{n} z :=
  incN_trans

instance : Trans (IncludedN (α := α) n) (IncludedN n) (IncludedN n) where
  trans := incN_trans

theorem incN_of_incN_le {n n'} {x y : α} (l1 : n' ≤ n) : x ≼{n} y → x ≼{n'} y :=
  l1.recOn id fun _ ih h => ih (incN_succ h)
theorem inc0_of_incN {n} {x y : α} : x ≼{n} y → x ≼{0} y := incN_of_incN_le (Nat.zero_le n)
theorem _root_.Iris.OrderN.IncludedN.le {n n'} {x y : α} :
    n' ≤ n → x ≼{n} y → x ≼{n'} y := incN_of_incN_le

theorem incN_of_incN_succ {n} {x y : α} : x ≼{n.succ} y → x ≼{n} y := incN_succ
theorem _root_.Iris.OrderN.IncludedN.succ {n} {x y : α} : x ≼{n.succ} y → x ≼{n} y :=
  incN_succ

section incRefl
variable [IncRefl α]

theorem incN_refl (x : α) : x ≼{n} x := (inc_refl x).incN
@[refl] theorem _root_.Iris.OrderN.Included.rfl {x : α} : x ≼ x := inc_refl x
@[refl] theorem _root_.Iris.OrderN.IncludedN.rfl {x : α} : x ≼{n} x := incN_refl x

theorem incN_of_dist {n} {x y : α} (h : x ≡{n}≡ y) : x ≼{n} y := incN_ne .rfl h (incN_refl x)
theorem _root_.Iris.OFE.Dist.to_incN {n} {x y : α} : x ≡{n}≡ y → x ≼{n} y := incN_of_dist

end incRefl

end orderN

theorem valid_of_inc {x y : α} (h : x ≼ y) : ✓ y → ✓ x :=
  valid_mapN fun n => validN_of_incN (incN_of_inc n h)

theorem _root_.Iris.OrderN.IncludedN.validN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x :=
  validN_of_incN

theorem validN_of_inc {n} {x y : α} (h : x ≼ y) : ✓{n} y → ✓{n} x :=
  validN_of_incN (incN_of_inc n h)
theorem _root_.Iris.OrderN.Included.validN {n} {x y : α} : x ≼ y → ✓{n} y → ✓{n} x :=
  validN_of_inc

theorem pcore_mono' {x y : α} {cx} (le : x ≼ y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼ cy :=
  pcore_mono le e

theorem pcore_monoN' {n} {x y : α} {cx} (h : x ≼{n} y) (e : pcore x ≡{n}≡ some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼{n} cy :=
  let ⟨_, hw, ew⟩ := OFE.dist_some e
  let ⟨cy, hcy, hi⟩ := pcore_monoN h hw
  ⟨cy, hcy, incN_of_dist_of_incN ew hi⟩

theorem op_monoN_right {n x y} (z : α) (h : x ≼{n} y) : z • x ≼{n} z • y :=
  (op_commN.incN op_commN).1 (op_monoN_left z h)

theorem op_mono_right {x y} (z : α) (h : x ≼ y) : z • x ≼ z • y := by
  rw [comm' (x := z) (y := x), comm' (x := z) (y := y)]; exact op_mono_left z h

theorem op_monoN {n} {x x' y y' : α} (hx : x ≼{n} x') (hy : y ≼{n} y') : x • y ≼{n} x' • y' :=
  (op_monoN_left _ hx).trans (op_monoN_right _ hy)

theorem op_mono {x x' y y' : α} (hx : x ≼ x') (hy : y ≼ y') : x • y ≼ x' • y' :=
  (op_mono_left _ hx).trans (op_mono_right _ hy)

theorem op?_monoN_left {n} {x y : α} (mz : Option α) (h : x ≼{n} y) : x •? mz ≼{n} y •? mz :=
  match mz with
  | none => h
  | some z => op_monoN_left z h

theorem op?_mono_left {x y : α} (mz : Option α) (h : x ≼ y) : x •? mz ≼ y •? mz :=
  match mz with
  | none => h
  | some z => op_mono_left z h

theorem _root_.Iris.OrderN.IncludedNR.op_left {n} {x y : α} (z : α) :
    x ≼*{n} y → x • z ≼*{n} y • z
  | .inl e => .inl e.op_l
  | .inr h => .inr (op_monoN_left z h)

theorem _root_.Iris.OrderN.IncludedR.op_left {x y : α} (z : α) : x ≼* y → x • z ≼* y • z
  | .inl e => .inl (e ▸ rfl)
  | .inr h => .inr (op_mono_left z h)

theorem _root_.Iris.OrderN.IncludedNR.validN {n} {x y : α} : x ≼*{n} y → ✓{n} y → ✓{n} x
  | .inl e, v => validN_ne e.symm v
  | .inr h, v => validN_of_incN h v

theorem _root_.Iris.OrderN.IncludedR.validN {n} {x y : α} : x ≼* y → ✓{n} y → ✓{n} x
  | .inl e, v => e ▸ v
  | .inr h, v => validN_of_inc h v

/-- Extension of a composition along the step index. -/
theorem op_extend {n} {x y₁ y₂ : α} (v : ✓{n} x) (h : y₁ • y₂ ≼{n} x) :
    ∃ z₁ z₂ : α, z₁ • z₂ ≼{n.succ} x ∧
      z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ :=
  let ⟨_, hx', e⟩ := incN_extend v h
  let ⟨z₁, z₂, hz, hz₁, hz₂⟩ := extend (validN_of_incN (incN_succ hx') v) e
  ⟨z₁, z₂, hz ▸ hx', hz₁, hz₂⟩

/-! ## Increasing elements -/

theorem Increasing.of_incNR {n} {x y : α} (h : Increasing x) (hxy : x ≼*{n} y) : Increasing y :=
  increasing_closed h hxy
theorem Increasing.of_dist {n} {x y : α} (h : Increasing x) (e : x ≡{n}≡ y) : Increasing y :=
  h.of_incNR (.inl e)
theorem Increasing.of_incN {n} {x y : α} (h : Increasing x) (hxy : x ≼{n} y) : Increasing y :=
  h.of_incNR (.inr hxy)
theorem Increasing.of_inc {x y : α} (h : Increasing x) (hxy : x ≼ y) : Increasing y :=
  h.of_incN (incN_of_inc 0 hxy)
theorem Increasing.of_incR {x y : α} (h : Increasing x) : x ≼* y → Increasing y
  | .inl e => e ▸ h
  | .inr hxy => h.of_inc hxy

theorem Increasing.incN {n} {x : α} (h : Increasing x) (y : α) : y ≼{n} x • y :=
  incN_of_inc n (h.increasing y)

instance (x : α) [CoreId x] : Increasing x := pcore_increasing core_id

instance Increasing.op (x y : α) [Increasing x] [Increasing y] : Increasing (x • y) where
  increasing z := calc
    z ≼ y • z := Increasing.increasing z
    _ ≼ x • (y • z) := Increasing.increasing _
    _ = (x • y) • z := assoc'

section total
variable [IsTotal α]

theorem core_incN_core {n} {x y : α} (inc : x ≼{n} y) : core x ≼{n} core y := by
  let ⟨cy, hcy, icy⟩ := pcore_monoN inc (pcore_eq_core x)
  cases (pcore_eq_core _).symm.trans hcy
  exact icy

theorem core_mono {x y : α} (inc : x ≼ y) : core x ≼ core y := by
  let ⟨cy, hcy, icy⟩ := pcore_mono inc (pcore_eq_core x)
  cases (pcore_eq_core _).symm.trans hcy
  exact icy

theorem core_op_mono (x y : α) : core x ≼ core (x • y) :=
  let ⟨_, hcxy, h⟩ := pcore_order_op (pcore_eq_core x) y
  Option.some.inj (hcxy.symm.trans (pcore_eq_core _)) ▸ h

instance increasing_core (x : α) : Increasing (core x) := pcore_increasing (pcore_eq_core x)

end total

/-! ## Affine algebras -/

section affine
variable [Affine α]

theorem inc_op_right (x y : α) : y ≼ x • y := (Affine.increasing x).increasing y
theorem inc_op_left (x y : α) : x ≼ x • y := comm' (x := y) (y := x) ▸ inc_op_right y x
theorem incN_op_left (n) (x y : α) : x ≼{n} x • y := (inc_op_left x y).incN
theorem incN_op_right (n) (x y : α) : y ≼{n} x • y := (inc_op_right x y).incN

/-- In an affine algebra the extension inclusion is contained in the order. -/
theorem incN_of_incExtN {n} {x y : α} : x ≼ₑ{n} y → x ≼{n} y
  | ⟨z, hz⟩ => incN_ne .rfl hz.symm (incN_op_left n x z)
theorem inc_of_incExt {x y : α} : x ≼ₑ y → x ≼ y
  | ⟨z, hz⟩ => hz ▸ inc_op_left x z

theorem pcore_inc_self {x : α} {cx} (e : pcore x = some cx) : cx ≼ x :=
  pcore_op_left e ▸ inc_op_left cx x

theorem core_inc_self [IsTotal α] {x : α} : core x ≼ x := pcore_inc_self (pcore_eq_core x)

end affine

section discreteCMRA

@[rocq_alias cmra_discrete_valid_iff]
theorem valid_iff_validN' [Discrete α] (n) {x : α} : ✓ x ↔ ✓{n} x :=
  ⟨Valid.validN, fun v => discrete_valid <| validN_of_le (Nat.zero_le n) v⟩

@[rocq_alias cmra_discrete_valid_iff_0]
theorem valid_0_iff_validN [Discrete α] (n) {x : α} : ✓{0} x ↔ ✓{n} x :=
  ⟨Valid.validN ∘ discrete_valid, validN_of_le (Nat.zero_le n)⟩

theorem inc_iff_incN [Discrete α] (n) {x y : α} : x ≼ y ↔ x ≼{n} y :=
  ⟨incN_of_inc _, fun h => discrete_inc (inc0_of_incN h)⟩

theorem inc_0_iff_incN [Discrete α] (n) {x y : α} : x ≼{0} y ↔ x ≼{n} y :=
  ⟨fun h => incN_of_inc n (discrete_inc h), inc0_of_incN⟩

end discreteCMRA

section cancelableElements

@[rocq_alias cancelable]
theorem cancelable {x y z : α} [Cancelable x] (v : ✓(x • y)) (e : x • y = x • z) : y = z :=
  OFE.eq_dist_2 fun _ => cancelableN v.validN e.dist

@[rocq_alias discrete_cancelable]
theorem discrete_cancelable {x : α} [Discrete α]
    (H : ∀ {y z : α}, ✓(x • y) → x • y = x • z → y = z) : Cancelable x where
  cancelableN {n} {_ _} v e := (H ((valid_iff_validN' n).mpr v) (Discrete.discrete e)).dist

@[rocq_alias cancelable_op]
instance cancelable_op {x y : α} [Cancelable x] [Cancelable y] : Cancelable (x • y) where
  cancelableN {n w _} v e :=
    have v1 : ✓{n} x • (y • w) := validN_ne op_assocN.symm v
    have v2 := validN_op_right v1
    cancelableN v2 <| cancelableN v1 <| op_assocN.trans <| e.trans op_assocN.symm

@[rocq_alias exclusive_cancelable]
instance exclusive_cancelable {x : α} [Exclusive x] : Cancelable x where
  cancelableN v _ := absurd v not_valid_exclN_op_left

#rocq_ignore cancelable_proper "OFE is Leibniz; use equality"

theorem op_opM_cancel_dist {x y z : α} [Cancelable x]
    (vxy : ✓{n} x • y) (h : x • y ≡{n}≡ (x • z) •? mw) : y ≡{n}≡ z •? mw :=
  match mw with
  | none => cancelableN vxy h
  | some _ => cancelableN vxy (h.trans (op_assocN.symm))

end cancelableElements

section idFreeElements

theorem IdFree.of_dist {x₁ x₂ : α} {n} (e : x₁ ≡{n}≡ x₂) (h : IdFree x₁) : IdFree x₂ where
  id_free0_r z v := fun h₂ =>
    have ee := Dist.le e (Nat.zero_le _)
    have := calc
      x₁ • z ≡{0}≡ x₂ • z := op_left_dist z ee
      _      ≡{0}≡ x₂ := h₂
      _      ≡{0}≡ x₁ := ee.symm
    h.id_free0_r _ ((validN_dist_iff ee).mpr v) this

@[rocq_alias id_free_ne]
theorem _root_.Iris.OFE.Dist.idFree {x₁ x₂ : α} (e : x₁ ≡{n}≡ x₂) : IdFree x₁ ↔ IdFree x₂ :=
  ⟨.of_dist e, .of_dist e.symm⟩

#rocq_ignore id_free_proper "OFE is Leibniz; use equality"

@[rocq_alias id_freeN_r]
theorem id_freeN_r {n n'} {x : α} [IdFree x] {y} (v : ✓{n} x) : ¬(x • y ≡{n'}≡ x) :=
  id_free0_r _ (validN_of_le (Nat.zero_le _) v) |>.imp (·.le (Nat.zero_le _))

@[rocq_alias id_freeN_l]
theorem id_freeN_l {n n'} {x : α} [IdFree x] {y} (v : ✓{n} x) : ¬(y • x ≡{n'}≡ x) :=
  id_freeN_r v ∘ comm'.dist.trans

@[rocq_alias id_free_r]
theorem id_free_r {x : α} [IdFree x] {y} (v : ✓x) : ¬(x • y = x) :=
  fun h => id_free0_r y (valid_iff_validN.mp v 0) h.dist

@[rocq_alias id_free_l]
theorem id_free_l {x : α} [IdFree x] {y} (v : ✓ x) : ¬(y • x = x) :=
  id_free_r v ∘ comm'.trans

@[rocq_alias discrete_id_free]
theorem discrete_id_free {x : α} [Discrete α] (H : ∀ y, ✓ x → ¬(x • y = x)) : IdFree x where
  id_free0_r y v h := H y (Discrete.discrete_valid v) (Discrete.discrete_0 h)

@[rocq_alias id_free_op_r]
instance idFree_op_r {x y : α} [IdFree y] [Cancelable x] : IdFree (x • y) where
  id_free0_r z v h :=
    id_free0_r z (validN_op_right v) (cancelableN v (op_assocN.trans h).symm).symm

@[rocq_alias id_free_op_l]
instance idFree_op_l {x y : α} [IdFree x] [Cancelable y] : IdFree (x • y) := by
  rw [comm']; exact inferInstance

@[rocq_alias exclusive_id_free]
instance exclusive_idFree {x : α} [Exclusive x] : IdFree x where
  id_free0_r z v h := exclusive0_l z ((validN_dist_iff h.symm).mp v)

end idFreeElements

section ucmra

variable {α : Type _} [UCMRA α]

@[rocq_alias ucmra_unit_validN]
theorem unit_validN {n} : ✓{n} (unit : α) := valid_iff_validN.mp (unit_valid) n

theorem unit_left_id_dist {n} (x : α) : unit • x ≡{n}≡ x := unit_left_id.dist

@[rocq_alias ucmra_unit_right_id]
theorem unit_right_id {x : α} : x • unit = x := comm'.trans unit_left_id

theorem unit_right_id_dist (x : α) : x • unit ≡{n}≡ x := comm'.dist.trans (unit_left_id_dist x)

@[rocq_alias ucmra_unit_leastN]
theorem _root_.Iris.RABase.incExtN_unit {n} {x : α} : unit ≼ₑ{n} x :=
  ⟨x, unit_left_id.symm.dist⟩

@[rocq_alias ucmra_unit_least]
theorem _root_.Iris.RABase.incExt_unit {x : α} : unit ≼ₑ x := ⟨x, unit_left_id.symm⟩

@[rocq_alias ucmra_unit_core_id]
instance unit_CoreId : CoreId (unit : α) where
  core_id := pcore_unit

@[rocq_alias cmra_unit_cmra_total]
instance unit_total : IsTotal α where
  total x :=
    let ⟨cx, hcx, _⟩ := pcore_order_op (pcore_unit (α := α)) x
    ⟨cx, unit_left_id (x := x) ▸ hcx⟩

@[rocq_alias empty_cancelable]
instance empty_cancelable : Cancelable (unit : α) where
  cancelableN {n w t} _ e := calc
    w ≡{n}≡ unit • w := unit_left_id.dist.symm
    _ ≡{n}≡ unit • t := e
    _ ≡{n}≡ t := unit_left_id.dist

/-- In a unital algebra, an element is increasing exactly when it lies above the unit. -/
theorem increasing_iff_unit_inc {x : α} : Increasing x ↔ unit ≼ x :=
  ⟨fun h => unit_right_id (x := x) ▸ h.increasing unit,
   fun h => ⟨fun y => calc
    y = unit • y := unit_left_id.symm
    _ ≼ x • y := op_mono_left y h⟩⟩

/-- The step-indexed form of `increasing_iff_unit_inc`: elements above the unit are increasing. -/
theorem incN_op_right_of_unit_incN {n} {x : α} (y : α) (h : unit ≼{n} x) : y ≼{n} x • y :=
  calc y ≡{n}≡ unit • y := (unit_left_id_dist y).symm
    _ ≼{n} x • y := op_monoN_left y h

theorem unit_inc_core (x : α) : unit ≼ core x := increasing_iff_unit_inc.mp (increasing_core x)

theorem unit_incN_core {n} (x : α) : unit ≼{n} core x := (unit_inc_core x).incN

section affine
variable [Affine α]

theorem incN_unit {n} {x : α} : unit ≼{n} x := unit_left_id (x := x) ▸ incN_op_left n unit x

theorem inc_unit {x : α} : unit ≼ x := unit_left_id (x := x) ▸ inc_op_left unit x

end affine

@[rocq_alias cmra_monoid]
instance ucmraMonoidOps {α : Type _} [UCMRA α] : Algebra.MonoidOps (CMRA.op (α := α)) UCMRA.unit where
  op_ne := ⟨fun _ _ _ hx _ _ hy => hx.op hy⟩
  op_assoc := CMRA.assoc.symm
  op_comm := CMRA.comm
  op_left_id := UCMRA.unit_left_id

end ucmra


section Leibniz

@[rocq_alias cmra_assoc_L]
theorem assoc_L {x y z : α} : x • (y • z) = (x • y) • z := assoc

@[rocq_alias cmra_comm_L]
theorem comm_L {x y : α} : x • y = y • x := comm

@[rocq_alias cmra_pcore_l_L]
theorem pcore_op_left_L {x cx : α} (h : pcore x = some cx) : cx • x = x :=
   pcore_op_left h

@[rocq_alias cmra_pcore_idemp_L]
theorem pcore_idem_L {x cx : α} (h : pcore x = some cx) : pcore cx = some cx :=
  pcore_idem h

@[rocq_alias cmra_op_opM_assoc_L]
theorem op_opM_assoc_L {x y : α} {mz} : (x • y) •? mz = x • (y •? mz) :=
  op_opM_assoc _ _ _

@[rocq_alias cmra_pcore_r_L]
theorem pcore_op_right_L {x cx : α} (h : pcore x = some cx) : x • cx = x :=
  pcore_op_right h

@[rocq_alias cmra_pcore_dup_L]
theorem pcore_op_self_L {x cx : α} (h : pcore x = some cx) : cx • cx = cx :=
  pcore_op_self h

@[rocq_alias core_id_dup_L]
theorem core_id_dup_L {x : α} [CoreId x] : x • x = x :=
  op_self x

@[rocq_alias cmra_core_r_L]
theorem op_core_L {x : α} [IsTotal α] : x • core x = x :=
  op_core x

@[rocq_alias cmra_core_l_L]
theorem core_op_L {x : α} [IsTotal α] : core x • x = x :=
  core_op x

@[rocq_alias cmra_core_idemp_L]
theorem core_idem_L {x : α} [IsTotal α] : core (core x) = core x :=
  core_idem x

@[rocq_alias cmra_core_dup_L]
theorem core_op_core_L {x : α} [IsTotal α] : core x • core x = core x :=
  core_op_core

@[rocq_alias core_id_total_L]
theorem coreId_iff_core_eq_self {x : α} [IsTotal α] : CoreId x ↔ core x = x :=
  coreId_iff_core_eqv_self
@[rocq_alias core_id_core_L]
theorem core_eq_self {x : α} [IsTotal α] [c : CoreId x] : core x = x :=
  coreId_iff_core_eq_self.mp c

end Leibniz


section UCMRA

variable {α : Type _} [UCMRA α]

@[rocq_alias ucmra_unit_valid]
theorem ucmra_unit_valid : ✓ (unit : α) := unit_valid

@[rocq_alias ucmra_unit_left_id]
theorem ucmra_unit_left_id {x : α} : unit • x = x := unit_left_id

@[rocq_alias ucmra_pcore_unit]
theorem ucmra_pcore_unit : pcore (unit : α) = some unit := pcore_unit

@[rocq_alias ucmra_unit_left_id_L]
theorem unit_left_id_L {x : α} : unit • x = x := unit_left_id

@[rocq_alias ucmra_unit_right_id_L]
theorem unit_right_id_L {x : α} : x • unit = x := unit_right_id

end UCMRA

section Hom

/-- A morphism between CMRAs, written `α -C> β`, is defined to be a non-expansive function which
preserves `validN`, `pcore`, `op`, the order and increasing elements. -/
@[ext, rocq_alias CmraMorphism]
structure Hom (α β : Type _) [CMRA α] [CMRA β] extends OFE.Hom α β where
  protected validN {n x} : ✓{n} x → ✓{n} (f x)
  protected pcore x : (pcore x).map f = pcore (f x)
  protected op x y : f (x • y) = f x • f y
  protected monoN {n x₁ x₂} : x₁ ≼{n} x₂ → f x₁ ≼{n} f x₂
  protected mono {x₁ x₂} : x₁ ≼ x₂ → f x₁ ≼ f x₂
  protected increasing {x} : Increasing x → Increasing (f x)

@[inherit_doc]
infixr:25 " -C> " => Hom

instance [CMRA β] : CoeFun (α -C> β) (fun _ => α → β) := ⟨fun F => F.f⟩

instance [CMRA β] : OFE (α -C> β) where
  Dist n f g := f.toHom ≡{n}≡ g.toHom
  dist_eqv := {
    refl _ := dist_eqv.refl _
    symm h := dist_eqv.symm h
    trans h1 h2 := dist_eqv.trans h1 h2
  }
  eq_dist' {_ _} := Hom.ext_iff.trans eq_dist
  dist_lt := dist_lt

@[rocq_alias cmra_morphism_id]
protected def Hom.id [CMRA α] : α -C> α where
  toHom := OFE.Hom.id
  validN := id
  pcore x := by dsimp; cases pcore x <;> rfl
  op _ _ := rfl
  monoN := id
  mono := id
  increasing := id

@[rocq_alias cmra_morphism_compose]
protected def Hom.comp [CMRA β] [CMRA γ] (g : β -C> γ) (f : α -C> β) : α -C> γ where
  toHom := OFE.Hom.comp g.toHom f.toHom
  validN v := g.validN (f.validN v)
  pcore x := ((Option.map_map ..).symm.trans (congrArg _ (f.pcore x))).trans (g.pcore (f x))
  op x y := (congrArg g.f (f.op x y)).trans (g.op ..)
  monoN h := g.monoN (f.monoN h)
  mono h := g.mono (f.mono h)
  increasing h := g.increasing (f.increasing h)

#rocq_ignore cmra_morphism_proper "OFE is Leibniz; use equality"

@[rocq_alias cmra_morphism_core]
protected theorem Hom.core [CMRA β] (f : α -C> β) {x : α} : core (f x) = f (core x) := by
  have h := f.pcore x
  unfold core
  cases hx : pcore x <;> rw [hx] at h <;> simp only [Option.map] at h <;> simp [← h]

@[rocq_alias cmra_morphism_mono]
protected theorem Hom.mono_ext [CMRA β] (f : α -C> β) {x₁ x₂ : α} :
    x₁ ≼ₑ x₂ → f x₁ ≼ₑ f x₂
  | ⟨z, hz⟩ => ⟨f.f z, (congrArg f.f hz).trans (f.op _ _)⟩

@[rocq_alias cmra_morphism_monoN]
protected theorem Hom.monoN_ext [CMRA β] (f : α -C> β) n {x₁ x₂ : α} :
    x₁ ≼ₑ{n} x₂ → f x₁ ≼ₑ{n} f x₂
  | ⟨z, hz⟩ => ⟨f.f z, (f.ne.ne hz).trans (f.op _ _).dist⟩

@[rocq_alias cmra_morphism_valid]
protected theorem Hom.valid [CMRA β] (f : α -C> β) {x : α} (H : ✓ x) : ✓ f x :=
  valid_iff_validN.mpr fun _ => f.validN H.validN

end Hom
end CMRA

section HomExt
open RABase
variable [RABase α] [ExtensionLaws α] [RABase β] [ExtensionLaws β]
attribute [local instance] RABase.extOrderN CMRA.withExtensionOrder

/-- A morphism between classical resource algebras needs only the classical fields: under the
extension order, `monoN`, `mono` and `increasing` follow from `op`. -/
@[reducible] def CMRA.Hom.withExtensionOrder (f : α -n> β)
    (validN : ∀ {n} {x : α}, ✓{n} x → ✓{n} (f x))
    (pcore : ∀ x, (CMRA.pcore x).map f = CMRA.pcore (f x))
    (op : ∀ x y, f (x • y) = f x • f y) : α -C> β where
  toHom := f
  validN := validN
  pcore := pcore
  op := op
  monoN | ⟨z, hz⟩ => ⟨f z, (f.ne.ne hz).trans (op _ _).dist⟩
  mono | ⟨z, hz⟩ => ⟨f z, (congrArg f hz).trans (op _ _)⟩
  increasing _ := increasing_ext _

end HomExt

section rFunctor

@[rocq_alias rFunctor]
class RFunctor (F : COFE.OFunctorPre) where
  [cmra [COFE α] [COFE β] : CMRA (F α β)]
  map [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -C> F α₂ β₂
  map_ne [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFE α] [COFE β] (x : F α β) : map (Hom.id (α := α)) (Hom.id (α := β)) x = x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x = map g g' (map f f' x)

@[rocq_alias rFunctorContractive]
class RFunctorContractive (F : COFE.OFunctorPre) extends (RFunctor F) where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [reducible, instance] RFunctor.cmra

#rocq_ignore rFunctor_apply "Just apply the underlying `OFunctorPre`"

@[rocq_alias rFunctor_to_oFunctor]
instance RFunctor.toOFunctor [R : RFunctor F] : COFE.OFunctor F where
  ofe        := RFunctor.cmra.toOFE
  map a b    := (RFunctor.map a b).toHom
  map_ne.ne  := RFunctor.map_ne.ne
  map_id x   := RFunctor.map_id x
  map_comp f g f' g' x := RFunctor.map_comp f g f' g' x

@[rocq_alias rFunctor_to_oFunctor_contractive]
instance RFunctorContractive.toOFunctorContractive
    [RFunctorContractive F] : COFE.OFunctorContractive F where
  map_contractive.1 := map_contractive.1

end rFunctor

section urFunctor

@[rocq_alias urFunctor]
class URFunctor (F : COFE.OFunctorPre) where
  [cmra [COFE α] [COFE β] : UCMRA (F α β)]
  map [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -C> F α₂ β₂
  map_ne [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFE α] [COFE β] (x : F α β) : map (Hom.id (α := α)) (Hom.id (α := β)) x = x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x = map g g' (map f f' x)

@[rocq_alias urFunctorContractive]
class URFunctorContractive (F : COFE.OFunctorPre) extends URFunctor F where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [reducible, instance] URFunctor.cmra

#rocq_ignore urFunctor_apply "Just apply the underlying `OFunctorPre`"

/-- A resource functor all of whose algebras are affine. The global ghost state of `IProp` is
affine — so that `IProp` is an affine logic — exactly when every functor of its bundle is. -/
class RFunctorAffine (F : COFE.OFunctorPre) [RFunctor F] : Prop where
  affine [COFE α] [COFE β] : CMRA.Affine (F α β)

attribute [instance] RFunctorAffine.affine

@[rocq_alias urFunctor_to_rFunctor]
instance URFunctor.toRFunctor [UF : URFunctor F] : RFunctor F where
  cmra     := URFunctor.cmra.toCMRA
  map f g  := URFunctor.map f g
  map_ne   := URFunctor.map_ne
  map_id   := URFunctor.map_id
  map_comp := URFunctor.map_comp

@[rocq_alias urFunctor_to_rFunctor_contractive]
instance URFunctorContractive.toRFunctorContractive
    [URFunctorContractive F] : RFunctorContractive F where
  map_contractive := map_contractive

end urFunctor

section ComposeRF

open COFE

theorem RFunctorContractive.map_distLater {F : OFunctorPre} [RFunctorContractive F]
    [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] {n} {f₁ f₂ : α₂ -n> α₁} {g₁ g₂ : β₁ -n> β₂}
    (hf : DistLater n f₁ f₂) (hg : DistLater n g₁ g₂) (x : F α₁ β₁) :
    RFunctor.map f₁ g₁ x ≡{n}≡ RFunctor.map f₂ g₂ x :=
  map_contractive.1 (x := (f₁, g₁)) (y := (f₂, g₂)) (fun m hm => ⟨hf m hm, hg m hm⟩) x

theorem URFunctorContractive.map_distLater {F : OFunctorPre} [URFunctorContractive F]
    [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] {n} {f₁ f₂ : α₂ -n> α₁} {g₁ g₂ : β₁ -n> β₂}
    (hf : DistLater n f₁ f₂) (hg : DistLater n g₁ g₂) (x : F α₁ β₁) :
    URFunctor.map f₁ g₁ x ≡{n}≡ URFunctor.map f₂ g₂ x :=
  map_contractive.1 (x := (f₁, g₁)) (y := (f₂, g₂)) (fun m hm => ⟨hf m hm, hg m hm⟩) x

variable {F₁ F₂ : OFunctorPre} [OFunctor F₂] [∀ α β, [COFE α] → [COFE β] → IsCOFE (F₂ α β)]

open OFunctor in
@[rocq_alias rFunctor_oFunctor_compose]
instance rFunctorComposeOF [RFunctor F₁] : RFunctor (ComposeOF F₁ F₂) where
  cmra := RFunctor.cmra (F := F₁)
  map f g := RFunctor.map (F := F₁) (map (F := F₂) g f) (map (F := F₂) f g)
  map_ne.ne _ _ _ hf _ _ hg _ :=
    (RFunctor.map_ne (F := F₁)).ne (fun _ => (map_ne (F := F₂)).ne hg hf _)
      (fun _ => (map_ne (F := F₂)).ne hf hg _) _
  map_id _ := by
    simp only [map_id_eq]
    exact RFunctor.map_id (F := F₁) _
  map_comp _ _ _ _ _ := by
    simp only [map_comp_eq]
    exact RFunctor.map_comp (F := F₁) _ _ _ _ _

open OFunctor in
@[rocq_alias urFunctor_oFunctor_compose]
instance urFunctorComposeOF [URFunctor F₁] : URFunctor (ComposeOF F₁ F₂) where
  cmra := URFunctor.cmra (F := F₁)
  map f g := URFunctor.map (F := F₁) (map (F := F₂) g f) (map (F := F₂) f g)
  map_ne.ne _ _ _ hf _ _ hg _ :=
    (URFunctor.map_ne (F := F₁)).ne (fun _ => (map_ne (F := F₂)).ne hg hf _)
      (fun _ => (map_ne (F := F₂)).ne hf hg _) _
  map_id _ := by
    simp only [map_id_eq]
    exact URFunctor.map_id (F := F₁) _
  map_comp _ _ _ _ _ := by
    simp only [map_comp_eq]
    exact URFunctor.map_comp (F := F₁) _ _ _ _ _

instance [RFunctor F₁] [RFunctorAffine F₁] : RFunctorAffine (ComposeOF F₁ F₂) where
  affine := RFunctorAffine.affine (F := F₁)

open OFunctor in
@[rocq_alias rFunctor_oFunctor_compose_contractive_1]
instance rFunctorComposeOF_contractive_left [RFunctorContractive F₁] :
    RFunctorContractive (ComposeOF F₁ F₂) where
  map_contractive := ⟨fun {_ _ _} h x =>
    RFunctorContractive.map_distLater (F := F₁)
      (fun m hm _ => (map_ne (F := F₂)).ne (h m hm).2 (h m hm).1 _)
      (fun m hm _ => (map_ne (F := F₂)).ne (h m hm).1 (h m hm).2 _) x⟩

open OFunctor in
@[rocq_alias urFunctor_oFunctor_compose_contractive_1]
instance urFunctorComposeOF_contractive_left [URFunctorContractive F₁] :
    URFunctorContractive (ComposeOF F₁ F₂) where
  map_contractive := ⟨fun {_ _ _} h x =>
    URFunctorContractive.map_distLater (F := F₁)
      (fun m hm _ => (map_ne (F := F₂)).ne (h m hm).2 (h m hm).1 _)
      (fun m hm _ => (map_ne (F := F₂)).ne (h m hm).1 (h m hm).2 _) x⟩

end ComposeRF

section ComposeRFContractive

open COFE OFunctorContractive

variable {F₁ F₂ : OFunctorPre} [OFunctorContractive F₂]
  [∀ α β, [COFE α] → [COFE β] → IsCOFE (F₂ α β)]

@[rocq_alias rFunctor_oFunctor_compose_contractive_2]
instance rFunctorComposeOF_contractive_right [RFunctor F₁] :
    RFunctorContractive (ComposeOF F₁ F₂) where
  map_contractive := ⟨fun {_ _ _} h x =>
    (RFunctor.map_ne (F := F₁)).ne
      (fun _ => map_distLater (F := F₂) (fun m hm => (h m hm).2) (fun m hm => (h m hm).1) _)
      (fun _ => map_distLater (F := F₂) (fun m hm => (h m hm).1) (fun m hm => (h m hm).2) _) x⟩

@[rocq_alias urFunctor_oFunctor_compose_contractive_2]
instance urFunctorComposeOF_contractive_right [URFunctor F₁] :
    URFunctorContractive (ComposeOF F₁ F₂) where
  map_contractive := ⟨fun {_ _ _} h x =>
    (URFunctor.map_ne (F := F₁)).ne
      (fun _ => map_distLater (F := F₂) (fun m hm => (h m hm).2) (fun m hm => (h m hm).1) _)
      (fun _ => map_distLater (F := F₂) (fun m hm => (h m hm).1) (fun m hm => (h m hm).2) _) x⟩

end ComposeRFContractive

section Id

@[rocq_alias constRF]
instance COFE.OFunctor.constOF_RFunctor [CMRA B] : RFunctor (constOF B) where
  cmra := inferInstance
  map _ _ := (CMRA.Hom.id : B -C> B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance COFE.OFunctor.constOF_RFunctorAffine [CMRA B] [CMRA.Affine B] :
    RFunctorAffine (constOF B) where
  affine := inferInstance

@[rocq_alias constRF_contractive]
instance OFunctor.constOF_RFunctorContractive [CMRA B] :
    RFunctorContractive (constOF B) where
  map_contractive.1 := fun _ => .rfl

@[rocq_alias constURF]
instance COFE.OFunctor.constOF_URFunctor [UCMRA B] : URFunctor (constOF B) where
  cmra := inferInstance
  map _ _ := (CMRA.Hom.id : B -C> B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

@[rocq_alias constURF_contractive]
instance OFunctor.constOF_URFunctorContractive [UCMRA B] :
    URFunctorContractive (constOF B) where
  map_contractive.1 _ := .rfl

end Id

/-! ## Transporting a CMRA equality

Rocq bundles a CMRA as a record, so a proof of `A = B` transports the whole algebra. In Lean
`CMRA` is a type class, and an equality of carriers says nothing about the two instances, so the
transport lemmas are replaced by `transpAp` and the `OFE.transpAp_*` family in
`Iris.Instances.IProp.Instance`, which carry the equality of the instances explicitly. -/

#rocq_ignore cmra_transport "Use `transpAp`"
#rocq_ignore cmra_transport_trans "Use `transpAp` with `Eq.trans`"
#rocq_ignore cmra_transport_ne "Use `OFE.transpAp_eqv_mp`"
#rocq_ignore cmra_transport_proper "OFE is Leibniz; use equality"
#rocq_ignore cmra_transport_op "Use `OFE.transpAp_op_mp`"
#rocq_ignore cmra_transport_core "Use `OFE.transpAp_pcore_mp`"
#rocq_ignore cmra_transport_validN
  "Use `OFE.transpAp_validN_mp` and its converse `OFE.validN_transpAp_mp`"
#rocq_ignore cmra_transport_valid
  "Use `OFE.transpAp_validN_mp`/`OFE.validN_transpAp_mp` with `CMRA.valid_iff_validN`"
#rocq_ignore cmra_transport_discrete "No counterpart; see the `transpAp` family"
#rocq_ignore cmra_transport_core_id "No counterpart; see the `transpAp` family"

section DiscreteFunO
open CMRA

#rocq_ignore discrete_fun_op_instance "Use CMRA instance"
#rocq_ignore discrete_fun_pcore_instance "Use CMRA instance"
#rocq_ignore discrete_fun_valid_instance "Use CMRA instance"
#rocq_ignore discrete_fun_validN_instance "Use CMRA instance"
#rocq_ignore discrete_fun_cmra_mixin "Use CMRA instance"

namespace DiscreteFun

variable {α : Type _} {β : α → Type _}

section
variable [∀ x, CMRA (β x)]

/-- The pointwise order on functions. -/
@[reducible] def orderN : OrderN (∀ x, β x) where
  IncludedN n f g := ∀ x, f x ≼{n} g x
  Included f g := ∀ x, f x ≼ g x
  incN_ne ef eg h x := incN_ne (ef x) (eg x) (h x)
  incN_succ h x := incN_succ (h x)
  incN_trans h₁ h₂ x := incN_trans (h₁ x) (h₂ x)
  inc_trans h₁ h₂ x := inc_trans (h₁ x) (h₂ x)
  incN_of_inc n h x := incN_of_inc n (h x)

attribute [local instance] orderN

theorem incNR_apply {n} {f g : ∀ x, β x} (h : f ≼*{n} g) (x : α) : f x ≼*{n} g x :=
  h.imp (· x) (· x)

variable [∀ x, IsTotal (β x)]

/-- The pointwise resource algebra on functions. -/
@[reducible] def raBase : RABase (∀ x, β x) where
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
  assoc := funext fun _ => assoc
  comm := funext fun _ => comm
  pcore_op_left := by rintro f _ ⟨⟩; exact funext fun x => core_op (f x)
  pcore_idem := by
    rintro f _ ⟨⟩; exact congrArg some (funext fun x => core_idem (f x))
  extend {n f f1 f2} Hv He := by
    let F x := extend (Hv x) (He x)
    exact ⟨fun x => (F x).1, fun x => (F x).2.1,
      funext fun x => (F x).2.2.1, fun x => (F x).2.2.2.1, fun x => (F x).2.2.2.2⟩

attribute [local instance] raBase

open Classical in
theorem increasing_apply {f : ∀ x, β x} (h : Increasing f) (x : α) : Increasing (f x) where
  increasing y := by
    let g : ∀ x', β x' := fun x' => if e : x' = x then e ▸ y else f x'
    have hg : g x = y := dif_pos rfl
    rw [← hg]
    exact h.increasing g x

theorem increasing_iff {f : ∀ x, β x} : Increasing f ↔ ∀ x, Increasing (f x) :=
  ⟨increasing_apply, fun h => { increasing := fun g x => (h x).increasing (g x) }⟩

variable (β) in
@[rocq_alias discrete_funR]
instance _root_.Iris.cmraDiscreteFunO : CMRA (∀ x, β x) where
  toRABase := raBase
  toOrderN := orderN
  op_monoN_left h H x := op_monoN_left (h x) (H x)
  op_mono_left h H x := op_mono_left (h x) (H x)
  validN_of_incN H V x := validN_of_incN (H x) (V x)
  pcore_monoN := by rintro n f g _ H ⟨⟩; exact ⟨_, rfl, fun x => core_incN_core (H x)⟩
  pcore_mono := by rintro f g _ H ⟨⟩; exact ⟨_, rfl, fun x => core_mono (H x)⟩
  pcore_order_op := by rintro f _ ⟨⟩ g; exact ⟨_, rfl, fun x => core_op_mono (f x) (g x)⟩
  pcore_increasing := by rintro f _ ⟨⟩; exact increasing_iff.mpr fun x => inferInstance
  increasing_closed H₁ H₂ :=
    increasing_iff.mpr fun x => increasing_closed (increasing_apply H₁ x) (incNR_apply H₂ x)
  incN_extend V H :=
    let ⟨z, hz⟩ := Classical.skolem.mp fun x => incN_extend (V x) (H x)
    ⟨z, fun x => (hz x).1, fun x => (hz x).2⟩

end

#rocq_ignore discrete_fun_unit_instance "Use UCMRA instance"
#rocq_ignore discrete_fun_ucmra_mixin "Use UCMRA instance"

variable (β) in
@[rocq_alias discrete_funUR]
instance _root_.Iris.ucmraDiscreteFunO [∀ x, UCMRA (β x)] : UCMRA (∀ x, β x) where
  unit _ := unit
  unit_valid _ := unit_valid
  unit_left_id := funext fun _ => unit_left_id
  pcore_unit := congrArg some (funext fun _ => core_eqv_self _)
  inc_refl f x := inc_refl (f x)

@[rocq_alias discrete_fun_lookup_op]
theorem op_apply [∀ x, CMRA (β x)] [∀ x, IsTotal (β x)] (f g : ∀ x, β x) (x : α) :
    (f • g) x = f x • g x := rfl

@[rocq_alias discrete_fun_lookup_core]
theorem core_apply [∀ x, CMRA (β x)] [∀ x, IsTotal (β x)] (f : ∀ x, β x) (x : α) :
    core f x = core (f x) := rfl

@[rocq_alias discrete_fun_lookup_empty]
theorem unit_apply [∀ x, UCMRA (β x)] (x : α) : (unit : ∀ x, β x) x = unit := rfl

@[rocq_alias discrete_fun_unit_discrete]
instance [∀ x, UCMRA (β x)] [∀ x, OFE.DiscreteE (unit : β x)] :
    OFE.DiscreteE (unit : ∀ x, β x) where
  discrete h := funext fun x => OFE.DiscreteE.discrete (h x)

variable [∀ x, CMRA (β x)] [∀ x, IsTotal (β x)]

theorem inc_apply {f g : ∀ x, β x} (h : f ≼ g) (x : α) : f x ≼ g x := h x

theorem inc_iff {f g : ∀ x, β x} : f ≼ g ↔ ∀ x, f x ≼ g x := .rfl

theorem incN_iff {n} {f g : ∀ x, β x} : f ≼{n} g ↔ ∀ x, f x ≼{n} g x := .rfl

@[rocq_alias discrete_fun_included_spec_1]
theorem incExt_apply {f g : ∀ x, β x} : f ≼ₑ g → ∀ x, f x ≼ₑ g x
  | ⟨h, hh⟩, x => ⟨h x, congrFun hh x⟩

/-- Note: The finiteness assumption from Iris-Rocq is removed using choice. -/
@[rocq_alias discrete_fun_included_spec]
theorem incExt_iff {f g : ∀ x, β x} : f ≼ₑ g ↔ ∀ x, f x ≼ₑ g x := by
  refine ⟨incExt_apply, fun h => ?_⟩
  obtain ⟨z, hz⟩ := Classical.skolem.mp h
  exact ⟨z, funext hz⟩

theorem incExtN_apply {n} {f g : ∀ x, β x} : f ≼ₑ{n} g → ∀ x, f x ≼ₑ{n} g x
  | ⟨h, hh⟩, x => ⟨h x, hh x⟩

/-- Note: The finiteness assumption from Iris-Rocq is removed using choice. -/
theorem incExtN_iff {n} {f g : ∀ x, β x} : f ≼ₑ{n} g ↔ ∀ x, f x ≼ₑ{n} g x := by
  refine ⟨incExtN_apply, fun h => ?_⟩
  obtain ⟨z, hz⟩ := Classical.skolem.mp h
  exact ⟨z, hz⟩

instance [∀ x, IncRefl (β x)] : IncRefl (∀ x, β x) where
  inc_refl f x := inc_refl (f x)

instance [∀ x, Affine (β x)] : Affine (∀ x, β x) where
  increasing f := increasing_iff.mpr fun x => Affine.increasing (f x)

end DiscreteFun

@[rocq_alias discrete_fun_map_cmra_morphism]
def mapCodHomC {α : Type _} {β₁ β₂ : α → Type _}
    [∀ x, UCMRA (β₁ x)] [∀ x, UCMRA (β₂ x)]
    (F : ∀ x, β₁ x -C> β₂ x) : (∀ x, β₁ x) -C> (∀ x, β₂ x) where
  toHom := mapCodHom fun x => (F x).toHom
  validN h x := (F x).validN (h x)
  pcore _ := congrArg some (funext fun x => (F x).core.symm)
  op f g := funext fun x => (F x).op (f x) (g x)
  monoN h x := (F x).monoN (h x)
  mono h x := (F x).mono (h x)
  increasing h := DiscreteFun.increasing_iff.mpr fun x =>
    (F x).increasing (DiscreteFun.increasing_apply h x)

end DiscreteFunO

section DiscreteFunURF

@[rocq_alias discrete_funURF]
instance urFunctorDiscreteFunOF {C} (F : C → COFE.OFunctorPre) [∀ c, URFunctor (F c)] :
    URFunctor (DiscreteFunOF F) where
  map f g := {
    toHom := COFE.OFunctor.map f g
    validN hv _ := (URFunctor.map f g).validN (hv _)
    pcore x := by
      simp only [CMRA.pcore, Option.map]
      exact congrArg some (funext fun c => ((URFunctor.map f g).core).symm)
    op x y := funext fun c => (URFunctor.map f g).op (x c) (y c)
    monoN h c := (URFunctor.map f g).monoN (h c)
    mono h c := (URFunctor.map f g).mono (h c)
    increasing h := DiscreteFun.increasing_iff.mpr fun c =>
      (URFunctor.map f g).increasing (DiscreteFun.increasing_apply h c)
  }
  map_ne.ne := COFE.OFunctor.map_ne.ne
  map_id x := COFE.OFunctor.map_id x
  map_comp f g f' g' x := COFE.OFunctor.map_comp f g f' g' x

instance {C} (F : C → COFE.OFunctorPre) [∀ c, URFunctor (F c)] [∀ c, RFunctorAffine (F c)] :
    RFunctorAffine (DiscreteFunOF F) where
  affine := inferInstance

@[rocq_alias discrete_funURF_contractive]
instance DiscreteFunOF_URFC {C} (F : C → COFE.OFunctorPre) [HURF : ∀ c, URFunctorContractive (F c)] :
    URFunctorContractive (DiscreteFunOF F) where
  map_contractive.1 h _ _ := URFunctorContractive.map_contractive.distLater_dist h _

end DiscreteFunURF

section option

open CMRA RABase Option

variable [CMRA α]

@[simp]
def optionCore (x : Option α) : Option α := x.bind pcore

@[simp]
def optionOp (x y : Option α) : Option α :=
  match x, y with
  | some x', some y' => some (CMRA.op x' y')
  | none, _ => y
  | _, none => x

@[simp]
def optionValidN (n : Nat) : Option α → Prop
  | some x => ✓{n} x
  | none => True

@[simp]
def optionValid : Option α → Prop
  | some x => ✓ x
  | none => True

/-- The step-indexed order on `Option α`: `none` lies below `none` and below every increasing
element, `some` is monotone up to `n`-equivalence, and nothing but `none` lies below `none`. -/
@[simp]
def optionIncludedN (n : Nat) : Option α → Option α → Prop
  | none, none => True
  | none, some y => Increasing y
  | some x, some y => x ≼*{n} y
  | some _, none => False

/-- The order on `Option α`; see `optionIncludedN`. -/
@[simp]
def optionIncluded : Option α → Option α → Prop
  | none, none => True
  | none, some y => Increasing y
  | some x, some y => x ≼* y
  | some _, none => False

#rocq_ignore option_op_instance "Use CMRA instance"
#rocq_ignore option_pcore_instance "Use CMRA instance"
#rocq_ignore option_valid_instance "Use CMRA instance"
#rocq_ignore option_validN_instance "Use CMRA instance"

namespace Option

/-- The resource algebra on `Option α`. -/
@[reducible] def raBase : RABase (Option α) where
  pcore x := some (optionCore x)
  op := optionOp
  ValidN := optionValidN
  Valid := optionValid
  op_ne.ne n x1 x2 H := by
    rename_i x
    rcases x1, x2, x with ⟨_|_, _|_, _|_⟩ <;> simp_all [op_right_dist]
  pcore_ne {n} x y cx H := by
    simp only [Option.some.injEq]; rintro rfl
    rcases x, y with ⟨_|x, _|y⟩ <;> simp_all [Dist, Option.Forall₂]
    cases Hv : pcore x <;> cases Hv' : pcore y <;> simp only []
    · cases pcore_ne H.symm Hv'; simp_all
    · cases pcore_ne H Hv; simp_all
    · obtain ⟨w, Hw1, Hw2⟩ := pcore_ne H.symm Hv'
      cases Hv.symm.trans Hw1
      exact Hw2.symm
  validN_ne {n} x y H := by
    rcases x, y with ⟨_|_, _|_⟩ <;> simp_all [Dist, Option.Forall₂]
    exact Dist.validN H |>.mp
  valid_iff_validN {x} := by
    rcases x with ⟨_|_⟩ <;> simp [valid_iff_validN]
  validN_succ {x n} := by
    rcases x with ⟨_|_⟩ <;> simp_all [validN_succ]
  validN_op_left {n x y} := by
    rcases x, y with ⟨_|_, _|_⟩ <;> simp_all
    apply validN_op_left
  assoc {x y z} := by
    rcases x, y, z with ⟨_|_, _|_, _|_⟩ <;> first | rfl | exact congrArg some assoc
  comm {x y} := by
    rcases x, y with ⟨_|_, _|_⟩ <;> first | rfl | exact congrArg some comm
  pcore_op_left {x cx} := by
    rcases x, cx with ⟨_|_, _|_⟩ <;> simp_all <;> intro h <;> exact pcore_op_left h
  pcore_idem := by
    rintro (_|x) <;> simp
    rcases H : pcore x with _|y <;> simp
    exact pcore_idem H
  extend {n} := by
    rintro (_|x) (_|mb1) (_|mb2) Hx Hx' <;> simp at Hx' ⊢
    · exists none, none
    · exists none, some x
    · exists some x, none
    · rcases extend Hx Hx' with ⟨mc1, mc2, hx, h1, h2⟩
      exact ⟨some mc1, some mc2, congrArg some hx, h1, h2⟩

/-- The order on `Option α`. -/
@[reducible] def orderN : OrderN (Option α) where
  IncludedN := optionIncludedN
  Included := optionIncluded
  incN_ne {n x x' y y'} ex ey h := by
    rcases x, x', y, y' with ⟨_|x, _|x', _|y, _|y'⟩ <;> simp_all [Dist, Option.Forall₂]
    · exact h.of_dist ey
    · exact OrderN.IncludedNR.ne ex ey h
  incN_succ {n x y} h := by
    rcases x, y with ⟨_|x, _|y⟩ <;> simp_all
    exact OrderN.IncludedNR.succ h
  incN_trans {n x y z} h₁ h₂ := by
    rcases x, y, z with ⟨_|x, _|y, _|z⟩ <;> simp_all
    · exact h₁.of_incNR h₂
    · exact OrderN.IncludedNR.trans h₁ h₂
  inc_trans {x y z} h₁ h₂ := by
    rcases x, y, z with ⟨_|x, _|y, _|z⟩ <;> simp_all
    · exact h₁.of_incR h₂
    · exact OrderN.IncludedR.trans h₁ h₂
  incN_of_inc {x y} n h := by
    rcases x, y with ⟨_|x, _|y⟩ <;> simp_all
    exact OrderN.IncludedR.incNR n h

section
attribute [local instance] raBase orderN

theorem some_incN_some_iff {n} {a b : α} : some a ≼{n} some b ↔ a ≡{n}≡ b ∨ a ≼{n} b :=
  .rfl
theorem some_inc_some_iff {a b : α} : some a ≼ some b ↔ a = b ∨ a ≼ b := .rfl
theorem none_incN_some_iff {n} {b : α} : none ≼{n} some b ↔ Increasing b := .rfl
theorem none_inc_some_iff {b : α} : none ≼ some b ↔ Increasing b := .rfl
theorem not_some_incN_none {n} {a : α} : ¬some a ≼{n} none := id
theorem not_some_inc_none {a : α} : ¬some a ≼ none := id

instance : IncRefl (Option α) where
  inc_refl | none => trivial | some _ => Or.inl rfl

theorem increasing_some_iff {a : α} : Increasing (some a) ↔ Increasing a where
  mp h := h.increasing none
  mpr h := ⟨fun | none => h | some b => Or.inr (h.increasing b)⟩

instance : Increasing (none : Option α) := ⟨fun | none => trivial | some _ => Or.inl rfl⟩

theorem increasing_pcore (x : α) : Increasing (pcore x : Option α) :=
  match h : pcore x with
  | none => inferInstance
  | some _ => increasing_some_iff.mpr (pcore_increasing h)

theorem none_incN_pcore {n} (x : α) : none ≼{n} pcore x :=
  match h : pcore x with
  | none => trivial
  | some _ => pcore_increasing h

theorem none_inc_pcore (x : α) : none ≼ pcore x :=
  match h : pcore x with
  | none => trivial
  | some _ => pcore_increasing h

theorem pcore_incN_pcore {n} {x y : α} (h : x ≼*{n} y) : pcore x ≼{n} pcore y := by
  cases hx : pcore x with
  | none => exact none_incN_pcore y
  | some cx =>
    rcases h with e | i
    · obtain ⟨cy, hcy, ecy⟩ := pcore_ne e hx
      rw [hcy]; exact Or.inl ecy
    · obtain ⟨cy, hcy, icy⟩ := pcore_monoN i hx
      rw [hcy]; exact Or.inr icy

theorem pcore_inc_pcore {x y : α} (h : x ≼* y) : pcore x ≼ pcore y := by
  cases hx : pcore x with
  | none => exact none_inc_pcore y
  | some cx =>
    rcases h with rfl | i
    · rw [hx]
    · obtain ⟨cy, hcy, icy⟩ := pcore_mono i hx
      rw [hcy]; exact Or.inr icy

theorem pcore_inc_pcore_op (x y : α) : (pcore x : Option α) ≼ pcore (x • y) := by
  cases hx : pcore x with
  | none => exact none_inc_pcore _
  | some cx =>
    obtain ⟨cxy, hcxy, i⟩ := pcore_order_op hx y
    rw [hcxy]; exact Or.inr i

@[rocq_alias optionR, rocq_alias option_cmra_mixin]
instance _root_.Iris.cmraOption : CMRA (Option α) where
  toRABase := raBase
  toOrderN := orderN
  op_monoN_left {n x y} z h :=
    match x, y, z, h with
    | none, none, none, _ => trivial
    | none, none, some _, _ => Or.inl .rfl
    | none, some _, none, h => h
    | none, some _, some z, h => Or.inr (Increasing.incN h z)
    | some _, none, _, h => False.elim h
    | some _, some _, none, h => h
    | some _, some _, some z, h => OrderN.IncludedNR.op_left z h
  op_mono_left {x y} z h :=
    match x, y, z, h with
    | none, none, none, _ => trivial
    | none, none, some _, _ => Or.inl rfl
    | none, some _, none, h => h
    | none, some _, some z, h => Or.inr (h.increasing z)
    | some _, none, _, h => False.elim h
    | some _, some _, none, h => h
    | some _, some _, some z, h => OrderN.IncludedR.op_left z h
  validN_of_incN {n x y} h v :=
    match x, y, h with
    | none, _, _ => trivial
    | some _, none, h => False.elim h
    | some _, some _, h => OrderN.IncludedNR.validN h v
  pcore_monoN {n x y _} h := by
    rintro ⟨⟩
    refine ⟨_, rfl, ?_⟩
    match x, y, h with
    | none, none, _ => trivial
    | none, some y, _ => exact none_incN_pcore y
    | some _, none, h => exact False.elim h
    | some x, some y, h => exact pcore_incN_pcore h
  pcore_mono {x y _} h := by
    rintro ⟨⟩
    refine ⟨_, rfl, ?_⟩
    match x, y, h with
    | none, none, _ => trivial
    | none, some y, _ => exact none_inc_pcore y
    | some _, none, h => exact False.elim h
    | some x, some y, h => exact pcore_inc_pcore h
  pcore_order_op {x _} := by
    rintro ⟨⟩ y
    refine ⟨_, rfl, ?_⟩
    match x, y with
    | none, none => trivial
    | none, some y => exact none_inc_pcore y
    | some x, none => exact inc_refl _
    | some x, some y => exact pcore_inc_pcore_op x y
  pcore_increasing {x _} := by
    rintro ⟨⟩
    match x with
    | none => exact (inferInstance : Increasing (none : Option α))
    | some x => exact increasing_pcore x
  increasing_closed {n x y} h h' :=
    match x, y, h' with
    | none, none, _ => inferInstance
    | none, some _, .inl e => False.elim e
    | none, some _, .inr i => increasing_some_iff.mpr i
    | some _, none, .inl e => False.elim e
    | some _, none, .inr i => False.elim i
    | some _, some _, .inl e => increasing_some_iff.mpr ((increasing_some_iff.mp h).of_dist e)
    | some _, some _, .inr i => increasing_some_iff.mpr ((increasing_some_iff.mp h).of_incNR i)
  incN_extend {n x y} v h :=
    match x, y, h with
    | none, none, _ => ⟨none, trivial, .rfl⟩
    | none, some _, h => ⟨none, h, .rfl⟩
    | some _, none, h => False.elim h
    | some _, some y, .inl e => ⟨some y, Or.inl .rfl, e.symm⟩
    | some _, some _, .inr i =>
      let ⟨z, hz, ez⟩ := incN_extend v i
      ⟨some z, Or.inr hz, ez⟩

#rocq_ignore option_unit_instance "Use UCMRA instance"
#rocq_ignore option_ucmra_mixin "Use UCMRA instance"

@[rocq_alias optionUR]
instance _root_.Iris.ucmraOption : UCMRA (Option α) where
  toCMRA := cmraOption
  unit := none
  unit_valid := trivial
  unit_left_id := by rintro ⟨⟩ <;> rfl
  pcore_unit := by rfl
  inc_refl := inc_refl

end

@[rocq_alias Some_op]
theorem some_op (a b : α) : some (a • b) = some a • some b := rfl

@[rocq_alias Some_valid]
theorem some_valid {a : α} : ✓ (some a) ↔ ✓ a := .rfl

@[rocq_alias Some_validN]
theorem some_validN {n} {a : α} : ✓{n} (some a) ↔ ✓{n} a := .rfl

@[rocq_alias pcore_Some]
theorem pcore_some (a : α) :
    CMRA.pcore (some a) = (some (CMRA.pcore a) : Option (Option α)) := rfl

@[rocq_alias Some_core]
theorem some_core [IsTotal α] (a : α) : some (CMRA.core a) = CMRA.core (some a) := by
  simp [CMRA.core, CMRA.pcore, optionCore]
  obtain ⟨c, hc⟩ := IsTotal.total a
  simp [hc]

@[rocq_alias Some_core_id]
instance some_core_id (a : α) [CoreId a] : CoreId (some a : Option α) where
  core_id := by simp [pcore_some]; exact CoreId.core_id

instance none_core_id : CoreId (none : Option α) := ⟨rfl⟩

@[rocq_alias option_core_id]
instance option_core_id (ma : Option α) [∀ x : α, CoreId x] : CoreId ma where
  core_id := by
    rcases ma with _|a
    · rfl
    · exact (some_core_id a).core_id

@[rocq_alias op_None]
theorem op_none_iff (ma mb : Option α) : ma • mb = none ↔ ma = none ∧ mb = none := by
  cases ma <;> cases mb <;> simp [CMRA.op, optionOp]

@[rocq_alias op_is_Some]
theorem op_isSome (ma mb : Option α) : (ma • mb).isSome ↔ ma.isSome ∨ mb.isSome := by
  cases ma <;> cases mb <;> simp [CMRA.op, optionOp]

@[rocq_alias op_None_left_id]
theorem op_none_left_id (a : Option α) : (none : Option α) • a = a := by
  cases a <;> rfl

@[rocq_alias op_None_right_id]
theorem op_none_right_id (a : Option α) : a • (none : Option α) = a := by
  cases a <;> rfl

theorem dist_of_some_dist_some {n} {x y : α} (H : some x ≡{n}≡ some y) : x ≡{n}≡ y := H

theorem eq_none_of_op_eq_none_left {x y : Option α} (h : x • y = none) : x = none := by
  match x, y with
  | none, _ => rfl
  | some _, none => simp [op] at h
  | some _, some _ => simp [op] at h

theorem eq_none_of_op_eq_none_right {x y : Option α} (h : x • y = none) : y = none := by
  match x, y with
  | _, none => rfl
  | none, some _ => simp [op] at h
  | some _, some _ => simp [op] at h

theorem op_some_opM_assoc {x y : α} {mz : Option α} : (x • y) •? mz = x •? (some y • mz) :=
  match mz with | none => rfl | some _ => assoc'.symm

@[rocq_alias Some_op_opM]
theorem some_op_opM {a : α} {ma : Option α} : some a • ma = some (a •? ma) := by
  rcases ma with ⟨_|_⟩ <;> simp [op?, op]

@[rocq_alias cmra_opM_opM_assoc, rocq_alias cmra_opM_opM_assoc_L]
theorem opM_opM_assoc {x : α} {y z : Option α} : (x •? y) •? z = x •? (y • z) := by
  rcases y, z with ⟨_|_, _|_⟩ <;> simp [op?, op, assoc.symm]

@[rocq_alias cmra_opM_opM_swap, rocq_alias cmra_opM_opM_swap_L]
theorem opM_opM_swap {x : α} {y z : Option α} : (x •? y) •? z = (x •? z) •? y :=
  opM_opM_assoc.trans <| (congrArg (x •? ·) CMRA.comm).trans opM_opM_assoc.symm

@[rocq_alias cmra_opM_fmap_Some]
theorem opM_map_some {ma₁ ma₂ : Option α} : ma₁ •? ma₂.map some = ma₁ • ma₂ := by
  rcases ma₁, ma₂ with ⟨_|_, _|_⟩ <;> rfl

theorem op_some_opM_assoc_dist {x y : α} {mz : Option α} : (x • y) •? mz ≡{n}≡ x •? (some y • mz) :=
  match mz with | none => .rfl | some _ => assoc.dist.symm

theorem exists_op_some_eqv_some (x : Option α) (y : α) : ∃ z, x • some y = some z :=
  match x with | .none => ⟨y, rfl⟩ | .some w => ⟨w • y, rfl⟩

theorem exists_op_some_dist_some {n} (x : Option α) (y : α) : ∃ z, x • some y ≡{n}≡ some z :=
  exists_op_some_eqv_some x y |>.elim (⟨·, ·.dist⟩)

theorem not_valid_some_exclN_op_left {n} {x : α} [Exclusive x] {y : α} : ¬✓{n} (some x • some y) :=
  not_valid_exclN_op_left (α := α)

@[rocq_alias exclusiveN_Some_l]
theorem exclusiveN_some_left {n} {a : α} [Exclusive a] {mb : Option α}
    (h : ✓{n} (some a • mb)) : mb = none := by
  cases mb with
  | none => rfl
  | some b => exact (not_valid_some_exclN_op_left h).elim

@[rocq_alias exclusiveN_Some_r]
theorem exclusiveN_some_right {n} {a : α} [Exclusive a] {mb : Option α}
    (h : ✓{n} (mb • some a)) : mb = none :=
  exclusiveN_some_left (CMRA.validN_ne CMRA.op_commN h)

@[rocq_alias exclusive_Some_l]
theorem exclusive_some_left {a : α} [Exclusive a] {mb : Option α}
    (h : ✓ (some a • mb)) : mb = none :=
  exclusiveN_some_left (n := 0) h.validN

@[rocq_alias exclusive_Some_r]
theorem exclusive_some_right {a : α} [Exclusive a] {mb : Option α}
    (h : ✓ (mb • some a)) : mb = none :=
  exclusiveN_some_right (n := 0) h.validN

theorem validN_op_unit {n} {x : Option α} (vx : ✓{n} x) : ✓{n} x • unit := by
  rcases x with ⟨_|_⟩ <;> trivial

/-! ### The order on `Option α` -/

theorem dist_or_incN_of_some_incN_some {n} {a b : α} (h : some a ≼{n} some b) :
    a ≡{n}≡ b ∨ a ≼{n} b := h

theorem some_incN_some_of_dist_or_incN {n} {a b : α} (h : a ≡{n}≡ b ∨ a ≼{n} b) :
    some a ≼{n} some b := h

theorem some_incN_some_of_incN {n} {a b : α} (h : a ≼{n} b) : some a ≼{n} some b := Or.inr h

theorem some_incN_some_of_dist {n} {a b : α} (h : a ≡{n}≡ b) : some a ≼{n} some b := Or.inl h

theorem isSome_of_some_incN {n} {a : α} {mb : Option α} (h : some a ≼{n} mb) : mb.isSome :=
  match mb, h with
  | some _, _ => rfl
  | none, h => False.elim h

theorem eq_or_inc_of_some_inc_some {a b : α} (h : some a ≼ some b) : a = b ∨ a ≼ b := h

theorem some_inc_some_of_eq_or_inc {a b : α} (h : a = b ∨ a ≼ b) : some a ≼ some b := h

theorem some_inc_some_of_inc {a b : α} (h : a ≼ b) : some a ≼ some b := Or.inr h

theorem some_inc_some_of_eq {a b : α} (h : a = b) : some a ≼ some b := Or.inl h

theorem isSome_of_some_inc {a : α} {mb : Option α} (h : some a ≼ mb) : mb.isSome :=
  match mb, h with
  | some _, _ => rfl
  | none, h => False.elim h

theorem isSome_monoN {n} {ma mb : Option α} (h : ma ≼{n} mb) : ma.isSome → mb.isSome := by
  cases ma with
  | none => simp
  | some _ => exact fun _ => isSome_of_some_incN h

theorem isSome_mono {ma mb : Option α} (h : ma ≼ mb) : ma.isSome → mb.isSome := by
  cases ma with
  | none => simp
  | some _ => exact fun _ => isSome_of_some_inc h

theorem inc_of_some_inc_some [IncRefl α] {x y : α} (H : some y ≼ some x) : y ≼ x :=
  Or.elim H (· ▸ inc_refl y) id

theorem incN_of_some_incN_some [IncRefl α] {n} {x y : α} (H : some y ≼{n} some x) :
    y ≼{n} x :=
  Or.elim H Dist.to_incN id

theorem some_inc_some_iff_incRefl [IncRefl α] {a b : α} : some a ≼ some b ↔ a ≼ b :=
  ⟨inc_of_some_inc_some, Or.inr⟩

theorem some_incN_some_iff_incRefl [IncRefl α] {n} {a b : α} :
    some a ≼{n} some b ↔ a ≼{n} b :=
  ⟨incN_of_some_incN_some, Or.inr⟩

theorem validN_of_incN_validN {n} {a b : α} (Hv : ✓{n} a) (Hinc : some b ≼{n} some a) :
    ✓{n} b :=
  validN_of_incN (α := Option α) Hinc Hv

theorem valid_of_inc_valid {a b : α} (Hv : ✓ a) (Hinc : some b ≼ some a) : ✓ b :=
  valid_of_inc (α := Option α) Hinc Hv

/-- Transport a pointwise order-to-extension conversion through `Option`. The conversion is a
plain hypothesis: classical components discharge it with `fun h => h`. -/
theorem incExtN_of_incN {n} {mx my : Option α}
    (hsub : ∀ {n : Nat} {x y : α}, x ≼{n} y → x ≼ₑ{n} y) (h : mx ≼{n} my) : mx ≼ₑ{n} my :=
  match mx, my, h with
  | none, none, _ => ⟨none, .rfl⟩
  | none, some b, _ => ⟨some b, .rfl⟩
  | some _, some _, .inl e => ⟨none, OFE.some_dist_some.mpr e.symm⟩
  | some _, some _, .inr i =>
    let ⟨z, hz⟩ := hsub i
    ⟨some z, OFE.some_dist_some.mpr hz⟩

/-- The limit-level form of `Option.incExtN_of_incN`. -/
theorem incExt_of_inc {mx my : Option α}
    (hsub : ∀ {x y : α}, x ≼ y → x ≼ₑ y) (h : mx ≼ my) : mx ≼ₑ my :=
  match mx, my, h with
  | none, none, _ => ⟨none, rfl⟩
  | none, some b, _ => ⟨some b, rfl⟩
  | some _, some _, .inl e => ⟨none, congrArg some e.symm⟩
  | some _, some _, .inr i =>
    let ⟨z, hz⟩ := hsub i
    ⟨some z, congrArg some hz⟩

instance [Affine α] : Affine (Option α) where
  increasing
    | none => inferInstance
    | some a => increasing_some_iff.mpr (Affine.increasing a)

/-! ### The extension inclusion on `Option α` -/

theorem some_incExt_some_of_dist_opM {n} {x y : α} {mz : Option α} (H : x ≡{n}≡ y •? mz) :
    some y ≼ₑ{n} some x :=
  match mz with | none => ⟨none, H⟩ | some z => ⟨some z, H⟩

theorem incExt_of_some_incExt_some [IsTotal α] {x y : α} (H : some y ≼ₑ some x) :
    y ≼ₑ x :=
  let ⟨mz, hmz⟩ := H
  match mz with
  | none => ⟨core y, (Option.some.inj hmz).trans (op_core y).symm⟩
  | some z => ⟨z, Option.some.inj hmz⟩

theorem incExtN_of_some_incExtN_some [IsTotal α] {n} {x y : α} :
    some y ≼ₑ{n} some x → y ≼ₑ{n} x
  | ⟨none, hmz⟩ => ⟨core y, dist_of_some_dist_some hmz |>.trans (op_core_dist y).symm⟩
  | ⟨some z, hmz⟩ => ⟨z, hmz⟩

@[rocq_alias option_included]
theorem incExt_iff {ma mb : Option α} :
    ma ≼ₑ mb ↔
      ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a = b ∨ a ≼ₑ b) := by
  refine ⟨fun ⟨mc, Hmc⟩ => ?_, ?_⟩
  · rcases ma with _|a
    · exact .inl rfl
    rcases mb with _|b
    · rcases mc with _|c <;> simp [CMRA.op, optionOp] at Hmc
    refine .inr ⟨a, b, rfl, rfl, ?_⟩
    rcases mc with _|c <;> simp [CMRA.op, optionOp] at Hmc
    · exact .inl Hmc.symm
    · exact .inr ⟨c, Hmc⟩
  · rintro (H|⟨_, _, _, _, (H|⟨z, _⟩)⟩) <;> subst_eqs
    · exists mb
    · exists none
    · exists some z

@[rocq_alias option_includedN]
theorem incExtN_iff {n} {ma mb : Option α} :
    ma ≼ₑ{n} mb ↔
      ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a ≡{n}≡ b ∨ a ≼ₑ{n} b) := by
  refine ⟨fun ⟨mc, Hmc⟩ => ?_, ?_⟩
  · rcases ma, mb, mc with ⟨_|_, _|_, _|_⟩ <;> simp_all [op]
    · exact .inl Hmc.symm
    · exact .inr ⟨_, Hmc⟩
  · rintro (H|⟨_, _, _, _, (H|⟨z, _⟩)⟩) <;> subst_eqs
    · exists mb
    · exists none; simp [op]; exact H.symm
    · exists some z

@[rocq_alias option_included_total]
theorem incExt_iff_isTotal [IsTotal α] {ma mb : Option α} :
    ma ≼ₑ mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼ₑ b := by
  rw [incExt_iff]
  constructor
  · rintro (rfl | ⟨a, b, ⟨⟩, ⟨⟩, (Heqv | Hinc)⟩)
    · simp
    · exact .inr ⟨a, b, rfl, rfl, ⟨core a, Heqv.symm.trans (op_core a).symm⟩⟩
    · exact .inr ⟨a, b, rfl, rfl, Hinc⟩
  · rintro (rfl | ⟨a, b, rfl, rfl, Hinc⟩)
    · simp
    · exact .inr ⟨a, b, rfl, rfl, .inr Hinc⟩

@[rocq_alias option_includedN_total]
theorem incExtN_iff_is_total [IsTotal α] {n} {ma mb : Option α} :
    ma ≼ₑ{n} mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼ₑ{n} b := by
  rw [incExtN_iff]
  constructor
  · rintro (rfl | ⟨a, b, ⟨⟩, ⟨⟩, (Heqv | Hinc)⟩)
    · simp
    · exact .inr ⟨a, b, rfl, rfl, ⟨core a, Heqv.symm.trans (op_core_dist a).symm⟩⟩
    · exact .inr ⟨a, b, rfl, rfl, Hinc⟩
  · rintro (rfl | ⟨a, b, rfl, rfl, Hinc⟩)
    · simp
    · exact .inr ⟨a, b, rfl, rfl, .inr Hinc⟩

@[rocq_alias Some_includedN]
theorem some_incExtN_some_iff {n} {a b : α} :
    some a ≼ₑ{n} some b ↔ a ≡{n}≡ b ∨ a ≼ₑ{n} b := by
  apply incExtN_iff.trans; simp

@[rocq_alias Some_includedN_1]
theorem dist_or_incExtN_of_some_incExtN_some {n} {a b : α} (h : some a ≼ₑ{n} some b) :
    a ≡{n}≡ b ∨ a ≼ₑ{n} b := some_incExtN_some_iff.mp h

@[rocq_alias Some_includedN_2]
theorem some_incExtN_some_of_dist_or_incExtN {n} {a b : α} (h : a ≡{n}≡ b ∨ a ≼ₑ{n} b) :
    some a ≼ₑ{n} some b := some_incExtN_some_iff.mpr h

@[rocq_alias Some_includedN_mono]
theorem some_incExtN_some_of_incExtN {n} {a b : α} (h : a ≼ₑ{n} b) : some a ≼ₑ{n} some b :=
  some_incExtN_some_iff.mpr (.inr h)

@[rocq_alias Some_includedN_refl]
theorem some_incExtN_some_of_dist {n} {a b : α} (h : a ≡{n}≡ b) : some a ≼ₑ{n} some b :=
  some_incExtN_some_iff.mpr (.inl h)

@[rocq_alias Some_includedN_is_Some]
theorem isSome_of_some_incExtN {n} {a : α} {mb : Option α} (h : some a ≼ₑ{n} mb) :
    mb.isSome := by
  rcases incExtN_iff.mp h with h | ⟨_, _, _, rfl, _⟩ <;> simp_all

@[rocq_alias Some_included]
theorem some_incExt_some_iff {a b : α} : some a ≼ₑ some b ↔ a = b ∨ a ≼ₑ b := by
  apply incExt_iff.trans; simp

@[rocq_alias Some_included_1]
theorem eq_or_incExt_of_some_incExt_some {a b : α} (h : some a ≼ₑ some b) :
    a = b ∨ a ≼ₑ b :=
  some_incExt_some_iff.mp h

@[rocq_alias Some_included_2]
theorem some_incExt_some_of_eq_or_incExt {a b : α} (h : a = b ∨ a ≼ₑ b) :
    some a ≼ₑ some b :=
  some_incExt_some_iff.mpr h

@[rocq_alias Some_included_mono]
theorem some_incExt_some_of_incExt {a b : α} (h : a ≼ₑ b) : some a ≼ₑ some b :=
  some_incExt_some_iff.mpr (.inr h)

@[rocq_alias Some_included_refl]
theorem some_incExt_some_of_eq {a b : α} (h : a = b) : some a ≼ₑ some b :=
  some_incExt_some_iff.mpr (.inl h)

@[rocq_alias Some_included_is_Some]
theorem isSome_of_some_incExt {a : α} {mb : Option α} (h : some a ≼ₑ mb) : mb.isSome := by
  rcases incExt_iff.mp h with h | ⟨_, _, _, rfl, _⟩ <;> simp_all

@[rocq_alias is_Some_includedN]
theorem isSome_monoN_ext {n} {ma mb : Option α} (h : ma ≼ₑ{n} mb) :
    ma.isSome → mb.isSome := by
  cases ma with
  | none => simp
  | some _ => exact fun _ => isSome_of_some_incExtN h

@[rocq_alias is_Some_included]
theorem isSome_mono_ext {ma mb : Option α} (h : ma ≼ₑ mb) : ma.isSome → mb.isSome := by
  cases ma with
  | none => simp
  | some _ => exact fun _ => isSome_of_some_incExt h

@[rocq_alias Some_included_exclusive]
theorem eqv_of_incExt_exclusive [Exclusive (a : α)] {b : α} (H : some a ≼ₑ some b)
    (Hv : ✓ b) : a = b := by
  rcases incExt_iff.mp H with (Hcontra|H)
  · simp at Hcontra
  · obtain ⟨_, _, ⟨_, _⟩, ⟨_, _⟩, (He|H)⟩ := H
    · exact He
    · exact not_valid_of_excl_incExt H Hv |>.elim

@[rocq_alias Some_includedN_exclusive]
theorem dist_of_incExtN_exclusive [Exclusive (a : α)] {n} {b : α} (H : some a ≼ₑ{n} some b)
    (Hv : ✓{n} b) : a ≡{n}≡ b := by
  rcases incExtN_iff.mp H with (Hcontra|H)
  · simp at Hcontra
  · obtain ⟨_, _, ⟨_, _⟩, ⟨_, _⟩, (_|H)⟩ := H
    · trivial
    · exact not_valid_of_exclN_incExt H Hv |>.elim

@[rocq_alias Some_included_total]
theorem some_incExt_some_iff_is_total [IsTotal α] {a b : α} :
    some a ≼ₑ some b ↔ a ≼ₑ b := by
  apply some_incExt_some_iff.trans
  refine ⟨?_, .inr⟩
  rintro (H|H)
  · exact ⟨_, H.symm.trans (op_core a).symm⟩
  · exact H

@[rocq_alias option_fmap_mono]
theorem map_mono_ext {β : Type _} [CMRA β] (f : α → β) {ma mb : Option α}
    (hf : ∀ x y : α, x ≼ₑ y → f x ≼ₑ f y) (h : ma ≼ₑ mb) :
    ma.map f ≼ₑ mb.map f := by
  rcases incExt_iff.mp h with rfl | ⟨a, b, rfl, rfl, hab⟩
  · exact ⟨mb.map f, by cases mb.map f <;> rfl⟩
  · rcases hab with rfl | hab
    · exact incExt_refl _
    · exact some_incExt_some_iff.mpr (.inr (hf a b hab))

@[rocq_alias Some_includedN_total]
theorem some_incExtN_some_iff_is_total [IsTotal α] {n} {a b : α} :
    some a ≼ₑ{n} some b ↔ a ≼ₑ{n} b := by
  apply some_incExtN_some_iff.trans
  refine ⟨?_, .inr⟩
  rintro (H|H)
  · exact ⟨_, H.symm.trans (CMRA.op_core_dist a).symm⟩
  · exact H

@[rocq_alias cancelable_Some]
instance {a : α} [IdFree a] [Cancelable a] : Cancelable (some a) := by
  refine ⟨@fun n b c Hv He => ?_⟩
  rcases b, c with ⟨_|b, _|c⟩
  · trivial
  · exact id_free0_r c (valid0_of_validN Hv) (He.symm.le <| n.zero_le)
  · refine id_free0_r b ?_ (He.le <| n.zero_le)
    exact valid0_of_validN (He.validN.mp Hv)
  · exact cancelableN (α := α) Hv He

@[rocq_alias option_cancelable]
instance {ma : Option α} [∀ a : α, IdFree a] [∀ a : α, Cancelable a] : Cancelable ma := by
  rcases ma with ⟨_|_⟩
  constructor
  · simp [op]
  · infer_instance

@[rocq_alias cmra_validN_Some_includedN]
theorem validN_of_incExtN_validN {n} {a b : α} (Hv : ✓{n} a) (Hinc : some b ≼ₑ{n} some a) :
    ✓{n} b :=
  validN_of_incExtN (α := Option α) Hinc Hv

@[rocq_alias cmra_valid_Some_included]
theorem valid_of_incExt_valid {a b : α} (Hv : ✓ a) (Hinc : some b ≼ₑ some a) : ✓ b :=
  valid_of_incExt (α := Option α) Hinc Hv

@[rocq_alias Some_included_opM]
theorem some_incExt_some_iff_opM {a b : α} : some a ≼ₑ some b ↔ ∃ mc, b = a •? mc := by
  simp [incExt_iff]
  constructor
  · rintro (Heqv | ⟨mc', Hinc⟩)
    · exact ⟨none, by simpa [CMRA.op?] using Heqv.symm⟩
    · exact ⟨some mc', Hinc⟩
  · rintro ⟨_|z, H⟩
    · exact .inl H.symm
    · exact .inr ⟨z, H⟩

@[rocq_alias Some_includedN_opM]
theorem some_incExtN_some_iff_opM {n} {a b : α} :
    some a ≼ₑ{n} some b ↔ ∃ mc, b ≡{n}≡ a •? mc := by
  simp [incExtN_iff]
  constructor
  · rintro (H|H)
    · exists none; simpa [op?] using H.symm
    · rcases H with ⟨mc', H⟩
      exists (some mc')
  · rintro ⟨(_|z), H⟩
    · exact .inl H.symm
    · right; exists z

@[rocq_alias option_cmra_discrete]
instance [CMRA.Discrete α] : CMRA.Discrete (Option α) where
  discrete_valid {x} :=
    match x with
    | none => fun _ => trivial
    | some _ => discrete_valid (α := α)
  discrete_inc {x y} h :=
    match x, y, h with
    | none, none, _ => trivial
    | none, some _, h => h
    | some _, none, h => False.elim h
    | some _, some _, h =>
      Or.elim h (fun e => Or.inl (OFE.Discrete.discrete_0 e))
        fun i => Or.inr (discrete_inc (α := α) i)

end Option
end option

section unit

#rocq_ignore unit_op_instance "Use CMRA instance"
#rocq_ignore unit_pcore_instance "Use CMRA instance"
#rocq_ignore unit_valid_instance "Use CMRA instance"
#rocq_ignore unit_validN_instance "Use CMRA instance"
#rocq_ignore unit_cancelable "Subsumed by empty_cancelable"
#rocq_ignore unit_core_id "Subsumed by unit_CoreId"

@[rocq_alias unit_cmra_mixin]
instance raBaseUnit : RABase Unit where
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
  assoc := rfl
  comm := rfl
  pcore_op_left _ := rfl
  pcore_idem _ := rfl
  extend _ _ := ⟨(), (), rfl, .rfl, .rfl⟩

instance : RABase.ExtensionLaws Unit where
  pcore_op_mono _ _ := ⟨.unit, rfl⟩

@[rocq_alias unitR]
instance cmraUnit : CMRA Unit := CMRA.withExtensionOrder

#rocq_ignore unit_unit_instance "Use UCMRA instance"
#rocq_ignore unit_ucmra_mixin "Use UCMRA instance"

instance unitalUnit : Unital Unit where
  unit := ()
  unit_valid := ⟨⟩
  unit_left_id := rfl
  pcore_unit := rfl

@[rocq_alias unitUR]
instance ucmraUnit : UCMRA Unit := UCMRA.withExtensionOrder

@[rocq_alias unit_cmra_discrete]
instance : CMRA.Discrete Unit where
  discrete_valid _ := ⟨⟩
  discrete_inc _ := ⟨(), rfl⟩

end unit

section empty

#rocq_ignore Empty_set_op_instance "Use CMRA instance"
#rocq_ignore Empty_set_pcore_instance "Use CMRA instance"
#rocq_ignore Empty_set_valid_instance "Use CMRA instance"
#rocq_ignore Empty_set_validN_instance "Use CMRA instance"
#rocq_ignore Empty_set_cmra_mixin "Use CMRA instance"

instance raBaseEmpty : RABase Empty where
  pcore x := some x
  op x _ := x
  ValidN _ _ := False
  Valid _ := False
  op_ne.ne _ _ _ _ := .rfl
  pcore_ne {_ x} := x.elim
  validN_ne _ := id
  valid_iff_validN {x} := x.elim
  validN_succ := id
  validN_op_left := id
  assoc {x} := x.elim
  comm {x} := x.elim
  pcore_op_left {x} := x.elim
  pcore_idem {x} := x.elim
  extend {_ x} := x.elim

instance : RABase.ExtensionLaws Empty where
  pcore_op_mono {x} := x.elim

@[rocq_alias Empty_setR]
instance cmraEmpty : CMRA Empty := CMRA.withExtensionOrder

@[rocq_alias Empty_set_cmra_discrete]
instance : CMRA.Discrete Empty where
  discrete_valid := id
  discrete_inc {x} := x.elim

@[rocq_alias Empty_set_core_id]
instance (x : Empty) : CMRA.CoreId x where
  core_id := rfl

@[rocq_alias Empty_set_cancelable]
instance (x : Empty) : CMRA.Cancelable x where
  cancelableN := x.elim

end empty

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

abbrev IncludedN n (x y : α × β) := x.fst ≼{n} y.fst ∧ x.snd ≼{n} y.snd

abbrev Included (x y : α × β) := x.fst ≼ y.fst ∧ x.snd ≼ y.snd

#rocq_ignore prod_op_instance "Use CMRA instance"
#rocq_ignore prod_pcore_instance "Use CMRA instance"
#rocq_ignore prod_valid_instance "Use CMRA instance"
#rocq_ignore prod_validN_instance "Use CMRA instance"

/-- The componentwise resource algebra. -/
@[reducible] def raBase : RABase (α × β) where
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
  assoc {x y z} := equiv_prod_ext CMRA.assoc CMRA.assoc
  comm {x y} := equiv_prod_ext CMRA.comm CMRA.comm
  pcore_op_left {x cx} h :=
    let ⟨a, ha, ho⟩ := Option.bind_eq_some_iff.mp h
    let ⟨b, hb, hh⟩ := Option.bind_eq_some_iff.mp ho
    (Option.some.inj hh) ▸
      (equiv_prod_ext (CMRA.pcore_op_left ha) (CMRA.pcore_op_left hb))
  pcore_idem {x cx} h := by
    have ⟨cx₁, hcx₁, this⟩ := Option.bind_eq_some_iff.mp h
    have ⟨cx₂, hcx₂, hcx⟩ := Option.bind_eq_some_iff.mp this
    have ⟨a, ha, ea⟩ := equiv_some (CMRA.pcore_idem hcx₁)
    have ⟨b, hb, eb⟩ := equiv_some (CMRA.pcore_idem hcx₂)
    have g : (a, b) = (cx₁, cx₂) := equiv_prod_ext ea eb
    rw [Option.some.inj hcx.symm]
    simp only [ha, hb, pcore]
    exact congrArg some g
  extend {n x y₁ y₂} := fun ⟨vx₁, vx₂⟩ e =>
    let ⟨z₁, w₁, hx₁, hz₁, hw₁⟩ := CMRA.extend vx₁ (OFE.dist_fst e)
    let ⟨z₂, w₂, hx₂, hz₂, hw₂⟩ := CMRA.extend vx₂ (OFE.dist_snd e)
    ⟨(z₁, z₂), (w₁, w₂), equiv_prod_ext hx₁ hx₂, ⟨hz₁, hz₂⟩, ⟨hw₁, hw₂⟩⟩

/-- The componentwise order. -/
@[reducible] def orderN : OrderN (α × β) where
  IncludedN := IncludedN
  Included := Included
  incN_ne ex ey h :=
    ⟨CMRA.incN_ne (dist_fst ex) (dist_fst ey) h.1, CMRA.incN_ne (dist_snd ex) (dist_snd ey) h.2⟩
  incN_succ h := ⟨CMRA.incN_succ h.1, CMRA.incN_succ h.2⟩
  incN_trans h₁ h₂ := ⟨CMRA.incN_trans h₁.1 h₂.1, CMRA.incN_trans h₁.2 h₂.2⟩
  inc_trans h₁ h₂ := ⟨CMRA.inc_trans h₁.1 h₂.1, CMRA.inc_trans h₁.2 h₂.2⟩
  incN_of_inc n h := ⟨CMRA.incN_of_inc n h.1, CMRA.incN_of_inc n h.2⟩

section
attribute [local instance] raBase orderN

@[rocq_alias prod_pcore_Some, rocq_alias prod_pcore_Some']
theorem pcore_eq_some {x cx : α × β} :
    CMRA.pcore x = some cx ↔ CMRA.pcore x.1 = some cx.1 ∧ CMRA.pcore x.2 = some cx.2 := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ =>
    Option.bind_eq_some_iff.mpr ⟨cx.1, h₁, Option.bind_eq_some_iff.mpr ⟨cx.2, h₂, rfl⟩⟩⟩
  obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  exact ⟨h₁, h₂⟩

theorem increasing_iff {x : α × β} :
    CMRA.Increasing x ↔ CMRA.Increasing x.1 ∧ CMRA.Increasing x.2 :=
  ⟨fun h =>
    ⟨⟨fun y => (h.increasing (y, x.2)).1⟩, ⟨fun y => (h.increasing (x.1, y)).2⟩⟩,
   fun ⟨h₁, h₂⟩ => ⟨fun y => ⟨h₁.increasing y.1, h₂.increasing y.2⟩⟩⟩

theorem incNR_fst {n} {x y : α × β} (h : x ≼*{n} y) : x.1 ≼*{n} y.1 :=
  h.imp dist_fst And.left
theorem incNR_snd {n} {x y : α × β} (h : x ≼*{n} y) : x.2 ≼*{n} y.2 :=
  h.imp dist_snd And.right

@[rocq_alias prodR, rocq_alias prod_cmra_mixin]
instance cmraProd : CMRA (α × β) where
  toRABase := raBase
  toOrderN := orderN
  op_monoN_left z h := ⟨CMRA.op_monoN_left z.1 h.1, CMRA.op_monoN_left z.2 h.2⟩
  op_mono_left z h := ⟨CMRA.op_mono_left z.1 h.1, CMRA.op_mono_left z.2 h.2⟩
  validN_of_incN h v := ⟨CMRA.validN_of_incN h.1 v.1, CMRA.validN_of_incN h.2 v.2⟩
  pcore_monoN h e :=
    let ⟨e₁, e₂⟩ := pcore_eq_some.mp e
    let ⟨cy₁, hcy₁, i₁⟩ := CMRA.pcore_monoN h.1 e₁
    let ⟨cy₂, hcy₂, i₂⟩ := CMRA.pcore_monoN h.2 e₂
    ⟨(cy₁, cy₂), pcore_eq_some.mpr ⟨hcy₁, hcy₂⟩, i₁, i₂⟩
  pcore_mono h e :=
    let ⟨e₁, e₂⟩ := pcore_eq_some.mp e
    let ⟨cy₁, hcy₁, i₁⟩ := CMRA.pcore_mono h.1 e₁
    let ⟨cy₂, hcy₂, i₂⟩ := CMRA.pcore_mono h.2 e₂
    ⟨(cy₁, cy₂), pcore_eq_some.mpr ⟨hcy₁, hcy₂⟩, i₁, i₂⟩
  pcore_order_op e y :=
    let ⟨e₁, e₂⟩ := pcore_eq_some.mp e
    let ⟨cxy₁, h₁, i₁⟩ := CMRA.pcore_order_op e₁ y.1
    let ⟨cxy₂, h₂, i₂⟩ := CMRA.pcore_order_op e₂ y.2
    ⟨(cxy₁, cxy₂), pcore_eq_some.mpr ⟨h₁, h₂⟩, i₁, i₂⟩
  pcore_increasing e :=
    let ⟨e₁, e₂⟩ := pcore_eq_some.mp e
    increasing_iff.mpr ⟨CMRA.pcore_increasing e₁, CMRA.pcore_increasing e₂⟩
  increasing_closed h h' :=
    let ⟨h₁, h₂⟩ := increasing_iff.mp h
    increasing_iff.mpr
      ⟨CMRA.increasing_closed h₁ (incNR_fst h'), CMRA.increasing_closed h₂ (incNR_snd h')⟩
  incN_extend v h :=
    let ⟨z₁, h₁, e₁⟩ := CMRA.incN_extend v.1 h.1
    let ⟨z₂, h₂, e₂⟩ := CMRA.incN_extend v.2 h.2
    ⟨(z₁, z₂), ⟨h₁, h₂⟩, dist_prod_ext e₁ e₂⟩

end

theorem valid_fst {x : α × β} (h : ✓ x) : ✓ x.fst := h.left
theorem valid_snd {x : α × β} (h : ✓ x) : ✓ x.snd := h.right

theorem validN_fst {n} {x : α × β} (h : ✓{n} x) : ✓{n} x.fst := h.left
theorem validN_snd {n} {x : α × β} (h : ✓{n} x) : ✓{n} x.snd := h.right

@[rocq_alias pair_op]
theorem mk_op_mk (a a' : α) (b b' : β) : (a, b) • (a', b') = (a • a', b • b') := rfl

@[rocq_alias pair_valid]
theorem mk_valid (a : α) (b : β) : ✓ (a, b) ↔ ✓ a ∧ ✓ b := .rfl

@[rocq_alias pair_validN]
theorem mk_validN {n} (a : α) (b : β) : ✓{n} (a, b) ↔ ✓{n} a ∧ ✓{n} b := .rfl

@[rocq_alias pair_pcore]
theorem mk_pcore (a : α) (b : β) :
    CMRA.pcore (a, b) = (CMRA.pcore a).bind fun c₁ => (CMRA.pcore b).bind fun c₂ => some (c₁, c₂) :=
  rfl

@[rocq_alias pair_core]
theorem mk_core [CMRA.IsTotal α] [CMRA.IsTotal β] (a : α) (b : β) :
    CMRA.core (a, b) = (CMRA.core a, CMRA.core b) :=
  congrArg (Option.getD · (a, b))
    (pcore_eq_some.mpr ⟨CMRA.pcore_eq_core a, CMRA.pcore_eq_core b⟩)

theorem inc_def {x y : α × β} : x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2 := .rfl

theorem incN_def {n} {x y : α × β} : x ≼{n} y ↔ x.1 ≼{n} y.1 ∧ x.2 ≼{n} y.2 := .rfl

theorem mk_inc_mk (a a' : α) (b b' : β) : (a, b) ≼ (a', b') ↔ a ≼ a' ∧ b ≼ b' := .rfl

theorem mk_incN_mk {n} (a a' : α) (b b' : β) :
    (a, b) ≼{n} (a', b') ↔ a ≼{n} a' ∧ b ≼{n} b' := .rfl

/-- Transport pointwise order-to-extension conversions through the product. The conversions
are plain hypotheses: classical components discharge them with `fun h => h`. -/
theorem incExtN_of_incN {n} {x y : α × β}
    (hsub₁ : ∀ {n : Nat} {a b : α}, a ≼{n} b → a ≼ₑ{n} b)
    (hsub₂ : ∀ {n : Nat} {a b : β}, a ≼{n} b → a ≼ₑ{n} b)
    (h : x ≼{n} y) : x ≼ₑ{n} y :=
  let ⟨z₁, hz₁⟩ := hsub₁ h.1
  let ⟨z₂, hz₂⟩ := hsub₂ h.2
  ⟨(z₁, z₂), ⟨hz₁, hz₂⟩⟩

/-- The limit-level form of `Prod.incExtN_of_incN`. -/
theorem incExt_of_inc {x y : α × β}
    (hsub₁ : ∀ {a b : α}, a ≼ b → a ≼ₑ b)
    (hsub₂ : ∀ {a b : β}, a ≼ b → a ≼ₑ b)
    (h : x ≼ y) : x ≼ₑ y :=
  let ⟨z₁, hz₁⟩ := hsub₁ h.1
  let ⟨z₂, hz₂⟩ := hsub₂ h.2
  ⟨(z₁, z₂), Prod.ext hz₁ hz₂⟩

@[rocq_alias prod_included]
theorem incExt_def {x y : α × β} : x ≼ₑ y ↔ x.1 ≼ₑ y.1 ∧ x.2 ≼ₑ y.2 :=
  ⟨fun ⟨z, hz⟩ => ⟨⟨z.1, congrArg Prod.fst hz⟩, ⟨z.2, congrArg Prod.snd hz⟩⟩,
   fun ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ => ⟨(z₁, z₂), Prod.ext hz₁ hz₂⟩⟩

@[rocq_alias prod_includedN]
theorem incExtN_def {n} {x y : α × β} :
    x ≼ₑ{n} y ↔ x.1 ≼ₑ{n} y.1 ∧ x.2 ≼ₑ{n} y.2 :=
  ⟨fun ⟨z, hz⟩ => ⟨⟨z.1, dist_fst hz⟩, ⟨z.2, dist_snd hz⟩⟩,
   fun ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ => ⟨(z₁, z₂), dist_prod_ext hz₁ hz₂⟩⟩

@[rocq_alias pair_included]
theorem mk_incExt_mk (a a' : α) (b b' : β) :
    (a, b) ≼ₑ (a', b') ↔ a ≼ₑ a' ∧ b ≼ₑ b' := incExt_def

@[rocq_alias pair_includedN]
theorem mk_incExtN_mk {n} (a a' : α) (b b' : β) :
    (a, b) ≼ₑ{n} (a', b') ↔ a ≼ₑ{n} a' ∧ b ≼ₑ{n} b' := incExtN_def

@[rocq_alias prod_cmra_total]
instance instIsTotalProd [CMRA.IsTotal α] [CMRA.IsTotal β] : CMRA.IsTotal (α × β) where
  total x :=
    let ⟨ca, ha⟩ := CMRA.total x.1
    let ⟨cb, hb⟩ := CMRA.total x.2
    ⟨(ca, cb), pcore_eq_some.mpr ⟨ha, hb⟩⟩

@[rocq_alias prod_cmra_discrete]
instance instCmraDiscreteProd [CMRA.Discrete α] [CMRA.Discrete β] : CMRA.Discrete (α × β) where
  discrete_valid v := ⟨CMRA.discrete_valid v.1, CMRA.discrete_valid v.2⟩
  discrete_inc h := ⟨CMRA.discrete_inc h.1, CMRA.discrete_inc h.2⟩

instance [IncRefl α] [IncRefl β] : IncRefl (α × β) where
  inc_refl x := ⟨CMRA.inc_refl x.1, CMRA.inc_refl x.2⟩

instance [CMRA.Affine α] [CMRA.Affine β] : CMRA.Affine (α × β) where
  increasing x := increasing_iff.mpr ⟨CMRA.Affine.increasing x.1, CMRA.Affine.increasing x.2⟩

@[rocq_alias pair_core_id]
instance instCoreIdPair {x : α} {y : β} [CMRA.CoreId x] [CMRA.CoreId y] :
    CMRA.CoreId (x, y) where
  core_id := pcore_eq_some.mpr ⟨CMRA.CoreId.core_id, CMRA.CoreId.core_id⟩

@[rocq_alias pair_exclusive_l]
instance instExclusivePairLeft {x : α} [CMRA.Exclusive x] {y : β} :
    CMRA.Exclusive (x, y) where
  exclusive0_l z hv := CMRA.exclusive0_l z.1 hv.1

@[rocq_alias pair_exclusive_r]
instance instExclusivePairRight {x : α} {y : β} [CMRA.Exclusive y] :
    CMRA.Exclusive (x, y) where
  exclusive0_l z hv := CMRA.exclusive0_l z.2 hv.2

@[rocq_alias pair_cancelable]
instance instCancelablePair {x : α} {y : β} [CMRA.Cancelable x] [CMRA.Cancelable y] :
    CMRA.Cancelable (x, y) where
  cancelableN hv he := ⟨CMRA.cancelableN hv.1 he.1, CMRA.cancelableN hv.2 he.2⟩

@[rocq_alias pair_id_free_l]
instance instIdFreePairLeft {x : α} [CMRA.IdFree x] {y : β} :
    CMRA.IdFree (x, y) where
  id_free0_r z hv he := CMRA.id_free0_r z.1 hv.1 he.1

@[rocq_alias pair_id_free_r]
instance instIdFreePairRight {x : α} {y : β} [CMRA.IdFree y] :
    CMRA.IdFree (x, y) where
  id_free0_r z hv he := CMRA.id_free0_r z.2 hv.2 he.2

end Prod

section ProdUnit
namespace Prod

variable {α β : Type _} [UCMRA α] [UCMRA β]

#rocq_ignore prod_unit_instance "Use UCMRA instance"
#rocq_ignore prod_ucmra_mixin "Use UCMRA instance"

@[rocq_alias prodUR]
instance ucmraProd : UCMRA (α × β) where
  unit := (UCMRA.unit, UCMRA.unit)
  unit_valid := ⟨UCMRA.unit_valid, UCMRA.unit_valid⟩
  unit_left_id := Prod.ext UCMRA.unit_left_id UCMRA.unit_left_id
  pcore_unit := pcore_eq_some.mpr ⟨UCMRA.pcore_unit, UCMRA.pcore_unit⟩
  inc_refl x := ⟨CMRA.inc_refl x.1, CMRA.inc_refl x.2⟩

@[rocq_alias pair_split, rocq_alias pair_split_L]
theorem mk_split (a : α) (b : β) : (a, b) = ((a, UCMRA.unit) : α × β) • (UCMRA.unit, b) :=
  Prod.ext CMRA.unit_right_id.symm CMRA.unit_left_id.symm

@[rocq_alias pair_op_1, rocq_alias pair_op_1_L]
theorem mk_op_fst (a a' : α) :
    ((a • a', UCMRA.unit) : α × β) = ((a, UCMRA.unit) : α × β) • (a', UCMRA.unit) :=
  Prod.ext rfl CMRA.unit_left_id.symm

@[rocq_alias pair_op_2, rocq_alias pair_op_2_L]
theorem mk_op_snd (b b' : β) :
    ((UCMRA.unit, b • b') : α × β) = ((UCMRA.unit, b) : α × β) • (UCMRA.unit, b') :=
  Prod.ext CMRA.unit_left_id.symm rfl

end Prod
end ProdUnit

section OptionProd

open CMRA RABase Option

variable {α β : Type _} [CMRA α] [CMRA β]

namespace Option

theorem some_mk_incN {n} {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) :
    some a₁ ≼{n} some a₂ ∧ some b₁ ≼{n} some b₂ :=
  Or.elim h (fun e => ⟨Or.inl e.1, Or.inl e.2⟩) fun i => ⟨Or.inr i.1, Or.inr i.2⟩

theorem some_mk_incN_left {n} {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) :
    some a₁ ≼{n} some a₂ := (some_mk_incN h).1

theorem some_mk_incN_right {n} {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) :
    some b₁ ≼{n} some b₂ := (some_mk_incN h).2

theorem some_mk_inc {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ some (a₂, b₂)) :
    some a₁ ≼ some a₂ ∧ some b₁ ≼ some b₂ :=
  Or.elim h (fun e => ⟨Or.inl (congrArg Prod.fst e), Or.inl (congrArg Prod.snd e)⟩)
    fun i => ⟨Or.inr i.1, Or.inr i.2⟩

theorem some_mk_inc_left {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ some (a₂, b₂)) :
    some a₁ ≼ some a₂ := (some_mk_inc h).1

theorem some_mk_inc_right {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ some (a₂, b₂)) :
    some b₁ ≼ some b₂ := (some_mk_inc h).2

@[rocq_alias Some_pair_includedN]
theorem some_mk_incExtN {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ₑ{n} some (a₂, b₂)) :
    some a₁ ≼ₑ{n} some a₂ ∧ some b₁ ≼ₑ{n} some b₂ := by
  rcases some_incExtN_some_iff.mp h with hd | hi
  · exact ⟨some_incExtN_some_of_dist hd.1, some_incExtN_some_of_dist hd.2⟩
  · have ⟨h₁, h₂⟩ := Prod.incExtN_def.mp hi
    exact ⟨some_incExtN_some_of_incExtN h₁, some_incExtN_some_of_incExtN h₂⟩

@[rocq_alias Some_pair_includedN_l]
theorem some_mk_incExtN_left {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ₑ{n} some (a₂, b₂)) : some a₁ ≼ₑ{n} some a₂ :=
  (some_mk_incExtN h).1

@[rocq_alias Some_pair_includedN_r]
theorem some_mk_incExtN_right {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ₑ{n} some (a₂, b₂)) : some b₁ ≼ₑ{n} some b₂ :=
  (some_mk_incExtN h).2

@[rocq_alias Some_pair_includedN_total_1]
theorem some_mk_incExtN_total_fst [IsTotal α] {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ₑ{n} some (a₂, b₂)) :
    a₁ ≼ₑ{n} a₂ ∧ some b₁ ≼ₑ{n} some b₂ :=
  let ⟨h₁, h₂⟩ := some_mk_incExtN h
  ⟨some_incExtN_some_iff_is_total.mp h₁, h₂⟩

@[rocq_alias Some_pair_includedN_total_2]
theorem some_mk_incExtN_total_snd [IsTotal β] {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ₑ{n} some (a₂, b₂)) :
    some a₁ ≼ₑ{n} some a₂ ∧ b₁ ≼ₑ{n} b₂ :=
  let ⟨h₁, h₂⟩ := some_mk_incExtN h
  ⟨h₁, some_incExtN_some_iff_is_total.mp h₂⟩

@[rocq_alias Some_pair_included]
theorem some_mk_incExt {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ₑ some (a₂, b₂)) :
    some a₁ ≼ₑ some a₂ ∧ some b₁ ≼ₑ some b₂ := by
  rcases some_incExt_some_iff.mp h with he | hi
  · exact ⟨some_incExt_some_of_eq (congrArg Prod.fst he),
      some_incExt_some_of_eq (congrArg Prod.snd he)⟩
  · have ⟨h₁, h₂⟩ := Prod.incExt_def.mp hi
    exact ⟨some_incExt_some_of_incExt h₁, some_incExt_some_of_incExt h₂⟩

@[rocq_alias Some_pair_included_l]
theorem some_mk_incExt_left {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ₑ some (a₂, b₂)) : some a₁ ≼ₑ some a₂ :=
  (some_mk_incExt h).1

@[rocq_alias Some_pair_included_r]
theorem some_mk_incExt_right {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ₑ some (a₂, b₂)) : some b₁ ≼ₑ some b₂ :=
  (some_mk_incExt h).2

@[rocq_alias Some_pair_included_total_1]
theorem some_mk_incExt_total_fst [IsTotal α] {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ₑ some (a₂, b₂)) :
    a₁ ≼ₑ a₂ ∧ some b₁ ≼ₑ some b₂ :=
  let ⟨h₁, h₂⟩ := some_mk_incExt h
  ⟨some_incExt_some_iff_is_total.mp h₁, h₂⟩

@[rocq_alias Some_pair_included_total_2]
theorem some_mk_incExt_total_snd [IsTotal β] {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ₑ some (a₂, b₂)) :
    some a₁ ≼ₑ some a₂ ∧ b₁ ≼ₑ b₂ :=
  let ⟨h₁, h₂⟩ := some_mk_incExt h
  ⟨h₁, some_incExt_some_iff_is_total.mp h₂⟩

end Option
end OptionProd

section OptionMor

open CMRA

variable {α β : Type _} [CMRA α] [CMRA β]

@[rocq_alias option_fmap_cmra_morphism]
def Option.mapC (f : α -C> β) : Option α -C> Option β where
  toHom := optionMap f.toHom
  validN {_ x} h := by cases x with | none => trivial | some a => exact f.validN h
  pcore x := by
    cases x with | none => rfl | some a => exact congrArg some (f.pcore a)
  op x y := by
    cases x <;> cases y <;> try rfl
    exact congrArg some (f.op ..)
  monoN {n x y} h :=
    match x, y, h with
    | none, none, _ => trivial
    | none, some _, h => f.increasing h
    | some _, none, h => False.elim h
    | some _, some _, h => Or.elim h (fun e => Or.inl (f.ne.ne e)) fun i => Or.inr (f.monoN i)
  mono {x y} h :=
    match x, y, h with
    | none, none, _ => trivial
    | none, some _, h => f.increasing h
    | some _, none, h => False.elim h
    | some _, some _, h => Or.elim h (fun e => Or.inl (congrArg f e)) fun i => Or.inr (f.mono i)
  increasing {x} h :=
    match x, h with
    | none, _ => (inferInstance : Increasing (none : Option β))
    | some _, h => Option.increasing_some_iff.mpr (f.increasing (Option.increasing_some_iff.mp h))

end OptionMor

section ProdMor

open CMRA

variable [CMRA A] [CMRA A'] [CMRA B] [CMRA B']

@[rocq_alias prod_map_cmra_morphism]
def Prod.mapC (f : A -C> A') (g : B -C> B') : A × B -C> A' × B' where
  f := Prod.map f g
  ne := inferInstance
  validN {n x} := fun ⟨h1, h2⟩ => ⟨Hom.validN _ h1, Hom.validN _ h2⟩
  pcore x := by
    simp [Option.map, Prod.map, CMRA.pcore, pcore]
    have h2 := Hom.pcore g x.snd
    have h1 := Hom.pcore f x.fst
    cases _ : CMRA.pcore x.fst
    · cases _ : CMRA.pcore (f.f x.fst) <;> simp_all
    · cases _ : CMRA.pcore x.snd <;>
      cases _ : CMRA.pcore (f.f x.fst) <;>
      cases _ : CMRA.pcore (g.f x.snd) <;>
      simp_all
  op x y := equiv_prod_ext (f.op x.fst y.fst) (g.op x.snd y.snd)
  monoN h := ⟨f.monoN h.1, g.monoN h.2⟩
  mono h := ⟨f.mono h.1, g.mono h.2⟩
  increasing h :=
    Prod.increasing_iff.mpr
      ⟨f.increasing (Prod.increasing_iff.mp h).1, g.increasing (Prod.increasing_iff.mp h).2⟩

end ProdMor

section ProdRF

open RFunctor

@[rocq_alias prodRF]
instance instRFunctorProdOF [RFunctor F1] [RFunctor F2] : RFunctor (ProdOF F1 F2) where
  map f g := Prod.mapC (map f g) (map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ :=
    Prod.map_ne (fun _ => map_ne.ne Hx Hy _) (fun _ => map_ne.ne Hx Hy _)
  map_id _ := equiv_prod_ext (map_id _) (map_id _)
  map_comp _ _ _ _ _ :=
    equiv_prod_ext (map_comp _ _ _ _ _) (map_comp _ _ _ _ _)

instance [RFunctor F1] [RFunctor F2] [RFunctorAffine F1] [RFunctorAffine F2] :
    RFunctorAffine (ProdOF F1 F2) where
  affine := inferInstance

@[rocq_alias prodRF_contractive]
instance instRFunctorContractiveProdOF
    [RFunctorContractive F1] [RFunctorContractive F2] :
    RFunctorContractive (ProdOF F1 F2) where
  map_contractive.1 H _ :=
    Prod.map_ne (fun _ => RFunctorContractive.map_contractive.1 H _)
      (fun _ => RFunctorContractive.map_contractive.1 H _)

@[rocq_alias prodURF]
instance instURFunctorProdOF [URFunctor F1] [URFunctor F2] : URFunctor (ProdOF F1 F2) where
  map f g := Prod.mapC (URFunctor.map f g) (URFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ :=
    Prod.map_ne (fun _ => URFunctor.map_ne.ne Hx Hy _) (fun _ => URFunctor.map_ne.ne Hx Hy _)
  map_id _ := equiv_prod_ext (URFunctor.map_id _) (URFunctor.map_id _)
  map_comp _ _ _ _ _ :=
    equiv_prod_ext (URFunctor.map_comp _ _ _ _ _) (URFunctor.map_comp _ _ _ _ _)

@[rocq_alias prodURF_contractive]
instance instURFunctorContractiveProdOF
    [URFunctorContractive F1] [URFunctorContractive F2] :
    URFunctorContractive (ProdOF F1 F2) where
  map_contractive.1 H _ :=
    Prod.map_ne (fun _ => URFunctorContractive.map_contractive.1 H _)
      (fun _ => URFunctorContractive.map_contractive.1 H _)

end ProdRF

section optionOF

variable {F : COFE.OFunctorPre}

@[rocq_alias optionURF]
instance urFunctorOptionOF [RFunctor F] : URFunctor (OptionOF F) where
  cmra := ucmraOption
  map f g := Option.mapC (RFunctor.map f g)
  map_ne.ne := COFE.OFunctor.map_ne.ne
  map_id x := COFE.OFunctor.map_id x
  map_comp f g f' g' x := COFE.OFunctor.map_comp f g f' g' x

instance [RFunctor F] [RFunctorAffine F] : RFunctorAffine (OptionOF F) where
  affine := inferInstance

@[rocq_alias optionURF_contractive]
instance urFunctorContractiveOptionOF
    [RFunctorContractive F] : URFunctorContractive (OptionOF F) where
  map_contractive.1 := COFE.OFunctorContractive.map_contractive.1

#rocq_ignore optionRF "Provided by `URFunctor.toRFunctor` from `urFunctorOptionOF`."
#rocq_ignore optionRF_contractive
  "Provided by `URFunctorContractive.toRFunctorContractive` from `urFunctorContractiveOptionOF`."

end optionOF

section CmraMixin

namespace RABase

variable {α β : Type _}

/-- Constructing a resource algebra `β` through a mapping into a resource algebra `α`.

The mapping may restrict the domain (i.e., we have an injection from `β` to `α`, not a
bijection) and validity. These two restrictions work on opposite "ends" of `α` according to
`≼ₑ`: domain restriction must prove that when an element is in the domain, so is its
composition with other elements; validity restriction must prove that if the composition of
two elements is valid, then so are both of the elements. The "domain" is the image of `g` in
`α`, or equivalently the part of `α` where `f` returns `some`. -/
@[reducible, rocq_alias inj_cmra_mixin_restrict_validity]
def ofInjRestrictValidity [RABase α] [OFE β]
    (pcore : β → Option β) (op : β → β → β) (Valid : β → Prop) (ValidN : Nat → β → Prop)
    (f : α → Option β) (g : β → α)
    -- `g` is non-expansive and injective w.r.t. OFE equality
    (g_dist : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ ↔ g y₁ ≡{n}≡ g y₂)
    -- `g` is surjective into the part of `α` where `f` returns `some`, and `f` is its inverse
    (gf_dist : ∀ (x : α) (y : β) n, f x ≡{n}≡ some y ↔ g y ≡{n}≡ x)
    -- `g` commutes with `pcore` (where it is defined) and with `op`
    (g_pcore_dist : ∀ (y cy : β) n,
      pcore y ≡{n}≡ some cy ↔ CMRA.pcore (g y) ≡{n}≡ some (g cy))
    (g_op : ∀ y₁ y₂, g (op y₁ y₂) = g y₁ • g y₂)
    -- the validity predicate on `β` restricts the one on `α`
    (g_validN : ∀ n (y : β), ValidN n y → ✓{n} (g y))
    -- the validity predicate on `β` satisfies the laws of validity
    (validN_ne : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ → ValidN n y₁ → ValidN n y₂)
    (valid_validN : ∀ y : β, Valid y ↔ ∀ n, ValidN n y)
    (validN_le : ∀ n n' (y : β), ValidN n y → n' ≤ n → ValidN n' y)
    (validN_op_left : ∀ n (y₁ y₂ : β), ValidN n (op y₁ y₂) → ValidN n y₁) :
    RABase β :=
  have g_ne : ∀ {n} {y₁ y₂ : β}, y₁ ≡{n}≡ y₂ → g y₁ ≡{n}≡ g y₂ := (g_dist ..).mp
  have g_eq : ∀ {y₁ y₂ : β}, y₁ = y₂ ↔ g y₁ = g y₂ :=
    eq_dist.trans <| (forall_congr' fun n => g_dist n _ _).trans eq_dist.symm
  have g_pcore : ∀ {y cy : β}, pcore y = some cy ↔ CMRA.pcore (g y) = some (g cy) :=
    eq_dist.trans <| (forall_congr' fun n => g_pcore_dist _ _ n).trans eq_dist.symm
  have gf : ∀ {x : α} {y : β}, f x = some y ↔ g y = x :=
    eq_dist.trans <| (forall_congr' fun n => gf_dist _ _ n).trans eq_dist.symm
  { pcore, op, Valid, ValidN
    op_ne.ne _ _ _ h := (g_dist ..).mpr <|
      (g_op ..).dist.trans <| (g_ne h).op_r.trans (g_op ..).symm.dist
    pcore_ne h hcy :=
      let ⟨c, hc, hcd⟩ := CMRA.pcore_ne (g_ne h) (g_pcore.mp hcy)
      dist_some <| (g_pcore_dist ..).mpr <| hc.dist.trans <| some_dist_some.mpr hcd.symm
    validN_ne h hv := validN_ne _ _ _ h hv
    valid_iff_validN := valid_validN _
    validN_succ hv := validN_le _ _ _ hv (Nat.le_succ _)
    validN_op_left hv := validN_op_left _ _ _ hv
    assoc := g_eq.mpr <| by
      simp only [g_op]
      exact CMRA.assoc
    comm := g_eq.mpr <| (g_op ..).trans <| CMRA.comm.trans (g_op ..).symm
    pcore_op_left h := g_eq.mpr <| (g_op ..).trans <| CMRA.pcore_op_left (g_pcore.mp h)
    pcore_idem h := g_pcore.mpr <| CMRA.pcore_idem (g_pcore.mp h)
    extend := fun hv he => by
      obtain ⟨x₁, x₂, hx, hx₁, hx₂⟩ :=
        CMRA.extend (g_validN _ _ hv) (((g_dist ..).mp he).trans (g_op ..).dist)
      obtain ⟨w₁, hw₁, hd₁⟩ := distSome ((gf_dist ..).mpr hx₁.symm)
      obtain ⟨w₂, hw₂, hd₂⟩ := distSome ((gf_dist ..).mpr hx₂.symm)
      refine ⟨w₁, w₂, g_eq.mpr ?_, hd₁.symm, hd₂.symm⟩
      rw [g_op, gf.mp hw₁, gf.mp hw₂]
      exact hx }

/-- `RABase.ofInjRestrictValidity` inherits the extension laws of `α`, provided `g` commutes
with `opM` when the right-hand side is produced by `f`, cancelling it. -/
theorem ofInjRestrictValidity_extensionLaws [RABase α] [ExtensionLaws α] [OFE β]
    (pcore : β → Option β) (op : β → β → β) (Valid : β → Prop) (ValidN : Nat → β → Prop)
    (f : α → Option β) (g : β → α)
    (g_dist : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ ↔ g y₁ ≡{n}≡ g y₂)
    (gf_dist : ∀ (x : α) (y : β) n, f x ≡{n}≡ some y ↔ g y ≡{n}≡ x)
    (g_pcore_dist : ∀ (y cy : β) n,
      pcore y ≡{n}≡ some cy ↔ CMRA.pcore (g y) ≡{n}≡ some (g cy))
    (g_op : ∀ y₁ y₂, g (op y₁ y₂) = g y₁ • g y₂)
    (g_opM_f : ∀ (x : α) (y : β), g ((f x).elim y (op y)) = g y • x)
    (g_validN : ∀ n (y : β), ValidN n y → ✓{n} (g y))
    (validN_ne : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ → ValidN n y₁ → ValidN n y₂)
    (valid_validN : ∀ y : β, Valid y ↔ ∀ n, ValidN n y)
    (validN_le : ∀ n n' (y : β), ValidN n y → n' ≤ n → ValidN n' y)
    (validN_op_left : ∀ n (y₁ y₂ : β), ValidN n (op y₁ y₂) → ValidN n y₁) :
    @ExtensionLaws β (ofInjRestrictValidity pcore op Valid ValidN f g g_dist gf_dist
      g_pcore_dist g_op g_validN validN_ne valid_validN validN_le validN_op_left) :=
  letI := ofInjRestrictValidity pcore op Valid ValidN f g g_dist gf_dist g_pcore_dist g_op
    g_validN validN_ne valid_validN validN_le validN_op_left
  have g_pcore : ∀ {y cy : β}, pcore y = some cy ↔ CMRA.pcore (g y) = some (g cy) :=
    eq_dist.trans <| (forall_congr' fun n => g_pcore_dist _ _ n).trans eq_dist.symm
  ⟨fun {y cy} h z => by
    obtain ⟨c, hc⟩ := pcore_op_mono (g_pcore.mp h) (g z)
    obtain ⟨w, hw⟩ : ∃ w, (f c).elim cy (op cy) = op cy w :=
      match f c with
      | some w => ⟨w, rfl⟩
      | none => ⟨cy, (CMRA.pcore_op_left (CMRA.pcore_idem h)).symm⟩
    rw [← g_op, ← g_opM_f c cy, hw] at hc
    exact ⟨w, g_pcore.mpr hc⟩⟩

/-- Constructing a resource algebra through an isomorphism that may restrict validity. -/
@[reducible, rocq_alias iso_cmra_mixin_restrict_validity]
def ofIsoRestrictValidity [RABase α] [OFE β]
    (pcore : β → Option β) (op : β → β → β) (Valid : β → Prop) (ValidN : Nat → β → Prop)
    (f : α → β) (g : β → α)
    -- `g` is non-expansive and injective w.r.t. OFE equality
    (g_dist : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ ↔ g y₁ ≡{n}≡ g y₂)
    -- `g` is surjective, and `f` is its inverse
    (gf : ∀ x : α, g (f x) = x)
    -- `g` commutes with `pcore` and with `op`
    (g_pcore : ∀ y : β, CMRA.pcore (g y) = (pcore y).map g)
    (g_op : ∀ y₁ y₂, g (op y₁ y₂) = g y₁ • g y₂)
    -- the validity predicate on `β` restricts the one on `α`
    (g_validN : ∀ n (y : β), ValidN n y → ✓{n} (g y))
    -- the validity predicate on `β` satisfies the laws of validity
    (validN_ne : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ → ValidN n y₁ → ValidN n y₂)
    (valid_validN : ∀ y : β, Valid y ↔ ∀ n, ValidN n y)
    (validN_le : ∀ n n' (y : β), ValidN n y → n' ≤ n → ValidN n' y)
    (validN_op_left : ∀ n (y₁ y₂ : β), ValidN n (op y₁ y₂) → ValidN n y₁) :
    RABase β :=
  ofInjRestrictValidity pcore op Valid ValidN (fun x => some (f x)) g g_dist
    (fun x y n => ⟨fun h => ((g_dist ..).mp h.symm).trans (gf x).dist,
      fun h => (g_dist ..).mpr <| (gf x).dist.trans h.symm⟩)
    (fun y cy n => by
      rw [g_pcore]
      cases pcore y with
      | none => simp
      | some z => exact g_dist n z cy)
    g_op g_validN validN_ne valid_validN validN_le validN_op_left

/-- `RABase.ofIsoRestrictValidity` inherits the extension laws of `α`. -/
theorem ofIsoRestrictValidity_extensionLaws [RABase α] [ExtensionLaws α] [OFE β]
    (pcore : β → Option β) (op : β → β → β) (Valid : β → Prop) (ValidN : Nat → β → Prop)
    (f : α → β) (g : β → α)
    (g_dist : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ ↔ g y₁ ≡{n}≡ g y₂)
    (gf : ∀ x : α, g (f x) = x)
    (g_pcore : ∀ y : β, CMRA.pcore (g y) = (pcore y).map g)
    (g_op : ∀ y₁ y₂, g (op y₁ y₂) = g y₁ • g y₂)
    (g_validN : ∀ n (y : β), ValidN n y → ✓{n} (g y))
    (validN_ne : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ → ValidN n y₁ → ValidN n y₂)
    (valid_validN : ∀ y : β, Valid y ↔ ∀ n, ValidN n y)
    (validN_le : ∀ n n' (y : β), ValidN n y → n' ≤ n → ValidN n' y)
    (validN_op_left : ∀ n (y₁ y₂ : β), ValidN n (op y₁ y₂) → ValidN n y₁) :
    @ExtensionLaws β (ofIsoRestrictValidity pcore op Valid ValidN f g g_dist gf g_pcore g_op
      g_validN validN_ne valid_validN validN_le validN_op_left) :=
  ofInjRestrictValidity_extensionLaws pcore op Valid ValidN (fun x => some (f x)) g g_dist _ _
    g_op (fun x y => (g_op y (f x)).trans <| congrArg (g y • ·) (gf x))
    g_validN validN_ne valid_validN validN_le validN_op_left

/-- Constructing a resource algebra through an isomorphism. -/
@[reducible, rocq_alias iso_cmra_mixin]
def ofIso [RABase α] [OFE β]
    (pcore : β → Option β) (op : β → β → β) (Valid : β → Prop) (ValidN : Nat → β → Prop)
    (f : α → β) (g : β → α)
    -- `g` is non-expansive and injective w.r.t. OFE equality
    (g_dist : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ ↔ g y₁ ≡{n}≡ g y₂)
    -- `g` is surjective, and `f` is its inverse
    (gf : ∀ x : α, g (f x) = x)
    -- `g` commutes with `pcore`, `op`, `Valid` and `ValidN`
    (g_pcore : ∀ y : β, CMRA.pcore (g y) = (pcore y).map g)
    (g_op : ∀ y₁ y₂, g (op y₁ y₂) = g y₁ • g y₂)
    (g_valid : ∀ y : β, ✓ (g y) ↔ Valid y)
    (g_validN : ∀ n (y : β), ✓{n} (g y) ↔ ValidN n y) :
    RABase β :=
  ofIsoRestrictValidity pcore op Valid ValidN f g g_dist gf g_pcore g_op
    (fun n y => (g_validN n y).mpr)
    (fun n y₁ y₂ h hv =>
      (g_validN n y₂).mp <| CMRA.validN_ne ((g_dist ..).mp h) <| (g_validN n y₁).mpr hv)
    (fun y => (g_valid y).symm.trans <|
      CMRA.valid_iff_validN.trans <| forall_congr' fun n => g_validN n y)
    (fun n n' y hv hle => (g_validN n' y).mp <| CMRA.validN_of_le hle <| (g_validN n y).mpr hv)
    (fun n y₁ y₂ hv => (g_validN n y₁).mp <| CMRA.validN_op_left <|
      g_op y₁ y₂ ▸ (g_validN n (op y₁ y₂)).mpr hv)

/-- `RABase.ofIso` inherits the extension laws of `α`. -/
theorem ofIso_extensionLaws [RABase α] [ExtensionLaws α] [OFE β]
    (pcore : β → Option β) (op : β → β → β) (Valid : β → Prop) (ValidN : Nat → β → Prop)
    (f : α → β) (g : β → α)
    (g_dist : ∀ n (y₁ y₂ : β), y₁ ≡{n}≡ y₂ ↔ g y₁ ≡{n}≡ g y₂)
    (gf : ∀ x : α, g (f x) = x)
    (g_pcore : ∀ y : β, CMRA.pcore (g y) = (pcore y).map g)
    (g_op : ∀ y₁ y₂, g (op y₁ y₂) = g y₁ • g y₂)
    (g_valid : ∀ y : β, ✓ (g y) ↔ Valid y)
    (g_validN : ∀ n (y : β), ✓{n} (g y) ↔ ValidN n y) :
    @ExtensionLaws β (ofIso pcore op Valid ValidN f g g_dist gf g_pcore g_op g_valid g_validN) :=
  ofIsoRestrictValidity_extensionLaws pcore op Valid ValidN f g g_dist gf g_pcore g_op _ _ _ _ _

@[reducible, rocq_alias discrete_cmra_mixin]
def ofDiscrete [OFE α] [OFE.Discrete α]
    (pcore : α → Option α) (op : α → α → α) (Valid : α → Prop)
    (assoc : ∀ x y z : α, op x (op y z) = op (op x y) z)
    (comm : ∀ x y : α, op x y = op y x)
    (pcore_op_left : ∀ x cx : α, pcore x = some cx → op cx x = x)
    (pcore_idem : ∀ x cx : α, pcore x = some cx → pcore cx = some cx)
    (valid_op_left : ∀ x y : α, Valid (op x y) → Valid x) :
    RABase α where
  pcore := pcore
  op := op
  ValidN _ := Valid
  Valid := Valid
  op_ne.ne _ _ _ h := (congrArg (op _) (OFE.discrete h)).dist
  pcore_ne h hcx := ⟨_, (OFE.discrete h) ▸ hcx, .rfl⟩
  validN_ne h hv := (OFE.discrete h) ▸ hv
  valid_iff_validN := (forall_const Nat).symm
  validN_succ := id
  validN_op_left := valid_op_left _ _
  assoc := assoc ..
  comm := comm ..
  pcore_op_left := pcore_op_left _ _
  pcore_idem := pcore_idem _ _
  extend _ h := ⟨_, _, OFE.discrete h, .rfl, .rfl⟩

@[reducible, rocq_alias ra_total_mixin]
def ofDiscreteTotal [OFE α] [OFE.Discrete α]
    (core : α → α) (op : α → α → α) (Valid : α → Prop)
    (assoc : ∀ x y z : α, op x (op y z) = op (op x y) z)
    (comm : ∀ x y : α, op x y = op y x)
    (core_op_left : ∀ x : α, op (core x) x = x)
    (core_idem : ∀ x : α, core (core x) = core x)
    (valid_op_left : ∀ x y : α, Valid (op x y) → Valid x) :
    RABase α :=
  ofDiscrete (fun x => some (core x)) op Valid assoc comm
    (fun _ _ h => Option.some.inj h ▸ core_op_left _)
    (fun _ _ h => Option.some.inj h ▸ congrArg some (core_idem _))
    valid_op_left

section OfDiscrete

@[rocq_alias discrete_cmra_discrete]
instance ofDiscrete_discrete [OFE α] [OFE.Discrete α] (pcore : α → Option α)
    (op : α → α → α) (Valid : α → Prop) h₁ h₂ h₃ h₄ h₅
    [H : @ExtensionLaws α (ofDiscrete pcore op Valid h₁ h₂ h₃ h₄ h₅)] :
    @CMRA.Discrete α
      (@CMRA.withExtensionOrder α (ofDiscrete pcore op Valid h₁ h₂ h₃ h₄ h₅) H) :=
  letI := ofDiscrete pcore op Valid h₁ h₂ h₃ h₄ h₅
  letI := CMRA.withExtensionOrder (α := α)
  { discrete_valid := id
    discrete_inc := incExt_of_incExt0 }

end OfDiscrete

end RABase
end CmraMixin
