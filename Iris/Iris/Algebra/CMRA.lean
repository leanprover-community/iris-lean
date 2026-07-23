/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Сухарик (@suhr), Markus de Medeiros, Puming Liu
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.Monoid
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris
open OFE

@[rocq_alias cmra]
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

  assoc : op x (op y z) = op (op x y) z
  comm : op x y = op y x

  pcore_op_left : pcore x = some cx → op cx x = x
  pcore_idem : pcore x = some cx → pcore cx = some cx
  pcore_op_mono : pcore x = some cx → ∀ y, ∃ cy, pcore (op x y) = some (op cx cy)

  extend : ValidN n x → x ≡{n}≡ op y₁ y₂ →
    Σ' z₁ z₂, x = op z₁ z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂

#rocq_ignore Op "Use the CMRA.op field."
#rocq_ignore PCore "Use the CMRA.pcore field."
#rocq_ignore Valid "Use the CMRA.Valid field."
#rocq_ignore ValidN "Use the CMRA.ValidN field."
#rocq_ignore CmraMixin "Use the CMRA type class."
#rocq_ignore cmra_mixin_of' "Not needed."
#rocq_ignore cmra_ofeO "Not needed."

/-- Reduction of `pcore_op_mono` to regular monotonicity -/
theorem pcore_op_mono_of_core_op_mono [OFE α] (op : α → α → α) (pcore : α → Option α)
    (h : (∀ x cx y : α, (∃ z, y = op x z) → pcore x = some cx →
      ∃ cy, pcore y = some cy ∧ ∃ z, cy = op cx z))
    (x cx) (e : pcore x = some cx) (y) : ∃ cy, pcore (op x y) = some (op cx cy) :=
  have ⟨_, hcy, z, hz⟩ := h x cx (op x y) ⟨y, rfl⟩ e
  ⟨z, hcy.trans (congrArg some hz)⟩

namespace CMRA
variable [CMRA α]

/-- The CMRA composition operation. -/
infix:60 " • " => op

/-- The inclusion order on a CMRA. -/
@[rocq_alias included]
def Included (x y : α) : Prop := ∃ z, y = x • z
@[inherit_doc]
infix:50 " ≼ " => Included

/-- The step-indexed inclusion order on a CMRA. -/
@[rocq_alias includedN]
def IncludedN (n : Nat) (x y : α) : Prop := ∃ z, y ≡{n}≡ x • z
@[inherit_doc] notation:50 x " ≼{" n "} " y:51 => IncludedN n x y

/-- The CMRA composition operation with an optional right argument. -/
@[rocq_alias opM]
def op? [CMRA α] (x : α) : Option α → α
  | some y => x • y
  | none => x
@[inherit_doc] infix:60 " •? " => op?

/-- The validity of a CMRA element. -/
prefix:50 "✓ " => Valid
/-- The step-indexed validity of a CMRA element. -/
notation:50 "✓{" n "} " x:51 => ValidN n x

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

@[rocq_alias CmraTotal]
class IsTotal (α : Type _) [CMRA α] where
  total (x : α) : ∃ cx, pcore x = some cx
export IsTotal (total)

#rocq_ignore cmra_total_mixin "Use CMRA + IsTotal"

@[rocq_alias core]
def core (x : α) := (pcore x).getD x

@[rocq_alias CmraDiscrete]
class Discrete (α : Type _) [CMRA α] extends OFE.Discrete α where
  discrete_valid {x : α} : ✓{0} x → ✓ x
export Discrete (discrete_valid)
#rocq_ignore discrete_cmra_discrete "Folded into Lean's CMRA.Discrete typeclass"
#rocq_ignore discrete_cmra_mixin "Lean uses the CMRA + CMRA.Discrete typeclasses directly."
#rocq_ignore discrete_validN_instance "Use CMRA instance"

end CMRA

@[rocq_alias ucmra]
class UCMRA (α : Type _) extends CMRA α where
  unit : α
  unit_valid : ✓ unit
  unit_left_id : unit • x = x
  pcore_unit : pcore unit = some unit

#rocq_ignore Unit "Lean uses the UCMRA.unit field; no separate class needed."
#rocq_ignore UcmraMixin "Lean uses the UCMRA type class directly; mixin/bundle separation is unnecessary."
#rocq_ignore ucmra_cmraR "Folded into Lean's UCMRA extends CMRA."
#rocq_ignore ucmra_ofeO "Folded into Lean's UCMRA → OFE."

class IsUnit [CMRA α] (ε : α) : Prop where
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

@[rocq_alias cmra_assoc]
theorem assoc' {x y z : α} : x • (y • z) = (x • y) • z := CMRA.assoc

@[rocq_alias cmra_comm]
theorem comm' {x y : α} : x • y = y • x := CMRA.comm

@[rocq_alias cmra_pcore_l]
theorem pcore_l {x cx : α} (e : pcore x = some cx) : cx • x = x := CMRA.pcore_op_left e

@[rocq_alias cmra_pcore_idemp]
theorem pcore_idemp {x cx : α} (e : pcore x = some cx) : pcore cx = some cx :=
  CMRA.pcore_idem e

@[rocq_alias cmra_extend]
def extend' {n} {x y₁ y₂ : α} (v : ✓{n} x) (e : x ≡{n}≡ y₁ • y₂) :
    Σ' z₁ z₂, x = (z₁ • z₂ : α) ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ :=
  let ⟨z₁, z₂, hx, hz, hw⟩ := extend (y₁ := y₁) (y₂ := y₂) v e
  ⟨z₁, z₂, hx, hz, hw⟩

@[rocq_alias cmra_validN_op_l]
theorem validN_op_l {n} {x y : α} : ✓{n} (x • y) → ✓{n} x := CMRA.validN_op_left

@[rocq_alias cmra_valid_validN]
theorem valid_validN {x : α} : ✓ x ↔ ∀ n, ✓{n} x := CMRA.valid_iff_validN

@[rocq_alias cmra_op_ne]
theorem op_ne' {x : α} : NonExpansive (x • ·) := CMRA.op_ne

@[rocq_alias cmra_pcore_ne]
theorem pcore_ne' {n} {x y : α} {cx} (h : x ≡{n}≡ y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy := CMRA.pcore_ne h e

@[rocq_alias cmra_validN_ne]
theorem validN_ne' {n} {x y : α} (h : x ≡{n}≡ y) : ✓{n} x → ✓{n} y := CMRA.validN_ne h

theorem opM_ne_right {n} {x : α} {y₁ y₂ : Option α} (h : y₁ ≡{n}≡ y₂) : x •? y₁ ≡{n}≡ x •? y₂ :=
  match y₁, y₂, h with
  | none, none, _ => .rfl
  | some _, some _, h => CMRA.op_ne.ne h

@[rocq_alias cmra_opM_ne]
instance : NonExpansive₂ (op? (α := α)) where
  ne _ _ _ e₁ y₁ y₂ e₂ :=
    match y₁, y₂, e₂ with
    | none, none, _ => e₁
    | some _, some _, e₂ =>
      (CMRA.op_ne.ne e₂).trans (Dist.of_eq comm |>.trans <|
        (CMRA.op_ne.ne e₁).trans (Dist.of_eq comm))

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

theorem coreId_of_eqv {x₁ x₂ : α} (e : x₁ ≡ x₂) (h : CoreId x₁) : CoreId x₂ where
  core_id := calc
    pcore x₂ = pcore x₁ := (NonExpansive.eqv e.symm).to_eq
    _        = some x₁  := h.core_id
    _        = some x₂  := congrArg some e.to_eq

@[rocq_alias CoreId_proper]
theorem coreId_iff {x₁ x₂ : α} (e : x₁ ≡ x₂) : CoreId x₁ ↔ CoreId x₂ :=
  ⟨coreId_of_eqv e, coreId_of_eqv e.symm⟩

/-! ## Op -/

theorem op_right_eqv (x : α) {y z : α} (e : y ≡ z) : x • y ≡ x • z := op_ne.eqv e
theorem _root_.Iris.OFE.Equiv.op_r {x y z : α} : y ≡ z → x • y ≡ x • z := op_right_eqv _

theorem op_right_dist (x : α) {y z : α} (e : y ≡{n}≡ z) : x • y ≡{n}≡ x • z :=
  op_ne.ne e
theorem _root_.Iris.OFE.Dist.op_r {x y z : α} : y ≡{n}≡ z → x • y ≡{n}≡ x • z := op_right_dist _

theorem op_commN {x y : α} : x • y ≡{n}≡ y • x := Dist.of_eq comm

theorem op_assocN {x y z : α} : x • (y • z) ≡{n}≡ (x • y) • z := Dist.of_eq assoc

theorem op_left_eqv {x y : α} (z : α) (e : x ≡ y) : x • z ≡ y • z :=
  (Equiv.of_eq comm').trans <| e.op_r.trans (Equiv.of_eq comm')
theorem _root_.Iris.OFE.Equiv.op_l {x y z : α} : x ≡ y → x • z ≡ y • z := op_left_eqv _

theorem op_left_dist {x y : α} (z : α) (e : x ≡{n}≡ y) : x • z ≡{n}≡ y • z :=
  op_commN.trans <| e.op_r.trans op_commN
theorem _root_.Iris.OFE.Dist.op_l {x y z : α} : x ≡{n}≡ y → x • z ≡{n}≡ y • z := op_left_dist _

theorem _root_.Iris.OFE.Dist.op {x x' y y' : α}
    (ex : x ≡{n}≡ x') (ey : y ≡{n}≡ y') : x • y ≡{n}≡ x' • y' := ex.op_l.trans ey.op_r

@[rocq_alias cmra_op_proper']
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

@[rocq_alias cmra_op_opM_assoc]
theorem op_opM_assoc (x y : α) (mz : Option α) : (x • y) •? mz = x • (y •? mz) := by
  unfold op?; cases mz <;> simp [assoc]

theorem op_opM_assoc_dist (x y : α) (mz : Option α) : (x • y) •? mz ≡{n}≡ x • (y •? mz) := by
  unfold op?; cases mz <;> simp [op_assocN, Dist.symm]


/-! ## Validity -/

theorem Valid.validN : ✓ (x : α) → ✓{n} x := (valid_iff_validN.1 · _)

theorem valid_mapN {x y : α} (f : ∀ n, ✓{n} x → ✓{n} y) (v : ✓ x) : ✓ y :=
  valid_iff_validN.mpr fun n => f n v.validN

theorem validN_of_eqv {x y : α} : x ≡ y → ✓{n} x → ✓{n} y :=
  fun e v => validN_ne (equiv_dist.mp e n) v

@[rocq_alias cmra_validN_ne']
theorem validN_dist_iff {x y : α} (e : x ≡{n}≡ y) : ✓{n} x ↔ ✓{n} y := ⟨validN_ne e, validN_ne e.symm⟩
theorem _root_.Iris.OFE.Dist.validN : (x : α) ≡{n}≡ y → (✓{n} x ↔ ✓{n} y) := validN_dist_iff

@[rocq_alias cmra_validN_proper]
theorem validN_eqv_iff {x y : α} (e : x ≡ y) : ✓{n} x ↔ ✓{n} y :=
  validN_dist_iff (equiv_dist.mp e n)

theorem valid_of_eqv {x y : α} : x ≡ y → ✓ x → ✓ y :=
  fun e => valid_mapN fun _ => validN_of_eqv e

@[rocq_alias cmra_valid_proper]
theorem valid_iff {x y : α} (e : x ≡ y) : ✓ x ↔ ✓ y := ⟨valid_of_eqv e, valid_of_eqv e.symm⟩
theorem _root_.Iris.OFE.Equiv.valid : (x : α) ≡ y → (✓ x ↔ ✓ y) := valid_iff

@[rocq_alias cmra_validN_le]
theorem validN_of_le {n n'} {x : α} (le : n' ≤ n) : ✓{n} x → ✓{n'} x :=
  le.recOn id fun  _ ih vs => ih (validN_succ vs)

@[rocq_alias cmra_validN_lt]
theorem validN_of_lt {n n'} {x : α} (lt : n' < n): ✓{n} x → ✓{n'} x :=
  validN_of_le (Nat.le_of_lt lt)

theorem valid0_of_validN {n} {x : α} : ✓{n} x → ✓{0} x := validN_of_le (Nat.zero_le n)

@[rocq_alias cmra_validN_op_r]
theorem validN_op_right {n} {x y : α} : ✓{n} (x • y) → ✓{n} y :=
  fun v => validN_op_left (validN_of_eqv (Equiv.of_eq comm') v)

@[rocq_alias cmra_valid_op_r]
theorem valid_op_right (x y : α) : ✓ (x • y) → ✓ y :=
  valid_mapN fun _ => validN_op_right

@[rocq_alias cmra_valid_op_l]
theorem valid_op_left {x y : α} : ✓ (x • y) → ✓ x :=
  fun v => valid_op_right y x (valid_of_eqv (Equiv.of_eq comm') v)

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

@[rocq_alias cmra_pcore_proper]
theorem pcore_proper {x y : α} (cx : α) (e : x ≡ y) (ps : pcore x = some cx)
    : ∃ cy, pcore y = some cy ∧ cx ≡ cy := by
  let ⟨cy, hcy, ecy⟩ := pcore_ne (equiv_dist.mp e 0) ps
  refine ⟨cy, hcy, ?_⟩
  have (n : Nat) : cx ≡{n}≡ cy :=
    let ⟨cy', hcy', ecy'⟩ := pcore_ne (equiv_dist.mp e n) ps
    have : cy' = cy := Option.some_inj.mp (hcy' ▸ hcy)
    this ▸ ecy'
  exact equiv_dist.mpr this

@[rocq_alias cmra_op_ne']
instance cmra_op_ne2 : NonExpansive₂ (op (α := α)) where
  ne _ _ _ e₁ _ _ e₂ := e₁.op e₂

@[rocq_alias cmra_pcore_proper']
theorem pcore_proper' {x y : α} (e : x ≡ y) : pcore x ≡ pcore y :=
  NonExpansive.eqv e

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
  validN_op_right (validN_of_eqv (Equiv.of_eq (pcore_op_right e).symm) v)

@[rocq_alias cmra_pcore_valid]
theorem pcore_valid {x : α} {cx} (e : pcore x = some cx) : ✓ x → ✓ cx :=
  valid_mapN fun _ => pcore_validN e

/-! ## Exclusive elements -/

@[rocq_alias exclusiveN_l]
theorem not_valid_exclN_op_left {n} {x : α} [Exclusive x] {y} : ¬✓{n} (x • y) :=
  n.recOn (Exclusive.exclusive0_l _) fun _ ih => ih ∘ validN_succ

@[rocq_alias exclusiveN_r]
theorem not_valid_exclN_op_right {n} {x : α} [Exclusive x] {y} : ¬✓{n} (y • x) :=
  fun v => not_valid_exclN_op_left (validN_of_eqv (Equiv.of_eq comm') v)

@[rocq_alias exclusive_l]
theorem not_valid_excl_op_left {x : α} [Exclusive x] {y} : ¬✓ (x • y) :=
  fun v => Exclusive.exclusive0_l _ v.validN

@[rocq_alias exclusive_r]
theorem not_excl_op_right {x : α} [Exclusive x] {y} : ¬✓ (y • x) :=
  fun v => not_valid_excl_op_left (valid_of_eqv (Equiv.of_eq comm') v)

@[rocq_alias exclusiveN_opM]
theorem none_of_excl_valid_op {n} {x : α} [Exclusive x] {my} : ✓{n} (x •? my) → my = none := by
  cases my <;> simp [op?, not_valid_exclN_op_left]

@[rocq_alias exclusive_includedN]
theorem not_valid_of_exclN_inc {n} {x : α} [Exclusive x] {y} : x ≼{n} y → ¬✓{n} y
  | ⟨_, hz⟩, v => not_valid_exclN_op_left (validN_ne hz v)

@[rocq_alias exclusive_included]
theorem not_valid_of_excl_inc {x : α} [Exclusive x] {y} : x ≼ y → ¬✓ y
  | ⟨_, hz⟩, v => Exclusive.exclusive0_l _ <| validN_of_eqv (Equiv.of_eq hz) v.validN

theorem Exclusive.of_eqv {x₁ x₂ : α} (e : x₁ ≡ x₂) (h : Exclusive x₁) : Exclusive x₂ where
  exclusive0_l y := h.exclusive0_l y ∘ e.op_l.dist.validN.2

@[rocq_alias Exclusive_proper]
theorem exclusive_iff {x₁ x₂ : α} (e : x₁ ≡ x₂) : Exclusive x₁ ↔ Exclusive x₂ :=
  ⟨.of_eqv e, .of_eqv e.symm⟩
theorem _root_.Iris.OFE.Dist.exclusive {x₁ x₂ : α} : x₁ ≡ x₂ → (Exclusive x₁ ↔ Exclusive x₂) :=
  exclusive_iff

/-! ## Order -/

theorem inc_of_eqv_of_inc (e : (a : α) ≡ b) : b ≼ c → a ≼ c
  | ⟨t, et⟩ => ⟨t, et.trans e.symm.op_l.to_eq⟩

instance : Trans Equiv (Included (α := α)) Included where
  trans := inc_of_eqv_of_inc

theorem inc_of_inc_of_eqv : (a : α) ≼ b → b ≡ c → a ≼ c
  | ⟨t, et⟩, e => ⟨t, e.symm.to_eq.trans et⟩

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

@[rocq_alias cmra_included_includedN]
theorem incN_of_inc (n) {x y : α} : x ≼ y → x ≼{n} y
  | ⟨z, hz⟩ => ⟨z, hz.dist⟩
theorem Included.incN {n} {x y : α} : x ≼ y → x ≼{n} y := incN_of_inc _

theorem inc_iff_left (e : (a : α) ≡ b) : a ≼ c ↔ b ≼ c :=
  ⟨inc_of_eqv_of_inc e.symm, inc_of_eqv_of_inc e⟩
theorem _root_.Iris.OFE.Equiv.inc_l : (a : α) ≡ b → (a ≼ c ↔ b ≼ c) := inc_iff_left

theorem inc_iff_right (e : (b : α) ≡ c) : a ≼ b ↔ a ≼ c :=
  ⟨(inc_of_inc_of_eqv · e), (inc_of_inc_of_eqv · e.symm)⟩
theorem _root_.Iris.OFE.Equiv.inc_r : (b : α) ≡ c → (a ≼ b ↔ a ≼ c) := inc_iff_right

@[rocq_alias cmra_included_proper]
theorem inc_iff (ea : (a : α) ≡ a') (eb : (b : α) ≡ b') : a ≼ b ↔ a' ≼ b' :=
  (inc_iff_left ea).trans (inc_iff_right eb)
theorem _root_.Iris.OFE.Equiv.inc : (a : α) ≡ a' → b ≡ b' → (a ≼ b ↔ a' ≼ b') := inc_iff

theorem incN_iff_left (e : (a : α) ≡{n}≡ b) : a ≼{n} c ↔ b ≼{n} c :=
  ⟨incN_of_dist_of_incN e.symm, incN_of_dist_of_incN e⟩
theorem _root_.Iris.OFE.Dist.incN_l : (a : α) ≡{n}≡ b → (a ≼{n} c ↔ b ≼{n} c) := incN_iff_left

theorem incN_iff_right (e : (b : α) ≡{n}≡ c) : a ≼{n} b ↔ a ≼{n} c :=
  ⟨(incN_of_incN_of_dist · e), (incN_of_incN_of_dist · e.symm)⟩
theorem _root_.Iris.OFE.Dist.incN_r : (b : α) ≡{n}≡ c → (a ≼{n} b ↔ a ≼{n} c) := incN_iff_right

@[rocq_alias cmra_includedN_ne]
theorem incN_dist_iff (ea : (a : α) ≡{n}≡ a') (eb : (b : α) ≡{n}≡ b') : a ≼{n} b ↔ a' ≼{n} b' :=
  (incN_iff_left ea).trans (incN_iff_right eb)
theorem _root_.Iris.OFE.Dist.incN :
    (a : α) ≡{n}≡ a' → b ≡{n}≡ b' → (a ≼{n} b ↔ a' ≼{n} b') := incN_dist_iff

@[rocq_alias cmra_includedN_proper]
theorem incN_eqv_iff (ea : (a : α) ≡ a') (eb : (b : α) ≡ b') : a ≼{n} b ↔ a' ≼{n} b' :=
  incN_dist_iff ea.dist eb.dist

@[rocq_alias cmra_included_trans]
theorem inc_trans {x y z : α} : x ≼ y → y ≼ z → x ≼ z
  | ⟨w, (hw : y = x • w)⟩, ⟨t, (ht : z = y • t)⟩ =>
    suffices h : z = x • (w • t) from ⟨w • t, h⟩
    calc
      z = y • t := ht
      _ = (x • w) • t := congrArg (· • t) hw
      _ = x • (w • t) := assoc.symm
theorem Included.trans : (x : α) ≼ y → y ≼ z → x ≼ z := inc_trans

instance : Trans (Included (α := α)) Included Included where
  trans := inc_trans

@[rocq_alias cmra_includedN_trans]
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

@[rocq_alias cmra_valid_included]
theorem valid_of_inc {x y : α} : x ≼ y → ✓ y → ✓ x
  | ⟨_, hz⟩, v => valid_op_left (valid_of_eqv (Equiv.of_eq hz) v)

@[rocq_alias cmra_validN_includedN]
theorem validN_of_incN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne hz v)
theorem IncludedN.validN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x := validN_of_incN

@[rocq_alias cmra_validN_included]
theorem validN_of_inc {n} {x y : α} : x ≼ y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne hz.dist v)
theorem Included.validN {n} {x y : α} : x ≼ y → ✓{n} y → ✓{n} x := validN_of_inc

@[rocq_alias cmra_includedN_le]
theorem incN_of_incN_le {n n'} {x y : α} (l1 : n' ≤ n) : x ≼{n} y → x ≼{n'} y
  | ⟨z, hz⟩ => ⟨z, Dist.le hz l1⟩
theorem inc0_of_incN {n} {x y : α} : x ≼{n} y → x ≼{0} y := incN_of_incN_le (Nat.zero_le n)
theorem IncludedN.le {n n'} {x y : α} : n' ≤ n → x ≼{n} y → x ≼{n'} y := incN_of_incN_le

@[rocq_alias cmra_includedN_S]
theorem incN_of_incN_succ {n} {x y : α} : x ≼{n.succ} y → x ≼{n} y :=
  incN_of_incN_le (Nat.le_succ n)
theorem IncludedN.succ {n} {x y : α} : x ≼{n.succ} y → x ≼{n} y := incN_of_incN_succ

@[rocq_alias cmra_includedN_l]
theorem incN_op_left (n) (x y : α) : x ≼{n} x • y := ⟨y, Dist.rfl⟩

@[rocq_alias cmra_included_l]
theorem inc_op_left (x y : α) : x ≼ x • y := ⟨y, rfl⟩

@[rocq_alias cmra_included_r]
theorem inc_op_right (x y : α) : y ≼ x • y := ⟨x, comm⟩

@[rocq_alias cmra_includedN_r]
theorem incN_op_right (n) (x y : α) : y ≼{n} x • y :=
  (inc_op_right x y).elim fun z hz => ⟨z, hz.dist⟩

@[rocq_alias cmra_pcore_mono]
theorem pcore_mono {x y : α} : x ≼ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ cy
  | ⟨_, hw⟩, e =>
    have ⟨z, hz⟩ := pcore_op_mono e _
    let ⟨t, ht, et⟩ := OFE.equiv_some ((congrArg pcore hw).trans hz)
    ⟨t, ht, z, et⟩

@[rocq_alias cmra_pcore_mono']
theorem pcore_mono' {x y : α} {cx} (le : x ≼ y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼ cy :=
  pcore_mono le e

@[rocq_alias cmra_pcore_monoN']
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

@[rocq_alias cmra_included_pcore]
theorem pcore_inc_self {x : α} {cx} (e : pcore x = some cx) : cx ≼ x :=
  ⟨x, (pcore_op_left e).symm⟩

@[rocq_alias cmra_mono_l]
theorem op_mono_right {x y} (z : α) : x ≼ y → z • x ≼ z • y
  | ⟨w, hw⟩ => ⟨w, (congrArg (z • ·) hw).trans assoc⟩

@[rocq_alias cmra_monoN_l]
theorem op_monoN_right {n x y} (z : α) : x ≼{n} y → z • x ≼{n} z • y
  | ⟨w, hw⟩ => ⟨w, hw.op_r.trans op_assocN⟩

@[rocq_alias cmra_monoN_r]
theorem op_monoN_left {n x y} (z : α) (h : x ≼{n} y) : x • z ≼{n} y • z :=
  (op_commN.incN op_commN).1 (op_monoN_right z h)

@[rocq_alias cmra_mono_r]
theorem op_mono_left {x y} (z : α) (h : x ≼ y) : x • z ≼ y • z :=
  ((Equiv.of_eq comm').inc (Equiv.of_eq comm')).1 (op_mono_right z h)

@[rocq_alias cmra_monoN]
theorem op_monoN {n} {x x' y y' : α} (hx : x ≼{n} x') (hy : y ≼{n} y') : x • y ≼{n} x' • y' :=
  (op_monoN_left _ hx).trans (op_monoN_right _ hy)

#rocq_ignore cmra_monoN' "Use cmra_monoN"

@[rocq_alias cmra_mono]
theorem op_mono {x x' y y' : α} (hx : x ≼ x') (hy : y ≼ y') : x • y ≼ x' • y' :=
  (op_mono_left _ hx).trans (op_mono_right _ hy)

#rocq_ignore cmra_mono' "Use cmra_mono"

@[rocq_alias core_id_dup]
theorem op_self (x : α) [CoreId x] : x • x = x := pcore_op_self' CoreId.core_id

@[rocq_alias core_id_extract]
theorem op_core_right_of_inc {x y : α} [CoreId x] : x ≼ y → x • y = y
  | ⟨z, hz⟩ =>
    calc x • y = x • (x • z) := congrArg (x • ·) hz
    _ = (x • x) • z := assoc'
    _ = x • z := congrArg (· • z) (op_self x)
    _ = y := hz.symm

@[rocq_alias cmra_included_dist_l]
theorem included_dist_l {n} {x1 x2 x1' : α} :
    x1 ≼ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ x2' ∧ x2' ≡{n}≡ x2
  | ⟨y, hy⟩, e => ⟨x1' • y, inc_op_left x1' y, e.op_l.trans hy.symm.dist⟩

theorem op_core_left_of_inc {x y : α} [CoreId x] (le : x ≼ y) : y • x = y :=
  comm'.trans (op_core_right_of_inc le)

@[rocq_alias cmra_pcore_core_id]
theorem CoreId.of_pcore_eq_some {x y : α} (e : pcore x = some y) : CoreId y where
  core_id := pcore_idem e

-- What's the best way to port these?
-- Global Instance cmra_includedN_preorder n : PreOrder (@includedN A _ _ n).
-- Global Instance cmra_included_preorder : PreOrder (@included A _ _).

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
theorem _root_.Iris.OFE.Equiv.core : ∀ {x₁ x₂ : α}, x₁ ≡ x₂ → core x₁ ≡ core x₂ := @core_ne.eqv

@[rocq_alias core_id_core]
theorem core_eqv_self (x : α) [CoreId x] : core (x : α) = x :=
  Option.some.inj ((pcore_eq_core x).symm.trans CoreId.core_id)

@[rocq_alias core_id_total]
theorem coreId_iff_core_eqv_self : CoreId (x : α) ↔ core x = x :=
  ⟨fun _ => core_eqv_self x, fun e => { core_id := (pcore_eq_core x).trans (congrArg some e) }⟩

@[rocq_alias cmra_core_idemp]
theorem core_idem (x : α) : core (core x) = core x := core_eqv_self _

theorem inc_refl (x : α) : x ≼ x := ⟨core x, (op_core x).symm⟩
@[refl] theorem Included.rfl {x : α} : x ≼ x := inc_refl x

theorem incN_refl (x : α) : x ≼{n} x := (inc_refl _).incN
@[refl] theorem IncludedN.rfl {x : α} : x ≼{n} x := incN_refl x

@[rocq_alias cmra_included_core]
theorem core_inc_self {x : α} [CoreId x] : core x ≼ x :=
  ⟨x, (core_op x).symm⟩

@[rocq_alias cmra_core_monoN]
theorem core_incN_core {n} {x y : α} (inc : x ≼{n} y) : core x ≼{n} core y := by
  let ⟨cy, hcy, icy⟩ := pcore_monoN' inc (Dist.of_eq (pcore_eq_core x))
  cases (pcore_eq_core _).symm.trans hcy
  exact icy

theorem core_op_mono (x y : α) : core x ≼ core (x • y) := by
  have ⟨cy, hcy⟩ := pcore_op_mono (pcore_eq_core x) y
  simp [pcore_eq_core] at hcy
  exact ⟨_, hcy⟩

@[rocq_alias cmra_core_mono]
theorem core_mono {x y : α} (Hinc : x ≼ y) : core x ≼ core y := by
  have ⟨z, hz⟩ := Hinc
  exact (Equiv.of_eq hz).core.inc_r.2 (core_op_mono x z)

end total

section discreteElements

variable {α : Type _} [CMRA α]

@[rocq_alias cmra_discrete_included_l]
theorem discrete_inc_l {x y : α} [HD : DiscreteE x] (Hv : ✓{0} y) (Hle : x ≼{0} y) : x ≼ y :=
  have ⟨_, hz⟩ := Hle
  let ⟨_, t, wt, wx, _⟩ := extend Hv hz
  ⟨t, wt.trans (congrArg (· • t) (HD.discrete wx.symm).symm)⟩

@[rocq_alias cmra_discrete_included_r]
theorem discrete_inc_r {x y : α} [HD : DiscreteE y] : x ≼{0} y → x ≼ y
  | ⟨z, hz⟩ => ⟨z, HD.discrete hz⟩

@[rocq_alias cmra_op_discrete]
theorem discrete_op {x y : α} (Hv : ✓{0} x • y) [Hx : DiscreteE x] [Hy : DiscreteE y] :
    DiscreteE (x • y) where
  discrete h :=
    let ⟨_w, _t, wt, wx, ty⟩ := extend ((Dist.validN h).mp Hv) h.symm
    (((Equiv.of_eq (Hx.discrete wx.symm)).op (Equiv.of_eq (Hy.discrete ty.symm))).trans
      (Equiv.of_eq wt).symm).to_eq

end discreteElements

section discreteCMRA

variable {α : Type _} [CMRA α]

@[rocq_alias cmra_discrete_valid_iff]
theorem valid_iff_validN' [Discrete α] (n) {x : α} : ✓ x ↔ ✓{n} x :=
  ⟨Valid.validN, fun v => discrete_valid <| validN_of_le (Nat.zero_le n) v⟩

@[rocq_alias cmra_discrete_valid_iff_0]
theorem valid_0_iff_validN [Discrete α] (n) {x : α} : ✓{0} x ↔ ✓{n} x :=
  ⟨Valid.validN ∘ discrete_valid, validN_of_le (Nat.zero_le n)⟩

@[rocq_alias cmra_discrete_included_iff]
theorem inc_iff_incN [OFE.Discrete α] (n) {x y : α} : x ≼ y ↔ x ≼{n} y :=
  ⟨incN_of_inc _, fun ⟨z, hz⟩ => ⟨z, discrete hz⟩⟩

@[rocq_alias cmra_discrete_included_iff_0]
theorem inc_0_iff_incN [OFE.Discrete α] (n) {x y : α} : x ≼{0} y ↔ x ≼{n} y :=
  ⟨fun ⟨z, hz⟩ => ⟨z, (discrete hz).dist⟩,
   fun a => incN_of_incN_le (Nat.zero_le n) a⟩

end discreteCMRA

section cancelableElements

variable {α : Type _} [CMRA α]

@[rocq_alias cancelable]
theorem cancelable {x y z : α} [Cancelable x] (v : ✓(x • y)) (e : x • y = x • z) : y = z :=
  Equiv.to_eq (equiv_dist.mpr fun _ => cancelableN v.validN e.dist)

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

theorem Cancelable.of_eqv {x₁ x₂ : α} (e : x₁ ≡ x₂) (h : Cancelable x₁) : Cancelable x₂ where
  cancelableN {n w _} v ee :=
    have v_xw : ✓{n} x₁ • w := e.symm.op_l.dist.validN.1 v
    h.cancelableN v_xw <| e.dist.op_l.trans <| ee.trans e.symm.dist.op_l

@[rocq_alias cancelable_proper]
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
    h.id_free0_r _ ((validN_dist_iff ee).mpr v) this

theorem _root_.Iris.OFE.Dist.idFree {x₁ x₂ : α} (e : x₁ ≡{n}≡ x₂) : IdFree x₁ ↔ IdFree x₂ :=
  ⟨.of_dist e, .of_dist e.symm⟩

theorem IdFree.of_eqv {x₁ x₂ : α} (e : x₁ ≡ x₂) (h : IdFree x₁) : IdFree x₂ :=
  h.of_dist e.dist (n := 0)

@[rocq_alias id_free_proper]
theorem idFree_iff {x₁ x₂ : α} (e : x₁ ≡ x₂) : IdFree x₁ ↔ IdFree x₂ :=
  e.dist.idFree (n := 0)
theorem _root_.Iris.OFE.Equiv.idFree {x₁ x₂ : α} : x₁ ≡ x₂ → (IdFree x₁ ↔ IdFree x₂) :=
  idFree_iff

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
instance idFree_op_l {x y : α} [IdFree x] [Cancelable y] : IdFree (x • y) :=
  (Equiv.of_eq comm').idFree.1 inferInstance

@[rocq_alias exclusive_id_free]
instance exclusive_idFree {x : α} [Exclusive x] : IdFree x where
  id_free0_r z v h := exclusive0_l z ((validN_dist_iff h.symm).mp v)

end idFreeElements


section ucmra

variable {α : Type _} [UCMRA α]

@[rocq_alias ucmra_unit_validN]
theorem unit_validN {n} : ✓{n} (unit : α) := valid_iff_validN.mp (unit_valid) n

@[rocq_alias ucmra_unit_leastN]
theorem incN_unit {n} {x : α} : unit ≼{n} x := ⟨x, unit_left_id.symm.dist⟩

@[rocq_alias ucmra_unit_least]
theorem inc_unit {x : α} : unit ≼ x := ⟨x, unit_left_id.symm⟩

theorem unit_left_id_dist {n} (x : α) : unit • x ≡{n}≡ x := unit_left_id.dist

@[rocq_alias ucmra_unit_right_id]
theorem unit_right_id {x : α} : x • unit = x := comm'.trans unit_left_id

theorem unit_right_id_dist (x : α) : x • unit ≡{n}≡ x := comm'.dist.trans (unit_left_id_dist x)

@[rocq_alias ucmra_unit_core_id]
instance unit_CoreId : CoreId (unit : α) where
  core_id := pcore_unit

@[rocq_alias cmra_unit_cmra_total]
instance unit_total : IsTotal α where
  total _ :=
    have ⟨y, hy, _⟩ := pcore_mono' inc_unit pcore_unit
    ⟨y, hy⟩

@[rocq_alias empty_cancelable]
instance empty_cancelable : Cancelable (unit : α) where
  cancelableN {n w t} _ e := calc
    w ≡{n}≡ unit • w := unit_left_id.dist.symm
    _ ≡{n}≡ unit • t := e
    _ ≡{n}≡ t := unit_left_id.dist

theorem _root_.Iris.OFE.Dist.to_incN {n} {x y : α} (H : x ≡{n}≡ y) : x ≼{n} y :=
  ⟨unit, (unit_right_id.dist.trans H).symm⟩

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

-- TODO: Typeclass

/-- A morphism between CMRAs, written `α -C> β`, is defined to be a non-expansive function which
preserves `validN`, `pcore` and `op`. -/
@[ext, rocq_alias CmraMorphism]
structure Hom (α β : Type _) [CMRA α] [CMRA β] extends OFE.Hom α β where
  protected validN {n x} : ✓{n} x → ✓{n} (f x)
  protected pcore x : (pcore x).map f = pcore (f x)
  protected op x y : f (x • y) = f x • f y

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
  eq_dist {_ _} := Hom.ext_iff.trans eq_dist
  dist_lt := dist_lt

@[rocq_alias cmra_morphism_id]
protected def Hom.id [CMRA α] : α -C> α where
  toHom := OFE.Hom.id
  validN := id
  pcore x := by dsimp; cases pcore x <;> rfl
  op _ _ := rfl

-- protected def Hom.comp [CMRA α] [CMRA β] [CMRA γ] (g : β -C> γ) (f : α -C> β) : α -C> γ where
--   toHom := OFE.Hom.comp g.toHom f.toHom
--   hom :=
--     ⟨fun v => g.mor.validN (f.mor.validN v),
--       fun x => sorry,
--       fun x y => sorry⟩

@[rocq_alias cmra_morphism_proper]
protected theorem Hom.eqv [CMRA β] (f : α -C> β) {x₁ x₂ : α} (X : x₁ ≡ x₂) : f x₁ ≡ f x₂ :=
  f.ne.eqv X

@[rocq_alias cmra_morphism_core]
protected theorem Hom.core [CMRA β] (f : α -C> β) {x : α} : core (f x) = f (core x) := by
  have h := f.pcore x
  unfold core
  cases hx : pcore x <;> rw [hx] at h <;> simp only [Option.map] at h <;> simp [← h]

@[rocq_alias cmra_morphism_mono]
protected theorem Hom.mono [CMRA β] (f : α -C> β) {x₁ x₂ : α} : x₁ ≼ x₂ → f x₁ ≼ f x₂
  | ⟨z, hz⟩ => ⟨f.f z, (congrArg f.f hz).trans (f.op _ _)⟩

@[rocq_alias cmra_morphism_monoN]
protected theorem Hom.monoN [CMRA β] (f : α -C> β) n {x₁ x₂ : α} : x₁ ≼{n} x₂ → f x₁ ≼{n} f x₂
  | ⟨z, hz⟩ => ⟨f.f z, (f.ne.ne hz).trans (f.op _ _).dist⟩

@[rocq_alias cmra_morphism_valid]
protected theorem Hom.valid [CMRA β] (f : α -C> β) {x : α} (H : ✓ x) : ✓ f x :=
  valid_iff_validN.mpr fun _ => f.validN H.validN

end Hom
end CMRA


section rFunctor

@[rocq_alias rFunctor]
class RFunctor (F : COFE.OFunctorPre) where
  [cmra [COFE α] [COFE β] : CMRA (F α β)]
  map [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -C> F α₂ β₂
  map_ne [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFE α] [COFE β] (x : F α β) : map (@Hom.id α _) (@Hom.id β _) x = x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x = map g g' (map f f' x)

@[rocq_alias rFunctorContractive]
class RFunctorContractive (F : COFE.OFunctorPre) extends (RFunctor F) where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [reducible, instance] RFunctor.cmra


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
  map_id [COFE α] [COFE β] (x : F α β) : map (@Hom.id α _) (@Hom.id β _) x = x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x = map g g' (map f f' x)

@[rocq_alias urFunctorContractive]
class URFunctorContractive (F : COFE.OFunctorPre) extends URFunctor F where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [reducible, instance] URFunctor.cmra

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

section Id

@[rocq_alias constRF]
instance COFE.OFunctor.constOF_RFunctor [CMRA B] : RFunctor (constOF B) where
  cmra := inferInstance
  map _ _ := (CMRA.Hom.id : B -C> B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

@[rocq_alias constRF_contractive]
instance OFunctor.constOF_RFunctorContractive [CMRA B] :
    RFunctorContractive (constOF B) where
  map_contractive.1 := fun _ => .rfl

instance COFE.OFunctor.constOF_URFunctor [UCMRA B] : URFunctor (constOF B) where
  cmra := inferInstance
  map _ _ := (CMRA.Hom.id : B -C> B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance OFunctor.constOF_URFunctorContractive [UCMRA B] :
    URFunctorContractive (constOF B) where
  map_contractive.1 _ := .rfl

end Id

section DiscreteFunO
open CMRA

#rocq_ignore discrete_fun_op_instance "Use CMRA instance"
#rocq_ignore discrete_fun_pcore_instance "Use CMRA instance"
#rocq_ignore discrete_fun_valid_instance "Use CMRA instance"
#rocq_ignore discrete_fun_validN_instance "Use CMRA instance"
#rocq_ignore discrete_fun_cmra_mixin "Use CMRA instance"

@[rocq_alias discrete_funR]
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
  assoc := funext fun _ => assoc
  comm := funext fun _ => comm
  pcore_op_left := by rintro f _ ⟨⟩; exact funext fun x => core_op (f x)
  pcore_idem := by
    rintro f _ ⟨⟩; exact congrArg some (funext fun x => core_idem (f x))
  pcore_op_mono := by
    rintro f _ ⟨⟩ g
    exact ⟨fun x => core (f x • g x), congrArg some (funext fun x =>
      (op_core_right_of_inc (core_op_mono (f x) (g x))).symm)⟩
  extend {n f f1 f2} Hv He := by
    let F x := extend (Hv x) (He x)
    exact ⟨fun x => (F x).1, fun x => (F x).2.1,
      funext fun x => (F x).2.2.1, fun x => (F x).2.2.2.1, fun x => (F x).2.2.2.2⟩

#rocq_ignore discrete_fun_unit_instance "Use UCMRA instance"
#rocq_ignore discrete_fun_ucmra_mixin "Use UCMRA instance"

@[rocq_alias discrete_funUR]
instance ucmraDiscreteFunO {α : Type _} (β : α → Type _) [∀ x, UCMRA (β x)] : UCMRA (∀ x, β x) where
  unit _ := unit
  unit_valid _ := unit_valid
  unit_left_id := funext fun _ => unit_left_id
  pcore_unit := congrArg some (funext fun _ => core_eqv_self _)

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
  }
  map_ne.ne := COFE.OFunctor.map_ne.ne
  map_id x := COFE.OFunctor.map_id x
  map_comp f g f' g' x := COFE.OFunctor.map_comp f g f' g' x

@[rocq_alias discrete_funURF_contractive]
instance DiscreteFunOF_URFC {C} (F : C → COFE.OFunctorPre) [HURF : ∀ c, URFunctorContractive (F c)] :
    URFunctorContractive (DiscreteFunOF F) where
  map_contractive.1 h _ _ := URFunctorContractive.map_contractive.distLater_dist h _

end DiscreteFunURF

section option

open CMRA Option

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

#rocq_ignore option_op_instance "Use CMRA instance"
#rocq_ignore option_pcore_instance "Use CMRA instance"
#rocq_ignore option_valid_instance "Use CMRA instance"
#rocq_ignore option_validN_instance "Use CMRA instance"

@[rocq_alias optionR, rocq_alias option_cmra_mixin]
instance cmraOption : CMRA (Option α) where
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
  pcore_op_mono := by
    rintro (_|x) _ ⟨⟩ y <;> simp
    cases H : pcore x
    · simp only []; exact ⟨_, rfl⟩
    obtain _|y := y <;> simp
    · exact ⟨none, H⟩
    obtain ⟨cy, H⟩ := pcore_op_mono H y
    exact ⟨some cy, H⟩
  extend {n} := by
    rintro (_|x) (_|mb1) (_|mb2) Hx Hx' <;> simp at Hx' ⊢
    · exists none, none
    · exists none, some x
    · exists some x, none
    · rcases extend Hx Hx' with ⟨mc1, mc2, hx, h1, h2⟩
      exact ⟨some mc1, some mc2, congrArg some hx, h1, h2⟩

#rocq_ignore option_unit_instance "Use UCMRA instance"
#rocq_ignore option_ucmra_mixin "Use UCMRA instance"

@[rocq_alias optionUR]
instance ucmraOption : UCMRA (Option α) where
  unit := none
  unit_valid := by simp [Valid]
  unit_left_id := by rintro ⟨⟩ <;> rfl
  pcore_unit := by rfl

namespace Option

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

theorem equiv_of_some_equiv_some {x y : α} (H : some x ≡ some y) : x ≡ y := H

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

@[rocq_alias cmra_opM_opM_assoc]
theorem opM_opM_assoc {x : α} {y z : Option α} : (x •? y) •? z = x •? (y • z) := by
  rcases y, z with ⟨_|_, _|_⟩ <;> simp [op?, op, assoc.symm]

theorem op_some_opM_assoc_dist {x y : α} {mz : Option α} : (x • y) •? mz ≡{n}≡ x •? (some y • mz) :=
  match mz with | none => .rfl | some _ => assoc.dist.symm

theorem some_inc_some_of_dist_opM {mz : Option α} (H : x ≡{n}≡ y •? mz) : some y ≼{n} some x :=
  match mz with | none => ⟨none, H⟩ | some z => ⟨some z, H⟩

theorem inc_of_some_inc_some [IsTotal α] {x y : α} (H : some y ≼ some x) : y ≼ x :=
  let ⟨mz, hmz⟩ := H
  match mz with
  | none => ⟨core y, (Option.some.inj hmz).trans (op_core y).symm⟩
  | some z => ⟨z, Option.some.inj hmz⟩

theorem some_incN_some_iff_some [IsTotal α] {x y : α} : some y ≼{n} some x → y ≼{n} x
  | ⟨none, hmz⟩ => ⟨core y, dist_of_some_dist_some hmz |>.trans (op_core_dist y).symm⟩
  | ⟨some z, hmz⟩ => ⟨z, hmz⟩

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

@[rocq_alias option_included]
theorem inc_iff {ma mb : Option α} :
    ma ≼ mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a = b ∨ a ≼ b) := by
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
theorem incN_iff {ma mb : Option α} :
    ma ≼{n} mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a ≡{n}≡ b ∨ a ≼{n} b) := by
  refine ⟨fun ⟨mc, Hmc⟩ => ?_, ?_⟩
  · rcases ma, mb, mc with ⟨_|_, _|_, _|_⟩ <;> simp_all [op]
    · exact .inl Hmc.symm
    · exact .inr ⟨_, Hmc⟩
  · rintro (H|⟨_, _, _, _, (H|⟨z, _⟩)⟩) <;> subst_eqs
    · exists mb
    · exists none; simp [op]; exact H.symm
    · exists some z

@[rocq_alias option_included_total]
theorem inc_iff_isTotal [IsTotal α] {ma mb : Option α} :
    ma ≼ mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼ b := by
  rw [inc_iff]
  constructor
  · rintro (rfl | ⟨a, b, ⟨⟩, ⟨⟩, (Heqv | Hinc)⟩)
    · simp
    · exact .inr ⟨a, b, rfl, rfl, ⟨core a, Heqv.symm.trans (op_core a).symm⟩⟩
    · exact .inr ⟨a, b, rfl, rfl, Hinc⟩
  · rintro (rfl | ⟨a, b, rfl, rfl, Hinc⟩)
    · simp
    · exact .inr ⟨a, b, rfl, rfl, .inr Hinc⟩

@[rocq_alias option_includedN_total]
theorem incN_iff_is_total [IsTotal α] {ma mb : Option α} :
    ma ≼{n} mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼{n} b := by
  rw [incN_iff]
  constructor
  · rintro (rfl | ⟨a, b, ⟨⟩, ⟨⟩, (Heqv | Hinc)⟩)
    · simp
    · exact .inr ⟨a, b, rfl, rfl, ⟨core a, Heqv.symm.trans (op_core_dist a).symm⟩⟩
    · exact .inr ⟨a, b, rfl, rfl, Hinc⟩
  · rintro (rfl | ⟨a, b, rfl, rfl, Hinc⟩)
    · simp
    · exact .inr ⟨a, b, rfl, rfl, .inr Hinc⟩

@[rocq_alias Some_includedN]
theorem some_incN_some_iff {a b : α} : some a ≼{n} some b ↔ a ≡{n}≡ b ∨ a ≼{n} b := by
  apply incN_iff.trans; simp

@[rocq_alias Some_included]
theorem some_inc_some_iff {a b : α} : some a ≼ some b ↔ a = b ∨ a ≼ b := by
  apply inc_iff.trans; simp

@[rocq_alias Some_included_exclusive]
theorem eqv_of_inc_exclusive [Exclusive (a : α)] {b : α} (H : some a ≼ some b) (Hv : ✓ b) :
     a = b := by
  rcases inc_iff.mp H with (Hcontra|H)
  · simp at Hcontra
  · obtain ⟨_, _, ⟨_, _⟩, ⟨_, _⟩, (He|H)⟩ := H
    · exact He
    · exact not_valid_of_excl_inc H Hv |>.elim

@[rocq_alias Some_includedN_exclusive]
theorem dist_of_inc_exclusive [Exclusive (a : α)] {b : α} (H : some a ≼{n} some b) (Hv : ✓{n} b)  :
    a ≡{n}≡ b := by
  rcases incN_iff.mp H with (Hcontra|H)
  · simp at Hcontra
  · obtain ⟨_, _, ⟨_, _⟩, ⟨_, _⟩, (_|H)⟩ := H
    · trivial
    · exact not_valid_of_exclN_inc H Hv |>.elim

@[rocq_alias Some_included_total]
theorem some_inc_some_iff_is_total [IsTotal α] {a b : α} : some a ≼ some b ↔ a ≼ b := by
  apply some_inc_some_iff.trans
  refine ⟨?_, .inr⟩
  rintro (H|H)
  · exact ⟨_, H.symm.trans (op_core a).symm⟩
  · exact H

@[rocq_alias Some_includedN_total]
theorem some_incN_some_iff_is_total [IsTotal α] {a b : α} : some a ≼{n} some b ↔ a ≼{n} b := by
  apply some_incN_some_iff.trans
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
theorem validN_of_incN_validN {a b : α} (Hv : ✓{n} a) (Hinc : some b ≼{n} some a) : ✓{n} b :=
  validN_of_incN (α := Option α) Hinc Hv

@[rocq_alias cmra_valid_Some_included]
theorem valid_of_inc_valid {a b : α} (Hv : ✓ a) (Hinc : some b ≼ some a) : ✓ b :=
  valid_of_inc (α := Option α) Hinc Hv

@[rocq_alias Some_included_opM]
theorem some_inc_some_iff_opM {a b : α} : some a ≼ some b ↔ ∃ mc, b = a •? mc := by
  simp [inc_iff]
  constructor
  · rintro (Heqv | ⟨mc', Hinc⟩)
    · exact ⟨none, by simpa [CMRA.op?] using Heqv.symm⟩
    · exact ⟨some mc', Hinc⟩
  · rintro ⟨_|z, H⟩
    · exact .inl H.symm
    · exact .inr ⟨z, H⟩

@[rocq_alias Some_includedN_opM]
theorem some_incN_some_iff_opM {a b : α} : some a ≼{n} some b ↔ ∃ mc, b ≡{n}≡ a •? mc := by
  simp [incN_iff]
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
  discrete_valid {x} := by
    cases x <;> simp [Valid, optionValid]
    exact (CMRA.discrete_valid ·)

end Option
end option

section unit

#rocq_ignore unit_op_instance "Use CMRA instance"
#rocq_ignore unit_pcore_instance "Use CMRA instance"
#rocq_ignore unit_valid_instance "Use CMRA instance"
#rocq_ignore unit_validN_instance "Use CMRA instance"
#rocq_ignore unit_cancelable "Subsumed by empty_cancelable"
#rocq_ignore unit_core_id "Subsumed by unit_CoreId"

@[rocq_alias unitR, rocq_alias unit_cmra_mixin]
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
  assoc := rfl
  comm := rfl
  pcore_op_left _ := rfl
  pcore_idem _ := rfl
  pcore_op_mono _ _ := ⟨.unit, rfl⟩
  extend _ _ := ⟨(), (), rfl, .rfl, .rfl⟩

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

#rocq_ignore prod_op_instance "Use CMRA instance"
#rocq_ignore prod_pcore_instance "Use CMRA instance"
#rocq_ignore prod_valid_instance "Use CMRA instance"
#rocq_ignore prod_validN_instance "Use CMRA instance"

@[rocq_alias prodR, rocq_alias prod_cmra_mixin]
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
  pcore_op_mono {x cx} h y := by
    have ⟨cx₁, hcx₁, this⟩ := Option.bind_eq_some_iff.mp h
    have ⟨cx₂, hcx₂, hcx⟩ := Option.bind_eq_some_iff.mp this
    have ⟨cy₁, hcy₁⟩ := CMRA.pcore_op_mono hcx₁ y.fst
    have ⟨cy₂, hcy₂⟩ := CMRA.pcore_op_mono hcx₂ y.snd
    have ⟨a, ha, ea⟩ := equiv_some hcy₁
    have ⟨b, hb, eb⟩ := equiv_some hcy₂
    unfold pcore
    rw [Option.some.inj hcx.symm, ha, hb]
    exact ⟨(cy₁, cy₂), congrArg some (equiv_prod_ext ea eb)⟩
  extend {n x y₁ y₂} := fun ⟨vx₁, vx₂⟩ e =>
    let ⟨z₁, w₁, hx₁, hz₁, hw₁⟩ := CMRA.extend vx₁ (OFE.dist_fst e)
    let ⟨z₂, w₂, hx₂, hz₂, hw₂⟩ := CMRA.extend vx₂ (OFE.dist_snd e)
    ⟨(z₁, z₂), (w₁, w₂), equiv_prod_ext hx₁ hx₂, ⟨hz₁, hz₂⟩, ⟨hw₁, hw₂⟩⟩

theorem valid_fst {x : α × β} (h : ✓ x) : ✓ x.fst := h.left
theorem valid_snd {x : α × β} (h : ✓ x) : ✓ x.snd := h.right

theorem validN_fst {n} {x : α × β} (h : ✓{n} x) : ✓{n} x.fst := h.left
theorem validN_snd {n} {x : α × β} (h : ✓{n} x) : ✓{n} x.snd := h.right

@[rocq_alias pair_includedN]
theorem incN_iff {n} (a a' : α) (b b' : β) :
    a ≼{n} a' ∧ b ≼{n} b' ↔ (a, b) ≼{n} (a', b') := by
  constructor
  · simp [CMRA.IncludedN]
    rintro x hx y hy
    exact ⟨x, ⟨y, ⟨hx, hy⟩⟩⟩
  · simp [CMRA.IncludedN]
    rintro x y ⟨ha, hb⟩
    constructor
    · exact ⟨x, Option.dist_of_some_dist_some ha⟩
    · exact ⟨y, Option.dist_of_some_dist_some hb⟩

@[rocq_alias prod_cmra_discrete]
instance instCmraDistreteProd [CMRA.Discrete α] [CMRA.Discrete β] : CMRA.Discrete (α × β) where
  discrete_valid := by
    rintro ⟨_, _⟩
    simp [CMRA.ValidN]
    exact (⟨CMRA.discrete_valid ·, CMRA.discrete_valid ·⟩)

@[rocq_alias pair_core_id]
instance instCoreIdPair {x : α} {y : β} [CMRA.CoreId x] [CMRA.CoreId y] : CMRA.CoreId (α := α × β) ⟨x, y⟩ where
  core_id := Equiv.to_eq <| by
    refine (equiv_dist.mpr (fun _ => ?_))
    simp only [CMRA.pcore, pcore]
    haveI : NonExpansive (fun b : β => some (x, b)) := ⟨fun _ _ _ H => some_dist_some.mpr (dist_prod_ext .rfl H)⟩
    haveI : NonExpansive ((fun a : α => (CMRA.pcore y).bind fun b : β => pure (a, b))) :=
      ⟨fun _ _ _ H => Option.bind_dist (fun _ => some_dist_some.mpr ⟨H, .rfl⟩)⟩
    refine ((Option.bind_fun_ne (fun a : α => (CMRA.pcore y).bind fun b => pure (a, b))).ne CMRA.CoreId.core_id.dist).trans ?_
    exact ((Option.bind_fun_ne (fun b : β => some (x, b))).ne CMRA.CoreId.core_id.dist).trans .rfl

end Prod

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

@[rocq_alias prodRF_contractive]
instance instRFunctorContractiveProdOF
    [RFunctorContractive F1] [RFunctorContractive F2] :
    RFunctorContractive (ProdOF F1 F2) where
  map_contractive.1 H _ :=
    Prod.map_ne (fun _ => RFunctorContractive.map_contractive.1 H _)
      (fun _ => RFunctorContractive.map_contractive.1 H _)

end ProdRF

section optionOF

variable {F : COFE.OFunctorPre}

@[rocq_alias optionURF]
instance urFunctorOptionOF [RFunctor F] : URFunctor (OptionOF F) where
  cmra {α β} := ucmraOption
  map f g := {
    toHom := COFE.OFunctor.map f g
    validN := by
      simp [COFE.OFunctor.map, CMRA.ValidN, optionMap]
      rintro n (_|x) <;> simp
      exact (RFunctor.map f g).validN
    pcore := by
      rintro (_|x) <;> simp [optionCore, CMRA.pcore, COFE.OFunctor.map, optionMap]
      have := (RFunctor.map f g).pcore x; revert this
      cases CMRA.pcore x <;> cases CMRA.pcore (RFunctor.map f g x)
        <;> simp
    op := by
      rintro (_|x) (_|y) <;> simp [CMRA.op, COFE.OFunctor.map, optionOp, optionMap]
      exact (RFunctor.map f g).op x y
  }
  map_ne.ne := COFE.OFunctor.map_ne.ne
  map_id x := COFE.OFunctor.map_id x
  map_comp f g f' g' x := COFE.OFunctor.map_comp f g f' g' x

@[rocq_alias optionURF_contractive]
instance urFunctorContractiveOptionOF
    [RFunctorContractive F] : URFunctorContractive (OptionOF F) where
  map_contractive.1 := COFE.OFunctorContractive.map_contractive.1

end optionOF
