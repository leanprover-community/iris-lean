/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Сухарик (@suhr), Markus de Medeiros, Puming Liu, Janine Lohse
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.Monoid
public import Iris.Algebra.StepIndexFinite

@[expose] public section

/-!
# Resource algebras

Following the module style, the step-index-free part of a resource algebra is separated from the
step-indexed part. The data classes `Op α` and `PCore α` carry their own SI-free laws; `RA α`
adds the law relating them (`pcore_op_left`) and `URA α` the unit and its laws. The step-indexed
classes take these as instance *parameters* and never extend them:
`ORA α [RA α]`, `CMRA α [RA α]`, `UORA α [URA α]`, `UCMRA α [URA α]`.

**Building instances.** A model declares the SI-free part first, then the step-indexed part:
* `instance : RA X where op := …; pcore := …; assoc := …; comm := …; pcore_idem := …;
  pcore_op_left := …`. If `Op X`/`PCore X` instances already exist, write only
  `instance : RA X where pcore_op_left := …`: the structure instance fills the missing parents
  `toOp`/`toPCore` by instance synthesis. `URA X` likewise (`where unit := …; unit_left_id := …;
  pcore_unit := …`, with `toRA` synthesized).
* The step-indexed instance is built from `[RA X]`: either directly
  (`instance : ORA X where …`), or through the input records/builders, which only ask for the
  step-indexed laws: `ORA.ofCMRAData (d : CMRAData X) : CMRA X`,
  `UORA.ofUCMRAData (d : UCMRAData X) : UCMRA X` (with `[URA X] [CMRA X]`),
  `CMRA.ofDiscrete`, `CMRA.ofDiscreteTotal`, `ORA.ofDiscrete`, `CMRA.ofIso`, ….

**Binder convention.** Lemmas whose statement does not mention the step index take only
`[RA α]`/`[URA α]` (plus SI-free mixins such as `IsTotal α`); lemmas mentioning validity, the
order or the distance take `[RA α] [ORA α]` (resp. `[URA α] [UORA α]`, …). No ``
pins are needed for SI-free laws.
-/

namespace Iris
open OFE

variable {SI : stepindex (Type _)} [instSI : SIdx SI]
local stepindex SI

/-- The underlying operation of a resource. -/
@[rocq_alias Op]
class Op (α : Type _) where
  /-- The composition operation. -/
  op : α → α → α
  assoc : op x (op y z) = op (op x y) z
  comm : op x y = op y x

namespace Op

@[inherit_doc op] infix:60 (priority := high) " • " => op

variable [Op α]

/-- The composition operation with an optional right argument. -/
@[rocq_alias opM]
def op? (x : α) : Option α → α
  | some y => x • y
  | none => x
@[inherit_doc op?] infix:60 " •? " => op?

end Op

variable (SI) in
/-- Non-expansiveness of the operation (Prop mixin; the data class `Op` carries no step index). -/
@[indexed]
class OpNE (α : Type _) [OFE α] [Op α] : Prop where
  op_ne {x : α} : OFE.NonExpansive (Op.op x)
export OpNE (op_ne)

/-- The partial core operator for a resource algebra. -/
@[rocq_alias PCore]
class PCore (α : Type _) where
  pcore : α → Option α
  pcore_idem : pcore x = some cx → pcore cx = some cx

namespace PCore
variable [PCore α]

/-- The total core operation. -/
@[rocq_alias core]
def core (x : α) := (pcore x).getD x

end PCore

variable (SI) in
/-- Non-expansiveness of the partial core (Prop mixin). -/
@[indexed]
class PCoreNE (α : Type _) [OFE α] [PCore α] : Prop where
  pcore_ne {n} {x y cx : α} : x ≡{n}≡ y → PCore.pcore x = some cx → ∃ cy, PCore.pcore y = some cy ∧ cx ≡{n}≡ cy
export PCoreNE (pcore_ne)

/-- A resource algebra whose core is total. -/
@[rocq_alias CmraTotal]
class IsTotal (α : Type _) [PCore α] : Prop where
  total (x : α) : ∃ cx, PCore.pcore x = some cx

theorem IsTotal.core_idem [PCore α] [IsTotal α] (x : α) : PCore.core (PCore.core x) = PCore.core x := by
  obtain ⟨cx, h⟩ := IsTotal.total x
  simp [PCore.core, h, PCore.pcore_idem h]
#rocq_ignore cmra_total_mixin "Use CMRA + IsTotal"

/-- A resource algebra without validity or step index: composition and partial core together
with the law relating them. The step-indexed structure lives in the mixin `ORA α`, which takes
`RA α` as a parameter. -/
class RA (α : Type _) extends Op α, PCore α where
  pcore_op_left {x cx : α} : pcore x = some cx → cx • x = x

/-- The unit of a unital resource algebra (parameter-free data). -/
class UnitOp (α : Type _) where
  unit : α

/-- A unital resource algebra without validity or step index. Its core is total (`IsTotal`): in
Iris this follows from the monotonicity of the core, which is not an SI-free law. -/
class URA (α : Type _) extends RA α, UnitOp α, IsTotal α where
  unit_left_id {x : α} : unit • x = x
  pcore_unit : pcore unit = some unit

-- NOTE: The linter here complains that `Valid` is duplicted here.
set_option linter.iris.dupNamespace false in
/-- The validity predicates of a resource algebra.  -/
@[indexed, rocq_alias Valid]
class Valid (SI : stepindex (Type _)) (α : Type _) where
  /-- The step-indexed validity predicate. -/
  ValidN : SI → α → Prop
  /-- The validity predicate. -/
  Valid {SI} : α → Prop
  valid_iff_validN : Valid x ↔ ∀ n, ValidN n x
attribute [indexed] Valid.ValidN

#rocq_ignore ValidN "Merged into the `Valid` type class"

namespace Valid

@[inherit_doc Valid.Valid] notation:50 "✓[" S "] " x:51 => Valid.Valid (SI := S) x
@[inherit_doc Valid.Valid] notation:50 "✓ " x:50 => Valid.Valid (SI := stepindex%) x
@[inherit_doc Valid.ValidN] notation:50 "✓{" n "} " x:51 => Valid.ValidN n x

end Valid

variable (SI) in
/-- Non-expansiveness and downward closure of validity (Prop mixin). -/
@[indexed]
class ValidNE (α : Type _) [OFE α] [Valid α] : Prop where
  validN_ne {n} {x y : α} : x ≡{n}≡ y → Valid.ValidN n x → Valid.ValidN n y
  validN_le {n n'} {x : α} : Valid.ValidN n x → n' ≤ n → Valid.ValidN n' x
export ValidNE (validN_ne validN_le)

/-- The ordering predicate on a resource algebra. -/
@[indexed]
class Ordered (SI : stepindex (Type _)) (α : Type _) where
  /-- The indexed ordering predicate. This is the generic ORA order predicate; if your ORA is
  `OrdInc`, the lemma `ordN_incN` converts it to the extension order typical of Iris CMRAs. -/
  OrderN : SI → α → α → Prop
  /-- The ordering predicate. This is the generic ORA order predicate; if your ORA is `OrdInc`,
  the {SI} lemma `ord_inc` converts it to the extension order typical of Iris CMRAs. -/
  Order {SI} : α → α → Prop
  ordN_trans {n} {x y z : α} : OrderN n x y → OrderN n y z → OrderN n x z
  ord_trans {SI} {x y z : α} : Order x y → Order y z → Order x z
  ordN_of_ord {x y : α} (n) : Order x y → OrderN n x y
attribute [indexed] Ordered.Order Ordered.OrderN

variable (SI) in
/-- Non-expansiveness and downward closure of the order (Prop mixin). -/
@[indexed]
class OrderedNE (α : Type _) [OFE α] [Ordered α] : Prop where
  ordN_ne {n} {x x' y y' : α} : x ≡{n}≡ x' → y ≡{n}≡ y' → Ordered.OrderN n x y →
    Ordered.OrderN n x' y'
  ordN_le {n n'} {x y : α} : Ordered.OrderN n x y → n' ≤ n → Ordered.OrderN n' x y
export OrderedNE (ordN_ne ordN_le)

namespace Ordered

@[inherit_doc OrderN] notation:50 x " ≼ₒ{" n "} " y:51 => OrderN n x y
@[inherit_doc Order] notation:50 x " ≼ₒ[" S "] " y:51 => Order (SI := S) x y
@[inherit_doc Ordered.Order] notation:50 x:51 " ≼ₒ " y:51 => Ordered.Order (SI := stepindex%) x y

variable [OFE α] [Ordered SI α]

/-- The reflexive closure of the step-indexed order. -/
@[indexed]
def OrderNR (n : SI) (x y : α) : Prop := x ≡{n}≡ y ∨ x ≼ₒ{n} y
@[inherit_doc OrderNR] notation:50 x " ≼ₒ*{" n "} " y:51 => OrderNR n x y

/-- The reflexive closure of the order. -/
def OrderR (x y : α) : Prop := x = y ∨ x ≼ₒ y
@[inherit_doc OrderR] notation:50 x " ≼ₒ*[" S "] " y:51 => OrderR (SI := S) x y
@[inherit_doc Ordered.OrderR] notation:50 x:51 " ≼ₒ* " y:51 => Ordered.OrderR (SI := stepindex%) x y

theorem OrderN.ordNR {n} {x y : α} : x ≼ₒ{n} y → x ≼ₒ*{n} y := .inr
omit [OFE α] instSI in
theorem Order.ordR {x y : α} : x ≼ₒ y → x ≼ₒ* y := .inr

@[refl] theorem OrderNR.rfl {n} {x : α} : x ≼ₒ*{n} x := .inl .rfl
omit [OFE α] instSI in
@[refl] theorem OrderR.rfl {x : α} : x ≼ₒ* x := .inl (Eq.refl x)

variable [OrderedNE α]

theorem OrderNR.ne {n} {x x' y y' : α} (ex : x ≡{n}≡ x') (ey : y ≡{n}≡ y') :
    x ≼ₒ*{n} y → x' ≼ₒ*{n} y'
  | .inl e => .inl (ex.symm.trans (e.trans ey))
  | .inr h => .inr (ordN_ne ex ey h)

theorem OrderNR.le {n n'} {x y : α} (le : n' ≤ n) : x ≼ₒ*{n} y → x ≼ₒ*{n'} y
  | .inl e => .inl (e.le le)
  | .inr h => .inr (ordN_le h le)

theorem OrderNR.succ [SIdxSucc] {n} {x y : α} : x ≼ₒ*{succᵢ n} y → x ≼ₒ*{n} y :=
  OrderNR.le SIdx.le_succ_diag_r

theorem OrderNR.trans {n} {x y z : α} : x ≼ₒ*{n} y → y ≼ₒ*{n} z → x ≼ₒ*{n} z
  | .inl e₁, .inl e₂ => .inl (e₁.trans e₂)
  | .inl e₁, .inr h₂ => .inr (ordN_ne e₁.symm .rfl h₂)
  | .inr h₁, .inl e₂ => .inr (ordN_ne .rfl e₂ h₁)
  | .inr h₁, .inr h₂ => .inr (ordN_trans h₁ h₂)

omit [OFE α] [OrderedNE α] instSI in
theorem OrderR.trans {x y z : α} : x ≼ₒ* y → y ≼ₒ* z → x ≼ₒ* z
  | .inl e₁, h₂ => e₁ ▸ h₂
  | h₁, .inl e₂ => e₂ ▸ h₁
  | .inr h₁, .inr h₂ => .inr (ord_trans h₁ h₂)

omit [OrderedNE α] in
theorem OrderR.ordNR (n) {x y : α} : x ≼ₒ* y → x ≼ₒ*{n} y
  | .inl e => .inl (e ▸ .rfl)
  | .inr h => .inr (ordN_of_ord n h)

end Ordered

/-- Reflexivity of the order: the order law of unital algebras (`UORA`), also enjoyed by
total algebras under their extension inclusion. -/
@[indexed]
class OrderRefl (SI : stepindex (Type _)) [SIdx SI] (α : Type _) [Ordered α] : Prop where
  ord_refl (x : α) : x ≼ₒ x
attribute [indexed] OrderRefl.ord_refl

/-- An element `x` is increasing if composing with it never shrinks a resource. Cores and units
are increasing; in an affine algebra every element is. -/
@[indexed]
class Increasing (SI : stepindex (Type _)) [SIdx SI] {α : Type _} [Op α] [Ordered α] (x : α) : Prop where
  increasing (y : α) : y ≼ₒ x • y

/-- The step-indexed extension inclusion: `y` is `x` composed with some frame. This is the
inclusion of classical resource algebras. -/
@[indexed, rocq_alias includedN]
def IncludedN {α : Type _} [HasDist α] [Op α] (n : SI) (x y : α) : Prop := ∃ z : α, y ≡{n}≡ x • z
@[inherit_doc IncludedN] notation:50 x " ≼{" n "} " y:51 => IncludedN n x y

/-- The extension inclusion: `y` is `x` composed with some frame. -/
@[rocq_alias included]
def Included {α : Type _} [Op α] (x y : α) : Prop := ∃ z : α, y = x • z
@[inherit_doc Included] infix:50 " ≼ " => Included

/-- The extension inclusion is contained in the order: every element is increasing. -/
@[indexed]
class IncOrd (SI : stepindex (Type _)) [SIdx SI] (α : Type _) [HasDist α] [Op α] [Ordered α] : Prop where
  inc_ord {x y : α} : x ≼ y → x ≼ₒ y

@[indexed, reducible] def ORA.Affine (α : Type _) [HasDist α] [Op α] [Ordered α] : Prop := IncOrd α

/-- The order is contained in the extension inclusion: every ordered pair has a frame. -/
@[indexed]
class OrdInc (SI : stepindex (Type _)) [SIdx SI] (α : Type _) [HasDist α] [Op α] [Ordered α] : Prop where
  ord_inc {x y : α} : x ≼ₒ y → x ≼ y
  ordN_incN {n} {x y : α} : x ≼ₒ{n} y → x ≼{n} y

/-- The order is the extension inclusion. -/
@[indexed]
class IsInc (SI : stepindex (Type _)) [SIdx SI] (α : Type _) [HasDist α] [Op α] [Ordered α] : Prop
    extends IncOrd α, OrdInc α

attribute [indexed] IncOrd.inc_ord OrdInc.ord_inc OrdInc.ordN_incN

section
variable {α : Type _} [OFE α] [Op α] [Ordered SI α]

theorem IncOrd.increasing [IncOrd α] (x : α) : Increasing x :=
  ⟨fun _ => IncOrd.inc_ord ⟨x, Op.comm⟩⟩

theorem IncOrd.of_increasing (h : ∀ x : α, Increasing x) : IncOrd α where
  inc_ord {x _} := fun ⟨z, e⟩ => by subst e; rw [Op.comm]; exact (h z).increasing x

instance instIncreasingOfIncOrd [IncOrd α] (x : α) : Increasing x := IncOrd.increasing x

theorem inc_iff_ord [IncOrd α] [OrdInc α] {x y : α} : x ≼ y ↔ x ≼ₒ y :=
  ⟨IncOrd.inc_ord, OrdInc.ord_inc⟩

theorem IncOrd.incN_ordN [OrderedNE α] [IncOrd α] {n} {x y : α} : x ≼{n} y → x ≼ₒ{n} y
  | ⟨z, hz⟩ => OrderedNE.ordN_ne .rfl hz.symm (Ordered.ordN_of_ord n (IncOrd.inc_ord ⟨z, rfl⟩))

theorem incN_iff_ordN [OrderedNE α] [IncOrd α] [OrdInc α] {n} {x y : α} : x ≼{n} y ↔ x ≼ₒ{n} y :=
  ⟨IncOrd.incN_ordN, OrdInc.ordN_incN⟩

/-! The `IncOrd`/`OrdInc` laws restated with instance-implicit binders: the projections take their
`SIdx`/`HasDist` instances implicitly and get stuck when only the order fixes them. -/
theorem inc_ord [IncOrd α] {x y : α} (h : x ≼ y) : x ≼ₒ y :=
  IncOrd.inc_ord h
theorem ord_inc [OrdInc α] {x y : α} (h : x ≼ₒ y) : x ≼ y :=
  OrdInc.ord_inc h
theorem ordN_incN [OrdInc α] {n} {x y : α} (h : x ≼ₒ{n} y) : x ≼{n} y :=
  OrdInc.ordN_incN h

end

/-! ## Order-free theory -/

namespace ORA
variable [OFE α] [Op α] [OpNE α]

export Op (op op? assoc comm)
export PCore (pcore pcore_idem core)
export Valid (Valid ValidN valid_iff_validN)
export IsTotal (total)

/-! ## Op -/

omit [OFE α] [OpNE α] in
@[rocq_alias cmra_comm]
theorem comm' {x y : α} : x • y = y • x := comm

omit [OFE α] [OpNE α] in
@[rocq_alias cmra_assoc]
theorem assoc' {x y z : α} : x • (y • z) = (x • y) • z := assoc

theorem op_right_dist {n} (x : α) {y z : α} (e : y ≡{n}≡ z) : x • y ≡{n}≡ x • z :=
  op_ne.ne e
theorem _root_.Iris.OFE.Dist.op_r {n} {x y z : α} : y ≡{n}≡ z → x • y ≡{n}≡ x • z := op_right_dist _

omit [OpNE α] in
theorem op_commN {n} {x y : α} : x • y ≡{n}≡ y • x := Dist.of_eq comm

omit [OpNE α] in
theorem op_assocN {n} {x y z : α} : x • (y • z) ≡{n}≡ (x • y) • z := Dist.of_eq assoc

theorem op_left_dist {n} {x y : α} (z : α) (e : x ≡{n}≡ y) : x • z ≡{n}≡ y • z :=
  op_commN.trans <| e.op_r.trans op_commN
theorem _root_.Iris.OFE.Dist.op_l {n} {x y z : α} : x ≡{n}≡ y → x • z ≡{n}≡ y • z := op_left_dist _

theorem _root_.Iris.OFE.Dist.op {n} {x x' y y' : α}
    (ex : x ≡{n}≡ x') (ey : y ≡{n}≡ y') : x • y ≡{n}≡ x' • y' := ex.op_l.trans ey.op_r

#rocq_ignore cmra_op_proper' "OFE is Leibniz; use equality"

theorem _root_.Iris.OFE.Dist.opM {n} {x₁ x₂ : α} {y₁ y₂ : Option α}
    (H1 : x₁ ≡{n}≡ x₂) (H2 : y₁ ≡{n}≡ y₂) : x₁ •? y₁ ≡{n}≡ x₂ •? y₂ :=
  match y₁, y₂, H2 with
  | none, none, _ => H1
  | some _, some _, H2 => H1.op H2

theorem opM_left_dist {n} {x y : α} (z : Option α) (e : x ≡{n}≡ y) : x •? z ≡{n}≡ y •? z :=
  e.opM Dist.rfl
theorem opM_right_dist {n} (x : α) {y z : Option α} (e : y ≡{n}≡ z) : x •? y ≡{n}≡ x •? z :=
  Dist.rfl.opM e

omit [OFE α] [OpNE α] in
@[rocq_alias cmra_op_opM_assoc]
theorem op_opM_assoc (x y : α) (mz : Option α) : (x • y) •? mz = x • (y •? mz) := by
  unfold op?; cases mz <;> simp [assoc]

omit [OpNE α] in
theorem op_opM_assoc_dist {n} (x y : α) (mz : Option α) : (x • y) •? mz ≡{n}≡ x • (y •? mz) := by
  unfold op?; cases mz <;> simp [op_assocN, Dist.symm]

theorem incN_ne {n} {x x' y y' : α} (ex : x ≡{n}≡ x') (ey : y ≡{n}≡ y') :
    x ≼{n} y → x' ≼{n} y'
  | ⟨z, hz⟩ => ⟨z, ey.symm.trans (hz.trans ex.op_l)⟩

theorem incN_of_incN_of_dist {n} (h : (a : α) ≼{n} b) (e : b ≡{n}≡ c) : a ≼{n} c := incN_ne .rfl e h

instance {n} : Trans (IncludedN (α := α) n) (Dist n) (IncludedN n) where
  trans := incN_of_incN_of_dist

theorem incN_of_dist_of_incN {n} (e : (a : α) ≡{n}≡ b) (h : b ≼{n} c) : a ≼{n} c :=
  incN_ne e.symm .rfl h

instance {n} : Trans (Dist (α := α) n) (IncludedN n) (IncludedN n) where
  trans := incN_of_dist_of_incN

omit [OpNE α] in
@[rocq_alias cmra_included_includedN]
theorem incN_of_inc (n) {x y : α} : x ≼ y → x ≼{n} y
  | ⟨z, hz⟩ => ⟨z, hz.dist⟩

#rocq_ignore cmra_included_proper "OFE is Leibniz; use equality"

theorem incN_iff_left {n} (e : (a : α) ≡{n}≡ b) : a ≼{n} c ↔ b ≼{n} c :=
  ⟨incN_ne e .rfl, incN_ne e.symm .rfl⟩
theorem _root_.Iris.OFE.Dist.incN_l {n} : (a : α) ≡{n}≡ b → (a ≼{n} c ↔ b ≼{n} c) := incN_iff_left

theorem incN_iff_right {n} (e : (b : α) ≡{n}≡ c) : a ≼{n} b ↔ a ≼{n} c :=
  ⟨incN_ne .rfl e, incN_ne .rfl e.symm⟩
theorem _root_.Iris.OFE.Dist.incN_r {n} : (b : α) ≡{n}≡ c → (a ≼{n} b ↔ a ≼{n} c) := incN_iff_right

@[rocq_alias cmra_includedN_ne]
theorem incN_dist_iff {n} (ea : (a : α) ≡{n}≡ a') (eb : (b : α) ≡{n}≡ b') :
    a ≼{n} b ↔ a' ≼{n} b' :=
  ⟨incN_ne ea eb, incN_ne ea.symm eb.symm⟩
theorem _root_.Iris.OFE.Dist.incN {n} :
    (a : α) ≡{n}≡ a' → b ≡{n}≡ b' → (a ≼{n} b ↔ a' ≼{n} b') :=
  incN_dist_iff

#rocq_ignore cmra_includedN_proper "OFE is Leibniz; use equality"

omit [OFE α] [OpNE α] in
@[rocq_alias cmra_included_trans]
theorem inc_trans {x y z : α} : x ≼ y → y ≼ z → x ≼ z
  | ⟨w, hw⟩, ⟨t, ht⟩ => ⟨w • t, ht.trans (hw ▸ assoc.symm)⟩

instance : Trans (Included (α := α)) Included Included where
  trans := inc_trans

@[rocq_alias cmra_includedN_trans]
theorem incN_trans {n} {x y z : α} : x ≼{n} y → y ≼{n} z → x ≼{n} z
  | ⟨w, hw⟩, ⟨t, ht⟩ => ⟨w • t, ht.trans (hw.op_l.trans op_assocN.symm)⟩

instance {n} : Trans (IncludedN (α := α) n) (IncludedN n) (IncludedN n) where
  trans := incN_trans

omit [OpNE α] in
@[rocq_alias cmra_includedN_le]
theorem incN_of_incN_le {n n'} {x y : α} (l1 : n' ≤ n) : x ≼{n} y → x ≼{n'} y
  | ⟨z, hz⟩ => ⟨z, Dist.le hz l1⟩
omit [OpNE α] in
theorem inc0_of_incN {n} {x y : α} : x ≼{n} y → x ≼{0} y := incN_of_incN_le SIdx.le_0_l

omit [OpNE α] in
@[rocq_alias cmra.cmra_includedN_S]
theorem incN_of_incN_succ [SIdxSucc] {n} {x y : α} : x ≼{succᵢ n} y → x ≼{n} y :=
  incN_of_incN_le SIdx.le_succ_diag_r

omit [OpNE α] in
@[rocq_alias cmra_includedN_l]
theorem incN_op_left (n) (x y : α) : x ≼{n} x • y := ⟨y, Dist.rfl⟩

omit [OFE α] [OpNE α] in
@[rocq_alias cmra_included_l]
theorem inc_op_left (x y : α) : x ≼ x • y := ⟨y, rfl⟩

omit [OFE α] [OpNE α] in
@[rocq_alias cmra_included_r]
theorem inc_op_right (x y : α) : y ≼ x • y := ⟨x, comm⟩

omit [OpNE α] in
@[rocq_alias cmra_includedN_r]
theorem incN_op_right (n) (x y : α) : y ≼{n} x • y := ⟨x, op_commN⟩

omit [OFE α] [OpNE α] in
@[rocq_alias cmra_mono_l]
theorem op_mono_right {x y} (z : α) : x ≼ y → z • x ≼ z • y
  | ⟨w, hw⟩ => ⟨w, (congrArg (z • ·) hw).trans assoc⟩

@[rocq_alias cmra_monoN_l]
theorem op_monoN_right {n} {x y} (z : α) : x ≼{n} y → z • x ≼{n} z • y
  | ⟨w, hw⟩ => ⟨w, hw.op_r.trans op_assocN⟩

@[rocq_alias cmra_monoN_r]
theorem op_monoN_left {n} {x y} (z : α) (h : x ≼{n} y) : x • z ≼{n} y • z :=
  (op_commN.incN op_commN).1 (op_monoN_right z h)

omit [OFE α] [OpNE α] in
@[rocq_alias cmra_mono_r]
theorem op_mono_left {x y} (z : α) (h : x ≼ y) : x • z ≼ y • z := by
  rw [comm' (x := x) (y := z), comm' (x := y) (y := z)]; exact op_mono_right z h

@[rocq_alias cmra_monoN]
theorem op_monoN {n} {x x' y y' : α} (hx : x ≼{n} x') (hy : y ≼{n} y') :
    x • y ≼{n} x' • y' :=
  incN_trans (op_monoN_left _ hx) (op_monoN_right _ hy)

#rocq_ignore cmra_monoN' "Use cmra_monoN"

omit [OFE α] [OpNE α] in
@[rocq_alias cmra_mono]
theorem op_mono {x x' y y' : α} (hx : x ≼ x') (hy : y ≼ y') :
    x • y ≼ x' • y' :=
  inc_trans (op_mono_left _ hx) (op_mono_right _ hy)

#rocq_ignore cmra_mono' "Use cmra_mono"

@[indexed, reducible] def extOrdered : Ordered α where
  OrderN := IncludedN
  Order := Included
  ordN_trans := incN_trans
  ord_trans := inc_trans
  ordN_of_ord n h := incN_of_inc n h

theorem extOrderedNE : @OrderedNE _ _ α _ extOrdered :=
  @OrderedNE.mk _ _ α _ extOrdered incN_ne (fun h le => incN_of_incN_le le h)

section pcore
variable [PCore α] [PCoreNE α]

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

section total
variable [IsTotal α]

omit [Op α] [OpNE α] [PCoreNE α] in
@[rocq_alias cmra_pcore_core]
theorem pcore_eq_core (x : α) : pcore x = some (core x) := by
  unfold core
  have ⟨cx, hcx⟩ := IsTotal.total x
  simp [hcx]

end total
end pcore

end ORA

/-! ## Ordered resource algebras -/

/-- An ordered resource algebra: the step-indexed mixin over a resource algebra `RA α`, giving
validity together with the laws relating it to composition and core, and a step-indexed order
that they respect. The order is neither required to be reflexive
(`OrderRefl`) nor to contain the extension inclusion (`IncOrd`). -/
@[indexed]
class ORA (SI : stepindex (Type _)) [instSI : SIdx SI] (α : Type _) [RA α]
    extends OFE α, Valid α, Ordered α,
      OpNE α, PCoreNE α, ValidNE α, OrderedNE α where
  validN_op_left {SI} {n} {x y : α} : ✓{n} (x • y) → ✓{n} x
  extend {SI} {n} {x y₁ y₂ : α} : ✓{n} x → x ≡{n}≡ y₁ • y₂ →
    Σ' z₁ z₂ : α, x = z₁ • z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂
  op_monoN_left_ord {SI} {n} {x y : α} (z : α) : x ≼ₒ{n} y → x • z ≼ₒ{n} y • z
  op_mono_left_ord {SI} {x y : α} (z : α) : x ≼ₒ y → x • z ≼ₒ y • z
  validN_of_ordN {SI} {n} {x y : α} : x ≼ₒ{n} y → ✓{n} y → ✓{n} x
  pcore_monoN_ord {SI} {n} {x y cx : α} : x ≼ₒ{n} y → PCore.pcore x = some cx →
    ∃ cy, PCore.pcore y = some cy ∧ cx ≼ₒ{n} cy
  pcore_mono_ord {SI} {x y cx : α} : x ≼ₒ y → PCore.pcore x = some cx → ∃ cy, PCore.pcore y = some cy ∧ cx ≼ₒ cy
  pcore_order_op {SI} {x cx : α} : PCore.pcore x = some cx → ∀ y, ∃ cxy, PCore.pcore (x • y) = some cxy ∧ cx ≼ₒ cxy
  pcore_increasing {SI} {x cx : α} : PCore.pcore x = some cx → Increasing cx
  increasing_closed {SI} {n} {x y : α} : Increasing x → x ≼ₒ*{n} y → Increasing y
  ordN_extend {SI} {n sn} {x y : α} : IsSucc n sn → ✓{n} y → x ≼ₒ{n} y → ∃ z, z ≼ₒ{sn} y ∧ z ≡{n}≡ x
attribute [indexed] ORA.op_mono_left_ord ORA.pcore_order_op
#rocq_ignore cmra_mixin_of' "Not needed."

#rocq_ignore cmra_ofeO "Not needed."
#rocq_ignore RAMixin
  "Bundled record of RA laws; Lean uses the SI-free class `RA`."

namespace ORA
export RA (pcore_op_left)
variable [RA α] [ORA α]

/-- Core-identity is a property of the core alone, so it takes only `[PCore α]` (no step index). -/
@[rocq_alias CoreId]
class CoreId {α : Type _} [PCore α] (x : α) where
  core_id : pcore x = some x
export CoreId (core_id)

variable (SI) in
@[indexed, rocq_alias Exclusive]
class Exclusive (x : α) where
  exclusive0_l y : ¬✓{0} x • y
export Exclusive (exclusive0_l)

variable (SI) in
@[indexed, rocq_alias Cancelable]
class Cancelable (x : α) where
  cancelableN {n} {y z : α} : ✓{n} x • y → x • y ≡{n}≡ x • z → y ≡{n}≡ z
export Cancelable (cancelableN)
#rocq_ignore Cancelable_proper "Derived from nonexpansivity"

variable (SI) in
@[indexed, rocq_alias IdFree]
class IdFree (x : α) where
  id_free0_r y : ✓{0} x → ¬x • y ≡{0}≡ x
export IdFree (id_free0_r)
#rocq_ignore IdFree_proper "Derived from nonexpansivity"

@[rocq_alias cmra_pcore_l]
theorem pcore_l {x cx : α} (e : pcore x = some cx) : cx • x = x := pcore_op_left e

@[rocq_alias cmra_pcore_idemp]
theorem pcore_idemp {x cx : α} (e : pcore x = some cx) : pcore cx = some cx := pcore_idem e

@[rocq_alias cmra_extend]
def extend' {n} {x y₁ y₂ : α} (v : ✓{n} x) (e : x ≡{n}≡ y₁ • y₂) :
    Σ' z₁ z₂, x = (z₁ • z₂ : α) ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ :=
  let ⟨z₁, z₂, hx, hz, hw⟩ := extend (y₁ := y₁) (y₂ := y₂) v e
  ⟨z₁, z₂, hx, hz, hw⟩

@[rocq_alias cmra_validN_op_l]
theorem validN_op_l {n} {x y : α} : ✓{n} (x • y) → ✓{n} x := validN_op_left

@[rocq_alias cmra_valid_validN]
theorem valid_validN {x : α} : ✓ x ↔ ∀ (n), ✓{n} x := valid_iff_validN

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
  ne _ x₁ _ e₁ y₁ y₂ e₂ := match y₁, y₂, e₂ with
    | none, none, _ => e₁
    | some _, some y₂, e₂ =>
      ((op_ne (x := x₁)).ne e₂).trans (Dist.of_eq comm |>.trans <|
        ((op_ne (x := y₂)).ne e₁).trans (Dist.of_eq comm))

#rocq_ignore cmra_opM_proper "Derived from nonexpansivity"

#rocq_ignore CoreId_proper "OFE is Leibniz; use equality"

/-! ## Validity -/

-- NOTE: The linter complains about this name, but it is correct.
set_option linter.iris.dupNamespace false in
theorem _root_.Iris.Valid.Valid.validN {n} : ✓ (x : α) → ✓{n} x := (valid_iff_validN.1 · _)
protected theorem Valid.validN {n} : ✓ (x : α) → ✓{n} x := Iris.Valid.Valid.validN

theorem valid_mapN {x y : α} (f : ∀ (n), ✓{n} x → ✓{n} y) (v : ✓ x) : ✓ y :=
  valid_iff_validN.mpr fun n => f n v.validN

@[rocq_alias cmra_validN_ne']
theorem validN_dist_iff {n} {x y : α} (e : x ≡{n}≡ y) : ✓{n} x ↔ ✓{n} y :=
  ⟨validN_ne e, validN_ne e.symm⟩
theorem _root_.Iris.OFE.Dist.validN {n} : (x : α) ≡{n}≡ y → (✓{n} x ↔ ✓{n} y) := validN_dist_iff

#rocq_ignore cmra_validN_proper "OFE is Leibniz; use equality"
#rocq_ignore cmra_valid_proper "OFE is Leibniz; use equality"

@[rocq_alias cmra_validN_le]
theorem validN_of_le {n n'} {x : α} (le : n' ≤ n) : ✓{n} x → ✓{n'} x :=
  (validN_le · le)

@[rocq_alias cmra_validN_lt]
theorem validN_of_lt {n n'} {x : α} (lt : n' < n) : ✓{n} x → ✓{n'} x :=
  validN_of_le (SIdx.lt_le_incl lt)

/-- The successor form of `validN_of_le`; a field of `Valid` before the step index was
generalized, since it does not imply `validN_le` at limit indices. -/
theorem validN_succ [SIdxSucc] {n} {x : α} : ✓{succᵢ n} x → ✓{n} x :=
  validN_of_le SIdx.le_succ_diag_r

theorem valid0_of_validN {n} {x : α} : ✓{n} x → ✓{0} x := validN_of_le SIdx.le_0_l

@[rocq_alias cmra_validN_op_r]
theorem validN_op_right {n} {x y : α} : ✓{n} (x • y) → ✓{n} y :=
  fun v => validN_op_left (comm' (x := x) (y := y) ▸ v)

@[rocq_alias cmra_valid_op_r]
theorem valid_op_right (x y : α) : ✓ (x • y) → ✓ y := valid_mapN fun _ => validN_op_right

@[indexed, rocq_alias cmra_valid_op_l]
theorem valid_op_left {x y : α} : ✓ (x • y) → ✓ x :=
  fun v => valid_op_right y x (comm' (x := x) (y := y) ▸ v)

theorem validN_opM {n} {x : α} {my : Option α} : ✓{n} (x •? my) → ✓{n} x := match my with
  | none => id  | some _ => validN_op_left

theorem valid_opM {x : α} {my : Option α} : ✓ (x •? my) → ✓ x := match my with
  | none => id  | some _ => valid_op_left

theorem validN_op_opM_left {n} {mz : Option α} : ✓{n} (x • y : α) •? mz → ✓{n} x •? mz := match mz with
  | .none => validN_op_left
  | .some z => fun h =>
    have := calc
      (x • y) • z ≡{n}≡ x • (y • z) := op_assocN.symm
      _           ≡{n}≡ x • (z • y) := op_right_dist x op_commN
      _           ≡{n}≡ (x • z) • y := op_assocN
    validN_op_left ((Dist.validN this).mp h)

theorem validN_op_opM_right {n} {mz : Option α} (h : ✓{n} (x • y : α) •? mz) : ✓{n} y •? mz :=
  validN_op_opM_left (validN_ne (opM_left_dist mz op_commN) h)

/-! ## Core -/

#rocq_ignore cmra_pcore_proper "OFE is Leibniz; use equality"

@[rocq_alias cmra_op_ne']
instance cmra_op_ne2 : NonExpansive₂ (op (α := α)) where
  ne _ _ _ e₁ _ _ e₂ := e₁.op e₂

#rocq_ignore cmra_pcore_proper' "OFE is Leibniz; use equality"

@[rocq_alias cmra_pcore_l']
theorem pcore_op_left' {x : α} {cx} (e : pcore x = some cx) : cx • x = x := pcore_l e

@[rocq_alias cmra_pcore_r]
theorem pcore_op_right {x : α} {cx} (e : pcore x = some cx) : x • cx = x := comm'.trans (pcore_l e)

@[rocq_alias cmra_pcore_r']
theorem pcore_op_right' {x : α} {cx} (e : pcore x = some cx) : x • cx = x := pcore_op_right e

@[rocq_alias cmra_pcore_idemp']
theorem pcore_idem' {x : α} {cx} (e : pcore x = some cx) : pcore cx = some cx := pcore_idemp e

@[rocq_alias cmra_pcore_dup]
theorem pcore_op_self {x : α} {cx} (e : pcore x = some cx) : cx • cx = cx :=
  pcore_op_right' (pcore_idem e)

@[rocq_alias cmra_pcore_dup']
theorem pcore_op_self' {x : α} {cx} (e : pcore x = some cx) : cx • cx = cx := pcore_op_self e

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
  fun h => Exclusive.exclusive0_l _ (validN_of_le SIdx.le_0_l h)

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

@[rocq_alias cmra_core_r]
theorem op_core (x : α) : x • core x = x := pcore_op_right (pcore_eq_core x)
@[rocq_alias cmra_core_l]
theorem core_op (x : α) : core x • x = x := comm'.trans (op_core x)

theorem op_core_dist {n} (x : α) : x • core x ≡{n}≡ x := Dist.of_eq (op_core x)
theorem core_op_dist {n} (x : α) : core x • x ≡{n}≡ x := Dist.of_eq (core_op x)

@[rocq_alias cmra_core_dup]
theorem core_op_core {x : α} : core x • core x = core x := pcore_op_self (pcore_eq_core x)
@[rocq_alias cmra_core_validN]
theorem validN_core {n} {x : α} (v : ✓{n} x) : ✓{n} core x := pcore_validN (pcore_eq_core x) v
@[rocq_alias cmra_core_valid]
theorem valid_core {x : α} (v : ✓ x) : ✓ core x := pcore_valid (pcore_eq_core x) v

@[rocq_alias cmra_core_core_id]
instance (y : α) : CoreId (core y) := CoreId.of_pcore_eq_some (pcore_eq_core _)

@[rocq_alias cmra_core_ne]
theorem core_ne : NonExpansive (core : α → α) where
  ne n x₁ x₂ H := by
    change some (core x₁) ≡{n}≡ some (core x₂)
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

instance instOrderReflOfIsTotal : OrderRefl α where
  ord_refl x :=
    (congrArg (x ≼ₒ ·) (core_op x)).mp ((pcore_increasing (pcore_eq_core x)).increasing x)

end total

/-! ## Discrete elements -/

@[rocq_alias cmra_op_discrete]
theorem discrete_op {x y : α} (Hv : ✓{0} x • y) [Hx : DiscreteE x] [Hy : DiscreteE y] :
    DiscreteE (x • y) where
  discrete h := by
    obtain ⟨_w, _t, wt, wx, ty⟩ := extend ((Dist.validN h).mp Hv) h.symm
    rw [Hx.discrete wx.symm, Hy.discrete ty.symm, wt]

end ORA

namespace ORA
export Ordered (OrderN Order ordN_trans ord_trans ordN_of_ord)

/-- `OrderRefl.ord_refl` restated with instance-implicit binders (the projection takes its `SIdx`
instance implicitly, so it gets stuck when nothing else fixes it). -/
@[indexed]
theorem ord_refl {α : Type _} [Ordered α] [OrderRefl α] (x : α) : x ≼ₒ x :=
  OrderRefl.ord_refl x
end ORA

/-! ## The extension inclusion -/

namespace ORA

variable [RA α] [ORA α]

@[indexed, rocq_alias cmra_valid_included]
theorem valid_of_inc {x y : α} : x ≼ y → ✓ y → ✓ x
  | ⟨_, hz⟩, v => valid_op_left (hz ▸ v)

@[rocq_alias cmra_validN_includedN]
theorem validN_of_incN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne hz v)

@[rocq_alias cmra_validN_included]
theorem validN_of_inc {n} {x y : α} : x ≼ y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne hz.dist v)

@[rocq_alias cmra_included_pcore]
theorem pcore_inc_self {x : α} {cx} (e : pcore x = some cx) : cx ≼ x := ⟨x, (pcore_op_left e).symm⟩

@[rocq_alias core_id_extract]
theorem op_core_right_of_inc {x y : α} [CoreId x] : x ≼ y → x • y = y
  | ⟨z, hz⟩ => hz ▸ assoc'.trans (congrArg (· • z) (op_self x))

theorem op_core_left_of_inc {x y : α} [CoreId x] (le : x ≼ y) : y • x = y :=
  comm'.trans (op_core_right_of_inc le)

@[rocq_alias cmra_included_dist_l]
theorem included_dist_l {n} {x1 x2 x1' : α} :
    x1 ≼ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ x2' ∧ x2' ≡{n}≡ x2
  | ⟨y, hy⟩, e => ⟨x1' • y, inc_op_left x1' y, e.op_l.trans hy.symm.dist⟩

@[rocq_alias exclusive_includedN]
theorem not_valid_of_exclN_inc {n} {x : α} [Exclusive x] {y} : x ≼{n} y → ¬✓{n} y
  | ⟨_, hz⟩, v => not_valid_exclN_op_left (validN_ne hz v)

@[rocq_alias exclusive_included]
theorem not_valid_of_excl_inc {x : α} [Exclusive x] {y} : x ≼ y → ¬✓ y
  | ⟨_, hz⟩, v => Exclusive.exclusive0_l _ <| hz ▸ v.validN

theorem incN_extend {n sn} {x y : α} (_ : IsSucc n sn) (v : ✓{n} y) :
    x ≼{n} y → ∃ z, z ≼{sn} y ∧ z ≡{n}≡ x
  | ⟨_, hw⟩ =>
    let ⟨z₁, z₂, hy, hz₁, _⟩ := extend v hw
    ⟨z₁, ⟨z₂, hy.dist⟩, hz₁⟩

theorem incN_map {β : Type _} [RA β] [ORA β] (f : α → β) [NonExpansive f]
    (hop : ∀ x y, f (x • y) = f x • f y) {n} {x y : α} : x ≼{n} y → f x ≼{n} f y
  | ⟨z, hz⟩ => ⟨f z, (NonExpansive.ne hz).trans (hop x z).dist⟩

theorem inc_map {β : Type _} [RA β] (f : α → β)
    (hop : ∀ x y, f (x • y) = f x • f y) {x y : α} : x ≼ y → f x ≼ f y
  | ⟨z, hz⟩ => ⟨f z, (congrArg f hz).trans (hop x z)⟩

section total
variable [IsTotal α]

theorem inc_refl (x : α) : x ≼ x := ⟨core x, (op_core x).symm⟩

theorem incN_refl {n} (x : α) : x ≼{n} x := incN_of_inc _ (inc_refl _)

#rocq_ignore cmra_included_preorder
  "Reflexivity is inc_refl; transitivity is the Trans instance"
#rocq_ignore cmra_includedN_preorder
  "Reflexivity is incN_refl; transitivity is the Trans instance"

theorem incN_of_dist {n} {x y : α} (h : x ≡{n}≡ y) : x ≼{n} y := incN_ne .rfl h (incN_refl x)
theorem _root_.Iris.OFE.Dist.to_incN {n} {x y : α} : x ≡{n}≡ y → x ≼{n} y := incN_of_dist

@[rocq_alias cmra_included_core]
theorem core_inc_self {x : α} : core x ≼ x := ⟨x, (core_op x).symm⟩

end total

section discrete

@[rocq_alias cmra_discrete_included_iff]
theorem inc_iff_incN [OFE.Discrete α] (n) {x y : α} : x ≼ y ↔ x ≼{n} y :=
  ⟨incN_of_inc _, fun ⟨z, hz⟩ => ⟨z, discrete hz⟩⟩

@[rocq_alias cmra_discrete_included_iff_0]
theorem inc_0_iff_incN [OFE.Discrete α] (n) {x y : α} : x ≼{0} y ↔ x ≼{n} y :=
  ⟨fun ⟨z, hz⟩ => ⟨z, (discrete hz).dist⟩, inc0_of_incN⟩

theorem inc_of_inc0 [OFE.Discrete α] {x y : α} : x ≼{0} y → x ≼ y := (inc_iff_incN 0).mpr

@[rocq_alias cmra_discrete_included_l]
theorem discrete_inc_l {x y : α} [HD : DiscreteE x] (Hv : ✓{0} y) (Hle : x ≼{0} y) :
    x ≼ y :=
  have ⟨_, hz⟩ := Hle
  let ⟨_, t, wt, wx, _⟩ := extend Hv hz
  ⟨t, wt.trans (congrArg (· • t) (HD.discrete wx.symm).symm)⟩

@[rocq_alias cmra_discrete_included_r]
theorem discrete_inc_r {x y : α} [HD : DiscreteE y] : x ≼{0} y → x ≼ y
  | ⟨z, hz⟩ => ⟨z, HD.discrete hz⟩

end discrete

end ORA

/-- A classical resource algebra: composition, core and validity together with the laws
relating them, and the monotonicity of the partial core along frames. It is not itself an
ordered resource algebra; `ORA.ofCMRAData` makes one of it, taking the order to be the extension
inclusion. -/
@[indexed, rocq_alias CmraMixin]
structure CMRAData (α : Type _) [OFE α] [RA α]
    extends Valid α, OpNE α, PCoreNE α, ValidNE α where
  validN_op_left {n} {x y : α} : ✓{n} (x • y) → ✓{n} x
  extend {n} {x y₁ y₂ : α} : ✓{n} x → x ≡{n}≡ y₁ • y₂ →
    Σ' z₁ z₂ : α, x = z₁ • z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂
  pcore_op_mono {x cx : α} : PCore.pcore x = some cx → ∀ y, ∃ cy : α, PCore.pcore (x • y) = some (cx • cy)

namespace CMRAData
open ORA

/-- The frame law follows from monotonicity of the partial core along the extension inclusion,
the form of the law in Iris-Rocq (`cmra_pcore_mono`). -/
theorem pcore_op_mono_of_pcore_mono [Op α] [PCore α]
    (h : ∀ {x y cx : α}, x ≼ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ cy)
    {x cx : α} (e : pcore x = some cx) (y) : ∃ cy : α, pcore (x • y) = some (cx • cy) :=
  let ⟨_, hcy, z, hz⟩ := h (inc_op_left _ y) e
  ⟨z, hcy.trans (congrArg some hz)⟩

theorem pcore_op_mono_of_core_mono [Op α] [PCore α] [IsTotal α]
    (h : ∀ x y : α, x ≼ y → core x ≼ core y)
    {x cx : α} (e : pcore x = some cx) (y) : ∃ cy : α, pcore (x • y) = some (cx • cy) :=
  pcore_op_mono_of_pcore_mono (fun {x y cx} hxy e =>
    have hcx : cx = core x := Option.some.inj (e.symm.trans (pcore_eq_core x))
    ⟨core y, pcore_eq_core y, hcx ▸ h x y hxy⟩) e y

/-- Converse of `pcore_op_mono_of_pcore_mono`: the frame law gives monotonicity of the partial core. -/
theorem pcore_mono_of_pcore_op_mono [Op α] [PCore α]
    (h : ∀ {x cx : α}, pcore x = some cx → ∀ y, ∃ cy : α, pcore (x • y) = some (cx • cy))
    {x y cx : α} : x ≼ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ cy
  | ⟨z, hw⟩, e =>
    let ⟨w, hw'⟩ := h e z
    ⟨cx • w, hw ▸ hw', w, rfl⟩

theorem core_op_mono_of_pcore_op_mono [Op α] [PCore α] [IsTotal α]
    (h : ∀ {x cx : α}, pcore x = some cx → ∀ y, ∃ cy : α, pcore (x • y) = some (cx • cy))
    (x y : α) : core x ≼ core (x • y) :=
  let ⟨cy, hcy⟩ := h (pcore_eq_core x) y
  ⟨cy, Option.some.inj ((pcore_eq_core _).symm.trans hcy)⟩

theorem core_mono_of_pcore_op_mono [Op α] [PCore α] [IsTotal α]
    (h : ∀ {x cx : α}, pcore x = some cx → ∀ y, ∃ cy : α, pcore (x • y) = some (cx • cy))
    {x y : α} : x ≼ y → core x ≼ core y
  | ⟨z, hz⟩ => hz ▸ core_op_mono_of_pcore_op_mono h x z

/-! The constructions below take the laws of a `CMRAData` record as hypotheses, so they need no instance
of it (Mathlib-style constructors); `ORA.ofCMRAData` instantiates them. -/

section build
variable [OFE α] [RA α] [Valid SI α] [OpNE α] [PCoreNE α] [ValidNE α]
variable (hv : ∀ {n : SI} {x y : α}, ✓{n} (x • y) → ✓{n} x)
variable (hpm : ∀ {x cx : α}, pcore x = some cx → ∀ y, ∃ cy : α, pcore (x • y) = some (cx • cy))

omit [OpNE α] [PCoreNE α] in
include hv in
theorem validN_of_incN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => hv (validN_ne hz v)

omit [OpNE α] [PCoreNE α] [ValidNE α] in
theorem incN_extend
    (he : ∀ {n} {x y₁ y₂ : α}, ✓{n} x → x ≡{n}≡ y₁ • y₂ →
      Σ' z₁ z₂ : α, x = z₁ • z₂ ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂)
    {n sn} {x y : α} (_ : IsSucc n sn) (v : ✓{n} y) :
    x ≼{n} y → ∃ z, z ≼{sn} y ∧ z ≡{n}≡ x
  | ⟨_, hw⟩ =>
    let ⟨z₁, z₂, hy, hz₁, _⟩ := he v hw
    ⟨z₁, ⟨z₂, hy.dist⟩, hz₁⟩

omit [Valid α] [ValidNE α] in
include hpm in
theorem pcore_monoN' {n} {x y : α} {cx} :
    x ≼{n} y → pcore x ≡{n}≡ some cx → ∃ cy, pcore y = some cy ∧ cx ≼{n} cy
  | ⟨z, hz⟩, e =>
    let ⟨_, hw, ew⟩ := OFE.dist_some e
    let ⟨t, ht⟩ := hpm hw z
    let ⟨r, hr, er⟩ := PCoreNE.pcore_ne hz.symm ht
    ⟨r, hr, incN_ne ew.symm er (incN_op_left n _ t)⟩

omit [Valid α] [ValidNE α] in
include hpm in
theorem pcore_monoN {n} {x y : α} {cx} (h : x ≼{n} y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼{n} cy :=
  pcore_monoN' hpm h (Dist.of_eq e)

end build

section extOrder
attribute [local instance] extOrdered

theorem increasing [OFE α] [Op α] [OpNE α] (x : α) : Increasing x where
  increasing y := inc_op_right x y

/-- The ordered resource algebra of a `CMRAData` record: the order is the extension inclusion. -/
@[reducible] def toORA [OFE α] [RA α] (d : CMRAData α) : ORA α where
  toValid := d.toValid
  toOpNE := d.toOpNE
  toPCoreNE := d.toPCoreNE
  toValidNE := d.toValidNE
  toOrdered := letI := d.toOpNE; extOrdered (α := α)
  toOrderedNE := letI := d.toOpNE; extOrderedNE (α := α)
  validN_op_left := d.validN_op_left
  extend := d.extend
  op_monoN_left_ord := letI := d.toOpNE; op_monoN_left
  op_mono_left_ord := op_mono_left
  validN_of_ordN := letI := d.toValid; letI := d.toOpNE; letI := d.toPCoreNE; letI := d.toValidNE
    validN_of_incN d.validN_op_left
  pcore_monoN_ord := letI := d.toOpNE; letI := d.toPCoreNE; pcore_monoN d.pcore_op_mono
  pcore_mono_ord := pcore_mono_of_pcore_op_mono d.pcore_op_mono
  pcore_order_op := fun {_ cx} e y =>
    let ⟨cy, hcy⟩ := d.pcore_op_mono e y
    ⟨cx • cy, hcy, inc_op_left cx cy⟩
  pcore_increasing := fun _ => letI := d.toOpNE; increasing _
  increasing_closed := fun _ _ => letI := d.toOpNE; increasing _
  ordN_extend := letI := d.toValid; letI := d.toOpNE; letI := d.toPCoreNE; letI := d.toValidNE
    incN_extend d.extend

end extOrder

end CMRAData

variable (SI) in
@[indexed, rocq_alias cmra]
class CMRA (α : Type _) [RA α] extends ORA α, IsInc α
instance (priority := low) CMRA.ofIsInc [RA α] [ORA α] [IsInc α] : CMRA α := {}

@[reducible] def ORA.ofCMRAData [OFE α] [RA α] (d : CMRAData α) : CMRA α :=
  letI := CMRAData.toORA d
  { inc_ord := id, ord_inc := id, ordN_incN := id }

namespace CMRA
open ORA
variable [RA α] [CMRA α]

theorem ord_of_ord0 [OFE.Discrete α] {x y : α} (h : x ≼ₒ{0} y) : x ≼ₒ y :=
  inc_iff_ord.mp (inc_of_inc0 (incN_iff_ordN.mpr h))

end CMRA

section
open ORA
variable [OFE α] [Op α] [OpNE α]

omit [OpNE α] in
theorem Included.incN {n} {x y : α} : x ≼ y → x ≼{n} y := incN_of_inc _
theorem Included.trans : (x : α) ≼ y → y ≼ z → x ≼ z := inc_trans
theorem IncludedN.trans {n} : (x : α) ≼{n} y → y ≼{n} z → x ≼{n} z := incN_trans
omit [OpNE α] in
theorem IncludedN.le {n n'} {x y : α} : n' ≤ n → x ≼{n} y → x ≼{n'} y := incN_of_incN_le
omit [OpNE α] in
theorem IncludedN.succ [SIdxSucc] {n} {x y : α} : x ≼{succᵢ n} y → x ≼{n} y := incN_of_incN_succ

end

section
open ORA
variable [RA α] [ORA α]

theorem Included.validN {n} {x y : α} : x ≼ y → ✓{n} y → ✓{n} x := validN_of_inc
theorem IncludedN.validN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x := validN_of_incN

variable [IsTotal α]

@[refl] theorem Included.rfl {x : α} : x ≼ x := inc_refl x
@[refl] theorem IncludedN.rfl {n} {x : α} : x ≼{n} x := incN_refl x

end

/-! ## Discrete and affine algebras -/

namespace ORA
variable [RA α] [ORA α]

variable (SI) in
@[indexed, rocq_alias CmraDiscrete]
class Discrete (α : Type _) [RA α] [ORA α] extends OFE.Discrete α where
  discrete_valid {x : α} : ✓{0} x → ✓ x
  discrete_ord {x y : α} : x ≼ₒ{0} y → x ≼ₒ y
export Discrete (discrete_valid discrete_ord)
#rocq_ignore discrete_validN_instance "Use CMRA instance"

end ORA

/-! ## Unital algebras -/

/-- An ordered unital resource algebra: the step-indexed mixin over `URA α`. -/
@[indexed]
class UORA (SI : stepindex (Type _)) [instSI : SIdx SI] (α : Type _) [URA α]
    extends ORA α, OrderRefl α where
  unit_valid {SI} : ✓ (UnitOp.unit : α)
#rocq_ignore Unit "Lean uses the UCMRA.unit field; no separate class needed."
#rocq_ignore ucmra_cmraR "Folded into Lean's UCMRA extends CMRA."
#rocq_ignore ucmra_ofeO "Folded into Lean's UCMRA → OFE."

/-- The validity of the unit of a classical unital resource algebra; the input of
`UORA.ofUCMRAData` (the unit and its SI-free laws live in `URA α`). -/
@[indexed, rocq_alias UcmraMixin]
structure UCMRAData (α : Type _) [URA α] [CMRA α] : Prop where
  unit_valid : ✓ (UnitOp.unit : α)

variable (SI) in
@[indexed, rocq_alias ucmra]
class UCMRA (α : Type _) [URA α] extends CMRA α, UORA α
instance (priority := low) UCMRA.ofIsInc [URA α] [UORA α] [IsInc α] : UCMRA α := {}

@[reducible] def UORA.ofUCMRAData [URA α] [CMRA α] (d : UCMRAData α) : UCMRA α where
  unit_valid := d.unit_valid
  ord_refl _ := IncOrd.inc_ord ⟨UnitOp.unit, (Op.comm.trans URA.unit_left_id).symm⟩

/-- `ε` is a left identity with core `ε` (SI-free part of a unit). -/
class IsRAUnit [RA α] (ε : α) : Prop where
  unit_left_id : ε • x = x
  pcore_unit : PCore.pcore ε = some ε

variable (SI) in
/-- `ε` is a valid unit: `IsRAUnit ε` plus validity, which is step-indexed. -/
@[indexed]
class IsUnit [RA α] [ORA α] (ε : α) [IsRAUnit ε] : Prop where
  unit_valid : ✓ ε

instance [URA α] : IsRAUnit (UnitOp.unit : α) where
  unit_left_id := URA.unit_left_id
  pcore_unit := URA.pcore_unit

instance [URA α] [UORA α] : IsUnit (UnitOp.unit : α) where
  unit_valid := UORA.unit_valid

export UnitOp (unit)

namespace ORA
export URA (unit_left_id pcore_unit)

/-- `UORA.unit_valid` restated with instance-implicit binders. -/
theorem unit_valid [URA α] [UORA α] : ✓ (unit : α) := UORA.unit_valid

variable [RA α] [ORA α]

/-! ## Order -/

section orderN
omit [RA α] [ORA α]
variable [OFE α] [Ordered SI α] [OrderedNE α]

theorem ordN_of_ordN_of_dist {n} (h : (a : α) ≼ₒ{n} b) (e : b ≡{n}≡ c) : a ≼ₒ{n} c := ordN_ne .rfl e h

instance instTransOrderNDist {n} : Trans (OrderN (α := α) n) (Dist n) (OrderN n) where
  trans := ordN_of_ordN_of_dist

theorem ordN_of_dist_of_ordN {n} (e : (a : α) ≡{n}≡ b) (h : b ≼ₒ{n} c) : a ≼ₒ{n} c :=
  ordN_ne e.symm .rfl h

instance {n} : Trans (Dist (α := α) n) (OrderN n) (OrderN n) where
  trans := ordN_of_dist_of_ordN

omit [OFE α] [OrderedNE α] instSI in
theorem _root_.Iris.Ordered.Order.ordN {n} {x y : α} : x ≼ₒ y → x ≼ₒ{n} y := ordN_of_ord _

theorem ordN_iff_left {n} (e : (a : α) ≡{n}≡ b) : a ≼ₒ{n} c ↔ b ≼ₒ{n} c :=
  ⟨ordN_ne e .rfl, ordN_ne e.symm .rfl⟩
theorem _root_.Iris.OFE.Dist.ordN_l {n} : (a : α) ≡{n}≡ b → (a ≼ₒ{n} c ↔ b ≼ₒ{n} c) := ordN_iff_left

theorem ordN_iff_right {n} (e : (b : α) ≡{n}≡ c) : a ≼ₒ{n} b ↔ a ≼ₒ{n} c :=
  ⟨ordN_ne .rfl e, ordN_ne .rfl e.symm⟩
theorem _root_.Iris.OFE.Dist.ordN_r {n} : (b : α) ≡{n}≡ c → (a ≼ₒ{n} b ↔ a ≼ₒ{n} c) := ordN_iff_right

theorem ordN_dist_iff {n} (ea : (a : α) ≡{n}≡ a') (eb : (b : α) ≡{n}≡ b') : a ≼ₒ{n} b ↔ a' ≼ₒ{n} b' :=
  ⟨ordN_ne ea eb, ordN_ne ea.symm eb.symm⟩
theorem _root_.Iris.OFE.Dist.ordN {n} :
    (a : α) ≡{n}≡ a' → b ≡{n}≡ b' → (a ≼ₒ{n} b ↔ a' ≼ₒ{n} b') := ordN_dist_iff

omit [OFE α] [OrderedNE α] instSI in
theorem _root_.Iris.Ordered.Order.trans : (x : α) ≼ₒ y → y ≼ₒ z → x ≼ₒ z := ord_trans

instance instTransOrder : Trans (Order (α := α)) (Order) (Order) where
  trans := ord_trans

omit [OFE α] [OrderedNE α] instSI in
theorem _root_.Iris.Ordered.OrderN.trans {n} : (x : α) ≼ₒ{n} y → y ≼ₒ{n} z → x ≼ₒ{n} z := ordN_trans

instance instTransOrderN {n} : Trans (OrderN (α := α) n) (OrderN n) (OrderN n) where
  trans := ordN_trans

theorem ordN_of_ordN_le {n n'} {x y : α} (l1 : n' ≤ n) : x ≼ₒ{n} y → x ≼ₒ{n'} y :=
  (ordN_le · l1)
theorem ord0_of_ordN {n} {x y : α} : x ≼ₒ{n} y → x ≼ₒ{0} y := ordN_of_ordN_le SIdx.le_0_l
theorem _root_.Iris.Ordered.OrderN.le {n n'} {x y : α} :
    n' ≤ n → x ≼ₒ{n} y → x ≼ₒ{n'} y := ordN_of_ordN_le

theorem ordN_of_ordN_succ [SIdxSucc] {n} {x y : α} : x ≼ₒ{succᵢ n} y → x ≼ₒ{n} y :=
  ordN_of_ordN_le SIdx.le_succ_diag_r
theorem _root_.Iris.Ordered.OrderN.succ [SIdxSucc] {n} {x y : α} : x ≼ₒ{succᵢ n} y → x ≼ₒ{n} y :=
  ordN_of_ordN_succ

section ordRefl
variable [OrderRefl α]

omit [OFE α] [OrderedNE α] in
theorem ordN_refl {n} (x : α) : x ≼ₒ{n} x := (ord_refl x).ordN
omit [OFE α] [OrderedNE α] in
@[refl] theorem _root_.Iris.Ordered.Order.rfl {x : α} : x ≼ₒ x := ord_refl x
omit [OFE α] [OrderedNE α] in
@[refl] theorem _root_.Iris.Ordered.OrderN.rfl {n} {x : α} : x ≼ₒ{n} x := ordN_refl x

theorem ordN_of_dist {n} {x y : α} (h : x ≡{n}≡ y) : x ≼ₒ{n} y := ordN_ne .rfl h (ordN_refl x)
theorem _root_.Iris.OFE.Dist.to_ordN {n} {x y : α} : x ≡{n}≡ y → x ≼ₒ{n} y := ordN_of_dist

end ordRefl

end orderN

theorem valid_of_ord {x y : α} (h : x ≼ₒ y) : ✓ y → ✓ x :=
  valid_mapN fun n => validN_of_ordN (ordN_of_ord n h)

theorem _root_.Iris.Ordered.OrderN.validN {n} {x y : α} : x ≼ₒ{n} y → ✓{n} y → ✓{n} x :=
  validN_of_ordN

theorem validN_of_ord {n} {x y : α} (h : x ≼ₒ y) : ✓{n} y → ✓{n} x :=
  validN_of_ordN (ordN_of_ord n h)
theorem _root_.Iris.Ordered.Order.validN {n} {x y : α} : x ≼ₒ y → ✓{n} y → ✓{n} x := validN_of_ord

theorem pcore_mono_ord' {x y : α} {cx} (le : x ≼ₒ y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼ₒ cy :=
  pcore_mono_ord le e

theorem pcore_monoN_ord' {n} {x y : α} {cx} (h : x ≼ₒ{n} y) (e : pcore x ≡{n}≡ some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼ₒ{n} cy :=
  let ⟨_, hw, ew⟩ := OFE.dist_some e
  let ⟨cy, hcy, hi⟩ := pcore_monoN_ord h hw
  ⟨cy, hcy, ordN_of_dist_of_ordN ew hi⟩

@[indexed, rocq_alias cmra_pcore_mono]
theorem pcore_mono [OrdInc α] {x y : α} :
    x ≼ y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ cx ≼ cy
  | ⟨z, hz⟩, e =>
    let ⟨cy, hcy, o⟩ := pcore_order_op e z
    ⟨cy, hz ▸ hcy, OrdInc.ord_inc o⟩

@[rocq_alias cmra_pcore_mono']
theorem pcore_mono' [OrdInc α] {x y : α} {cx} (le : x ≼ y) (e : pcore x = some cx) :
    ∃ cy, pcore y = some cy ∧ cx ≼ cy :=
  pcore_mono le e

@[rocq_alias cmra_pcore_monoN']
theorem pcore_monoN' [OrdInc α] {n} {x y : α} {cx} :
    x ≼{n} y → pcore x ≡{n}≡ some cx → ∃ cy, pcore y = some cy ∧ cx ≼{n} cy
  | ⟨z, hz⟩, e =>
    let ⟨_, hw, ew⟩ := OFE.dist_some e
    let ⟨_, ht, o⟩ := pcore_order_op hw z
    let ⟨r, hr, er⟩ := pcore_ne' hz.symm ht
    ⟨r, hr, incN_ne ew.symm er (incN_of_inc n (OrdInc.ord_inc o))⟩

@[indexed]
theorem pcore_op_mono [OrdInc α] {x cx : α} (e : pcore x = some cx) (y : α) :
    ∃ cy, pcore (x • y) = some (cx • cy) :=
  let ⟨_, h, o⟩ := pcore_order_op e y
  let ⟨z, hz⟩ := OrdInc.ord_inc o
  ⟨z, h.trans (congrArg some hz)⟩

theorem op_monoN_right_ord {n} {x y} (z : α) (h : x ≼ₒ{n} y) : z • x ≼ₒ{n} z • y :=
  (op_commN.ordN op_commN).1 (op_monoN_left_ord z h)

theorem op_mono_right_ord {x y} (z : α) (h : x ≼ₒ y) : z • x ≼ₒ z • y := by
  rw [comm' (x := z) (y := x), comm' (x := z) (y := y)]; exact op_mono_left_ord z h

theorem op_monoN_ord {n} {x x' y y' : α} (hx : x ≼ₒ{n} x') (hy : y ≼ₒ{n} y') :
    x • y ≼ₒ{n} x' • y' :=
  (op_monoN_left_ord _ hx).trans (op_monoN_right_ord _ hy)

theorem op_mono_ord {x x' y y' : α} (hx : x ≼ₒ x') (hy : y ≼ₒ y') : x • y ≼ₒ x' • y' :=
  (op_mono_left_ord _ hx).trans (op_mono_right_ord _ hy)

theorem op?_monoN_left_ord {n} {x y : α} (mz : Option α) (h : x ≼ₒ{n} y) : x •? mz ≼ₒ{n} y •? mz :=
  match mz with
  | none => h
  | some z => op_monoN_left_ord z h

theorem op?_mono_left_ord {x y : α} (mz : Option α) (h : x ≼ₒ y) : x •? mz ≼ₒ y •? mz :=
  match mz with
  | none => h
  | some z => op_mono_left_ord z h

theorem _root_.Iris.Ordered.OrderNR.op_left {n} {x y : α} (z : α) :
    x ≼ₒ*{n} y → x • z ≼ₒ*{n} y • z
  | .inl e => .inl e.op_l
  | .inr h => .inr (op_monoN_left_ord z h)

theorem _root_.Iris.Ordered.OrderR.op_left {x y : α} (z : α) : x ≼ₒ* y → x • z ≼ₒ* y • z
  | .inl e => .inl (e ▸ rfl)
  | .inr h => .inr (op_mono_left_ord z h)

theorem _root_.Iris.Ordered.OrderNR.validN {n} {x y : α} : x ≼ₒ*{n} y → ✓{n} y → ✓{n} x
  | .inl e, v => validN_ne e.symm v
  | .inr h, v => validN_of_ordN h v

theorem _root_.Iris.Ordered.OrderR.validN {n} {x y : α} : x ≼ₒ* y → ✓{n} y → ✓{n} x
  | .inl e, v => e ▸ v
  | .inr h, v => validN_of_ord h v

theorem op_extend_ord {n sn} {x y₁ y₂ : α} (hs : IsSucc n sn) (v : ✓{n} x) (h : y₁ • y₂ ≼ₒ{n} x) :
    ∃ z₁ z₂ : α, z₁ • z₂ ≼ₒ{sn} x ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂ :=
  let ⟨_, hx', e⟩ := ordN_extend hs v h
  let ⟨z₁, z₂, hz, hz₁, hz₂⟩ := extend (validN_of_ordN (ordN_of_ordN_le (SIdx.lt_le_incl hs.lt) hx') v) e
  ⟨z₁, z₂, hz ▸ hx', hz₁, hz₂⟩

end ORA

/-! ## Increasing elements -/

section
open ORA
variable [RA α] [ORA α]

namespace Increasing

theorem of_ordNR {n} {x y : α} (h : Increasing x) (hxy : x ≼ₒ*{n} y) : Increasing y :=
  increasing_closed h hxy
theorem of_dist {n} {x y : α} (h : Increasing x) (e : x ≡{n}≡ y) : Increasing y :=
  h.of_ordNR (.inl e)
theorem of_ordN {n} {x y : α} (h : Increasing x) (hxy : x ≼ₒ{n} y) : Increasing y :=
  h.of_ordNR (.inr hxy)
theorem of_ord {x y : α} (h : Increasing x) (hxy : x ≼ₒ y) : Increasing y :=
  h.of_ordN (ordN_of_ord 0 hxy)
theorem of_ordR {x y : α} (h : Increasing x) : x ≼ₒ* y → Increasing y
  | .inl e => e ▸ h
  | .inr hxy => h.of_ord hxy

theorem ordN {n} {x : α} (h : Increasing x) (y : α) : y ≼ₒ{n} x • y :=
  ordN_of_ord n (h.increasing y)

instance op (x y : α) [Increasing x] [Increasing y] : Increasing (x • y) where
  increasing z := calc
    z ≼ₒ y • z := Increasing.increasing z
    _ ≼ₒ x • (y • z) := Increasing.increasing _
    _ = (x • y) • z := assoc'

end Increasing

instance instIncreasingOfCoreId (x : α) [CoreId x] : Increasing x := pcore_increasing core_id

end

namespace ORA
variable [RA α] [ORA α]

section total
variable [IsTotal α]

@[indexed]
theorem core_ordN_core {n} {x y : α} (le : x ≼ₒ{n} y) : core x ≼ₒ{n} core y :=
  let ⟨_, hcy, icy⟩ := pcore_monoN_ord le (pcore_eq_core x)
  Option.some.inj (hcy.symm.trans (pcore_eq_core y)) ▸ icy

@[indexed]
theorem core_mono_ord {x y : α} (le : x ≼ₒ y) : core x ≼ₒ core y :=
  let ⟨_, hcy, icy⟩ := pcore_mono_ord le (pcore_eq_core x)
  Option.some.inj (hcy.symm.trans (pcore_eq_core y)) ▸ icy

@[indexed]
theorem core_op_mono_ord (x y : α) : core x ≼ₒ core (x • y) :=
  let ⟨_, hcxy, h⟩ := pcore_order_op (pcore_eq_core x) y
  Option.some.inj (hcxy.symm.trans (pcore_eq_core _)) ▸ h

@[rocq_alias cmra_core_monoN]
theorem core_incN_core [OrdInc α] {n} {x y : α} (le : x ≼{n} y) : core x ≼{n} core y :=
  let ⟨_, hcy, icy⟩ := pcore_monoN' le (Dist.of_eq (pcore_eq_core x))
  Option.some.inj (hcy.symm.trans (pcore_eq_core y)) ▸ icy

@[indexed]
theorem core_op_mono [OrdInc α] (x y : α) : core x ≼ core (x • y) :=
  OrdInc.ord_inc (core_op_mono_ord x y)

@[rocq_alias cmra_core_mono]
theorem core_mono [OrdInc α] {x y : α} : x ≼ y → core x ≼ core y
  | ⟨z, hz⟩ => hz ▸ core_op_mono x z

instance increasing_core (x : α) : Increasing (core x) := pcore_increasing (pcore_eq_core x)

end total

/-! ## Composition with increasing elements -/

section increasing

theorem ord_op_right (x y : α) [Increasing x] : y ≼ₒ x • y := Increasing.increasing y
theorem ord_op_left (x y : α) [Increasing y] : x ≼ₒ x • y :=
  comm' (x := y) (y := x) ▸ ord_op_right y x
theorem ordN_op_left (n) (x y : α) [Increasing y] : x ≼ₒ{n} x • y := (ord_op_left x y).ordN
theorem ordN_op_right (n) (x y : α) [Increasing x] : y ≼ₒ{n} x • y := (ord_op_right x y).ordN

theorem pcore_ord_self {x : α} {cx} [Increasing x] (e : pcore x = some cx) : cx ≼ₒ x :=
  pcore_op_left e ▸ ord_op_left cx x

theorem core_ord_self [IsTotal α] {x : α} [Increasing x] : core x ≼ₒ x :=
  pcore_ord_self (pcore_eq_core x)

end increasing

section discreteORA

@[rocq_alias cmra_discrete_valid_iff]
theorem valid_iff_validN' [Discrete α] (n) {x : α} : ✓ x ↔ ✓{n} x :=
  ⟨Valid.validN, fun v => discrete_valid <| validN_of_le SIdx.le_0_l v⟩

@[rocq_alias cmra_discrete_valid_iff_0]
theorem valid_0_iff_validN [Discrete α] (n) {x : α} : ✓{0} x ↔ ✓{n} x :=
  ⟨Valid.validN ∘ discrete_valid, validN_of_le SIdx.le_0_l⟩

theorem ord_iff_ordN [Discrete α] (n) {x y : α} : x ≼ₒ y ↔ x ≼ₒ{n} y :=
  ⟨ordN_of_ord _, fun h => discrete_ord (ord0_of_ordN h)⟩

theorem ord_0_iff_ordN [Discrete α] (n) {x y : α} : x ≼ₒ{0} y ↔ x ≼ₒ{n} y :=
  ⟨fun h => ordN_of_ord n (discrete_ord h), ord0_of_ordN⟩

end discreteORA

section cancelableElements

@[rocq_alias cancelable]
theorem cancelable {x y z : α} [Cancelable x] (v : ✓ (x • y)) (e : x • y = x • z) : y = z :=
  OFE.eq_dist_2 fun _ => cancelableN v.validN e.dist

@[rocq_alias discrete_cancelable]
theorem discrete_cancelable {x : α} [Discrete α]
    (H : ∀ {y z : α}, ✓ (x • y) → x • y = x • z → y = z) : Cancelable x where
  cancelableN {n} {_ _} v e := (H ((valid_iff_validN' n).mpr v) (Discrete.discrete e)).dist

@[rocq_alias cancelable_op]
instance cancelable_op {x y : α} [Cancelable x] [Cancelable y] : Cancelable (x • y) where
  cancelableN {n} {w _} v e :=
    have v1 : ✓{n} x • (y • w) := validN_ne op_assocN.symm v
    have v2 := validN_op_right v1
    cancelableN v2 <| cancelableN v1 <| op_assocN.trans <| e.trans op_assocN.symm

@[rocq_alias exclusive_cancelable]
instance exclusive_cancelable {x : α} [Exclusive x] : Cancelable x where
  cancelableN v _ := absurd v not_valid_exclN_op_left

#rocq_ignore cancelable_proper "OFE is Leibniz; use equality"

theorem op_opM_cancel_dist {n} {x y z : α} [Cancelable x]
    (vxy : ✓{n} x • y) (h : x • y ≡{n}≡ (x • z) •? mw) : y ≡{n}≡ z •? mw :=
  match mw with
  | none => cancelableN vxy h
  | some _ => cancelableN vxy (h.trans (op_assocN.symm))

end cancelableElements

section idFreeElements

theorem IdFree.of_dist {x₁ x₂ : α} {n} (e : x₁ ≡{n}≡ x₂) (h : IdFree x₁) : IdFree x₂ where
  id_free0_r z v := fun h₂ =>
    have ee := Dist.le e SIdx.le_0_l
    have := calc
      x₁ • z ≡{0}≡ x₂ • z := op_left_dist z ee
      _      ≡{0}≡ x₂ := h₂
      _      ≡{0}≡ x₁ := ee.symm
    h.id_free0_r _ ((validN_dist_iff ee).mpr v) this

@[rocq_alias id_free_ne]
theorem _root_.Iris.OFE.Dist.idFree {n} {x₁ x₂ : α} (e : x₁ ≡{n}≡ x₂) : IdFree x₁ ↔ IdFree x₂ :=
  ⟨.of_dist e, .of_dist e.symm⟩

#rocq_ignore id_free_proper "OFE is Leibniz; use equality"

@[rocq_alias id_freeN_r]
theorem id_freeN_r {n n'} {x : α} [IdFree x] {y} (v : ✓{n} x) : ¬(x • y ≡{n'}≡ x) :=
  id_free0_r _ (validN_of_le SIdx.le_0_l v) |>.imp (·.le SIdx.le_0_l)

@[rocq_alias id_freeN_l]
theorem id_freeN_l {n n'} {x : α} [IdFree x] {y} (v : ✓{n} x) : ¬(y • x ≡{n'}≡ x) :=
  id_freeN_r v ∘ comm'.dist.trans

@[rocq_alias id_free_r]
theorem id_free_r {x : α} [IdFree x] {y} (v : ✓ x) : ¬(x • y = x) :=
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

variable {α : Type _} [URA α] [UORA α]

@[rocq_alias ucmra_unit_validN]
theorem unit_validN {n} : ✓{n} (unit : α) := valid_iff_validN.mp (unit_valid) n

theorem unit_left_id_dist {n} (x : α) : unit • x ≡{n}≡ x := unit_left_id.dist

@[rocq_alias ucmra_unit_right_id]
theorem unit_right_id {x : α} : x • unit = x := comm'.trans unit_left_id

theorem unit_right_id_dist {n} (x : α) : x • unit ≡{n}≡ x := comm'.dist.trans (unit_left_id_dist x)

@[rocq_alias ucmra_unit_leastN]
theorem incN_unit {n} {x : α} : unit ≼{n} x := ⟨x, unit_left_id.symm.dist⟩

@[rocq_alias ucmra_unit_least]
theorem inc_unit {x : α} : unit ≼ x := ⟨x, unit_left_id.symm⟩

@[rocq_alias ucmra_unit_core_id]
instance unit_CoreId : CoreId (unit : α) where
  core_id := pcore_unit

@[rocq_alias cmra_unit_cmra_total]
theorem unit_total : IsTotal α := inferInstance

@[rocq_alias empty_cancelable]
instance empty_cancelable : Cancelable (unit : α) where
  cancelableN {n} {w t} _ e := calc
    w ≡{n}≡ unit • w := unit_left_id.dist.symm
    _ ≡{n}≡ unit • t := e
    _ ≡{n}≡ t := unit_left_id.dist

theorem increasing_iff_unit_ord {x : α} : Increasing x ↔ unit ≼ₒ x :=
  ⟨fun h => unit_right_id (x := x) ▸ h.increasing unit,
   fun h => ⟨fun y => calc
    y = unit • y := unit_left_id.symm
    _ ≼ₒ x • y := op_mono_left_ord y h⟩⟩

theorem ordN_op_right_of_unit_ordN {n} {x : α} (y : α) (h : unit ≼ₒ{n} x) : y ≼ₒ{n} x • y :=
  calc y ≡{n}≡ unit • y := (unit_left_id_dist y).symm
    _ ≼ₒ{n} x • y := op_monoN_left_ord y h

theorem unit_ord_core (x : α) : unit ≼ₒ core x := increasing_iff_unit_ord.mp (increasing_core x)

theorem unit_ordN_core {n} (x : α) : unit ≼ₒ{n} core x := (unit_ord_core x).ordN

theorem exists_op_ordN_iff_ordN [IncOrd α] {n} {x y : α} : (∃ c, x • c ≼ₒ{n} y) ↔ x ≼ₒ{n} y :=
  ⟨fun ⟨c, h⟩ => (ordN_op_left n x c).trans h, fun h => ⟨unit, (unit_right_id (x := x)).symm ▸ h⟩⟩

theorem exists_op_ord_iff_ord [IncOrd α] {x y : α} : (∃ c, x • c ≼ₒ y) ↔ x ≼ₒ y :=
  ⟨fun ⟨c, h⟩ => (ord_op_left x c).trans h, fun h => ⟨unit, (unit_right_id (x := x)).symm ▸ h⟩⟩

theorem exists_op_ordN_iff_incN [OrdInc α] {n} {x y : α} : (∃ c, x • c ≼ₒ{n} y) ↔ x ≼{n} y :=
  ⟨fun ⟨c, h⟩ => (incN_op_left n x c).trans (OrdInc.ordN_incN h),
   fun ⟨c, hc⟩ => ⟨c, hc.symm.to_ordN⟩⟩

theorem exists_op_ord_iff_inc [OrdInc α] {x y : α} : (∃ c, x • c ≼ₒ y) ↔ x ≼ y :=
  ⟨fun ⟨c, h⟩ => (inc_op_left x c).trans (OrdInc.ord_inc h), fun ⟨c, hc⟩ => ⟨c, hc ▸ .rfl⟩⟩

section increasing

theorem ordN_unit {n} {x : α} [Increasing x] : unit ≼ₒ{n} x :=
  unit_left_id (x := x) ▸ ordN_op_left n unit x

theorem ord_unit {x : α} [Increasing x] : unit ≼ₒ x := unit_left_id (x := x) ▸ ord_op_left unit x

end increasing

@[rocq_alias cmra_monoid]
instance ucmraMonoidOps {α : Type _} [URA α] : Algebra.MonoidOps (op (α := α)) unit where
  op_assoc := assoc.symm
  op_comm := comm
  op_left_id := unit_left_id

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

section UORA

variable {α : Type _} [URA α] [UORA α]

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

end UORA

end ORA

/-- A morphism between CMRAs is defined to be a non-expansive function which
preserves `validN`, `pcore` and `op`. -/
@[indexed, rocq_alias CmraMorphism]
structure CMRA.Hom (α β : Type _) [OFE α] [Op α] [PCore α] [Valid α]
    [OFE β] [Op β] [PCore β] [Valid β] extends OFE.Hom α β where
  protected validN {n} {x} : ✓{n} x → ✓{n} (f x)
  protected pcore x : (PCore.pcore x).map f = PCore.pcore (f x)
  protected op x y : f (x • y) = f x • f y

namespace ORA
variable [RA α] [ORA α]

section Hom

/-- A morphism between ORAs, written `α -C> β`, is defined to be a non-expansive function which
preserves `validN`, `pcore`, `op`, the order and increasing elements. -/
@[indexed, ext]
structure Hom (α β : Type _) [RA α] [ORA α] [RA β] [ORA β] extends toCMRAHom : CMRA.Hom α β where
  protected monoN_ord {n} {x₁ x₂} : x₁ ≼ₒ{n} x₂ → f x₁ ≼ₒ{n} f x₂
  protected mono_ord {x₁ x₂} : x₁ ≼ₒ x₂ → f x₁ ≼ₒ f x₂
  protected increasing {x} : Increasing x → Increasing (f x)

/-- ORA morphisms, `α -C> β`. -/
notation:25 α:26 " -C>[" S "] " β:25 => Iris.ORA.Hom (SI := S) α β
@[inherit_doc Iris.ORA.Hom]
notation:25 α:26 " -C> " β:25 => Iris.ORA.Hom (SI := stepindex%) α β

instance [RA β] [ORA β] : CoeFun (α -C> β) (fun _ => α → β) := ⟨fun F => F.f⟩

instance [RA β] [ORA β] : OFE (α -C> β) where
  dist n f g := f.toHom ≡{n}≡ g.toHom
  dist_eqv := {
    refl _ := dist_eqv.refl _
    symm h := dist_eqv.symm h
    trans h1 h2 := dist_eqv.trans h1 h2
  }
  eq_dist' {_ _} := Hom.ext_iff.trans eq_dist
  dist_lt := dist_lt

@[rocq_alias cmra_morphism_id]
protected def Hom.id [RA α] [ORA α] : α -C> α where
  toHom := OFE.Hom.id
  validN := id
  pcore x := by dsimp; cases pcore x <;> rfl
  op _ _ := rfl
  monoN_ord := id
  mono_ord := id
  increasing := id

@[rocq_alias cmra_morphism_compose]
protected def Hom.comp [RA β] [ORA β] [RA γ] [ORA γ] (g : β -C> γ) (f : α -C> β) : α -C> γ where
  toHom := OFE.Hom.comp g.toHom f.toHom
  validN v := g.validN (f.validN v)
  pcore x := ((Option.map_map ..).symm.trans (congrArg _ (f.pcore x))).trans (g.pcore (f x))
  op x y := (congrArg g.f (f.op x y)).trans (g.op ..)
  monoN_ord h := g.monoN_ord (f.monoN_ord h)
  mono_ord h := g.mono_ord (f.mono_ord h)
  increasing h := g.increasing (f.increasing h)

#rocq_ignore cmra_morphism_proper "OFE is Leibniz; use equality"

@[rocq_alias cmra_morphism_core]
protected theorem Hom.core [RA β] [ORA β] (f : α -C> β) {x : α} : core (f x) = f (core x) := by
  have h := f.pcore x
  unfold core
  cases hx : pcore x <;> rw [hx] at h <;> simp only [Option.map] at h <;> simp [← h]

@[rocq_alias cmra_morphism_mono]
protected theorem Hom.mono [RA β] [ORA β] (f : α -C> β) {x₁ x₂ : α} :
    x₁ ≼ x₂ → f x₁ ≼ f x₂ :=
  inc_map f.f f.op

@[rocq_alias cmra_morphism_monoN]
protected theorem Hom.monoN [RA β] [ORA β] (f : α -C> β) (n) {x₁ x₂ : α} :
    x₁ ≼{n} x₂ → f x₁ ≼{n} f x₂ :=
  incN_map f.f f.op

@[rocq_alias cmra_morphism_valid]
protected theorem Hom.valid [RA β] [ORA β] (f : α -C> β) {x : α} (H : ✓ x) : ✓ f x :=
  valid_iff_validN.mpr fun _ => f.validN H.validN

end Hom
end ORA

section HomExt
open ORA
variable [RA α] [ORA α] [RA β] [ORA β] [OrdInc α] [IncOrd β]

/-- A morphism between classical resource algebras needs only the classical fields: under the
extension order, `monoN_ord`, `mono_ord` and `increasing` follow from `op`. -/
@[reducible] def CMRA.Hom.toORA (g : CMRA.Hom α β) : α -C> β where
  toCMRAHom := g
  monoN_ord h := IncOrd.incN_ordN (incN_map g.f g.op (OrdInc.ordN_incN h))
  mono_ord h := IncOrd.inc_ord (inc_map g.f g.op (OrdInc.ord_inc h))
  increasing _ := IncOrd.increasing _

end HomExt

section rFunctor

variable (SI) in
@[indexed, rocq_alias rFunctor]
class RFunctor (F : COFE.OFunctorPre) where
  [ra [COFE α] [COFE β] : RA (F α β)]
  [cmra [COFE α] [COFE β] : ORA (F α β)]
  map [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -C> F α₂ β₂
  map_ne [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFE α] [COFE β] (x : F α β) : map (Hom.id (α := α)) (Hom.id (α := β)) x = x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x = map g g' (map f f' x)

variable (SI) in
@[indexed, rocq_alias rFunctorContractive]
class RFunctorContractive (F : COFE.OFunctorPre) extends (RFunctor F) where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [reducible, instance] RFunctor.ra RFunctor.cmra

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
open ORA

variable (SI) in
@[indexed, rocq_alias urFunctor]
class URFunctor (F : COFE.OFunctorPre) where
  [ura [COFE α] [COFE β] : URA (F α β)]
  [cmra [COFE α] [COFE β] : UORA (F α β)]
  map [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -C> F α₂ β₂
  map_ne [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFE α] [COFE β] (x : F α β) : map (Hom.id (α := α)) (Hom.id (α := β)) x = x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x = map g g' (map f f' x)

variable (SI) in
@[indexed, rocq_alias urFunctorContractive]
class URFunctorContractive (F : COFE.OFunctorPre) extends URFunctor F where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [reducible, instance] URFunctor.ura URFunctor.cmra

#rocq_ignore urFunctor_apply "Just apply the underlying `OFunctorPre`"

variable (SI) in
@[indexed]
class RFunctorAffine (F : COFE.OFunctorPre) [RFunctor F] : Prop where
  affine [COFE α] [COFE β] : IncOrd (F α β)

attribute [instance] RFunctorAffine.affine

@[rocq_alias urFunctor_to_rFunctor]
instance URFunctor.toRFunctor [UF : URFunctor F] : RFunctor F where
  ra       := URFunctor.ura.toRA
  cmra     := URFunctor.cmra.toORA
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
  ra := RFunctor.ra (F := F₁)
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
  ura := URFunctor.ura (F := F₁)
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

instance instRFunctorAffineComposeOF [RFunctor F₁] [RFunctorAffine F₁] :
    RFunctorAffine (ComposeOF F₁ F₂) where
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
open ORA

@[rocq_alias constRF]
instance COFE.OFunctor.constOF_RFunctor [RA B] [ORA B] : RFunctor (constOF B) where
  cmra := inferInstance
  map _ _ := (Hom.id : B -C> B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance COFE.OFunctor.constOF_RFunctorAffine [RA B] [ORA B] [IncOrd B] : RFunctorAffine (constOF B) where
  affine := inferInstance

@[rocq_alias constRF_contractive]
instance OFunctor.constOF_RFunctorContractive [RA B] [ORA B] : RFunctorContractive (constOF B) where
  map_contractive.1 := fun _ => .rfl

@[rocq_alias constURF]
instance COFE.OFunctor.constOF_URFunctor [URA B] [UORA B] : URFunctor (constOF B) where
  cmra := inferInstance
  map _ _ := (Hom.id : B -C> B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

@[rocq_alias constURF_contractive]
instance OFunctor.constOF_URFunctorContractive [URA B] [UORA B] : URFunctorContractive (constOF B) where
  map_contractive.1 _ := .rfl

end Id

/-! ## Transporting a CMRA equality

Rocq bundles a CMRA as a record, so a proof of `A = B` transports the whole algebra. In Lean
`ORA` is a type class, and an equality of carriers says nothing about the two instances, so the
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
  "Use `OFE.transpAp_validN_mp`/`OFE.validN_transpAp_mp` with `ORA.valid_iff_validN`"
#rocq_ignore cmra_transport_discrete "No counterpart; see the `transpAp` family"
#rocq_ignore cmra_transport_core_id "No counterpart; see the `transpAp` family"

section DiscreteFunO
open ORA

#rocq_ignore discrete_fun_cmra_mixin "Use CMRA instance"

namespace DiscreteFun

variable {α : Type _} {β : α → Type _}

@[reducible] def raOrdered [∀ x, Ordered (β x)] : Ordered (∀ x, β x) where
  OrderN n f g := ∀ x, f x ≼ₒ{n} g x
  Order f g := ∀ x, f x ≼ₒ g x
  ordN_trans h₁ h₂ x := ordN_trans (h₁ x) (h₂ x)
  ord_trans h₁ h₂ x := ord_trans (h₁ x) (h₂ x)
  ordN_of_ord n h x := ordN_of_ord n (h x)

@[reducible, rocq_alias discrete_fun_op_instance]
instance raOp [∀ x, Op (β x)] : Op (∀ x, β x) where
  op f g x := f x • g x
  assoc := funext fun _ => assoc
  comm := funext fun _ => comm

@[reducible, rocq_alias discrete_fun_pcore_instance]
instance raPCore [∀ x, PCore (β x)] [∀ x, IsTotal (β x)] : PCore (∀ x, β x) where
  pcore f := some fun x => core (f x)
  pcore_idem := by
    rintro f _ ⟨⟩; exact congrArg some (funext fun x => IsTotal.core_idem (f x))

instance raIsTotal [∀ x, PCore (β x)] [∀ x, IsTotal (β x)] : IsTotal (∀ x, β x) where
  total _ := ⟨_, rfl⟩

instance raRA [∀ x, RA (β x)] [∀ x, IsTotal (β x)] : RA (∀ x, β x) where
  pcore_op_left := by rintro f _ ⟨⟩; exact funext fun x => core_op (f x)

instance raURA [∀ x, URA (β x)] : URA (∀ x, β x) where
  unit _ := unit
  unit_left_id := funext fun _ => URA.unit_left_id
  pcore_unit := congrArg some (funext fun _ => core_eqv_self _)

@[reducible, rocq_alias discrete_fun_valid_instance, rocq_alias discrete_fun_validN_instance]
def raValid [∀ x, _root_.Iris.Valid (β x)] : _root_.Iris.Valid (∀ x, β x) where
  ValidN n f := ∀ x, ✓{n} f x
  Valid f := ∀ x, ✓ f x
  valid_iff_validN {g} := by simpa [valid_iff_validN] using forall_comm

section
variable [∀ x, RA (β x)] [∀ x, ORA (β x)]

attribute [local instance] raOrdered

theorem ordNR_apply {n} {f g : ∀ x, β x} (h : f ≼ₒ*{n} g) (x : α) : f x ≼ₒ*{n} g x :=
  h.imp (· x) (· x)

variable [∀ x, IsTotal (β x)]

attribute [local instance] raOp raPCore raValid

omit [∀ (x : α), IsTotal (β x)] in
open Classical in
theorem increasing_apply {f : ∀ x, β x} (h : Increasing f) (x : α) : Increasing (f x) where
  increasing y := by
    let g : ∀ x', β x' := fun x' => if e : x' = x then e ▸ y else f x'
    have hg : g x = y := dite_eq_left rfl
    rw [← hg]
    exact h.increasing g x

omit [∀ (x : α), IsTotal (β x)] in
theorem increasing_iff {f : ∀ x, β x} : Increasing f ↔ ∀ x, Increasing (f x) :=
  ⟨increasing_apply, fun h => { increasing := fun g x => (h x).increasing (g x) }⟩

end

end DiscreteFun

section
open DiscreteFun
variable {α : Type _} {β : α → Type _} [∀ x, RA (β x)] [∀ x, ORA (β x)] [∀ x, IsTotal (β x)]
attribute [local instance] raOp raPCore raValid raOrdered

variable (β) in
@[rocq_alias discrete_funR]
instance cmraDiscreteFunO : ORA (∀ x, β x) where
  toValid := raValid
  op_ne.ne _ _ _ H y := (H y).op_r
  pcore_ne {n} {f g _} H := by rintro ⟨⟩; exact ⟨_, rfl, fun x => (H _).core⟩
  validN_ne {n} {x y} H H1 y := (H y).validN.mp (H1 y)
  validN_le H le x := validN_le (H x) le
  ordN_ne ef eg h x := ordN_ne (ef x) (eg x) (h x)
  ordN_le h le x := ordN_le (h x) le
  validN_op_left H _ := validN_op_left (H _)
  extend {n} {f f1 f2} Hv He := by
    let F x := extend (Hv x) (He x)
    exact ⟨fun x => (F x).1, fun x => (F x).2.1,
      funext fun x => (F x).2.2.1, fun x => (F x).2.2.2.1, fun x => (F x).2.2.2.2⟩
  toOrdered := raOrdered
  op_monoN_left_ord h H x := op_monoN_left_ord (h x) (H x)
  op_mono_left_ord h H x := op_mono_left_ord (h x) (H x)
  validN_of_ordN H V x := validN_of_ordN (H x) (V x)
  pcore_monoN_ord := by rintro n f g _ H ⟨⟩; exact ⟨_, rfl, fun x => core_ordN_core (H x)⟩
  pcore_mono_ord := by rintro f g _ H ⟨⟩; exact ⟨_, rfl, fun x => core_mono_ord (H x)⟩
  pcore_order_op := by rintro f _ ⟨⟩ g; exact ⟨_, rfl, fun x => core_op_mono_ord (f x) (g x)⟩
  pcore_increasing := by rintro f _ ⟨⟩; exact increasing_iff.mpr fun x => inferInstance
  increasing_closed H₁ H₂ :=
    increasing_iff.mpr fun x => increasing_closed (increasing_apply H₁ x) (ordNR_apply H₂ x)
  ordN_extend hs V H :=
    let ⟨z, hz⟩ := Classical.skolem.mp fun x => ordN_extend hs (V x) (H x)
    ⟨z, fun x => (hz x).1, fun x => (hz x).2⟩

end

#rocq_ignore discrete_fun_unit_instance "Use UCMRA instance"
#rocq_ignore discrete_fun_ucmra_mixin "Use UCMRA instance"

@[rocq_alias discrete_funUR]
instance ucmraDiscreteFunO {α : Type _} (β : α → Type _) [∀ x, URA (β x)] [∀ x, UORA (β x)] :
    UORA (∀ x, β x) where
  unit_valid _ := unit_valid
  ord_refl f x := ord_refl (f x)

namespace DiscreteFun

variable {α : Type _} {β : α → Type _}

@[rocq_alias discrete_fun_lookup_op]
theorem op_apply [∀ x, RA (β x)] (f g : ∀ x, β x) (x : α) :
    (f • g) x = f x • g x := rfl

@[rocq_alias discrete_fun_lookup_core]
theorem core_apply [∀ x, RA (β x)] [∀ x, IsTotal (β x)] (f : ∀ x, β x) (x : α) :
    core f x = core (f x) := rfl

@[rocq_alias discrete_fun_lookup_empty]
theorem unit_apply [∀ x, URA (β x)] (x : α) : (unit : ∀ x, β x) x = unit := rfl

@[rocq_alias discrete_fun_unit_discrete]
instance [∀ x, URA (β x)] [∀ x, UORA (β x)] [∀ x, OFE.DiscreteE (unit : β x)] : OFE.DiscreteE (unit : ∀ x, β x) where
  discrete h := funext fun x => OFE.DiscreteE.discrete (h x)

variable [∀ x, RA (β x)] [∀ x, ORA (β x)] [∀ x, IsTotal (β x)]

theorem ord_apply {f g : ∀ x, β x} (h : f ≼ₒ g) (x : α) : f x ≼ₒ g x := h x

theorem ord_iff {f g : ∀ x, β x} : f ≼ₒ g ↔ ∀ x, f x ≼ₒ g x := .rfl

theorem ordN_iff {n} {f g : ∀ x, β x} : f ≼ₒ{n} g ↔ ∀ x, f x ≼ₒ{n} g x := .rfl

omit [∀ x, IsTotal (β x)] in
@[rocq_alias discrete_fun_included_spec_1]
theorem inc_apply {f g : ∀ x, β x} : f ≼ g → ∀ x, f x ≼ g x
  | ⟨h, hh⟩, x => ⟨h x, congrFun hh x⟩

omit [∀ x, IsTotal (β x)] in
/-- Note: The finiteness assumption from Iris-Rocq is removed using choice. -/
@[rocq_alias discrete_fun_included_spec]
theorem inc_iff {f g : ∀ x, β x} : f ≼ g ↔ ∀ x, f x ≼ g x := by
  refine ⟨inc_apply, fun h => ?_⟩
  obtain ⟨z, hz⟩ := Classical.skolem.mp h
  exact ⟨z, funext hz⟩

omit [∀ x, IsTotal (β x)] in
theorem incN_apply {n} {f g : ∀ x, β x} : f ≼{n} g → ∀ x, f x ≼{n} g x
  | ⟨h, hh⟩, x => ⟨h x, hh x⟩

omit [∀ x, IsTotal (β x)] in
/-- Note: The finiteness assumption from Iris-Rocq is removed using choice. -/
theorem incN_iff {n} {f g : ∀ x, β x} : f ≼{n} g ↔ ∀ x, f x ≼{n} g x :=
  ⟨incN_apply, Classical.skolem.mp⟩

instance instOrderRefl [∀ x, OrderRefl (β x)] : OrderRefl (∀ x, β x) where
  ord_refl f x := ord_refl (f x)

instance instIncOrd [∀ x, IncOrd (β x)] : IncOrd (∀ x, β x) :=
  IncOrd.of_increasing fun f => increasing_iff.mpr fun x => IncOrd.increasing (f x)

instance instOrdInc [∀ x, OrdInc (β x)] : OrdInc (∀ x, β x) where
  ord_inc h := inc_iff.mpr fun x => OrdInc.ord_inc (h x)
  ordN_incN h := incN_iff.mpr fun x => OrdInc.ordN_incN (h x)

instance instIsInc [∀ x, IsInc (β x)] : IsInc (∀ x, β x) := {}

end DiscreteFun

@[rocq_alias discrete_fun_map_cmra_morphism]
def mapCodHomC {α : Type _} {β₁ β₂ : α → Type _}
    [∀ x, URA (β₁ x)] [∀ x, UORA (β₁ x)] [∀ x, URA (β₂ x)] [∀ x, UORA (β₂ x)]
    (F : ∀ x, β₁ x -C> β₂ x) : (∀ x, β₁ x) -C> (∀ x, β₂ x) where
  toHom := mapCodHom fun x => (F x).toHom
  validN h x := (F x).validN (h x)
  pcore _ := congrArg some (funext fun x => (F x).core.symm)
  op f g := funext fun x => (F x).op (f x) (g x)
  monoN_ord h x := (F x).monoN_ord (h x)
  mono_ord h x := (F x).mono_ord (h x)
  increasing h := DiscreteFun.increasing_iff.mpr fun x =>
    (F x).increasing (DiscreteFun.increasing_apply h x)

end DiscreteFunO

section DiscreteFunURF
open ORA

@[rocq_alias discrete_funURF]
instance urFunctorDiscreteFunOF {C} (F : C → COFE.OFunctorPre) [∀ c, URFunctor (F c)] :
    URFunctor (DiscreteFunOF F) where
  map f g := {
    toHom := COFE.OFunctor.map f g
    validN hv _ := (URFunctor.map f g).validN (hv _)
    pcore x := by
      simp only [pcore, Option.map]
      exact congrArg some (funext fun c => ((URFunctor.map f g).core).symm)
    op x y := funext fun c => (URFunctor.map f g).op (x c) (y c)
    monoN_ord h c := (URFunctor.map f g).monoN_ord (h c)
    mono_ord h c := (URFunctor.map f g).mono_ord (h c)
    increasing h := DiscreteFun.increasing_iff.mpr fun c =>
      (URFunctor.map f g).increasing (DiscreteFun.increasing_apply h c)
  }
  map_ne.ne := COFE.OFunctor.map_ne.ne
  map_id x := COFE.OFunctor.map_id x
  map_comp f g f' g' x := COFE.OFunctor.map_comp f g f' g' x

instance instRFunctorAffineDiscreteFunOF {C} (F : C → COFE.OFunctorPre) [∀ c, URFunctor (F c)]
    [∀ c, RFunctorAffine (F c)] : RFunctorAffine (DiscreteFunOF F) where
  affine := inferInstance

@[rocq_alias discrete_funURF_contractive]
instance DiscreteFunOF_URFC {C} (F : C → COFE.OFunctorPre) [HURF : ∀ c, URFunctorContractive (F c)] :
    URFunctorContractive (DiscreteFunOF F) where
  map_contractive.1 h _ _ := URFunctorContractive.map_contractive.distLater_dist h _

end DiscreteFunURF

section option

open ORA Iris.Option Iris.OFE.Option

@[simp]
def optionCore [PCore α] (x : Option α) : Option α := x.bind pcore

@[simp]
def optionOp [Op α] (x y : Option α) : Option α :=
  match x, y with
  | some x', some y' => some (op x' y')
  | none, _ => y
  | _, none => x

variable [RA α] [ORA α]

@[simp]
def optionValidN (n : SI) : Option α → Prop
  | some x => ✓{n} x
  | none => True

@[indexed, simp]
def optionValid : Option α → Prop
  | some x => ✓ x
  | none => True

/-- The step-indexed order on `Option α`: `none` lies below `none` and below every increasing
element, `some` is monotone up to `n`-equivalence, and nothing but `none` lies below `none`. -/
@[simp]
def optionOrderN (n : SI) : Option α → Option α → Prop
  | none, none => True
  | none, some y => Increasing y
  | some x, some y => x ≼ₒ*{n} y
  | some _, none => False

@[indexed, simp]
def optionOrder : Option α → Option α → Prop
  | none, none => True
  | none, some y => Increasing y
  | some x, some y => x ≼ₒ* y
  | some _, none => False

namespace Option

@[reducible, rocq_alias option_op_instance]
instance raOp [Op α] : Op (Option α) where
  op := optionOp
  assoc {x y z} := by
    rcases x, y, z with ⟨_|_, _|_, _|_⟩ <;> first | rfl | exact congrArg some assoc
  comm {x y} := by
    rcases x, y with ⟨_|_, _|_⟩ <;> first | rfl | exact congrArg some comm

@[reducible, rocq_alias option_pcore_instance]
instance raPCore [PCore α] : PCore (Option α) where
  pcore x := some (optionCore x)
  pcore_idem := by
    rintro (_|x) <;> simp
    rcases H : pcore x with _|y <;> simp
    exact pcore_idem H

instance raRA : RA (Option α) where
  pcore_op_left {x cx} := by
    rcases x, cx with ⟨_|_, _|_⟩ <;> simp_all [Op.op, optionOp, PCore.pcore, optionCore]
    intro h; exact pcore_op_left h

instance raURA : URA (Option α) where
  unit := none
  unit_left_id := by rintro ⟨⟩ <;> rfl
  pcore_unit := by rfl
  total _ := ⟨_, rfl⟩

@[reducible, rocq_alias option_valid_instance, rocq_alias option_validN_instance]
def raValid : _root_.Iris.Valid (Option α) where
  ValidN := optionValidN
  Valid := optionValid
  valid_iff_validN {x} := by
    rcases x with ⟨_|_⟩ <;> simp [valid_iff_validN]

@[reducible] def raOrdered : Ordered (Option α) where
  OrderN := optionOrderN
  Order := optionOrder
  ordN_trans {n} {x y z} h₁ h₂ := by
    rcases x, y, z with ⟨_|x, _|y, _|z⟩ <;> simp_all
    · exact h₁.of_ordNR h₂
    · exact Ordered.OrderNR.trans h₁ h₂
  ord_trans {x y z} h₁ h₂ := by
    rcases x, y, z with ⟨_|x, _|y, _|z⟩ <;> simp_all
    · exact h₁.of_ordR h₂
    · exact Ordered.OrderR.trans h₁ h₂
  ordN_of_ord {x y} n h := by
    rcases x, y with ⟨_|x, _|y⟩ <;> simp_all
    exact Ordered.OrderR.ordNR n h

attribute [local instance] raOrdered in
theorem raOrderedNE : OrderedNE (Option α) where
  ordN_ne {n} {x x' y y'} ex ey h := by
    rcases x, x', y, y' with ⟨_|x, _|x', _|y, _|y'⟩ <;>
      simp_all [Dist, HasDist.dist, Option.Forall₂, Ordered.OrderN]
    · exact h.of_dist ey
    · exact Ordered.OrderNR.ne ex ey h
  ordN_le {n n'} {x y} h le := by
    rcases x, y with ⟨_|x, _|y⟩ <;> simp_all [Ordered.OrderN]
    exact Ordered.OrderNR.le le h

section
attribute [local instance] raOp raPCore raValid raOrdered raOrderedNE

theorem some_ordN_some_iff {n} {a b : α} : some a ≼ₒ{n} some b ↔ a ≡{n}≡ b ∨ a ≼ₒ{n} b := .rfl

theorem some_ord_some_iff {a b : α} : some a ≼ₒ some b ↔ a = b ∨ a ≼ₒ b := .rfl

theorem none_ordN_some_iff {n} {b : α} : none ≼ₒ{n} some b ↔ Increasing b := .rfl

theorem none_ord_some_iff {b : α} : none ≼ₒ some b ↔ Increasing b := .rfl

theorem not_some_ordN_none {n} {a : α} : ¬some a ≼ₒ{n} none := id

theorem eq_none_of_ordN_none {n} {ma : Option α} : ma ≼ₒ{n} none → ma = none :=
  match ma with | none => fun _ => rfl | some _ => False.elim

theorem exists_of_some_ordN {n} {a : α} {mb : Option α} :
    some a ≼ₒ{n} mb → ∃ b, mb = some b ∧ some a ≼ₒ{n} some b :=
  match mb with | none => False.elim | some b => fun h => ⟨b, rfl, h⟩

theorem exists_of_some_ord {a : α} {mb : Option α} :
    some a ≼ₒ mb → ∃ b, mb = some b ∧ some a ≼ₒ some b :=
  match mb with | none => False.elim | some b => fun h => ⟨b, rfl, h⟩

theorem not_some_ord_none {a : α} : ¬some a ≼ₒ none := id

instance instOrderRefl : OrderRefl (Option α) where
  ord_refl | none => trivial | some _ => Or.inl rfl

theorem increasing_some_iff {a : α} : Increasing (some a) ↔ Increasing a where
  mp h := h.increasing none
  mpr h := ⟨fun | none => h | some b => Or.inr (h.increasing b)⟩

instance instIncreasingNone : Increasing (none : Option α) :=
  ⟨fun | none => trivial | some _ => Or.inl rfl⟩

theorem increasing_pcore (x : α) : Increasing (pcore x : Option α) := match h : pcore x with
  | none => inferInstance
  | some _ => increasing_some_iff.mpr (pcore_increasing h)

theorem none_ord_pcore (x : α) : none ≼ₒ pcore x := match h : pcore x with
  | none => trivial
  | some _ => pcore_increasing h

theorem none_ordN_pcore {n} (x : α) : none ≼ₒ{n} pcore x := Ordered.ordN_of_ord n (none_ord_pcore x)

theorem pcore_ordN_pcore {n} {x y : α} : x ≼ₒ*{n} y → pcore x ≼ₒ{n} pcore y
  | .inl e => (NonExpansive.ne (f := pcore) e).to_ordN
  | .inr i => match hx : pcore x with
    | none => none_ordN_pcore y
    | some _ => let ⟨_, hcy, icy⟩ := pcore_monoN_ord i hx; hcy ▸ Or.inr icy

theorem pcore_ord_pcore {x y : α} : x ≼ₒ* y → pcore x ≼ₒ pcore y
  | .inl rfl => .rfl
  | .inr i => match hx : pcore x with
    | none => none_ord_pcore y
    | some _ => let ⟨_, hcy, icy⟩ := pcore_mono_ord i hx; hcy ▸ Or.inr icy

theorem pcore_ord_pcore_op (x y : α) : (pcore x : Option α) ≼ₒ pcore (x • y) :=
  match hx : pcore x with
  | none => none_ord_pcore _
  | some _ => let ⟨_, hcxy, i⟩ := pcore_order_op hx y; hcxy ▸ Or.inr i

end

end Option

section
attribute [local instance] Option.raOp Option.raPCore Option.raValid Option.raOrdered
  Option.raOrderedNE

@[rocq_alias optionR, rocq_alias option_cmra_mixin]
instance cmraOption : ORA (Option α) where
  toValid := Option.raValid
  op_ne.ne n x1 x2 H := by
    rename_i x
    rcases x1, x2, x with ⟨_|_, _|_, _|_⟩ <;> simp_all [Op.op, optionOp, op_right_dist]
  pcore_ne {n} {x y cx} H := by
    simp only [PCore.pcore, Option.some.injEq]; rintro rfl
    refine ⟨optionCore y, rfl, ?_⟩
    match x, y, H with
    | none, none, _ => exact Dist.rfl
    | some x, some y, (H : x ≡{n}≡ y) => exact NonExpansive.ne (f := pcore) H
  validN_ne {n} {x y} H := by
    rcases x, y with ⟨_|_, _|_⟩ <;> simp_all [Dist, HasDist.dist, Option.Forall₂, Valid.ValidN]
    exact Dist.validN H |>.mp
  validN_le {n n'} {x} := by
    rcases x with ⟨_|_⟩ <;> simp_all [Valid.ValidN]
    exact fun h le => validN_le h le
  toOrderedNE := Option.raOrderedNE
  validN_op_left {n} {x y} := by
    rcases x, y with ⟨_|_, _|_⟩ <;> simp_all [Op.op, optionOp, Valid.ValidN, optionValidN]
    apply validN_op_left
  extend {n} := by
    rintro (_|x) (_|mb1) (_|mb2) Hx Hx' <;> simp [Op.op, optionOp] at Hx' ⊢
    · exists none, none
    · exists none, some x
    · exists some x, none
    · rcases extend Hx Hx' with ⟨mc1, mc2, hx, h1, h2⟩
      exact ⟨some mc1, some mc2, congrArg some hx, h1, h2⟩
  toOrdered := Option.raOrdered
  op_monoN_left_ord {n} {x y} z h := match x, y, z, h with
    | none, none, _, _ => .rfl
    | none, some _, none, h => h
    | none, some _, some z, h => Or.inr (Increasing.ordN h z)
    | some _, none, _, h => False.elim h
    | some _, some _, none, h => h
    | some _, some _, some z, h => Ordered.OrderNR.op_left z h
  op_mono_left_ord {x y} z h := match x, y, z, h with
    | none, none, _, _ => .rfl
    | none, some _, none, h => h
    | none, some _, some z, h => Or.inr (h.increasing z)
    | some _, none, _, h => False.elim h
    | some _, some _, none, h => h
    | some _, some _, some z, h => Ordered.OrderR.op_left z h
  validN_of_ordN {n} {x y} h v := match x, y, h with
    | none, _, _ => trivial
    | some _, none, h => False.elim h
    | some _, some _, h => Ordered.OrderNR.validN h v
  pcore_monoN_ord {n} {x y _} h := by
    rintro ⟨⟩
    refine ⟨_, rfl, ?_⟩
    match x, y, h with
    | none, none, _ => trivial
    | none, some y, _ => exact none_ordN_pcore y
    | some _, none, h => exact False.elim h
    | some x, some y, h => exact pcore_ordN_pcore h
  pcore_mono_ord {x y _} h := by
    rintro ⟨⟩
    refine ⟨_, rfl, ?_⟩
    match x, y, h with
    | none, none, _ => trivial
    | none, some y, _ => exact none_ord_pcore y
    | some _, none, h => exact False.elim h
    | some x, some y, h => exact pcore_ord_pcore h
  pcore_order_op {x _} := by
    rintro ⟨⟩ y
    refine ⟨_, rfl, ?_⟩
    match x, y with
    | none, none => trivial
    | none, some y => exact none_ord_pcore y
    | some x, none => exact ord_refl _
    | some x, some y => exact pcore_ord_pcore_op x y
  pcore_increasing {x _} := by
    rintro ⟨⟩
    match x with
    | none => exact (inferInstance : Increasing (none : Option α))
    | some x => exact increasing_pcore x
  increasing_closed {n} {x y} h h' := match x, y, h' with
    | none, none, _ => inferInstance
    | none, some _, .inl e => False.elim e
    | none, some _, .inr i => increasing_some_iff.mpr i
    | some _, none, .inl e => False.elim e
    | some _, none, .inr i => False.elim i
    | some _, some _, h' =>
      increasing_some_iff.mpr ((increasing_some_iff.mp h).of_ordNR (h'.elim .inl id))
  ordN_extend {n} {sn} {x y} hs v h := match x, y, h with
    | none, none, _ => ⟨none, trivial, .rfl⟩
    | none, some _, h => ⟨none, h, .rfl⟩
    | some _, none, h => False.elim h
    | some _, some y, .inl e => ⟨some y, Or.inl .rfl, e.symm⟩
    | some _, some _, .inr i =>
      let ⟨z, hz, ez⟩ := ordN_extend hs v i
      ⟨some z, Or.inr hz, ez⟩

#rocq_ignore option_unit_instance "Use UCMRA instance"
#rocq_ignore option_ucmra_mixin "Use UCMRA instance"

@[rocq_alias optionUR]
instance ucmraOption : UORA (Option α) where
  unit_valid := trivial
  ord_refl := ord_refl

end

namespace Option

@[rocq_alias Some_op]
theorem some_op (a b : α) : some (a • b) = some a • some b := rfl

@[rocq_alias Some_valid]
theorem some_valid {a : α} : ✓ (some a) ↔ ✓ a := .rfl

@[rocq_alias Some_validN]
theorem some_validN {n} {a : α} : ✓{n} (some a) ↔ ✓{n} a := .rfl

@[rocq_alias pcore_Some]
theorem pcore_some (a : α) :
    pcore (some a) = (some (pcore a) : Option (Option α)) := rfl

@[rocq_alias Some_core]
theorem some_core [IsTotal α] (a : α) : some (core a) = core (some a) := by
  simp [core, pcore, optionCore]
  obtain ⟨c, hc⟩ := IsTotal.total a
  simp [hc]

omit [ORA α] in
/-- SI-free: core-identity only involves the core. -/
@[rocq_alias Some_core_id]
instance some_core_id [PCore α] (a : α) [CoreId a] : CoreId (some a : Option α) where
  core_id := by
    change some (optionCore (some a)) = some (some a)
    simp [optionCore, CoreId.core_id (x := a)]

instance none_core_id : CoreId (none : Option α) := ⟨rfl⟩

@[rocq_alias option_core_id]
instance option_core_id (ma : Option α) [∀ x : α, CoreId x] : CoreId ma where
  core_id := by
    rcases ma with _|a
    · rfl
    · exact (some_core_id a).core_id

@[rocq_alias op_None]
theorem op_none_iff (ma mb : Option α) : ma • mb = none ↔ ma = none ∧ mb = none := by
  cases ma <;> cases mb <;> simp [op, optionOp]

@[rocq_alias op_is_Some]
theorem op_isSome (ma mb : Option α) : (ma • mb).isSome ↔ ma.isSome ∨ mb.isSome := by
  cases ma <;> cases mb <;> simp [op, optionOp]

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
  opM_opM_assoc.trans <| (congrArg (x •? ·) comm).trans opM_opM_assoc.symm

@[rocq_alias cmra_opM_fmap_Some]
theorem opM_map_some {ma₁ ma₂ : Option α} : ma₁ •? ma₂.map some = ma₁ • ma₂ := by
  rcases ma₁, ma₂ with ⟨_|_, _|_⟩ <;> rfl

theorem op_some_opM_assoc_dist {n} {x y : α} {mz : Option α} : (x • y) •? mz ≡{n}≡ x •? (some y • mz) :=
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
  exclusiveN_some_left (validN_ne op_commN h)

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

theorem dist_or_ordN_of_some_ordN_some {n} {a b : α} (h : some a ≼ₒ{n} some b) :
    a ≡{n}≡ b ∨ a ≼ₒ{n} b := h

theorem some_ordN_some_of_dist_or_ordN {n} {a b : α} (h : a ≡{n}≡ b ∨ a ≼ₒ{n} b) :
    some a ≼ₒ{n} some b := h

theorem some_ordN_some_of_ordN {n} {a b : α} (h : a ≼ₒ{n} b) : some a ≼ₒ{n} some b := Or.inr h

theorem some_ordN_some_of_dist {n} {a b : α} (h : a ≡{n}≡ b) : some a ≼ₒ{n} some b := Or.inl h

theorem isSome_of_some_ordN {n} {a : α} {mb : Option α} (h : some a ≼ₒ{n} mb) : mb.isSome :=
  match mb, h with
  | some _, _ => rfl
  | none, h => False.elim h

theorem eq_or_ord_of_some_ord_some {a b : α} (h : some a ≼ₒ some b) : a = b ∨ a ≼ₒ b := h

theorem some_ord_some_of_eq_or_ord {a b : α} (h : a = b ∨ a ≼ₒ b) : some a ≼ₒ some b := h

theorem some_ord_some_of_ord {a b : α} (h : a ≼ₒ b) : some a ≼ₒ some b := Or.inr h

theorem some_ord_some_of_eq {a b : α} (h : a = b) : some a ≼ₒ some b := Or.inl h

theorem isSome_of_some_ord {a : α} {mb : Option α} (h : some a ≼ₒ mb) : mb.isSome :=
  match mb, h with
  | some _, _ => rfl
  | none, h => False.elim h

theorem isSome_monoN_ord {n} {ma mb : Option α} (h : ma ≼ₒ{n} mb) : ma.isSome → mb.isSome := by
  cases ma with
  | none => simp
  | some _ => exact fun _ => isSome_of_some_ordN h

theorem isSome_mono_ord {ma mb : Option α} (h : ma ≼ₒ mb) : ma.isSome → mb.isSome := by
  cases ma with
  | none => simp
  | some _ => exact fun _ => isSome_of_some_ord h

theorem ord_of_some_ord_some [OrderRefl α] {x y : α} (H : some y ≼ₒ some x) : y ≼ₒ x :=
  Or.elim H (· ▸ ord_refl y) id

theorem ordN_of_some_ordN_some [OrderRefl α] {n} {x y : α} (H : some y ≼ₒ{n} some x) :
    y ≼ₒ{n} x :=
  Or.elim H Dist.to_ordN id

theorem some_ord_some_iff_orderRefl [OrderRefl α] {a b : α} : some a ≼ₒ some b ↔ a ≼ₒ b :=
  ⟨ord_of_some_ord_some, Or.inr⟩

theorem some_ordN_some_iff_orderRefl [OrderRefl α] {n} {a b : α} :
    some a ≼ₒ{n} some b ↔ a ≼ₒ{n} b :=
  ⟨ordN_of_some_ordN_some, Or.inr⟩

theorem validN_of_ordN_validN {n} {a b : α} (Hv : ✓{n} a) (Hinc : some b ≼ₒ{n} some a) :
    ✓{n} b :=
  validN_of_ordN (α := Option α) Hinc Hv

theorem valid_of_ord_valid {a b : α} (Hv : ✓ a) (Hinc : some b ≼ₒ some a) : ✓ b :=
  valid_of_ord (α := Option α) Hinc Hv

theorem ord_iff [IncOrd α] {ma mb : Option α} :
    ma ≼ₒ mb ↔
      ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a = b ∨ a ≼ₒ b) :=
  match ma, mb with
  | none, none => ⟨fun _ => .inl rfl, fun _ => trivial⟩
  | none, some b => ⟨fun _ => .inl rfl, fun _ => IncOrd.increasing b⟩
  | some _, none => ⟨False.elim, nofun⟩
  | some a, some b => ⟨fun h => .inr ⟨a, b, rfl, rfl, h⟩, fun | .inr ⟨_, _, rfl, rfl, h⟩ => h⟩

theorem ordN_iff [IncOrd α] {n} {ma mb : Option α} :
    ma ≼ₒ{n} mb ↔
      ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a ≡{n}≡ b ∨ a ≼ₒ{n} b) :=
  match ma, mb with
  | none, none => ⟨fun _ => .inl rfl, fun _ => trivial⟩
  | none, some b => ⟨fun _ => .inl rfl, fun _ => IncOrd.increasing b⟩
  | some _, none => ⟨False.elim, nofun⟩
  | some a, some b => ⟨fun h => .inr ⟨a, b, rfl, rfl, h⟩, fun | .inr ⟨_, _, rfl, rfl, h⟩ => h⟩

theorem ord_iff_orderRefl [IncOrd α] [OrderRefl α] {ma mb : Option α} :
    ma ≼ₒ mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼ₒ b :=
  ord_iff.trans <| or_congr_right <| exists₂_congr fun _ _ =>
    and_congr_right fun _ => and_congr_right fun _ => some_ord_some_iff_orderRefl

theorem ordN_iff_orderRefl [IncOrd α] [OrderRefl α] {n} {ma mb : Option α} :
    ma ≼ₒ{n} mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼ₒ{n} b :=
  ordN_iff.trans <| or_congr_right <| exists₂_congr fun _ _ =>
    and_congr_right fun _ => and_congr_right fun _ => some_ordN_some_iff_orderRefl

theorem eqv_of_ord_exclusive [OrdInc α] [Exclusive (a : α)] {b : α} (H : some a ≼ₒ some b)
    (Hv : ✓ b) : a = b :=
  H.elim id fun h => (not_valid_of_excl_inc (OrdInc.ord_inc h) Hv).elim

theorem dist_of_ord_exclusive [OrdInc α] [Exclusive (a : α)] {n} {b : α}
    (H : some a ≼ₒ{n} some b) (Hv : ✓{n} b) : a ≡{n}≡ b :=
  H.elim id fun h => (not_valid_of_exclN_inc (OrdInc.ordN_incN h) Hv).elim

theorem map_mono_ord {β : Type _} [RA β] [ORA β] [IncOrd β] (f : α → β) {ma mb : Option α}
    (hf : ∀ x y : α, x ≼ₒ y → f x ≼ₒ f y) (h : ma ≼ₒ mb) :
    ma.map f ≼ₒ mb.map f :=
  match ma, mb, h with
  | none, none, _ => trivial
  | none, some b, _ => IncOrd.increasing (f b)
  | some a, some b, h => h.elim (fun e => .inl (congrArg f e)) fun i => .inr (hf a b i)

instance instIncOrd [IncOrd α] : IncOrd (Option α) := IncOrd.of_increasing fun
    | none => inferInstance
    | some a => increasing_some_iff.mpr (IncOrd.increasing a)

instance instOrdInc [OrdInc α] : OrdInc (Option α) where
  ord_inc {mx my} h := match mx, my, h with
    | none, none, _ => ⟨none, rfl⟩
    | none, some b, _ => ⟨some b, rfl⟩
    | some _, some _, .inl e => ⟨none, congrArg some e.symm⟩
    | some _, some _, .inr i =>
      let ⟨z, hz⟩ := OrdInc.ord_inc i
      ⟨some z, congrArg some hz⟩
  ordN_incN {_ mx my} h := match mx, my, h with
    | none, none, _ => ⟨none, .rfl⟩
    | none, some b, _ => ⟨some b, .rfl⟩
    | some _, some _, .inl e => ⟨none, OFE.some_dist_some.mpr e.symm⟩
    | some _, some _, .inr i =>
      let ⟨z, hz⟩ := OrdInc.ordN_incN i
      ⟨some z, OFE.some_dist_some.mpr hz⟩

instance instIsInc [IsInc α] : IsInc (Option α) := {}

/-! ### The extension inclusion on `Option α` -/

theorem some_inc_some_of_dist_opM {n} {x y : α} {mz : Option α} (H : x ≡{n}≡ y •? mz) :
    some y ≼{n} some x :=
  match mz with | none => ⟨none, H⟩ | some z => ⟨some z, H⟩

theorem some_ordN_some_of_dist_opM [IncOrd α] {n} {x y : α} {mz : Option α}
    (H : x ≡{n}≡ y •? mz) : some y ≼ₒ{n} some x :=
  IncOrd.incN_ordN (some_inc_some_of_dist_opM H)

theorem inc_of_some_inc_some [IsTotal α] {x y : α} (H : some y ≼ some x) :
    y ≼ x :=
  let ⟨mz, hmz⟩ := H
  match mz with
  | none => ⟨core y, (Option.some.inj hmz).trans (op_core y).symm⟩
  | some z => ⟨z, Option.some.inj hmz⟩

theorem some_incN_some_iff_some [IsTotal α] {n} {x y : α} :
    some y ≼{n} some x → y ≼{n} x
  | ⟨none, hmz⟩ => ⟨core y, dist_of_some_dist_some hmz |>.trans (op_core_dist y).symm⟩
  | ⟨some z, hmz⟩ => ⟨z, hmz⟩

@[rocq_alias option_included]
theorem inc_iff {ma mb : Option α} :
    ma ≼ mb ↔
      ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a = b ∨ a ≼ b) := by
  refine ⟨fun ⟨mc, Hmc⟩ => ?_, ?_⟩
  · rcases ma with _|a
    · exact .inl rfl
    rcases mb with _|b
    · rcases mc with _|c <;> simp [op, optionOp] at Hmc
    refine .inr ⟨a, b, rfl, rfl, ?_⟩
    rcases mc with _|c <;> simp [op, optionOp] at Hmc
    · exact .inl Hmc.symm
    · exact .inr ⟨c, Hmc⟩
  · rintro (H|⟨_, _, _, _, (H|⟨z, _⟩)⟩) <;> subst_eqs
    · exists mb
    · exists none
    · exists some z

@[rocq_alias option_includedN]
theorem incN_iff {n} {ma mb : Option α} :
    ma ≼{n} mb ↔
      ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ (a ≡{n}≡ b ∨ a ≼{n} b) := by
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
    ma ≼ mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼ b :=
  inc_iff.trans <| or_congr_right <| exists₂_congr fun _ _ => and_congr_right fun _ =>
    and_congr_right fun _ => ⟨fun h => h.elim (· ▸ inc_refl _) id, .inr⟩

@[rocq_alias option_includedN_total]
theorem incN_iff_is_total [IsTotal α] {n} {ma mb : Option α} :
    ma ≼{n} mb ↔ ma = none ∨ ∃ a b, ma = some a ∧ mb = some b ∧ a ≼{n} b :=
  incN_iff.trans <| or_congr_right <| exists₂_congr fun a _ => and_congr_right fun _ =>
    and_congr_right fun _ =>
      ⟨fun h => h.elim (⟨core a, ·.symm.trans (op_core_dist a).symm⟩) id, .inr⟩

@[rocq_alias Some_includedN]
theorem some_incN_some_iff {n} {a b : α} :
    some a ≼{n} some b ↔ a ≡{n}≡ b ∨ a ≼{n} b := by
  apply incN_iff.trans; simp

@[rocq_alias Some_includedN_1]
theorem dist_or_incN_of_some_incN_some {n} {a b : α} (h : some a ≼{n} some b) :
    a ≡{n}≡ b ∨ a ≼{n} b := some_incN_some_iff.mp h

@[rocq_alias Some_includedN_2]
theorem some_incN_some_of_dist_or_incN {n} {a b : α} (h : a ≡{n}≡ b ∨ a ≼{n} b) :
    some a ≼{n} some b := some_incN_some_iff.mpr h

@[rocq_alias Some_includedN_mono]
theorem some_incN_some_of_incN {n} {a b : α} (h : a ≼{n} b) : some a ≼{n} some b :=
  some_incN_some_iff.mpr (.inr h)

@[rocq_alias Some_includedN_refl]
theorem some_incN_some_of_dist {n} {a b : α} (h : a ≡{n}≡ b) : some a ≼{n} some b :=
  some_incN_some_iff.mpr (.inl h)

@[rocq_alias Some_includedN_is_Some]
theorem isSome_of_some_incN {n} {a : α} {mb : Option α} (h : some a ≼{n} mb) :
    mb.isSome := by
  rcases incN_iff.mp h with h | ⟨_, _, _, rfl, _⟩ <;> simp_all

@[rocq_alias Some_included]
theorem some_inc_some_iff {a b : α} : some a ≼ some b ↔ a = b ∨ a ≼ b := by
  apply inc_iff.trans; simp

@[rocq_alias Some_included_1]
theorem eq_or_inc_of_some_inc_some {a b : α} (h : some a ≼ some b) :
    a = b ∨ a ≼ b :=
  some_inc_some_iff.mp h

@[rocq_alias Some_included_2]
theorem some_inc_some_of_eq_or_inc {a b : α} (h : a = b ∨ a ≼ b) :
    some a ≼ some b :=
  some_inc_some_iff.mpr h

@[rocq_alias Some_included_mono]
theorem some_inc_some_of_inc {a b : α} (h : a ≼ b) : some a ≼ some b :=
  some_inc_some_iff.mpr (.inr h)

@[rocq_alias Some_included_refl]
theorem some_inc_some_of_eq {a b : α} (h : a = b) : some a ≼ some b :=
  some_inc_some_iff.mpr (.inl h)

@[rocq_alias Some_included_is_Some]
theorem isSome_of_some_inc {a : α} {mb : Option α} (h : some a ≼ mb) : mb.isSome := by
  rcases inc_iff.mp h with h | ⟨_, _, _, rfl, _⟩ <;> simp_all

@[rocq_alias is_Some_includedN]
theorem isSome_monoN {n} {ma mb : Option α} (h : ma ≼{n} mb) :
    ma.isSome → mb.isSome := by
  cases ma with
  | none => simp
  | some _ => exact fun _ => isSome_of_some_incN h

@[rocq_alias is_Some_included]
theorem isSome_mono {ma mb : Option α} (h : ma ≼ mb) : ma.isSome → mb.isSome := by
  cases ma with
  | none => simp
  | some _ => exact fun _ => isSome_of_some_inc h

@[rocq_alias Some_included_exclusive]
theorem eqv_of_inc_exclusive [Exclusive (a : α)] {b : α} (H : some a ≼ some b)
    (Hv : ✓ b) : a = b :=
  (eq_or_inc_of_some_inc_some H).elim id fun h => (not_valid_of_excl_inc h Hv).elim

@[rocq_alias Some_includedN_exclusive]
theorem dist_of_inc_exclusive [Exclusive (a : α)] {n} {b : α} (H : some a ≼{n} some b)
    (Hv : ✓{n} b) : a ≡{n}≡ b :=
  (dist_or_incN_of_some_incN_some H).elim id fun h => (not_valid_of_exclN_inc h Hv).elim

@[rocq_alias Some_included_total]
theorem some_inc_some_iff_is_total [IsTotal α] {a b : α} :
    some a ≼ some b ↔ a ≼ b :=
  ⟨inc_of_some_inc_some, some_inc_some_of_inc⟩

@[rocq_alias option_fmap_mono]
theorem map_mono {β : Type _} [RA β] (f : α → β) {ma mb : Option α}
    (hf : ∀ x y : α, x ≼ y → f x ≼ f y) (h : ma ≼ mb) :
    ma.map f ≼ mb.map f := by
  rcases inc_iff.mp h with rfl | ⟨a, b, rfl, rfl, hab⟩
  · exact ⟨mb.map f, by cases mb.map f <;> rfl⟩
  · rcases hab with rfl | hab
    · exact inc_refl _
    · exact some_inc_some_iff.mpr (.inr (hf a b hab))

@[rocq_alias Some_includedN_total]
theorem some_incN_some_iff_is_total [IsTotal α] {n} {a b : α} :
    some a ≼{n} some b ↔ a ≼{n} b :=
  ⟨some_incN_some_iff_some, some_incN_some_of_incN⟩

@[rocq_alias cancelable_Some]
instance {a : α} [IdFree a] [Cancelable a] : Cancelable (some a) := by
  refine ⟨@fun n b c Hv He => ?_⟩
  rcases b, c with ⟨_|b, _|c⟩
  · trivial
  · exact id_free0_r c (valid0_of_validN Hv) (He.symm.le SIdx.le_0_l)
  · refine id_free0_r b ?_ (He.le SIdx.le_0_l)
    exact valid0_of_validN (He.validN.mp Hv)
  · exact cancelableN (α := α) Hv He

@[rocq_alias option_cancelable]
instance {ma : Option α} [∀ a : α, IdFree a] [∀ a : α, Cancelable a] : Cancelable ma := by
  rcases ma with ⟨_|_⟩
  constructor
  · simp [op]
  · infer_instance

@[rocq_alias cmra_validN_Some_includedN]
theorem validN_of_incN_validN {n} {a b : α} (Hv : ✓{n} a) (Hinc : some b ≼{n} some a) :
    ✓{n} b :=
  validN_of_incN (α := Option α) Hinc Hv

@[rocq_alias cmra_valid_Some_included]
theorem valid_of_inc_valid {a b : α} (Hv : ✓ a) (Hinc : some b ≼ some a) : ✓ b :=
  valid_of_inc (α := Option α) Hinc Hv

@[rocq_alias Some_included_opM]
theorem some_inc_some_iff_opM {a b : α} : some a ≼ some b ↔ ∃ mc, b = a •? mc := by
  simp [inc_iff]
  constructor
  · rintro (Heqv | ⟨mc', Hinc⟩)
    · exact ⟨none, by simpa [op?] using Heqv.symm⟩
    · exact ⟨some mc', Hinc⟩
  · rintro ⟨_|z, H⟩
    · exact .inl H.symm
    · exact .inr ⟨z, H⟩

@[rocq_alias Some_includedN_opM]
theorem some_incN_some_iff_opM {n} {a b : α} :
    some a ≼{n} some b ↔ ∃ mc, b ≡{n}≡ a •? mc := by
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
instance [ORA.Discrete α] : ORA.Discrete (Option α) where
  discrete_valid {x} := match x with
    | none => fun _ => trivial
    | some _ => discrete_valid (α := α)
  discrete_ord {x y} h := match x, y, h with
    | none, none, _ => trivial
    | none, some _, h => h
    | some _, none, h => False.elim h
    | some _, some _, h =>
      Or.elim h (fun e => Or.inl (OFE.Discrete.discrete_0 e))
        fun i => Or.inr (discrete_ord (α := α) i)

end Option
end option

section unit
open ORA

#rocq_ignore unit_op_instance "Use CMRA instance"
#rocq_ignore unit_pcore_instance "Use CMRA instance"
#rocq_ignore unit_valid_instance "Use CMRA instance"
#rocq_ignore unit_validN_instance "Use CMRA instance"
#rocq_ignore unit_cancelable "Subsumed by empty_cancelable"
#rocq_ignore unit_core_id "Subsumed by unit_CoreId"

instance Unit.instURA : URA Unit where
  pcore _ := some ()
  op _ _ := ()
  assoc := rfl
  comm := rfl
  pcore_op_left _ := rfl
  pcore_idem _ := rfl
  unit := ()
  unit_left_id := rfl
  pcore_unit := rfl
  total _ := ⟨(), rfl⟩

@[reducible] def Unit.cmraData : CMRAData Unit where
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ := id
  pcore_ne _ _ := ⟨(), rfl, .rfl⟩
  validN_ne _ := id
  valid_iff_validN := ⟨fun _ _ => ⟨⟩, fun _ => ⟨⟩⟩
  validN_le := fun h _ => h
  validN_op_left := id
  extend _ _ := ⟨(), (), rfl, .rfl, .rfl⟩
  pcore_op_mono _ _ := ⟨.unit, rfl⟩

@[rocq_alias unit_cmra_mixin, rocq_alias unitR]
instance cmraUnit : CMRA Unit := ofCMRAData Unit.cmraData

#rocq_ignore unit_unit_instance "Use UCMRA instance"
#rocq_ignore unit_ucmra_mixin "Use UCMRA instance"

theorem Unit.ucmraData : UCMRAData Unit where
  unit_valid := ⟨⟩

@[rocq_alias unitUR]
instance ucmraUnit : UCMRA Unit := UORA.ofUCMRAData Unit.ucmraData

@[rocq_alias unit_cmra_discrete]
instance : ORA.Discrete Unit where
  discrete_valid _ := ⟨⟩
  discrete_ord _ := ⟨(), rfl⟩

end unit

section empty
open ORA

#rocq_ignore Empty_set_op_instance "Use CMRA instance"
#rocq_ignore Empty_set_pcore_instance "Use CMRA instance"
#rocq_ignore Empty_set_valid_instance "Use CMRA instance"
#rocq_ignore Empty_set_validN_instance "Use CMRA instance"
#rocq_ignore Empty_set_cmra_mixin "Use CMRA instance"

instance Empty.instRA : RA Empty where
  pcore x := some x
  op x _ := x
  assoc {x} := x.elim
  comm {x} := x.elim
  pcore_op_left {x} := x.elim
  pcore_idem {x} := x.elim

@[reducible] def Empty.cmraData : CMRAData Empty where
  ValidN _ _ := False
  Valid _ := False
  op_ne.ne _ _ _ _ := .rfl
  pcore_ne {_ x} := x.elim
  validN_ne _ := id
  valid_iff_validN {x} := x.elim
  validN_le := fun h _ => h
  validN_op_left := id
  extend {_ x} := x.elim
  pcore_op_mono {x} := x.elim

@[rocq_alias Empty_setR]
instance cmraEmpty : CMRA Empty := ofCMRAData Empty.cmraData

@[rocq_alias Empty_set_cmra_discrete]
instance : ORA.Discrete Empty where
  discrete_valid := id
  discrete_ord {x} := x.elim

@[rocq_alias Empty_set_core_id]
instance (x : Empty) : CoreId x where
  core_id := rfl

@[rocq_alias Empty_set_cancelable]
instance (x : Empty) : Cancelable x where
  cancelableN := x.elim

end empty

namespace Prod
open ORA

variable {α β : Type _}

abbrev pcore [PCore α] [PCore β] (x : α × β) : Option (α × β) := (ORA.pcore x.fst).bind fun a =>
  (ORA.pcore x.snd).bind fun b =>
  return (a, b)

abbrev op [Op α] [Op β] (x y : α × β) : α × β :=
  (x.1 • y.1, x.2 • y.2)

@[reducible, rocq_alias prod_op_instance]
instance raOp [Op α] [Op β] : Op (α × β) where
  op := op
  assoc := Prod.ext assoc assoc
  comm := Prod.ext comm comm

@[reducible, rocq_alias prod_pcore_instance]
instance raPCore [PCore α] [PCore β] : PCore (α × β) where
  pcore := pcore
  pcore_idem {x cx} h := by
    have ⟨cx₁, hcx₁, this⟩ := Option.bind_eq_some_iff.mp h
    have ⟨cx₂, hcx₂, hcx⟩ := Option.bind_eq_some_iff.mp this
    rw [Option.some.inj hcx.symm]
    have h₁ : PCore.pcore cx₁ = some cx₁ := PCore.pcore_idem hcx₁
    have h₂ : PCore.pcore cx₂ = some cx₂ := PCore.pcore_idem hcx₂
    simp [pcore, h₁, h₂]

instance raRA [RA α] [RA β] : RA (α × β) where
  pcore_op_left h :=
    let ⟨_, ha, ho⟩ := Option.bind_eq_some_iff.mp h
    let ⟨_, hb, hh⟩ := Option.bind_eq_some_iff.mp ho
    (Option.some.inj hh) ▸ (equiv_prod_ext (RA.pcore_op_left ha) (RA.pcore_op_left hb))

variable [RA α] [ORA α] [RA β] [ORA β]

abbrev ValidN (n) (x : α × β) := ✓{n} x.fst ∧ ✓{n} x.snd

@[indexed]
abbrev Valid (x : α × β) := ✓ x.fst ∧ ✓ x.snd

abbrev OrderN (n) (x y : α × β) := x.fst ≼ₒ{n} y.fst ∧ x.snd ≼ₒ{n} y.snd

abbrev Order (x y : α × β) := x.fst ≼ₒ y.fst ∧ x.snd ≼ₒ y.snd

@[reducible, rocq_alias prod_valid_instance, rocq_alias prod_validN_instance]
def raValid : _root_.Iris.Valid (α × β) where
  ValidN := ValidN
  Valid := Valid
  valid_iff_validN {x} := by
    refine ⟨fun ⟨va, vb⟩ n => ⟨va.validN, vb.validN⟩, fun h => ⟨?_, ?_⟩⟩
    · exact valid_iff_validN.mpr fun n => (h n).left
    · exact valid_iff_validN.mpr fun n => (h n).right

@[reducible] def raOrdered : Ordered (α × β) where
  OrderN := OrderN
  Order := Order
  ordN_trans h₁ h₂ := ⟨ordN_trans h₁.1 h₂.1, ordN_trans h₁.2 h₂.2⟩
  ord_trans h₁ h₂ := ⟨ord_trans h₁.1 h₂.1, ord_trans h₁.2 h₂.2⟩
  ordN_of_ord n h := ⟨ordN_of_ord n h.1, ordN_of_ord n h.2⟩

attribute [local instance] raOrdered in
theorem raOrderedNE : OrderedNE (α × β) where
  ordN_ne ex ey h :=
    ⟨ordN_ne (dist_fst ex) (dist_fst ey) h.1, ordN_ne (dist_snd ex) (dist_snd ey) h.2⟩
  ordN_le h le := ⟨ordN_le h.1 le, ordN_le h.2 le⟩

section
open ORA
attribute [local instance] raOp raPCore raValid raOrdered raOrderedNE

@[rocq_alias prod_pcore_Some, rocq_alias prod_pcore_Some']
theorem pcore_eq_some {x cx : α × β} :
    ORA.pcore x = some cx ↔ ORA.pcore x.1 = some cx.1 ∧ ORA.pcore x.2 = some cx.2 := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ =>
    Option.bind_eq_some_iff.mpr ⟨cx.1, h₁, Option.bind_eq_some_iff.mpr ⟨cx.2, h₂, rfl⟩⟩⟩
  obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  exact ⟨h₁, h₂⟩

theorem increasing_iff {x : α × β} : Increasing x ↔ Increasing x.1 ∧ Increasing x.2 := ⟨fun h =>
    ⟨⟨fun y => (h.increasing (y, x.2)).1⟩, ⟨fun y => (h.increasing (x.1, y)).2⟩⟩,
   fun ⟨h₁, h₂⟩ => ⟨fun y => ⟨h₁.increasing y.1, h₂.increasing y.2⟩⟩⟩

theorem ordNR_fst {n} {x y : α × β} (h : x ≼ₒ*{n} y) : x.1 ≼ₒ*{n} y.1 := h.imp dist_fst And.left
theorem ordNR_snd {n} {x y : α × β} (h : x ≼ₒ*{n} y) : x.2 ≼ₒ*{n} y.2 := h.imp dist_snd And.right

@[rocq_alias prodR, rocq_alias prod_cmra_mixin]
instance cmraProd : ORA (α × β) where
  toValid := raValid
  op_ne.ne _ _ _ h := dist_prod_ext (Dist.op_r <| dist_fst h) (Dist.op_r <| dist_snd h)
  pcore_ne {n} {x y cx} h ph := by
    have ⟨cx₁, hcx₁, this⟩ := Option.bind_eq_some_iff.mp ph
    have ⟨cx₂, hcx₂, hcx⟩ := Option.bind_eq_some_iff.mp this
    have ⟨cy₁, hcy₁, hxy₁⟩ := pcore_ne (dist_fst h) hcx₁
    have ⟨cy₂, hcy₂, hxy₂⟩ := pcore_ne (dist_snd h) hcx₂
    suffices g : cx ≡{n}≡ (cy₁, cy₂) by simp [hcy₁, hcy₂, g, pcore, PCore.pcore]
    calc
      cx ≡{n}≡ (cx₁, cx₂) := Dist.of_eq (Option.some.inj hcx).symm
      _  ≡{n}≡ (cy₁, cy₂) := dist_prod_ext hxy₁ hxy₂
  validN_ne {_ x y} H := fun ⟨vx1, vx2⟩ => ⟨H.1.validN.mp vx1, H.2.validN.mp vx2⟩
  validN_le {n n'} {x} := fun ⟨va, vb⟩ le => ⟨validN_le va le, validN_le vb le⟩
  toOrderedNE := raOrderedNE
  validN_op_left := fun ⟨va, vb⟩ => ⟨validN_op_left va, validN_op_left vb⟩
  extend := fun ⟨vx₁, vx₂⟩ e =>
    let ⟨z₁, w₁, hx₁, hz₁, hw₁⟩ := extend vx₁ (OFE.dist_fst e)
    let ⟨z₂, w₂, hx₂, hz₂, hw₂⟩ := extend vx₂ (OFE.dist_snd e)
    ⟨(z₁, z₂), (w₁, w₂), equiv_prod_ext hx₁ hx₂, ⟨hz₁, hz₂⟩, ⟨hw₁, hw₂⟩⟩
  toOrdered := raOrdered
  op_monoN_left_ord z h := ⟨op_monoN_left_ord z.1 h.1, op_monoN_left_ord z.2 h.2⟩
  op_mono_left_ord z h := ⟨op_mono_left_ord z.1 h.1, op_mono_left_ord z.2 h.2⟩
  validN_of_ordN h v := ⟨validN_of_ordN h.1 v.1, validN_of_ordN h.2 v.2⟩
  pcore_monoN_ord h e :=
    let ⟨e₁, e₂⟩ := pcore_eq_some.mp e
    let ⟨cy₁, hcy₁, i₁⟩ := pcore_monoN_ord h.1 e₁
    let ⟨cy₂, hcy₂, i₂⟩ := pcore_monoN_ord h.2 e₂
    ⟨(cy₁, cy₂), pcore_eq_some.mpr ⟨hcy₁, hcy₂⟩, i₁, i₂⟩
  pcore_mono_ord h e :=
    let ⟨e₁, e₂⟩ := pcore_eq_some.mp e
    let ⟨cy₁, hcy₁, i₁⟩ := pcore_mono_ord h.1 e₁
    let ⟨cy₂, hcy₂, i₂⟩ := pcore_mono_ord h.2 e₂
    ⟨(cy₁, cy₂), pcore_eq_some.mpr ⟨hcy₁, hcy₂⟩, i₁, i₂⟩
  pcore_order_op e y :=
    let ⟨e₁, e₂⟩ := pcore_eq_some.mp e
    let ⟨cxy₁, h₁, i₁⟩ := pcore_order_op e₁ y.1
    let ⟨cxy₂, h₂, i₂⟩ := pcore_order_op e₂ y.2
    ⟨(cxy₁, cxy₂), pcore_eq_some.mpr ⟨h₁, h₂⟩, i₁, i₂⟩
  pcore_increasing e :=
    let ⟨e₁, e₂⟩ := pcore_eq_some.mp e
    increasing_iff.mpr ⟨pcore_increasing e₁, pcore_increasing e₂⟩
  increasing_closed h h' :=
    let ⟨h₁, h₂⟩ := increasing_iff.mp h
    increasing_iff.mpr ⟨increasing_closed h₁ (ordNR_fst h'), increasing_closed h₂ (ordNR_snd h')⟩
  ordN_extend hs v h :=
    let ⟨z₁, h₁, e₁⟩ := ordN_extend hs v.1 h.1
    let ⟨z₂, h₂, e₂⟩ := ordN_extend hs v.2 h.2
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
    ORA.pcore (a, b) = (ORA.pcore a).bind fun c₁ => (ORA.pcore b).bind fun c₂ => some (c₁, c₂) :=
  rfl

@[rocq_alias pair_core]
theorem mk_core [IsTotal α] [IsTotal β] (a : α) (b : β) :
    core (a, b) = (core a, core b) :=
  congrArg (Option.getD · (a, b)) (pcore_eq_some.mpr ⟨pcore_eq_core a, pcore_eq_core b⟩)

theorem ord_def {x y : α × β} : x ≼ₒ y ↔ x.1 ≼ₒ y.1 ∧ x.2 ≼ₒ y.2 := .rfl

theorem ordN_def {n} {x y : α × β} : x ≼ₒ{n} y ↔ x.1 ≼ₒ{n} y.1 ∧ x.2 ≼ₒ{n} y.2 := .rfl

theorem mk_ord_mk (a a' : α) (b b' : β) : (a, b) ≼ₒ (a', b') ↔ a ≼ₒ a' ∧ b ≼ₒ b' := .rfl

theorem mk_ordN_mk {n} (a a' : α) (b b' : β) :
    (a, b) ≼ₒ{n} (a', b') ↔ a ≼ₒ{n} a' ∧ b ≼ₒ{n} b' := .rfl

@[rocq_alias prod_included]
theorem inc_def {x y : α × β} : x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2 :=
  ⟨fun ⟨z, hz⟩ => ⟨⟨z.1, congrArg Prod.fst hz⟩, ⟨z.2, congrArg Prod.snd hz⟩⟩,
   fun ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ => ⟨(z₁, z₂), Prod.ext hz₁ hz₂⟩⟩

@[rocq_alias prod_includedN]
theorem incN_def {n} {x y : α × β} :
    x ≼{n} y ↔ x.1 ≼{n} y.1 ∧ x.2 ≼{n} y.2 :=
  ⟨fun ⟨z, hz⟩ => ⟨⟨z.1, dist_fst hz⟩, ⟨z.2, dist_snd hz⟩⟩,
   fun ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ => ⟨(z₁, z₂), dist_prod_ext hz₁ hz₂⟩⟩

@[rocq_alias pair_included]
theorem mk_inc_mk (a a' : α) (b b' : β) :
    (a, b) ≼ (a', b') ↔ a ≼ a' ∧ b ≼ b' := inc_def

@[rocq_alias pair_includedN]
theorem mk_incN_mk {n} (a a' : α) (b b' : β) :
    (a, b) ≼{n} (a', b') ↔ a ≼{n} a' ∧ b ≼{n} b' := incN_def

@[rocq_alias prod_cmra_total]
instance instIsTotalProd [IsTotal α] [IsTotal β] : IsTotal (α × β) where
  total x :=
    let ⟨ca, ha⟩ := total x.1
    let ⟨cb, hb⟩ := total x.2
    ⟨(ca, cb), pcore_eq_some.mpr ⟨ha, hb⟩⟩

@[rocq_alias prod_cmra_discrete]
instance instCmraDiscreteProd [ORA.Discrete α] [ORA.Discrete β] : ORA.Discrete (α × β) where
  discrete_valid v := ⟨discrete_valid v.1, discrete_valid v.2⟩
  discrete_ord h := ⟨discrete_ord h.1, discrete_ord h.2⟩

instance instOrderRefl [OrderRefl α] [OrderRefl β] : OrderRefl (α × β) where
  ord_refl x := ⟨ord_refl x.1, ord_refl x.2⟩

instance instIncOrd [IncOrd α] [IncOrd β] : IncOrd (α × β) :=
  IncOrd.of_increasing fun x => increasing_iff.mpr ⟨IncOrd.increasing x.1, IncOrd.increasing x.2⟩

instance instOrdInc [OrdInc α] [OrdInc β] : OrdInc (α × β) where
  ord_inc h := inc_def.mpr (h.imp OrdInc.ord_inc OrdInc.ord_inc)
  ordN_incN h := incN_def.mpr (h.imp OrdInc.ordN_incN OrdInc.ordN_incN)

instance instIsInc [IsInc α] [IsInc β] : IsInc (α × β) := {}

omit [ORA α] [ORA β] in
/-- SI-free: core-identity only involves the cores. -/
@[rocq_alias pair_core_id]
instance instCoreIdPair [PCore α] [PCore β] {x : α} {y : β} [CoreId x] [CoreId y] :
    CoreId (x, y) where
  core_id := by
    change Prod.pcore (x, y) = some (x, y)
    simp [Prod.pcore, CoreId.core_id (x := x), CoreId.core_id (x := y)]

@[rocq_alias pair_exclusive_l]
instance instExclusivePairLeft {x : α} [Exclusive x] {y : β} : Exclusive (x, y) where
  exclusive0_l z hv := exclusive0_l z.1 hv.1

@[rocq_alias pair_exclusive_r]
instance instExclusivePairRight {x : α} {y : β} [Exclusive y] : Exclusive (x, y) where
  exclusive0_l z hv := exclusive0_l z.2 hv.2

@[rocq_alias pair_cancelable]
instance instCancelablePair {x : α} {y : β} [Cancelable x] [Cancelable y] : Cancelable (x, y) where
  cancelableN hv he := ⟨cancelableN hv.1 he.1, cancelableN hv.2 he.2⟩

@[rocq_alias pair_id_free_l]
instance instIdFreePairLeft {x : α} [IdFree x] {y : β} : IdFree (x, y) where
  id_free0_r z hv he := id_free0_r z.1 hv.1 he.1

@[rocq_alias pair_id_free_r]
instance instIdFreePairRight {x : α} {y : β} [IdFree y] : IdFree (x, y) where
  id_free0_r z hv he := id_free0_r z.2 hv.2 he.2

end Prod

section ProdUnit
namespace Prod
open ORA

instance raURA {α β : Type _} [URA α] [URA β] : URA (α × β) where
  unit := (unit, unit)
  unit_left_id := Prod.ext URA.unit_left_id URA.unit_left_id
  pcore_unit := pcore_eq_some.mpr ⟨URA.pcore_unit, URA.pcore_unit⟩
  total x := ⟨(core x.1, core x.2), pcore_eq_some.mpr ⟨pcore_eq_core _, pcore_eq_core _⟩⟩

variable {α β : Type _} [URA α] [UORA α] [URA β] [UORA β]

#rocq_ignore prod_unit_instance "Use UCMRA instance"
#rocq_ignore prod_ucmra_mixin "Use UCMRA instance"

@[rocq_alias prodUR]
instance ucmraProd : UORA (α × β) where
  unit_valid := ⟨unit_valid, unit_valid⟩

@[rocq_alias pair_split, rocq_alias pair_split_L]
theorem mk_split (a : α) (b : β) : (a, b) = ((a, unit) : α × β) • (unit, b) :=
  Prod.ext unit_right_id.symm unit_left_id.symm

@[rocq_alias pair_op_1, rocq_alias pair_op_1_L]
theorem mk_op_fst (a a' : α) :
    ((a • a', unit) : α × β) = ((a, unit) : α × β) • (a', unit) :=
  Prod.ext rfl unit_left_id.symm

@[rocq_alias pair_op_2, rocq_alias pair_op_2_L]
theorem mk_op_snd (b b' : β) :
    ((unit, b • b') : α × β) = ((unit, b) : α × β) • (unit, b') :=
  Prod.ext unit_left_id.symm rfl

end Prod
end ProdUnit

section OptionProd

open ORA Iris.Option Iris.OFE.Option

variable {α β : Type _} [RA α] [ORA α] [RA β] [ORA β]

namespace Option

theorem some_mk_ordN {n} {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ₒ{n} some (a₂, b₂)) :
    some a₁ ≼ₒ{n} some a₂ ∧ some b₁ ≼ₒ{n} some b₂ :=
  h.elim (·.imp .inl .inl) (·.imp .inr .inr)

theorem some_mk_ordN_left {n} {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ₒ{n} some (a₂, b₂)) :
    some a₁ ≼ₒ{n} some a₂ := (some_mk_ordN h).1

theorem some_mk_ordN_right {n} {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ₒ{n} some (a₂, b₂)) :
    some b₁ ≼ₒ{n} some b₂ := (some_mk_ordN h).2

theorem some_mk_ord {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ₒ some (a₂, b₂)) :
    some a₁ ≼ₒ some a₂ ∧ some b₁ ≼ₒ some b₂ :=
  h.elim (fun e => (Prod.mk.inj e).imp .inl .inl) (·.imp .inr .inr)

theorem some_mk_ord_left {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ₒ some (a₂, b₂)) :
    some a₁ ≼ₒ some a₂ := (some_mk_ord h).1

theorem some_mk_ord_right {a₁ a₂ : α} {b₁ b₂ : β} (h : some (a₁, b₁) ≼ₒ some (a₂, b₂)) :
    some b₁ ≼ₒ some b₂ := (some_mk_ord h).2

@[rocq_alias Some_pair_includedN]
theorem some_mk_incN {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) :
    some a₁ ≼{n} some a₂ ∧ some b₁ ≼{n} some b₂ := by
  rcases some_incN_some_iff.mp h with hd | hi
  · exact ⟨some_incN_some_of_dist hd.1, some_incN_some_of_dist hd.2⟩
  · have ⟨h₁, h₂⟩ := Prod.incN_def.mp hi
    exact ⟨some_incN_some_of_incN h₁, some_incN_some_of_incN h₂⟩

@[rocq_alias Some_pair_includedN_l]
theorem some_mk_incN_left {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) : some a₁ ≼{n} some a₂ :=
  (some_mk_incN h).1

@[rocq_alias Some_pair_includedN_r]
theorem some_mk_incN_right {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) : some b₁ ≼{n} some b₂ :=
  (some_mk_incN h).2

@[rocq_alias Some_pair_includedN_total_1]
theorem some_mk_incN_total_fst [IsTotal α] {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) :
    a₁ ≼{n} a₂ ∧ some b₁ ≼{n} some b₂ :=
  let ⟨h₁, h₂⟩ := some_mk_incN h
  ⟨some_incN_some_iff_is_total.mp h₁, h₂⟩

@[rocq_alias Some_pair_includedN_total_2]
theorem some_mk_incN_total_snd [IsTotal β] {n} {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼{n} some (a₂, b₂)) :
    some a₁ ≼{n} some a₂ ∧ b₁ ≼{n} b₂ :=
  let ⟨h₁, h₂⟩ := some_mk_incN h
  ⟨h₁, some_incN_some_iff_is_total.mp h₂⟩

@[rocq_alias Some_pair_included]
theorem some_mk_inc {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ some (a₂, b₂)) :
    some a₁ ≼ some a₂ ∧ some b₁ ≼ some b₂ := by
  rcases (some_inc_some_iff (α := α × β)).mp h with he | hi
  · exact ⟨some_inc_some_of_eq (congrArg Prod.fst he),
      some_inc_some_of_eq (congrArg Prod.snd he)⟩
  · have ⟨h₁, h₂⟩ := Prod.inc_def.mp hi
    exact ⟨some_inc_some_of_inc h₁, some_inc_some_of_inc h₂⟩

@[rocq_alias Some_pair_included_l]
theorem some_mk_inc_left {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ some (a₂, b₂)) : some a₁ ≼ some a₂ :=
  (some_mk_inc h).1

@[rocq_alias Some_pair_included_r]
theorem some_mk_inc_right {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ some (a₂, b₂)) : some b₁ ≼ some b₂ :=
  (some_mk_inc h).2

@[rocq_alias Some_pair_included_total_1]
theorem some_mk_inc_total_fst [IsTotal α] {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ some (a₂, b₂)) :
    a₁ ≼ a₂ ∧ some b₁ ≼ some b₂ :=
  let ⟨h₁, h₂⟩ := some_mk_inc h
  ⟨some_inc_some_iff_is_total.mp h₁, h₂⟩

@[rocq_alias Some_pair_included_total_2]
theorem some_mk_inc_total_snd [IsTotal β] {a₁ a₂ : α} {b₁ b₂ : β}
    (h : some (a₁, b₁) ≼ some (a₂, b₂)) :
    some a₁ ≼ some a₂ ∧ b₁ ≼ b₂ :=
  let ⟨h₁, h₂⟩ := some_mk_inc h
  ⟨h₁, some_inc_some_iff_is_total.mp h₂⟩

end Option
end OptionProd

section OptionMor

open ORA

variable {α β : Type _} [RA α] [ORA α] [RA β] [ORA β]

@[rocq_alias option_fmap_cmra_morphism]
def Option.mapC (f : α -C> β) : Option α -C> Option β where
  toHom := optionMap f.toHom
  validN {_ x} h := by cases x with | none => trivial | some a => exact f.validN h
  pcore x := by
    cases x with | none => rfl | some a => exact congrArg some (f.pcore a)
  op x y := by
    cases x <;> cases y <;> try rfl
    exact congrArg some (f.op ..)
  monoN_ord {n} {x y} h := match x, y, h with
    | none, none, _ => trivial
    | none, some _, h => f.increasing h
    | some _, some _, h => h.imp (f.ne.ne ·) f.monoN_ord
  mono_ord {x y} h := match x, y, h with
    | none, none, _ => trivial
    | none, some _, h => f.increasing h
    | some _, some _, h => h.imp (congrArg f) f.mono_ord
  increasing {x} h := match x, h with
    | none, _ => (inferInstance : Increasing (none : Option β))
    | some _, h => Option.increasing_some_iff.mpr (f.increasing (Option.increasing_some_iff.mp h))

end OptionMor

section ProdMor

open ORA

variable [RA A] [ORA A] [RA A'] [ORA A'] [RA B] [ORA B] [RA B'] [ORA B']

@[rocq_alias prod_map_cmra_morphism]
def Prod.mapC (f : A -C> A') (g : B -C> B') : A × B -C> A' × B' where
  f := Prod.map f g
  ne := inferInstance
  validN {n} {x} := fun ⟨h1, h2⟩ => ⟨f.validN h1, g.validN h2⟩
  pcore x := by
    simp [Option.map, Prod.map, ORA.pcore, pcore]
    have h2 := g.pcore x.snd
    have h1 := f.pcore x.fst
    cases _ : ORA.pcore x.fst
    · cases _ : ORA.pcore (f.f x.fst) <;> simp_all
    · cases _ : ORA.pcore x.snd <;>
      cases _ : ORA.pcore (f.f x.fst) <;>
      cases _ : ORA.pcore (g.f x.snd) <;>
      simp_all
  op x y := equiv_prod_ext (f.op x.fst y.fst) (g.op x.snd y.snd)
  monoN_ord h := ⟨f.monoN_ord h.1, g.monoN_ord h.2⟩
  mono_ord h := ⟨f.mono_ord h.1, g.mono_ord h.2⟩
  increasing h :=
    Prod.increasing_iff.mpr <| (Prod.increasing_iff.mp h).imp f.increasing g.increasing

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

instance instRFunctorAffineProdOF [RFunctor F1] [RFunctor F2] [RFunctorAffine F1]
    [RFunctorAffine F2] : RFunctorAffine (ProdOF F1 F2) where
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

instance instRFunctorAffineOptionOF [RFunctor F] [RFunctorAffine F] :
    RFunctorAffine (OptionOF F) where
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

namespace CMRA
open ORA

variable {α β : Type _}

/-- Constructing a CMRA `β` through a mapping into a CMRA `α`.

The mapping may restrict the domain (i.e., we have an injection from `β` to `α`, not a
bijection) and validity. These two restrictions work on opposite "ends" of `α` according to
`≼`: domain restriction must prove that when an element is in the domain, so is its
composition with other elements; validity restriction must prove that if the composition of
two elements is valid, then so are both of the elements. The "domain" is the image of `g` in
`α`, or equivalently the part of `α` where `f` returns `some`. -/
@[reducible, rocq_alias inj_cmra_mixin_restrict_validity]
def ofInjRestrictValidity [RA α] [CMRA α] [OFE β] [RA β]
    (Valid : β → Prop) (ValidN : SI → β → Prop)
    (f : α → Option β) (g : β → α)
    -- `g` is non-expansive and injective w.r.t. OFE equality
    (g_dist : ∀ (n) (y₁ y₂ : β), y₁ ≡{n}≡ y₂ ↔ g y₁ ≡{n}≡ g y₂)
    -- `g` is surjective into the part of `α` where `f` returns `some`, and `f` is its inverse
    (gf_dist : ∀ (x : α) (y : β) (n), f x ≡{n}≡ some y ↔ g y ≡{n}≡ x)
    -- `g` commutes with `pcore` (where it is defined) and with `op`
    (g_pcore_dist : ∀ (y cy : β) (n), PCore.pcore y ≡{n}≡ some cy ↔ ORA.pcore (g y) ≡{n}≡ some (g cy))
    (g_op : ∀ y₁ y₂, g (y₁ • y₂) = g y₁ • g y₂)
    -- `g` commutes with `opM` when the right-hand side is produced by `f`, cancelling it
    (g_opM_f : ∀ (x : α) (y : β), g ((f x).elim y (y • ·)) = g y • x)
    -- the validity predicate on `β` restricts the one on `α`
    (g_validN : ∀ (n) (y : β), ValidN n y → ✓{n} (g y))
    -- the validity predicate on `β` satisfies the laws of validity
    (validN_ne : ∀ (n) (y₁ y₂ : β), y₁ ≡{n}≡ y₂ → ValidN n y₁ → ValidN n y₂)
    (valid_validN : ∀ y : β, Valid y ↔ ∀ n, ValidN n y)
    (validN_le : ∀ n n' (y : β), ValidN n y → n' ≤ n → ValidN n' y)
    (validN_op_left : ∀ n (y₁ y₂ : β), ValidN n (y₁ • y₂) → ValidN n y₁) :
    CMRA β :=
  have g_ne : ∀ {n} {y₁ y₂ : β}, y₁ ≡{n}≡ y₂ → g y₁ ≡{n}≡ g y₂ := (g_dist ..).mp
  have g_eq : ∀ {y₁ y₂ : β}, y₁ = y₂ ↔ g y₁ = g y₂ :=
    eq_dist.trans <| (forall_congr' fun n => g_dist n _ _).trans eq_dist.symm
  have g_pcore : ∀ {y cy : β}, PCore.pcore y = some cy ↔ ORA.pcore (g y) = some (g cy) :=
    eq_dist.trans <| (forall_congr' fun n => g_pcore_dist _ _ n).trans eq_dist.symm
  have gf : ∀ {x : α} {y : β}, f x = some y ↔ g y = x :=
    eq_dist.trans <| (forall_congr' fun n => gf_dist _ _ n).trans eq_dist.symm
  ofCMRAData {
    Valid, ValidN
    op_ne.ne _ _ _ h := (g_dist ..).mpr <|
      (g_op ..).dist.trans <| (g_ne h).op_r.trans (g_op ..).symm.dist
    pcore_ne h hcy :=
      let ⟨c, hc, hcd⟩ := pcore_ne (g_ne h) (g_pcore.mp hcy)
      dist_some <| (g_pcore_dist ..).mpr <| hc.dist.trans <| some_dist_some.mpr hcd.symm
    validN_ne h hv := validN_ne _ _ _ h hv
    valid_iff_validN := valid_validN _
    validN_le hv le := validN_le _ _ _ hv le
    validN_op_left hv := validN_op_left _ _ _ hv
    extend := fun hv he => by
      obtain ⟨x₁, x₂, hx, hx₁, hx₂⟩ :=
        extend (g_validN _ _ hv) (((g_dist ..).mp he).trans (g_op ..).dist)
      obtain ⟨w₁, hw₁, hd₁⟩ := distSome ((gf_dist ..).mpr hx₁.symm)
      obtain ⟨w₂, hw₂, hd₂⟩ := distSome ((gf_dist ..).mpr hx₂.symm)
      refine ⟨w₁, w₂, g_eq.mpr ?_, hd₁.symm, hd₂.symm⟩
      rw [g_op, gf.mp hw₁, gf.mp hw₂]
      exact hx
    pcore_op_mono := fun {y cy} h z => by
      obtain ⟨c, hc⟩ := ORA.pcore_op_mono (g_pcore.mp h) (g z)
      obtain ⟨w, hw⟩ : ∃ w, (f c).elim cy (cy • ·) = cy • w := match f c with
        | some w => ⟨w, rfl⟩
        | none => ⟨cy, (pcore_op_left (pcore_idem h)).symm⟩
      rw [← g_op, ← g_opM_f c cy, hw] at hc
      exact ⟨w, g_pcore.mpr hc⟩ }

/-- Constructing a CMRA through an isomorphism that may restrict validity. -/
@[reducible, rocq_alias iso_cmra_mixin_restrict_validity]
def ofIsoRestrictValidity [RA α] [CMRA α] [OFE β] [RA β]
    (Valid : β → Prop) (ValidN : SI → β → Prop)
    (f : α → β) (g : β → α)
    -- `g` is non-expansive and injective w.r.t. OFE equality
    (g_dist : ∀ (n) (y₁ y₂ : β), y₁ ≡{n}≡ y₂ ↔ g y₁ ≡{n}≡ g y₂)
    -- `g` is surjective, and `f` is its inverse
    (gf : ∀ x : α, g (f x) = x)
    -- `g` commutes with `pcore` and with `op`
    (g_pcore : ∀ y : β, ORA.pcore (g y) = (PCore.pcore y).map g)
    (g_op : ∀ y₁ y₂, g (y₁ • y₂) = g y₁ • g y₂)
    -- the validity predicate on `β` restricts the one on `α`
    (g_validN : ∀ (n) (y : β), ValidN n y → ✓{n} (g y))
    -- the validity predicate on `β` satisfies the laws of validity
    (validN_ne : ∀ (n) (y₁ y₂ : β), y₁ ≡{n}≡ y₂ → ValidN n y₁ → ValidN n y₂)
    (valid_validN : ∀ y : β, Valid y ↔ ∀ n, ValidN n y)
    (validN_le : ∀ n n' (y : β), ValidN n y → n' ≤ n → ValidN n' y)
    (validN_op_left : ∀ n (y₁ y₂ : β), ValidN n (y₁ • y₂) → ValidN n y₁) :
    CMRA β :=
  ofInjRestrictValidity Valid ValidN (fun x => some (f x)) g g_dist
    (fun x y n => ⟨fun h => ((g_dist ..).mp h.symm).trans (gf x).dist,
      fun h => (g_dist ..).mpr <| (gf x).dist.trans h.symm⟩)
    (fun y cy n => by
      rw [g_pcore]
      cases PCore.pcore y with
      | none => simp
      | some z => exact g_dist n z cy)
    g_op (fun x y => (g_op y (f x)).trans <| congrArg (g y • ·) (gf x))
    g_validN validN_ne valid_validN validN_le validN_op_left

/-- Constructing a CMRA through an isomorphism. -/
@[reducible, rocq_alias iso_cmra_mixin]
def ofIso [RA α] [CMRA α] [OFE β] [RA β]
    (Valid : β → Prop) (ValidN : SI → β → Prop)
    (f : α → β) (g : β → α)
    -- `g` is non-expansive and injective w.r.t. OFE equality
    (g_dist : ∀ (n) (y₁ y₂ : β), y₁ ≡{n}≡ y₂ ↔ g y₁ ≡{n}≡ g y₂)
    -- `g` is surjective, and `f` is its inverse
    (gf : ∀ x : α, g (f x) = x)
    -- `g` commutes with `pcore`, `op`, `Valid` and `ValidN`
    (g_pcore : ∀ y : β, ORA.pcore (g y) = (PCore.pcore y).map g)
    (g_op : ∀ y₁ y₂, g (y₁ • y₂) = g y₁ • g y₂)
    (g_valid : ∀ y : β, ✓ (g y) ↔ Valid y)
    (g_validN : ∀ (n) (y : β), ✓{n} (g y) ↔ ValidN n y) :
    CMRA β :=
  ofIsoRestrictValidity Valid ValidN f g g_dist gf g_pcore g_op
    (fun n y => (g_validN n y).mpr)
    (fun n y₁ y₂ h hv =>
      (g_validN n y₂).mp <| validN_ne ((g_dist ..).mp h) <| (g_validN n y₁).mpr hv)
    (fun y => (g_valid y).symm.trans <|
      valid_iff_validN.trans <| forall_congr' fun n => g_validN n y)
    (fun n n' y hv hle => (g_validN n' y).mp <| validN_of_le hle <| (g_validN n y).mpr hv)
    (fun n y₁ y₂ hv => (g_validN n y₁).mp <| validN_op_left <|
      g_op y₁ y₂ ▸ (g_validN n (y₁ • y₂)).mpr hv)

/-- Constructing a CMRA on a discrete OFE from its SI-free resource algebra `RA α`: only the
validity predicate and its laws are asked for. -/
@[indexed, reducible, rocq_alias discrete_cmra_mixin]
def ofDiscrete [OFE α] [OFE.Discrete α] [RA α] (Valid : α → Prop)
    (valid_op_left : ∀ x y : α, Valid (x • y) → Valid x)
    (pcore_op_mono : ∀ x cx : α, pcore x = some cx → ∀ y, ∃ cy, pcore (x • y) = some (cx • cy)) :
    CMRA α := ofCMRAData {
  ValidN _ := Valid
  Valid := Valid
  op_ne.ne _ _ _ h := (congrArg (_ • ·) (OFE.discrete h)).dist
  pcore_ne h hcx := ⟨_, (OFE.discrete h) ▸ hcx, .rfl⟩
  validN_ne h hv := (OFE.discrete h) ▸ hv
  valid_iff_validN := (forall_const _).symm
  validN_le := fun h _ => h
  validN_op_left := valid_op_left _ _
  extend _ h := ⟨_, _, OFE.discrete h, .rfl, .rfl⟩
  pcore_op_mono := pcore_op_mono _ _ }

/-- `ofDiscrete` for a resource algebra with a total core. -/
@[reducible, rocq_alias ra_total_mixin]
def ofDiscreteTotal [OFE α] [OFE.Discrete α] [RA α] [IsTotal α] (Valid : α → Prop)
    (valid_op_left : ∀ x y : α, Valid (x • y) → Valid x)
    (core_op_mono : ∀ x y : α, ∃ cy, core (x • y) = core x • cy) :
    CMRA α :=
  ofDiscrete Valid valid_op_left fun x _ h y => by
    cases (pcore_eq_core x).symm.trans h
    exact (core_op_mono x y).imp fun _ e => (pcore_eq_core _).trans (congrArg some e)

section OfDiscrete

@[rocq_alias discrete_cmra_discrete]
instance ofDiscrete_discrete [OFE α] [OFE.Discrete α] [RA α] (Valid : α → Prop) h₁ h₂ :
    @Discrete _ _ α _ (ofDiscrete Valid h₁ h₂).toORA :=
  letI := ofDiscrete Valid h₁ h₂
  { discrete_valid := id
    discrete_ord := CMRA.ord_of_ord0 (α := α) }

end OfDiscrete
end CMRA

namespace ORA

/-- Constructing an ordered resource algebra on a discrete OFE from its SI-free resource algebra
`RA α`. Because the OFE is discrete the step-indexed laws follow from their plain counterparts,
so only the latter are asked for. -/
@[reducible] def ofDiscrete [OFE α] [OFE.Discrete α] [RA α]
    (Valid : α → Prop) (Order : α → α → Prop)
    (valid_op_left : ∀ x y : α, Valid (x • y) → Valid x)
    (ord_trans : ∀ x y z : α, Order x y → Order y z → Order x z)
    (op_mono_left : ∀ x y z : α, Order x y → Order (x • z) (y • z))
    (valid_of_ord : ∀ x y : α, Order x y → Valid y → Valid x)
    (pcore_mono : ∀ x y cx : α, Order x y → pcore x = some cx →
      ∃ cy, pcore y = some cy ∧ Order cx cy)
    (pcore_order_op : ∀ x cx : α, pcore x = some cx →
      ∀ y, ∃ cxy, pcore (x • y) = some cxy ∧ Order cx cxy)
    (pcore_increasing : ∀ x cx : α, pcore x = some cx → ∀ y, Order y (cx • y))
    (increasing_closed : ∀ x y : α, (∀ z, Order z (x • z)) → Order x y → ∀ z, Order z (y • z)) :
    ORA α :=
  letI : _root_.Iris.Valid α :=
    { Valid
      ValidN _ := Valid
      valid_iff_validN := (forall_const _).symm }
  letI : Ordered α :=
    { Order
      OrderN _ := Order
      ordN_trans := ord_trans _ _ _
      ord_trans := ord_trans _ _ _
      ordN_of_ord _ := id }
  { op_ne.ne _ _ _ h := (congrArg (_ • ·) (OFE.discrete h)).dist
    pcore_ne h hcx := ⟨_, (OFE.discrete h) ▸ hcx, .rfl⟩
    validN_ne h hv := (OFE.discrete h) ▸ hv
    validN_le := fun h _ => h
    ordN_ne ex ey h := (OFE.discrete ex) ▸ (OFE.discrete ey) ▸ h
    ordN_le := fun h _ => h
    validN_op_left := valid_op_left _ _
    extend _ h := ⟨_, _, OFE.discrete h, .rfl, .rfl⟩
    op_monoN_left_ord z h := op_mono_left _ _ z h
    op_mono_left_ord z h := op_mono_left _ _ z h
    validN_of_ordN := valid_of_ord _ _
    pcore_monoN_ord h e := pcore_mono _ _ _ h e
    pcore_mono_ord h e := pcore_mono _ _ _ h e
    pcore_order_op e y := pcore_order_op _ _ e y
    pcore_increasing e := ⟨pcore_increasing _ _ e⟩
    increasing_closed {_ x y} hx h := ⟨fun z => match h with
        | .inl e => (OFE.discrete e) ▸ hx.increasing z
        | .inr ho => increasing_closed x y (fun w => hx.increasing w) ho z⟩
    ordN_extend _ _ h := ⟨_, h, .rfl⟩ }

end ORA
end CmraMixin
end Iris


/-! Printing of the step-index-free notations (see `Iris.Algebra.StepIndex`). -/
namespace Iris.StepIndexSugar


@[app_unexpander Valid.Valid] meta def unexpandValid : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `(✓ $x)
  | _ => throw ()
@[app_unexpander Ordered.Order] meta def unexpandOrder : Lean.PrettyPrinter.Unexpander
  | `($_ $x $y) => `($x ≼ₒ $y)
  | _ => throw ()
@[app_unexpander Ordered.OrderR] meta def unexpandOrderR : Lean.PrettyPrinter.Unexpander
  | `($_ $x $y) => `($x ≼ₒ* $y)
  | _ => throw ()
@[app_unexpander Iris.ORA.Hom] meta def unexpandORAHom : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a -C> $b)
  | _ => throw ()

end Iris.StepIndexSugar
