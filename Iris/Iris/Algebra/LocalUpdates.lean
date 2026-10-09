/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Сухарик (@suhr), Mario Carneiro
-/
module

public import Iris.Algebra.CMRA

@[expose] public section

namespace Iris

variable {SI : Type _} [instSI : SIdx SI]

variable (SI) in
@[rocq_alias local_update]
def LocalUpdate [ORA SI α] (x y : α × α) : Prop :=
  ∀ (n : SI) mz, ✓{n} x.1 → x.1 ≡{n}≡ x.2 •? mz → ✓{n} y.1 ∧ y.1 ≡{n}≡ y.2 •? mz

notation:50 x:51 " ~l~>[" SI "] " y:50 => Iris.LocalUpdate SI x y

section LocalUpdate
open ORA

section ORA

variable [ORA SI α]

@[refl]
theorem LocalUpdate.id (x : α × α) : x ~l~>[SI] x := fun _ _ vx e => ⟨vx, e⟩

theorem LocalUpdate.trans {x y z : α × α} (uxy : x ~l~>[SI] y) (uyz : y ~l~>[SI] z) : x ~l~>[SI] z :=
  fun n mz vx e => (uxy n mz vx e).elim (uyz n mz)

instance : Trans (LocalUpdate SI (α := α)) (LocalUpdate SI) (LocalUpdate SI) where
  trans := LocalUpdate.trans

#rocq_ignore local_update_preorder "Use LocalUpdate.id and LocalUpdate.trans"
#rocq_ignore local_update_proper "OFE is Leibniz; use equality"

@[rocq_alias exclusive_local_update]
theorem LocalUpdate.exclusive [Exclusive SI y] {x x' : α}
    (vx' : ✓[SI] x') : (x, y) ~l~>[SI] (x', x') := by
  intro n mz vx e
  cases none_of_excl_valid_op ((OFE.Dist.validN e).mp vx)
  exact ⟨vx'.validN, .rfl⟩

@[rocq_alias op_local_update]
theorem LocalUpdate.op {x y z : α}
    (h : ∀ (n : SI), ✓{n} x → ✓{n} (z • x)) : (x, y) ~l~>[SI] (z • x, z • y) := by
  refine fun n mz vx e => ⟨h n vx, ?_⟩
  calc
    (z • x) ≡{n}≡ z • (y •? mz) := e.op_r
    _       ≡{n}≡ (z • y) •? mz := OFE.Dist.symm (op_opM_assoc_dist z y mz)

@[rocq_alias op_local_update_discrete]
theorem LocalUpdate.op_discrete [Discrete SI α] (x y z : α)
    (h : ✓[SI] x → ✓[SI] (z • x)) : (x, y) ~l~>[SI] (z • x, z • y) :=
  .op fun n vx => (h ((valid_iff_validN' n).mpr vx)).validN

@[rocq_alias op_local_update_frame]
theorem LocalUpdate.op_frame (x y x' y' yf : α)
    (h : (x, y) ~l~>[SI] (x', y')) : (x, y • yf) ~l~>[SI] (x', y' • yf) := by
  intro n mz vx e
  have ⟨h1, h2⟩ := h n (some yf • mz) vx <| calc
    x ≡{n}≡ (y • yf) •? mz := e
    _ ≡{n}≡ y •? (some yf • mz) := Option.op_some_opM_assoc_dist
  exists h1
  calc
    x' ≡{n}≡ y' •? (some yf • mz) := h2
    _  ≡{n}≡ (y' • yf) •? mz      := Option.op_some_opM_assoc_dist.symm

@[rocq_alias cancel_local_update]
theorem LocalUpdate.cancel (x y z : α) [Cancelable SI x] : (x • y, x • z) ~l~>[SI] (y, z) :=
  fun _ _ vx e => ⟨validN_op_right vx, op_opM_cancel_dist vx e⟩

@[rocq_alias replace_local_update]
theorem LocalUpdate.replace (x y : α) [IdFree SI x] (h : ✓[SI] y) : (x, x) ~l~>[SI] (y, y) := by
  intro _ mz vx e
  match mz with
  | none   => exact ⟨h.validN, .rfl⟩
  | some _ => cases id_freeN_r vx e.symm

@[rocq_alias core_id_local_update]
theorem LocalUpdate.core_id (x y z : α) [CoreId y] (le : y ≼ x) :
    (x, z) ~l~>[SI] (x, z • y) := by
  refine fun n mz vx e => ⟨vx, ?_⟩
  refine (op_core_right_of_inc le).symm.dist.trans ?_
  match mz with
  | none => calc
    y • x ≡{n}≡ y • z := e.op_r
    _     ≡{n}≡ z • y := op_commN
  | some w => calc
    y • x ≡{n}≡ y • (z • w) := op_right_dist y e
    _     ≡{n}≡ (y • z) • w := op_assocN
    _     ≡{n}≡ (z • y) • w := op_commN.op_l

@[rocq_alias local_update_discrete]
theorem LocalUpdate.discrete [Discrete SI α] (x y x' y' : α) :
    (x, y) ~l~>[SI] (x', y') ↔ ∀ mz, ✓[SI] x → x = y •? mz → (✓[SI] x' ∧ x' = y' •? mz) := by
  refine ⟨fun h mz vx e => ?_, fun h n mz vx e => ?_⟩
  · have ⟨vx', e⟩ := h 0 mz vx.validN e.dist
    exact ⟨discrete_valid vx', OFE.discrete_0 e⟩
  · have ⟨vx', e'⟩ := h mz ((valid_iff_validN' n).mpr vx) (OFE.discrete e)
    exact ⟨vx'.validN, e'.dist⟩

@[rocq_alias local_update_valid0]
theorem LocalUpdate.valid0 {x y x' y' : α}
    (h : ✓{(0 : SI)} x → ✓{(0 : SI)} y → some y ≼{(0 : SI)} some x → (x, y) ~l~>[SI] (x', y')) :
    (x, y) ~l~>[SI] (x', y') := by
  intro n mz vx e
  have v0y : ✓{(0 : SI)} y := valid0_of_validN <| validN_opM ((OFE.Dist.validN e).mp vx)
  have : some y ≼{(0 : SI)} some x := inc0_of_incN (Option.some_inc_some_of_dist_opM e)
  exact h (valid0_of_validN vx) v0y this n mz vx e

@[rocq_alias local_update_valid]
theorem LocalUpdate.valid [Discrete SI α] {x y x' y' : α}
    (h : ✓[SI] x → ✓[SI] y → some y ≼ some x → (x, y) ~l~>[SI] (x', y')) : (x, y) ~l~>[SI] (x', y') :=
  .valid0 fun vx0 vy0 mz =>
    h (discrete_valid vx0) (discrete_valid vy0) (inc_of_inc0 mz)

@[rocq_alias local_update_total_valid0]
theorem LocalUpdate.total_valid0 [IsTotal α] {x y x' y' : α}
    (h : ✓{(0 : SI)} x → ✓{(0 : SI)} y → y ≼{(0 : SI)} x → (x, y) ~l~>[SI] (x', y')) : (x, y) ~l~>[SI] (x', y') :=
  .valid0 fun vx0 vy0 mz => h vx0 vy0 (Option.some_incN_some_iff_is_total.mp mz)

@[rocq_alias local_update_total_valid]
theorem LocalUpdate.total_valid [IsTotal α] [Discrete SI α] {x y x' y' : α}
    (h : ✓[SI] x → ✓[SI] y → y ≼ x → (x, y) ~l~>[SI] (x', y')) : (x, y) ~l~>[SI] (x', y') :=
  .valid fun vx vy le => h vx vy (Option.inc_of_some_inc_some le)

end ORA

section UORA

variable [UORA SI α]

@[rocq_alias local_update_unital]
theorem local_update_unital {x y x' y' : α} :
    (x, y) ~l~>[SI] (x', y') ↔ ∀ (n : SI) z, ✓{n} x → x ≡{n}≡ y • z → (✓{n} x' ∧ x' ≡{n}≡ y' • z) where
  mp h n z := h n (some z)
  mpr h n mz vx e :=
    match mz with
    | none =>
      let ⟨h1, h2⟩ := h n unit vx (e.trans (unit_right_id_dist y).symm)
      ⟨h1, h2.trans (unit_right_id_dist y')⟩
    | some z => h n z vx e

@[rocq_alias local_update_unital_discrete]
theorem local_update_unital_discrete [Discrete SI α] (x y x' y' : α) :
    (x, y) ~l~>[SI] (x', y') ↔ ∀ z, ✓[SI] x → x = y • z → (✓[SI] x' ∧ x' = y' • z) where
  mp h z vx e :=
    have ⟨vx', e'⟩ := h 0 (some z) (Valid.validN vx) e.dist
    ⟨discrete_valid vx', OFE.discrete_0 e'⟩
  mpr h := by
    refine local_update_unital.mpr fun n z vnx e => ?_
    have ⟨vx', e'⟩ := h z ((valid_iff_validN' n).mpr vnx) (OFE.discrete e)
    exact ⟨vx'.validN, e'.dist⟩

@[rocq_alias cancel_local_update_unit]
theorem cancel_local_update_unit (x y : α) [Cancelable SI x] : (x • y, x) ~l~>[SI] (y, unit) :=
  have e : (x • y, x • unit) = (x • y, x) := OFE.equiv_prod_ext rfl unit_right_id
  e ▸ LocalUpdate.cancel x y unit

/-- Necessary and sufficient condition for a local update on a unital discrete leibniz ORA
  with trivial validity predicate -/
theorem discrete_unital_triv_local_update [Discrete SI α]
    (Hv : ∀ x : α, ✓[SI] x)
    (H : ∀ {z : α}, x = y • z → x' = y' • z) :
    (x,y) ~l~>[SI] (x', y') := by
  refine (local_update_unital_discrete x y x' y').mpr fun _ _ He => ?_
  refine ⟨Hv _, H He⟩

end UORA

@[rocq_alias unit_local_update]
theorem LocalUpdate.unit {x y x' y' : Unit} : (x, y) ~l~>[SI] (x', y') := .id ((), ())

@[rocq_alias discrete_fun_local_update]
theorem LocalUpdate.discrete_fun {β : α → Type _} [∀ x, UORA SI (β x)]
    {f g f' g' : ∀ x, β x} (h : ∀ x : α, (f x, g x) ~l~>[SI] (f' x, g' x)) :
    (f, g) ~l~>[SI] (f', g') := by
  refine fun n mz vx e => ⟨fun x => ?_, fun x => ?_⟩
  · match mz with
    | none => exact (h x n none (vx x) (e x)).left
    | some z => exact (h x n (some (z x)) (vx x) (e x)).left
  · match mz with
    | none => exact (h x n none (vx x) (e x)).right
    | some z => exact (h x n (some (z x)) (vx x) (e x)).right

variable [ORA SI α] [ORA SI β]

@[rocq_alias prod_local_update]
theorem LocalUpdate.prod {x y x' y' : α × β}
    (hl : (x.1, y.1) ~l~>[SI] (x'.1, y'.1)) (hr : (x.2, y.2) ~l~>[SI] (x'.2, y'.2)) :
    (x, y) ~l~>[SI] (x', y') := by
  intro n mz vx e
  match mz with
  | none =>
    have ⟨v₁, e₁⟩ := hl n none vx.left e.left
    have ⟨v₂, e₂⟩ := hr n none vx.right e.right
    exact ⟨⟨v₁, v₂⟩, ⟨e₁, e₂⟩⟩
  | some z =>
    have ⟨v₁, e₁⟩ := hl n (some z.fst) vx.left e.left
    have ⟨v₂, e₂⟩ := hr n (some z.snd) vx.right e.right
    exact ⟨⟨v₁, v₂⟩, ⟨e₁, e₂⟩⟩

@[rocq_alias prod_local_update']
theorem LocalUpdate.prod' {x1 y1 x1' y1' : α} {x2 y2 x2' y2' : β}
    (hl : (x1, y1) ~l~>[SI] (x1', y1')) (hr : (x2, y2) ~l~>[SI] (x2', y2')) :
    ((x1, x2), (y1, y2)) ~l~>[SI] ((x1', x2'), (y1', y2')) :=
  .prod hl hr

@[rocq_alias prod_local_update_1]
theorem LocalUpdate.prod_1 {x1 y1 x1' y1' : α} (x2 y2 : β)
    (h : (x1, y1) ~l~>[SI] (x1', y1')) : ((x1, x2), (y1, y2)) ~l~>[SI] ((x1', x2), (y1', y2)) :=
  .prod' h (.id _)

@[rocq_alias prod_local_update_2]
theorem LocalUpdate.prod_2 (x1 y1 : α) {x2 y2 x2' y2' : β}
    (h : (x2, y2) ~l~>[SI] (x2', y2')) : ((x1, x2), (y1, y2)) ~l~>[SI] ((x1, x2'), (y1, y2')) :=
  .prod' (.id _) h

@[rocq_alias option_local_update]
theorem LocalUpdate.option {x y x' y' : α}
    (h : (x, y) ~l~>[SI] (x', y')) : (some x, some y) ~l~>[SI] (some x', some y') := by
  intro n mz
  match mz with
  | none | some none => exact h n none
  | some (some z) => exact h n (some z)

@[rocq_alias option_local_update_None]
theorem LocalUpdate.option_none {α} [UORA SI α] {x x' y' : α}
    (h : (x, UnitOp.unit) ~l~>[SI] (x', y')) : (some x, none) ~l~>[SI] (some x', some y') := by
  intro n mz vx e
  let .some (some z) := mz
  exact h n (some z) vx (.trans e (unit_left_id_dist z).symm)

@[rocq_alias alloc_option_local_update]
theorem LocalUpdate.alloc_option {x : α} (y : Option α)
    (vx : ✓[SI] x) : (none, y) ~l~>[SI] (some x, some x) := by
  intro n mz _ e
  match mz with
  | none | some none => exact ⟨vx.validN, .rfl⟩
  | some (some z) =>
    have ⟨_, hw⟩ := Option.exists_op_some_dist_some (n := n) y z
    cases e.trans hw

@[rocq_alias delete_option_local_update]
theorem LocalUpdate.delete_option (x : Option α) (y : α) [Exclusive SI y] :
    (x, some y) ~l~>[SI] (none, none) := by
  intro n mz vx e
  match mz with
  | none | some none => exact ⟨trivial, .rfl⟩
  | some (some z) => cases Option.not_valid_some_exclN_op_left <| (OFE.Dist.validN e).mp vx

@[rocq_alias delete_option_local_update_cancelable]
theorem LocalUpdate.delete_option_cancelable
    (mx : Option α) [Cancelable SI mx] : (mx, mx) ~l~>[SI] (none, none) := by
  intro _ mz vx e
  match mz with
  | none | some none => exact ⟨trivial, .rfl⟩
  | some (some _) =>
    exact ⟨trivial, cancelableN (Option.validN_op_unit vx) ((unit_right_id_dist mx).trans e)⟩

end LocalUpdate

end Iris
