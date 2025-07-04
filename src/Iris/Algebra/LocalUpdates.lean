/-
Copyright (c) 2025 Сухарик. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Сухарик (@suhr), Mario Carneiro
-/
import Iris.Algebra.CMRA

namespace Iris

def LocalUpdate [CMRA α] (x y : α × α) : Prop :=
  ∀n mz, ✓{n} x.1 → x.1 ≡{n}≡ x.2 •? mz → ✓{n} y.1 ∧ y.1 ≡{n}≡ y.2 •? mz

infixr:50 " ~l~> " => LocalUpdate

section localUpdate

section CMRA

variable [CMRA α]

-- Global Instance local_update_proper :
-- Proper ((≡) ==> (≡) ==> iff) (@local_update SI A).
-- Proof. unfold local_update. by repeat intro; setoid_subst. Qed.

theorem LocalUpdate.id (x : α × α) : x ~l~> x := fun _ _ vx e => ⟨vx, e⟩

theorem LocalUpdate.equiv_left {x y : α × α} (z : α × α) (h : x ≡ y) : x ~l~> z → y ~l~> z := by
  intro u n mw v e
  refine u n mw ((OFE.Dist.validN h.1.dist.symm).mp v) ?_
  calc
    x.fst ≡{n}≡ y.fst       := h.1.dist
    _     ≡{n}≡ y.snd •? mw := e
    _     ≡{n}≡ x.snd •? mw := CMRA.opM_left_dist mw (OFE.equiv_snd h).dist.symm

theorem LocalUpdate.equiv_right (x : α × α) {y z : α × α} (h : y ≡ z) : x ~l~> y → x ~l~> z := by
  intro u n mw v e
  let ⟨vy, e⟩ := u n mw v e
  refine ⟨h.dist.1.validN.mp vy, ?_⟩
  calc
    z.fst ≡{n}≡ y.fst       := h.dist.1.symm
    _     ≡{n}≡ y.snd •? mw := e
    _     ≡{n}≡ z.snd •? mw := h.dist.2.opM .rfl

-- Global Instance local_update_preorder : PreOrder (@local_update SI A).
-- Proof. split; unfold local_update; red; naive_solver. Qed.

theorem LocalUpdate.exclusive [CMRA.Exclusive y] {x x' : α}
    (vx' : ✓ x') : (x, y) ~l~> (x', x') := by
  intro n mz vx e
  cases CMRA.none_of_excl_valid_op ((OFE.Dist.validN e).mp vx)
  exact ⟨vx'.validN, .rfl⟩

theorem LocalUpdate.op {x y z : α}
    (h : ∀ n, ✓{n} x → ✓{n} (z • x)) : (x, y) ~l~> (z • x, z • y) := by
  refine fun n mz vx e => ⟨h n vx, ?_⟩
  calc
    (z • x) ≡{n}≡ z • (y •? mz) := e.op_r
    _       ≡{n}≡ (z • y) •? mz := OFE.Dist.symm (CMRA.op_opM_assoc_dist z y mz)

theorem LocalUpdate.op_discrete [CMRA.Discrete α] (x y z : α)
    (h : ✓ x → ✓ (z • x)) : (x, y) ~l~> (z • x, z • y) :=
  .op fun n vx => (h ((CMRA.valid_iff_validN' n).mpr vx)).validN

theorem LocalUpdate.op_frame (x y x' y' yf : α)
    (h : (x, y) ~l~> (x', y')) : (x, y • yf) ~l~> (x', y' • yf) := by
  intro n mz vx e
  have ⟨h1, h2⟩ := h n (some yf • mz) vx <| calc
    x ≡{n}≡ (y • yf) •? mz := e
    _ ≡{n}≡ y •? (some yf • mz) := CMRA.op_some_opM_assoc_dist y yf mz
  exists h1
  calc
    x' ≡{n}≡ y' •? (some yf • mz) := h2
    _  ≡{n}≡ (y' • yf) •? mz      := (CMRA.op_some_opM_assoc_dist y' yf mz).symm

theorem LocalUpdate.cancel (x y z : α) [CMRA.Cancelable x] : (x • y, x • z) ~l~> (y, z) :=
  fun _ _ vx e => ⟨CMRA.validN_op_right vx, CMRA.op_opM_cancel_dist vx e⟩

theorem LocalUpdate.replace (x y : α) [CMRA.IdFree x] (h : ✓ y) : (x, x) ~l~> (y, y) := by
  intro _ mz vx e
  match mz with
  | none   => exact ⟨h.validN, .rfl⟩
  | some _ => cases CMRA.id_freeN_r vx e.symm

theorem LocalUpdate.core_id (x y z : α) [CMRA.CoreId y] (inc : y ≼ x) : (x, z) ~l~> (x, z • y) := by
  refine fun n mz vx e => ⟨vx, ?_⟩
  refine (CMRA.op_core_right_of_inc inc).symm.dist.trans ?_
  match mz with
  | none => calc
    y • x ≡{n}≡ y • z := e.op_r
    _     ≡{n}≡ z • y := CMRA.op_commN
  | some w => calc
    y • x ≡{n}≡ y • (z • w) := CMRA.op_right_dist y e
    _     ≡{n}≡ (y • z) • w := CMRA.op_assocN
    _     ≡{n}≡ (z • y) • w := CMRA.op_commN.op_l

theorem LocalUpdate.discrete [CMRA.Discrete α] (x y x' y' : α) :
    (x, y) ~l~> (x', y') ↔ ∀ mz, ✓ x → x ≡ y •? mz → (✓ x' ∧ x' ≡ y' •? mz) := by
  refine ⟨fun h mz vx e => ?_, fun h n mz vx e => ?_⟩
  · have ⟨vx', e⟩ := h 0 mz vx.validN e.dist
    exact ⟨CMRA.discrete_valid vx', OFE.discrete_0 e⟩
  · have ⟨vx', e'⟩ := h mz ((CMRA.valid_iff_validN' n).mpr vx) (OFE.discrete e)
    exact ⟨vx'.validN, e'.dist⟩

theorem LocalUpdate.valid0 {x y x' y' : α}
    (h : ✓{0} x → ✓{0} y → some y ≼{0} some x → (x, y) ~l~> (x', y')) :
    (x, y) ~l~> (x', y') := by
  intro n mz vx e
  have v0y : ✓{0} y := CMRA.valid0_of_validN <| CMRA.validN_opM ((OFE.Dist.validN e).mp vx)
  have : some y ≼{0} some x := CMRA.inc0_of_incN (CMRA.some_inc_some_of_dist_opM e)
  exact h (CMRA.valid0_of_validN vx) v0y this n mz vx e

theorem LocalUpdate.valid [CMRA.Discrete α] {x y x' y' : α}
    (h : ✓ x → ✓ y → some y ≼ some x → (x, y) ~l~> (x', y')) : (x, y) ~l~> (x', y') :=
  .valid0 fun vx0 vy0 mz =>
    h (CMRA.discrete_valid vx0) (CMRA.discrete_valid vy0) ((CMRA.inc_iff_incN 0).mpr mz)

theorem LocalUpdate.total_valid0 [CMRA.IsTotal α] {x y x' y' : α}
    (h : ✓{0} x → ✓{0} y → y ≼{0} x → (x, y) ~l~> (x', y')) : (x, y) ~l~> (x', y') :=
  .valid0 fun vx0 vy0 mz => h vx0 vy0 (CMRA.incN_of_some_incN_some mz)

theorem LocalUpdate.total_valid [CMRA.IsTotal α] [CMRA.Discrete α] {x y x' y' : α}
    (h : ✓ x → ✓ y → y ≼ x → (x, y) ~l~> (x', y')) : (x, y) ~l~> (x', y') :=
  .valid fun vx vy inc => h vx vy (CMRA.inc_of_some_inc_some inc)

end CMRA

section UCMRA

variable [UCMRA α]

theorem local_update_unital {x y x' y' : α} :
    (x, y) ~l~> (x', y') ↔ ∀ n z, ✓{n} x → x ≡{n}≡ y • z → (✓{n} x' ∧ x' ≡{n}≡ y' • z) where
  mp h n z := h n (some z)
  mpr h n mz vx e :=
    match mz with
    | none =>
      let ⟨h1, h2⟩ := h n CMRA.unit vx (e.trans (CMRA.unit_right_id_dist y).symm)
      ⟨h1, h2.trans (CMRA.unit_right_id_dist y')⟩
    | some z => h n z vx e

theorem local_update_unital_discrete [CMRA.Discrete α] (x y x' y' : α) :
    (x, y) ~l~> (x', y') ↔ ∀ z, ✓ x → x ≡ y • z → (✓ x' ∧ x' ≡ y' • z) where
  mp h z vx e :=
    have ⟨vx', e'⟩ := h 0 (some z) (CMRA.Valid.validN vx) e.dist
    ⟨CMRA.discrete_valid vx', OFE.discrete_0 e'⟩
  mpr h := by
    refine local_update_unital.mpr fun n z vnx e => ?_
    have ⟨vx', e'⟩ := h z ((CMRA.valid_iff_validN' n).mpr vnx) (OFE.discrete e)
    exact ⟨vx'.validN, e'.dist⟩

theorem cancel_local_update_unit (x y : α) [CMRA.Cancelable x] : (x • y, x) ~l~> (y, CMRA.unit) :=
  have e : (x • y, x • CMRA.unit) ≡ (x • y, x) := ⟨.rfl, CMRA.unit_right_id⟩
  .equiv_left _ e (.cancel x y CMRA.unit)

end UCMRA

theorem LocalUpdate.unit {x y x' y' : Unit} : (x, y) ~l~> (x', y') := .id ((), ())

theorem LocalUpdate.discrete_fun {β : α → Type _} [∀ x, UCMRA (β x)]
    {f g f' g' : ∀ x, β x} (h : ∀ x : α, (f x, g x) ~l~> (f' x, g' x)) :
    (f, g) ~l~> (f', g') := by
  refine fun n mz vx e => ⟨fun x => ?_, fun x => ?_⟩
  · match mz with
    | none => exact (h x n none (vx x) (e x)).left
    | some z => exact (h x n (some (z x)) (vx x) (e x)).left
  · match mz with
    | none => exact (h x n none (vx x) (e x)).right
    | some z => exact (h x n (some (z x)) (vx x) (e x)).right

variable [CMRA α] [CMRA β]

theorem LocalUpdate.prod {x y x' y' : α × β}
    (hl : (x.1, y.1) ~l~> (x'.1, y'.1)) (hr : (x.2, y.2) ~l~> (x'.2, y'.2)) :
    (x, y) ~l~> (x', y') := by
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

theorem LocalUpdate.prod' {x1 y1 x1' y1' : α} {x2 y2 x2' y2' : β}
    (hl : (x1, y1) ~l~> (x1', y1')) (hr : (x2, y2) ~l~> (x2', y2')) :
    ((x1, x2), (y1, y2)) ~l~> ((x1', x2'), (y1', y2')) :=
  .prod hl hr

theorem LocalUpdate.prod_1 {x1 y1 x1' y1' : α} (x2 y2 : β)
    (h : (x1, y1) ~l~> (x1', y1')) : ((x1, x2), (y1, y2)) ~l~> ((x1', x2), (y1', y2)) :=
  .prod' h (.id _)

theorem LocalUpdate.prod_2 (x1 y1 : α) {x2 y2 x2' y2' : β}
    (h : (x2, y2) ~l~> (x2', y2')) : ((x1, x2), (y1, y2)) ~l~> ((x1, x2'), (y1, y2')) :=
  .prod' (.id _) h

theorem LocalUpdate.option {x y x' y' : α}
    (h : (x, y) ~l~> (x', y')) : (some x, some y) ~l~> (some x', some y') := by
  intro n mz
  match mz with
  | none | some none => exact h n none
  | some (some z) => exact h n (some z)

theorem LocalUpdate.option_none {α} [UCMRA α] {x x' y' : α}
    (h : (x, CMRA.unit) ~l~> (x', y')) : (some x, none) ~l~> (some x', some y') := by
  intro n mz vx e
  let .some (some z) := mz
  exact h n (some z) vx (.trans e (CMRA.unit_left_id_dist z).symm)

theorem LocalUpdate.alloc_option {x : α} (y : Option α)
    (vx : ✓ x) : (none, y) ~l~> (some x, some x) := by
  intro n mz _ e
  match mz with
  | none | some none => exact ⟨vx.validN, .rfl⟩
  | some (some z) =>
    have ⟨_, hw⟩ := CMRA.exists_op_some_dist_some (n := n) y z
    cases e.trans hw

theorem LocalUpdate.delete_option (x : Option α) (y : α) [CMRA.Exclusive y] :
    (x, some y) ~l~> (none, none) := by
  intro n mz vx e
  match mz with
  | none | some none => exact ⟨trivial, .rfl⟩
  | some (some z) => cases not_valid_some_exclN_op_left <| (OFE.Dist.validN e).mp vx

theorem LocalUpdate.delete_option_cancelable
    (mx : Option α) [CMRA.Cancelable mx] : (mx, mx) ~l~> (none, none) := by
  intro _ mz vx e
  match mz with
  | none | some none => exact ⟨trivial, .rfl⟩
  | some (some _) =>
    exact ⟨trivial, CMRA.cancelableN (validN_op_unit vx) ((CMRA.unit_right_id_dist mx).trans e)⟩
