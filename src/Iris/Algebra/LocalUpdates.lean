import Iris.Algebra.CMRA

namespace Iris

def LocalUpdate {α: Type}[CMRA α] (x y: α × α) :=
  ∀n mz, ✓{n} x.1 → x.1 ≡{n}≡ x.2 •? mz → ✓{n} y.1 ∧ y.1 ≡{n}≡ y.2 •? mz

infixr:50 " ~l~> " => LocalUpdate

namespace LocalUpdate

section CMRA
  variable [cmr: CMRA α]

  -- Global Instance local_update_proper :
  -- Proper ((≡) ==> (≡) ==> iff) (@local_update SI A).
  -- Proof. unfold local_update. by repeat intro; setoid_subst. Qed.

  -- Global Instance local_update_preorder : PreOrder (@local_update SI A).
  -- Proof. split; unfold local_update; red; naive_solver. Qed.

  theorem exclusive_local_update {y: α}[CMRA.Exclusive y](x x': α)(vx': ✓ x'): (x,y) ~l~> (x', x') :=
    fun n mz vx e =>
      have : mz = none         := CMRA.none_of_excl_valid_op ((OFE.Dist.validN e).mp vx)
      have : x' ≡{n}≡ x' •? mz := calc
        x' ≡{n}≡ x'   := OFE.Dist.of_eq rfl
        _  = x' •? mz := by rw[this]; rfl
      ⟨vx'.validN, this⟩

  theorem op_local_update (x y z : α) (h : ∀ n, ✓{n} x → ✓{n} (z • x)) : (x, y) ~l~> (z • x, z • y) :=
    fun n mz vx (e : x ≡{n}≡ y •? mz) =>
      have g1 : ✓{n} (z • x) := h n vx
      have g2 := calc
        (z • x) ≡{n}≡ z • (y •? mz) := CMRA.op_right_dist z e
        _       ≡{n}≡ (z • y) •? mz := OFE.Dist.symm (CMRA.op_opM_assoc_dist z y mz)
      ⟨g1, g2⟩

  theorem op_local_update_discrete [CMRA.Discrete α] (x y z : α)
      (h : ✓ x → ✓ (z • x)) : (x, y) ~l~> (z • x, z • y) :=
    fun n mz vx e =>
      have this n (vx: ✓{n} x): ✓{n} (z • x) :=
        CMRA.Valid.validN (h ((CMRA.valid_iff_validN' n).mpr vx))
      op_local_update x y z this n mz vx e

  theorem op_local_update_frame (x y x' y' yf : α)
      (h : (x, y) ~l~> (x', y')) : (x, y • yf) ~l~> (x', y' • yf) :=
    fun n mz vx e =>
      have := h n (some yf • mz) vx
      have := calc
        x ≡{n}≡ (y • yf) •? mz := e
        _ ≡{n}≡ y •? (some yf • mz) := (CMRA.op_some_opM_assoc y yf mz).dist
      have u := h n (some yf • mz) vx this
      have := calc
        x' ≡{n}≡ y' •? (some yf • mz) := u.2
        _  ≡{n}≡ (y' • yf) •? mz      := (CMRA.op_some_opM_assoc y' yf mz).symm.dist
      ⟨u.1, this⟩

  theorem cancel_local_update (x y z : α) [CMRA.Cancelable x] : (x • y, x • z) ~l~> (y, z) :=
  sorry

  theorem replace_local_update (x y : α) [CMRA.IdFree x] (h : ✓ y) : (x, x) ~l~> (y, y) :=
  sorry

  theorem core_id_local_update (x y z : α) [CMRA.CoreId y] (h : y ≼ x) : (x, z) ~l~> (x, z • y) :=
  sorry

  theorem local_update_discrete [CMRA.Discrete α] (x y x' y' : α) :
    (x, y) ~l~> (x', y') ↔ ∀ (mz : α), ✓ x → x ≡ y •? mz → (✓ x' ∧ x' ≡ y' •? mz) :=
  sorry

  theorem local_update_valid0 (x y x' y' : α) :
    (✓{0} x → ✓{0} y → some y ≼{0} some x → (x, y) ~l~> (x', y')) →
    (x, y) ~l~> (x', y') :=
  sorry

  theorem local_update_valid [CMRA.Discrete α] (x y x' y' : α) :
    (✓ x → ✓ y → some y ≼ some x → (x, y) ~l~> (x', y')) →
    (x, y) ~l~> (x', y') :=
  sorry

  theorem local_update_total_valid0 [CMRA.IsTotal α] (x y x' y' : α) :
    (✓{0} x → ✓{0} y → y ≼{0} x → (x, y) ~l~> (x', y')) →
    (x, y) ~l~> (x', y') :=
  sorry

  theorem local_update_total_valid [CMRA.IsTotal α] [CMRA.Discrete α] (x y x' y' : α) :
    (✓ x → ✓ y → y ≼ x → (x, y) ~l~> (x', y')) →
    (x, y) ~l~> (x', y') :=
  sorry
end CMRA

section UCMRA
  variable [uc: UCMRA α]

  -- the rest of the section
end UCMRA

section updates_unital
  variable [UCMRA α]
  -- variable {x y : α}

  theorem local_update_unital (x y x' y' : α) :
    (x, y) ~l~> (x', y') ↔ ∀ n z,
      ✓{n} x → x ≡{n}≡ y • z → (✓{n} x' ∧ x' ≡{n}≡ y' • z) :=
  sorry

  theorem local_update_unital_discrete [CMRA.Discrete α] (x y x' y' : α) :
    (x, y) ~l~> (x', y') ↔ ∀ z,
      ✓ x → x ≡ y • z → (✓ x' ∧ x' ≡ y' • z) :=
  sorry

  theorem cancel_local_update_unit (x y : α) [CMRA.Cancelable x] :
    (x • y, x) ~l~> (y, unit) :=
  sorry
end updates_unital

-- section updates_unit

--   theorem unit_local_update (x y x' y' : Unit) : (x, y) ~l~> (x', y') :=
--   sorry
-- end updates_unit

-- section updates_discrete_fun

--   theorem discrete_fun_local_update {α : Type} {B : α → UCMRA}
--     (f g f' g' : ∀ x, B x) :
--     (∀ x : α, (f x, g x) ~l~> (f' x, g' x)) →
--     (f, g) ~l~> (f', g') :=
--   sorry
-- end updates_discrete_fun

-- section updates_product

--   theorem prod_local_update {α β : Type} [CMRA α] [CMRA β]
--     (x y x' y' : α × β) :
--     (x.1, y.1) ~l~> (x'.1, y'.1) →
--     (x.2, y.2) ~l~> (x'.2, y'.2) →
--     (x, y) ~l~> (x', y') :=
--   sorry

--   theorem prod_local_update' {α β : Type} [CMRA α] [CMRA β]
--     (x1 y1 x1' y1' : α) (x2 y2 x2' y2' : β) :
--     (x1, y1) ~l~> (x1', y1') →
--     (x2, y2) ~l~> (x2', y2') →
--     ((x1, x2), (y1, y2)) ~l~> ((x1', x2'), (y1', y2')) :=
--   sorry

--   theorem prod_local_update_1 {α β : Type} [CMRA α] [CMRA β]
--     (x1 y1 x1' y1' : α) (x2 y2 : β) :
--     (x1, y1) ~l~> (x1', y1') →
--     ((x1, x2), (y1, y2)) ~l~> ((x1', x2), (y1', y2)) :=
--   sorry

--   theorem prod_local_update_2 {α β : Type} [CMRA α] [CMRA β]
--     (x1 y1 : α) (x2 y2 x2' y2' : β) :
--     (x2, y2) ~l~> (x2', y2') →
--     ((x1, x2), (y1, y2)) ~l~> ((x1, x2'), (y1, y2')) :=
--   sorry
-- end updates_product

section updates_option
  theorem option_local_update {α : Type} [CMRA α]
    (x y x' y' : α) :
    (x, y) ~l~> (x', y') →
    (some x, some y) ~l~> (some x', some y') :=
  sorry

  theorem option_local_update_none {α : Type} [UCMRA α]
    (x x' y' : α) :
    (x, UCMRA.unit) ~l~> (x', y') →
    (some x, none) ~l~> (some x', some y') :=
  sorry

  theorem alloc_option_local_update {α : Type} [CMRA α] (x : α) (y : α) :
    ✓ x →
    (none, y) ~l~> (some x, some x) :=
  sorry

  theorem delete_option_local_update {α : Type} [CMRA α]
    (x : Option α) (y : α) [CMRA.Exclusive y] :
    (x, some y) ~l~> (none, none) :=
  sorry

  theorem delete_option_local_update_cancelable {α : Type} [CMRA α]
    (mx : Option α) [CMRA.Cancelable mx] :
    (mx, mx) ~l~> (none, none) :=
  sorry
end updates_option

end LocalUpdate
