/-
Copyright (c) 2025 Сухарик. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Сухарик (@suhr)
-/
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

  theorem local_update_id (x: α × α): x ~l~> x := fun _ _ vx e => ⟨vx, e⟩

  theorem local_update_left_eqv {x y: α × α} (z: α × α) (h: x ≡ y) : x ~l~> z → y ~l~> z :=
    fun u => fun n mw v e =>
      have e1: x.fst ≡{n}≡ y.fst := (OFE.equiv_fst h).dist
      have := calc
        x.fst       ≡{n}≡ y.fst       := e1
        y.fst       ≡{n}≡ y.snd •? mw := e
        y.snd •? mw ≡{n}≡ x.snd •? mw := CMRA.opM_left_dist mw (OFE.equiv_snd h).dist.symm
      u n mw ((OFE.Dist.validN e1.symm).mp v) this

  theorem local_update_right_eqv (x: α × α) {y z: α × α} (h: y ≡ z): x ~l~> y → x ~l~> z :=
    fun u => fun n mw v e =>
      let ⟨vy, e⟩ := u n mw v e
      have e1: y.fst ≡{n}≡ z.fst := OFE.dist_fst (OFE.Equiv.dist h)
      have := calc
        z.fst ≡{n}≡ y.fst := e1.symm
        _ ≡{n}≡ y.snd •? mw := e
        _ ≡{n}≡ z.snd •? mw := CMRA.opM_left_dist mw $ OFE.dist_snd (OFE.Equiv.dist h)
      ⟨(OFE.Dist.validN e1).mp vy, this⟩

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
        _ ≡{n}≡ y •? (some yf • mz) := CMRA.op_some_opM_assoc_dist y yf mz
      have u := h n (some yf • mz) vx this
      have := calc
        x' ≡{n}≡ y' •? (some yf • mz) := u.2
        _  ≡{n}≡ (y' • yf) •? mz      := (CMRA.op_some_opM_assoc_dist y' yf mz).symm
      ⟨u.1, this⟩

  theorem cancel_local_update (x y z : α) [CMRA.Cancelable x] : (x • y, x • z) ~l~> (y, z) :=
    fun _ _ vx e => ⟨CMRA.validN_op_right vx, CMRA.op_opM_cancel_dist vx e⟩

  theorem replace_local_update (x y : α) [CMRA.IdFree x] (h : ✓ y) : (x, x) ~l~> (y, y) :=
    fun _ mz vx e =>
      match mz with
      | none   => ⟨CMRA.Valid.validN h, OFE.Dist.symm (OFE.Dist.of_eq rfl)⟩
      | some _ => absurd e.symm (CMRA.id_freeN_r vx)

  theorem core_id_local_update (x y z : α) [CMRA.CoreId y] (inc : y ≼ x) : (x, z) ~l~> (x, z • y) :=
    fun n mz vx e =>
      have g: x ≡{n}≡ (z • y) •? mz :=
        suffices h: y • x ≡{n}≡ (z • y) •? mz
          from (CMRA.op_core_right_of_inc inc).symm.dist.trans h
        match mz with
        | none =>
          calc
            y • x ≡{n}≡ y • z := CMRA.op_right_dist y e
            _ ≡{n}≡ z • y := CMRA.op_commN
        | some w =>
          calc
            y • x ≡{n}≡ y • (z • w) := CMRA.op_right_dist y e
            _ ≡{n}≡ (y • z) • w := CMRA.op_assocN
            _ ≡{n}≡ (z • y) • w := CMRA.op_left_dist w (CMRA.op_commN)
      ⟨vx, g⟩

  theorem local_update_discrete [CMRA.Discrete α] (x y x' y' : α) :
      (x, y) ~l~> (x', y') ↔ ∀ mz, ✓ x → x ≡ y •? mz → (✓ x' ∧ x' ≡ y' •? mz) :=
    Iff.intro
      (fun h mz vx e =>
        have ⟨vx', e⟩ := h 0 mz vx.validN e.dist
        ⟨CMRA.Discrete.discrete_valid vx', OFE.discrete_0 e⟩)
      (fun h n mz vx e =>
        have ⟨vx', e'⟩ := h mz ((CMRA.valid_iff_validN' n).mpr vx) (OFE.discrete_n e)
        ⟨CMRA.Valid.validN vx', e'.dist⟩)

  theorem local_update_valid0 (x y x' y' : α)
      (h: ✓{0} x → ✓{0} y → some y ≼{0} some x → (x, y) ~l~> (x', y')) :
      (x, y) ~l~> (x', y') :=
    fun n mz vx e =>
      have v0y: ✓{0} y := CMRA.valid0_of_validN $ CMRA.validN_opM ((OFE.Dist.validN e).mp vx)
      have: some y ≼{0} some x := CMRA.inc0_of_incN (CMRA.some_inc_some_of_dist_opM e)
      have: (x, y) ~l~> (x', y') := h (CMRA.valid0_of_validN vx) v0y this
      this n mz vx e

  theorem local_update_valid [CMRA.Discrete α] (x y x' y' : α)
      (h: ✓ x → ✓ y → some y ≼ some x → (x, y) ~l~> (x', y')) : (x, y) ~l~> (x', y') :=
    have h0 vx0 vy0 mz: (x, y) ~l~> (x', y') :=
      h (CMRA.discrete_valid vx0) (CMRA.discrete_valid vy0) ((CMRA.inc_iff_incN 0).mpr mz)
    local_update_valid0 x y x' y' h0

  theorem local_update_total_valid0 [CMRA.IsTotal α] (x y x' y' : α)
      (h: ✓{0} x → ✓{0} y → y ≼{0} x → (x, y) ~l~> (x', y')) : (x, y) ~l~> (x', y') :=
    have h0 (vx0: ✓{0} x) (vy0: ✓{0} y) (mz : some y ≼{0} some x) : (x, y) ~l~> (x', y') :=
      h vx0 vy0 (CMRA.incN_of_some_incN_some mz)
    local_update_valid0 x y x' y' h0

  theorem local_update_total_valid [CMRA.IsTotal α] [CMRA.Discrete α] (x y x' y' : α)
      (h: ✓ x → ✓ y → y ≼ x → (x, y) ~l~> (x', y')) : (x, y) ~l~> (x', y') :=
    have hs vx vy inc : (x, y) ~l~> (x', y') := h vx vy (CMRA.inc_of_some_inc_some inc)
    local_update_valid x y x' y' hs
end CMRA

section updates_unital
  variable [UCMRA α]

  theorem local_update_unital (x y x' y' : α) :
      (x, y) ~l~> (x', y') ↔ ∀ n z, ✓{n} x → x ≡{n}≡ y • z → (✓{n} x' ∧ x' ≡{n}≡ y' • z) where
    mp  h n z       := h n (some z)
    mpr h n mz vx e :=
      match mz with
      | none =>
        have := h n UCMRA.unit vx (e.trans (CMRA.unit_right_id_dist y).symm)
        ⟨this.left, this.right.trans (CMRA.unit_right_id_dist y')⟩
      | some z => h n z vx e

  theorem local_update_unital_discrete [CMRA.Discrete α] (x y x' y' : α) :
      (x, y) ~l~> (x', y') ↔ ∀ z, ✓ x → x ≡ y • z → (✓ x' ∧ x' ≡ y' • z) where
    mp  h z vx e :=
      have ⟨vx', e'⟩ := h 0 (some z) (CMRA.Valid.validN vx) e.dist
      ⟨CMRA.discrete_valid vx', OFE.discrete_0 e'⟩
    mpr h :=
      have h' n z vnx e : (✓{n} x' ∧ x' ≡{n}≡ y' • z) :=
        have ⟨vx', e'⟩ := h z ((CMRA.valid_iff_validN' n).mpr vnx) (OFE.discrete_n e)
        ⟨CMRA.Valid.validN vx', OFE.Equiv.dist e'⟩
      (local_update_unital x y x' y').mpr h'

  theorem cancel_local_update_unit (x y : α) [CMRA.Cancelable x] :
      (x • y, x) ~l~> (y, UCMRA.unit) :=
    have e : (x • y, x • UCMRA.unit) ≡ (x • y, x) :=
      OFE.equiv_prod_ext OFE.Equiv.rfl (CMRA.unit_right_id)
    local_update_left_eqv _ e (cancel_local_update x y UCMRA.unit)

end updates_unital

section updates_unit

  theorem unit_local_update (x y x' y' : Unit) : (x, y) ~l~> (x', y') :=
    match x, y, x', y' with
    | .unit, .unit, .unit, .unit => local_update_id ((), ())

end updates_unit

section updates_discrete_fun

  theorem discrete_fun_local_update {α : Type} (β : α → Type _) [∀ x, UCMRA (β x)]
      (f g f' g' : ∀ x, β x) (h : ∀ x : α, (f x, g x) ~l~> (f' x, g' x))
      : (f, g) ~l~> (f', g') :=
    fun n mz vx e =>
      have g₁ : ✓{n} f' := fun x =>
        match mz with
        | .none => (h x n .none (vx x) (e x)).left
        | .some z => (h x n (.some (z x)) (vx x) (e x)).left
      have g₂ : f' ≡{n}≡ g' •? mz := fun x =>
        match mz with
        | .none => (h x n .none (vx x) (e x)).right
        | .some z => (h x n (.some (z x)) (vx x) (e x)).right
      ⟨g₁, g₂⟩

end updates_discrete_fun

section updates_product
  variable [CMRA α] [CMRA β]

  theorem prod_local_update
      {x y x' y' : α × β} (hl: (x.1, y.1) ~l~> (x'.1, y'.1)) (hr: (x.2, y.2) ~l~> (x'.2, y'.2))
      : (x, y) ~l~> (x', y') :=
    fun n mz vx e =>
      match mz with
      | .none =>
        have ⟨v₁, e₁⟩ := hl n .none vx.left e.left
        have ⟨v₂, e₂⟩ := hr n .none vx.right e.right
        ⟨⟨v₁, v₂⟩, ⟨e₁, e₂⟩⟩
      | .some z =>
        have ⟨v₁, e₁⟩ := hl n (.some z.fst) vx.left e.left
        have ⟨v₂, e₂⟩ := hr n (.some z.snd) vx.right e.right
        ⟨⟨v₁, v₂⟩, ⟨e₁, e₂⟩⟩

  theorem prod_local_update'
      {x1 y1 x1' y1' : α} {x2 y2 x2' y2' : β}
      (hl: (x1, y1) ~l~> (x1', y1')) (hr: (x2, y2) ~l~> (x2', y2'))
      : ((x1, x2), (y1, y2)) ~l~> ((x1', x2'), (y1', y2')) :=
    prod_local_update hl hr

  theorem prod_local_update_1
      (x1 y1 x1' y1' : α) (x2 y2 : β) (h: (x1, y1) ~l~> (x1', y1'))
      : ((x1, x2), (y1, y2)) ~l~> ((x1', x2), (y1', y2)) :=
    prod_local_update' h (local_update_id (x2, y2))

  theorem prod_local_update_2
      (x1 y1 : α) (x2 y2 x2' y2' : β) (h: (x2, y2) ~l~> (x2', y2'))
      : ((x1, x2), (y1, y2)) ~l~> ((x1, x2'), (y1, y2')) :=
    prod_local_update' (local_update_id (x1, y1)) h

end updates_product

section updates_option
  theorem option_local_update {α : Type} [CMRA α]
      {x y x' y' : α} (h: (x, y) ~l~> (x', y')) : (some x, some y) ~l~> (some x', some y') :=
    fun n mz vx e =>
      match mz with
      | .none           => h n .none vx e
      | .some .none     => have ⟨vx, e⟩ := h n .none vx e;  ⟨vx, e⟩
      | .some (.some z) => have ⟨vx, e⟩ := h n (.some z) vx e;  ⟨vx, e⟩

  theorem option_local_update_none {α : Type} [UCMRA α]
      {x x' y' : α} (h: (x, UCMRA.unit) ~l~> (x', y')): (some x, none) ~l~> (some x', some y') :=
    fun n mz vx e =>
      match mz with
      | .none           => False.elim e
      | .some .none     => False.elim e
      | .some (.some z) =>
        have e: x ≡{n}≡ z := e
        have ⟨vx, e⟩ := h n (.some z) vx (e.trans (CMRA.unit_left_id_dist z).symm)
        ⟨vx, e⟩

  theorem alloc_option_local_update {α : Type} [CMRA α]
      {x : α} (y : Option α) (vx: ✓ x): (none, y) ~l~> (some x, some x) :=
    fun n mz _ e =>
      match mz with
      | .none           => ⟨CMRA.Valid.validN vx, OFE.Dist.of_eq rfl⟩
      | .some .none     => ⟨CMRA.Valid.validN vx, OFE.Dist.of_eq rfl⟩
      | .some (.some z) =>
        have ⟨_, hw⟩ := CMRA.exists_op_some_dist_some (n := n) y z
        False.elim (e.trans hw)

  theorem delete_option_local_update {α : Type} [CMRA α]
      (x : Option α) (y : α) [CMRA.Exclusive y] :
      (x, some y) ~l~> (none, none) :=
    fun n mz vx e =>
      match mz with
      | .none           => ⟨True.intro, OFE.Dist.of_eq rfl⟩
      | .some .none     => ⟨True.intro, OFE.Dist.of_eq rfl⟩
      | .some (.some z) =>
        have : ✓{n} some y • some z := (OFE.Dist.validN e).mp vx
        absurd this not_valid_some_exclN_op_left

  theorem delete_option_local_update_cancelable {α : Type} [CMRA α]
      (mx : Option α) [CMRA.Cancelable mx] : (mx, mx) ~l~> (none, none) :=
    fun n mz vx e =>
      match mz with
      | .none           => ⟨True.intro, OFE.Dist.of_eq rfl⟩
      | .some .none     => ⟨True.intro, OFE.Dist.of_eq rfl⟩
      | .some (.some z) =>
        have : CMRA.unit ≡{n}≡ some z :=
          CMRA.cancelableN (validN_op_unit vx) ((CMRA.unit_right_id_dist mx).trans e)
        ⟨True.intro, this⟩

end updates_option

end LocalUpdate
