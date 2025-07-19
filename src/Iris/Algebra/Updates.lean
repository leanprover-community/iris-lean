/-
Copyright (c) 2025 Сухарик. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Сухарик (@suhr)
-/
import Iris.Algebra.CMRA

namespace Iris

def UpdateP [CMRA α] (x : α) (P : α → Prop) := ∀ n mz,
  ✓{n} (x •? mz) → ∃ y, P y ∧ ✓{n} (y •? mz)
infixr:50 " ~~>: " => UpdateP

def Update [CMRA α] (x y : α) := ∀ n mz,
  ✓{n} (x •? mz) → ✓{n} (y •? mz)
infixr:50 " ~~> " => Update

section updates

variable [CMRA α] [CMRA β] (f : α → β) (g : β → α)

-- (* Global Instance cmra_updateP_proper :
--   Proper ((≡) ==> pointwise_relation _ iff ==> iff) (@cmra_updateP SI A).
-- Proof. Admitted. *)

-- (* Global Instance cmra_update_proper :
--   Proper ((≡) ==> (≡) ==> iff) (@cmra_update SI A).
-- Proof. Admitted. *)

theorem UpdateP.equiv_left {P : α → Prop} {x y : α} (e : x ≡ y) (u : x ~~>: P) : y ~~>: P :=
  fun n mz v => u n mz (CMRA.validN_ne (CMRA.opM_left_dist mz e.symm.dist) v)

theorem Update.equiv_left {x y z : α} (e : x ≡ y) (u : x ~~> z) : y ~~> z :=
  fun n mz v => u n mz (CMRA.validN_ne (CMRA.opM_left_dist mz e.symm.dist) v)

theorem Update.equiv_right {x y z : α} (e : y ≡ z) (u : x ~~> y) : x ~~> z :=
  fun n mz v => CMRA.validN_ne (CMRA.opM_left_dist mz e.dist) (u n mz v)

instance [CMRA α] : Trans OFE.Equiv UpdateP UpdateP (α := α) where
  trans e u := UpdateP.equiv_left e.symm u

instance [CMRA α] : Trans OFE.Equiv Update Update (α := α) where
  trans e u := Update.equiv_left (id (OFE.Equiv.symm e)) u

instance [CMRA α] : Trans Update OFE.Equiv Update (α := α) where
  trans u e := Update.equiv_right e u

theorem Update.of_updateP {x y : α} (h : x ~~>: (y = ·)) : x ~~> y :=
  fun n mz v => let ⟨_, e, v⟩ := (h n mz v); e ▸ v

theorem UpdateP.of_update {x y : α} (h : x ~~> y) : x ~~>: (y = ·) :=
  fun n mz v => ⟨y, rfl, h n mz v⟩

theorem UpdateP.id {P : α → Prop} {x} (h : P x) : x ~~>: P :=
  fun _ _ v => ⟨x, h, v⟩

theorem Update.id {x : α} : x ~~> x := fun _ _ h => h

theorem Update.trans {x y z : α} (uxy : x ~~> y) (uyz : y ~~> z) : x ~~> z :=
  fun n mz v => uyz n mz (uxy n mz v)

theorem UpdateP.trans {x : α} (ux : x ~~>: P) (upq : ∀ y, P y → y ~~>: Q) : x ~~>: Q :=
  fun n mz v => let ⟨y, py, vy⟩ := ux n mz v; upq y py n mz vy

theorem Update.transP {x y : α} (uxy : x ~~> y) (uyq : y ~~>: Q) : x ~~>: Q :=
  fun n mz v => uyq n mz (uxy n mz v)

theorem UpdateP.weaken {x : α} (uxp : x ~~>: P) (pq : ∀ y, P y → Q y) : x ~~>: Q :=
  fun n mz v => let ⟨y, py, vy⟩ := uxp n mz v; ⟨y, pq y py, vy⟩

theorem Update.exclusive {x y : α} [CMRA.Exclusive x] (vy : ✓ y) : x ~~> y :=
  fun _ _ P => CMRA.none_of_excl_valid_op P ▸ vy.validN

instance [CMRA α] : Trans Update Update Update (α := α) where
  trans := Update.trans

instance [CMRA α] : Trans Update UpdateP UpdateP (α := α) where
  trans := Update.transP

-- (** Updates form a preorder. *)
-- (** We set this rewrite relation's cost above the stdlib's
--   ([impl], [iff], [eq], ...) and [≡] but below [⊑].
--   [eq] (at 100) < [≡] (at 150) < [cmra_update] (at 170) < [⊑] (at 200) *)

-- (* Global Instance cmra_update_rewrite_relation :
--   RewriteRelation (@cmra_update SI A) | 170 := {}. *)

-- (* Global Instance cmra_update_preorder : PreOrder (@cmra_update SI A).
-- Proof. Admitted. *)

-- (* Global Instance cmra_update_proper_update :
--   Proper (flip cmra_update ==> cmra_update ==> impl) (@cmra_update SI A).
-- Proof. Admitted. *)

-- (* Global Instance cmra_update_flip_proper_update :
--   Proper (cmra_update ==> flip cmra_update ==> flip impl) (@cmra_update SI A).
-- Proof. Admitted. *)

theorem UpdateP.op {P Q R : α → Prop} {x y}
    (uxp : x ~~>: P) (uyq : y ~~>: Q) (pqr : ∀z w, P z → Q w → R (z • w)) : x • y ~~>: R := by
  intro n mz v
  have e₁ : (x • y) •? mz ≡{n}≡ y •? some (x •? mz) :=
    (CMRA.opM_left_dist mz CMRA.op_commN).trans (CMRA.op_opM_assoc_dist _ _ mz)
  let ⟨w, pw, vw⟩ := uyq n (some (x •? mz)) (CMRA.validN_ne e₁ v)
  have e₂ : w •? some (x •? mz) ≡{n}≡ x •? some (w •? mz) := calc
    w •? some (x •? mz) ≡{n}≡ (w • x) •? mz       := (CMRA.op_opM_assoc_dist w x mz).symm
    _                   ≡{n}≡ (x • w) •? mz       := (CMRA.opM_left_dist mz CMRA.op_commN)
    _                   ≡{n}≡ x •? some (w •? mz) := CMRA.op_opM_assoc_dist x w mz
  let ⟨z, pz, vz⟩ := uxp n (some (w •? mz)) (CMRA.validN_ne e₂ vw)
  exact ⟨z • w, pqr z w pz pw, CMRA.validN_ne (CMRA.op_opM_assoc_dist z w mz).symm vz⟩

theorem UpdateP.op' {P Q : α → Prop} {x y : α} (uxp : x ~~>: P) (uyq : y ~~>: Q) :
    (x • y : α) ~~>: λ t ↦ ∃ z w, t = (z • w : α) ∧ P z ∧ Q w :=
  .op uxp uyq fun z w pz qw => ⟨z, w, rfl, pz, qw⟩

theorem Update.op {x₁ x₂ y₁ y₂ : α} (xy₁ : x₁ ~~> y₁) (xy₂ : x₂ ~~> y₂) : x₁ • x₂ ~~> y₁ • y₂ :=
  .of_updateP <| .op (.of_update xy₁) (.of_update xy₂) fun _ _ ez ew => ez ▸ ew ▸ rfl

-- (* Global Instance cmra_update_op_proper :
--   Proper (cmra_update ==> cmra_update ==> cmra_update) (op (A:=A)).
-- Proof. Admitted. *)

-- (* Global Instance cmra_update_op_flip_proper :
--   Proper (flip cmra_update ==> flip cmra_update ==> flip cmra_update) (op (A:=A)).
-- Proof. Admitted. *)

-- (* Global Instance cmra_update_op_proper :
--   Proper (cmra_update ==> cmra_update ==> cmra_update) (op (A:=A)).
-- Proof. Admitted. *)

-- (* Global Instance cmra_update_op_flip_proper :
--   Proper (flip cmra_update ==> flip cmra_update ==> flip cmra_update) (op (A:=A)).
-- Proof. Admitted. *)

theorem Update.op_l {x y : α} : x • y ~~> x := fun _ _ => CMRA.validN_op_opM_left

theorem Update.op_r {x y : α} : x • y ~~> y := fun _ _ => CMRA.validN_op_opM_right

theorem Update.included {x y : α} : x ≼ y → y ~~> x := fun ⟨_, ez⟩ => .equiv_left ez.symm .op_l

theorem Update.valid0 {x y : α} : (✓{0} x → x ~~> y) → x ~~> y :=
  fun h n mz v => h (CMRA.valid0_of_validN (CMRA.validN_opM v)) n mz v

/-! ## Frame preserving updates for total and discete CMRAs -/

theorem UpdateP.total [CMRA.IsTotal α] :
    x ~~>: P ↔ ∀ (n : Nat) (z : α), ✓{n} (x • z) → ∃ y, P y ∧ ✓{n} (y • z) where
  mp uxp := fun n z v => uxp n (some z) v
  mpr h := fun n mz v =>
    match mz with
    | none =>
      let ⟨y, py, vy⟩ := h n (CMRA.core x) (CMRA.validN_ne (CMRA.op_core_dist x).symm v)
      ⟨y, py, CMRA.validN_op_opM_left vy⟩
    | some z => h n z v

theorem Update.total [CMRA.IsTotal α] :
    x ~~> y ↔ ∀ (n : Nat) (z : α), ✓{n} (x • z) → ✓{n} (y • z) where
  mp uxy := fun n z v => uxy n (some z) v
  mpr h := fun n mz v =>
    match mz with
    | none =>
      CMRA.validN_op_opM_left $ h n (CMRA.core x) (CMRA.validN_ne (CMRA.op_core_dist x).symm v)
    | some z => h n z v

theorem UpdateP.discrete [CMRA.Discrete α] :
    x ~~>: P ↔ ∀ (mz : Option α), ✓ (x •? mz) → ∃ y, P y ∧ ✓ (y •? mz) where
  mp uxp := fun mz v =>
    let ⟨y, py, vy⟩ := uxp 0 mz (CMRA.Valid.validN v)
    ⟨y, py, CMRA.discrete_valid vy⟩
  mpr h := fun n mz v =>
    let ⟨y, py, vy⟩ := h mz ((CMRA.valid_iff_validN' n).mpr v)
    ⟨y, py, CMRA.Valid.validN vy⟩

theorem Update.discrete [CMRA.Discrete α] {x y : α} :
    x ~~> y ↔ ∀ (mz : Option α), ✓ (x •? mz) → ✓ (y •? mz) where
  mp uxp := fun mz v => CMRA.discrete_valid $ uxp 0 mz (CMRA.Valid.validN v)
  mpr h := fun n mz v => CMRA.Valid.validN $ h mz ((CMRA.valid_iff_validN' n).mpr v)

theorem UpdateP.discrete_total [CMRA.Discrete α] [CMRA.IsTotal α] :
    x ~~>: P ↔ ∀ (z : α), ✓ (x • z) → ∃ y, P y ∧ ✓ (y • z) where
  mp uxp := fun z vz =>
    let ⟨y, py, vy⟩ := UpdateP.total.mp uxp 0 z (CMRA.Valid.validN vz)
    ⟨y, py, CMRA.discrete_valid vy⟩
  mpr h :=
    UpdateP.total.mpr fun n z v =>
      let ⟨y, py, vy⟩ := h z ((CMRA.valid_iff_validN' n).mpr v)
      ⟨y, py, CMRA.Valid.validN vy⟩

theorem Update.discrete_total [CMRA.Discrete α] [CMRA.IsTotal α] :
    x ~~> y ↔ ∀ (z : α), ✓ (x • z) → ✓ (y • z) where
  mp uxp := fun z vz =>
    CMRA.discrete_valid $ Update.total.mp uxp 0 z (CMRA.Valid.validN vz)
  mpr h := Update.total.mpr fun n z v => (h z ((CMRA.valid_iff_validN' n).mpr v)).validN

-- (** * Transport *)
-- Section cmra_transport.
--   Context {SI : sidx} {A B : cmra} (H : A = B).
--   Notation T := (cmra_transport H).
--   Lemma cmra_transport_updateP (P : A → Prop) (Q : B → Prop) x :
--     x ~~>: P → (∀ y, P y → Q (T y)) → T x ~~>: Q.
--   Proof. Admitted.

--   Lemma cmra_transport_updateP' (P : A → Prop) x :
--     x ~~>: P → T x ~~>: λ y, ∃ y', y = cmra_transport H y' ∧ P y'.
--   Proof. Admitted.

-- End cmra_transport.

/-! ## Isomorphism -/
theorem UpdateP.iso
    (gf : ∀ x, g (f x) ≡ x)
    (g_op : ∀ y1 y2, g (y1 • y2) ≡ g y1 • g y2)
    (g_validN : ∀ n y, ✓{n} (g y) ↔ ✓{n} y)
    (uyp : y ~~>: P)
    (pq : ∀ y', P y' → Q (g y')) :
    g y ~~>: Q := by
  intro n mz v
  have : ✓{n} y •? Option.map f mz :=
    match mz with
    | none => (g_validN n _).mp v
    | some z =>
      have : g y • z ≡ g (y • f z) :=
        (CMRA.op_right_eqv _ (gf z).symm).trans (g_op y (f z)).symm
      (g_validN n _).mp (CMRA.validN_ne this.dist v)
  have ⟨x, px, vx⟩ := uyp n (mz.map f) this
  have : g (x •? Option.map f mz) ≡ g x •? mz :=
    match mz with
    | none => OFE.Equiv.rfl
    | some z => (g_op x (f z)).trans (CMRA.op_right_eqv (g x) (gf z))
  exact ⟨g x, pq x px, CMRA.validN_ne this.dist ((g_validN n _).mpr vx)⟩

theorem UpdateP.iso'
    (gf : ∀ x, g (f x) ≡ x)
    (g_op : ∀ y1 y2, g (y1 • y2) ≡ g y1 • g y2)
    (g_validN : ∀ n y, ✓{n} (g y) ↔ ✓{n} y)
    (uyp : y ~~>: P) :
    g y ~~>: λ x ↦ ∃ y, x = g y ∧ P y :=
  .iso f g gf g_op g_validN uyp fun z pz => ⟨z, rfl, pz⟩

/-! ## Lift -/
theorem Update.lift_updateP (x y : β)
    (H : ∀ P, x ~~>: P → g x ~~>: λ a' ↦ ∃ b', a' = g b' ∧ P b')
    (uxy : x ~~> y) : g x ~~> g y :=
  .of_updateP fun n mz v =>
    have ⟨z, hz, vz⟩ := H _ (.of_update uxy) n mz v
    have hz : z = g y := by simp at hz ⊢; exact hz
    ⟨z, hz.symm, vz⟩

/-! ## Product -/
theorem UpdateP.prod {P : α → Prop} {Q : β → Prop} {R : α × β → Prop} {x : α × β}
    (uxp : x.fst ~~>: P) (uxq : x.snd ~~>: Q) (pq : ∀ a b, P a → Q b → R (a, b)) :
    x ~~>: R := by
  intro n mz v
  match mz with
  | none =>
    have ⟨y₁, py, vy₁⟩ := uxp n none v.1
    have ⟨y₂, qy, vy₂⟩ := uxq n none v.2
    exact ⟨(y₁, y₂), pq y₁ y₂ py qy, ⟨vy₁, vy₂⟩⟩
  | some z =>
    have ⟨y₁, py, vy₁⟩ := uxp n (some z.fst) v.1
    have ⟨y₂, qy, vy₂⟩ := uxq n (some z.snd) v.2
    exact ⟨(y₁, y₂), pq y₁ y₂ py qy, ⟨vy₁, vy₂⟩⟩

theorem UpdateP.prod' (P : α → Prop) (Q : β → Prop) (x : α × β)
    (uxp : x.fst ~~>: P) (uxq : x.snd ~~>: Q) : x ~~>: λ y ↦ P (y.fst) ∧ Q (y.snd) :=
  .prod uxp uxq fun _ _ px qy => ⟨px, qy⟩

theorem Update.prod (x : α × β) (uxy₁ : x.fst ~~> y.fst) (uxy₂ : x.snd ~~> y.snd) : x ~~> y :=
  .of_updateP <| .prod (.of_update uxy₁) (.of_update uxy₂) fun _ _ ya yb => Prod.ext ya yb

/-! ## Option -/
theorem UpdateP.option {P : α → Prop} {Q : Option α → Prop} {x : α}
    (uxp : x ~~>: P) (pq : ∀ y, P y → Q (some y)) : some x ~~>: Q := by
  intro n mz v
  match mz with
  | none | some none => let ⟨w, pw, vw⟩ := uxp n none v; exact ⟨w, pq w pw, vw⟩
  | some (some z) => let ⟨w, pw, vw⟩ := uxp n (some z) v; exact ⟨w, pq w pw, vw⟩

theorem UpdateP.option' (P : α → Prop) (x : α) (uxp : x ~~>: P) : some x ~~>: Option.rec False P :=
  .option uxp fun _ py => py

theorem Update.option (x y : α) (uxy : x ~~> y) : some x ~~> some y :=
  .of_updateP <| .option (.of_update uxy) fun _ => congrArg some
