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
variable [CMRA α]

-- (* Global Instance cmra_updateP_proper :
--   Proper ((≡) ==> pointwise_relation _ iff ==> iff) (@cmra_updateP SI A).
-- Proof. Admitted. *)

-- (* Global Instance cmra_update_proper :
--   Proper ((≡) ==> (≡) ==> iff) (@cmra_update SI A).
-- Proof. Admitted. *)

theorem UpdateP.left_eqv {P : α → Prop} {x y: α} (e: x ≡ y) (u: x ~~>: P): y ~~>: P :=
  fun n mz v => u n mz (CMRA.validN_ne (CMRA.opM_left_dist mz e.symm.dist) v)

theorem Update.left_eqv {x y z: α} (e: x ≡ y) (u: x ~~> z): y ~~> z :=
  fun n mz v => u n mz (CMRA.validN_ne (CMRA.opM_left_dist mz e.symm.dist) v)

theorem Update.right_eqv {x y z: α} (e: y ≡ z) (u: x ~~> y): x ~~> z :=
  fun n mz v => CMRA.validN_ne (CMRA.opM_left_dist mz e.dist) (u n mz v)

instance [CMRA α] : Trans OFE.Equiv UpdateP UpdateP (α := α) where
  trans e u := UpdateP.left_eqv e.symm u

instance [CMRA α] : Trans OFE.Equiv Update Update (α := α) where
  trans e u := Update.left_eqv (id (OFE.Equiv.symm e)) u

instance [CMRA α] : Trans Update OFE.Equiv Update (α := α) where
  trans u e := Update.right_eqv e u


theorem Update.of_updateP {x y: α} (h: x ~~>: (y = ·)): x ~~> y :=
  fun n mz v => let ⟨_, e, v⟩ := (h n mz v);  e ▸ v

theorem UpdateP.of_update {x y: α} (h: x ~~> y): x ~~>: (y = ·) :=
  fun n mz v => ⟨y, rfl, h n mz v⟩

theorem UpdateP.id (P : α → Prop) x (h: P x): x ~~>: P :=
  fun _ _ v => ⟨x, h, v⟩

theorem Update.id (x : α): x ~~> x := fun _ _ h => h

theorem Update.trans {x y z: α} (uxy: x ~~> y) (uyz: y ~~> z) : x ~~> z :=
  fun n mz v => uyz n mz (uxy n mz v)

theorem UpdateP.trans (P Q : α → Prop) x (ux: x ~~>: P) (upq : ∀ y, P y → y ~~>: Q)
    : x ~~>: Q :=
  fun n mz v => let ⟨y, py, vy⟩ := ux n mz v;  upq y py n mz vy

theorem Update.transP {Q : α → Prop} {x y} (uxy: x ~~> y) (uyq: y ~~>: Q) : x ~~>: Q :=
  fun n mz v => uyq n mz (uxy n mz v)

theorem UpdateP.weaken (P Q : α → Prop) x (uxp: x ~~>: P) (pq: ∀ y, P y → Q y)
    : x ~~>: Q :=
  fun n mz v => let ⟨y, py, vy⟩ := uxp n mz v;  ⟨y, pq y py, vy⟩

theorem Update.exclusive {x y: α} [CMRA.Exclusive x] (vy: ✓ y): x ~~> y :=
  fun _ _ P => (CMRA.none_of_excl_valid_op P) ▸ CMRA.Valid.validN vy

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
    (uxp: x ~~>: P) (uyq: y ~~>: Q) (pqr: ∀z w, P z → Q w → R (z • w))
    : x • y ~~>: R :=
  fun n mz v =>
    have e₁: (x • y) •? mz ≡{n}≡ y •? some (x •? mz) :=
      (CMRA.opM_left_dist mz CMRA.op_commN).trans (CMRA.op_opM_assoc_dist _ _ mz)
    let ⟨w, pw, vw⟩ := uyq n (some (x •? mz)) (CMRA.validN_ne e₁ v)
    have e₂: w •? some (x •? mz) ≡{n}≡ x •? some (w •? mz) := calc
      w •? some (x •? mz) ≡{n}≡ (w • x) •? mz       := (CMRA.op_opM_assoc_dist w x mz).symm
      _                   ≡{n}≡ (x • w) •? mz       := (CMRA.opM_left_dist mz CMRA.op_commN)
      _                   ≡{n}≡ x •? some (w •? mz) := CMRA.op_opM_assoc_dist x w mz
    let ⟨z, pz, vz⟩ := uxp n (some (w •? mz)) (CMRA.validN_ne e₂ vw)
    ⟨z • w, pqr z w pz pw, CMRA.validN_ne (CMRA.op_opM_assoc_dist z w mz).symm vz⟩

theorem UpdateP.op' {P Q : α → Prop} {x y: α} (uxp: x ~~>: P) (uyq: y ~~>: Q)
    : x • y ~~>: λ t ↦ ∃ z w, t = z • w ∧ P z ∧ Q w :=
  UpdateP.op uxp uyq (fun z w pz qw => ⟨z, w, rfl, pz, qw⟩)

theorem Update.op {x₁ x₂ y₁ y₂ : α} (xy₁: x₁ ~~> y₁) (xy₂: x₂ ~~> y₂)
    : x₁ • x₂ ~~> y₁ • y₂ :=
  Update.of_updateP $
    UpdateP.op (UpdateP.of_update xy₁) (UpdateP.of_update xy₂)
      fun _ _ ez ew => ez ▸ ew ▸ rfl

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


theorem Update.op_l (x y : α) : x • y ~~> x := fun _ _ => CMRA.validN_op_opM_left

theorem Update.op_r (x y : α) : x • y ~~> y := fun _ _ => CMRA.validN_op_opM_right

theorem Update.included (x y : α) : x ≼ y → y ~~> x :=
  fun ⟨z, ez⟩ => Update.left_eqv ez.symm (Update.op_l x z)

theorem Update.valid0 (x y : α) : (✓{0} x → x ~~> y) → x ~~> y :=
  fun h n mz v => h (CMRA.valid0_of_validN (CMRA.validN_opM v)) n mz v

-- Frame preserving updates for total and discete CMRAs

theorem total_updateP [CMRA.IsTotal α] (x : α) (P : α → Prop)
    : x ~~>: P ↔ ∀ (n : Nat) (z : α), ✓{n} (x • z) → ∃ y, P y ∧ ✓{n} (y • z) where
  mp uxp := fun n z v => uxp n (some z) v
  mpr h := fun n mz v =>
    match mz with
    | .none =>
      let ⟨y, py, vy⟩ := h n (CMRA.core x) (CMRA.validN_ne (CMRA.op_core_dist x).symm v)
      ⟨y, py, CMRA.validN_op_opM_left vy⟩
    | .some z => h n z v

theorem total_update [CMRA.IsTotal α] (x y : α)
    : x ~~> y ↔ ∀ (n : Nat) (z : α), ✓{n} (x • z) → ✓{n} (y • z) where
  mp uxy := fun n z v => uxy n (some z) v
  mpr h := fun n mz v =>
    match mz with
    | .none =>
      CMRA.validN_op_opM_left $ h n (CMRA.core x) (CMRA.validN_ne (CMRA.op_core_dist x).symm v)
    | .some z => h n z v


theorem discrete_updateP [CMRA.Discrete α] (x : α) (P : α → Prop)
    : x ~~>: P ↔ ∀ (mz : Option α), ✓ (x •? mz) → ∃ y, P y ∧ ✓ (y •? mz) where
  mp uxp := fun mz v =>
    let ⟨y, py, vy⟩ := uxp 0 mz (CMRA.Valid.validN v)
    ⟨y, py, CMRA.discrete_valid vy⟩
  mpr h := fun n mz v =>
    let ⟨y, py, vy⟩ := h mz ((CMRA.valid_iff_validN' n).mpr v)
    ⟨y, py, CMRA.Valid.validN vy⟩

theorem discrete_update [CMRA.Discrete α] (x y : α)
    : x ~~> y ↔ ∀ (mz : Option α), ✓ (x •? mz) → ✓ (y •? mz) where
  mp uxp := fun mz v => CMRA.discrete_valid $ uxp 0 mz (CMRA.Valid.validN v)
  mpr h := fun n mz v => CMRA.Valid.validN $ h mz ((CMRA.valid_iff_validN' n).mpr v)

theorem discrete_total_updateP [CMRA.Discrete α] [CMRA.IsTotal α] (x : α) (P : α → Prop)
    : x ~~>: P ↔ ∀ (z : α), ✓ (x • z) → ∃ y, P y ∧ ✓ (y • z) where
  mp uxp := fun z vz =>
    let ⟨y, py, vy⟩ := (total_updateP x P).mp uxp 0 z (CMRA.Valid.validN vz)
    ⟨y, py, CMRA.discrete_valid vy⟩
  mpr h :=
    have this n z (v: ✓{n} x • z): ∃ y, P y ∧ ✓{n} (y • z) :=
      let ⟨y, py, vy⟩ := h z ((CMRA.valid_iff_validN' n).mpr v)
      ⟨y, py, CMRA.Valid.validN vy⟩
    (total_updateP x P).mpr this

theorem discrete_total_update [CMRA.Discrete α] [CMRA.IsTotal α] (x y : α)
    : x ~~> y ↔ ∀ (z : α), ✓ (x • z) → ✓ (y • z) where
  mp uxp := fun z vz =>
    CMRA.discrete_valid $ (total_update x y).mp uxp 0 z (CMRA.Valid.validN vz)
  mpr h :=
    have this n z (v: ✓{n} x • z): ✓{n} (y • z) :=
      CMRA.Valid.validN $ h z ((CMRA.valid_iff_validN' n).mpr v)
    (total_update x y).mpr this

end updates

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

-- Isomorphism
section iso_cmra
  variable [CMRA α] [CMRA β] (f : α → β) (g : β → α)

  theorem iso_updateP {P : β → Prop} {Q : α → Prop} {y : β}
      (gf : ∀ x, g (f x) ≡ x)
      (g_op : ∀ y1 y2, g (y1 • y2) ≡ g y1 • g y2)
      (g_validN : ∀ n y, ✓{n} (g y) ↔ ✓{n} y)
      (uyp: y ~~>: P)
      (pq: ∀ y', P y' → Q (g y'))
      : g y ~~>: Q :=
    fun n mz v =>
      have : ✓{n} y •? Option.map f mz :=
        match mz with
        | .none => (g_validN n _).mp v
        | .some z =>
          have : g y • z ≡ g (y • f z) :=
            (CMRA.op_right_eqv _ (gf z).symm).trans (g_op y (f z)).symm
          (g_validN n _).mp (CMRA.validN_ne this.dist v)
      have ⟨x, px, vx⟩ := uyp n (mz.map f) this
      have : g (x •? Option.map f mz) ≡ g x •? mz :=
        match mz with
        | .none => OFE.Equiv.rfl
        | .some z => (g_op x (f z)).trans (CMRA.op_right_eqv (g x) (gf z))
      ⟨g x, pq x px, CMRA.validN_ne this.dist ((g_validN n _).mpr vx)⟩

  theorem iso_updateP' (P : β → Prop) (y : β)
      (gf : ∀ x, g (f x) ≡ x)
      (g_op : ∀ y1 y2, g (y1 • y2) ≡ g y1 • g y2)
      (g_validN : ∀ n y, ✓{n} (g y) ↔ ✓{n} y)
      (uyp: y ~~>: P)
      : g y ~~>: λ x ↦ ∃ y, x = g y ∧ P y :=
    iso_updateP f g gf g_op g_validN uyp (fun z pz => ⟨z, rfl, pz⟩)

end iso_cmra

section update_lift_cmra
  variable  [CMRA α] [CMRA β]

  theorem Update.lift_updateP (f : β → α) (x : β) (y : β)
    (H : ∀ P, x ~~>: P → f x ~~>: λ a' ↦ ∃ b', a' = f b' ∧ P b')
    (uxy: x ~~> y)
    : f x ~~> f y :=
  Update.of_updateP fun n mz v =>
    have ⟨z, hz, vz⟩ := H _ (UpdateP.of_update uxy) n mz v
    have hz : z = f y := by simp at hz ⊢; exact hz
    ⟨z, hz.symm, vz⟩

end update_lift_cmra

section prod
  variable [CMRA α] [CMRA β]

  theorem prod_updateP {P : α → Prop} {Q : β → Prop} {R : α × β → Prop} {x : α × β}
      (uxp: x.fst ~~>: P) (uxq: x.snd ~~>: Q) (pq: ∀ a b, P a → Q b → R (a, b))
      : x ~~>: R :=
    fun n mz v =>
      match mz with
      | .none =>
        have ⟨y₁, py, vy₁⟩ := uxp n .none (Prod.validN_fst v)
        have ⟨y₂, qy, vy₂⟩ := uxq n .none (Prod.validN_snd v)
        ⟨(y₁, y₂), pq y₁ y₂ py qy, ⟨vy₁, vy₂⟩⟩
      | .some z =>
        have ⟨y₁, py, vy₁⟩ := uxp n (.some z.fst) (Prod.validN_fst v)
        have ⟨y₂, qy, vy₂⟩ := uxq n (.some z.snd) (Prod.validN_snd v)
        ⟨(y₁, y₂), pq y₁ y₂ py qy, ⟨vy₁, vy₂⟩⟩

  theorem prod_updateP' (P : α → Prop) (Q : β → Prop) (x : α × β)
     (uxp: x.fst ~~>: P) (uxq: x.snd ~~>: Q) : x ~~>: λ y ↦ P (y.fst) ∧ Q (y.snd) :=
    prod_updateP uxp uxq (fun _ _ px qy => ⟨px, qy⟩)

  theorem prod_update (x : α × β) (uxy₁: x.fst ~~> y.fst) (uxy₂: x.snd ~~> y.snd) : x ~~> y :=
    Update.of_updateP $
      prod_updateP (UpdateP.of_update uxy₁) (UpdateP.of_update uxy₂)
        (fun _ _ ya yb => Prod.ext ya yb)

end prod

section option
  variable [CMRA α]

  theorem option_updateP {P : α → Prop} {Q : Option α → Prop} {x : α}
      (uxp: x ~~>: P) (pq: ∀ y, P y → Q (some y)) : some x ~~>: Q :=
    fun n mz v =>
      match mz with
      | .none           => let ⟨w, pw, vw⟩ := uxp n .none v;  ⟨w, pq w pw, vw⟩
      | .some .none     => let ⟨w, pw, vw⟩ := uxp n .none v;  ⟨w, pq w pw, vw⟩
      | .some (.some z) => let ⟨w, pw, vw⟩ := uxp n (.some z) v;  ⟨w, pq w pw, vw⟩

  theorem option_updateP' (P : α → Prop) (x : α) (uxp: x ~~>: P)
      : some x ~~>: Option.rec False P :=
    option_updateP uxp (fun _ py => py)

  theorem option_update (x y : α) (uxy: x ~~> y): some x ~~> some y :=
    Update.of_updateP $
      option_updateP (UpdateP.of_update uxy) (fun _ => congrArg some)

end option
