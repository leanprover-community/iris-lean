/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.OFE

/-! # Approximations

The domain behind guarded fixpoints. An `Approx α` is a ball of `α`: everything that agrees with a
point at a downward-closed set of step-indices. Ordered by inclusion (smaller balls are more
precise), approximations form a `CCPO`, so `partial_fixpoint` can define them by recursion.

`lift G` runs `G` on every point of an approximation. It is monotone for every `G`, and when `G` is
contractive, its fixpoint is exact: `get` of it is the fixpoint of `G` (`lift_fix_get`).

This is a variant of the domain of formal balls of Edalat and Heckmann, "A computational model for
metric spaces" (TCS 193, 1998). -/

@[expose] public section

namespace Iris
open OFE Lean.Order

namespace Approx
variable {α : Type _} [OFE α] -- TODO: This file must be generalized based on the step index changes.

/-- The ball around `c` determined by the set of levels `P`. -/
def ball (c : α) (P : Nat → Prop) : α → Prop := fun y => ∀ m, P m → c ≡{m}≡ y

/-- Levels at which all elements of `S` agree. -/
def prec (S : α → Prop) (m : Nat) : Prop := ∀ a b, S a → S b → a ≡{m}≡ b

/-- `S` is a ball. -/
def IsApprox (S : α → Prop) : Prop := ∃ c P, S = ball c P

end Approx

/-- Approximations of an element: a ball, of finite precision or a singleton. -/
def Approx (α : Type _) [OFE α] := {S : α → Prop // Approx.IsApprox S}

namespace Approx
variable {α : Type _} [OFE α]

/-! ## Approximations form a CCPO -/

instance : PartialOrder (Approx α) where
  rel S T := ∀ y, T.1 y → S.1 y
  rel_refl := fun _ h => h
  rel_trans h1 h2 := fun y h => h1 y (h2 y h)
  rel_antisymm h1 h2 := Subtype.ext (funext fun y => propext ⟨h2 y, h1 y⟩)

theorem ball_self (c : α) (P) : ball c P c := fun _ _ => .rfl

theorem IsApprox.nonempty {S : α → Prop} (h : IsApprox S) : ∃ a, S a :=
  let ⟨c, P, e⟩ := h
  ⟨c, e ▸ ball_self c P⟩

theorem prec_mono {S : α → Prop} {m n} (h : prec S n) (hmn : m ≤ n) : prec S m :=
  fun a b ha hb => (h a b ha hb).le hmn

/-- Every approximation is the ball around any of its elements, at its own precision. -/
theorem IsApprox.eq_ball {S : α → Prop} (h : IsApprox S) {a} (ha : S a) : S = ball a (prec S) := by
  obtain ⟨c, P, rfl⟩ := h
  have hP {m} (hm : P m) : prec (ball c P) m := fun _ _ hx hy => (hx m hm).symm.trans (hy m hm)
  funext y
  exact propext ⟨fun hy m hm => hm a y ha hy,
    fun hy m hm => (hP hm c a (ball_self c P) ha).trans (hy m (hP hm))⟩

/-- A point of an approximation. -/
noncomputable def get (S : Approx α) : α := Classical.choose S.2.nonempty

theorem get_mem (S : Approx α) : S.1 (get S) := Classical.choose_spec S.2.nonempty

/-- Two points of a chain's elements agree at any level both elements are precise at. -/
theorem chain_dist {c : Approx α → Prop} (hc : chain c) {S T : Approx α} (hS : c S) (hT : c T)
    {a b : α} (ha : S.1 a) (hb : T.1 b) {m} (hSm : prec S.1 m) (hTm : prec T.1 m) : a ≡{m}≡ b :=
  (hc S T hS hT).elim (fun h => hSm a b ha (h b hb)) (fun h => hTm a b (h a ha) hb)

/-- The intersection of a chain: its sup. -/
def inter (c : Approx α → Prop) : α → Prop := fun y => ∀ S, c S → S.1 y

/-- The levels at which some element of `c` is precise. -/
def precs (c : Approx α → Prop) (m : Nat) : Prop := ∃ S, c S ∧ prec S.1 m

/-- If `x` is in every element of `c`, their intersection is the ball around `x` at the levels
some element is precise at. -/
theorem inter_eq_ball {c : Approx α → Prop} {x : α} (hx : ∀ S, c S → S.1 x) :
    inter c = ball x (precs c) := by
  funext y
  refine propext ⟨fun hy m ⟨S, hS, hm⟩ => hm x y (hx S hS) (hy S hS), fun hy S hS => ?_⟩
  rw [S.2.eq_ball (hx S hS)]
  exact fun m hm => hy m ⟨S, hS, hm⟩

/-- A downward-closed set of levels other than all of them is the set of levels below some `K`. -/
theorem exists_bound {P : Nat → Prop} (hP : ∀ {m n}, m ≤ n → P n → P m) {k} (hk : ¬ P k) :
    ∃ K, ∀ m, P m ↔ m < K := by
  induction k with
  | zero =>
    exact ⟨0, fun m =>
      ⟨fun h => (hk (hP (Nat.zero_le m) h)).elim, fun h => (Nat.not_lt_zero m h).elim⟩⟩
  | succ k ih =>
    by_cases h : P k
    · exact ⟨k + 1, fun m => ⟨fun hm => Nat.lt_of_not_le fun hle => hk (hP hle hm),
        fun hm => hP (Nat.le_of_lt_succ hm) h⟩⟩
    · exact ih h

variable [IsCOFE α] [Inhabited α]

/-- Every chain has a point in all of its elements. -/
theorem exists_common {c : Approx α → Prop} (hc : chain c) : ∃ x, ∀ S, c S → S.1 x := by
  -- At each level `m` some element is precise at, pick such an element and its point `p m`.
  let S {m} (h : precs c m) : Approx α := Classical.choose h
  have hS {m} (h : precs c m) : c (S h) ∧ prec (S h).1 m := Classical.choose_spec h
  let p {m} (h : precs c m) := get (S h)
  -- These points agree at the lower level.
  have agree {m n} (hmn : m ≤ n) (hm : precs c m) (hn : precs c n) : p hn ≡{m}≡ p hm :=
    chain_dist hc (hS hn).1 (hS hm).1 (get_mem _) (get_mem _) (prec_mono (hS hn).2 hmn) (hS hm).2
  -- A point that agrees with each `p m` at level `m` is in every element.
  suffices ∃ x, ∀ m (h : precs c m), p h ≡{m}≡ x by
    obtain ⟨x, hx⟩ := this
    refine ⟨x, fun T hT => ?_⟩
    obtain ⟨t, ht⟩ := T.2.nonempty
    rw [T.2.eq_ball ht]
    intro m hm
    have h : precs c m := ⟨T, hT, hm⟩
    exact (chain_dist hc hT (hS h).1 ht (get_mem _) hm (hS h).2).trans (hx m h)
  by_cases hall : ∀ m, precs c m
  · -- Precise at every level: the limit of the points.
    let ch : Chain α := ⟨fun n => p (hall n), fun hni => agree hni _ _⟩
    exact ⟨COFE.compl ch, fun m _ => (COFE.conv_compl (c := ch) (n := m)).symm⟩
  · -- Precise below some level `K`: the point at the last level below it, if any.
    obtain ⟨k, hk⟩ := Classical.not_forall.mp hall
    obtain ⟨K, hK⟩ := exists_bound (fun hmn ⟨S, hS, hn⟩ => ⟨S, hS, prec_mono hn hmn⟩) hk
    match K with
    | 0 => exact ⟨default, fun m h => ((Nat.not_lt_zero m) ((hK m).mp h)).elim⟩
    | j + 1 =>
      exact ⟨p ((hK j).mpr (Nat.lt_succ_self j)),
        fun m h => (agree (Nat.le_of_lt_succ ((hK m).mp h)) h _).symm⟩

instance : CCPO (Approx α) where
  has_csup {c} hc :=
    let ⟨x, hx⟩ := exists_common hc
    ⟨⟨inter c, x, precs c, inter_eq_ball hx⟩, fun _ =>
      ⟨fun h y hy S hS => h S hS y hy, fun h S hS y hy => h y hy S hS⟩⟩

/-! ## Lifting a function to approximations -/

omit [IsCOFE α] in
/-- The smallest ball containing `T`, or everything when `T` is empty. -/
def hull (T : α → Prop) : Approx α :=
  ⟨fun z => ∀ m, prec T m → ∀ a, T a → a ≡{m}≡ z, by
    by_cases hne : ∃ a, T a
    · obtain ⟨a, ha⟩ := hne
      refine ⟨a, prec T, funext fun z => propext ⟨fun h m hm => h m hm a ha, ?_⟩⟩
      exact fun h m hm b hb => (hm b a hb ha).trans (h m hm)
    · exact ⟨default, fun _ => False, funext fun _ =>
        propext ⟨fun _ _ h => h.elim, fun _ _ _ a ha => (hne ⟨a, ha⟩).elim⟩⟩⟩

omit [IsCOFE α] in
theorem mem_hull {T : α → Prop} {a : α} (ha : T a) : (hull T).1 a :=
  fun _ hm _ hb => hm _ _ hb ha

omit [IsCOFE α] in
theorem prec_hull {T : α → Prop} {n : Nat} (hT : prec T n) (hne : ∃ a, T a) :
    prec (hull T).1 n :=
  let ⟨a, ha⟩ := hne
  fun _ _ hy hz => (hy n hT a ha).symm.trans (hz n hT a ha)

omit [IsCOFE α] in
/-- `hull` is monotone on nonempty sets. -/
theorem hull_mono {T T' : α → Prop} (h : ∀ a, T' a → T a) (hne : ∃ a, T' a) :
    ∀ z, (hull T').1 z → (hull T).1 z :=
  let ⟨b, hb⟩ := hne
  fun _ hz m hm a ha =>
    (hm a b ha (h b hb)).trans (hz m (fun x y hx hy => hm x y (h x hx) (h y hy)) b hb)

/-- Run `G` on every point of `S`. -/
def lift (G : α → α) (S : Approx α) : Approx α := hull fun y => ∃ x, S.1 x ∧ y = G x

omit [IsCOFE α] in
/-- Lifting is monotone, for any `G`. -/
theorem lift_mono (G : α → α) : monotone (lift G) :=
  fun _ S' h => hull_mono (fun _ ⟨x, hx, e⟩ => ⟨x, h x hx, e⟩) ⟨_, _, get_mem S', rfl⟩

omit [IsCOFE α] in
/-- For a contractive `G`, a fixpoint of `lift G` is a single point, and a fixpoint of `G`. -/
theorem lift_fix_get (G : α → α) [Contractive G] {S : Approx α} (hS : lift G S = S) :
    get S = G (get S) := by
  -- Each application of `G` gains a level of precision.
  have hprec n : prec S.1 n := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      rw [← hS]
      refine prec_hull ?_ ⟨_, _, get_mem S, rfl⟩
      rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact Contractive.distLater_dist fun m hm => ih m hm x y hx hy
  have hG : (lift G S).1 (G (get S)) := mem_hull ⟨_, get_mem S, rfl⟩
  rw [hS] at hG
  exact OFE.eq_dist'.mpr fun n => hprec n _ _ (get_mem S) hG

omit [Inhabited α] in
/-- A fixpoint of `lift G` is the Banach fixpoint of `G`, whatever the default point. -/
theorem get_eq_fixpoint {i j : Inhabited α} (G : α → α) [Contractive G] {S : Approx α}
    (hS : @lift α _ i G S = S) : get S = @fixpoint α _ j G _ :=
  @fixpoint_unique α _ j G.toContractiveHom _ (@lift_fix_get α _ i G _ S hS)

end Approx

end Iris
