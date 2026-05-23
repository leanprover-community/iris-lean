module

public import Iris

@[expose] public section

open Iris OFE

namespace IrisMath

/-! # Direct limits of OFEs

This module exposes the inductive (direct, sequential colimit) of a `Nat`-indexed
*cotower* of OFEs. A **cotower** is dual to a `Tower`:

* a family `carrier : Nat → Type _` of carriers,
* an OFE structure on each `carrier n`,
* non-expansive *injection* maps `inj n : carrier n -n> carrier (n + 1)`.

The *direct limit* of a cotower is the OFE of *eventually-defined elements*:
equivalence classes of pairs `(n, a : carrier n)`, where two such pairs are
identified iff they agree after iterated injection at some common level above
both indices. The corresponding `Dist` is taken at that common level.

Whereas the inverse limit is used for "ever-truncated" structures (formal power
series, `p`-adic integers), the direct limit captures "ever-growing" ones (e.g.
the free group on a countable alphabet, polynomial rings in countably many
indeterminates).

## Scope of this file

This file lands the structural skeleton: the `CoTower` structure, iterated
injection (`injIter`) with its non-expansiveness and equivalence-preservation
lemmas, the underlying additive "pre-equivalence" relation on indexed pre-elements
(`PreEquiv`) with proofs of reflexivity and symmetry, and concrete examples
(`unitCoTower`, `constCoTower`, `prodCoTower`).

Transitivity of `PreEquiv` is established only via its **reflexive-transitive
closure** (`EqvGen`, defined locally below), since proving direct transitivity
requires nontrivial dependent transport reasoning that we have not formalised.
The full quotient is exposed as `DirectLimit T`, but the OFE/COFE structure on
the quotient is **left as future work**: equipping it requires showing that the
`Dist`-relation on pre-elements descends through the `EqvGen` closure, which is
the same dependent-transport obstacle.
-/

/-- A `Nat`-indexed cotower of OFEs with non-expansive injection maps. Dual to
`Tower`: data is a family of carriers, their OFE instances, and injection maps
`inj n : carrier n -n> carrier (n + 1)`. -/
structure CoTower where
  /-- The carrier type at each cotower level. -/
  carrier : Nat → Type _
  /-- The OFE instance at each cotower level. -/
  ofe : ∀ n, OFE (carrier n)
  /-- The non-expansive injection from level `n` into level `n + 1`. -/
  inj : ∀ n, @Hom (carrier n) (carrier (n + 1)) (ofe n) (ofe (n + 1))

attribute [instance] CoTower.ofe

namespace DirectLimit

variable {T : CoTower}

/-! ## Iterated injection

We package the iterated injection in the form `injIter n m : T.carrier n →
T.carrier (n + m)`. This is the *additive* version: arithmetic on the index
side is precisely `Nat` addition, which keeps definitional reductions simple
(`(n + 0) = n` and `(n + (m + 1)) = (n + m) + 1` both hold by `rfl`).
-/

/-- The iterated injection `T.carrier n → T.carrier (n + m)`, obtained by applying
`T.inj` repeatedly `m` times starting at level `n`. -/
def injIter (T : CoTower) (n : Nat) : (m : Nat) → T.carrier n → T.carrier (n + m)
  | 0, x => x
  | m + 1, x => T.inj (n + m) (injIter T n m x)

@[simp] theorem injIter_zero (T : CoTower) (n : Nat) (x : T.carrier n) :
    injIter T n 0 x = x := rfl

@[simp] theorem injIter_succ (T : CoTower) (n m : Nat) (x : T.carrier n) :
    injIter T n (m + 1) x = T.inj (n + m) (injIter T n m x) := rfl

/-- The iterated injection is non-expansive at every iteration step. -/
theorem injIter_dist {T : CoTower} {n m k : Nat} {x y : T.carrier n}
    (h : x ≡{k}≡ y) : injIter T n m x ≡{k}≡ injIter T n m y := by
  induction m with
  | zero => exact h
  | succ m ih => exact (T.inj (n + m)).ne.ne ih

/-- The iterated injection preserves equivalence. -/
theorem injIter_equiv {T : CoTower} {n m : Nat} {x y : T.carrier n}
    (h : x ≡ y) : injIter T n m x ≡ injIter T n m y :=
  equiv_dist.mpr fun _ ↦ injIter_dist h.dist

/-- One step of iteration agrees with `T.inj`. -/
theorem injIter_one (T : CoTower) (n : Nat) (x : T.carrier n) :
    injIter T n 1 x = T.inj n x := rfl

/-! ## Transport helpers

The pre-equivalence is phrased via an existential equality `n + m₁ = m + m₂` on
indices, and the witnessing equivalence is taken across the transport of one
side along that equality. To reason about this without invoking heavy
machinery, we package the basic transport-symmetry lemma here. -/

/-- Symmetry of a transported equivalence on the `T.carrier` family: if `h ▸ x
≡ y`, then `h.symm ▸ y ≡ x`. This is the dependent analogue of `Eq.symm`. -/
theorem carrier_transport_symm {T : CoTower} {n k : Nat}
    (h : n = k) (x : T.carrier n) (y : T.carrier k) (hxy : h ▸ x ≡ y) :
    (h.symm ▸ y : T.carrier n) ≡ x := by
  cases h
  exact hxy.symm

/-! ## Pre-elements and the additive equivalence -/

/-- The "pre-element" type: a sigma of an index and an inhabitant of that level. -/
abbrev PreElem (T : CoTower) : Type _ := Σ' n, T.carrier n

/-- Smart constructor for `PreElem`. -/
@[simp] def PreElem.mk (T : CoTower) (n : Nat) (x : T.carrier n) : PreElem T := ⟨n, x⟩

/-- The "additive" form of the direct-limit equivalence on pre-elements
`⟨n, a⟩ ~ ⟨m, b⟩`: there exist amounts `m₁, m₂ : Nat` and a witness
`n + m₁ = m + m₂` such that the iterated injections of the two sides agree (up
to `≡`) at the common level. The witness equality is used as a transport on the
`carrier` family to bring the two iterated injections to the same type. -/
def PreEquiv (T : CoTower) : PreElem T → PreElem T → Prop
  | ⟨n, a⟩, ⟨m, b⟩ =>
    ∃ m₁ m₂ : Nat, ∃ heq : n + m₁ = m + m₂,
      heq ▸ injIter T n m₁ a ≡ injIter T m m₂ b

/-- `PreEquiv` is reflexive: take `m₁ = m₂ = 0`. -/
theorem PreEquiv.refl (T : CoTower) (p : PreElem T) : PreEquiv T p p := by
  obtain ⟨n, a⟩ := p
  exact ⟨0, 0, rfl, Equiv.rfl⟩

/-- `PreEquiv` is symmetric. -/
theorem PreEquiv.symm {T : CoTower} {p q : PreElem T}
    (h : PreEquiv T p q) : PreEquiv T q p := by
  obtain ⟨n, a⟩ := p
  obtain ⟨m, b⟩ := q
  obtain ⟨m₁, m₂, heq, hab⟩ := h
  exact ⟨m₂, m₁, heq.symm, carrier_transport_symm heq _ _ hab⟩

/-- Bumping a pre-element up by one level via `T.inj` does not change its
equivalence class. -/
theorem PreEquiv.inj_step (T : CoTower) (n : Nat) (a : T.carrier n) :
    PreEquiv T ⟨n, a⟩ ⟨n + 1, T.inj n a⟩ := by
  refine ⟨1, 0, ?_, ?_⟩
  · omega
  · -- LHS-iterate is `T.inj n a`; RHS-iterate is `T.inj n a`. After the
    -- transport along `n + 1 = (n+1) + 0`, both sides agree definitionally.
    have heq : n + 1 = (n + 1) + 0 := rfl
    -- We can in fact just use `Equiv.rfl` because `n + 1 = (n + 1) + 0` holds
    -- by reduction in `Nat`.
    exact Equiv.rfl

/-! ## EqvGen — the equivalence closure (local definition)

We hand-roll `EqvGen` so we don't depend on Mathlib. It is the smallest
equivalence relation containing a given relation. -/

/-- The reflexive-symmetric-transitive closure of a relation. -/
inductive EqvGen {α : Sort _} (r : α → α → Prop) : α → α → Prop
  /-- Base step: the underlying relation embeds. -/
  | rel (x y : α) (h : r x y) : EqvGen r x y
  /-- Reflexivity. -/
  | refl (x : α) : EqvGen r x x
  /-- Symmetry. -/
  | symm (x y : α) (h : EqvGen r x y) : EqvGen r y x
  /-- Transitivity. -/
  | trans (x y z : α) (h₁ : EqvGen r x y) (h₂ : EqvGen r y z) : EqvGen r x z

/-- The equivalence closure is, by construction, an equivalence relation. -/
theorem EqvGen.is_equivalence {α : Sort _} (r : α → α → Prop) : Equivalence (EqvGen r) where
  refl := EqvGen.refl
  symm h := EqvGen.symm _ _ h
  trans h₁ h₂ := EqvGen.trans _ _ _ h₁ h₂

/-- The setoid on `PreElem T` for the direct-limit construction, obtained as the
equivalence closure of `PreEquiv`. Since direct transitivity of `PreEquiv` is
not formalised in this file (see module docstring), this setoid is the cleanest
sorry-free way to expose the quotient carrier. -/
def setoid (T : CoTower) : Setoid (PreElem T) where
  r := EqvGen (PreEquiv T)
  iseqv := EqvGen.is_equivalence _

/-- The direct limit carrier: pre-elements of the cotower modulo the
equivalence closure of `PreEquiv`. The OFE structure on this quotient is left
as future work — see the module docstring. -/
def _root_.IrisMath.DirectLimit (T : CoTower) : Type _ := Quotient (setoid T)

/-- The canonical class of a pre-element in the direct limit. -/
def mk (T : CoTower) (p : PreElem T) : DirectLimit T := Quotient.mk _ p

/-- Inclusion of a single level `n` into the direct limit. -/
def levelIncl (T : CoTower) (n : Nat) (a : T.carrier n) : DirectLimit T :=
  mk T ⟨n, a⟩

/-- The level inclusion is "stable under further injection": `levelIncl n a`
and `levelIncl (n+1) (T.inj n a)` agree in the direct limit. -/
theorem levelIncl_inj (T : CoTower) (n : Nat) (a : T.carrier n) :
    levelIncl T n a = levelIncl T (n + 1) (T.inj n a) := by
  apply Quotient.sound
  -- It suffices to give a single `PreEquiv` step.
  exact EqvGen.rel _ _ (PreEquiv.inj_step T n a)

/-- `mk` respects `PreEquiv` directly: equivalent pre-elements have equal
quotient classes. -/
theorem mk_eq_of_preEquiv {T : CoTower} {p q : PreElem T} (h : PreEquiv T p q) :
    mk T p = mk T q :=
  Quotient.sound (EqvGen.rel _ _ h)

end DirectLimit

/-! ## Concrete examples -/

/-- The trivial cotower: every level is `Unit`, with the unique injection. -/
def unitCoTower : CoTower where
  carrier _ := Unit
  ofe _ := inferInstance
  inj _ := ⟨fun _ ↦ (), ⟨fun _ _ _ _ ↦ trivial⟩⟩

/-- The constant cotower at a single OFE `α`: every level is `α` and every
injection is the identity. Pre-elements are then pairs `(n, a)` with the
obvious "shift one up" identification. -/
def constCoTower (α : Type _) [OFE α] : CoTower where
  carrier _ := α
  ofe _ := inferInstance
  inj _ := Hom.id

/-- Any element `a : α` gives a pre-element in the constant cotower at level `0`. -/
def constPreElem {α : Type _} [OFE α] (a : α) : DirectLimit.PreElem (constCoTower α) :=
  ⟨0, a⟩

/-- In the constant cotower, the iterated injection is the identity. -/
theorem constCoTower_injIter_eq {α : Type _} [OFE α] (n m : Nat) (a : α) :
    DirectLimit.injIter (constCoTower α) n m a = a := by
  induction m with
  | zero => rfl
  | succ m ih => simp [DirectLimit.injIter, constCoTower]; exact ih

/-- Transport on the constant-`α` carrier family is trivial. -/
theorem constCoTower_transport {α : Type _} [OFE α] {n k : Nat}
    (h : n = k) (a : α) : (h ▸ a : (constCoTower α).carrier k) = a := by
  cases h; rfl

/-- Two pre-elements of the constant cotower starting from the same element are
related by `PreEquiv`. -/
theorem constCoTower_preEquiv {α : Type _} [OFE α] (n m : Nat) (a : α) :
    DirectLimit.PreEquiv (constCoTower α) ⟨n, a⟩ ⟨m, a⟩ := by
  -- Take `m₁ := m`, `m₂ := n`; then `n + m = m + n` holds by `Nat.add_comm`.
  refine ⟨m, n, Nat.add_comm n m, ?_⟩
  -- After applying the transport, both sides reduce to `a` (because the
  -- iterated injection is the identity in the constant cotower).
  rw [constCoTower_injIter_eq, constCoTower_injIter_eq, constCoTower_transport]

/-- The level-`n` inclusion of `a` in the direct limit of the constant cotower
equals the level-`0` inclusion of `a`, for any `n`. -/
theorem constCoTower_levelIncl_eq {α : Type _} [OFE α] (n : Nat) (a : α) :
    DirectLimit.levelIncl (constCoTower α) n a =
      DirectLimit.levelIncl (constCoTower α) 0 a := by
  -- Direct from `mk_eq_of_preEquiv`: the constant cotower identifies all
  -- levels of the same element.
  exact DirectLimit.mk_eq_of_preEquiv (constCoTower_preEquiv n 0 a)

/-- The *product* of two cotowers, level by level. Dual to `prodTower`. -/
def prodCoTower (S T : CoTower) : CoTower where
  carrier n := S.carrier n × T.carrier n
  ofe _ := inferInstance
  inj n :=
    { f := fun p ↦ (S.inj n p.1, T.inj n p.2)
      ne.ne _ _ _ h := ⟨(S.inj n).ne.ne h.1, (T.inj n).ne.ne h.2⟩ }

/-- A pre-element of a product cotower is canonically built from a pair of
pre-elements at the same level. -/
def prodPreElem {S T : CoTower} (n : Nat) (x : S.carrier n) (y : T.carrier n) :
    DirectLimit.PreElem (prodCoTower S T) :=
  ⟨n, (x, y)⟩

end IrisMath
