module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.TypeTags.Finite
public import IrisMath.InverseLimit
public import Iris

@[expose] public section

open Iris IrisMath

namespace IrisMath.Profinite

/-! # Profinite-like groups as COFEs via inverse limits

A *profinite group* is, by the standard definition, an inverse limit of finite
discrete groups along surjective group homomorphisms. Equivalently, it is a
compact, Hausdorff, totally disconnected topological group. This file packages
the *algebraic* half of that picture — the tower of finite groups together with
its connecting homomorphisms — as a `FiniteQuotientTower`, and produces the
associated COFE `ProfiniteGroupCOFE T` by feeding it through
`IrisMath.InverseLimit`.

Since each level is a *finite* group, we equip it with the discrete (Leibniz)
OFE. Every set-theoretic function between Leibniz OFEs is automatically
non-expansive, so the group-homomorphism transitions lift to non-expansive
tower transitions with no extra effort. Every level is also a `COFE` (Leibniz
on any type is complete), so the inverse limit is a `COFE`.

Two concrete instances of the recipe land here:

* `unitTower'` / `unitProfiniteGroupCOFE`: the trivial tower at the unit group.
* `factorialZModTower` / `factorialZModProfiniteGroupCOFE`: the additive
  group tower `n ↦ ZMod (n+1)!` with transitions induced by the divisibility
  `(n+1)! ∣ (n+2)!`. This is genuinely non-degenerate and is *not* the same
  tower as the `ZMod (p^n)` tower built in `IrisMath.WittVectors`.

The smart constructor `ProfiniteGroupCOFE.ofGroup` exhibits the universal
property of the inverse limit in concrete form: a "global" group `G` equipped
with a compatible system of group homomorphisms `G →* T.group n` (one per
level, intertwining the tower transitions) maps canonically into
`ProfiniteGroupCOFE T`, by sending each `g : G` to its family of images. This
is the group-flavoured analogue of `IrisMath.AdicCompletion.mkOfElementHom` and
of `IrisMath.WittVectors.ofWitt`.

Forward references to sister files:

* `IrisMath.WittVectors` — the ring-flavoured tower of truncated Witt vectors,
  together with the `ZMod (p ^ n)` tower for `p`-adic integers.
* `IrisMath.AdicCompletion` — the `I`-adic completion of a commutative ring,
  which subsumes the `ZMod (p ^ n)` and formal-power-series towers and which
  carries an analogous `mkOfElement`/`mkOfElementHom` smart constructor.

Note: a hypothetical link to Mathlib's bundled `ProfiniteGrp` category would
require navigating topological-group instances and is deliberately out of
scope here. The point of this file is to expose the elementary tower-based
recipe in a Mathlib-friendly form. -/

/-! ## Finite-quotient towers -/

/-- The data of a "finite-quotient tower": a `Nat`-indexed family of finite
groups together with transition group homomorphisms `proj n : group (n+1) →* group n`.

This abstracts the situation `G = lim G/N_n` for a decreasing chain of
finite-index normal subgroups: each `group n` is `G/N_n`, and `proj n` is the
canonical projection induced by `N_(n+1) ⊆ N_n`. We do not need the ambient
`G` to set up the inverse-limit COFE — the tower data alone suffices. -/
structure FiniteQuotientTower where
  /-- The carrier group at level `n`. -/
  group : Nat → Type _
  /-- The group structure at each level. -/
  groupInst : ∀ n, Group (group n)
  /-- Finiteness of every level — the "finite-quotient" content of the tower. -/
  finiteInst : ∀ n, Finite (group n)
  /-- The group-homomorphism transition from level `n+1` down to level `n`. -/
  proj : ∀ n, group (n + 1) →* group n

attribute [instance] FiniteQuotientTower.groupInst FiniteQuotientTower.finiteInst

namespace FiniteQuotientTower

variable (T : FiniteQuotientTower)

/-- The underlying OFE tower of a `FiniteQuotientTower`: every level is the
discrete (Leibniz) OFE on the finite group at that level, and the transition
maps are the underlying functions of the group homomorphisms, packaged as
non-expansive maps. Non-expansiveness is automatic because the source level is
Leibniz: `Dist k` on `LeibnizO α` reduces to equality, which any function
preserves. -/
def toTower : Tower where
  carrier n := LeibnizO (T.group n)
  ofe _ := inferInstance
  proj n :=
    ⟨fun x ↦ ⟨T.proj n x.car⟩, ⟨fun _ _ _ h ↦ by cases h; rfl⟩⟩

/-- Every level of `T.toTower` is a `COFE`: it is a `LeibnizO`, and the Leibniz
OFE on any type is complete (chains are eventually constant). -/
instance instIsCOFE_carrier (n : Nat) : IsCOFE (T.toTower.carrier n) :=
  (inferInstance : IsCOFE (LeibnizO (T.group n)))

end FiniteQuotientTower

/-! ## The profinite-group COFE -/

/-- The COFE associated to a `FiniteQuotientTower`, defined as the inverse limit
of its tower of Leibniz-discrete OFEs on the finite levels.

Elements are compatible families `x : (n : ℕ) → T.group n` with
`T.proj n (x (n + 1)) = x n` for every `n`. This is the underlying type of the
profinite group `G = lim T.group n`, viewed as a step-indexed object. -/
def ProfiniteGroupCOFE (T : FiniteQuotientTower) : Type _ :=
  InverseLimit T.toTower

namespace ProfiniteGroupCOFE

variable {T : FiniteQuotientTower}

/-- The inverse-limit OFE on `ProfiniteGroupCOFE T`. -/
instance instOFE : OFE (ProfiniteGroupCOFE T) :=
  InverseLimit.instOFE

/-- The inverse-limit COFE on `ProfiniteGroupCOFE T`: every level is a `COFE`
(Leibniz on any type is complete), and `InverseLimit.instIsCOFE` lifts this to
the limit. -/
instance instIsCOFE : IsCOFE (ProfiniteGroupCOFE T) :=
  InverseLimit.instIsCOFE

/-- Level-`n` projection out of `ProfiniteGroupCOFE T`, packaged as a
non-expansive map into the Leibniz OFE on `T.group n`. Inherited from
`InverseLimit.levelHom`. -/
def levelHom (n : Nat) : ProfiniteGroupCOFE T -n> LeibnizO (T.group n) :=
  InverseLimit.levelHom (T := T.toTower) n

/-- The identity element of the profinite group, as a compatible family of
identity elements at every level. Compatibility holds because each transition
`T.proj n` is a *group homomorphism*, so sends `1` to `1`. -/
def one : ProfiniteGroupCOFE T :=
  ⟨fun _ ↦ ⟨1⟩, fun n ↦ by
    -- Goal: `(T.toTower.proj n) ⟨1⟩ ≡ ⟨1⟩`, which unfolds to
    -- `⟨T.proj n (1 : T.group (n+1))⟩ = ⟨1⟩`. Apply `map_one`.
    change (⟨T.proj n (1 : T.group (n + 1))⟩ : LeibnizO _) ≡ ⟨1⟩
    rw [map_one]⟩

/-! ### Smart constructor from a global group

The universal property of an inverse limit of groups: any group `G` together
with a compatible system of group homomorphisms `φ n : G →* T.group n`
(intertwining the tower transitions, i.e. `T.proj n ∘ φ (n + 1) = φ n`) maps
canonically into `ProfiniteGroupCOFE T`. We expose two flavours: the bare
set-theoretic version `ofGroup`, and the non-expansive version `ofGroupHom`
that takes a Leibniz-OFE input. -/

/-- The image of a global group element `g : G` in `ProfiniteGroupCOFE T` along
a compatible system `φ : ∀ n, G →* T.group n` of group homomorphisms. The
compatibility hypothesis `hφ` says the `φ`s intertwine the tower transitions
`T.proj`, which is exactly the condition the inverse limit demands. -/
def ofGroup {G : Type _} [Group G] (φ : ∀ n, G →* T.group n)
    (hφ : ∀ n g, T.proj n (φ (n + 1) g) = φ n g) (g : G) :
    ProfiniteGroupCOFE T :=
  ⟨fun n ↦ ⟨φ n g⟩, fun n ↦ by
    change (⟨T.proj n (φ (n + 1) g)⟩ : LeibnizO _) ≡ ⟨φ n g⟩
    rw [hφ n g]⟩

@[simp] theorem ofGroup_val {G : Type _} [Group G] (φ : ∀ n, G →* T.group n)
    (hφ : ∀ n g, T.proj n (φ (n + 1) g) = φ n g) (g : G) (n : Nat) :
    (ofGroup φ hφ g).val n = ⟨φ n g⟩ := rfl

/-- Sanity lemma: `ofGroup` sends `1 : G` to `one`. Both sides are the
compatible family `n ↦ ⟨1⟩`; the equality holds because each `φ n` is a group
homomorphism and therefore preserves `1`. -/
theorem ofGroup_one {G : Type _} [Group G] (φ : ∀ n, G →* T.group n)
    (hφ : ∀ n g, T.proj n (φ (n + 1) g) = φ n g) :
    ofGroup φ hφ (1 : G) = one := by
  refine InverseLimit.ext (T := T.toTower) (fun n ↦ ?_)
  change (⟨φ n (1 : G)⟩ : LeibnizO _) = ⟨1⟩
  rw [map_one]

/-- The "include a global group" map `G → ProfiniteGroupCOFE T`, packaged as a
non-expansive map out of the Leibniz OFE on `G`. This is the
profinite-group analogue of `IrisMath.AdicCompletion.mkOfElementHom`: a
compatible system of group homomorphisms `φ : ∀ n, G →* T.group n` assembles
into the canonical "universal" map from the global group into the inverse
limit, via `InverseLimit.mkHom`. -/
def ofGroupHom {G : Type _} [Group G] (φ : ∀ n, G →* T.group n)
    (hφ : ∀ n g, T.proj n (φ (n + 1) g) = φ n g) :
    LeibnizO G -n> ProfiniteGroupCOFE T :=
  InverseLimit.mkHom
    (T := T.toTower)
    (fun n ↦
      ⟨fun g ↦ ⟨φ n g.car⟩, ⟨fun _ _ _ h ↦ by cases h; rfl⟩⟩)
    (fun n g ↦ by
      change (⟨T.proj n (φ (n + 1) g.car)⟩ : LeibnizO _) ≡ ⟨φ n g.car⟩
      rw [hφ n g.car])

@[simp] theorem ofGroupHom_apply_val {G : Type _} [Group G]
    (φ : ∀ n, G →* T.group n) (hφ : ∀ n g, T.proj n (φ (n + 1) g) = φ n g)
    (g : LeibnizO G) (n : Nat) :
    (ofGroupHom φ hφ g).val n = ⟨φ n g.car⟩ := rfl

end ProfiniteGroupCOFE

/-! ## Example 1: the trivial tower

The unit-group tower: every level is `Unit` (with its canonical group
structure), and every transition is the trivial homomorphism. This is the
profinite-group analogue of the trivial tower in `IrisMath.InverseLimit`, and
shows that the machinery typechecks end-to-end. -/

/-- The unit-group tower: every level is `Unit` and every transition is the
trivial group homomorphism. -/
def unitTower' : FiniteQuotientTower where
  group _ := Unit
  groupInst _ := inferInstance
  finiteInst _ := inferInstance
  proj _ := 1

/-- The COFE associated to the unit-group tower. Degenerate but well-typed:
exhibits the construction without any algebraic content. -/
def unitProfiniteGroupCOFE : Type :=
  ProfiniteGroupCOFE unitTower'

/-- The inverse-limit OFE on `unitProfiniteGroupCOFE`. -/
instance : OFE unitProfiniteGroupCOFE := ProfiniteGroupCOFE.instOFE

/-- The inverse-limit COFE on `unitProfiniteGroupCOFE`. -/
instance : IsCOFE unitProfiniteGroupCOFE := ProfiniteGroupCOFE.instIsCOFE

example : OFE unitProfiniteGroupCOFE := inferInstance
example : IsCOFE unitProfiniteGroupCOFE := inferInstance

/-! ## Example 2: the factorial `ZMod` tower

A genuinely non-trivial example that is distinct from the `ZMod (p^n)` tower
already built in `IrisMath.WittVectors`: level `n` is `ZMod (n + 1)!` (the
factorial of `n + 1`), with the transition from level `n + 1` to level `n`
induced by the divisibility `(n + 1)! ∣ (n + 2)!` (which holds because
`(n + 2)! = (n + 2) * (n + 1)!`).

The inverse limit is morally `ẑ` viewed through the factorial filtration on
the integers — a profinite completion of `ℤ` along a *different* (and finer
on the divisibility lattice) chain than the `p`-adic one. -/

/-- Divisibility witness for the factorial transition: `(n + 1)! ∣ (n + 2)!`.
This follows from `Nat.factorial_dvd_factorial` applied to `n + 1 ≤ n + 2`. -/
lemma factorial_dvd_succ (n : Nat) : (n + 1).factorial ∣ (n + 2).factorial :=
  Nat.factorial_dvd_factorial (Nat.le_succ _)

/-- The factorial `ZMod` tower: level `n` is the additive group `ZMod (n + 1)!`,
and the transition from level `n + 1` to level `n` is the canonical reduction
`ZMod.castHom (factorial_dvd_succ n) (ZMod (n + 1)!)`. All levels are finite. -/
def factorialZModTower : FiniteQuotientTower where
  group n := Multiplicative (ZMod (n + 1).factorial)
  groupInst _ := inferInstance
  finiteInst n :=
    haveI : NeZero (n + 1).factorial := ⟨Nat.factorial_ne_zero _⟩
    inferInstance
  proj n :=
    -- Lift the additive `ZMod.castHom` to a multiplicative group hom via
    -- `Multiplicative`. The underlying function is just `ZMod.castHom`.
    { toFun := fun x ↦
        Multiplicative.ofAdd
          (ZMod.castHom (factorial_dvd_succ n) (ZMod (n + 1).factorial)
            (Multiplicative.toAdd x))
      map_one' := by
        -- `1` in `Multiplicative (ZMod _)` is `ofAdd 0`; `castHom` sends `0` to `0`.
        change Multiplicative.ofAdd
            (ZMod.castHom (factorial_dvd_succ n) (ZMod (n + 1).factorial) 0) = _
        rw [map_zero]
        rfl
      map_mul' := fun x y ↦ by
        -- `mul` on `Multiplicative` is `add` on the underlying type;
        -- `castHom` is a ring homomorphism, in particular additive.
        change Multiplicative.ofAdd
            (ZMod.castHom (factorial_dvd_succ n) (ZMod (n + 1).factorial)
              (Multiplicative.toAdd x + Multiplicative.toAdd y))
          = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
        rw [map_add]
        rfl }

/-- The COFE associated to the factorial `ZMod` tower. Elements are compatible
families `x : (n : ℕ) → Multiplicative (ZMod (n + 1)!)` whose adjacent levels
agree under the factorial reduction. -/
def factorialZModProfiniteGroupCOFE : Type :=
  ProfiniteGroupCOFE factorialZModTower

/-- The inverse-limit OFE on `factorialZModProfiniteGroupCOFE`. -/
instance : OFE factorialZModProfiniteGroupCOFE := ProfiniteGroupCOFE.instOFE

/-- The inverse-limit COFE on `factorialZModProfiniteGroupCOFE`. -/
instance : IsCOFE factorialZModProfiniteGroupCOFE := ProfiniteGroupCOFE.instIsCOFE

example : OFE factorialZModProfiniteGroupCOFE := inferInstance
example : IsCOFE factorialZModProfiniteGroupCOFE := inferInstance

/-- The identity element of the factorial tower's profinite group, presented
as a compatible family of `ofAdd 0`s. -/
def factorialZModOne : factorialZModProfiniteGroupCOFE :=
  ProfiniteGroupCOFE.one

end IrisMath.Profinite
