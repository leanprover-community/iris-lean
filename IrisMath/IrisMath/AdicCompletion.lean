module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.Algebra.Polynomial.Basic
public import IrisMath.InverseLimit
public import Iris

@[expose] public section

open Iris IrisMath

namespace IrisMath

/-! # `I`-adic completion of a commutative ring as a COFE

For a commutative ring `R` and an ideal `I : Ideal R`, the `I`-adic completion is the
projective limit `R̂_I = lim_n R ⧸ I ^ n` of the tower of quotient rings, equipped with
the discrete (Leibniz) OFE on each level. The transition maps are the canonical ring
homomorphisms `R ⧸ I ^ (n + 1) →+* R ⧸ I ^ n` induced by `I ^ (n + 1) ≤ I ^ n` via
`Ideal.Quotient.factor` (a.k.a. `Ideal.Quotient.factorPow`).

This construction unifies a number of classical step-indexed completions that are
otherwise built by hand: each is recovered by specialising `R` and `I`.

* **`p`-adic integers**: take `R = ℤ` and `I = Ideal.span {p}`. The resulting tower
  is `n ↦ ℤ ⧸ (p)^n`, canonically isomorphic to the `ZMod (p ^ n)` tower built in
  `IrisMath.WittVectors`, so `AdicCompletion ℤ (Ideal.span {p})` is (up to iso)
  `ℤ_p`.
* **Formal power series**: take `R = R₀[X]` and `I = Ideal.span {X}`. The tower
  `n ↦ R₀[X] ⧸ (X)^n` is the tower of polynomial truncations, whose limit is the
  ring of formal power series `R₀⟦X⟧`.
* **`ZMod` tower**: the `WittVectors.ZModTowerCOFE p` construction is the same
  inverse limit, written with `ZMod.castHom` instead of `Ideal.Quotient.factor`.

Since every level is a `LeibnizO`, every set-theoretic function between levels is
non-expansive and every level is a `COFE`, so the inverse limit is automatically a
`COFE` via `IrisMath.InverseLimit.instIsCOFE`.

Mathlib provides its own `AdicCompletion I M` as a submodule of compatible families
for modules; this file builds the *ring*-flavoured version directly as an
`InverseLimit`, focusing on the OFE/COFE structure.
-/

variable (R : Type _) [CommRing R] (I : Ideal R)

/-- The `I`-adic tower of `R`: level `n` is the Leibniz OFE on the quotient ring
`R ⧸ I ^ n`, and the transition from level `n + 1` to level `n` is the ring
homomorphism `Ideal.Quotient.factor` induced by `I ^ (n + 1) ≤ I ^ n`.

Non-expansiveness of the transition is automatic because each level is discrete
(Leibniz): `Dist` on `LeibnizO` reduces to equality, which every function preserves. -/
def adicTower : Tower where
  carrier n := LeibnizO (R ⧸ I ^ n)
  ofe _ := inferInstance
  proj n :=
    ⟨fun x ↦ ⟨Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n)) x.car⟩,
      ⟨fun _ _ _ h ↦ by cases h; rfl⟩⟩

/-- Every level of the adic tower is a `COFE`: it is a `LeibnizO`, and the Leibniz OFE
on any type is complete (chains are eventually constant). -/
instance instIsCOFE_adicTower_carrier (n : ℕ) : IsCOFE ((adicTower R I).carrier n) :=
  (inferInstance : IsCOFE (LeibnizO (R ⧸ I ^ n)))

/-- The `I`-adic completion of `R` as the inverse limit of the tower
`n ↦ LeibnizO (R ⧸ I ^ n)`. Elements are compatible families
`x : (n : ℕ) → R ⧸ I ^ n` satisfying
`Ideal.Quotient.factor _ (x (n + 1)) = x n` for every `n`. -/
def AdicCompletion : Type _ :=
  InverseLimit (adicTower R I)

namespace AdicCompletion

/-- The inverse-limit OFE on the `I`-adic completion, inherited from
`InverseLimit.instOFE`. -/
instance instOFE : OFE (AdicCompletion R I) :=
  InverseLimit.instOFE

/-- The inverse-limit COFE on the `I`-adic completion: every level is a `COFE`
(Leibniz on any type is complete), and `InverseLimit.instIsCOFE` lifts this to the
limit. -/
instance instIsCOFE : IsCOFE (AdicCompletion R I) :=
  InverseLimit.instIsCOFE

example : OFE (AdicCompletion R I) := inferInstance
example : IsCOFE (AdicCompletion R I) := inferInstance

/-- Level-`n` projection out of the `I`-adic completion, packaged as a non-expansive
map into the Leibniz OFE on `R ⧸ I ^ n`. Inherited from `InverseLimit.levelHom`. -/
def levelHom (n : ℕ) :
    AdicCompletion R I -n> LeibnizO (R ⧸ I ^ n) :=
  InverseLimit.levelHom (T := adicTower R I) n

/-! ## Concrete elements -/

/-- The zero element of the `I`-adic completion: the constantly-`0` residue family.
Compatibility holds because the transition `Ideal.Quotient.factor` is a ring
homomorphism, hence sends `0` to `0`. -/
def zero : AdicCompletion R I :=
  ⟨fun _ ↦ ⟨0⟩, fun n ↦ by
    change (⟨Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))
        (0 : R ⧸ I ^ (n + 1))⟩ : LeibnizO _) ≡ ⟨0⟩
    rw [map_zero]⟩

/-- A ring element `r : R`, viewed as a compatible family in the `I`-adic completion:
the level-`n` component is `(Ideal.Quotient.mk (I ^ n)) r`. Compatibility across
`n ↦ n + 1` follows from the defining commutation
`Ideal.Quotient.factor h ∘ Ideal.Quotient.mk J = Ideal.Quotient.mk K` for `J ≤ K`. -/
def mkOfElement (r : R) : AdicCompletion R I :=
  ⟨fun n ↦ ⟨Ideal.Quotient.mk (I ^ n) r⟩, fun n ↦ by
    change (⟨Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))
        (Ideal.Quotient.mk (I ^ (n + 1)) r)⟩ : LeibnizO _) ≡ ⟨Ideal.Quotient.mk (I ^ n) r⟩
    rfl⟩

/-- The "include constants" map `R → AdicCompletion R I`, packaged as a non-expansive
map out of the Leibniz OFE on `R`. This is the canonical map sending a ring element to
its compatible family of residues; it is the adic-completion analogue of
`InverseLimit.mkHom` applied to the obvious level-wise inclusion. -/
def mkOfElementHom : LeibnizO R -n> AdicCompletion R I :=
  InverseLimit.mkHom
    (T := adicTower R I)
    (fun n ↦
      ⟨fun r ↦ ⟨Ideal.Quotient.mk (I ^ n) r.car⟩,
        ⟨fun _ _ _ h ↦ by cases h; rfl⟩⟩)
    (fun n r ↦ by
      change (⟨Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))
          (Ideal.Quotient.mk (I ^ (n + 1)) r.car)⟩ : LeibnizO _) ≡
        ⟨Ideal.Quotient.mk (I ^ n) r.car⟩
      rfl)

@[simp] theorem mkOfElementHom_apply_val (r : LeibnizO R) (n : ℕ) :
    (mkOfElementHom R I r).val n = ⟨Ideal.Quotient.mk (I ^ n) r.car⟩ := rfl

/-- Sanity lemma: `mkOfElement` sends `0` to `zero`. Both sides are the compatible
family `n ↦ ⟨0⟩`; the equality holds because `Ideal.Quotient.mk` is a ring homomorphism
and therefore preserves `0`. -/
theorem mkOfElement_zero : mkOfElement R I 0 = zero R I := by
  refine InverseLimit.ext (T := adicTower R I) (fun n ↦ ?_)
  change (⟨Ideal.Quotient.mk (I ^ n) (0 : R)⟩ : LeibnizO _) = ⟨0⟩
  rw [map_zero]

/-! ## Example: the `p`-adic integers via `R = ℤ`, `I = (p)`

The `(p)`-adic completion of `ℤ` is (isomorphic to) the ring of `p`-adic integers
`ℤ_p`. As an `InverseLimit` this matches the `n ↦ ZMod (p ^ n)` tower constructed in
`IrisMath.WittVectors`, up to the canonical ring isomorphism `ℤ ⧸ (p) ^ n ≃ ZMod (p ^ n)`.
-/

/-- The `p`-adic integers, presented as the `(p : ℤ)`-adic completion of `ℤ`. -/
example (p : ℤ) : Type _ := AdicCompletion ℤ (Ideal.span {p})

/-- The OFE structure on the `p`-adic integers (presented as an adic completion). -/
example (p : ℤ) : OFE (AdicCompletion ℤ (Ideal.span {p})) := inferInstance

/-- The COFE structure on the `p`-adic integers (presented as an adic completion). -/
example (p : ℤ) : IsCOFE (AdicCompletion ℤ (Ideal.span {p})) := inferInstance

/-- The zero `p`-adic integer. -/
example (p : ℤ) : AdicCompletion ℤ (Ideal.span {p}) :=
  zero ℤ (Ideal.span {p})

/-- The image of an integer in the `p`-adic completion. -/
example (p n : ℤ) : AdicCompletion ℤ (Ideal.span {p}) :=
  mkOfElement ℤ (Ideal.span {p}) n

/-- The non-expansive "constant" inclusion `ℤ -n> ℤ_p` (presented as an adic completion). -/
example (p : ℤ) : LeibnizO ℤ -n> AdicCompletion ℤ (Ideal.span {p}) :=
  mkOfElementHom ℤ (Ideal.span {p})

/-! ## Example: formal power series via `R = R₀[X]`, `I = (X)`

The `(X)`-adic completion of the polynomial ring `R₀[X]` is the ring of formal power
series `R₀⟦X⟧`. The level-`n` quotient `R₀[X] ⧸ (X) ^ n` is the ring of polynomials
truncated to degree `< n`, and the inverse limit assembles a power series from its
sequence of polynomial truncations. -/

open Polynomial in
/-- The ring of formal power series in `X` over `R₀`, presented as the `(X)`-adic
completion of the polynomial ring `R₀[X]`. -/
noncomputable example (R₀ : Type _) [CommRing R₀] : Type _ :=
  AdicCompletion R₀[X] (Ideal.span {(X : R₀[X])})

open Polynomial in
/-- The OFE structure on the power-series-style adic completion. -/
noncomputable example (R₀ : Type _) [CommRing R₀] :
    OFE (AdicCompletion R₀[X] (Ideal.span {(X : R₀[X])})) := inferInstance

open Polynomial in
/-- The COFE structure on the power-series-style adic completion. -/
noncomputable example (R₀ : Type _) [CommRing R₀] :
    IsCOFE (AdicCompletion R₀[X] (Ideal.span {(X : R₀[X])})) := inferInstance

end AdicCompletion

end IrisMath
