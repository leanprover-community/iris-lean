/-
Copyright (c) 2026 Iris-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import IrisMath

@[expose] public section

/-!
# IrisMath showcase

This file is a documentation-by-example tour of the major OFE / COFE / CMRA
constructions assembled in `IrisMath`. Every declaration is either an
`example` checking that a key instance is inferrable, a tiny derived `theorem`
illustrating the recipe at work, or a comment connecting two modules.

The file deliberately contains no new instances or definitions: every result
is supposed to follow by `inferInstance`, by unfolding the relevant `_def`
lemma, or by reusing a non-expansive map already exposed elsewhere.

## Recipe taxonomy

The CMRAs in IrisMath fall into three broad families, mirroring the three
flavours of recipe in `Iris/Algebra/Numbers.lean`:

* **Universal-core, idempotent.** Every element is its own core; the
  operation is idempotent (`a + a = a`). These come from a (semi)lattice with
  a least element. Examples: `SigmaAlgebraCMRA`, `OpensCMRA`, `ClosedsCMRA`,
  `TopologicalSpaceCMRA`, `FinsetCMRA`, `CardinalMaxCMRA`, `IdealCMRA`,
  `SubmoduleCMRA`, `SublatticeCMRA`, `GCDCMRA`, `FilterCMRA`, `SetoidCMRA`.
* **Constant-core, non-idempotent.** `pcore` is the constant `some 0`, and
  only `0` is its own core. Examples: `MultisetCMRA`, `FreeAbelianGroupCMRA`,
  `CardinalAddCMRA`.
* **Step-indexed (non-discrete).** Genuine non-trivial dependence of
  `Dist n` on `n`. Examples: `UltraO (Padic p)`, `PowerSeries R`,
  `Polynomial R`, `Filtration.ProcessO`, `WittCOFE`, `ZModTowerCOFE`,
  `AdicCompletion`.
-/

open Iris

-- The scoped `instOFE` for power series and polynomials lives inside the
-- respective namespaces; opening them makes those instances visible.
open IrisMath.PowerSeries
open IrisMath.Polynomial

namespace IrisMath.Showcase

/-! ## Lattice CMRAs catalog

Idempotent, universal-core UCMRAs harvested from Mathlib's (semi)lattice
infrastructure. The operation is always `⊔`/`⊓`, the unit is `⊥`/`⊤`, and the
core is the element itself. -/

section LatticeCatalog

example : UCMRA (IrisMath.Lattice.GCDNat) := inferInstance

example : UCMRA (IrisMath.Lattice.FilterCMRA Nat) := inferInstance

example : UCMRA (IrisMath.Lattice.SubmoduleCMRA ℤ ℤ) := inferInstance

example : UCMRA (IrisMath.Lattice.IdealCMRA ℤ) := inferInstance

example : UCMRA (IrisMath.SigmaAlgebra.SigmaAlgebraCMRA Nat) := inferInstance

/-- For the topological CMRAs we need a `TopologicalSpace` instance on the
carrier type. The discrete topology (`⊥` in the `TopologicalSpace` lattice)
is always available and is the simplest choice. -/
example [TopologicalSpace Nat] : UCMRA (IrisMath.Opens.OpensCMRA Nat) := inferInstance

example [TopologicalSpace Nat] : UCMRA (IrisMath.Opens.ClosedsCMRA Nat) := inferInstance

example : UCMRA (IrisMath.TopologicalSpace.TopologicalSpaceCMRA Nat) := inferInstance

example : UCMRA (IrisMath.Setoid.SetoidCMRA Nat) := inferInstance

example : UCMRA (IrisMath.Sublattice.SublatticeCMRA (Finset Nat)) := inferInstance

/-- All lattice CMRAs are discrete: their OFE structure is `LeibnizO`. -/
example : OFE.Discrete (IrisMath.Lattice.IdealCMRA ℤ) := inferInstance

example : OFE.Leibniz (IrisMath.SigmaAlgebra.SigmaAlgebraCMRA Nat) := inferInstance

end LatticeCatalog

/-! ## Monoid CMRAs catalog

UCMRAs built from the constant-core `CommMonoidLike` recipe, plus the
idempotent `FinsetCMRA` and `CardinalMaxCMRA`. -/

section MonoidCatalog

example : UCMRA (IrisMath.MultisetCMRA Nat) := inferInstance

example : UCMRA (IrisMath.FinsetCMRA Nat) := inferInstance

example : UCMRA (IrisMath.FreeAbelianGroupCMRA Nat) := inferInstance

noncomputable example : UCMRA (IrisMath.CardinalAddCMRA) := inferInstance

noncomputable example : UCMRA (IrisMath.CardinalMaxCMRA) := inferInstance

/-- The free abelian group is also a group, so addition is left-cancellative. -/
example : LeftCancelAdd (IrisMath.FreeAbelianGroupCMRA Nat) := inferInstance

/-- The multiset CMRA is likewise left-cancellative. -/
example : LeftCancelAdd (IrisMath.MultisetCMRA Nat) := inferInstance

end MonoidCatalog

/-! ## Step-indexed OFEs catalog

These are the "real" step-indexed OFEs in IrisMath: their `Dist n` genuinely
depends on `n`. -/

section StepIndexed

/-- `p`-adic numbers via the ultrametric-OFE construction. -/
example : Fact (Nat.Prime 2) := ⟨by decide⟩

noncomputable example : COFE (IrisMath.Ultrametric.UltraO (Padic 2)) := inferInstance

noncomputable example : COFE (IrisMath.Ultrametric.UltraO (PadicInt 2)) := inferInstance

/-- Formal power series carry the X-adic OFE and are complete. -/
noncomputable example : COFE (PowerSeries ℤ) := inferInstance

/-- Polynomials carry the X-adic OFE but are deliberately **not** a COFE:
the file `IrisMath.Polynomial` skips the `IsCOFE` instance to highlight that
`Polynomial R` is the dense finite-support subspace of the completion
`PowerSeries R`. Only the OFE structure is asserted here. -/
example : OFE (Polynomial ℤ) := inferInstance

/-- Adapted processes / filtration-indexed OFEs from `IrisMath.Filtration`. -/
example {Ω β : Type*} : OFE (IrisMath.Filtration.ProcessO Ω β) := inferInstance

example {Ω β : Type*} : COFE (IrisMath.Filtration.ProcessO Ω β) := inferInstance

end StepIndexed

/-! ## Contractive endomaps catalog

The headlines of step-indexing: multiplication-by-`X` on power series and
polynomials is contractive, and the `prepend` endomap on adapted processes
is contractive. These are the canonical witnesses to which Banach's
fixed-point principle (and Iris's `Löb` induction) applies. -/

section Contractive

example {R : Type*} [CommRing R] :
    OFE.Contractive (fun (x : PowerSeries R) ↦ PowerSeries.X * x) :=
  inferInstance

example {R : Type*} [CommRing R] :
    OFE.Contractive (fun (x : Polynomial R) ↦ Polynomial.X * x) :=
  inferInstance

example {Ω β : Type*} (x₀ : Ω → β) :
    OFE.Contractive (IrisMath.Filtration.ProcessO.prepend x₀) :=
  IrisMath.Filtration.ProcessO.prepend_contractive x₀

/-- Iterating the basic contractive map: any positive power of `X` acts
contractively on polynomials. -/
example {R : Type*} [CommRing R] {j : ℕ} (hj : 1 ≤ j) :
    OFE.Contractive (fun (x : Polynomial R) ↦ Polynomial.X ^ j * x) :=
  IrisMath.Polynomial.contractive_X_pow_mul hj

/-- The non-expansive inclusion `Polynomial R ↪ PowerSeries R` makes
`Polynomial R` a sub-OFE of `PowerSeries R`. This is exactly the embedding of
the dense subspace into its completion. -/
example {R : Type*} [CommRing R] : Polynomial R -n> PowerSeries R :=
  IrisMath.Polynomial.toPowerSeriesHom

end Contractive

/-! ## Cross-module: `AdicCompletion` specialises to classical examples

`IrisMath.AdicCompletion R I` is the inverse limit of the tower
`n ↦ R ⧸ I ^ n` with the Leibniz OFE on each level. Specialising:

* `R = ℤ`, `I = (p)` recovers the `p`-adic integers `ℤ_p` (cf.
  `IrisMath.WittVectors.ZModTowerCOFE p`, which is the same limit written
  with `ZMod.castHom` instead of `Ideal.Quotient.factor`).
* `R = R₀[X]`, `I = (X)` recovers the formal power series `R₀⟦X⟧` (cf.
  `IrisMath.PowerSeries`, where the same OFE is built coefficient-wise).
-/

section AdicSpecialisations

/-- The `p`-adic integers, presented as the `(p)`-adic completion of `ℤ`. -/
example (p : ℤ) : Type := IrisMath.AdicCompletion ℤ (Ideal.span {p})

example (p : ℤ) : COFE (IrisMath.AdicCompletion ℤ (Ideal.span {p})) := inferInstance

/-- Formal power series, presented as the `(X)`-adic completion of `R₀[X]`. -/
noncomputable example (R₀ : Type) [CommRing R₀] : Type :=
  IrisMath.AdicCompletion (Polynomial R₀) (Ideal.span {(Polynomial.X : Polynomial R₀)})

noncomputable example (R₀ : Type) [CommRing R₀] :
    COFE (IrisMath.AdicCompletion (Polynomial R₀)
        (Ideal.span {(Polynomial.X : Polynomial R₀)})) :=
  inferInstance

end AdicSpecialisations

/-! ## Cross-module: `Filtration → SigmaAlgebra`

A measure-theoretic `Filtration ℕ m` produces a sequence of σ-algebras
that is monotone in the σ-algebra lattice — which is exactly the CMRA
inclusion order on `SigmaAlgebraCMRA Ω`. The bridge is
`IrisMath.SigmaAlgebra.filtrationSeq`. -/

section FiltrationSigmaAlgebra

open MeasureTheory IrisMath.SigmaAlgebra in
/-- Given any filtration on `ℕ`, projecting it through `filtrationSeq` lands
in `SigmaAlgebraCMRA Ω`. -/
example {Ω : Type*} {m : MeasurableSpace Ω} (f : Filtration ℕ m) :
    ℕ → SigmaAlgebraCMRA Ω :=
  SigmaAlgebraCMRA.filtrationSeq f

open MeasureTheory IrisMath.SigmaAlgebra in
/-- The monotonicity of a filtration is exactly the CMRA inclusion
`j ≤ k → (filtrationSeq f j).car ≤ (filtrationSeq f k).car`. -/
example {Ω : Type*} {m : MeasurableSpace Ω} (f : Filtration ℕ m) {j k : ℕ}
    (h : j ≤ k) :
    (SigmaAlgebraCMRA.filtrationSeq f j).car ≤
      (SigmaAlgebraCMRA.filtrationSeq f k).car :=
  SigmaAlgebraCMRA.filtrationSeq_mono f h

end FiltrationSigmaAlgebra

/-! ## Inverse-limit applications

The `IrisMath.InverseLimit` recipe assembles a COFE from a tower of OFEs.
Two profinite-style applications are exposed: Witt vectors and the
`ZMod (p ^ n)` tower of `p`-adic residues. -/

section InverseLimit

noncomputable example {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] :
    COFE (IrisMath.WittVectors.WittCOFE p R) :=
  inferInstance

example {p : ℕ} [Fact p.Prime] : COFE (IrisMath.WittVectors.ZModTowerCOFE p) :=
  inferInstance

/-- The level-`n` projection out of `WittCOFE p R` is non-expansive. -/
noncomputable example {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (n : ℕ) :
    IrisMath.WittVectors.WittCOFE p R -n> LeibnizO (TruncatedWittVector p n R) :=
  IrisMath.WittVectors.levelHom p R n

/-- Likewise the level-`n` projection out of `ZModTowerCOFE p`. -/
example {p : ℕ} (n : ℕ) :
    IrisMath.WittVectors.ZModTowerCOFE p -n> LeibnizO (ZMod (p ^ n)) :=
  IrisMath.WittVectors.zmodLevelHom (p := p) n

end InverseLimit

end IrisMath.Showcase
