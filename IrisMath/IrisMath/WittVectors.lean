module

public import Mathlib.RingTheory.WittVector.Truncated
public import Mathlib.Data.ZMod.Basic
public import IrisMath.InverseLimit
public import Iris

@[expose] public section

open Iris IrisMath

namespace IrisMath.WittVectors

/-! # Witt vectors as a COFE via inverse limits of OFEs

Mathlib exposes the ring `TruncatedWittVector p n R` of `p`-typical Witt vectors of length `n`,
together with the ring-homomorphism restrictions `TruncatedWittVector.truncate (h : n ≤ m)`
from `TruncatedWittVector p m R` to `TruncatedWittVector p n R`.

The full ring `WittVector p R` is morally the projective limit of these truncations along the
chain `… → TruncatedWittVector p (n+1) R → TruncatedWittVector p n R → …`. This file packages
that limit as an `IrisMath.Tower` of OFEs (with the *discrete* OFE on each level, via Iris's
`LeibnizO`) and obtains the resulting `OFE`/`COFE` structure on the inverse limit through
`IrisMath.InverseLimit`. The level-`n` projection `levelHom` and a smart constructor `ofWitt`
transporting Mathlib's `WittVector p R` into the limit complete the picture.

Since every level is discrete (Leibniz), every set-theoretic function between levels is
automatically non-expansive — in particular the truncation map. Each level is also a `COFE`
(the Leibniz OFE on any type is complete: chains are eventually constant), so by
`InverseLimit.instIsCOFE` the projective limit itself is a `COFE`.

This is the canonical profinite-style example of the tower-of-OFEs construction. As a second,
even more elementary instance of the same recipe, we also build the `ZMod`-tower
`n ↦ ZMod (p^n)` with the natural surjections `ZMod.castHom` between residue rings, producing
the COFE `ZModTowerCOFE p` of `p`-adic integers (qua compatible families of residues).
-/

/-! ## Witt vector tower -/

variable (p : ℕ) [Fact p.Prime] (R : Type _) [CommRing R]

/-- The Witt tower: level `n` is the (Leibniz-discrete) OFE on `TruncatedWittVector p n R`,
and the transition map from level `n+1` to level `n` is Mathlib's truncation
`TruncatedWittVector.truncate (Nat.le_succ n)`. Non-expansiveness is automatic because every
level is discrete: distance on `LeibnizO` reduces to equality, which every function preserves. -/
noncomputable def wittTower : Tower where
  carrier n := LeibnizO (TruncatedWittVector p n R)
  ofe _ := inferInstance
  proj n :=
    ⟨fun x ↦ ⟨TruncatedWittVector.truncate (Nat.le_succ n) x.car⟩,
      ⟨fun _ _ _ h ↦ by cases h; rfl⟩⟩

/-- Every level of the Witt tower is a `COFE`: it is a `LeibnizO`, and the Leibniz OFE on any
type is complete (chains are eventually constant). -/
instance instIsCOFE_carrier (n : ℕ) : IsCOFE ((wittTower p R).carrier n) :=
  (inferInstance : IsCOFE (LeibnizO (TruncatedWittVector p n R)))

/-- The COFE of Witt vectors over `R` at prime `p`, defined as the inverse limit of the
tower of truncated Witt vector rings, each carrying the discrete (Leibniz) OFE.

Elements are compatible families `x : (n : ℕ) → TruncatedWittVector p n R` satisfying
`TruncatedWittVector.truncate (Nat.le_succ n) (x (n + 1)) = x n` for every `n`. -/
noncomputable def WittCOFE : Type _ :=
  InverseLimit (wittTower p R)

/-- The inverse-limit OFE on `WittCOFE p R`, inherited from `InverseLimit.instOFE`. -/
noncomputable instance instOFE : OFE (WittCOFE p R) :=
  InverseLimit.instOFE

/-- The inverse-limit COFE on `WittCOFE p R`: every level is a `COFE` (Leibniz on any type
is complete), and `InverseLimit.instIsCOFE` lifts this to the limit. -/
noncomputable instance instIsCOFE : IsCOFE (WittCOFE p R) :=
  InverseLimit.instIsCOFE

noncomputable example : OFE (WittCOFE p R) := inferInstance
noncomputable example : IsCOFE (WittCOFE p R) := inferInstance

/-- Level-`n` projection out of `WittCOFE p R`, packaged as a non-expansive map into the
Leibniz OFE on `TruncatedWittVector p n R`. Inherited from `InverseLimit.levelHom`. -/
noncomputable def levelHom (n : ℕ) :
    WittCOFE p R -n> LeibnizO (TruncatedWittVector p n R) :=
  InverseLimit.levelHom (T := wittTower p R) n

/-! ## Concrete elements and transport from `WittVector`

We exhibit the canonical map from Mathlib's full Witt vector ring into the inverse-limit COFE,
sending a Witt vector `w` to its compatible family of truncations `n ↦ WittVector.truncate n w`.
Compatibility is `TruncatedWittVector.truncate_comp_wittVector_truncate`. -/

/-- A Witt vector, viewed as a compatible family in the inverse-limit COFE. The level-`n`
component is `WittVector.truncate n w`, and compatibility across `n ↦ n+1` is exactly
`TruncatedWittVector.truncate_comp_wittVector_truncate`. -/
noncomputable def ofWitt (w : WittVector p R) : WittCOFE p R :=
  ⟨fun n ↦ ⟨WittVector.truncate n w⟩, fun n ↦ by
    -- Goal reduces to equality of Leibniz-wrapped truncations, i.e.
    -- `⟨TruncatedWittVector.truncate _ (WittVector.truncate (n+1) w)⟩ = ⟨WittVector.truncate n w⟩`.
    change (⟨TruncatedWittVector.truncate (Nat.le_succ n) (WittVector.truncate (n + 1) w)⟩
        : LeibnizO _) ≡ ⟨WittVector.truncate n w⟩
    -- The compatibility of Witt vector truncations across the tower is a ring-hom equality
    -- between the composed truncation and the direct truncation; apply it at `w`.
    have hw : TruncatedWittVector.truncate (Nat.le_succ n) (WittVector.truncate (n + 1) w)
        = WittVector.truncate n w :=
      RingHom.congr_fun
        (TruncatedWittVector.truncate_comp_wittVector_truncate (Nat.le_succ n)) w
    exact congrArg LeibnizO.mk hw⟩

/-- The zero Witt vector as a compatible family: the level-`n` component is `0`, and
compatibility holds because truncation is a ring homomorphism (so sends `0` to `0`). -/
noncomputable def zero : WittCOFE p R :=
  ⟨fun _ ↦ ⟨0⟩, fun n ↦ by
    -- Compatibility: `(wittTower p R).proj n ⟨0⟩ ≡ ⟨0⟩`, which reduces to
    -- `⟨TruncatedWittVector.truncate _ 0⟩ = ⟨0⟩`. Apply `map_zero` to the truncation hom.
    change (⟨TruncatedWittVector.truncate (Nat.le_succ n) (0 : TruncatedWittVector p (n+1) R)⟩
        : LeibnizO _) ≡ ⟨0⟩
    rw [map_zero]⟩

/-! ## `ZMod` tower: `p`-adic integers as a COFE

The same machinery applied to the *much* simpler tower `n ↦ ZMod (p^n)` yields the COFE of
`p`-adic integers (presented as compatible residue families). The transition from level `n+1`
to level `n` is `ZMod.castHom` along `p^n ∣ p^(n+1)`. -/

/-- The `ZMod` tower at prime `p`: level `n` is the Leibniz OFE on `ZMod (p^n)`, and the
transition from level `n+1` to level `n` is the natural reduction
`ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ n)) (ZMod (p^n))`. -/
def zmodTower : Tower where
  carrier n := LeibnizO (ZMod (p ^ n))
  ofe _ := inferInstance
  proj n :=
    ⟨fun x ↦ ⟨ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x.car⟩,
      ⟨fun _ _ _ h ↦ by cases h; rfl⟩⟩

/-- Every level of the `ZMod` tower is a `COFE` (`LeibnizO` is always complete). -/
instance instIsCOFE_zmod_carrier (n : ℕ) : IsCOFE ((zmodTower p).carrier n) :=
  (inferInstance : IsCOFE (LeibnizO (ZMod (p ^ n))))

/-- The COFE of `p`-adic integers obtained as the inverse limit of the residue tower
`n ↦ ZMod (p^n)`. Elements are compatible families `x : (n : ℕ) → ZMod (p^n)` with
`ZMod.castHom _ _ (x (n+1)) = x n`. -/
def ZModTowerCOFE : Type :=
  InverseLimit (zmodTower p)

/-- The inverse-limit OFE on `ZModTowerCOFE p`. -/
instance instOFE_zmod : OFE (ZModTowerCOFE p) :=
  InverseLimit.instOFE

/-- The inverse-limit COFE on `ZModTowerCOFE p`. -/
instance instIsCOFE_zmod : IsCOFE (ZModTowerCOFE p) :=
  InverseLimit.instIsCOFE

/-- Level-`n` projection out of `ZModTowerCOFE p`, as a non-expansive map to
`LeibnizO (ZMod (p^n))`. -/
def zmodLevelHom (n : ℕ) : ZModTowerCOFE p -n> LeibnizO (ZMod (p ^ n)) :=
  InverseLimit.levelHom (T := zmodTower p) n

/-- The zero element of `ZModTowerCOFE p`: the constantly-`0` residue family. Compatibility
holds because `ZMod.castHom` is a ring homomorphism. -/
def zmodZero : ZModTowerCOFE p :=
  ⟨fun _ ↦ ⟨0⟩, fun n ↦ by
    change (⟨ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))
        (0 : ZMod (p ^ (n + 1)))⟩ : LeibnizO _) ≡ ⟨0⟩
    rw [map_zero]⟩

end IrisMath.WittVectors
