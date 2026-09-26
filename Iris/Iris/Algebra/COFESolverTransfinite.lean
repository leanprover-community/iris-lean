/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Algebra.Truncation

/-! # The transfinite COFE solver

This file ports the transfinite solver for recursive domain equations of Transfinite Iris
(`theories/algebra/cofe_solver.v`): for a contractive bifunctor `F` on COFEs over an arbitrary type
of step-indices, it constructs a COFE `X` with `F X X ≅ X`.

The solution is the inverse limit of approximations `X γ` (one for every step-index `γ`), where
`X γ` is truncated at `γ` and `X (γ + 1) = [F (X γ) (X γ)]_{γ + 1}`. At a limit index `γ`, the
approximation is obtained from the inverse limit `L` of the earlier approximations as
`X γ = [F L L]_{γ}`.

## Differences to the Rocq development

- Truncations are quotients (`TruncO`, `Iris.Algebra.Truncation`), so the functor does not need
  to be `Truncatable`.
- Rocq defines the approximations by well-founded induction-recursion (`wf_IR.v`), keeping track of
  the agreement of different approximations with transports. Here, one well-founded recursion
  defines a `Stage` for every index, which stores its own component and copies of the earlier
  components (`Stage.prev`). The copies agree with the earlier stages by the unfolding equation of
  the recursion. Maps between earlier components are recovered by casting along this agreement,
  with a junk default when it fails (it never does).
- The functor of Iris-Lean takes COFEs as arguments, so the inverse limit at a limit index needs a
  COFE structure (Rocq only needs an OFE). Its completion of bounded chains uses the laws of the
  earlier approximations, so the limit step branches (classically) on these laws (`FamGood`),
  which are proved afterwards for the actual approximations.

## Assumptions

As in Rocq, bounded limits in the images of `F` must be unique (`BcomplUniqueLim`).
-/

@[expose] public section

namespace Iris.COFE.OFunctor.Transfinite
open OFE

universe u

variable {SI : Type u} [instSI : SIdx SI]
local stepindex SI

local notation "σ" => SIdx.succ

attribute [local instance low] Classical.propDecidable

/-! ## Bundled COFEs -/

/-- An inhabited COFE, bundled. -/
structure Obj where
  car : Type u
  [cofe : COFE (SI := SI) car]
  [inh : Inhabited car]

attribute [instance] Obj.cofe Obj.inh

/-- Casting along an equality of bundled COFEs. -/
def castObj {A B : Obj (SI := SI)} (h : A = B) : A.car -n> B.car := h ▸ Hom.id

@[simp] theorem castObj_rfl {A : Obj (SI := SI)} (x : A.car) : castObj (rfl : A = A) x = x := rfl

theorem castObj_castObj {A B C : Obj (SI := SI)} (h1 : A = B) (h2 : B = C) (x : A.car) :
    castObj h2 (castObj h1 x) = castObj (h1.trans h2) x := by
  subst h1 h2; rfl

@[simp] theorem castObj_symm_castObj {A B : Obj (SI := SI)} (h : A = B) (x : A.car) :
    castObj h.symm (castObj h x) = x := by
  subst h; rfl

@[simp] theorem castObj_castObj_symm {A B : Obj (SI := SI)} (h : A = B) (x : B.car) :
    castObj h (castObj h.symm x) = x := by
  subst h; rfl

theorem castObj_heq {A B : Obj (SI := SI)} (h : A = B) (x : A.car) : HEq (castObj h x) x := by
  subst h; rfl

/-- A constant non-expansive map. -/
def constHom {A B : Type _} [OFE A] [OFE B] (y : B) : A -n> B := ⟨fun _ => y, ⟨fun _ _ _ _ => .rfl⟩⟩

@[simp] theorem constHom_apply {A B : Type _} [OFE A] [OFE B] (y : B) (x : A) :
    constHom y x = y := rfl

/-! ## The functor -/

variable {F : ∀ α β [COFE α] [COFE β], Type u} [OFunctorContractive F]
variable [∀ α [COFE α], IsCOFE (F α α)]
variable [inh : Inhabited (F (ULift Unit) (ULift Unit))]

/-- The unit COFE, bundled. -/
def unitObj : Obj (SI := SI) := ⟨ULift Unit⟩

/-- The functor is inhabited on every inhabited COFE. -/
instance Finh {A : Type u} [COFE A] [Inhabited A] : Inhabited (F A A) :=
  ⟨map (F := F) (constHom ⟨()⟩ : A -n> ULift Unit) (constHom default) inh.default⟩

variable (F) in
/-- The truncation `[F X X]_{α}` of the functor applied to `X` (Rocq: `[G X]_{α}`). -/
noncomputable abbrev TG (α : SI) (X : Obj (SI := SI)) : Obj (SI := SI) :=
  ⟨TruncO α (F X.car X.car)⟩

theorem TG_car (α : SI) (X : Obj (SI := SI)) : (TG F α X).car = TruncO α (F X.car X.car) := rfl

theorem map_congr {A B C D : Type u} [COFE A] [COFE B] [COFE C] [COFE D]
    {f f' : C -n> A} {g g' : B -n> D} (h1 : ∀ x, f x = f' x) (h2 : ∀ x, g x = g' x) (y : F A B) :
    map (F := F) f g y = map (F := F) f' g' y := by
  rw [Hom.ext (funext h1), Hom.ext (funext h2)]

/-! ## Stages and families of approximations -/

variable (F) in
/-- A stage of the construction at index `γ`: the approximation at `γ`, copies of the earlier
approximations, the embedding-projection pairs from the earlier approximations, and the bounded
isomorphism between `X γ` and `[F (X γ) (X γ)]_{γ + 1}`. -/
structure Stage (γ : SI) where
  X : Obj (SI := SI)
  prev : ∀ β, β < γ → Obj (SI := SI)
  e : ∀ β (h : β < γ), (prev β h).car -n> X.car
  p : ∀ β (h : β < γ), X.car -n> (prev β h).car
  ϕ : X.car -n> (TG F (σ γ) X).car
  ψ : (TG F (σ γ) X).car -n> X.car

variable (F) in
/-- A family of approximations below `γ`, with the maps between them (Rocq: `bounded_approx` for
the predicate `· < γ`, without its laws). `unf` and `fld` are the identifications of
`X (β + 1)` with `[F (X β) (X β)]_{β + 1}`. -/
structure Fam (γ : SI) where
  X : ∀ β, β < γ → Obj (SI := SI)
  e : ∀ β δ (hβ : β < γ) (hδ : δ < γ), β < δ → (X β hβ).car -n> (X δ hδ).car
  p : ∀ β δ (hβ : β < γ) (hδ : δ < γ), β < δ → (X δ hδ).car -n> (X β hβ).car
  ϕ : ∀ β (hβ : β < γ), (X β hβ).car -n> (TG F (σ β) (X β hβ)).car
  ψ : ∀ β (hβ : β < γ), (TG F (σ β) (X β hβ)).car -n> (X β hβ).car
  unf : ∀ β (hβ : β < γ) (hs : σ β < γ), (X (σ β) hs).car -n> (TG F (σ β) (X β hβ)).car
  fld : ∀ β (hβ : β < γ) (hs : σ β < γ), (TG F (σ β) (X β hβ)).car -n> (X (σ β) hs).car

/-- The laws of a family of approximations (Rocq: `is_bounded_approx`). -/
structure FamGood {γ : SI} (f : Fam F γ) : Prop where
  xs β hβ hs : f.X (σ β) hs = TG F (σ β) (f.X β hβ)
  unf_eq β hβ hs : f.unf β hβ hs = castObj (xs β hβ hs)
  fld_eq β hβ hs : f.fld β hβ hs = castObj (xs β hβ hs).symm
  truncated β hβ : Truncated (f.X β hβ).car β
  p_e β δ hβ hδ hlt x : f.p β δ hβ hδ hlt (f.e β δ hβ hδ hlt x) = x
  e_p β δ hβ hδ hlt x : f.e β δ hβ hδ hlt (f.p β δ hβ hδ hlt x) ≡{β}≡ x
  e_funct β η δ hβ hη hδ h1 h2 h3 x :
    f.e η δ hη hδ h2 (f.e β η hβ hη h1 x) = f.e β δ hβ hδ h3 x
  p_funct β η δ hβ hη hδ h1 h2 h3 x :
    f.p β η hβ hη h1 (f.p η δ hη hδ h2 x) = f.p β δ hβ hδ h3 x
  ψ_ϕ β hβ x : f.ψ β hβ (f.ϕ β hβ x) = x
  ϕ_ψ β hβ x : f.ϕ β hβ (f.ψ β hβ x) ≡{β}≡ x
  Fep_p γ0 γ1 h0 h1 hs0 hs1 hlt hlts x :
    f.fld γ0 h0 hs0 (truncMap (σ γ1) (σ γ0)
        (map (F := F) (f.e γ0 γ1 h0 h1 hlt) (f.p γ0 γ1 h0 h1 hlt)) (f.unf γ1 h1 hs1 x)) =
      f.p (σ γ0) (σ γ1) hs0 hs1 hlts x
  p_ψ_unfold β hβ hs hlt x : f.p β (σ β) hβ hs hlt x = f.ψ β hβ (f.unf β hβ hs x)
  e_fold_ϕ β hβ hs hlt x : f.e β (σ β) hβ hs hlt x = f.fld β hβ hs (f.ϕ β hβ x)
  ϕ_succ β hβ hs x :
    f.ϕ (σ β) hs x = truncMap (σ β) (σ (σ β))
      (map (F := F) ((f.ψ β hβ).comp (f.unf β hβ hs)) ((f.fld β hβ hs).comp (f.ϕ β hβ)))
      (f.unf β hβ hs x)
  ψ_succ β hβ hs x :
    f.ψ (σ β) hs x = f.fld β hβ hs (truncMap (σ (σ β)) (σ β)
      (map (F := F) ((f.fld β hβ hs).comp (f.ϕ β hβ)) ((f.ψ β hβ).comp (f.unf β hβ hs))) x)
  Fep_p_limit γ0 γ1 (hlim : SIdx.Limit γ1) h0 hs0 h1 hlt hslt x :
    f.fld γ0 h0 hs0 (truncMap (σ γ1) (σ γ0)
        (map (F := F) (f.e γ0 γ1 h0 h1 hlt) (f.p γ0 γ1 h0 h1 hlt)) x) =
      f.p (σ γ0) γ1 hs0 h1 hslt (f.ψ γ1 h1 x)

/-- The family below `γ` obtained from the stages below `γ`. Maps between the earlier stages are
obtained by casting along the agreement of the copies with the stages, with a junk default. -/
noncomputable def famOf {γ : SI} (IH : ∀ β, β < γ → Stage F β) : Fam F γ where
  X β h := (IH β h).X
  e β δ hβ hδ hlt :=
    if hc : (IH δ hδ).prev β hlt = (IH β hβ).X then
      ((IH δ hδ).e β hlt).comp (castObj hc.symm)
    else constHom default
  p β δ hβ hδ hlt :=
    if hc : (IH δ hδ).prev β hlt = (IH β hβ).X then
      (castObj hc).comp ((IH δ hδ).p β hlt)
    else constHom default
  ϕ β h := (IH β h).ϕ
  ψ β h := (IH β h).ψ
  unf β hβ hs :=
    if hc : (IH (σ β) hs).X = TG F (σ β) (IH β hβ).X then castObj hc else constHom default
  fld β hβ hs :=
    if hc : (IH (σ β) hs).X = TG F (σ β) (IH β hβ).X then castObj hc.symm else constHom default

/-! ### The zero stage -/

variable (F) in
/-- The stage at `0`: `X 0 = [F 1 1]_{0}` (Rocq: `approx_base`). -/
noncomputable def zeroStage : Stage F (0 : SI) :=
  let U := unitObj (SI := SI)
  let X := TG F 0 U
  let ϕ0' : U.car -n> X.car := constHom (truncate 0 inh.default)
  let ψ0' : X.car -n> U.car := constHom ⟨()⟩
  { X := X
    prev := fun β h => absurd h (SIdx.not_lt_zero β)
    e := fun β h => absurd h (SIdx.not_lt_zero β)
    p := fun β h => absurd h (SIdx.not_lt_zero β)
    ϕ := truncMap 0 (σ 0) (map (F := F) ψ0' ϕ0')
    ψ := truncMap (σ 0) 0 (map (F := F) ϕ0' ψ0') }

/-! ### The successor stage -/

theorem lt_of_lt_succ_ne {β m : SI} (h : β < σ m) (hne : β ≠ m) : β < m :=
  (SIdx.le_lteq.mp (SIdx.lt_succ_r.mp h)).resolve_right hne

variable (F) in
/-- The stage at `m + 1`: `X (m + 1) = [F (X m) (X m)]_{m + 1}` (Rocq: `succ_extension`). -/
noncomputable def succStage (m : SI) (f : Fam F (σ m)) : Stage F (σ m) :=
  let hm : m < σ m := SIdx.lt_succ_self m
  let Y := f.X m hm
  { X := TG F (σ m) Y
    prev := f.X
    e := fun β h =>
      if hβ : β = m then (f.ϕ m hm).comp (castObj (by subst hβ; rfl))
      else (f.ϕ m hm).comp (f.e β m h hm (lt_of_lt_succ_ne h hβ))
    p := fun β h =>
      if hβ : β = m then (castObj (by subst hβ; rfl)).comp (f.ψ m hm)
      else (f.p β m h hm (lt_of_lt_succ_ne h hβ)).comp (f.ψ m hm)
    ϕ := truncMap (σ m) (σ (σ m)) (map (F := F) (f.ψ m hm) (f.ϕ m hm))
    ψ := truncMap (σ (σ m)) (σ m) (map (F := F) (f.ϕ m hm) (f.ψ m hm)) }

/-! ### Derived laws of good families -/

namespace FamGood

variable {γ : SI} {f : Fam F γ} (hf : FamGood f)
include hf

theorem unf_fld β hβ hs x : f.unf β hβ hs (f.fld β hβ hs x) = x := by
  rw [hf.unf_eq, hf.fld_eq]; exact castObj_castObj_symm _ _

theorem fld_unf β hβ hs x : f.fld β hβ hs (f.unf β hβ hs x) = x := by
  rw [hf.unf_eq, hf.fld_eq]; exact castObj_symm_castObj _ _

/-- Rocq: `Fep_unfold`. -/
theorem Fep_unfold γ0 γ1 h0 h1 hs0 hs1 hlt hlts x :
    truncMap (σ γ1) (σ γ0) (map (F := F) (f.e γ0 γ1 h0 h1 hlt) (f.p γ0 γ1 h0 h1 hlt))
        (f.unf γ1 h1 hs1 x) =
      f.unf γ0 h0 hs0 (f.p (σ γ0) (σ γ1) hs0 hs1 hlts x) := by
  rw [← hf.Fep_p γ0 γ1 h0 h1 hs0 hs1 hlt hlts x, hf.unf_fld]

/-- Rocq: `fold_Fep`. -/
theorem fold_Fep γ0 γ1 h0 h1 hs0 hs1 hlt hlts y :
    f.fld γ0 h0 hs0 (truncMap (σ γ1) (σ γ0) (map (F := F) (f.e γ0 γ1 h0 h1 hlt) (f.p γ0 γ1 h0 h1 hlt))
        y) =
      f.p (σ γ0) (σ γ1) hs0 hs1 hlts (f.fld γ1 h1 hs1 y) := by
  rw [← hf.Fep_p γ0 γ1 h0 h1 hs0 hs1 hlt hlts, hf.unf_fld]

/-- Rocq: `ψ_p_fold`. -/
theorem ψ_p_fold β hβ hs hlt x : f.ψ β hβ x = f.p β (σ β) hβ hs hlt (f.fld β hβ hs x) := by
  rw [hf.p_ψ_unfold, hf.unf_fld]

/-- Rocq: `ϕ_unfold_e`. -/
theorem ϕ_unfold_e β hβ hs hlt x : f.ϕ β hβ x = f.unf β hβ hs (f.e β (σ β) hβ hs hlt x) := by
  rw [hf.e_fold_ϕ, hf.unf_fld]

end FamGood

/-! ### The limit stage -/

section LimitStage

variable {γ : SI} (hlim : SIdx.Limit γ) (f : Fam F γ)

variable (F) in
/-- The components of the inverse limit: `[F (X β) (X β)]_{β + 1}`, i.e. `X (β + 1)`
(Rocq: `FX`). -/
noncomputable abbrev FX (β : SI) (hβ : β < γ) : Obj (SI := SI) := TG F (σ β) (f.X β hβ)

/-- The maps between the components of the inverse limit (Rocq: `Fep`). -/
noncomputable def Fep (β δ : SI) (hβ : β < γ) (hδ : δ < γ) (hlt : β < δ) :
    (FX F f δ hδ).car -n> (FX F f β hβ).car :=
  truncMap (σ δ) (σ β) (map (F := F) (f.e β δ hβ hδ hlt) (f.p β δ hβ hδ hlt))

/-- The inverse limit of the family below the limit index `γ` (Rocq: `Xβ`, `inv_lim`). -/
@[ext]
structure LimCar where
  val : ∀ β (hβ : β < γ), (FX F f β hβ).car
  coh : ∀ β δ hβ hδ (hlt : β < δ), Fep f β δ hβ hδ hlt (val δ hδ) = val β hβ

noncomputable instance LimCar.instOFE : OFE (LimCar f) where
  Dist n x y := ∀ β hβ, x.val β hβ ≡{n}≡ y.val β hβ
  dist_eqv := {
    refl _ _ _ := .rfl
    symm h β hβ := (h β hβ).symm
    trans h h' β hβ := (h β hβ).trans (h' β hβ)
  }
  eq_dist' := by
    intro x y
    constructor
    · rintro rfl _ _ _; exact .rfl
    · intro h
      refine LimCar.ext (funext fun β => funext fun hβ => ?_)
      exact OFE.eq_dist.mpr fun n => h n β hβ
  dist_lt h hlt β hβ := (h β hβ).lt hlt

theorem LimCar.dist_def {n : SI} {x y : LimCar f} :
    x ≡{n}≡ y ↔ ∀ β hβ, x.val β hβ ≡{n}≡ y.val β hβ := .rfl

include hlim in
/-- The inverse limit is truncated at the limit index (Rocq: `lXβ_truncated`). -/
theorem LimCar.truncated : Truncated (LimCar f) γ where
  eq_of_dist {x y} h := by
    refine LimCar.ext (funext fun β => funext fun hβ => ?_)
    exact Truncated.eq_of_dist_le (A := (FX F f β hβ).car)
      (SIdx.lt_le_incl (hlim.succ_lt β hβ)) (h β hβ)

/-- The projection to a component. -/
def projL (β : SI) (hβ : β < γ) : LimCar f -n> (FX F f β hβ).car :=
  ⟨fun x => x.val β hβ, ⟨fun _ _ _ h => h β hβ⟩⟩

include hlim in
/-- The value of the embedding of `X n` into the inverse limit at the component `β`. -/
noncomputable def eLval (n : SI) (hn : n < γ) (x : (f.X n hn).car) (β : SI) (hβ : β < γ) :
    (FX F f β hβ).car :=
  match SIdx.lt_trichotomyT (σ β) n with
  | .inl h => f.unf β hβ (hlim.succ_lt β hβ) (f.p (σ β) n (hlim.succ_lt β hβ) hn h x)
  | .inr (.inl h) => f.unf β hβ (hlim.succ_lt β hβ)
      (castObj (A := f.X n hn) (B := f.X (σ β) (hlim.succ_lt β hβ)) (by subst h; rfl) x)
  | .inr (.inr h) => f.unf β hβ (hlim.succ_lt β hβ) (f.e n (σ β) hn (hlim.succ_lt β hβ) h x)

theorem eLval_lt {n : SI} (hn : n < γ) (x : (f.X n hn).car) {β : SI} (hβ : β < γ) hs
    (h : σ β < n) : eLval hlim f n hn x β hβ = f.unf β hβ hs (f.p (σ β) n hs hn h x) := by
  unfold eLval; split
  · rfl
  · rename_i h' _; exact absurd (h' ▸ h) (SIdx.lt_irrefl _)
  · rename_i h' _; exact absurd (SIdx.lt_trans h h') (SIdx.lt_irrefl _)

theorem eLval_eq {β : SI} (hβ : β < γ) hs (x : (f.X (σ β) hs).car) :
    eLval hlim f (σ β) hs x β hβ = f.unf β hβ hs x := by
  unfold eLval; split
  · rename_i h _; exact absurd h (SIdx.lt_irrefl _)
  · rfl
  · rename_i h _; exact absurd h (SIdx.lt_irrefl _)

theorem eLval_gt {n : SI} (hn : n < γ) (x : (f.X n hn).car) {β : SI} (hβ : β < γ) hs
    (h : n < σ β) : eLval hlim f n hn x β hβ = f.unf β hβ hs (f.e n (σ β) hn hs h x) := by
  unfold eLval; split
  · rename_i h' _; exact absurd (SIdx.lt_trans h h') (SIdx.lt_irrefl _)
  · rename_i h' _; exact absurd (h' ▸ h) (SIdx.lt_irrefl _)
  · rfl

variable {f} (hf : FamGood f)
include hlim hf

/-- The embedding values form a coherent family (Rocq: `eβ`, equaliser property). -/
theorem eLval_coh (n : SI) (hn : n < γ) (x : (f.X n hn).car) (β δ : SI) (hβ : β < γ) (hδ : δ < γ)
    (hlt : β < δ) :
    Fep f β δ hβ hδ hlt (eLval hlim f n hn x δ hδ) = eLval hlim f n hn x β hβ := by
  have hsβ := hlim.succ_lt β hβ
  have hsδ := hlim.succ_lt δ hδ
  have hlts : σ β < σ δ := SIdx.succ_lt_mono.mp hlt
  rcases SIdx.lt_trichotomyT (σ δ) n with h1 | h1 | h1
  · -- `σ β < σ δ < n`
    rw [eLval_lt hlim f hn x hδ hsδ h1, eLval_lt hlim f hn x hβ hsβ (SIdx.lt_trans hlts h1)]
    unfold Fep
    rw [hf.Fep_unfold β δ hβ hδ hsβ hsδ hlt hlts, hf.p_funct]
  · -- `σ δ = n`
    subst h1
    rw [eLval_eq hlim f hδ hsδ x, eLval_lt hlim f hsδ x hβ hsβ hlts]
    unfold Fep
    rw [hf.Fep_unfold β δ hβ hδ hsβ hsδ hlt hlts]
  · rcases SIdx.lt_trichotomyT (σ β) n with h0 | h0 | h0
    · -- `σ β < n < σ δ`
      rw [eLval_gt hlim f hn x hδ hsδ h1, eLval_lt hlim f hn x hβ hsβ h0]
      unfold Fep
      rw [hf.Fep_unfold β δ hβ hδ hsβ hsδ hlt hlts,
        ← hf.p_funct (σ β) n (σ δ) hsβ hn hsδ h0 h1 hlts, hf.p_e]
    · -- `σ β = n < σ δ`
      subst h0
      rw [eLval_gt hlim f hsβ x hδ hsδ h1, eLval_eq hlim f hβ hsβ x]
      unfold Fep
      rw [hf.Fep_unfold β δ hβ hδ hsβ hsδ hlt hlts, hf.p_e]
    · -- `n < σ β < σ δ`
      rw [eLval_gt hlim f hn x hδ hsδ h1, eLval_gt hlim f hn x hβ hsβ h0]
      unfold Fep
      rw [hf.Fep_unfold β δ hβ hδ hsβ hsδ hlt hlts,
        ← hf.e_funct n (σ β) (σ δ) hn hsβ hsδ h0 hlts h1, hf.p_e]

/-- The embedding of `X n` into the inverse limit (Rocq: `eβ`). -/
noncomputable def eL (n : SI) (hn : n < γ) : (f.X n hn).car -n> LimCar f where
  f x := ⟨eLval hlim f n hn x, fun β δ hβ hδ hlt => eLval_coh hlim hf n hn x β δ hβ hδ hlt⟩
  ne := ⟨fun k x y h β hβ => by
    show eLval hlim f n hn x β hβ ≡{k}≡ eLval hlim f n hn y β hβ
    unfold eLval
    split
    · exact (f.unf _ _ _).ne.1 ((f.p _ _ _ _ _).ne.1 h)
    · exact (f.unf _ _ _).ne.1 ((castObj _).ne.1 h)
    · exact (f.unf _ _ _).ne.1 ((f.e _ _ _ _ _).ne.1 h)⟩

theorem eL_val (n : SI) (hn : n < γ) (x) (β : SI) (hβ : β < γ) :
    (eL hlim hf n hn x).val β hβ = eLval hlim f n hn x β hβ := rfl

omit hlim hf in
/-- The projection of the inverse limit to `X n` (Rocq: `pβ`). -/
noncomputable def pL (f : Fam F γ) (n : SI) (hn : n < γ) : LimCar f -n> (f.X n hn).car :=
  (f.ψ n hn).comp (projL f n hn)

omit hlim hf in
theorem pL_apply (f : Fam F γ) (n : SI) (hn : n < γ) (x : LimCar f) :
    pL f n hn x = f.ψ n hn (x.val n hn) := rfl

/-- Rocq: `eβ_pβ_id`. -/
theorem eL_pL (n : SI) (hn : n < γ) (x : LimCar f) : eL hlim hf n hn (pL f n hn x) ≡{n}≡ x := by
  intro δ hδ
  rw [eL_val, pL_apply]
  have hsδ := hlim.succ_lt δ hδ
  have hsn := hlim.succ_lt n hn
  rcases SIdx.lt_trichotomyT (σ δ) n with h | h | h
  · rw [eLval_lt hlim f hn _ hδ hsδ h, hf.ψ_p_fold n hn hsn (SIdx.lt_succ_self n),
      hf.p_funct (σ δ) n (σ n) hsδ hn hsn h (SIdx.lt_succ_self n)
        (SIdx.lt_trans h (SIdx.lt_succ_self n)),
      ← hf.Fep_unfold δ n hδ hn hsδ hsn (SIdx.succ_lt_mono.mpr (SIdx.lt_trans h (SIdx.lt_succ_self n)))
        (SIdx.lt_trans h (SIdx.lt_succ_self n)),
      hf.unf_fld]
    exact Dist.of_eq (x.coh δ n hδ hn _)
  · subst h
    rw [eLval_eq hlim f hδ hsδ, hf.ψ_p_fold (σ δ) hsδ hsn (SIdx.lt_succ_self _),
      ← hf.Fep_p δ (σ δ) hδ hsδ hsδ hsn (SIdx.lt_succ_self δ) (SIdx.lt_succ_self _),
      hf.unf_fld, hf.unf_fld]
    exact Dist.of_eq (x.coh δ (σ δ) hδ hsδ _)
  · rw [eLval_gt hlim f hn _ hδ hsδ h]
    rcases SIdx.le_lteq.mp (SIdx.lt_succ_r.mp h) with h' | h'
    · -- `n < δ`
      have hlts : σ n < σ δ := SIdx.succ_lt_mono.mp h'
      rw [hf.ψ_p_fold n hn hsn (SIdx.lt_succ_self n),
        ← hf.e_funct n (σ n) (σ δ) hn hsn hsδ (SIdx.lt_succ_self n) hlts h]
      refine ((f.unf δ hδ hsδ).ne.1 ((f.e (σ n) (σ δ) hsn hsδ hlts).ne.1
        (hf.e_p n (σ n) hn hsn _ _))).trans ?_
      rw [← x.coh n δ hn hδ h', Fep, hf.fold_Fep n δ hn hδ hsn hsδ h' hlts]
      refine ((f.unf δ hδ hsδ).ne.1 ((hf.e_p (σ n) (σ δ) hsn hsδ hlts _).le
        (SIdx.lt_le_incl (SIdx.lt_succ_self n)))).trans ?_
      rw [hf.unf_fld]
      exact .rfl
    · -- `n = δ`
      subst h'
      rw [hf.e_fold_ϕ, hf.unf_fld]
      exact hf.ϕ_ψ n hn _

/-- Rocq: `pβ_eβ_id`. -/
theorem pL_eL (n : SI) (hn : n < γ) (x) : pL f n hn (eL hlim hf n hn x) = x := by
  rw [pL_apply, eL_val, eLval_gt hlim f hn x hn (hlim.succ_lt n hn) (SIdx.lt_succ_self n),
    ← hf.p_ψ_unfold n hn _ (SIdx.lt_succ_self n), hf.p_e]

/-- Rocq: `eβ_functorial`. -/
theorem eL_functorial (n0 n1 : SI) (h0 : n0 < γ) (h1 : n1 < γ) (hlt : n0 < n1) (x) :
    eL hlim hf n0 h0 x = eL hlim hf n1 h1 (f.e n0 n1 h0 h1 hlt x) := by
  refine LimCar.ext (funext fun β => funext fun hβ => ?_)
  rw [eL_val, eL_val]
  have hsβ := hlim.succ_lt β hβ
  rcases SIdx.lt_trichotomyT (σ β) n0 with h | h | h
  · rw [eLval_lt hlim f h0 x hβ hsβ h, eLval_lt hlim f h1 _ hβ hsβ (SIdx.lt_trans h hlt),
      ← hf.p_funct (σ β) n0 n1 hsβ h0 h1 h hlt, hf.p_e]
  · subst h
    rw [eLval_eq hlim f hβ hsβ, eLval_lt hlim f h1 _ hβ hsβ hlt, hf.p_e]
  · rcases SIdx.lt_trichotomyT (σ β) n1 with h' | h' | h'
    · rw [eLval_gt hlim f h0 x hβ hsβ h, eLval_lt hlim f h1 _ hβ hsβ h',
        ← hf.e_funct n0 (σ β) n1 h0 hsβ h1 h h' hlt, hf.p_e]
    · subst h'
      rw [eLval_gt hlim f h0 x hβ hsβ h, eLval_eq hlim f hβ hsβ]
    · rw [eLval_gt hlim f h0 x hβ hsβ h, eLval_gt hlim f h1 _ hβ hsβ h',
        hf.e_funct n0 n1 (σ β) h0 h1 hsβ hlt h' h]

omit hlim in
/-- Rocq: `pβ_functorial`. -/
theorem pL_functorial (n0 n1 : SI) (h0 : n0 < γ) (h1 : n1 < γ) (hlt : n0 < n1)
    (hs0 : σ n0 < γ) (hs1 : σ n1 < γ) (x : LimCar f) :
    pL f n0 h0 x = f.p n0 n1 h0 h1 hlt (pL f n1 h1 x) := by
  have hlts : σ n0 < σ n1 := SIdx.succ_lt_mono.mp hlt
  rw [pL_apply, pL_apply, hf.ψ_p_fold n0 h0 hs0 (SIdx.lt_succ_self n0), ← x.coh n0 n1 h0 h1 hlt,
    Fep, hf.fold_Fep n0 n1 h0 h1 hs0 hs1 hlt hlts,
    hf.p_funct n0 (σ n0) (σ n1) h0 hs0 hs1 (SIdx.lt_succ_self n0) hlts
      (SIdx.lt_trans (SIdx.lt_succ_self n0) hlts),
    ← hf.p_funct n0 n1 (σ n1) h0 h1 hs1 hlt (SIdx.lt_succ_self n1)
      (SIdx.lt_trans (SIdx.lt_succ_self n0) hlts),
    ← hf.ψ_p_fold n1 h1 hs1 (SIdx.lt_succ_self n1)]

/-! ### The COFE structure of the inverse limit -/

omit hf in
/-- The completion of a bounded chain of the full length `γ`: its components stabilize. -/
noncomputable def limStab {n : SI} (hγn : γ = n) (c : BChain (LimCar f) n) : LimCar f where
  val β hβ := (c.bchain (σ β) (hγn ▸ hlim.succ_lt β hβ)).val β hβ
  coh β δ hβ hδ hlt := by
    rw [(c.bchain (σ δ) _).coh β δ hβ hδ hlt]
    exact Truncated.eq_of_dist (A := (FX F f β hβ).car) (α := σ β)
      (c.bcauchy (hγn ▸ hlim.succ_lt β hβ) (hγn ▸ hlim.succ_lt δ hδ)
        (SIdx.lt_le_incl (SIdx.succ_lt_mono.mp hlt)) β hβ)

/-- The completion of bounded chains in the inverse limit. -/
noncomputable def limLb {n : SI} (hn : SIdx.Limit n) (c : BChain (LimCar f) n) : LimCar f :=
  match SIdx.lt_trichotomyT γ n with
  | .inl h => c.bchain γ h
  | .inr (.inl h) => limStab hlim h c
  | .inr (.inr h) => eL hlim hf n h (IsCOFE.lbcompl hn (c.map (pL f n h)))

theorem limLb_lt {n : SI} (hn : SIdx.Limit n) (c : BChain (LimCar f) n) (h : γ < n) :
    limLb hlim hf hn c = c.bchain γ h := by
  unfold limLb; split
  · rfl
  · rename_i h' _; exact absurd (h' ▸ h) (SIdx.lt_irrefl _)
  · rename_i h' _; exact absurd (SIdx.lt_trans h h') (SIdx.lt_irrefl _)

theorem limLb_eq {n : SI} (hn : SIdx.Limit n) (c : BChain (LimCar f) n) (h : γ = n) :
    limLb hlim hf hn c = limStab hlim h c := by
  unfold limLb; split
  · rename_i h' _; exact absurd (h ▸ h') (SIdx.lt_irrefl _)
  · rfl
  · rename_i h' _; exact absurd (h ▸ h') (SIdx.lt_irrefl _)

theorem limLb_gt {n : SI} (hn : SIdx.Limit n) (c : BChain (LimCar f) n) (h : n < γ) :
    limLb hlim hf hn c = eL hlim hf n h (IsCOFE.lbcompl hn (c.map (pL f n h))) := by
  unfold limLb; split
  · rename_i h' _; exact absurd (SIdx.lt_trans h h') (SIdx.lt_irrefl _)
  · rename_i h' _; exact absurd (h' ▸ h) (SIdx.lt_irrefl _)
  · rfl

/-- The inverse limit is a COFE. Unlike the components, it is not closed under componentwise
limits of bounded chains of length `n < γ`; those are obtained by embedding the limit in `X n`. -/
@[reducible] noncomputable def LimCar.instCOFE : IsCOFE (LimCar f) where
  compl c := c γ
  conv_compl {n c} := by
    rcases SIdx.le_total (n := n) (m := γ) with h | h
    · exact c.cauchy h
    · exact Dist.of_eq ((LimCar.truncated hlim f).eq_of_dist (c.cauchy h)).symm
  lbcompl hn c := limLb hlim hf hn c
  conv_lbcompl {n} hn c m hm := by
    rcases SIdx.lt_trichotomyT γ n with h | h | h
    · rw [limLb_lt hlim hf hn c h]
      rcases SIdx.le_total (n := m) (m := γ) with h' | h'
      · exact c.bcauchy hm h h'
      · exact Dist.of_eq ((LimCar.truncated hlim f).eq_of_dist (c.bcauchy h hm h')).symm
    · rw [limLb_eq hlim hf hn c h]
      intro β hβ
      show (c.bchain (σ β) _).val β hβ ≡{m}≡ (c.bchain m hm).val β hβ
      rcases SIdx.le_total (n := σ β) (m := m) with h' | h'
      · exact Dist.of_eq (Truncated.eq_of_dist (A := (FX F f β hβ).car) (α := σ β)
          (c.bcauchy _ hm h' β hβ)).symm
      · exact c.bcauchy hm _ h' β hβ
    · rw [limLb_gt hlim hf hn c h]
      refine ((eL hlim hf n h).ne.1 (IsCOFE.conv_lbcompl hn _ hm)).trans ?_
      exact (eL_pL hlim hf n h _).lt hm
  lbcompl_ne {n} hn c1 c2 m hc := by
    rcases SIdx.lt_trichotomyT γ n with h | h | h
    · rw [limLb_lt hlim hf hn c1 h, limLb_lt hlim hf hn c2 h]; exact hc γ h
    · rw [limLb_eq hlim hf hn c1 h, limLb_eq hlim hf hn c2 h]
      intro β hβ; exact hc _ _ β hβ
    · rw [limLb_gt hlim hf hn c1 h, limLb_gt hlim hf hn c2 h]
      exact (eL hlim hf n h).ne.1 (IsCOFE.lbcompl_ne hn _ _ fun p hp => (pL f n h).ne.1 (hc p hp))

/-- The inverse limit, bundled. -/
noncomputable def LimObj : Obj (SI := SI) :=
  letI := LimCar.instCOFE hlim hf
  letI : Inhabited (LimCar f) := ⟨eL hlim hf 0 hlim.limit_lt_0 default⟩
  ⟨LimCar f⟩

theorem LimObj_car : (LimObj hlim hf).car = LimCar f := rfl

/-- `eL` as a map into the bundled inverse limit. -/
noncomputable def eL' (n : SI) (hn : n < γ) : (f.X n hn).car -n> (LimObj hlim hf).car :=
  eL hlim hf n hn

/-- `pL` as a map out of the bundled inverse limit. -/
noncomputable def pL' (n : SI) (hn : n < γ) : (LimObj hlim hf).car -n> (f.X n hn).car :=
  pL f n hn

/-! ### The maps between the inverse limit and `[F L L]_{γ}` -/

/-- Rocq: `ψβ`. -/
noncomputable def ψL : (TG F γ (LimObj hlim hf)).car -n> LimCar f where
  f x := {
    val := fun β hβ => truncMap γ (σ β) (map (F := F) (eL' hlim hf β hβ) (pL' hlim hf β hβ)) x
    coh := fun β δ hβ hδ hlt => by
      rw [Fep]
      refine Truncated.eq_of_dist (A := (FX F f β hβ).car) (α := σ β) ?_
      refine ((truncMap_comp_dist γ (σ β) (σ δ) _ _ x).symm.le
        (SIdx.lt_le_incl (SIdx.succ_lt_mono.mp hlt))).trans (Dist.of_eq ?_)
      congr 2
      refine Hom.ext (funext fun y => ?_)
      rw [Hom.comp_apply, ← OFunctor.map_comp]
      congr 2
      · exact Hom.ext (funext fun z => (eL_functorial hlim hf β δ hβ hδ hlt z).symm)
      · exact Hom.ext (funext fun z => (pL_functorial hf β δ hβ hδ hlt (hlim.succ_lt β hβ)
          (hlim.succ_lt δ hδ) z).symm) }
  ne := ⟨fun _ _ _ h β hβ => (truncMap _ _ _).ne.1 h⟩

/-- The bounded chain whose limit is `ϕL x` (Rocq: the chain in `ϕβ`). -/
noncomputable def ϕLchain (x : LimCar f) : BChain (TG F γ (LimObj hlim hf)).car γ where
  bchain β hβ := truncMap (σ β) γ (map (F := F) (pL' hlim hf β hβ) (eL' hlim hf β hβ)) (x.val β hβ)
  bcauchy {m p} hm hp h := by
    rcases SIdx.le_lteq.mp h with h | rfl
    · -- rewrite the `m`-th component as the image of the `p`-th one
      rw [← x.coh m p hm hp h, Fep]
      have H1 : (map (F := F) (pL' hlim hf p hp) (eL' hlim hf p hp)) ≡{m}≡
          ((map (F := F) (pL' hlim hf m hm) (eL' hlim hf m hm)).comp
            (map (F := F) (f.e m p hm hp h) (f.p m p hm hp h))) := by
        intro y
        rw [Hom.comp_apply, ← OFunctor.map_comp]
        refine OFunctor.map_ne.ne (fun z => ?_) (fun z => ?_) y
        · show pL f p hp z ≡{m}≡ f.e m p hm hp h (pL f m hm z)
          have e1 : f.e m p hm hp h (pL f m hm z) =
              f.e m p hm hp h (f.p m p hm hp h (pL f p hp z)) :=
            congrArg _ (pL_functorial hf m p hm hp h (hlim.succ_lt m hm) (hlim.succ_lt p hp) z)
          exact ((Dist.of_eq e1).trans (hf.e_p m p hm hp h _)).symm
        · show eL hlim hf p hp z ≡{m}≡ eL hlim hf m hm (f.p m p hm hp h z)
          rw [eL_functorial hlim hf m p hm hp h]
          exact (eL hlim hf p hp).ne.1 (hf.e_p m p hm hp h z).symm
      exact ((truncMap_ne (σ p) γ).ne H1 (x.val p hp)).trans
        ((truncMap_comp_dist (σ p) γ (σ m) _ _ (x.val p hp)).le
          (SIdx.lt_le_incl (SIdx.lt_succ_self m)))
    · exact .rfl

/-- `ψL` as a map into the bundled inverse limit. -/
noncomputable def ψL' : (TG F γ (LimObj hlim hf)).car -n> (LimObj hlim hf).car := ψL hlim hf

variable [∀ α [COFE α], BcomplUniqueLim (F α α)]

/-- Rocq: `ϕβ`. -/
noncomputable def ϕL : (LimObj hlim hf).car -n> (TG F γ (LimObj hlim hf)).car where
  f x := IsCOFE.lbcompl hlim (ϕLchain hlim hf x)
  ne := ⟨fun k x y h => by
    have hc : ∀ β hβ, k ≤ β → ∀ (hk : k ≤ β),
        (ϕLchain hlim hf x).bchain β hβ ≡{k}≡ (ϕLchain hlim hf y).bchain β hβ := by
      intro β hβ _ _
      exact (truncMap _ _ _).ne.1 (h β hβ)
    rcases SIdx.lt_trichotomyT k γ with hk | hk | hk
    · refine (IsCOFE.conv_lbcompl hlim _ hk).trans ?_
      refine .trans ?_ (IsCOFE.conv_lbcompl hlim _ hk).symm
      exact (truncMap _ _ _).ne.1 (h k hk)
    · subst hk
      exact BcomplUniqueLim.lbcompl_unique hlim _ _ fun β hβ =>
        (truncMap _ _ _).ne.1 ((h β hβ).lt hβ)
    · refine Truncated.dist_of_dist_le (A := (TG F γ (LimObj hlim hf)).car) (α := γ)
        (SIdx.lt_le_incl hk) ?_
      exact BcomplUniqueLim.lbcompl_unique hlim _ _ fun β hβ =>
        (truncMap _ _ _).ne.1 ((h β hβ).le (SIdx.lt_le_incl (SIdx.lt_trans hβ hk)))⟩

/-- The embeddings into the new limit approximation `[F L L]_{γ}` (Rocq: `eβ'`). -/
noncomputable abbrev eS (β : SI) (hβ : β < γ) : (f.X β hβ).car -n> (TG F γ (LimObj hlim hf)).car :=
  (ϕL hlim hf).comp (eL' hlim hf β hβ)

/-- The projections out of the new limit approximation (Rocq: `pβ'`). -/
noncomputable abbrev pS (β : SI) (hβ : β < γ) : (TG F γ (LimObj hlim hf)).car -n> (f.X β hβ).car :=
  (pL' hlim hf β hβ).comp (ψL' hlim hf)

/-- Rocq: `ϕβ'`. -/
noncomputable abbrev ϕS :
    (TG F γ (LimObj hlim hf)).car -n> (TG F (σ γ) (TG F γ (LimObj hlim hf))).car :=
  truncMap γ (σ γ) (map (F := F) (ψL' hlim hf) (ϕL hlim hf))

/-- Rocq: `ψβ'`. -/
noncomputable abbrev ψS :
    (TG F (σ γ) (TG F γ (LimObj hlim hf))).car -n> (TG F γ (LimObj hlim hf)).car :=
  truncMap (σ γ) γ (map (F := F) (ϕL hlim hf) (ψL' hlim hf))

variable (F) in
/-- The stage at the limit index `γ`: `X γ = [F L L]_{γ}` for the inverse limit `L`
(Rocq: `limit_extension`). -/
noncomputable def limitStage : Stage F γ where
  X := TG F γ (LimObj hlim hf)
  prev := f.X
  e := eS hlim hf
  p := pS hlim hf
  ϕ := ϕS hlim hf
  ψ := ψS hlim hf

end LimitStage

section LimitStageLaws

variable {γ : SI} (hlim : SIdx.Limit γ) {f : Fam F γ} (hf : FamGood f)
variable [∀ α [COFE α], BcomplUniqueLim (F α α)]

/-! ### Laws of the limit stage -/

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
/-- Rocq: `pβ_eβ_up`. -/
theorem pL_eL_up (β β' : SI) (hβ : β < γ) (hβ' : β' < γ) (hlt : β < β') (x) :
    pL f β' hβ' (eL hlim hf β hβ x) = f.e β β' hβ hβ' hlt x := by
  rw [eL_functorial hlim hf β β' hβ hβ' hlt, pL_eL]

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
/-- Rocq: `pβ_eβ_down`. -/
theorem pL_eL_down (β' β : SI) (hβ' : β' < γ) (hβ : β < γ) (hlt : β' < β) (x) :
    pL f β' hβ' (eL hlim hf β hβ x) = f.p β' β hβ' hβ hlt x := by
  rw [pL_functorial hf β' β hβ' hβ hlt (hlim.succ_lt β' hβ') (hlim.succ_lt β hβ), pL_eL]

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
theorem ψL_val (y) (β : SI) (hβ : β < γ) :
    (ψL hlim hf y).val β hβ = truncMap γ (σ β) (map (F := F) (eL' hlim hf β hβ) (pL' hlim hf β hβ)) y :=
  rfl

/-- Rocq: `ψβ_ϕβ_id`. -/
theorem ψL_ϕL (x : LimCar f) : ψL hlim hf (ϕL hlim hf x) = x := by
  refine LimCar.ext (funext fun β => funext fun hβ => ?_)
  have hs := hlim.succ_lt β hβ
  rw [ψL_val]
  refine Truncated.eq_of_dist (A := (FX F f β hβ).car) (α := σ β) ?_
  refine ((truncMap γ (σ β) _).ne.1 (IsCOFE.conv_lbcompl hlim (ϕLchain hlim hf x) hs)).trans
    (Dist.of_eq ?_)
  show truncMap γ (σ β) _ (truncMap (σ (σ β)) γ _ (x.val (σ β) hs)) = _
  rw [truncMap_truncMap (SIdx.lt_le_incl hs)]
  rw [← x.coh β (σ β) hβ hs (SIdx.lt_succ_self β), Fep]
  refine truncMap_congr (fun y => ?_) _
  rw [Hom.comp_apply, ← OFunctor.map_comp]
  exact map_congr (fun z => pL_eL_up hlim hf β (σ β) hβ hs (SIdx.lt_succ_self β) z)
    (fun z => pL_eL_down hlim hf β (σ β) hβ hs (SIdx.lt_succ_self β) z) y

/-- Rocq: `ϕβ_ψβ_id`. -/
theorem ϕL_ψL (y) (k : SI) (hk : k < γ) : ϕL hlim hf (ψL' hlim hf y) ≡{k}≡ y := by
  refine (IsCOFE.conv_lbcompl hlim (ϕLchain hlim hf (ψL hlim hf y)) hk).trans ?_
  show truncMap (σ k) γ _ (truncMap γ (σ k) _ y) ≡{k}≡ y
  refine ((truncMap_comp_dist γ γ (σ k) _ _ y).symm.le (SIdx.lt_le_incl (SIdx.lt_succ_self k))).trans ?_
  refine (((truncMap_ne γ γ).ne (n := k) (fun z => ?_)) y).trans (Dist.of_eq (truncMap_id γ y))
  rw [Hom.comp_apply, ← OFunctor.map_comp]
  refine ((OFunctor.map_ne.ne (fun w => ?_) (fun w => ?_) z).trans (Dist.of_eq (OFunctor.map_id z)))
  · exact eL_pL hlim hf k hk w
  · exact eL_pL hlim hf k hk w

/-- Rocq: `Fep_p_limit` (for the inverse limit). -/
theorem fld_truncMap_eL (γ0 : SI) (h0 : γ0 < γ) (hs0 : σ γ0 < γ) (y) :
    f.fld γ0 h0 hs0 (truncMap γ (σ γ0) (map (F := F) (eL' hlim hf γ0 h0) (pL' hlim hf γ0 h0)) y) =
      pL f (σ γ0) hs0 (ψL hlim hf y) := by
  rw [pL_apply, ψL_val, hf.ψ_succ γ0 h0 hs0, truncMap_truncMap
    (SIdx.lt_le_incl (SIdx.lt_succ_self (σ γ0)))]
  congr 1
  refine truncMap_congr (fun y => ?_) _
  rw [Hom.comp_apply, ← OFunctor.map_comp]
  refine map_congr (fun z => ?_) (fun z => ?_) y
  · show eL hlim hf γ0 h0 z = eL hlim hf (σ γ0) hs0 (f.fld γ0 h0 hs0 (f.ϕ γ0 h0 z))
    rw [← hf.e_fold_ϕ γ0 h0 hs0 (SIdx.lt_succ_self γ0), ← eL_functorial]
  · show pL f γ0 h0 z = f.ψ γ0 h0 (f.unf γ0 h0 hs0 (pL f (σ γ0) hs0 z))
    exact (pL_functorial hf γ0 (σ γ0) h0 hs0 (SIdx.lt_succ_self γ0) hs0 (hlim.succ_lt _ hs0) z).trans
      (hf.p_ψ_unfold γ0 h0 hs0 (SIdx.lt_succ_self γ0) _)

/-- Rocq: `ψβ'_ϕβ'_id`. -/
theorem ψS_ϕS (x : (TG F γ (LimObj hlim hf)).car) : ψS hlim hf (ϕS hlim hf x) = x := by
  show truncMap (σ γ) γ _ (truncMap γ (σ γ) _ x) = x
  rw [truncMap_truncMap (SIdx.lt_le_incl (SIdx.lt_succ_self γ))]
  refine (truncMap_congr (fun y => ?_) x).trans (truncMap_id γ x)
  rw [Hom.comp_apply, ← OFunctor.map_comp]
  exact (map_congr (f' := Hom.id) (g' := Hom.id)
    (fun (z : (LimObj hlim hf).car) => (ψL_ϕL hlim hf z : ψL' hlim hf (ϕL hlim hf z) = z))
    (fun (z : (LimObj hlim hf).car) => (ψL_ϕL hlim hf z : ψL' hlim hf (ϕL hlim hf z) = z)) y).trans
    (OFunctor.map_id y)

/-- Rocq: `ϕβ'_ψβ'_id`. -/
theorem ϕS_ψS (x) : ϕS hlim hf (ψS hlim hf x) ≡{γ}≡ x := by
  show truncMap γ (σ γ) _ (truncMap (σ γ) γ _ x) ≡{γ}≡ x
  refine (truncMap_comp_dist (σ γ) (σ γ) γ _ _ x).symm.trans ?_
  refine (((truncMap_ne (σ γ) (σ γ)).ne (n := γ) (fun y => ?_)) x).trans
    (Dist.of_eq (truncMap_id (σ γ) x))
  show map (F := F) _ _ (map (F := F) _ _ y) ≡{γ}≡ y
  rw [← OFunctor.map_comp]
  refine ((OFunctorContractive.map_contractive (F := F)).distLater_dist
    (x := (((ϕL hlim hf).comp (ψL' hlim hf)), ((ϕL hlim hf).comp (ψL' hlim hf))))
    (y := (Hom.id, Hom.id)) (fun k hk => ⟨fun z => ϕL_ψL hlim hf z k hk,
      fun z => ϕL_ψL hlim hf z k hk⟩) y).trans (Dist.of_eq (OFunctor.map_id y))

/-- Rocq: `pβ'_eβ'_id`. -/
theorem pS_eS (β : SI) (hβ : β < γ) (x) : pS hlim hf β hβ (eS hlim hf β hβ x) = x :=
  (congrArg (pL f β hβ) (ψL_ϕL hlim hf (eL hlim hf β hβ x))).trans (pL_eL hlim hf β hβ x)

/-- Rocq: `eβ'_pβ'_id`. -/
theorem eS_pS (β : SI) (hβ : β < γ) (y) : eS hlim hf β hβ (pS hlim hf β hβ y) ≡{β}≡ y :=
  ((ϕL hlim hf).ne.1 (eL_pL hlim hf β hβ _)).trans (ϕL_ψL hlim hf y β hβ)

/-- Rocq: `eβ'_functorial`. -/
theorem eS_functorial (β β' : SI) (hβ : β < γ) (hβ' : β' < γ) (hlt : β < β') (x) :
    eS hlim hf β' hβ' (f.e β β' hβ hβ' hlt x) = eS hlim hf β hβ x :=
  congrArg (ϕL hlim hf) (eL_functorial hlim hf β β' hβ hβ' hlt x).symm

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
/-- Rocq: `pβ'_functorial`. -/
theorem pS_functorial (β β' : SI) (hβ : β < γ) (hβ' : β' < γ) (hlt : β < β') (y) :
    f.p β β' hβ hβ' hlt (pS hlim hf β' hβ' y) = pS hlim hf β hβ y :=
  (pL_functorial hf β β' hβ hβ' hlt (hlim.succ_lt β hβ) (hlim.succ_lt β' hβ') _).symm

/-- Rocq: `Fep_p_limit0`. -/
theorem fld_truncMap_eS (γ0 : SI) (h0 : γ0 < γ) (hs0 : σ γ0 < γ) (x) :
    f.fld γ0 h0 hs0 (truncMap (σ γ) (σ γ0) (map (F := F) (eS hlim hf γ0 h0) (pS hlim hf γ0 h0)) x) =
      pS hlim hf (σ γ0) hs0 (ψS hlim hf x) := by
  refine Eq.trans ?_ (fld_truncMap_eL hlim hf γ0 h0 hs0 _)
  congr 1
  show _ = truncMap γ (σ γ0) _ (truncMap (σ γ) γ _ x)
  rw [truncMap_truncMap (SIdx.lt_le_incl (hlim.succ_lt γ0 h0))]
  refine truncMap_congr (fun y => ?_) x
  rw [Hom.comp_apply, ← OFunctor.map_comp]

end LimitStageLaws

/-! ## The recursion -/

variable [∀ α [COFE α], BcomplUniqueLim (F α α)]

variable (F) in
/-- A junk stage, used at limit indices whose earlier stages do not satisfy the laws (which never
happens). -/
noncomputable def junkStage (γ : SI) (IH : ∀ β, β < γ → Stage F β) : Stage F γ where
  X := unitObj
  prev β h := (IH β h).X
  e _ _ := constHom default
  p _ _ := constHom default
  ϕ := constHom default
  ψ := constHom default

variable (F) in
/-- One step of the recursion. -/
noncomputable def step (γ : SI) (IH : ∀ β, β < γ → Stage F β) : Stage F γ :=
  match SIdx.case γ with
  | .inl h => by subst h; exact zeroStage F
  | .inr (.inl ⟨m, h⟩) => by subst h; exact succStage F m (famOf IH)
  | .inr (.inr hlim) =>
    if hf : FamGood (famOf IH) then limitStage F hlim hf else junkStage F γ IH

theorem step_zero (IH : ∀ β, β < (0 : SI) → Stage F β) : step F 0 IH = zeroStage F := by
  unfold step
  split
  · rfl
  · rename_i h _; exact absurd h.symm SIdx.neq_succ_0
  · rename_i h _; exact absurd h SIdx.limit_0

theorem step_succ (m : SI) (IH : ∀ β, β < σ m → Stage F β) :
    step F (σ m) IH = succStage F m (famOf IH) := by
  unfold step
  split
  · rename_i h _; exact absurd h SIdx.neq_succ_0
  · rename_i m' h _
    obtain rfl := SIdx.succ_inj h
    rfl
  · rename_i h _; exact absurd h (SIdx.limit_S m)

theorem step_limit {γ : SI} (hlim : SIdx.Limit γ) (IH : ∀ β, β < γ → Stage F β)
    (hf : FamGood (famOf IH)) : step F γ IH = limitStage F hlim hf := by
  unfold step
  split
  · rename_i h _; exact absurd (h ▸ hlim) SIdx.limit_0
  · rename_i m h _; exact absurd (h ▸ hlim) (SIdx.limit_S m)
  · exact dite_eq_left hf

theorem step_limit_junk {γ : SI} (hlim : SIdx.Limit γ) (IH : ∀ β, β < γ → Stage F β)
    (hf : ¬ FamGood (famOf IH)) : step F γ IH = junkStage F γ IH := by
  unfold step
  split
  · rename_i h _; exact absurd (h ▸ hlim) SIdx.limit_0
  · rename_i m h _; exact absurd (h ▸ hlim) (SIdx.limit_S m)
  · exact dite_eq_right hf

variable (F) in
/-- The stages of the construction. -/
noncomputable def stage : ∀ γ : SI, Stage F γ := instSI.lt_wf.fix (step F)

theorem stage_eq (γ : SI) : stage F γ = step F γ (fun β _ => stage F β) :=
  instSI.lt_wf.fix_eq _ γ

/-! ## The approximations -/

variable (F) in
/-- The approximation at `γ`. -/
noncomputable abbrev X (γ : SI) : Obj (SI := SI) := (stage F γ).X

/-- The copies of earlier approximations in a stage agree with the earlier stages. -/
theorem prev_eq (γ β : SI) (h : β < γ) : (stage F γ).prev β h = X F β := by
  rw [stage_eq (F := F) γ]
  rcases SIdx.case γ with h0 | ⟨m, rfl⟩ | hlim
  · subst h0; exact absurd h (SIdx.not_lt_zero β)
  · rw [step_succ]; rfl
  · by_cases hf : FamGood (famOf (fun β (_ : β < γ) => stage F β))
    · rw [step_limit hlim _ hf]; rfl
    · rw [step_limit_junk hlim _ hf]; rfl

theorem stage_succ (m : SI) :
    stage F (σ m) = succStage F m (famOf (fun β (_ : β < σ m) => stage F β)) := by
  rw [stage_eq (F := F) (σ m), step_succ]

/-- `X (m + 1) = [F (X m) (X m)]_{m + 1}` (Rocq: `approx_eq`). -/
theorem X_succ (m : SI) : X F (σ m) = TG F (σ m) (X F m) := by
  show (stage F (σ m)).X = _
  rw [stage_succ]; rfl

variable (F) in
/-- The embeddings between approximations. -/
noncomputable def e (β γ : SI) (h : β < γ) : (X F β).car -n> (X F γ).car :=
  ((stage F γ).e β h).comp (castObj (prev_eq γ β h).symm)

variable (F) in
/-- The projections between approximations. -/
noncomputable def p (β γ : SI) (h : β < γ) : (X F γ).car -n> (X F β).car :=
  (castObj (prev_eq γ β h)).comp ((stage F γ).p β h)

variable (F) in
/-- The bounded isomorphism `X γ ≅ [F (X γ) (X γ)]_{γ + 1}`. -/
noncomputable def ϕ (γ : SI) : (X F γ).car -n> (TG F (σ γ) (X F γ)).car := (stage F γ).ϕ

variable (F) in
noncomputable def ψ (γ : SI) : (TG F (σ γ) (X F γ)).car -n> (X F γ).car := (stage F γ).ψ

variable (F) in
/-- The identification `X (m + 1) → [F (X m) (X m)]_{m + 1}` (Rocq: `unfold`). -/
noncomputable def unfold (m : SI) : (X F (σ m)).car -n> (TG F (σ m) (X F m)).car :=
  castObj (X_succ m)

variable (F) in
/-- The identification `[F (X m) (X m)]_{m + 1} → X (m + 1)` (Rocq: `fold`). -/
noncomputable def fold (m : SI) : (TG F (σ m) (X F m)).car -n> (X F (σ m)).car :=
  castObj (X_succ m).symm

@[simp] theorem unfold_fold (m : SI) (x) : unfold F m (fold F m x) = x :=
  castObj_castObj_symm _ _

@[simp] theorem fold_unfold (m : SI) (x) : fold F m (unfold F m x) = x :=
  castObj_symm_castObj _ _

/-- The family of all approximations below `γ`. -/
noncomputable abbrev famBelow (γ : SI) : Fam F γ := famOf (fun β (_ : β < γ) => stage F β)

theorem famBelow_e (γ β δ : SI) hβ hδ hlt :
    (famBelow (F := F) γ).e β δ hβ hδ hlt = e F β δ hlt :=
  dite_eq_left (prev_eq δ β hlt)

theorem famBelow_p (γ β δ : SI) hβ hδ hlt :
    (famBelow (F := F) γ).p β δ hβ hδ hlt = p F β δ hlt :=
  dite_eq_left (prev_eq δ β hlt)

theorem famBelow_unf (γ β : SI) hβ hs :
    (famBelow (F := F) γ).unf β hβ hs = unfold F β :=
  dite_eq_left (X_succ β)

theorem famBelow_fld (γ β : SI) hβ hs :
    (famBelow (F := F) γ).fld β hβ hs = fold F β :=
  dite_eq_left (X_succ β)

end Iris.COFE.OFunctor.Transfinite
