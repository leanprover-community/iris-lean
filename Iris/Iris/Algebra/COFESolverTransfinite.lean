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

universe u v

variable {SI : Type v} [instSI : SIdx SI]
local stepindex SI

local notation "σ" => SIdx.succ

attribute [local instance low] Classical.propDecidable

/-! ## Bundled COFEs -/

/-- An inhabited COFE, bundled. -/
structure Obj where
  car : Type (max u v)
  [cofe : COFE (SI := SI) car]
  [inh : Inhabited car]

attribute [local instance] Obj.cofe Obj.inh

/-- Casting along an equality of bundled COFEs. -/
def castObj {A B : Obj.{u} (SI := SI)} (h : A = B) : A.car -n> B.car := h ▸ Hom.id

theorem castObj_rfl {A : Obj.{u} (SI := SI)} (x : A.car) : castObj (rfl : A = A) x = x := rfl

theorem castObj_castObj {A B C : Obj.{u} (SI := SI)} (h1 : A = B) (h2 : B = C) (x : A.car) :
    castObj h2 (castObj h1 x) = castObj (h1.trans h2) x := by
  subst h1 h2; rfl

theorem castObj_symm_castObj {A B : Obj.{u} (SI := SI)} (h : A = B) (x : A.car) :
    castObj h.symm (castObj h x) = x := by
  subst h; rfl

theorem castObj_castObj_symm {A B : Obj.{u} (SI := SI)} (h : A = B) (x : B.car) :
    castObj h (castObj h.symm x) = x := by
  subst h; rfl

theorem castObj_heq {A B : Obj.{u} (SI := SI)} (h : A = B) (x : A.car) : HEq (castObj h x) x := by
  subst h; rfl

/-- A constant non-expansive map. -/
def constHom {A B : Type _} [OFE A] [OFE B] (y : B) : A -n> B := ⟨fun _ => y, ⟨fun _ _ _ _ => .rfl⟩⟩

theorem constHom_apply {A B : Type _} [OFE A] [OFE B] (y : B) (x : A) :
    constHom y x = y := rfl

/-! ## The functor -/

variable {F : ∀ α β [COFE α] [COFE β], Type (max u v)} [OFunctorContractive F]
variable [∀ α [COFE α], IsCOFE (F α α)]
variable [inh : Inhabited (F (ULift Unit) (ULift Unit))]

/-- The unit COFE, bundled. -/
def unitObj : Obj.{u} (SI := SI) := ⟨ULift Unit⟩

/-- The functor is inhabited on every inhabited COFE. -/
@[local instance] def Finh {A : Type (max u v)} [COFE A] [Inhabited A] : Inhabited (F A A) :=
  ⟨map (F := F) (constHom ⟨()⟩ : A -n> ULift Unit) (constHom default) inh.default⟩

variable (F) in
/-- The truncation `[F X X]_{α}` of the functor applied to `X` (Rocq: `[G X]_{α}`). -/
noncomputable abbrev TG (α : SI) (X : Obj.{u} (SI := SI)) : Obj.{u} (SI := SI) :=
  ⟨TruncO α (F X.car X.car)⟩

theorem TG_car (α : SI) (X : Obj.{u} (SI := SI)) : (TG F α X).car = TruncO α (F X.car X.car) := rfl

omit [∀ α [COFE α], IsCOFE (F α α)] inh in
theorem map_congr {A B C D : Type (max u v)} [COFE A] [COFE B] [COFE C] [COFE D]
    {f f' : C -n> A} {g g' : B -n> D} (h1 : ∀ x, f x = f' x) (h2 : ∀ x, g x = g' x) (y : F A B) :
    map (F := F) f g y = map (F := F) f' g' y := by
  rw [Hom.ext (funext h1), Hom.ext (funext h2)]

/-! ## Stages and families of approximations -/

variable (F) in
/-- A stage of the construction at index `γ`: the approximation at `γ`, copies of the earlier
approximations, the embedding-projection pairs from the earlier approximations, and the bounded
isomorphism between `X γ` and `[F (X γ) (X γ)]_{γ + 1}`. -/
structure Stage (γ : SI) where
  X : Obj.{u} (SI := SI)
  prev : ∀ β, β < γ → Obj.{u} (SI := SI)
  e : ∀ β (h : β < γ), (prev β h).car -n> X.car
  p : ∀ β (h : β < γ), X.car -n> (prev β h).car
  ϕ : X.car -n> (TG F (σ γ) X).car
  ψ : (TG F (σ γ) X).car -n> X.car

variable (F) in
/-- A family of approximations below `γ`, with the maps between them (Rocq: `bounded_approx` for
the predicate `· < γ`, without its laws). `unf` and `fld` are the identifications of
`X (β + 1)` with `[F (X β) (X β)]_{β + 1}`. -/
structure Fam (γ : SI) where
  X : ∀ β, β < γ → Obj.{u} (SI := SI)
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
@[reducible] noncomputable def famOf {γ : SI} (IH : ∀ β, β < γ → Stage F β) : Fam F γ where
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
@[reducible] noncomputable def zeroStage : Stage F (0 : SI) :=
  let U := unitObj.{u} (SI := SI)
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
@[reducible] noncomputable def succStage (m : SI) (f : Fam F (σ m)) : Stage F (σ m) :=
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
noncomputable abbrev FX (β : SI) (hβ : β < γ) : Obj.{u} (SI := SI) := TG F (σ β) (f.X β hβ)

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
    change eLval hlim f n hn x β hβ ≡{k}≡ eLval hlim f n hn y β hβ
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
      change (c.bchain (σ β) _).val β hβ ≡{m}≡ (c.bchain m hm).val β hβ
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
noncomputable def LimObj : Obj.{u} (SI := SI) :=
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
        · change pL f p hp z ≡{m}≡ f.e m p hm hp h (pL f m hm z)
          have e1 : f.e m p hm hp h (pL f m hm z) =
              f.e m p hm hp h (f.p m p hm hp h (pL f p hp z)) :=
            congrArg _ (pL_functorial hf m p hm hp h (hlim.succ_lt m hm) (hlim.succ_lt p hp) z)
          exact ((Dist.of_eq e1).trans (hf.e_p m p hm hp h _)).symm
        · change eL hlim hf p hp z ≡{m}≡ eL hlim hf m hm (f.p m p hm hp h z)
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
@[reducible] noncomputable def limitStage : Stage F γ where
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
  change truncMap γ (σ β) _ (truncMap (σ (σ β)) γ _ (x.val (σ β) hs)) = _
  rw [truncMap_truncMap (SIdx.lt_le_incl hs)]
  rw [← x.coh β (σ β) hβ hs (SIdx.lt_succ_self β), Fep]
  refine truncMap_congr (fun y => ?_) _
  rw [Hom.comp_apply, ← OFunctor.map_comp]
  exact map_congr (fun z => pL_eL_up hlim hf β (σ β) hβ hs (SIdx.lt_succ_self β) z)
    (fun z => pL_eL_down hlim hf β (σ β) hβ hs (SIdx.lt_succ_self β) z) y

/-- Rocq: `ϕβ_ψβ_id`. -/
theorem ϕL_ψL (y) (k : SI) (hk : k < γ) : ϕL hlim hf (ψL' hlim hf y) ≡{k}≡ y := by
  refine (IsCOFE.conv_lbcompl hlim (ϕLchain hlim hf (ψL hlim hf y)) hk).trans ?_
  change truncMap (σ k) γ _ (truncMap γ (σ k) _ y) ≡{k}≡ y
  refine ((truncMap_comp_dist γ γ (σ k) _ _ y).symm.le (SIdx.lt_le_incl (SIdx.lt_succ_self k))).trans ?_
  refine (((truncMap_ne γ γ).ne (n := k) (fun z => ?_)) y).trans (Dist.of_eq (truncMap_id γ y))
  rw [Hom.comp_apply, ← OFunctor.map_comp]
  refine ((OFunctor.map_ne.ne (fun w => ?_) (fun w => ?_) z).trans (Dist.of_eq (OFunctor.map_id z)))
  · exact eL_pL hlim hf k hk w
  · exact eL_pL hlim hf k hk w

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
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
  · change eL hlim hf γ0 h0 z = eL hlim hf (σ γ0) hs0 (f.fld γ0 h0 hs0 (f.ϕ γ0 h0 z))
    rw [← hf.e_fold_ϕ γ0 h0 hs0 (SIdx.lt_succ_self γ0), ← eL_functorial]
  · change pL f γ0 h0 z = f.ψ γ0 h0 (f.unf γ0 h0 hs0 (pL f (σ γ0) hs0 z))
    exact (pL_functorial hf γ0 (σ γ0) h0 hs0 (SIdx.lt_succ_self γ0) hs0 (hlim.succ_lt _ hs0) z).trans
      (hf.p_ψ_unfold γ0 h0 hs0 (SIdx.lt_succ_self γ0) _)

/-- Rocq: `ψβ'_ϕβ'_id`. -/
theorem ψS_ϕS (x : (TG F γ (LimObj hlim hf)).car) : ψS hlim hf (ϕS hlim hf x) = x := by
  change truncMap (σ γ) γ _ (truncMap γ (σ γ) _ x) = x
  rw [truncMap_truncMap (SIdx.lt_le_incl (SIdx.lt_succ_self γ))]
  refine (truncMap_congr (fun y => ?_) x).trans (truncMap_id γ x)
  rw [Hom.comp_apply, ← OFunctor.map_comp]
  exact (map_congr (f' := Hom.id) (g' := Hom.id)
    (fun (z : (LimObj hlim hf).car) => (ψL_ϕL hlim hf z : ψL' hlim hf (ϕL hlim hf z) = z))
    (fun (z : (LimObj hlim hf).car) => (ψL_ϕL hlim hf z : ψL' hlim hf (ϕL hlim hf z) = z)) y).trans
    (OFunctor.map_id y)

/-- Rocq: `ϕβ'_ψβ'_id`. -/
theorem ϕS_ψS (x) : ϕS hlim hf (ψS hlim hf x) ≡{γ}≡ x := by
  change truncMap γ (σ γ) _ (truncMap (σ γ) γ _ x) ≡{γ}≡ x
  refine (truncMap_comp_dist (σ γ) (σ γ) γ _ _ x).symm.trans ?_
  refine (((truncMap_ne (σ γ) (σ γ)).ne (n := γ) (fun y => ?_)) x).trans
    (Dist.of_eq (truncMap_id (σ γ) x))
  change map (F := F) _ _ (map (F := F) _ _ y) ≡{γ}≡ y
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
  change _ = truncMap γ (σ γ0) _ (truncMap (σ γ) γ _ x)
  rw [truncMap_truncMap (SIdx.lt_le_incl (hlim.succ_lt γ0 h0))]
  refine truncMap_congr (fun y => ?_) x
  rw [Hom.comp_apply, ← OFunctor.map_comp]

end LimitStageLaws

/-! ## The recursion -/

variable [∀ α [COFE α], BcomplUniqueLim (F α α)]

variable (F) in
/-- A junk stage, used at limit indices whose earlier stages do not satisfy the laws (which never
happens). -/
@[reducible] noncomputable def junkStage (γ : SI) (IH : ∀ β, β < γ → Stage F β) : Stage F γ where
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
noncomputable abbrev X (γ : SI) : Obj.{u} (SI := SI) := (stage F γ).X

/-- The copies of earlier approximations in a stage agree with the earlier stages. -/
theorem prev_eq (γ β : SI) (h : β < γ) : (stage F γ).prev β h = X F β := by
  rw [stage_eq (F := F) γ]
  rcases SIdx.case γ with h0 | ⟨m, rfl⟩ | hlim
  · subst h0; exact absurd h (SIdx.not_lt_zero β)
  · rw [step_succ]
  · by_cases hf : FamGood (famOf (fun β (_ : β < γ) => stage F β))
    · rw [step_limit hlim _ hf]
    · rw [step_limit_junk hlim _ hf]

theorem stage_succ (m : SI) :
    stage F (σ m) = succStage F m (famOf (fun β (_ : β < σ m) => stage F β)) := by
  rw [stage_eq (F := F) (σ m), step_succ]

/-- `X (m + 1) = [F (X m) (X m)]_{m + 1}` (Rocq: `approx_eq`). -/
theorem X_succ (m : SI) : X F (σ m) = TG F (σ m) (X F m) := by
  change (stage F (σ m)).X = _
  rw [stage_succ]

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

theorem unfold_fold (m : SI) (x) : unfold F m (fold F m x) = x :=
  castObj_castObj_symm _ _

theorem fold_unfold (m : SI) (x) : fold F m (unfold F m x) = x :=
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

/-! ## Characterization of the approximations -/

section Transport

variable {γ : SI} {T S : Stage F γ} (hTS : T = S)
include hTS

theorem transport_e (β : SI) (h : β < γ) (hT : T.prev β h = X F β) (hS : S.prev β h = X F β)
    (x : (X F β).car) :
    T.e β h (castObj hT.symm x) = castObj (congrArg Stage.X hTS).symm (S.e β h (castObj hS.symm x)) := by
  subst hTS; rfl

theorem transport_p (β : SI) (h : β < γ) (hT : T.prev β h = X F β) (hS : S.prev β h = X F β)
    (y : T.X.car) :
    castObj hT (T.p β h y) = castObj hS (S.p β h (castObj (congrArg Stage.X hTS) y)) := by
  subst hTS; rfl

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
theorem transport_ϕ (y : T.X.car) :
    T.ϕ y = castObj (congrArg (fun S : Stage F γ => TG F (σ γ) S.X) hTS).symm
      (S.ϕ (castObj (congrArg Stage.X hTS) y)) := by
  subst hTS; rfl

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
theorem transport_ψ (z : (TG F (σ γ) T.X).car) :
    T.ψ z = castObj (congrArg Stage.X hTS).symm
      (S.ψ (castObj (congrArg (fun S : Stage F γ => TG F (σ γ) S.X) hTS) z)) := by
  subst hTS; rfl

end Transport

/-! ### Successor indices -/

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
/-- Transport along an equality of COFEs commutes with the functor. -/
theorem cast_truncMap_map {A B C : Obj.{u} (SI := SI)} (hAB : A = B) (α α' : SI)
    (h' : TG F α A = TG F α B) (g : A.car -n> C.car) (h : C.car -n> A.car)
    (w : TruncO α' (F C.car C.car)) :
    castObj h' (truncMap α' α (map (F := F) g h) w) =
      truncMap α' α (map (F := F) (g.comp (castObj hAB.symm)) ((castObj hAB).comp h)) w := by
  subst hAB; rfl

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
/-- Transport along an equality of COFEs commutes with the functor. -/
theorem truncMap_map_cast {A B C : Obj.{u} (SI := SI)} (hAB : A = B) (α α' : SI)
    (h' : TG F α' B = TG F α' A) (g : C.car -n> A.car) (h : A.car -n> C.car)
    (w : TruncO α' (F B.car B.car)) :
    truncMap α' α (map (F := F) g h) (castObj h' w) =
      truncMap α' α (map (F := F) ((castObj hAB).comp g) (h.comp (castObj hAB.symm))) w := by
  subst hAB; rfl

section Succ

variable (m : SI)

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
theorem succStage_e_self (f : Fam F (σ m)) (h : m < σ m) (x : (f.X m h).car) :
    (succStage F m f).e m h x = f.ϕ m h x := by
  unfold succStage; dsimp only; rw [dite_eq_left rfl]; rfl

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
theorem succStage_e_lt (f : Fam F (σ m)) (β : SI) (h : β < σ m) (hβ : β < m) (x) :
    (succStage F m f).e β h x = f.ϕ m (SIdx.lt_succ_self m) (f.e β m h _ hβ x) := by
  unfold succStage; dsimp only
  rw [dite_eq_right (fun (hβm : β = m) => SIdx.lt_irrefl m (hβm ▸ hβ))]; rfl

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
theorem succStage_p_self (f : Fam F (σ m)) (h : m < σ m) (y) :
    (succStage F m f).p m h y = f.ψ m h y := by
  unfold succStage; dsimp only; rw [dite_eq_left rfl]; rfl

omit [∀ α [COFE α], BcomplUniqueLim (F α α)] in
theorem succStage_p_lt (f : Fam F (σ m)) (β : SI) (h : β < σ m) (hβ : β < m) (y) :
    (succStage F m f).p β h y = f.p β m h _ hβ (f.ψ m (SIdx.lt_succ_self m) y) := by
  unfold succStage; dsimp only
  rw [dite_eq_right (fun (hβm : β = m) => SIdx.lt_irrefl m (hβm ▸ hβ))]; rfl

theorem e_succ_self (h : m < σ m) (x) : e F m (σ m) h x = fold F m (ϕ F m x) := by
  change (stage F (σ m)).e m h (castObj (prev_eq (σ m) m h).symm x) = _
  rw [transport_e (stage_succ m) m h (prev_eq (σ m) m h) rfl x, succStage_e_self]
  rfl

theorem e_succ_lt (β : SI) (hβ : β < m) (h : β < σ m) (x) :
    e F β (σ m) h x = e F m (σ m) (SIdx.lt_succ_self m) (e F β m hβ x) := by
  change (stage F (σ m)).e β h (castObj (prev_eq (σ m) β h).symm x) = _
  rw [transport_e (stage_succ m) β h (prev_eq (σ m) β h) rfl x, e_succ_self,
    succStage_e_lt m _ β h hβ, famBelow_e]
  rfl

theorem p_succ_self (h : m < σ m) (y) : p F m (σ m) h y = ψ F m (unfold F m y) := by
  change castObj (prev_eq (σ m) m h) ((stage F (σ m)).p m h y) = _
  rw [transport_p (stage_succ m) m h (prev_eq (σ m) m h) rfl y, succStage_p_self]
  rfl

theorem p_succ_lt (β : SI) (hβ : β < m) (h : β < σ m) (y) :
    p F β (σ m) h y = p F β m hβ (p F m (σ m) (SIdx.lt_succ_self m) y) := by
  change castObj (prev_eq (σ m) β h) ((stage F (σ m)).p β h y) = _
  rw [transport_p (stage_succ m) β h (prev_eq (σ m) β h) rfl y, p_succ_self,
    succStage_p_lt m _ β h hβ, famBelow_p]
  rfl

theorem ϕ_succ (y) :
    ϕ F (σ m) y = truncMap (σ m) (σ (σ m))
      (map (F := F) ((ψ F m).comp (unfold F m)) ((fold F m).comp (ϕ F m))) (unfold F m y) := by
  change (stage F (σ m)).ϕ y = _
  rw [transport_ϕ (stage_succ m) y]
  exact cast_truncMap_map (congrArg Stage.X (stage_succ m)).symm (σ (σ m)) (σ m) _ _ _ _

theorem ψ_succ (z) :
    ψ F (σ m) z = fold F m (truncMap (σ (σ m)) (σ m)
      (map (F := F) ((fold F m).comp (ϕ F m)) ((ψ F m).comp (unfold F m))) z) := by
  change (stage F (σ m)).ψ z = _
  rw [transport_ψ (stage_succ m) z]
  congr 1
  exact truncMap_map_cast (congrArg Stage.X (stage_succ m)).symm (σ m) (σ (σ m)) _ _ _ _

end Succ

/-! ### Limit indices -/

section Limit

variable {γ : SI} (hlim : SIdx.Limit γ) (hg : FamGood (famBelow (F := F) γ))

theorem stage_limit : stage F γ = limitStage F hlim hg := by
  rw [stage_eq (F := F) γ, step_limit hlim _ hg]

/-- The approximation at a limit index is `[F L L]_{γ}` for the inverse limit `L`. -/
theorem X_limit : X F γ = TG F γ (LimObj hlim hg) := congrArg Stage.X (stage_limit hlim hg)

theorem e_limit (β : SI) (h : β < γ) (x) :
    e F β γ h x = castObj (X_limit hlim hg).symm (eS hlim hg β h x) := by
  change (stage F γ).e β h (castObj (prev_eq γ β h).symm x) = _
  rw [transport_e (stage_limit hlim hg) β h (prev_eq γ β h) rfl x]
  rfl

theorem p_limit (β : SI) (h : β < γ) (y) :
    p F β γ h y = pS hlim hg β h (castObj (X_limit hlim hg) y) := by
  change castObj (prev_eq γ β h) ((stage F γ).p β h y) = _
  rw [transport_p (stage_limit hlim hg) β h (prev_eq γ β h) rfl y]
  rfl

theorem ϕ_limit (y) :
    ϕ F γ y = castObj (congrArg (TG F (σ γ)) (X_limit hlim hg)).symm
      (ϕS hlim hg (castObj (X_limit hlim hg) y)) := by
  change (stage F γ).ϕ y = _
  rw [transport_ϕ (stage_limit hlim hg) y]

theorem ψ_limit (z) :
    ψ F γ z = castObj (X_limit hlim hg).symm
      (ψS hlim hg (castObj (congrArg (TG F (σ γ)) (X_limit hlim hg)) z)) := by
  change (stage F γ).ψ z = _
  rw [transport_ψ (stage_limit hlim hg) z]

end Limit

/-! ### The zero index -/

theorem stage_zero : stage F 0 = zeroStage F := by
  rw [stage_eq (F := F) 0, step_zero]

theorem X_zero : X F 0 = TG F 0 unitObj := congrArg Stage.X (stage_zero (F := F))

theorem ϕ_zero (y) :
    ϕ F 0 y = castObj (congrArg (TG F (σ 0)) (X_zero (F := F))).symm
      ((zeroStage F).ϕ (castObj (X_zero (F := F)) y)) := by
  change (stage F 0).ϕ y = _
  rw [transport_ϕ (stage_zero (F := F)) y]

theorem ψ_zero (z) :
    ψ F 0 z = castObj (X_zero (F := F)).symm
      ((zeroStage F).ψ (castObj (congrArg (TG F (σ 0)) (X_zero (F := F))) z)) := by
  change (stage F 0).ψ z = _
  rw [transport_ψ (stage_zero (F := F)) z]

/-! ## The laws of the approximations -/

/-- The laws hold for all approximations below `γ`. -/
abbrev Good (γ : SI) : Prop := FamGood (famBelow (F := F) γ)

namespace Good

variable {δ : SI} (hg : Good (F := F) δ)
include hg

theorem p_e (β η : SI) (hβ : β < δ) (hη : η < δ) (hlt : β < η) (x) :
    p F β η hlt (e F β η hlt x) = x := by
  have h := FamGood.p_e hg β η hβ hη hlt x
  rw [famBelow_p δ β η hβ hη hlt, famBelow_e δ β η hβ hη hlt] at h
  exact h

theorem e_p (β η : SI) (hβ : β < δ) (hη : η < δ) (hlt : β < η) (x) :
    e F β η hlt (p F β η hlt x) ≡{β}≡ x := by
  have h := FamGood.e_p hg β η hβ hη hlt x
  rw [famBelow_p δ β η hβ hη hlt, famBelow_e δ β η hβ hη hlt] at h
  exact h

theorem e_funct (β η ζ : SI) (hβ : β < δ) (hη : η < δ) (hζ : ζ < δ) (h1 : β < η) (h2 : η < ζ)
    (h3 : β < ζ) (x) : e F η ζ h2 (e F β η h1 x) = e F β ζ h3 x := by
  have h := FamGood.e_funct hg β η ζ hβ hη hζ h1 h2 h3 x
  rw [famBelow_e δ β η hβ hη h1, famBelow_e δ η ζ hη hζ h2, famBelow_e δ β ζ hβ hζ h3] at h
  exact h

theorem p_funct (β η ζ : SI) (hβ : β < δ) (hη : η < δ) (hζ : ζ < δ) (h1 : β < η) (h2 : η < ζ)
    (h3 : β < ζ) (x) : p F β η h1 (p F η ζ h2 x) = p F β ζ h3 x := by
  have h := FamGood.p_funct hg β η ζ hβ hη hζ h1 h2 h3 x
  rw [famBelow_p δ β η hβ hη h1, famBelow_p δ η ζ hη hζ h2, famBelow_p δ β ζ hβ hζ h3] at h
  exact h

theorem ψ_ϕ (β : SI) (hβ : β < δ) (x) : ψ F β (ϕ F β x) = x := FamGood.ψ_ϕ hg β hβ x

theorem ϕ_ψ (β : SI) (hβ : β < δ) (x) : ϕ F β (ψ F β x) ≡{β}≡ x := FamGood.ϕ_ψ hg β hβ x

theorem Fep_p (γ0 γ1 : SI) (h0 : γ0 < δ) (h1 : γ1 < δ) (hs0 : σ γ0 < δ) (hs1 : σ γ1 < δ)
    (hlt : γ0 < γ1) (hlts : σ γ0 < σ γ1) (x) :
    fold F γ0 (truncMap (σ γ1) (σ γ0) (map (F := F) (e F γ0 γ1 hlt) (p F γ0 γ1 hlt))
      (unfold F γ1 x)) = p F (σ γ0) (σ γ1) hlts x := by
  have h := FamGood.Fep_p hg γ0 γ1 h0 h1 hs0 hs1 hlt hlts x
  rw [famBelow_fld δ γ0 h0 hs0, famBelow_unf δ γ1 h1 hs1, famBelow_e δ γ0 γ1 h0 h1 hlt,
    famBelow_p δ γ0 γ1 h0 h1 hlt, famBelow_p δ (σ γ0) (σ γ1) hs0 hs1 hlts] at h
  exact h

theorem Fep_p_limit (γ0 γ1 : SI) (hlim : SIdx.Limit γ1) (h0 : γ0 < δ) (hs0 : σ γ0 < δ)
    (h1 : γ1 < δ) (hlt : γ0 < γ1) (hslt : σ γ0 < γ1) (x) :
    fold F γ0 (truncMap (σ γ1) (σ γ0) (map (F := F) (e F γ0 γ1 hlt) (p F γ0 γ1 hlt)) x) =
      p F (σ γ0) γ1 hslt (ψ F γ1 x) := by
  have h := FamGood.Fep_p_limit hg γ0 γ1 hlim h0 hs0 h1 hlt hslt x
  rw [famBelow_fld δ γ0 h0 hs0, famBelow_e δ γ0 γ1 h0 h1 hlt, famBelow_p δ γ0 γ1 h0 h1 hlt,
    famBelow_p δ (σ γ0) γ1 hs0 h1 hslt] at h
  exact h

end Good

theorem truncated_of_eq {A B : Obj.{u} (SI := SI)} (h : A = B) {α : SI} [Truncated B.car α] :
    Truncated A.car α := by
  subst h; assumption

/-! ### Laws at successor indices -/

section SuccLaws

variable (m : SI) (hg : Good (F := F) (σ m))
include hg

theorem p_e_succ_self (x) :
    p F m (σ m) (SIdx.lt_succ_self m) (e F m (σ m) (SIdx.lt_succ_self m) x) = x := by
  rw [p_succ_self, e_succ_self, unfold_fold, hg.ψ_ϕ m (SIdx.lt_succ_self m)]

theorem p_e_succ (β : SI) (h : β < σ m) (x) : p F β (σ m) h (e F β (σ m) h x) = x := by
  rcases SIdx.le_lteq.mp (SIdx.lt_succ_r.mp h) with hβ | hβ
  · rw [e_succ_lt m β hβ h, p_succ_lt m β hβ h, p_e_succ_self m hg,
      hg.p_e β m h (SIdx.lt_succ_self m) hβ]
  · subst hβ; exact p_e_succ_self β hg x

theorem e_p_succ_self (y) :
    e F m (σ m) (SIdx.lt_succ_self m) (p F m (σ m) (SIdx.lt_succ_self m) y) ≡{m}≡ y := by
  rw [p_succ_self, e_succ_self]
  refine ((fold F m).ne.1 (hg.ϕ_ψ m (SIdx.lt_succ_self m) _)).trans (Dist.of_eq (fold_unfold m y))

theorem e_p_succ (β : SI) (h : β < σ m) (y) : e F β (σ m) h (p F β (σ m) h y) ≡{β}≡ y := by
  rcases SIdx.le_lteq.mp (SIdx.lt_succ_r.mp h) with hβ | hβ
  · rw [e_succ_lt m β hβ h, p_succ_lt m β hβ h]
    refine ((e F m (σ m) _).ne.1 (hg.e_p β m h (SIdx.lt_succ_self m) hβ _)).trans ?_
    exact (e_p_succ_self m hg y).le (SIdx.lt_le_incl hβ)
  · subst hβ; exact e_p_succ_self β hg y

theorem e_funct_succ (β η : SI) (h1 : β < η) (h2 : η < σ m) (h3 : β < σ m) (x) :
    e F η (σ m) h2 (e F β η h1 x) = e F β (σ m) h3 x := by
  rcases SIdx.le_lteq.mp (SIdx.lt_succ_r.mp h2) with hη | hη
  · rw [e_succ_lt m η hη h2, e_succ_lt m β (SIdx.lt_trans h1 hη) h3,
      hg.e_funct β η m h3 h2 (SIdx.lt_succ_self m) h1 hη (SIdx.lt_trans h1 hη)]
  · subst hη; rw [e_succ_lt η β h1 h3]

theorem p_funct_succ (β η : SI) (h1 : β < η) (h2 : η < σ m) (h3 : β < σ m) (y) :
    p F β η h1 (p F η (σ m) h2 y) = p F β (σ m) h3 y := by
  rcases SIdx.le_lteq.mp (SIdx.lt_succ_r.mp h2) with hη | hη
  · rw [p_succ_lt m η hη h2, p_succ_lt m β (SIdx.lt_trans h1 hη) h3,
      hg.p_funct β η m h3 h2 (SIdx.lt_succ_self m) h1 hη (SIdx.lt_trans h1 hη)]
  · subst hη; rw [p_succ_lt η β h1 h3]

theorem ψ_ϕ_succ (x) : ψ F (σ m) (ϕ F (σ m) x) = x := by
  rw [ψ_succ, ϕ_succ, truncMap_truncMap (SIdx.lt_le_incl (SIdx.lt_succ_self (σ m)))]
  refine Eq.trans ?_ (fold_unfold m x)
  congr 1
  refine (truncMap_congr (fun y => ?_) _).trans (truncMap_id _ _)
  rw [Hom.comp_apply, ← OFunctor.map_comp]
  refine (map_congr (fun z => ?_) (fun z => ?_) y).trans (OFunctor.map_id y)
  · change ψ F m (unfold F m (fold F m (ϕ F m z))) = z
    rw [unfold_fold, hg.ψ_ϕ m (SIdx.lt_succ_self m)]
  · change ψ F m (unfold F m (fold F m (ϕ F m z))) = z
    rw [unfold_fold, hg.ψ_ϕ m (SIdx.lt_succ_self m)]

theorem ϕ_ψ_succ (z) : ϕ F (σ m) (ψ F (σ m) z) ≡{σ m}≡ z := by
  rw [ϕ_succ, ψ_succ, unfold_fold]
  refine (truncMap_comp_dist (σ (σ m)) (σ (σ m)) (σ m) _ _ z).symm.trans ?_
  refine (((truncMap_ne (σ (σ m)) (σ (σ m))).ne (n := σ m) (fun y => ?_)) z).trans
    (Dist.of_eq (truncMap_id _ z))
  change map (F := F) _ _ (map (F := F) _ _ y) ≡{σ m}≡ y
  rw [← OFunctor.map_comp]
  have H : ∀ w, ((fold F m).comp (ϕ F m)).comp ((ψ F m).comp (unfold F m)) w ≡{m}≡ w := fun w => by
    change fold F m (ϕ F m (ψ F m (unfold F m w))) ≡{m}≡ w
    exact ((fold F m).ne.1 (hg.ϕ_ψ m (SIdx.lt_succ_self m) _)).trans (Dist.of_eq (fold_unfold m w))
  refine ((OFunctorContractive.map_contractive (F := F)).distLater_dist
    (x := (((fold F m).comp (ϕ F m)).comp ((ψ F m).comp (unfold F m)),
      ((fold F m).comp (ϕ F m)).comp ((ψ F m).comp (unfold F m))))
    (y := (Hom.id, Hom.id)) (fun k hk => ⟨fun w => (H w).le (SIdx.lt_succ_r.mp hk),
      fun w => (H w).le (SIdx.lt_succ_r.mp hk)⟩) y).trans (Dist.of_eq (OFunctor.map_id y))

omit hg in
theorem truncated_succ : Truncated (X F (σ m)).car (σ m) := truncated_of_eq (X_succ m)

end SuccLaws

/-- Rocq: `Fep_sp'` (the law `approx_Fep_p` at a successor index). -/
theorem Fep_p_succ (γ0 γ1 : SI) (hlt : γ0 < γ1) (hlts : σ γ0 < σ γ1) (hg : Good (F := F) (σ γ1))
    (x) :
    fold F γ0 (truncMap (σ γ1) (σ γ0) (map (F := F) (e F γ0 γ1 hlt) (p F γ0 γ1 hlt))
      (unfold F γ1 x)) = p F (σ γ0) (σ γ1) hlts x := by
  rcases SIdx.le_lteq.mp (SIdx.le_succ_l.mpr hlt) with hs | hs
  · rw [p_succ_lt γ1 (σ γ0) hs hlts, p_succ_self]
    generalize unfold F γ1 x = z
    rcases SIdx.case γ1 with h0 | ⟨β', rfl⟩ | hlim1
    · subst h0; exact absurd hs (SIdx.not_lt_zero _)
    · have hβ' : γ0 < β' := SIdx.succ_lt_mono.mpr hs
      have l1 : β' < σ (σ β') := SIdx.lt_trans (SIdx.lt_succ_self β') (SIdx.lt_succ_self _)
      have l2 : σ β' < σ (σ β') := SIdx.lt_succ_self _
      rw [ψ_succ β' z, ← hg.Fep_p γ0 β' (SIdx.lt_trans hβ' l1) l1 (SIdx.lt_trans hs l2) l2 hβ' hs,
        unfold_fold, truncMap_truncMap (SIdx.lt_le_incl hs)]
      congr 1
      refine truncMap_congr (fun y => ?_) z
      rw [Hom.comp_apply, ← OFunctor.map_comp]
      refine map_congr (fun w => ?_) (fun w => ?_) y
      · change e F γ0 (σ β') hlt w = fold F β' (ϕ F β' (e F γ0 β' hβ' w))
        rw [← e_succ_self β' (SIdx.lt_succ_self β'), hg.e_funct γ0 β' (σ β') (SIdx.lt_trans hβ' l1) l1 l2 hβ'
          (SIdx.lt_succ_self β') hlt]
      · change p F γ0 (σ β') hlt w = p F γ0 β' hβ' (ψ F β' (unfold F β' w))
        rw [← p_succ_self β' (SIdx.lt_succ_self β'), hg.p_funct γ0 β' (σ β') (SIdx.lt_trans hβ' l1) l1 l2 hβ'
          (SIdx.lt_succ_self β') hlt]
    · exact hg.Fep_p_limit γ0 γ1 hlim1 (SIdx.lt_trans hlt (SIdx.lt_succ_self γ1))
        (SIdx.lt_trans hs (SIdx.lt_succ_self γ1)) (SIdx.lt_succ_self γ1) hlt hs z
  · subst hs
    rw [p_succ_self (σ γ0), ψ_succ γ0]
    congr 1
    refine truncMap_congr (fun y => ?_) _
    exact map_congr (fun w => e_succ_self γ0 hlt w) (fun w => p_succ_self γ0 hlt w) y

/-! ### Laws at limit indices -/

section LimitLaws

variable {δ : SI} (hlim : SIdx.Limit δ) (hg : Good (F := F) δ)
include hlim hg

theorem p_e_limit (β : SI) (h : β < δ) (x) : p F β δ h (e F β δ h x) = x := by
  rw [e_limit hlim hg, p_limit hlim hg, castObj_castObj_symm]
  exact pS_eS hlim hg β h x

theorem e_p_limit (β : SI) (h : β < δ) (y) : e F β δ h (p F β δ h y) ≡{β}≡ y := by
  rw [p_limit hlim hg, e_limit hlim hg]
  exact ((castObj _).ne.1 (eS_pS hlim hg β h _)).trans (Dist.of_eq (castObj_symm_castObj _ _))

theorem e_funct_limit (β η : SI) (h1 : β < η) (h2 : η < δ) (h3 : β < δ) (x) :
    e F η δ h2 (e F β η h1 x) = e F β δ h3 x := by
  rw [e_limit hlim hg, e_limit hlim hg]
  congr 1
  have H := eS_functorial hlim hg β η h3 h2 h1 x
  rw [famBelow_e δ β η h3 h2 h1] at H
  exact H

theorem p_funct_limit (β η : SI) (h1 : β < η) (h2 : η < δ) (h3 : β < δ) (y) :
    p F β η h1 (p F η δ h2 y) = p F β δ h3 y := by
  rw [p_limit hlim hg, p_limit hlim hg]
  have H := pS_functorial hlim hg β η h3 h2 h1 (castObj (X_limit hlim hg) y)
  rw [famBelow_p δ β η h3 h2 h1] at H
  exact H

theorem ψ_ϕ_limit (x) : ψ F δ (ϕ F δ x) = x := by
  rw [ψ_limit hlim hg, ϕ_limit hlim hg, castObj_castObj_symm, ψS_ϕS, castObj_symm_castObj]

theorem ϕ_ψ_limit (z) : ϕ F δ (ψ F δ z) ≡{δ}≡ z := by
  rw [ϕ_limit hlim hg, ψ_limit hlim hg, castObj_castObj_symm]
  exact ((castObj _).ne.1 (ϕS_ψS hlim hg _)).trans (Dist.of_eq (castObj_symm_castObj _ _))

theorem Fep_p_limit_limit (γ0 : SI) (h0 : γ0 < δ) (hs0 : σ γ0 < δ) (z) :
    fold F γ0 (truncMap (σ δ) (σ γ0) (map (F := F) (e F γ0 δ h0) (p F γ0 δ h0)) z) =
      p F (σ γ0) δ hs0 (ψ F δ z) := by
  have he : e F γ0 δ h0 = (castObj (X_limit hlim hg).symm).comp (eS hlim hg γ0 h0) :=
    Hom.ext (funext (e_limit hlim hg γ0 h0))
  have hp : p F γ0 δ h0 = (pS hlim hg γ0 h0).comp (castObj (X_limit hlim hg)) :=
    Hom.ext (funext (p_limit hlim hg γ0 h0))
  rw [ψ_limit hlim hg, p_limit hlim hg, castObj_castObj_symm, he, hp,
    ← truncMap_map_cast (X_limit hlim hg).symm (σ γ0) (σ δ)
      (congrArg (TG F (σ δ)) (X_limit hlim hg)) (eS hlim hg γ0 h0) (pS hlim hg γ0 h0) z]
  have H := fld_truncMap_eS hlim hg γ0 h0 hs0 (castObj (congrArg (TG F (σ δ)) (X_limit hlim hg)) z)
  rw [famBelow_fld δ γ0 h0 hs0] at H
  exact H

theorem truncated_limit : Truncated (X F δ).car δ := truncated_of_eq (X_limit hlim hg)

end LimitLaws

/-! ### Laws at `0` -/

theorem ψ_ϕ_zero (x) : ψ F 0 (ϕ F 0 x) = x := by
  rw [ψ_zero, ϕ_zero, castObj_castObj_symm]
  refine Eq.trans ?_ (castObj_symm_castObj (X_zero (F := F)) x)
  congr 1
  change truncMap (σ 0) 0 _ (truncMap 0 (σ 0) _ _) = _
  rw [truncMap_truncMap (SIdx.lt_le_incl (SIdx.lt_succ_self 0))]
  refine (truncMap_congr (fun y => ?_) _).trans (truncMap_id _ _)
  rw [Hom.comp_apply, ← OFunctor.map_comp]
  exact (map_congr (fun _ => rfl) (fun _ => rfl) y).trans (OFunctor.map_id y)

theorem ϕ_ψ_zero (z) : ϕ F 0 (ψ F 0 z) ≡{0}≡ z := by
  rw [ϕ_zero, ψ_zero, castObj_castObj_symm]
  refine ((castObj _).ne.1 ?_).trans
    (Dist.of_eq (castObj_symm_castObj (congrArg (TG F (σ 0)) (X_zero (F := F))) z))
  change truncMap 0 (σ 0) _ (truncMap (σ 0) 0 _ _) ≡{0}≡ _
  refine (truncMap_comp_dist (σ 0) (σ 0) 0 _ _ _).symm.trans ?_
  refine (((truncMap_ne (σ 0) (σ 0)).ne (n := 0) (fun y => ?_)) _).trans
    (Dist.of_eq (truncMap_id _ _))
  change map (F := F) _ _ (map (F := F) _ _ y) ≡{0}≡ y
  rw [← OFunctor.map_comp]
  exact ((OFunctorContractive.map_contractive (F := F)).zero (x := (_, _)) (y := (Hom.id, Hom.id))
    _ y).trans (Dist.of_eq (OFunctor.map_id y))

theorem truncated_zero : Truncated (X F 0).car 0 := truncated_of_eq X_zero

/-! ### All laws hold -/

theorem truncated_at (δ : SI) (hg : Good (F := F) δ) : Truncated (X F δ).car δ := by
  rcases SIdx.case δ with h0 | ⟨m, rfl⟩ | hlim
  · subst h0; exact truncated_zero
  · exact truncated_succ m
  · exact truncated_limit hlim hg

theorem p_e_at (δ : SI) (hg : Good (F := F) δ) (β : SI) (h : β < δ) (x) :
    p F β δ h (e F β δ h x) = x := by
  rcases SIdx.case δ with h0 | ⟨m, rfl⟩ | hlim
  · subst h0; exact absurd h (SIdx.not_lt_zero β)
  · exact p_e_succ m hg β h x
  · exact p_e_limit hlim hg β h x

theorem e_p_at (δ : SI) (hg : Good (F := F) δ) (β : SI) (h : β < δ) (y) :
    e F β δ h (p F β δ h y) ≡{β}≡ y := by
  rcases SIdx.case δ with h0 | ⟨m, rfl⟩ | hlim
  · subst h0; exact absurd h (SIdx.not_lt_zero β)
  · exact e_p_succ m hg β h y
  · exact e_p_limit hlim hg β h y

theorem e_funct_at (δ : SI) (hg : Good (F := F) δ) (β η : SI) (h1 : β < η) (h2 : η < δ)
    (h3 : β < δ) (x) : e F η δ h2 (e F β η h1 x) = e F β δ h3 x := by
  rcases SIdx.case δ with h0 | ⟨m, rfl⟩ | hlim
  · subst h0; exact absurd h2 (SIdx.not_lt_zero η)
  · exact e_funct_succ m hg β η h1 h2 h3 x
  · exact e_funct_limit hlim hg β η h1 h2 h3 x

theorem p_funct_at (δ : SI) (hg : Good (F := F) δ) (β η : SI) (h1 : β < η) (h2 : η < δ)
    (h3 : β < δ) (y) : p F β η h1 (p F η δ h2 y) = p F β δ h3 y := by
  rcases SIdx.case δ with h0 | ⟨m, rfl⟩ | hlim
  · subst h0; exact absurd h2 (SIdx.not_lt_zero η)
  · exact p_funct_succ m hg β η h1 h2 h3 y
  · exact p_funct_limit hlim hg β η h1 h2 h3 y

theorem ψ_ϕ_at (δ : SI) (hg : Good (F := F) δ) (x) : ψ F δ (ϕ F δ x) = x := by
  rcases SIdx.case δ with h0 | ⟨m, rfl⟩ | hlim
  · subst h0; exact ψ_ϕ_zero x
  · exact ψ_ϕ_succ m hg x
  · exact ψ_ϕ_limit hlim hg x

theorem ϕ_ψ_at (δ : SI) (hg : Good (F := F) δ) (z) : ϕ F δ (ψ F δ z) ≡{δ}≡ z := by
  rcases SIdx.case δ with h0 | ⟨m, rfl⟩ | hlim
  · subst h0; exact ϕ_ψ_zero z
  · exact ϕ_ψ_succ m hg z
  · exact ϕ_ψ_limit hlim hg z

/-- All approximations satisfy the laws (Rocq: `full_approximation`, `IR_spec`). -/
theorem good (γ : SI) : Good (F := F) γ := by
  induction γ using instSI.lt_wf.induction with
  | _ γ IH =>
    exact {
      xs := fun β _ _ => X_succ β
      unf_eq := fun β hβ hs => famBelow_unf γ β hβ hs
      fld_eq := fun β hβ hs => famBelow_fld γ β hβ hs
      truncated := fun β hβ => truncated_at β (IH β hβ)
      p_e := fun β δ hβ hδ hlt x => by
        rw [famBelow_p γ β δ hβ hδ hlt, famBelow_e γ β δ hβ hδ hlt]
        exact p_e_at δ (IH δ hδ) β hlt x
      e_p := fun β δ hβ hδ hlt x => by
        rw [famBelow_p γ β δ hβ hδ hlt, famBelow_e γ β δ hβ hδ hlt]
        exact e_p_at δ (IH δ hδ) β hlt x
      e_funct := fun β η δ hβ hη hδ h1 h2 h3 x => by
        rw [famBelow_e γ β η hβ hη h1, famBelow_e γ η δ hη hδ h2, famBelow_e γ β δ hβ hδ h3]
        exact e_funct_at δ (IH δ hδ) β η h1 h2 h3 x
      p_funct := fun β η δ hβ hη hδ h1 h2 h3 x => by
        rw [famBelow_p γ β η hβ hη h1, famBelow_p γ η δ hη hδ h2, famBelow_p γ β δ hβ hδ h3]
        exact p_funct_at δ (IH δ hδ) β η h1 h2 h3 x
      ψ_ϕ := fun β hβ x => ψ_ϕ_at β (IH β hβ) x
      ϕ_ψ := fun β hβ x => ϕ_ψ_at β (IH β hβ) x
      Fep_p := fun γ0 γ1 h0 h1 hs0 hs1 hlt hlts x => by
        rw [famBelow_fld γ γ0 h0 hs0, famBelow_unf γ γ1 h1 hs1, famBelow_e γ γ0 γ1 h0 h1 hlt,
          famBelow_p γ γ0 γ1 h0 h1 hlt, famBelow_p γ (σ γ0) (σ γ1) hs0 hs1 hlts]
        exact Fep_p_succ γ0 γ1 hlt hlts (IH (σ γ1) hs1) x
      p_ψ_unfold := fun β hβ hs hlt x => by
        rw [famBelow_p γ β (σ β) hβ hs hlt, famBelow_unf γ β hβ hs]; exact p_succ_self β hlt x
      e_fold_ϕ := fun β hβ hs hlt x => by
        rw [famBelow_e γ β (σ β) hβ hs hlt, famBelow_fld γ β hβ hs]; exact e_succ_self β hlt x
      ϕ_succ := fun β hβ hs x => by
        rw [famBelow_unf γ β hβ hs, famBelow_fld γ β hβ hs]; exact ϕ_succ β x
      ψ_succ := fun β hβ hs x => by
        rw [famBelow_unf γ β hβ hs, famBelow_fld γ β hβ hs]; exact ψ_succ β x
      Fep_p_limit := fun γ0 γ1 hlim h0 hs0 h1 hlt hslt x => by
        rw [famBelow_fld γ γ0 h0 hs0, famBelow_e γ γ0 γ1 h0 h1 hlt, famBelow_p γ γ0 γ1 h0 h1 hlt,
          famBelow_p γ (σ γ0) γ1 hs0 h1 hslt]
        exact Fep_p_limit_limit hlim (IH γ1 h1) γ0 hlt hslt x }

/-! ## The laws for arbitrary indices -/

section Global

theorem gp_e (β γ : SI) (h : β < γ) (x) : p F β γ h (e F β γ h x) = x := p_e_at γ (good γ) β h x

theorem ge_p (β γ : SI) (h : β < γ) (y) : e F β γ h (p F β γ h y) ≡{β}≡ y := e_p_at γ (good γ) β h y

theorem ge_funct (β η γ : SI) (h1 : β < η) (h2 : η < γ) (h3 : β < γ) (x) :
    e F η γ h2 (e F β η h1 x) = e F β γ h3 x := e_funct_at γ (good γ) β η h1 h2 h3 x

theorem gp_funct (β η γ : SI) (h1 : β < η) (h2 : η < γ) (h3 : β < γ) (y) :
    p F β η h1 (p F η γ h2 y) = p F β γ h3 y := p_funct_at γ (good γ) β η h1 h2 h3 y

theorem gFep_p (γ0 γ1 : SI) (hlt : γ0 < γ1) (hlts : σ γ0 < σ γ1) (x) :
    fold F γ0 (truncMap (σ γ1) (σ γ0) (map (F := F) (e F γ0 γ1 hlt) (p F γ0 γ1 hlt))
      (unfold F γ1 x)) = p F (σ γ0) (σ γ1) hlts x := Fep_p_succ γ0 γ1 hlt hlts (good (σ γ1)) x

theorem gFep_unfold (γ0 γ1 : SI) (hlt : γ0 < γ1) (hlts : σ γ0 < σ γ1) (x) :
    truncMap (σ γ1) (σ γ0) (map (F := F) (e F γ0 γ1 hlt) (p F γ0 γ1 hlt)) (unfold F γ1 x) =
      unfold F γ0 (p F (σ γ0) (σ γ1) hlts x) := by
  rw [← gFep_p γ0 γ1 hlt hlts x, unfold_fold]

theorem gfold_Fep (γ0 γ1 : SI) (hlt : γ0 < γ1) (hlts : σ γ0 < σ γ1) (y) :
    fold F γ0 (truncMap (σ γ1) (σ γ0) (map (F := F) (e F γ0 γ1 hlt) (p F γ0 γ1 hlt)) y) =
      p F (σ γ0) (σ γ1) hlts (fold F γ1 y) := by
  rw [← gFep_p γ0 γ1 hlt hlts, unfold_fold]

theorem gψ_p_fold (γ : SI) (x) : ψ F γ x = p F γ (σ γ) (SIdx.lt_succ_self γ) (fold F γ x) := by
  rw [p_succ_self, unfold_fold]

end Global

/-! ## The final inverse limit -/

variable (F) in
/-- The components of the solution: `[F (X γ) (X γ)]_{γ + 1}` (Rocq: `FX_lim`). -/
noncomputable abbrev FXl (γ : SI) : Obj.{u} (SI := SI) := TG F (σ γ) (X F γ)

variable (F) in
/-- Rocq: `Fep_lim`. -/
noncomputable def Fepl (γ0 γ1 : SI) (hlt : γ0 < γ1) : (FXl F γ1).car -n> (FXl F γ0).car :=
  truncMap (σ γ1) (σ γ0) (map (F := F) (e F γ0 γ1 hlt) (p F γ0 γ1 hlt))

variable (F) in
/-- The solution: the inverse limit of all approximations (Rocq: `Xlim`). -/
@[ext]
structure SolCar where
  val : ∀ γ : SI, (FXl F γ).car
  coh : ∀ γ0 γ1 (hlt : γ0 < γ1), Fepl F γ0 γ1 hlt (val γ1) = val γ0

noncomputable instance SolCar.instOFE : OFE (SolCar F) where
  Dist n x y := ∀ γ, x.val γ ≡{n}≡ y.val γ
  dist_eqv := {
    refl _ _ := .rfl
    symm h γ := (h γ).symm
    trans h h' γ := (h γ).trans (h' γ)
  }
  eq_dist' := by
    intro x y
    constructor
    · rintro rfl _ _; exact .rfl
    · intro h
      exact SolCar.ext (funext fun γ => OFE.eq_dist.mpr fun n => h n γ)
  dist_lt h hlt γ := (h γ).lt hlt

/-- The projection to a component. -/
def projSol (γ : SI) : SolCar F -n> (FXl F γ).car := ⟨fun x => x.val γ, ⟨fun _ _ _ h => h γ⟩⟩

/-- The value of the embedding of `X γ` into the solution (Rocq: `e_lim`). -/
noncomputable def elimVal (γ : SI) (x : (X F γ).car) (γ' : SI) : (FXl F γ').car :=
  match SIdx.lt_trichotomyT (σ γ') γ with
  | .inl h => unfold F γ' (p F (σ γ') γ h x)
  | .inr (.inl h) => unfold F γ' (castObj (A := X F γ) (B := X F (σ γ')) (by subst h; rfl) x)
  | .inr (.inr h) => unfold F γ' (e F γ (σ γ') h x)

theorem elimVal_lt {γ : SI} (x) {γ' : SI} (h : σ γ' < γ) :
    elimVal γ x γ' = unfold F γ' (p F (σ γ') γ h x) := by
  unfold elimVal; split
  · rfl
  · rename_i h' _; exact absurd (h' ▸ h) (SIdx.lt_irrefl _)
  · rename_i h' _; exact absurd (SIdx.lt_trans h h') (SIdx.lt_irrefl _)

theorem elimVal_eq {γ' : SI} (x : (X F (σ γ')).car) : elimVal (σ γ') x γ' = unfold F γ' x := by
  unfold elimVal; split
  · rename_i h _; exact absurd h (SIdx.lt_irrefl _)
  · rfl
  · rename_i h _; exact absurd h (SIdx.lt_irrefl _)

theorem elimVal_gt {γ : SI} (x) {γ' : SI} (h : γ < σ γ') :
    elimVal γ x γ' = unfold F γ' (e F γ (σ γ') h x) := by
  unfold elimVal; split
  · rename_i h' _; exact absurd (SIdx.lt_trans h h') (SIdx.lt_irrefl _)
  · rename_i h' _; exact absurd (h' ▸ h) (SIdx.lt_irrefl _)
  · rfl

theorem elimVal_coh (γ : SI) (x : (X F γ).car) (β δ : SI) (hlt : β < δ) :
    Fepl F β δ hlt (elimVal γ x δ) = elimVal γ x β := by
  have hlts : σ β < σ δ := SIdx.succ_lt_mono.mp hlt
  rcases SIdx.lt_trichotomyT (σ δ) γ with h1 | h1 | h1
  · rw [elimVal_lt x h1, elimVal_lt x (SIdx.lt_trans hlts h1), Fepl, gFep_unfold β δ hlt hlts,
      gp_funct]
  · subst h1
    rw [elimVal_eq x, elimVal_lt x hlts, Fepl, gFep_unfold β δ hlt hlts]
  · rcases SIdx.lt_trichotomyT (σ β) γ with h0 | h0 | h0
    · rw [elimVal_gt x h1, elimVal_lt x h0, Fepl, gFep_unfold β δ hlt hlts,
        ← gp_funct (σ β) γ (σ δ) h0 h1 hlts, gp_e]
    · subst h0
      rw [elimVal_gt x h1, elimVal_eq x, Fepl, gFep_unfold β δ hlt hlts, gp_e]
    · rw [elimVal_gt x h1, elimVal_gt x h0, Fepl, gFep_unfold β δ hlt hlts,
        ← ge_funct γ (σ β) (σ δ) h0 hlts h1, gp_e]

/-- The embedding of `X γ` into the solution (Rocq: `e_lim`). -/
noncomputable def elim (γ : SI) : (X F γ).car -n> SolCar F where
  f x := ⟨elimVal γ x, fun β δ hlt => elimVal_coh γ x β δ hlt⟩
  ne := ⟨fun k x y h γ' => by
    change elimVal γ x γ' ≡{k}≡ elimVal γ y γ'
    unfold elimVal
    split
    · exact (unfold F γ').ne.1 ((p F _ _ _).ne.1 h)
    · exact (unfold F γ').ne.1 ((castObj _).ne.1 h)
    · exact (unfold F γ').ne.1 ((e F _ _ _).ne.1 h)⟩

theorem elim_val (γ : SI) (x) (γ' : SI) : (elim γ x).val γ' = elimVal (F := F) γ x γ' := rfl

/-- The projection of the solution to `X γ` (Rocq: `p_lim`). -/
noncomputable def plim (γ : SI) : SolCar F -n> (X F γ).car := (ψ F γ).comp (projSol γ)

theorem plim_apply (γ : SI) (x : SolCar F) : plim γ x = ψ F γ (x.val γ) := rfl

/-- Rocq: `e_lim_p_lim_id`. -/
theorem elim_plim (γ : SI) (x : SolCar F) : elim γ (plim γ x) ≡{γ}≡ x := by
  intro δ
  rw [elim_val, plim_apply]
  rcases SIdx.lt_trichotomyT (σ δ) γ with h | h | h
  · have h' : σ δ < σ γ := SIdx.lt_trans h (SIdx.lt_succ_self γ)
    rw [elimVal_lt _ h, gψ_p_fold γ, gp_funct (σ δ) γ (σ γ) h (SIdx.lt_succ_self γ) h',
      ← gFep_unfold δ γ (SIdx.succ_lt_mono.mpr h') h', unfold_fold]
    exact Dist.of_eq (x.coh δ γ _)
  · subst h
    rw [elimVal_eq, gψ_p_fold (σ δ), ← gFep_p δ (σ δ) (SIdx.lt_succ_self δ) (SIdx.lt_succ_self _),
      unfold_fold, unfold_fold]
    exact Dist.of_eq (x.coh δ (σ δ) _)
  · rw [elimVal_gt _ h]
    rcases SIdx.le_lteq.mp (SIdx.lt_succ_r.mp h) with h' | h'
    · have hlts : σ γ < σ δ := SIdx.succ_lt_mono.mp h'
      rw [gψ_p_fold γ, ← ge_funct γ (σ γ) (σ δ) (SIdx.lt_succ_self γ) hlts h]
      refine ((unfold F δ).ne.1 ((e F (σ γ) (σ δ) hlts).ne.1 (ge_p γ (σ γ) _ _))).trans ?_
      rw [← x.coh γ δ h', Fepl, gfold_Fep γ δ h' hlts]
      refine ((unfold F δ).ne.1 ((ge_p (σ γ) (σ δ) hlts _).le
        (SIdx.lt_le_incl (SIdx.lt_succ_self γ)))).trans ?_
      rw [unfold_fold]
      exact .rfl
    · subst h'
      rw [e_succ_self, unfold_fold]
      exact ϕ_ψ_at γ (good γ) _

/-- Rocq: `p_lim_e_lim_id`. -/
theorem plim_elim (γ : SI) (x) : plim γ (elim (F := F) γ x) = x := by
  rw [plim_apply, elim_val, elimVal_gt x (SIdx.lt_succ_self γ), ← p_succ_self γ (SIdx.lt_succ_self γ), gp_e]

/-- Rocq: `e_lim_funct`. -/
theorem elim_funct (γ0 γ1 : SI) (hlt : γ0 < γ1) (x) :
    elim (F := F) γ0 x = elim γ1 (e F γ0 γ1 hlt x) := by
  refine SolCar.ext (funext fun β => ?_)
  rw [elim_val, elim_val]
  rcases SIdx.lt_trichotomyT (σ β) γ0 with h | h | h
  · rw [elimVal_lt x h, elimVal_lt _ (SIdx.lt_trans h hlt), ← gp_funct (σ β) γ0 γ1 h hlt, gp_e]
  · subst h
    rw [elimVal_eq, elimVal_lt _ hlt, gp_e]
  · rcases SIdx.lt_trichotomyT (σ β) γ1 with h' | h' | h'
    · rw [elimVal_gt x h, elimVal_lt _ h', ← ge_funct γ0 (σ β) γ1 h h' hlt, gp_e]
    · subst h'
      rw [elimVal_gt x h, elimVal_eq]
    · rw [elimVal_gt x h, elimVal_gt _ h', ge_funct γ0 γ1 (σ β) hlt h' h]

/-- Rocq: `p_lim_funct`. -/
theorem plim_funct (γ0 γ1 : SI) (hlt : γ0 < γ1) (x : SolCar F) :
    plim γ0 x = p F γ0 γ1 hlt (plim γ1 x) := by
  have hlts : σ γ0 < σ γ1 := SIdx.succ_lt_mono.mp hlt
  rw [plim_apply, plim_apply, gψ_p_fold γ0, ← x.coh γ0 γ1 hlt, Fepl, gfold_Fep γ0 γ1 hlt hlts,
    gp_funct γ0 (σ γ0) (σ γ1) (SIdx.lt_succ_self γ0) hlts
      (SIdx.lt_trans (SIdx.lt_succ_self γ0) hlts),
    ← gp_funct γ0 γ1 (σ γ1) hlt (SIdx.lt_succ_self γ1) (SIdx.lt_trans (SIdx.lt_succ_self γ0) hlts),
    ← gψ_p_fold γ1]


theorem chain_ext {A : Type _} [OFE A] {c d : Chain A} (h : ∀ n, c n = d n) : c = d := by
  cases c; cases d; congr; exact funext h

/-- The solution is a COFE. Limits of bounded chains of length `n` are obtained by embedding the
limit in `X n`. -/
noncomputable instance SolCar.instCOFE : IsCOFE (SolCar F) where
  compl c := {
    val := fun γ => COFE.compl (c.map (projSol γ))
    coh := fun γ0 γ1 hlt => by
      rw [← COFE.compl_map]
      congr 1
      exact chain_ext fun n => (c n).coh γ0 γ1 hlt }
  conv_compl γ := COFE.conv_compl
  lbcompl {n} hn c := elim n (IsCOFE.lbcompl hn (c.map (plim n)))
  conv_lbcompl {n} hn c m hm :=
    ((elim n).ne.1 (IsCOFE.conv_lbcompl hn _ hm)).trans ((elim_plim n _).lt hm)
  lbcompl_ne {n} hn c1 c2 m hc :=
    (elim n).ne.1 (IsCOFE.lbcompl_ne hn _ _ fun p hp => (plim n).ne.1 (hc p hp))

noncomputable instance SolCar.instInhabited : Inhabited (SolCar F) := ⟨elim (F := F) 0 default⟩

/-- Rocq: `ψ_lim`. -/
noncomputable def ψlim : F (SolCar F) (SolCar F) -n> SolCar F where
  f x := {
    val := fun γ => truncate (σ γ) (map (F := F) (elim γ) (plim γ) x)
    coh := fun γ0 γ1 hlt => by
      rw [Fepl, truncMap_apply]
      refine Truncated.eq_of_dist (A := (FXl F γ0).car) (α := σ γ0) ?_
      refine ((truncate (σ γ0)).ne.1 ((map (F := F) _ _).ne.1 ((expand_truncate (σ γ1) _).le
        (SIdx.lt_le_incl (SIdx.succ_lt_mono.mp hlt))))).trans (Dist.of_eq ?_)
      rw [← OFunctor.map_comp]
      congr 1
      exact map_congr (fun z => (elim_funct γ0 γ1 hlt z).symm)
        (fun z => (plim_funct γ0 γ1 hlt z).symm) x }
  ne := ⟨fun _ _ _ h γ => (truncate (σ γ)).ne.1 ((map (F := F) _ _).ne.1 h)⟩

theorem ψlim_val (x) (γ : SI) :
    (ψlim (F := F) x).val γ = truncate (σ γ) (map (F := F) (elim γ) (plim γ) x) := rfl

/-- The chain whose limit is `ϕlim x`. -/
noncomputable def ϕlimChain (x : SolCar F) : Chain (F (SolCar F) (SolCar F)) where
  chain γ := map (F := F) (plim γ) (elim γ) (expand (σ γ) (x.val γ))
  cauchy {n i} h := by
    rcases SIdx.le_lteq.mp h with hlt | hlt
    · change map (F := F) (plim i) (elim i) (expand (σ i) (x.val i)) ≡{n}≡
        map (F := F) (plim n) (elim n) (expand (σ n) (x.val n))
      rw [← x.coh n i hlt, Fepl, truncMap_apply]
      refine .trans ?_ ((map (F := F) _ _).ne.1 ((expand_truncate (σ n) _).le
        (SIdx.lt_le_incl (SIdx.lt_succ_self n)))).symm
      rw [← OFunctor.map_comp]
      refine OFunctor.map_ne.ne (fun z => ?_) (fun z => ?_) _
      · change plim i z ≡{n}≡ e F n i hlt (plim n z)
        rw [plim_funct n i hlt z]
        exact (ge_p n i hlt _).symm
      · change elim i z ≡{n}≡ elim n (p F n i hlt z)
        rw [elim_funct n i hlt]
        exact (elim i).ne.1 (ge_p n i hlt z).symm
    · subst hlt; exact .rfl

/-- Rocq: `ϕ_lim`. -/
noncomputable def ϕlim : SolCar F -n> F (SolCar F) (SolCar F) where
  f x := COFE.compl (ϕlimChain x)
  ne := ⟨fun k x y h => (COFE.conv_compl (c := ϕlimChain x) (n := k)).trans (Dist.trans
    ((map (F := F) _ _).ne.1 ((expand (σ k)).ne.1 (h k)))
    (COFE.conv_compl (c := ϕlimChain y) (n := k)).symm)⟩

/-- Rocq: `ϕ_lim_ψ_lim_id`. -/
theorem ϕlim_ψlim (x : F (SolCar F) (SolCar F)) : ϕlim (F := F) (ψlim (F := F) x) = x := by
  refine OFE.eq_dist.mpr fun α => COFE.conv_compl.trans ?_
  change map (F := F) (plim α) (elim α) (expand (σ α) (truncate (σ α) _)) ≡{α}≡ x
  refine ((map (F := F) _ _).ne.1 ((expand_truncate (σ α) _).le
    (SIdx.lt_le_incl (SIdx.lt_succ_self α)))).trans ?_
  rw [← OFunctor.map_comp]
  exact (OFunctor.map_ne.ne (fun z => elim_plim α z) (fun z => elim_plim α z) x).trans
    (Dist.of_eq (OFunctor.map_id x))

/-- Rocq: `ψ_lim_ϕ_lim_id`. -/
theorem ψlim_ϕlim (x : SolCar F) : ψlim (F := F) (ϕlim (F := F) x) = x := by
  refine SolCar.ext (funext fun γ => ?_)
  rw [ψlim_val]
  refine Truncated.eq_of_dist (A := (FXl F γ).car) (α := σ γ) ?_
  refine ((truncate (σ γ)).ne.1 ((map (F := F) _ _).ne.1
    (COFE.conv_compl (c := ϕlimChain x) (n := σ γ)))).trans (Dist.of_eq ?_)
  change truncate (σ γ) (map (F := F) (elim γ) (plim γ)
    (map (F := F) (plim (σ γ)) (elim (σ γ)) (expand (σ (σ γ)) (x.val (σ γ))))) = x.val γ
  rw [← OFunctor.map_comp, ← x.coh γ (σ γ) (SIdx.lt_succ_self γ), Fepl, truncMap_apply]
  congr 1
  refine map_congr (fun z => ?_) (fun z => ?_) _
  · change plim (σ γ) (elim γ z) = e F γ (σ γ) _ z
    rw [elim_funct γ (σ γ) (SIdx.lt_succ_self γ), plim_elim]
  · change plim γ (elim (σ γ) z) = p F γ (σ γ) _ z
    rw [plim_funct γ (σ γ) (SIdx.lt_succ_self γ), plim_elim]

/-! ## The solution -/

variable (F) in
/-- The solution of the recursive domain equation `F X X ≅ X` for a contractive functor `F` over an
arbitrary type of step-indices (Rocq: `solver.solution_F`). -/
def Fix : Type (max u v) := SolCar F

noncomputable instance : COFE (Fix F) := inferInstanceAs (COFE (SolCar F))
noncomputable instance : Inhabited (Fix F) := inferInstanceAs (Inhabited (SolCar F))

/-- The isomorphism `F (Fix F) (Fix F) ≅ Fix F`. -/
noncomputable def Fix.iso : OFE.Iso (F (Fix F) (Fix F)) (Fix F) where
  hom := ψlim (F := F)
  inv := ϕlim (F := F)
  hom_inv := ψlim_ϕlim (F := F) _
  inv_hom := ϕlim_ψlim (F := F) _

/-- Rocq: `solution_fold`. -/
noncomputable def Fix.fold : F (Fix F) (Fix F) -n> Fix F := Fix.iso.hom

/-- Rocq: `solution_unfold`. -/
noncomputable def Fix.unfold : Fix F -n> F (Fix F) (Fix F) := Fix.iso.inv

theorem Fix.fold_unfold (x : Fix F) : Fix.fold (Fix.unfold x) = x := Fix.iso.hom_inv

theorem Fix.unfold_fold (x : F (Fix F) (Fix F)) : Fix.unfold (Fix.fold x) = x := Fix.iso.inv_hom


end Iris.COFE.OFunctor.Transfinite
