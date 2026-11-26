/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Graf, Sergei Stepanenko
-/
module

public import Iris.Algebra.Enriched
public meta import Iris.Std.RocqPorting

/-!
For a given locally contractive functor with e : F(1, 1), the solver can be called:
- unconditionally classically under classical truncations;
- conditionally constructively if the functor is truncatable;
- unconditionally constructively under finite step-index types.
See `Iris.Examples.Fix` for concrete examples.
-/

@[expose] public section

universe v w

namespace Iris.Enriched

open OFE Iris.COFE

variable {SI : Type w} [SIdx SI]
local stepindex SI

namespace COFE

abbrev CofeObj := (A : Type (max v w)) × COFE A

instance (A : CofeObj.{v, w}) : COFE A.1 := A.2

instance instEnrichedCat : EnrichedCat CofeObj.{v, w} where
  Hom A B := A.1 -n> B.1
  cofe _ _ := inferInstance
  id _ := OFE.Hom.id
  comp g f := g.comp f
  comp_ne {_ _ _ _ _ g' _ _} hg hf := fun x => (hg _).trans (g'.ne.ne (hf x))
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance instHasTerminal : HasTerminal CofeObj.{v, w} where
  terminal := ⟨ULift.{max v w} Unit, inferInstance⟩
  toTerminal _ := (⟨fun _ => ⟨()⟩, ⟨fun _ _ _ _ => .rfl⟩⟩ : _ -n> ULift.{max v w} Unit)
  toTerminal_unique _ := OFE.Hom.ext (funext fun _ => rfl)

instance {A B : CofeObj.{v, w}} : CoeFun (A ⟶ₑ B) fun _ => A.1 → B.1 :=
  inferInstanceAs (CoeFun (A.1 -n> B.1) _)

theorem Hom.congr_fun {A B : CofeObj.{v, w}} {f g : A ⟶ₑ B} (h : f = g) (x : A.1) :
    f x = g x :=
  h ▸ rfl

end COFE

open COFE

theorem Determined.points {K : LimitCut} {Y : CofeObj.{v, w}} (h : Determined K Y) :
    PointsDetermined K Y.1 := fun x y hxy =>
  Hom.congr_fun (h (⟨fun _ => x, ⟨fun _ _ _ _ => .rfl⟩⟩ : HasTerminal.terminal SI ⟶ₑ Y)
    ⟨fun _ => y, ⟨fun _ _ _ _ => .rfl⟩⟩ fun m hm _ => hxy m hm) ⟨()⟩

theorem Determined.of_points {K : LimitCut} {Y : CofeObj.{v, w}}
    (h : PointsDetermined K Y.1) : Determined K Y :=
  fun _ _ hg => OFE.Hom.ext (funext fun z => h _ _ fun m hm => hg m hm z)

namespace COFE

section TowerLimit

variable {P : Site} (T : Tower CofeObj.{v, w} P) (hT : T.Lawful)

@[ext, rocq_alias solver.tower]
structure TowerLimit (hT : T.Lawful) where
  π : ∀ β (hβ : P.mem β), (T.X hβ).1
  proj_π {β δ} {hβ : P.mem β} {hδ : P.mem δ} (h : β < δ) : T.proj hβ hδ h (π δ hδ) = π β hβ

instance : OFE (TowerLimit T hT) where
  dist n x y := ∀ β hβ, x.π β hβ ≡{n}≡ y.π β hβ
  dist_eqv := {
    refl _ _ _ := .rfl
    symm h β hβ := (h β hβ).symm
    trans h h' β hβ := (h β hβ).trans (h' β hβ)
  }
  eq_dist' := ⟨fun h => h ▸ fun _ _ _ => .rfl,
    fun h => TowerLimit.ext (funext fun β => funext fun hβ => OFE.eq_dist.mpr fun n => h n β hβ)⟩
  dist_lt h hlt β hβ := (h β hβ).lt hlt

namespace TowerLimit

@[rocq_alias solver.project]
def proj {β} (hβ : P.mem β) : TowerLimit T hT -n> (T.X hβ).1 :=
  ⟨fun x => x.π β hβ, ⟨fun _ _ _ h => h β hβ⟩⟩

include hT in
theorem proj_hom_apply {β δ n : SI} {hβ : P.mem β} {hδ : P.mem δ} {hn : P.mem n} (hlt : β < δ)
    (x : (T.X hn).1) : T.proj hβ hδ hlt (T.hom hδ hn x) = T.hom hβ hn x :=
  Hom.congr_fun (Tower.proj_comp_hom hT hlt) x

@[rocq_alias solver.embed]
def emb {n : SI} (hn : P.mem n) : (T.X hn).1 -n> TowerLimit T hT where
  f x := ⟨fun _ hβ => T.hom hβ hn x, fun hlt => proj_hom_apply T hT hlt x⟩
  ne := ⟨fun _ _ _ h _ hβ => (T.hom hβ hn).ne.ne h⟩

@[rocq_alias solver.embed_tower]
theorem emb_π_dist {n : SI} (hn : P.mem n) (x : TowerLimit T hT) {m} (hm : m < n) :
    emb T hT hn (x.π n hn) ≡{m}≡ x := by
  intro β hβ
  change T.hom hβ hn (x.π n hn) ≡{m}≡ x.π β hβ
  rcases SIdx.lt_trichotomyT β n with h | rfl | h
  · rw [T.hom_lt h]
    exact .of_eq (x.proj_π h)
  · rw [T.hom_self]
    exact .rfl
  · rw [T.hom_gt h, ← x.proj_π (hδ := hβ) h]
    exact hT.emb_comp_proj h hm (x.π β hβ)

def diag {n : SI} (hn : SIdx.Limit n) (hnP : ¬ P.mem n) (c : BChain (TowerLimit T hT) n) :
    TowerLimit T hT where
  π _ hβ := IsCOFE.lbcompl hn (c.map (proj T hT hβ))
  proj_π {_ _ hβ hδ} hlt := Determined.points (hT.determined hβ) _ _ fun m hm => by
    have hmn := lt_of_mem_seg hn (Site.lt_of_not_mem hnP hβ) hm
    refine ((T.proj hβ hδ hlt).ne.ne (IsCOFE.conv_lbcompl hn _ hmn)).trans ?_
    refine (Dist.of_eq ((c.bchain m hmn).proj_π hlt)).trans ?_
    exact (IsCOFE.conv_lbcompl hn (c.map (proj T hT hβ)) hmn).symm

end TowerLimit

open TowerLimit in
instance : IsCOFE (TowerLimit T hT) where
  compl c := ⟨fun _ hβ => COFE.compl (c.map (proj T hT hβ)), fun {_ _ hβ hδ} hlt => by
    change T.proj hβ hδ hlt (COFE.compl _) = _
    rw [← COFE.compl_map, ← Chain.map_comp]
    congr 2
    exact OFE.Hom.ext (funext fun (x : TowerLimit T hT) => x.proj_π hlt)⟩
  conv_compl _ _ := COFE.conv_compl
  lbcompl {n} hn c :=
    if h : P.mem n then emb T hT h (IsCOFE.lbcompl hn (c.map (proj T hT h)))
    else diag T hT hn h c
  conv_lbcompl {n} hn c m hm := by
    by_cases h : P.mem n
    · rw [dite_eq_left h]
      exact ((emb T hT h).ne.1 (IsCOFE.conv_lbcompl hn _ hm)).trans (emb_π_dist T hT h _ hm)
    · rw [dite_eq_right h]
      exact fun _ hβ => IsCOFE.conv_lbcompl hn (c.map (proj T hT hβ)) hm
  lbcompl_ne {n} hn c1 c2 m hc := by
    by_cases h : P.mem n
    · simp only [dite_eq_left h]
      exact (emb T hT h).ne.1
        (IsCOFE.lbcompl_ne hn _ _ fun p hp => (proj T hT h).ne.1 (hc p hp))
    · simp only [dite_eq_right h]
      exact fun β hβ => IsCOFE.lbcompl_ne hn _ _ fun p hp => hc p hp β hβ

#rocq_ignore solver.tower_equiv "Included in the OFE (TowerLimit T hT) instance"
#rocq_ignore solver.tower_dist "Included in the OFE (TowerLimit T hT) instance"
#rocq_ignore solver.tower_ofe_mixin "Included in the OFE (TowerLimit T hT) instance"
#rocq_ignore solver.tower_cofe "Use the IsCOFE (TowerLimit T hT) instance"
#rocq_ignore solver.tower_compl "Use the IsCOFE (TowerLimit T hT) instance"
#rocq_ignore solver.tower_car_ne "Implicit in TowerLimit.proj"

def TowerLimit.cofeObj : CofeObj.{v, w} := ⟨TowerLimit T hT, inferInstance⟩

def TowerLimit.lift {Y : CofeObj.{v, w}} (g : ∀ {β} (hβ : P.mem β), Y ⟶ₑ T.X hβ)
    (hg : ∀ {β δ} {hβ : P.mem β} {hδ : P.mem δ} (h : β < δ), T.proj hβ hδ h ⊚ g hδ = g hβ) :
    Y ⟶ₑ TowerLimit.cofeObj T hT :=
  (⟨fun y => ⟨fun _ hβ => g hβ y, fun h => Hom.congr_fun (hg h) y⟩,
    ⟨fun _ _ _ h _ hβ => (g hβ).ne.ne h⟩⟩ : Y.1 -n> TowerLimit T hT)

end TowerLimit

instance instHasTowerLimits : HasTowerLimits CofeObj.{v, w} where
  lim hT := TowerLimit.cofeObj _ hT
  π hT _ hβ := TowerLimit.proj _ hT hβ
  proj_comp_π hT := fun h => OFE.Hom.ext (funext fun (x : TowerLimit _ hT) => x.proj_π h)
  lift hT := TowerLimit.lift _ hT
  π_comp_lift _ := fun _ _ => rfl
  ext_dist _ := fun h y _ hβ => h hβ y

section Solution

variable (F : ∀ (α β : Type (max v w)) [COFE α] [COFE β], Type (max v w))
  [OFunctorContractive F] [∀ (α β : Type (max v w)) [COFE α] [COFE β], IsCOFE (F α β)]

def oFunctorObj (A B : CofeObj.{v, w}) : CofeObj.{v, w} := ⟨F A.1 B.1, inferInstance⟩

instance instEFunctor : EFunctor (oFunctorObj F) where
  map f g := (OFunctor.map (F := F) f g : _ -n> _)
  map_contractive := OFunctorContractive.map_contractive.distLater_dist
  map_id _ _ := OFE.Hom.ext (funext fun x => OFunctor.map_id (F := F) x)
  map_comp f g f' g' := OFE.Hom.ext (funext fun x => OFunctor.map_comp (F := F) f g f' g' x)

@[reducible] def truncatableOfTruncations
    (t : ∀ (K : LimitCut) (A : CofeObj.{v, w}), Determined K A → Truncation K (F A.1 A.1)) :
    ETruncatable (oFunctorObj F) where
  trunc hA := ⟨(t _ _ hA).Fixed, inferInstance⟩
  proj hA := Truncation.Fixed.proj (t _ _ hA)
  rep hA := Truncation.Fixed.inclusion (t _ _ hA)
  proj_rep _ := OFE.Hom.ext (funext fun y => Subtype.ext y.2)
  rep_proj hA := fun hm x => (t _ _ hA).conv x _ hm
  determined _ := Determined.of_points (Truncation.Fixed.determined _)

instance (priority := low) instETruncatable [OFunctorTruncatable F] :
    ETruncatable (oFunctorObj F) :=
  truncatableOfTruncations F fun _ _ hA => OFunctorTruncatable.truncation hA.points

instance instHasSeed [Inhabited (F (ULift.{max v w} Unit) (ULift.{max v w} Unit))] :
    HasSeed (oFunctorObj F) where
  seed := (⟨fun _ => default, ⟨fun _ _ _ _ => .rfl⟩⟩ :
    _ -n> F (ULift.{max v w} Unit) (ULift.{max v w} Unit))

end Solution

end COFE

end Iris.Enriched

namespace Iris.COFE.OFunctor

open OFE Iris.Enriched Iris.Enriched.COFE

variable {SI : Type w} [SIdx SI]
local stepindex SI
variable (F : ∀ (α β : Type (max v w)) [COFE α] [COFE β], Type (max v w)) [OFunctorContractive F]
  [∀ (α β : Type (max v w)) [COFE α] [COFE β], IsCOFE (F α β)]
  [Inhabited (F (ULift.{max v w} Unit) (ULift.{max v w} Unit))]
  [ETruncatable (oFunctorObj F)]

#rocq_ignore solution "Use OFE.Iso + Inhabited + COFE"
#rocq_ignore solver.A' "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.A_cofe "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.f "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.g "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.f_S "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.g_S "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.gf "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.fg "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.ff "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.gg "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.ggff "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.f_tower "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.ff_tower "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.gg_tower "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.coerce "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.coerce_id "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.coerce_proper "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.coerce_f "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.g_coerce "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.embed_coerce "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.embed' "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.embed_ne "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.g_embed_coerce "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.gg_gg "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.ff_ff "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.embed_f "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.tower_chain "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.unfold_chain "Internal to Rocq's ℕ-indexed construction; see Enriched.lean"
#rocq_ignore solver.result "Use `Fix F` with Inhabited + COFE instances and Fix.iso"

@[rocq_alias solver.T]
def Fix : Type (max v w) := (Enriched.Fix (oFunctorObj F)).1

instance instCOFEFix : COFE (Fix F) := (Enriched.Fix (oFunctorObj F)).2

#rocq_ignore solver.tower_inhabited "Implicit in Lean's Inhabited (Fix F) instance"
instance : Inhabited (Fix F) := ⟨(Enriched.Fix.point (oFunctorObj F)) ⟨()⟩⟩

variable {F}

opaque Fix.iso : OFE.Iso (F (Fix F) (Fix F)) (Fix F) := {
  hom := Enriched.Fix.fold (oFunctorObj F)
  inv := Enriched.Fix.unfold (oFunctorObj F)
  hom_inv := Hom.congr_fun (Enriched.Fix.fold_comp_unfold (oFunctorObj F)) _
  inv_hom := Hom.congr_fun (Enriched.Fix.unfold_comp_fold (oFunctorObj F)) _ }

@[rocq_alias solver.fold]
def Fix.fold : F (Fix F) (Fix F) -n> Fix F := Fix.iso.hom
#rocq_ignore solver.fold_ne "Implicit in the OFE.Iso structure"

@[rocq_alias solver.unfold]
def Fix.unfold : Fix F -n> F (Fix F) (Fix F) := Fix.iso.inv
#rocq_ignore solver.unfold_ne "Implicit in the OFE.Iso structure"

theorem Fix.fold_unfold (X : Fix F) : Fix.fold (Fix.unfold X) = X := Fix.iso.hom_inv

theorem Fix.unfold_fold (X : F (Fix F) (Fix F)) : Fix.unfold (Fix.fold X) = X := Fix.iso.inv_hom

attribute [irreducible] Fix instCOFEFix Fix.fold Fix.unfold

end Iris.COFE.OFunctor
