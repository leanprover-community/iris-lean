/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Graf, Sergei Stepanenko
-/
module

public import Iris.Algebra.Enriched
public meta import Iris.Std.RocqPorting

@[expose] public section

universe v w

namespace Iris.Enriched

open OFE Iris.COFE

variable {SI : Type v} [SIdx SI]

/- The solver needs a successor operation (see `Enriched`); Iris-Rocq's solver does not. -/
variable [SIdxSucc SI]

namespace COFE

def PointsDetermined (K : LimitCut SI) (A : Type _) [OFE SI A] : Prop :=
  ∀ (x y : A), K.dist x y → x = y

variable (SI) in
abbrev CofeObj := (A : Type (max v w)) × COFE SI A

instance (A : CofeObj.{v, w} SI) : COFE SI A.1 := A.2

instance instEnrichedCat : EnrichedCat SI (CofeObj.{v, w} SI) where
  Hom A B := A.1 -n>[SI] B.1
  cofe _ _ := inferInstance
  id _ := OFE.Hom.id
  comp g f := g.comp f
  comp_ne {_ _ _ _ _ g' _ _} hg hf := fun x => (hg _).trans (g'.ne.ne (hf x))
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance instHasTerminal : HasTerminal SI (CofeObj.{v, w} SI) where
  one := ⟨ULift.{max v w} Unit, inferInstance⟩
  toOne _ := (⟨fun _ => ⟨()⟩, ⟨fun _ _ _ _ => .rfl⟩⟩ : _ -n>[SI] ULift.{max v w} Unit)
  toOne_unique _ := OFE.Hom.ext (funext fun _ => rfl)

end COFE

open COFE

abbrev EnrichedCat.Hom.toOFEHom {A B : CofeObj.{v, w} SI} (f : Hom SI A B) : A.1 -n>[SI] B.1 := f

omit [SIdxSucc SI] in
theorem Determined.points {K : LimitCut SI} {Y : CofeObj.{v, w} SI} (h : Determined K Y) :
    PointsDetermined K Y.1 := fun x y hxy =>
  congrArg (fun g : Hom SI (HasTerminal.one SI) Y => g.toOFEHom ⟨()⟩)
    (h (⟨fun _ => x, ⟨fun _ _ _ _ => .rfl⟩⟩ : Hom SI (HasTerminal.one SI) Y)
      ⟨fun _ => y, ⟨fun _ _ _ _ => .rfl⟩⟩ fun m hm _ => hxy m hm)

omit [SIdxSucc SI] in
theorem Determined.of_points {K : LimitCut SI} {Y : CofeObj.{v, w} SI}
    (h : PointsDetermined K Y.1) : Determined K Y :=
  fun _ _ hg => OFE.Hom.ext (funext fun z => h _ _ fun m hm => hg m hm z)

namespace COFE

section TowerLimit

variable {P : Site SI} (T : Tower (CofeObj.{v, w} SI) P) (hT : T.Lawful)

@[ext, rocq_alias solver.tower]
structure TowerLimit (hT : T.Lawful) where
  π : ∀ (β : SI) (hβ : P.mem β), (T.X β hβ).1
  proj_π : ∀ (β δ : SI) hβ hδ (h : β < δ), (T.proj β δ hβ hδ h).toOFEHom (π δ hδ) = π β hβ

instance : OFE SI (TowerLimit T hT) where
  dist n x y := ∀ (β : SI) hβ, x.π β hβ ≡{n}≡ y.π β hβ
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
def proj (β : SI) hβ : TowerLimit T hT -n>[SI] (T.X β hβ).1 :=
  ⟨fun x => x.π β hβ, ⟨fun _ _ _ h => h β hβ⟩⟩

include hT in
theorem proj_hom_apply (n : SI) (hn : P.mem n) (β δ : SI) hβ hδ (hlt : β < δ) x :
    (T.proj β δ hβ hδ hlt).toOFEHom ((T.hom δ n hδ hn).toOFEHom x) =
      (T.hom β n hβ hn).toOFEHom x :=
  congrArg (fun g : Hom SI _ _ => g.toOFEHom x) (Tower.proj_comp_hom hT n hn β δ hβ hδ hlt)

@[rocq_alias solver.embed]
def emb (n : SI) (hn : P.mem n) : (T.X n hn).1 -n>[SI] TowerLimit T hT where
  f x := ⟨fun β hβ => (T.hom β n hβ hn).toOFEHom x, fun β δ hβ hδ hlt =>
    proj_hom_apply T hT n hn β δ hβ hδ hlt x⟩
  ne := ⟨fun _ _ _ h β hβ => (T.hom β n hβ hn).toOFEHom.ne.ne h⟩

@[rocq_alias solver.embed_tower]
theorem emb_π_dist (n : SI) (hn : P.mem n) (x : TowerLimit T hT) (m : SI)
    (hm : m < n) :
    emb T hT n hn (x.π n hn) ≡{m}≡ x := by
  intro β hβ
  change (T.hom β n hβ hn).toOFEHom (x.π n hn) ≡{m}≡ x.π β hβ
  rcases SIdx.lt_trichotomyT β n with h | rfl | h
  · rw [T.hom_lt hβ hn h]
    exact .of_eq (x.proj_π β n hβ hn h)
  · rw [T.hom_self hβ hn]
    exact .rfl
  · rw [T.hom_gt hβ hn h, ← x.proj_π n β hn hβ h]
    exact hT.emb_comp_proj n β hn hβ h m hm (x.π β hβ)

theorem lt_of_mem_seg {n a m : SI} (hl : SIdx.Limit n) (ha : a < n) (hm : (seg a).mem m) :
    m < n := by
  rcases SIdx.lt_ge_cases n m with h | h
  · exact h
  · exact absurd ⟨n, hl, ha, h⟩ hm

def diag {n : SI} (hn : SIdx.Limit n) (hnP : ¬ P.mem n) (c : BChain SI (TowerLimit T hT) n) :
    TowerLimit T hT where
  π β hβ := IsCOFE.lbcompl hn (c.map (proj T hT β hβ))
  proj_π β δ hβ hδ hlt := Determined.points (hT.determined β hβ) _ _ fun m hm => by
    have hmn := lt_of_mem_seg hn (Site.lt_of_not_mem hnP hβ) hm
    refine ((T.proj β δ hβ hδ hlt).toOFEHom.ne.ne (IsCOFE.conv_lbcompl hn _ hmn)).trans ?_
    refine (Dist.of_eq ((c.bchain m hmn).proj_π β δ hβ hδ hlt)).trans ?_
    exact (IsCOFE.conv_lbcompl hn (c.map (proj T hT β hβ)) hmn).symm

end TowerLimit

open TowerLimit in
instance : IsCOFE SI (TowerLimit T hT) where
  compl c := ⟨fun β hβ => COFE.compl (c.map (proj T hT β hβ)), fun β δ hβ hδ hlt => by
    change (T.proj β δ hβ hδ hlt).toOFEHom (COFE.compl _) = _
    rw [← COFE.compl_map, ← Chain.map_comp]
    congr 2
    exact OFE.Hom.ext (funext fun (x : TowerLimit T hT) => x.proj_π β δ hβ hδ hlt)⟩
  conv_compl _ _ := COFE.conv_compl
  lbcompl {n : SI} hn c :=
    if h : P.mem n then emb T hT n h (IsCOFE.lbcompl hn (c.map (proj T hT n h)))
    else diag T hT hn h c
  conv_lbcompl {n : SI} hn c m hm := by
    by_cases h : P.mem n
    · rw [dite_eq_left h]
      exact ((emb T hT n h).ne.1 (IsCOFE.conv_lbcompl hn _ hm)).trans
        (emb_π_dist T hT n h _ m hm)
    · rw [dite_eq_right h]
      exact fun β hβ => IsCOFE.conv_lbcompl hn (c.map (proj T hT β hβ)) hm
  lbcompl_ne {n : SI} hn c1 c2 m hc := by
    by_cases h : P.mem n
    · simp only [dite_eq_left h]
      exact (emb T hT n h).ne.1
        (IsCOFE.lbcompl_ne hn _ _ fun p hp => (proj T hT n h).ne.1 (hc p hp))
    · simp only [dite_eq_right h]
      exact fun β hβ => IsCOFE.lbcompl_ne hn _ _ fun p hp => hc p hp β hβ

#rocq_ignore solver.tower_equiv "Included in the OFE (TowerLimit T hT) instance"
#rocq_ignore solver.tower_dist "Included in the OFE (TowerLimit T hT) instance"
#rocq_ignore solver.tower_ofe_mixin "Included in the OFE (TowerLimit T hT) instance"
#rocq_ignore solver.tower_cofe "Use the IsCOFE SI (TowerLimit T hT) instance"
#rocq_ignore solver.tower_compl "Use the IsCOFE SI (TowerLimit T hT) instance"
#rocq_ignore solver.tower_car_ne "Implicit in TowerLimit.proj"

def TowerLimit.cofeObj : CofeObj.{v, w} SI := ⟨TowerLimit T hT, inferInstance⟩

def TowerLimit.lift {Y : CofeObj.{v, w} SI} (g : ∀ (β : SI) hβ, Hom SI Y (T.X β hβ))
    (hg : ∀ (β δ : SI) hβ hδ (h : β < δ), T.proj β δ hβ hδ h ⊚ g δ hδ = g β hβ) :
    Hom SI Y (TowerLimit.cofeObj T hT) :=
  (⟨fun y => ⟨fun β hβ => (g β hβ).toOFEHom y, fun β δ hβ hδ h =>
      congrArg (fun k : Hom SI Y (T.X β hβ) => k.toOFEHom y) (hg β δ hβ hδ h)⟩,
    ⟨fun _ _ _ h β hβ => (g β hβ).toOFEHom.ne.ne h⟩⟩ : Y.1 -n>[SI] TowerLimit T hT)

end TowerLimit

instance instHasTowerLimits : HasTowerLimits SI (CofeObj.{v, w} SI) where
  lim T hT := TowerLimit.cofeObj T hT
  π T hT β hβ := TowerLimit.proj T hT β hβ
  proj_comp_π T hT β δ hβ hδ h :=
    OFE.Hom.ext (funext fun (x : TowerLimit T hT) => x.proj_π β δ hβ hδ h)
  lift T hT _ g hg := TowerLimit.lift T hT g hg
  π_comp_lift _ _ _ _ _ _ _ := rfl
  ext_dist _ _ _ _ _ _ h := fun y β hβ => h β hβ y

structure Truncation (K : LimitCut SI) (A : Type _) [OFE SI A] where
  truncate : A -n>[SI] A
  conv : ∀ x (m : SI), K.mem m → truncate x ≡{m}≡ x
  truncated : ∀ x y, K.dist x y → truncate x = truncate y

namespace Truncation

variable {K : LimitCut SI} {A : Type _} [COFE SI A] (t : Truncation K A)

omit [SIdxSucc SI] in
theorem truncate_truncate (x : A) : t.truncate (t.truncate x) = t.truncate x :=
  t.truncated _ _ fun m hm => t.conv x m hm

def Fixed : Type _ := {x : A // t.truncate x = x}

instance : OFE SI t.Fixed := inferInstanceAs (OFE SI {x : A // t.truncate x = x})

def Fixed.proj : A -n>[SI] t.Fixed :=
  ⟨fun x => ⟨t.truncate x, t.truncate_truncate x⟩, ⟨fun _ _ _ h => t.truncate.ne.ne h⟩⟩

def Fixed.inclusion : t.Fixed -n>[SI] A := ⟨Subtype.val, ⟨fun _ _ _ h => h⟩⟩

instance : IsCOFE SI t.Fixed where
  compl c := Fixed.proj t (COFE.compl (c.map (Fixed.inclusion t)))
  conv_compl {n c} := by
    change t.truncate (COFE.compl (c.map (Fixed.inclusion t))) ≡{n}≡ (c n).val
    rw [← (c n).2]
    exact (Fixed.proj t).ne.ne (COFE.conv_compl (c := c.map (Fixed.inclusion t)))
  lbcompl hl c := Fixed.proj t (IsCOFE.lbcompl hl (c.map (Fixed.inclusion t)))
  conv_lbcompl hl c m hm := by
    change t.truncate (IsCOFE.lbcompl hl (c.map (Fixed.inclusion t))) ≡{m}≡ (c.bchain m hm).val
    rw [← (c.bchain m hm).2]
    exact (Fixed.proj t).ne.ne (IsCOFE.conv_lbcompl hl (c.map (Fixed.inclusion t)) hm)
  lbcompl_ne hl _ _ _ hc :=
    (Fixed.proj t).ne.ne (IsCOFE.lbcompl_ne hl _ _ fun p hp => hc p hp)

omit [SIdxSucc SI] in
theorem Fixed.determined : PointsDetermined K t.Fixed := fun x y h =>
  Subtype.ext (x.2 ▸ y.2 ▸ t.truncated _ _ h)

end Truncation

section Classical

variable (K : LimitCut SI) {A : Type _} [COFE SI A]

noncomputable def classicalRep (x : A) : A := @Classical.epsilon A ⟨x⟩ fun y => K.dist x y

omit [SIdxSucc SI] in
theorem classicalRep_spec (x : A) : K.dist x (classicalRep K x) :=
  @Classical.epsilon_spec A (fun y => K.dist x y) ⟨x, fun _ _ => .rfl⟩

omit [SIdxSucc SI] in
theorem classicalRep_congr {x y : A} (h : K.dist x y) : classicalRep K x = classicalRep K y := by
  unfold classicalRep
  congr 1
  exact funext fun _ => propext ⟨fun hz n hn => (h n hn).symm.trans (hz n hn),
    fun hz n hn => (h n hn).trans (hz n hn)⟩

noncomputable def classicalTruncation : Truncation K A where
  truncate := ⟨classicalRep K, ⟨fun m x y h => by
    by_cases hm : K.mem m
    · exact (classicalRep_spec K x m hm).symm.trans (h.trans (classicalRep_spec K y m hm))
    · refine .of_eq (classicalRep_congr K fun n hn => h.le ?_)
      rcases SIdx.le_total (n := n) (m := m) with h' | h'
      · exact h'
      · exact absurd (K.down h' hn) hm⟩⟩
  conv x m hm := (classicalRep_spec K x m hm).symm
  truncated _ _ h := classicalRep_congr K h

end Classical

section Solution

variable (F : ∀ (α β : Type (max v w)) [COFE SI α] [COFE SI β], Type (max v w))
  [OFunctorContractive SI F]
  [∀ (α β : Type (max v w)) [COFE SI α] [COFE SI β], IsCOFE SI (F α β)]

def oFunctorObj (A B : CofeObj.{v, w} SI) : CofeObj.{v, w} SI := ⟨F A.1 B.1, inferInstance⟩

instance instEFunctor : EFunctor SI (oFunctorObj F) where
  map f g := (OFunctor.map (F := F) f g : _ -n>[SI] _)
  map_contractive := OFunctorContractive.map_contractive.distLater_dist
  map_id _ _ := OFE.Hom.ext (funext fun x => OFunctor.map_id (F := F) x)
  map_comp f g f' g' := OFE.Hom.ext (funext fun x => OFunctor.map_comp (F := F) f g f' g' x)

@[reducible] def truncatableOfTruncations
    (t : ∀ (K : LimitCut SI) (A : CofeObj.{v, w} SI), Determined K A → Truncation K (F A.1 A.1)) :
    Truncatable SI (oFunctorObj F) where
  trunc K A hA := ⟨(t K A hA).Fixed, inferInstance⟩
  proj K A hA := Truncation.Fixed.proj (t K A hA)
  rep K A hA := Truncation.Fixed.inclusion (t K A hA)
  proj_rep _ _ _ := OFE.Hom.ext (funext fun y => Subtype.ext y.2)
  rep_proj K A hA m hm := fun x => (t K A hA).conv x m hm
  determined _ _ _ := Determined.of_points (Truncation.Fixed.determined _)

/-- Truncations by choice for every functor. Not an instance, so that using choice is explicit:
enable it with `attribute [local instance] classicalOFunctorTruncatable`. -/
@[reducible] noncomputable def classicalOFunctorTruncatable :
    Truncatable SI (oFunctorObj F) :=
  truncatableOfTruncations F fun K _ _ => classicalTruncation K

instance instHasSeed [Inhabited (F (ULift.{max v w} Unit) (ULift.{max v w} Unit))] :
    HasSeed SI (oFunctorObj F) where
  seed := (⟨fun _ => default, ⟨fun _ _ _ _ => .rfl⟩⟩ :
    _ -n>[SI] F (ULift.{max v w} Unit) (ULift.{max v w} Unit))

end Solution

end COFE

end Iris.Enriched

namespace Iris.COFE.OFunctor

open OFE Iris.Enriched Iris.Enriched.COFE

variable {SI : Type v} [SIdx SI] [SIdxSucc SI]
variable (F : ∀ (α β : Type (max v w)) [COFE SI α] [COFE SI β], Type (max v w))
  [OFunctorContractive SI F]
  [∀ (α β : Type (max v w)) [COFE SI α] [COFE SI β], IsCOFE SI (F α β)]
  [Inhabited (F (ULift.{max v w} Unit) (ULift.{max v w} Unit))]
  [Truncatable SI (oFunctorObj F)]

#rocq_ignore solution "Use OFE.Iso + Inhabited + COFE"
#rocq_ignore solver.A' "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.A_cofe "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.f "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.g "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.f_S "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.g_S "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.gf "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.fg "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.ff "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.gg "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.ggff "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.f_tower "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.ff_tower "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.gg_tower "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.coerce "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.coerce_id "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.coerce_proper "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.coerce_f "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.g_coerce "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.embed_coerce "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.embed' "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.embed_ne "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.g_embed_coerce "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.gg_gg "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.ff_ff "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.embed_f "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.tower_chain "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.unfold_chain "Internal to the old nat-indexed solver; see Enriched.lean"
#rocq_ignore solver.result "Use `Fix F` with Inhabited + COFE instances and Fix.iso"

@[rocq_alias solver.T]
def Fix : Type (max v w) := (Enriched.Fix SI (oFunctorObj F)).1

instance instCOFEFix : COFE SI (Fix F) := (Enriched.Fix SI (oFunctorObj F)).2

#rocq_ignore solver.tower_inhabited "Implicit in Lean's Inhabited (Fix F) instance"
instance : Inhabited (Fix F) :=
  ⟨(Enriched.Fix.point (oFunctorObj F)).toOFEHom ⟨()⟩⟩

variable {F}

def Fix.iso : OFE.Iso SI (F (Fix F) (Fix F)) (Fix F) where
  hom := Enriched.Fix.fold (SI := SI) (oFunctorObj (SI := SI) F)
  inv := Enriched.Fix.unfold (SI := SI) (oFunctorObj (SI := SI) F)
  hom_inv := congrArg (fun g : EnrichedCat.Hom SI _ _ => g.toOFEHom _)
    (Enriched.Fix.fold_comp_unfold (F := oFunctorObj (SI := SI) F))
  inv_hom := congrArg (fun g : EnrichedCat.Hom SI _ _ => g.toOFEHom _)
    (Enriched.Fix.unfold_comp_fold (F := oFunctorObj F))

@[rocq_alias solver.fold]
def Fix.fold : F (Fix F) (Fix F) -n>[SI] Fix F := Fix.iso.hom
#rocq_ignore solver.fold_ne "Implicit in the OFE.Iso structure"

@[rocq_alias solver.unfold]
def Fix.unfold : Fix F -n>[SI] F (Fix F) (Fix F) := Fix.iso.inv
#rocq_ignore solver.unfold_ne "Implicit in the OFE.Iso structure"

theorem Fix.fold_unfold (X : Fix F) : Fix.fold (Fix.unfold X) = X := Fix.iso.hom_inv

theorem Fix.unfold_fold (X : F (Fix F) (Fix F)) : Fix.unfold (Fix.fold X) = X := Fix.iso.inv_hom

attribute [irreducible] Fix instCOFEFix Fix.fold Fix.unfold Fix.iso

end Iris.COFE.OFunctor
