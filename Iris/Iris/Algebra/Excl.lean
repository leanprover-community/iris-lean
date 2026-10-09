/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Mario Carneiro
-/
module

public import Iris.Algebra.CMRA

@[expose] public section

namespace Iris

variable {SI : Type _} [instSI : SIdx SI]

section excl

@[rocq_alias excl]
inductive Excl α where
  | excl : α → Excl α
  | invalid : Excl α

#rocq_ignore maybe_Excl "std++ `Maybe` class; pattern match instead"

namespace Excl
open OFE ORA

/-! ## COFE -/

#rocq_ignore excl_equiv "OFE is Leibniz; use equality"

@[simp, rocq_alias excl_dist] protected def Dist [OFE SI α] (n : SI) : Excl α → Excl α → Prop
  | excl a, excl b => a ≡{n}≡ b
  | invalid, invalid => True
  | _, _ => False

theorem dist_eqv [OFE SI α] {n : SI} : Equivalence (Excl.Dist (α := α) n) where
  refl {x} := by
    cases x with
    | excl a => exact Dist.of_eq rfl
    | invalid => trivial
  symm {x y} h := by
    cases x <;> cases y <;> try trivial
    exact Dist.symm h
  trans {x y z} h₁ h₂ := by
    cases x <;> cases y <;> cases z <;> try trivial
    exact Dist.trans h₁ h₂

#rocq_ignore excl_ofe_mixin "Not needed"

@[rocq_alias exclO]
instance [OFE SI α] : OFE SI (Excl α) where
  dist := Excl.Dist
  dist_eqv
  eq_dist' {x y} := by
    cases x <;> cases y <;> simp [Excl.Dist, eq_dist (SI := SI)]
  dist_lt {n : SI} {x y m} hn hlt := by
    cases x <;> cases y <;> simp at *
    exact Dist.lt hn hlt

@[rocq_alias Excl_ne]
instance [OFE SI α] : NonExpansive SI excl (α := α) where
  ne _ _ _ a := a

/-- Note: Not an instance, due to instance coherence problems. -/
theorem ne_match [OFE SI α] {B : Type _} [OFE SI B]
    (f : α → B) (hf : NonExpansive SI f) (g : B) :
    NonExpansive SI (fun x : Excl α => match x with | .excl a => f a | .invalid => g) :=
  ⟨fun {n : SI} {x' y'} (h : Excl.Dist n x' y') =>
    match x', y', h with
    | .excl _, .excl _, h => hf.ne h
    | .excl _, .invalid, h => h.elim
    | .invalid, .excl _, h => h.elim
    | .invalid, .invalid, _ => Dist.rfl⟩

@[rocq_alias excl_ofe_discrete]
instance [OFE SI α] [OFE.Discrete SI α] : OFE.Discrete SI (Excl α) where
  discrete_0 {x y} h' := by
    cases x <;> cases y
    · exact congrArg excl (discrete_0 (α := α) h')
    · exact h'.elim
    · exact h'.elim
    · rfl

#rocq_ignore excl_leibniz "Not needed"

@[rocq_alias Excl_discrete]
instance [OFE SI α] {a : α} [h : DiscreteE SI a] : DiscreteE SI (excl a) where
  discrete {x} h' := by
    cases x
    · exact congrArg excl (h.discrete h')
    · exact h'.elim

@[rocq_alias ExclInvalid_discrete]
instance [OFE SI α] : DiscreteE SI (@invalid α) where
  discrete {x} h := by
    cases x
    · exact h.elim
    · rfl

/- Adapted from the corresponding definitions for [Option]. -/
/- This could be simplified if there was an isomorphism lemma for [COFE]s in [OFE.lean]. -/
@[simp] def getD (x : Excl α) (dflt : α) : α :=
  match x with
  | excl a => a
  | invalid => dflt

@[simp, rocq_alias excl_map] def map (f : α → β) : Excl α → Excl β
  | excl a => excl (f a)
  | invalid => invalid

def exclChain [OFE SI α] (c : Chain SI (Excl α)) (a : α) : Chain SI α := by
  refine ⟨fun n => (c n).getD a, fun {n : SI} {i} H => ?_⟩
  dsimp; have := c.cauchy H; revert this
  cases c.chain i <;> cases c.chain n <;> simp [Dist, HasDist.dist]

@[rocq_alias excl_cofe]
instance [SIdxFinite SI] [OFE SI α] [IsCOFE SI α] : IsCOFE SI (Excl α) where
  compl c := (c 0).map fun x => IsCOFE.compl (exclChain c x)
  conv_compl {n : SI} c := by
    have := c.cauchy (i := n) SIdx.le_0_l; revert this
    obtain _|x' := c.chain 0 <;> rcases e : c.chain n with _|y' <;> simp [Dist, HasDist.dist]
    refine fun _ => Dist.trans IsCOFE.conv_compl ?_
    simp [exclChain, e]
  lbcompl := (·.elim)
  conv_lbcompl := (·.elim)
  lbcompl_ne := (·.elim)

/-! ## ORA -/
@[simp] def Valid : Excl α → Prop
  | excl _ => True
  | invalid => False

#rocq_ignore excl_op_instance "Use CMRA instance"
#rocq_ignore excl_pcore_instance "Use CMRA instance"
#rocq_ignore excl_validN_instance "Use CMRA instance"
#rocq_ignore excl_valid_instance "Use CMRA instance"
#rocq_ignore excl_cmra_mixin "Not needed"

instance {α : Type _} : RA (Excl α) where
  pcore _ := none
  op _ _ := invalid
  assoc := rfl
  comm := rfl
  pcore_op_left := nofun
  pcore_idem := nofun

@[instance_reducible] def cmraData [OFE SI α] : CMRAData SI (Excl α) where
  ValidN _ := Valid
  Valid
  op_ne.ne _ _ _ _ := trivial
  pcore_ne := by simp [PCore.pcore]
  validN_ne {n : SI} {x y} h₁ h₂ := by cases x <;> cases y <;> trivial
  valid_iff_validN {x} := by
    constructor
    · intro h n; cases x <;> trivial
    · intro h; cases x <;> simp_all
  validN_le {n n' : SI} {x} h _ := by cases x <;> trivial
  validN_op_left := by simp [Op.op]
  extend {n : SI} {x y₁ y₂} h₁ h₂ := by cases x <;> trivial
  pcore_op_mono := by simp [PCore.pcore]

@[rocq_alias exclR]
instance [OFE SI α] : CMRA SI (Excl α) := ofCMRAData Excl.cmraData

theorem ord_iff [OFE SI α] {x y : Excl α} : x ≼ₒ[SI] y ↔ y = invalid := by
  constructor
  · rintro ⟨z, hz⟩
    exact hz
  · intro h
    exact ⟨invalid, h⟩

@[rocq_alias excl_included]
theorem inc_iff {x y : Excl α} : x ≼ y ↔ y = invalid :=
  ⟨fun ⟨_, hz⟩ => hz, fun h => ⟨invalid, h⟩⟩

theorem ordN_iff [OFE SI α] {x y : Excl α} (n : SI) : x ≼ₒ{n} y ↔ y = invalid := by
  constructor
  · intro ⟨z, hz⟩; cases x <;> cases y <;> first | rfl | exact hz.elim
  · rintro rfl; exists invalid

@[rocq_alias excl_includedN]
theorem incN_iff [OFE SI α] {x y : Excl α} (n : SI) : x ≼{n} y ↔ y = invalid :=
  incN_iff_ordN.trans (ordN_iff n)

@[rocq_alias Excl_inj]
theorem excl_inj {α : Type _} {a b : α} (h : (some (excl a) : Option (Excl α)) = some (excl b)) :
    a = b := Excl.excl.inj (Option.some.inj h)

@[rocq_alias Excl_dist_inj]
theorem excl_dist_inj [OFE SI α] {a b : α} {n : SI}
    (h : (some (excl a) : Option (Excl α)) ≡{n}≡ some (excl b)) : a ≡{n}≡ b :=
  OFE.some_dist_some.mp h

theorem excl_ord [OFE SI α] {a b : α} :
    (some (excl a) : Option (Excl α)) ≼ₒ[SI] some (excl b) ↔ a = b := by
  refine ⟨fun h => ?_, fun h => Or.inl (congrArg excl h)⟩
  rcases h with h | ⟨_, hz⟩
  · exact excl.inj h
  · exact (hz.dist (n := (0 : SI))).elim

@[rocq_alias Excl_included]
theorem excl_included {a b : α} :
    (some (excl a) : Option (Excl α)) ≼ some (excl b) ↔ a = b := by
  refine ⟨fun ⟨z, hz⟩ => ?_, fun h => ⟨none, h ▸ rfl⟩⟩
  cases z with
  | none => exact (excl.inj (Option.some.inj hz)).symm
  | some _ => cases hz

theorem excl_ordN [OFE SI α] {a b : α} {n : SI} :
    (some (excl a) : Option (Excl α)) ≼ₒ{n} some (excl b) ↔ a ≡{n}≡ b := by
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | ⟨_, hz⟩
  · exact h
  · exact (hz : excl b ≡{n}≡ invalid).elim

@[rocq_alias Excl_includedN]
theorem excl_includedN [OFE SI α] {a b : α} {n : SI} :
    (some (excl a) : Option (Excl α)) ≼{n} some (excl b) ↔ a ≡{n}≡ b :=
  incN_iff_ordN.trans excl_ordN

@[rocq_alias excl_validN_inv_l]
theorem validN_inv_some_l [OFE SI α] {n : SI} {mx : Option (Excl α)} {a : α}
    (h : ✓{n} (some (excl a) • mx)) : mx = none := by
  cases mx with
  | none => rfl
  | some _ => exact h.elim

@[rocq_alias excl_validN_inv_r]
theorem validN_inv_some_r [OFE SI α] {n : SI} {mx : Option (Excl α)} {a : α}
    (h : ✓{n} (mx • some (excl a))) : mx = none := by
  cases mx with
  | none => rfl
  | some _ => exact h.elim

@[rocq_alias excl_exclusive]
instance [OFE SI α] {x : Excl α} : Exclusive SI x where exclusive0_l := fun _ a => a

@[rocq_alias excl_cmra_discrete]
instance [OFE SI α] [OFE.Discrete SI α] : ORA.Discrete SI (Excl α) where
  discrete_valid a := a
  discrete_ord := CMRA.ord_of_ord0

theorem invalid_ord [OFE SI α] (ea : Excl α) : ea ≼ₒ[SI] invalid := by exists invalid

@[rocq_alias ExclInvalid_included]
theorem invalid_inc (ea : Excl α) : ea ≼ invalid := inc_iff.mpr rfl

/-! ## Functors -/
@[rocq_alias excl_map_id]
theorem map_id : map id x = x := by
  cases x <;> simp

@[rocq_alias excl_map_compose]
theorem map_comp (f : α → β) (g : β → γ) :
    map (g ∘ f) x = map g (map f x) := by
  cases x <;> simp

@[rocq_alias excl_map_ext]
theorem map_ext {α β : Type _} {x : Excl α} (f g : α → β) (h : ∀ x, f x = g x) : map f x = map g x := by
  cases x <;> simp [h]

@[rocq_alias excl_map_ne]
theorem map_ne [OFE SI α] [OFE SI β] (f : α -n>[SI] β) : NonExpansive SI (map f) where
  ne n x₁ x₂ h := by
    cases x₁ <;> cases x₂ <;> try trivial
    have ⟨hne⟩ := f.ne
    exact hne h

#rocq_ignore Excl_proper "Derivable from NonExpansive.eqv"

@[rocq_alias excl_map_cmra_morphism]
def hom [OFE SI α] [OFE SI β] (f : α -n>[SI] β) : Excl α -C>[SI] Excl β := by
  refine CMRA.Hom.toORA ⟨⟨map f, map_ne f⟩, ?_, ?_, ?_⟩
  · intro n x h; cases x <;> trivial
  · intro x; trivial
  · intro x y; trivial

@[rocq_alias exclO_map]
def oMap [OFE SI α] [OFE SI β] (f : α -n>[SI] β) : Excl α -n>[SI] Excl β := ⟨map f, map_ne f⟩

@[rocq_alias exclO_map_ne]
instance oMap_ne [OFE SI α] [OFE SI β] : NonExpansive SI (oMap (SI := SI) (α := α) (β := β)) where
  ne _ _ _ h x := by cases x with
    | excl _ => exact h _
    | invalid => exact .rfl

@[rocq_alias exclRF]
abbrev ExclOF (F : COFE.OFunctorPre SI) : COFE.OFunctorPre SI :=
  fun A B _ _ => Excl (F A B)

instance {F} [COFE.OFunctor SI F] : RFunctor SI (ExclOF F) where
  cmra := inferInstance
  map f g := hom (COFE.OFunctor.map f g)
  map_ne.ne := by
    intros n f₁ f₂ hf g₁ g₂ hg x
    cases x with
    | excl a =>
      apply COFE.OFunctor.map_ne.ne
      exact hf
      exact hg
    | invalid => trivial
  map_id {_ _} _ _ x := by
    cases x
    · exact congrArg excl (COFE.OFunctor.map_id _)
    · trivial
  map_comp f g f' g' x := by
    cases x
    · exact congrArg excl (COFE.OFunctor.map_comp _ _ _ _ _)
    · trivial

instance instRFunctorAffine {F} [COFE.OFunctor SI F] : RFunctorAffine SI (ExclOF F) where
  affine := inferInstance

@[rocq_alias exclRF_contractive]
instance {F} [COFE.OFunctorContractive SI F] : RFunctorContractive SI (ExclOF F) where
  map_contractive.1 {n : SI} {x y} HKL z := by
    rewrite [RFunctor.map]
    cases z
    · apply COFE.OFunctorContractive.map_contractive.1
      exact HKL
    · trivial

end Excl

end excl

end Iris
