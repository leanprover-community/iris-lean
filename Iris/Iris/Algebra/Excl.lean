/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Mario Carneiro
-/
module

public import Iris.Algebra.CMRA

@[expose] public section

namespace Iris

variable {SI : stepindex (Type _)} [instSI : SIdx SI]
local stepindex SI

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

@[indexed, simp, rocq_alias excl_dist] protected def Dist [OFE α] (n : SI) : Excl α → Excl α → Prop
  | excl a, excl b => a ≡{n}≡ b
  | invalid, invalid => True
  | _, _ => False

theorem dist_eqv [OFE α] {n} : Equivalence (Excl.Dist (α := α) n) where
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
instance [OFE α] : OFE (Excl α) where
  dist := Excl.Dist
  dist_eqv
  eq_dist' {x y} := by
    cases x <;> cases y <;> simp [Excl.Dist, eq_dist (SI := SI)]
  dist_lt {n} {x y m} hn hlt := by
    cases x <;> cases y <;> simp at *
    exact Dist.lt hn hlt

@[rocq_alias Excl_ne]
instance [OFE α] : NonExpansive excl (α := α) where
  ne _ _ _ a := a

/-- Note: Not an instance, due to instance coherence problems. -/
theorem ne_match [OFE α] {B : Type _} [OFE B]
    (f : α → B) (hf : NonExpansive f) (g : B) :
    NonExpansive (fun x : Excl α => match x with | .excl a => f a | .invalid => g) :=
  ⟨fun {n} {x' y'} (h : Excl.Dist n x' y') =>
    match x', y', h with
    | .excl _, .excl _, h => hf.ne h
    | .excl _, .invalid, h => h.elim
    | .invalid, .excl _, h => h.elim
    | .invalid, .invalid, _ => Dist.rfl⟩

@[rocq_alias excl_ofe_discrete]
instance [OFE α] [OFE.Discrete α] : OFE.Discrete (Excl α) where
  discrete_0 {x y} h' := by
    cases x <;> cases y
    · exact congrArg excl (discrete_0 (α := α) h')
    · exact h'.elim
    · exact h'.elim
    · rfl

#rocq_ignore excl_leibniz "Not needed"

@[rocq_alias Excl_discrete]
instance [OFE α] {a : α} [h : DiscreteE a] : DiscreteE (excl a) where
  discrete {x} h' := by
    cases x
    · exact congrArg excl (h.discrete h')
    · exact h'.elim

@[rocq_alias ExclInvalid_discrete]
instance [OFE α] : DiscreteE (@invalid α) where
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

def exclChain [OFE α] (c : Chain (Excl α)) (a : α) : Chain α := by
  refine ⟨fun n => (c n).getD a, fun {n} {i} H => ?_⟩
  dsimp; have := c.cauchy H; revert this
  cases c.chain i <;> cases c.chain n <;> simp [Dist, HasDist.dist]

@[rocq_alias excl_cofe]
instance [SIdxFinite] [OFE α] [IsCOFE α] : IsCOFE (Excl α) where
  compl c := (c 0).map fun x => IsCOFE.compl (exclChain c x)
  conv_compl {n} c := by
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

@[reducible] def cmraData [OFE α] : CMRAData (Excl α) where
  ValidN _ := Valid
  Valid
  op_ne.ne _ _ _ _ := trivial
  pcore_ne := by simp [PCore.pcore]
  validN_ne {n} {x y} h₁ h₂ := by cases x <;> cases y <;> trivial
  valid_iff_validN {x} := by
    constructor
    · intro h n; cases x <;> trivial
    · intro h; cases x <;> simp_all
  validN_le {n n'} {x} h _ := by cases x <;> trivial
  validN_op_left := by simp [Op.op]
  extend {n} {x y₁ y₂} h₁ h₂ := by cases x <;> trivial
  pcore_op_mono := by simp [PCore.pcore]

@[rocq_alias exclR]
instance [OFE α] : CMRA (Excl α) := ofCMRAData Excl.cmraData

theorem ord_iff [OFE α] {x y : Excl α} : x ≼ₒ y ↔ y = invalid := by
  constructor
  · rintro ⟨z, hz⟩
    exact hz
  · intro h
    exact ⟨invalid, h⟩

@[rocq_alias excl_included]
theorem inc_iff {x y : Excl α} : x ≼ y ↔ y = invalid :=
  ⟨fun ⟨_, hz⟩ => hz, fun h => ⟨invalid, h⟩⟩

theorem ordN_iff [OFE α] {x y : Excl α} (n) : x ≼ₒ{n} y ↔ y = invalid := by
  constructor
  · intro ⟨z, hz⟩; cases x <;> cases y <;> first | rfl | exact hz.elim
  · rintro rfl; exists invalid

@[rocq_alias excl_includedN]
theorem incN_iff [OFE α] {x y : Excl α} (n) : x ≼{n} y ↔ y = invalid :=
  incN_iff_ordN.trans (ordN_iff n)

@[rocq_alias Excl_inj]
theorem excl_inj {α : Type _} {a b : α} (h : (some (excl a) : Option (Excl α)) = some (excl b)) :
    a = b := Excl.excl.inj (Option.some.inj h)

@[rocq_alias Excl_dist_inj]
theorem excl_dist_inj [OFE α] {a b : α} {n}
    (h : (some (excl a) : Option (Excl α)) ≡{n}≡ some (excl b)) : a ≡{n}≡ b :=
  OFE.some_dist_some.mp h

theorem excl_ord [OFE α] {a b : α} :
    (some (excl a) : Option (Excl α)) ≼ₒ some (excl b) ↔ a = b := by
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

theorem excl_ordN [OFE α] {a b : α} {n} :
    (some (excl a) : Option (Excl α)) ≼ₒ{n} some (excl b) ↔ a ≡{n}≡ b := by
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | ⟨_, hz⟩
  · exact h
  · exact (hz : excl b ≡{n}≡ invalid).elim

@[rocq_alias Excl_includedN]
theorem excl_includedN [OFE α] {a b : α} {n} :
    (some (excl a) : Option (Excl α)) ≼{n} some (excl b) ↔ a ≡{n}≡ b :=
  incN_iff_ordN.trans excl_ordN

@[rocq_alias excl_validN_inv_l]
theorem validN_inv_some_l [OFE α] {n} {mx : Option (Excl α)} {a : α}
    (h : ✓{n} (some (excl a) • mx)) : mx = none := by
  cases mx with
  | none => rfl
  | some _ => exact h.elim

@[rocq_alias excl_validN_inv_r]
theorem validN_inv_some_r [OFE α] {n} {mx : Option (Excl α)} {a : α}
    (h : ✓{n} (mx • some (excl a))) : mx = none := by
  cases mx with
  | none => rfl
  | some _ => exact h.elim

@[rocq_alias excl_exclusive]
instance [OFE α] {x : Excl α} : Exclusive x where exclusive0_l := fun _ a => a

@[rocq_alias excl_cmra_discrete]
instance [OFE α] [OFE.Discrete α] : ORA.Discrete (Excl α) where
  discrete_valid a := a
  discrete_ord := CMRA.ord_of_ord0

theorem invalid_ord [OFE α] (ea : Excl α) : ea ≼ₒ invalid := by exists invalid

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
theorem map_ne [OFE α] [OFE β] (f : α -n> β) : NonExpansive (map f) where
  ne n x₁ x₂ h := by
    cases x₁ <;> cases x₂ <;> try trivial
    have ⟨hne⟩ := f.ne
    exact hne h

#rocq_ignore Excl_proper "Derivable from NonExpansive.eqv"

@[rocq_alias excl_map_cmra_morphism]
def hom [OFE α] [OFE β] (f : α -n> β) : Excl α -C> Excl β := by
  refine CMRA.Hom.toORA ⟨⟨map f, map_ne f⟩, ?_, ?_, ?_⟩
  · intro n x h; cases x <;> trivial
  · intro x; trivial
  · intro x y; trivial

@[indexed, rocq_alias exclO_map]
def oMap [OFE α] [OFE β] (f : α -n> β) : Excl α -n> Excl β := ⟨map f, map_ne f⟩

@[rocq_alias exclO_map_ne]
instance oMap_ne [OFE α] [OFE β] : NonExpansive (oMap (α := α) (β := β)) where
  ne _ _ _ h x := by cases x with
    | excl _ => exact h _
    | invalid => exact .rfl

@[rocq_alias exclRF]
abbrev ExclOF (F : COFE.OFunctorPre) : COFE.OFunctorPre :=
  fun A B _ _ => Excl (F A B)

instance {F} [COFE.OFunctor F] : RFunctor (ExclOF F) where
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

instance instRFunctorAffine {F} [COFE.OFunctor F] : RFunctorAffine (ExclOF F) where
  affine := inferInstance

@[rocq_alias exclRF_contractive]
instance {F} [COFE.OFunctorContractive F] : RFunctorContractive (ExclOF F) where
  map_contractive.1 {n} {x y} HKL z := by
    rewrite [RFunctor.map]
    cases z
    · apply COFE.OFunctorContractive.map_contractive.1
      exact HKL
    · trivial

end Excl

end excl

end Iris
