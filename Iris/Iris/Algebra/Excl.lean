/-
Copyright (c) 2025 Oliver Soeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Soeser, Mario Carneiro
-/
module

public import Iris.Algebra.CMRA
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

section excl

@[rocq_alias excl]
inductive Excl α where
  | excl : α → Excl α
  | invalid : Excl α

namespace Excl
open OFE

/-! ## COFE -/
@[simp, rocq_alias excl_equiv, deprecated "OFE is Leibniz; use `congrArg`/`rw`" (since := "2026-07")] protected def Equiv [OFE α] : Excl α → Excl α → Prop
  | excl a, excl b => a ≡ b
  | invalid, invalid => True
  | _, _ => False

@[simp, rocq_alias excl_dist] protected def Dist [OFE α] (n : Nat) : Excl α → Excl α → Prop
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
  Dist := Excl.Dist
  dist_eqv
  eq_dist {x y} := by
    cases x <;> cases y <;> simp [Excl.Dist, eq_dist]
  dist_lt {n x y m} hn hlt := by
    cases x <;> cases y <;> simp at *
    exact Dist.lt hn hlt

@[rocq_alias Excl_ne]
instance [OFE α] : NonExpansive excl (α := α) where
  ne _ _ _ a := a

/-- Note: Not an instance, due to instance coherence problems. -/
theorem ne_match [OFE α] {B : Type _} [OFE B]
    (f : α → B) (hf : NonExpansive f) (g : B) :
    NonExpansive (fun x : Excl α => match x with | .excl a => f a | .invalid => g) :=
  ⟨fun {n x' y'} (h : Excl.Dist n x' y') =>
    match x', y', h with
    | .excl _, .excl _, h => hf.ne h
    | .excl _, .invalid, h => h.elim
    | .invalid, .excl _, h => h.elim
    | .invalid, .invalid, _ => Dist.rfl⟩

@[rocq_alias excl_ofe_discrete]
instance [OFE α] [Discrete α] : Discrete (Excl α) where
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
  refine ⟨fun n => (c n).getD a, fun {n i} H => ?_⟩
  dsimp; have := c.cauchy H; revert this
  cases c.chain i <;> cases c.chain n <;> simp [Dist]

@[rocq_alias excl_cofe]
instance [OFE α] [IsCOFE α] : IsCOFE (Excl α) where
  compl c := (c 0).map fun x => IsCOFE.compl (exclChain c x)
  conv_compl {n} c := by
    have := c.cauchy (Nat.zero_le n); revert this
    obtain _|x' := c.chain 0 <;> rcases e : c.chain n with _|y' <;> simp [Dist]
    refine fun _ => .trans IsCOFE.conv_compl ?_
    simp [exclChain, e]

/-! ## CMRA -/
@[simp] def Valid : Excl α → Prop
  | excl _ => True
  | invalid => False

#rocq_ignore excl_op_instance "Use CMRA instance"
#rocq_ignore excl_pcore_instance "Use CMRA instance"
#rocq_ignore excl_validN_instance "Use CMRA instance"
#rocq_ignore excl_valid_instance "Use CMRA instance"
#rocq_ignore excl_cmra_mixin "Not needed"

@[rocq_alias exclR]
instance [OFE α] : CMRA (Excl α) where
  pcore _ := none
  op _ _ := invalid
  ValidN _ := Valid
  Valid
  op_ne.ne _ _ _ _ := trivial
  pcore_ne := by simp
  validN_ne {n x y} h₁ h₂ := by cases x <;> cases y <;> trivial
  valid_iff_validN {x} := by
    constructor
    · intro h n; cases x <;> trivial
    · intro h; cases x <;> simp_all
  validN_succ {x n} h := by cases x <;> trivial
  assoc := by simp
  comm := by simp
  pcore_op_left := by simp
  pcore_idem := by simp
  pcore_op_mono := by simp
  validN_op_left := by simp
  extend {n x y₁ y₂} h₁ h₂ := by cases x <;> trivial

@[rocq_alias excl_included]
theorem inc_iff [OFE α] {x y : Excl α} : x ≼ y ↔ y = invalid := by
  constructor
  · rintro ⟨z, hz⟩
    exact hz
  · intro h
    exact ⟨invalid, h⟩

@[rocq_alias excl_includedN]
theorem incN_iff [OFE α] {x y : Excl α} (n) : x ≼{n} y ↔ y = invalid := by
  constructor
  · intro ⟨z, hz⟩; cases x <;> cases y <;> first | rfl | exact hz.elim
  · rintro rfl; exists invalid

@[rocq_alias Excl_inj]
theorem excl_inj [OFE α] {a b : α} (h : (some (excl a) : Option (Excl α)) = some (excl b)) :
    a = b := Excl.excl.inj (Option.some.inj h)

@[rocq_alias Excl_dist_inj]
theorem excl_dist_inj [OFE α] {a b : α} {n}
    (h : (some (excl a) : Option (Excl α)) ≡{n}≡ some (excl b)) : a ≡{n}≡ b :=
  OFE.some_dist_some.mp h

@[rocq_alias Excl_included]
theorem excl_included [OFE α] {a b : α} :
    (some (excl a) : Option (Excl α)) ≼ some (excl b) ↔ a = b := by
  refine ⟨fun ⟨z, hz⟩ => ?_,
    fun h => ⟨none, congrArg (fun x => some (excl x)) h.symm⟩⟩
  rcases z with _|z
  · exact (excl_inj hz).symm
  · exact (hz.dist (n := 0)).elim

@[rocq_alias Excl_includedN]
theorem excl_includedN [OFE α] {a b : α} {n} :
    (some (excl a) : Option (Excl α)) ≼{n} some (excl b) ↔ a ≡{n}≡ b := by
  refine ⟨fun ⟨z, hz⟩ => ?_, fun h => ⟨none, OFE.some_dist_some.mpr (show excl b ≡{n}≡ excl a from h.symm)⟩⟩
  rcases z with _|z
  · exact (OFE.some_dist_some.mp hz : excl b ≡{n}≡ excl a).symm
  · exact (OFE.some_dist_some.mp hz : excl b ≡{n}≡ invalid).elim

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
instance [OFE α] {x : Excl α} : CMRA.Exclusive x where exclusive0_l := fun _ a => a

@[rocq_alias excl_cmra_discrete]
instance [OFE α] [OFE.Discrete α] : CMRA.Discrete (Excl α) where
  discrete_valid a := a

@[rocq_alias ExclInvalid_included]
theorem invalid_inc [OFE α] (ea : Excl α) : ea ≼ invalid := by exists invalid

/-! ## Functors -/
@[rocq_alias excl_map_id]
theorem map_id : map id x = x := by
  cases x <;> simp

@[rocq_alias excl_map_compose]
theorem map_comp (f : α → β) (g : β → γ) :
    map (g ∘ f) x = map g (map f x) := by
  cases x <;> simp

@[rocq_alias excl_map_ext]
theorem map_ext [OFE α] [OFE β] (f g : α → β) (h : ∀ x, f x = g x) : map f x = map g x := by
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
  refine ⟨⟨map f, map_ne f⟩, ?_, ?_, ?_⟩
  · intro n x h; cases x <;> trivial
  · intro x; trivial
  · intro x y; trivial

@[rocq_alias exclO_map]
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

@[rocq_alias exclRF_contractive]
instance {F} [COFE.OFunctorContractive F] : RFunctorContractive (ExclOF F) where
  map_contractive.1 {n x y} HKL z := by
    rewrite [RFunctor.map]
    cases z
    · apply COFE.OFunctorContractive.map_contractive.1
      exact HKL
    · trivial
