/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.StepIndexFinite
meta import Iris.Std.RocqPorting

@[expose] public section
local stepindex Nat

namespace Iris

open OFE COFE

namespace Completion.Raw

variable {α : Type u} [OFE α]

@[rocq_alias chain_equiv]
def Equiv (x y : Chain α) : Prop :=
  ∀ n, x n ≡{n}≡ y n

theorem equiv_equivalence : Equivalence (Equiv (α := α)) where
  refl _ _ := .rfl
  symm h _ := (h _).symm
  trans h₁ h₂ _ := (h₁ _).trans (h₂ _)

def quotientSetoid : Setoid (Chain α) := ⟨Equiv, equiv_equivalence⟩

@[rocq_alias chain_dist]
def dist (n : Nat) (x y : Chain α) : Prop :=
  ∀ m, m ≤ n → x m ≡{m}≡ y m

theorem dist_equivalence : Equivalence (dist (α := α) n) where
  refl _ _ _ := .rfl
  symm h _ hm := (h _ hm).symm
  trans h₁ h₂ _ hm := (h₁ _ hm).trans (h₂ _ hm)

theorem dist_lt {n m : Nat} {x y : Chain α} (h : dist n x y) (hlt : m < n) :
    dist m x y :=
  fun k hk => h k (Nat.le_trans hk (Nat.le_of_lt hlt))

theorem equiv_iff_dist (x y : Chain α) : Equiv x y ↔ ∀ n, dist n x y :=
  ⟨fun h _ _ _ => h _, fun h n => h n n (Nat.le_refl n)⟩

end Completion.Raw

namespace Chain

@[rocq_alias chain_inhabited]
instance instInhabited [OFE α] [Inhabited α] : Inhabited (Chain α) :=
  ⟨Chain.const default⟩

end Chain

def Completion (α : Type u) [OFE α] :=
  Quotient (Completion.Raw.quotientSetoid (α := α))

namespace Completion

variable {α : Type u} [OFE α]

def mk (c : Chain α) : Completion α := OFE.ofQuotient.mk Raw.quotientSetoid c

@[elab_as_elim, induction_eliminator]
theorem ind {motive : Completion α → Prop} (mk : ∀ c : Chain α, motive (Completion.mk c))
    (x : Completion α) : motive x :=
  OFE.ofQuotient.ind mk x

@[elab_as_elim]
theorem ind₂ {motive : Completion α → Completion α → Prop}
    (mk : ∀ c d : Chain α, motive (Completion.mk c) (Completion.mk d))
    (x y : Completion α) : motive x y :=
  OFE.ofQuotient.ind₂ mk x y

theorem sound {x y : Chain α} (h : Raw.Equiv x y) : mk x = mk y :=
  OFE.ofQuotient.sound h

theorem exact {x y : Chain α} (h : mk x = mk y) : Raw.Equiv x y :=
  OFE.ofQuotient.exact h

theorem mk_eq {x y : Chain α} : mk x = mk y ↔ Raw.Equiv x y :=
  OFE.ofQuotient.mk_eq

def lift {β : Sort v} (f : Chain α → β)
    (resp : ∀ x y, Raw.Equiv x y → f x = f y) : Completion α → β :=
  OFE.ofQuotient.lift f resp

@[simp]
theorem lift_mk {β : Sort v} (f : Chain α → β) (resp) (c : Chain α) :
    lift f resp (mk c) = f c :=
  rfl

#rocq_ignore chain_ofe_mixin "Non needed."

@[rocq_alias chainO]
instance instOFE : OFE (Completion α) :=
  OFE.ofQuotient (s := Raw.quotientSetoid) Raw.dist Raw.dist_equivalence Raw.dist_lt
    Raw.equiv_iff_dist

@[simp]
theorem dist_mk {n} {x y : Chain α} :
    mk x ≡{n}≡ mk y ↔ Raw.dist n x y :=
  Iff.rfl

def unit : α -n> Completion α where
  f a := mk (Chain.const a)
  ne.ne _ _ _ h := dist_mk.mpr fun _ hm => h.le hm

#rocq_ignore chain_const_ne "Implicit in the type of `Completion.unit`."
#rocq_ignore chain_const_proper "OFE equality is Leibniz equality."

instance [Inhabited α] : Inhabited (Completion α) := ⟨unit default⟩

theorem exists_limit (c : Chain (Completion α)) :
  ∃ x : Completion α, ∀ n, x ≡{n}≡ c n := by
  have hrep (n : Nat) : ∃ d : Chain α, mk d = c n :=
    ind (fun d => ⟨d, rfl⟩) (c n)
  let d (n : Nat) : Chain α := Classical.choose (hrep n)
  have hd (n : Nat) : mk (d n) = c n := Classical.choose_spec (hrep n)
  let diagonal : Chain α := {
    chain := fun n => d n n
    cauchy := by
      intro n i hni
      refine (d i).cauchy hni |>.trans ?_
      refine dist_mk.mp ?_ n (Nat.le_refl n)
      rw [hd i, hd n]
      exact c.cauchy hni
  }
  refine ⟨mk diagonal, fun n => ?_⟩
  rw [← hd n]
  refine dist_mk.mpr fun m hmn => ?_
  change d m m ≡{m}≡ d n m
  refine (dist_mk.mp ?_ m (Nat.le_refl m)).symm
  rw [hd n, hd m]
  exact c.cauchy hmn

@[rocq_alias chain_compl]
noncomputable def diagonal (c : Chain (Completion α)) : Completion α :=
  Classical.choose (exists_limit c)

@[rocq_alias chain_cofe]
noncomputable instance instIsCOFE : IsCOFE (Completion α) where
  compl := diagonal
  conv_compl {n c} := Classical.choose_spec (exists_limit c) n
  lbcompl := (·.elim)
  conv_lbcompl := (·.elim)
  lbcompl_ne := (·.elim)

def complete [IsCOFE α] : Completion α -n> α where
  f := lift COFE.compl fun x y h => OFE.eq_dist.mpr fun n =>
    (COFE.conv_compl (c := x)).trans ((h n).trans (COFE.conv_compl (c := y)).symm)
  ne.ne {n x y} h := by
    induction x, y using ind₂ with
    | mk c d =>
      exact (COFE.conv_compl (c := c)).trans
        ((dist_mk.mp h n (Nat.le_refl n)).trans (COFE.conv_compl (c := d)).symm)

@[simp]
theorem complete_mk [IsCOFE α] (c : Chain α) : complete (mk c) = COFE.compl c :=
  rfl

#rocq_ignore compl_ne "Implicit in the type of `Completion.complete`."
#rocq_ignore compl_proper "OFE equality is Leibniz equality."

@[rocq_alias chain_iso]
def idemp [IsCOFE α] : OFE.Iso α (Completion α) where
  hom := unit
  inv := complete
  hom_inv := by
    intro x
    induction x using ind with
    | mk c =>
      apply sound
      intro n
      exact COFE.conv_compl
  inv_hom := by
    intro x
    exact COFE.compl_const x

@[rocq_alias chainO_map]
def map {β : Type v} [OFE β] (f : α -n> β) : Completion α -n> Completion β where
  f := OFE.ofQuotient.map (s := Raw.quotientSetoid) (s' := Raw.quotientSetoid)
    (Chain.map f) fun _ _ h n => f.ne.ne (h n)
  ne.ne {n x y} h := by
    induction x, y using ind₂ with
    | mk c d =>
      refine dist_mk.mpr fun m hm => ?_
      exact f.ne.ne (dist_mk.mp h m hm)

@[simp]
theorem map_mk {β : Type v} [OFE β] (f : α -n> β) (c : Chain α) :
    map f (mk c) = mk (Chain.map f c) :=
  rfl

#rocq_ignore chain_map_ne "Implicit in the type of `Completion.map`."

@[rocq_alias chain_map_id]
theorem map_id (x : Completion α) : map OFE.Hom.id x = x := by
  induction x using ind with
  | mk c => simp only [map_mk, Chain.map_id]

@[rocq_alias chain_map_compose]
theorem map_comp {β : Type v} {γ : Type w} [OFE β] [OFE γ]
    (f : β -n> γ) (g : α -n> β) (x : Completion α) :
    map (f.comp g) x = map f (map g x) := by
  induction x using ind with
  | mk c => simp only [map_mk, Chain.map_comp]

@[rocq_alias chain_map_ext_ne]
theorem map_ext_ne {β : Type v} [OFE β] (f g : α -n> β) (x : Completion α) {n}
    (h : ∀ a, f a ≡{n}≡ g a) : map f x ≡{n}≡ map g x := by
  induction x using ind with
  | mk c =>
    refine dist_mk.mpr fun m hm => ?_
    exact (h (c m)).le hm

@[rocq_alias chain_map_ext]
theorem map_ext {β : Type v} [OFE β] (f g : α -n> β) (x : Completion α)
    (h : ∀ a, f a = g a) : map f x = map g x := by
  apply OFE.eq_dist.mpr
  intro n
  exact map_ext_ne f g x fun a => (h a).dist

@[rocq_alias chainO_map_ne]
instance map_ne {β : Type v} [OFE β] : NonExpansive (map (α := α) (β := β)) where
  ne {_ f g} h x := map_ext_ne f g x fun a => h a

end Completion

abbrev CompletionOF (F : COFE.OFunctorPre) [COFE.OFunctor F] : COFE.OFunctorPre :=
  fun α β _ _ => Completion (F α β)

@[rocq_alias chainOF]
instance instOFunctorCompletionOF (F : COFE.OFunctorPre) [COFE.OFunctor F] :
    COFE.OFunctor (CompletionOF F) where
  ofe := inferInstance
  map f g := Completion.map (COFE.OFunctor.map f g)
  map_ne.ne _ _ _ hf _ _ hg :=
    NonExpansive.ne (f := Completion.map) (COFE.OFunctor.map_ne.ne hf hg)
  map_id x :=
    (Completion.map_ext _ _ x fun y => COFE.OFunctor.map_id y).trans (Completion.map_id x)
  map_comp f g f' g' x :=
    (Completion.map_ext _ _ x fun y => COFE.OFunctor.map_comp f g f' g' y).trans
      (Completion.map_comp _ _ x)

@[rocq_alias chainOF_contractive]
instance instOFunctorContractiveCompletionOF (F : COFE.OFunctorPre)
    [COFE.OFunctorContractive F] : COFE.OFunctorContractive (CompletionOF F) where
  map_contractive.1 h :=
    NonExpansive.ne (f := Completion.map) (COFE.OFunctorContractive.map_contractive.1 h)

end Iris

end
