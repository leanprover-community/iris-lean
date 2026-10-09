/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko
-/
module

public import Iris.Algebra.OFE
public import Iris.Algebra.StepIndexFinite
meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

variable {SI : Type _} [instSI : SIdx SI]

open OFE COFE

namespace Completion.Raw

variable {α : Type u} [OFE SI α]

@[rocq_alias chain_equiv]
def Equiv (x y : Chain SI α) : Prop :=
  ∀ (n : SI), x n ≡{n}≡ y n

theorem equiv_equivalence : Equivalence (Equiv (SI := SI) (α := α)) where
  refl _ _ := .rfl
  symm h _ := (h _).symm
  trans h₁ h₂ _ := (h₁ _).trans (h₂ _)

def quotientSetoid : Setoid (Chain SI α) := ⟨Equiv, equiv_equivalence⟩

@[rocq_alias chain_dist]
def dist (n : SI) (x y : Chain SI α) : Prop :=
  ∀ (m : SI), m ≤ n → x m ≡{m}≡ y m

theorem dist_equivalence : Equivalence (dist (SI := SI) (α := α) n) where
  refl _ _ _ := .rfl
  symm h _ hm := (h _ hm).symm
  trans h₁ h₂ _ hm := (h₁ _ hm).trans (h₂ _ hm)

theorem dist_lt {n m : SI} {x y : Chain SI α} (h : dist n x y) (hlt : m < n) :
    dist m x y :=
  fun k hk => h k (SIdx.le_trans hk (SIdx.lt_le_incl hlt))

theorem equiv_iff_dist (x y : Chain SI α) : Equiv x y ↔ ∀ n, dist n x y :=
  ⟨fun h _ _ _ => h _, fun h n => h n n SIdx.le_refl⟩

end Completion.Raw

namespace Chain

@[rocq_alias chain_inhabited]
instance instInhabited [OFE SI α] [Inhabited α] : Inhabited (Chain SI α) :=
  ⟨Chain.const default⟩

end Chain

variable (SI) in
def Completion (α : Type u) [OFE SI α] :=
  Quotient (Completion.Raw.quotientSetoid (SI := SI) (α := α))

namespace Completion

variable {α : Type u} [OFE SI α]

def mk (c : Chain SI α) : Completion SI α := OFE.ofQuotient.mk Raw.quotientSetoid c

@[elab_as_elim, induction_eliminator]
theorem ind {motive : Completion SI α → Prop} (mk : ∀ c : Chain SI α, motive (Completion.mk c))
    (x : Completion SI α) : motive x :=
  OFE.ofQuotient.ind mk x

@[elab_as_elim]
theorem ind₂ {motive : Completion SI α → Completion SI α → Prop}
    (mk : ∀ c d : Chain SI α, motive (Completion.mk c) (Completion.mk d))
    (x y : Completion SI α) : motive x y :=
  OFE.ofQuotient.ind₂ mk x y

theorem sound {x y : Chain SI α} (h : Raw.Equiv x y) : mk x = mk y :=
  OFE.ofQuotient.sound h

theorem exact {x y : Chain SI α} (h : mk x = mk y) : Raw.Equiv x y :=
  OFE.ofQuotient.exact h

theorem mk_eq {x y : Chain SI α} : mk x = mk y ↔ Raw.Equiv x y :=
  OFE.ofQuotient.mk_eq

def lift {β : Sort v} (f : Chain SI α → β)
    (resp : ∀ x y, Raw.Equiv x y → f x = f y) : Completion SI α → β :=
  OFE.ofQuotient.lift f resp

@[simp]
theorem lift_mk {β : Sort v} (f : Chain SI α → β) (resp) (c : Chain SI α) :
    lift f resp (mk c) = f c :=
  rfl

#rocq_ignore chain_ofe_mixin "Non needed."

@[rocq_alias chainO]
instance instOFE : OFE SI (Completion SI α) :=
  OFE.ofQuotient (s := Raw.quotientSetoid) Raw.dist Raw.dist_equivalence Raw.dist_lt
    Raw.equiv_iff_dist

@[simp]
theorem dist_mk {n : SI} {x y : Chain SI α} :
    mk x ≡{n}≡ mk y ↔ Raw.dist n x y :=
  Iff.rfl

def unit : α -n>[SI] Completion SI α where
  f a := mk (Chain.const a)
  ne.ne _ _ _ h := dist_mk.mpr fun _ hm => h.le hm

#rocq_ignore chain_const_ne "Implicit in the type of `Completion.unit`."
#rocq_ignore chain_const_proper "OFE equality is Leibniz equality."

instance [Inhabited α] : Inhabited (Completion SI α) := ⟨unit (SI := SI) default⟩

theorem exists_limit (c : Chain SI (Completion SI α)) :
  ∃ x : Completion SI α, ∀ (n : SI), x ≡{n}≡ c n := by
  have hrep (n : SI) : ∃ d : Chain SI α, mk d = c n :=
    ind (fun d => ⟨d, rfl⟩) (c n)
  let d (n : SI) : Chain SI α := Classical.choose (hrep n)
  have hd (n : SI) : mk (d n) = c n := Classical.choose_spec (hrep n)
  let diagonal : Chain SI α := {
    chain := fun n => d n n
    cauchy := by
      intro n i hni
      refine (d i).cauchy hni |>.trans ?_
      refine dist_mk.mp ?_ n SIdx.le_refl
      rw [hd i, hd n]
      exact c.cauchy hni
  }
  refine ⟨mk diagonal, fun n => ?_⟩
  rw [← hd n]
  refine dist_mk.mpr fun m hmn => ?_
  change d m m ≡{m}≡ d n m
  refine (dist_mk.mp ?_ m SIdx.le_refl).symm
  rw [hd n, hd m]
  exact c.cauchy hmn

@[rocq_alias chain_compl]
noncomputable def diagonal (c : Chain SI (Completion SI α)) : Completion SI α :=
  Classical.choose (exists_limit c)

@[rocq_alias chain_cofe]
noncomputable instance instIsCOFE [SIdxFinite SI] : IsCOFE SI (Completion SI α) where
  compl := diagonal
  conv_compl {n : SI} {c} := Classical.choose_spec (exists_limit c) n
  lbcompl := (·.elim)
  conv_lbcompl := (·.elim)
  lbcompl_ne := (·.elim)

def complete [IsCOFE SI α] : Completion SI α -n>[SI] α where
  f := lift COFE.compl fun x y h => OFE.eq_dist_2 fun n =>
    (COFE.conv_compl (c := x)).trans ((h n).trans (COFE.conv_compl (c := y)).symm)
  ne.ne {n : SI} {x y} h := by
    induction x, y using ind₂ with
    | mk c d =>
      exact (COFE.conv_compl (c := c)).trans
        ((dist_mk.mp h n SIdx.le_refl).trans (COFE.conv_compl (c := d)).symm)

@[simp]
theorem complete_mk [IsCOFE SI α] (c : Chain SI α) : complete (SI := SI) (mk c) = COFE.compl c :=
  rfl

#rocq_ignore compl_ne "Implicit in the type of `Completion.complete`."
#rocq_ignore compl_proper "OFE equality is Leibniz equality."

@[rocq_alias chain_iso]
def idemp [IsCOFE SI α] : OFE.Iso SI α (Completion SI α) where
  hom := unit
  inv := complete
  hom_inv := by
    intro x
    induction x using ind with
    | mk c =>
      apply sound
      intro n
      exact COFE.conv_compl (SI := SI)
  inv_hom := by
    intro x
    exact COFE.compl_const x

@[rocq_alias chainO_map]
def map {β : Type v} [OFE SI β] (f : α -n>[SI] β) : Completion SI α -n>[SI] Completion SI β where
  f := OFE.ofQuotient.map (s := Raw.quotientSetoid) (s' := Raw.quotientSetoid)
    (Chain.map f) fun _ _ h n => f.ne.ne (h n)
  ne.ne {n : SI} {x y} h := by
    induction x, y using ind₂ with
    | mk c d =>
      refine dist_mk.mpr fun m hm => ?_
      exact f.ne.ne (dist_mk.mp h m hm)

@[simp]
theorem map_mk {β : Type v} [OFE SI β] (f : α -n>[SI] β) (c : Chain SI α) :
    map f (mk c) = mk (Chain.map f c) :=
  rfl

#rocq_ignore chain_map_ne "Implicit in the type of `Completion.map`."

@[rocq_alias chain_map_id]
theorem map_id (x : Completion SI α) : map OFE.Hom.id x = x := by
  induction x using ind with
  | mk c => simp only [map_mk, Chain.map_id]

@[rocq_alias chain_map_compose]
theorem map_comp {β : Type v} {γ : Type w} [OFE SI β] [OFE SI γ]
    (f : β -n>[SI] γ) (g : α -n>[SI] β) (x : Completion SI α) :
    map (f.comp g) x = map f (map g x) := by
  induction x using ind with
  | mk c => simp only [map_mk, Chain.map_comp]

@[rocq_alias chain_map_ext_ne]
theorem map_ext_ne {β : Type v} [OFE SI β] (f g : α -n>[SI] β) (x : Completion SI α) {n : SI}
    (h : ∀ a, f a ≡{n}≡ g a) : map f x ≡{n}≡ map g x := by
  induction x using ind with
  | mk c =>
    refine (dist_mk (SI := SI)).mpr fun m hm => ?_
    exact (h (c m)).le hm

@[rocq_alias chain_map_ext]
theorem map_ext {β : Type v} [OFE SI β] (f g : α -n>[SI] β) (x : Completion SI α)
    (h : ∀ a, f a = g a) : map f x = map g x := by
  refine OFE.eq_dist_2 fun (n : SI) => ?_
  exact map_ext_ne f g x fun a => (h a).dist

@[rocq_alias chainO_map_ne]
instance map_ne {β : Type v} [OFE SI β] : NonExpansive SI (map (SI := SI) (α := α) (β := β)) where
  ne {_ f g} h x := map_ext_ne f g x fun a => h a

end Completion

abbrev CompletionOF (F : COFE.OFunctorPre SI) [COFE.OFunctor SI F] : COFE.OFunctorPre SI :=
  fun α β _ _ => Completion SI (F α β)

@[rocq_alias chainOF]
instance instOFunctorCompletionOF (F : COFE.OFunctorPre SI) [COFE.OFunctor SI F] :
    COFE.OFunctor SI (CompletionOF F) where
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
instance instOFunctorContractiveCompletionOF (F : COFE.OFunctorPre SI)
    [COFE.OFunctorContractive SI F] : COFE.OFunctorContractive SI (CompletionOF F) where
  map_contractive.1 h :=
    NonExpansive.ne (SI := SI) (f := Completion.map) (COFE.OFunctorContractive.map_contractive.1 h)

end Iris

end
