/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Graf, Sergei Stepanenko
-/
module

public meta import Iris.Std.RocqPorting

@[expose] public section

namespace Iris

/-- Ordered family of equivalences -/
@[rocq_alias ofe]
class OFE (α : Type _) where
  Dist : Nat → α → α → Prop
  dist_eqv : Equivalence (Dist n)
  eq_dist : x = y ↔ ∀ n, Dist n x y
  dist_lt : Dist n x y → m < n → Dist m x y

def OFE.Equiv [OFE α] (x y : α) : Prop := (∀ n, Dist n x y)

#rocq_ignore OfeMixin "Use the OFE type class"
#rocq_ignore ofe_mixin_of' "Not needed"
#rocq_ignore Dist "Use OFE.Dist"

#rocq_ignore dist_ne "Rewrite using Equiv.trans"
#rocq_ignore dist_proper "Rewrite using Equiv.trans"
#rocq_ignore dist_proper_2 "Rewrite using Equiv.trans"

open OFE

scoped infix:40 " ≡ " => OFE.Equiv
scoped notation:40 x " ≡{" n "}≡ " y:41 => OFE.Dist n x y

namespace OFE

@[rocq_alias dist_equivalence]
theorem dist_equivalence [OFE α] {n} : Equivalence (Dist (α := α) n) := dist_eqv

@[rocq_alias dist_lt]
theorem Dist.lt [OFE α] {m n} {x y : α} : x ≡{n}≡ y → m < n → x ≡{m}≡ y := dist_lt

@[rocq_alias dist_le]
theorem Dist.le [OFE α] {m n} {x y : α} (h : x ≡{n}≡ y) (h' : m ≤ n) : x ≡{m}≡ y :=
  if hm : m = n then hm ▸ h else h.lt (Nat.lt_of_le_of_ne h' hm)
#rocq_ignore dist_le' "Use Dist.le"
#rocq_ignore dist_S "Subsumed by `Dist.lt`/`Dist.le`."

@[simp, refl] theorem Dist.rfl [OFE α] {n} {x : α} : x ≡{n}≡ x := dist_eqv.1 _
@[symm] theorem Dist.symm [OFE α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ x := dist_eqv.2
theorem Dist.trans [OFE α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ z → x ≡{n}≡ z := dist_eqv.3
theorem Dist.of_eq [OFE α] {x y : α} : x = y → x ≡{n}≡ y := (· ▸ .rfl)

theorem equiv_dist [OFE α] {x y : α} : x ≡ y ↔ ∀ n, x ≡{n}≡ y := .rfl

@[rocq_alias ofe_equivalence]
theorem equiv_eqv [ofe : OFE α] : Equivalence ofe.Equiv := by
  constructor
  · rintro x; rw [ofe.equiv_dist]; rintro n; exact Dist.rfl
  · rintro x y; simp only [ofe.equiv_dist]; rintro h n; exact Dist.symm (h n)
  · rintro x y z; simp only [ofe.equiv_dist]; rintro h₁ h₂ n; exact Dist.trans (h₁ n) (h₂ n)

@[simp, refl] theorem Equiv.rfl [OFE α] {x : α} : x ≡ x := equiv_eqv.1 _
@[symm] theorem Equiv.symm [OFE α] {x : α} : x ≡ y → y ≡ x := equiv_eqv.2
theorem Equiv.trans [OFE α] {x : α} : x ≡ y → y ≡ z → x ≡ z := equiv_eqv.3
theorem Equiv.dist [OFE α] {x : α} : x ≡ y → x ≡{n}≡ y := (equiv_dist.1 · _)
theorem Equiv.to_eq [OFE α] {x y : α} (h : x ≡ y) : x = y := OFE.eq_dist.mpr h
theorem Equiv.of_eq [OFE α] {x y : α} : x = y → x ≡ y := (· ▸ .rfl)

instance [OFE α] : Trans OFE.Equiv OFE.Equiv (OFE.Equiv : α → α → Prop) where
  trans := Equiv.trans

instance [OFE α] {n : Nat} : Trans (OFE.Dist n) (OFE.Dist n) (OFE.Dist n : α → α → Prop) where
  trans := Dist.trans

/-- A function `f : α → β` is non-expansive if it preserves `n`-equivalence. -/
class NonExpansive [OFE α] [OFE β] (f : α → β) where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → f x₁ ≡{n}≡ f x₂

instance id_ne [OFE α] : NonExpansive (@id α) := ⟨fun _ _ _ h => h⟩

instance const_ne [OFE α] [OFE β] {x : α} : NonExpansive (Function.const β x) := ⟨fun _ _ _ _ => .rfl⟩

/-- Note: Not an instance, as any function can be decomposed as a composition in multiple ways. -/
theorem NonExpansive.comp [OFE α] [OFE β] [OFE γ] {g : β → γ} {f : α → β}
    (hg : NonExpansive g) (hf : NonExpansive f) : NonExpansive (g ∘ f) :=
  ⟨fun {_ _ _} h => hg.ne (hf.ne h)⟩

/-- A non-expansive function preserves equivalence. -/
@[rocq_alias ne_proper]
theorem NonExpansive.eqv [OFE α] [OFE β] {f : α → β} [NonExpansive f]
    ⦃x₁ x₂⦄ (h : x₁ ≡ x₂) : f x₁ ≡ f x₂ :=
  equiv_dist.2 fun _ => ne (equiv_dist.1 h _)

/-- A function `f : α → β → γ` is non-expansive if it preserves `n`-equivalence in each argument. -/
class NonExpansive₂ [OFE α] [OFE β] [OFE γ] (f : α → β → γ) where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → ∀ ⦃y₁ y₂⦄, y₁ ≡{n}≡ y₂ → f x₁ y₁ ≡{n}≡ f x₂ y₂

@[rocq_alias ne_proper_2]
theorem NonExpansive₂.eqv [OFE α] [OFE β] [OFE γ] {f : α → β → γ} [NonExpansive₂ f]
    ⦃x₁ x₂⦄ (hx : x₁ ≡ x₂) ⦃y₁ y₂⦄ (hy : y₁ ≡ y₂) : f x₁ y₁ ≡ f x₂ y₂ :=
  equiv_dist.2 fun _ => ne hx.dist hy.dist

/-- Note: Not an instance, for symmetry with NonExpansive₂.ne_left, which cannot be an instance. -/
theorem NonExpansive₂.ne_right [OFE α] [OFE β] [OFE γ] (f : α → β → γ) [NonExpansive₂ f]
    (a : α) : NonExpansive (f a) :=
  ⟨fun {_ _ _} h => ne Dist.rfl h⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem NonExpansive₂.ne_left [OFE α] [OFE β] [OFE γ] (f : α → β → γ) [NonExpansive₂ f]
    (b : β) : NonExpansive (f · b) :=
  ⟨fun {_ _ _} h => ne h Dist.rfl⟩

/-- `DistLater n x y` means that `x` and `y` are `m`-equivalent for all `m < n`. -/
@[rocq_alias dist_later]
def DistLater [OFE α] (n : Nat) (x y : α) : Prop := ∀ m, m < n → x ≡{m}≡ y

@[simp, refl] theorem DistLater.rfl [OFE α] {n} {x : α} : DistLater n x x := fun _ _ => .rfl
@[symm] theorem DistLater.symm [OFE α] {n} {x : α} (h : DistLater n x y) : DistLater n y x :=
  fun _ hm => (h _ hm).symm
theorem DistLater.trans [OFE α] {n} {x : α} (h1 : DistLater n x y) (h2 : DistLater n y z) :
    DistLater n x z := fun _ hm => (h1 _ hm).trans (h2 _ hm)

/-- `DistLater n`-equivalence is an equivalence relation. -/
@[rocq_alias dist_later_equivalence]
theorem distLater_eqv [OFE α] {n} : Equivalence (α := α) (DistLater n) where
  refl _ := DistLater.rfl
  symm h := h.symm
  trans h1 := h1.trans

/-- `n`-equivalence implies `DistLater n`-equivalence. -/
@[rocq_alias dist_dist_later]
theorem Dist.distLater [OFE α] {n} {x y : α} (h : x ≡{n}≡ y) : DistLater n x y :=
  fun _ => dist_lt h

/-- `DistLater n`-equivalence implies `m`-equivalence for all `m < n`. -/
@[rocq_alias dist_later_dist_lt]
theorem DistLater.dist_lt [OFE α] {m n} {x y : α} (h : DistLater n x y) (hm : m < n) : x ≡{m}≡ y :=
  h _ hm

/-- `DistLater 0`-equivalence is trivial. -/
@[simp, rocq_alias dist_later_0] theorem distLater_zero [OFE α] {x y : α} : DistLater 0 x y := nofun

/-- `DistLater n`-equivalence is equivalent to `(n + 1)`-equivalence. -/
@[rocq_alias dist_later_S]
theorem distLater_succ [OFE α] {n} {x y : α} : DistLater n.succ x y ↔ x ≡{n}≡ y :=
  ⟨(·.dist_lt (Nat.lt_succ_self _)), fun h1 _ h2 => h1.le (Nat.le_of_lt_succ h2)⟩

theorem distLater_soundness [OFE α] {x y : α} (H : ∀ n, DistLater n x y → x ≡{n}≡ y) : x ≡ y := by
  refine equiv_dist.mpr fun n => ?_
  induction n with
  | zero => exact H 0 distLater_zero
  | succ n IH => exact H (n + 1) (distLater_succ.mpr IH)

/-- A function `f : α → β` is contractive if it sends `DistLater n`-equivalent inputs to
`n`-equivalent outputs. -/
class Contractive [OFE α] [OFE β] (f : α → β) where
  distLater_dist : DistLater n x y → f x ≡{n}≡ f y

@[simp, rocq_alias contractive_0] theorem Contractive.zero [OFE α] [OFE β] (f : α → β)
    [Contractive f] {x y} : f x ≡{0}≡ f y :=
  Contractive.distLater_dist distLater_zero

@[rocq_alias contractive_S]
theorem Contractive.succ [OFE α] [OFE β] (f : α → β) [Contractive f] {n x y}
    (h : x ≡{n}≡ y) : f x ≡{n.succ}≡ f y :=
  Contractive.distLater_dist (distLater_succ.2 h)

/-- A contractive function is non-expansive. -/
@[rocq_alias contractive_ne]
instance ne_of_contractive [OFE α] [OFE β] (f : α → β) [Contractive f] : NonExpansive f where
  ne := fun _ _ _ h => Contractive.distLater_dist (Dist.distLater h)

/-- A contractive function preserves equivalence. -/
@[rocq_alias contractive_proper]
theorem Contractive.eqv [OFE α] [OFE β] (f : α → β) [Contractive f] ⦃x y : α⦄ (h : x ≡ y) :
    f x ≡ f y := NonExpansive.eqv h

/-- Constant functions are contractive. -/
@[rocq_alias const_contractive]
instance [OFE α] [OFE β] {x : β} : Contractive (fun _ : α => x) where
  distLater_dist := fun _ => Dist.rfl

/-- The discrete OFE obtained from an equivalence relation `Equiv` -/
@[reducible, rocq_alias discrete_ofe_mixin]
def ofDiscrete (α : Type _) : OFE α where
  Dist _ := Eq
  dist_eqv := ⟨congrFun rfl, (Eq.symm ·), (· ▸ ·)⟩
  eq_dist := (forall_const _).symm
  dist_lt h _ := h

/-- A discrete element in an OFE -/
@[rocq_alias Discrete]
class DiscreteE {α : Type _} [OFE α] (x : α) : Prop where
  discrete : x ≡{0}≡ y → x ≡ y

/-- A discrete OFE is one where equivalence is implied by `0`-equivalence. -/
@[rocq_alias OfeDiscrete]
class Discrete (α : Type _) [OFE α] where
  discrete_0 {x y : α} : x ≡{0}≡ y → x ≡ y
export OFE.Discrete (discrete_0)

@[rocq_alias Discrete_proper]
theorem discreteE_eqv [OFE α] {x y : α} (h : x ≡ y): DiscreteE x ↔ DiscreteE y :=
  ⟨fun ⟨dx⟩ => ⟨fun e => h.symm.trans (dx (h.dist.trans e))⟩,
   fun ⟨dy⟩ => ⟨fun e => h.trans (dy (h.symm.dist.trans e))⟩⟩

#rocq_ignore ofe_discrete_subrelation "Not needed"
#rocq_ignore discrete_ofe_discrete "Not needed"

/-- For discrete OFEs, `n`-equivalence implies equivalence for any `n`. -/
@[rocq_alias discrete]
theorem Discrete.discrete [OFE α] [Discrete α] {n} {x y : α} (h : x ≡{n}≡ y) : x ≡ y :=
  discrete_0 (h.le (Nat.zero_le _))
export OFE.Discrete (discrete)

instance Discrete.toDiscreteE [OFE α] [Discrete α] (x : α) : DiscreteE x := ⟨discrete_0⟩

/-- For discrete OFEs, `n`-equivalence implies equivalence for any `n`. -/
theorem Discrete.discrete_n [OFE α] [Discrete α] {n} {x y : α} (h : x ≡{0}≡ y) : x ≡{n}≡ y :=
  (discrete h).dist
export OFE.Discrete (discrete_n)

@[rocq_alias discrete_iff]
theorem Discrete.discrete_iff [OFE α] [Discrete α] (n) {x y : α} : x ≡ y ↔ x ≡{n}≡ y :=
  ⟨Equiv.dist, discrete⟩

@[rocq_alias discrete_iff_0]
theorem Discrete.discrete_iff_0 [OFE α] [Discrete α] (n) {x y : α} : x ≡{0}≡ y ↔ x ≡{n}≡ y :=
  ⟨discrete_n, fun h => h.le (Nat.zero_le _)⟩

#rocq_ignore boolO "Canonical Leibniz OFE on `bool`; Lean uses `ofDiscrete Bool`."
#rocq_ignore natO "Canonical Leibniz OFE on `nat`; Lean uses `ofDiscrete Nat`."
#rocq_ignore positiveO "Canonical Leibniz OFE on `positive`; not applicable in Lean."
#rocq_ignore NO "Canonical Leibniz OFE on `N`; not applicable in Lean."
#rocq_ignore ZO "Canonical Leibniz OFE on `Z`; not applicable in Lean."
#rocq_ignore PropO "Canonical discrete OFE on `Prop`; Lean uses `ofDiscrete Prop`."

#rocq_ignore ofe_leibniz_subrelation "Generalized-rewriting subrelation; not needed in Lean."

/-- The setoid on `X` identifying points that agree at every step index:
`x ≈ y ↔ ∀ n, dist n x y`. -/
@[reducible]
def QuotientO {X : Type u} (dist : Nat → X → X → Prop) (heqv : ∀ {n}, Equivalence (dist n)) :
    Setoid X where
  r x y := ∀ n, dist n x y
  iseqv :=
    ⟨fun _ _ => heqv.refl _,
     fun h n => heqv.symm (h n),
     fun h₁ h₂ n => heqv.trans (h₁ n) (h₂ n)⟩

/--
EXPERIMENT: Explicit use of quotients to force quotiented (by Equiv) OFE to be Leibniz by
quotienting by propositional equality.
https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/Evaluating.20a.20specialization.20to.20Leibnize.20OFE.27s/with/606745235

Build a `Leibniz` OFE from a step-indexed distance `dist` satisfying the OFE distance axioms
by quotienting the carrier `X` by the OFE equivalence `fun x y => ∀ n, dist n x y`. -/
@[reducible] def mkQuotient {X : Type u} (dist : Nat → X → X → Prop)
    (heqv : ∀ {n}, Equivalence (dist n))
    (hlt : ∀ {n m : Nat} {x y : X}, dist n x y → m < n → dist m x y) :
    OFE (Quotient (QuotientO dist heqv)) :=
  letI D : Nat → Quotient (QuotientO dist heqv) → Quotient (QuotientO dist heqv) → Prop :=
    fun n => Quotient.lift₂ (dist n) fun _ _ _ _ hac hbd => propext
      ⟨fun h => heqv.trans (heqv.trans (heqv.symm (hac n)) h) (hbd n),
       fun h => heqv.trans (heqv.trans (hac n) h) (heqv.symm (hbd n))⟩
  { Dist := D
    dist_eqv := by
      refine ⟨Quotient.ind fun a => heqv.refl a, fun {x y} h => ?_, fun {x y z} h₁ h₂ => ?_⟩
      · induction x, y using Quotient.ind₂ with | _ a b => exact heqv.symm h
      · induction x, y using Quotient.ind₂ with | _ a b =>
          induction z using Quotient.ind with | _ c => exact heqv.trans h₁ h₂
    eq_dist {x y} := by
      induction x, y using Quotient.ind₂ with | _ a b =>
        exact ⟨fun h n => Quotient.exact h n, fun h => Quotient.sound fun n => h n⟩
    dist_lt := fun {n x y m} h hlt' => by
      induction x, y using Quotient.ind₂ with | _ a b => exact hlt h hlt' }

namespace mkQuotient

variable {X : Type u} {dist : Nat → X → X → Prop} {heqv : ∀ {n}, Equivalence (dist n)}

@[reducible] def mk (x : X) : Quotient (QuotientO dist heqv) := Quotient.mk _ x

@[elab_as_elim] theorem ind {motive : Quotient (QuotientO dist heqv) → Prop}
    (h : ∀ x : X, motive (mk x)) (q : Quotient (QuotientO dist heqv)) : motive q :=
  Quotient.ind h q

theorem sound {x y : X} (h : ∀ n, dist n x y) :
    (mk x : Quotient (QuotientO dist heqv)) = mk y := Quotient.sound h

theorem mk_eq {x y : X} :
    (mk x : Quotient (QuotientO dist heqv)) = mk y ↔ ∀ n, dist n x y :=
  ⟨Quotient.exact, sound⟩

@[reducible] def lift {β : Sort v} (f : X → β)
    (resp : ∀ x y, (∀ n, dist n x y) → f x = f y) :
    Quotient (QuotientO dist heqv) → β := Quotient.lift f resp

@[simp] theorem lift_mk {β : Sort v} (f : X → β) (resp) (x : X) :
    lift (dist := dist) (heqv := heqv) f resp (mk x) = f x := rfl

@[reducible] def lift₂ {β : Sort v} (f : X → X → β)
    (resp : ∀ a b c d, (∀ n, dist n a c) → (∀ n, dist n b d) → f a b = f c d) :
    Quotient (QuotientO dist heqv) → Quotient (QuotientO dist heqv) → β := Quotient.lift₂ f resp

@[simp] theorem lift₂_mk {β : Sort v} (f : X → X → β) (resp) (x y : X) :
    lift₂ (dist := dist) (heqv := heqv) f resp (mk x) (mk y) = f x y := rfl

@[reducible] def map {X' : Type u'} {dist' : Nat → X' → X' → Prop} {heqv' : ∀ {n}, Equivalence (dist' n)}
    (f : X → X') (hf : ∀ n x y, dist n x y → dist' n (f x) (f y)) :
    Quotient (QuotientO dist heqv) → Quotient (QuotientO dist' heqv') :=
  Quotient.lift (fun x => mk (f x)) (fun _ _ h => Quotient.sound fun n => hf n _ _ (h n))

@[simp] theorem map_mk {X' : Type u'} {dist' : Nat → X' → X' → Prop}
    {heqv' : ∀ {n}, Equivalence (dist' n)} (f : X → X') (hf) (x : X) :
    map (dist := dist) (heqv := heqv) (dist' := dist') (heqv' := heqv') f hf (mk x) = mk (f x) := rfl

theorem dist_mk {hlt : ∀ {n m : Nat} {x y : X}, dist n x y → m < n → dist m x y}
    {n} {x y : X} : (mkQuotient dist heqv hlt).Dist n (mk x) (mk y) ↔ dist n x y := Iff.rfl

end mkQuotient

/-- A morphism between OFEs, written `α -n> β`, is defined to be a function that is
non-expansive. -/
@[ext, rocq_alias ofe_mor] structure Hom (α β : Type _) [OFE α] [OFE β] where
  f : α → β
  ne : NonExpansive f
#rocq_ignore ofe_mor_proper "Derived from nonexpansivity"
#rocq_ignore ofe_mor_ext "Use ext"

@[inherit_doc]
infixr:25 " -n> " => Hom

instance [OFE α] [OFE β] : CoeFun (α -n> β) (fun _ => α → β) := ⟨Hom.f⟩
instance [OFE α] [OFE β] (f : α -n> β) : NonExpansive f := f.ne

/-- The identity morphism on an OFE. -/
@[rocq_alias cid]
protected def Hom.id [OFE α] : α -n> α where
  f := id
  ne.ne _ _ _ := id

/-- The composition of two morphisms between OFEs. -/
@[rocq_alias ccompose]
protected def Hom.comp [OFE α] [OFE β] [OFE γ] (g : β -n> γ) (f : α -n> β) : α -n> γ where
  f := g.f ∘ f.f
  ne.1 _ _ _ h := g.ne.1 (f.ne.1 h)
#rocq_ignore ccompose_ne "Implicit in type of ccompose"
#rocq_ignore ccompose_proper "Derived from nonexpansivity"

@[simp] theorem Hom.id_apply [OFE α] {x} : (Hom.id : α -n> α) x = x := rfl
@[simp] theorem Hom.comp_apply [OFE α] [OFE β] [OFE γ] {g : β -n> γ} {f : α -n> β} {x} :
    (g.comp f) x = g (f x) := rfl

@[simp] theorem Hom.id_comp [OFE α] [OFE β] {f : α -n> β} : Hom.id.comp f = f := rfl
@[simp] theorem Hom.comp_id [OFE α] [OFE β] {f : α -n> β} : f.comp Hom.id = f := rfl

theorem Hom.comp_assoc [OFE α] [OFE β] [OFE γ] [OFE δ]
    (h : γ -n> δ) (g : β -n> γ) (f : α -n> β) : (h.comp g).comp f = h.comp (g.comp f) := rfl

/-- Construct a `Hom` from a subtype bundling a function with its nonexpansiveness proof. -/
def Hom.ofSubtype [OFE α] [OFE β] (f : { f : α → β // NonExpansive f }) : α -n> β :=
  ⟨f.val, f.property⟩

@[ext] structure ContractiveHom (α β : Type _) [OFE α] [OFE β] extends Hom α β where
  [contractive : Contractive f]
  ne := ne_of_contractive f

infixr:25 " -c> " => ContractiveHom

instance [OFE α] [OFE β] : CoeFun (α -c> β) (fun _ => α → β) := ⟨fun x => x.toHom.f⟩
instance [OFE α] [OFE β] (f : α -c> β) : Contractive f := f.contractive

def _root_.Function.toContractiveHom (f : α → β) [OFE α] [OFE β] [ι : OFE.Contractive f] : α -c> β where
  f := f
  contractive := ι

@[simp] theorem _root_.Function.toContractiveHom_apply {f : α → β} [OFE α] [OFE β] [ι : OFE.Contractive f] {x} :
  f.toContractiveHom x = f x := by rfl

theorem InvImage.equivalence {α : Sort u} {β : Sort v}
    {r : β → β → Prop} {f : α → β} (H : Equivalence r) : Equivalence (InvImage r f) where
  refl _ := H.refl _
  symm := H.symm
  trans := H.trans

@[rocq_alias unit_ofe_mixin]
instance : OFE Unit where
  Dist _ _ _ := True
  dist_eqv := ⟨fun _ => ⟨⟩, id, fun _ => id⟩
  eq_dist := by simp
  dist_lt _ _ := ⟨⟩
#rocq_ignore unitO "Use the unit type"
#rocq_ignore unit_dist "Local Dist instance; folded into Lean's OFE Unit instance."

instance : DiscreteE (() : Unit) := ⟨fun _ _ => trivial⟩

instance [OFE α] : OFE (ULift α) where
  Dist n x y := x.down ≡{n}≡ y.down
  dist_eqv := InvImage.equivalence dist_eqv
  eq_dist {x y} := by cases x; cases y; rw [ULift.up.injEq]; exact eq_dist
  dist_lt := dist_lt

def uliftUpHom [OFE α] : α -n> ULift α where
  f := .up
  ne.1 _ _ _ := id

def uliftDownHom [OFE α] : ULift α -n> α where
  f := ULift.down
  ne.1 _ _ _ := id

def _root_.Option.Forall₂ (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem _root_.Option.Forall₂.equivalence {R : α → α → Prop}
    (H : Equivalence R) : Equivalence (Option.Forall₂ R) where
  refl | none => trivial | some _ => H.1 _
  symm {x y} := by cases x <;> cases y <;> simp [Option.Forall₂]; apply H.2
  trans {x y z} := by cases x <;> cases y <;> cases z <;> simp [Option.Forall₂]; apply H.3

@[rocq_alias option_ofe_mixin]
instance [OFE α] : OFE (Option α) where
  Dist n := Option.Forall₂ (Dist n)
  dist_eqv := Option.Forall₂.equivalence dist_eqv
  eq_dist {x y} := by cases x <;> cases y <;> simp [Option.Forall₂, eq_dist]
  dist_lt {_ x y _} := by cases x <;> cases y <;> simp [Option.Forall₂]; apply dist_lt
#rocq_ignore optionO "Use Option"
#rocq_ignore option_dist "Local Dist instance; folded into Lean's OFE (Option α) instance."
#rocq_ignore option_dist_Forall2 "Local Dist unfolding lemma; trivial in Lean."

@[rocq_alias option_ofe_discrete]
instance [OFE α] [OFE.Discrete α] : OFE.Discrete (Option α) where
  discrete_0 {mx my} e :=
    match mx, my with
    | none,   none   => .rfl
    | none,   some _ => e.elim
    | some _, none   => e.elim
    | some x, some y => show x ≡ y from discrete_0 e

@[simp] theorem some_eqv_some [OFE α] {x y : α} : (some x ≡ some y) ↔ x ≡ y := .rfl
@[simp] theorem not_some_eqv_none [OFE α] {x : α} : ¬some x ≡ none := (· 0)
@[simp] theorem not_none_eqv_some [OFE α] {x : α} : ¬none ≡ some x := (· 0)

@[simp, rocq_alias dist_Some]
theorem some_dist_some [OFE α] {n} {x y : α} : (some x ≡{n}≡ some y) ↔ x ≡{n}≡ y := .rfl
@[simp] theorem not_some_dist_none [OFE α] {n} {x : α} : ¬some x ≡{n}≡ none := id
@[simp] theorem not_none_dist_some [OFE α] {n} {x : α} : ¬none ≡{n}≡ some x := id

theorem equiv_some [OFE α] {o : Option α} {y : α} (e : o ≡ some y) :
    ∃ z, o = some z ∧ z ≡ y := by
  cases o with
  | none => exact (e 0).elim
  | some x => exact ⟨x, rfl, e⟩

theorem equiv_none [OFE α] {o : Option α} : o ≡ none ↔ o = none :=
  ⟨fun h => by cases o with | none => rfl | some _ => exact (h 0).elim, (· ▸ .rfl)⟩

@[rocq_alias dist_None]
theorem dist_none [OFE α] {o : Option α} : o ≡{n}≡ none ↔ o = none :=
  ⟨fun h => by cases o with | none => rfl | some _ => exact h.elim, (· ▸ .rfl)⟩

@[rocq_alias dist_Some_inv_r']
theorem dist_some [OFE α] {n mx y} (h : mx ≡{n}≡ some y) :
    ∃ z : α, mx = some z ∧ y ≡{n}≡ z :=
  suffices hh : ∀ mx my y, mx ≡{n}≡ my → my = some y → ∃ t, mx = some t ∧ t ≡{n}≡ y from
    (hh mx (some y) _ h rfl).elim (fun t h => ⟨t, h.left, h.right.symm⟩)
  fun mx _ y e1 e2 =>
    match mx with
    | some t => ⟨t, rfl, (e2 ▸ e1 : some t ≡{n}≡ some y)⟩
    | none => False.elim (e2 ▸ e1 : none ≡{n}≡ some y)

instance [OFE α] [Discrete α] : Discrete (Option α) where
  discrete_0 {x y} H :=
    match x, y with
    | none, none => .rfl
    | some _, some _ => some_eqv_some.mpr (discrete_0 H)
    | none, some _ => H.elim
    | some _, none => H.elim

@[rocq_alias Some_ne]
instance OFE.Option.some.ne [OFE α] : OFE.NonExpansive (some : α → Option α) := ⟨fun _ _ _ => id⟩

@[rocq_alias Some_discrete]
instance Option.some_is_discrete [OFE α] {e : α} [OFE.DiscreteE e] : OFE.DiscreteE (some e) where
  discrete {y} h :=
    match y with
    | .none => absurd h not_some_dist_none
    | .some y => show e ≡ y from DiscreteE.discrete h

/-- Note: Not an instance, due to instance coherence problems. -/
theorem Option.ne_match [OFE α] {B : Type _} [OFE B]
    (f : α → B) (hf : NonExpansive f) (g : B) :
    NonExpansive (fun x : Option α => match x with | some a => f a | none => g) :=
  ⟨fun {n x' y'} (h : Option.Forall₂ (Dist n) x' y') =>
    match x', y', h with | some _, some _, h => hf.ne h | none, none, _ => Dist.rfl⟩

@[rocq_alias None_discrete]
instance Option.none_is_discrete [OFE α] : DiscreteE (none : Option α) := by
  constructor; rintro (_|_) <;> simp

instance Option.merge_ne [OFE α] {op : α → α → α} [NonExpansive₂ op] :
    NonExpansive₂ (Option.merge op) where
  ne n x1 x2 Hx y1 y2 Hy := by
    rcases x1, x2, y1, y2 with ⟨_|_, _|_, _|_, _|_⟩ <;> simp_all
    exact NonExpansive₂.ne Hx Hy

instance Option.bind_fun_ne [OFE α] [OFE β] (f : α → Option β) [NonExpansive f] : NonExpansive (flip Option.bind f) where
  ne _ _ x2 Hx := match x2 with
    | some _ => (dist_some Hx).choose_spec.left ▸ (NonExpansive.ne (f := f) (dist_some Hx).choose_spec.right.symm)
    | none => (dist_none.mp Hx).symm ▸ .rfl

theorem Option.bind_dist [OFE α] [OFE β] {x : Option α} {f g : α → Option β} (H : ∀ x, f x ≡{n}≡ g x) : Option.bind x f ≡{n}≡ Option.bind x g :=
  match x with
  | some _ => H _
  | none => .rfl

theorem Option.bind_equiv [OFE α] [OFE β] {x : Option α} {f g : α → Option β} (H : ∀ x, f x ≡ g x) : Option.bind x f ≡ Option.bind x g :=
  match x with
  | some _ => H _
  | none => .rfl

abbrev OFEFun {α : Type _} (β : α → Type _) := ∀ a, OFE (β a)

@[rocq_alias discrete_fun_ofe_mixin]
instance [OFEFun (β : α → _)] : OFE ((x : α) → β x) where
  Dist n f g := ∀ x, f x ≡{n}≡ g x
  dist_eqv := {
    refl _ _ := dist_eqv.refl _
    symm h _ := dist_eqv.symm (h _)
    trans h1 h2 _ := dist_eqv.trans (h1 _) (h2 _)
  }
  eq_dist {_ _} := by rw [funext_iff]; simpa only [eq_dist] using forall_comm
  dist_lt h1 h2 _ := dist_lt (h1 _) h2
#rocq_ignore discrete_funO "Use a function type"
#rocq_ignore discrete_fun "Lean uses `(x : α) → β x` directly with `OFEFun`."
#rocq_ignore discrete_fun_equiv "Local Equiv instance; folded into Lean's instance."
#rocq_ignore discrete_fun_dist "Local Dist instance; folded into Lean's instance."

@[rocq_alias ofe_mor_ofe_mixin]
instance [OFE α] [OFE β] : OFE (α -n> β) where
  Dist n f g := f.f ≡{n}≡ g.f
  dist_eqv := {
    refl _ := dist_eqv.refl _
    symm h := dist_eqv.symm h
    trans h1 h2 := dist_eqv.trans h1 h2
  }
  eq_dist {_ _} := Hom.ext_iff.trans eq_dist
  dist_lt := dist_lt
#rocq_ignore ofe_morO "Use Hom type"
#rocq_ignore ofe_mor_equiv "Inlined in OFE (α -n> β) instance"
#rocq_ignore ofe_mor_dist "Inlined in OFE (α -n> β) instance"
#rocq_ignore ofe_mor_chain "Inlined in IsCOFE instance"

@[rocq_alias ofe_mor_car_ne]
instance ofe_mor_car_ne [OFE α] [OFE β] :
    NonExpansive₂ (fun (f : α -n> β) (x : α) => f x) where
  ne _ _ _ hf _ _ hx := dist_eqv.trans (hf _) (NonExpansive.ne hx)

@[rocq_alias ofe_mor_car_proper]
theorem ofe_mor_car_proper [OFE α] [OFE β] ⦃f g : α -n> β⦄ (hfg : f ≡ g)
    ⦃x y : α⦄ (hxy : x ≡ y) : f x ≡ g y :=
  NonExpansive₂.eqv (f := fun (f : α -n> β) (x : α) => f x) hfg hxy

@[rocq_alias ofe_mor_inhabited]
instance [OFE α] [OFE β] [Inhabited β] : Inhabited (α -n> β) where
  default := { f := Function.const α default, ne := const_ne }

instance [OFE α] [OFE β] : OFE (α -c> β) where
  Dist n f g := Dist n f.toHom g.toHom
  dist_eqv := {
    refl _ := dist_eqv.refl _
    symm h := dist_eqv.symm h
    trans h1 h2 := dist_eqv.trans h1 h2
  }
  eq_dist {_ _} := ContractiveHom.ext_iff.trans eq_dist
  dist_lt := dist_lt

def applyHom [OFEFun (β : α → _)] (x : α) : ((x : α) → β x) -n> β x where
  f f := f x
  ne.1 _ _ _ H := H x

def applyNe [OFE α] [OFE β] (x : α) : (α -n> β) -n> β where
  f f := f x
  ne.1 _ _ _ H := H x

instance [OFE α] [OFE β] : NonExpansive (applyNe (α := α) (β := β)) where
  ne _ _ _ H f := f.ne.1 H

@[rocq_alias discrete_funO_map]
def mapCodHom [OFEFun (β₁ : α → _)] [OFEFun β₂]
    (F : ∀ x, β₁ x -n> β₂ x) : ((x : α) → β₁ x) -n> ((x : α) → β₂ x) where
  f f x := F x (f x)
  ne.1 _ _ _ H x := (F x).ne.1 (H x)
#rocq_ignore discrete_fun_map "Underlying map of mapCodHom"
#rocq_ignore discrete_fun_map_ext "Use ext"
#rocq_ignore discrete_fun_map_ne "Implicit in type of mapCodHom"
#rocq_ignore discrete_fun_map_ne "Implicit in type of mapCodHom"
#rocq_ignore discrete_funO_map_ne "Implicit in type of mapCodHom"

@[rocq_alias prod_ofe_mixin]
instance [OFE α] [OFE β] : OFE (α × β) where
  Dist n a b := a.1 ≡{n}≡ b.1 ∧ a.2 ≡{n}≡ b.2
  dist_eqv := {
    refl _ := ⟨dist_eqv.refl _, dist_eqv.refl _⟩
    symm h := ⟨dist_eqv.symm h.1, dist_eqv.symm h.2⟩
    trans h1 h2 := ⟨dist_eqv.trans h1.1 h2.1, dist_eqv.trans h1.2 h2.2⟩
  }
  eq_dist {_ _} := by rw [Prod.ext_iff]; simp only [eq_dist, forall_and]
  dist_lt h1 h2 := ⟨dist_lt h1.1 h2, dist_lt h1.2 h2⟩
#rocq_ignore prodO "Use product type"
#rocq_ignore prod_dist "Implicit in Prod OFE"

theorem equiv_fst [OFE α] [OFE β] {x y : α × β} (h : x ≡ y) : x.fst ≡ y.fst := fun n => (h n).left
theorem equiv_snd [OFE α] [OFE β] {x y : α × β} (h : x ≡ y) : x.snd ≡ y.snd := fun n => (h n).right
theorem equiv_prod_ext [OFE α] [OFE β] {x₁ x₂ : α} {y₁ y₂ : β}
    (ex : x₁ ≡ x₂) (ey : y₁ ≡ y₂) : (x₁, y₁) ≡ (x₂, y₂) := fun n => ⟨ex n, ey n⟩

theorem dist_fst {n} [OFE α] [OFE β] {x y : α × β} (h : x ≡{n}≡ y) : x.fst ≡{n}≡ y.fst := h.left
theorem dist_snd {n} [OFE α] [OFE β] {x y : α × β} (h : x ≡{n}≡ y) : x.snd ≡{n}≡ y.snd := h.right

@[rocq_alias pair_dist]
theorem dist_prod_ext {n} [OFE α] [OFE β] {x₁ x₂ : α} {y₁ y₂ : β}
    (ex : x₁ ≡{n}≡ x₂) (ey : y₁ ≡{n}≡ y₂) : (x₁, y₁) ≡{n}≡ (x₂, y₂) := ⟨ex, ey⟩

@[rocq_alias pair_ne]
instance Prod.mk_ne [OFE α] [OFE β] : NonExpansive₂ (Prod.mk (α := α) (β := β)) where
  ne _ _ _ hx _ _ hy := dist_prod_ext hx hy

/-- Note: Not an instance, due to instance coherence problems. -/
theorem prod_mk_ne_left [OFE α] [OFE β] (b : β) : NonExpansive (β := α × β) (·, b) :=
  ⟨fun {_ _ _} h => dist_prod_ext h Dist.rfl⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem prod_mk_ne_right [OFE α] [OFE β] (a : α) : NonExpansive (β := α × β) (a, ·) :=
  ⟨fun {_ _ _} h => dist_prod_ext Dist.rfl h⟩

@[rocq_alias fst_ne]
instance [OFE α] [OFE β] : NonExpansive (Prod.fst (α := α) (β := β)) :=
  ⟨fun {_ _ _} h => dist_fst h⟩

@[rocq_alias snd_ne]
instance [OFE α] [OFE β] : NonExpansive (Prod.snd (α := α) (β := β)) :=
  ⟨fun {_ _ _} h => dist_snd h⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem NonExpansive₂.uncurry [OFE α] [OFE β] [OFE γ] {f : α → β → γ} (hf : NonExpansive₂ f) :
    NonExpansive (Function.uncurry f) :=
  ⟨fun {_ _ _} (h : _ ∧ _) => hf.ne h.1 h.2⟩

@[rocq_alias prod_discrete]
instance prod.is_discrete [OFE α] [OFE β] {a : α} {b : β} [DiscreteE a] [DiscreteE b] :
    DiscreteE (a, b) := by
  constructor
  intro y H; exact fun n => ⟨DiscreteE.discrete H.1 n, DiscreteE.discrete H.2 n⟩

@[rocq_alias prod_ofe_discrete]
instance instDiscreteProd [OFE α] [OFE β] [Discrete α] [Discrete β] : Discrete (α × β) where
  discrete_0 H := fun n => ⟨discrete_0 H.1 n, discrete_0 H.2 n⟩

section sum

variable [OFE α] [OFE β]

@[rocq_alias sum_ofe_mixin]
instance : OFE (α ⊕ β) where
  Dist n
    | .inl a, .inl b => a ≡{n}≡ b
    | .inr a, .inr b => a ≡{n}≡ b
    | _, _ => False
  dist_eqv := {
    refl
    | .inl _ => dist_eqv.refl _
    | .inr _ => dist_eqv.refl _
    symm {a b} h := match a, b with
    | .inl _, .inl _ => h.symm
    | .inr _, .inr _ => h.symm
    | .inr _, .inl _ => h
    | .inl _, .inr _ => h
    trans {a b c} h1 h2 := match a, b, c with
    | .inl _, .inl _, .inl _ => h1.trans h2
    | .inr _, .inr _, .inr _ => h1.trans h2
    | .inr _, .inl _, _ => h1.elim
    | .inl _, .inr _, _ => h1.elim
    | _, .inr _, .inl _ => h2.elim
  }
  eq_dist {a b} := by
    match a, b with
    | .inl _, .inl _ => rw [Sum.inl.injEq]; exact eq_dist
    | .inr _, .inr _ => rw [Sum.inr.injEq]; exact eq_dist
    | .inl _, .inr _ => exact ⟨fun h => (nomatch h), fun x => (x 0).elim⟩
    | .inr _, .inl _ => exact ⟨fun h => (nomatch h), fun x => (x 0).elim⟩
  dist_lt {_ a b} := match a, b with
    | .inl _, .inl _ => dist_lt
    | .inr _, .inr _ => dist_lt
    | .inl _, .inr _ => (False.elim ·)
    | .inr _, .inl _ => (False.elim ·)
#rocq_ignore sumO "Use sum type"
#rocq_ignore sum_dist "Inlined in OFE (α ⊕ β) instance"


theorem equiv_inl {x y : α} (h : x ≡ y) : (.inl x : α ⊕ β) ≡ .inl y := h
theorem equiv_inr {x y : β} (h : x ≡ y) : (.inr x : α ⊕ β) ≡ .inr y := h
theorem equiv_ext_left {x y : α} (h : (.inl x : α ⊕ β) ≡ .inl y) : x ≡ y := h
theorem equiv_ext_right {x y : β} (h : (.inr x : α ⊕ β) ≡ .inr y) : x ≡ y := h

theorem dist_inl (h : x ≡{n}≡ y) : (.inl x : α ⊕ β) ≡{n}≡ .inl y := h
theorem dist_inr {x y : β} (h : x ≡{n}≡ y) : (.inr x : α ⊕ β) ≡{n}≡ .inr y := h
theorem dist_ext_left {x y : α} (h : (.inl x : α ⊕ β) ≡{n}≡ .inl y) : x ≡{n}≡ y := h
theorem dist_ext_right {x y : β} (h : (.inr x : α ⊕ β) ≡{n}≡ .inr y) : x ≡{n}≡ y := h

@[rocq_alias inl_ne]
instance instNonExpansiveInl: NonExpansive (Sum.inl (α := α) (β := β)) where
  ne {_ _ _} H := dist_inl H

@[rocq_alias inr_ne]
instance instNonExpansiveInr : NonExpansive (Sum.inr (α := α) (β := β)) where
  ne {_ _ _} H := dist_inr H

instance instNonExpansiveElim [OFE γ] {f₁ : α → γ} {f₂ : β → γ} [NonExpansive f₁] [NonExpansive f₂] :
    NonExpansive (Sum.elim f₁ f₂) where
  ne {_ x y} := match x, y with
    | .inl _, .inl _ => (NonExpansive.ne (f := f₁) <| dist_ext_left ·)
    | .inr _, .inr _ => (NonExpansive.ne (f := f₂) <| dist_ext_right ·)
    | .inl _, .inr _ => (False.elim ·)
    | .inr _, .inl _ => (False.elim ·)

@[rocq_alias inl_discrete]
theorem discreteE_inl {a : α} (Ha : DiscreteE a) : DiscreteE (.inl a : α ⊕ β) := by
  constructor
  rintro (_|_) H
  · exact Ha.discrete H
  · exact H.elim

@[rocq_alias inr_discrete]
theorem discreteE_inr {a : β} (Ha : DiscreteE a) : DiscreteE (.inr a : α ⊕ β) := by
  constructor
  rintro (_|_) H
  · exact H.elim
  · exact Ha.discrete H

@[rocq_alias sum_ofe_discrete]
instance instDiscreteSum [Discrete α] [Discrete β] : Discrete (α ⊕ β) where
  discrete_0 {x y} := match x, y with
    | .inl _, .inl _ => (equiv_inl <| discrete_0 (α := α) <| dist_ext_left ·)
    | .inr _, .inr _ => (equiv_inr <| discrete_0 (α := β) <| dist_ext_right ·)
    | .inl _, .inr _ => (False.elim ·)
    | .inr _, .inl _ => (False.elim ·)

end sum

@[rocq_alias sig_ofe_mixin]
instance [OFE α] (P : α → Prop) : OFE (Subtype P) where
  Dist n x y := x.val ≡{n}≡ y.val
  dist_eqv := ⟨fun _ => .rfl, Dist.symm, Dist.trans⟩
  eq_dist {_ _} := Subtype.ext_iff.trans eq_dist
  dist_lt := dist_lt
#rocq_ignore sigO "Use subtype"
#rocq_ignore sig_equiv "Local Equiv instance; folded into Lean's OFE (Subtype P) instance."
#rocq_ignore sig_dist "Local Dist instance; folded into Lean's OFE (Subtype P) instance."
#rocq_ignore sig_equiv_def "Trivial unfolding lemma; definitional in Lean."
#rocq_ignore sig_dist_def "Trivial unfolding lemma; definitional in Lean."

@[rocq_alias sig_discrete]
instance [OFE α] [Discrete α] (P : α → Prop) : Discrete (Subtype P) where
  discrete_0 h := @Discrete.discrete_0 α _ _ _ _ h

@[rocq_alias proj1_sig_ne]
instance [OFE α] (P : α → Prop) : NonExpansive (Subtype.val : Subtype P → α) where
  ne {_ _ _} := id

instance Hom.ofSubtype_ne [OFE α] [OFE β] : NonExpansive (Hom.ofSubtype (α := α) (β := β)) :=
  ⟨fun {_ _ _} h => h⟩

/-- Extract the underlying subtype from a `Hom`. -/
def Hom.toSubtype [OFE α] [OFE β] (f : α -n> β) : { f : α → β // NonExpansive f } :=
  ⟨f.f, f.ne⟩

instance Hom.toSubtype_ne [OFE α] [OFE β] : NonExpansive (Hom.toSubtype (α := α) (β := β)) :=
  ⟨fun {_ _ _} h => h⟩

@[rocq_alias sigT_ofe_mixin]
instance instOFESigma (P : α → Type _) [∀ x, OFE (P x)] : OFE (Sigma P) where
  Dist n x y := ∃ heq : x.fst = y.fst, heq ▸ x.snd ≡{n}≡ y.snd
  dist_eqv := {
    refl _ := ⟨rfl, .rfl⟩
    symm {x y} := match x, y with
      | ⟨x, xH⟩, ⟨y, yH⟩ => fun
        | ⟨heq, H⟩ => ⟨heq.symm, by simp only at heq; subst heq; exact H.symm⟩
    trans {x y z} := match x, y, z with
      | ⟨x, xH⟩, ⟨y, yH⟩, ⟨z, zH⟩ => fun
        | ⟨heq, H⟩, ⟨heq', H'⟩ =>
          ⟨heq.trans heq', by simp only at heq heq'; subst heq; subst heq'; exact H.trans H'⟩
  }
  eq_dist {x y} := by
    refine ⟨fun h n => h ▸ ⟨rfl, .rfl⟩, fun h => ?_⟩
    obtain ⟨heq, _⟩ := h 0
    obtain ⟨xf, xs⟩ := x; obtain ⟨yf, ys⟩ := y
    simp only at heq; subst heq
    exact congrArg _ (eq_dist.mpr fun n => (h n).2)
  dist_lt {_ x y} := match x, y with
    | ⟨x, xH⟩, ⟨y, yH⟩ => fun
      | ⟨heq, H⟩ => fun hlt => ⟨heq, by simp only at heq; subst heq; exact dist_lt H hlt⟩
#rocq_ignore sigTO "Use sigma type"
#rocq_ignore sigT_dist "Local Dist instance; folded into Lean's OFE (Sigma P) instance."
#rocq_ignore sigT_equiv "Local Equiv instance; folded into Lean's OFE (Sigma P) instance."

@[rocq_alias sigT_discrete]
instance instDiscreteESigma {P : α → Type _} [∀ x, OFE (P x)] {x : Sigma P} [inst : DiscreteE x.snd] :
    DiscreteE x where
  discrete {y} := by
    rcases x, y with ⟨⟨x, xH⟩, ⟨y, yH⟩⟩; rintro ⟨heq, H⟩ n
    simp only at heq; subst heq
    exact ⟨rfl, (inst.discrete H).dist⟩

@[rocq_alias sigT_ofe_discrete]
instance instDiscreteSigma {P : α → Type _} [∀ x, OFE (P x)] [∀ x, Discrete (P x)] :
    Discrete (Sigma P) where
  discrete_0 {x y} H := match x, y, H with
    | ⟨x, xH⟩, ⟨y, yH⟩, ⟨heq, H⟩ => fun _ => ⟨heq, by simp only at heq; subst heq; exact (discrete_0 H).dist⟩

@[rocq_alias sigT_equiv_eq_alt]
theorem Sigma.equiv_eq_alt {P : α → Type _} [∀ x, OFE (P x)] {x1 x2 : Sigma P} :
    x1 ≡ x2 ↔ ∃ heq : x1.fst = x2.fst, heq ▸ x1.snd ≡ x2.snd := by
  refine ⟨fun h => ?_, fun ⟨heq, h⟩ n => ⟨heq, equiv_dist.1 h n⟩⟩
  obtain ⟨heq, _⟩ := h 0
  exact ⟨heq, equiv_dist.2 fun n => (proof_irrel _ heq) ▸ (h n).2⟩

@[rocq_alias projT1_ne]
instance Sigma.fst_ne {P : α → Type _} [OFE α] [∀ x, OFE (P x)] :
    NonExpansive (Sigma.fst : Sigma P → α) where
  ne {_ _ _} h := Dist.of_eq h.1
#rocq_ignore projT1_proper "Derived from nonexpansivity."

@[rocq_alias projT2_ne]
theorem Sigma.dist_snd {P : α → Type _} [∀ x, OFE (P x)] {n} {x y : Sigma P}
    (h : x ≡{n}≡ y) : h.1 ▸ x.snd ≡{n}≡ y.snd := h.2

@[rocq_alias projT2_proper]
theorem Sigma.equiv_snd {P : α → Type _} [∀ x, OFE (P x)] {x y : Sigma P}
    (h : x ≡ y) : (h 0).1 ▸ x.snd ≡ y.snd :=
  equiv_dist.2 fun n => (proof_irrel (h n).1 (h 0).1) ▸ (h n).2

@[rocq_alias existT_ne]
theorem Sigma.mk_dist {P : α → Type _} [∀ x, OFE (P x)] {n} {i1 i2 : α} {v1 : P i1} {v2 : P i2}
    (heq : i1 = i2) (h : heq ▸ v1 ≡{n}≡ v2) : Sigma.mk i1 v1 ≡{n}≡ Sigma.mk i2 v2 :=
  ⟨heq, h⟩

@[rocq_alias existT_proper]
theorem Sigma.mk_equiv {P : α → Type _} [∀ x, OFE (P x)] {i1 i2 : α} {v1 : P i1} {v2 : P i2}
    (heq : i1 = i2) (h : heq ▸ v1 ≡ v2) : Sigma.mk i1 v1 ≡ Sigma.mk i2 v2 :=
  fun n => ⟨heq, equiv_dist.1 h n⟩

@[rocq_alias existT_ne_2]
instance Sigma.mk_ne {P : α → Type _} [∀ x, OFE (P x)] (a : α) :
    NonExpansive (Sigma.mk a : P a → Sigma P) where
  ne {_ _ _} h := ⟨rfl, h⟩

/-- An isomorphism between two OFEs is a pair of morphisms whose composition is equivalent to the
identity morphism. -/
@[ext, rocq_alias ofe_iso] structure Iso (α β : Type _) [OFE α] [OFE β] where
  hom : α -n> β
  inv : β -n> α
  hom_inv : hom (inv x) ≡ x
  inv_hom : inv (hom x) ≡ x
#rocq_ignore ofe_isoO "Use Iso"
#rocq_ignore ofe_iso_1_ne "Implicit from the type of `Iso.Hom`"
#rocq_ignore ofe_iso_2_ne "Implicit from the type of `Iso.Inv`"

attribute [simp] Iso.hom_inv Iso.inv_hom

instance [OFE α] [OFE β] : CoeFun (Iso α β) (fun _ => α -n> β) := ⟨Iso.hom⟩
instance [OFE α] [OFE β] (iso : Iso α β) : NonExpansive iso.hom := iso.hom.ne
instance [OFE α] [OFE β] (iso : Iso α β) : NonExpansive iso.inv := iso.inv.ne

@[simp] theorem Iso.hom_inv_dist [OFE α] [OFE β] (iso : Iso α β) {n} {x} :
    iso.hom (iso.inv x) ≡{n}≡ x :=
  OFE.equiv_dist.mp (Iso.hom_inv iso) _

@[simp] theorem Iso.inv_hom_dist [OFE α] [OFE β] (iso : Iso α β) {n} {x} :
    iso.inv (iso.hom x) ≡{n}≡ x :=
  OFE.equiv_dist.mp (Iso.inv_hom iso) _

/-- OFE isomorphisms preserve equivalence. -/
theorem Iso.hom_eqv [OFE α] [OFE β] (iso : Iso α β) ⦃x y⦄ :
    x ≡ y ↔ iso.hom x ≡ iso.hom y :=
  ⟨fun h => NonExpansive.eqv h,
  fun h => Equiv.trans (Equiv.symm iso.inv_hom) <| Equiv.trans (NonExpansive.eqv h) (iso.inv_hom)⟩

/-- The inverse of an OFE isomorphism preserves equivalence. -/
theorem Iso.inv_eqv [OFE α] [OFE β] (iso : Iso α β) ⦃x y⦄ :
    x ≡ y ↔ iso.inv x ≡ iso.inv y :=
  ⟨fun h => NonExpansive.eqv h,
  fun h => Equiv.trans (Equiv.symm iso.hom_inv) <| Equiv.trans (NonExpansive.eqv h) (iso.hom_inv)⟩

/-- OFE isomorphisms preserve `n`-equivalence. -/
theorem Iso.hom_dist [OFE α] [OFE β] (iso : Iso α β) {n} ⦃x y⦄ :
    x ≡{n}≡ y ↔ iso.hom x ≡{n}≡ iso.hom y :=
  ⟨fun h => NonExpansive.ne h, fun h => Dist.trans (Dist.symm iso.inv_hom_dist) <|
    Dist.trans (NonExpansive.ne h) (iso.inv_hom_dist)⟩

/-- The inverse of an OFE isomorphism preserves `n`-equivalence. -/
theorem Iso.inv_dist [OFE α] [OFE β] (iso : Iso α β) {n} ⦃x y⦄ :
    x ≡{n}≡ y ↔ iso.inv x ≡{n}≡ iso.inv y :=
  ⟨fun h => NonExpansive.ne h, fun h => Dist.trans (Dist.symm iso.hom_inv_dist) <|
    Dist.trans (NonExpansive.ne h) (iso.hom_inv_dist)⟩

/-- The identity OFE isomorphism -/
@[rocq_alias iso_ofe_refl]
def Iso.id [OFE α] : Iso α α where
  hom := Hom.id
  inv := Hom.id
  hom_inv := by intro x; simp
  inv_hom := by intro x; simp

@[simp] theorem Iso.id_apply [OFE α] {x} : ((Iso.id : Iso α α) : α -n> α) x = x := rfl

/-- The inverse of an OFE isomorphism -/
@[rocq_alias iso_ofe_sym]
def Iso.symm [OFE α] [OFE β] (iso : Iso α β) : Iso β α where
  hom := iso.inv
  inv := iso.hom
  hom_inv := by intro x; simp
  inv_hom := by intro x; simp
#rocq_ignore iso_ofe_sym_ne "Implicit in the type of Iso.symm.hom"
#rocq_ignore iso_ofe_trans_ne "Implicit in the type of Iso.symm.inv"

/-- Composition of OFE isomorphisms -/
@[rocq_alias iso_ofe_trans]
def Iso.comp [OFE α] [OFE β] [OFE γ] (iso1 : Iso β γ) (iso2 : Iso α β) : Iso α γ where
  hom := iso1.hom.comp iso2.hom
  inv := iso2.inv.comp iso1.inv
  hom_inv := by
    intro x; simp
    exact .trans (NonExpansive.eqv <| .trans iso2.hom_inv .rfl) iso1.hom_inv
  inv_hom := by
    intro x; simp
    exact .trans (NonExpansive.eqv <| .trans iso1.inv_hom .rfl) iso2.inv_hom

end OFE

/-- A chain in an OFE is a `Nat`-indexed sequence of elements that is upward-closed in terms of
`n`-equivalence. -/
@[rocq_alias chain] structure Chain (α : Type _) [OFE α] where
  chain : Nat → α
  cauchy : n ≤ i → chain i ≡{n}≡ chain n

instance [OFE α] : CoeFun (Chain α) (fun _ => Nat → α) := ⟨Chain.chain⟩

namespace Chain

/-- The constant chain. -/
@[rocq_alias chain_const]
def const [OFE α] (a : α) : Chain α where
  chain := fun _ => a
  cauchy _ := OFE.Dist.rfl

@[simp] theorem const_apply [OFE α] {a : α} {n} : const a n = a := rfl

/-- Mapping a chain through a non-expansive function. -/
@[rocq_alias chain_map]
def map [OFE α] [OFE β] (f : α -n> β) (c : Chain α) : Chain β where
  chain n := f (c n)
  cauchy h := f.ne.1 (c.cauchy h)

@[simp] theorem map_apply [OFE α] [OFE β] {f : α -n> β} {c : Chain α} {n} :
    map f c n = f (c n) := rfl

@[simp] theorem map_id [OFE α] {c : Chain α} : map (Hom.id : α -n> α) c = c := by
  simp [map]

theorem map_comp [OFE α] [OFE β] [OFE γ] {f : α -n> β} {g : β -n> γ} {c : Chain α} :
    map (g.comp f) c = map g (map f c) := by
  simp [map]

end Chain

/-- If a chain of Option is ever none, is the constant none chain. -/
theorem chain_none_const [OFE V] {c : Chain (Option V)} (H : c n = none) :
    c = Chain.const none := by
  rcases c with ⟨c, Hc⟩
  congr 1; refine funext (fun k => ?_)
  rcases Nat.le_or_ge n k with (Hnk|Hnk)
  · suffices c k ≡{n}≡ c n by cases _ : c k <;> simp_all
    exact Hc Hnk
  · suffices c k ≡{k}≡ c n by cases _ : c k <;> simp_all
    exact (Hc Hnk).symm

/-- If a chain of Option is ever some, it is the lift a chain by some. -/
theorem chain_option_some [OFE V] {c : Chain (Option V)} (H : c n = some v) :
    ∃ c' : Chain V, c = Chain.map ⟨some, OFE.Option.some.ne⟩ c' := by
  have HVc (k) : ∃ v', c k = some v' := by
    rcases h : c.chain k with (_|v')
    · simp [chain_none_const h] at H
    · exists v'
  let c' : Chain V :=
    ⟨fun n => Classical.choose <| HVc n,
     by
       intro n i Hni
       have HR := c.cauchy Hni
       rw [Classical.choose_spec (HVc n), Classical.choose_spec (HVc i)] at HR
       exact HR ⟩
  exists c'
  rcases hcc : c with ⟨cc, Hcc⟩
  simp only [Chain.map, Chain.mk.injEq]
  refine funext (fun i => ?_)
  simp only [c']
  have Hchoose := Classical.choose_spec (HVc i)
  rw [← Hchoose]
  simp [hcc]

/-- Complete ordered family of equivalences -/
@[rocq_alias Cofe]
class IsCOFE (α : Type _) [OFE α] where
  compl : Chain α → α
  conv_compl {c : Chain α} : compl c ≡{n}≡ c n

/-- Complete ordered family of equivalences -/
class abbrev COFE (α : Type _) := OFE α, IsCOFE α

namespace COFE
export IsCOFE (compl conv_compl)

@[rocq_alias conv_compl_le]
theorem conv_compl' [COFE α] {c : Chain α} {n i} (h : n ≤ i) : compl c ≡{n}≡ c i :=
  conv_compl.trans (c.cauchy h).symm

/-- Chain maps commute with completion. -/
@[rocq_alias compl_chain_map]
theorem compl_map [COFE α] [COFE β] (f : α -n> β) (c : Chain α) :
    compl (Chain.map f c) ≡ f (compl c) := by
  refine OFE.equiv_dist.mpr (fun n => ?_)
  exact Dist.trans conv_compl (NonExpansive.ne (Dist.symm conv_compl))

/-- Constant chains complete to their constant value -/
@[simp, rocq_alias compl_chain_const]
theorem compl_const [COFE α] (a : α) : compl (Chain.const a) ≡ a :=
  OFE.equiv_dist.mpr (fun _ => conv_compl)

/-- Completion of discrete COFEs is the constant value. -/
@[simp] theorem discrete_cofe_compl [COFE α] [OFE.Discrete α] (c : Chain α) : compl c ≡ c 0 :=
  Discrete.discrete_0 conv_compl

/-- The discrete COFE obtained from an equivalence relation `Equiv` -/
@[reducible, rocq_alias discrete_cofe]
def ofDiscrete (α : Type _) : COFE α :=
  let _ := OFE.ofDiscrete α
  { compl := fun c => c 0
    conv_compl := fun {n c} => (c.cauchy (Nat.zero_le n)).symm }

instance [COFE α] : COFE (ULift α) where
  compl c := ⟨compl (c.map uliftDownHom)⟩
  conv_compl := conv_compl

@[rocq_alias unit_ofe_discrete]
instance : Discrete Unit where
  discrete_0 _ := .rfl

@[rocq_alias unit_cofe]
instance : COFE Unit where
  compl _ := ()
  conv_compl := ⟨⟩

abbrev IsCOFEFun {α : Type _} (β : α → Type _) [OFEFun β] := ∀ x : α, IsCOFE (β x)

instance instIsCOFEOption [OFE α] [IsCOFE α] : IsCOFE (Option α) where
  compl c := match c 0 with
    | .some seed => .some <| compl <| c.map ⟨_, Option.ne_match id inferInstance seed⟩
    | .none => none
  conv_compl {n c} := by
    cases h1 : c.chain 0 with
    | none =>
      refine Equiv.dist <| Option.none_is_discrete.discrete ?_
      exact h1 ▸ c.cauchy (Nat.zero_le n) |>.symm
    | some seed =>
      refine (some_dist_some.mpr conv_compl).trans ?_
      dsimp only [Chain.map_apply]
      cases h2 : c.chain n with
      | none => exact (h1 ▸ h2 ▸ c.cauchy (by omega : 0 ≤ n)).elim
      | some _ => rfl
#rocq_ignore option_compl "Local Compl definition; folded into Lean's IsCOFE instance."

@[rocq_alias discrete_fun_cofe]
instance {α : Type _} (β : α → Type _) [∀ x, COFE (β x)] : COFE ((x : α) → β x) where
  compl c x := compl (c.map (applyHom x))
  conv_compl _ := IsCOFE.conv_compl
#rocq_ignore discrete_fun_chain "Local helper; folded into Lean's IsCOFE instance."

@[rocq_alias ofe_mor_cofe]
instance instIsCOFEHom [OFE α] [OFE β] [IsCOFE β] : IsCOFE (α -n> β) where
  compl c := by
    refine ⟨(compl <| c.map <| applyNe ·), ⟨fun n _ _ H => ?_⟩⟩
    refine conv_compl.trans (.trans ?_ conv_compl.symm)
    exact NonExpansive.ne (f := c.chain n) H
  conv_compl _ := IsCOFE.conv_compl
#rocq_ignore ofe_mor_compl "Inlined in IsCOFE instance"

@[rocq_alias prod_cofe]
instance instIsCOFEProd [OFE α] [OFE β] [IsCOFE α] [IsCOFE β] : IsCOFE (α × β) where
  compl c := ⟨compl (c.map ⟨Prod.fst, inferInstance⟩), compl (c.map ⟨Prod.snd, inferInstance⟩)⟩
  conv_compl := ⟨conv_compl, conv_compl⟩

@[rocq_alias sum_cofe]
instance instIsCOFESum  [OFE α] [OFE β] [IsCOFE α] [IsCOFE β] : IsCOFE (α ⊕ β) where
  compl c := match c 0 with
    | .inl seed => .inl (compl (c.map ⟨Sum.elim id (Function.const _ seed), inferInstance⟩))
    | .inr seed => .inr (compl (c.map ⟨Sum.elim (Function.const _ seed) id, inferInstance⟩))
  conv_compl {n c} := by
    cases h1 : c.chain 0 with
    | inl seed =>
      refine (dist_inl conv_compl).trans ?_
      dsimp only [Chain.map_apply]
      cases h2 : c.chain n with
      | inl _ => simp
      | inr _ => exact (h1 ▸ h2 ▸ c.cauchy (by omega : 0 ≤ n)).elim
    | inr seed =>
      refine (dist_inr conv_compl).trans ?_
      dsimp only [Chain.map_apply]
      cases h2 : c.chain n with
      | inl _ => exact (h1 ▸ h2 ▸ c.cauchy (by omega : 0 ≤ n)).elim
      | inr _ => simp
#rocq_ignore inl_chain "Local helper for `sum_compl`; folded into Lean's IsCOFE instance."
#rocq_ignore inr_chain "Local helper for `sum_compl`; folded into Lean's IsCOFE instance."
#rocq_ignore sum_compl "Local Compl definition; folded into Lean's IsCOFE instance."

@[rocq_alias sigT_chain_const_proj1]
theorem Sigma.chain_const_proj1 {P : α → Type _} [∀ x, OFE (P x)] [∀ x, IsCOFE (P x)]
  (c : Chain (Sigma P)) n : (c n).fst = (c 0).fst := (c.cauchy (by omega : 0 ≤ n)).choose

@[rocq_alias chain_map_snd]
def Sigma.chain_map_snd {P : α → Type _} [∀ x, OFE (P x)] [∀ x, IsCOFE (P x)] (c : Chain (Sigma P)) :
    Chain (P (c 0).fst) where
  chain n := Sigma.chain_const_proj1 c n ▸ (c n).snd
  cauchy {n i} hle := by
    obtain ⟨heq, hequiv⟩ := c.cauchy hle
    clear hle
    rw [show Sigma.chain_const_proj1 c i = heq.trans (Sigma.chain_const_proj1 c n) by rfl]
    generalize Sigma.chain_const_proj1 c n = heq'
    revert heq' hequiv heq; cases c.chain i; cases c.chain n
    rintro ⟨⟩ hequiv ⟨⟩
    exact hequiv

@[rocq_alias sigT_cofe]
instance {P : α → Type _} [∀ x, OFE (P x)] [∀ x, IsCOFE (P x)] : IsCOFE (Sigma P) where
  compl c := ⟨(c 0).fst, compl (Sigma.chain_map_snd c)⟩
  conv_compl {n c} := by
    refine ⟨(Sigma.chain_const_proj1 c n).symm, ?_⟩
    have hequiv := conv_compl (c := Sigma.chain_map_snd c) (n := n)
    revert hequiv
    dsimp only [Sigma.chain_map_snd]
    generalize Sigma.chain_const_proj1 c n = heq
    revert heq; cases c.chain n
    rintro ⟨⟩ hequiv
    exact hequiv
#rocq_ignore sigT_compl "Local Compl definition; folded into Lean's IsCOFE instance."

set_option linter.checkUnivs false in
abbrev OFunctorPre := ∀ α β [COFE α] [COFE β], Type _
#rocq_ignore oFunctor_apply "Definition for application of an `oFunctor`; subsumed by `OFunctorPre` in Lean."

@[rocq_alias oFunctor]
class OFunctor (F : OFunctorPre) where
  ofe [COFE α] [COFE β] : OFE (F α β)
  map [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -n> F α₂ β₂
  map_ne [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    NonExpansive₂ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFE α] [COFE β] (x : F α β) : map (@Hom.id α _) (@Hom.id β _) x ≡ x
  map_comp [COFE α₁] [COFE α₂] [COFE α₃] [COFE β₁] [COFE β₂] [COFE β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x ≡ map g g' (map f f' x)

@[rocq_alias oFunctorContractive]
class OFunctorContractive (F : OFunctorPre) extends OFunctor F where
  map_contractive [COFE α₁] [COFE α₂] [COFE β₁] [COFE β₂] :
    Contractive (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [reducible, instance] OFunctor.ofe

end COFE

/- Discrete OFE structure on a type -/
@[ext] structure DiscreteO (α : Type _) where
  car : α

instance : COFE (DiscreteO α) := COFE.ofDiscrete _

instance {α : Type _} : OFE.Discrete (DiscreteO α) := ⟨fun h _ => h⟩

#rocq_ignore leibnizO_leibniz "Not needed"

theorem DiscreteO.eqv_inj {x y : α} (H : DiscreteO.mk x ≡ DiscreteO.mk y) : x = y :=
  show (DiscreteO.mk x).car = (DiscreteO.mk y).car from congrArg DiscreteO.car (H 0)

theorem DiscreteO.dist_inj {x y : α} {n} (H : DiscreteO.mk x ≡{n}≡ DiscreteO.mk y) : x = y :=
  DiscreteO.eqv_inj <| discrete H

section DiscreteFunOF
open COFE

abbrev DiscreteFunOF {C : Type _} (F : C → OFunctorPre) : OFunctorPre :=
  fun A B _ _ => (c : C) → F c A B

@[rocq_alias discrete_funOF]
instance oFunctor_discreteFunOF {C} (F : C → OFunctorPre) [∀ c, OFunctor (F c)] :
    OFunctor (DiscreteFunOF F) where
  ofe := _
  map f₁ f₂ := mapCodHom fun _ => OFunctor.map f₁ f₂
  map_ne.ne _ _ _ Hx _ _ Hy _ _ := OFunctor.map_ne.ne Hx Hy ..
  map_id x := fun n c => OFunctor.map_id (x c) n
  map_comp f g f' g' x := fun n c => OFunctor.map_comp f g f' g' (x c) n

end DiscreteFunOF

section Option
variable [OFE α]

@[rocq_alias option_chain]
def optionChain (c : Chain (Option α)) (x : α) : Chain α := by
  refine ⟨fun n => (c n).getD x, fun {n i} H => ?_⟩
  have := c.cauchy H; revert this
  cases c.chain i <;> cases c.chain n <;> simp [Dist, Option.Forall₂]

@[rocq_alias option_cofe]
instance isCOFE_option [IsCOFE α] : IsCOFE (Option α) where
  compl c := (c 0).map fun x => IsCOFE.compl (optionChain c x)
  conv_compl {n} c := by
    have := c.cauchy (Nat.zero_le n); revert this
    rcases c.chain 0 with _|x' <;> rcases e : c.chain n with _|y' <;> simp [Dist, Option.Forall₂]
    refine fun _ => OFE.dist_eqv.trans IsCOFE.conv_compl ?_
    simp [optionChain, e]

@[rocq_alias optionO_map]
def optionMap {α β : Type _} [OFE α] [OFE β] (f : α -n> β) : Option α -n> Option β := by
  refine ⟨Option.map f, ⟨?_⟩⟩
  rintro _ ⟨⟩ ⟨⟩ H <;> simp_all [Dist, Option.Forall₂]
  exact f.ne.ne H

@[rocq_alias option_fmap_ne]
theorem Option.map_ne [OFE β] {f g : α → β} {x y : Option α} {n} :
    (∀ x y, x ≡{n}≡ y → f x ≡{n}≡ g y) → x ≡{n}≡ y → Option.map f x ≡{n}≡ Option.map g y := by
  intro hf hxy
  cases x <;> cases y <;> simp_all [Dist, Option.Forall₂]

theorem Option.map_forall₂ {α β : Type _} [OFE α] [OFE β] (f : α → β) [hf : OFE.NonExpansive f]
    {o1 o2 : Option α} (h : o1 ≡ o2) : o1.map f ≡ o2.map f := by
  cases o1 <;> cases o2 <;> simp_all []
  exact hf.eqv h

@[rocq_alias optionO_map_ne]
instance optionMap_ne [OFE β] : NonExpansive (optionMap (α := α) (β := β)) where
  ne _ f _ h o :=
    Option.map_ne (fun _ _ hab => dist_eqv.trans (f.ne.ne hab) (h _)) (dist_eqv.refl o)

@[rocq_alias option_mbind_ne]
theorem Option.bind_ne [OFE β] {f g : α → Option β} {x y : Option α} {n}
    (hf : ∀ x y, x ≡{n}≡ y → f x ≡{n}≡ g y) (hxy : x ≡{n}≡ y) : x.bind f ≡{n}≡ y.bind g := by
  cases x <;> cases y <;> simp_all [Dist, Option.Forall₂]

@[rocq_alias option_mjoin_ne]
theorem Option.join_ne {x y : Option (Option α)} {n} (hxy : x ≡{n}≡ y) : x.join ≡{n}≡ y.join := by
  cases x <;> cases y <;> simp_all [Dist, Option.Forall₂]

@[rocq_alias from_option_ne]
theorem Option.elim_ne {β : Type _} (R : β → β → Prop) {f g : α → β} {d d' : β}
    {x y : Option α} {n} (hf : ∀ x y, x ≡{n}≡ y → R (f x) (g y)) (hd : R d d')
    (hxy : x ≡{n}≡ y) : R (x.elim d f) (y.elim d' g) := by
  cases x <;> cases y <;> simp_all [Dist, Option.Forall₂]

end Option

section OptionOF
open COFE

abbrev OptionOF (F : OFunctorPre) : OFunctorPre :=
  fun A B _ _ => Option (F A B)

variable (F : OFunctorPre)

@[rocq_alias optionOF]
instance oFunctorOption [OFunctor F] : OFunctor (OptionOF F) where
  ofe := _
  map f g := optionMap (OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy z := by
    cases z <;> simp [optionMap, Dist, Option.Forall₂]
    exact OFunctor.map_ne.ne Hx Hy ..
  map_id z := by
    cases z with
    | none => exact .rfl
    | some c => exact some_eqv_some.mpr (OFunctor.map_id c)
  map_comp f g f' g' z := by
    cases z with
    | none => exact .rfl
    | some c => exact some_eqv_some.mpr (OFunctor.map_comp f g f' g' c)

@[rocq_alias optionOF_contractive]
instance [OFunctorContractive F] : OFunctorContractive (OptionOF F) where
  map_contractive.1 H z := by
    have := (OFunctorContractive.map_contractive (F := F)).distLater_dist H
    cases z <;> simp_all [optionMap, Dist, Option.Forall₂, Function.uncurry, OFunctor.map]

end OptionOF

section ProdOF

open COFE

variable [OFE A] [OFE A'] [OFE B] [OFE B']

@[rocq_alias prod_map_ne]
instance instNonExpansiveProdMap (f : A → A') (g : B → B') [NonExpansive f] [NonExpansive g] :
    NonExpansive (Prod.map f g) where
  ne _ _ _ H := by
    constructor
    · rw [Prod.map_fst]
      exact NonExpansive.ne H.1
    · rw [Prod.map_snd]
      exact NonExpansive.ne H.2

omit [OFE A] [OFE B] in
theorem Prod.map_ext {f f' : A → A'} {g g' : B → B'} (Hf : ∀ a, f a ≡ f' a)
    (Hg : ∀ a, g a ≡ g' a) : Prod.map f g x ≡ Prod.map f' g' x :=
  fun n => ⟨Hf x.fst n, Hg x.snd n⟩

omit [OFE A] [OFE B] in
theorem Prod.map_ne {f f' : A → A'} {g g' : B → B'} (Hf : ∀ a, f a ≡{n}≡ f' a)
    (Hg : ∀ a, g a ≡{n}≡ g' a) : Prod.map f g x ≡{n}≡ Prod.map f' g' x :=
  ⟨Hf x.fst, Hg x.snd⟩

@[rocq_alias prodO_map]
def Prod.mapO (f : A -n> A') (g : B -n> B') : A × B -n> A' × B' where
  f := .map f g
  ne := inferInstance

@[rocq_alias prodO_map_ne]
instance Prod.mapO_ne : NonExpansive₂ (Prod.mapO (A := A) (A' := A') (B := B) (B' := B')) where
  ne _ _ _ Hf _ _ Hg _ := Prod.map_ne Hf Hg

abbrev ProdOF (F1 F2 : OFunctorPre) : OFunctorPre := fun A B => (F1 A B) × (F2 A B)

open OFunctor in
@[rocq_alias prodOF]
instance instOFunctorProdOF [OFunctor F1] [OFunctor F2] : OFunctor (ProdOF F1 F2) where
  ofe := inferInstance
  map f g := Prod.mapO (map f g) (map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ := ⟨map_ne.ne Hx Hy _, map_ne.ne Hx Hy _⟩
  map_id _ := equiv_prod_ext (map_id _) (map_id _)
  map_comp _ _ _ _ _ := equiv_prod_ext (map_comp _ _ _ _ _) (map_comp _ _ _ _ _)

open OFunctorContractive in
@[rocq_alias prodOF_contractive]
instance instOFunctorContractiveProdOF [OFunctorContractive F1] [OFunctorContractive F2] :
    OFunctorContractive (ProdOF F1 F2) where
  map_contractive.1 H _ :=
   Prod.map_ne (fun _ => map_contractive.1 H _) (fun _ => map_contractive.1 H _)

end ProdOF

section SumOF

open COFE

variable [OFE A] [OFE A'] [OFE B] [OFE B']

@[rocq_alias sum_map_ne]
instance instNonExpansiveSumMap (f : A → A') (g : B → B') [NonExpansive f] [NonExpansive g] :
    NonExpansive (Sum.map f g) where
  ne _ x y H := match x, y with
    | .inl _, .inl _ => NonExpansive.ne (f := Sum.inl) (NonExpansive.ne (dist_ext_left H))
    | .inr _, .inr _ => NonExpansive.ne (f := Sum.inr) (NonExpansive.ne (dist_ext_right H))

omit [OFE A] [OFE B] in
theorem Sum.map_ext {f f' : A → A'} {g g' : B → B'} (Hf : ∀ a, f a ≡ f' a)
    (Hg : ∀ a, g a ≡ g' a) : Sum.map f g x ≡ Sum.map f' g' x :=
    match x with
    | .inl _ => equiv_inl (Hf _)
    | .inr _ => equiv_inr (Hg _)

omit [OFE A] [OFE B] in
theorem Sum.map_ne {f f' : A → A'} {g g' : B → B'} (Hf : ∀ a, f a ≡{n}≡ f' a)
    (Hg : ∀ a, g a ≡{n}≡ g' a) : Sum.map f g x ≡{n}≡ Sum.map f' g' x :=
    match x with
    | .inl _ => dist_inl (Hf _)
    | .inr _ => dist_inr (Hg _)

@[rocq_alias sumO_map]
def Sum.mapO (f : A -n> A') (g : B -n> B') : A ⊕ B -n> A' ⊕ B' where
  f := .map f g
  ne := inferInstance

@[rocq_alias sumO_map_ne]
instance Sum.mapO_ne : NonExpansive₂ (Sum.mapO (A := A) (A' := A') (B := B) (B' := B')) where
  ne _ _ _ Hf _ _ Hg _ := Sum.map_ne Hf Hg

abbrev SumOF (F1 F2 : OFunctorPre) : OFunctorPre := fun A B => (F1 A B) ⊕ (F2 A B)

open OFunctor in
@[rocq_alias sumOF]
instance instOFunctorSumOF [OFunctor F1] [OFunctor F2] : OFunctor (SumOF F1 F2) where
  ofe := inferInstance
  map f g := Sum.mapO (map f g) (map f g)
  map_ne.ne _ _ _ Hx _ _ Hy x := match x with
    | .inl _ => dist_inl (map_ne.ne Hx Hy _)
    | .inr _ => dist_inr (map_ne.ne Hx Hy _)
  map_id x := match x with
    | .inl _ => equiv_inl (map_id _)
    | .inr _ => equiv_inr (map_id _)
  map_comp _ _ _ _ x := match x with
    | .inl _ => equiv_inl (map_comp _ _ _ _ _)
    | .inr _ => equiv_inr (map_comp _ _ _ _ _)

open OFunctorContractive in
@[rocq_alias sumOF_contractive]
instance instOFunctorContractiveSumOF [OFunctorContractive F1] [OFunctorContractive F2] :
    OFunctorContractive (SumOF F1 F2) where
  map_contractive.1 H _ :=
    Sum.map_ne (fun _ => map_contractive.1 H _) (fun _ => map_contractive.1 H _)

end SumOF

section SigmaOF

open COFE

@[rocq_alias sigT_map]
def Sigma.mapO {P1 P2 : A → Type _} [∀ x, OFE (P1 x)] [∀ x, OFE (P2 x)] :
  ((a : A) → P1 a -n> P2 a) -n> Sigma P1 -n> Sigma P2 where
  f g := ⟨fun x => ⟨_, g x.fst x.snd⟩, ⟨by rintro n ⟨x, xH⟩ ⟨y, yH⟩ ⟨⟨⟩, hdist⟩; exact ⟨rfl, (g x).ne.ne hdist⟩⟩⟩
  ne := ⟨fun n f g hdist x => ⟨rfl, hdist _ _⟩⟩

open OFunctor in
abbrev SigmaOF (F : A → OFunctorPre) : OFunctorPre :=
  fun B C => Sigma (fun (a : A) => (F a) B C)

open OFunctor in
@[rocq_alias sigTOF]
instance instOFunctorSigmaOF {F : A → OFunctorPre} [∀ a, OFunctor (F a)] : OFunctor (SigmaOF F) where
  ofe := inferInstance
  map f g := Sigma.mapO (fun _ => map f g)
  map_ne.ne _ _ _ Hx _ _ Hy := NonExpansive.ne (fun _ => map_ne.ne Hx Hy)
  map_id _ _ := ⟨rfl, (map_id _).dist⟩
  map_comp _ _ _ _ _ _ := ⟨rfl, (map_comp _ _ _ _ _).dist⟩

open OFunctorContractive in
@[rocq_alias sigTOF_contractive]
instance instOFunctorContractiveSigmaOF [∀ a, OFunctorContractive (F a)] :
    OFunctorContractive (SigmaOF F) where
  map_contractive.1 H := Sigma.mapO.ne.ne (fun _ => map_contractive.1 H)

end SigmaOF

section constOF

open COFE

abbrev constOF (B : Type) : OFunctorPre := fun _ _ _ _ => B

@[rocq_alias constOF]
instance oFunctorConstOF [COFE B] : OFunctor (constOF B) where
  ofe := _
  map _ _ := ⟨id, id_ne⟩
  map_ne := by intros; constructor; simp
  map_id := by simp
  map_comp := by simp

@[rocq_alias constOF_contractive]
instance OFunctor.constOF_contractive [COFE B] : OFunctorContractive (constOF B) where
  map_contractive.1 := by simp [OFunctor.map]

end constOF

section IdOF

open COFE

abbrev IdOF : OFunctorPre := fun (_ : Type _) (B : Type _) (_ : COFE _) (_ : COFE B) => B

open OFunctor in
@[rocq_alias idOF]
instance : OFunctor IdOF where
  ofe := inferInstance
  map _ g := g
  map_ne.ne _ _ _ _ _ _ Hy := Hy
  map_id _ := .rfl
  map_comp _ _ _ _ _ := .rfl

end IdOF

section HomOF

open COFE

variable [OFE A] [OFE A'] [OFE B] [OFE B']

@[rocq_alias ofe_morO_map]
def Hom.map (pre : A' -n> A) (post : B -n> B') : (A -n> B) -n> (A' -n> B') where
  f h := post.comp (h.comp pre)
  ne.ne _ _ _ Hh := fun x => post.ne.ne (Hh (pre x))
#rocq_ignore ofe_mor_map "Function-space map; subsumed by `Hom.map` in Lean."
#rocq_ignore ofe_mor_map_ne "Function-space map proof; subsumed by `Hom.map` in Lean."

@[rocq_alias ofe_morO_map_ne]
instance instNonExpansive₂HomMap :
    NonExpansive₂ (Hom.map (A := A) (A' := A') (B := B) (B' := B')) where
  ne {_ _ _} Hx {y₁ _} Hy f g :=
    (NonExpansive.ne (f := y₁) (NonExpansive.ne (f := f) (Hx g))).trans (Hy _)

abbrev HomOF (F1 F2 : OFunctorPre) [OFunctor F1] [OFunctor F2] : OFunctorPre :=
  fun (A : Type _) (B : Type _) (_ : COFE A) (_ : COFE B) => @F1 B A _ _ -n> @F2 A B _ _

open OFunctor in
@[rocq_alias ofe_morOF]
instance instOFunctorHomOF [OFunctor F1] [OFunctor F2] : OFunctor (HomOF F1 F2) where
  ofe := inferInstance
  map f g := Hom.map (map (F := F1) g f) (map (F := F2) f g)
  map_ne.ne _ _ _ Hf _ _ Hg := NonExpansive₂.ne (map_ne.ne Hg Hf) (map_ne.ne Hf Hg)
  map_id _ _ _ := ((map_id _).trans (NonExpansive.eqv (map_id _))).dist
  map_comp _ _ _ _ _ _ _ := ((map_comp _ _ _ _ _).trans
    (NonExpansive.eqv (NonExpansive.eqv (NonExpansive.eqv ((map_comp _ _ _ _ _).trans .rfl))))).dist

open OFunctorContractive in
@[rocq_alias ofe_morOF_contractive]
instance instOFunctorContractiveHomOF [OFunctorContractive F1] [OFunctorContractive F2] :
    OFunctorContractive (HomOF F1 F2) where
  map_contractive.1 {n} ab ab' h := match ab, ab' with
    | ⟨a, b⟩, ⟨a', b'⟩ => by
      simp only [Function.uncurry_apply_pair, OFunctor.map]
      have h' : DistLater n (b, a) (b', a') :=
        match n with
        | 0 => distLater_zero
        | _ + 1 => distLater_succ.mpr ⟨(distLater_succ.mp h).2, (distLater_succ.mp h).1⟩
      refine NonExpansive₂.ne ?_ ?_
      · exact (map_contractive (F := F1)).1 h'
      · exact (map_contractive (F := F2)).1 h

end HomOF

section Fixpoint

@[rocq_alias LimitPreserving]
def LimitPreserving [COFE α] (P : α → Prop) : Prop :=
  ∀ (c : Chain α), (∀ n, P (c n)) → P (COFE.compl c)

@[rocq_alias limit_preserving_const]
theorem LimitPreserving.const [COFE α] {P : Prop} : LimitPreserving fun (_ : α) => P := by
  simp [LimitPreserving]

@[rocq_alias limit_preserving_discrete]
theorem LimitPreserving.discrete [COFE α] {P : α → Prop} :
    (∀ {x y : α}, x ≡{0}≡ y → (P x → P y)) → LimitPreserving P :=
  fun Hdisc _ H => Hdisc COFE.conv_compl.symm (H _)

@[rocq_alias limit_preserving_and]
theorem LimitPreserving.and [COFE α] {P Q : α → Prop} (HP : LimitPreserving P)
    (HQ : LimitPreserving Q) : LimitPreserving fun a => P a ∧ Q a :=
  fun _ HPQ => ⟨HP _ (fun n => (HPQ n).left), HQ _ (fun n => (HPQ n).right)⟩

@[rocq_alias limit_preserving_forall]
theorem LimitPreserving.forall [COFE α] (P : β → α → Prop) (Hlim : ∀ y, LimitPreserving (P y)) :
    LimitPreserving (∀ y, P y ·) :=
  fun c H y => Hlim y c (H · y)

@[rocq_alias limit_preserving_impl]
theorem LimitPreserving.impl [COFE α] (P1 P2 : α → Prop)
    (HP1 : ∀ {x y : α}, x ≡{0}≡ y → P1 x → P1 y)
    (Hcompl : LimitPreserving P2) :
    LimitPreserving (fun x => P1 x → P2 x) :=
  fun _ Hc HP1c => Hcompl _ <| fun n => Hc _ (HP1 (COFE.conv_compl' (Nat.zero_le n)) HP1c)

@[rocq_alias limit_preserving_equiv]
theorem LimitPreserving.equiv [COFE α] [COFE β] (f g : α -n> β) :
    LimitPreserving (fun x => f x ≡ g x) := by
  intro c Hfg
  refine equiv_dist.mpr fun n => ?_
  apply (COFE.compl_map _ _).symm.dist.trans
  apply (COFE.conv_compl' (Nat.le_refl n)).trans
  apply (Hfg _).dist.trans
  exact g.ne.ne COFE.conv_compl.symm

@[rocq_alias limit_preserving_ext]
theorem LimitPreserving.ext {α}[COFE α] {P Q : α -> Prop} (he : ∀ {x}, (P x ↔ Q x))
    (hp : LimitPreserving P) : LimitPreserving Q := fun _ => (he.1 <| hp _ <| fun _ => he.2 <| · _)

def Fixpoint.chain [OFE α] [Inhabited α] (f : α → α) [Contractive f] : Chain α where
  chain n := Nat.repeat f (n + 1) default
  cauchy {n} := by
    induction n with simp [Nat.repeat] | succ n IH
    rintro (_|i) <;> simp
    intro H
    apply Contractive.distLater_dist
    intro _ Hm
    exact (IH H).le (Nat.le_of_lt_succ Hm)

/-- The chain construction of the Banach fixpoint. `fixpointP` packages it, together with
its unfolding equation, behind an opaque constant. -/
def fixpointAux [COFE α] [Inhabited α] (f : α → α) [Contractive f] : α :=
  COFE.compl <| Fixpoint.chain f

theorem fixpointAux_unfold [COFE α] [Inhabited α] (f : α -c> α) :
    fixpointAux f ≡ f (fixpointAux f) := by
  refine equiv_dist.mpr fun n => ?_
  apply COFE.conv_compl.trans
  refine .trans ?_ (NonExpansive.ne COFE.conv_compl.symm)
  induction n with
  | zero => exact Contractive.zero f.f
  | succ _ IH => exact (Contractive.succ f.f IH.symm).symm

/-- The Banach fixpoint packed together with its unfolding equation as a single opaque
value. Being opaque, it is a stuck constant for definitional-equality checks in both the
elaborator and the kernel, which keeps the approximation chain of `fixpointAux` sealed. -/
opaque fixpointP [COFE α] [Inhabited α] (f : α → α) [Contractive f] : { x : α // x ≡ f x } :=
  ⟨fixpointAux f, fixpointAux_unfold f.toContractiveHom⟩

/-- Fixpoints inside of a COFE -/
@[rocq_alias fixpoint]
def fixpoint [COFE α] [Inhabited α] (f : α → α) [Contractive f] : α :=
  (fixpointP f).val
#rocq_ignore fixpoint_def "Use fixpoint"
#rocq_ignore fixpoint_aux "Use fixpoint"
#rocq_ignore fixpoint_unseal "fixpoint is unsealed by default"

nonrec abbrev OFE.ContractiveHom.fixpoint [COFE α] [Inhabited α] (f : α -c> α) : α := fixpoint f.f

@[rocq_alias fixpoint_unfold]
theorem fixpoint_unfold [COFE α] [Inhabited α] (f : α -c> α) :
    fixpoint f ≡ f (fixpoint f) :=
  (fixpointP f).property

@[rocq_alias fixpoint_unique]
theorem fixpoint_unique [COFE α] [Inhabited α] {f : α -c> α} {x : α} (H : x ≡ f x) :
    x ≡ fixpoint f := by
  refine equiv_dist.mpr fun n => ?_
  induction n with refine H.dist.trans <| .trans ?_ (fixpoint_unfold f).dist.symm
  | zero => exact Contractive.zero f.f
  | succ _ IH => exact Contractive.succ f.f IH

@[rocq_alias fixpoint_ne]
instance OFE.ContractiveHom.fixpoint_ne [COFE α] [Inhabited α] :
    NonExpansive (ContractiveHom.fixpoint (α := α)) where
  ne n f1 f2 H := by
    induction n with
      refine (fixpoint_unfold f1).dist.trans <|
        ((H _).trans ?_).trans (fixpoint_unfold f2).dist.symm
    | zero => exact Contractive.zero f2.f
    | succ _ IH => exact Contractive.succ f2.f <| IH <| Dist.lt H (Nat.lt_add_one _)

@[elab_as_elim, rocq_alias fixpoint_ind]
theorem OFE.ContractiveHom.fixpoint_ind [COFE α] [Inhabited α] (f : α -c> α)
    (P : α → Prop) (HProper : ∀ A B : α, A ≡ B → P A → P B) (x : α) (Hbase : P x)
    (Hind : ∀ x, P x → P (f x)) (Hlim : LimitPreserving P) :
    P f.fixpoint := by
  let chain : Chain α := by
    refine ⟨fun i => Nat.repeat f (i + 1) x, fun {n i} H => ?_⟩
    induction n generalizing i with
    | zero => simp [Nat.repeat]
    | succ _ IH =>
      cases i <;> simp at H
      exact Contractive.succ _ <| IH H
  refine HProper _ _ (fixpoint_unique (x := COFE.compl chain) ?_) ?_
  · refine equiv_dist.mpr fun n => ?_
    apply COFE.conv_compl.trans
    refine .trans ?_ (f.ne.ne COFE.conv_compl).symm
    induction n
    · exact Contractive.zero f.f
    · rename_i IH; apply Contractive.succ _ IH
  · apply Hlim; intro n
    induction n with
    | zero => exact Hind (Nat.repeat f.f 0 x) Hbase
    | succ _ IH => apply Hind (Nat.repeat f.f _ x) IH

end Fixpoint

section FixpointAB

open OFE

instance [OFE α] [OFE β] [OFE γ] : CoeFun (α -c> β -n> γ) (fun _ => α → β → γ) := ⟨fun f x => (f.f x).f⟩
instance [OFE α] [OFE β] [OFE γ] : CoeFun (α -c> β -c> γ) (fun _ => α → β → γ) := ⟨fun f x => (f.f x).f⟩

/-- A Contractive function with NonExpansive function codomain is NonExpansive₂. -/
instance ne₂_of_contractive_ne [OFE α] [OFE β] [OFE γ] (fA : α -c> β -n> γ) : NonExpansive₂ fA where
  ne n x₁ x₂ Hx y₁ y₂ Hy := by
    refine .trans ?_ ((fA.f x₂).ne.ne Hy)
    apply fA.ne.ne Hx

/-- A Contractive function with Contractive function codomain is NonExpansive₂. -/
instance ne₂_of_contractive [OFE α] [OFE β] [OFE γ] (fB : α -c> β -c> γ) : NonExpansive₂ fB where
  ne n x₁ x₂ Hx y₁ y₂ Hy := by
    refine .trans ?_ ((fB.f x₂).ne.ne Hy)
    apply fB.ne.ne Hx

@[rocq_alias fixpoint_AB]
def fixpointAB [COFE α] [COFE β] [Inhabited α] [Inhabited β] (fB : α -c> β -c> β) (x : α) : β := by
  let con_hom : β -c> β := {
    f := fB x,
    contractive := ⟨fB.f x |>.contractive.distLater_dist⟩
  }
  exact con_hom.fixpoint

@[rocq_alias fixpoint_AB_contractive]
theorem fixpointAB_contractive [COFE α] [COFE β] [Inhabited α] [Inhabited β] (fB : α -c> β -c> β) :
    Contractive (fixpointAB fB) where
  distLater_dist {n _ _} Dl := by
    apply ContractiveHom.fixpoint_ne.ne
    apply fB.contractive.distLater_dist
    exact Dl

@[rocq_alias fixpoint_AA]
def fixpointAA [COFE α] [COFE β] [Inhabited α] [Inhabited β] (fA : α -c> β -n> α)
    (fB : α -c> β -c> β) (x : α) : α :=
  fA x (fixpointAB fB x)

@[rocq_alias fixpoint_AA_contractive]
theorem fixpointAA_contractive [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) : Contractive (fixpointAA fA fB) where
  distLater_dist {_ _ x₂} Dl := by
    refine .trans ?_ ((fA.f x₂).ne.ne ((fixpointAB_contractive fB).distLater_dist Dl))
    apply fA.contractive.distLater_dist
    exact Dl

@[rocq_alias fixpoint_A]
def fixpointA [COFE α] [COFE β] [Inhabited α] [Inhabited β] (fA : α -c> β -n> α)
    (fB : α -c> β -c> β) : α := by
  let con_hom : α -c> α := {
    f := fixpointAA fA fB,
    contractive := ⟨(fixpointAA_contractive fA fB).distLater_dist⟩
  }
  exact con_hom.fixpoint

@[rocq_alias fixpoint_B]
def fixpointB [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) : β :=
  fixpointAB fB <| fixpointA fA fB

@[rocq_alias fixpoint_A_unfold]
theorem fixpointA_unfold [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) :
    fA (fixpointA fA fB) (fixpointB fA fB) ≡ (fixpointA fA fB) := by
  exact .symm (fixpoint_unfold _)

@[rocq_alias fixpoint_B_unfold]
theorem fixpointB_unfold [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) :
    fB (fixpointA fA fB) (fixpointB fA fB) ≡ (fixpointB fA fB) := by
  exact .symm (fixpoint_unfold _)

@[rocq_alias fixpoint_A_unique]
theorem fixpointA_unique [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) (Hp : fA p q ≡ p) (Hq : fB p q ≡ q) :
    p ≡ (fixpointA fA fB) := by
  refine Hp.symm.trans ?_
  apply fixpoint_unique
  have := ne₂_of_contractive_ne fA
  refine NonExpansive₂.eqv (f := fA) Hp.symm ?_
  apply fixpoint_unique
  have := ne₂_of_contractive fB
  exact Hq.symm.trans (NonExpansive₂.eqv (f := fB) Hp.symm .rfl)

@[rocq_alias fixpoint_B_unique]
theorem fixpointB_unique [COFE α] [COFE β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) (Hp : fA p q ≡ p) (Hq : fB p q ≡ q) :
    q ≡ (fixpointB fA fB) := by
  apply fixpoint_unique
  have := ne₂_of_contractive fB
  refine Hq.symm.trans (NonExpansive₂.eqv (f := fB) ?_ .rfl)
  exact fixpointA_unique fA fB Hp Hq

@[rocq_alias fixpoint_A_ne]
instance fixpointA_ne [COFE α] [COFE β] [Inhabited α] [Inhabited β] :
    NonExpansive₂ (fixpointA (α := α) (β := β)) where
  ne n fA fA' HfA fB fB' HfB := by
    apply OFE.ContractiveHom.fixpoint_ne.ne
    intro z₁
    refine ((ne₂_of_contractive_ne fA).ne .rfl ?_).trans (HfA z₁ _)
    exact ContractiveHom.fixpoint_ne.ne (HfB z₁)

@[rocq_alias fixpoint_B_ne]
instance fixpointB_ne [COFE α] [COFE β] [Inhabited α] [Inhabited β] :
    NonExpansive₂ (fixpointB (α := α) (β := β)) where
  ne n fA fA' HfA fB fB' HfB := by
    apply ContractiveHom.fixpoint_ne.ne
    intro z₁
    refine ((ne₂_of_contractive fB).ne ?_ .rfl).trans (HfB _ z₁)
    exact fixpointA_ne.ne HfA HfB

end FixpointAB

section Later

@[rocq_alias later] structure Later (A : Type u) : Type u where
  next :: car : A

@[rocq_alias later_ofe_mixin]
instance isOFE_later [OFE A] : OFE (Later A) where
  Dist n x y := DistLater n x.car y.car
  dist_eqv := ⟨fun _ => .rfl, .symm, .trans⟩
  eq_dist {x y} := by
    obtain ⟨a⟩ := x; obtain ⟨b⟩ := y
    simp only [Later.next.injEq, eq_dist]
    exact ⟨fun H n => (H n).distLater, fun H n => (H (n+1)).dist_lt (Nat.lt_succ_self n)⟩
  dist_lt Hxy Hmn _ Hkm := Hxy _ (Nat.lt_trans Hkm Hmn)
#rocq_ignore laterO "Use the later type"

#rocq_ignore later_equiv "Local Equiv instance; folded into Lean's OFE (Later A) instance."
#rocq_ignore later_dist "Local Dist instance; folded into Lean's OFE (Later A) instance."


@[rocq_alias Next_contractive]
instance NextContractive {A : Type _} [OFE A] : Contractive (@Later.next A) where
  distLater_dist := id


@[rocq_alias later_chain]
def laterChain [OFE A] (c : Chain (Later A)) : Chain A where
  chain n := (c (Nat.succ n)).car
  cauchy Hle := c.cauchy (Nat.succ_le_succ Hle) _ (Nat.lt_succ_self _)

@[rocq_alias later_cofe]
instance isCOFE_later [OFE A] [IsCOFE A] : IsCOFE (Later A) where
  compl c := Later.next (IsCOFE.compl (laterChain c))
  conv_compl {n} c := by
    rcases n with _|n' <;> simp [Dist, DistLater]
    intros m Hlt
    exact (IsCOFE.conv_compl (n := n') (c := laterChain c)).le (Nat.le_of_lt_succ Hlt)

@[rocq_alias laterO_map]
def laterMap [OFE A] [OFE B] (f : A -n> B)  : Later A -n> Later B := by
  refine ⟨fun x => Later.next (f x.car), ⟨?_⟩⟩
  rintro _ ⟨⟩ ⟨⟩ H <;> simp_all only [Dist, DistLater]
  intros m Hlt; exact f.ne.ne (H m Hlt)
#rocq_ignore later_map "Underlying map of laterMap"

#rocq_ignore later_map_ne "Implicit in type of laterMap"
#rocq_ignore later_map_ne' "Implicit in type of laterMap"
#rocq_ignore later_map_proper "Derived from nonexpansivity"

end Later

section LaterOF
open COFE

abbrev LaterOF (F : OFunctorPre) : OFunctorPre :=
  fun A B _ _ => Later (F A B)

variable (F : OFunctorPre)

@[rocq_alias laterOF]
instance instOFunctorLater [OFunctor F] : OFunctor (LaterOF F) where
  ofe := _
  map f g := laterMap (OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ _ := (OFunctor.map_ne.ne Hx Hy _).lt
  map_id x := fun _ m _ => (OFunctor.map_id x.car) m
  map_comp f g f' g' x := fun _ m _ => (OFunctor.map_comp f g f' g' x.car) m

@[rocq_alias laterOF_contractive]
instance instOFunctorContractiveLater [OFunctor F] : OFunctorContractive (LaterOF F) where
  map_contractive.1 H _ _ hlt :=
    OFunctor.map_ne.ne (DistLater.dist_lt H hlt).1 (DistLater.dist_lt H hlt).2 _

end LaterOF

theorem OFE.cast_dist [Iα : OFE α] [Iβ : OFE β] {x y : α}
    (Ht : α = β) (HIt : Iα = Ht ▸ Iβ)  (H : x ≡{n}≡ y) :
    (Ht ▸ x) ≡{n}≡ (Ht ▸ y) := by
  subst Ht; subst HIt; exact H
