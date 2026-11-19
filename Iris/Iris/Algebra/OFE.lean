/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Graf, Sergei Stepanenko, Markus de Medeiros
-/
module

public import Iris.Std.Nat
public import Iris.Algebra.StepIndex
public import Iris.Std.Option

@[expose] public section

namespace Iris

/-- An indexed family of distances, on a type -/
@[indexed, rocq_alias Dist]
class HasDist (SI : stepindex (Type _)) (α : Type _) where
  dist : SI → α → α → Prop

/-- Ordered family of equivalences -/
@[indexed, rocq_alias ofe]
class OFE (SI : stepindex (Type _)) [SIdx SI] (α : Type _) extends HasDist SI α where
  dist_eqv : Equivalence (dist n)
  eq_dist' : x = y ↔ ∀ n, dist n x y
  dist_lt : dist n x y → m < n → dist m x y

@[indexed]
abbrev OFE.Dist {SI : stepindex (Type _)} {α : Type _} [HasDist SI α] : SI → α → α → Prop :=
  HasDist.dist

#rocq_ignore OfeMixin "Use the OFE type class"
#rocq_ignore ofe_mixin_of' "Not needed"

#rocq_ignore dist_ne "Rewrite using Equiv.trans"
#rocq_ignore dist_proper "Rewrite using Equiv.trans"
#rocq_ignore dist_proper_2 "Rewrite using Equiv.trans"

open OFE

scoped notation:40 x " ≡{" n "}≡ " y:41 => OFE.Dist (SI := stepindex%) n x y

/-- Prints `OFE.Dist n x y` as `x ≡{n}≡ y`; the notation passes its step index by name, so no
unexpander is generated for it. -/
@[app_unexpander OFE.Dist] meta def OFE.Dist.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $n $x $y) => `($x ≡{$n}≡ $y)
  | _ => throw ()

variable {SI : stepindex (Type _)} [SIdx SI]
local stepindex SI

@[indexed, rocq_alias equiv_dist]
theorem OFE.eq_dist [OFEᵢ α] {x y : α} : x = y ↔ ∀ n, x ≡{n}≡ y := OFE.eq_dist'

@[indexed] theorem OFE.dist_of_eq [OFEᵢ α] {x y : α} : x = y → ∀ n, x ≡{n}≡ y :=
  OFE.eq_dist.mp

@[indexed] theorem OFE.eq_of_dist [OFEᵢ α] {x y : α} : (∀ n, x ≡{n}≡ y) → x = y :=
  OFE.eq_dist.mpr

namespace OFE

@[rocq_alias dist_equivalence]
theorem dist_equivalence [OFEᵢ α] {n} : Equivalence (Distᵢ (α := α) n) := dist_eqv

@[rocq_alias dist_lt]
theorem Dist.lt [OFEᵢ α] {m n} {x y : α} : x ≡{n}≡ y → m < n → x ≡{m}≡ y := dist_lt

@[rocq_alias ofe.dist_le]
theorem Dist.le [OFEᵢ α] {m n} {x y : α} (h : x ≡{n}≡ y) (h' : m ≤ n) : x ≡{m}≡ y :=
  if hm : m = n then hm ▸ h else h.lt (SIdx.le_neq.mpr ⟨h', hm⟩)
#rocq_ignore dist_le' "Use Dist.le"
#rocq_ignore ofe.dist_S "Subsumed by `Dist.lt`/`Dist.le`."

@[simp, refl] theorem Dist.rfl [OFEᵢ α] {n} {x : α} : x ≡{n}≡ x := dist_eqv.1 _
@[simp, refl] theorem Dist.refl [OFEᵢ α] {n} (x : α) : x ≡{n}≡ x := dist_eqv.1 _
@[symm] theorem Dist.symm [OFEᵢ α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ x := dist_eqv.2
theorem Dist.trans [OFEᵢ α] {n} {x : α} : x ≡{n}≡ y → y ≡{n}≡ z → x ≡{n}≡ z := dist_eqv.3
theorem Dist.of_eq [OFEᵢ α] {x y : α} : x = y → x ≡{n}≡ y := (· ▸ .rfl)

#rocq_ignore ofe_equivalence "OFE is Leibniz; use equality"
theorem _root_.Eq.dist [OFEᵢ α] {x y : α} (h : x = y) : x ≡{n}≡ y := h ▸ .rfl

instance [OFEᵢ α] {n} : Trans (OFE.Distᵢ n) (OFE.Distᵢ n) (OFE.Distᵢ n : α → α → Prop) where
  trans := Dist.trans

variable (SI) in
/-- A function `f : α → β` is non-expansive if it preserves `n`-equivalence. -/
@[indexed]
class NonExpansive [OFEᵢ α] [OFEᵢ β] (f : α → β) where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → f x₁ ≡{n}≡ f x₂

instance id_ne [OFEᵢ α] : NonExpansiveᵢ (@id α) := ⟨fun _ _ _ h => h⟩

instance const_ne [OFEᵢ α] [OFEᵢ β] {x : α} : NonExpansiveᵢ (Function.const β x) := ⟨fun _ _ _ _ => .rfl⟩

/-- Note: Not an instance, as any function can be decomposed as a composition in multiple ways. -/
theorem NonExpansive.comp [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] {g : β → γ} {f : α → β}
    (hg : NonExpansiveᵢ g) (hf : NonExpansiveᵢ f) : NonExpansiveᵢ (g ∘ f) :=
  ⟨fun {_ _ _} h => hg.ne (hf.ne h)⟩

#rocq_ignore ne_proper "OFE is Leibniz; use equality"

variable (SI) in
/-- A function `f : α → β → γ` is non-expansive if it preserves `n`-equivalence in each argument. -/
@[indexed]
class NonExpansive₂ [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] (f : α → β → γ) where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → ∀ ⦃y₁ y₂⦄, y₁ ≡{n}≡ y₂ → f x₁ y₁ ≡{n}≡ f x₂ y₂

#rocq_ignore ne_proper_2 "OFE is Leibniz; use equality"

/-- Note: Not an instance, for symmetry with NonExpansive₂.ne_left, which cannot be an instance. -/
@[indexed]
theorem NonExpansive₂.ne_right [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] (f : α → β → γ) [NonExpansive₂ᵢ f]
    (a : α) : NonExpansiveᵢ (f a) :=
  ⟨fun {_ _ _} h => ne Dist.rfl h⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem NonExpansive₂.ne_left [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] (f : α → β → γ) [NonExpansive₂ᵢ f]
    (b : β) : NonExpansiveᵢ (f · b) :=
  ⟨fun {_ _ _} h => ne h Dist.rfl⟩

variable (SI) in
/-- A function `f : α → β → γ → δ` is non-expansive if it preserves `n`-equivalence in each
argument. -/
@[indexed]
class NonExpansive₃ [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] [OFEᵢ δ] (f : α → β → γ → δ) where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → ∀ ⦃y₁ y₂⦄, y₁ ≡{n}≡ y₂ → ∀ ⦃z₁ z₂⦄, z₁ ≡{n}≡ z₂ →
    f x₁ y₁ z₁ ≡{n}≡ f x₂ y₂ z₂

variable (SI) in
/-- A function `f : α → β → γ → δ → ε` is non-expansive if it preserves `n`-equivalence in each
argument. -/
@[indexed]
class NonExpansive₄ [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] [OFEᵢ δ] [OFEᵢ ε] (f : α → β → γ → δ → ε) where
  ne : ∀ ⦃n x₁ x₂⦄, x₁ ≡{n}≡ x₂ → ∀ ⦃y₁ y₂⦄, y₁ ≡{n}≡ y₂ → ∀ ⦃z₁ z₂⦄, z₁ ≡{n}≡ z₂ →
    ∀ ⦃w₁ w₂⦄, w₁ ≡{n}≡ w₂ → f x₁ y₁ z₁ w₁ ≡{n}≡ f x₂ y₂ z₂ w₂

/-- `DistLater n x y` means that `x` and `y` are `m`-equivalent for all `m < n`. -/
@[indexed, rocq_alias dist_later]
def DistLater [OFEᵢ α] (n : SI) (x y : α) : Prop := ∀ m, m < n → x ≡{m}≡ y

@[simp, refl] theorem DistLater.rfl [OFEᵢ α] {n} {x : α} : DistLaterᵢ n x x := fun _ _ => .rfl
@[simp, refl] theorem DistLater.refl [OFEᵢ α] {n} (x : α) : DistLaterᵢ n x x := fun _ _ => .rfl
@[symm] theorem DistLater.symm [OFEᵢ α] {n} {x : α} (h : DistLaterᵢ n x y) : DistLaterᵢ n y x :=
  fun _ hm => (h _ hm).symm
theorem DistLater.trans [OFEᵢ α] {n} {x : α} (h1 : DistLaterᵢ n x y) (h2 : DistLaterᵢ n y z) :
    DistLaterᵢ n x z := fun _ hm => (h1 _ hm).trans (h2 _ hm)

/-- `DistLater n`-equivalence is an equivalence relation. -/
@[rocq_alias dist_later_equivalence]
theorem distLater_eqv [OFEᵢ α] {n} : Equivalence (α := α) (DistLaterᵢ n) where
  refl := DistLater.refl
  symm h := h.symm
  trans h1 := h1.trans

/-- `n`-equivalence implies `DistLater n`-equivalence. -/
@[rocq_alias dist_dist_later]
theorem Dist.distLater [OFEᵢ α] {n} {x y : α} (h : x ≡{n}≡ y) : DistLaterᵢ n x y :=
  fun _ => dist_lt h

/-- `DistLater n`-equivalence implies `m`-equivalence for all `m < n`. -/
@[rocq_alias dist_later_dist_lt]
theorem DistLater.dist_lt [OFEᵢ α] {m n} {x y : α} (h : DistLaterᵢ n x y) (hm : m < n) : x ≡{m}≡ y :=
  h _ hm

/-- `DistLater 0`-equivalence is trivial. -/
@[simp, rocq_alias dist_later_0] theorem distLater_zero [OFEᵢ α] {x y : α} : DistLaterᵢ 0 x y :=
  fun m hm => absurd hm (SIdx.not_lt_zero m)

/-- `DistLater n`-equivalence is equivalent to `(n + 1)`-equivalence. -/
@[rocq_alias ofe.dist_later_S]
theorem distLater_succ [OFEᵢ α] {n} {x y : α} : DistLaterᵢ (SIdx.succ n) x y ↔ x ≡{n}≡ y :=
  ⟨(·.dist_lt (SIdx.lt_succ_self _)), fun h1 _ h2 => h1.le (SIdx.lt_succ_r.mp h2)⟩

theorem distLater_soundness [OFEᵢ α] {x y : α} (H : ∀ n, DistLaterᵢ n x y → x ≡{n}≡ y) : x = y :=
  OFE.eq_of_distᵢ (SIdx.lt_wf.induction · H)

variable (SI) in
/-- A function `f : α → β` is contractive if it sends `DistLater n`-equivalent inputs to
`n`-equivalent outputs. -/
@[indexed]
class Contractive [OFEᵢ α] [OFEᵢ β] (f : α → β) where
  distLater_dist : DistLaterᵢ n x y → f x ≡{n}≡ f y

@[simp, rocq_alias contractive_0] theorem Contractive.zero [OFEᵢ α] [OFEᵢ β] (f : α → β)
    [Contractiveᵢ f] {x y} : f x ≡{0}≡ f y :=
  Contractive.distLater_dist distLater_zero

@[rocq_alias ofe.contractive_S]
theorem Contractive.succ [OFEᵢ α] [OFEᵢ β] (f : α → β) [Contractiveᵢ f] {n} {x y}
    (h : x ≡{n}≡ y) : f x ≡{SIdx.succ n}≡ f y :=
  Contractive.distLater_dist (distLater_succ.2 h)

/-- A contractive function is non-expansive. -/
@[rocq_alias contractive_ne]
instance ne_of_contractive [OFEᵢ α] [OFEᵢ β] (f : α → β) [Contractiveᵢ f] : NonExpansiveᵢ f where
  ne := fun _ _ _ h => Contractive.distLater_dist (Dist.distLater h)

#rocq_ignore contractive_proper "OFE is Leibniz; use equality"

@[rocq_alias contractive_dist_later_dist]
theorem Contractive.dist_later_dist [OFEᵢ α] [OFEᵢ β] (f : α → β) [Contractiveᵢ f] {n x y}
    (h : DistLaterᵢ n x y) : f x ≡{n}≡ f y := Contractive.distLater_dist h

/-- Pre-composing a non-expansive function preserves `DistLater`. -/
@[rocq_alias ne_dist_later]
theorem ne_dist_later [OFEᵢ α] [OFEᵢ β] (f : α → β) [NonExpansiveᵢ f] {n x y}
    (h : DistLaterᵢ n x y) : DistLaterᵢ n (f x) (f y) := fun m hm => NonExpansive.ne (h m hm)

@[rocq_alias dist_pointwise_lt]
theorem dist_pointwise_lt [OFEᵢ β] {n m} {f g : α → β} (hlt : m < n)
    (hp : ∀ a, DistLaterᵢ n (f a) (g a)) : ∀ a, f a ≡{m}≡ g a := fun a => hp a m hlt

/-- Constant functions are contractive. -/
@[rocq_alias const_contractive]
instance [OFEᵢ α] [OFEᵢ β] {x : β} : Contractiveᵢ (fun _ : α => x) where
  distLater_dist := fun _ => Dist.rfl

/-- The discrete OFE obtained from an equality relation `Eq` -/
@[reducible, rocq_alias discrete_ofe_mixin]
def ofDiscrete (α : Type _) : OFEᵢ α where
  dist _ := Eq
  dist_eqv := ⟨congrFun rfl, (Eq.symm ·), (· ▸ ·)⟩
  eq_dist' := (forall_const _).symm
  dist_lt h _ := h

variable (SI) in
/-- A discrete element in an OFE -/
@[indexed, rocq_alias Discrete]
class DiscreteE {α : Type _} [OFEᵢ α] (x : α) : Prop where
  discrete : x ≡{0}≡ y → x = y
attribute [indexed] DiscreteE.discrete

variable (SI) in
/-- A discrete OFE is one where equality is implied by `0`-equivalence. -/
@[indexed, rocq_alias OfeDiscrete]
class Discrete (α : Type _) [OFEᵢ α] where
  discrete_0 {x y : α} : x ≡{0}≡ y → x = y
export OFE.Discrete (discrete_0)

@[rocq_alias Discrete_proper]
theorem discreteE_eq [OFEᵢ α] {x y : α} (h : x = y) : DiscreteEᵢ x ↔ DiscreteEᵢ y := h ▸ Iff.rfl

#rocq_ignore ofe_discrete_subrelation "Not needed"
#rocq_ignore discrete_ofe_discrete "Not needed"

/-- For discrete OFEs, `n`-equivalence implies equality. -/
@[rocq_alias discrete]
theorem Discrete.discrete [OFEᵢ α] [Discreteᵢ α] {n} {x y : α} (h : x ≡{n}≡ y) : x = y :=
  discrete_0 <| h.le SIdx.le_0_l
export OFE.Discrete (discrete)

/-- Every function out of a discrete OFE is non-expansive. -/
instance ne_of_discrete [OFEᵢ α] [Discreteᵢ α] [OFEᵢ β] (f : α → β) :
    NonExpansiveᵢ f :=
  ⟨fun _ _ _ Hx => .of_eq (congrArg f <| discrete Hx)⟩

instance Discrete.toDiscreteE [OFEᵢ α] [Discreteᵢ α] (x : α) : DiscreteEᵢ x := ⟨discrete_0⟩

/-- For discrete OFEs, `0`-equivalence implies equivalence for any `n`. -/
theorem Discrete.discrete_n [OFEᵢ α] [Discreteᵢ α] {n} {x y : α} (h : x ≡{0}≡ y) : x ≡{n}≡ y :=
  (discrete h).dist
export OFE.Discrete (discrete_n)

@[rocq_alias discrete_iff]
theorem Discrete.discrete_iff [OFEᵢ α] [Discreteᵢ α] (n) {x y : α} : x = y ↔ x ≡{n}≡ y :=
  ⟨Eq.dist, discrete⟩

@[rocq_alias discrete_iff_0]
theorem Discrete.discrete_iff_0 [OFEᵢ α] [Discreteᵢ α] (n) {x y : α} : x ≡{0}≡ y ↔ x ≡{n}≡ y :=
  ⟨discrete_n, fun h => h.le SIdx.le_0_l⟩

#rocq_ignore boolO "Canonical Leibniz OFE on `bool`; Lean uses `ofDiscrete Bool`."
#rocq_ignore natO "Canonical Leibniz OFE on `nat`; Lean uses `ofDiscrete Nat`."
#rocq_ignore positiveO "Canonical Leibniz OFE on `positive`; not applicable in Lean."
#rocq_ignore NO "Canonical Leibniz OFE on `N`; not applicable in Lean."
#rocq_ignore ZO "Canonical Leibniz OFE on `Z`; not applicable in Lean."
#rocq_ignore PropO "Canonical discrete OFE on `Prop`; Lean uses `ofDiscrete Prop`."
#rocq_ignore discrete_dist "All equivalences are equalities in Iris-Lean."
#rocq_ignore Prop_equiv "All equivalences are equalities in Iris-Lean."
#rocq_ignore Prop_equivalence "Consequence of propext."

#rocq_ignore ofe_leibniz_subrelation "Generalized-rewriting subrelation; not needed in Lean."

/-- Build a Leibniz OFE on `Quotient s` from a step-indexed distance `dist` on the carrier,
given that the setoid relation coincides with the OFE equivalence `fun x y => ∀ n, dist n x y`
(hypothesis `hs`). Quotienting forces the resulting OFE equality to be Leibniz, while
`Quotient.sound`/`Quotient.exact` keep speaking about the domain relation `s.r`. See
https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/Evaluating.20a.20specialization.20to.20Leibnize.20OFE.27s/with/606745235 -/
@[reducible] def ofQuotient {X : Type u} {s : Setoid X} (dist : SI → X → X → Prop)
    (heqv : ∀ {n}, Equivalence (dist n))
    (hlt : ∀ {n m} {x y : X}, dist n x y → m < n → dist m x y)
    (hs : ∀ x y : X, s.r x y ↔ ∀ n, dist n x y) : OFEᵢ (Quotient s) :=
  letI D : SI → Quotient s → Quotient s → Prop :=
    fun n => Quotient.lift₂ (dist n) fun _ _ _ _ hac hbd => propext <|
      have hac' := (hs _ _).mp hac
      have hbd' := (hs _ _).mp hbd
      ⟨fun h => heqv.trans (heqv.trans (heqv.symm (hac' n)) h) (hbd' n),
       fun h => heqv.trans (heqv.trans (hac' n) h) (heqv.symm (hbd' n))⟩
  { dist := D
    dist_eqv := by
      refine ⟨Quotient.ind fun a => heqv.refl a, fun {x y} h => ?_, fun {x y z} h₁ h₂ => ?_⟩
      · induction x, y using Quotient.ind₂ with | _ a b => exact heqv.symm h
      · induction x, y using Quotient.ind₂ with | _ a b =>
          induction z using Quotient.ind with | _ c => exact heqv.trans h₁ h₂
    eq_dist' {x y} := by
      induction x, y using Quotient.ind₂ with | _ a b =>
        exact ⟨fun h n => (hs _ _).mp (Quotient.exact h) n,
               fun h => Quotient.sound ((hs _ _).mpr h)⟩
    dist_lt := fun {n x y m} h hlt' => by
      induction x, y using Quotient.ind₂ with | _ a b => exact hlt h hlt' }

namespace ofQuotient

variable {X : Type u} {s : Setoid X}

@[reducible] def mk (s : Setoid X) (x : X) : Quotient s := Quotient.mk s x

@[elab_as_elim] theorem ind {motive : Quotient s → Prop}
    (mk : ∀ x : X, motive (mk s x)) (q : Quotient s) : motive q :=
  Quotient.ind mk q

@[elab_as_elim] theorem ind₂ {motive : Quotient s → Quotient s → Prop}
    (mk : ∀ x y : X, motive (mk s x) (mk s y)) (x y : Quotient s) : motive x y :=
  Quotient.ind₂ mk x y

@[elab_as_elim] theorem ind₃ {motive : Quotient s → Quotient s → Quotient s → Prop}
    (mk : ∀ x y z : X, motive (mk s x) (mk s y) (mk s z)) (x y z : Quotient s) :
    motive x y z :=
  ind₂ (fun x y => Quotient.ind (mk x y)) x y z

theorem sound {x y : X} (h : s.r x y) : mk s x = mk s y := Quotient.sound h

theorem exact {x y : X} (h : mk s x = mk s y) : s.r x y := Quotient.exact h

theorem mk_eq {x y : X} : mk s x = mk s y ↔ s.r x y := ⟨exact, sound⟩

@[reducible] def lift {β : Sort v} (f : X → β)
    (resp : ∀ x y, s.r x y → f x = f y) : Quotient s → β := Quotient.lift f resp

@[simp] theorem lift_mk {β : Sort v} (f : X → β) (resp) (x : X) :
    lift (s := s) f resp (mk s x) = f x := rfl

@[reducible] def lift₂ {β : Sort v} (f : X → X → β)
    (resp : ∀ a b c d, s.r a c → s.r b d → f a b = f c d) :
    Quotient s → Quotient s → β := Quotient.lift₂ f resp

@[simp] theorem lift₂_mk {β : Sort v} (f : X → X → β) (resp) (x y : X) :
    lift₂ (s := s) f resp (mk s x) (mk s y) = f x y := rfl

@[reducible] def map {X' : Type u'} {s' : Setoid X'} (f : X → X')
    (hf : ∀ x y, s.r x y → s'.r (f x) (f y)) : Quotient s → Quotient s' :=
  Quotient.lift (fun x => mk s' (f x)) (fun _ _ h => sound (hf _ _ h))

@[simp] theorem map_mk {X' : Type u'} {s' : Setoid X'} (f : X → X') (hf) (x : X) :
    map (s := s) (s' := s') f hf (mk s x) = mk s' (f x) := rfl

theorem dist_mk {dist : SI → X → X → Prop} {heqv : ∀ {n}, Equivalence (dist n)}
    {hlt : ∀ {n m} {x y : X}, dist n x y → m < n → dist m x y}
    {hs : ∀ x y : X, s.r x y ↔ ∀ n, dist n x y} {n} {x y : X} :
    (ofQuotient dist heqv hlt hs).dist n (mk s x) (mk s y) ↔ dist n x y := Iff.rfl

end ofQuotient

/-- A morphism between OFEs, written `α -n> β`, is defined to be a function that is
non-expansive. -/
@[indexed, ext, rocq_alias ofe_mor] structure Hom (α β : Type _) [OFEᵢ α] [OFEᵢ β] where
  f : α → β
  ne : NonExpansiveᵢ f
#rocq_ignore ofe_mor_proper "Derived from nonexpansivity"
#rocq_ignore ofe_mor_ext "Use ext"

/-- Non-expansive functions. -/
notation:25 α:26 " -n> " β:25 => Iris.OFE.Hom (SI := stepindex%) α β

/-- Prints `OFE.Hom α β` as `α -n> β`. -/
@[app_unexpander Iris.OFE.Hom] meta def Hom.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $α $β) => `($α -n> $β)
  | _ => throw ()

instance [OFEᵢ α] [OFEᵢ β] : CoeFun (α -n> β) (fun _ => α → β) := ⟨Hom.f⟩
instance [OFEᵢ α] [OFEᵢ β] (f : α -n> β) : NonExpansiveᵢ f := f.ne

/-- The identity morphism on an OFE. -/
@[rocq_alias cid]
protected def Hom.id [OFEᵢ α] : α -n> α where
  f := id
  ne.ne _ _ _ := id

/-- The composition of two morphisms between OFEs. -/
@[rocq_alias ccompose]
protected def Hom.comp [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] (g : β -n> γ) (f : α -n> β) : α -n> γ where
  f := g.f ∘ f.f
  ne.1 _ _ _ h := g.ne.1 (f.ne.1 h)
#rocq_ignore ccompose_ne "Implicit in type of ccompose"
#rocq_ignore ccompose_proper "Derived from nonexpansivity"

@[simp] theorem Hom.id_apply [OFEᵢ α] {x} : (Hom.id : α -n> α) x = x := rfl
@[simp] theorem Hom.comp_apply [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] {g : β -n> γ} {f : α -n> β} {x} :
    (g.comp f) x = g (f x) := rfl

@[simp] theorem Hom.id_comp [OFEᵢ α] [OFEᵢ β] {f : α -n> β} : Hom.id.comp f = f := rfl
@[simp] theorem Hom.comp_id [OFEᵢ α] [OFEᵢ β] {f : α -n> β} : f.comp Hom.id = f := rfl

theorem Hom.comp_assoc [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] [OFEᵢ δ]
    (h : γ -n> δ) (g : β -n> γ) (f : α -n> β) : (h.comp g).comp f = h.comp (g.comp f) := rfl

@[rocq_alias cconst]
protected def Hom.const [OFEᵢ α] [OFEᵢ β] (x : β) : α -n> β where
  f := Function.const α x
  ne.ne _ _ _ _ := Dist.rfl

@[simp] theorem Hom.const_apply [OFEᵢ α] [OFEᵢ β] {x : β} {a : α} :
    (Hom.const x : α -n> β) a = x := rfl

/-- Construct a `Hom` from a subtype bundling a function with its nonexpansiveness proof. -/
@[indexed]
def Hom.ofSubtype [OFEᵢ α] [OFEᵢ β] (f : { f : α → β // NonExpansiveᵢ f }) : α -n> β :=
  ⟨f.val, f.property⟩

@[indexed, ext] structure ContractiveHom (α β : Type _) [OFEᵢ α] [OFEᵢ β] extends Homᵢ α β where
  [contractive : Contractiveᵢ f]
  ne := ne_of_contractive f

/-- Contractive functions. -/
notation:25 α:26 " -c> " β:25 => Iris.OFE.ContractiveHom (SI := stepindex%) α β

/-- Prints `OFE.ContractiveHom α β` as `α -c> β`. -/
@[app_unexpander Iris.OFE.ContractiveHom] meta def ContractiveHom.unexpand :
    Lean.PrettyPrinter.Unexpander
  | `($_ $α $β) => `($α -c> $β)
  | _ => throw ()

instance [OFEᵢ α] [OFEᵢ β] : CoeFun (α -c> β) (fun _ => α → β) := ⟨fun x => x.toHom.f⟩
instance [OFEᵢ α] [OFEᵢ β] (f : α -c> β) : Contractiveᵢ f := f.contractive

@[indexed]
def _root_.Function.toContractiveHom (f : α → β) [OFEᵢ α] [OFEᵢ β] [ι : Contractiveᵢ f] :
    α -c> β where
  f := f
  contractive := ι

@[simp] theorem _root_.Function.toContractiveHom_apply {f : α → β} [OFEᵢ α] [OFEᵢ β]
    [ι : Contractiveᵢ f] {x} :
  Function.toContractiveHomᵢ f x = f x := by rfl

theorem InvImage.equivalence {α : Sort u} {β : Sort v}
    {r : β → β → Prop} {f : α → β} (H : Equivalence r) : Equivalence (InvImage r f) where
  refl _ := H.refl _
  symm := H.symm
  trans := H.trans

@[rocq_alias unit_ofe_mixin]
instance unitOFE : OFEᵢ Unit where
  dist _ _ _ := True
  dist_eqv := ⟨fun _ => ⟨⟩, id, fun _ => id⟩
  eq_dist' := by simp
  dist_lt _ _ := ⟨⟩
#rocq_ignore unitO "Use the unit type"
#rocq_ignore unit_dist "Local Dist instance; folded into Lean's OFE Unit instance."

instance : DiscreteEᵢ (() : Unit) := ⟨fun _ => Subsingleton.elim _ _⟩

@[rocq_alias Empty_set_ofe_mixin]
instance : OFEᵢ Empty where
  dist _ _ _ := True
  dist_eqv := ⟨fun _ => ⟨⟩, id, fun _ => id⟩
  eq_dist' {x} := x.elim
  dist_lt _ _ := ⟨⟩
#rocq_ignore Empty_setO "Use the empty type"
#rocq_ignore Empty_set_dist "Local Dist instance; folded into Lean's OFE Empty instance."

instance [OFEᵢ α] : OFEᵢ (ULift α) where
  dist n x y := x.down ≡{n}≡ y.down
  dist_eqv := InvImage.equivalence dist_eqv
  eq_dist' {x y} := by cases x; cases y; rw [ULift.up.injEq]; exact OFE.eq_distᵢ
  dist_lt := dist_lt

instance [OFEᵢ α] [Discreteᵢ α] : Discreteᵢ (ULift α) where
  discrete_0 h := congrArg ULift.up (discrete_0 h)

def uliftUpHom [OFEᵢ α] : α -n> ULift α where
  f := .up
  ne.1 _ _ _ := id

def uliftDownHom [OFEᵢ α] : ULift α -n> α where
  f := ULift.down
  ne.1 _ _ _ := id

@[rocq_alias option_ofe_mixin]
instance [OFEᵢ α] : OFEᵢ (Option α) where
  dist n := Option.Forall₂ (Distᵢ n)
  dist_eqv := Option.Forall₂.equivalence dist_eqv
  eq_dist' {x y} := by cases x <;> cases y <;> simp [Option.Forall₂]; exact OFE.eq_distᵢ
  dist_lt {_ x y _} := by cases x <;> cases y <;> simp [Option.Forall₂]; apply dist_lt
#rocq_ignore optionO "Use Option"
#rocq_ignore option_dist "Local Dist instance; folded into Lean's OFE (Option α) instance."
#rocq_ignore option_dist_Forall2 "Local Dist unfolding lemma; trivial in Lean."

@[rocq_alias option_ofe_discrete]
instance [OFEᵢ α] [OFE.Discreteᵢ α] : OFE.Discreteᵢ (Option α) where
  discrete_0 {mx my} e :=
    match mx, my with
    | none,   none   => rfl
    | none,   some _ => e.elim
    | some _, none   => e.elim
    | some _, some _ => congrArg some (discrete_0 e)

@[simp, rocq_alias dist_Some]
theorem some_dist_some [OFEᵢ α] {n} {x y : α} : (some x ≡{n}≡ some y) ↔ x ≡{n}≡ y := .rfl
@[simp] theorem not_some_dist_none [OFEᵢ α] {n} {x : α} : ¬some x ≡{n}≡ none := id
@[simp] theorem not_none_dist_some [OFEᵢ α] {n} {x : α} : ¬none ≡{n}≡ some x := id

theorem equiv_some {o : Option α} {y : α} (e : o = some y) :
    ∃ z, o = some z ∧ z = y := ⟨y, e, rfl⟩

@[rocq_alias dist_None]
theorem dist_none {n} [OFEᵢ α] {o : Option α} : o ≡{n}≡ none ↔ o = none :=
  ⟨fun h => by cases o with | none => rfl | some _ => exact h.elim, (· ▸ .rfl)⟩

@[rocq_alias dist_Some_inv_r']
theorem dist_some [OFEᵢ α] {n mx y} (h : mx ≡{n}≡ some y) :
    ∃ z : α, mx = some z ∧ y ≡{n}≡ z :=
  suffices hh : ∀ mx my y, mx ≡{n}≡ my → my = some y → ∃ t, mx = some t ∧ t ≡{n}≡ y from
    (hh mx (some y) _ h rfl).elim (fun t h => ⟨t, h.left, h.right.symm⟩)
  fun mx _ y e1 e2 =>
    match mx with
    | some t => ⟨t, rfl, (e2 ▸ e1 : some t ≡{n}≡ some y)⟩
    | none => False.elim (e2 ▸ e1 : none ≡{n}≡ some y)

/-- Data-valued form of `dist_some`, for building the witnesses of `ORA.extend`. -/
def distSome [OFEᵢ α] {n} {mx : Option α} {y : α} (h : mx ≡{n}≡ some y) :
    (z : α) ×' mx = some z ∧ y ≡{n}≡ z :=
  match mx, h with
  | some _, h => ⟨_, rfl, h.symm⟩
  | none, h => h.elim

#rocq_ignore Some_dist_inj "`Inj` instance; subsumed by `some_dist_some`."

@[rocq_alias dist_Some_inv_l]
theorem dist_some_inv_l [OFEᵢ α] {n} {mx my : Option α} {x} (h : mx ≡{n}≡ my)
    (e : mx = some x) : ∃ y, my = some y ∧ x ≡{n}≡ y := by
  subst e; exact dist_some h.symm

@[rocq_alias dist_Some_inv_r]
theorem dist_some_inv_r [OFEᵢ α] {n} {mx my : Option α} {y} (h : mx ≡{n}≡ my)
    (e : my = some y) : ∃ x, mx = some x ∧ x ≡{n}≡ y := by
  subst e; obtain ⟨z, hz, hd⟩ := dist_some h; exact ⟨z, hz, hd.symm⟩

@[rocq_alias dist_Some_inv_l']
theorem dist_some_inv_l' [OFEᵢ α] {n} {my : Option α} {x} (h : some x ≡{n}≡ my) :
    ∃ x', some x' = my ∧ x ≡{n}≡ x' :=
  let ⟨y, hy, hd⟩ := dist_some_inv_l h rfl; ⟨y, hy.symm, hd⟩

#rocq_ignore is_Some_ne "`Proper (dist n ==> iff)` setoid instance; not needed in Lean."

@[rocq_alias fmap_Some_dist]
theorem fmap_some_dist [OFEᵢ β] (f : α → β) {mx : Option α} {y : β} {n} :
    (Option.map f mx ≡{n}≡ some y) ↔ ∃ x, mx = some x ∧ y ≡{n}≡ f x := by
  refine ⟨fun h => ?_, ?_⟩
  · match mx with
    | none => exact absurd h not_none_dist_some
    | some x => exact ⟨x, rfl, (some_dist_some.mp h).symm⟩
  · rintro ⟨x, rfl, hd⟩; exact some_dist_some.mpr hd.symm

#rocq_ignore option_fmap_dist_inj "`Inj` instance for `fmap`; setoid rewriting, not needed in Lean."

@[rocq_alias Some_ne]
instance Option.some.ne [OFEᵢ α] : NonExpansiveᵢ (some : α → Option α) := ⟨fun _ _ _ => id⟩

@[rocq_alias Some_discrete]
instance Option.some_is_discrete [OFEᵢ α] {e : α} [DiscreteEᵢ e] : DiscreteEᵢ (some e) where
  discrete {y} h :=
    match y with
    | .none => absurd h not_some_dist_none
    | .some _ => congrArg some (OFE.DiscreteE.discreteᵢ h)

/-- Note: Not an instance, due to instance coherence problems. -/
theorem Option.ne_match [OFEᵢ α] {B : Type _} [OFEᵢ B]
    (f : α → B) (hf : NonExpansiveᵢ f) (g : B) :
    NonExpansiveᵢ (fun x : Option α => match x with | some a => f a | none => g) :=
  ⟨fun {n x' y'} (h : Option.Forall₂ (Distᵢ n) x' y') =>
    match x', y', h with | some _, some _, h => hf.ne h | none, none, _ => Dist.rfl⟩

@[rocq_alias None_discrete]
instance Option.none_is_discrete [OFEᵢ α] : DiscreteEᵢ (none : Option α) := by
  constructor; rintro (_|_) <;> simp

instance Option.merge_ne [OFEᵢ α] {op : α → α → α} [NonExpansive₂ᵢ op] :
    NonExpansive₂ᵢ (Option.merge op) where
  ne n x1 x2 Hx y1 y2 Hy := by
    rcases x1, x2, y1, y2 with ⟨_|_, _|_, _|_, _|_⟩ <;> simp_all
    exact NonExpansive₂.ne Hx Hy

instance Option.bind_fun_ne [OFEᵢ α] [OFEᵢ β] (f : α → Option β) [NonExpansiveᵢ f] : NonExpansiveᵢ (flip Option.bind f) where
  ne _ _ x2 Hx := match x2 with
    | some _ => (dist_some Hx).choose_spec.left ▸ (NonExpansive.ne (f := f) (dist_some Hx).choose_spec.right.symm)
    | none => (dist_none.mp Hx).symm ▸ .rfl

theorem Option.bind_dist [OFEᵢ β] {x : Option α} {f g : α → Option β} (H : ∀ x, f x ≡{n}≡ g x) :
    x.bind f ≡{n}≡ x.bind g :=
  match x with
  | some _ => H _
  | none => .rfl

theorem Option.bind_equiv {x : Option α} {f g : α → Option β} (H : ∀ x, f x = g x) :
    x.bind f = x.bind g :=
  match x with
  | some _ => H _
  | none => rfl

@[indexed]
abbrev OFEFun {α : Type _} (β : α → Type _) := ∀ a, OFEᵢ (β a)

@[rocq_alias discrete_fun_ofe_mixin]
instance [OFEFunᵢ (β : α → _)] : OFEᵢ ((x : α) → β x) where
  dist n f g := ∀ x, f x ≡{n}≡ g x
  dist_eqv := {
    refl _ _ := dist_eqv.refl _
    symm h _ := dist_eqv.symm (h _)
    trans h1 h2 _ := dist_eqv.trans (h1 _) (h2 _)
  }
  eq_dist' {_ _} := funext_iff.trans <| (forall_congr' fun _ => OFE.eq_distᵢ).trans forall_comm
  dist_lt h1 h2 _ := dist_lt (h1 _) h2
#rocq_ignore discrete_funO "Use a function type"
#rocq_ignore discrete_fun "Lean uses `(x : α) → β x` directly with `OFEFun`."
#rocq_ignore discrete_fun_equiv "Local Equiv instance; folded into Lean's instance."
#rocq_ignore discrete_fun_dist "Local Dist instance; folded into Lean's instance."

@[rocq_alias ofe_mor_ofe_mixin]
instance [OFEᵢ α] [OFEᵢ β] : OFEᵢ (α -n> β) where
  dist n f g := f.f ≡{n}≡ g.f
  dist_eqv := {
    refl _ := dist_eqv.refl _
    symm h := dist_eqv.symm h
    trans h1 h2 := dist_eqv.trans h1 h2
  }
  eq_dist' {_ _} := Hom.ext_iff.trans OFE.eq_distᵢ
  dist_lt := dist_lt
#rocq_ignore ofe_morO "Use Hom type"
#rocq_ignore ofe_mor_equiv "Inlined in OFE (α -n> β) instance"
#rocq_ignore ofe_mor_dist "Inlined in OFE (α -n> β) instance"
#rocq_ignore ofe_mor_chain "Inlined in IsCOFE instance"

@[rocq_alias ofe_mor_car_ne]
instance ofe_mor_car_ne [OFEᵢ α] [OFEᵢ β] :
    NonExpansive₂ᵢ (fun (f : α -n> β) (x : α) => f x) where
  ne _ _ _ hf _ _ hx := dist_eqv.trans (hf _) (NonExpansive.ne hx)

@[rocq_alias ofe_mor_car_proper]
theorem ofe_mor_car_proper [OFEᵢ α] [OFEᵢ β] ⦃f g : α -n> β⦄ (hfg : f = g)
    ⦃x y : α⦄ (hxy : x = y) : f x = g y := by
  subst hfg; subst hxy; rfl

@[rocq_alias ofe_mor_inhabited]
instance [OFEᵢ α] [OFEᵢ β] [Inhabited β] : Inhabited (α -n> β) where
  default := { f := Function.const α default, ne := const_ne }

instance [OFEᵢ α] [OFEᵢ β] : OFEᵢ (α -c> β) where
  dist n f g := f.toHom ≡{n}≡ g.toHom
  dist_eqv := {
    refl _ := dist_eqv.refl _
    symm h := dist_eqv.symm h
    trans h1 h2 := dist_eqv.trans h1 h2
  }
  eq_dist' {_ _} := ContractiveHom.ext_iff.trans OFE.eq_distᵢ
  dist_lt := dist_lt

/-- Evaluation at a fixed argument is non-expansive for the pointwise OFE.
Instance priority is lowered for performance. -/
@[indexed, instance 100]
theorem apply_ne [OFEFunᵢ (β : α → _)] (x : α) :
    NonExpansiveᵢ (fun f : (x : α) → β x => f x) where
  ne _ _ _ H := H x

@[indexed]
def applyHom [OFEFunᵢ (β : α → _)] (x : α) : ((x : α) → β x) -n> β x where
  f f := f x
  ne := OFE.apply_neᵢ x

@[indexed]
def applyNe [OFEᵢ α] [OFEᵢ β] (x : α) : (α -n> β) -n> β where
  f f := f x
  ne.1 _ _ _ H := H x

instance [OFEᵢ α] [OFEᵢ β] : NonExpansiveᵢ (OFE.applyNeᵢ (α := α) (β := β)) where
  ne _ _ _ H f := f.ne.1 H

@[indexed, rocq_alias discrete_funO_map]
def mapCodHom [OFEFunᵢ (β₁ : α → _)] [OFEFunᵢ β₂]
    (F : ∀ x, β₁ x -n> β₂ x) : ((x : α) → β₁ x) -n> ((x : α) → β₂ x) where
  f f x := F x (f x)
  ne.1 _ _ _ H x := (F x).ne.1 (H x)
#rocq_ignore discrete_fun_map "Underlying map of mapCodHom"
#rocq_ignore discrete_fun_map_ext "Use ext"
#rocq_ignore discrete_fun_map_ne "Implicit in type of mapCodHom"
#rocq_ignore discrete_fun_map_ne "Implicit in type of mapCodHom"
#rocq_ignore discrete_funO_map_ne "Implicit in type of mapCodHom"

@[rocq_alias discrete_fun_map_id]
theorem mapCodHom_id [OFEFunᵢ (β : α → _)] (g : (x : α) → β x) :
    OFE.mapCodHomᵢ (fun _ => Hom.id) g = g := rfl

@[rocq_alias discrete_fun_map_compose]
theorem mapCodHom_compose [OFEFunᵢ (β₁ : α → _)] [OFEFunᵢ β₂] [OFEFunᵢ β₃]
    (f₁ : ∀ x, β₁ x -n> β₂ x) (f₂ : ∀ x, β₂ x -n> β₃ x) (g : (x : α) → β₁ x) :
  OFE.mapCodHomᵢ (fun x => (f₂ x).comp (f₁ x)) g = OFE.mapCodHomᵢ f₂ (OFE.mapCodHomᵢ f₁ g) := rfl

open Classical in
@[rocq_alias discrete_fun_lookup_discrete]
instance mapCod_lookup_discrete [OFEFunᵢ (β : α → _)]
    (f : (x : α) → β x) (x : α) [hf : DiscreteEᵢ f] : DiscreteEᵢ (f x) where
  discrete {y} h := by
    let g : (x' : α) → β x' := fun x' => if e : x = x' then e ▸ y else f x'
    have hgx : g x = y := dite_eq_left rfl
    have hne : ∀ x', x ≠ x' → g x' = f x' := fun x' e => dite_eq_right e
    refine (congrFun (hf.discrete fun x' => ?_) x).trans hgx
    by_cases e : x = x'
    · grind
    · exact .of_eq (hne x' e).symm

@[rocq_alias prod_ofe_mixin]
instance [OFEᵢ α] [OFEᵢ β] : OFEᵢ (α × β) where
  dist n a b := a.1 ≡{n}≡ b.1 ∧ a.2 ≡{n}≡ b.2
  dist_eqv := {
    refl _ := ⟨dist_eqv.refl _, dist_eqv.refl _⟩
    symm h := ⟨dist_eqv.symm h.1, dist_eqv.symm h.2⟩
    trans h1 h2 := ⟨dist_eqv.trans h1.1 h2.1, dist_eqv.trans h1.2 h2.2⟩
  }
  eq_dist' {_ _} := Prod.ext_iff.trans <| (and_congr OFE.eq_distᵢ OFE.eq_distᵢ).trans forall_and.symm
  dist_lt h1 h2 := ⟨dist_lt h1.1 h2, dist_lt h1.2 h2⟩
#rocq_ignore prodO "Use product type"
#rocq_ignore prod_dist "Implicit in Prod OFE"

theorem dist_fst {n} [OFEᵢ α] [OFEᵢ β] {x y : α × β} (h : x ≡{n}≡ y) : x.fst ≡{n}≡ y.fst := h.left
theorem dist_snd {n} [OFEᵢ α] [OFEᵢ β] {x y : α × β} (h : x ≡{n}≡ y) : x.snd ≡{n}≡ y.snd := h.right

@[rocq_alias pair_dist]
theorem dist_prod_ext {n} [OFEᵢ α] [OFEᵢ β] {x₁ x₂ : α} {y₁ y₂ : β}
    (ex : x₁ ≡{n}≡ x₂) (ey : y₁ ≡{n}≡ y₂) : (x₁, y₁) ≡{n}≡ (x₂, y₂) := ⟨ex, ey⟩

@[rocq_alias pair_ne]
instance Prod.mk_ne [OFEᵢ α] [OFEᵢ β] : NonExpansive₂ᵢ (Prod.mk (α := α) (β := β)) where
  ne _ _ _ hx _ _ hy := dist_prod_ext hx hy

#rocq_ignore pair_dist_inj "`Inj2` instance; subsumed by the definitional `pair_dist`."

/-- Note: Not an instance, due to instance coherence problems. -/
theorem prod_mk_ne_left [OFEᵢ α] [OFEᵢ β] (b : β) : NonExpansiveᵢ (β := α × β) (·, b) :=
  ⟨fun {_ _ _} h => dist_prod_ext h Dist.rfl⟩

/-- Note: Not an instance, due to instance coherence problems. -/
theorem prod_mk_ne_right [OFEᵢ α] [OFEᵢ β] (a : α) : NonExpansiveᵢ (β := α × β) (a, ·) :=
  ⟨fun {_ _ _} h => dist_prod_ext Dist.rfl h⟩

@[rocq_alias fst_ne]
instance [OFEᵢ α] [OFEᵢ β] : NonExpansiveᵢ (Prod.fst (α := α) (β := β)) :=
  ⟨fun {_ _ _} h => dist_fst h⟩

@[rocq_alias snd_ne]
instance [OFEᵢ α] [OFEᵢ β] : NonExpansiveᵢ (Prod.snd (α := α) (β := β)) :=
  ⟨fun {_ _ _} h => dist_snd h⟩

/-- Note: Not an instance, due to instance coherence problems. -/
@[rocq_alias uncurry_ne]
theorem NonExpansive₂.uncurry [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] {f : α → β → γ} (hf : NonExpansive₂ᵢ f) :
    NonExpansiveᵢ (Function.uncurry f) :=
  ⟨fun {_ _ _} (h : _ ∧ _) => hf.ne h.1 h.2⟩

/-- Note: Not an instance, due to instance coherence problems. -/
@[rocq_alias curry_ne]
theorem NonExpansive.curry [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] {f : α × β → γ} (hf : NonExpansiveᵢ f) :
    NonExpansive₂ᵢ (Function.curry f) :=
  ⟨fun _ _ _ hx _ _ hy => hf.ne ⟨hx, hy⟩⟩

/-- Note: Not an instance, due to instance coherence problems. -/
@[rocq_alias curry3_ne]
theorem NonExpansive.curry₃ [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] [OFEᵢ δ] {f : α × β × γ → δ}
    (hf : NonExpansiveᵢ f) : NonExpansive₃ᵢ fun a b c => f (a, b, c) :=
  ⟨fun _ _ _ hx _ _ hy _ _ hz => hf.ne ⟨hx, hy, hz⟩⟩

/-- Note: Not an instance, due to instance coherence problems. -/
@[rocq_alias uncurry3_ne]
theorem NonExpansive₃.uncurry [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] [OFEᵢ δ] {f : α → β → γ → δ}
    (hf : NonExpansive₃ᵢ f) : NonExpansiveᵢ fun p : α × β × γ => f p.1 p.2.1 p.2.2 :=
  ⟨fun {_ _ _} (h : _ ∧ _ ∧ _) => hf.ne h.1 h.2.1 h.2.2⟩

/-- Note: Not an instance, due to instance coherence problems. -/
@[rocq_alias curry4_ne]
theorem NonExpansive.curry₄ [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] [OFEᵢ δ] [OFEᵢ ε] {f : α × β × γ × δ → ε}
    (hf : NonExpansiveᵢ f) : NonExpansive₄ᵢ fun a b c d => f (a, b, c, d) :=
  ⟨fun _ _ _ hx _ _ hy _ _ hz _ _ hw => hf.ne ⟨hx, hy, hz, hw⟩⟩

/-- Note: Not an instance, due to instance coherence problems. -/
@[rocq_alias uncurry4_ne]
theorem NonExpansive₄.uncurry [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] [OFEᵢ δ] [OFEᵢ ε] {f : α → β → γ → δ → ε}
    (hf : NonExpansive₄ᵢ f) : NonExpansiveᵢ fun p : α × β × γ × δ => f p.1 p.2.1 p.2.2.1 p.2.2.2 :=
  ⟨fun {_ _ _} (h : _ ∧ _ ∧ _ ∧ _) => hf.ne h.1 h.2.1 h.2.2.1 h.2.2.2⟩

@[rocq_alias prod_discrete]
instance prod.is_discrete [OFEᵢ α] [OFEᵢ β] {a : α} {b : β} [DiscreteEᵢ a] [DiscreteEᵢ b] :
    DiscreteEᵢ (a, b) := by
  constructor
  intro y H; exact Prod.ext (OFE.DiscreteE.discreteᵢ H.1) (OFE.DiscreteE.discreteᵢ H.2)

@[rocq_alias prod_ofe_discrete]
instance instDiscreteProd [OFEᵢ α] [OFEᵢ β] [Discreteᵢ α] [Discreteᵢ β] : Discreteᵢ (α × β) where
  discrete_0 H := Prod.ext (discrete_0 H.1) (discrete_0 H.2)

section sum

variable [OFEᵢ α] [OFEᵢ β]

@[rocq_alias sum_ofe_mixin]
instance : OFEᵢ (α ⊕ β) where
  dist n
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
  eq_dist' {a b} := by
    match a, b with
    | .inl _, .inl _ => rw [Sum.inl.injEq]; exact OFE.eq_distᵢ
    | .inr _, .inr _ => rw [Sum.inr.injEq]; exact OFE.eq_distᵢ
    | .inl _, .inr _ => exact ⟨fun h => (nomatch h), fun x => (x 0).elim⟩
    | .inr _, .inl _ => exact ⟨fun h => (nomatch h), fun x => (x 0).elim⟩
  dist_lt {_ a b} := match a, b with
    | .inl _, .inl _ => dist_lt
    | .inr _, .inr _ => dist_lt
    | .inl _, .inr _ => (False.elim ·)
    | .inr _, .inl _ => (False.elim ·)
#rocq_ignore sumO "Use sum type"
#rocq_ignore sum_dist "Inlined in OFE (α ⊕ β) instance"

theorem dist_inl (h : x ≡{n}≡ y) : (.inl x : α ⊕ β) ≡{n}≡ .inl y := h
theorem dist_inr {x y : β} (h : x ≡{n}≡ y) : (.inr x : α ⊕ β) ≡{n}≡ .inr y := h
@[rocq_alias inl_ne_inj]
theorem dist_ext_left {x y : α} (h : (.inl x : α ⊕ β) ≡{n}≡ .inl y) : x ≡{n}≡ y := h
@[rocq_alias inr_ne_inj]
theorem dist_ext_right {x y : β} (h : (.inr x : α ⊕ β) ≡{n}≡ .inr y) : x ≡{n}≡ y := h
@[simp, grind =] theorem inl_dist_inl {x y : α} : (.inl x : α ⊕ β) ≡{n}≡ .inl y ↔ x ≡{n}≡ y := .rfl
@[simp, grind =] theorem inr_dist_inr {x y : β} : (.inr x : α ⊕ β) ≡{n}≡ .inr y ↔ x ≡{n}≡ y := .rfl
@[simp, grind .] theorem not_inl_dist_inr {x : α} {y : β} : ¬(.inl x : α ⊕ β) ≡{n}≡ .inr y := id
@[simp, grind .] theorem not_inr_dist_inl {x : β} {y : α} : ¬(.inr x : α ⊕ β) ≡{n}≡ .inl y := id

@[rocq_alias inl_ne]
instance instNonExpansiveInl : NonExpansiveᵢ (Sum.inl (α := α) (β := β)) where
  ne {_ _ _} H := dist_inl H

@[rocq_alias inr_ne]
instance instNonExpansiveInr : NonExpansiveᵢ (Sum.inr (α := α) (β := β)) where
  ne {_ _ _} H := dist_inr H

instance instNonExpansiveElim [OFEᵢ γ] {f₁ : α → γ} {f₂ : β → γ} [NonExpansiveᵢ f₁] [NonExpansiveᵢ f₂] :
    NonExpansiveᵢ (Sum.elim f₁ f₂) where
  ne {_ x y} := match x, y with
    | .inl _, .inl _ => (NonExpansive.ne (f := f₁) <| dist_ext_left ·)
    | .inr _, .inr _ => (NonExpansive.ne (f := f₂) <| dist_ext_right ·)
    | .inl _, .inr _ => (False.elim ·)
    | .inr _, .inl _ => (False.elim ·)

@[rocq_alias inl_discrete]
theorem discreteE_inl {a : α} (Ha : DiscreteEᵢ a) : DiscreteEᵢ (.inl a : α ⊕ β) := by
  constructor
  rintro (_|_) H
  · exact congrArg Sum.inl (Ha.discrete H)
  · exact H.elim

@[rocq_alias inr_discrete]
theorem discreteE_inr {a : β} (Ha : DiscreteEᵢ a) : DiscreteEᵢ (.inr a : α ⊕ β) := by
  constructor
  rintro (_|_) H
  · exact H.elim
  · exact congrArg Sum.inr (Ha.discrete H)

@[rocq_alias sum_ofe_discrete]
instance instDiscreteSum [Discreteᵢ α] [Discreteᵢ β] : Discreteᵢ (α ⊕ β) where
  discrete_0 {x y} := match x, y with
    | .inl _, .inl _ => (congrArg Sum.inl <| discrete_0 (α := α) <| dist_ext_left ·)
    | .inr _, .inr _ => (congrArg Sum.inr <| discrete_0 (α := β) <| dist_ext_right ·)
    | .inl _, .inr _ => (False.elim ·)
    | .inr _, .inl _ => (False.elim ·)

end sum

@[rocq_alias sig_ofe_mixin]
instance [OFEᵢ α] (P : α → Prop) : OFEᵢ (Subtype P) where
  dist n x y := x.val ≡{n}≡ y.val
  dist_eqv := ⟨fun _ => .rfl, Dist.symm, Dist.trans⟩
  eq_dist' {_ _} := Subtype.ext_iff.trans OFE.eq_distᵢ
  dist_lt := dist_lt
#rocq_ignore sigO "Use subtype"
#rocq_ignore sig_equiv "Local Equiv instance; folded into Lean's OFE (Subtype P) instance."
#rocq_ignore sig_dist "Local Dist instance; folded into Lean's OFE (Subtype P) instance."
#rocq_ignore sig_equiv_def "Trivial unfolding lemma; definitional in Lean."
#rocq_ignore sig_dist_def "Trivial unfolding lemma; definitional in Lean."

@[rocq_alias sig_discrete]
instance [OFEᵢ α] (P : α → Prop) (x : Subtype P) [DiscreteEᵢ x.val] : DiscreteEᵢ x where
  discrete h := Subtype.ext <| OFE.DiscreteE.discreteᵢ h

@[rocq_alias sig_ofe_discrete]
instance [OFEᵢ α] [Discreteᵢ α] (P : α → Prop) : Discreteᵢ (Subtype P) where
  discrete_0 h := Subtype.ext <| Discrete.discrete_0 h

@[rocq_alias exist_ne]
theorem exist_ne [OFEᵢ α] {P : α → Prop} {n} {a1 a2 : α} (H1 : P a1) (H2 : P a2)
    (h : a1 ≡{n}≡ a2) : (⟨a1, H1⟩ : Subtype P) ≡{n}≡ ⟨a2, H2⟩ := h

@[rocq_alias proj1_sig_ne]
instance [OFEᵢ α] (P : α → Prop) : NonExpansiveᵢ (Subtype.val : Subtype P → α) where
  ne {_ _ _} := id

instance Hom.ofSubtype_ne [OFEᵢ α] [OFEᵢ β] : NonExpansiveᵢ (OFE.Hom.ofSubtypeᵢ (α := α) (β := β)) :=
  ⟨fun {_ _ _} h => h⟩

/-- Extract the underlying subtype from a `Hom`. -/
@[indexed]
def Hom.toSubtype [OFEᵢ α] [OFEᵢ β] (f : α -n> β) : { f : α → β // NonExpansiveᵢ f } :=
  ⟨f.f, f.ne⟩

instance Hom.toSubtype_ne [OFEᵢ α] [OFEᵢ β] : NonExpansiveᵢ (OFE.Hom.toSubtypeᵢ (α := α) (β := β)) :=
  ⟨fun {_ _ _} h => h⟩

@[rocq_alias sigT_ofe_mixin]
instance instOFESigma (P : α → Type _) [∀ x, OFEᵢ (P x)] : OFEᵢ (Sigma P) where
  dist n x y := ∃ heq : x.fst = y.fst, heq ▸ x.snd ≡{n}≡ y.snd
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
  eq_dist' {x y} := by
    refine ⟨fun h n => h ▸ ⟨rfl, .rfl⟩, fun h => ?_⟩
    obtain ⟨heq, _⟩ := h 0
    obtain ⟨xf, xs⟩ := x; obtain ⟨yf, ys⟩ := y
    simp only at heq; subst heq
    exact congrArg _ (OFE.eq_of_distᵢ fun n => (h n).2)
  dist_lt {_ x y} := match x, y with
    | ⟨x, xH⟩, ⟨y, yH⟩ => fun
      | ⟨heq, H⟩ => fun hlt => ⟨heq, by simp only at heq; subst heq; exact dist_lt H hlt⟩
#rocq_ignore sigTO "Use sigma type"
#rocq_ignore sigT_dist "Local Dist instance; folded into Lean's OFE (Sigma P) instance."
#rocq_ignore sigT_equiv "Local Equiv instance; folded into Lean's OFE (Sigma P) instance."

@[rocq_alias sigT_discrete]
instance instDiscreteESigma {P : α → Type _} [∀ x, OFEᵢ (P x)] {x : Sigma P} [DiscreteEᵢ x.snd] :
    DiscreteEᵢ x where
  discrete {y} := by
    rcases x, y with ⟨⟨x, xH⟩, ⟨y, yH⟩⟩; rintro ⟨heq, H⟩
    simp only at heq; subst heq
    exact congrArg _ (OFE.DiscreteE.discreteᵢ H)

@[rocq_alias sigT_ofe_discrete]
instance instDiscreteSigma {P : α → Type _} [∀ x, OFEᵢ (P x)] [∀ x, Discreteᵢ (P x)] :
    Discreteᵢ (Sigma P) where
  discrete_0 {x y} H := match x, y, H with
    | ⟨x, xH⟩, ⟨y, yH⟩, ⟨heq, H⟩ => by simp only at heq; subst heq; exact congrArg _ (discrete_0 H)

@[rocq_alias sigT_equiv_eq_alt]
theorem Sigma.equiv_eq_alt {P : α → Type _} {x1 x2 : Sigma P} :
    x1 = x2 ↔ ∃ heq : x1.fst = x2.fst, heq ▸ x1.snd = x2.snd := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨heq, h⟩ => ?_⟩
  obtain ⟨x1f, x1s⟩ := x1; obtain ⟨x2f, x2s⟩ := x2
  simp only at heq; subst heq; simp only at h; subst h; rfl

@[rocq_alias sigT_equiv_eq]
theorem Sigma.equiv_eq {P : α → Type _} [∀ x, OFEᵢ (P x)] {x1 x2 : Sigma P} :
    x1 = x2 ↔ ∀ n, x1 ≡{n}≡ x2 := OFE.eq_distᵢ

@[rocq_alias sigT_dist_eq]
theorem Sigma.dist_eq {P : α → Type _} [∀ x, OFEᵢ (P x)] {n} {x1 x2 : Sigma P} :
    (x1 ≡{n}≡ x2) ↔ ∃ heq : x1.fst = x2.fst, heq ▸ x1.snd ≡{n}≡ x2.snd := Iff.rfl

@[rocq_alias sigT_dist_proj1]
theorem Sigma.dist_proj1 {P : α → Type _} [∀ x, OFEᵢ (P x)] {n} {x y : Sigma P}
    (h : x ≡{n}≡ y) : x.fst = y.fst := h.1

@[rocq_alias sigT_equiv_proj1]
theorem Sigma.equiv_proj1 {P : α → Type _} {x y : Sigma P}
    (h : x = y) : x.fst = y.fst := congrArg Sigma.fst h

@[rocq_alias projT1_ne]
instance Sigma.fst_ne {P : α → Type _} [OFEᵢ α] [∀ x, OFEᵢ (P x)] :
    NonExpansiveᵢ (Sigma.fst : Sigma P → α) where
  ne {_ _ _} h := Dist.of_eq h.1
#rocq_ignore projT1_proper "Derived from nonexpansivity."

/-- The first components of `n`-equivalent dependent pairs are equal.

Split out of `Sigma.dist_snd` so that the projection happens in a body rather than in a statement:
in a statement the `OFE (Sigma P)` instance argument is still an unsolved metavariable, so `h`'s
type cannot be reduced to the `∃ heq, ..` of `instOFESigma` to project out of. -/
theorem Sigma.dist_fst {P : α → Type _} [∀ x, OFEᵢ (P x)] {n} {x y : Sigma P}
    (h : x ≡{n}≡ y) : x.fst = y.fst := h.1

@[rocq_alias projT2_ne]
theorem Sigma.dist_snd {P : α → Type _} [∀ x, OFEᵢ (P x)] {n} {x y : Sigma P}
    (h : x ≡{n}≡ y) : Sigma.dist_fst h ▸ x.snd ≡{n}≡ y.snd := h.2

@[rocq_alias projT2_proper]
theorem Sigma.equiv_snd {P : α → Type _} {x y : Sigma P}
    (h : x = y) : congrArg Sigma.fst h ▸ x.snd = y.snd := by
  subst h; rfl

@[rocq_alias existT_ne]
theorem Sigma.mk_dist {P : α → Type _} [∀ x, OFEᵢ (P x)] {n} {i1 i2 : α} {v1 : P i1} {v2 : P i2}
    (heq : i1 = i2) (h : heq ▸ v1 ≡{n}≡ v2) : Sigma.mk i1 v1 ≡{n}≡ Sigma.mk i2 v2 :=
  ⟨heq, h⟩

@[rocq_alias existT_proper]
theorem Sigma.mk_equiv {P : α → Type _} {i1 i2 : α} {v1 : P i1} {v2 : P i2}
    (heq : i1 = i2) (h : heq ▸ v1 = v2) : Sigma.mk i1 v1 = Sigma.mk i2 v2 := by
  subst heq; subst h; rfl

@[rocq_alias existT_ne_2]
instance Sigma.mk_ne {P : α → Type _} [∀ x, OFEᵢ (P x)] (a : α) :
    NonExpansiveᵢ (Sigma.mk a : P a → Sigma P) where
  ne {_ _ _} h := ⟨rfl, h⟩
#rocq_ignore existT_proper_2 "Derived from nonexpansivity (`existT_ne_2`); Leibniz."

/-- An isomorphism between two OFEs is a pair of morphisms whose composition is equivalent to the
identity morphism. -/
@[indexed, ext, rocq_alias ofe_iso] structure Iso (α β : Type _) [OFEᵢ α] [OFEᵢ β] where
  hom : α -n> β
  inv : β -n> α
  hom_inv : hom (inv x) = x
  inv_hom : inv (hom x) = x
#rocq_ignore ofe_isoO "Use Iso"
#rocq_ignore ofe_iso_1_ne "Implicit from the type of `Iso.Hom`"
#rocq_ignore ofe_iso_2_ne "Implicit from the type of `Iso.Inv`"

attribute [simp] Iso.hom_inv Iso.inv_hom

instance [OFEᵢ α] [OFEᵢ β] : CoeFun (Isoᵢ α β) (fun _ => α -n> β) := ⟨Iso.hom⟩
instance [OFEᵢ α] [OFEᵢ β] (iso : Isoᵢ α β) : NonExpansiveᵢ iso.hom := iso.hom.ne
instance [OFEᵢ α] [OFEᵢ β] (iso : Isoᵢ α β) : NonExpansiveᵢ iso.inv := iso.inv.ne

@[simp] theorem Iso.hom_inv_dist [OFEᵢ α] [OFEᵢ β] (iso : Isoᵢ α β) {n} {x} :
    iso.hom (iso.inv x) ≡{n}≡ x :=
  (Iso.hom_inv iso).dist

@[simp] theorem Iso.inv_hom_dist [OFEᵢ α] [OFEᵢ β] (iso : Isoᵢ α β) {n} {x} :
    iso.inv (iso.hom x) ≡{n}≡ x :=
  (Iso.inv_hom iso).dist

/-- OFE isomorphisms preserve equivalence. -/
theorem Iso.hom_eqv [OFEᵢ α] [OFEᵢ β] (iso : Isoᵢ α β) ⦃x y⦄ :
    x = y ↔ iso.hom x = iso.hom y :=
  ⟨fun h => h ▸ rfl,
   fun h => iso.inv_hom.symm.trans ((congrArg iso.inv h).trans iso.inv_hom)⟩

/-- The inverse of an OFE isomorphism preserves equivalence. -/
theorem Iso.inv_eqv [OFEᵢ α] [OFEᵢ β] (iso : Isoᵢ α β) ⦃x y⦄ :
    x = y ↔ iso.inv x = iso.inv y :=
  ⟨fun h => h ▸ rfl,
   fun h => iso.hom_inv.symm.trans ((congrArg iso.hom h).trans iso.hom_inv)⟩

/-- OFE isomorphisms preserve `n`-equivalence. -/
theorem Iso.hom_dist [OFEᵢ α] [OFEᵢ β] (iso : Isoᵢ α β) {n} ⦃x y⦄ :
    x ≡{n}≡ y ↔ iso.hom x ≡{n}≡ iso.hom y :=
  ⟨fun h => NonExpansive.ne h, fun h => Dist.trans (Dist.symm iso.inv_hom_dist) <|
    Dist.trans (NonExpansive.ne h) (iso.inv_hom_dist)⟩

/-- The inverse of an OFE isomorphism preserves `n`-equivalence. -/
theorem Iso.inv_dist [OFEᵢ α] [OFEᵢ β] (iso : Isoᵢ α β) {n} ⦃x y⦄ :
    x ≡{n}≡ y ↔ iso.inv x ≡{n}≡ iso.inv y :=
  ⟨fun h => NonExpansive.ne h, fun h => Dist.trans (Dist.symm iso.hom_inv_dist) <|
    Dist.trans (NonExpansive.ne h) (iso.hom_inv_dist)⟩

/-- The identity OFE isomorphism -/
@[rocq_alias iso_ofe_refl]
def Iso.id [OFEᵢ α] : Isoᵢ α α where
  hom := Hom.id
  inv := Hom.id
  hom_inv := by intro x; simp
  inv_hom := by intro x; simp

@[simp] theorem Iso.id_apply [OFEᵢ α] {x} : ((Iso.id : Isoᵢ α α) : α -n> α) x = x := rfl

/-- The inverse of an OFE isomorphism -/
@[rocq_alias iso_ofe_sym]
def Iso.symm [OFEᵢ α] [OFEᵢ β] (iso : Isoᵢ α β) : Isoᵢ β α where
  hom := iso.inv
  inv := iso.hom
  hom_inv := by intro x; simp
  inv_hom := by intro x; simp
#rocq_ignore iso_ofe_sym_ne "Implicit in the type of Iso.symm.hom"
#rocq_ignore iso_ofe_trans_ne "Implicit in the type of Iso.symm.inv"

/-- Composition of OFE isomorphisms -/
@[rocq_alias iso_ofe_trans]
def Iso.comp [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] (iso1 : Isoᵢ β γ) (iso2 : Isoᵢ α β) : Isoᵢ α γ where
  hom := iso1.hom.comp iso2.hom
  inv := iso2.inv.comp iso1.inv
  hom_inv := by intro x; simp
  inv_hom := by intro x; simp

end OFE

/-- A chain in an OFE is a `Nat`-indexed sequence of elements that is upward-closed in terms of
`n`-equivalence. -/
@[indexed, rocq_alias chain] structure Chain (α : Type _) [OFEᵢ α] where
  chain : SI → α
  cauchy {n i} : n ≤ i → chain i ≡{n}≡ chain n

instance [OFEᵢ α] : CoeFun (Chainᵢ α) (fun _ => SI → α) := ⟨Chain.chain⟩

namespace Chain

/-- The constant chain. -/
@[indexed, rocq_alias chain_const]
def const [OFEᵢ α] (a : α) : Chainᵢ α where
  chain := fun _ => a
  cauchy _ := OFE.Dist.rfl

@[simp] theorem const_apply [OFEᵢ α] {a : α} {n} : Chain.constᵢ a n = a := rfl

/-- Mapping a chain through a non-expansive function. -/
@[rocq_alias chain_map]
def map [OFEᵢ α] [OFEᵢ β] (f : α -n> β) (c : Chainᵢ α) : Chainᵢ β where
  chain n := f (c n)
  cauchy h := f.ne.1 (c.cauchy h)

@[simp] theorem map_apply [OFEᵢ α] [OFEᵢ β] {f : α -n> β} {c : Chainᵢ α} {n} :
    map f c n = f (c n) := rfl

@[simp] theorem map_id [OFEᵢ α] {c : Chainᵢ α} : map (Hom.id : α -n> α) c = c := by
  simp [map]

theorem map_comp [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] {f : α -n> β} {g : β -n> γ} {c : Chainᵢ α} :
    map (g.comp f) c = map g (map f c) := by
  simp [map]

/-- If a chain of Option is ever none, is the constant none chain. -/
theorem chain_none_const [OFEᵢ V] {c : Chainᵢ (Option V)} (H : c n = none) :
    c = Chain.constᵢ none := by
  rcases c with ⟨c, Hc⟩
  congr 1; refine funext (fun k => ?_)
  rcases (SIdx.le_total : n ≤ k ∨ k ≤ n) with (Hnk|Hnk)
  · suffices c k ≡{n}≡ c n by cases _ : c k <;> simp_all
    exact Hc Hnk
  · suffices c k ≡{k}≡ c n by cases _ : c k <;> simp_all
    exact (Hc Hnk).symm

/-- If a chain of Option is ever some, it is the lift a chain by some. -/
theorem chain_option_some [OFEᵢ V] {c : Chainᵢ (Option V)} (H : c n = some v) :
    ∃ c' : Chainᵢ V, c = Chain.map ⟨some, OFE.Option.some.ne⟩ c' := by
  have HVc (k) : ∃ v', c k = some v' := by
    rcases h : c.chain k with (_|v')
    · simp [chain_none_const h] at H
    · exists v'
  let c' : Chainᵢ V :=
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

end Chain

@[indexed, rocq_alias bchain]
structure BChain (α : Type _) [OFEᵢ α] (n : SI) where
  bchain m : m < n → α
  bcauchy {m} {p} (hm : m < n) (hp : p < n) (h : m ≤ p) : bchain p hp ≡{m}≡ bchain m hm

namespace BChain
variable [OFEᵢ α] [OFEᵢ β]

@[rocq_alias bchain_map]
def map (f : α -n> β) {n} (c : BChainᵢ α n) : BChainᵢ β n where
  bchain m hm := f <| c.bchain m hm
  bcauchy hm hp h := f.ne.ne <| c.bcauchy hm hp h

@[indexed, rocq_alias bchain_const]
def const (a : α) (n) : BChainᵢ α n where
  bchain _ _ := a
  bcauchy _ _ _ := .rfl

@[rocq_alias bchain_le]
def le {n} (c : BChainᵢ α n) {m} (hm : m ≤ n) : BChainᵢ α m where
  bchain m' hm' := c.bchain m' (SIdx.lt_le_trans hm' hm)
  bcauchy _ _ h := c.bcauchy _ _ h

@[simp] theorem map_apply {f : α -n> β} {n} {c : BChainᵢ α n} {m} {hm : m < n} :
    (map f c).bchain m hm = f (c.bchain m hm) := rfl

@[simp] theorem const_apply {a : α} {n m} {hm : m < n} :
    (BChain.constᵢ a n).bchain m hm = a := rfl

end BChain

/-- Complete ordered family of equivalences -/
@[indexed, rocq_alias Cofe]
class IsCOFE (SI : stepindex (Type _)) (α : Type _) [SIdx SI] [OFEᵢ α] where
  compl : Chainᵢ α → α
  conv_compl {c : Chainᵢ α} : compl c ≡{n}≡ c n
  lbcompl {n} : SIdx.Limit n → BChainᵢ α n → α
  conv_lbcompl {n} (Hn : SIdx.Limit n) (c : BChainᵢ α n) {m} (hm : m < n) :
    lbcompl Hn c ≡{m}≡ c.bchain m hm
  lbcompl_ne {n} (hn : SIdx.Limit n) (c1 c2 : BChainᵢ α n) {m} :
    (∀ p (Hp : p < n), c1.bchain p Hp ≡{m}≡ c2.bchain p Hp) →
    lbcompl hn c1 ≡{m}≡ lbcompl hn c2

variable (SI) in
/-- Complete ordered family of equivalences -/
@[indexed]
class abbrev COFE (α : Type _) := OFEᵢ α, IsCOFEᵢ α

namespace COFE
export IsCOFE (compl conv_compl)

@[rocq_alias conv_compl_le]
theorem conv_compl' [COFEᵢ α] {c : Chainᵢ α} {n i} (h : n ≤ i) : compl c ≡{n}≡ c i :=
  conv_compl.trans (c.cauchy h).symm

/-- Chain maps commute with completion. -/
@[rocq_alias compl_chain_map]
theorem compl_map [COFEᵢ α] [COFEᵢ β] (f : α -n> β) (c : Chainᵢ α) :
    compl (Chain.map f c) = f (compl c) := by
  refine OFE.eq_of_distᵢ (fun n => ?_)
  exact conv_compl.trans (NonExpansive.ne (Dist.symm conv_compl))

/-- Constant chains complete to their constant value -/
@[simp, rocq_alias compl_chain_const]
theorem compl_const [COFEᵢ α] (a : α) : compl (Chain.constᵢ a) = a :=
  OFE.eq_of_distᵢ (fun _ => conv_compl)

/-- Completion of discrete COFEs is the constant value. -/
@[simp] theorem discrete_cofe_compl [COFEᵢ α] [OFE.Discreteᵢ α] (c : Chainᵢ α) : compl c = c 0 :=
  Discrete.discrete_0 conv_compl

/-- The discrete COFE obtained from an equality relation `Eq` -/
@[reducible, rocq_alias discrete_cofe]
def ofDiscrete (α : Type _) : COFEᵢ α :=
  letI : OFEᵢ α := OFE.ofDiscrete α
  {
    compl c := c 0
    conv_compl {_ c} := (c.cauchy SIdx.le_0_l).symm
    lbcompl hn c := c.bchain 0 hn.limit_lt_0
    conv_lbcompl hn c _ hm := (c.bcauchy hn.limit_lt_0 hm SIdx.le_0_l).symm
    lbcompl_ne hn _ _ _ hc := hc 0 hn.limit_lt_0
  }

instance [COFEᵢ α] : COFEᵢ (ULift α) where
  compl c := ⟨compl (c.map uliftDownHom)⟩
  conv_compl := conv_compl
  lbcompl hn c := ⟨IsCOFE.lbcompl hn (c.map uliftDownHom)⟩
  conv_lbcompl hn c _ hm:= IsCOFE.conv_lbcompl hn (c.map uliftDownHom) hm
  lbcompl_ne hn _ _ _ hc := IsCOFE.lbcompl_ne hn _ _ (fun p hp => hc p hp)

@[rocq_alias unit_ofe_discrete]
instance : Discreteᵢ Unit where
  discrete_0 _ := Subsingleton.elim _ _

@[rocq_alias unit_cofe]
instance : COFEᵢ Unit where
  compl _ := ()
  conv_compl := ⟨⟩
  lbcompl _ _ := ()
  conv_lbcompl _ _ _ _ := ⟨⟩
  lbcompl_ne _ _ _ _ _ := ⟨⟩

@[rocq_alias Empty_set_ofe_discrete]
instance : Discreteᵢ Empty where
  discrete_0 {x} _ := x.elim

@[rocq_alias Empty_set_cofe]
instance : COFEᵢ Empty where
  compl c := (c 0).elim
  conv_compl {_ c} := (c 0).elim
  lbcompl hn c := (c.bchain 0 hn.limit_lt_0).elim
  conv_lbcompl hn c := (c.bchain 0 hn.limit_lt_0).elim
  lbcompl_ne hn c := (c.bchain 0 hn.limit_lt_0).elim

@[indexed]
abbrev IsCOFEFun {α : Type _} (β : α → Type _) [OFEFunᵢ β] := ∀ x : α, IsCOFEᵢ (β x)

#rocq_ignore option_compl "Local Compl definition; folded into Lean's IsCOFE instance."

@[rocq_alias discrete_fun_cofe]
instance {α : Type _} (β : α → Type _) [∀ x, COFEᵢ (β x)] : COFEᵢ ((x : α) → β x) where
  compl c x := compl (c.map (OFE.applyHomᵢ x))
  conv_compl _ := IsCOFE.conv_compl
  lbcompl hn c x := IsCOFE.lbcompl hn (c.map (OFE.applyHomᵢ x))
  conv_lbcompl hn _ _ hm _ := IsCOFE.conv_lbcompl hn _ hm
  lbcompl_ne hn _ _ _ hc x := IsCOFE.lbcompl_ne hn _ _ (fun p hp => hc p hp x)
#rocq_ignore discrete_fun_chain "Local helper; folded into Lean's IsCOFE instance."

@[rocq_alias ofe_mor_cofe]
instance instIsCOFEHom [OFEᵢ α] [OFEᵢ β] [IsCOFEᵢ β] : IsCOFEᵢ (α -n> β) where
  compl c := by
    refine ⟨(compl <| c.map <| OFE.applyNeᵢ ·), ⟨fun n _ _ H => ?_⟩⟩
    refine conv_compl.trans (.trans ?_ conv_compl.symm)
    exact NonExpansive.ne (f := c.chain n) H
  conv_compl _ := IsCOFE.conv_compl
  lbcompl {n} hn c := by
    refine ⟨fun x => IsCOFE.lbcompl hn (c.map (OFE.applyNeᵢ x)), ⟨fun m x y H => ?_⟩⟩
    exact IsCOFE.lbcompl_ne hn _ _ (fun p hp => (c.bchain p hp).ne.ne H)
  conv_lbcompl hn c _ hm := fun _ => IsCOFE.conv_lbcompl hn _ hm
  lbcompl_ne hn c1 c2 _ hc := fun x => IsCOFE.lbcompl_ne hn _ _ (fun p hp => hc p hp x)
#rocq_ignore ofe_mor_compl "Inlined in IsCOFE instance"

@[rocq_alias prod_cofe]
instance instIsCOFEProd [OFEᵢ α] [OFEᵢ β] [IsCOFEᵢ α] [IsCOFEᵢ β] : IsCOFEᵢ (α × β) where
  compl c := ⟨compl (c.map ⟨Prod.fst, inferInstance⟩), compl (c.map ⟨Prod.snd, inferInstance⟩)⟩
  conv_compl := ⟨conv_compl, conv_compl⟩
  lbcompl hn c :=
    (IsCOFE.lbcompl hn (c.map ⟨Prod.fst, inferInstance⟩),
     IsCOFE.lbcompl hn (c.map ⟨Prod.snd, inferInstance⟩))
  conv_lbcompl hn _ _ hm := ⟨IsCOFE.conv_lbcompl hn _ hm, IsCOFE.conv_lbcompl hn _ hm⟩
  lbcompl_ne hn _ _ _ hc :=
    ⟨IsCOFE.lbcompl_ne hn _ _ (fun p hp => (hc p hp).left),
     IsCOFE.lbcompl_ne hn _ _ (fun p hp => (hc p hp).right)⟩

private theorem elim_const_dist_left [OFEᵢ α] [OFEᵢ β] {x y : α ⊕ β} {s₁ s₂ : α}
    (h : x ≡{n}≡ y) (hs : s₁ ≡{n}≡ s₂) :
    Sum.elim id (Function.const _ s₁) x ≡{n}≡ Sum.elim id (Function.const _ s₂) y :=
  match x, y with
  | .inl _, .inl _ => h
  | .inr _, .inr _ => hs
  | .inl _, .inr _ | .inr _, .inl _ => h.elim

private theorem elim_const_dist_right [OFEᵢ α] [OFEᵢ β] {x y : α ⊕ β} {s₁ s₂ : β}
    (h : x ≡{n}≡ y) (hs : s₁ ≡{n}≡ s₂) :
    Sum.elim (Function.const _ s₁) id x ≡{n}≡ Sum.elim (Function.const _ s₂) id y :=
  match x, y with
  | .inl _, .inl _ => hs
  | .inr _, .inr _ => h
  | .inl _, .inr _ | .inr _, .inl _ => h.elim

theorem IsCOFE.conv_compl_map [OFEᵢ α] [OFEᵢ β] [IsCOFEᵢ β] {c : Chainᵢ α} {f : α -n> β} {n} :
    compl (c.map f) ≡{n}≡ f.f (c n) := conv_compl
grind_pattern IsCOFE.conv_compl_map => compl (c.map f), c.chain n

theorem IsCOFE.conv_lbcompl_map [OFEᵢ α] [OFEᵢ β] [IsCOFEᵢ β] {n} {hn : SIdx.Limit n} {c : BChainᵢ α n}
    {f : α -n> β} {m} {hm : m < n} : IsCOFE.lbcompl hn (c.map f) ≡{m}≡ f.f (c.bchain m hm) :=
  IsCOFE.conv_lbcompl hn _ hm
grind_pattern IsCOFE.conv_lbcompl_map => IsCOFE.lbcompl hn (c.map f), c.bchain m hm

theorem Chain.dist_zero [OFEᵢ α] (c : Chainᵢ α) (n) : c n ≡{0}≡ c 0 := c.cauchy SIdx.le_0_l
grind_pattern Chain.dist_zero => c.chain n

theorem BChain.dist_zero [OFEᵢ α] {n} (hn : 0 < n) (c : BChainᵢ α n) {m} (hm : m < n) :
    c.bchain m hm ≡{0}≡ c.bchain 0 hn := c.bcauchy hn hm SIdx.le_0_l
grind_pattern BChain.dist_zero => c.bchain m hm, c.bchain 0 hn

@[rocq_alias sum_cofe]
instance instIsCOFESum [OFEᵢ α] [OFEᵢ β] [IsCOFEᵢ α] [IsCOFEᵢ β] : IsCOFEᵢ (α ⊕ β) where
  compl c := match c 0 with
    | .inl seed => .inl (compl (c.map ⟨Sum.elim id (Function.const _ seed), inferInstance⟩))
    | .inr seed => .inr (compl (c.map ⟨Sum.elim (Function.const _ seed) id, inferInstance⟩))
  conv_compl {n c} := by cases h : c.chain n <;> grind
  lbcompl {n} hn c :=
    match c.bchain 0 hn.limit_lt_0 with
    | .inl seed =>
      .inl (IsCOFE.lbcompl hn (c.map ⟨Sum.elim id (Function.const _ seed), inferInstance⟩))
    | .inr seed =>
      .inr (IsCOFE.lbcompl hn (c.map ⟨Sum.elim (Function.const _ seed) id, inferInstance⟩))
  conv_lbcompl {n} hn c {m} hm := by cases h : c.bchain m hm <;> grind
  lbcompl_ne {n} hn c1 c2 {m} hc := by
    have h0 := hc 0 hn.limit_lt_0
    cases h1 : c1.bchain 0 hn.limit_lt_0 <;> cases h2 : c2.bchain 0 hn.limit_lt_0
    · exact dist_inl <| IsCOFE.lbcompl_ne hn _ _ fun p hp =>
        elim_const_dist_left (hc p hp) (dist_ext_left (h1 ▸ h2 ▸ h0))
    · exact (h1 ▸ h2 ▸ h0).elim
    · exact (h1 ▸ h2 ▸ h0).elim
    · exact dist_inr <| IsCOFE.lbcompl_ne hn _ _ fun p hp =>
        elim_const_dist_right (hc p hp) (dist_ext_right (h1 ▸ h2 ▸ h0))

#rocq_ignore inl_chain "Local helper for `sum_compl`; folded into Lean's IsCOFE instance."
#rocq_ignore inr_chain "Local helper for `sum_compl`; folded into Lean's IsCOFE instance."
#rocq_ignore sum_compl "Local Compl definition; folded into Lean's IsCOFE instance."

@[rocq_alias sigT_chain_const_proj1]
theorem Sigma.chain_const_proj1 {P : α → Type _} [∀ x, OFEᵢ (P x)]
    (c : Chainᵢ (Sigma P)) n : (c n).fst = (c 0).fst :=
  (c.cauchy SIdx.le_0_l).choose

@[rocq_alias sigT_bchain_const_proj1]
theorem Sigma.bchain_const_proj1 {P : α → Type _} [∀ x, OFEᵢ (P x)]
    {n} (hn : SIdx.Limit n) (c : BChainᵢ (Sigma P) n) {m} (hm : m < n) :
    (c.bchain m hm).fst = (c.bchain 0 hn.limit_lt_0).fst :=
  (c.bcauchy hn.limit_lt_0 hm SIdx.le_0_l).choose

theorem Sigma.dist_cast_of_dist {P : α → Type _} [∀ x, OFEᵢ (P x)] {n}
    {x y : Sigma P} (h : x ≡{n}≡ y) {b : α} (hx : x.fst = b) (hy : y.fst = b) :
    (hx ▸ x.snd : P b) ≡{n}≡ (hy ▸ y.snd : P b) := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only at h1 hx
  subst h1; subst hx
  exact h2

theorem Sigma.mk_dist_of_dist_cast {P : α → Type _} [∀ x, OFEᵢ (P x)] {n} {x : Sigma P}
    {b : α} {hx : x.fst = b} {v : P b} (h : v ≡{n}≡ (hx ▸ x.snd : P b)) :
    (⟨b, v⟩ : Sigma P) ≡{n}≡ x := by
  cases x; subst hx; exact ⟨rfl, h⟩

@[rocq_alias bchain_map_snd]
def Sigma.bchain_map_snd {P : α → Type _} [∀ x, OFEᵢ (P x)]
    {n} (hn : SIdx.Limit n) (c : BChainᵢ (Sigma P) n) :
    BChainᵢ (P (c.bchain 0 hn.limit_lt_0).fst) n where
  bchain m hm := Sigma.bchain_const_proj1 hn c hm ▸ (c.bchain m hm).snd
  bcauchy _ hp hle :=
    Sigma.dist_cast_of_dist (c.bcauchy _ hp hle)
      (Sigma.bchain_const_proj1 hn c hp) (Sigma.bchain_const_proj1 hn c _)

theorem Sigma.lbcompl_cast {P : α → Type _} [∀ x, OFEᵢ (P x)] [∀ x, IsCOFEᵢ (P x)]
    {a b : α} (eq : a = b) {n} (hn : SIdx.Limit n) (c : BChainᵢ (P a) n) :
    (eq ▸ IsCOFE.lbcompl hn c : P b)
      = IsCOFE.lbcompl hn (eq ▸ c : BChainᵢ (P b) n) := by
  subst eq; rfl

theorem Sigma.bchain_cast_apply {P : α → Type _} [∀ x, OFEᵢ (P x)] {a b : α} (eq : a = b)
    {n} (c : BChainᵢ (P a) n) {p} (hp : p < n) :
    (eq ▸ c : BChainᵢ (P b) n).bchain p hp = eq ▸ c.bchain p hp := by
  subst eq; rfl

theorem Sigma.cast_cast {P : α → Type _} {a b c : α} (h1 : a = b) (h2 : b = c) (x : P a) :
    (h2 ▸ (h1 ▸ x : P b) : P c) = (h1.trans h2) ▸ x := by
  subst h1; subst h2; rfl

@[rocq_alias chain_map_snd]
def Sigma.chain_map_snd {P : α → Type _} [∀ x, OFEᵢ (P x)] (c : Chainᵢ (Sigma P)) :
    Chainᵢ (P (c 0).fst) where
  chain n := Sigma.chain_const_proj1 c n ▸ (c n).snd
  cauchy {n} {i} hle :=
    Sigma.dist_cast_of_dist (c.cauchy hle)
      (Sigma.chain_const_proj1 c i) (Sigma.chain_const_proj1 c n)

@[rocq_alias sigT_cofe]
instance {P : α → Type _} [∀ x, OFEᵢ (P x)] [∀ x, IsCOFEᵢ (P x)] : IsCOFEᵢ (Sigma P) where
  compl c := ⟨(c 0).fst, compl (Sigma.chain_map_snd c)⟩
  conv_compl {n} {c} :=
    Sigma.mk_dist_of_dist_cast (conv_compl (c := Sigma.chain_map_snd c) (n := n))
  lbcompl {n} hn c :=
    ⟨(c.bchain 0 hn.limit_lt_0).fst, IsCOFE.lbcompl hn (Sigma.bchain_map_snd hn c)⟩
  conv_lbcompl hn c _ hm :=
    Sigma.mk_dist_of_dist_cast (IsCOFE.conv_lbcompl hn (Sigma.bchain_map_snd hn c) hm)
  lbcompl_ne {n} hn c1 c2 {m} hc := by
    obtain ⟨eq, -⟩ := hc 0 hn.limit_lt_0
    refine ⟨eq, ?_⟩
    rw [Sigma.lbcompl_cast eq hn (Sigma.bchain_map_snd hn c1)]
    refine IsCOFE.lbcompl_ne hn _ _ (fun p hp => ?_)
    simp only [Sigma.bchain_cast_apply, Sigma.bchain_map_snd, Sigma.cast_cast]
    exact Sigma.dist_cast_of_dist (hc p hp) _ _

#rocq_ignore sigT_compl "Local Compl definition; folded into Lean's IsCOFE instance."

set_option linter.checkUnivs false in
@[indexed]
abbrev OFunctorPre := ∀ α β [COFEᵢ α] [COFEᵢ β], Type _
#rocq_ignore oFunctor_apply "Definition for application of an `oFunctor`; subsumed by `OFunctorPre` in Lean."

variable (SI) in
@[indexed, rocq_alias oFunctor]
class OFunctor (F : OFunctorPreᵢ) where
  ofe [COFEᵢ α] [COFEᵢ β] : OFEᵢ (F α β)
  map [COFEᵢ α₁] [COFEᵢ α₂] [COFEᵢ β₁] [COFEᵢ β₂] :
    (α₂ -n> α₁) → (β₁ -n> β₂) → F α₁ β₁ -n> F α₂ β₂
  map_ne [COFEᵢ α₁] [COFEᵢ α₂] [COFEᵢ β₁] [COFEᵢ β₂] :
    NonExpansive₂ᵢ (@map α₁ α₂ β₁ β₂ _ _ _ _)
  map_id [COFEᵢ α] [COFEᵢ β] (x : F α β) : map (Hom.id (α := α)) (Hom.id (α := β)) x = x
  map_comp [COFEᵢ α₁] [COFEᵢ α₂] [COFEᵢ α₃] [COFEᵢ β₁] [COFEᵢ β₂] [COFEᵢ β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) (x : F α₁ β₁) :
    map (f.comp g) (g'.comp f') x = map g g' (map f f' x)

variable (SI) in
@[indexed, rocq_alias oFunctorContractive]
class OFunctorContractive (F : OFunctorPreᵢ) extends OFunctorᵢ F where
  map_contractive [COFEᵢ α₁] [COFEᵢ α₂] [COFEᵢ β₁] [COFEᵢ β₂] :
    Contractiveᵢ (Function.uncurry (@map α₁ α₂ β₁ β₂ _ _ _ _))

attribute [reducible, instance] OFunctor.ofe

end COFE

/- Discrete OFE structure on a type -/
@[ext] structure DiscreteO (α : Type _) where
  car : α

section DiscreteO
instance : COFEᵢ (DiscreteO α) := COFE.ofDiscrete _
instance {α : Type _} : OFE.Discreteᵢ (DiscreteO α) := ⟨fun h => h⟩

#rocq_ignore leibnizO_leibniz "Not needed"

theorem DiscreteO.eqv_inj {x y : α} (H : DiscreteO.mk x = DiscreteO.mk y) : x = y :=
  congrArg DiscreteO.car H

theorem DiscreteO.dist_inj {x y : α} {n} (H : DiscreteO.mk x ≡{n}≡ DiscreteO.mk y) : x = y :=
  DiscreteO.eqv_inj <| discrete H

end DiscreteO

section ComposeOF
open COFE

/-- The composition of two functors, `F₁` applied to `F₂`. -/
@[indexed]
abbrev ComposeOF (F₁ F₂ : OFunctorPreᵢ) [OFunctorᵢ F₂]
    [∀ α β, [COFEᵢ α] → [COFEᵢ β] → IsCOFEᵢ (F₂ α β)] : OFunctorPreᵢ :=
  fun α β _ _ => F₁ (F₂ β α) (F₂ α β)

theorem COFE.OFunctor.map_id_eq {F : OFunctorPreᵢ} [OFunctorᵢ F] [COFEᵢ α] [COFEᵢ β] :
    OFunctor.map (F := F) (Hom.id (α := α)) (Hom.id (α := β)) = Hom.id :=
  Hom.ext (funext fun y => OFunctor.map_id y)

theorem COFE.OFunctor.map_comp_eq {F : OFunctorPreᵢ} [OFunctorᵢ F]
    [COFEᵢ α₁] [COFEᵢ α₂] [COFEᵢ α₃] [COFEᵢ β₁] [COFEᵢ β₂] [COFEᵢ β₃]
    (f : α₂ -n> α₁) (g : α₃ -n> α₂) (f' : β₁ -n> β₂) (g' : β₂ -n> β₃) :
    OFunctor.map (F := F) (f.comp g) (g'.comp f') =
      (OFunctor.map g g').comp (OFunctor.map f f') :=
  Hom.ext (funext fun y => OFunctor.map_comp f g f' g' y)

theorem COFE.OFunctorContractive.map_distLater {F : OFunctorPreᵢ} [OFunctorContractiveᵢ F]
    [COFEᵢ α₁] [COFEᵢ α₂] [COFEᵢ β₁] [COFEᵢ β₂] {n} {f₁ f₂ : α₂ -n> α₁} {g₁ g₂ : β₁ -n> β₂}
    (hf : DistLaterᵢ n f₁ f₂) (hg : DistLaterᵢ n g₁ g₂) (x : F α₁ β₁) :
    OFunctor.map f₁ g₁ x ≡{n}≡ OFunctor.map f₂ g₂ x :=
  map_contractive.1 (x := (f₁, g₁)) (y := (f₂, g₂)) (fun m hm => ⟨hf m hm, hg m hm⟩) x

variable {F₁ F₂ : OFunctorPreᵢ} [OFunctorᵢ F₂] [∀ α β, [COFEᵢ α] → [COFEᵢ β] → IsCOFEᵢ (F₂ α β)]

open OFunctor in
@[rocq_alias oFunctor_oFunctor_compose]
instance oFunctor_composeOF [OFunctorᵢ F₁] : OFunctorᵢ (ComposeOFᵢ F₁ F₂) where
  ofe := _
  map f g := map (F := F₁) (map (F := F₂) g f) (map (F := F₂) f g)
  map_ne.ne _ _ _ hf _ _ hg _ :=
    (map_ne (F := F₁)).ne (fun _ => (map_ne (F := F₂)).ne hg hf _)
      (fun _ => (map_ne (F := F₂)).ne hf hg _) _
  map_id _ := by
    simp only [map_id_eq]
    rfl
  map_comp _ _ _ _ _ := by
    simp only [map_comp_eq]
    rfl

open OFunctor OFunctorContractive in
@[rocq_alias oFunctor_oFunctor_compose_contractive_1]
instance oFunctor_composeOF_contractive_left [OFunctorContractiveᵢ F₁] :
    OFunctorContractiveᵢ (ComposeOFᵢ F₁ F₂) where
  map_contractive := ⟨fun {_ _ _} h x =>
    map_distLater (F := F₁)
      (fun m hm _ => (map_ne (F := F₂)).ne (h m hm).2 (h m hm).1 _)
      (fun m hm _ => (map_ne (F := F₂)).ne (h m hm).1 (h m hm).2 _) x⟩

end ComposeOF

section ComposeOFContractive
open COFE OFunctor OFunctorContractive

variable {F₁ F₂ : OFunctorPreᵢ} [OFunctorContractiveᵢ F₂]
  [∀ α β, [COFEᵢ α] → [COFEᵢ β] → IsCOFEᵢ (F₂ α β)]

@[rocq_alias oFunctor_oFunctor_compose_contractive_2]
instance oFunctor_composeOF_contractive_right [OFunctorᵢ F₁] :
    OFunctorContractiveᵢ (ComposeOFᵢ F₁ F₂) where
  map_contractive := ⟨fun {_ _ _} h x =>
    (map_ne (F := F₁)).ne
      (fun _ => map_distLater (F := F₂) (fun m hm => (h m hm).2) (fun m hm => (h m hm).1) _)
      (fun _ => map_distLater (F := F₂) (fun m hm => (h m hm).1) (fun m hm => (h m hm).2) _) x⟩

end ComposeOFContractive

section DiscreteFunOF
open COFE

@[indexed]
abbrev DiscreteFunOF {C : Type _} (F : C → OFunctorPreᵢ) : OFunctorPreᵢ :=
  fun A B _ _ => (c : C) → F c A B

@[rocq_alias discrete_funOF]
instance oFunctor_discreteFunOF {C} (F : C → OFunctorPreᵢ) [∀ c, OFunctorᵢ (F c)] :
    OFunctorᵢ (DiscreteFunOFᵢ F) where
  ofe := _
  map f₁ f₂ := OFE.mapCodHomᵢ fun _ => OFunctor.map f₁ f₂
  map_ne.ne _ _ _ Hx _ _ Hy _ _ := OFunctor.map_ne.ne Hx Hy ..
  map_id x := funext fun c => OFunctor.map_id (x c)
  map_comp f g f' g' x := funext fun c => OFunctor.map_comp f g f' g' (x c)

@[rocq_alias discrete_funOF_contractive]
instance oFunctor_discreteFunOF_contractive {C} (F : C → OFunctorPreᵢ)
    [∀ c, OFunctorContractiveᵢ (F c)] : OFunctorContractiveᵢ (DiscreteFunOFᵢ F) where
  map_contractive.1 h _ _ := OFunctorContractive.map_contractive.distLater_dist h _

end DiscreteFunOF

section Option
variable [OFEᵢ α]

@[rocq_alias option_chain]
def optionChain (c : Chainᵢ (Option α)) (x : α) : Chainᵢ α := by
  refine ⟨fun n => (c n).getD x, fun {n} {i} H => ?_⟩
  have := c.cauchy H; revert this
  cases c.chain i <;> cases c.chain n <;> simp [Dist]

@[rocq_alias option_bchain]
def optionBChain {n} (c : BChainᵢ (Option α) n) (x : α) : BChainᵢ α n := by
  refine ⟨fun m hm => (c.bchain m hm).getD x, fun {m} {p} hm hp H => ?_⟩
  have := c.bcauchy hm hp H; revert this
  cases c.bchain p hp <;> cases c.bchain m hm <;> simp [Dist]

@[rocq_alias option_cofe]
instance isCOFE_option [IsCOFEᵢ α] : IsCOFEᵢ (Option α) where
  compl c := (c 0).map fun x => IsCOFE.compl (optionChain c x)
  conv_compl {n} c := by
    have := c.cauchy (SIdx.le_0_l (n := n)); revert this
    rcases c.chain 0 with _|x' <;> rcases e : c.chain n with _|y' <;> simp [Dist]
    refine fun _ => OFE.dist_eqv.trans IsCOFE.conv_compl ?_
    simp [optionChain, e]
  lbcompl {n} hn c :=
    (c.bchain 0 hn.limit_lt_0).map fun x => IsCOFE.lbcompl hn (optionBChain c x)
  conv_lbcompl {n} hn c {m} hm := by
    have := c.bcauchy hn.limit_lt_0 hm SIdx.le_0_l; revert this
    rcases c.bchain 0 hn.limit_lt_0 with _ | x' <;> rcases e : c.bchain m hm with _ | y' <;>
      simp [Dist]
    refine fun _ => OFE.dist_eqv.trans (IsCOFE.conv_lbcompl hn _ hm) ?_
    simp [optionBChain, e]
  lbcompl_ne {n} hn c1 c2 {m} hc := by
    have h0 := hc 0 hn.limit_lt_0
    revert h0
    rcases e1 : c1.bchain 0 hn.limit_lt_0 with _ | x1 <;>
      rcases e2 : c2.bchain 0 hn.limit_lt_0 with _ | x2 <;>
      simp only [Option.map, Dist] <;> intro h0
    · trivial
    · exact h0.elim
    · exact h0.elim
    · refine IsCOFE.lbcompl_ne hn _ _ (fun p hp => ?_)
      have hp' := hc p hp
      simp only [optionBChain]
      cases f1 : c1.bchain p hp with
      | none =>
        cases f2 : c2.bchain p hp with rw [f1, f2] at hp'
        | none => exact h0
        | some _ => exact hp'.elim
      | some _ =>
        cases f2 : c2.bchain p hp with rw [f1, f2] at hp'
        | none => exact hp'.elim
        | some _ => exact hp'

@[indexed, rocq_alias optionO_map]
def optionMap {α β : Type _} [OFEᵢ α] [OFEᵢ β] (f : α -n> β) : Option α -n> Option β := by
  refine ⟨Option.map f, ⟨?_⟩⟩
  rintro _ ⟨⟩ ⟨⟩ H <;> simp_all [Dist]
  exact f.ne.ne H

@[rocq_alias option_fmap_ne]
theorem Option.map_ne [OFEᵢ β] {f g : α → β} {x y : Option α} {n} :
    (∀ x y, x ≡{n}≡ y → f x ≡{n}≡ g y) → x ≡{n}≡ y → Option.map f x ≡{n}≡ Option.map g y := by
  intro hf hxy
  cases x <;> cases y <;> simp_all [Dist]

theorem Option.map_forall₂ {α β : Type _} (f : α → β)
    {o1 o2 : Option α} (h : o1 = o2) : o1.map f = o2.map f := congrArg (Option.map f) h

@[rocq_alias optionO_map_ne]
instance optionMap_ne [OFEᵢ β] : NonExpansiveᵢ (optionMapᵢ (α := α) (β := β)) where
  ne _ f _ h o :=
    Option.map_ne (fun _ _ hab => dist_eqv.trans (f.ne.ne hab) (h _)) (dist_eqv.refl o)

@[rocq_alias option_mbind_ne]
theorem Option.bind_ne [OFEᵢ β] {f g : α → Option β} {x y : Option α} {n}
    (hf : ∀ x y, x ≡{n}≡ y → f x ≡{n}≡ g y) (hxy : x ≡{n}≡ y) : x.bind f ≡{n}≡ y.bind g := by
  cases x <;> cases y <;> simp_all [Dist]

@[rocq_alias option_mjoin_ne]
theorem Option.join_ne {x y : Option (Option α)} {n} (hxy : x ≡{n}≡ y) : x.join ≡{n}≡ y.join := by
  cases x <;> cases y <;> simp_all [Dist]

@[rocq_alias from_option_ne]
theorem Option.elim_ne {β : Type _} (R : β → β → Prop) {f g : α → β} {d d' : β}
    {x y : Option α} {n} (hf : ∀ x y, x ≡{n}≡ y → R (f x) (g y)) (hd : R d d')
    (hxy : x ≡{n}≡ y) : R (x.elim d f) (y.elim d' g) := by
  cases x <;> cases y <;> simp_all [Dist]

end Option

section OptionOF
open COFE

@[indexed]
abbrev OptionOF (F : OFunctorPreᵢ) : OFunctorPreᵢ :=
  fun A B _ _ => Option (F A B)

variable (F : OFunctorPreᵢ)

@[rocq_alias optionOF]
instance oFunctorOption [OFunctorᵢ F] : OFunctorᵢ (OptionOFᵢ F) where
  ofe := _
  map f g := optionMapᵢ (OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy z := by
    cases z <;> simp [optionMap, Dist]
    exact OFunctor.map_ne.ne Hx Hy ..
  map_id z := by
    cases z with
    | none => rfl
    | some c => exact Option.some_inj.mpr (OFunctor.map_id c)
  map_comp f g f' g' z := by
    cases z with
    | none => rfl
    | some c => exact Option.some_inj.mpr (OFunctor.map_comp f g f' g' c)

@[rocq_alias optionOF_contractive]
instance [OFunctorContractiveᵢ F] : OFunctorContractiveᵢ (OptionOFᵢ F) where
  map_contractive.1 H z := by
    have := (OFunctorContractive.map_contractive (F := F)).distLater_dist H
    cases z <;> simp_all [optionMap, Dist, HasDist.dist, Option.Forall₂, Function.uncurry, OFunctor.map]

end OptionOF

section ProdOF

open COFE

theorem Prod.map_ext {f f' : A → A'} {g g' : B → B'} (Hf : ∀ a, f a = f' a)
    (Hg : ∀ a, g a = g' a) : Prod.map f g x = Prod.map f' g' x :=
  Prod.ext (Hf x.fst) (Hg x.snd)

theorem Prod.map_ne [OFEᵢ A'] [OFEᵢ B'] {n} {f f' : A → A'} {g g' : B → B'}
    (Hf : ∀ a, f a ≡{n}≡ f' a) (Hg : ∀ a, g a ≡{n}≡ g' a) : Prod.map f g x ≡{n}≡ Prod.map f' g' x :=
  ⟨Hf x.fst, Hg x.snd⟩

variable [OFEᵢ A] [OFEᵢ A'] [OFEᵢ B] [OFEᵢ B']

@[rocq_alias prod_map_ne]
instance instNonExpansiveProdMap (f : A → A') (g : B → B') [NonExpansiveᵢ f] [NonExpansiveᵢ g] :
    NonExpansiveᵢ (Prod.map f g) where
  ne _ _ _ H := by
    constructor
    · rw [Prod.map_fst]
      exact NonExpansive.ne H.1
    · rw [Prod.map_snd]
      exact NonExpansive.ne H.2

@[indexed, rocq_alias prodO_map]
def Prod.mapO (f : A -n> A') (g : B -n> B') : A × B -n> A' × B' where
  f := .map f g
  ne := inferInstance

@[rocq_alias prodO_map_ne]
instance Prod.mapO_ne : NonExpansive₂ᵢ (Prod.mapOᵢ (A := A) (A' := A') (B := B) (B' := B')) where
  ne _ _ _ Hf _ _ Hg _ := Prod.map_ne Hf Hg

@[indexed]
abbrev ProdOF (F1 F2 : OFunctorPreᵢ) : OFunctorPreᵢ :=
  fun A B => (F1 A B) × (F2 A B)

open OFunctor in
@[rocq_alias prodOF]
instance instOFunctorProdOF [OFunctorᵢ F1] [OFunctorᵢ F2] : OFunctorᵢ (ProdOFᵢ F1 F2) where
  ofe := inferInstance
  map f g := Prod.mapOᵢ (map f g) (map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ := ⟨map_ne.ne Hx Hy _, map_ne.ne Hx Hy _⟩
  map_id _ := Prod.ext (map_id _) (map_id _)
  map_comp _ _ _ _ _ := Prod.ext (map_comp _ _ _ _ _) (map_comp _ _ _ _ _)

open OFunctorContractive in
@[rocq_alias prodOF_contractive]
instance instOFunctorContractiveProdOF [OFunctorContractiveᵢ F1] [OFunctorContractiveᵢ F2] :
    OFunctorContractiveᵢ (ProdOFᵢ F1 F2) where
  map_contractive.1 H _ :=
   Prod.map_ne (fun _ => map_contractive.1 H _) (fun _ => map_contractive.1 H _)

end ProdOF

section SumOF

open COFE

theorem Sum.map_ext {f f' : A → A'} {g g' : B → B'} (Hf : ∀ a, f a = f' a)
    (Hg : ∀ a, g a = g' a) : Sum.map f g x = Sum.map f' g' x :=
    match x with
    | .inl _ => congrArg Sum.inl (Hf _)
    | .inr _ => congrArg Sum.inr (Hg _)

theorem Sum.map_ne [OFEᵢ A'] [OFEᵢ B'] {n} {f f' : A → A'} {g g' : B → B'}
    (Hf : ∀ a, f a ≡{n}≡ f' a) (Hg : ∀ a, g a ≡{n}≡ g' a) : Sum.map f g x ≡{n}≡ Sum.map f' g' x :=
    match x with
    | .inl _ => dist_inl (Hf _)
    | .inr _ => dist_inr (Hg _)

variable [OFEᵢ A] [OFEᵢ A'] [OFEᵢ B] [OFEᵢ B']

@[rocq_alias sum_map_ne]
instance instNonExpansiveSumMap (f : A → A') (g : B → B') [NonExpansiveᵢ f] [NonExpansiveᵢ g] :
    NonExpansiveᵢ (Sum.map f g) where
  ne _ x y H := match x, y with
    | .inl _, .inl _ => NonExpansive.ne (f := Sum.inl) (NonExpansive.ne (dist_ext_left H))
    | .inr _, .inr _ => NonExpansive.ne (f := Sum.inr) (NonExpansive.ne (dist_ext_right H))

@[indexed, rocq_alias sumO_map]
def Sum.mapO (f : A -n> A') (g : B -n> B') : A ⊕ B -n> A' ⊕ B' where
  f := .map f g
  ne := inferInstance

@[rocq_alias sumO_map_ne]
instance Sum.mapO_ne : NonExpansive₂ᵢ (Sum.mapOᵢ (A := A) (A' := A') (B := B) (B' := B')) where
  ne _ _ _ Hf _ _ Hg _ := Sum.map_ne Hf Hg

@[indexed]
abbrev SumOF (F1 F2 : OFunctorPreᵢ) : OFunctorPreᵢ := fun A B => (F1 A B) ⊕ (F2 A B)

open OFunctor in
@[rocq_alias sumOF]
instance instOFunctorSumOF [OFunctorᵢ F1] [OFunctorᵢ F2] : OFunctorᵢ (SumOFᵢ F1 F2) where
  ofe := inferInstance
  map f g := Sum.mapOᵢ (map f g) (map f g)
  map_ne.ne _ _ _ Hx _ _ Hy x := match x with
    | .inl _ => dist_inl (map_ne.ne Hx Hy _)
    | .inr _ => dist_inr (map_ne.ne Hx Hy _)
  map_id x := match x with
    | .inl _ => congrArg Sum.inl (map_id _)
    | .inr _ => congrArg Sum.inr (map_id _)
  map_comp _ _ _ _ x := match x with
    | .inl _ => congrArg Sum.inl (map_comp _ _ _ _ _)
    | .inr _ => congrArg Sum.inr (map_comp _ _ _ _ _)

open OFunctorContractive in
@[rocq_alias sumOF_contractive]
instance instOFunctorContractiveSumOF [OFunctorContractiveᵢ F1] [OFunctorContractiveᵢ F2] :
    OFunctorContractiveᵢ (SumOFᵢ F1 F2) where
  map_contractive.1 H _ :=
    Sum.map_ne (fun _ => map_contractive.1 H _) (fun _ => map_contractive.1 H _)

end SumOF

section SigmaOF

open COFE

@[indexed, rocq_alias sigT_map]
def Sigma.mapO {P1 P2 : A → Type _} [∀ x, OFEᵢ (P1 x)] [∀ x, OFEᵢ (P2 x)] :
  ((a : A) → P1 a -n> P2 a) -n> Sigma P1 -n> Sigma P2 where
  f g := ⟨fun x => ⟨_, g x.fst x.snd⟩, ⟨by rintro n ⟨x, xH⟩ ⟨y, yH⟩ ⟨⟨⟩, hdist⟩; exact ⟨rfl, (g x).ne.ne hdist⟩⟩⟩
  ne := ⟨fun n f g hdist x => ⟨rfl, hdist _ _⟩⟩

open OFunctor in
@[indexed]
abbrev SigmaOF (F : A → OFunctorPreᵢ) : OFunctorPreᵢ :=
  fun B C => Sigma (fun (a : A) => (F a) B C)

open OFunctor in
@[rocq_alias sigTOF]
instance instOFunctorSigmaOF {F : A → OFunctorPreᵢ} [∀ a, OFunctorᵢ (F a)] : OFunctorᵢ (SigmaOFᵢ F) where
  ofe := inferInstance
  map f g := Sigma.mapOᵢ (fun _ => map f g)
  map_ne.ne _ _ _ Hx _ _ Hy := NonExpansive.ne (fun _ => map_ne.ne Hx Hy)
  map_id x := by obtain ⟨a, v⟩ := x; exact congrArg (Sigma.mk a) (OFunctor.map_id v)
  map_comp f g f' g' x := by
    obtain ⟨a, v⟩ := x; exact congrArg (Sigma.mk a) (OFunctor.map_comp f g f' g' v)

open OFunctorContractive in
@[rocq_alias sigTOF_contractive]
instance instOFunctorContractiveSigmaOF [∀ a, OFunctorContractiveᵢ (F a)] :
    OFunctorContractiveᵢ (SigmaOFᵢ F) where
  map_contractive.1 H := Sigma.mapO.ne.ne (fun _ => map_contractive.1 H)

end SigmaOF

section constOF

open COFE

@[indexed]
abbrev constOF (B : Type) : OFunctorPreᵢ := fun _ _ _ _ => B

@[rocq_alias constOF]
instance oFunctorConstOF [COFEᵢ B] : OFunctorᵢ (constOFᵢ B) where
  ofe := _
  map _ _ := ⟨id, id_ne⟩
  map_ne := by intros; constructor; simp
  map_id := by simp
  map_comp := by simp

@[rocq_alias constOF_contractive]
instance OFunctor.constOF_contractive [COFEᵢ B] : OFunctorContractiveᵢ (constOFᵢ B) where
  map_contractive.1 := by simp [OFunctor.map]

end constOF

section IdOF

open COFE

@[indexed]
abbrev IdOF : OFunctorPreᵢ := fun (_ : Type _) (B : Type _) (_ : COFEᵢ _) (_ : COFEᵢ B) => B

open OFunctor in
@[rocq_alias idOF]
instance : OFunctorᵢ IdOFᵢ where
  ofe := inferInstance
  map _ g := g
  map_ne.ne _ _ _ _ _ _ Hy := Hy
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

end IdOF

section HomOF

open COFE

variable [OFEᵢ A] [OFEᵢ A'] [OFEᵢ B] [OFEᵢ B']

@[indexed, rocq_alias ofe_morO_map]
def Hom.map (pre : A' -n> A) (post : B -n> B') : (A -n> B) -n> (A' -n> B') where
  f h := post.comp (h.comp pre)
  ne.ne _ _ _ Hh := fun x => post.ne.ne (Hh (pre x))
#rocq_ignore ofe_mor_map "Function-space map; subsumed by `Hom.map` in Lean."
#rocq_ignore ofe_mor_map_ne "Function-space map proof; subsumed by `Hom.map` in Lean."

@[rocq_alias ofe_morO_map_ne]
instance instNonExpansive₂HomMap :
    NonExpansive₂ᵢ (Hom.mapᵢ (A := A) (A' := A') (B := B) (B' := B')) where
  ne {_ _ _} Hx {y₁ _} Hy f g :=
    (NonExpansive.ne (f := y₁) (NonExpansive.ne (f := f) (Hx g))).trans (Hy _)

@[indexed]
abbrev HomOF (F1 F2 : OFunctorPreᵢ) [OFunctorᵢ F1] [OFunctorᵢ F2] : OFunctorPreᵢ :=
  fun (A : Type _) (B : Type _) (_ : COFEᵢ A) (_ : COFEᵢ B) => @F1 B A _ _ -n> @F2 A B _ _

open OFunctor in
@[rocq_alias ofe_morOF]
instance instOFunctorHomOF [OFunctorᵢ F1] [OFunctorᵢ F2] : OFunctorᵢ (HomOFᵢ F1 F2) where
  ofe := inferInstance
  map f g := Hom.mapᵢ (map (F := F1) g f) (map (F := F2) f g)
  map_ne.ne _ _ _ Hf _ _ Hg := NonExpansive₂.ne (map_ne.ne Hg Hf) (map_ne.ne Hf Hg)
  map_id x := OFE.eq_of_distᵢ fun _ a => ((map_id _).trans (congrArg x.f (map_id a))).dist
  map_comp _ _ _ _ x := OFE.eq_of_distᵢ fun _ _ =>
    ((map_comp ..).trans (congrArg _ (congrArg _ (congrArg x.f (map_comp ..))))).dist

open OFunctorContractive in
@[rocq_alias ofe_morOF_contractive]
instance instOFunctorContractiveHomOF [OFunctorContractiveᵢ F1] [OFunctorContractiveᵢ F2] :
    OFunctorContractiveᵢ (HomOFᵢ F1 F2) where
  map_contractive.1 {n} ab ab' h := match ab, ab' with
    | ⟨a, b⟩, ⟨a', b'⟩ => by
      simp only [Function.uncurry_apply_pair, OFunctor.map]
      have h' : DistLaterᵢ n (b, a) (b', a') := fun m hm => ⟨(h m hm).right, (h m hm).left⟩
      refine NonExpansive₂.ne (f := Hom.mapᵢ) ?_ ?_
      · exact (map_contractive (F := F1)).1 h'
      · exact (map_contractive (F := F2)).1 h

end HomOF

section Fixpoint

variable (SI) in
@[indexed, rocq_alias LimitPreserving]
class LimitPreserving [COFEᵢ α] (P : α → Prop) : Prop where
  compl (c : Chainᵢ α) : (∀ n, P (c n)) → P (COFE.compl c)
  lbcompl {n} (hn : SIdx.Limit n) (c : BChainᵢ α n) :
    (∀ m (hm : m < n), P (c.bchain m hm)) → P (IsCOFE.lbcompl hn c)

@[rocq_alias limit_preserving_const]
theorem LimitPreserving.const [COFEᵢ α] {P : Prop} : LimitPreservingᵢ fun (_ : α) => P where
  compl _ H := H 0
  lbcompl hn _ H := H 0 hn.limit_lt_0

@[rocq_alias limit_preserving_discrete]
theorem LimitPreserving.discrete [COFEᵢ α] {P : α → Prop}
    (hdiscrete : ∀ {x y : α}, x ≡{0}≡ y → (P x → P y)) : LimitPreservingᵢ P where
  compl _ H := hdiscrete (COFE.conv_compl (n := 0)).symm (H 0)
  lbcompl hn c H := hdiscrete (IsCOFE.conv_lbcompl hn c hn.limit_lt_0).symm (H 0 hn.limit_lt_0)

@[rocq_alias limit_preserving_and]
theorem LimitPreserving.and [COFEᵢ α] {P Q : α → Prop} (HP : LimitPreservingᵢ P)
    (HQ : LimitPreservingᵢ Q) : LimitPreservingᵢ fun a => P a ∧ Q a where
  compl c H := by
    constructor
    · exact HP.compl c fun n => (H n).left
    · exact HQ.compl c fun n => (H n).right
  lbcompl hn c H := by
    constructor
    · exact HP.lbcompl hn c fun m hm => (H m hm).left
    · exact HQ.lbcompl hn c fun m hm => (H m hm).right

@[rocq_alias limit_preserving_forall]
theorem LimitPreserving.forall [COFEᵢ α] (P : β → α → Prop) (Hlim : ∀ y, LimitPreservingᵢ (P y)) :
    LimitPreservingᵢ (∀ y, P y ·) where
  compl c H y := (Hlim y).compl c fun n => H n y
  lbcompl hn c H y := (Hlim y).lbcompl hn c fun m hm => H m hm y

@[rocq_alias limit_preserving_impl]
theorem LimitPreserving.impl [COFEᵢ α] (P1 P2 : α → Prop)
    (HP1 : ∀ {x y : α}, x ≡{0}≡ y → P1 x → P1 y)
    (Hcompl : LimitPreservingᵢ P2) :
    LimitPreservingᵢ (fun x => P1 x → P2 x) where
  compl c Hc HP1c :=
    Hcompl.compl c fun n => Hc n (HP1 (COFE.conv_compl' SIdx.le_0_l) HP1c)
  lbcompl hn c Hc HP1c :=
    Hcompl.lbcompl hn c fun m hm =>
      Hc m hm (HP1 ((IsCOFE.conv_lbcompl hn c hm).le SIdx.le_0_l) HP1c)

@[rocq_alias limit_preserving_impl']
theorem LimitPreserving.impl' [COFEᵢ α] (P1 P2 : α → Prop)
    (HP1 : ∀ {x y : α}, x ≡{0}≡ y → (P1 x ↔ P1 y))
    (Hcompl : LimitPreservingᵢ P2) :
    LimitPreservingᵢ (fun x => P1 x → P2 x) :=
  LimitPreserving.impl P1 P2 (fun h => (HP1 h).mp) Hcompl

@[rocq_alias limit_preserving_sidx_finite]
theorem LimitPreserving.of_sidx_finite [SIdxFinite SI] [COFEᵢ α] {P : α → Prop} :
    (∀ c : Chainᵢ α, (∀ n, P (c n)) → P (COFE.compl c)) ↔ LimitPreservingᵢ P := by
  constructor <;> intro h
  · exact { compl := h, lbcompl hn _ _ := absurd hn (SIdx.limit_finite _) }
  · exact h.compl

@[rocq_alias limit_preserving_equiv]
theorem LimitPreserving.equiv [SIdxFinite SI] [COFEᵢ α] [COFEᵢ β] (f g : α -n> β) :
    LimitPreservingᵢ (fun x => f x = g x) := by
  apply of_sidx_finite.mp
  intro c Hfg
  refine OFE.eq_of_distᵢ fun n => ?_
  apply (COFE.compl_map _ _).symm.dist.trans
  apply (COFE.conv_compl' SIdx.le_refl).trans
  apply (Hfg _).dist.trans
  exact g.ne.ne COFE.conv_compl.symm

@[rocq_alias limit_preserving_ext]
theorem LimitPreserving.ext {α} [COFEᵢ α] {P Q : α -> Prop} (he : ∀ {x}, (P x ↔ Q x))
    (hp : LimitPreservingᵢ P) : LimitPreservingᵢ Q where
  compl c H := he.mp (hp.compl c fun n => he.mpr (H n))
  lbcompl hn c H := he.mp (hp.lbcompl hn c fun m hm => he.mpr (H m hm))

section BCompl

variable [COFEᵢ α] [Inhabited α]

@[rocq_alias bcompl]
def bcompl (n) (c : BChainᵢ α n) : α :=
  match SIdx.case n with
  | .inl _              => default
  | .inr (.inl ⟨m, hm⟩) => c.bchain m (SIdx.lt_succ_diag_r' hm)
  | .inr (.inr hlim)    => IsCOFE.lbcompl hlim c

@[rocq_alias conv_bcompl]
theorem conv_bcompl {n} (c : BChainᵢ α n) {m} (hm : m < n) :
    bcompl n c ≡{m}≡ c.bchain m hm := by
  unfold bcompl
  rcases hcase : SIdx.case n with h0 | ⟨p, hp⟩ | hlim
  · exact absurd (h0 ▸ hm) (SIdx.not_lt_zero m)
  · exact c.bcauchy _ _ (SIdx.lt_succ_r.mp (hp ▸ hm))
  · exact IsCOFE.conv_lbcompl hlim c hm

@[rocq_alias bcompl_ne]
theorem bcompl_ne {n} (c1 c2 : BChainᵢ α n) {m}
    (Hc : ∀ p (hp : p < n), c1.bchain p hp ≡{m}≡ c2.bchain p hp) :
    bcompl n c1 ≡{m}≡ bcompl n c2 := by
  unfold bcompl
  rcases hcase : SIdx.case n with h0 | ⟨p, hp⟩ | hlim
  · rfl
  · exact Hc _ _
  · exact IsCOFE.lbcompl_ne hlim c1 c2 Hc

@[rocq_alias limit_preserving_bcompl]
theorem LimitPreserving.bcompl {P : α → Prop} (n) (c : BChainᵢ α n)
    (H0 : n ≠ 0 ∨ P default) (HP : LimitPreservingᵢ P)
    (Hc : ∀ m (hm : m < n), P (c.bchain m hm)) : P (bcompl n c) := by
  unfold Iris.bcompl
  rcases hcase : SIdx.case n with h0 | ⟨p, hp⟩ | hlim
  · exact H0.resolve_left (fun hne => hne h0)
  · exact Hc _ _
  · exact HP.lbcompl hlim c Hc

end BCompl

section BFChain

variable [COFEᵢ α] [Inhabited α] (f : α → α) [Contractiveᵢ f]

@[indexed, rocq_alias bfchain]
structure BFChain (n) where
  car : BChainᵢ α n
  fixpoint : ∀ p, p < n → f (bcompl n car) ≡{p}≡ bcompl n car

@[rocq_alias bfchain_chain_unique]
theorem BFChain.unique {n m} (c1 : BFChainᵢ f n) (c2 : BFChainᵢ f m) :
    ∀ p, p < n → p < m → bcompl n c1.car ≡{p}≡ bcompl m c2.car := by
  intro p
  induction p using (SIdx.lt_wf (I := SI)).induction with
  | h p IH =>
    intro Hn Hm
    refine ((c1.fixpoint p Hn).symm.trans ?_).trans (c2.fixpoint p Hm)
    exact Contractive.distLater_dist fun q Hq =>
      IH q Hq (SIdx.lt_trans Hq Hn) (SIdx.lt_trans Hq Hm)

def BFChain.goChain (n) (rec : ∀ m, m < n → BFChainᵢ f m) : BChainᵢ α n where
  bchain m Hm := f (bcompl m (rec m Hm).car)
  bcauchy := fun {m} {p} Hm Hp Hmp =>
    Contractive.distLater_dist fun q Hq =>
      BFChain.unique f (rec p Hp) (rec m Hm) q (SIdx.lt_le_trans Hq Hmp) Hq

@[rocq_alias fixpoint_bchain_go]
def BFChain.go (n) (rec : ∀ m, m < n → BFChainᵢ f m) : BFChainᵢ f n where
  car := BFChain.goChain f n rec
  fixpoint p Hp := by
    refine .trans (Contractive.distLater_dist (y := bcompl p (rec p Hp).car) ?_)
      (conv_bcompl (BFChain.goChain f n rec) Hp).symm
    intro q Hq
    exact ((conv_bcompl (BFChain.goChain f n rec) Hp).lt Hq).trans ((rec p Hp).fixpoint q Hq)

@[indexed, rocq_alias fixpoint_bchain]
def fixpointBFChain (n) : BFChainᵢ f n := SIdx.lt_wf.fix (BFChain.go f) n

theorem fixpointBFChain_unfold (n) :
    fixpointBFChainᵢ f n = BFChain.go f n (fun m _ => fixpointBFChainᵢ f m) :=
  SIdx.lt_wf.fix_eq (BFChain.go f) n

end BFChain

@[indexed, rocq_alias fixpoint_chain]
def Fixpoint.chain [COFEᵢ α] [Inhabited α] (f : α → α) [Contractiveᵢ f] : Chainᵢ α where
  chain n := f (bcompl n (fixpointBFChainᵢ f n).car)
  cauchy {n i} H := by
    rcases SIdx.le_lteq.mp H with (Hni | rfl)
    · exact Contractive.distLater_dist fun p Hp =>
        BFChain.unique f (fixpointBFChainᵢ f i) (fixpointBFChainᵢ f n) p
          (SIdx.lt_trans Hp Hni) Hp
    · rfl

/-- The chain construction of the Banach fixpoint. `fixpointP` packages it, together with
its unfolding equation, behind an opaque constant. -/
@[indexed]
def fixpointAux [COFEᵢ α] [Inhabited α] (f : α → α) [Contractiveᵢ f] : α :=
  COFE.compl <| Fixpoint.chainᵢ f

theorem fixpointAux_unfold [COFEᵢ α] [Inhabited α] (f : α -c> α) :
    fixpointAuxᵢ f = f (fixpointAuxᵢ f) := by
  refine OFE.eq_of_distᵢ fun n => ?_
  apply COFE.conv_compl.trans
  refine .trans ?_ (NonExpansive.ne COFE.conv_compl.symm)
  exact Contractive.distLater_dist fun p Hp => ((fixpointBFChainᵢ f.f n).fixpoint p Hp).symm

/-- The Banach fixpoint packed together with its unfolding equation as a single opaque
value. Being opaque, it is a stuck constant for definitional-equality checks in both the
elaborator and the kernel, which keeps the approximation chain of `fixpointAux` sealed. -/
@[indexed]
opaque fixpointP [COFEᵢ α] [Inhabited α] (f : α → α) [Contractiveᵢ f] : { x : α // x = f x } :=
  ⟨fixpointAuxᵢ f, fixpointAux_unfold f.toContractiveHom⟩

/-- Fixpoints inside of a COFE -/
@[indexed, rocq_alias fixpoint]
def fixpoint [COFEᵢ α] [Inhabited α] (f : α → α) [Contractiveᵢ f] : α :=
  (fixpointPᵢ f).val
#rocq_ignore fixpoint_def "Use fixpoint"
#rocq_ignore fixpoint_aux "Use fixpoint"
#rocq_ignore fixpoint_unseal "fixpoint is unsealed by default"

@[indexed]
nonrec abbrev OFE.ContractiveHom.fixpoint [COFEᵢ α] [Inhabited α] (f : α -c> α) : α := fixpointᵢ f.f

@[rocq_alias fixpoint_unfold]
theorem fixpoint_unfold [COFEᵢ α] [Inhabited α] (f : α -c> α) :
    fixpointᵢ f = f (fixpointᵢ f) :=
  (fixpointPᵢ f).property

@[rocq_alias fixpoint_unique]
theorem fixpoint_unique [COFEᵢ α] [Inhabited α] {f : α -c> α} {x : α} (h : x = f x) :
    x = fixpointᵢ f := by
  refine OFE.eq_of_distᵢ fun n => ?_
  induction n using (SIdx.lt_wf (I := SI)).induction with
  | h n ih =>
    exact h.dist.trans <| Dist.trans (Contractive.distLater_dist ih) (fixpoint_unfold f).dist.symm

@[rocq_alias fixpoint_ne]
instance OFE.ContractiveHom.fixpoint_ne [COFEᵢ α] [Inhabited α] :
    NonExpansiveᵢ (OFE.ContractiveHom.fixpointᵢ (α := α)) where
  ne n f1 f2 h := by
    revert h
    induction n using (SIdx.lt_wf (I := SI)).induction with
    | h n ih =>
      intro h
      calc
        _ ≡{n}≡ f1.f (fixpointᵢ f1.f) := (fixpoint_unfold f1).dist
        _ ≡{n}≡ f2.f (fixpointᵢ f1.f) := h _
        _ ≡{n}≡ f2.f (fixpointᵢ f2.f) := Contractive.distLater_dist fun p Hp => ih p Hp (h.lt Hp)
        _ ≡{n}≡ fixpointᵢ f2.f        := (fixpoint_unfold f2).dist.symm

theorem fixpoint_dist [COFEᵢ α] [Inhabited α] {f g : α → α} [Contractiveᵢ f] [Contractiveᵢ g] {n}
    (H : ∀ z, f z ≡{n}≡ g z) : fixpointᵢ f ≡{n}≡ fixpointᵢ g :=
  (OFE.ContractiveHom.fixpoint_ne (α := α)).ne
    (x₁ := f.toContractiveHom) (x₂ := g.toContractiveHom) H

@[rocq_alias fixpoint_proper]
theorem fixpoint_proper [COFEᵢ α] [Inhabited α] {f g : α → α} [Contractiveᵢ f] [Contractiveᵢ g]
    (H : ∀ x, f x = g x) : fixpointᵢ f = fixpointᵢ g :=
  funext H ▸ rfl

@[elab_as_elim, rocq_alias fixpoint_ind]
theorem OFE.ContractiveHom.fixpoint_ind [COFEᵢ α] [Inhabited α] (f : α -c> α)
    (P : α → Prop) (x : α) (Hbase : P x) (Hind : ∀ x, P x → P (f x)) (Hlim : LimitPreservingᵢ P) :
    P f.fixpoint := by
  obtain ⟨y, hy, hfy⟩ : ∃ y : α, P y ∧ y = f y := by
    letI : Inhabited α := ⟨x⟩
    exists fixpointAuxᵢ f.f
    constructor
    · refine Hlim.compl (Fixpoint.chainᵢ f.f) fun n => Hind _ ?_
      induction n using (SIdx.lt_wf (I := SI)).induction with
      | h n ih =>
        refine LimitPreserving.bcompl n _ (.inr Hbase) Hlim fun m hm => ?_
        rw [fixpointBFChain_unfold]
        exact Hind _ (ih m hm)
    · exact fixpointAux_unfold f
  exact (congrArg P (fixpoint_unique hfy)).mp hy

theorem repeat_dist [OFEᵢ α] (f g : α → α) [NonExpansiveᵢ f] {n} (Hfg : ∀ z, f z ≡{n}≡ g z) :
    ∀ k z, Nat.repeat f k z ≡{n}≡ Nat.repeat g k z :=
  Nat.repeat_rel dist_eqv (fun h => NonExpansive.ne h) Hfg

@[indexed, rocq_alias fixpointK]
def fixpointK [COFEᵢ α] [Inhabited α] (k : Nat) (f : α → α)
    [Contractiveᵢ (Nat.repeat f k)] : α := fixpointᵢ (Nat.repeat f k)

@[rocq_alias fixpointK_unfold]
theorem fixpointK_unfold [COFEᵢ α] [Inhabited α] (k : Nat) (f : α → α)
    [Contractiveᵢ (Nat.repeat f k)] : fixpointKᵢ k f = f (fixpointKᵢ k f) := by
  refine (fixpoint_unique (f := (Nat.repeat f k).toContractiveHom) ?_).symm
  change f (fixpointKᵢ k f) = Nat.repeat f k (f (fixpointKᵢ k f))
  refine ((Nat.repeat_apply_comm f k (fixpointKᵢ k f)).trans (congrArg f ?_)).symm
  exact (fixpoint_unfold (Nat.repeat f k).toContractiveHom).symm

@[rocq_alias fixpointK_unique]
theorem fixpointK_unique [COFEᵢ α] [Inhabited α] (k : Nat) (f : α → α)
    [Contractiveᵢ (Nat.repeat f k)] {x : α} (H : x = f x) : x = fixpointKᵢ k f :=
  fixpoint_unique (f := (Nat.repeat f k).toContractiveHom) (Nat.repeat_fixed f H k)

@[rocq_alias fixpointK_ne]
theorem fixpointK_ne [COFEᵢ α] [Inhabited α] (k : Nat) (f g : α → α)
    [Contractiveᵢ (Nat.repeat f k)] [Contractiveᵢ (Nat.repeat g k)] [NonExpansiveᵢ f] {n}
    (Hfg : ∀ z, f z ≡{n}≡ g z) : fixpointKᵢ k f ≡{n}≡ fixpointKᵢ k g :=
  fixpoint_dist (repeat_dist f g Hfg k)

@[rocq_alias fixpointK_proper]
theorem fixpointK_proper [COFEᵢ α] [Inhabited α] (k : Nat) (f g : α → α)
    [Contractiveᵢ (Nat.repeat f k)] [Contractiveᵢ (Nat.repeat g k)] [NonExpansiveᵢ f]
    (Hfg : ∀ z, f z = g z) : fixpointKᵢ k f = fixpointKᵢ k g :=
  eq_dist.mpr fun _ => fixpointK_ne k f g fun z => (Hfg z).dist

@[elab_as_elim, rocq_alias fixpointK_ind]
theorem fixpointK_ind [COFEᵢ α] [Inhabited α] (k : Nat) (f : α → α) [Contractiveᵢ (Nat.repeat f k)]
    (P : α → Prop) (x : α) (Hbase : P x)
    (Hind : ∀ x, P x → P (f x)) (Hlim : LimitPreservingᵢ P) : P (fixpointKᵢ k f) :=
  OFE.ContractiveHom.fixpoint_ind (Nat.repeat f k).toContractiveHom P x Hbase
    (fun _ Hy => Nat.repeat_ind f Hind Hy k) Hlim

end Fixpoint

section FixpointAB

open OFE

instance [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] : CoeFun (α -c> β -n> γ) (fun _ => α → β → γ) := ⟨fun f x => (f.f x).f⟩
instance [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] : CoeFun (α -c> β -c> γ) (fun _ => α → β → γ) := ⟨fun f x => (f.f x).f⟩

/-- A Contractive function with NonExpansive function codomain is NonExpansive₂. -/
instance ne₂_of_contractive_ne [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] (fA : α -c> β -n> γ) : NonExpansive₂ᵢ fA where
  ne n x₁ x₂ Hx y₁ y₂ Hy := by
    refine .trans ?_ ((fA.f x₂).ne.ne Hy)
    apply fA.ne.ne Hx

/-- A Contractive function with Contractive function codomain is NonExpansive₂. -/
instance ne₂_of_contractive [OFEᵢ α] [OFEᵢ β] [OFEᵢ γ] (fB : α -c> β -c> γ) : NonExpansive₂ᵢ fB where
  ne n x₁ x₂ Hx y₁ y₂ Hy := by
    refine .trans ?_ ((fB.f x₂).ne.ne Hy)
    apply fB.ne.ne Hx

@[rocq_alias fixpoint_AB]
def fixpointAB [COFEᵢ α] [COFEᵢ β] [Inhabited β] (fB : α -c> β -c> β) (x : α) : β := by
  let con_hom : β -c> β := {
    f := fB x,
    contractive := ⟨fB.f x |>.contractive.distLater_dist⟩
  }
  exact con_hom.fixpoint

@[rocq_alias fixpoint_AB_contractive]
theorem fixpointAB_contractive [COFEᵢ α] [COFEᵢ β] [Inhabited β] (fB : α -c> β -c> β) :
    Contractiveᵢ (fixpointAB fB) where
  distLater_dist {n} {_ _} Dl := by
    apply ContractiveHom.fixpoint_ne.ne
    apply fB.contractive.distLater_dist
    exact Dl

@[rocq_alias fixpoint_AA]
def fixpointAA [COFEᵢ α] [COFEᵢ β] [Inhabited β] (fA : α -c> β -n> α)
    (fB : α -c> β -c> β) (x : α) : α :=
  fA x (fixpointAB fB x)

@[rocq_alias fixpoint_AA_contractive]
theorem fixpointAA_contractive [COFEᵢ α] [COFEᵢ β] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) : Contractiveᵢ (fixpointAA fA fB) where
  distLater_dist {_ _ x₂} Dl := by
    refine .trans ?_ ((fA.f x₂).ne.ne ((fixpointAB_contractive fB).distLater_dist Dl))
    apply fA.contractive.distLater_dist
    exact Dl

@[indexed, rocq_alias fixpoint_A]
def fixpointA [COFEᵢ α] [COFEᵢ β] [Inhabited α] [Inhabited β] (fA : α -c> β -n> α)
    (fB : α -c> β -c> β) : α := by
  let con_hom : α -c> α := {
    f := fixpointAA fA fB,
    contractive := ⟨(fixpointAA_contractive fA fB).distLater_dist⟩
  }
  exact con_hom.fixpoint

@[indexed, rocq_alias fixpoint_B]
def fixpointB [COFEᵢ α] [COFEᵢ β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) : β :=
  fixpointAB fB <| fixpointAᵢ fA fB

@[rocq_alias fixpoint_A_unfold]
theorem fixpointA_unfold [COFEᵢ α] [COFEᵢ β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) :
    fA (fixpointAᵢ fA fB) (fixpointBᵢ fA fB) = (fixpointAᵢ fA fB) := by
  exact .symm (fixpoint_unfold _)

@[rocq_alias fixpoint_B_unfold]
theorem fixpointB_unfold [COFEᵢ α] [COFEᵢ β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) :
    fB (fixpointAᵢ fA fB) (fixpointBᵢ fA fB) = (fixpointBᵢ fA fB) := by
  exact .symm (fixpoint_unfold _)

@[rocq_alias fixpoint_A_unique]
theorem fixpointA_unique [COFEᵢ α] [COFEᵢ β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) (Hp : fA p q = p) (Hq : fB p q = q) :
    p = (fixpointAᵢ fA fB) :=
    fixpoint_unique <| Hp.symm.trans <| congrArg (fA p) (fixpoint_unique Hq.symm)

@[rocq_alias fixpoint_B_unique]
theorem fixpointB_unique [COFEᵢ α] [COFEᵢ β] [Inhabited α] [Inhabited β]
    (fA : α -c> β -n> α) (fB : α -c> β -c> β) (Hp : fA p q = p) (Hq : fB p q = q) :
    q = (fixpointBᵢ fA fB) := by
  apply fixpoint_unique
  exact Hq.symm.trans (congrArg (fun z => fB z q) (fixpointA_unique fA fB Hp Hq))

@[rocq_alias fixpoint_A_ne]
instance fixpointA_ne [COFEᵢ α] [COFEᵢ β] [Inhabited α] [Inhabited β] :
    NonExpansive₂ᵢ (fixpointAᵢ (α := α) (β := β)) where
  ne n fA fA' HfA fB fB' HfB := by
    apply OFE.ContractiveHom.fixpoint_ne.ne
    intro z₁
    refine ((ne₂_of_contractive_ne fA).ne .rfl ?_).trans (HfA z₁ _)
    exact ContractiveHom.fixpoint_ne.ne (HfB z₁)

@[rocq_alias fixpoint_B_ne]
instance fixpointB_ne [COFEᵢ α] [COFEᵢ β] [Inhabited α] [Inhabited β] :
    NonExpansive₂ᵢ (fixpointBᵢ (α := α) (β := β)) where
  ne n fA fA' HfA fB fB' HfB := by
    apply ContractiveHom.fixpoint_ne.ne
    intro z₁
    refine ((ne₂_of_contractive fB).ne ?_ .rfl).trans (HfB _ z₁)
    exact fixpointA_ne.ne HfA HfB

@[rocq_alias fixpoint_A_proper]
theorem fixpointA_proper [COFEᵢ α] [COFEᵢ β] [Inhabited α] [Inhabited β]
    (fA fA' : α -c> β -n> α) (fB fB' : α -c> β -c> β)
    (HA : ∀ x y, fA x y = fA' x y) (HB : ∀ x y, fB x y = fB' x y) :
    fixpointAᵢ fA fB = fixpointAᵢ fA' fB' :=
  eq_dist.mpr fun _ => fixpointA_ne.ne (fun x y => (HA x y).dist) (fun x y => (HB x y).dist)

@[rocq_alias fixpoint_B_proper]
theorem fixpointB_proper [COFEᵢ α] [COFEᵢ β] [Inhabited α] [Inhabited β]
    (fA fA' : α -c> β -n> α) (fB fB' : α -c> β -c> β)
    (HA : ∀ x y, fA x y = fA' x y) (HB : ∀ x y, fB x y = fB' x y) :
    fixpointBᵢ fA fB = fixpointBᵢ fA' fB' :=
  eq_dist.mpr fun _ => fixpointB_ne.ne (fun x y => (HA x y).dist) (fun x y => (HB x y).dist)

end FixpointAB

section Later

@[rocq_alias later] structure Later (A : Type u) : Type u where
  next :: car : A

@[rocq_alias later_ofe_mixin]
instance isOFE_later [OFEᵢ A] : OFEᵢ (Later A) where
  dist n x y := DistLaterᵢ n x.car y.car
  dist_eqv := ⟨fun _ => .rfl, .symm, .trans⟩
  eq_dist' {x y} := by
    obtain ⟨a⟩ := x; obtain ⟨b⟩ := y
    rw [Later.next.injEq, OFE.eq_distᵢ]
    exact ⟨fun H n => (H n).distLater, fun H n => (H (SIdx.succ n)).dist_lt (SIdx.lt_succ_self n)⟩
  dist_lt Hxy Hmn _ Hkm := Hxy _ (SIdx.lt_trans Hkm Hmn)
#rocq_ignore laterO "Use the later type"

#rocq_ignore later_equiv "Local Equiv instance; folded into Lean's OFE (Later A) instance."
#rocq_ignore later_dist "Local Dist instance; folded into Lean's OFE (Later A) instance."


@[rocq_alias Next_contractive]
instance NextContractive {A : Type _} [OFEᵢ A] : Contractiveᵢ (@Later.next A) where
  distLater_dist := id

#rocq_ignore Next_inj "`Inj` instance; `Later` dist is definitionally `DistLater` on the payload."
#rocq_ignore later_car_anti_contractive
  "`Proper` setoid instance; `Later` dist is definitionally `DistLater` on the payload."

@[rocq_alias Next_uninj]
theorem Later.uninj {A : Type _} (x : Later A) : ∃ a, x = Later.next a := ⟨x.car, rfl⟩

@[rocq_alias contractive_alt]
theorem contractive_alt [OFEᵢ A] [OFEᵢ B] (f : A → B) :
    Contractiveᵢ f ↔ ∃ g : Later A → B, NonExpansiveᵢ g ∧ ∀ x, f x = g (Later.next x) := by
  refine ⟨fun hf => ⟨fun x => f x.car, ⟨fun _ _ _ h => hf.distLater_dist h⟩, fun _ => rfl⟩, ?_⟩
  rintro ⟨g, hg, hf⟩
  refine ⟨fun {n} {x y} h => ?_⟩
  rw [hf, hf]; exact hg.ne h

@[rocq_alias later_chain]
def laterChain [OFEᵢ A] (c : Chainᵢ (Later A)) : Chainᵢ A where
  chain n := (c (SIdx.succ n)).car
  cauchy Hle := c.cauchy (SIdx.succ_le_mono.mp Hle) _ (SIdx.lt_succ_self _)

@[rocq_alias later_limit_bchain]
def laterLimitBChain [OFEᵢ A] {n} (c : BChainᵢ (Later A) n) (hn : SIdx.Limit n) :
    BChainᵢ A n where
  bchain m hm := (c.bchain succᵢ m (hn.succ_lt m hm)).car
  bcauchy {m} {p} hm hp h :=
    c.bcauchy (hn.succ_lt m hm) (hn.succ_lt p hp) (SIdx.succ_le_mono.mp h) m (SIdx.lt_succ_self m)

@[rocq_alias later_cofe]
instance isCOFE_later [OFEᵢ A] [IsCOFEᵢ A] : IsCOFEᵢ (Later A) where
  compl c := Later.next (IsCOFE.compl (laterChain c))
  conv_compl {n} c := by
    intros m Hlt
    refine IsCOFE.conv_compl.trans ?_
    exact ((c.cauchy <| SIdx.succ_le_of_lt Hlt) m (SIdx.lt_succ_self m)).symm
  lbcompl {n} hn c := Later.next (IsCOFE.lbcompl hn (laterLimitBChain c hn))
  conv_lbcompl {n} hn c {m} hm := by
    intro p hp
    refine (IsCOFE.conv_lbcompl hn (laterLimitBChain c hn) (SIdx.lt_trans hp hm)).trans ?_
    exact (c.bcauchy (hn.succ_lt p (SIdx.lt_trans hp hm)) hm
      (SIdx.le_succ_l.mpr hp) p (SIdx.lt_succ_self p)).symm
  lbcompl_ne {n} hn c1 c2 {m} hc :=
    fun p hp => IsCOFE.lbcompl_ne hn _ _ (fun q hq => hc succᵢ q (hn.succ_lt q hq) p hp)

@[indexed, rocq_alias laterO_map]
def laterMap [OFEᵢ A] [OFEᵢ B] (f : A -n> B) : Later A -n> Later B := by
  refine ⟨fun x => Later.next (f x.car), ⟨?_⟩⟩
  rintro _ ⟨⟩ ⟨⟩ H; simp_all only [Dist]
  intros m Hlt; exact f.ne.ne (H m Hlt)
#rocq_ignore later_map "Underlying map of laterMap"

#rocq_ignore later_map_ne "Implicit in type of laterMap"
#rocq_ignore later_map_ne' "Implicit in type of laterMap"
#rocq_ignore later_map_proper "Derived from nonexpansivity"

@[simp, rocq_alias later_map_Next]
theorem laterMap_next [OFEᵢ A] [OFEᵢ B] (f : A -n> B) (x : A) :
    laterMapᵢ f (Later.next x) = Later.next (f x) := rfl

@[rocq_alias later_map_id]
theorem laterMap_id [OFEᵢ A] (x : Later A) : laterMapᵢ Hom.id x = x := rfl

@[rocq_alias later_map_compose]
theorem laterMap_compose [OFEᵢ A] [OFEᵢ B] [OFEᵢ C] (f : A -n> B) (g : B -n> C) (x : Later A) :
    laterMapᵢ (g.comp f) x = laterMapᵢ g (laterMapᵢ f x) := rfl

@[rocq_alias later_map_ext]
theorem laterMap_ext [OFEᵢ A] [OFEᵢ B] {f g : A -n> B} (x : Later A) (h : ∀ a, f a = g a) :
    laterMapᵢ f x = laterMapᵢ g x := congrArg Later.next (h x.car)

@[rocq_alias laterO_map_contractive]
instance laterMap_contractive [OFEᵢ A] [OFEᵢ B] :
    Contractiveᵢ (laterMapᵢ : (A -n> B) → Later A -n> Later B) where
  distLater_dist H x m hm := H m hm x.car

end Later

section LaterOF
open COFE

abbrev LaterOF (F : OFunctorPreᵢ) : OFunctorPreᵢ :=
  fun A B _ _ => Later (F A B)

variable (F : OFunctorPreᵢ)

@[rocq_alias laterOF]
instance instOFunctorLater [OFunctorᵢ F] : OFunctorᵢ (LaterOF F) where
  ofe := _
  map f g := laterMapᵢ (OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ _ := (OFunctor.map_ne.ne Hx Hy _).lt
  map_id x := congrArg Later.next (OFunctor.map_id x.car)
  map_comp f g f' g' x := congrArg Later.next (OFunctor.map_comp f g f' g' x.car)

@[rocq_alias laterOF_contractive]
instance instOFunctorContractiveLater [OFunctorᵢ F] : OFunctorContractiveᵢ (LaterOF F) where
  map_contractive.1 H _ _ hlt :=
    OFunctor.map_ne.ne (DistLater.dist_lt H hlt).1 (DistLater.dist_lt H hlt).2 _

end LaterOF

section IsoCofe
open OFE COFE

variable {α β : Type _}

@[reducible, rocq_alias iso_cofe_subtype]
def isoCofeSubtype [COFEᵢ α] [OFEᵢ β] (P : α → Prop) (f : ∀ x, P x → β) (g : β -n> α)
    (g_dist : ∀ (n) (y1 y2 : β), y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
    (gf : ∀ x (Hx : P x), g (f x Hx) = x)
    (Hlimit : ∀ c : Chainᵢ β, P (COFE.compl (c.map g)))
    (Hblimit : ∀ {n} (hn : SIdx.Limit n) (c : BChainᵢ β n),
      P (IsCOFE.lbcompl hn (c.map g))) : IsCOFEᵢ β where
  compl c := f (COFE.compl (c.map g)) (Hlimit c)
  conv_compl {n} {c} := by
    refine (g_dist n _ _).mpr ?_
    rw [gf]; exact COFE.conv_compl
  lbcompl hn c := f (IsCOFE.lbcompl hn (c.map g)) (Hblimit hn c)
  conv_lbcompl hn c m hm := by
    refine (g_dist m _ _).mpr ?_
    rw [gf]; exact IsCOFE.conv_lbcompl hn (c.map g) hm
  lbcompl_ne hn c1 c2 m hc := by
    refine (g_dist m _ _).mpr ?_
    rw [gf, gf]
    exact IsCOFE.lbcompl_ne hn _ _ fun p hp => g.ne.ne (hc p hp)

@[reducible, rocq_alias iso_cofe_subtype']
def isoCofeSubtype' [COFEᵢ α] [OFEᵢ β] (P : α → Prop) (f : ∀ x, P x → β) (g : β -n> α)
    (Pg : ∀ y, P (g y))
    (g_dist : ∀ (n) (y1 y2 : β), y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
    (gf : ∀ x (Hx : P x), g (f x Hx) = x) (Hlimit : LimitPreservingᵢ P) : IsCOFEᵢ β :=
  isoCofeSubtype P f g g_dist gf (fun c => Hlimit.compl (c.map g) fun n => Pg (c n))
    (fun hn c => Hlimit.lbcompl hn (c.map g) fun m hm => Pg (c.bchain m hm))

@[reducible, rocq_alias iso_cofe]
def isoCofe [COFEᵢ α] [OFEᵢ β] (f : α → β) (g : β -n> α)
    (g_dist : ∀ (n) (y1 y2 : β), y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
    (gf : ∀ x, g (f x) = x) : IsCOFEᵢ β :=
  isoCofeSubtype (fun _ => True) (fun x _ => f x) g g_dist (fun x _ => gf x)
    (fun _ => trivial) (fun _ _ => trivial)

#rocq_ignore iso_ofe_mixin "OFE from an injection; Lean builds OFE instances directly (cf. `OfeMixin`)."

@[reducible, rocq_alias sig_cofe]
def sigCofe [COFEᵢ α] {P : α → Prop} (H : LimitPreservingᵢ P) : IsCOFEᵢ (Subtype P) :=
  isoCofeSubtype' P (fun x h => ⟨x, h⟩) ⟨Subtype.val, inferInstance⟩ (fun y => y.property)
    (fun _ _ _ => Iff.rfl) (fun _ _ => rfl) H

@[rocq_alias ofe_iso_ofe_mixin]
instance [OFEᵢ α] [OFEᵢ β] : OFEᵢ (Isoᵢ α β) where
  dist n I1 I2 := I1.hom ≡{n}≡ I2.hom ∧ I1.inv ≡{n}≡ I2.inv
  dist_eqv := ⟨fun _ => ⟨.rfl, .rfl⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩,
    fun ⟨a1, a2⟩ ⟨b1, b2⟩ => ⟨a1.trans b1, a2.trans b2⟩⟩
  eq_dist' {_ _} := ⟨fun h _ => h ▸ ⟨.rfl, .rfl⟩,
    fun H => Iso.ext (eq_dist.mpr fun n => (H n).1) (eq_dist.mpr fun n => (H n).2)⟩
  dist_lt h hlt := ⟨h.1.lt hlt, h.2.lt hlt⟩
#rocq_ignore ofe_iso_dist "Local Dist instance; folded into Lean's OFE (Iso α β) instance."
#rocq_ignore ofe_iso_equiv "Local Equiv instance; folded into Lean's OFE (Iso α β) instance."

@[rocq_alias ofe_iso_cofe]
instance ofeIsoCofe [SIdxFinite SI] [COFEᵢ α] [COFEᵢ β] : IsCOFEᵢ (Isoᵢ α β) := by
  refine isoCofeSubtype'
    (P := fun I : (α -n> β) × (β -n> α) => (∀ y, I.1 (I.2 y) = y) ∧ (∀ x, I.2 (I.1 x) = x))
    (fun I HI => ⟨I.1, I.2, fun {x} => HI.1 x, fun {x} => HI.2 x⟩)
    ⟨fun I => (I.hom, I.inv), ⟨fun _ _ _ h => h⟩⟩
    (fun I => ⟨fun _ => I.hom_inv, fun _ => I.inv_hom⟩)
    (fun _ _ _ => Iff.rfl) (fun _ _ => rfl) ?_
  refine LimitPreserving.and ?_ ?_
  · refine LimitPreserving.forall _ fun y => ?_
    refine LimitPreserving.equiv
      ⟨fun I : (α -n> β) × (β -n> α) => I.1 (I.2 y), ⟨fun _ I I' h => ?_⟩⟩ (Hom.const y)
    exact (h.1 _).trans (I'.1.ne.ne (h.2 y))
  · refine LimitPreserving.forall _ fun x => ?_
    refine LimitPreserving.equiv
      ⟨fun I : (α -n> β) × (β -n> α) => I.2 (I.1 x), ⟨fun _ I I' h => ?_⟩⟩ (Hom.const x)
    exact (h.2 _).trans (I'.2.ne.ne (h.1 x))

@[rocq_alias iso_ofe_cong]
def isoOfeCong (F : OFunctorPreᵢ) [OFunctorᵢ F] {A B : Type _} [COFEᵢ A] [COFEᵢ B] (I : Isoᵢ A B) :
    Isoᵢ (F A A) (F B B) where
  hom := OFunctor.map I.inv I.hom
  inv := OFunctor.map I.hom I.inv
  hom_inv {x} := by
    rw [← OFunctor.map_comp I.hom I.inv I.inv I.hom x,
      show I.hom.comp I.inv = Hom.id from Hom.ext (funext fun _ => I.hom_inv), OFunctor.map_id]
  inv_hom {x} := by
    rw [← OFunctor.map_comp I.inv I.hom I.hom I.inv x,
      show I.inv.comp I.hom = Hom.id from Hom.ext (funext fun _ => I.inv_hom), OFunctor.map_id]

@[rocq_alias iso_ofe_cong_ne]
instance isoOfeCong_ne (F : OFunctorPreᵢ) [OFunctorᵢ F] {A B : Type _} [COFEᵢ A] [COFEᵢ B] :
    NonExpansiveᵢ (isoOfeCong F (A := A) (B := B)) where
  ne _ _ _ h := ⟨OFunctor.map_ne.ne h.2 h.1, OFunctor.map_ne.ne h.1 h.2⟩

@[rocq_alias iso_ofe_cong_contractive]
instance isoOfeCong_contractive (F : OFunctorPreᵢ) [OFunctorContractiveᵢ F] {A B : Type _}
    [COFEᵢ A] [COFEᵢ B] : Contractiveᵢ (isoOfeCong F (A := A) (B := B)) where
  distLater_dist H :=
    ⟨fun x => OFunctorContractive.map_distLater (fun m hm => (H m hm).2) (fun m hm => (H m hm).1) x,
     fun x => OFunctorContractive.map_distLater (fun m hm => (H m hm).1) (fun m hm => (H m hm).2) x⟩

end IsoCofe

theorem OFE.cast_dist {n} [Iα : OFEᵢ α] [Iβ : OFEᵢ β] {x y : α}
    (Ht : α = β) (HIt : Iα = Ht ▸ Iβ) (H : x ≡{n}≡ y) :
    (Ht ▸ x) ≡{n}≡ (Ht ▸ y) := by
  subst Ht; subst HIt; exact H

end Iris
