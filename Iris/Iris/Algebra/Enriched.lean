/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko
-/
module

public import Iris.Algebra.OFE

/-!
# Transfinite solver for recursive domain equations

## What breaks with transfinite COFEs
Consider solving a domain equation over (ω + ω)-COFEs.
When we construct it, we have a problem at stage ω.
Naturally, we would ask for a categorical limit of the tower constructed before.
However, (ω + ω)-COFEs (and COFEs with step-indexing above ω in general) don't have general limits.
E.g., if we consider f, g : X → Y, and consider a set-like equalizer
E = { x : X | f x = g x } with an obvious embedding e : E → X,
we cannot show that it's a COFE, because there is no guarantee that E has limits of bounded chains,
as non-expansive maps preserve only limits of full chains.

There are two solutions to this problem:
- Consider a subcategory of COFEs with "continuous" maps (that preserve bounded limits);
- Put additional conditions on tower diagrams, for which we can construct categorical limits.

We go with the latter.

## What we do to restore it
A tower over a limit ordinal λ is a family of COFEs Xᵢ for i < λ with embeddings e : Xᵢ → Xⱼ and
projections p : Xⱼ → Xᵢ for i < j, closed under composition, such that p ∘ e = id and
e ∘ p ≡{m}≡ id for m < i.

We say that a (C)OFE is determined at a limit ordinal λ if x ≡{m}≡ y for all m < λ implies x = y.
This is stronger than ≡{m}≡ coinciding with = for m ≥ λ, since ≡{λ}≡ need not be
the intersection of ≡{m}≡ for m < λ.

We make the following observations:
- For a tower over a limit ordinal λ with all stages determined at λ,
  COFEs have its limit, and the limit is determined at λ as well.
- To keep stages determined, it is enough to truncate successor stages at the next limit ordinal.
  For n : SI, we define b(n) to be the least limit ordinal ≥ n.
  The truncation Tₙ(A) is a retract of A that agrees with A below b(n) and is determined at b(n):
  there are q : A → Tₙ(A) and r : Tₙ(A) → A with q ∘ r = id and r ∘ q ≡{m}≡ id for m < b(n).
  For COFEs, Tₙ(A) picks a representative of each class of A modulo agreement below b(n).

The invariant of the construction is that every stage Xᵢ is determined at b(i + 1),
the first limit above i. It implies that the stages below a limit λ are determined at λ.
Limit stages preserve it (the limit over λ is determined at λ, hence at b(λ + 1)).

The full solver then builds the solution as:
```
X₀ = 1
Xₙ₊₁ = Tₙ₊₁(F(Xₙ, Xₙ))
Xₖ = lim Xᵢ            (where k is a limit ordinal, and i ranges over [0..k))
```

Each stage also carries fold : F(Xᵢ, Xᵢ) → Xᵢ and unfold : Xᵢ → F(Xᵢ, Xᵢ) with fold ∘ unfold = id
and unfold ∘ fold ≡{m}≡ id for m < i, which are compatible with the projections.
We call a tower with these maps a partial solution.
So, morally, we gradually solve the equation over ω-COFEs, (ω + ω)-COFEs, and so on.
The final solution is lim Xᵢ, where the diagram ranges over all SI.

## Technicalities
- Instead of indexing constructions by SI, we index them by down-sets of SI
  (which morally live in the successor of SI, when considered as a limit ordinal),
  which allows us to unify intermediate limit constructions with the final one.
- Both Rocq and Lean lack inductive-recursive types, which would allow us to define the stages
  by recursion while proving them coherent (the construction at step j, restricted to indices
  ≤ i, must be exactly the construction at step i, which is a statement about the function
  being defined).
  Instead, we define the canonical extension of a partial solution below i (building Xᵢ with
  its embeddings, projections, fold, and unfold by the cases above), call a stage canonical
  if it extends canonical earlier stages, show that canonical stages are unique and coherent,
  and glue them into the full solution.
- Assuming classical axioms, one can provide truncation for any COFE over any SI,
  so the assumptions are exactly as for the America-Rutten solver:
  F(1,1) is inhabited, F is locally contractive.
- Over SI = ℕ, the only truncation is identity, so the construction can be shown equal
  to the America-Rutten solver of standard Iris.
- Without assuming classical axioms, it is possible to provide truncation for many functors
  (e.g., polynomial ones, exponential, UPred).
- We first solve the equation in the enriched setting (enrichment is in COFE), and
  then show that COFEs are self-enriched in COFESolver.lean.
-/

@[expose] public section

universe u v w

namespace Iris.Enriched

open OFE

variable {SI : Type w} [SIdx SI]
local stepindex SI

structure Site where
  mem : SI → Prop
  down : ∀ {a b : SI}, a ≤ b → mem b → mem a
  [dec : ∀ m, Decidable (mem m)]

namespace Site

variable {P : Site}

def univ : Site := ⟨fun _ => True, fun _ _ => trivial⟩

abbrev below (α : SI) : Site := ⟨fun m => m < α, fun h h' => SIdx.le_lt_trans h h'⟩

theorem lt_of_not_mem {m n : SI} (hm : ¬ P.mem m) (hn : P.mem n) : n < m := by
  rcases SIdx.lt_trichotomyT m n with h | rfl | h
  · exact absurd (P.down (SIdx.lt_le_incl h) hn) hm
  · exact absurd hn hm
  · exact h

instance : LE Site := ⟨fun P Q => ∀ m, P.mem m → Q.mem m⟩

theorem below_le_of_mem {γ : SI} (h : P.mem γ) : below γ ≤ P :=
  fun _ hm => P.down (SIdx.lt_le_incl hm) h

theorem below_le_below {γ δ : SI} (h : γ ≤ δ) : below γ ≤ below δ :=
  fun _ hm => SIdx.lt_le_trans hm h

structure Chain (A : Type v) [OFE A] (P : Site) where
  val : ∀ β, P.mem β → A
  cauchy : ∀ {m p} (hm : P.mem m) (hp : P.mem p), m ≤ p → val p hp ≡{m}≡ val m hm

def IsLimit (P : Site) : Prop := P.mem 0 ∧ ∀ {n}, P.mem n → ∃ m, n < m ∧ P.mem m

theorem IsLimit.succ_mem (hP : P.IsLimit) {k : SI} (hk : P.mem k) : P.mem (succᵢ k) := by
  obtain ⟨m, h1, h2⟩ := hP.2 hk
  exact P.down (SIdx.le_succ_l.mpr h1) h2

theorem below_isLimit {t : SI} (hl : SIdx.Limit t) : (below t).IsLimit :=
  ⟨hl.limit_lt_0, fun {n} h => ⟨succᵢ n, SIdx.lt_succ_self n, hl.succ_lt _ h⟩⟩

theorem univ_isLimit : univ.IsLimit :=
  ⟨trivial, fun {n} _ => ⟨succᵢ n, SIdx.lt_succ_self n, trivial⟩⟩

end Site

@[indexed SI]
class EnrichedCat (Obj : Type u) where
  Hom : Obj → Obj → Type v
  [cofe : ∀ a b, COFE (Hom a b)]
  id : ∀ a, Hom a a
  comp : ∀ {a b c : Obj}, Hom b c → Hom a b → Hom a c
  comp_ne : ∀ {a b c : Obj} {n : SI} {g g' : Hom b c} {f f' : Hom a b},
    OFE.Dist n g g' → OFE.Dist n f f' → OFE.Dist n (comp g f) (comp g' f')
  id_comp : ∀ {a b : Obj} (f : Hom a b), comp (id b) f = f
  comp_id : ∀ {a b : Obj} (f : Hom a b), comp f (id a) = f
  assoc : ∀ {a b c d : Obj} (h : Hom c d) (g : Hom b c) (f : Hom a b),
    comp (comp h g) f = comp h (comp g f)

attribute [reducible, instance] EnrichedCat.cofe
attribute [simp] EnrichedCat.id_comp EnrichedCat.comp_id EnrichedCat.assoc

export EnrichedCat (Hom)

infixr:80 " ⊚ " => EnrichedCat.comp

scoped notation:30 a:31 " ⟶ " b:31 => EnrichedCat.Hom stepindex% a b

open Lean PrettyPrinter in
@[scoped app_unexpander EnrichedCat.Hom]
meta def unexpandHom : Unexpander
  | `($_ $_ $a $b) => `($a ⟶ $b)
  | _ => throw ()

section EnrichedCat

variable {Obj : Type u} [EnrichedCat Obj] {a b c : Obj}

theorem comp_dist_l {n : SI} {g g' : b ⟶ c} (h : g ≡{n}≡ g') (f : a ⟶ b) :
    g ⊚ f ≡{n}≡ g' ⊚ f :=
  EnrichedCat.comp_ne h .rfl

theorem comp_dist_r {n : SI} (g : b ⟶ c) {f f' : a ⟶ b} (h : f ≡{n}≡ f') :
    g ⊚ f ≡{n}≡ g ⊚ f' :=
  EnrichedCat.comp_ne .rfl h

end EnrichedCat

@[indexed SI]
class EFunctor {Obj : Type u} [EnrichedCat Obj] (F : Obj → Obj → Obj) where
  map : ∀ {a a' b b' : Obj}, a' ⟶ a → b ⟶ b' → F a b ⟶ F a' b'
  map_contractive : ∀ {a a' b b' : Obj} {n : SI} {f f' : a' ⟶ a} {g g' : b ⟶ b'},
    OFE.DistLater n (f, g) (f', g') → OFE.Dist n (map f g) (map f' g')
  map_id : ∀ a b, map (EnrichedCat.id a) (EnrichedCat.id b) = EnrichedCat.id (F a b)
  map_comp : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : Obj} (f : a₂ ⟶ a₁) (g : a₃ ⟶ a₂) (f' : b₁ ⟶ b₂)
    (g' : b₂ ⟶ b₃), map (f ⊚ g) (g' ⊚ f') = map g g' ⊚ map f f'

theorem map_dist {Obj : Type u} [EnrichedCat Obj] (F : Obj → Obj → Obj) [EFunctor F]
    {a a' b b' : Obj} {n : SI} {f f' : a' ⟶ a} {g g' : b ⟶ b'} (hf : f ≡{n}≡ f')
    (hg : g ≡{n}≡ g') : EFunctor.map (F := F) f g ≡{n}≡ EFunctor.map f' g' :=
  EFunctor.map_contractive fun _ hm => ⟨hf.lt hm, hg.lt hm⟩

structure LimitCut where
  mem : SI → Prop
  zero : mem 0
  unbounded : ∀ {n}, mem n → ∃ m, n < m ∧ mem m
  down : ∀ {a b : SI}, a ≤ b → mem b → mem a

namespace LimitCut

def dist (K : LimitCut) {A : Type _} [OFE A] (x y : A) : Prop := ∀ m, K.mem m → x ≡{m}≡ y

theorem mem_of_finite [SIdxFinite SI] (K : LimitCut) (n : SI) : K.mem n := by
  induction n using (SIdx.lt_wf (I := SI)).induction with
  | _ n ih =>
    rcases SIdxFinite.finite_index n with rfl | ⟨m, rfl⟩
    · exact K.zero
    · obtain ⟨k, hmk, hk⟩ := K.unbounded (ih m (SIdx.lt_succ_self m))
      exact K.down (SIdx.succ_le_of_lt hmk) hk

end LimitCut

def seg (c : SI) : LimitCut where
  mem n := ¬ ∃ l, SIdx.Limit l ∧ c < l ∧ l ≤ n
  zero := fun ⟨l, hl, _, h⟩ => SIdx.limit_0 (SIdx.le_0_r.mp h ▸ hl)
  unbounded {n} h := ⟨succᵢ n, SIdx.lt_succ_self n, fun ⟨l, hl, h1, h2⟩ => by
    rcases SIdx.le_lteq.mp h2 with h2 | rfl
    · exact h ⟨l, hl, h1, SIdx.lt_succ_r.mp h2⟩
    · exact SIdx.limit_S n hl⟩
  down hab h := fun ⟨l, hl, h1, h2⟩ => h ⟨l, hl, h1, SIdx.le_trans h2 hab⟩

theorem mem_seg_of_le {c m : SI} (h : m ≤ c) : (seg c).mem m :=
  fun ⟨_, _, h1, h2⟩ => SIdx.lt_irrefl _ (SIdx.lt_le_trans h1 (SIdx.le_trans h2 h))

theorem mem_seg_mono {a b m : SI} (hab : a ≤ b) (h : (seg a).mem m) : (seg b).mem m :=
  fun ⟨l, hl, h1, h2⟩ => h ⟨l, hl, SIdx.le_lt_trans hab h1, h2⟩

theorem lt_of_mem_seg {n a m : SI} (hl : SIdx.Limit n) (ha : a < n) (hm : (seg a).mem m) :
    m < n :=
  (SIdx.lt_ge_cases n m).resolve_right fun h => hm ⟨n, hl, ha, h⟩

theorem LimitCut.mem_of_mem_seg (K : LimitCut) {c : SI} (hc : K.mem c) :
    ∀ m, (seg c).mem m → K.mem m := by
  intro m
  induction m using SIdx.lt_wf.induction with
  | _ m ih =>
    intro hm
    rcases SIdx.le_total (n := m) (m := c) with h | h
    · exact K.down h hc
    · match SIdx.case m with
      | .inl h0 => exact h0 ▸ K.zero
      | .inr (.inl ⟨k, hk⟩) =>
        subst hk
        obtain ⟨m', h1, h2⟩ :=
          K.unbounded (ih k (SIdx.lt_succ_self k) ((seg c).down SIdx.le_succ_diag_r hm))
        exact K.down (SIdx.le_succ_l.mpr h1) h2
      | .inr (.inr hl) =>
        rcases SIdx.le_lteq.mp h with h | rfl
        · exact absurd ⟨m, hl, h, SIdx.le_refl⟩ hm
        · exact hc

section Determined

variable {Obj : Type u} [EnrichedCat Obj]

abbrev Determined (K : LimitCut) (Y : Obj) : Prop :=
  ∀ {Z : Obj} (g g' : Z ⟶ Y), K.dist g g' → g = g'

theorem Determined.mono {K K' : LimitCut} (h : ∀ m, K.mem m → K'.mem m) {Y : Obj}
    (hY : Determined K Y) : Determined K' Y :=
  fun g g' hg => hY g g' fun m hm => hg m (h m hm)

end Determined

section

variable {Obj : Type u} [EnrichedCat Obj]

variable (Obj) in
structure Tower (P : Site) where
  X {β} : P.mem β → Obj
  emb {β δ} (hβ : P.mem β) (hδ : P.mem δ) : β < δ → X hβ ⟶ X hδ
  proj {β δ} (hβ : P.mem β) (hδ : P.mem δ) : β < δ → X hδ ⟶ X hβ

structure Tower.Lawful {P : Site} (T : Tower Obj P) : Prop where
  proj_comp_emb {β δ} {hβ : P.mem β} {hδ : P.mem δ} (h : β < δ) :
    T.proj hβ hδ h ⊚ T.emb hβ hδ h = EnrichedCat.id _
  emb_comp_proj {β δ} {hβ : P.mem β} {hδ : P.mem δ} (h : β < δ) {m} (hm : m < β) :
    T.emb hβ hδ h ⊚ T.proj hβ hδ h ≡{m}≡ EnrichedCat.id _
  emb_comp_emb {β η δ} {hβ : P.mem β} {hη : P.mem η} {hδ : P.mem δ} (h1 : β < η) (h2 : η < δ) :
    T.emb hη hδ h2 ⊚ T.emb hβ hη h1 = T.emb hβ hδ (SIdx.lt_trans h1 h2)
  proj_comp_proj {β η δ} {hβ : P.mem β} {hη : P.mem η} {hδ : P.mem δ} (h1 : β < η)
    (h2 : η < δ) : T.proj hβ hη h1 ⊚ T.proj hη hδ h2 = T.proj hβ hδ (SIdx.lt_trans h1 h2)
  determined {β} (hβ : P.mem β) : Determined (seg β) (T.X hβ)

namespace Tower

variable {P : Site} (T : Tower Obj P)

def hom {β n : SI} (hβ : P.mem β) (hn : P.mem n) : T.X hn ⟶ T.X hβ :=
  match SIdx.lt_trichotomyT β n with
  | .inl h => T.proj hβ hn h
  | .inr (.inl h) => h ▸ EnrichedCat.id _
  | .inr (.inr h) => T.emb hn hβ h

theorem hom_lt {β n : SI} {hβ : P.mem β} {hn : P.mem n} (h : β < n) :
    T.hom hβ hn = T.proj hβ hn h := by
  unfold hom
  exact match SIdx.lt_trichotomyT β n with
  | .inl _ => rfl
  | .inr (.inl h') => absurd (h' ▸ h) (SIdx.lt_irrefl _)
  | .inr (.inr h') => absurd (SIdx.lt_trans h h') (SIdx.lt_irrefl _)

theorem hom_self {β : SI} {hβ hβ' : P.mem β} : T.hom hβ hβ' = EnrichedCat.id _ := by
  unfold hom
  exact match SIdx.lt_trichotomyT β β with
  | .inl h => absurd h (SIdx.lt_irrefl _)
  | .inr (.inl _) => rfl
  | .inr (.inr h) => absurd h (SIdx.lt_irrefl _)

theorem hom_gt {β n : SI} {hβ : P.mem β} {hn : P.mem n} (h : n < β) :
    T.hom hβ hn = T.emb hn hβ h := by
  unfold hom
  exact match SIdx.lt_trichotomyT β n with
  | .inl h' => absurd (SIdx.lt_trans h h') (SIdx.lt_irrefl _)
  | .inr (.inl h') => absurd (h' ▸ h) (SIdx.lt_irrefl _)
  | .inr (.inr _) => rfl

theorem proj_comp_hom {T : Tower Obj P} (hT : T.Lawful) {β δ n : SI} {hβ : P.mem β}
    {hδ : P.mem δ} {hn : P.mem n} (hlt : β < δ) :
    T.proj hβ hδ hlt ⊚ T.hom hδ hn = T.hom hβ hn := by
  rcases SIdx.lt_trichotomyT δ n with h1 | rfl | h1
  · rw [T.hom_lt h1, T.hom_lt (SIdx.lt_trans hlt h1), hT.proj_comp_proj]
  · rw [T.hom_self, T.hom_lt hlt, EnrichedCat.comp_id]
  · rw [T.hom_gt h1]
    rcases SIdx.lt_trichotomyT β n with h0 | rfl | h0
    · rw [T.hom_lt h0, ← hT.proj_comp_proj (hη := hn) h0 h1, EnrichedCat.assoc,
        hT.proj_comp_emb, EnrichedCat.comp_id]
    · rw [T.hom_self, hT.proj_comp_emb]
    · rw [T.hom_gt h0, ← hT.emb_comp_emb (hη := hβ) h0 hlt, ← EnrichedCat.assoc,
        hT.proj_comp_emb, EnrichedCat.id_comp]

end Tower

end

@[indexed SI]
class HasTowerLimits (Obj : Type u) [EnrichedCat Obj] where
  lim {P : Site} {T : Tower Obj P} : T.Lawful → Obj
  π {P : Site} {T : Tower Obj P} (hT : T.Lawful) {β} (hβ : P.mem β) : lim hT ⟶ T.X hβ
  proj_comp_π {P : Site} {T : Tower Obj P} (hT : T.Lawful) {β δ} {hβ : P.mem β} {hδ : P.mem δ}
    (h : β < δ) : T.proj hβ hδ h ⊚ π hT hδ = π hT hβ
  lift {P : Site} {T : Tower Obj P} (hT : T.Lawful) {Y : Obj}
    (g : ∀ {β} (hβ : P.mem β), Y ⟶ T.X hβ)
    (hg : ∀ {β δ} {hβ : P.mem β} {hδ : P.mem δ} (h : β < δ), T.proj hβ hδ h ⊚ g hδ = g hβ) :
    Y ⟶ lim hT
  π_comp_lift {P : Site} {T : Tower Obj P} (hT : T.Lawful) {Y : Obj}
    (g : ∀ {β} (hβ : P.mem β), Y ⟶ T.X hβ) hg {β} {hβ : P.mem β} :
    π hT hβ ⊚ lift hT g hg = g hβ
  ext_dist {P : Site} {T : Tower Obj P} (hT : T.Lawful) {Y : Obj} {n : SI} {f f' : Y ⟶ lim hT} :
    (∀ {β} (hβ : P.mem β), π hT hβ ⊚ f ≡{n}≡ π hT hβ ⊚ f') → f ≡{n}≡ f'

namespace InvLim

open HasTowerLimits

variable {Obj : Type u} [EnrichedCat Obj] [HasTowerLimits Obj] {P : Site}
  {T : Tower Obj P} (hT : T.Lawful)

def emb {n : SI} (hn : P.mem n) : T.X hn ⟶ lim hT :=
  lift hT (fun hβ => T.hom hβ hn) fun h => Tower.proj_comp_hom hT h

theorem π_comp_emb {β n : SI} {hβ : P.mem β} {hn : P.mem n} :
    π hT hβ ⊚ emb hT hn = T.hom hβ hn :=
  π_comp_lift hT _ _

theorem π_comp_emb_self {n : SI} {hn : P.mem n} : π hT hn ⊚ emb hT hn = EnrichedCat.id _ := by
  rw [π_comp_emb, T.hom_self]

theorem ext {Y : Obj} {g g' : Y ⟶ lim hT}
    (h : ∀ {β} (hβ : P.mem β), π hT hβ ⊚ g = π hT hβ ⊚ g') : g = g' :=
  OFE.eq_dist.mpr fun _ => ext_dist hT fun hβ => .of_eq (h hβ)

theorem emb_comp_π {n : SI} {hn : P.mem n} {m} (hm : m < n) :
    emb hT hn ⊚ π hT hn ≡{m}≡ EnrichedCat.id _ := by
  refine ext_dist hT fun {β} hβ => ?_
  rw [← EnrichedCat.assoc, π_comp_emb, EnrichedCat.comp_id]
  rcases SIdx.lt_trichotomyT β n with h | rfl | h
  · rw [T.hom_lt h, proj_comp_π]
  · rw [T.hom_self, EnrichedCat.id_comp]
  · rw [T.hom_gt h, ← proj_comp_π hT (hδ := hβ) h, ← EnrichedCat.assoc]
    exact (comp_dist_l (hT.emb_comp_proj h hm) _).trans (.of_eq (EnrichedCat.id_comp _))

theorem emb_comp_emb {β δ : SI} {hβ : P.mem β} {hδ : P.mem δ} (hlt : β < δ) :
    emb hT hδ ⊚ T.emb hβ hδ hlt = emb hT hβ := by
  refine ext hT fun {η} hη => ?_
  rw [← EnrichedCat.assoc, π_comp_emb, π_comp_emb]
  rcases SIdx.lt_trichotomyT η β with h | rfl | h
  · rw [T.hom_lt h, T.hom_lt (SIdx.lt_trans h hlt), ← hT.proj_comp_proj (hη := hβ) h hlt,
      EnrichedCat.assoc, hT.proj_comp_emb, EnrichedCat.comp_id]
  · rw [T.hom_self, T.hom_lt hlt, hT.proj_comp_emb]
  · rcases SIdx.lt_trichotomyT η δ with h' | rfl | h'
    · rw [T.hom_gt h, T.hom_lt h', ← hT.emb_comp_emb (hη := hη) h h', ← EnrichedCat.assoc,
        hT.proj_comp_emb, EnrichedCat.id_comp]
    · rw [T.hom_gt h, T.hom_self, EnrichedCat.id_comp]
    · rw [T.hom_gt h, T.hom_gt h', hT.emb_comp_emb hlt h']

end InvLim

@[indexed SI]
class HasTerminal (Obj : Type u) [EnrichedCat Obj] where
  one : Obj
  toOne : ∀ a, a ⟶ one
  toOne_unique : ∀ {a} (f : a ⟶ one), f = toOne a

@[indexed SI]
class HasSeed {Obj : Type u} [EnrichedCat Obj] [HasTerminal Obj] (F : Obj → Obj → Obj) where
  seed : HasTerminal.one SI ⟶ F (HasTerminal.one SI) (HasTerminal.one SI)

@[indexed SI]
class Truncatable {Obj : Type u} [EnrichedCat Obj] (F : Obj → Obj → Obj) where
  trunc {K : LimitCut} {A : Obj} : Determined K A → Obj
  proj {K A} (hA : Determined K A) : F A A ⟶ trunc hA
  rep {K A} (hA : Determined K A) : trunc hA ⟶ F A A
  proj_rep {K A} (hA : Determined K A) : proj hA ⊚ rep hA = EnrichedCat.id _
  rep_proj {K A} (hA : Determined K A) {m} : K.mem m → rep hA ⊚ proj hA ≡{m}≡ EnrichedCat.id _
  determined {K A} (hA : Determined K A) : Determined K (trunc hA)

instance finiteTruncatable [SIdxFinite SI] {Obj : Type u} [EnrichedCat Obj]
    (F : Obj → Obj → Obj) : Truncatable F where
  trunc {_ A} _ := F A A
  proj _ := EnrichedCat.id _
  rep _ := EnrichedCat.id _
  proj_rep _ := EnrichedCat.id_comp _
  rep_proj _ := fun _ => .of_eq (EnrichedCat.id_comp _)
  determined {K} _ _ := fun _ _ hg => OFE.eq_dist.mpr fun n => hg n (K.mem_of_finite n)

section Solver

variable {Obj : Type u} [EnrichedCat Obj]
variable {F : Obj → Obj → Obj} [EFunctor F]

variable (F) in
structure PartialSol (P : Site) extends Tower Obj P where
  fold {β} (hβ : P.mem β) : F (X hβ) (X hβ) ⟶ X hβ
  unfold {β} (hβ : P.mem β) : X hβ ⟶ F (X hβ) (X hβ)

def PartialSol.restrict {P Q : Site} (f : PartialSol F P) (h : Q ≤ P) : PartialSol F Q where
  X hβ := f.X (h _ hβ)
  emb _ _ hlt := f.emb _ _ hlt
  proj _ _ hlt := f.proj _ _ hlt
  fold _ := f.fold _
  unfold _ := f.unfold _

structure Extension {γ : SI} (f : PartialSol F (Site.below γ)) where
  X : Obj
  emb {β} (h : β < γ) : f.X h ⟶ X
  proj {β} (h : β < γ) : X ⟶ f.X h
  fold : F X X ⟶ X
  unfold : X ⟶ F X X

structure Extension.Lawful {γ : SI} {f : PartialSol F (Site.below γ)} (S : Extension f) :
    Prop where
  proj_comp_emb {β} (h : β < γ) : S.proj h ⊚ S.emb h = EnrichedCat.id _
  emb_comp_proj {β} (h : β < γ) {m} (hm : m < β) : S.emb h ⊚ S.proj h ≡{m}≡ EnrichedCat.id _
  emb_comp_emb {β η} (h1 : β < η) (h2 : η < γ) :
    S.emb h2 ⊚ f.emb (SIdx.lt_trans h1 h2) h2 h1 = S.emb (SIdx.lt_trans h1 h2)
  proj_comp_proj {β η} (h1 : β < η) (h2 : η < γ) :
    f.proj (SIdx.lt_trans h1 h2) h2 h1 ⊚ S.proj h2 = S.proj (SIdx.lt_trans h1 h2)
  fold_comp_unfold : S.fold ⊚ S.unfold = EnrichedCat.id _
  unfold_comp_fold {m} (hm : m < γ) : S.unfold ⊚ S.fold ≡{m}≡ EnrichedCat.id _
  proj_comp_fold {β} (h : β < γ) :
    S.proj h ⊚ S.fold = f.fold h ⊚ EFunctor.map (S.emb h) (S.proj h)
  determined : Determined (seg γ) S.X

namespace PartialSol

variable {P : Site} (f : PartialSol F P)

def topAt {δ : SI} (hδ : P.mem δ) : Extension (f.restrict (Site.below_le_of_mem hδ)) where
  X := f.X hδ
  emb h := f.emb _ hδ h
  proj h := f.proj _ hδ h
  fold := f.fold hδ
  unfold := f.unfold hδ

structure Lawful : Prop extends tower : f.toTower.Lawful where
  fold_comp_unfold {β} {hβ : P.mem β} : f.fold hβ ⊚ f.unfold hβ = EnrichedCat.id _
  unfold_comp_fold {β} {hβ : P.mem β} {m} (hm : m < β) :
    f.unfold hβ ⊚ f.fold hβ ≡{m}≡ EnrichedCat.id _
  proj_comp_fold {β δ} {hβ : P.mem β} {hδ : P.mem δ} (h : β < δ) :
    f.proj hβ hδ h ⊚ f.fold hδ = f.fold hβ ⊚ EFunctor.map (f.emb hβ hδ h) (f.proj hβ hδ h)

end PartialSol

namespace PartialSol.Lawful

variable {P : Site} {f : PartialSol F P}

theorem of_topAt (H : ∀ {δ} (hδ : P.mem δ), (f.topAt hδ).Lawful) : f.Lawful where
  proj_comp_emb {_ _ _ hδ} h := (H hδ).proj_comp_emb h
  emb_comp_proj {_ _ _ hδ} h _ hm := (H hδ).emb_comp_proj h hm
  emb_comp_emb {_ _ _ _ _ hδ} h1 h2 := (H hδ).emb_comp_emb h1 h2
  proj_comp_proj {_ _ _ _ _ hδ} h1 h2 := (H hδ).proj_comp_proj h1 h2
  determined hβ := (H hβ).determined
  fold_comp_unfold {_ hβ} := (H hβ).fold_comp_unfold
  unfold_comp_fold {_ hβ} _ hm := (H hβ).unfold_comp_fold hm
  proj_comp_fold {_ _ _ hδ} h := (H hδ).proj_comp_fold h

variable (hf : f.Lawful)
include hf

theorem topAt {δ : SI} (hδ : P.mem δ) : (f.topAt hδ).Lawful where
  proj_comp_emb h := hf.proj_comp_emb h
  emb_comp_proj h _ hm := hf.emb_comp_proj h hm
  emb_comp_emb h1 h2 := hf.emb_comp_emb h1 h2
  proj_comp_proj h1 h2 := hf.proj_comp_proj h1 h2
  fold_comp_unfold := hf.fold_comp_unfold
  unfold_comp_fold hm := hf.unfold_comp_fold hm
  proj_comp_fold h := hf.proj_comp_fold h
  determined := hf.determined hδ

theorem restrict {Q : Site} (h : Q ≤ P) : (f.restrict h).Lawful :=
  of_topAt fun hδ => hf.topAt (h _ hδ)

theorem hom_comp_hom {a b c : SI} {ha : P.mem a} {hb : P.mem b} {hc : P.mem c} (hab : a ≤ b)
    (hbc : b ≤ c) : f.hom ha hb ⊚ f.hom hb hc = f.hom ha hc := by
  rcases SIdx.le_lteq.mp hab with hab | rfl
  · rcases SIdx.le_lteq.mp hbc with hbc | rfl
    · rw [f.hom_lt hab, f.hom_lt hbc, f.hom_lt (SIdx.lt_trans hab hbc)]
      exact hf.proj_comp_proj hab hbc
    · rw [f.hom_self, EnrichedCat.comp_id]
  · rw [f.hom_self, EnrichedCat.id_comp]

theorem hom_comp_hom_of_le {a c : SI} {ha : P.mem a} {hc : P.mem c} (hac : a ≤ c) :
    f.hom ha hc ⊚ f.hom hc ha = EnrichedCat.id _ := by
  rcases SIdx.le_lteq.mp hac with h | rfl
  · rw [f.hom_lt h, f.hom_gt h]; exact hf.proj_comp_emb h
  · rw [f.hom_self, EnrichedCat.id_comp]

theorem hom_comp_hom_dist {a c : SI} {ha : P.mem a} {hc : P.mem c} (hac : a ≤ c) {m}
    (hm : m < a) : f.hom hc ha ⊚ f.hom ha hc ≡{m}≡ EnrichedCat.id _ := by
  rcases SIdx.le_lteq.mp hac with h | rfl
  · rw [f.hom_lt h, f.hom_gt h]; exact hf.emb_comp_proj h hm
  · rw [f.hom_self, EnrichedCat.id_comp]

theorem hom_comp_emb {a b c : SI} {ha : P.mem a} {hb : P.mem b} {hc : P.mem c} (hab : a < b)
    (hbc : b ≤ c) : f.hom hc hb ⊚ f.emb ha hb hab = f.hom hc ha := by
  rcases SIdx.le_lteq.mp hbc with h | rfl
  · rw [f.hom_gt h, f.hom_gt (SIdx.lt_trans hab h)]
    exact hf.emb_comp_emb hab h
  · rw [f.hom_self, EnrichedCat.id_comp, f.hom_gt hab]

theorem hom_comp_fold {a c : SI} {ha : P.mem a} {hc : P.mem c} (hac : a ≤ c) :
    f.hom ha hc ⊚ f.fold hc = f.fold ha ⊚ EFunctor.map (f.hom hc ha) (f.hom ha hc) := by
  rcases SIdx.le_lteq.mp hac with h | rfl
  · rw [f.hom_lt h, f.hom_gt h]; exact hf.proj_comp_fold h
  · simp only [f.hom_self, EFunctor.map_id, EnrichedCat.id_comp, EnrichedCat.comp_id]

theorem map_comp_unfold {a c : SI} {ha : P.mem a} {hc : P.mem c} (hac : a ≤ c) {m}
    (hm : m < a) :
    EFunctor.map (f.hom hc ha) (f.hom ha hc) ⊚ f.unfold hc ≡{m}≡ f.unfold ha ⊚ f.hom ha hc :=
  calc
    _ = EnrichedCat.id _ ⊚ (EFunctor.map (f.hom hc ha) (f.hom ha hc) ⊚ f.unfold hc) :=
      (EnrichedCat.id_comp _).symm
    _ ≡{m}≡ (f.unfold ha ⊚ f.fold ha) ⊚
        (EFunctor.map (f.hom hc ha) (f.hom ha hc) ⊚ f.unfold hc) :=
      comp_dist_l (hf.unfold_comp_fold hm).symm _
    _ = f.unfold ha ⊚ f.hom ha hc := by
      rw [EnrichedCat.assoc, ← EnrichedCat.assoc (f.fold ha), ← hf.hom_comp_fold hac,
        EnrichedCat.assoc, hf.fold_comp_unfold, EnrichedCat.comp_id]

end PartialSol.Lawful

section Zero

variable [HasTerminal Obj] [HasSeed F]

open HasTerminal in
def zeroTop {γ : SI} (h0 : γ = 0) (f : PartialSol F (Site.below γ)) : Extension f where
  X := one SI
  emb {β} h := absurd (h0 ▸ h) (SIdx.not_lt_zero β)
  proj {β} h := absurd (h0 ▸ h) (SIdx.not_lt_zero β)
  fold := toOne _
  unfold := HasSeed.seed (F := F)

theorem zeroTop_lawful {γ : SI} (h0 : γ = 0) (f : PartialSol F (Site.below γ)) :
    (zeroTop h0 f).Lawful where
  proj_comp_emb {β} h := absurd (h0 ▸ h) (SIdx.not_lt_zero β)
  emb_comp_proj {β} h := absurd (h0 ▸ h) (SIdx.not_lt_zero β)
  emb_comp_emb {_ η} _ h2 := absurd (h0 ▸ h2) (SIdx.not_lt_zero η)
  proj_comp_proj {_ η} _ h2 := absurd (h0 ▸ h2) (SIdx.not_lt_zero η)
  fold_comp_unfold := (HasTerminal.toOne_unique _).trans (HasTerminal.toOne_unique _).symm
  unfold_comp_fold {m} hm := absurd (h0 ▸ hm) (SIdx.not_lt_zero m)
  proj_comp_fold {β} h := absurd (h0 ▸ h) (SIdx.not_lt_zero β)
  determined g g' _ := (HasTerminal.toOne_unique g).trans (HasTerminal.toOne_unique g').symm

end Zero

section Succ

variable [Truncatable F]
open Truncatable

variable {γ m : SI} (hm : γ = succᵢ m)

include hm in
theorem le_of_below_succ {β : SI} (h : β < γ) : β ≤ m := SIdx.lt_succ_r.mp (hm ▸ h)

include hm in
theorem lt_of_eq_succ : m < γ := hm ▸ SIdx.lt_succ_self m

variable {f : PartialSol F (Site.below γ)} (hf : f.Lawful)

abbrev succStage : Obj := trunc (F := F) (hf.determined (lt_of_eq_succ hm))

def succEmb : f.X (lt_of_eq_succ hm) ⟶ succStage hm hf :=
  proj (F := F) (hf.determined _) ⊚ f.unfold (lt_of_eq_succ hm)

def succProj : succStage hm hf ⟶ f.X (lt_of_eq_succ hm) :=
  f.fold (lt_of_eq_succ hm) ⊚ rep (F := F) (hf.determined _)

def succTop : Extension f where
  X := succStage hm hf
  emb h := succEmb hm hf ⊚ f.hom (lt_of_eq_succ hm) h
  proj h := f.hom h (lt_of_eq_succ hm) ⊚ succProj hm hf
  fold := proj (F := F) (hf.determined _) ⊚ EFunctor.map (succEmb hm hf) (succProj hm hf)
  unfold := EFunctor.map (succProj hm hf) (succEmb hm hf) ⊚ rep (F := F) (hf.determined _)

theorem succProj_comp_proj {n : SI} (hn : (seg m).mem n) :
    succProj hm hf ⊚ proj (F := F) (hf.determined _) ≡{n}≡ f.fold (lt_of_eq_succ hm) := by
  rw [succProj, EnrichedCat.assoc]
  exact (comp_dist_r _ (rep_proj (F := F) (hf.determined _) hn)).trans
    (.of_eq (EnrichedCat.comp_id _))

theorem succProj_comp_succEmb : succProj hm hf ⊚ succEmb hm hf = EnrichedCat.id _ :=
  hf.determined (lt_of_eq_succ hm) _ _ fun n hn => by
    rw [succEmb, ← EnrichedCat.assoc]
    exact (comp_dist_l (succProj_comp_proj hm hf hn) _).trans (.of_eq hf.fold_comp_unfold)

theorem succEmb_comp_succProj {k} (hk : k < m) :
    succEmb hm hf ⊚ succProj hm hf ≡{k}≡ EnrichedCat.id _ := by
  rw [succEmb, succProj, EnrichedCat.assoc, ← EnrichedCat.assoc (f.unfold _)]
  refine (comp_dist_r _ (comp_dist_l (hf.unfold_comp_fold hk) _)).trans (.of_eq ?_)
  rw [EnrichedCat.id_comp, proj_rep (F := F) (hf.determined _)]

theorem succTop_lawful : (succTop hm hf).Lawful where
  proj_comp_emb h := by
    simp only [succTop, EnrichedCat.assoc]
    rw [← EnrichedCat.assoc (succProj hm hf), succProj_comp_succEmb hm hf, EnrichedCat.id_comp]
    exact hf.hom_comp_hom_of_le (le_of_below_succ hm h)
  emb_comp_proj h _ hk := by
    simp only [succTop, EnrichedCat.assoc]
    rw [← EnrichedCat.assoc (f.hom (lt_of_eq_succ hm) h)]
    refine (comp_dist_r _ (comp_dist_l
      (hf.hom_comp_hom_dist (le_of_below_succ hm h) hk) _)).trans ?_
    rw [EnrichedCat.id_comp]
    exact succEmb_comp_succProj hm hf (SIdx.lt_le_trans hk (le_of_below_succ hm h))
  emb_comp_emb h1 h2 := by
    simp only [succTop, EnrichedCat.assoc]
    rw [hf.hom_comp_emb h1 (le_of_below_succ hm h2)]
  proj_comp_proj h1 h2 := by
    simp only [succTop]
    rw [← EnrichedCat.assoc, ← f.hom_lt h1,
      hf.hom_comp_hom (SIdx.lt_le_incl h1) (le_of_below_succ hm h2)]
  fold_comp_unfold := by
    simp only [succTop, EnrichedCat.assoc]
    rw [← EnrichedCat.assoc (EFunctor.map _ _), ← EFunctor.map_comp, succProj_comp_succEmb hm hf,
      EFunctor.map_id, EnrichedCat.id_comp, proj_rep (F := F) (hf.determined _)]
  unfold_comp_fold hk := by
    simp only [succTop, EnrichedCat.assoc]
    rw [← EnrichedCat.assoc (rep (F := F) (hf.determined _))]
    refine (comp_dist_r _ (comp_dist_l
      (rep_proj (F := F) (hf.determined _) (mem_seg_of_le (le_of_below_succ hm hk))) _)).trans ?_
    rw [EnrichedCat.id_comp, ← EFunctor.map_comp, ← EFunctor.map_id]
    exact EFunctor.map_contractive fun j hj =>
      have hj' := SIdx.lt_le_trans hj (le_of_below_succ hm hk)
      ⟨succEmb_comp_succProj hm hf hj', succEmb_comp_succProj hm hf hj'⟩
  proj_comp_fold h := hf.determined h _ _ fun n hn => by
    simp only [succTop, EnrichedCat.assoc]
    rw [← EnrichedCat.assoc (succProj hm hf)]
    refine (comp_dist_r _ (comp_dist_l
      (succProj_comp_proj hm hf (mem_seg_mono (le_of_below_succ hm h) hn)) _)).trans (.of_eq ?_)
    rw [← EnrichedCat.assoc, hf.hom_comp_fold (le_of_below_succ hm h), EnrichedCat.assoc,
      ← EFunctor.map_comp]
  determined := Determined.mono (fun _ hn => mem_seg_mono (SIdx.lt_le_incl (lt_of_eq_succ hm)) hn)
    (determined (F := F) (hf.determined _))

end Succ

section Limit

variable [HasTowerLimits Obj]
open HasTowerLimits

variable {P : Site} (hP : P.IsLimit) (f : PartialSol F P) (hf : f.Lawful)

abbrev limObj : Obj := lim hf.tower

theorem hom_comp_π {c c' : SI} {hc : P.mem c} {hc' : P.mem c'} (h : c ≤ c') :
    f.hom hc hc' ⊚ π hf.tower hc' = π hf.tower hc := by
  rcases SIdx.le_lteq.mp h with h | rfl
  · rw [f.hom_lt h]; exact proj_comp_π hf.tower h
  · rw [f.hom_self, EnrichedCat.id_comp]

theorem emb_comp_hom {c c' : SI} {hc : P.mem c} {hc' : P.mem c'} (h : c ≤ c') :
    InvLim.emb hf.tower hc' ⊚ f.hom hc' hc = InvLim.emb hf.tower hc := by
  rcases SIdx.le_lteq.mp h with h | rfl
  · rw [f.hom_gt h]; exact InvLim.emb_comp_emb hf.tower h
  · rw [f.hom_self, EnrichedCat.comp_id]

theorem limFold_compatible {β δ} {hβ : P.mem β} {hδ : P.mem δ} (h : β < δ) :
    f.proj hβ hδ h ⊚ (f.fold hδ ⊚ EFunctor.map (InvLim.emb hf.tower hδ) (π hf.tower hδ)) =
      f.fold hβ ⊚ EFunctor.map (InvLim.emb hf.tower hβ) (π hf.tower hβ) := by
  rw [← EnrichedCat.assoc, hf.proj_comp_fold, EnrichedCat.assoc, ← EFunctor.map_comp,
    InvLim.emb_comp_emb, proj_comp_π]

def limFold : F (limObj f hf) (limObj f hf) ⟶ limObj f hf :=
  lift hf.tower (fun hc => f.fold hc ⊚ EFunctor.map (InvLim.emb hf.tower hc) (π hf.tower hc))
    (limFold_compatible f hf)

theorem π_comp_limFold {c : SI} {hc : P.mem c} : π hf.tower hc ⊚ limFold f hf =
    f.fold hc ⊚ EFunctor.map (InvLim.emb hf.tower hc) (π hf.tower hc) :=
  π_comp_lift hf.tower _ _

def chainAt {c : SI} (hc : P.mem c) : limObj f hf ⟶ F (limObj f hf) (limObj f hf) :=
  EFunctor.map (π hf.tower hc) (InvLim.emb hf.tower hc) ⊚ f.unfold hc ⊚ π hf.tower hc

theorem chainAt_dist {c c' : SI} {hc : P.mem c} {hc' : P.mem c'} (h : c ≤ c') {m} (hm : m < c) :
    chainAt f hf hc' ≡{m}≡ chainAt f hf hc := by
  calc chainAt f hf hc'
      ≡{m}≡ EFunctor.map (π hf.tower hc') (InvLim.emb hf.tower hc') ⊚
        (EFunctor.map (f.hom hc hc') (f.hom hc' hc) ⊚ (f.unfold hc ⊚ f.hom hc hc')) ⊚
          π hf.tower hc' := comp_dist_r _ (comp_dist_l ?_ _)
    _ = chainAt f hf hc := by
      rw [chainAt, ← hom_comp_π f hf (hc' := hc') h, ← emb_comp_hom f hf (hc' := hc') h,
        EFunctor.map_comp]
      simp only [EnrichedCat.assoc]
  refine .symm ((comp_dist_r _ (hf.map_comp_unfold h hm).symm).trans ?_)
  rw [← EnrichedCat.assoc, ← EFunctor.map_comp]
  refine (comp_dist_l (map_dist F (hf.hom_comp_hom_dist h hm) (hf.hom_comp_hom_dist h hm))
    _).trans ?_
  rw [EFunctor.map_id, EnrichedCat.id_comp]

theorem π_comp_limFold_comp_chainAt {c c' : SI} {hc : P.mem c} {hc' : P.mem c'} (h : c ≤ c') :
    π hf.tower hc ⊚ limFold f hf ⊚ chainAt f hf hc' = π hf.tower hc := by
  rw [← EnrichedCat.assoc, π_comp_limFold]
  simp only [chainAt, EnrichedCat.assoc]
  rw [← EnrichedCat.assoc (EFunctor.map _ _) (EFunctor.map _ _), ← EFunctor.map_comp,
    InvLim.π_comp_emb, InvLim.π_comp_emb, ← EnrichedCat.assoc, ← hf.hom_comp_fold h,
    EnrichedCat.assoc, ← EnrichedCat.assoc (f.fold hc'), hf.fold_comp_unfold, EnrichedCat.id_comp,
    hom_comp_π f hf h]

theorem chainAt_comp_limFold {c : SI} {hc : P.mem c} {m} (hm : m < c) :
    chainAt f hf hc ⊚ limFold f hf ≡{m}≡ EnrichedCat.id _ := by
  simp only [chainAt, EnrichedCat.assoc]
  rw [π_comp_limFold, ← EnrichedCat.assoc (f.unfold hc)]
  refine (comp_dist_r _ (comp_dist_l (hf.unfold_comp_fold hm) _)).trans ?_
  rw [EnrichedCat.id_comp, ← EFunctor.map_comp, ← EFunctor.map_id]
  exact EFunctor.map_contractive fun j hj =>
    ⟨InvLim.emb_comp_π hf.tower (SIdx.lt_trans hj hm),
      InvLim.emb_comp_π hf.tower (SIdx.lt_trans hj hm)⟩

theorem lim_determined {K : LimitCut} (hK : ∀ c, P.mem c → ∀ n, (seg c).mem n → K.mem n) :
    Determined K (limObj f hf) := fun _ _ h =>
  InvLim.ext hf.tower fun hc =>
    hf.determined hc _ _ fun n hn => comp_dist_r _ (h n (hK _ hc n hn))

def limChain : Site.Chain (limObj f hf ⟶ F (limObj f hf) (limObj f hf)) P where
  val _ hk := chainAt f hf (hP.succ_mem hk)
  cauchy {m _} _ _ h := chainAt_dist f hf (SIdx.succ_le_mono.mp h) (SIdx.lt_succ_self m)

variable {u : limObj f hf ⟶ F (limObj f hf) (limObj f hf)}
  (hu : ∀ {k} (hk : P.mem k), u ≡{k}≡ chainAt f hf (hP.succ_mem hk))

include hu in
theorem limFold_comp_unfold : limFold f hf ⊚ u = EnrichedCat.id _ :=
  InvLim.ext hf.tower fun {c} hc => hf.determined hc _ _ fun n hn => by
    rw [EnrichedCat.comp_id, ← EnrichedCat.assoc]
    rcases SIdx.le_total (n := n) (m := c) with hnc | hcn
    · refine (comp_dist_r _ ((hu hc).le hnc)).trans (.of_eq ?_)
      rw [EnrichedCat.assoc]
      exact π_comp_limFold_comp_chainAt f hf SIdx.le_succ_diag_r
    · have hn' := LimitCut.mem_of_mem_seg ⟨P.mem, hP.1, hP.2, P.down⟩ hc n hn
      refine (comp_dist_r _ (hu hn')).trans (.of_eq ?_)
      rw [EnrichedCat.assoc]
      exact π_comp_limFold_comp_chainAt f hf (SIdx.le_trans hcn SIdx.le_succ_diag_r)

include hu in
theorem unfold_comp_limFold {m : SI} (hm : P.mem m) :
    u ⊚ limFold f hf ≡{m}≡ EnrichedCat.id _ :=
  (comp_dist_l (hu hm) _).trans (chainAt_comp_limFold f hf (SIdx.lt_succ_self m))

end Limit

section LimitTop

variable [HasTowerLimits Obj]
variable {γ : SI} (hl : SIdx.Limit γ) (f : PartialSol F (Site.below γ)) (hf : f.Lawful)

def limitTop : Extension f where
  X := limObj f hf
  emb h := InvLim.emb hf.tower h
  proj h := HasTowerLimits.π hf.tower h
  fold := limFold f hf
  unfold := let c := limChain (Site.below_isLimit hl) f hf; IsCOFE.lbcompl hl ⟨c.val, c.cauchy⟩

theorem limitTop_lawful : (limitTop hl f hf).Lawful where
  proj_comp_emb _ := InvLim.π_comp_emb_self hf.tower
  emb_comp_proj _ _ hk := InvLim.emb_comp_π hf.tower hk
  emb_comp_emb h1 _ := InvLim.emb_comp_emb hf.tower h1
  proj_comp_proj h1 _ := HasTowerLimits.proj_comp_π hf.tower h1
  fold_comp_unfold := limFold_comp_unfold (Site.below_isLimit hl) f hf (IsCOFE.conv_lbcompl hl _)
  unfold_comp_fold := unfold_comp_limFold (Site.below_isLimit hl) f hf (IsCOFE.conv_lbcompl hl _)
  proj_comp_fold _ := π_comp_limFold f hf
  determined := lim_determined f hf fun _ hc _ hn => mem_seg_mono (SIdx.lt_le_incl hc) hn

end LimitTop

variable (F) in
structure ClosedSol (γ : SI) where
  below : PartialSol F (Site.below γ)
  top : Extension below
  below_lawful : below.Lawful
  top_lawful : top.Lawful

namespace ClosedSol

variable {γ : SI}

def restrict {β : SI} (h : β < γ) (t : ClosedSol F γ) : ClosedSol F β where
  below := t.below.restrict (Site.below_le_below (SIdx.lt_le_incl h))
  top := t.below.topAt h
  below_lawful := t.below_lawful.restrict _
  top_lawful := t.below_lawful.topAt h

end ClosedSol

def Coherent {P : Site} (fam : ∀ γ, P.mem γ → ClosedSol F γ) : Prop :=
  ∀ {γ δ} (hγδ : γ < δ) (hδ : P.mem δ),
    (fam δ hδ).restrict hγδ = fam γ (P.down (SIdx.lt_le_incl hγδ) hδ)

def glue {P : Site} (fam : ∀ γ, P.mem γ → ClosedSol F γ) (hcoh : Coherent fam) :
    PartialSol F P where
  X hβ := (fam _ hβ).top.X
  emb _ hδ hlt := hcoh hlt hδ ▸ (fam _ hδ).top.emb hlt
  proj _ hδ hlt := hcoh hlt hδ ▸ (fam _ hδ).top.proj hlt
  fold hβ := (fam _ hβ).top.fold
  unfold hβ := (fam _ hβ).top.unfold

section Glued

variable {γ : SI} (IH : ∀ β, β < γ → ClosedSol F β) (T : ClosedSol F γ)
  (hT : ∀ (β : SI) (h : β < γ), T.restrict h = IH β h)
include hT

theorem coherent_of_restrict : Coherent (P := Site.below γ) IH := fun {β β'} h hβ' =>
  (congrArg (ClosedSol.restrict h) (hT β' hβ')).symm.trans (hT β (SIdx.lt_trans h hβ'))

def gluedTop : Extension (glue (P := Site.below γ) IH (coherent_of_restrict IH T hT)) where
  X := T.top.X
  emb h := (hT _ h ▸ T.top.emb h : (IH _ h).top.X ⟶ _)
  proj h := (hT _ h ▸ T.top.proj h : _ ⟶ (IH _ h).top.X)
  fold := T.top.fold
  unfold := T.top.unfold

end Glued

theorem gluedTop_lawful {γ : SI} {IH IH' : ∀ β, β < γ → ClosedSol F β} (hIH : IH = IH')
    (T : ClosedSol F γ) {hT : ∀ (β : SI) (h : β < γ), T.restrict h = IH β h}
    {hT' : ∀ (β : SI) (h : β < γ), T.restrict h = IH' β h} (h : (gluedTop IH T hT).Lawful) :
    (gluedTop IH' T hT').Lawful := by
  subst hIH; exact h

theorem glued_congr {γ : SI} {IH IH' : ∀ β, β < γ → ClosedSol F β} (hIH : IH = IH')
    (T : ClosedSol F γ) {hT : ∀ (β : SI) (h : β < γ), T.restrict h = IH β h}
    {hT' : ∀ (β : SI) (h : β < γ), T.restrict h = IH' β h} {hl hl' ht ht'} :
    (⟨glue (P := Site.below γ) IH (coherent_of_restrict IH T hT), gluedTop IH T hT, hl, ht⟩ :
      ClosedSol F γ) =
      ⟨glue (P := Site.below γ) IH' (coherent_of_restrict IH' T hT'), gluedTop IH' T hT', hl',
        ht'⟩ := by
  subst hIH; rfl

theorem glue_lawful {P : Site} (fam : ∀ γ, P.mem γ → ClosedSol F γ) (hcoh : Coherent fam) :
    (glue fam hcoh).Lawful :=
  .of_topAt fun hδ => gluedTop_lawful (IH := fun _ h => (fam _ hδ).restrict h)
    (IH' := fun β h => fam β (P.down (SIdx.lt_le_incl h) hδ))
    (funext fun _ => funext fun h => hcoh h hδ) (fam _ hδ) (hT := fun _ _ => rfl)
    (hT' := fun _ h => hcoh h hδ) (fam _ hδ).top_lawful

section Recursion

variable [HasTerminal Obj] [HasSeed F] [Truncatable F] [HasTowerLimits Obj]

def closeTop (α : SI) (f : PartialSol F (Site.below α)) (hf : f.Lawful) : Extension f :=
  match SIdx.case α with
  | .inl h0 => zeroTop h0 f
  | .inr (.inl ⟨_, hm⟩) => succTop hm hf
  | .inr (.inr hl) => limitTop hl f hf

theorem closeTop_lawful (α : SI) (f : PartialSol F (Site.below α)) (hf : f.Lawful) :
    (closeTop α f hf).Lawful := by
  unfold closeTop
  exact match SIdx.case α with
  | .inl h0 => zeroTop_lawful h0 f
  | .inr (.inl ⟨_, hm⟩) => succTop_lawful hm hf
  | .inr (.inr hl) => limitTop_lawful hl f hf

def zeroPoint (f : PartialSol F (Site.below (0 : SI))) (hf : f.Lawful) :
    HasTerminal.one SI ⟶ (closeTop 0 f hf).X := by
  unfold closeTop
  exact match SIdx.case (0 : SI) with
  | .inl _ => EnrichedCat.id _
  | .inr (.inl ⟨_, hm⟩) => absurd hm.symm SIdx.neq_succ_0
  | .inr (.inr hl) => absurd hl SIdx.limit_0

namespace ClosedSol

variable (F) in
def extend (α : SI) (fam : ∀ γ, γ < α → ClosedSol F γ) (hcoh : Coherent (P := Site.below α) fam) :
    ClosedSol F α :=
  let hg := glue_lawful (P := Site.below α) fam hcoh
  ⟨glue (P := Site.below α) fam hcoh, closeTop α _ hg, hg, closeTop_lawful α _ hg⟩

theorem extend_restrict {α : SI} (fam : ∀ γ, γ < α → ClosedSol F γ)
    (hcoh : Coherent (P := Site.below α) fam) {γ : SI} (hγ : γ < α) :
    (extend F α fam hcoh).restrict hγ = fam γ hγ :=
  glued_congr (IH := fun β h => fam β (SIdx.lt_trans h hγ))
    (IH' := fun _ h => (fam γ hγ).restrict h) (funext fun _ => funext fun h => (hcoh h hγ).symm)
    (fam γ hγ) (hT := fun _ h => hcoh h hγ) (hT' := fun _ _ => rfl)

variable (F) in
def graph (α : SI) : ClosedSol F α → Prop :=
  SIdx.lt_wf.fix
    (C := fun α => ClosedSol F α → Prop)
    (fun α below t => ∃ (fam : ∀ γ, γ < α → ClosedSol F γ) (_ : ∀ γ hγ, below γ hγ (fam γ hγ))
      (hcoh : Coherent (P := Site.below α) fam), t = extend F α fam hcoh)
    α

theorem graph_iff {α : SI} {t : ClosedSol F α} :
    graph F α t ↔ ∃ (fam : ∀ γ, γ < α → ClosedSol F γ) (_ : ∀ γ hγ, graph F γ (fam γ hγ))
      (hcoh : Coherent (P := Site.below α) fam),
      t = extend F α fam hcoh := by
  unfold graph; rw [WellFounded.fix_eq]

theorem graph_unique : ∀ α (t s : ClosedSol F α), graph F α t → graph F α s → t = s := by
  intro α
  induction α using (SIdx.lt_wf (I := SI)).induction with
  | _ α ih =>
    intro t s ht hs
    obtain ⟨tf, htf, _, rfl⟩ := graph_iff.mp ht
    obtain ⟨sf, hsf, _, rfl⟩ := graph_iff.mp hs
    obtain rfl : tf = sf := funext fun γ => funext fun hγ => ih γ hγ _ _ (htf γ hγ) (hsf γ hγ)
    rfl

theorem graph_restrict {γ δ : SI} (hγδ : γ < δ) {t : ClosedSol F δ} {s : ClosedSol F γ}
    (ht : graph F δ t) (hs : graph F γ s) : t.restrict hγδ = s := by
  obtain ⟨fam, hG, hcoh, rfl⟩ := graph_iff.mp ht
  rw [extend_restrict]
  exact graph_unique γ _ s (hG γ hγδ) hs

variable (F) in
def canonical : ∀ α, {t : ClosedSol F α // graph F α t} :=
  SIdx.lt_wf.fix fun α ih =>
    ⟨extend F α (fun γ hγ => (ih γ hγ).1) fun hγδ hδ => graph_restrict hγδ (ih _ hδ).2 (ih _ _).2,
     graph_iff.mpr ⟨_, fun γ hγ => (ih γ hγ).2, _, rfl⟩⟩

variable (F) in
theorem canonical_coherent {P : Site} : Coherent (P := P) fun γ _ => (canonical F γ).1 :=
  fun hγδ _ => graph_restrict hγδ (canonical F _).2 (canonical F _).2

variable (F) in
theorem canonical_eq (α : SI) :
    (canonical F α).1 = extend F α (fun γ _ => (canonical F γ).1) (canonical_coherent F) := by
  unfold canonical
  rw [WellFounded.fix_eq]

end ClosedSol

variable (F)

def globalSol : PartialSol F Site.univ :=
  glue (fun γ _ => (ClosedSol.canonical F γ).1) (ClosedSol.canonical_coherent F)

theorem globalSol_lawful : (globalSol F).Lawful :=
  glue_lawful (fun γ _ => (ClosedSol.canonical F γ).1) (ClosedSol.canonical_coherent F)

abbrev Fix : Obj := limObj (globalSol F) (globalSol_lawful F)

def Fix.fold : F (Fix F) (Fix F) ⟶ Fix F := limFold (globalSol F) (globalSol_lawful F)

def Fix.unfold : Fix F ⟶ F (Fix F) (Fix F) :=
  let c := limChain Site.univ_isLimit (globalSol F) (globalSol_lawful F)
  IsCOFE.compl ⟨fun n => c.val n trivial, fun h => c.cauchy _ _ h⟩

theorem Fix.fold_comp_unfold : Fix.fold F ⊚ Fix.unfold F = EnrichedCat.id _ :=
  limFold_comp_unfold Site.univ_isLimit _ _ fun _ => IsCOFE.conv_compl

theorem Fix.unfold_comp_fold : Fix.unfold F ⊚ Fix.fold F = EnrichedCat.id _ :=
  OFE.eq_dist.mpr fun _ =>
    unfold_comp_limFold Site.univ_isLimit _ _ (fun _ => IsCOFE.conv_compl) trivial

def Fix.point : HasTerminal.one SI ⟶ Fix F :=
  InvLim.emb (globalSol_lawful F).tower (n := 0) trivial ⊚
    (ClosedSol.canonical_eq F 0 ▸ zeroPoint _ _ : _ ⟶ (ClosedSol.canonical F 0).1.top.X)

end Recursion

end Solver

end Iris.Enriched
