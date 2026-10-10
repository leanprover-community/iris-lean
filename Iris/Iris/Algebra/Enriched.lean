/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergei Stepanenko
-/
module

public import Iris.Algebra.OFE

@[expose] public section

universe u v w

namespace Iris.Enriched

open OFE

variable {SI : stepindex (Type w)} [SIdx SI]
local stepindex SI

variable (SI) in
@[indexed]
structure Site where
  mem : SI → Prop
  down : ∀ {a b}, a ≤ b → mem b → mem a
  dec : ∀ m, Decidable (mem m)

attribute [instance] Site.dec

namespace Site

variable {P : Site}

@[reducible, indexed] def univ : Site := ⟨fun _ => True, fun _ _ => trivial, fun _ => inferInstance⟩

@[reducible, indexed] def below (α : SI) : Site :=
  ⟨fun m => m < α, fun h h' => SIdx.le_lt_trans h h', fun _ => inferInstance⟩

theorem lt_of_not_mem {m n} (hm : ¬ P.mem m) (hn : P.mem n) : n < m := by
  rcases SIdx.lt_trichotomyT m n with h | rfl | h
  · exact absurd (P.down (SIdx.lt_le_incl h) hn) hm
  · exact absurd hn hm
  · exact h

instance : LE Site := ⟨fun P Q => ∀ m, P.mem m → Q.mem m⟩

theorem below_le_of_mem {γ} (h : P.mem γ) : below γ ≤ P :=
  fun _ hm => P.down (SIdx.lt_le_incl hm) h

theorem below_le_below {γ δ} (h : γ ≤ δ) : below γ ≤ below δ :=
  fun _ hm => SIdx.lt_le_trans hm h

structure Chain (A : Type v) [OFE A] (P : Site) where
  val : ∀ β, P.mem β → A
  cauchy : ∀ {m p} (hm : P.mem m) (hp : P.mem p), m ≤ p → val p hp ≡{m}≡ val m hm

class HasCompl (P : Site) where
  compl : ∀ {A : Type v} [COFE A] [Inhabited A], Site.Chain A P → A
  conv_compl : ∀ {A : Type v} [COFE A] [Inhabited A] (c : Site.Chain A P) {n}
    (hn : P.mem n), compl c ≡{n}≡ c.val n hn

instance (α) : HasCompl.{v, _} (below α) where
  compl c :=
    match SIdx.case α with
    | .inl _ => default
    | .inr (.inl ⟨β, h⟩) => c.val β h.lt
    | .inr (.inr hl) => IsCOFE.lbcompl hl ⟨c.val, c.cauchy⟩
  conv_compl c n hn :=
    match SIdx.case α with
    | .inl h => absurd (h ▸ hn) (SIdx.not_lt_zero n)
    | .inr (.inl ⟨_, h⟩) => c.cauchy hn _ (h.le_of_lt hn)
    | .inr (.inr hl) => IsCOFE.conv_lbcompl hl _ hn

instance : HasCompl.{v, _} (univ : Site) where
  compl c := COFE.compl ⟨fun n => c.val n trivial, fun h => c.cauchy _ _ h⟩
  conv_compl _ _ _ := COFE.conv_compl

def IsLimit (P : Site) : Prop :=
  P.mem 0 ∧ ∀ {n}, P.mem n → ∃ m, n < m ∧ P.mem m

theorem IsLimit.succ_mem (hP : P.IsLimit) {k sk} (hs : IsSucc k sk) (hk : P.mem k) : P.mem sk := by
  obtain ⟨m, h1, h2⟩ := hP.2 hk
  exact P.down (SIdx.is_succ_gt_l hs h1) h2

theorem below_isLimit {t} (hl : SIdx.Limit t) : (below t).IsLimit :=
  ⟨hl.limit_lt_0, fun {_} h => let ⟨sn, hs, hlt⟩ := hl.exists_succ_lt h; ⟨sn, hs.lt, hlt⟩⟩

theorem univ_isLimit [SIdxSucc] : (univ : Site).IsLimit :=
  ⟨trivial, fun {n} _ => ⟨succᵢ n, SIdx.lt_succ_self n, trivial⟩⟩

end Site

variable (SI) in
@[indexed]
class EnrichedCat (Obj : Type u) where
  Hom : Obj → Obj → Type v
  [cofe : ∀ a b, COFE (Hom a b)]
  id : ∀ a, Hom a a
  comp : ∀ {a b c : Obj}, Hom b c → Hom a b → Hom a c
  comp_ne : ∀ {a b c : Obj} {n} {g g' : Hom b c} {f f' : Hom a b},
    OFE.Dist n g g' → OFE.Dist n f f' → OFE.Dist n (comp g f) (comp g' f')
  id_comp : ∀ {a b : Obj} (f : Hom a b), comp (id b) f = f
  comp_id : ∀ {a b : Obj} (f : Hom a b), comp f (id a) = f
  assoc : ∀ {a b c d : Obj} (h : Hom c d) (g : Hom b c) (f : Hom a b),
    comp (comp h g) f = comp h (comp g f)

attribute [reducible, instance] EnrichedCat.cofe
attribute [simp] EnrichedCat.id_comp EnrichedCat.comp_id EnrichedCat.assoc

export EnrichedCat (Hom)
attribute [indexed] EnrichedCat.Hom

infixr:80 " ⊚ " => EnrichedCat.comp

section EnrichedCat

variable {Obj : Type u} [EnrichedCat Obj] {a b c : Obj}

theorem comp_dist_l {n} {g g' : Hom b c} (h : g ≡{n}≡ g') (f : Hom a b) :
    g ⊚ f ≡{n}≡ g' ⊚ f :=
  EnrichedCat.comp_ne h .rfl

theorem comp_dist_r {n} (g : Hom b c) {f f' : Hom a b} (h : f ≡{n}≡ f') :
    g ⊚ f ≡{n}≡ g ⊚ f' :=
  EnrichedCat.comp_ne .rfl h

end EnrichedCat

variable (SI) in
@[indexed]
class EFunctor {Obj : Type u} [EnrichedCat Obj]
    (F : Obj → Obj → Obj) where
  map : ∀ {a a' b b' : Obj}, Hom a' a → Hom b b' → Hom (F a b) (F a' b')
  map_contractive : ∀ {a a' b b' : Obj} {n} {f f' : Hom a' a} {g g' : Hom b b'},
    OFE.DistLater n (f, g) (f', g') → OFE.Dist n (map f g) (map f' g')
  map_id : ∀ a b, map (EnrichedCat.id a) (EnrichedCat.id b) = EnrichedCat.id (F a b)
  map_comp : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : Obj} (f : Hom a₂ a₁) (g : Hom a₃ a₂) (f' : Hom b₁ b₂)
    (g' : Hom b₂ b₃), map (f ⊚ g) (g' ⊚ f') = map g g' ⊚ map f f'

theorem map_dist {Obj : Type u} [EnrichedCat Obj] (F : Obj → Obj → Obj) [EFunctor F]
    {a a' b b' : Obj} {n} {f f' : Hom a' a} {g g' : Hom b b'} (hf : f ≡{n}≡ f')
    (hg : g ≡{n}≡ g') : EFunctor.map (F := F) f g ≡{n}≡ EFunctor.map f' g' :=
  EFunctor.map_contractive fun _ hm => ⟨hf.lt hm, hg.lt hm⟩

variable (SI) in
@[indexed]
structure LimitCut where
  mem : SI → Prop
  zero : mem 0
  unbounded : ∀ {n}, mem n → ∃ m, n < m ∧ mem m
  down : ∀ {a b}, a ≤ b → mem b → mem a

namespace LimitCut

def dist (K : LimitCut) {A : Type _} [OFE A] (x y : A) : Prop :=
  ∀ m, K.mem m → x ≡{m}≡ y

theorem mem_of_finite [SIdxFinite] (K : LimitCut) (n) : K.mem n := by
  induction n using (SIdx.lt_wf).induction with
  | _ n ih =>
    rcases SIdxFinite.finite_index n with rfl | ⟨m, hm⟩
    · exact K.zero
    · obtain ⟨k, hmk, hk⟩ := K.unbounded (ih m hm.lt)
      exact K.down (SIdx.is_succ_gt_l hm hmk) hk

end LimitCut

def Site.cut (P : Site) (hP : P.IsLimit) : LimitCut := ⟨P.mem, hP.1, hP.2, P.down⟩

/-- Needs a successor operation: `seg c` needs an index above every index. -/
@[indexed]
def seg [SIdxSucc] (c : SI) : LimitCut where
  mem n := ¬ ∃ l, SIdx.Limit l ∧ c < l ∧ l ≤ n
  zero := fun ⟨l, hl, _, h⟩ => SIdx.limit_0 (SIdx.le_0_r.mp h ▸ hl)
  unbounded {n} h := ⟨succᵢ n, SIdx.lt_succ_self n, fun ⟨l, hl, h1, h2⟩ => by
    rcases SIdx.le_lteq.mp h2 with h2 | rfl
    · exact h ⟨l, hl, h1, SIdx.lt_succ_r.mp h2⟩
    · exact SIdx.limit_S n hl⟩
  down hab h := fun ⟨l, hl, h1, h2⟩ => h ⟨l, hl, h1, SIdx.le_trans h2 hab⟩

theorem mem_seg_of_le [SIdxSucc] {c m} (h : m ≤ c) : (seg c).mem m :=
  fun ⟨_, _, h1, h2⟩ => SIdx.lt_irrefl _ (SIdx.lt_le_trans h1 (SIdx.le_trans h2 h))

theorem mem_seg_mono [SIdxSucc] {a b m} (hab : a ≤ b) (h : (seg a).mem m) : (seg b).mem m :=
  fun ⟨l, hl, h1, h2⟩ => h ⟨l, hl, SIdx.le_lt_trans hab h1, h2⟩

theorem LimitCut.mem_of_mem_seg [SIdxSucc] (K : LimitCut) {c} (hc : K.mem c) :
    ∀ m, (seg c).mem m → K.mem m := by
  intro m
  induction m using (SIdx.lt_wf).induction with
  | _ m ih =>
    intro hm
    rcases SIdx.le_total (n := m) (m := c) with h | h
    · exact K.down h hc
    · match SIdx.case m with
      | .inl h0 => exact h0 ▸ K.zero
      | .inr (.inl ⟨k, hk⟩) =>
        obtain ⟨m', h1, h2⟩ :=
          K.unbounded (ih k hk.lt ((seg c).down (SIdx.lt_le_incl hk.lt) hm))
        exact K.down (SIdx.is_succ_gt_l hk h1) h2
      | .inr (.inr hl) =>
        rcases SIdx.le_lteq.mp h with h | rfl
        · exact absurd ⟨m, hl, h, SIdx.le_refl⟩ hm
        · exact hc

section Determined

variable {Obj : Type u} [EnrichedCat Obj]

@[reducible] def Determined (K : LimitCut) (Y : Obj) : Prop :=
  ∀ {Z : Obj} (g g' : Hom Z Y), K.dist g g' → g = g'

theorem Determined.mono {K K' : LimitCut} (h : ∀ m, K.mem m → K'.mem m) {Y : Obj}
    (hY : Determined K Y) : Determined K' Y :=
  fun g g' hg => hY g g' fun m hm => hg m (h m hm)

end Determined

/-! From here on the solver needs a successor operation (`Tower.Lawful` uses `seg`). Iris-Rocq's
solver is built differently and does not. -/
variable [SIdxSucc]

section

variable {Obj : Type u} [EnrichedCat Obj]

variable (Obj) in
structure Tower (P : Site) where
  X : ∀ β, P.mem β → Obj
  emb : ∀ β δ (hβ : P.mem β) (hδ : P.mem δ), β < δ → Hom (X β hβ) (X δ hδ)
  proj : ∀ β δ (hβ : P.mem β) (hδ : P.mem δ), β < δ → Hom (X δ hδ) (X β hβ)

structure Tower.Lawful {P : Site} (T : Tower Obj P) : Prop where
  proj_comp_emb : ∀ β δ hβ hδ (h : β < δ),
    T.proj β δ hβ hδ h ⊚ T.emb β δ hβ hδ h = EnrichedCat.id _
  emb_comp_proj : ∀ β δ hβ hδ (h : β < δ) (m), m < β →
    T.emb β δ hβ hδ h ⊚ T.proj β δ hβ hδ h ≡{m}≡ EnrichedCat.id _
  emb_comp_emb : ∀ β η δ hβ hη hδ (h1 : β < η) (h2 : η < δ) (h3 : β < δ),
    T.emb η δ hη hδ h2 ⊚ T.emb β η hβ hη h1 = T.emb β δ hβ hδ h3
  proj_comp_proj : ∀ β η δ hβ hη hδ (h1 : β < η) (h2 : η < δ) (h3 : β < δ),
    T.proj β η hβ hη h1 ⊚ T.proj η δ hη hδ h2 = T.proj β δ hβ hδ h3
  determined : ∀ β hβ, Determined (seg β) (T.X β hβ)

namespace Tower

variable {P : Site} (T : Tower Obj P)

def hom (β n) (hβ : P.mem β) (hn : P.mem n) : Hom (T.X n hn) (T.X β hβ) :=
  match SIdx.lt_trichotomyT β n with
  | .inl h => T.proj β n hβ hn h
  | .inr (.inl h) => h ▸ EnrichedCat.id _
  | .inr (.inr h) => T.emb n β hn hβ h

omit [SIdxSucc] in
theorem hom_lt {β n} (hβ : P.mem β) (hn : P.mem n) (h : β < n) :
    T.hom β n hβ hn = T.proj β n hβ hn h := by
  unfold hom
  exact match SIdx.lt_trichotomyT β n with
  | .inl _ => rfl
  | .inr (.inl h') => absurd (h' ▸ h) (SIdx.lt_irrefl _)
  | .inr (.inr h') => absurd (SIdx.lt_trans h h') (SIdx.lt_irrefl _)

omit [SIdxSucc] in
theorem hom_self {β} (hβ hβ' : P.mem β) : T.hom β β hβ hβ' = EnrichedCat.id _ := by
  unfold hom
  exact match SIdx.lt_trichotomyT β β with
  | .inl h => absurd h (SIdx.lt_irrefl _)
  | .inr (.inl _) => rfl
  | .inr (.inr h) => absurd h (SIdx.lt_irrefl _)

omit [SIdxSucc] in
theorem hom_gt {β n} (hβ : P.mem β) (hn : P.mem n) (h : n < β) :
    T.hom β n hβ hn = T.emb n β hn hβ h := by
  unfold hom
  exact match SIdx.lt_trichotomyT β n with
  | .inl h' => absurd (SIdx.lt_trans h h') (SIdx.lt_irrefl _)
  | .inr (.inl h') => absurd (h' ▸ h) (SIdx.lt_irrefl _)
  | .inr (.inr _) => rfl

theorem proj_comp_hom {T : Tower Obj P} (hT : T.Lawful) (n) (hn : P.mem n) (β δ)
    (hβ : P.mem β) (hδ : P.mem δ) (hlt : β < δ) :
    T.proj β δ hβ hδ hlt ⊚ T.hom δ n hδ hn = T.hom β n hβ hn := by
  rcases SIdx.lt_trichotomyT δ n with h1 | rfl | h1
  · rw [T.hom_lt hδ hn h1, T.hom_lt hβ hn (SIdx.lt_trans hlt h1), hT.proj_comp_proj]
  · rw [T.hom_self, T.hom_lt hβ hn hlt, EnrichedCat.comp_id]
  · rw [T.hom_gt hδ hn h1]
    rcases SIdx.lt_trichotomyT β n with h0 | rfl | h0
    · rw [T.hom_lt hβ hn h0, ← hT.proj_comp_proj β n δ hβ hn hδ h0 h1 hlt, EnrichedCat.assoc,
        hT.proj_comp_emb, EnrichedCat.comp_id]
    · rw [T.hom_self, hT.proj_comp_emb]
    · rw [T.hom_gt hβ hn h0, ← hT.emb_comp_emb n β δ hn hβ hδ h0 hlt h1, ← EnrichedCat.assoc,
        hT.proj_comp_emb, EnrichedCat.id_comp]

end Tower

end

variable (SI) in
@[indexed]
class HasTowerLimits (Obj : Type u) [EnrichedCat Obj] where
  lim : ∀ {P : Site} (T : Tower Obj P), T.Lawful → Obj
  π : ∀ {P} (T : Tower Obj P) (hT : T.Lawful) β hβ, Hom (lim T hT) (T.X β hβ)
  proj_comp_π : ∀ {P} (T : Tower Obj P) (hT : T.Lawful) β δ hβ hδ (h : β < δ),
    T.proj β δ hβ hδ h ⊚ π T hT δ hδ = π T hT β hβ
  lift : ∀ {P} (T : Tower Obj P) (hT : T.Lawful) {Y : Obj} (g : ∀ β hβ, Hom Y (T.X β hβ)),
    (∀ β δ hβ hδ (h : β < δ), T.proj β δ hβ hδ h ⊚ g δ hδ = g β hβ) → Hom Y (lim T hT)
  π_comp_lift : ∀ {P} (T : Tower Obj P) (hT : T.Lawful) {Y : Obj}
    (g : ∀ β hβ, Hom Y (T.X β hβ)) hg β hβ, π T hT β hβ ⊚ lift T hT g hg = g β hβ
  ext_dist : ∀ {P} (T : Tower Obj P) (hT : T.Lawful) {Y : Obj} {n}
    (f f' : Hom Y (lim T hT)),
    (∀ β hβ, π T hT β hβ ⊚ f ≡{n}≡ π T hT β hβ ⊚ f') → f ≡{n}≡ f'

namespace InvLim

open HasTowerLimits

variable {Obj : Type u} [EnrichedCat Obj] [HasTowerLimits Obj] {P : Site}
  {T : Tower Obj P} (hT : T.Lawful)

def emb (n) (hn : P.mem n) : Hom (T.X n hn) (lim T hT) :=
  lift T hT (fun β hβ => T.hom β n hβ hn) fun β δ hβ hδ hlt =>
    Tower.proj_comp_hom hT n hn β δ hβ hδ hlt

theorem π_comp_emb (n) (hn : P.mem n) β hβ : π T hT β hβ ⊚ emb hT n hn = T.hom β n hβ hn :=
  π_comp_lift T hT _ _ β hβ

theorem π_comp_emb_self (n) (hn : P.mem n) : π T hT n hn ⊚ emb hT n hn = EnrichedCat.id _ := by
  rw [π_comp_emb, T.hom_self]

theorem ext {Y : Obj} (g g' : Hom Y (lim T hT))
    (h : ∀ β hβ, π T hT β hβ ⊚ g = π T hT β hβ ⊚ g') :
    g = g' :=
  OFE.eq_dist.mpr fun _ => ext_dist T hT g g' fun β hβ => .of_eq (h β hβ)

theorem emb_comp_π (n) (hn : P.mem n) m (hm : m < n) :
    emb hT n hn ⊚ π T hT n hn ≡{m}≡ EnrichedCat.id _ := by
  refine ext_dist T hT _ _ fun β hβ => ?_
  rw [← EnrichedCat.assoc, π_comp_emb, EnrichedCat.comp_id]
  rcases SIdx.lt_trichotomyT β n with h | rfl | h
  · rw [T.hom_lt hβ hn h, proj_comp_π]
  · rw [T.hom_self, EnrichedCat.id_comp]
  · rw [T.hom_gt hβ hn h, ← proj_comp_π T hT n β hn hβ h, ← EnrichedCat.assoc]
    exact (comp_dist_l (hT.emb_comp_proj n β hn hβ h m hm) _).trans
      (.of_eq (EnrichedCat.id_comp _))

theorem emb_comp_emb (β δ) (hβ : P.mem β) (hδ : P.mem δ) (hlt : β < δ) :
    emb hT δ hδ ⊚ T.emb β δ hβ hδ hlt = emb hT β hβ := by
  refine ext hT _ _ fun η hη => ?_
  rw [← EnrichedCat.assoc, π_comp_emb, π_comp_emb]
  rcases SIdx.lt_trichotomyT η β with h | rfl | h
  · rw [T.hom_lt hη hβ h, T.hom_lt hη hδ (SIdx.lt_trans h hlt),
      ← hT.proj_comp_proj η β δ hη hβ hδ h hlt, EnrichedCat.assoc, hT.proj_comp_emb,
      EnrichedCat.comp_id]
  · rw [T.hom_self, T.hom_lt hη hδ hlt, hT.proj_comp_emb]
  · rcases SIdx.lt_trichotomyT η δ with h' | rfl | h'
    · rw [T.hom_gt hη hβ h, T.hom_lt hη hδ h', ← hT.emb_comp_emb β η δ hβ hη hδ h h' hlt,
        ← EnrichedCat.assoc, hT.proj_comp_emb, EnrichedCat.id_comp]
    · rw [T.hom_gt hη hβ h, T.hom_self, EnrichedCat.id_comp]
    · rw [T.hom_gt hη hβ h, T.hom_gt hη hδ h', hT.emb_comp_emb β δ η hβ hδ hη hlt h' h]

end InvLim

variable (SI) in
@[indexed]
class HasTerminal (Obj : Type u) [EnrichedCat Obj] where
  one : Obj
  toOne : ∀ a, Hom a one
  toOne_unique : ∀ {a} (f : Hom a one), f = toOne a
attribute [indexed] Iris.Enriched.HasTerminal.one

variable (SI) in
@[indexed]
class HasSeed {Obj : Type u} [EnrichedCat Obj] [HasTerminal Obj] (F : Obj → Obj → Obj) where
  seed : Hom (HasTerminal.one (Obj := Obj))
    (F (HasTerminal.one (Obj := Obj)) (HasTerminal.one (Obj := Obj)))

variable (SI) in
@[indexed]
class Truncatable {Obj : Type u} [EnrichedCat Obj] (F : Obj → Obj → Obj) where
  trunc : ∀ (K : LimitCut) (A : Obj), Determined K A → Obj
  proj : ∀ K A hA, Hom (F A A) (trunc K A hA)
  rep : ∀ K A hA, Hom (trunc K A hA) (F A A)
  proj_rep : ∀ K A hA, proj K A hA ⊚ rep K A hA = EnrichedCat.id _
  rep_proj : ∀ K A hA (m), K.mem m → rep K A hA ⊚ proj K A hA ≡{m}≡ EnrichedCat.id _
  determined : ∀ K A hA, Determined K (trunc K A hA)

instance finiteTruncatable [SIdxFinite] {Obj : Type u} [EnrichedCat Obj]
    (F : Obj → Obj → Obj) : Truncatable F where
  trunc _ A _ := F A A
  proj _ _ _ := EnrichedCat.id _
  rep _ _ _ := EnrichedCat.id _
  proj_rep _ _ _ := EnrichedCat.id_comp _
  rep_proj _ _ _ _ _ := .of_eq (EnrichedCat.id_comp _)
  determined K _ _ := fun _ _ hg => OFE.eq_dist.mpr fun n => hg n (K.mem_of_finite n)

section Solver

variable {Obj : Type u} [EnrichedCat Obj]
variable {F : Obj → Obj → Obj} [EFunctor F]

variable (F) in
structure PartialSol (P : Site) extends Tower Obj P where
  fold : ∀ β (hβ : P.mem β), Hom (F (X β hβ) (X β hβ)) (X β hβ)
  unfold : ∀ β (hβ : P.mem β), Hom (X β hβ) (F (X β hβ) (X β hβ))

def PartialSol.restrict {P Q : Site} (f : PartialSol F P) (h : Q ≤ P) : PartialSol F Q where
  X β hβ := f.X β (h β hβ)
  emb β δ _ _ hlt := f.emb β δ _ _ hlt
  proj β δ _ _ hlt := f.proj β δ _ _ hlt
  fold β _ := f.fold β _
  unfold β _ := f.unfold β _

structure Extension {γ} (f : PartialSol F (Site.below γ)) where
  X : Obj
  emb : ∀ β (h : β < γ), Hom (f.X β h) X
  proj : ∀ β (h : β < γ), Hom X (f.X β h)
  fold : Hom (F X X) X
  unfold : Hom X (F X X)

structure Extension.Lawful {γ} {f : PartialSol F (Site.below γ)} (S : Extension f) :
    Prop where
  proj_comp_emb : ∀ β (hβ : β < γ), S.proj β hβ ⊚ S.emb β hβ = EnrichedCat.id _
  emb_comp_proj : ∀ β (hβ : β < γ) (m), m < β →
    S.emb β hβ ⊚ S.proj β hβ ≡{m}≡ EnrichedCat.id _
  emb_comp_emb : ∀ β η (h1 : β < η) (h2 : η < γ),
    S.emb η h2 ⊚ f.emb β η (SIdx.lt_trans h1 h2) h2 h1 = S.emb β (SIdx.lt_trans h1 h2)
  proj_comp_proj : ∀ β η (h1 : β < η) (h2 : η < γ),
    f.proj β η (SIdx.lt_trans h1 h2) h2 h1 ⊚ S.proj η h2 = S.proj β (SIdx.lt_trans h1 h2)
  fold_comp_unfold : S.fold ⊚ S.unfold = EnrichedCat.id _
  unfold_comp_fold : ∀ m, m < γ → S.unfold ⊚ S.fold ≡{m}≡ EnrichedCat.id _
  proj_comp_fold : ∀ β (hβ : β < γ),
    S.proj β hβ ⊚ S.fold = f.fold β hβ ⊚ EFunctor.map (S.emb β hβ) (S.proj β hβ)
  determined : Determined (seg γ) S.X

namespace PartialSol

variable {P : Site} (f : PartialSol F P)

def topAt (δ) (hδ : P.mem δ) : Extension (f.restrict (Site.below_le_of_mem hδ)) where
  X := f.X δ hδ
  emb β h := f.emb β δ _ hδ h
  proj β h := f.proj β δ _ hδ h
  fold := f.fold δ hδ
  unfold := f.unfold δ hδ

def Lawful : Prop := ∀ δ (hδ : P.mem δ), (f.topAt δ hδ).Lawful

end PartialSol

namespace PartialSol.Lawful

variable {P : Site} {f : PartialSol F P} (hf : f.Lawful)
include hf

theorem proj_comp_emb β δ hβ hδ hlt :
    f.proj β δ hβ hδ hlt ⊚ f.emb β δ hβ hδ hlt = EnrichedCat.id _ :=
  (hf δ hδ).proj_comp_emb β hlt

theorem emb_comp_proj β δ hβ hδ hlt (m) (hm : m < β) :
    f.emb β δ hβ hδ hlt ⊚ f.proj β δ hβ hδ hlt ≡{m}≡ EnrichedCat.id _ :=
  (hf δ hδ).emb_comp_proj β hlt m hm

theorem emb_comp_emb β η δ hβ hη hδ h1 h2 h3 :
    f.emb η δ hη hδ h2 ⊚ f.emb β η hβ hη h1 = f.emb β δ hβ hδ h3 :=
  (hf δ hδ).emb_comp_emb β η h1 h2

theorem proj_comp_proj β η δ hβ hη hδ h1 h2 h3 :
    f.proj β η hβ hη h1 ⊚ f.proj η δ hη hδ h2 = f.proj β δ hβ hδ h3 :=
  (hf δ hδ).proj_comp_proj β η h1 h2

theorem fold_comp_unfold β hβ : f.fold β hβ ⊚ f.unfold β hβ = EnrichedCat.id _ :=
  (hf β hβ).fold_comp_unfold

theorem unfold_comp_fold β hβ (m) (hm : m < β) :
    f.unfold β hβ ⊚ f.fold β hβ ≡{m}≡ EnrichedCat.id _ :=
  (hf β hβ).unfold_comp_fold m hm

theorem proj_comp_fold β δ hβ hδ hlt : f.proj β δ hβ hδ hlt ⊚ f.fold δ hδ =
    f.fold β hβ ⊚ EFunctor.map (f.emb β δ hβ hδ hlt) (f.proj β δ hβ hδ hlt) :=
  (hf δ hδ).proj_comp_fold β hlt

theorem determined β hβ : Determined (seg β) (f.X β hβ) := (hf β hβ).determined

theorem restrict {Q : Site} (h : Q ≤ P) : (f.restrict h).Lawful :=
  fun δ hδ => hf δ (h δ hδ)

theorem tower : f.toTower.Lawful where
  proj_comp_emb := hf.proj_comp_emb
  emb_comp_proj := hf.emb_comp_proj
  emb_comp_emb := hf.emb_comp_emb
  proj_comp_proj := hf.proj_comp_proj
  determined := hf.determined

theorem hom_comp_hom {a b c} (ha : P.mem a) (hb : P.mem b) (hc : P.mem c) (hab : a ≤ b)
    (hbc : b ≤ c) : f.hom a b ha hb ⊚ f.hom b c hb hc = f.hom a c ha hc := by
  rcases SIdx.le_lteq.mp hab with hab | rfl
  · rcases SIdx.le_lteq.mp hbc with hbc | rfl
    · rw [f.hom_lt _ _ hab, f.hom_lt _ _ hbc, f.hom_lt _ _ (SIdx.lt_trans hab hbc)]
      exact hf.proj_comp_proj a b c ha hb hc hab hbc _
    · rw [f.hom_self, EnrichedCat.comp_id]
  · rw [f.hom_self, EnrichedCat.id_comp]

theorem hom_comp_hom_of_le {a c} (ha : P.mem a) (hc : P.mem c) (hac : a ≤ c) :
    f.hom a c ha hc ⊚ f.hom c a hc ha = EnrichedCat.id _ := by
  rcases SIdx.le_lteq.mp hac with h | rfl
  · rw [f.hom_lt _ _ h, f.hom_gt _ _ h]; exact hf.proj_comp_emb a c ha hc h
  · rw [f.hom_self, EnrichedCat.id_comp]

theorem hom_comp_hom_dist {a c} (ha : P.mem a) (hc : P.mem c) (hac : a ≤ c) m
    (hm : m < a) : f.hom c a hc ha ⊚ f.hom a c ha hc ≡{m}≡ EnrichedCat.id _ := by
  rcases SIdx.le_lteq.mp hac with h | rfl
  · rw [f.hom_lt _ _ h, f.hom_gt _ _ h]; exact hf.emb_comp_proj a c ha hc h m hm
  · rw [f.hom_self, EnrichedCat.id_comp]

theorem hom_comp_emb {a b c} (ha : P.mem a) (hb : P.mem b) (hc : P.mem c) (hab : a < b)
    (hbc : b ≤ c) : f.hom c b hc hb ⊚ f.emb a b ha hb hab = f.hom c a hc ha := by
  rcases SIdx.le_lteq.mp hbc with h | rfl
  · rw [f.hom_gt _ _ h, f.hom_gt _ _ (SIdx.lt_trans hab h)]
    exact hf.emb_comp_emb a b c ha hb hc hab h _
  · rw [f.hom_self, EnrichedCat.id_comp, f.hom_gt _ _ hab]

theorem hom_comp_fold {a c} (ha : P.mem a) (hc : P.mem c) (hac : a ≤ c) :
    f.hom a c ha hc ⊚ f.fold c hc = f.fold a ha ⊚ EFunctor.map (f.hom c a hc ha) (f.hom a c ha hc) := by
  rcases SIdx.le_lteq.mp hac with h | rfl
  · rw [f.hom_lt _ _ h, f.hom_gt _ _ h]; exact hf.proj_comp_fold a c ha hc h
  · simp only [f.hom_self, EFunctor.map_id, EnrichedCat.id_comp, EnrichedCat.comp_id]

theorem map_comp_unfold {a c} (ha : P.mem a) (hc : P.mem c) (hac : a ≤ c) m (hm : m < a) :
    EFunctor.map (f.hom c a hc ha) (f.hom a c ha hc) ⊚ f.unfold c hc ≡{m}≡
      f.unfold a ha ⊚ f.hom a c ha hc :=
  calc
    _ = EnrichedCat.id _ ⊚ (EFunctor.map (f.hom c a hc ha) (f.hom a c ha hc) ⊚ f.unfold c hc) :=
      (EnrichedCat.id_comp _).symm
    _ ≡{m}≡ (f.unfold a ha ⊚ f.fold a ha) ⊚ (EFunctor.map (f.hom c a hc ha) (f.hom a c ha hc) ⊚
        f.unfold c hc) := comp_dist_l (hf.unfold_comp_fold a ha m hm).symm _
    _ = f.unfold a ha ⊚ f.hom a c ha hc := by
      rw [EnrichedCat.assoc, ← EnrichedCat.assoc (f.fold a ha), ← hf.hom_comp_fold ha hc hac,
        EnrichedCat.assoc, hf.fold_comp_unfold, EnrichedCat.comp_id]

end PartialSol.Lawful

section Zero

variable [HasTerminal Obj] [HasSeed F]

open HasTerminal in
def zeroTop {γ} (h0 : γ = 0) (f : PartialSol F (Site.below γ)) : Extension f where
  X := one
  emb β h := absurd (h0 ▸ h) (SIdx.not_lt_zero β)
  proj β h := absurd (h0 ▸ h) (SIdx.not_lt_zero β)
  fold := toOne _
  unfold := HasSeed.seed (F := F)

theorem zeroTop_lawful {γ} (h0 : γ = 0) (f : PartialSol F (Site.below γ)) :
    (zeroTop h0 f).Lawful where
  proj_comp_emb β h := absurd (h0 ▸ h) (SIdx.not_lt_zero β)
  emb_comp_proj β h := absurd (h0 ▸ h) (SIdx.not_lt_zero β)
  emb_comp_emb _ η _ h2 := absurd (h0 ▸ h2) (SIdx.not_lt_zero η)
  proj_comp_proj _ η _ h2 := absurd (h0 ▸ h2) (SIdx.not_lt_zero η)
  fold_comp_unfold := (HasTerminal.toOne_unique _).trans (HasTerminal.toOne_unique _).symm
  unfold_comp_fold m hm := absurd (h0 ▸ hm) (SIdx.not_lt_zero m)
  proj_comp_fold β h := absurd (h0 ▸ h) (SIdx.not_lt_zero β)
  determined g g' _ := (HasTerminal.toOne_unique g).trans (HasTerminal.toOne_unique g').symm

end Zero

section Succ

variable [Truncatable F]
open Truncatable

variable {γ m : SI} (hm : γ = succᵢ m)

include hm in
theorem le_of_below_succ {β} (h : β < γ) : β ≤ m := SIdx.lt_succ_r.mp (hm ▸ h)

include hm in
theorem lt_of_eq_succ : m < γ := hm ▸ SIdx.lt_succ_self m

variable {f : PartialSol F (Site.below γ)} (hf : f.Lawful)

abbrev succStage : Obj :=
  trunc (F := F) (seg m) (f.X m (lt_of_eq_succ hm)) (hf.determined m _)

def succEmb : Hom (f.X m (lt_of_eq_succ hm)) (succStage hm hf) :=
  proj (F := F) (seg m) _ _ ⊚ f.unfold m (lt_of_eq_succ hm)

def succProj : Hom (succStage hm hf) (f.X m (lt_of_eq_succ hm)) :=
  f.fold m (lt_of_eq_succ hm) ⊚ rep (F := F) (seg m) _ _

@[reducible] def succTop : Extension f where
  X := succStage hm hf
  emb β h := succEmb hm hf ⊚ f.hom m β (lt_of_eq_succ hm) h
  proj β h := f.hom β m h (lt_of_eq_succ hm) ⊚ succProj hm hf
  fold := proj (F := F) (seg m) _ _ ⊚ EFunctor.map (succEmb hm hf) (succProj hm hf)
  unfold := EFunctor.map (succProj hm hf) (succEmb hm hf) ⊚ rep (F := F) (seg m) _ _

theorem succProj_comp_proj {n} (hn : (seg m).mem n) :
    succProj hm hf ⊚ proj (F := F) (seg m) _ _ ≡{n}≡ f.fold m (lt_of_eq_succ hm) := by
  rw [succProj, EnrichedCat.assoc]
  exact (comp_dist_r _ (rep_proj (F := F) _ _ _ n hn)).trans (.of_eq (EnrichedCat.comp_id _))

theorem succProj_comp_succEmb : succProj hm hf ⊚ succEmb hm hf = EnrichedCat.id _ :=
  hf.determined m (lt_of_eq_succ hm) _ _ fun n hn => by
    rw [succEmb, ← EnrichedCat.assoc]
    exact (comp_dist_l (succProj_comp_proj hm hf hn) _).trans (.of_eq (hf.fold_comp_unfold m _))

theorem succEmb_comp_succProj (k) (hk : k < m) :
    succEmb hm hf ⊚ succProj hm hf ≡{k}≡ EnrichedCat.id _ := by
  rw [succEmb, succProj, EnrichedCat.assoc, ← EnrichedCat.assoc (f.unfold m _)]
  refine (comp_dist_r _ (comp_dist_l (hf.unfold_comp_fold m _ k hk) _)).trans (.of_eq ?_)
  rw [EnrichedCat.id_comp, proj_rep (F := F)]

theorem succTop_lawful : (succTop hm hf).Lawful where
  proj_comp_emb β h := by
    simp only [succTop, EnrichedCat.assoc]
    rw [← EnrichedCat.assoc (succProj hm hf), succProj_comp_succEmb hm hf, EnrichedCat.id_comp]
    exact hf.hom_comp_hom_of_le h _ (le_of_below_succ hm h)
  emb_comp_proj β h k hk := by
    simp only [succTop, EnrichedCat.assoc]
    rw [← EnrichedCat.assoc (f.hom m β _ _)]
    refine (comp_dist_r _ (comp_dist_l
      (hf.hom_comp_hom_dist h _ (le_of_below_succ hm h) k hk) _)).trans ?_
    rw [EnrichedCat.id_comp]
    exact succEmb_comp_succProj hm hf k (SIdx.lt_le_trans hk (le_of_below_succ hm h))
  emb_comp_emb β η h1 h2 := by
    simp only [succTop, EnrichedCat.assoc]
    rw [hf.hom_comp_emb _ h2 _ h1 (le_of_below_succ hm h2)]
  proj_comp_proj β η h1 h2 := by
    simp only [succTop]
    rw [← EnrichedCat.assoc, ← f.hom_lt _ h2 h1,
      hf.hom_comp_hom _ h2 _ (SIdx.lt_le_incl h1) (le_of_below_succ hm h2)]
  fold_comp_unfold := by
    simp only [succTop, EnrichedCat.assoc]
    rw [← EnrichedCat.assoc (EFunctor.map _ _), ← EFunctor.map_comp, succProj_comp_succEmb hm hf,
      EFunctor.map_id, EnrichedCat.id_comp, proj_rep (F := F)]
  unfold_comp_fold k hk := by
    simp only [succTop, EnrichedCat.assoc]
    rw [← EnrichedCat.assoc (rep (F := F) _ _ _)]
    refine (comp_dist_r _ (comp_dist_l
      (rep_proj (F := F) _ _ _ k (mem_seg_of_le (le_of_below_succ hm hk))) _)).trans ?_
    rw [EnrichedCat.id_comp, ← EFunctor.map_comp, ← EFunctor.map_id]
    exact EFunctor.map_contractive fun j hj =>
      have hj' := SIdx.lt_le_trans hj (le_of_below_succ hm hk)
      ⟨succEmb_comp_succProj hm hf j hj', succEmb_comp_succProj hm hf j hj'⟩
  proj_comp_fold β h := hf.determined β h _ _ fun n hn => by
    simp only [succTop, EnrichedCat.assoc]
    rw [← EnrichedCat.assoc (succProj hm hf)]
    refine (comp_dist_r _ (comp_dist_l
      (succProj_comp_proj hm hf (mem_seg_mono (le_of_below_succ hm h) hn)) _)).trans (.of_eq ?_)
    rw [← EnrichedCat.assoc, hf.hom_comp_fold h _ (le_of_below_succ hm h), EnrichedCat.assoc,
      ← EFunctor.map_comp]
  determined := Determined.mono (fun _ hn => mem_seg_mono (SIdx.lt_le_incl (lt_of_eq_succ hm)) hn)
    (determined (F := F) (seg m) _ _)

end Succ

section Limit

variable [HasTowerLimits Obj]
open HasTowerLimits

variable {P : Site} (hP : P.IsLimit) (f : PartialSol F P) (hf : f.Lawful)

abbrev limObj : Obj := lim f.toTower hf.tower

include hf in
theorem hom_comp_π {c c'} (hc : P.mem c) (hc' : P.mem c') (h : c ≤ c') :
    f.hom c c' hc hc' ⊚ π _ hf.tower c' hc' = π _ hf.tower c hc := by
  rcases SIdx.le_lteq.mp h with h | rfl
  · rw [f.hom_lt _ _ h]; exact proj_comp_π _ hf.tower c c' hc hc' h
  · rw [f.hom_self, EnrichedCat.id_comp]

include hf in
theorem emb_comp_hom {c c'} (hc : P.mem c) (hc' : P.mem c') (h : c ≤ c') :
    InvLim.emb hf.tower c' hc' ⊚ f.hom c' c hc' hc = InvLim.emb hf.tower c hc := by
  rcases SIdx.le_lteq.mp h with h | rfl
  · rw [f.hom_gt _ _ h]; exact InvLim.emb_comp_emb hf.tower c c' hc hc' h
  · rw [f.hom_self, EnrichedCat.comp_id]

theorem limFold_compatible β δ hβ hδ (h : β < δ) :
    f.proj β δ hβ hδ h ⊚ (f.fold δ hδ ⊚ EFunctor.map (InvLim.emb hf.tower δ hδ) (π _ hf.tower δ hδ)) =
      f.fold β hβ ⊚ EFunctor.map (InvLim.emb hf.tower β hβ) (π _ hf.tower β hβ) := by
  rw [← EnrichedCat.assoc, hf.proj_comp_fold, EnrichedCat.assoc, ← EFunctor.map_comp,
    InvLim.emb_comp_emb, proj_comp_π]

def limFold : Hom (F (limObj f hf) (limObj f hf)) (limObj f hf) :=
  lift _ hf.tower
    (fun c hc => f.fold c hc ⊚ EFunctor.map (InvLim.emb hf.tower c hc) (π _ hf.tower c hc))
    (limFold_compatible f hf)

theorem π_comp_limFold c hc : π _ hf.tower c hc ⊚ limFold f hf =
    f.fold c hc ⊚ EFunctor.map (InvLim.emb hf.tower c hc) (π _ hf.tower c hc) :=
  π_comp_lift _ hf.tower _ _ c hc

def chainAt (c) (hc : P.mem c) : Hom (limObj f hf) (F (limObj f hf) (limObj f hf)) :=
  EFunctor.map (π _ hf.tower c hc) (InvLim.emb hf.tower c hc) ⊚ f.unfold c hc ⊚ π _ hf.tower c hc

theorem chainAt_dist {c c'} (hc : P.mem c) (hc' : P.mem c') (h : c ≤ c') m (hm : m < c) :
    chainAt f hf c' hc' ≡{m}≡ chainAt f hf c hc := by
  calc chainAt f hf c' hc'
      ≡{m}≡ EFunctor.map (π _ hf.tower c' hc') (InvLim.emb hf.tower c' hc') ⊚
        (EFunctor.map (f.hom c c' hc hc') (f.hom c' c hc' hc) ⊚ (f.unfold c hc ⊚ f.hom c c' hc hc')) ⊚
          π _ hf.tower c' hc' := comp_dist_r _ (comp_dist_l ?_ _)
    _ = chainAt f hf c hc := by
      rw [chainAt, ← hom_comp_π f hf hc hc' h, ← emb_comp_hom f hf hc hc' h, EFunctor.map_comp]
      simp only [EnrichedCat.assoc]
  refine .symm ((comp_dist_r _ (hf.map_comp_unfold hc hc' h m hm).symm).trans ?_)
  rw [← EnrichedCat.assoc, ← EFunctor.map_comp]
  refine (comp_dist_l (map_dist F (hf.hom_comp_hom_dist hc hc' h m hm)
    (hf.hom_comp_hom_dist hc hc' h m hm)) _).trans ?_
  rw [EFunctor.map_id, EnrichedCat.id_comp]

theorem π_comp_limFold_comp_chainAt {c c'} (hc : P.mem c) (hc' : P.mem c') (h : c ≤ c') :
    π _ hf.tower c hc ⊚ limFold f hf ⊚ chainAt f hf c' hc' = π _ hf.tower c hc := by
  rw [← EnrichedCat.assoc, π_comp_limFold]
  simp only [chainAt, EnrichedCat.assoc]
  rw [← EnrichedCat.assoc (EFunctor.map _ _) (EFunctor.map _ _), ← EFunctor.map_comp, InvLim.π_comp_emb,
    InvLim.π_comp_emb, ← EnrichedCat.assoc, ← hf.hom_comp_fold hc hc' h, EnrichedCat.assoc,
    ← EnrichedCat.assoc (f.fold c' hc'), hf.fold_comp_unfold, EnrichedCat.id_comp,
    hom_comp_π f hf hc hc' h]

theorem chainAt_comp_limFold (c) (hc : P.mem c) m (hm : m < c) :
    chainAt f hf c hc ⊚ limFold f hf ≡{m}≡ EnrichedCat.id _ := by
  simp only [chainAt, EnrichedCat.assoc]
  rw [π_comp_limFold, ← EnrichedCat.assoc (f.unfold c hc)]
  refine (comp_dist_r _ (comp_dist_l (hf.unfold_comp_fold c hc m hm) _)).trans ?_
  rw [EnrichedCat.id_comp, ← EFunctor.map_comp, ← EFunctor.map_id]
  exact EFunctor.map_contractive fun j hj =>
    ⟨InvLim.emb_comp_π hf.tower c hc j (SIdx.lt_trans hj hm),
      InvLim.emb_comp_π hf.tower c hc j (SIdx.lt_trans hj hm)⟩

theorem lim_determined {K : LimitCut}
    (hK : ∀ c, P.mem c → ∀ n, (seg c).mem n → K.mem n) :
    Determined K (limObj f hf) := fun g g' h =>
  InvLim.ext hf.tower g g' fun c hc =>
    hf.determined c hc _ _ fun n hn => comp_dist_r _ (h n (hK c hc n hn))

def limChain : Site.Chain (Hom (limObj f hf) (F (limObj f hf) (limObj f hf))) P where
  val k hk := chainAt f hf (succᵢ k) (hP.succ_mem (SIdxSucc.succ_isSucc _) hk)
  cauchy {m _} _ _ h := chainAt_dist f hf _ _ (SIdx.succ_le_mono.mp h) m (SIdx.lt_succ_self m)

variable [Site.HasCompl.{v, w} P]

def limUnfold : Hom (limObj f hf) (F (limObj f hf) (limObj f hf)) :=
  @Site.HasCompl.compl _ _ P _ _ _ ⟨chainAt f hf _ (hP.succ_mem (SIdxSucc.succ_isSucc _) hP.1)⟩ (limChain hP f hf)

theorem limUnfold_dist {k} (hk : P.mem k) :
    limUnfold hP f hf ≡{k}≡ chainAt f hf (succᵢ k) (hP.succ_mem (SIdxSucc.succ_isSucc _) hk) :=
  @Site.HasCompl.conv_compl _ _ P _ _ _ ⟨chainAt f hf _ (hP.succ_mem (SIdxSucc.succ_isSucc _) hP.1)⟩ _ _ hk

theorem limFold_comp_limUnfold : limFold f hf ⊚ limUnfold hP f hf = EnrichedCat.id _ :=
  InvLim.ext hf.tower _ _ fun c hc => hf.determined c hc _ _ fun n hn => by
    rw [EnrichedCat.comp_id, ← EnrichedCat.assoc]
    rcases SIdx.le_total (n := n) (m := c) with hnc | hcn
    · refine (comp_dist_r _ ((limUnfold_dist hP f hf hc).le hnc)).trans (.of_eq ?_)
      rw [EnrichedCat.assoc]
      exact π_comp_limFold_comp_chainAt f hf hc _ SIdx.le_succ_diag_r
    · refine (comp_dist_r _ (limUnfold_dist hP f hf ((P.cut hP).mem_of_mem_seg hc n hn))).trans
        (.of_eq ?_)
      rw [EnrichedCat.assoc]
      exact π_comp_limFold_comp_chainAt f hf hc _ (SIdx.le_trans hcn SIdx.le_succ_diag_r)

theorem limUnfold_comp_limFold {m} (hm : P.mem m) :
    limUnfold hP f hf ⊚ limFold f hf ≡{m}≡ EnrichedCat.id _ :=
  (comp_dist_l (limUnfold_dist hP f hf hm) _).trans
    (chainAt_comp_limFold f hf _ _ m (SIdx.lt_succ_self m))

end Limit

section LimitTop

variable [HasTowerLimits Obj]
variable {γ : SI} (hl : SIdx.Limit γ) (f : PartialSol F (Site.below γ)) (hf : f.Lawful)

def limitTop : Extension f where
  X := limObj f hf
  emb β h := InvLim.emb hf.tower β h
  proj β h := HasTowerLimits.π _ hf.tower β h
  fold := limFold f hf
  unfold := limUnfold (Site.below_isLimit hl) f hf

theorem limitTop_lawful : (limitTop hl f hf).Lawful where
  proj_comp_emb β h := InvLim.π_comp_emb_self hf.tower β h
  emb_comp_proj β h k hk := InvLim.emb_comp_π hf.tower β h k hk
  emb_comp_emb β η h1 h2 := InvLim.emb_comp_emb hf.tower β η _ h2 h1
  proj_comp_proj β η h1 h2 := HasTowerLimits.proj_comp_π _ hf.tower β η _ h2 h1
  fold_comp_unfold := limFold_comp_limUnfold _ f hf
  unfold_comp_fold m hm := limUnfold_comp_limFold _ f hf (m := m) hm
  proj_comp_fold β h := π_comp_limFold f hf β h
  determined := lim_determined f hf fun _ hc _ hn => mem_seg_mono (SIdx.lt_le_incl hc) hn

end LimitTop

variable (F) in
@[indexed]
structure ClosedSol (γ : SI) where
  below : PartialSol F (Site.below γ)
  top : Extension below
  below_lawful : below.Lawful
  top_lawful : top.Lawful

namespace ClosedSol

variable {γ : SI}

def restrict {β} (h : β < γ) (t : ClosedSol F γ) : ClosedSol F β where
  below := t.below.restrict (Site.below_le_below (SIdx.lt_le_incl h))
  top := t.below.topAt β h
  below_lawful := t.below_lawful.restrict _
  top_lawful := t.below_lawful β h

def castDom {t t' : ClosedSol F γ} (h : t = t') {Z : Obj} (g : Hom t.top.X Z) :
    Hom t'.top.X Z :=
  h ▸ g

def castCod {t t' : ClosedSol F γ} (h : t = t') {Z : Obj} (g : Hom Z t.top.X) :
    Hom Z t'.top.X :=
  h ▸ g

end ClosedSol

def Coherent {P : Site} (fam : ∀ γ, P.mem γ → ClosedSol F γ) : Prop :=
  ∀ {γ δ} (hγδ : γ < δ) (hδ : P.mem δ),
    (fam δ hδ).restrict hγδ = fam γ (P.down (SIdx.lt_le_incl hγδ) hδ)

def glue {P : Site} (fam : ∀ γ, P.mem γ → ClosedSol F γ) (hcoh : Coherent fam) :
    PartialSol F P where
  X β hβ := (fam β hβ).top.X
  emb β δ _ hδ hlt := ClosedSol.castDom (hcoh hlt hδ) ((fam δ hδ).top.emb β hlt)
  proj β δ _ hδ hlt := ClosedSol.castCod (hcoh hlt hδ) ((fam δ hδ).top.proj β hlt)
  fold β hβ := (fam β hβ).top.fold
  unfold β hβ := (fam β hβ).top.unfold

section Glued

variable {γ : SI} (IH : ∀ β, β < γ → ClosedSol F β) (T : ClosedSol F γ)
  (hT : ∀ β (h : β < γ), T.restrict h = IH β h)
include hT

theorem coherent_of_restrict : Coherent (P := Site.below γ) IH := fun {β β'} h hβ' =>
  (congrArg (ClosedSol.restrict h) (hT β' hβ')).symm.trans (hT β (SIdx.lt_trans h hβ'))

def gluedTop : Extension (glue (P := Site.below γ) IH (coherent_of_restrict IH T hT)) where
  X := T.top.X
  emb β h := ClosedSol.castDom (hT β h) (T.top.emb β h)
  proj β h := ClosedSol.castCod (hT β h) (T.top.proj β h)
  fold := T.top.fold
  unfold := T.top.unfold

end Glued

theorem gluedTop_lawful {γ} {IH IH' : ∀ β, β < γ → ClosedSol F β} (hIH : IH = IH')
    (T : ClosedSol F γ) {hT : ∀ β (h : β < γ), T.restrict h = IH β h}
    {hT' : ∀ β (h : β < γ), T.restrict h = IH' β h} (h : (gluedTop IH T hT).Lawful) :
    (gluedTop IH' T hT').Lawful := by
  subst hIH; exact h

theorem glued_congr {γ} {IH IH' : ∀ β, β < γ → ClosedSol F β} (hIH : IH = IH')
    (T : ClosedSol F γ) {hT : ∀ β (h : β < γ), T.restrict h = IH β h}
    {hT' : ∀ β (h : β < γ), T.restrict h = IH' β h} {hl hl' ht ht'} :
    (⟨glue (P := Site.below γ) IH (coherent_of_restrict IH T hT), gluedTop IH T hT, hl, ht⟩ :
      ClosedSol F γ) =
      ⟨glue (P := Site.below γ) IH' (coherent_of_restrict IH' T hT'), gluedTop IH' T hT', hl',
        ht'⟩ := by
  subst hIH; rfl

theorem glue_lawful {P : Site} (fam : ∀ γ, P.mem γ → ClosedSol F γ)
    (hcoh : Coherent fam) :
    (glue fam hcoh).Lawful := fun δ hδ =>
  gluedTop_lawful (IH := fun _ h => (fam δ hδ).restrict h)
    (IH' := fun β h => fam β (P.down (SIdx.lt_le_incl h) hδ))
    (funext fun _ => funext fun h => hcoh h hδ) (fam δ hδ) (hT := fun _ _ => rfl)
    (hT' := fun _ h => hcoh h hδ) (fam δ hδ).top_lawful

section Recursion

variable [HasTerminal Obj] [HasSeed F] [Truncatable F] [HasTowerLimits Obj]

def closeTop (α) (f : PartialSol F (Site.below α)) (hf : f.Lawful) : Extension f :=
  match SIdx.case_succ α with
  | .inl h0 => zeroTop h0 f
  | .inr (.inl ⟨_, hm⟩) => succTop hm hf
  | .inr (.inr hl) => limitTop hl f hf

theorem closeTop_lawful (α) (f : PartialSol F (Site.below α)) (hf : f.Lawful) :
    (closeTop α f hf).Lawful := by
  unfold closeTop
  exact match SIdx.case_succ α with
  | .inl h0 => zeroTop_lawful h0 f
  | .inr (.inl ⟨_, hm⟩) => succTop_lawful hm hf
  | .inr (.inr hl) => limitTop_lawful hl f hf

def zeroPoint (f : PartialSol F (Site.below 0)) (hf : f.Lawful) :
    Hom HasTerminal.one (closeTop 0 f hf).X := by
  unfold closeTop
  exact match SIdx.case_succ 0 with
  | .inl _ => EnrichedCat.id _
  | .inr (.inl ⟨_, hm⟩) => absurd hm.symm SIdx.neq_succ_0
  | .inr (.inr hl) => absurd hl SIdx.limit_0

namespace ClosedSol

variable (F) in
def extend (α) (fam : ∀ γ, γ < α → ClosedSol F γ)
    (hcoh : Coherent (P := Site.below α) fam) :
    ClosedSol F α :=
  let hg := glue_lawful (P := Site.below α) fam hcoh
  ⟨glue (P := Site.below α) fam hcoh, closeTop α _ hg, hg, closeTop_lawful α _ hg⟩

theorem extend_restrict {α} (fam : ∀ γ, γ < α → ClosedSol F γ)
    (hcoh : Coherent (P := Site.below α) fam) {γ} (hγ : γ < α) :
    (extend F α fam hcoh).restrict hγ = fam γ hγ :=
  glued_congr (IH := fun β h => fam β (SIdx.lt_trans h hγ))
    (IH' := fun _ h => (fam γ hγ).restrict h) (funext fun _ => funext fun h => (hcoh h hγ).symm)
    (fam γ hγ) (hT := fun _ h => hcoh h hγ) (hT' := fun _ _ => rfl)

variable (F) in
def graph (α) : ClosedSol F α → Prop :=
  (SIdx.lt_wf).fix (C := fun α => ClosedSol F α → Prop) (fun α below t =>
    ∃ (fam : ∀ γ, γ < α → ClosedSol F γ) (_ : ∀ γ hγ, below γ hγ (fam γ hγ))
      (hcoh : Coherent (P := Site.below α) fam),
      t = extend F α fam hcoh) α

theorem graph_iff {α} {t : ClosedSol F α} :
    graph F α t ↔ ∃ (fam : ∀ γ, γ < α → ClosedSol F γ)
      (_ : ∀ γ hγ, graph F γ (fam γ hγ))
      (hcoh : Coherent (P := Site.below α) fam),
      t = extend F α fam hcoh := by
  unfold graph; rw [WellFounded.fix_eq]

theorem graph_unique : ∀ α (t s : ClosedSol F α), graph F α t → graph F α s → t = s := by
  intro α
  induction α using (SIdx.lt_wf).induction with
  | _ α ih =>
    intro t s ht hs
    obtain ⟨tf, htf, _, rfl⟩ := graph_iff.mp ht
    obtain ⟨sf, hsf, _, rfl⟩ := graph_iff.mp hs
    obtain rfl : tf = sf := funext fun γ => funext fun hγ => ih γ hγ _ _ (htf γ hγ) (hsf γ hγ)
    rfl

theorem graph_restrict {γ δ} (hγδ : γ < δ) {t : ClosedSol F δ} {s : ClosedSol F γ}
    (ht : graph F δ t) (hs : graph F γ s) : t.restrict hγδ = s := by
  obtain ⟨fam, hG, hcoh, rfl⟩ := graph_iff.mp ht
  rw [extend_restrict]
  exact graph_unique γ _ s (hG γ hγδ) hs

variable (F) in
@[indexed]
def canonical : ∀ α, {t : ClosedSol F α // graph F α t} :=
  (SIdx.lt_wf).fix fun α ih =>
    ⟨extend F α (fun γ hγ => (ih γ hγ).1) fun hγδ hδ => graph_restrict hγδ (ih _ hδ).2 (ih _ _).2,
      graph_iff.mpr ⟨_, fun γ hγ => (ih γ hγ).2, _, rfl⟩⟩

variable (F) in
theorem canonical_eq (α) : (canonical F α).1 = extend F α (fun γ _ => (canonical F γ).1)
    fun hγδ _ => graph_restrict hγδ (canonical F _).2 (canonical F _).2 := by
  unfold canonical
  rw [WellFounded.fix_eq]

end ClosedSol

variable (F)

variable (SI) in
@[indexed]
def globalSol : PartialSol F (Site.univ : Site) :=
  glue (fun γ _ => (ClosedSol.canonical F γ).1) fun hγδ _ =>
    ClosedSol.graph_restrict hγδ (ClosedSol.canonical F _).2 (ClosedSol.canonical F _).2

theorem globalSol_lawful : (globalSol F).Lawful :=
  glue_lawful (fun γ _ => (ClosedSol.canonical F γ).1) fun hγδ _ =>
    ClosedSol.graph_restrict hγδ (ClosedSol.canonical F _).2 (ClosedSol.canonical F _).2

variable (SI) in
@[indexed]
def Fix : Obj := limObj (globalSol F) (globalSol_lawful F)

@[indexed]
def Fix.fold : Hom (F (Fix F) (Fix F)) (Fix F) :=
  limFold (globalSol F) (globalSol_lawful F)

@[indexed]
def Fix.unfold : Hom (Fix F) (F (Fix F) (Fix F)) :=
  limUnfold Site.univ_isLimit (globalSol F) (globalSol_lawful F)

theorem Fix.fold_comp_unfold : Fix.fold F ⊚ Fix.unfold F = EnrichedCat.id _ :=
  limFold_comp_limUnfold _ _ _

theorem Fix.unfold_comp_fold : Fix.unfold F ⊚ Fix.fold F = EnrichedCat.id _ :=
  OFE.eq_dist.mpr fun _ => limUnfold_comp_limFold _ _ _ trivial

def Fix.point : Hom HasTerminal.one (Fix F) :=
  InvLim.emb (globalSol_lawful F).tower 0 trivial ⊚
    (ClosedSol.canonical_eq F (0 : SI) ▸ zeroPoint _ _ :
      Hom _ (ClosedSol.canonical F 0).1.top.X)

end Recursion

end Solver

section Bifree

variable {Obj : Type u} [EnrichedCat Obj] {F : Obj → Obj → Obj} [EFunctor F]

def Bifree {A B : Obj} (i : Hom (F A A) A) (j : Hom A (F A A)) (f : Hom (F B B) B)
    (g : Hom B (F B B)) (k : Hom B A) (h : Hom A B) : Prop :=
  j ⊚ k = EFunctor.map h k ⊚ g ∧ h ⊚ i = f ⊚ EFunctor.map k h

variable {A B : Obj} (i : Hom (F A A) A) (j : Hom A (F A A)) (f : Hom (F B B) B)
  (g : Hom B (F B B))

def bifreeStep : (Hom B A × Hom A B) -c> (Hom B A × Hom A B) where
  f kh := (i ⊚ EFunctor.map kh.2 kh.1 ⊚ g, f ⊚ EFunctor.map kh.1 kh.2 ⊚ j)
  contractive := ⟨fun h => ⟨comp_dist_r i (comp_dist_l (EFunctor.map_contractive fun m hm =>
    ⟨(h m hm).2, (h m hm).1⟩) g), comp_dist_r f (comp_dist_l (EFunctor.map_contractive h) j)⟩⟩

variable {i j} (hij : i ⊚ j = EnrichedCat.id _) (hji : j ⊚ i = EnrichedCat.id _)
include hij hji

omit [SIdxSucc] in
theorem bifree_iff {k : Hom B A} {h : Hom A B} :
    Bifree i j f g k h ↔ (k, h) = bifreeStep i j f g (k, h) := by
  refine ⟨fun ⟨hk, hh⟩ => Prod.ext ?_ ?_, fun e => ⟨?_, ?_⟩⟩
  · change k = i ⊚ EFunctor.map h k ⊚ g
    rw [← hk, ← EnrichedCat.assoc, hij, EnrichedCat.id_comp]
  · change h = f ⊚ EFunctor.map k h ⊚ j
    rw [← EnrichedCat.assoc, ← hh, EnrichedCat.assoc, hij, EnrichedCat.comp_id]
  · calc j ⊚ k = j ⊚ (i ⊚ EFunctor.map h k ⊚ g) := congrArg (j ⊚ ·) (congrArg Prod.fst e)
      _ = EFunctor.map h k ⊚ g := by rw [← EnrichedCat.assoc, hji, EnrichedCat.id_comp]
  · calc h ⊚ i = (f ⊚ EFunctor.map k h ⊚ j) ⊚ i := congrArg (· ⊚ i) (congrArg Prod.snd e)
      _ = f ⊚ EFunctor.map k h := by rw [EnrichedCat.assoc, EnrichedCat.assoc, hji, EnrichedCat.comp_id]

omit [SIdxSucc] in
theorem bifree_unique [Inhabited (Hom B A)] [Inhabited (Hom A B)] {k k' : Hom B A}
    {h h' : Hom A B} (h₁ : Bifree i j f g k h) (h₂ : Bifree i j f g k' h') : k = k' ∧ h = h' :=
  Prod.ext_iff.mp ((fixpoint_unique ((bifree_iff f g hij hji).mp h₁)).trans
    (fixpoint_unique ((bifree_iff f g hij hji).mp h₂)).symm)

omit [SIdxSucc] in
theorem bifree_exists [Inhabited (Hom B A)] [Inhabited (Hom A B)] :
    Bifree i j f g (fixpoint (bifreeStep i j f g)).1
      (fixpoint (bifreeStep i j f g)).2 :=
  (bifree_iff f g hij hji).mpr (fixpoint_unfold (bifreeStep i j f g))

omit hij hji in
omit [SIdxSucc] in
theorem bifree_id : Bifree i j i j (EnrichedCat.id A) (EnrichedCat.id A) := by
  constructor <;> simp [EFunctor.map_id]

omit hij hji in
omit [SIdxSucc] in
theorem bifree_comp {i' : Hom (F B B) B} {j' : Hom B (F B B)} {k : Hom B A}
    {h : Hom A B} {k' : Hom A B} {h' : Hom B A} (e : Bifree i j i' j' k h)
    (e' : Bifree i' j' i j k' h') :
    Bifree i j i j (k ⊚ k') (h' ⊚ h) := by
  constructor
  · rw [← EnrichedCat.assoc, e.1, EnrichedCat.assoc, e'.1, ← EnrichedCat.assoc, ← EFunctor.map_comp]
  · rw [EnrichedCat.assoc, e.2, ← EnrichedCat.assoc, e'.2, EnrichedCat.assoc, ← EFunctor.map_comp]

omit f g in
omit [SIdxSucc] in
theorem solution_unique {i' : Hom (F B B) B} {j' : Hom B (F B B)}
    (hij' : i' ⊚ j' = EnrichedCat.id _) (hji' : j' ⊚ i' = EnrichedCat.id _) [Inhabited (Hom B A)]
    [Inhabited (Hom A B)] :
    ∃ (u : Hom A B) (v : Hom B A), u ⊚ v = EnrichedCat.id _ ∧ v ⊚ u = EnrichedCat.id _ := by
  haveI : ∀ C : Obj, Inhabited (Hom C C) := fun C => ⟨EnrichedCat.id C⟩
  exact ⟨_, _, (bifree_unique i' j' hij' hji'
      (bifree_comp (bifree_exists i j hij' hji') (bifree_exists i' j' hij hji)) bifree_id).1,
    (bifree_unique i j hij hji
      (bifree_comp (bifree_exists i' j' hij hji) (bifree_exists i j hij' hji')) bifree_id).1⟩

end Bifree

end Iris.Enriched
