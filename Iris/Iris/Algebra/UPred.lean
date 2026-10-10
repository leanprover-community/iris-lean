/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.COFESolver

@[expose] public section

namespace Iris

variable {SI : stepindex (Type _)} [instSI : SIdx SI]
local stepindex SI
open ORA

-- EXPERIMENT: UPred Leibniz by construction
-- https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean/topic/Bi-entailment.20and.20generalized.20rewriting/with/565019365
@[indexed, ext]
structure ValidAt (M : Type _) [URA M] [UORA M] (n : SI) where
  val : M
  property : ✓{n} val

instance {M : Type _} [URA M] [UORA M] {n : SI} : CoeOut (ValidAt M n) M where
  coe := (·.val)

def ValidAt.le {M : Type _} [URA M] [UORA M] {n m : SI} (Hle : m ≤ n) : ValidAt M n → ValidAt M m :=
  fun v => ⟨v.val, validN_of_le Hle v.property⟩

@[simp]
theorem ValidAt.le_val {M : Type _} [URA M] [UORA M] {n m : SI} {Hle : m ≤ n} {v : ValidAt M n} :
  (v.le Hle).val = v.val := by rfl

@[simp]
theorem ValidAt.le_rfl {M : Type _} [URA M] [UORA M] {n : SI} {Hle : n ≤ n} {v : ValidAt M n} :
  v.le Hle = v := by rfl

/-- The data of a UPred object is an indexed proposition over M (Bundled version) -/
@[indexed, ext, rocq_alias uPred]
structure UPred (M : Type _) [URA M] [UORA M] where
  holds : (n : SI) → ValidAt M n → Prop
  mono {n1 n2 : SI} {x1 : ValidAt M n1} {x2 : ValidAt M n2} :
    holds n1 x1 → (x1 : M) ≼ₒ{n2} (x2 : M) → (Hle : n2 ≤ n1) → holds n2 x2

def UPred.holds_unpacked {M : Type _} [URA M] [UORA M] (P : UPred M) (n : SI) (x : M) (Hx : ✓{n} x) :
    Prop :=
  P.holds n ⟨x, Hx⟩

theorem UPred.mono_unpacked {M : Type _} [URA M] [UORA M] (P : UPred M) {n1 n2 : SI} {x1 x2 : M}
    (Hx1 : ✓{n1} x1) (Hx2 : ✓{n2} x2) (HP : P.holds_unpacked n1 x1 Hx1) (Hxle : x1 ≼ₒ{n2} x2)
    (Hle : n2 ≤ n1) : P.holds_unpacked n2 x2 Hx2 :=
  P.mono HP Hxle Hle

/-- The definition of UPred is equivalent to separately proving pointwise down-closure,
non-expansivity, and monotonicity. -/
@[rocq_alias uPred_alt]
theorem uPred_alt {M : Type _} [URA M] [UORA M] (P : SI → M → Prop) :
    (∀ {n1 n2 : SI} {x1 x2 : M}, P n1 x1 → x1 ≼ₒ{n1} x2 → n2 ≤ n1 → P n2 x2) ↔
    ((∀ {x : M} {n1 n2 : SI}, n2 ≤ n1 → P n1 x → P n2 x) ∧
     (∀ {n : SI} {x1 x2 : M}, x1 ≡{n}≡ x2 → ∀ (m : SI), m ≤ n → (P m x1 ↔ P m x2)) ∧
     (∀ {n : SI} {x1 x2 : M}, x1 ≼ₒ{n} x2 → ∀ (m : SI), m ≤ n → P m x1 → P m x2)) := by
  constructor
  · intro H
    refine ⟨fun Hle HP => H HP .rfl Hle, ?_, ?_⟩
    · refine fun He m Hm => ⟨fun HP => ?_, fun HP => ?_⟩
      · exact H HP (ordN_of_dist_of_ordN (He.le Hm) .rfl) SIdx.le_refl
      · exact H HP (ordN_of_dist_of_ordN (He.le Hm).symm .rfl) SIdx.le_refl
    · exact fun Hinc m Hm HP => H HP (ordN_of_ordN_le Hm Hinc) SIdx.le_refl
  · refine fun ⟨Hdc, _, Hmono⟩ n1 n2 x1 x2 HP Hinc Hle => ?_
    exact Hmono (ordN_of_ordN_le Hle Hinc) n2 SIdx.le_refl (Hdc Hle HP)

instance [URA M] [UORA M] : Inhabited (UPred M) := ⟨fun _ _ => True, fun _ _ _ => ⟨⟩⟩

instance [URA M] [UORA M] : CoeFun (UPred M) (fun _ => (n : SI) → ValidAt M n → Prop) where
  coe x := x.holds

section UPred

variable [URA M] [UORA M]

open UPred

@[rocq_alias uPredO]
instance : OFE (UPred M) where
  dist n P Q := ∀ (n' : SI) (x : M), n' ≤ n → (p : ✓{n'} x) → (P n' ⟨x, p⟩ ↔ Q n' ⟨x, p⟩)
  dist_eqv := {
    refl _ _ _ _ _ := .rfl
    symm H _ _ A B := (H _ _ A B).symm
    trans H1 H2 _ _ A B := (H1 _ _ A B).trans (H2 _ _ A B) }
  eq_dist' {P Q} := by
    refine ⟨fun h _ _ _ _ _ => h ▸ Iff.rfl, fun h => ?_⟩
    ext n e
    exact h n n e.val SIdx.le_refl e.property
  dist_lt Hdist Hlt _ _ Hle Hvalid :=
    Hdist _ _ (SIdx.le_trans Hle (SIdx.lt_le_incl Hlt)) Hvalid

#rocq_ignore uPred_equiv' "Inlined in the `OFE` construction"
#rocq_ignore uPred_equiv "Not needed"
#rocq_ignore uPred_dist' "Inlined in the `OFE` construction"
#rocq_ignore uPred_dist "Not needed"
#rocq_ignore uPred_ofe_mixin "Not needed"


@[rocq_alias uPred_ne]
theorem uPred_ne {P : UPred M} {n : SI} {m₁ m₂ : ValidAt M n} (H : (m₁ : M) ≡{n}≡ (m₂ : M)) : P n m₁ ↔ P n m₂ :=
  ⟨fun H' => P.mono H' H.to_ordN SIdx.le_refl, fun H' => P.mono H' H.symm.to_ordN SIdx.le_refl⟩

#rocq_ignore uPred_proper "OFE is Leibniz; use equality"

@[rocq_alias uPred_holds_ne]
theorem uPred_holds_ne {P Q : UPred M} {n₁ n₂ : SI} {x : M}
    (HPQ : P ≡{n₂}≡ Q) (Hn : n₂ ≤ n₁) (Hx : ✓{n₂} x) (Hx' : ✓{n₁} x) (HQ : Q n₁ ⟨x, Hx'⟩) : P n₂ ⟨x, Hx⟩ :=
  (HPQ _ _ SIdx.le_refl Hx).mpr (Q.mono HQ .rfl Hn)

@[rocq_alias uPred_cofe]
instance : IsCOFE (UPred M) where
  compl c := {
    holds n x := ∀ n', (Hle : n' ≤ n) → (c n') n' (x.le Hle)
    mono {n1 n2 : SI} {x1 x2 HP Hx12 Hn12 n3 Hn23} := by
      refine mono _ (HP n3 (SIdx.le_trans Hn23 Hn12)) ?_ SIdx.le_refl
      exact Hx12.le Hn23
  }
  conv_compl {n : SI} {c i x} Hin Hv := by
    refine .trans ?_ (c.cauchy Hin _ _ SIdx.le_refl Hv).symm
    refine ⟨fun H => H _ SIdx.le_refl, fun H n' Hn' => ?_⟩
    exact (c.cauchy Hn' _ _ SIdx.le_refl _).mp (mono _ H .rfl Hn')
  lbcompl {n : SI} _ c := {
    holds k x := ∀ (k' : SI), (Hle : k' ≤ k) → (Hlt : k' < n) → (c.bchain k' Hlt) k' (x.le Hle)
    mono {k1 k2 : SI} {x1 x2 HP Hx12 Hk12 k Hk Hlt} := by
      refine mono _ (HP k (SIdx.le_trans Hk Hk12) Hlt) ?_ SIdx.le_refl
      exact Hx12.le Hk
  }
  conv_lbcompl {n : SI} _ c (m : SI) Hm (k : SI) x Hk Hv := by
    refine ⟨fun H => ?_, fun H k' Hk' Hlt => ?_⟩
    · have Hlt := SIdx.le_lt_trans Hk Hm
      exact (c.bcauchy Hlt Hm Hk _ _ SIdx.le_refl Hv).mpr (H k SIdx.le_refl Hlt)
    · refine (c.bcauchy Hlt Hm (SIdx.le_trans Hk' Hk) _ _ SIdx.le_refl _).mp ?_
      exact mono _ H .rfl Hk'
  lbcompl_ne _ _ _ _ Hc (k : SI) x Hk _ :=
    forall_congr' fun k' => forall_congr' fun Hk' => forall_congr' fun Hlt =>
      Hc k' Hlt k' x (SIdx.le_trans Hk' Hk) _

#rocq_ignore uPred_compl "Inlined in the `IsCOFE` construction"

def UPred.truncate (K : Enriched.LimitCut SI) : UPred M -n> UPred M where
  f P := {
    holds n x := ∀ (m : SI), K.mem m → (Hle : m ≤ n) → P m (x.le Hle)
    mono {n1 n2 : SI} {x1 x2 HP Hx12 Hn12 m Hm Hle} := by
      refine P.mono (HP m Hm (SIdx.le_trans Hle Hn12)) ?_ SIdx.le_refl
      exact Hx12.le Hle
  }
  ne.ne _ _ _ HPQ (n : SI) x Hn _ :=
    forall_congr' fun m => forall_congr' fun _ => forall_congr' fun Hle =>
      HPQ m x (SIdx.le_trans Hle Hn) _

def UPred.truncation (K : Enriched.LimitCut SI) : Enriched.COFE.Truncation K (UPred M) where
  truncate := UPred.truncate K
  conv P _ HK (n : SI) _ Hn _ :=
    ⟨fun H => H n (K.down Hn HK) SIdx.le_refl, fun H _ _ Hle => P.mono H .rfl Hle⟩
  truncated _ _ HPQ := by
    ext (n : SI) x
    exact forall_congr' fun m => forall_congr' fun Hm => forall_congr' fun _ =>
      HPQ m Hm m _ SIdx.le_refl _

abbrev UPredOF (F : COFE.OFunctorPre) [URFunctor F] : COFE.OFunctorPre :=
  fun A B _ _ => UPred (F B A)

@[rocq_alias uPredO_map]
def uPred_map [URA α] [UORA α] [URA β] [UORA β] (f : β -C> α) : UPred α -n> UPred β := by
  refine ⟨fun P => ⟨fun n x => P n ⟨(f x.val), f.validN x.property⟩, ?_⟩, ⟨?_⟩⟩
  · intro n1 n2 x1 x2 HP Hm Hn
    exact P.mono HP (f.monoN_ord Hm) Hn
  · intro n x1 x2 Hx1x2 n' y Hn' Hv
    exact Hx1x2 _ _ Hn' (f.validN Hv)

#rocq_ignore uPred_map "Inlined in `uPred_map`"
#rocq_ignore uPred_map_ne "Inlined in the bundled `-n>` of `uPred_map`."

@[rocq_alias uPredOF]
instance [URFunctor F] : COFE.OFunctor (UPredOF F) where
  ofe := inferInstance
  map f g := uPred_map (URFunctor.map (F := F) g f)
  map_ne.ne _ _ _ Hx _ _ Hy _ _ z2 Hn _ := by
    simp only [uPred_map]
    exact uPred_ne <| URFunctor.map_ne.ne (Hy.le Hn) (Hx.le Hn) z2
  map_id x := OFE.eq_dist_2 <| by
    intro (_ : SI) _ z _ _
    simp only [uPred_map]
    simp only [URFunctor.map_id]
  map_comp f g f' g' x := OFE.eq_dist_2 <| by
    intro (_ : SI) _ H _ _
    simp only [uPred_map]
    simp only [URFunctor.map_comp]

#rocq_ignore uPredO_map_ne "Inlined as the `map_ne` field of the `COFE.OFunctor (UPredOF F)` instance."
#rocq_ignore uPred_map_id "Inlined as the `map_id` field of the `COFE.OFunctor (UPredOF F)` instance."
#rocq_ignore uPred_map_compose "Inlined as the `map_comp` field of the `COFE.OFunctor (UPredOF F)` instance."
#rocq_ignore uPred_map_ext "Inlined as the `map_ne` field of the `COFE.OFunctor (UPredOF F)` instance."

@[rocq_alias uPredOF_contractive]
instance instUPredOFunctorContractive [URFunctorContractive F] : COFE.OFunctorContractive (UPredOF F) where
  map_contractive.1 {n : SI} {x y} HKL := by
    intro P (m : SI) a Hmn Ha
    refine uPred_ne (P := P) <|
      ((URFunctorContractive.map_contractive.1 (x := (x.snd, x.fst)) (y := (y.snd, y.fst))) ?_ a).le Hmn
    exact fun m Hm => ⟨(HKL m Hm).2, (HKL m Hm).1⟩

instance instUPredOFTruncatable [URFunctorContractive F] :
    Enriched.Truncatable SI (Enriched.COFE.oFunctorObj (UPredOF F)) :=
  Enriched.COFE.truncatableOfTruncations _ fun K _ _ => UPred.truncation K

end UPred

end Iris
