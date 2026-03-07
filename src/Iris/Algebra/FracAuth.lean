import Iris.Algebra.Auth

namespace Iris

abbrev FracAuth (Q : Type _) (A : Type _) [UFraction Q] [CMRA A] :=
  Auth Q (Option (Frac Q × A))

namespace FracAuth

open COFE OFE CMRA Auth

variable {Q A : Type _} [UFraction Q] [CMRA A]

def wholeFrac : Frac Q :=
  ((1 : Q) : Frac Q)

def fracAuthElem (q : Frac Q) (a : A) : Option (Frac Q × A) :=
  some (q, a)

def fracAuthAuth (dq : DFrac Q) (a : A) : FracAuth Q A :=
  ●{dq} (fracAuthElem (wholeFrac (Q := Q)) a)

def fracAuthAuthFull (a : A) : FracAuth Q A :=
  fracAuthAuth (Q := Q) (DFrac.own (1 : Q)) a

def fracAuthAuthDiscarded (a : A) : FracAuth Q A :=
  fracAuthAuth (Q := Q) DFrac.discard a

def fracAuthFrag (q : Q) (a : A) : FracAuth Q A :=
  ◯ (fracAuthElem ((q : Q) : Frac Q) a)

theorem fracAuthElem_validN (n : Nat) (q : Frac Q) (a : A) :
    ✓{n} fracAuthElem q a ↔ ✓ q ∧ ✓{n} a := by
  change ✓{n} ((q, a) : Frac Q × A) ↔ ✓ q ∧ ✓{n} a
  simp [CMRA.ValidN, CMRA.Valid]

theorem fracAuthElem_valid (q : Frac Q) (a : A) :
    ✓ fracAuthElem q a ↔ ✓ q ∧ ✓ a := by
  change ✓ ((q, a) : Frac Q × A) ↔ ✓ q ∧ ✓ a
  simp [CMRA.Valid]

instance fracAuthElem_one_exclusive (a : A) :
    CMRA.Exclusive ((wholeFrac (Q := Q), a) : Frac Q × A) where
  exclusive0_l := by
    rintro ⟨q, _⟩ ⟨hq, _⟩
    refine (UFraction.one_whole (α := Q)).2 ?_
    exact ⟨q.1, by simpa [wholeFrac, CMRA.op, CMRA.ValidN] using hq⟩

theorem fracAuth_dfrac_validN (dq : DFrac Q) (n : Nat) (a : A) :
    ✓ dq → ✓{n} a → ✓{n} (fracAuthAuth (Q := Q) dq a • fracAuthFrag (1 : Q) a) := by
  intro hdq ha
  change ✓{n} ((●{dq} fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) •
      ◯ fracAuthElem (wholeFrac (Q := Q)) a)
  rw [Auth.both_dfrac_validN]
  refine ⟨hdq, CMRA.incN_refl _, ?_⟩
  exact (fracAuthElem_validN (Q := Q) (A := A) n (wholeFrac (Q := Q)) a).2
    ⟨UFraction.one_whole.1, ha⟩

theorem fracAuth_validN (n : Nat) (a : A) :
    ✓{n} a → ✓{n} (fracAuthAuthFull (Q := Q) a • fracAuthFrag (1 : Q) a) :=
  fracAuth_dfrac_validN (Q := Q) (dq := DFrac.own (1 : Q)) n a DFrac.valid_own_one

theorem fracAuth_dfrac_valid (dq : DFrac Q) (a : A) :
    ✓ dq → ✓ a → ✓ (fracAuthAuth (Q := Q) dq a • fracAuthFrag (1 : Q) a) := by
  intro hdq ha
  change ✓ ((●{dq} fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) •
      ◯ fracAuthElem (wholeFrac (Q := Q)) a)
  refine Auth.auth_both_dfrac_valid_2 hdq ?_ (CMRA.inc_refl _)
  exact (fracAuthElem_valid (Q := Q) (A := A) (wholeFrac (Q := Q)) a).2
    ⟨UFraction.one_whole.1, ha⟩

theorem fracAuth_valid (a : A) :
    ✓ a → ✓ (fracAuthAuthFull (Q := Q) a • fracAuthFrag (1 : Q) a) :=
  fracAuth_dfrac_valid (Q := Q) (dq := DFrac.own (1 : Q)) a DFrac.valid_own_one

theorem fracAuth_agreeN (n : Nat) (dq : DFrac Q) (a b : A) :
    ✓{n} (fracAuthAuth (Q := Q) dq a • fracAuthFrag (1 : Q) b) → a ≡{n}≡ b := by
  intro h
  change ✓{n} ((●{dq} fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) •
      ◯ fracAuthElem (wholeFrac (Q := Q)) b) at h
  obtain ⟨_, hinc, hv⟩ := (Auth.both_dfrac_validN
    (F := Q) (a := fracAuthElem (wholeFrac (Q := Q)) a)
    (b := fracAuthElem (wholeFrac (Q := Q)) b)).1 h
  have hvPair : ✓{n} ((wholeFrac (Q := Q), a) : Frac Q × A) := by
    simpa [wholeFrac] using hv
  have hpair :
      ((wholeFrac (Q := Q), b) : Frac Q × A) ≡{n}≡ ((wholeFrac (Q := Q), a) : Frac Q × A) :=
    Option.dist_of_inc_exclusive
      (a := ((wholeFrac (Q := Q), b) : Frac Q × A))
      (b := ((wholeFrac (Q := Q), a) : Frac Q × A))
      hinc hvPair
  simpa using (OFE.dist_snd hpair).symm

theorem fracAuth_agree (dq : DFrac Q) (a b : A) :
    ✓ (fracAuthAuth (Q := Q) dq a • fracAuthFrag (1 : Q) b) → a ≡ b := by
  intro h
  refine equiv_dist.mpr fun n => ?_
  exact fracAuth_agreeN (Q := Q) n dq a b h.validN

theorem fracAuth_agree_L [Leibniz A] (dq : DFrac Q) (a b : A) :
    ✓ (fracAuthAuth (Q := Q) dq a • fracAuthFrag (1 : Q) b) → a = b :=
  Leibniz.eq_of_eqv ∘ fracAuth_agree (Q := Q) dq a b

theorem fracAuth_includedN (n : Nat) (dq : DFrac Q) (q : Q) (a b : A) :
    ✓{n} (fracAuthAuth (Q := Q) dq a • fracAuthFrag q b) → (some b : Option A) ≼{n} some a := by
  intro h
  change ✓{n} ((●{dq} fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) •
      ◯ fracAuthElem ((q : Q) : Frac Q) b) at h
  obtain ⟨_, hinc, _⟩ := (Auth.both_dfrac_validN
    (F := Q) (a := fracAuthElem (wholeFrac (Q := Q)) a)
    (b := fracAuthElem ((q : Q) : Frac Q) b)).1 h
  rcases Option.some_incN_some_iff_opM.mp hinc with ⟨mz, hmz⟩
  cases mz with
  | none =>
      exact Option.some_inc_some_of_dist_opM (x := a) (y := b) (mz := none) (OFE.dist_snd hmz)
  | some z =>
      exact Option.some_inc_some_of_dist_opM (x := a) (y := b) (mz := some z.2) (OFE.dist_snd hmz)

theorem fracAuth_included [CMRA.Discrete A] (dq : DFrac Q) (q : Q) (a b : A) :
    ✓ (fracAuthAuth (Q := Q) dq a • fracAuthFrag q b) → (some b : Option A) ≼ some a := by
  intro h
  exact (CMRA.inc_iff_incN (α := Option A) 0).mpr <|
    fracAuth_includedN (Q := Q) 0 dq q a b h.validN

theorem fracAuth_includedN_total [CMRA.IsTotal A] (n : Nat) (dq : DFrac Q) (q : Q) (a b : A) :
    ✓{n} (fracAuthAuth (Q := Q) dq a • fracAuthFrag q b) → b ≼{n} a :=
  Option.some_incN_some_iff_isTotal.mp ∘ fracAuth_includedN (Q := Q) n dq q a b

theorem fracAuth_included_total [CMRA.Discrete A] [CMRA.IsTotal A] (dq : DFrac Q) (q : Q)
    (a b : A) :
    ✓ (fracAuthAuth (Q := Q) dq a • fracAuthFrag q b) → b ≼ a :=
  Option.some_inc_some_iff_isTotal.mp ∘ fracAuth_included (Q := Q) dq q a b

theorem fracAuth_auth_dfrac_validN (n : Nat) (dq : DFrac Q) (a : A) :
    ✓{n} (fracAuthAuth (Q := Q) dq a) ↔ ✓ dq ∧ ✓{n} a := by
  change (✓{n} (●{dq} fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A)) ↔ ✓ dq ∧ ✓{n} a
  rw [Auth.auth_dfrac_validN, fracAuthElem_validN]
  constructor
  · rintro ⟨hdq, _, ha⟩
    exact ⟨hdq, ha⟩
  · rintro ⟨hdq, ha⟩
    exact ⟨hdq, UFraction.one_whole.1, ha⟩

theorem fracAuth_auth_validN (n : Nat) (a : A) :
    ✓{n} (fracAuthAuthFull (Q := Q) a) ↔ ✓{n} a := by
  rw [fracAuthAuthFull, fracAuth_auth_dfrac_validN]
  constructor
  · exact fun ⟨_, ha⟩ => ha
  · exact fun ha => ⟨DFrac.valid_own_one, ha⟩

theorem fracAuth_auth_dfrac_valid (dq : DFrac Q) (a : A) :
    ✓ (fracAuthAuth (Q := Q) dq a) ↔ ✓ dq ∧ ✓ a := by
  change (✓ (●{dq} fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A)) ↔ ✓ dq ∧ ✓ a
  rw [Auth.auth_dfrac_valid, fracAuthElem_valid]
  constructor
  · rintro ⟨hdq, _, ha⟩
    exact ⟨hdq, ha⟩
  · rintro ⟨hdq, ha⟩
    exact ⟨hdq, UFraction.one_whole.1, ha⟩

theorem fracAuth_auth_valid (a : A) :
    ✓ (fracAuthAuthFull (Q := Q) a) ↔ ✓ a := by
  rw [fracAuthAuthFull, fracAuth_auth_dfrac_valid]
  constructor
  · exact fun ⟨_, ha⟩ => ha
  · exact fun ha => ⟨DFrac.valid_own_one, ha⟩

theorem fracAuth_frag_validN (n : Nat) (q : Q) (a : A) :
    ✓{n} (fracAuthFrag (Q := Q) q a) ↔ Fraction.Proper q ∧ ✓{n} a := by
  change (✓{n} (◯ fracAuthElem ((q : Q) : Frac Q) a : FracAuth Q A)) ↔
      Fraction.Proper q ∧ ✓{n} a
  simpa [CMRA.ValidN, CMRA.Valid] using
    (Auth.frag_validN (F := Q) (b := fracAuthElem ((q : Q) : Frac Q) a))

theorem fracAuth_frag_valid (q : Q) (a : A) :
    ✓ (fracAuthFrag (Q := Q) q a) ↔ Fraction.Proper q ∧ ✓ a := by
  change (✓ (◯ fracAuthElem ((q : Q) : Frac Q) a : FracAuth Q A)) ↔
      Fraction.Proper q ∧ ✓ a
  simpa [CMRA.ValidN, CMRA.Valid] using
    (Auth.frag_valid (F := Q) (b := fracAuthElem ((q : Q) : Frac Q) a))

theorem fracAuth_auth_dfrac_op (dq1 dq2 : DFrac Q) (a : A) :
    fracAuthAuth (Q := Q) (dq1 • dq2) a ≡
      fracAuthAuth dq1 a • fracAuthAuth dq2 a := by
  change (●{dq1 • dq2} fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) ≡
      (●{dq1} fracAuthElem (wholeFrac (Q := Q)) a) • ●{dq2} fracAuthElem (wholeFrac (Q := Q)) a
  simpa using (Auth.auth_dfrac_op (F := Q) (dq1 := dq1) (dq2 := dq2)
    (a := fracAuthElem (wholeFrac (Q := Q)) a))

theorem fracAuth_frag_op (q1 q2 : Q) (a1 a2 : A) :
    fracAuthFrag (Q := Q) (q1 + q2) (a1 • a2) ≡
      fracAuthFrag q1 a1 • fracAuthFrag q2 a2 := by
  change (◯ fracAuthElem (((q1 + q2 : Q)) : Frac Q) (a1 • a2) : FracAuth Q A) ≡
      (◯ fracAuthElem ((q1 : Q) : Frac Q) a1 : FracAuth Q A) •
        (◯ fracAuthElem ((q2 : Q) : Frac Q) a2 : FracAuth Q A)
  have h := (Auth.frag_op (F := Q)
    (b1 := fracAuthElem ((q1 : Q) : Frac Q) a1)
    (b2 := fracAuthElem ((q2 : Q) : Frac Q) a2)).symm
  have h' :
      (◯ fracAuthElem (((q1 + q2 : Q)) : Frac Q) (a1 • a2) : FracAuth Q A) =
        (◯ fracAuthElem ((q1 : Q) : Frac Q) a1 : FracAuth Q A) •
          (◯ fracAuthElem ((q2 : Q) : Frac Q) a2 : FracAuth Q A) := by
    simpa [fracAuthElem, CMRA.op] using h
  exact OFE.Equiv.of_eq h'

theorem fracAuth_auth_dfrac_op_validN (n : Nat) (dq1 dq2 : DFrac Q) (a b : A) :
    ✓{n} (fracAuthAuth (Q := Q) dq1 a • fracAuthAuth dq2 b) →
      ✓ (dq1 • dq2) ∧ a ≡{n}≡ b := by
  intro h
  change ✓{n} ((●{dq1} fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) •
      ●{dq2} fracAuthElem (wholeFrac (Q := Q)) b) at h
  obtain ⟨hdq, hpair, _⟩ := (Auth.auth_dfrac_op_validN
    (F := Q) (a1 := fracAuthElem (wholeFrac (Q := Q)) a)
    (a2 := fracAuthElem (wholeFrac (Q := Q)) b)).1 h
  exact ⟨hdq, OFE.dist_snd (Option.dist_of_some_dist_some hpair)⟩

theorem fracAuth_auth_op_validN (n : Nat) (a b : A) :
    ✓{n} (fracAuthAuthFull (Q := Q) a • fracAuthAuthFull b) → False := by
  intro h
  change ✓{n} ((● fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) •
      ● fracAuthElem (wholeFrac (Q := Q)) b) at h
  exact (Auth.auth_op_validN (F := Q)
    (a1 := fracAuthElem (wholeFrac (Q := Q)) a)
    (a2 := fracAuthElem (wholeFrac (Q := Q)) b)).1 h

theorem fracAuth_auth_dfrac_op_valid (dq1 dq2 : DFrac Q) (a b : A) :
    ✓ (fracAuthAuth (Q := Q) dq1 a • fracAuthAuth dq2 b) →
      ✓ (dq1 • dq2) ∧ a ≡ b := by
  intro h
  refine ⟨(fracAuth_auth_dfrac_op_validN (Q := Q) 0 dq1 dq2 a b h.validN).1, ?_⟩
  exact equiv_dist.mpr fun n => (fracAuth_auth_dfrac_op_validN (Q := Q) n dq1 dq2 a b h.validN).2

theorem fracAuth_auth_op_valid (a b : A) :
    ✓ (fracAuthAuthFull (Q := Q) a • fracAuthAuthFull b) → False := by
  intro h
  exact fracAuth_auth_op_validN (Q := Q) 0 a b h.validN

theorem fracAuth_frag_op_validN (n : Nat) (q1 q2 : Q) (a b : A) :
    ✓{n} (fracAuthFrag (Q := Q) q1 a • fracAuthFrag q2 b) ↔
      Fraction.Proper (q1 + q2) ∧ ✓{n} (a • b) := by
  change (✓{n} (((◯ fracAuthElem ((q1 : Q) : Frac Q) a : FracAuth Q A) •
      (◯ fracAuthElem ((q2 : Q) : Frac Q) b : FracAuth Q A)))) ↔
      Fraction.Proper (q1 + q2) ∧ ✓{n} (a • b)
  rw [Auth.frag_op_validN]
  simpa [fracAuthElem, CMRA.op] using
    (fracAuthElem_validN (Q := Q) (A := A) n ((((q1 + q2 : Q)) : Frac Q)) (a • b))

theorem fracAuth_frag_op_valid (q1 q2 : Q) (a b : A) :
    ✓ (fracAuthFrag (Q := Q) q1 a • fracAuthFrag q2 b) ↔
      Fraction.Proper (q1 + q2) ∧ ✓ (a • b) := by
  change (✓ (((◯ fracAuthElem ((q1 : Q) : Frac Q) a : FracAuth Q A) •
      (◯ fracAuthElem ((q2 : Q) : Frac Q) b : FracAuth Q A)))) ↔
      Fraction.Proper (q1 + q2) ∧ ✓ (a • b)
  rw [Auth.frag_op_valid]
  simpa [fracAuthElem, CMRA.op] using
    (fracAuthElem_valid (Q := Q) (A := A) ((((q1 + q2 : Q)) : Frac Q)) (a • b))

theorem fracAuth_update (q : Q) (a b a' b' : A) :
    (a, b) ~l~> (a', b') →
      fracAuthAuthFull (Q := Q) a • fracAuthFrag q b ~~>
        fracAuthAuthFull a' • fracAuthFrag q b' := by
  intro hup
  change ((● fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) •
      ◯ fracAuthElem ((q : Q) : Frac Q) b) ~~>
        ((● fracAuthElem (wholeFrac (Q := Q)) a' : FracAuth Q A) •
          ◯ fracAuthElem ((q : Q) : Frac Q) b')
  apply Auth.auth_update
  exact LocalUpdate.option <|
    LocalUpdate.prod_2 (x1 := wholeFrac (Q := Q)) (y1 := ((q : Q) : Frac Q)) hup

theorem fracAuth_update_1 (a b a' : A) :
    ✓ a' → fracAuthAuthFull (Q := Q) a • fracAuthFrag (1 : Q) b ~~>
      fracAuthAuthFull a' • fracAuthFrag (1 : Q) a' := by
  intro ha'
  change ((● fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) •
      ◯ fracAuthElem (wholeFrac (Q := Q)) b) ~~>
        ((● fracAuthElem (wholeFrac (Q := Q)) a' : FracAuth Q A) •
          ◯ fracAuthElem (wholeFrac (Q := Q)) a')
  apply Auth.auth_update
  apply LocalUpdate.option
  refine LocalUpdate.exclusive (y := (wholeFrac (Q := Q), b)) ?_
  exact (fracAuthElem_valid (Q := Q) (A := A) (wholeFrac (Q := Q)) a').2
    ⟨UFraction.one_whole.1, ha'⟩

theorem fracAuth_update_auth_persist (dq : DFrac Q) (a : A) :
    fracAuthAuth (Q := Q) dq a ~~> fracAuthAuthDiscarded a := by
  change (●{dq} fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) ~~>
      ●{DFrac.discard} fracAuthElem (wholeFrac (Q := Q)) a
  simpa [fracAuthAuth, fracAuthAuthDiscarded] using
    (Auth.auth_update_auth_persist (F := Q)
      (dq := dq) (a := fracAuthElem (wholeFrac (Q := Q)) a))

theorem fracAuth_updateP_auth_unpersist [IsSplitFraction Q] (a : A) :
    fracAuthAuthDiscarded (Q := Q) a ~~>:
      fun k => ∃ q, k = fracAuthAuth (Q := Q) (DFrac.own q) a := by
  change (●{DFrac.discard} fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) ~~>:
      fun k => ∃ q, k = ●{DFrac.own q} fracAuthElem (wholeFrac (Q := Q)) a
  simpa [fracAuthAuth, fracAuthAuthDiscarded] using
    (Auth.auth_updateP_auth_unpersist (F := Q)
      (a := fracAuthElem (wholeFrac (Q := Q)) a))

theorem fracAuth_updateP_both_unpersist [IsSplitFraction Q] (q : Q) (a b : A) :
    fracAuthAuthDiscarded (Q := Q) a • fracAuthFrag q b ~~>:
      fun k => ∃ q', k = fracAuthAuth (Q := Q) (DFrac.own q') a • fracAuthFrag q b := by
  change ((●{DFrac.discard} fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) •
      ◯ fracAuthElem ((q : Q) : Frac Q) b) ~~>:
        fun k => ∃ q', k =
          (●{DFrac.own q'} fracAuthElem (wholeFrac (Q := Q)) a : FracAuth Q A) •
            ◯ fracAuthElem ((q : Q) : Frac Q) b
  simpa [fracAuthAuth, fracAuthAuthDiscarded, fracAuthFrag] using
    (Auth.auth_updateP_both_unpersist (F := Q)
      (a := fracAuthElem (wholeFrac (Q := Q)) a)
      (b := fracAuthElem ((q : Q) : Frac Q) b))

abbrev FracAuthPayloadRF (Q : Type _) [UFraction Q] (T : COFE.OFunctorPre) : COFE.OFunctorPre :=
  ProdOF (constOF (Frac Q)) T

instance {Q T} [UFraction Q] [RFunctor T] : RFunctor (FracAuthPayloadRF Q T) where
  map f g := Prod.mapC (CMRA.Hom.id (α := Frac Q)) (RFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ :=
    Prod.map_ne (fun _ => rfl) (fun _ => RFunctor.map_ne.ne Hx Hy _)
  map_id x := by
    cases x
    exact OFE.equiv_prod_ext (OFE.Equiv.of_eq rfl) (RFunctor.map_id _)
  map_comp f g f' g' x := by
    cases x
    exact OFE.equiv_prod_ext (OFE.Equiv.of_eq rfl) (RFunctor.map_comp f g f' g' _)

instance {Q T} [UFraction Q] [RFunctorContractive T] : RFunctorContractive (FracAuthPayloadRF Q T) where
  map_contractive.1 H _ :=
    Prod.map_ne (fun _ => rfl) (fun _ => RFunctorContractive.map_contractive.1 H _)

abbrev FracAuthURF (Q : Type _) [UFraction Q] (T : COFE.OFunctorPre) [RFunctor T] :
    COFE.OFunctorPre :=
  AuthURF (F := Q) (OptionOF (FracAuthPayloadRF Q T))

instance {Q T} [UFraction Q] [RFunctor T] : URFunctor (FracAuthURF Q T) := by
  let _ : RFunctor (FracAuthPayloadRF Q T) := inferInstance
  simpa [FracAuthURF] using
    (inferInstance : URFunctor (AuthURF (F := Q) (OptionOF (FracAuthPayloadRF Q T))))

instance {Q T} [UFraction Q] [RFunctorContractive T] : URFunctorContractive (FracAuthURF Q T) := by
  let _ : RFunctor (FracAuthPayloadRF Q T) := inferInstance
  let _ : RFunctorContractive (FracAuthPayloadRF Q T) := inferInstance
  simpa [FracAuthURF] using
    (inferInstance : URFunctorContractive (AuthURF (F := Q) (OptionOF (FracAuthPayloadRF Q T))))

abbrev FracAuthRF (Q : Type _) [UFraction Q] (T : COFE.OFunctorPre) [RFunctor T] :
    COFE.OFunctorPre :=
  AuthRF (F := Q) (OptionOF (FracAuthPayloadRF Q T))

instance {Q T} [UFraction Q] [RFunctor T] : RFunctor (FracAuthRF Q T) := by
  let _ : RFunctor (FracAuthPayloadRF Q T) := inferInstance
  simpa [FracAuthRF] using
    (inferInstance : RFunctor (AuthRF (F := Q) (OptionOF (FracAuthPayloadRF Q T))))

instance {Q T} [UFraction Q] [RFunctorContractive T] : RFunctorContractive (FracAuthRF Q T) := by
  let _ : RFunctor (FracAuthPayloadRF Q T) := inferInstance
  let _ : RFunctorContractive (FracAuthPayloadRF Q T) := inferInstance
  simpa [FracAuthRF] using
    (inferInstance : RFunctorContractive (AuthRF (F := Q) (OptionOF (FracAuthPayloadRF Q T))))

end FracAuth

end Iris
