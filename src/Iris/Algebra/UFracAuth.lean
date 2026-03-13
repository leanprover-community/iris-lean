import Iris.Algebra.Auth
import Iris.Algebra.UFrac

namespace Iris

abbrev UFracAuth (Q : Type _) (A : Type _) [UFraction Q] [CMRA A] :=
  Auth Q (Option (UFrac Q × A))

namespace UFracAuth

open COFE OFE CMRA Auth

variable {Q A : Type _} [UFraction Q] [CMRA A]

abbrev uFracAuthElem (q : UFrac Q) (a : A) : Option (UFrac Q × A) :=
  some (q, a)

def uFracAuthAuth (q : Q) (a : A) : UFracAuth Q A :=
  ● (uFracAuthElem ((q : Q) : UFrac Q) a)

def uFracAuthFrag (q : Q) (a : A) : UFracAuth Q A :=
  ◯ (uFracAuthElem ((q : Q) : UFrac Q) a)

theorem uFracAuthElem_validN (n : Nat) (q : UFrac Q) (a : A) :
    ✓{n} uFracAuthElem q a ↔ ✓{n} a := by
  change ✓{n} ((q, a) : UFrac Q × A) ↔ ✓{n} a
  simp [CMRA.ValidN]

theorem uFracAuthElem_valid (q : UFrac Q) (a : A) :
    ✓ uFracAuthElem q a ↔ ✓ a := by
  change ✓ ((q, a) : UFrac Q × A) ↔ ✓ a
  simp [CMRA.Valid]

theorem uFracAuth_validN (n : Nat) (p : Q) (a : A) :
    ✓{n} a → ✓{n} (uFracAuthAuth (Q := Q) p a • uFracAuthFrag p a) := by
  intro ha
  change ✓{n} ((● uFracAuthElem ((p : Q) : UFrac Q) a : UFracAuth Q A) •
      ◯ uFracAuthElem ((p : Q) : UFrac Q) a)
  rw [Auth.both_validN]
  exact ⟨CMRA.incN_refl _, (uFracAuthElem_validN (Q := Q) (A := A) n ((p : Q) : UFrac Q) a).2 ha⟩

theorem uFracAuth_valid (p : Q) (a : A) :
    ✓ a → ✓ (uFracAuthAuth (Q := Q) p a • uFracAuthFrag p a) := by
  intro ha
  change ✓ ((● uFracAuthElem ((p : Q) : UFrac Q) a : UFracAuth Q A) •
      ◯ uFracAuthElem ((p : Q) : UFrac Q) a)
  refine Auth.auth_both_valid_2 ?_ (CMRA.inc_refl _)
  exact (uFracAuthElem_valid (Q := Q) (A := A) ((p : Q) : UFrac Q) a).2 ha

theorem uFracAuth_agreeN (n : Nat) (p : Q) (a b : A) :
    ✓{n} (uFracAuthAuth (Q := Q) p a • uFracAuthFrag p b) → a ≡{n}≡ b := by
  intro h
  change ✓{n} ((● uFracAuthElem ((p : Q) : UFrac Q) a : UFracAuth Q A) •
      ◯ uFracAuthElem ((p : Q) : UFrac Q) b) at h
  obtain ⟨hinc, _⟩ := (Auth.both_validN
    (F := Q) (a := uFracAuthElem ((p : Q) : UFrac Q) a)
    (b := uFracAuthElem ((p : Q) : UFrac Q) b)).1 h
  cases (Option.some_incN_some_iff.mp hinc) with
  | inl hpair =>
      simpa using (OFE.dist_snd hpair).symm
  | inr hpair =>
      rcases hpair with ⟨z, hz⟩
      exact False.elim <|
        CMRA.id_freeN_r (n := n) (n' := n) (x := ((p : Q) : UFrac Q)) trivial hz.1.symm

theorem uFracAuth_agree (p : Q) (a b : A) :
    ✓ (uFracAuthAuth (Q := Q) p a • uFracAuthFrag p b) → a ≡ b := by
  intro h
  refine equiv_dist.mpr fun n => ?_
  exact uFracAuth_agreeN (Q := Q) n p a b h.validN

theorem uFracAuth_agree_L [Leibniz A] (p : Q) (a b : A) :
    ✓ (uFracAuthAuth (Q := Q) p a • uFracAuthFrag p b) → a = b :=
  Leibniz.eq_of_eqv ∘ uFracAuth_agree (Q := Q) p a b

theorem uFracAuth_includedN (n : Nat) (p q : Q) (a b : A) :
    ✓{n} (uFracAuthAuth (Q := Q) p a • uFracAuthFrag q b) → (some b : Option A) ≼{n} some a := by
  intro h
  change ✓{n} ((● uFracAuthElem ((p : Q) : UFrac Q) a : UFracAuth Q A) •
      ◯ uFracAuthElem ((q : Q) : UFrac Q) b) at h
  obtain ⟨hinc, _⟩ := (Auth.both_validN
    (F := Q) (a := uFracAuthElem ((p : Q) : UFrac Q) a)
    (b := uFracAuthElem ((q : Q) : UFrac Q) b)).1 h
  rcases Option.some_incN_some_iff_opM.mp hinc with ⟨mz, hmz⟩
  cases mz with
  | none =>
      exact Option.some_inc_some_of_dist_opM (x := a) (y := b) (mz := none) (OFE.dist_snd hmz)
  | some z =>
      exact Option.some_inc_some_of_dist_opM (x := a) (y := b) (mz := some z.2) (OFE.dist_snd hmz)

theorem uFracAuth_included [CMRA.Discrete A] (q p : Q) (a b : A) :
    ✓ (uFracAuthAuth (Q := Q) p a • uFracAuthFrag q b) → (some b : Option A) ≼ some a := by
  intro h
  exact (CMRA.inc_iff_incN (α := Option A) 0).mpr <|
    uFracAuth_includedN (Q := Q) 0 p q a b h.validN

theorem uFracAuth_includedN_total [CMRA.IsTotal A] (n : Nat) (q p : Q) (a b : A) :
    ✓{n} (uFracAuthAuth (Q := Q) p a • uFracAuthFrag q b) → b ≼{n} a :=
  Option.some_incN_some_iff_isTotal.mp ∘ uFracAuth_includedN (Q := Q) n p q a b

theorem uFracAuth_included_total [CMRA.Discrete A] [CMRA.IsTotal A] (q p : Q) (a b : A) :
    ✓ (uFracAuthAuth (Q := Q) p a • uFracAuthFrag q b) → b ≼ a :=
  Option.some_inc_some_iff_isTotal.mp ∘ uFracAuth_included (Q := Q) q p a b

theorem uFracAuth_auth_validN (n : Nat) (q : Q) (a : A) :
    ✓{n} (uFracAuthAuth (Q := Q) q a) ↔ ✓{n} a := by
  change (✓{n} (● uFracAuthElem ((q : Q) : UFrac Q) a : UFracAuth Q A)) ↔ ✓{n} a
  rw [Auth.auth_validN, uFracAuthElem_validN]

theorem uFracAuth_auth_valid (q : Q) (a : A) :
    ✓ (uFracAuthAuth (Q := Q) q a) ↔ ✓ a := by
  change (✓ (● uFracAuthElem ((q : Q) : UFrac Q) a : UFracAuth Q A)) ↔ ✓ a
  rw [Auth.auth_valid, uFracAuthElem_valid]

theorem uFracAuth_frag_validN (n : Nat) (q : Q) (a : A) :
    ✓{n} (uFracAuthFrag (Q := Q) q a) ↔ ✓{n} a := by
  change (✓{n} (◯ uFracAuthElem ((q : Q) : UFrac Q) a : UFracAuth Q A)) ↔ ✓{n} a
  rw [Auth.frag_validN, uFracAuthElem_validN]

theorem uFracAuth_frag_valid (q : Q) (a : A) :
    ✓ (uFracAuthFrag (Q := Q) q a) ↔ ✓ a := by
  change (✓ (◯ uFracAuthElem ((q : Q) : UFrac Q) a : UFracAuth Q A)) ↔ ✓ a
  rw [Auth.frag_valid, uFracAuthElem_valid]

theorem uFracAuth_frag_op (q1 q2 : Q) (a1 a2 : A) :
    uFracAuthFrag (Q := Q) (q1 + q2) (a1 • a2) ≡
      uFracAuthFrag q1 a1 • uFracAuthFrag q2 a2 := by
  change (◯ uFracAuthElem (((q1 + q2 : Q)) : UFrac Q) (a1 • a2) : UFracAuth Q A) ≡
      (◯ uFracAuthElem ((q1 : Q) : UFrac Q) a1 : UFracAuth Q A) •
        (◯ uFracAuthElem ((q2 : Q) : UFrac Q) a2 : UFracAuth Q A)
  have h := (Auth.frag_op (F := Q)
    (b1 := uFracAuthElem ((q1 : Q) : UFrac Q) a1)
    (b2 := uFracAuthElem ((q2 : Q) : UFrac Q) a2)).symm
  have h' :
      (◯ uFracAuthElem (((q1 + q2 : Q)) : UFrac Q) (a1 • a2) : UFracAuth Q A) =
        (◯ uFracAuthElem ((q1 : Q) : UFrac Q) a1 : UFracAuth Q A) •
          (◯ uFracAuthElem ((q2 : Q) : UFrac Q) a2 : UFracAuth Q A) := by
    simpa [uFracAuthElem, CMRA.op] using h
  exact OFE.Equiv.of_eq h'

theorem uFracAuth_frag_op_validN (n : Nat) (q1 q2 : Q) (a b : A) :
    ✓{n} (uFracAuthFrag (Q := Q) q1 a • uFracAuthFrag q2 b) ↔ ✓{n} (a • b) := by
  change (✓{n} (((◯ uFracAuthElem ((q1 : Q) : UFrac Q) a : UFracAuth Q A) •
      (◯ uFracAuthElem ((q2 : Q) : UFrac Q) b : UFracAuth Q A)))) ↔ ✓{n} (a • b)
  rw [Auth.frag_op_validN]
  simpa [uFracAuthElem, CMRA.op] using
    (uFracAuthElem_validN (Q := Q) (A := A) n ((((q1 + q2 : Q)) : UFrac Q)) (a • b))

theorem uFracAuth_frag_op_valid (q1 q2 : Q) (a b : A) :
    ✓ (uFracAuthFrag (Q := Q) q1 a • uFracAuthFrag q2 b) ↔ ✓ (a • b) := by
  change (✓ (((◯ uFracAuthElem ((q1 : Q) : UFrac Q) a : UFracAuth Q A) •
      (◯ uFracAuthElem ((q2 : Q) : UFrac Q) b : UFracAuth Q A)))) ↔ ✓ (a • b)
  rw [Auth.frag_op_valid]
  simpa [uFracAuthElem, CMRA.op] using
    (uFracAuthElem_valid (Q := Q) (A := A) ((((q1 + q2 : Q)) : UFrac Q)) (a • b))

theorem uFracAuth_update (p q : Q) (a b a' b' : A) :
    (a, b) ~l~> (a', b') →
      uFracAuthAuth (Q := Q) p a • uFracAuthFrag q b ~~>
        uFracAuthAuth p a' • uFracAuthFrag q b' := by
  intro hup
  change ((● uFracAuthElem ((p : Q) : UFrac Q) a : UFracAuth Q A) •
      ◯ uFracAuthElem ((q : Q) : UFrac Q) b) ~~>
        ((● uFracAuthElem ((p : Q) : UFrac Q) a' : UFracAuth Q A) •
          ◯ uFracAuthElem ((q : Q) : UFrac Q) b')
  apply Auth.auth_update
  exact LocalUpdate.option <|
    LocalUpdate.prod_2 (x1 := ((p : Q) : UFrac Q)) (y1 := ((q : Q) : UFrac Q)) hup

instance uFracAuthPair_cancelable {q : UFrac Q} {a : A} [CMRA.Cancelable a] :
    CMRA.Cancelable ((q, a) : UFrac Q × A) where
  cancelableN {_ _ _} hv he := ⟨cancelableN (x := q) hv.1 he.1, cancelableN (x := a) hv.2 he.2⟩

instance uFracAuthPair_idFree {q : UFrac Q} {a : A} [CMRA.Cancelable a] :
    CMRA.IdFree ((q, a) : UFrac Q × A) where
  id_free0_r z hv he := id_free0_r (x := q) z.1 hv.1 he.1

theorem uFracAuth_frag_auth_comm (p q : Q) (a b : A) :
    uFracAuthElem ((q : Q) : UFrac Q) b • uFracAuthElem ((p : Q) : UFrac Q) a ≡
      uFracAuthElem (((p + q : Q)) : UFrac Q) (a • b) := by
  change (some ((((q : Q) : UFrac Q), b) • (((p : Q) : UFrac Q), a)) : Option (UFrac Q × A)) ≡
      some ((((p : Q) : UFrac Q), a) • (((q : Q) : UFrac Q), b))
  simpa [uFracAuthElem, CMRA.op] using
    (CMRA.comm (x := ((((q : Q) : UFrac Q), b) : UFrac Q × A))
      (y := ((((p : Q) : UFrac Q), a) : UFrac Q × A)))

theorem uFracAuth_update_surplus (p q : Q) (a b : A) :
    ✓ (a • b) → uFracAuthAuth (Q := Q) p a ~~>
      uFracAuthAuth (p + q) (a • b) • uFracAuthFrag q b := by
  intro hvalid
  change (● uFracAuthElem ((p : Q) : UFrac Q) a : UFracAuth Q A) ~~>
      ((● uFracAuthElem (((p + q : Q)) : UFrac Q) (a • b) : UFracAuth Q A) •
        ◯ uFracAuthElem ((q : Q) : UFrac Q) b)
  let x : Option (UFrac Q × A) := uFracAuthElem ((p : Q) : UFrac Q) a
  let f : Option (UFrac Q × A) := uFracAuthElem ((q : Q) : UFrac Q) b
  let x' : Option (UFrac Q × A) := uFracAuthElem (((p + q : Q)) : UFrac Q) (a • b)
  have hfx : f • x ≡ x' := uFracAuth_frag_auth_comm (Q := Q) p q a b
  apply Auth.auth_update_alloc
  refine LocalUpdate.equiv_right (x := (x, unit)) (y := (f • x, f • unit)) (z := (x', f)) ?_ ?_
  · exact ⟨hfx, by simpa [f] using (CMRA.unit_right_id (x := f))⟩
  · refine LocalUpdate.op (x := x) (y := unit) (z := f) ?_
    intro n _
    exact (OFE.Dist.validN hfx.dist).mpr <|
      (uFracAuthElem_validN (Q := Q) (A := A) n ((((p + q : Q)) : UFrac Q)) (a • b)).2 hvalid.validN

theorem uFracAuth_update_surplus_cancel (p q : Q) (a b : A) [CMRA.Cancelable b] :
    uFracAuthAuth (Q := Q) (p + q) (a • b) • uFracAuthFrag q b ~~> uFracAuthAuth p a := by
  change ((● uFracAuthElem (((p + q : Q)) : UFrac Q) (a • b) : UFracAuth Q A) •
      ◯ uFracAuthElem ((q : Q) : UFrac Q) b) ~~>
        ● uFracAuthElem ((p : Q) : UFrac Q) a
  let x : Option (UFrac Q × A) := uFracAuthElem (((p + q : Q)) : UFrac Q) (a • b)
  let f : Option (UFrac Q × A) := uFracAuthElem ((q : Q) : UFrac Q) b
  let z : Option (UFrac Q × A) := uFracAuthElem ((p : Q) : UFrac Q) a
  have hfz : f • z ≡ x := uFracAuth_frag_auth_comm (Q := Q) p q a b
  apply Auth.auth_update_dealloc
  refine LocalUpdate.equiv_left (z := (z, unit)) (x := (f • z, f • unit)) (y := (x, f)) ?_ ?_
  · exact ⟨hfz, by simpa [f] using (CMRA.unit_right_id (x := f))⟩
  · simpa [f, z] using
      (LocalUpdate.cancel
        (x := (uFracAuthElem ((q : Q) : UFrac Q) b : Option (UFrac Q × A)))
        (y := z) (z := (unit : Option (UFrac Q × A))))

abbrev UFracAuthPayloadRF (Q : Type _) [UFraction Q] (T : COFE.OFunctorPre) : COFE.OFunctorPre :=
  ProdOF (constOF (UFrac Q)) T

instance {Q T} [UFraction Q] [RFunctor T] : RFunctor (UFracAuthPayloadRF Q T) where
  map f g := Prod.mapC (CMRA.Hom.id (α := UFrac Q)) (RFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy _ :=
    Prod.map_ne (fun _ => rfl) (fun _ => RFunctor.map_ne.ne Hx Hy _)
  map_id x := by
    cases x
    exact OFE.equiv_prod_ext (OFE.Equiv.of_eq rfl) (RFunctor.map_id _)
  map_comp f g f' g' x := by
    cases x
    exact OFE.equiv_prod_ext (OFE.Equiv.of_eq rfl) (RFunctor.map_comp f g f' g' _)

instance {Q T} [UFraction Q] [RFunctorContractive T] : RFunctorContractive (UFracAuthPayloadRF Q T) where
  map_contractive.1 H _ :=
    Prod.map_ne (fun _ => rfl) (fun _ => RFunctorContractive.map_contractive.1 H _)

abbrev UFracAuthURF (Q : Type _) [UFraction Q] (T : COFE.OFunctorPre) [RFunctor T] :
    COFE.OFunctorPre :=
  AuthURF (F := Q) (OptionOF (UFracAuthPayloadRF Q T))

instance {Q T} [UFraction Q] [RFunctor T] : URFunctor (UFracAuthURF Q T) := by
  let _ : RFunctor (UFracAuthPayloadRF Q T) := inferInstance
  simpa [UFracAuthURF] using
    (inferInstance : URFunctor (AuthURF (F := Q) (OptionOF (UFracAuthPayloadRF Q T))))

instance {Q T} [UFraction Q] [RFunctorContractive T] : URFunctorContractive (UFracAuthURF Q T) := by
  let _ : RFunctor (UFracAuthPayloadRF Q T) := inferInstance
  let _ : RFunctorContractive (UFracAuthPayloadRF Q T) := inferInstance
  simpa [UFracAuthURF] using
    (inferInstance : URFunctorContractive (AuthURF (F := Q) (OptionOF (UFracAuthPayloadRF Q T))))

abbrev UFracAuthRF (Q : Type _) [UFraction Q] (T : COFE.OFunctorPre) [RFunctor T] :
    COFE.OFunctorPre :=
  AuthRF (F := Q) (OptionOF (UFracAuthPayloadRF Q T))

instance {Q T} [UFraction Q] [RFunctor T] : RFunctor (UFracAuthRF Q T) := by
  let _ : RFunctor (UFracAuthPayloadRF Q T) := inferInstance
  simpa [UFracAuthRF] using
    (inferInstance : RFunctor (AuthRF (F := Q) (OptionOF (UFracAuthPayloadRF Q T))))

instance {Q T} [UFraction Q] [RFunctorContractive T] : RFunctorContractive (UFracAuthRF Q T) := by
  let _ : RFunctor (UFracAuthPayloadRF Q T) := inferInstance
  let _ : RFunctorContractive (UFracAuthPayloadRF Q T) := inferInstance
  simpa [UFracAuthRF] using
    (inferInstance : RFunctorContractive (AuthRF (F := Q) (OptionOF (UFracAuthPayloadRF Q T))))

end UFracAuth

end Iris
