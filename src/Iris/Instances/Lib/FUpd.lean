/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers
public import Iris.ProofMode
public import Iris.BI.Algebra
public import Iris.Instances.IProp
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits

@[expose] public section

namespace Iris.FUpd

open Iris OFE COFE BI Auth Lc

section HasLC

inductive HasLc where
  | HasLc : HasLc
  | HasNoLc : HasLc

end HasLC

section InvG

class InvGpreS (GF : BundledGFunctors) where
  toWsatGpreS : WsatGpreS GF
  toLcGpreS : LcGpreS GF

class InvGS_gen (hlc : HasLc) (GF : BundledGFunctors) extends InvGpreS GF where
  toWsatGS : WsatGS GF
  toLcGS : LcGS GF

attribute [reducible, instance] InvGS_gen.toWsatGS
attribute [reducible, instance] InvGS_gen.toLcGS

abbrev InvGS := InvGS_gen HasLc.HasLc

end InvG

section FUpd

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

def uPred_fupd (E1 E2 : CoPset) (P : IProp GF) : IProp GF :=
  iprop(wsat ∗ ownE E1 -∗ le_upd_if (match hlc with | HasLc.HasLc => true | _ => false) iprop(◇ (wsat ∗ ownE E2 ∗ P)))

instance uPred_fupd_instance [InvGS GF] : FUpd (IProp GF) where
  fupd := uPred_fupd (hlc := HasLc.HasLc)

end FUpd

section Instances

variable {GF : BundledGFunctors} [InvGS_gen hlc GF]

instance uPred_bi_fupd : BIFUpdate (IProp GF) := sorry

instance uPred_bi_fupd_sbi_no_lc : BIFUpdatePlainly (IProp GF) := sorry

end Instances

section LaterCreditLemmas

variable {GF : BundledGFunctors} [InvGS GF]

theorem lc_fupd_elim_later {E : CoPset} {P : IProp GF} :
  ⊢ £ 1 -∗ (▷ P) -∗ |={E}=> P := by
  sorry

theorem lc_fupd_add_later {E : CoPset} {P : IProp GF} :
  ⊢ £ 1 -∗ (|={E}=> ▷ P) -∗ |={E}=> P := by
  sorry

theorem lc_fupd_add_laterN (n : Nat) {E : CoPset} {P : IProp GF} :
  ⊢ £ n -∗ (|={E}=> ▷^[n] P) -∗ |={E}=> P := by
  sorry

end LaterCreditLemmas

section Soundness

variable {GF : BundledGFunctors}

theorem fupd_soundness_no_lc_unfold [InvGpreS GF] {E1 E2 : CoPset} {P : IProp GF} :
  (|={E1,E2}=> P) ⊢ |==> P := by
  sorry

theorem fupd_soundness_no_lc [InvGpreS GF] {E1 E2 : CoPset} {P : IProp GF} [Plain P] :
  (∀ (_ : InvGS_gen HasLc.HasNoLc GF), ⊢ |={E1,E2}=> P) → ⊢ P := by
  sorry

theorem fupd_soundness_lc [InvGpreS GF] (m : Nat) {E1 E2 : CoPset} {P : IProp GF} [Plain P] :
  (∀ (_ : InvGS GF), ⊢ £ m -∗ |={E1,E2}=> P) → ⊢ P := by
  sorry

theorem fupd_soundness_gen (hlc : HasLc) [InvGpreS GF]
  (m : Nat) {E1 E2 : CoPset} {P : IProp GF} [Plain P] :
  (∀ (_ : InvGS_gen hlc GF), ⊢ match hlc with
    | HasLc.HasLc => iprop(£ m -∗ |={E1,E2}=> P)
    | HasLc.HasNoLc => iprop(|={E1,E2}=> P)) → ⊢ P := by
  sorry

end Soundness

section StepIndexed

variable {GF : BundledGFunctors}

theorem step_fupdN_soundness_no_lc [InvGpreS GF]
  (n : Nat) {E1 E2 : CoPset} {P : IProp GF} [Plain P] :
  (∀ (_ : InvGS_gen HasLc.HasNoLc GF),
    ⊢ Nat.fold n (fun _ _ Q => iprop(|={E1,E1}=> ▷ Q)) (iprop(|={E1,E2}=> P))) → ⊢ P := by
  sorry

theorem step_fupdN_soundness_lc [InvGpreS GF]
  (n : Nat) {E1 E2 : CoPset} {P : IProp GF} [Plain P] :
  (∀ (_ : InvGS GF),
    ⊢ £ n -∗ Nat.fold n (fun _ _ Q => iprop(|={E1,E1}=> ▷ Q)) (iprop(|={E1,E2}=> P))) → ⊢ P := by
  sorry

-- theorem step_fupdN_soundness_gen (hlc : HasLc) [InvGpreS GF]
--   (n : Nat) {E1 E2 : CoPset} {P : IProp GF} [Plain P] :
--   (∀ (_ : InvGS_gen hlc GF),
--     ⊢ match hlc with
--       | HasLc.HasLc => iprop(£ n -∗ Nat.fold n (fun _ _ Q => iprop(|={E1,E1}=> ▷ Q)) iprop((|={E1,E2}=> P)))
--       | HasLc.HasNoLc => Nat.fold n (fun _ _ Q => iprop(|={E1,E1}=> ▷ Q)) iprop((|={E1,E2}=> P)) → ⊢ P) := by
--   sorry

end StepIndexed

end Iris.FUpd

end
