module

public import Iris.HeapLang.Syntax
public import Iris.HeapLang.Semantics
public import Iris.HeapLang.Notation
public import Iris.HeapLang.Instances
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.Lifting
public import Iris.Instances.Lib.FUpd
public import Iris.Instances.Lib.WSat
public import Iris.Algebra.HeapView
public import Iris.Algebra.Auth
public import Iris.Algebra.Agree
public import Iris.Algebra.Excl
public import Iris.Algebra.Numbers
public import Iris.ProofMode
public import Std.Data.ExtTreeMap

@[expose] public section
namespace Iris.HeapLang

open Iris Auth ProgramLogic Language.Notation Std HeapView
-- open _root_.Std (Associative Commutative LeftIdentity LawfulLeftIdentity)

abbrev Steps := Nat

-- scoped instance : Associative (Add.add (α := Steps)) := ⟨Nat.add_assoc⟩
-- scoped instance : Commutative (Add.add (α := Steps)) := ⟨Nat.add_comm⟩
-- scoped instance : LeftIdentity (Add.add (α := Steps)) (0 : Steps) where
-- scoped instance : LawfulLeftIdentity (Add.add (α := Steps)) (0 : Steps) := ⟨Nat.zero_add⟩
-- scoped instance : LeftCancelAdd Steps := ⟨Nat.add_left_cancel⟩

-- scoped instance : COFE Steps := COFE.ofDiscrete _ Eq_Equivalence
-- scoped instance : OFE.Discrete Steps := ⟨congrArg id⟩
-- scoped instance : OFE.Leibniz Steps := ⟨congrArg id⟩
-- scoped instance : UCMRA Steps := CommMonoidLike.instUCMRA
-- scoped instance : CMRA.Discrete Steps := CommMonoidLike.instDiscrete
-- scoped instance {a : Steps} : CMRA.Cancelable a := inferInstance

instance : OFE Val := OFE.ofDiscrete _ Eq_Equivalence

instance {F : Type _} [UFraction F] [UCMRA A] {α : A} [IsUnit α] : IsUnit (Auth.frag (F := F) (A := A) α) where
  unit_valid := Auth.frag_valid.mpr IsUnit.unit_valid
  unit_left_id := ⟨UCMRA.unit_left_id, IsUnit.unit_left_id⟩
  pcore_unit := ⟨.rfl, (OFE.Option.ne_match id inferInstance _).eqv IsUnit.pcore_unit⟩

section HeapLangGS

abbrev GenHeapF : COFE.OFunctorPre :=
  HeapViewURF (F := PNat) (H := fun V => Std.ExtTreeMap Loc V compare)
  (constOF (DFrac PNat × Excl Val))

abbrev ProphMapF : COFE.OFunctorPre :=
  HeapViewURF (F := PNat) (H := fun V => Std.ExtTreeMap ProphId V compare)
  (constOF (DFrac PNat × Excl (Val × Val)))

abbrev StepCounterF : COFE.OFunctorPre :=
  AuthURF (F := PNat) (constOF Steps)

class HeapLangGpreS (hlc : outParam Bool) (GF : BundledGFunctors) extends IrisGS_gen hlc Exp GF where
  heap : ElemG GF GenHeapF
  proph : ElemG GF ProphMapF
  steps : ElemG GF StepCounterF

attribute [reducible, instance] HeapLangGpreS.heap
attribute [reducible, instance] HeapLangGpreS.proph
attribute [reducible, instance] HeapLangGpreS.steps

class HeapLangGS (hlc : outParam Bool) (GF : BundledGFunctors) extends HeapLangGpreS hlc GF where
  heap_name : GName
  proph_name : GName
  steps_name : GName

end HeapLangGS

section Predicates

variable {GF : BundledGFunctors} {hlc : Bool} [H : HeapLangGS hlc GF]

def pointsto (l : Loc) (dq : DFrac PNat) (v : Val) : IProp GF :=
  iOwn (E := H.heap) H.heap_name
    (HeapView.Frag (K := Loc) (V := (DFrac PNat × Excl Val)) l dq (dq, Excl.excl v))

def steps_auth (n : Nat) : IProp GF :=
  iOwn (E := H.steps) H.steps_name (Auth.auth (DFrac.own 1) n)

def steps_lb (n : Nat) : IProp GF :=
  iOwn (E := H.steps) H.steps_name (Auth.frag n)

end Predicates

notation:20 l " ↦{" dq "} " v => (pointsto (hlc := _) l dq v)
notation:20 l " ↦ " v => (pointsto (hlc := _) l (DFrac.own 1) v)

section StepCounter

variable {GF : BundledGFunctors} {hlc : Bool} [HeapLangGS hlc GF]

theorem steps_lb_0 : ⊢ |==> steps_lb (hlc := hlc) (GF := GF) 0 := by
  unfold steps_lb
  exact iOwn_unit (ε := UCMRA.unit)

theorem steps_lb_valid (n m : Nat) :
  steps_auth (hlc := hlc) (GF := GF) n -∗
  steps_lb (hlc := hlc) (GF := GF) m -∗
  ⌜m ≤ n⌝ := by
  unfold steps_auth steps_lb
  iintro Hauth Hfrag
  icombine Hauth Hfrag as Hval
  icases iOwn_cmraValid $$ Hval with Hval
  icases auth_both_validI $$ Hval with ⟨%Hval, -⟩
  ipure_intro
  obtain ⟨k, ⟨⟩⟩ := Hval
  simp [CMRA.op, Add.add]

theorem steps_lb_get (n : Nat) :
  steps_auth (hlc := hlc) (GF := GF) n -∗
  steps_lb (hlc := hlc) (GF := GF) n := by
  unfold steps_auth steps_lb
  iintro Hauth
  sorry

theorem steps_lb_le (n n' : Nat) (h : n' ≤ n) :
  steps_lb (hlc := hlc) (GF := GF) n -∗
  steps_lb (hlc := hlc) (GF := GF) n' := by
  unfold steps_lb
  iintro Hfrag
  iapply iOwn_mono $$ Hfrag
  apply Auth.frag_inc_of_inc
  refine ⟨n - n', .of_eq ?_⟩
  exact (Nat.add_sub_of_le h).symm

end StepCounter

section PointsTo

variable {GF : BundledGFunctors} {hlc : Bool} [H : HeapLangGS hlc GF]

theorem pointsto_valid (l : Loc) (dq : DFrac PNat) (v : Val) :
  (l ↦{dq} v) ⊢ (⌜✓ dq⌝ : IProp GF) := by
  unfold pointsto
  iintro Hpt
  icases iOwn_cmraValid $$ Hpt with Hval
  icases internalCmraValid_elim $$ Hval with %Hval
  ipure_intro
  exact (HeapView.frag_validN_iff.mp Hval).left

theorem pointsto_conflict_frac (l : Loc) (dq1 dq2 : DFrac PNat) (v1 v2 : Val) :
  (l ↦{dq1} v1) ∗ (l ↦{dq2} v2) ⊢ (False : IProp GF) := by
  unfold pointsto
  iintro ⟨Hpt1, Hpt2⟩
  icombine Hpt1 Hpt2 as Hres
  icases iOwn_cmraValid $$ Hres with Hval
  icases frag_op_frag_validI $$ Hval with ⟨%Hval, Hval⟩
  icases internalCmraValid_elim $$ Hval with %Hval'
  exact Hval'.right.elim

theorem pointsto_conflict (l : Loc) (v1 v2 : Val) :
  (l ↦ v1) ∗ (l ↦ v2) ⊢ (False : IProp GF) := by
  unfold pointsto
  iintro ⟨Hpt1, Hpt2⟩
  icombine Hpt1 Hpt2 as Hres
  icases iOwn_cmraValid $$ Hres with Hval
  icases frag_op_frag_validI $$ Hval with ⟨%Hval, Hval⟩
  icases internalCmraValid_elim $$ Hval with %Hval'
  exact Hval'.right.elim

end PointsTo

section Lifting

variable {GF : BundledGFunctors} {hlc : Bool}
variable [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}

theorem wp_alloc (v : Val) :
  ⊢ (WP (hl(ref(v(v)))) @ s; E {{ l, ∃ l' : Loc, ⌜l = .lit (.loc l')⌝ ∗ (l' ↦ v)}} : IProp GF) := by
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_free (l : Loc) (v : Val) :
  ▷ (l ↦ v) ⊢ (WP (hl(free(#(.loc l)))) @ s; E {{ w, ⌜w = .lit .unit⌝}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_load (l : Loc) (dq : DFrac PNat) (v : Val) :
  ▷ (l ↦{dq} v) ⊢ (WP (hl(!#(.loc l))) @ s; E {{ w, ⌜w = v⌝ ∗ (l ↦{dq} v)}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_store (l : Loc) (v v' : Val) :
  ▷ (l ↦ v') ⊢ (WP (hl(#(.loc l) ← v(v))) @ s; E {{ w, ⌜w = .lit .unit⌝ ∗ (l ↦ v)}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_xchg (l : Loc) (v v' : Val) :
  ▷ (l ↦ v') ⊢ (WP (hl(xchg(#(.loc l), v(v)))) @ s; E {{ w, ⌜w = v'⌝ ∗ (l ↦ v)}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_cmpxchg_fail (l : Loc) (v1 v2 v' : Val)
    (hneq : v' ≠ v1) (hsafe : v'.compareSafe v1) :
  ▷ (l ↦ v') ⊢ (WP (hl(cmpXchg(#(.loc l), v(v1), v(v2)))) @ s; E {{ w, ⌜w = .pair v' (.lit (.bool false))⌝ ∗ (l ↦ v')}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_cmpxchg_suc (l : Loc) (v1 v2 v' : Val)
    (heq : v' = v1) (hsafe : v'.compareSafe v1) :
  ▷ (l ↦ v') ⊢ (WP (hl(cmpXchg(#(.loc l), v(v1), v(v2)))) @ s; E {{ w, ⌜w = .pair v' (.lit (.bool true))⌝ ∗ (l ↦ v2)}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_faa (l : Loc) (i1 i2 : Int) :
  ▷ (l ↦ (.lit (.int i1))) ⊢
    (WP (hl(faa(#(.loc l), #(.int i2)))) @ s; E {{ v, ⌜v = .lit (.int i1)⌝ ∗ (l ↦ (.lit (.int (i1 + i2))))}} : IProp GF) := by
  iintro Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

theorem wp_fork {GF : BundledGFunctors} {hlc : Bool} (s : Stuckness) (E : CoPset)
    (e : Exp) (Φ : Val → IProp GF) [HeapLangGS hlc GF] :
  (▷ WP e @ s; ⊤ {{ _v, emp }}) -∗
  (▷ (Φ (Val.lit BaseLit.unit))) -∗
  (WP (hl(fork(e))) @ s; E {{ Φ }}) := by
  iintro Hwp HΦ
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ

  sorry

end Lifting

end Iris.HeapLang
