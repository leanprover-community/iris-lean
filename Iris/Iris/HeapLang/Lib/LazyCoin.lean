module

public import Iris.HeapLang
public import Iris.BI
public import Iris.HeapLang.Lib.NondetBool

namespace Iris.HeapLang

-- type Coin := Ref (Option Bool) × ProphId
def newCoin := hl_val%
  λ _, (ref(none()), newProph())

-- readCoin(cp : Coin) : Bool
def readCoin := hl_val%
  λ cp,
    let c := fst(cp);
    let p := snd(cp);
    match !c with
    | none() => -- The prophecy hasn't been resolved yet
      let r := &nondetBool #();
      c ← some(r);
      resolveProph(p, r);
      r
    | some(v) => -- The prophecy has been resolved already
      v

variable {hlc GF} [HeapLangGS hlc GF]

section Proofs

open HeapLang

def prophecyToBool (vs : List (Val × Val)) : Bool :=
  if let some (_, v) := vs.head? then
    v = hl_val(#true)
  else false

@[simp, grind =]
theorem prophecyToBool_of_bool (vs : List (Val × Val)) (v : Val) (b : Bool) :
    prophecyToBool ((v, hl_val(#b)) :: vs) = b := by
  cases b <;> rfl

/-- `cp` is a pair of `c` and `p`, where if p is a prophecy with resolutions `vs`
    such that if `c` is non-null, it points to the first resolution value of  `vs` -/
def coin (cp : Val) (b : Bool) : IProp GF := iprop%
  ∃ (c : Loc) (p : ProphId) (vs : List (Val × Val)),
  ⌜ cp = hl_val((#c, #p)) ⌝ ∗ proph p vs ∗
  (c ↦ hl_val(some(#b)) ∨ (c ↦ hl_val(none()) ∗ ⌜ b = prophecyToBool vs ⌝))

theorem newCoin.spec : ⊢@{IProp GF}
    {{ True }} hl(&newCoin #()) {{ c b, RET c; coin c b }} := by
  iintro %Φ - K
  unfold newCoin
  wp_pures
  wp_bind newProph()
  ihave ∗aux := wp_new_proph
  iapply wp_strong_mono (Std.IsPreorder.le_refl _) CoPset.subseteq_refl $$ aux
  iintro %v ⟨%p, %pvs, %eq, h⟩ !>; subst eq
  wp_pures
  wp_bind ref(_)
  iapply wp_alloc
  iintro %l !> Hl
  wp_pures
  iintro !>
  iapply K
  unfold coin
  iexists l, p, pvs
  isplitl []; itrivial
  iframe
  iright
  iframe
  ipureintro
  rfl

theorem readCoin.spec (cp : Val) (b : Bool) : ⊢@{IProp GF}
    {{ coin cp b }} hl(&readCoin &cp) {{ RET hl_val(#b); coin cp b }} := by
  conv => enter [1,1]; unfold coin
  iintro %Φ ⟨%c, %p, %pvs, %cp_eq, proph, disj⟩ K
  unfold readCoin
  subst cp_eq
  wp_pures
  wp_bind !_
  icases disj with (Hsome | ⟨Hnone, %b_eq⟩)
  · iapply wp_load $$ Hsome
    iintro !> Hc
    wp_pures
    iintro !>
    iapply K
    iexists c, p, pvs
    iframe; ipureintro; rfl
  · subst b_eq
    iapply wp_load $$ Hnone
    iintro !> Hc
    wp_pures
    wp_bind &nondetBool _; iapply nondetBool.spec $$ [//]; iintro !> %b -
    wp_pures
    wp_bind _ ← _; iapply wp_store $$ Hc; iintro !> Hc
    wp_pure; wp_pure
    wp_bind resolveProph(_, _); iapply wp_resolve_proph $$ proph
    iintro %pvs' %pvs_eq proph
    subst pvs_eq
    wp_pures
    iintro !>
    simp only [prophecyToBool_of_bool]
    iapply K
    iexists c, p, pvs'
    iframe; ipureintro; rfl
