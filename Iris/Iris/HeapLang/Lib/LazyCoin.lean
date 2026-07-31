module

public import Iris.HeapLang
public import Iris.BI
public import Iris.HeapLang.Lib.NondetBool

namespace Iris.HeapLang

-- type Coin := Ref (Option Bool) × ProphId
@[rocq_alias new_coin]
def newCoin := hl_val%
  λ _, (ref(none()), newProph())

-- readCoin(cp : Coin) : Bool
@[rocq_alias read_coin]
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

#rocq_ignore val_to_bool "prohecy_to_bool no longer makes use of this definition"

@[rocq_alias prophecy_to_bool]
def prophecyToBool (vs : List (Val × Val)) : Bool :=
  if let some (_, v) := vs.head? then
    v = hl_val(#true)
  else false

@[simp, grind =, rocq_alias prophecy_to_bool_of_bool]
theorem prophecyToBool_of_bool (vs : List (Val × Val)) (v : Val) (b : Bool) :
    prophecyToBool ((v, hl_val(#b)) :: vs) = b := by
  cases b <;> rfl

/-- `cp` is a pair of `c` and `p`, where if p is a prophecy with resolutions `vs`
    such that if `c` is non-null, it points to the first resolution value of  `vs` -/
@[rocq_alias coin]
def coin (cp : Val) (b : Bool) : IProp GF := iprop%
  ∃ (c : Loc) (p : ProphId) (vs : List (Val × Val)),
  ⌜ cp = hl_val((#c, #p)) ⌝ ∗ proph p vs ∗
  (c ↦ hl_val(some(#b)) ∨ (c ↦ hl_val(none()) ∗ ⌜ b = prophecyToBool vs ⌝))

@[rocq_alias new_coin_spec]
theorem newCoin.spec : ⊢@{IProp GF}
    {{ True }} hl(&newCoin #()) {{ c b, RET c; coin c b }} := by
  iintro %Φ - K
  unfold newCoin
  wp_pures
  wp_bind newProph()
  iapply wp_new_proph
  iintro %p %pvs Hp
  wp_alloc l with Hl
  wp_pures
  iintro !>
  iapply K
  unfold coin
  iexists l, p, pvs
  isplitr; itrivial
  iframe
  iright
  iframe
  ipureintro
  rfl

@[rocq_alias read_coin_spec]
theorem readCoin.spec (cp : Val) (b : Bool) : ⊢@{IProp GF}
    {{ coin cp b }} hl(&readCoin &cp) {{ RET hl_val(#b); coin cp b }} := by
  conv => enter [1,1]; unfold coin
  iintro %Φ ⟨%c, %p, %pvs, %cp_eq, proph, disj⟩ K
  unfold readCoin
  subst cp_eq
  wp_pures
  wp_bind !_
  icases disj with (Hsome | ⟨Hnone, %rfl⟩)
  · wp_load
    wp_pures
    iintro !>
    iapply K
    iexists c, p, pvs
    iframe; ipureintro; rfl
  · wp_load
    wp_pures
    wp_bind &nondetBool _; iapply nondetBool.spec $$ [//]; iintro !> %b -
    wp_store
    wp_pure; wp_pure
    wp_bind resolveProph(_, _); iapply wp_resolve_proph $$ proph
    iintro %pvs' %pvs_eq proph
    subst pvs_eq
    wp_pures
    iintro !>
    simp only [prophecyToBool_of_bool]
    iapply K
    iframe; itrivial
