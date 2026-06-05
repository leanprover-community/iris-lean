module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

namespace Quicksort

def cons : Val := hl_val% λ x, injr(ref(x))

def append : Val := hl_val% rec append f := ref(#false)

def partition : Val := hl_val% rec append f := ref(#false)

def quicksort : Val := hl_val%
  rec quicksort l :=
    match l with
    | none() => l
    | some(x) =>
      (let p := !x;
       let head := fst(p);
       let tail := snd(p);
       let part := ?partition (head, tail);
       let a := quicksort (fst(part));
       let b := quicksort (snd(part));
       let e := ?cons (head, b);
       ?append (a, e))

section Predicates

variable [HeapLangGS hlc GF]

def isList (v : Val) : List Int → IProp GF
  | [] => iprop% ⌜v = hl_val(none())⌝
  | x :: xs => iprop% ∃ l tl, ⌜v = hl_val(some(#(.loc l)))⌝ ∗
    l ↦ some hl_val((#x, ?tl)) ∗ isList tl xs

end Predicates

section Specs

variable {GF : BundledGFunctors} [HeapLangGS hlc GF]

theorem cons_spec x l ls Φ :
    isList (GF:=GF) l ls -∗
    (∀ v, isList v (x :: ls) -∗ Φ v) -∗
    WP hl(?cons v((#x, ?l))) {{ Φ }} := by
  iintro Hl HΦ
  iapply wp_rec; rfl; simp [Exp.subst, Exp.substStr]
  imodintro
  wp_pures
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %l Hl
  wp_pures
  imodintro
  iapply HΦ
  rw (occs:=[3]) [isList.eq_def]
  simp only
  iexists _, _; iframe
  itrivial

theorem append_spec l1 ls1 l2 ls2 Φ :
    isList (GF:=GF) l1 ls1 -∗
    isList l2 ls2 -∗
    (∀ v, isList v (ls1 ++ ls2) -∗ Φ v) -∗
    WP hl(?append v((?l1, ?l2))) {{ Φ }} := by
  sorry

theorem partition_spec x l ls Φ :
    isList (GF:=GF) l ls -∗
    (∀ l1 l2,
      isList l1 (ls.filter (· ≤ x)) -∗
      isList l2 (ls.filter (x < ·)) -∗
      Φ hl_val((?l1, ?l2))) -∗
    WP hl(?partition v((#x, ?l))) {{ Φ }} := by
  sorry

-- set_option profiler true in
theorem quicksort_spec l ls Φ :
    isList (GF:=GF) l ls -∗
    (∀ l' ls',
      isList l' ls' -∗
      ⌜List.Pairwise LE.le ls'⌝ -∗
      ⌜List.Perm ls ls'⌝ -∗
      Φ l') -∗
    WP hl(?quicksort ?l) {{ Φ }} := by
  iintro Hl HΦ
  iloeb as IH generalizing %l %ls %Φ
  iapply wp_rec; rfl; simp [Exp.subst, Exp.substStr]
  imodintro
  rw (occs:=[2]) [isList.eq_def]
  cases ls with
  | nil =>
    simp
    iclear IH
    icases Hl with %heq; subst heq
    wp_pures; simp [Exp.subst]
    imodintro
    iapply HΦ $$ %_ %([])
    · unfold isList; itrivial
    · itrivial
    · itrivial
  | cons head tail =>
    simp
    icases Hl with ⟨%l, %tl, %heq, Hpt, Hl⟩; subst heq
    wp_pures; simp [Exp.subst, Exp.substStr]
    wp_bind !_
    iapply wp_load $$ [$]
    iintro !> Hpt
    wp_pures; simp [Exp.subst, Exp.substStr]
    wp_pures; simp [Exp.subst, Exp.substStr]
    wp_pures; simp [Exp.subst, Exp.substStr]
    wp_pures
    wp_bind ?partition _
    iapply partition_spec $$ [$]
    iintro %l1 %l2 Hl1 Hl2
    wp_pures; simp [Exp.subst, Exp.substStr]
    wp_pures
    wp_bind ?quicksort _
    iapply IH $$ [$]
    iintro %l1' %ls1' Hl1 %_ %_
    wp_pures; simp [Exp.subst, Exp.substStr]
    wp_pures
    wp_bind ?quicksort _
    iapply IH $$ [$]
    iintro %l2' %ls2' Hl2 %_ %_
    wp_pures; simp [Exp.subst, Exp.substStr]
    wp_pures
    wp_bind ?cons _
    iapply cons_spec $$ Hl2
    iintro %_ _
    wp_pures; simp [Exp.subst, Exp.substStr]
    wp_pures
    iapply append_spec $$ [$] [$]
    iintro %_ _
    iapply HΦ $$ [$]
    · ipureintro
      have : ls2'.all (head < ·) := by grind
      grind [List.pairwise_cons]
    · ipureintro
      grind [List.filter_append_perm]


-- example (l l1 l2 : List Int) x :
--   List.Perm (l.filter (· ≤ x)) l1 →
--   List.Perm (l.filter (x < ·)) l2 →
--   List.Perm (x :: l) (l1 ++ x :: l2) := by
--     intro h1 h2
--     have : List.Perm l (l.filter (· ≤ x) ++ l.filter (x < ·)) := by
--       grind [List.filter_append_perm]
--     grind

-- example (l l1 l2 : List Int) x :
--   List.Perm (l.filter (· ≤ x)) l1 →
--   List.Pairwise LE.le l1 →
--   List.Pairwise LE.le l2 →
--   List.Perm (l.filter (x < ·)) l2 →
--   List.Pairwise LE.le (l1 ++ x :: l2) := by
--     intro h1 h2 h3 h4
--     have : l2.all (x < ·) := by grind [List.Perm.mem_iff]
--     grind [List.pairwise_cons]
