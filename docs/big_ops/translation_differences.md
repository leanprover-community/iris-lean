# BigOpList.lean vs Rocq big_op.v: Translation Differences

This document tracks theorems in `BigOpList.lean` and `BigOpList2.lean` that differ from or are missing compared to the Rocq Iris `big_op.v` file.

---

## Part A: BigSepL (Single List) Differences

### 1. Missing `Timeless` Instances

**Location:** Lines 262-297 (commented out)

**Rocq has:**
- `big_sepL_timeless`
- `big_sepL_timeless'`
- `big_sepL_timeless_id`

**Reason:** The Lean version lacks a `sep_timeless` instance (Timeless for `P ∗ Q` when both are Timeless). The Rocq version relies on `big_opL_closed` which requires this infrastructure.

---

### 2. `big_sepL_submseteq` Signature Difference

**Rocq:** Uses `l1 ⊆+ l2` (submultiset relation from stdpp)

**Lean:** Takes explicit permutation witness `(l₁ ++ l).Perm l₂`

**Reason:** Lean lacks stdpp's submultiset relation. The explicit permutation witness is how stdpp defines submultiset internally.

---

### 3. `big_sepL_intro` Signature Difference

**Rocq:** `□ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x) ⊢ [∗ list] k↦x ∈ l, Φ k x`

**Lean:** Uses `[Intuitionistic P]` typeclass constraint on source proposition

**Reason:** Different encoding styles. Lean's approach is more explicit about the resource P being duplicable via typeclass.

---

### 4. Missing `big_sepL_zip_seqZ` (Integer-indexed)

**Rocq has:** `big_sepL_zip_seqZ` using `Z` (integers)

**Lean has:** Only `zip_seq` with `Nat`

**Reason:** Lean doesn't emphasize integers as much as Coq's standard library.

---

## Part B: BigSepL2 (Two Lists) Differences

### 8. `big_sepL2_later_1`

**Rocq:**
```coq
Lemma big_sepL2_later_1 `{BiAffine PROP} Φ l1 l2 :
  ▷ ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2) ⊢
    ◇ [∗ list] k↦x1;x2 ∈ l1;l2, ▷ Φ k x1 x2.
```

**Lean:**
```lean
theorem later_1 [BIAffine PROP] {Φ : Nat → A → B → PROP} {l1 : List A} {l2 : List B}:
    later (bigSepL2 Φ l1 l2) ⊢ except0 (bigSepL2 (fun k x1 x2 => later (Φ k x1 x2)) l1 l2)
```

**Status:** Now ported with except-0 (`◇`) support. Both versions require BIAffine.

---

### 9. Missing `big_sepL2_proper_2` (OFE on A, B)

**Rocq has:**
```coq
Lemma big_sepL2_proper_2 {A B : ofe} (Φ Ψ : nat → A → B → PROP) l1 l2 l1' l2' :
  l1 ≡ l1' → l2 ≡ l2' →
  (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 ⊣⊢ Ψ k y1 y2) →
  ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢ ([∗ list] k↦y1;y2 ∈ l1';l2', Ψ k y1 y2).
```

**Lean:** Not ported.

**Reason:** Requires OFE structure on `A` and `B` (list element types). Current Lean formalization focuses on cases where `A` and `B` are plain types.

---

### 10. Missing `big_sepL2_closed` (Meta-Lemma)

**Rocq has:**
```coq
Lemma big_sepL2_closed (C : PROP → Prop) Φ l1 l2 :
  C emp →
  C False →
  (∀ P Q, C P → C Q → C (P ∗ Q)) →
  (∀ k x1 x2, l1 !! k = Some x1 → l2 !! k = Some x2 → C (Φ k x1 x2)) →
  C ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2).
```

**Lean:** Not ported.

**Reason:** This is a meta-lemma for proving properties like Persistent, Affine, Timeless close under bigSepL2. Lean uses direct inductive proofs for each typeclass instance instead.

---

### 11. Missing `big_sepL2_timeless` Family

**Rocq has:**
- `big_sepL2_nil_timeless`
- `big_sepL2_timeless`
- `big_sepL2_timeless'`

**Lean:** Not ported.

**Reason:** Same as BigSepL - requires `sep_timeless` infrastructure.

## Part C: BigAndL (Big Conjunction) Differences

### 12. `big_andL_submseteq` Not Ported

**Rocq:**
```coq
Lemma big_andL_submseteq (Φ : A → PROP) l1 l2 :
  l1 ⊆+ l2 → ([∧ list] y ∈ l2, Φ y) ⊢ [∧ list] y ∈ l1, Φ y.
```

**Lean:** Not ported.

**Reason:** Lean lacks stdpp's `⊆+` (submultiset) relation. The `perm` lemma covers the permutation case directly.

---

### 13. `big_andL_mono'` and `big_andL_id_mono'` Not Ported

**Rocq has:**
- `big_andL_mono'` - unconditional pointwise entailment
- `big_andL_id_mono'` - Proper instance for Forall2

**Lean:** Not ported (uses direct `mono` and `proper` instead).

**Reason:** These are convenience wrappers. Lean's `mono` covers the conditional case, and `proper`/`congr` handle equivalences.

---

### 14. Missing `big_andL_ne` (OFE Non-Expansiveness)

**Rocq has:**
```coq
Lemma big_andL_ne Φ Ψ l n :
  (∀ k y, l !! k = Some y → Φ k y ≡{n}≡ Ψ k y) →
  ([∧ list] k ↦ y ∈ l, Φ k y) ≡{n}≡ ([∧ list] k ↦ y ∈ l, Ψ k y).
```

**Lean:** Not ported.

**Reason:** The OFE-level non-expansiveness is handled at the `BigOpL.congr_ne` level in the algebra layer. BI-level lemmas typically work with `≡` (equivalence) via `proper` rather than `≡{n}≡` (n-distance).

---

### 15. Missing `big_andL_timeless` Family

**Rocq has:**
- `big_andL_nil_timeless`
- `big_andL_timeless`
- `big_andL_timeless'`

**Lean:** Not ported.

**Reason:** Timeless instances require infrastructure for `and_timeless : Timeless P → Timeless Q → Timeless (P ∧ Q)`. This is simpler than `sep_timeless` and could be added.

---

### 16. Missing `big_andL_absorbing` Family

**Rocq has:**
- `big_andL_nil_absorbing` - instance for nil
- `big_andL_absorbing` - conditional lemma
- `big_andL_absorbing'` - unconditional instance

**Lean:** Not ported.

**Reason:** Absorbing typeclass instances for BigAndL not yet implemented.

---

## Part D: BigOrL (Big Disjunction) Differences

### 17. `big_orL_submseteq` Signature Difference

**Rocq:**
```coq
Lemma big_orL_submseteq (Φ : A → PROP) l1 l2 :
  l1 ⊆+ l2 → ([∨ list] y ∈ l1, Φ y) ⊢ [∨ list] y ∈ l2, Φ y.
```

**Lean:**
```lean
theorem submseteq {Φ : A → PROP} {l₁ l₂ l : List A}
    (h : (l₁ ++ l).Perm l₂) :
    ([∨ list] x ∈ l₁, Φ x) ⊢ [∨ list] x ∈ l₂, Φ x
```

**Reason:** Lean lacks stdpp's `⊆+` relation. Uses explicit permutation witness instead. Note direction: for BigOrL the entailment goes FROM smaller list TO larger.

---

### 18. `big_orL_id_mono'` Signature Difference

**Rocq:**
```coq
Global Instance big_orL_id_mono' :
  Proper (Forall2 (⊢) ==> (⊢)) (big_opL (@bi_or PROP) (λ _ P, P)).
```

**Lean:**
```lean
theorem id_mono' {l₁ l₂ : List PROP}
    (hlen : l₁.length = l₂.length)
    (h : ∀ (i : Nat) (P Q : PROP), l₁[i]? = some P → l₂[i]? = some Q → P ⊢ Q) :
    ([∨ list] P ∈ l₁, P) ⊢ [∨ list] P ∈ l₂, P
```

**Reason:** Lean lacks `Forall2` in its standard library. Uses indexed lookup instead.

---

### 19. Missing `big_orL_ne` (OFE Non-Expansiveness)

**Rocq has:**
```coq
Lemma big_orL_ne Φ Ψ l n :
  (∀ k y, l !! k = Some y → Φ k y ≡{n}≡ Ψ k y) →
  ([∨ list] k ↦ y ∈ l, Φ k y) ≡{n}≡ ([∨ list] k ↦ y ∈ l, Ψ k y).
```

**Lean:** Not ported.

**Reason:** Same as BigAndL - handled at the algebra layer via `BigOpL.congr_ne`.

---

### 20. Missing `big_orL_timeless` Family

**Rocq has:**
- `big_orL_nil_timeless`
- `big_orL_timeless`
- `big_orL_timeless'`

**Lean:** Not ported.

**Reason:** Requires `or_timeless : Timeless P → Timeless Q → Timeless (P ∨ Q)` infrastructure.

---

### 21. `big_orL_zip_seqZ` Integer Version

**Rocq has:**
```coq
Lemma big_orL_zip_seqZ (Φ : Z * A → PROP) n len l :
  length l ≤ len →
  ([∨ list] ky ∈ zip (seqZ n len) l, Φ ky) ⊣⊢
  ([∨ list] k ↦ y ∈ l, Φ ((n + k)%Z, y)).
```

**Lean has:** `BigOrL.zip_seqZ` but uses `Nat` instead of `Z`.

**Reason:** Lean port focuses on `Nat` indexing; `Z` (integers) not ported.

---

## Summary Table

| Category | Status | Priority |
|----------|--------|----------|
| Timeless instances (BigSepL) | Blocked on `sep_timeless` | Medium |
| Timeless instances (BigSepL2) | Blocked on `sep_timeless` | Medium |
| Timeless instances (BigAndL) | Blocked on `and_timeless` | Low |
| Timeless instances (BigOrL) | Blocked on `or_timeless` | Low |
| Absorbing instances (BigAndL) | Not ported | Low |
| Integer variants (`seqZ`) | Missing (uses Nat) | Low |
| `submseteq` (BigAndL) | Not ported (uses `perm`) | Low |
| `submseteq` (BigOrL) | Ported with perm witness | Done |
| `mono'`/`id_mono'` (BigAndL) | Not ported | Low |
| `mono'`/`id_mono'` (BigOrL) | Ported with indexed lookup | Done |
| `intro` signature | Design difference | N/A |
| `proper_2` (OFE on elements) | Not ported | Low |
| `closed` meta-lemma | Direct proofs instead | N/A |
| `later_1` | Ported with except-0 (`◇`) | Done |
| `app`/`snoc` length arguments | **Aligned with Rocq** | Done |
| `forall'` Persistent arg | Design difference | N/A |
| `ne` (OFE non-expansiveness) | Algebra layer handles | N/A |
| BigOrL `persistent` naming | `_cond` suffix pattern | Done |
| BigOrL `zip_seqZ` | Uses `Nat` not `Z` | Done |
| BigAndL `zip_seqZ` | Uses `Nat` not `Z` | Done |
| BigSepM `lookup` | Split into Affine/Absorbing | Done |
| BigSepM `lookup_dom` | Uses explicit value, Affine only | Done |
| BigSepM `insert_2` | Split into Affine/Absorbing | Done |
| BigSepM `subseteq` | Sorry (needs map laws) | Partial |
| BigSepM `delete` | Added `toList_erase` law | Done |
| BigSepM `intro` | Uses [Intuitionistic P] | Done |
| BigSepM `forall'` | Split into _1'/\_2' helpers | Done |
| BigSepM `dup` | Uses ⊢ not -∗ | Done |
| BigSepM `impl`/`wand` | Uses ⊢ + single -∗ | Done |
| BigSepM `persistently` | Requires BIAffine | Done |
| BigSepM `later`/`laterN` | Biconditional requires BIAffine | Done |
| BigSepM `pure'` | Requires BIAffine | Done |
| BigSepM map transforms | Explicit perm proofs | Done |
| BigSepM `union` | Perm proof (not ##ₘ) | Done |
| BigSepM `filter` | Requires FiniteMapLawsSelf | Done |
| BigSepM `mapForall` | Local definition | Done |
| BigSepM `fn_insert*` | Not ported | Low |
| BigSepM `sep_zip*` | Not ported | Low |
| BigSepM `impl_strong` etc. | Not ported | Low |
| BigSepM `kmap` | Not ported | Low |
| BigAndM `subseteq` | Sorry (needs map laws) | Partial |
| BigAndM `intro` | Simpler (no Intuitionistic) | Done |
| BigAndM `and'` | Biconditional (idempotent) | Done |
| BigAndM unit | Uses `True` not `emp` | Done |
| BigAndM `persistently` | No BIAffine needed | Done |
| BigAndM `later`/`laterN` | No BIAffine needed | Done |
| BigAndM `pure_2` | No affinely needed | Done |
| BigAndM `affine` instance | Lean-only, requires BIAffine | Done |
| BigAndM map transforms | Explicit perm proofs | Done |
| BigAndM `union` | Perm proof (not ##ₘ) | Done |
| BigAndM `map_to_list` | Lean-only addition | Done |
| BigAndM `fn_insert*` | Not ported | Low |
| BigAndM `kmap` | Not ported | Low |
| BigAndM `map_seq*` | Not ported | Low |
| BigAndM Timeless | Not ported | Low |

---

## Part E: BigSepM (Map) Differences

### 22. `big_sepM_lookup` Split into Separate Lemmas

**Rocq:**
```coq
Lemma big_sepM_lookup Φ m i x
  `{!TCOr (∀ j y, Affine (Φ j y)) (Absorbing (Φ i x))} :
  m !! i = Some x → ([∗ map] k↦y ∈ m, Φ k y) ⊢ Φ i x.
```

**Lean:**
```lean
theorem lookup {Φ : K → V → PROP} {m : M} {k : K} {v : V} [∀ j w, Affine (Φ j w)]
    (h : get? m k = some v) :
    ([∗ map] k' ↦ x ∈ m, Φ k' x) ⊢ Φ k v

theorem lookup_absorbing {Φ : K → V → PROP} {m : M} {k : K} {v : V} [Absorbing (Φ k v)]
    (h : get? m k = some v) :
    ([∗ map] k' ↦ x ∈ m, Φ k' x) ⊢ Φ k v
```

**Reason:** Lean splits TCOr-based lemmas into separate versions for Affine and Absorbing cases. This makes typeclass inference more predictable.

---

### 23. `big_sepM_delete` Requires New FiniteMapLaws

**Rocq:** Uses `big_opM_delete` which relies on stdpp's map infrastructure.

**Lean:** Added `toList_erase` law to `FiniteMapLaws`:
```lean
toList_erase : ∀ (m : M) k v, get? m k = some v →
  (toList m).Perm ((k, v) :: toList (erase m k))
```

**Reason:** The abstract `FiniteMap` interface needed an additional law to express that erasing a key produces a permutation-equivalent list.

---

### 24. `big_sepM_subseteq` Uses Sorry

**Rocq:**
```coq
Lemma big_sepM_subseteq Φ m1 m2 `{!∀ k x, Affine (Φ k x)} :
  m2 ⊆ m1 → ([∗ map] k ↦ x ∈ m1, Φ k x) ⊢ [∗ map] k ↦ x ∈ m2, Φ k x.
Proof.
  intros ?. rewrite -(map_difference_union m2 m1) //.
  rewrite big_opM_union; last by apply map_disjoint_difference_r1.
  assert (∀ kx, Affine (uncurry Φ kx)) by (intros []; apply _).
  by rewrite sep_elim_l.
Qed.
```

**Lean:** Uses sorry because the proof requires:
1. Map difference operation: `m₁ ∖ m₂`
2. `map_difference_union : m₂ ∪ (m₁ ∖ m₂) = m₁` when `m₂ ⊆ m₁`
3. `big_sepM_union` for disjoint maps
4. Proof that `m₂ ##ₘ (m₁ ∖ m₂)` when `m₂ ⊆ m₁`

**Status:** Blocked on extending the abstract FiniteMap interface with difference and disjoint union laws.

---

### 25. `big_sepM_intro` Uses Intuitionistic Typeclass

**Rocq:**
```coq
Lemma big_sepM_intro Φ m :
  □ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x) ⊢ [∗ map] k↦x ∈ m, Φ k x.
```

**Lean:**
```lean
theorem intro {P : PROP} {Φ : K → V → PROP} {m : M} [Intuitionistic P]
    (h : ∀ k v, get? m k = some v → P ⊢ Φ k v) :
    P ⊢ [∗ map] k ↦ x ∈ m, Φ k x
```

**Reason:** Lean uses the `[Intuitionistic P]` typeclass constraint instead of the `□` modality in the statement. This makes the typeclass system handle the resource-duplication property.

---

### 26. `big_sepM_forall` Biconditional with Helpers

**Rocq:**
```coq
Lemma big_sepM_forall `{!BiAffine PROP} Φ m :
  (∀ k x, Persistent (Φ k x)) →
  ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x).
```

**Lean:**
```lean
theorem forall' {Φ : K → V → PROP} {m : M} [BIAffine PROP]
    [∀ k v, Persistent (Φ k v)] :
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ ∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v)

theorem forall_1' : ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ ∀ k, ∀ v, iprop(⌜get? m k = some v⌝ → Φ k v)
theorem forall_2' : (∀ k v, iprop(⌜get? m k = some v⌝ → Φ k v)) ⊢ [∗ map] k ↦ x ∈ m, Φ k x
```

**Reason:** Lean splits the biconditional into helper lemmas `forall_1'` and `forall_2'` for forward and backward directions. This makes proofs more modular.

---

### 27. `big_sepM_dup` Statement Difference

**Rocq:**
```coq
Lemma big_sepM_dup P `{!Affine P} m :
  □ (P -∗ P ∗ P) -∗ P -∗ [∗ map] k↦x ∈ m, P.
```

**Lean:**
```lean
theorem dup {P : PROP} [Affine P] {m : M} :
    □ (P -∗ P ∗ P) ⊢ P -∗ [∗ map] _k ↦ _x ∈ m, P
```

**Reason:** Lean uses `⊢` instead of `-∗` for the outer entailment, making the wand_intro more explicit in the proof.

---

## Part F: BigAndM (Map Conjunction) Differences

### 28. BigAndM Uses `iprop(True)` as Unit

**Rocq:** Big conjunction uses `True` as the unit (identity element).

**Lean:**
```lean
abbrev bigAndM [BI PROP] {M K V} [FiniteMap M K V]
    (Φ : K → V → PROP) (m : M) : PROP :=
  bigOpL and iprop(True) (fun _ kv => Φ kv.1 kv.2) (toList m)
```

**Reason:** This is the same as Rocq; `iprop(True)` is Lean's notation for the BI `True` proposition.

---

### 29. `big_andM_subseteq` Uses Sorry

**Rocq:**
```coq
Lemma big_andM_subseteq (Φ : K → A → PROP) m1 m2 :
  m2 ⊆ m1 → ([∧ map] k↦x ∈ m1, Φ k x) ⊢ [∧ map] k↦x ∈ m2, Φ k x.
```

**Lean:** Uses `sorry` for the same reason as `BigSepM.subseteq`:
- Requires map difference/union laws not yet in the abstract FiniteMap interface

**Status:** Blocked on extending FiniteMap with subset/difference operations.

---

### 30. BigAndM Simpler Than BigSepM

Several BigAndM lemmas are simpler than their BigSepM counterparts:

| Lemma | BigSepM | BigAndM | Reason |
|-------|---------|---------|--------|
| `intro` | Requires `[Intuitionistic P]` | No constraint needed | `∧` doesn't consume resources |
| `and'` | One direction only | Biconditional | `∧` is idempotent |
| `pure_2` | Requires `⬚` (affinely) | Direct `⌜P⌝ ⊢ ...` | `True ∧ ⌜P⌝ ⊣⊢ ⌜P⌝` |

---

### 31. BigAndM Missing Affine Instances

**Rocq:** BigAndM doesn't have Affine instances (since `True ∧ ... ∧ True` is not generally affine unless the BI is affine).

**Lean:** Same - no Affine typeclass instances for BigAndM.

---

### 32. `true_and` Helper Pattern

**Lean:** Uses a local helper in proofs involving the unit:
```lean
have true_and : ∀ (X : PROP), iprop(True) ∧ X ⊣⊢ X :=
  fun X => ⟨and_elim_r, and_intro true_intro .rfl⟩
```

**Reason:** Unlike `emp_sep` which has dedicated lemmas, `True ∧ X ⊣⊢ X` is composed inline from basic laws.

---

## Summary Table Update (BigAndM)

| Category | Status | Priority |
|----------|--------|----------|
| BigAndM `subseteq` | Sorry (needs map laws) | Partial |
| BigAndM `intro` | Simpler than BigSepM | Done |
| BigAndM `and'` | Biconditional | Done |
| BigAndM Affine instances | Not applicable | N/A |
| BigAndM Timeless instances | Not ported | Low |

---

## Part G: BigSepM Additional Differences

### 33. `big_sepM_persistently` Requires `BIAffine`

**Rocq:**
```coq
Lemma big_sepM_persistently `{BiAffine PROP} Φ m :
  <pers> ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ [∗ map] k↦x ∈ m, <pers> Φ k x.
```

**Lean:**
```lean
theorem persistently {Φ : K → V → PROP} {m : M} [BIAffine PROP] :
    iprop(<pers> [∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗ map] k ↦ x ∈ m, <pers> Φ k x
```

**Status:** Same signature, both require `BIAffine`.

---

### 34. `big_sepM_later` Requires `BIAffine`

**Rocq:**
```coq
Lemma big_sepM_later `{BiAffine PROP} Φ m :
  ▷ ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ [∗ map] k↦x ∈ m, ▷ Φ k x.
```

**Lean:**
```lean
theorem later [BIAffine PROP] {Φ : K → V → PROP} {m : M} :
    iprop(▷ [∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗ map] k ↦ x ∈ m, ▷ Φ k x
```

**Status:** Same signature, both require `BIAffine`. The `later_2` direction does not require `BIAffine`.

---

### 35. `big_sepM_pure` Requires `BIAffine`

**Rocq:**
```coq
Lemma big_sepM_pure `{!BiAffine PROP} (φ : K → A → Prop) m :
  ([∗ map] k↦x ∈ m, ⌜φ k x⌝) ⊣⊢ ⌜map_Forall φ m⌝.
```

**Lean:**
```lean
theorem pure' [BIAffine PROP] {φ : K → V → Prop} {m : M} :
    ([∗ map] k ↦ x ∈ m, ⌜φ k x⌝) ⊣⊢ (⌜mapForall φ m⌝ : PROP)
```

**Status:** Same signature, both require `BIAffine`. The forward direction (`pure_1`) does not require `BIAffine`.

---

### 36. `mapForall` Definition

**Rocq:** Uses `map_Forall` from stdpp.

**Lean:** Defines `mapForall` locally:
```lean
def mapForall (φ : K → V → Prop) (m : M) : Prop :=
  ∀ k v, get? m k = some v → φ k v
```

**Reason:** Lean implementation provides its own definition equivalent to stdpp's `map_Forall`.

---

### 37. Map Transformation Lemmas Require Explicit Permutation Proofs

The following BigSepM lemmas take explicit permutation proofs instead of using typeclasses:

| Lemma | Permutation Required |
|-------|---------------------|
| `fmap` | `(toList (map f m)).Perm ((toList m).map ...)` |
| `omap` | `(toList (filterMap f m)).Perm ((toList m).filterMap ...)` |
| `union` | `(toList (m₁ ∪ m₂)).Perm (toList m₁ ++ toList m₂)` |
| `list_to_map` | `(toList (ofList l)).Perm l` |

**Reason:** The abstract `FiniteMap` interface doesn't provide these permutation proofs automatically. Users must supply them for their specific map implementations.

---

### 38. Filter Lemmas Require `FiniteMapLawsSelf`

**Rocq:** Uses `mapset.countable` and related infrastructure.

**Lean:**
```lean
theorem filter' {Φ : K → V → PROP} {m : M} (p : K → V → Bool) :
    ([∗ map] k ↦ x ∈ FiniteMap.filter p m, Φ k x) ⊣⊢ ...
```

**Requires:** `[FiniteMapLawsSelf M K V]` which provides `toList_filter` law.

**Reason:** The `FiniteMapLawsSelf` typeclass provides the necessary law that filtering preserves the list permutation property.

---

### 39. `big_sepM_filter` BIAffine Difference

**Rocq:**
```coq
Lemma big_sepM_filter `{!BiAffine PROP}
    (φ : K * A → Prop) `{∀ kx, Decision (φ kx)} Φ m :
  ([∗ map] k ↦ x ∈ filter φ m, Φ k x) ⊣⊢
  ([∗ map] k ↦ x ∈ m, ⌜φ (k, x)⌝ → Φ k x).
```

**Lean:**
```lean
theorem filter'' [BIAffine PROP] {Φ : K → V → PROP} {m : M} (p : K → V → Bool) :
    ([∗ map] k ↦ x ∈ FiniteMap.filter p m, Φ k x) ⊣⊢
      [∗ map] k ↦ x ∈ m, iprop(⌜p k x = true⌝ → Φ k x)
```

**Note:** Both require `BIAffine`. The Rocq version uses `decide_emp` trick internally. The `filter'` version (without `BIAffine`) uses `if ... then ... else emp` in both.

---

### 40. `big_sepM_union` Disjointness vs Permutation

**Rocq:**
```coq
Lemma big_sepM_union Φ m1 m2 :
  m1 ##ₘ m2 →
  ([∗ map] k↦y ∈ m1 ∪ m2, Φ k y)
  ⊣⊢ ([∗ map] k↦y ∈ m1, Φ k y) ∗ ([∗ map] k↦y ∈ m2, Φ k y).
```

**Lean:**
```lean
theorem union {Φ : K → V → PROP} {m₁ m₂ : M}
    (hperm : (toList (m₁ ∪ m₂)).Perm (toList m₁ ++ toList m₂)) :
    ([∗ map] k ↦ y ∈ m₁ ∪ m₂, Φ k y) ⊣⊢
      ([∗ map] k ↦ y ∈ m₁, Φ k y) ∗ [∗ map] k ↦ y ∈ m₂, Φ k y
```

**Difference:** Rocq takes a disjointness hypothesis `m1 ##ₘ m2`. Lean takes an explicit permutation proof. Users providing permutation proofs typically have disjoint maps (otherwise union is not a simple append).

---

### 41. `big_sepM_lookup_dom` Uses `is_Some` vs Explicit Value

**Rocq:**
```coq
Lemma big_sepM_lookup_dom (Φ : K → PROP) m i
  `{!TCOr (∀ j, Affine (Φ j)) (Absorbing (Φ i))} :
  is_Some (m !! i) → ([∗ map] k↦_ ∈ m, Φ k) ⊢ Φ i.
```

**Lean:**
```lean
theorem lookup_dom {Φ : K → PROP} {m : M} {k : K} {v : V} [∀ j, Affine (Φ j)]
    (h : get? m k = some v) :
    bigSepM (fun k' _ => Φ k') m ⊢ Φ k
```

**Difference:** Rocq uses `is_Some (m !! i)` and `TCOr` for Affine/Absorbing. Lean requires an explicit value `v` and only has the Affine version. An Absorbing version could be added.

---

### 42. `big_sepM_impl` Statement Difference

**Rocq:**
```coq
Lemma big_sepM_impl Φ Ψ m :
  ([∗ map] k↦x ∈ m, Φ k x) -∗
  □ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x -∗ Ψ k x) -∗
  [∗ map] k↦x ∈ m, Ψ k x.
```

**Lean:**
```lean
theorem impl {Φ Ψ : K → V → PROP} {m : M} :
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊢
      □ (∀ k v, iprop(⌜get? m k = some v⌝ → Φ k v -∗ Ψ k v)) -∗ [∗ map] k ↦ x ∈ m, Ψ k x
```

**Difference:** Rocq uses two separate wands (`-∗ ... -∗`). Lean uses entailment followed by single wand (`⊢ ... -∗`). Semantically equivalent due to curry/uncurry.

---

### 43. `big_sepM_wand` Statement Difference

**Rocq:**
```coq
Lemma big_sepM_wand Φ Ψ m :
  ([∗ map] k↦x ∈ m, Φ k x) -∗
  ([∗ map] k↦x ∈ m, Φ k x -∗ Ψ k x) -∗
  [∗ map] k↦x ∈ m, Ψ k x.
```

**Lean:**
```lean
theorem wand {Φ Ψ : K → V → PROP} {m : M} :
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊢
      ([∗ map] k ↦ x ∈ m, Φ k x -∗ Ψ k x) -∗ [∗ map] k ↦ x ∈ m, Ψ k x
```

**Difference:** Same as `impl` - Rocq uses two wands, Lean uses entailment + wand.

---

### 44. Not Ported: `big_sepM_fn_insert*`

**Rocq has:**
```coq
Lemma big_sepM_fn_insert {B} (Ψ : K → A → B → PROP) (f : K → B) m i x b :
  m !! i = None →
     ([∗ map] k↦y ∈ <[i:=x]> m, Ψ k y (<[i:=b]> f k))
  ⊣⊢ (Ψ i x b ∗ [∗ map] k↦y ∈ m, Ψ k y (f k)).

Lemma big_sepM_fn_insert' (Φ : K → PROP) m i x P :
  m !! i = None →
  ([∗ map] k↦y ∈ <[i:=x]> m, <[i:=P]> Φ k) ⊣⊢ (P ∗ [∗ map] k↦y ∈ m, Φ k).
```

**Lean:** Not ported.

**Reason:** Low priority. These lemmas handle function insertion which is less common.

---

### 45. Not Ported: `big_sepM_sep_zip*`

**Rocq has:**
```coq
Lemma big_sepM_sep_zip_with ... (f : A → B → C) ... m1 m2 :
  ...
  ([∗ map] k↦xy ∈ map_zip_with f m1 m2, Φ1 k (g1 xy) ∗ Φ2 k (g2 xy)) ⊣⊢
  ([∗ map] k↦x ∈ m1, Φ1 k x) ∗ ([∗ map] k↦y ∈ m2, Φ2 k y).

Lemma big_sepM_sep_zip ...
```

**Lean:** Not ported.

**Reason:** Low priority. Requires `map_zip_with` infrastructure.

---

### 46. Not Ported: `big_sepM_impl_strong`, `big_sepM_impl_dom_subseteq`

**Rocq has:** These lemmas for advanced impl patterns with filtered maps.

**Lean:** Not ported.

**Reason:** Low priority. Complex lemmas for specialized use cases.

---

### 47. Not Ported: `big_sepM_kmap`

**Rocq:**
```coq
Lemma big_sepM_kmap `{Countable K1, Countable K2} {A}
    (h : K1 → K2) `{!Inj (=) (=) h} (Φ : K2 → A → PROP) (m : gmap K1 A) :
  ([∗ map] k2 ↦ y ∈ kmap h m, Φ k2 y) ⊣⊢ ([∗ map] k1 ↦ y ∈ m, Φ (h k1) y).
```

**Lean:** Not ported.

**Reason:** Requires `kmap` (key mapping) operation on maps.

---

## Part I: BigAndM Additional Differences

### 48. BigAndM Uses `True` as Unit (vs `emp` for BigSepM)

**BigSepM:** Uses `emp` as the unit for empty maps.
```lean
abbrev bigSepM ... := bigOpL sep emp ...
```

**BigAndM:** Uses `True` as the unit for empty maps.
```lean
abbrev bigAndM ... := bigOpL and iprop(True) ...
```

**Implication:** This affects `omap` and `filter'` lemmas:
- BigSepM `omap`: `none` case produces `emp`
- BigAndM `omap`: `none` case produces `True`
- BigSepM `filter'`: `false` case produces `emp`
- BigAndM `filter'`: `false` case produces `True`

---

### 49. BigAndM `persistently` Does NOT Require `BIAffine`

**Rocq:**
```coq
Lemma big_andM_persistently Φ m :
  <pers> ([∧ map] k↦x ∈ m, Φ k x) ⊣⊢ [∧ map] k↦x ∈ m, <pers> Φ k x.
```

**Lean:**
```lean
theorem persistently {Φ : K → V → PROP} {m : M} :
    iprop(<pers> [∧ map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∧ map] k ↦ x ∈ m, <pers> Φ k x
```

**Status:** Same - neither requires `BIAffine`. This is a key difference from `BigSepM.persistently` which requires `BIAffine`.

---

### 50. BigAndM `later` Does NOT Require `BIAffine`

**Rocq:**
```coq
Lemma big_andM_later Φ m :
  ▷ ([∧ map] k↦x ∈ m, Φ k x) ⊣⊢ [∧ map] k↦x ∈ m, ▷ Φ k x.
```

**Lean:**
```lean
theorem later {Φ : K → V → PROP} {m : M} :
    iprop(▷ [∧ map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∧ map] k ↦ x ∈ m, ▷ Φ k x
```

**Status:** Same - neither requires `BIAffine`. This is a key difference from `BigSepM.later` which requires `BIAffine`.

---

### 51. BigAndM `pure_2` Does NOT Require `affinely`

**Rocq:**
```coq
Lemma big_andM_pure_2 (φ : K → A → Prop) m :
  ⌜map_Forall φ m⌝ ⊢ [∧ map] k↦x ∈ m, ⌜φ k x⌝.
```

**Lean:**
```lean
theorem pure_2 {φ : K → V → Prop} {m : M} :
    (⌜mapForall φ m⌝ : PROP) ⊢ ([∧ map] k ↦ x ∈ m, ⌜φ k x⌝)
```

**Difference from BigSepM:** `BigSepM.affinely_pure_2` requires `<affine>` on the pure proposition because `emp` is not `True`. BigAndM doesn't need this because `True ∧ ⌜P⌝ ⊣⊢ ⌜P⌝`.

---

### 52. BigAndM `affine` Instance Requires `BIAffine`

**Rocq:** BigAndM doesn't have Affine instances in general.

**Lean:**
```lean
instance affine {Φ : K → V → PROP} {m : M} [BIAffine PROP] :
    Affine ([∧ map] k ↦ x ∈ m, Φ k x)
```

**Reason:** In a `BIAffine` setting, any proposition is affine, including big conjunctions. This is a Lean-only convenience instance.

---

### 53. BigAndM Map Transformation Lemmas

Same as BigSepM, the following BigAndM lemmas take explicit permutation proofs:

| Lemma | Permutation Required |
|-------|---------------------|
| `fmap` | `(toList (map f m)).Perm ((toList m).map ...)` |
| `omap` | `(toList (filterMap f m)).Perm ((toList m).filterMap ...)` |
| `union` | `(toList (m₁ ∪ m₂)).Perm (toList m₁ ++ toList m₂)` |

---

### 54. `big_andM_map_to_list` is Lean-Only

**Rocq:** Implicit in the definition.

**Lean:**
```lean
theorem map_to_list {Φ : K → V → PROP} {m : M} :
    ([∧ map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∧ list] kv ∈ toList m, Φ kv.1 kv.2)
```

**Reason:** Explicitly provided for convenience and symmetry with `BigSepM.map_to_list`.

---

## Implementation Notes

### Blocking Dependencies

1. **Timeless instances** require `sep_timeless : Timeless P → Timeless Q → Timeless (P ∗ Q)` to be defined first.

### Design Decisions

- Lean uses `[k]?` (Lean 4 list indexing) vs Rocq's `!! k` notation
- Lean uses `l.set i x` vs Rocq's `<[i:=x]>l` for list update
- Lean uses explicit `Intuitionistic` typeclass vs Rocq's `□` modality in some lemma statements
- Lean exposes permutation witnesses explicitly rather than using stdpp's `⊆+` relation
- Lean splits TCOr-based lemmas into separate Affine and Absorbing versions
- Lean adds `∧ emp` to nil_inv lemmas to preserve BI structure in non-affine settings

### Notation Differences

| Rocq | Lean |
|------|------|
| `[∗ list] k↦x1;x2 ∈ l1;l2, Φ` | `[∗ list] k ↦ x1,x2 ∈ l1,l2, Φ` |
| `l !! i` | `l[i]?` |
| `<[i:=x]>l` | `l.set i x` |
| `S n` | `n + 1` |
| `length l` | `l.length` |
| `reverse l` | `l.reverse` |
| `replicate n x` | `List.replicate n x` |
