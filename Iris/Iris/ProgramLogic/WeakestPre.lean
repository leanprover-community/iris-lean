/-
Copyright (c) 2026 Haokun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haokun Li
-/
module

public import Iris.ProgramLogic.Language
public import Iris.Algebra.OFE
public import Iris.Algebra.IProp
public import Iris.Instances.IProp
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.FUpd
public import Iris.BI
public import Iris.BI.BigOp
public import Iris.BI.Updates
public import Iris.ProofMode

@[expose] public section

/-! # Weakest Precondition (Stage 1: fixpoint skeleton)

References (Stage 1 接口审视，三参考交叉对比)：

- **Canonical**: Coq Iris `iris/program_logic/weakestpre.v` (commit d663f775)
  Defines `Inductive stuckness`, `Class irisGS_gen`, `Definition wp_pre`,
  `Local Instance wp_pre_contractive`, `Definition wp_def := λ s, fixpoint (wp_pre s)`,
  `Lemma wp_unfold`. 本文件 def/命题严格 1:1 自此处。
- **Proof-side reference**: `hxrts/iris-lean@fork/iris/vendor:src/Iris/ProgramLogic/WeakestPre.lean`
  (lines 60-470). 命题形态参考、tactic 思路参考——不复制代码。
- **Upstream operator source**: `Iris/Algebra/OFE.lean` (Contractive, fixpoint, fixpoint_unfold)；
  `Iris/Instances/Lib/{WSat,FUpd}.lean` (`InvGS_gen`, `uPred_fupd`, `BIFUpdate (IProp GF)`)；
  `Iris/BI/Updates.lean` (notation `|={E1,E2}=>`, `|={E}[E']▷=>`, `|={E}▷=>^[n]`)；
  `Iris/BI/BigOp/BigSepList.lean` (`[∗list] k ↦ x ∈ l, P k x`).
  本 stage 算子全部走 upstream，**不**复制 hxrts vendor 算子。

Phase 1-A 简化（CLAUDE.md §7 规定阶段 1 节奏 = 接口签名 + 命题真实 + proof sorry）：

- `num_laters_per_step = 0` （即每步用 1 个 ▷；matches hxrts；Coq 原版是 `S (num_laters_per_step ns)`）。
- `IrisGS` typeclass 暂不含 `state_interp_mono` 字段——Phase 1-B 在补真证明时回填。
- 所有 lemma proof = `sorry`。Stage 1 只需保证 lake build 通过 + 命题与 Coq weakestpre.v 1:1。

Stage 1 出口：Stuckness + IrisGS + wp_pre + wp_pre_contractive + wp + wp_unfold。
后续 stages（参见 CLAUDE.md §7 stage 分支组织）：

- stage/2-wp-basic: wp_value_fupd / wp_strong_mono / fupd_wp 等 ~10 lemma
- stage/3-wp-frame-bind: wp_frame_l/r / wp_wand / wp_bind / wp_pure_step
- stage/4-lifting: 见 Lifting.lean
- stage/5-7: Adequacy 系列
- stage/8-9: GhostMap / GenHeap
-/

namespace Iris.ProgramLogic

open Iris OFE COFE BI Iris.BI Iris.Algebra Iris.ProgramLogic.PrimStep

/-! ## Stuckness

Coq weakestpre.v: `Inductive stuckness := NotStuck | MaybeStuck.`
hxrts WeakestPre.lean line ~50: 用 `Stuckness.notStuck / .maybeStuck`（小写）。
本文件采用 hxrts 命名（Lean 习惯）。 -/

inductive Stuckness where
  | notStuck
  | maybeStuck
  deriving DecidableEq

namespace Stuckness

/-- 偏序：`notStuck ≤ maybeStuck`（即 NotStuck 是更强的要求）。
Coq weakestpre.v: `Definition stuckness_le ...`
hxrts WeakestPre.lean line ~260。 -/
def le : Stuckness → Stuckness → Prop
  | .notStuck, _ => True
  | .maybeStuck, .maybeStuck => True
  | .maybeStuck, .notStuck => False

end Stuckness

/-! ## IrisGS typeclass

Coq weakestpre.v `irisGS_gen`:
```
Class irisGS_gen (hlc : has_lc) (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS  : invGS_gen hlc Σ;
  state_interp : state Λ → nat → list (observation Λ) → nat → iProp Σ;
  fork_post : val Λ → iProp Σ;
  num_laters_per_step : nat → nat;
  state_interp_mono σ ns κs nt :
    state_interp σ ns κs nt ⊢ |={∅}=> state_interp σ (S ns) κs nt
}.
```

简化（vs Coq 原版，PR-ready 评估后保留）：
- 固定 `hlc = true`（即 `InvGS GF = InvGS_gen true GF`）；upstream `Examples/IProp.lean` 同样
  不参数化 hlc。

补全（vs hxrts，2026-05-12 PR-ready 化）：
- `num_laters_per_step` 字段：与 Coq 严格 1:1（per-step laters 参数化，HeapLang 风格 instance
  可填 `fun _ => 0`）。
- `state_interp_mono` 字段：与 Coq 与 hxrts 一致。 -/

class IrisGS (Expr : Type _) (State Obs Val : outParam (Type _))
    [Language Expr State Obs Val] (GF : BundledGFunctors)
    extends InvGS GF where
  /-- State interpretation: `σ → step_count → past_observations → num_forks → iProp`.
  Coq: field of `irisGS_gen`. -/
  state_interp : State → Nat → List Obs → Nat → IProp GF
  /-- Fixed postcondition for forked threads.
  Coq: field of `irisGS_gen`. -/
  fork_post : Val → IProp GF
  /-- Per-step number of `▷` laters (allows step-indexed reasoning to vary across step count).
  Coq: field of `irisGS_gen`. HeapLang-style instance 填 `fun _ => 0`. -/
  num_laters_per_step : Nat → Nat
  /-- State interpretation 关于 step_count 的单调性（Coq 原版字段）。
  Coq weakestpre.v `irisGS_gen.state_interp_mono`. -/
  state_interp_mono (σ : State) (ns : Nat) (κs : List Obs) (nt : Nat) :
    state_interp σ ns κs nt ⊢ iprop(|={∅}=> state_interp σ (ns + 1) κs nt)

/-! ## wp_pre

Coq weakestpre.v `wp_pre`:
```
Definition wp_pre `{!irisGS_gen hlc Λ Σ} (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ns κ κs nt,
     state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
       ⌜match s with NotStuck => reducible e1 σ1 | MaybeStuck => True end⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝
         ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
       state_interp σ2 (S ns) κs (length efs + nt) ∗
       wp E e2 Φ ∗
       [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post
  end%I.
```

2026-05-12 PR-ready 化：用 `S (IrisGS.num_laters_per_step ns)` 替代硬编码 1，严格 1:1 自 Coq。 -/

variable {Expr State Obs Val : Type _} [Language Expr State Obs Val]
variable {GF : BundledGFunctors} [iG : IrisGS Expr State Obs Val GF]

/-- 是否可还原（按 stuckness 选择）。Coq weakestpre.v 用 `match s with NotStuck => reducible | _ => True`。 -/
def stuckPred (s : Stuckness) (e : Expr) (σ : State) : Prop :=
  match s with
  | .notStuck => PrimStep.Reducible (Expr := Expr) (Obs := List Obs) (e, σ)
  | .maybeStuck => True

/-- 类型简写：wp 的函数类型 = `CoPset → Expr → (Val → IProp GF) → IProp GF`。
Coq 用 `coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ`. -/
abbrev WPFun (Expr Val : Type _) (GF : BundledGFunctors) :=
  CoPset → Expr → (Val → IProp GF) → IProp GF

/-- Pre-fixpoint of weakest precondition. Recursive call `wp` is a parameter.
Coq weakestpre.v `wp_pre`. hxrts WeakestPre.lean:301. -/
noncomputable def wp_pre (s : Stuckness)
    (wp : WPFun Expr Val GF)
    (E : CoPset) (e : Expr) (Φ : Val → IProp GF) : IProp GF :=
  match toVal (Val := Val) e with
  | some v => iprop(|={E}=> Φ v)
  | none => iprop(
      ∀ (σ1 : State) (ns : Nat) (κ κs : List Obs) (nt : Nat),
        IrisGS.state_interp (Expr := Expr) σ1 ns (κ ++ κs) nt ={E,∅}=∗
          ⌜stuckPred s e σ1⌝ ∗
          ∀ (e2 : Expr) (σ2 : State) (efs : List Expr),
            ⌜PrimStep.primStep (e, σ1) κ (e2, σ2, efs)⌝
              ={ ∅ }▷=∗^[ iG.num_laters_per_step ns + 1 ] (|={∅,E}=>
                IrisGS.state_interp (Expr := Expr) σ2 (ns + 1) κs (efs.length + nt) ∗
                wp E e2 Φ ∗
                [∗list] _i ↦ ef ∈ efs, wp ⊤ ef (IrisGS.fork_post (Expr := Expr))))

/-- Helper: `step_fupdN_ne` —— `|={E1}[E2]▷=∗^[k]` 是 NonExpansive in 内层 Q.

证明：induction over k；每层用 `BIFUpdate.ne + later_ne + BIFUpdate.ne`. -/
private theorem step_fupdN_ne {E1 E2 : CoPset} {k : Nat} {n : Nat}
    {X Y : IProp GF} (h : X ≡{n}≡ Y) :
    Nat.repeat (fun Q : IProp GF => iprop(|={E1}[E2]▷=> Q)) k X ≡{n}≡
      Nat.repeat (fun Q : IProp GF => iprop(|={E1}[E2]▷=> Q)) k Y := by
  induction k with
  | zero => exact h
  | succ k' IH =>
    refine BIFUpdate.ne.ne ?_
    refine later_ne.ne ?_
    refine BIFUpdate.ne.ne ?_
    exact IH

/-- Contractive instance for `wp_pre s`.
Coq weakestpre.v: `Local Instance wp_pre_contractive : Contractive (wp_pre s)`.
hxrts WeakestPre.lean:315 `wp_pre_contractive`（思路参考）。
模板：`Iris/Examples/IProp.lean:131-142` `wp_F_contractive`. -/
noncomputable instance wp_pre_contractive (s : Stuckness) :
    Contractive (fun W : WPFun Expr Val GF => wp_pre s W) where
  distLater_dist {n W₁ W₂ HW} E e Φ := by
    show wp_pre s W₁ E e Φ ≡{n}≡ wp_pre s W₂ E e Φ
    cases hto : toVal (Val := Val) e with
    | some v =>
        unfold wp_pre
        simp only [hto]
        exact .rfl
    | none =>
        unfold wp_pre
        simp only [hto]
        refine forall_ne fun σ => ?_
        refine forall_ne fun ns => ?_
        refine forall_ne fun κ => ?_
        refine forall_ne fun κs => ?_
        refine forall_ne fun nt => ?_
        refine wand_ne.ne .rfl ?_
        refine BIFUpdate.ne.ne ?_
        refine sep_ne.ne .rfl ?_
        refine forall_ne fun e2 => ?_
        refine forall_ne fun σ2 => ?_
        refine forall_ne fun efs => ?_
        refine wand_ne.ne .rfl ?_
        -- `_ ▷=∗^[k+1]` macro → `Nat.repeat _ (k+1) X = (fun Q => |={∅}[∅]▷=> Q) (Nat.repeat _ k X)`
        -- 透过外层 |={∅,∅}=> ▷ |={∅,∅}=> ...，▷ 那一层用 distLater_dist
        refine BIFUpdate.ne.ne ?_
        refine Contractive.distLater_dist fun m hm => ?_
        refine BIFUpdate.ne.ne ?_
        -- 现在余 `Nat.repeat _ (num_laters_per_step ns) inner` 两边对比——用 step_fupdN_ne helper
        refine step_fupdN_ne ?_
        -- 内 inner = |={∅,E}=> (state_interp ∗ W E e2 Φ ∗ [∗list])
        refine BIFUpdate.ne.ne ?_
        refine sep_ne.ne .rfl ?_
        refine sep_ne.ne ?_ ?_
        · exact HW m hm E e2 Φ
        · exact Iris.BI.BigSepL.bigSepL_dist fun {_ _} _ => HW m hm ⊤ _ _

/- `WPFun Expr Val GF` 自动是 COFE：

- `IProp GF = UPred (IResUR GF)` 是 COFE，通过 `instance : IsCOFE (UPred M)`
  (Iris/Algebra/UPred.lean:93) 与 `class abbrev COFE := OFE + IsCOFE` (OFE.lean:796) 合成
- 函数空间封闭性 `instance [∀ x, COFE (β x)] : COFE ((x : α) → β x)`
  (Iris/Algebra/OFE.lean:854) 套用 3 层：`Val → IProp GF`, `Expr → ...`, `CoPset → ...`

不需要显式 instance —— typeclass resolution 自动 derive。

旧 sorry 实例（Stage 1 接口骨架阶段占位）已移除（2026-05-12 Phase 1-B 消 sorry）. -/

/-- 强制 `WPFun Expr Val GF` 有默认值（fixpoint 需要 Inhabited）。 -/
noncomputable instance : Inhabited (WPFun Expr Val GF) :=
  ⟨fun _ _ _ => iprop(True)⟩

/-! ## wp 定义

Coq weakestpre.v:
```
Definition wp_def `{!irisGS_gen hlc Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) stuckness :=
  λ s : stuckness, fixpoint (wp_pre s).
```

hxrts WeakestPre.lean:416 `wp` 把 stuckness 一起带进 fixpoint（`wp_pre_all`）。
我们沿 Coq 原版风格：每个 stuckness 一个 fixpoint。 -/

/-- The weakest precondition.
Coq weakestpre.v: `Definition wp_def := λ s, fixpoint (wp_pre s)`.

Phase 1-B（2026-05-12）：COFE / Inhabited / wp_pre_contractive 都已就位，
fixpoint 可直接 elaborate。 -/
noncomputable def wp (s : Stuckness) : WPFun Expr Val GF :=
  fixpoint (fun W : WPFun Expr Val GF => wp_pre s W)

/-! ## wp_unfold

Coq weakestpre.v `wp_unfold`:
```
Lemma wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre s (wp s) E e Φ.
```

Phase 1-B（2026-05-12）：用 upstream `fixpoint_unfold` 翻 `≡` 为 `⊣⊢`。 -/
theorem wp_unfold (s : Stuckness) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) :
    wp (Expr := Expr) (Val := Val) (GF := GF) s E e Φ ⊣⊢
      wp_pre s (wp (Expr := Expr) (Val := Val) (GF := GF) s) E e Φ := by
  let F : ContractiveHom (WPFun Expr Val GF) (WPFun Expr Val GF) :=
    { f := fun W => wp_pre s W, contractive := inferInstance }
  have h := fixpoint_unfold F
  exact BI.equiv_iff.mp (h E e Φ)

end Iris.ProgramLogic
