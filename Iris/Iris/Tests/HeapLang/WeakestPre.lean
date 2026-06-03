module

public import Iris.BI
public import Iris.Instances
public import Iris.HeapLang.Notation
public import Iris.HeapLang.ProofMode
public import Iris.HeapLang.Instances
public import Iris.ProgramLogic.WeakestPre

namespace Iris.HeapLang

variable {hlc} {GF : BundledGFunctors} [ι : IrisGS_gen hlc HeapLang.Exp GF]
set_option linter.unusedVariables false

namespace wp_bind

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl(((#0 + #1) + #2)) {{ v, WP hl(({↑v} + #3)) {{ v, True }} }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(((#0 + #1) + #2) + #3) {{ v, True }} := by
  wp_bind ((#0 + _) + _)

/-- error: Couldn't unify hl((#2 + {?m.28})) with any possible evaluation context -/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(((#0 + #1) + #2) + #3) {{ v, True }} := by
  wp_bind (#2 + _)

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl(((#0 + #1) + #2)) {{ v, WP hl(({↑v} + #3)) {{ v, True }} }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(((#0 + #1) + #2) + #3) {{ v, True }} := by
  wp_bind (_ + #2)

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl((#0 + #1)) {{ v, WP hl((({↑v} + #2) + #3)) {{ v, True }} }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(((#0 + #1) + #2) + #3) {{ v, True }} := by
  wp_bind (#0 + #1)

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl((#2 + (#1 + #2))) {{ v, WP ↑v {{ v, True }} }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(#2 + (#1 + #2)) {{ v, True }} := by
  wp_bind (#2 + _)


/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl((#1 + #2)) {{ v, WP hl((#2 + {↑v})) {{ v, True }} }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(#2 + (#1 + #2)) {{ v, True }} := by
  wp_bind (_ + #2)

end wp_bind


/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl(#0) {{ v, True }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(if #false then #1 else #0) {{ v, True }} := by
  istart
  wp_pure

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP hl(#1) {{ v, True }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(if #true then #1 else #0) {{ v, True }} := by
  istart
  wp_pure

/--
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
ι : IrisGS_gen hlc Exp GF
⊢ ⏎
  ⊢ WP ↑hl_val(#2) {{ v, True }}
-/
#guard_msgs in
example : ⊢@{IProp GF}  WP hl(snd(v((#1,#2)))) {{ v, True }} := by
  istart
  wp_pure
