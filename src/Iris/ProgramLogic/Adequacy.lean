/-
Copyright (c) 2026 Sam Hart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Hart
-/
import Iris.ProgramLogic.Adequacy.ThreadPool
import Iris.ProgramLogic.Adequacy.WptpHelpersA
import Iris.ProgramLogic.Adequacy.WptpHelpersB
import Iris.ProgramLogic.Adequacy.WptpHelpersC
import Iris.ProgramLogic.Adequacy.FUpd
import Iris.ProgramLogic.Adequacy.WpStep
import Iris.ProgramLogic.Adequacy.WptpStep
import Iris.ProgramLogic.Adequacy.Preservation
import Iris.ProgramLogic.Adequacy.Adequate
import Iris.ProgramLogic.Adequacy.StrongAdequacy
import Iris.ProgramLogic.Adequacy.SimplifiedAdequacy
import Iris.ProgramLogic.Adequacy.Invariance

/-! # Adequacy

Reference: `iris/program_logic/adequacy.v`

This file re-exports the adequacy development, which is split across
smaller submodules to keep each file within the project size limits.
-/
