/-
Copyright (c) 2025 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
import Iris.BI.BigOp.BigOp
import Iris.BI.BigOp.BigSepList
import Iris.BI.BigOp.BigSepMap
import Iris.BI.BigOp.BigSepSet
import Iris.BI.BigOp.BigAndList
import Iris.BI.BigOp.BigAndMap
import Iris.BI.BigOp.BigOrList

/-! # Big Operations for Separation Logic

This file exports all big operation modules for Iris/BI:
- Core definitions (bigSepL, bigAndL, bigOrL, bigSepM, bigAndM, bigSepS)
- Implementation lemmas for lists, maps, and sets
- Lemmas for separating conjunction, conjunction, and disjunction

Import this file to get access to all big operation functionality.
-/
