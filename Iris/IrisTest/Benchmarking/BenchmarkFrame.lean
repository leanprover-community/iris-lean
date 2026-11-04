module

public import Iris
import IrisTest.Benchmarking.Timing

namespace IrisTest.Benchmarking
open Iris BI ProofMode

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

variable {PROP : Type u} [BI PROP] (P : Nat → PROP)

/-! ### Framing: goal in the same order as the premises -/

theorem frame_simple_pat_10 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9⟩
  itime "frame_simple_pat|frame|10" (iframe)

theorem frame_simple_pat_15 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14⟩
  itime "frame_simple_pat|frame|15" (iframe)

theorem frame_simple_pat_20 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19⟩
  itime "frame_simple_pat|frame|20" (iframe)

theorem frame_simple_pat_25 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24⟩
  itime "frame_simple_pat|frame|25" (iframe)

theorem frame_simple_pat_30 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29⟩
  itime "frame_simple_pat|frame|30" (iframe)

theorem frame_simple_pat_40 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29, H30, H31, H32, H33, H34, H35, H36, H37, H38, H39⟩;
  itime "frame_simple_pat|frame|40" (iframe)

theorem frame_simple_pat_60 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59) ⊢ (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29, H30, H31, H32, H33, H34, H35, H36, H37, H38, H39, H40, H41, H42, H43, H44, H45, H46, H47, H48, H49, H50, H51, H52, H53, H54, H55, H56, H57, H58, H59⟩;
  itime "frame_simple_pat|frame|60" (iframe)


/-! ### Framing: goal in the reverse order of the premises -/

theorem frame_reverse_pat_10 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9) ⊢ (P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9⟩
  itime "frame_reverse_pat|frame|10" (iframe)

theorem frame_reverse_pat_15 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14) ⊢ (P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14⟩
  itime "frame_reverse_pat|frame|15" (iframe)

theorem frame_reverse_pat_20 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19) ⊢ (P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19⟩
  itime "frame_reverse_pat|frame|20" (iframe)

theorem frame_reverse_pat_25 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24) ⊢ (P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24⟩
  itime "frame_reverse_pat|frame|25" (iframe)

theorem frame_reverse_pat_30 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29) ⊢ (P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29⟩
  itime "frame_reverse_pat|frame|30" (iframe)

theorem frame_reverse_pat_40 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39) ⊢ (P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29, H30, H31, H32, H33, H34, H35, H36, H37, H38, H39⟩;
  itime "frame_reverse_pat|frame|40" (iframe)

theorem frame_reverse_pat_60 : (P 0 ∗ P 1 ∗ P 2 ∗ P 3 ∗ P 4 ∗ P 5 ∗ P 6 ∗ P 7 ∗ P 8 ∗ P 9 ∗ P 10 ∗ P 11 ∗ P 12 ∗ P 13 ∗ P 14 ∗ P 15 ∗ P 16 ∗ P 17 ∗ P 18 ∗ P 19 ∗ P 20 ∗ P 21 ∗ P 22 ∗ P 23 ∗ P 24 ∗ P 25 ∗ P 26 ∗ P 27 ∗ P 28 ∗ P 29 ∗ P 30 ∗ P 31 ∗ P 32 ∗ P 33 ∗ P 34 ∗ P 35 ∗ P 36 ∗ P 37 ∗ P 38 ∗ P 39 ∗ P 40 ∗ P 41 ∗ P 42 ∗ P 43 ∗ P 44 ∗ P 45 ∗ P 46 ∗ P 47 ∗ P 48 ∗ P 49 ∗ P 50 ∗ P 51 ∗ P 52 ∗ P 53 ∗ P 54 ∗ P 55 ∗ P 56 ∗ P 57 ∗ P 58 ∗ P 59) ⊢ (P 59 ∗ P 58 ∗ P 57 ∗ P 56 ∗ P 55 ∗ P 54 ∗ P 53 ∗ P 52 ∗ P 51 ∗ P 50 ∗ P 49 ∗ P 48 ∗ P 47 ∗ P 46 ∗ P 45 ∗ P 44 ∗ P 43 ∗ P 42 ∗ P 41 ∗ P 40 ∗ P 39 ∗ P 38 ∗ P 37 ∗ P 36 ∗ P 35 ∗ P 34 ∗ P 33 ∗ P 32 ∗ P 31 ∗ P 30 ∗ P 29 ∗ P 28 ∗ P 27 ∗ P 26 ∗ P 25 ∗ P 24 ∗ P 23 ∗ P 22 ∗ P 21 ∗ P 20 ∗ P 19 ∗ P 18 ∗ P 17 ∗ P 16 ∗ P 15 ∗ P 14 ∗ P 13 ∗ P 12 ∗ P 11 ∗ P 10 ∗ P 9 ∗ P 8 ∗ P 7 ∗ P 6 ∗ P 5 ∗ P 4 ∗ P 3 ∗ P 2 ∗ P 1 ∗ P 0) := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29, H30, H31, H32, H33, H34, H35, H36, H37, H38, H39, H40, H41, H42, H43, H44, H45, H46, H47, H48, H49, H50, H51, H52, H53, H54, H55, H56, H57, H58, H59⟩;
  itime "frame_reverse_pat|frame|60" (iframe)

end IrisTest.Benchmarking
