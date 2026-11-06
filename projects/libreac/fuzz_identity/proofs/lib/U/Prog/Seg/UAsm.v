From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
Import ListNotations.
Open Scope Z_scope.

Section Seg.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : lib.Reusable.YM05.RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.

Hypothesis sA01 : Hcut B APIf ra (Inv_U12f50 B APIf ra empty) -> Hcut B APIf ra (Inv_U13f4c B APIf ra empty) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Hypothesis sA02 : Hcut B APIf ra (Inv_U12f58 B APIf ra empty) -> Hcut B APIf ra (Inv_U12f50 B APIf ra empty).
Hypothesis sA03 : Hcut B APIf ra (Inv_U12f6c B APIf ra empty) -> Hcut B APIf ra (Inv_U12f58 B APIf ra empty).
Hypothesis sA04 : Hcut B APIf ra (Inv_U12f8c B APIf ra empty) -> Hcut B APIf ra (Inv_U12f6c B APIf ra empty).
Hypothesis sA05 : Hcut B APIf ra (Inv_U12fa4 B APIf ra empty) -> Hcut B APIf ra (Inv_U12f8c B APIf ra empty).
Hypothesis sA06 : Hcut B APIf ra (Inv_U12fc4 B APIf ra empty) -> Hcut B APIf ra (Inv_U12fa4 B APIf ra empty).
Hypothesis sA07 : Hcut B APIf ra (Inv_U12fe4 B APIf ra empty) -> Hcut B APIf ra (Inv_U12fc4 B APIf ra empty).
Hypothesis sA08 : Hcut B APIf ra (Inv_U12ff0 B APIf ra empty) -> Hcut B APIf ra (Inv_U12fe4 B APIf ra empty).
Hypothesis sA09 : Hrec B APIf ra (Inv_U13058_at B APIf ra empty) 0 -> Hcut B APIf ra (Inv_U136ec B APIf ra empty) -> Hcut B APIf ra (Inv_U136f4 B APIf ra empty) -> Hcut B APIf ra (Inv_U12ff0 B APIf ra empty).
Hypothesis sC01 : Hcut B APIf ra (Inv_U136b0 B APIf ra empty) -> Hcut B APIf ra (Inv_U136a0 B APIf ra empty).
Hypothesis sC02 : Hcut B APIf ra (Inv_U13700 B APIf ra empty) -> Hcut B APIf ra (Inv_U136c8 B APIf ra empty) -> Hcut B APIf ra (Inv_U136b0 B APIf ra empty).
Hypothesis sC03 : Hcut B APIf ra (Inv_U13f04 B APIf ra empty) -> Hcut B APIf ra (Inv_U13700 B APIf ra empty) -> Hcut B APIf ra (Inv_U136c8 B APIf ra empty).
Hypothesis sC04 : Hcut B APIf ra (Inv_U136fc B APIf ra empty) -> Hcut B APIf ra (Inv_U136ec B APIf ra empty) /\ Hcut B APIf ra (Inv_U136f4 B APIf ra empty).
Hypothesis sC05 : Hcut B APIf ra (Inv_U13704 B APIf ra empty) -> Hcut B APIf ra (Inv_U136fc B APIf ra empty) /\ Hcut B APIf ra (Inv_U13700 B APIf ra empty) /\ Hcut B APIf ra (Inv_U13f04 B APIf ra empty).
Hypothesis sD01 : Hcut B APIf ra (Inv_U13784 B APIf ra empty) -> Hcut B APIf ra (Inv_U13704 B APIf ra empty).
Hypothesis sE01 : Hcut B APIf ra (Inv_U13794 B APIf ra empty) -> Hcut B APIf ra (Inv_U13784 B APIf ra empty).
Hypothesis sE02 : Hcut B APIf ra (Inv_U137ac B APIf ra empty) -> Hcut B APIf ra (Inv_U13794 B APIf ra empty).
Hypothesis sE03 : Hcut B APIf ra (Inv_U137b8 B APIf ra empty) -> Hcut B APIf ra (Inv_U137ac B APIf ra empty).
Hypothesis sE04 : Hcut B APIf ra (Inv_U137c8 B APIf ra empty) -> Hcut B APIf ra (Inv_U137b8 B APIf ra empty).
Hypothesis sE05 : Hcut B APIf ra (Inv_U137d4 B APIf ra empty) -> Hcut B APIf ra (Inv_U137c8 B APIf ra empty).
Hypothesis sE06 : Hcut B APIf ra (Inv_U137dc B APIf ra empty) -> Hcut B APIf ra (Inv_U137d4 B APIf ra empty).
Hypothesis sE07 : Hcut B APIf ra (Inv_U137e4 B APIf ra empty) -> Hcut B APIf ra (Inv_U137dc B APIf ra empty).
Hypothesis sE08 : Hcut B APIf ra (Inv_U13804 B APIf ra empty) -> Hcut B APIf ra (Inv_U137e4 B APIf ra empty).
Hypothesis sE09 : Hcut B APIf ra (Inv_U13810 B APIf ra empty) -> Hcut B APIf ra (Inv_U13804 B APIf ra empty).
Hypothesis sE10 : Hcut B APIf ra (Inv_U13818 B APIf ra empty) -> Hcut B APIf ra (Inv_U13810 B APIf ra empty).
Hypothesis sF01 : Hcut B APIf ra (Inv_U1384c B APIf ra empty) -> Hcut B APIf ra (Inv_U13818 B APIf ra empty).
Hypothesis sF02 : Hcut B APIf ra (Inv_U1389c B APIf ra empty) -> Hcut B APIf ra (Inv_U1384c B APIf ra empty).
Hypothesis sF03 : Hcut B APIf ra (Inv_U138c8 B APIf ra empty) -> Hcut B APIf ra (Inv_U1389c B APIf ra empty).
Hypothesis sF04 : Hcut B APIf ra (Inv_U138e0 B APIf ra empty) -> Hcut B APIf ra (Inv_U138c8 B APIf ra empty).
Hypothesis sG01 : Hcut B APIf ra (Inv_U138f4 B APIf ra empty) -> Hcut B APIf ra (Inv_U138fc B APIf ra empty) -> Hcut B APIf ra (Inv_U138e0 B APIf ra empty).
Hypothesis sG02 : Hcut B APIf ra (Inv_U13908 B APIf ra empty) -> Hcut B APIf ra (Inv_U138f4 B APIf ra empty) /\ Hcut B APIf ra (Inv_U138fc B APIf ra empty).
Hypothesis sG03 : Hcut B APIf ra (Inv_U13930 B APIf ra empty) -> Hcut B APIf ra (Inv_U13908 B APIf ra empty).
Hypothesis sG04 : Hcut B APIf ra (Inv_U1393c B APIf ra empty) -> Hcut B APIf ra (Inv_U13930 B APIf ra empty).
Hypothesis sG05 : Hcut B APIf ra (Inv_U13948 B APIf ra empty) -> Hcut B APIf ra (Inv_U1393c B APIf ra empty).
Hypothesis sG06 : Hcut B APIf ra (Inv_U13978 B APIf ra empty) -> Hcut B APIf ra (Inv_U13948 B APIf ra empty).
Hypothesis sG07 : Hcut B APIf ra (Inv_U139ac B APIf ra empty) -> Hcut B APIf ra (Inv_U13978 B APIf ra empty).
Hypothesis sH01 : Hcut B APIf ra (Inv_U13a98 B APIf ra empty) -> Hcut B APIf ra (Inv_U13d84 B APIf ra empty) -> Hcut B APIf ra (Inv_U139ac B APIf ra empty).
Hypothesis sH02 : Hcut B APIf ra (Inv_U13aac B APIf ra empty) -> Hcut B APIf ra (Inv_U13a98 B APIf ra empty).
Hypothesis sH03 : Hcut B APIf ra (Inv_U13ae8 B APIf ra empty) -> Hcut B APIf ra (Inv_U13b10 B APIf ra empty) -> Hcut B APIf ra (Inv_U13aac B APIf ra empty).
Hypothesis sH04 : Hcut B APIf ra (Inv_U13b08 B APIf ra empty) -> Hcut B APIf ra (Inv_U13ae8 B APIf ra empty).
Hypothesis sH05 : Hcut B APIf ra (Inv_U13b98 B APIf ra empty) -> Hcut B APIf ra (Inv_U13bf4 B APIf ra empty) -> Hcut B APIf ra (Inv_U13b08 B APIf ra empty) /\ Hcut B APIf ra (Inv_U13b10 B APIf ra empty).
Hypothesis sH06 : Hcut B APIf ra (Inv_U13bc8 B APIf ra empty) -> Hcut B APIf ra (Inv_U13b98 B APIf ra empty).
Hypothesis sH07 : Hcut B APIf ra (Inv_U13be8 B APIf ra empty) -> Hcut B APIf ra (Inv_U13bc8 B APIf ra empty).
Hypothesis sH08 : Hcut B APIf ra (Inv_U13c24 B APIf ra empty) -> Hcut B APIf ra (Inv_U13be8 B APIf ra empty) /\ Hcut B APIf ra (Inv_U13bf0 B APIf ra empty) /\ Hcut B APIf ra (Inv_U13bf4 B APIf ra empty).
Hypothesis sH09 : Hcut B APIf ra (Inv_U13c44 B APIf ra empty) -> Hcut B APIf ra (Inv_U13c24 B APIf ra empty).
Hypothesis sH10 : Hcut B APIf ra (Inv_U13c98 B APIf ra empty) -> Hcut B APIf ra (Inv_U13c44 B APIf ra empty).
Hypothesis sH11 : Hcut B APIf ra (Inv_U13cb0 B APIf ra empty) -> Hcut B APIf ra (Inv_U13c98 B APIf ra empty).
Hypothesis sH12 : Hcut B APIf ra (Inv_U13cd4 B APIf ra empty) -> Hcut B APIf ra (Inv_U13cb0 B APIf ra empty).
Hypothesis sH13 : Hcut B APIf ra (Inv_U13cf0 B APIf ra empty) -> Hcut B APIf ra (Inv_U13cd4 B APIf ra empty).
Hypothesis sH14 : Hcut B APIf ra (Inv_U13d08 B APIf ra empty) -> Hcut B APIf ra (Inv_U13cf0 B APIf ra empty).
Hypothesis sH15 : Hcut B APIf ra (Inv_U13d2c B APIf ra empty) -> Hcut B APIf ra (Inv_U13d08 B APIf ra empty).
Hypothesis sH16 : Hcut B APIf ra (Inv_U13d58 B APIf ra empty) -> Hcut B APIf ra (Inv_U13d74 B APIf ra empty) -> Hcut B APIf ra (Inv_U13d2c B APIf ra empty).
Hypothesis sH17 : Hcut B APIf ra (Inv_U13d84 B APIf ra empty) -> Hcut B APIf ra (Inv_U13d58 B APIf ra empty) /\ Hcut B APIf ra (Inv_U13d74 B APIf ra empty).
Hypothesis sI01 : Hcut B APIf ra (Inv_U13d90 B APIf ra empty) -> Hcut B APIf ra (Inv_U13f34 B APIf ra empty) -> Hcut B APIf ra (Inv_U13d84 B APIf ra empty).
Hypothesis sI02 : Hcut B APIf ra (Inv_U13da0 B APIf ra empty) -> Hcut B APIf ra (Inv_U13d90 B APIf ra empty).
Hypothesis sI03 : Hcut B APIf ra (Inv_U13da8 B APIf ra empty) -> Hcut B APIf ra (Inv_U13da0 B APIf ra empty).
Hypothesis sI04 : Hcut B APIf ra (Inv_U13db8 B APIf ra empty) -> Hcut B APIf ra (Inv_U13da8 B APIf ra empty).
Hypothesis sI05 : Hcut B APIf ra (Inv_U13dc0 B APIf ra empty) -> Hcut B APIf ra (Inv_U13db8 B APIf ra empty).
Hypothesis sI06 : Hcut B APIf ra (Inv_U13dd0 B APIf ra empty) -> Hcut B APIf ra (Inv_U13dc0 B APIf ra empty).
Hypothesis sI07 : Hcut B APIf ra (Inv_U13ddc B APIf ra empty) -> Hcut B APIf ra (Inv_U13dd0 B APIf ra empty).
Hypothesis sI08 : Hcut B APIf ra (Inv_U13dec B APIf ra empty) -> Hcut B APIf ra (Inv_U13ddc B APIf ra empty).
Hypothesis sI09 : Hcut B APIf ra (Inv_U13e08 B APIf ra empty) -> Hcut B APIf ra (Inv_U13dec B APIf ra empty).
Hypothesis sI10 : Hcut B APIf ra (Inv_U13e54 B APIf ra empty) -> Hcut B APIf ra (Inv_U13e08 B APIf ra empty).
Hypothesis sI11 : Hcut B APIf ra (Inv_U13e70 B APIf ra empty) -> Hcut B APIf ra (Inv_U13e54 B APIf ra empty).
Hypothesis sJ01 : Hcut B APIf ra (Inv_U13ebc B APIf ra empty) -> Hcut B APIf ra (Inv_U13e70 B APIf ra empty).
Hypothesis sJ02 : Hcut B APIf ra (Inv_U13ef8 B APIf ra empty) -> Hcut B APIf ra (Inv_U13ee4 B APIf ra empty).
Hypothesis sJ03 : Hcut B APIf ra (Inv_U13f30 B APIf ra empty) -> Hcut B APIf ra (Inv_U13f24 B APIf ra empty) -> Hcut B APIf ra (Inv_U13ebc B APIf ra empty).
Hypothesis sJ04 : Hcut B APIf ra (Inv_U13f30 B APIf ra empty) -> Hcut B APIf ra (Inv_U13ef8 B APIf ra empty) /\ Hcut B APIf ra (Inv_U13efc B APIf ra empty).
Hypothesis sJ05 : Hcut B APIf ra (Inv_U13f3c B APIf ra empty) -> Hcut B APIf ra (Inv_U13f24 B APIf ra empty) /\ Hcut B APIf ra (Inv_U13f30 B APIf ra empty) /\ Hcut B APIf ra (Inv_U13f34 B APIf ra empty).
Hypothesis sJ06 : Hcut B APIf ra (Inv_U13f44 B APIf ra empty) -> Hcut B APIf ra (Inv_U13f3c B APIf ra empty).
Hypothesis sJ07 : Hcut B APIf ra (Inv_U13f4c B APIf ra empty) -> Hcut B APIf ra (Inv_U13f44 B APIf ra empty).
Hypothesis sJ08 : Hcut B APIf ra (Inv_U13f4c B APIf ra empty).
Hypothesis sB00 : Hcut B APIf ra (Inv_U136a0 B APIf ra empty) -> forall i, Hrec B APIf ra (Inv_U13058_at B APIf ra empty) i.
Theorem slot_entry : Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Proof.
  pose proof (sJ08) as q1_0.
  pose proof (sJ07 q1_0) as q2_0.
  pose proof (sJ06 q2_0) as q3_0.
  destruct (sJ05 q3_0) as (q4_0 & q4_1 & q4_2).
  pose proof (sJ03 q4_1 q4_0) as q5_0.
  destruct (sJ04 q4_1) as (q6_0 & q6_1).
  pose proof (sJ01 q5_0) as q7_0.
  pose proof (sJ02 q6_0) as q8_0.
  pose proof (sI11 q7_0) as q9_0.
  pose proof (sI10 q9_0) as q10_0.
  pose proof (sI09 q10_0) as q11_0.
  pose proof (sI08 q11_0) as q12_0.
  pose proof (sI07 q12_0) as q13_0.
  pose proof (sI06 q13_0) as q14_0.
  pose proof (sI05 q14_0) as q15_0.
  pose proof (sI04 q15_0) as q16_0.
  pose proof (sI03 q16_0) as q17_0.
  pose proof (sI02 q17_0) as q18_0.
  pose proof (sI01 q18_0 q4_2) as q19_0.
  destruct (sH17 q19_0) as (q20_0 & q20_1).
  pose proof (sH16 q20_0 q20_1) as q21_0.
  pose proof (sH15 q21_0) as q22_0.
  pose proof (sH14 q22_0) as q23_0.
  pose proof (sH13 q23_0) as q24_0.
  pose proof (sH12 q24_0) as q25_0.
  pose proof (sH11 q25_0) as q26_0.
  pose proof (sH10 q26_0) as q27_0.
  pose proof (sH09 q27_0) as q28_0.
  destruct (sH08 q28_0) as (q29_0 & q29_1 & q29_2).
  pose proof (sH07 q29_0) as q30_0.
  pose proof (sH06 q30_0) as q31_0.
  destruct (sH05 q31_0 q29_2) as (q32_0 & q32_1).
  pose proof (sH04 q32_0) as q33_0.
  pose proof (sH03 q33_0 q32_1) as q34_0.
  pose proof (sH02 q34_0) as q35_0.
  pose proof (sH01 q35_0 q19_0) as q36_0.
  pose proof (sG07 q36_0) as q37_0.
  pose proof (sG06 q37_0) as q38_0.
  pose proof (sG05 q38_0) as q39_0.
  pose proof (sG04 q39_0) as q40_0.
  pose proof (sG03 q40_0) as q41_0.
  destruct (sG02 q41_0) as (q42_0 & q42_1).
  pose proof (sG01 q42_0 q42_1) as q43_0.
  pose proof (sF04 q43_0) as q44_0.
  pose proof (sF03 q44_0) as q45_0.
  pose proof (sF02 q45_0) as q46_0.
  pose proof (sF01 q46_0) as q47_0.
  pose proof (sE10 q47_0) as q48_0.
  pose proof (sE09 q48_0) as q49_0.
  pose proof (sE08 q49_0) as q50_0.
  pose proof (sE07 q50_0) as q51_0.
  pose proof (sE06 q51_0) as q52_0.
  pose proof (sE05 q52_0) as q53_0.
  pose proof (sE04 q53_0) as q54_0.
  pose proof (sE03 q54_0) as q55_0.
  pose proof (sE02 q55_0) as q56_0.
  pose proof (sE01 q56_0) as q57_0.
  pose proof (sD01 q57_0) as q58_0.
  destruct (sC05 q58_0) as (q59_0 & q59_1 & q59_2).
  pose proof (sC03 q59_2 q59_1) as q60_0.
  destruct (sC04 q59_0) as (q61_0 & q61_1).
  pose proof (sC02 q59_1 q60_0) as q62_0.
  pose proof (sC01 q62_0) as q63_0.
  pose proof (sB00 q63_0 0%nat) as q64.
  pose proof (sA09 q64 q61_0 q61_1) as q65_0.
  pose proof (sA08 q65_0) as q66_0.
  pose proof (sA07 q66_0) as q67_0.
  pose proof (sA06 q67_0) as q68_0.
  pose proof (sA05 q68_0) as q69_0.
  pose proof (sA04 q69_0) as q70_0.
  pose proof (sA03 q70_0) as q71_0.
  pose proof (sA02 q71_0) as q72_0.
  pose proof (sA01 q72_0 q1_0) as q73_0.
  exact q73_0.
Qed.

End Seg.
