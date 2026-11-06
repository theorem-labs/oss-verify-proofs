(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the walk piece W6c of LLVMFuzzerTestOneInput
   (0x80c40) closed: lib/AU/HPgSeg.v's hsu_piece_W6c_stmt at segs = Img0U.rsegs, I = headamp_himg_B,
   BI = headamp_bld_B, ent_build's cases 6, 7 and 8 from their switch entries (0x81f08, 0x81d88, 0x81f5c) to the join
   J 0x82618. Proves no function (kind: segment lemma).

   The piece is HPgW6c.hsu_piece_W6c_of_cases over the three case statements; each case is its head
   (HPgW6cH6.w6c_head6, HPgW6cH7.w6c_head7, HPgW6cH8.w6c_head8) chained with its tail (HPgW6cTake.w6c_take for cases 6
   and 7, HPgW6cFill.w6c_fill for case 8) by HPgW6cCase.w6c_case_of_headT / w6c_case_of_headF; the step at each memory
   intrinsic is HPgCaseB.cb_intrin_at (HPgW6c.w6c_intrin).
   OPEN SECTION HYPOTHESES, as in every walk lane that calls them: MTL (the meter's laws), AMEMCPY (image B's
   __asan_memcpy realizes OCpy at 0x51d8c, the `jal` target at 0x82474) and AMEMSET (__asan_memset realizes OSet at
   0x52228, the `jal` target at 0x822c0); the unit's top theorem carries them. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSteps HPgCaseB
  HPgCaseBJ HPgW6cEng HPgW6cCase HPgW6c HPgW6cH6 HPgW6cH7 HPgW6cH8.
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6C_CPY.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6C_SET.

Theorem hsu_piece_W6c : hsu_piece_W6c_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof using MTL AMEMCPY AMEMSET.
apply (hsu_piece_W6c_of_cases B MT MTL).
- exact (w6c_case_of_headT B MT MTL (w6c_intrin B) AMEMCPY 6 W6C_T6 (or_introl (conj eq_refl eq_refl))
    (w6c_head6 B MT MTL)).
- exact (w6c_case_of_headT B MT MTL (w6c_intrin B) AMEMCPY 7 W6C_T7 (or_intror (conj eq_refl eq_refl))
    (w6c_head7 B MT MTL)).
- exact (w6c_case_of_headF B MT MTL (w6c_intrin B) AMEMSET (w6c_head8 B MT MTL)).
Qed.
End b.

Print Assumptions hsu_piece_W6c.
