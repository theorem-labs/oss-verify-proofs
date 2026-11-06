(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the two piece lemmas of the builder piece W6a of LLVMFuzzerTestOneInput (0x80c40), as lib/AU/HPgSeg.v
   states them, at image B's own record headamp_himg_B and builder pcs headamp_bld_B.

     w6b_piece_disp   hsu_piece_W6a_disp_stmt: the pod loop's head C 0x81888 through ent_build's dispatch, to every
                      switch entry hsu_pc_D kd and to D0E 0x819c0;
     w6b_piece_cases  hsu_piece_W6a_cases_stmt: ent_build's cases 2 and 3 (kd mod 10 in [2; 3]) from their switch
                      entries 0x81cbc / 0x81d34 to the join J 0x82618.

   Each is the chaining lemma of lib/AU/HPgW6a.v (w6b_disp_of, w6b_cases_of) applied to the block lemmas, one file
   per block: lib/AU/HPgW6aHead.v (w6b_head), HPgW6aKind.v (w6b_kind), HPgW6aC2.v (w6b_c2), HPgW6aC3.v (w6b_c3),
   HPgW6aTail.v (w6b_tail2u, w6b_tail2, w6b_tail3u, w6b_tail3); the fuzz_u32 read-ahead blocks and the jump table
   are lib/AU/HPgSteps.v's.

   The open Section hypotheses are the kernel's meter laws MTL and AMEMSET, the contract of __asan_memset at image
   B's entry 0x52228 (lib/Reusable/YG0d.v aintrin_realizes OSet), which the head block's call takes. The cases piece
   calls nothing and needs only MTL. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgSeg HPgCaseB.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import
HPgW6aBase HPgW6aHead HPgW6aKind HPgW6aC2 HPgW6aC3 HPgW6aTail HPgW6a.
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
(* __asan_memset at image B's entry 0x52228: the kernel's contract of the intrinsic, called by the head block *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6B_MEMSET.

Theorem w6b_piece_disp : hsu_piece_W6a_disp_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof using MTL AMEMSET.
assert (HH : w6b_head_stmt B MT) by (exact (w6b_head B MT MTL AMEMSET)).
assert (HK : w6b_kind_stmt B MT) by (first [exact (w6b_kind B MT MTL) | exact (w6b_kind B MT)]).
eapply w6b_disp_of; eassumption.
Qed.

Theorem w6b_piece_cases : hsu_piece_W6a_cases_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof using MTL.
assert (H2 : w6b_c2_stmt B MT) by (first [exact (w6b_c2 B MT MTL) | exact (w6b_c2 B MT)]).
assert (H3 : w6b_c3_stmt B MT) by (first [exact (w6b_c3 B MT MTL) | exact (w6b_c3 B MT)]).
assert (T2u : w6b_tail2u_stmt B MT) by (first [exact (w6b_tail2u B MT MTL) | exact (w6b_tail2u B MT)]).
assert (T2 : w6b_tail2_stmt B MT) by (first [exact (w6b_tail2 B MT MTL) | exact (w6b_tail2 B MT)]).
assert (T3u : w6b_tail3u_stmt B MT) by (first [exact (w6b_tail3u B MT MTL) | exact (w6b_tail3u B MT)]).
assert (T3 : w6b_tail3_stmt B MT) by (first [exact (w6b_tail3 B MT MTL) | exact (w6b_tail3 B MT)]).
eapply w6b_cases_of; eassumption.
Qed.

End d.
End b.

Check w6b_piece_disp.
Check w6b_piece_cases.
Print Assumptions w6b_piece_disp.
Print Assumptions w6b_piece_cases.
