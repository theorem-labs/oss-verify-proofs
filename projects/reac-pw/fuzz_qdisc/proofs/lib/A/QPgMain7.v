(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements
   are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc image A (fuzz_qdisc.asan, sha256
   980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e) from
   proofs/libreac/fuzz_knock/lib/A/APgMain7.v (its lemma rt_XP_aux / rt_X, lines 184-237) at
   origin/ossv/recipes 6ebe35ba632, with its module paths changed (h-small-a3).
   rule 24 (reuse): no function is proved here; this is SEGMENT S7, the exit block of
   LLVMFuzzerTestOneInput's walk.

   THE CODE, 0x7e81c-0x7e850 (14 instructions; capstone 5.0.7 over the pinned image):
     0x7e81c  mv a0, zero                 the return value
     0x7e820-0x7e848  11 x `ld` of ra and s0..s9 from 0x58(sp) .. 8(sp)
     0x7e84c  addi sp, sp, 0x60
     0x7e850  ret
   Three edges enter it: 0x7e6c8 `bltu a3,a2` (n = 0, lib/A/QPgMain0.v), 0x7e6f0 `beqz s4`
   (no budget, QPgMain0.v) and 0x7e7e4 `j` (the budgets are spent, QPgMain3.v).

   AGAINST KNOCK'S S7. knock's exit repoisons its fake frame's 16 shadow bytes, retires the frame header
   and stores through the frame's flag pointer to free it, so its segment needs aj_run_flag_sh, the
   frame-flag law, astack_free_law and a write-range argument over the frame and its shadow. qdisc owns no
   fake frame (lib/A/QPgRt.v, change Q1): the exit block writes NOTHING, so this segment is one plain run
   and the `ret` leaf, it takes neither ASF nor FFL, and rt_post's block list is S3's unchanged (knock had
   to push it through stack_free_state). *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AWalkFw1 AWalkFw2 ACfm QPgRt QPgLoop0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Lemma rt_X : rt_from B MT FP (rt_post B MT FP) ss_X (INV_X B MT).
Proof.
rt_prelude.
pose proof HINV as (Hk3 & Hacc & HPerm3). cbn [c_ly c_S] in HPerm3. cbn [c_T] in Hacc.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
pl_run HS HJ3 AG. clear_frames.
rreg HS (1%bv : bv 5) Rra. rreg HS (10%bv : bv 5) Ra0.
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
intros mat'. unfold rt_post, rt_postP. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_E0 c_T].
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ ?kx =>
lazymatch goal with |- exists ly' S' regs' mem' md' k', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx, kx end end.
split.
{ unfold cfg_at. rewrite Rra. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia.
rewrite (AG 1%nat) by lia. rewrite (EE 1%nat 1%bv eq_refl). rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
rewrite Hra1. unfold raZ in Hra. unfold w64. rewrite <- Hra, Z_to_bv_bv_unsigned. reflexivity. }
split; [cbn [ms_mem]; apply (ajournal_materialize tfibsegs _ LAWS tfib_segs_low); exact HJ3|].
split; [exact Hk3|].
split; [apply aregs_preserved_eqs; creg HS AG EE|].
split; [rewrite Ra0; reflexivity|].
split; [exact HPerm3|].
split; [exact (mo_le_mono MT MTL _ _ _ _ HMLE Hacc)|].
exact I.
Qed.
End c.
End b.
