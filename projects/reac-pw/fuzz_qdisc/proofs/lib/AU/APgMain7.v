(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements
   are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc image A (fuzz_qdisc.asan, sha256
   980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e) from
   proofs/libreac/fuzz_knock/lib/A/APgMain7.v (its lemma rt_XP_aux / rt_X, lines 184-237) at
   origin/ossv/recipes 6ebe35ba632, with its module paths changed.
   rule 24 (reuse): no function is proved here; this is SEGMENT S7, the exit block of
   LLVMFuzzerTestOneInput's walk.

   AGAINST KNOCK'S S7. knock's exit repoisons its fake frame's 16 shadow bytes, retires the frame header
   and stores through the frame's flag pointer to free it, so its segment needs aj_run_flag_sh, the
   frame-flag law, astack_free_law and a write-range argument over the frame and its shadow. qdisc owns no
   fake frame (lib/AU/APgRt.v, change Q1): the exit block writes NOTHING, so this segment is one plain run
   and the `ret` leaf, it takes neither ASF nor FFL, and rt_post's block list is S3's unchanged (knock had
   to push it through stack_free_state). *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/QPgMain7.v of this library, for fuzz_qdisc's
   ASan-UBSan image (fuzz_qdisc.asan-ubsan, sha256 eb657d77bd4b27038d93f75626dcc6b37a48be09c889fda664b4f451c6602062),
   LLVMFuzzerTestOneInput at 0x7e694. The framework imports move to the lib/AU twins (AWalkFw0 YCef YF0l YCej YCeh
   YCem YCep AWalkFw1 AWalkFw2 YCfm) and the walk's context and states to lib/AU/APgRt.v / lib/AU/APgLoop0.v; the
   proof is the A file's text.

   THE CODE, 0x7e848-0x7e880 (15 instructions; capstone 5.0.7 over the pinned image):
     0x7e848  mv a0, zero                 the return value
     0x7e84c-0x7e878  12 x `ld` of ra and s0..s10 from 0x58(sp) .. 0(sp)
     0x7e87c  addi sp, sp, 0x60
     0x7e880  ret
   What differs from the A image (0x7e81c-0x7e850, 14 instructions): the block starts at 0x7e848 (ss_X of
   lib/AU/APgLoop0.v) and restores TWELVE words, s10 (x26) from 0(sp) as well, because the asan-ubsan
   prologue saves s10 (0x7e6c4 `sd s10,0(sp)`): the harness keeps its remaining byte count there. So x26 is
   dead at ss_X and comes back from the save area's chunk at sp0 - 96 (APgLoop0.ql_saves), and
   aregs_preserved holds for it the way it does for s0..s9. No call and no store.
   Three edges enter it: 0x7e6d4 `bltu a3,a2` (n = 0, lib/AU/APgMain0.v), 0x7e708 `beqz s4`
   (no budget, APgMain0.v) and 0x7e7c0 `j` (the budgets are spent, lib/AU/APgMain3.v). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm APgRt APgLoop0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
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
