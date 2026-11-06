(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v, with its module paths and module names changed; 80 of its 105 lines of code are new or changed and 215 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0DigW.v at 97ea9c9eafa (its walk dg_walk);
   re-walked on image B's own code: image B's three runs (lib/AU/HPgE0DigK.v, lib/AU/HPgE0DigR.v), its registers,
   the frame of class 4 and its shadow row in HPgMem's hmu_sh words, and the R-cell R+0xc0 the pointer-overflow
   test reads. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the walk of the DIG block of
   ent_build's case 0 (pod.h:237-246: the decimal text of v = c mod 64 into ch with its NUL, through r[4]) in
   LLVMFuzzerTestOneInput 0x80c40, from DIG 0x81a1c to G 0x81afc, over the journal (no cut state).
   Proves no function (kind: segment lemma).

   HOW. Three runs chained by SRr_bind: run 1 (0x81a1c -> 0x81a30, r into scope: the frame's shadow row becomes
   HPgE0Def.e0_PR), run 2 (0x81a30 -> 0x81af8, the digits, the reverse into ch and its NUL, for the literal v = c mod
   64), run 3 (0x81af8 -> 0x81afc, r out of scope). The post: the journal at the block's start layout and state,
   every register but a0 .. a7 kept, every byte but ch [F+0xa0, F+0xb8), r [F+0xe0, F+0xe4) and r's shadow byte kept,
   ch holding dec64 (c mod 64) and its NUL, r's shadow byte 0xf8 again.
   Registers used: s3 (19) = shadow_addr F, s11 (27) = K, s6 (22) = F+0xe0, s2 (18) = F+0xa0, s8 (24) = HSU_MULT10,
   a3 (13) = c, t0 (5) = 4, t3 (28) = 9, t2 (7) = 10, s7 (23) = -8, s1 (9) = R; the R-cell R+0xc0 = ~&ch. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgMem HPgSeg HPgE0Def HPgE0Base.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgE0DigK HPgE0DigR HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

Lemma dg_walk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k (regs : bvmap 5 word) F pos R c,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
In (4, pos) own -> F = frame_addr lyc 4 pos ->
getr regs 19 = w64 (shadow_addr F) -> getr regs 27 = w64 SHADOW_OFF -> getr regs 22 = w64 (F + 0xe0) ->
getr regs 18 = w64 (F + 0xa0) -> getr regs 24 = w64 HSU_MULT10 -> getr regs 13 = w64 c ->
getr regs 5 = w64 4 -> getr regs 28 = w64 9 -> getr regs 7 = w64 10 -> getr regs 23 = w64 (-8) ->
getr regs 9 = w64 R -> alloc_ceiling + 16384 <= R -> R + 0x220 <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) mem) (R + 0xc0) 8 ((- F - 0xa0 - 1) mod 2 ^ 64) ->
0 <= c < 256 ->
hd_fsh rsegs (w_H W) mem F (hsu_PG headamp_himg_B) ->
SRr rsegs W (cfg_at rsegs E0_DIG regs mem md)
(cb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x81afc regs mem md dg_clob (dg_wr F)
  (fun _ mem2 => hm_bytes rsegs (w_H W) mem2 (F + 0xa0) (dec64 (c mod 64) ++ [NUL]) /\
     aview rsegs (w_H W) mem2 (shadow_addr F + 0x1c) = Some 0xf8)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs F pos R c
  HJ Hown HF H19 H27 H22 H18 H24 H13 H5 H28 H7 H23 H9 HRlo HRhi HKc Hc Hfsh.
destruct (dg_frame B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k F pos HJ Hown HF)
  as (HF32 & HF4096 & HFhi & HFapp & _ & _).
pose proof (dg_frame_ceil B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k F pos HJ Hown HF) as HFc.
pose proof (dg_sh_bounds F HF4096 HFhi) as (SB0 & SB1).
pose proof asan_consts as (C1 & _).
assert (HFR : F + 1024 <= R) by lia.
assert (HshR : shadow_addr F + 128 <= R) by (unfold SHADOW_OFF in *; lia).
rewrite e0_PG_sh in Hfsh.
(* ---- run 1 ---- *)
eapply SRr_bind.
{ unfold cfg_at, w64. exact (dg_run1 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs F pos c HJ Hown HF
    H19 H13 H5 H22 Hc). }
intros W1 c1 _ (-> & r1 & m1 & d1 & -> & HJ1 & Hio1 & Hk1 & Hm1 & Hp1 & R12 & R16 & R11 & R17 & R1sh).
assert (Hfsh1 : hd_fsh rsegs (w_H W) m1 F e0_PR).
{ unfold e0_PR. rewrite <- (hmu_sh_r_in true true false false false true false false).
  apply (hm_fsh_set rsegs (w_H W) mem (w_H W) m1 F _ 28 1 4 Hfsh).
  - intros i Hi. replace i with 0x1c by lia. exact R1sh.
  - intros i Hi Hn. rewrite hmu_sh_len in Hi. apply Hm1; [unfold SHADOW_OFF in *; lia | lia]. }
assert (HKc1 : val_mem rsegs (mrestrict (w_H W) m1) (R + 0xc0) 8 ((- F - 0xa0 - 1) mod 2 ^ 64)).
{ apply (val_mem_kept rsegs (w_H W) (w_H W) mem m1 (R + 0xc0) 8 _); [|exact HKc].
  intros j Hj. apply Hm1; lia. }
(* ---- run 2 ---- *)
eapply SRr_bind.
{ refine (dg_run2 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 d1 k r1 F pos R (c mod 64) HJ1 Hown HF
    _ _ _ _ HFR HRhi HKc1 R12 R11 R17 _ _ _ _ R16 _ Hfsh1).
  - dg_keep Hk1. exact H27.
  - dg_keep Hk1. exact H22.
  - dg_keep Hk1. exact H18.
  - dg_keep Hk1. exact H9.
  - dg_keep Hk1. exact H5.
  - dg_keep Hk1. exact H28.
  - dg_keep Hk1. exact H7.
  - dg_keep Hk1. exact H24.
  - apply Z.mod_pos_bound. lia. }
intros W2 c2 _ (-> & r2 & m2 & d2 & -> & HJ2 & Hio2 & Hk2 & Hm2 & Hp2 & R2ch).
(* ---- run 3 ---- *)
eapply SRr_mono.
{ refine (dg_run3 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m2 d2 k r2 F pos HJ2 Hown HF _ _).
  - rewrite (Hk2 19%bv ltac:(vm_compute; discriminate) ltac:(unfold dg_clob; dg_notin)). dg_keep Hk1. exact H19.
  - rewrite (Hk2 23%bv ltac:(vm_compute; discriminate) ltac:(unfold dg_clob; dg_notin)). dg_keep Hk1. exact H23. }
intros W3 c3 _ (-> & r3 & m3 & d3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hp3 & R3sh).
split; [reflexivity|]. exists r3, m3, d3.
split; [reflexivity|]. split; [exact HJ3|].
split; [eapply same_io_trans; [exact Hio1|]; eapply same_io_trans; [exact Hio2 | exact Hio3]|].
split.
{ intros r Hr0 Hn. unfold dg_clob in Hn. cbn [In] in Hn.
  rewrite (Hk3 r Hr0 ltac:(cbn [In]; tauto)), (Hk2 r Hr0 ltac:(unfold dg_clob; cbn [In]; tauto)),
    (Hk1 r Hr0 ltac:(cbn [In]; tauto)).
  reflexivity. }
split.
{ intros a Ha Hn. unfold dg_wr in Hn.
  rewrite (Hm3 a Ha ltac:(tauto)), (Hm2 a Ha ltac:(tauto)), (Hm1 a Ha ltac:(tauto)). reflexivity. }
split; [intros a Hpa; apply Hp3, Hp2, Hp1, Hpa|].
split; [|exact R3sh].
eapply (hm_bytes_kept rsegs); [exact R2ch|]. intros x Hx.
pose proof (dec64_len (c mod 64)) as Hl. rewrite length_app in Hx. cbn [length] in Hx.
apply Hm3; [unfold DG_FHI in HFhi; lia|].
apply (dg_app_not_sh F 1024 x F HFapp); [lia | exact HF4096 | exact HFhi].
Qed.
End d.
End b.

Print Assumptions dg_walk.
