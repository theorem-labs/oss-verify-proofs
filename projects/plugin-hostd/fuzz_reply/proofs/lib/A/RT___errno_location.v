(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contract aerrno_realizes (lib/A/W_sites.v) proved for
   fuzz_reply.asan's musl __errno_location at 0x8c9a8. *)
(* The code is `mv a0,tp ; addi a0,a0,-164 ; ret` (fuzz_reply.asan 0x8c9a8, the same 12 bytes as the plain build's
   lib/Prog/__errno_location.v).  It reads and writes no memory, so the proof steps the three instructions
   concretely (SRr_msteps), and the allocator state is carried over the materialised model by AR_laws's frame law.
   The theorem is in the donor's corollary shape (proofs/cgif/cgif_file_fuzzer/lib/A/AF0s.v:514): it holds for every
   asyms B whose AR obeys AR_laws, at the placement PB_fr (lib/A/W_img.v), whose pa_segs is frsegs. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_tbl W_place W_kit W_img W_journal W_contract W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* Build identity: this is fuzz_reply.asan (ofl_head 0x5f9b68 is the ASan sink head AE2k.tfib_sink_head carries;
   main and LLVMFuzzerTestOneInput begin with their frame allocations at 0x81e4c and 0x840b0), and the entry the
   walks call as WS_errno_location is 0x8c9a8. *)
Lemma rt_errno_build_id :
  AE2k.A_ofl_head = 0x5f9b68 /\ @YI16.sk_ofl_head AE2k.tfib_sink_head = 0x5f9b68 /\
  fr_sigma WS_errno_location = 0x8c9a8 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x81e4c)) = Some 0xfb010113 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x840b0)) = Some 0xec010113.
Proof. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; vm_compute; reflexivity. Qed.

(* The code table of __errno_location's three words, decided against the image. *)
Definition errno_tbl : ctable := Eval vm_compute in build_table frsegs 0x8c9a8 3 TEmpty.
Lemma errno_tbl_eq : errno_tbl = build_table frsegs 0x8c9a8 3 TEmpty.
Proof. vm_cast_no_check (eq_refl errno_tbl). Qed.
Lemma errno_tbl_ok : table_ok frsegs errno_tbl.
Proof. rewrite errno_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
Lemma errno_fetch : forall (p : word) (w : bv 32), clookup errno_tbl (bv_unsigned p) = Some (bv_unsigned w) ->
fetch_word frsegs p = Some w.
Proof. intros p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w). apply errno_tbl_ok. exact H. Qed.
Lemma errno_F0 : fetch_word frsegs (w64 0x8c9a8) = Some (0x00020513%bv : bv 32).
Proof. apply errno_fetch. vm_compute. reflexivity. Qed.
Lemma errno_F1 : fetch_word frsegs (v_addi (w64 0x8c9a8) 4) = Some (0xf5c50513%bv : bv 32).
Proof. apply errno_fetch. vm_compute. reflexivity. Qed.
Lemma errno_F2 : fetch_word frsegs (v_addi (v_addi (w64 0x8c9a8) 4) 4) = Some (0x00008067%bv : bv 32).
Proof. apply errno_fetch. vm_compute. reflexivity. Qed.
Lemma errno_D0 : decode_any (0x00020513%bv : bv 32) = Some (OpImm ALU_ADD (10%bv : bv 5) (4%bv : bv 5) (0%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma errno_D1 : decode_any (0xf5c50513%bv : bv 32) = Some (OpImm ALU_ADD (10%bv : bv 5) (10%bv : bv 5) (3932%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma errno_D2 : decode_any (0x00008067%bv : bv 32) = Some (Jalr (0%bv : bv 5) (1%bv : bv 5) (0%bv : bv 12), 4%Z).
Proof. vm_refl_bv. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The value the two addi leave in a0: tp - 164, as a word. *)
Lemma errno_value : forall t : word, v_addi (v_addi t (bv_signed (0%bv : bv 12))) (bv_signed (3932%bv : bv 12)) =
w64 (bv_unsigned t - 164).
Proof.
intros t. change (bv_signed (0%bv : bv 12)) with 0. change (bv_signed (3932%bv : bv 12)) with (-164).
unfold v_addi, w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.add_0_r. pose proof (bv_unsigned_in_range _ t) as Ht. unfold bv_modulus in Ht.
rewrite (Z.mod_small (bv_unsigned t)) by (change (2 ^ Z.of_N 64) with (2 ^ 64) in Ht; lia). reflexivity.
Qed.

Theorem rt___errno_location : forall B, AR_laws frsegs B ->
aerrno_realizes (PI := PB_fr) B (fr_sigma WS_errno_location).
Proof.
intros B LAWS ly S W regs mem md HPRE.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
unfold cfg_at.
eapply (SRr_msteps frsegs fr_wx W).
{ rewrite restrict_mkst_fx.
  eapply mst_step; [reflexivity | exact (step_addi frsegs _ _ _ _ _ _ _ _ errno_F0 eq_refl errno_D0) |].
  eapply mst_step; [reflexivity | exact (step_addi frsegs _ _ _ _ _ _ _ _ errno_F1 eq_refl errno_D1) |].
  eapply mst_step; [reflexivity | exact (step_jalr_x0 frsegs _ _ _ _ _ _ _ _ errno_F2 eq_refl errno_D2 eq_refl) |].
  apply mst_refl. }
intros md' Hsame _.
rewrite unrestrict_mkst_mrestrict.
pose (r1 := regupd regs (10%bv : bv 5) (v_addi (getr regs (4%bv : bv 5)) (bv_signed (0%bv : bv 12)))).
pose (r2 := regupd r1 (10%bv : bv 5) (v_addi (getr r1 (10%bv : bv 5)) (bv_signed (3932%bv : bv 12)))).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r ?p ?m ?rom) ?d) _ =>
  change (mkst r p m rom) with (mkst r2 (v_jalr (getr r2 (1%bv : bv 5)) (bv_signed (0%bv : bv 12))) m rom) end.
assert (K : forall r : bv 5, r <> (10%bv : bv 5) -> getr r2 r = getr regs r).
{ intros r Hr. unfold r2, r1. rewrite !getr_other by exact Hr. reflexivity. }
assert (R10 : getr r2 (10%bv : bv 5) = w64 (as_tp B - 164)).
{ unfold r2. rewrite getr_same by discriminate. unfold r1. rewrite getr_same by discriminate.
  rewrite errno_value, Htp. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zminus_mod_idemp_l. reflexivity. }
assert (RA : v_jalr (getr r2 (1%bv : bv 5)) (bv_signed (0%bv : bv 12)) = w64 (raZ regs)).
{ rewrite (K (1%bv : bv 5)) by discriminate. change (bv_signed (0%bv : bv 12)) with 0. rewrite Hra.
  unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
rewrite RA.
apply SRr_ret. unfold aentry_post.
split; [reflexivity|]. exists r2, mem, md'.
split; [reflexivity|].
split.
{ pose proof (same_but_materialized_frame md md' Hsame) as MF.
  apply (al_frame _ _ LAWS ly S W mem md mem md' HAR).
  - intros a _ _. reflexivity.
  - intros a Ha. exact Ha.
  - apply MF.
  - apply MF.
  - apply MF.
  - intros a _ _. reflexivity. }
split.
{ intros r Hr. apply K. intros E. unfold acallee_saved in Hr.
  assert (U : bv_unsigned (Z_to_bv 5 r) = 10) by (rewrite E; reflexivity).
  rewrite Z_to_bv_unsigned in U. unfold bv_wrap in U. change (bv_modulus 5) with 32 in U.
  rewrite Z.mod_small in U by lia. lia. }
split; [exact Hsame|].
split; [exact R10|].
split; [intros a _ _ _; reflexivity|].
intros a Ha. exact Ha.
Qed.

End a.
