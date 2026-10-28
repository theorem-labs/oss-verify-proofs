(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma rn_st_ok_any : forall E pc sr (regsM : bvmap 5 word) (rs : smem) (G : facts) mem,
regs_ok E sr regsM -> regions_wf rs = true -> Forall (region_ok SEGS E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
st_ok SEGS E (mkSS pc sr rs None G) (mkst regsM (Z_to_bv 64 pc) mem (seg_rom SEGS)).
Proof.
intros E pc sr regsM rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Lemma alu_sll1 : forall i, 0 <= i <= 9 -> alu64 ALU_SLL (Z_to_bv 64 1) (Z_to_bv 64 i) = Z_to_bv 64 (2 ^ i).
Proof.
intros i Hi.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma denot_sll1 : forall E n1 n i, ew E n1 = Z_to_bv 64 1 -> ew E n = Z_to_bv 64 i -> 0 <= i <= 9 ->
sv_denot E (SAlu ALU_SLL (SOff n1 0) (SOff n 0)) = Z_to_bv 64 (2 ^ i).
Proof.
intros E n1 n i H1 Hn Hi. cbn [sv_denot]. rewrite H1, Hn, !unsigned_lit_small, !Z.add_0_r by lia. apply alu_sll1. exact Hi.
Qed.
Lemma aview_wrap : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte, mrestrict.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma aview_kept_nil : forall E H (m m' : word -> option byte),
frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E H m m' HF a. rewrite (aview_wrap H m' a), (aview_wrap H m a).
apply (aview_kept_frame E [] H m m' 0 HF ltac:(lia)); [| apply Z.mod_pos_bound; lia].
intros x Hx (r & Hin & _). exact Hin.
Qed.
Lemma regions_kept_all : forall E H (m m2 : word -> option byte) rs,
(forall a, aview SEGS H m2 a = aview SEGS H m a) -> (forall a, apresent H m a -> apresent H m2 a) ->
Forall (region_kept SEGS E (mrestrict H m) (mrestrict H m2)) rs.
Proof.
intros E H m m2 rs Hav Hpr. apply Forall_forall. intros r _. split; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav.
- apply writable_kept. apply Hpr.
Qed.
Lemma regions_kept_out : forall E H (m m2 : word -> option byte) lo hi rs,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
Forall (fun r => 0 <= base_val E (YP09.r_base r) + YP09.r_lo r /\ base_val E (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val E (YP09.r_base r) + YP09.r_hi r <= lo \/ hi <= base_val E (YP09.r_base r) + YP09.r_lo r)) rs ->
Forall (region_kept SEGS E (mrestrict H m) (mrestrict H m2)) rs.
Proof.
intros E H m m2 lo hi rs Hav Hpr Hrs. apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (H1 & H2 & H3). split; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav; lia.
- apply writable_kept. apply Hpr.
Qed.
Lemma aview_kept_out : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF a Ha Hno. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hno.
Qed.
End c.
End b.
