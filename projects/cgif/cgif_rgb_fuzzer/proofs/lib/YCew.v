(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCfu YCe9.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma rn_st_ok_any : forall E pc sr (regsM : bvmap 5 word) (rs : smem) (G : facts) mem,
regs_ok E sr regsM -> regions_wf rs = true -> Forall (region_ok trbsegs E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
st_ok trbsegs E (mkSS pc sr rs None G) (mkst regsM (Z_to_bv 64 pc) mem (seg_rom trbsegs)).
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
Lemma aview_wrap : forall H (m : word -> option byte) a, aview trbsegs H m a = aview trbsegs H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte, mrestrict.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma aview_kept_nil : forall E H (m m' : word -> option byte),
frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, aview trbsegs H m' a = aview trbsegs H m a.
Proof.
intros E H m m' HF a. rewrite (aview_wrap H m' a), (aview_wrap H m a).
apply (aview_kept_frame E [] H m m' 0 HF ltac:(lia)); [| apply Z.mod_pos_bound; lia].
intros x Hx (r & Hin & _). exact Hin.
Qed.
Lemma regions_kept_all : forall E H (m m2 : word -> option byte) rs,
(forall a, aview trbsegs H m2 a = aview trbsegs H m a) -> (forall a, apresent H m a -> apresent H m2 a) ->
Forall (region_kept trbsegs E (mrestrict H m) (mrestrict H m2)) rs.
Proof.
intros E H m m2 rs Hav Hpr. apply Forall_forall. intros r _. split; intros a Ha.
- apply (mbyte_of_aview trbsegs). apply Hav.
- apply writable_kept. apply Hpr.
Qed.
Lemma regions_kept_out : forall E H (m m2 : word -> option byte) lo hi rs,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview trbsegs H m2 a = aview trbsegs H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
Forall (fun r => 0 <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= lo \/ hi <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r)) rs ->
Forall (region_kept trbsegs E (mrestrict H m) (mrestrict H m2)) rs.
Proof.
intros E H m m2 lo hi rs Hav Hpr Hrs. apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (H1 & H2 & H3). split; intros a Ha.
- apply (mbyte_of_aview trbsegs). apply Hav; lia.
- apply writable_kept. apply Hpr.
Qed.
Lemma aview_kept_out : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview trbsegs H m' a = aview trbsegs H m a.
Proof.
intros E rs H m m' HF a Ha Hno. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hno.
Qed.
End b.
