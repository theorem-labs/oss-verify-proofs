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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx
YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCjo YI0g YP14 YI0c YP16 YI0f YI09 YM02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Export YCqj.
Lemma cx_cond_cnt_nz : forall E n cnt, ew E n = Z_to_bv 64 cnt -> 1 <= cnt < 2 ^ 31 ->
branch_taken BC_NE (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit 0)) = true.
Proof.
intros E n cnt Hn Hc. rewrite branch_ne_U, (U_sext32_small E n cnt Hn) by lia. change (U E (SLit 0)) with 0.
apply Bool.negb_true_iff, Z.eqb_neq. lia.
Qed.
Lemma cx_cond_cnt_gt : forall E n cnt, ew E n = Z_to_bv 64 cnt -> 256 <= cnt < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SLit 255)) (sv_denot E (SOff n 0)) = true.
Proof.
intros E n cnt Hn Hc. rewrite YO3v.branch_ltu_U, (U_atom E n cnt Hn) by lia. change (U E (SLit 255)) with 255. apply Z.ltb_lt. lia.
Qed.
Lemma cx_cond_N_nz : forall E nh nw H W, ew E nh = Z_to_bv 64 H -> ew E nw = Z_to_bv 64 W -> 0 <= H < 2 ^ 16 -> 0 <= W < 2 ^ 16 -> 1 <= H * W < 2 ^ 31 ->
branch_taken BC_NE (sv_denot E (SMdw M_MUL (SOff nh 0) (SOff nw 0))) (sv_denot E (SLit 0)) = true.
Proof.
intros E nh nw H W Hh Hw RH RW RHW. rewrite branch_ne_U, (U_HW E nh nw H W Hh Hw RH RW) by lia. change (U E (SLit 0)) with 0.
apply Bool.negb_true_iff, Z.eqb_neq. lia.
Qed.
Lemma cx_cond_fmt : forall E n fmt, ew E n = Z_to_bv 64 fmt -> fmt = 3 \/ fmt = 4 ->
branch_taken BC_GEU (sv_denot E (SLit 1)) (sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff n 0)) (SLit (-3)))) = true.
Proof.
intros E n fmt Hn Hf. rewrite branch_geu_U. apply Bool.negb_true_iff, Z.ltb_ge.
rewrite U_lit by lia. rewrite U_SAluw. cbn [zalu_raw]. rewrite (U_sext32_low E n fmt Hn) by lia. rewrite U_SLit.
destruct Hf as [-> | ->]; vm_compute; discriminate.
Qed.
Lemma c_means_ok_of_facts : forall (t : tnode) (nd : anode (A := entry)) E lo hi,
ent_ok E -> 0 <= lo -> hi < elen E -> n_seg nd = zsub E lo hi -> length (tn_mean t) = 3%nat ->
tn_facts t nd -> tnode_means_ok t.
Proof.
intros t nd E lo hi HE Hlo Hhi Hseg Hlen [TF _]. rewrite Hseg in TF. unfold tnode_means_ok.
assert (M : forall d, 0 <= d <= 2 -> mean_ok (nth (Z.to_nat d) (tn_mean t) 0)).
{ intros d Hd. exists (wdot (dseg d E lo hi)), (wsum (dseg d E lo hi)). split; [exact (TF d Hd)|].
pose proof (wdot_bounds _ (dseg_node_ok d E lo hi HE Hlo Hhi)). lia. }
destruct (tn_mean t) as [|m0 [|m1 [|m2 [|]]]]; try discriminate Hlen.
constructor; [exact (M 0 ltac:(lia))|]. constructor; [exact (M 1 ltac:(lia))|]. constructor; [exact (M 2 ltac:(lia)) | constructor].
Qed.
