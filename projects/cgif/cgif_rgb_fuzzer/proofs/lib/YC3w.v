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
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC4o YC4q YC4p YC46 YC4g YC4c YC4d YC4h YC49.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Local Ltac joinF HS HJ3 SHOK AG fpos F EFA3 RF' Hk3 Eab3 K1 EK HK1r HK1s vtac rtac :=
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RABspan 0x88d58; [awrRA AG fpos F EFA3|]; clear_frames;
let Qa0 := fresh "Qa0" in let HEv := fresh "HEv" in let En := fresh "En" in
rreg HS (10%bv : bv 5) Qa0; vtac Qa0;
rebaseE HS AG HEv; clear HEv;
ra_join HS ss_F 300%nat ra_deads_F
ltac:(idtac; ra_join_val HS 300%nat 0%nat Qa0 En;
ra_join_fact HS 300%nat (mkAF 3 9 0) ltac:(rewrite En; rewrite ?unsigned_lit_small by rtac; rewrite Z.pow_0_r, Z.mod_1_r; split; [rtac | split; [reflexivity | clear; lia]]));
ra_hand RF' HS; split; [exact Hk3|]; split; [exact Eab3|]; exists K1;
split; [rewrite ew_havoc_old by (clear; lia); exact EK | split; [exact HK1r | exact HK1s]].
Lemma ra_E_aux : ra_from B ss_F (INV_D B) -> ra_from B ss_E (INV_D B).
Proof.
intros RF'. ra_prelude.
pose proof HINV as (Hk3 & Eab3 & K1 & EK & HK1r & HK1s).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
reshok_bx HS 40%nat.
fact_of HS 251%nat F251.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RABspan 0x88d38; [awrRA AG fpos F EFA3|]. clear_frames.
rreg HS (10%bv : bv 5) Ra0. rreg HS (13%bv : bv 5) Ra3. rreg HS (12%bv : bv 5) Ra2.
rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 251)) in Ra2.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (ra_pow2b B LAWS 9 0 (bv_unsigned (ew E 251)) W3 (ms_regs msX) (ms_mem msX) _ TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)] ly3 S3 k eq_refl HJ3);
[ exact Ra0 | exact Ra3 | exact Ra2 | clear; lia | clear - F251; lia | right; reflexivity ] end. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & K & -> & HJ5 & HK14 & HK10 & HK15 & HKlo & HKs1 & HKs2 & Hav5 & Hpr5 & Hrg5).
clear Ra0 Ra3 Ra2.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch HS kk regs5 (mrestrict (w_H W3) mem5) POW_CLOB_C 0x88d48 HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5));
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS; rebaseE HS AG HEv;
let kk1 := eval vm_compute in (kk + 1)%nat in
lazymatch type of HS with st_ok _ ?Ev2 _ _ =>
assert (EK0 : ew Ev2 kk = Z_to_bv 64 (K + 1)) by (rewrite HEv; unfold POW_CLOB_C; cbn [map]; rewrite (ew_havoc_new _ kk _ 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK10);
assert (EKK : ew Ev2 kk1 = Z_to_bv 64 K) by (rewrite HEv; unfold POW_CLOB_C; cbn [map]; change kk1 with (kk + 1)%nat; rewrite Nat.add_1_r;
rewrite (ew_havoc_new _ kk _ 1 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK14) end;
clear HEv end.
norm_ss HS. relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
aj_run_tok tratbl_lib_ok HS HJ5 SHOK RABspan; [awrRA AG fpos F EFA3|]. clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RABspan.
-
unfold branch_taken in Hc.
match type of HS with st_ok _ ?Ev _ _ => rewrite (denot_and255 Ev _ K EKK ltac:(clear - HKlo; lia)) in Hc end.
cbn [sv_denot] in Hc. rewrite bv_ltu_unsigned, !unsigned_lit_small in Hc by (clear - HKlo; lia).
apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc.
joinF HS HJ5 SHOK AG fpos F EFA3 RF' Hk3 Eab3 K1 EK HK1r HK1s ltac:(fun Q => rewrite EK0 in Q) ltac:(clear - HKlo Hc; lia).
-
joinF HS HJ5 SHOK AG fpos F EFA3 RF' Hk3 Eab3 K1 EK HK1r HK1s ltac:(fun Q => idtac) ltac:(clear; lia).
Qed.
Lemma ra_E : ra_from B ss_F (INV_D B) -> ra_from B ss_E (INV_D B).
Proof. exact ra_E_aux. Qed.
End b.
End a.
