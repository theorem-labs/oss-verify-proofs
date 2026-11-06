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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC4o YC4q YC4p YC46 YC4g YC4c YC4d YC4h.
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
Local Ltac joinE HS HJ3 SHOK AG fpos F EFA3 RE Hk3 Eab3 K1 EK HK1r HK1s vtac rtac :=
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RABspan 0x88d24; [awrRA AG fpos F EFA3|]; clear_frames;
let Qa2 := fresh "Qa2" in let HEv := fresh "HEv" in let En := fresh "En" in
rreg HS (12%bv : bv 5) Qa2; vtac Qa2;
rebaseE HS AG HEv; clear HEv;
ra_join HS ss_E 250%nat ra_deads_E
ltac:(idtac; ra_join_val HS 250%nat 1%nat Qa2 En;
ra_join_fact HS 251%nat (mkAF 0 256 0) ltac:(rewrite En; rewrite ?unsigned_lit_small by rtac; rewrite Z.pow_0_r, Z.mod_1_r; split; [rtac | split; [reflexivity | clear; lia]]));
ra_hand RE HS; split; [exact Hk3|]; split; [exact Eab3|]; exists K1;
split; [rewrite ew_havoc_old by (clear; lia); exact EK | split; [exact HK1r | exact HK1s]].
Lemma ra_D_aux : ra_from B ss_E (INV_D B) -> ra_from B ss_D (INV_D B).
Proof.
intros RE. ra_prelude.
pose proof HINV as (Hk3 & Eab3 & K1 & EK & HK1r & HK1s).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
reshok_bx HS 40%nat.
fact_of HS 201%nat F201.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK RABspan.
all: try (obl_blk HJ3 E10n E40 Hraw3).
1: awrRA AG fpos F EFA3.
clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RABspan.
-
joinE HS HJ3 SHOK AG fpos F EFA3 RE Hk3 Eab3 K1 EK HK1r HK1s ltac:(fun Q => idtac) ltac:(clear - F201; lia).
- aj_run_tok tratbl_lib_ok HS HJ3 SHOK RABspan; [awrRA AG fpos F EFA3|]. clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RABspan.
+
joinE HS HJ3 SHOK AG fpos F EFA3 RE Hk3 Eab3 K1 EK HK1r HK1s ltac:(fun Q => idtac) ltac:(clear - F201; lia).
+
aj_run_tok tratbl_lib_ok HS HJ3 SHOK RABspan.
all: try (oblFA HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
1: awrRA AG fpos F EFA3.
clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RABspan.
*
joinE HS HJ3 SHOK AG fpos F EFA3 RE Hk3 Eab3 K1 EK HK1r HK1s ltac:(fun Q => idtac) ltac:(clear - F201; lia).
*
joinE HS HJ3 SHOK AG fpos F EFA3 RE Hk3 Eab3 K1 EK HK1r HK1s ltac:(fun Q => rewrite E51, unsigned_lit_small in Q by lia) ltac:(clear - Rtidx; lia).
Qed.
Lemma ra_D : ra_from B ss_E (INV_D B) -> ra_from B ss_D (INV_D B).
Proof. exact ra_D_aux. Qed.
End b.
End a.
