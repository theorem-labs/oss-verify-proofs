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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC4o YC4q YC46 YC4g YC4c YC4h.
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
Lemma ra_B8_aux : ra_from B ss_C (INV_0 B 1) -> ra_from B ss_X (INV_X B) -> ra_from B ss_B8 (INV_0 B 1).
Proof.
intros RC RX. ra_prelude.
pose proof HINV as (Hk3 & Eab3).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
relow HS AG E10 E32 E10n E32n.
reshok_bx HS 40%nat.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK RABspan; [awrRA AG fpos F EFA3 |].
clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RABspan.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact trasegs Ev _ _ 49 (mkAF 0 256 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E49, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS end.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RABspan 0x88c2c; [awrRA AG fpos F EFA3 |]. clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_C 102%nat (@nil (bv 5)) ltac:(idtac).
ra_hand RC HS. exact HINV.
-
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RABspan 0x89434.
all: try (obl_blk HJ3 E10n E40 Hraw3).
1: awrRA AG fpos F EFA3.
clear_frames.
match type of HS with st_ok _ _ ?ssx _ => idtac "B8-X" ssx end.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_X 930%nat ra_deads_X ltac:(idtac).
ra_hand RX HS. split; [lia | rewrite Eab3; apply Permutation_refl].
Qed.
Lemma ra_B8 : ra_from B ss_C (INV_0 B 1) -> ra_from B ss_X (INV_X B) -> ra_from B ss_B8 (INV_0 B 1).
Proof. exact ra_B8_aux. Qed.
Lemma ra_A2_aux : ra_from B ss_B8 (INV_0 B 1) -> ra_from B ss_X (INV_X B) -> ra_from B ss_A2 (INV_0 B 1).
Proof.
intros RB RX. ra_prelude.
pose proof HINV as (Hk3 & Eab3).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
relow HS AG E10 E32 E10n E32n.
reshok_bx HS 40%nat.
srr_branch_tok tratbl_lib_ok HS SHOK RABspan.
-
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RABspan 0x88c10; [awrRA AG fpos F EFA3 |]. clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_B8 100%nat ([11; 21]%bv : list (bv 5)) ltac:(idtac).
ra_hand RB HS. exact HINV.
- aj_run_tok tratbl_lib_ok HS HJ3 SHOK RABspan; [awrRA AG fpos F EFA3 |]. clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RABspan.
+
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RABspan 0x89434; [awrRA AG fpos F EFA3 |]. clear_frames.
match type of HS with st_ok _ _ ?ssx _ => idtac "A2-X" ssx end.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_X 930%nat ra_deads_X ltac:(idtac).
ra_hand RX HS. split; [lia | rewrite Eab3; apply Permutation_refl].
+ aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RABspan 0x88c10; [awrRA AG fpos F EFA3 |]. clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_B8 100%nat ([11; 21]%bv : list (bv 5)) ltac:(idtac).
ra_hand RB HS. exact HINV.
Qed.
Lemma ra_A2 : ra_from B ss_B8 (INV_0 B 1) -> ra_from B ss_X (INV_X B) -> ra_from B ss_A2 (INV_0 B 1).
Proof. exact ra_A2_aux. Qed.
End b.
End a.
