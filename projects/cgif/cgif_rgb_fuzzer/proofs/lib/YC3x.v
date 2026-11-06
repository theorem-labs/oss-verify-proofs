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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC4o YC4q YC4p YC46 YC4g YC4c YC4d YC4h YC4b YC49.
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
Lemma ra_F_aux : ra_from B ss_P (INV_D B) -> ra_from B ss_I (INV_D B) -> ra_from B ss_F (INV_D B).
Proof.
intros RP RI. ra_prelude.
pose proof HINV as (Hk3 & Eab3 & K1 & EK & HK1r & HK1s).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
reshok_bx HS 40%nat.
fact_of HS 300%nat F300.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RABspan 0x88d70; [awrRA AG fpos F EFA3|]. clear_frames.
frame_pres HJ3 Hfin3 EFA3 F HFpres4 HFSpres4.
fs_rwA HS E70 HFSpres4.
aj_run_to_sh tratbl_lib_ok HS HJ3 0x88dac; [awrRA AG fpos F EFA3|]. clear_frames.
fs_roA HS. relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK RABspan.
all: try (oblFA HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
clear_frames.
set (ics := bv_unsigned (ew E 300)) in F300.
assert (E300 : ew E 300 = Z_to_bv 64 ics) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (Hidl : 4 <= 2 ^ (ics - 1) <= 256).
{ clear - F300. split; [change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia | change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia]. }
Local Ltac joinFI HS R tgt ics E300 F300 Hidl Hk3 Eab3 K1 EK HK1r HK1s :=
let En1 := fresh "En" in let En2 := fresh "En" in let Qt4 := fresh "Qt4" in let Qa6 := fresh "Qa6" in
slot_val HS (Some 2%nat) (-320) (-184) (Z_to_bv 64 ics) ltac:(exact (denot_ics _ 300 ics E300 ltac:(clear - F300; lia))) Qt4;
slot_val HS (Some 2%nat) (-320) (-192) (Z_to_bv 64 (2 ^ (ics - 1))) ltac:(exact (denot_idl _ 300 ics E300 ltac:(clear - F300; lia))) Qa6;
ra_join_slots HS tgt 350%nat ra_deads_FI [(Some 2%nat, -320, -192); (Some 2%nat, -320, -184)]
ltac:(idtac; ra_join_val HS 350%nat 5%nat Qa6 En1; ra_join_val HS 350%nat 6%nat Qt4 En2;
ra_join_fact HS 355%nat (mkAF 4 256 0) ltac:(rewrite En1; rewrite unsigned_lit_small by (clear - Hidl; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Hidl; lia);
ra_join_fact HS 356%nat (mkAF 3 9 0) ltac:(rewrite En2; rewrite unsigned_lit_small by (clear - F300; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - F300; lia));
ra_hand R HS; split; [exact Hk3|]; split; [exact Eab3|]; exists K1;
split; [rewrite ew_havoc_old by (clear; lia); exact EK | split; [exact HK1r | exact HK1s]].
srr_branch_tok tratbl_lib_ok HS SHOK RABspan.
-
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RABspan 0x88e74; [awrRA AG fpos F EFA3|]. clear_frames.
rebaseE HS AG HEv. clear HEv.
joinFI HS RI ss_I ics E300 F300 Hidl Hk3 Eab3 K1 EK HK1r HK1s.
-
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RABspan 0x88e2c; [awrRA AG fpos F EFA3|]. clear_frames.
rebaseE HS AG HEv. clear HEv.
joinFI HS RP ss_P ics E300 F300 Hidl Hk3 Eab3 K1 EK HK1r HK1s.
Qed.
Lemma ra_F : ra_from B ss_P (INV_D B) -> ra_from B ss_I (INV_D B) -> ra_from B ss_F (INV_D B).
Proof. exact ra_F_aux. Qed.
End b.
End a.
