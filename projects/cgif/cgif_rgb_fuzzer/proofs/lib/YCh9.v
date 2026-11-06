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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCgi YChv YChx YChw YCgl YChb YChm YChi YChj YChk YChn.
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
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma ra_Tf_aux : ra_from B ss_X1 (INV_X B) -> ra_from B ss_Tf (INV_Tf B).
Proof.
intros RX. ra_prelude.
pose proof HINV as (Hk3 & _ & HPerm3).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RABspan 0x8a0ac.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_X1 900%nat ra_deads_X ltac:(idtac).
ra_hand RX HS. split; [rewrite HEV; clear - Hk3; lia | exact HPerm3].
Qed.
Lemma ra_Tf : ra_from B ss_X1 (INV_X B) -> ra_from B ss_Tf (INV_Tf B).
Proof. exact ra_Tf_aux. Qed.
Lemma ra_T0_aux : ra_from B ss_G2 (INV_T0 B) -> ra_from B ss_T0 (INV_T0 B).
Proof.
intros RG. ra_prelude.
pose proof HINV as (Hk3 & (K1 & EK & HK1r & HK1s) & (bb & Lbb & M & E600 & E601 & HPerm3 & Hbb4096 & HM & Abb & Tbb)).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _ (YQ0b.mkRegion (Some 2%nat) (-336) (-320) (-336) (-320) []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite (AG 2%nat) by lia; rewrite Usp; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); apply HJpres; rewrite FFS; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawadd, CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 40%nat.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RABspan.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: try (oblFA HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK RABspan.
-
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RABspan.
all: try (oblFA HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK RABspan.
+
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RABspan 0x89ee4.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: try (obl_blk HJ3 E32n E40 Hing3).
all: try (oblFA HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_G2 700%nat ra_deads_G2 ltac:(idtac).
ra_hand RG HS. solve_INV_T0 Hk3 EK HK1r HK1s E600 E601 HPerm3 Hbb4096 HM Abb Tbb.
+
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RABspan 0x89ee4.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: try (obl_blk HJ3 E32n E40 Hing3).
all: try (oblFA HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_G2 700%nat ra_deads_G2 ltac:(idtac).
ra_hand RG HS. solve_INV_T0 Hk3 EK HK1r HK1s E600 E601 HPerm3 Hbb4096 HM Abb Tbb.
-
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RABspan 0x89ee4; [awrRA AG fpos F EFA3|]. clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_G2 700%nat ra_deads_G2 ltac:(idtac).
ra_hand RG HS. solve_INV_T0 Hk3 EK HK1r HK1s E600 E601 HPerm3 Hbb4096 HM Abb Tbb.
Qed.
Lemma ra_T0 : ra_from B ss_G2 (INV_T0 B) -> ra_from B ss_T0 (INV_T0 B).
Proof. exact ra_T0_aux. Qed.
End b.
End a.
