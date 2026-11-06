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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20 YI1k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC1z YC1y YC27 YC23 YC28 YC1w YC24.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac hc_atom H n v En rtac :=
lazymatch type of H with context [U ?E' (SOff n 0)] =>
rewrite (U_atom E' n v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En)) in H by rtac end.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma fl_R1_aux : fl_from B ss_R2 (INV_R2 B) -> fl_from B ss_R (INV_R B).
Proof.
intros RR2. fl_prelude.
pose proof HINV as ((gen & E180 & Rgen) & E184 & (pt & w & h & top & left & tidx & E402 & E403 & E404 & E400 & E405 & E401 & Hrpt & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & Htidx & Hpt)).
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)).
{ intros x Hx. destruct Hpt as [(_ & _ & Eab3) | (_ & _ & (_ & _ & _ & Eab3 & _))]; rewrite Eab3; [exact Hx | apply in_app_iff; left; exact Hx]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan.
-
hc_bool Hc ltac:(fun H => hc_atom H 402%nat pt E402 ltac:(clear - Hrpt; lia)).
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x87928.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
rreg HS (23%bv : bv 5) Q23;
add_atom HS 450%nat (sv_denot Ev (SOff 402 0)) E450;
rechunk_off HS 75%nat 40 (SOff 450 0) ltac:(rewrite sv_denot_SOff0, E450; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join HS ss_R2 451%nat fl_R2_deads_bv ltac:(idtac; ra_join_val HS 451%nat 0%nat Q23 E451);
fl_hand RR2 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
exists pt, w, h, top, left, tidx, (pt). cbn [c_s c_f c_ly c_S].
split; [rewrite E451; exact E402|].
split; [rewrite !ew_havoc_old by (clear; lia); exact E403|].
split; [rewrite !ew_havoc_old by (clear; lia); exact E404|].
split; [rewrite !ew_havoc_old by (clear; lia); exact E400|].
split; [rewrite !ew_havoc_old by (clear; lia); exact E405|].
split; [rewrite !ew_havoc_old by (clear; lia); exact E401|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E450, sv_denot_SOff0; exact E402|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|]. split; [exact Htidx|].
right. hc_prop Hc. destruct Hpt as [(Hp0 & _) | (Hp1 & Hk2 & Htb)]; [exfalso; exact (Hc Hp0)|].
split; [exact Hp1|]. split; [reflexivity|]. split; [exact Hk2 | exact Htb].
-
hc_bool Hc ltac:(fun H => hc_atom H 402%nat pt E402 ltac:(clear - Hrpt; lia)).
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x87928.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
rreg HS (23%bv : bv 5) Q23;
add_atom HS 450%nat (sv_denot Ev (SOff 51 0)) E450;
rechunk_off HS 75%nat 40 (SOff 450 0) ltac:(rewrite sv_denot_SOff0, E450; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join HS ss_R2 451%nat fl_R2_deads_bv ltac:(idtac; ra_join_val HS 451%nat 0%nat Q23 E451);
fl_hand RR2 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
exists pt, w, h, top, left, tidx, (fr_img f). cbn [c_s c_f c_ly c_S].
split; [rewrite E451; hc_prop Hc; rewrite Hc; reflexivity|].
split; [rewrite !ew_havoc_old by (clear; lia); exact E403|].
split; [rewrite !ew_havoc_old by (clear; lia); exact E404|].
split; [rewrite !ew_havoc_old by (clear; lia); exact E400|].
split; [rewrite !ew_havoc_old by (clear; lia); exact E405|].
split; [rewrite !ew_havoc_old by (clear; lia); exact E401|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E450, sv_denot_SOff0; exact E51|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|]. split; [exact Htidx|].
left. hc_prop Hc. destruct Hpt as [(Hp0 & Hk0 & Eab3) | (Hp1 & _)]; [|exfalso; exact (Hp1 Hc)].
split; [exact Hc|]. split; [reflexivity|]. split; [exact Hk0 | exact Eab3].
Qed.
Lemma fl_R1 : fl_from B ss_R2 (INV_R2 B) -> fl_from B ss_R (INV_R B).
Proof. exact fl_R1_aux. Qed.
End b.
End a.
