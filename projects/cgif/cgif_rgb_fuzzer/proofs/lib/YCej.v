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
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20 YI1k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCgl YCfu YCft YCrb YCez YCev YCf6 YCf2 YCf7 YCet YCf3 YCey YCf5.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
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
Lemma fl_R3_aux : fl_from B ss_R4 (INV_R4 B) -> fl_from B ss_R3 (INV_R3 B).
Proof.
intros RR4. fl_prelude.
pose proof HINV as ((gen & E180 & Rgen) & E184 & (attr & E460 & Hattr) & (pt & w & h & top & left & tidx & img & E451 & E403 & E404 & E400 & E405 & E401 & E450 & Hrpt & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & Htidx & Hpt)).
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)).
{ intros x Hx. destruct Hpt as [(_ & _ & _ & Eab3) | (_ & _ & _ & (_ & _ & _ & Eab3 & _))]; rewrite Eab3; [exact Hx | apply in_app_iff; left; exact Hx]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
-
hc_bool Hc ltac:(fun H => hc_atom H 52%nat (fr_attr f) E52 ltac:(clear - Q2; lia)).
rebase_goal.
lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict ?Hw ?msx) |- _ =>
pose proof (reg_and1_zero Hw Ev ssx msx (10%bv : bv 5) 52 (fr_attr f) HS ltac:(vm_compute; reflexivity) E52 ltac:(clear - Q2; lia) ltac:(hc_prop Hc; exact Hc)) as Qa0z;
ws_pin HS (10%bv : bv 5) (SLit 0) Qa0z ltac:(reflexivity) end.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan 0x88764.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
add_atom HS 470%nat (sv_denot Ev (SLit 0)) E470;
rechunk_off HS 75%nat 62 (SOff 470 0) ltac:(rewrite sv_denot_SOff0, E470; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join HS ss_R4 471%nat fl_R4_deads_bv ltac:(idtac;
ra_join_fact HS 470%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E470; rewrite Z.pow_0_r, Z.mod_1_r; rewrite (denot_lit_U _ (SLit 0)), U_lit, unsigned_lit_small by (clear; lia); clear; lia));
fl_hand RR4 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists attr; split; [rewrite !ew_havoc_old by (clear; lia); exact E460 | exact Hattr]|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E470; unfold fl_slct, fl_uselct; cbn [c_f c_s]; hc_prop Hc; rewrite Hc; cbn [negb Z.eqb]; reflexivity|].
exists pt, w, h, top, left, tidx, img. cbn [c_s c_f c_ly c_S].
rewrite !ew_havoc_old by (clear; lia).
split; [exact E451|]. split; [exact E403|]. split; [exact E404|]. split; [exact E400|]. split; [exact E405|]. split; [exact E401|]. split; [exact E450|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|]. split; [exact Htidx|].
exact Hpt.
-
hc_bool Hc ltac:(fun H => hc_atom H 52%nat (fr_attr f) E52 ltac:(clear - Q2; lia)).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan 0x88764.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
add_atom HS 470%nat (sv_denot Ev (SOff 55 0)) E470;
rechunk_off HS 75%nat 62 (SOff 470 0) ltac:(rewrite sv_denot_SOff0, E470; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join HS ss_R4 471%nat fl_R4_deads_bv ltac:(idtac;
ra_join_fact HS 470%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E470; rewrite Z.pow_0_r, Z.mod_1_r; rewrite sv_denot_SOff0; rewrite ?ew_havoc_old by (clear; lia); rewrite E55, unsigned_lit_small by (clear - Q5; lia); clear - Q5; lia));
fl_hand RR4 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists attr; split; [rewrite !ew_havoc_old by (clear; lia); exact E460 | exact Hattr]|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E470; unfold fl_slct, fl_uselct; cbn [c_f c_s]; hc_prop Hc; destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [exfalso; exact (Hc ltac:(assumption))|]; cbn [negb]; rewrite sv_denot_SOff0; exact E55|].
exists pt, w, h, top, left, tidx, img. cbn [c_s c_f c_ly c_S].
rewrite !ew_havoc_old by (clear; lia).
split; [exact E451|]. split; [exact E403|]. split; [exact E404|]. split; [exact E400|]. split; [exact E405|]. split; [exact E401|]. split; [exact E450|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|]. split; [exact Htidx|].
exact Hpt.
Qed.
Lemma fl_R3 : fl_from B ss_R4 (INV_R4 B) -> fl_from B ss_R3 (INV_R3 B).
Proof. exact fl_R3_aux. Qed.
End b.
End a.
