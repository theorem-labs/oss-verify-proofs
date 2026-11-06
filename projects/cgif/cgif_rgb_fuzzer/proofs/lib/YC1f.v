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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC1z YC1y YC27 YC23 YC28.
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
Ltac joinB2 RB2 gtac :=
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end;
lazymatch goal with HS : st_ok _ ?Ev ?ssv _, AG : forall n, (n < 33)%nat -> _ |- _ =>
let rs := eval vm_compute in (ss_mem ssv) in
let i := idx_of_base rs 11%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let cs := eval vm_compute in (YQ0b.r_chunks r) in
let j := idx_of_off cs 20 in let j := eval vm_compute in j in
lazymatch (eval vm_compute in (nth_error cs j)) with Some (YQ0b.mkChunk 20 (CVal 4 ?e)) =>
let E90 := fresh "E150" in let HEv := fresh "HEv" in
add_atom HS 150%nat (sv_denot Ev e) E90;
rechunk HS i j (SOff 150 0) ltac:(rewrite sv_denot_SOff0, E90; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity);
ra_join HS ss_B2 151%nat ra_deads_B2 ltac:(idtac; ra_join_fact HS 150%nat (mkAF 0 4294967295 0)
ltac:(rewrite ew_havoc_old by (clear; lia); rewrite E90; rewrite Z.pow_0_r, Z.mod_1_r;
rewrite (denot_lit_U Ev e), unsigned_lit_small by (pose proof (U_range Ev e); rewrite M64_val in *; lia);
let HHH := fresh "HHH" in enough (HHH : 0 <= U Ev e <= 4294967295) by (clear - HHH; lia); gtac));
fl_hand RB2 HS end end.
Lemma fl_B1_aux : fl_from B ss_B2 (INV_B2 B) -> fl_from B ss_B (INV_0 B 0).
Proof.
intros RB2. fl_prelude.
pose proof HINV as (Hk3 & Eab3).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n.
fs_roF HS. reshok HS.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E10n E32n Hing3).
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan.
-
assert (HpBef : frame_ptr (nth (i - 1) (cg_frames s) None) <> 0).
{ intros Hb0. rewrite branch_eq_U, U_lit in Hc by lia. apply Z.eqb_eq in Hc. apply (U_front_isfirst _ _ Hc).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rewrite (U_atom Ev 12 _ ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 12%nat) by lia; exact E12)); [exact Hb0 | rewrite Hb0; lia] end. }
aj_run_tok tratbl_lib_ok HS HJ3 SHOK FLBspan. 1: awrFL AG fpos F EFA3. clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan.
+ aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x86f4c. 1: awrFL AG fpos F EFA3. clear_frames.
joinB2 RB2 ltac:(idtac; rewrite (U_atom _ 53 (fr_gen f) E53) by lia; clear - Q3; lia).
split; [exact Hk3|]. split; [exact Eab3|]. exists (fr_gen f).
split; [rewrite ew_havoc_old by (clear; lia); rewrite E150, sv_denot_SOff0; exact E53|]. split; [clear - Q3; lia|].
intros Hb0. exfalso. exact (HpBef Hb0).
+ aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x86f4c.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3. clear_frames.
joinB2 RB2 ltac:(idtac; rewrite U_and_m2, (U_atom _ 53 (fr_gen f) E53) by lia; pose proof (clr2_rng (fr_gen f) ltac:(clear - Q3; lia)); clear - Q3 H; lia).
split; [exact Hk3|]. split; [exact Eab3|]. exists (2 * (fr_gen f / 2)).
split; [rewrite ew_havoc_old by (clear; lia); rewrite E150, denot_lit_U, U_and_m2, (U_atom _ 53 (fr_gen f) E53) by lia; reflexivity|].
split; [pose proof (clr2_rng (fr_gen f) ltac:(clear - Q3; lia)); clear - Q3 H; lia|]. intros Hb0. exfalso. exact (HpBef Hb0).
-
aj_run_tok tratbl_lib_ok HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3. clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan.
+ aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x86f4c. 1: awrFL AG fpos F EFA3. clear_frames.
joinB2 RB2 ltac:(idtac; rewrite U_and_m4, (U_atom _ 53 (fr_gen f) E53) by lia; pose proof (clr4_rng (fr_gen f) ltac:(clear - Q3; lia)); clear - Q3 H; lia).
split; [exact Hk3|]. split; [exact Eab3|]. exists (4 * (fr_gen f / 4)).
split; [rewrite ew_havoc_old by (clear; lia); rewrite E150, denot_lit_U, U_and_m4, (U_atom _ 53 (fr_gen f) E53) by lia; reflexivity|].
split; [pose proof (clr4_rng (fr_gen f) ltac:(clear - Q3; lia)); clear - Q3 H; lia|]. intros _. rewrite Z.mul_comm. apply Z_mod_mult.
+ aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x86f4c.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3. clear_frames.
joinB2 RB2 ltac:(idtac; rewrite U_and_m2, U_and_m4, (U_atom _ 53 (fr_gen f) E53) by lia; rewrite clr42 by (clear - Q3; lia);
pose proof (clr4_rng (fr_gen f) ltac:(clear - Q3; lia)); clear - Q3 H; lia).
split; [exact Hk3|]. split; [exact Eab3|]. exists (4 * (fr_gen f / 4)).
split; [rewrite ew_havoc_old by (clear; lia); rewrite E150, denot_lit_U, U_and_m2, U_and_m4, (U_atom _ 53 (fr_gen f) E53) by lia; rewrite clr42 by (clear - Q3; lia); reflexivity|].
split; [pose proof (clr4_rng (fr_gen f) ltac:(clear - Q3; lia)); clear - Q3 H; lia|]. intros _. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma fl_B1 : fl_from B ss_B2 (INV_B2 B) -> fl_from B ss_B (INV_0 B 0).
Proof. exact fl_B1_aux. Qed.
End b.
End a.
