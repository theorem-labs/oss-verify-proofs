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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCgl YCfu YCft YCrb YCez YCev YCf6 YCf2 YCf7.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma clr2_mod4 : forall x, x mod 4 = 0 -> (2 * (x / 2)) mod 4 = 0.
Proof.
intros x Hx. assert (E : x = 2 * (2 * (x / 4))).
{ pose proof (Z.div_mod x 4 ltac:(lia)). lia. }
rewrite E at 1. rewrite (Z.mul_comm 2 (2 * (x / 4))), Z_div_mult by lia.
replace (2 * (2 * (x / 4))) with (x / 4 * 4) by lia. apply Z_mod_mult.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma fl_B2_aux : fl_from B ss_B3 (INV_B3 B) -> fl_from B ss_B2 (INV_B2 B).
Proof.
intros RB3. fl_prelude.
pose proof HINV as (Hk3 & Eab3 & gen & E150 & Rgen & Hgen4).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E10n E32n Hing3).
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
Local Ltac joinB3 RB3 gtac ntac :=
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end;
lazymatch goal with HS : st_ok _ ?Ev ?ssv _, AG : forall n, (n < 33)%nat -> _ |- _ =>
let rs := eval vm_compute in (ss_mem ssv) in
let i := idx_of_base rs 11%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let cs := eval vm_compute in (YQ0b.r_chunks r) in
let j := idx_of_off cs 20 in let j := eval vm_compute in j in
lazymatch (eval vm_compute in (nth_error cs j)) with Some (YQ0b.mkChunk 20 (CVal 4 ?e)) =>
let E180 := fresh "E180" in let Qa4 := fresh "Qa4" in let E184 := fresh "E184" in
rreg HS (20%bv : bv 5) Qa4;
add_atom HS 180%nat (sv_denot Ev e) E180;
rechunk HS i j (SOff 180 0) ltac:(rewrite sv_denot_SOff0, E180; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity);
ra_join HS ss_B3 181%nat ra_deads_B3 ltac:(idtac;
ra_join_val HS 181%nat 3%nat Qa4 E184;
ra_join_fact HS 180%nat (mkAF 0 4294967295 0)
ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E180; rewrite Z.pow_0_r, Z.mod_1_r;
rewrite (denot_lit_U Ev e), unsigned_lit_small by (pose proof (U_range Ev e); rewrite M64_val in *; lia);
let HHH := fresh "HHH" in enough (HHH : 0 <= U Ev e <= 4294967295) by (clear - HHH; lia); gtac);
ra_join_fact HS 184%nat (mkAF 0 65535 0) ltac:(rewrite E184; rewrite Z.pow_0_r, Z.mod_1_r; ntac));
fl_hand RB3 HS end end.
Local Ltac tailB3 RB3 ntac :=
lazymatch goal with HS : st_ok _ _ _ _, SHOK : sh_ok _ _ _ _ _, HJ3 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, AG : forall n, (n < 33)%nat -> _,
Hing3 : In (_, CGIF_SIZE) (ablocks _ _ _), Hcur3 : In (_, FRAME_SIZE) (ablocks _ _ _),
E10n : ew _ 10 = _, E11n : ew _ 11 = _, E32n : ew _ 32 = _, EFA3 : forall c p, frame_addr _ c p = _ |- _ =>
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan;
[
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan 0x8796c;
[ try (oblG HJ3 E11n E32n Hcur3) .. | ];
[ lazymatch goal with F0 := frame_addr _ 1 ?fp |- _ => awrFL AG fp F0 EFA3 end | ];
clear_frames;
joinB3 RB3 ltac:(idtac; lazymatch goal with E150 : ew ?Ev 150 = Z_to_bv 64 ?gen, Rgen : 0 <= ?gen < _ |- _ => rewrite (U_atom Ev 150 gen E150) by lia; clear - Rgen; lia end) ntac
| aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan 0x8796c;
[ try (oblG HJ3 E11n E32n Hcur3) .. | ];
[ lazymatch goal with F0 := frame_addr _ 1 ?fp |- _ => awrFL AG fp F0 EFA3 end | ];
clear_frames;
joinB3 RB3 ltac:(idtac; lazymatch goal with E150 : ew ?Ev 150 = Z_to_bv 64 ?gen, Rgen : 0 <= ?gen < _ |- _ =>
rewrite U_and_m2, (U_atom Ev 150 gen E150) by lia; let Hclr := fresh "Hclr" in pose proof (clr2_rng gen ltac:(clear - Rgen; lia)) as Hclr; clear - Rgen Hclr; lia end) ntac ] end.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
-
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E10n E32n Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3. clear_frames.
hc_bool Hc ltac:(fun H => rewrite (U_atom _ 52 (fr_attr f) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E52)) in H by lia).
tailB3 RB3 ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E42, unsigned_lit_small by (clear - R9; lia); clear - R9; lia).
+   split; [exact Hk3|]. split; [exact Eab3|]. split.
* exists gen. split; [rewrite ew_havoc_old by (clear; lia); rewrite E180, sv_denot_SOff0; exact E150|]. split; [exact Rgen|]. exact Hgen4.
* rewrite E184. unfold fl_npal, fl_uselct; cbn [c_f c_s]. rewrite Hc. cbn [negb]. exact E42.
+   split; [exact Hk3|]. split; [exact Eab3|]. split.
* exists (2 * (gen / 2)). split; [rewrite ew_havoc_old by (clear; lia); rewrite E180, denot_lit_U, U_and_m2, (U_atom _ 150 gen E150) by lia; reflexivity|].
split; [pose proof (clr2_rng gen ltac:(clear - Rgen; lia)); clear - Rgen H; lia|]. intros Hb0. apply clr2_mod4. exact (Hgen4 Hb0).
* rewrite E184. unfold fl_npal, fl_uselct; cbn [c_f c_s]. rewrite Hc. cbn [negb]. exact E42.
-
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3. clear_frames.
hc_bool Hc ltac:(fun H => rewrite (U_atom _ 52 (fr_attr f) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E52)) in H by lia).
tailB3 RB3 ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E55, unsigned_lit_small by (clear - Q5; lia); clear - Q5; lia).
+   split; [exact Hk3|]. split; [exact Eab3|]. split.
* exists gen. split; [rewrite ew_havoc_old by (clear; lia); rewrite E180, sv_denot_SOff0; exact E150|]. split; [exact Rgen|]. exact Hgen4.
* rewrite E184. unfold fl_npal, fl_uselct; cbn [c_f c_s]. rewrite Hc. cbn [negb]. exact E55.
+   split; [exact Hk3|]. split; [exact Eab3|]. split.
* exists (2 * (gen / 2)). split; [rewrite ew_havoc_old by (clear; lia); rewrite E180, denot_lit_U, U_and_m2, (U_atom _ 150 gen E150) by lia; reflexivity|].
split; [pose proof (clr2_rng gen ltac:(clear - Rgen; lia)); clear - Rgen H; lia|]. intros Hb0. apply clr2_mod4. exact (Hgen4 Hb0).
* rewrite E184. unfold fl_npal, fl_uselct; cbn [c_f c_s]. rewrite Hc. cbn [negb]. exact E55.
Qed.
Lemma fl_B2 : fl_from B ss_B3 (INV_B3 B) -> fl_from B ss_B2 (INV_B2 B).
Proof. exact fl_B2_aux. Qed.
End b.
End a.
