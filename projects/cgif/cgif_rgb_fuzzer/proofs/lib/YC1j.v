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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC1z YC1y YC27 YC23 YC28 YC1w YC24 YC26 YC29.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac nat_side := first [ apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (Nat.eqb_neq _ _)); vm_compute; reflexivity ].
Ltac rebaseF HS AG HEv :=
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG end end.
Lemma w_all_disjoint_ext_l : forall E r r' l,
YQ0b.r_base r' = YQ0b.r_base r -> YQ0b.r_lo r' = YQ0b.r_lo r -> YQ0b.r_hi r' = YQ0b.r_hi r ->
all_disjoint E r l -> all_disjoint E r' l.
Proof.
intros E r r' l Hb Hl Hh. induction l as [|x l IH]; cbn; [tauto|]. intros [H1 H2]. split; [|exact (IH H2)].
unfold extent_disjoint in *. rewrite Hb, Hl, Hh. exact H1.
Qed.
Lemma w_all_disjoint_ext_r : forall E y r r' l1 l2,
YQ0b.r_base r' = YQ0b.r_base r -> YQ0b.r_lo r' = YQ0b.r_lo r -> YQ0b.r_hi r' = YQ0b.r_hi r ->
all_disjoint E y (l1 ++ r :: l2) -> all_disjoint E y (l1 ++ r' :: l2).
Proof.
intros E y r r' l1 l2 Hb Hl Hh. induction l1 as [|x l1 IH]; cbn; intros [H1 H2]; (split; [|first [exact H2 | exact (IH H2)]]).
- unfold extent_disjoint in *. rewrite Hb, Hl, Hh. exact H1.
- exact H1.
Qed.
Lemma w_pairwise_disjoint_ext : forall E r r' l1 l2,
YQ0b.r_base r' = YQ0b.r_base r -> YQ0b.r_lo r' = YQ0b.r_lo r -> YQ0b.r_hi r' = YQ0b.r_hi r ->
pairwise_disjoint E (l1 ++ r :: l2) -> pairwise_disjoint E (l1 ++ r' :: l2).
Proof.
intros E r r' l1 l2 Hb Hl Hh. induction l1 as [|y l1 IH]; cbn; intros [H1 H2]; split.
- exact (w_all_disjoint_ext_l E r r' l2 Hb Hl Hh H1).
- exact H2.
- exact (w_all_disjoint_ext_r E y r r' l1 l2 Hb Hl Hh H1).
- exact (IH H2).
Qed.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma w_st_ok_add_chunk : forall E ss ms l1 nb lo hi wlo whi cs l2 c,
st_ok trasegs E ss ms -> ss_mem ss = l1 ++ YQ0b.mkRegion nb lo hi wlo whi cs :: l2 ->
regions_wf (l1 ++ YQ0b.mkRegion nb lo hi wlo whi (c :: cs) :: l2) = true ->
YQ0b.chunk_ok trasegs E (ms_mem ms) (base_val E nb) c ->
st_ok trasegs E (mkSS (ss_pc ss) (ss_regs ss) (l1 ++ YQ0b.mkRegion nb lo hi wlo whi (c :: cs) :: l2) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms l1 nb lo hi wlo whi cs l2 c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hrs Hwf' Hc.
rewrite Hrs in Hok, Hpd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact Hwf'|]. split.
- apply Forall_app in Hok as [Ha Hb]. inversion Hb as [|x l Hr Hl]; subst. apply Forall_app. split; [exact Ha|]. constructor; [|exact Hl].
unfold region_ok in Hr |- *. cbv zeta in Hr |- *. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks] in Hr |- *.
destruct Hr as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. constructor; [exact Hc | exact R4].
- exact (w_pairwise_disjoint_ext E (YQ0b.mkRegion nb lo hi wlo whi cs) (YQ0b.mkRegion nb lo hi wlo whi (c :: cs)) l1 l2 eq_refl eq_refl eq_refl Hpd).
Qed.
Section b.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Ltac add_fact HS n lo hi Hv tac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_fact trasegs Ev ssx msx n (mkAF lo hi 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Hv, unsigned_lit_small by tac; rewrite Z.pow_0_r, Z.mod_1_r; split; [tac | split; [reflexivity | clear; lia]])) as HS3;
clear HS; rename HS3 into HS end.
Ltac ws_pin HS r e Hr dtac :=
let HS3 := fresh "HS3" in
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv r e HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Hr; cbn [sv_denot]; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac seat160 HS na h E70 Ena V160 sptac htac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 70%nat in let il := eval vm_compute in il in
let l1 := eval vm_compute in (firstn il rs) in
let rt := eval vm_compute in (nth il rs got_region) in
let l2 := eval vm_compute in (skipn (S il) rs) in
lazymatch rt with YQ0b.mkRegion ?nb ?lo ?hi ?wlo ?whi ?cs =>
let HS3 := fresh "HS3" in
pose proof (w_st_ok_add_chunk Ev ssx msv l1 nb lo hi wlo whi cs l2 (YQ0b.mkChunk 160 (CVal 8 (SOff na 0))) HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(cbn [base_val]; rewrite ?ew_havoc_old by nat_side; rewrite E70, unsigned_lit_small by sptac;
apply (chunk_ok_val trasegs Ev _ _ 160 8 _ h);
[ cbn [sv_denot]; rewrite Ena, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn [Z.of_N Z.mul]; htac | cbn; lia | exact V160 ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end end.
Ltac d1_join RD1 w h top left Qw Qt Ql wtac htac ttac ltac_ :=
let E446 := fresh "E446" in let E447 := fresh "E447" in let E448 := fresh "E448" in let E449 := fresh "E449" in
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
add_atom HS 446%nat (Z_to_bv 64 w) E446; add_fact HS 446%nat 1 65535 E446 wtac;
add_atom HS 447%nat (Z_to_bv 64 h) E447; add_fact HS 447%nat 1 65535 E447 htac;
add_atom HS 448%nat (Z_to_bv 64 top) E448; add_fact HS 448%nat 0 65535 E448 ttac;
add_atom HS 449%nat (Z_to_bv 64 left) E449; add_fact HS 449%nat 0 65535 E449 ltac_;
norm_ss HS;
rechunk_off HS 75%nat 112 (SOff 448 0) ltac:(rewrite !sv_denot_SOff0; rewrite ?ew_havoc_old by nat_side; rewrite E448; cbn [sv_denot]; rewrite ?ew_havoc_old by nat_side;
first [reflexivity | lazymatch goal with E : ew _ 421 = _ |- _ => rewrite E; reflexivity end | match goal with |- ?g => idtac "RECHUNK112" g end]);
rechunk_off HS 75%nat 128 (SOff 449 0) ltac:(rewrite !sv_denot_SOff0; rewrite ?ew_havoc_old by nat_side; rewrite E449; cbn [sv_denot]; rewrite ?ew_havoc_old by nat_side;
first [reflexivity | lazymatch goal with E : ew _ 422 = _ |- _ => rewrite E; reflexivity end | match goal with |- ?g => idtac "RECHUNK128" g end]);
rechunk_off HS 70%nat 160 (SOff 447 0) ltac:(rewrite !sv_denot_SOff0; rewrite ?ew_havoc_old by nat_side; rewrite E447; rewrite ?ew_havoc_old by nat_side;
first [lazymatch goal with E : ew _ 439 = _ |- _ => rewrite E; reflexivity end | match goal with |- ?g => idtac "RECHUNK160" g end]);
ws_pin HS (@BV 5 26 I) (SOff 446 0) Qw ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_havoc_old by nat_side; exact E446);
ws_pin HS (@BV 5 27 I) (SOff 448 0) Qt ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_havoc_old by nat_side; exact E448);
ws_pin HS (@BV 5 23 I) (SOff 449 0) Ql ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_havoc_old by nat_side; exact E449);
ra_join HS ss_D1 450%nat fl_D1_deads_bv ltac:(idtac);
fl_hand RD1 HS end.
Lemma fl_D_aux : fl_from B ss_D1 (INV_D1 B) -> fl_from B ss_DIMS (INV_DIMS B).
Proof.
intros RD1. fl_prelude.
pose proof HINV as (Hk3 & Eab3 & (gen & E180 & Rgen) & E184 & (fb & Hfb & EB) & (w & h & top & left & E420 & V160 & E421 & E422 & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth)).
cbn [c_i c_s] in Hfb. cbn [c_s] in Hlw, Hth. cbn [c_sp1] in V160.
pose proof (EB 0%nat _ eq_refl) as E210. pose proof (EB 1%nat _ eq_refl) as E211. pose proof (EB 2%nat _ eq_refl) as E212.
pose proof (EB 3%nat _ eq_refl) as E213. pose proof (EB 4%nat _ eq_refl) as E214. pose proof (EB 5%nat _ eq_refl) as E215.
pose proof (EB 6%nat _ eq_refl) as E216. pose proof (EB 7%nat _ eq_refl) as E217. pose proof (EB 8%nat _ eq_refl) as E218.
cbn [Nat.add] in E210, E211, E212, E213, E214, E215, E216, E217, E218.
assert (HW65 : cg_W s <= 65535) by (clear - R7; lia).
assert (HH65 : cg_H s <= 65535) by (clear - R8; lia).
add_fact HS 420%nat 1 65535 E420 ltac:(clear - Hw1 Hl0 Hlw HW65; lia).
add_fact HS 421%nat 0 65535 E421 ltac:(clear - Hh1 Ht0 Hth HH65; lia).
add_fact HS 422%nat 0 65535 E422 ltac:(clear - Hw1 Hl0 Hlw HW65; lia).
norm_ss HS.
add_atom HS 439%nat (Z_to_bv 64 h) E439. add_fact HS 439%nat 1 65535 E439 ltac:(clear - Hh1 Ht0 Hth HH65; lia).
seat160 HS 439%nat h E70 E439 V160 ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia) ltac:(clear - Hh1 Ht0 Hth HH65; lia).
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseF HS0 AG0 HEv0; clear HEv0 end.
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x87588.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseF HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
rreg HS (@BV 5 26 I) Qw; rreg HS (@BV 5 27 I) Qt; rreg HS (@BV 5 23 I) Ql end.
rewrite E420 in Qw. rewrite E421 in Qt. rewrite E422 in Ql.
d1_join RD1 w h top left Qw Qt Ql ltac:(clear - Hw1 Hl0 Hlw HW65; lia) ltac:(clear - Hh1 Ht0 Hth HH65; lia) ltac:(clear - Hh1 Ht0 Hth HH65; lia) ltac:(clear - Hw1 Hl0 Hlw HW65; lia).
split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; repeat (apply fl_bef_havoc; [clear; lia|]); split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
exists w, h, top, left. cbn [c_s].
split; [rewrite 4 ew_havoc_old by (clear; lia); exact E446|].
split; [rewrite 3 ew_havoc_old by (clear; lia); exact E447|].
split; [rewrite 2 ew_havoc_old by (clear; lia); exact E448|].
split; [rewrite 1 ew_havoc_old by (clear; lia); exact E449|].
split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0 | exact Hth].
Qed.
Lemma fl_D : fl_from B ss_D1 (INV_D1 B) -> fl_from B ss_DIMS (INV_DIMS B).
Proof. exact fl_D_aux. Qed.
Lemma fl_Di_aux : fl_from B ss_D1 (INV_D1 B) -> fl_from B ss_DIMSi (INV_DIMSi B).
Proof.
intros RD1. fl_prelude.
pose proof HINV as (Hk3 & Eab3 & (gen & E180 & Rgen) & E184 & (fb & Hfb & EB) & V160).
cbn [c_i c_s] in Hfb. cbn [c_sp1] in V160.
pose proof (EB 0%nat _ eq_refl) as E210. pose proof (EB 1%nat _ eq_refl) as E211. pose proof (EB 2%nat _ eq_refl) as E212.
pose proof (EB 3%nat _ eq_refl) as E213. pose proof (EB 4%nat _ eq_refl) as E214. pose proof (EB 5%nat _ eq_refl) as E215.
pose proof (EB 6%nat _ eq_refl) as E216. pose proof (EB 7%nat _ eq_refl) as E217. pose proof (EB 8%nat _ eq_refl) as E218.
cbn [Nat.add] in E210, E211, E212, E213, E214, E215, E216, E217, E218.
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
add_atom HS 439%nat (Z_to_bv 64 1) E439. add_fact HS 439%nat 1 65535 E439 ltac:(clear; lia).
seat160 HS 439%nat 1 E70 E439 V160 ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia) ltac:(clear; lia).
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseF HS0 AG0 HEv0; clear HEv0 end.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x87588.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseF HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
rreg HS (@BV 5 26 I) Qw; rreg HS (@BV 5 27 I) Qt; rreg HS (@BV 5 23 I) Ql end.
d1_join RD1 1 1 0 0 Qw Qt Ql ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia).
split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; repeat (apply fl_bef_havoc; [clear; lia|]); split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
exists 1, 1, 0, 0. cbn [c_s].
split; [rewrite 4 ew_havoc_old by (clear; lia); exact E446|].
split; [rewrite 3 ew_havoc_old by (clear; lia); exact E447|].
split; [rewrite 2 ew_havoc_old by (clear; lia); exact E448|].
split; [rewrite 1 ew_havoc_old by (clear; lia); exact E449|].
split; [clear; lia|]. split; [clear; lia|]. split; [clear - HW1; lia|]. split; [clear; lia|]. split; [clear; lia | clear - HH1; lia].
Qed.
Lemma fl_Di : fl_from B ss_D1 (INV_D1 B) -> fl_from B ss_DIMSi (INV_DIMSi B).
Proof. exact fl_Di_aux. Qed.
End b.
End a.
