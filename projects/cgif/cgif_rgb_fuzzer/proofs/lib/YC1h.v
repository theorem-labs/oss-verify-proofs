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
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma mod4_land2 : forall x, 0 <= x -> x mod 4 = 0 -> Z.land x 2 = 0.
Proof.
intros x Hx H4. replace x with ((x / 4) * 2 ^ 2) by (pose proof (Z.div_mod x 4 ltac:(lia)); lia).
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec n 2) as [Hl|Hge].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 2 n) with false; [apply andb_false_r|]. symmetry. change 2 with (2 ^ 1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Lemma mod4_land1 : forall x, 0 <= x -> x mod 4 = 0 -> Z.land x 1 = 0.
Proof.
intros x Hx H4. replace x with ((x / 4) * 2 ^ 2) by (pose proof (Z.div_mod x 4 ltac:(lia)); lia).
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec n 2) as [Hl|Hge].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 1 n) with false; [apply andb_false_r|]. symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
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
Ltac bef_facts fb :=
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
assert (E210 : ew Ev 210 = Z_to_bv 64 (fr_lpal fb)) by reflexivity;
assert (E211 : ew Ev 211 = Z_to_bv 64 (fr_img fb)) by reflexivity;
assert (E212 : ew Ev 212 = Z_to_bv 64 (fr_attr fb)) by reflexivity;
assert (E213 : ew Ev 213 = Z_to_bv 64 (fr_gen fb)) by reflexivity;
assert (E214 : ew Ev 214 = Z_to_bv 64 (fr_delay fb)) by reflexivity;
assert (E215 : ew Ev 215 = Z_to_bv 64 (fr_nlp fb)) by reflexivity;
assert (E216 : ew Ev 216 = Z_to_bv 64 (fr_ctidx fb)) by reflexivity;
assert (E217 : ew Ev 217 = Z_to_bv 64 (fr_disp fb)) by reflexivity;
assert (E218 : ew Ev 218 = Z_to_bv 64 (fr_tidx fb)) by reflexivity end.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Lemma fl_C_aux : fl_from B ss_R (INV_R B) -> fl_from B ss_T0 (INV_T0 B) -> fl_from B ss_DIFF (INV_DIFF B) -> fl_from B ss_B3 (INV_B3 B).
Proof.
intros RR RT RD. fl_prelude.
pose proof HINV as (Hk3 & Eab3 & (gen & E180 & Rgen & Hgen4) & E184).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan.
-
hc_bool Hc ltac:(fun H => rewrite (U_atom _ 180 gen ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E180)) in H by lia).
destruct (nth (i - 1) (cg_frames s) None) as [fb|] eqn:Hfb.
2:{ exfalso. pose proof (mod4_land2 gen ltac:(lia) (Hgen4 eq_refl)) as X. rewrite X in Hc. discriminate Hc. }
cbn [frame_ptr] in E12.
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
pose proof (Ofr fb Hfbi) as Ob.
destruct (fl_bef_blocks B ly S g s N rest fb HPerm Hfbi) as (Hbef_in & Hbimg_in & Hblpal).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR Hbef_in) as (Hb16 & Hb4096 & Hbceil & [Hbh1 Hbh2] & Hbpres & _).
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Hbef_in) as Hbh_img.
destruct (al_blocks _ _ LAWS ly S W mem md (fr_img fb) N HAR Hbimg_in) as (Hbi16 & Hbi4096 & Hbiceil & [Hbih1 Hbih2] & _ & _).
change (req_size FRAME_SIZE) with 40 in *.
assert (Hqi : 1 <= req_size N) by (unfold req_size; destruct (Z.eqb_spec N 0); lia).
pose proof (fl_bef_sep B LAWS ly S W mem md g s N rest i f fb HAR HPerm Hf Hfbe Hi) as Hsep_cb.
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ g CGIF_SIZE (fr_ptr fb) FRAME_SIZE HAR Hing Hbef_in ltac:(unfold CGIF_SIZE, FRAME_SIZE; intros X; injection X; lia)) as Hsep_gb.
unfold zdisjoint in Hsep_gb. cbn [fst snd] in Hsep_gb. change (req_size CGIF_SIZE) with 96 in Hsep_gb. change (req_size FRAME_SIZE) with 40 in Hsep_gb.
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr fb) FRAME_SIZE HAR Hraw_in Hbef_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as Hsep_rb.
unfold zdisjoint in Hsep_rb. cbn [fst snd] in Hsep_rb. change (req_size RAW_SIZE) with 48 in Hsep_rb. change (req_size FRAME_SIZE) with 40 in Hsep_rb.
assert (Hbef3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hbef_in).
pose proof (sep_block_frame trasegs _ LAWS ly3 S3 _ _ _ (fr_ptr fb) FRAME_SIZE 2 fpos HAR3 Hbef3 Hfin3) as HdFB.
unfold zdisjoint in HdFB; cbn [fst snd] in HdFB; change (req_size FRAME_SIZE) with 40 in HdFB; change (fs_frame_bytes 2) with 256 in HdFB; rewrite EFA3 in HdFB. fold F in HdFB.
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (Ob3 : obj_at trasegs (mrestrict (w_H Wx) (ms_mem msx)) (fr_ptr fb) LAY_Frame (frame_vals fb)) end.
{ eapply (aj_obj_kept B); [exact HJ3 | exact Hbef_in | exact Hbef3 | exact Ob | vm_compute; reflexivity |].
change (req_size FRAME_SIZE) with 40. intros j Hj. apply fl_fp_out_frame; [clear - Hsep_cb; lia | clear - Hsep_rb; lia | exact Hj]. }
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) =>
assert (E12n : ew Ev 12 = Z_to_bv 64 (fr_ptr fb)) by (rewrite (AG 12%nat) by lia; exact E12);
pose proof (st_ok_add_bef Ev ssv Hh msv fb HS ltac:(vm_compute; reflexivity)
ltac:(rewrite E12n; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) Hbh1 Hbceil Hb16 Hbih1 ltac:(clear - Hbih2 Hqi; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) Hbi16 Ob3
ltac:(unfold fl_Ebef, fl_bef_region; cbn [map frame_vals]; lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, CGIF_SIZE, FRAME_SIZE;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 Hbh1 Hbh2 Hbh_img HF8hi HF8lo HF8c HFceil HdFB Hsep_gb Hsep_cb; ceil; unfold off_img, ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kHighMemBeg in *; repeat split; try lia;
match goal with |- ?g => idtac "DISJ-LEFT" g end)) as HS3;
clear HS; rename HS3 into HS end.
unfold fl_Ebef in HS. cbn [map frame_vals] in HS. norm_ss HS.
bef_facts fb.
reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x87044.
all: try (oblG HJ3 E11n E32n Hcur3).
all: try (oblG HJ3 E12n E32n Hbef3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseF HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ => ra_join HS ss_DIFF 240%nat ([] : list (bv 5)) ltac:(idtac); fl_hand RD HS end.
split; [exact Hk3|]. split; [exact Eab3|].
split; [exists gen; split; [rewrite ew_havoc_old by (clear; lia); assumption|]; split; [exact Rgen|]; apply Z.eqb_neq; exact Hc|].
split; [rewrite ew_havoc_old by (clear; lia); assumption|].
exists fb. apply fl_bef_havoc; [clear; lia|]. split; [exact Hfb|]. cbn [c_i c_s]. bef_EB.
-
hc_bool Hc ltac:(fun H => rewrite (U_atom _ 180 gen ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by lia; exact E180)) in H by lia).
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x87674.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
destruct (Z.eqb_spec (Z.land gen 1) 0) as [Hg1|Hg1].
+
reshok HS.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan.
*
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x878c0.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseF HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
rreg HS (23%bv : bv 5) Q23; rreg HS (27%bv : bv 5) Q27;
add_atom HS 398%nat (sv_denot Ev (SOff 40 0)) E398;
rechunk_off HS 70%nat 168 (SOff 398 0) ltac:(rewrite sv_denot_SOff0, E398; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
add_atom HS 399%nat (sv_denot Ev (SLit 0)) E399;
rechunk_off HS 70%nat 144 (SOff 399 0) ltac:(rewrite sv_denot_SOff0, E399; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
add_atom HS 400%nat (sv_denot Ev (SLit 0)) E400;
rechunk_off HS 70%nat 152 (SOff 400 0) ltac:(rewrite sv_denot_SOff0, E400; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
add_atom HS 401%nat (sv_denot Ev (SOff 58 0)) E401;
rechunk_off HS 70%nat 232 (SOff 401 0) ltac:(rewrite sv_denot_SOff0, E401; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join HS ss_R 402%nat fl_R_deads_bv ltac:(idtac;
ra_join_val HS 402%nat 0%nat Q23 E402; ra_join_val HS 402%nat 2%nat Q27 E404;
ra_join_fact HS 398%nat (mkAF 1 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E398, sv_denot_SOff0; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E40, unsigned_lit_small by (clear - R7 HW1; lia); clear - R7 HW1; lia);
ra_join_fact HS 399%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E399; rewrite Z.pow_0_r, Z.mod_1_r; rewrite (denot_lit_U _ (SLit 0)), U_lit, unsigned_lit_small by (clear; lia); clear; lia);
ra_join_fact HS 400%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E400; rewrite Z.pow_0_r, Z.mod_1_r; rewrite (denot_lit_U _ (SLit 0)), U_lit, unsigned_lit_small by (clear; lia); clear; lia);
ra_join_fact HS 404%nat (mkAF 1 65535 0) ltac:(rewrite E404; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E41, unsigned_lit_small by (clear - R8 HH1; lia); clear - R8 HH1; lia));
fl_hand RR HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
exists 0, (cg_W s), (cg_H s), 0, 0, (fr_tidx f). cbn [c_s c_ly c_S].
split; [rewrite E402; reflexivity|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E398, sv_denot_SOff0; exact E40|].
split; [rewrite E404; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; exact E41|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E400; reflexivity|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E399; reflexivity|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E401, sv_denot_SOff0; rewrite !ew_havoc_old by (clear; lia); exact E58|].
split; [clear; lia|].
split; [exact HW1|]. split; [clear; lia|]. split; [clear; lia|]. split; [exact HH1|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear - Q8; lia|].
left. split; [reflexivity|]. split; [exact Hk3 | exact Eab3].
* hc_bool Hc0 ltac:(fun H => hc_atom H 180%nat gen E180 ltac:(clear - Rgen; lia)).
exfalso. rewrite Hg1 in Hc0. cbn in Hc0. discriminate Hc0.
+
destruct (nth (i - 1) (cg_frames s) None) as [fb|] eqn:Hfb.
2:{ exfalso. exact (Hg1 (mod4_land1 gen ltac:(lia) (Hgen4 eq_refl))). }
cbn [frame_ptr] in E12.
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
pose proof (Ofr fb Hfbi) as Ob.
destruct (fl_bef_blocks B ly S g s N rest fb HPerm Hfbi) as (Hbef_in & Hbimg_in & Hblpal).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR Hbef_in) as (Hb16 & Hb4096 & Hbceil & [Hbh1 Hbh2] & Hbpres & _).
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Hbef_in) as Hbh_img.
destruct (al_blocks _ _ LAWS ly S W mem md (fr_img fb) N HAR Hbimg_in) as (Hbi16 & Hbi4096 & Hbiceil & [Hbih1 Hbih2] & _ & _).
change (req_size FRAME_SIZE) with 40 in *.
assert (Hqi : 1 <= req_size N) by (unfold req_size; destruct (Z.eqb_spec N 0); lia).
pose proof (fl_bef_sep B LAWS ly S W mem md g s N rest i f fb HAR HPerm Hf Hfbe Hi) as Hsep_cb.
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ g CGIF_SIZE (fr_ptr fb) FRAME_SIZE HAR Hing Hbef_in ltac:(unfold CGIF_SIZE, FRAME_SIZE; intros X; injection X; lia)) as Hsep_gb.
unfold zdisjoint in Hsep_gb. cbn [fst snd] in Hsep_gb. change (req_size CGIF_SIZE) with 96 in Hsep_gb. change (req_size FRAME_SIZE) with 40 in Hsep_gb.
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr fb) FRAME_SIZE HAR Hraw_in Hbef_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as Hsep_rb.
unfold zdisjoint in Hsep_rb. cbn [fst snd] in Hsep_rb. change (req_size RAW_SIZE) with 48 in Hsep_rb. change (req_size FRAME_SIZE) with 40 in Hsep_rb.
assert (Hbef3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hbef_in).
pose proof (sep_block_frame trasegs _ LAWS ly3 S3 _ _ _ (fr_ptr fb) FRAME_SIZE 2 fpos HAR3 Hbef3 Hfin3) as HdFB.
unfold zdisjoint in HdFB; cbn [fst snd] in HdFB; change (req_size FRAME_SIZE) with 40 in HdFB; change (fs_frame_bytes 2) with 256 in HdFB; rewrite EFA3 in HdFB. fold F in HdFB.
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msx) =>
assert (Ob3 : obj_at trasegs (mrestrict (w_H Wx) (ms_mem msx)) (fr_ptr fb) LAY_Frame (frame_vals fb)) end.
{ eapply (aj_obj_kept B); [exact HJ3 | exact Hbef_in | exact Hbef3 | exact Ob | vm_compute; reflexivity |].
change (req_size FRAME_SIZE) with 40. intros j Hj. apply fl_fp_out_frame; [clear - Hsep_cb; lia | clear - Hsep_rb; lia | exact Hj]. }
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) =>
assert (E12n : ew Ev 12 = Z_to_bv 64 (fr_ptr fb)) by (rewrite (AG 12%nat) by lia; exact E12);
pose proof (st_ok_add_bef Ev ssv Hh msv fb HS ltac:(vm_compute; reflexivity)
ltac:(rewrite E12n; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) Hbh1 Hbceil Hb16 Hbih1 ltac:(clear - Hbih2 Hqi; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) Hbi16 Ob3
ltac:(unfold fl_Ebef, fl_bef_region; cbn [map frame_vals]; lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, CGIF_SIZE, FRAME_SIZE;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 Hbh1 Hbh2 Hbh_img HF8hi HF8lo HF8c HFceil HdFB Hsep_gb Hsep_cb; ceil; unfold off_img, ASAN_CEIL, kHighMemBeg, kLowShadowBeg, kHighMemBeg in *; repeat split; try lia;
match goal with |- ?g => idtac "DISJ-LEFT" g end)) as HS3;
clear HS; rename HS3 into HS end.
unfold fl_Ebef in HS. cbn [map frame_vals] in HS. norm_ss HS. bef_facts fb.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseF HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
rreg HS (23%bv : bv 5) Q23; rreg HS (27%bv : bv 5) Q27;
add_atom HS 238%nat (sv_denot Ev (SOff 40 0)) E238;
rechunk_off HS 70%nat 168 (SOff 238 0) ltac:(rewrite sv_denot_SOff0, E238; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
add_atom HS 239%nat (sv_denot Ev (SLit 0)) E239;
rechunk_off HS 70%nat 144 (SOff 239 0) ltac:(rewrite sv_denot_SOff0, E239; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
add_atom HS 240%nat (sv_denot Ev (SLit 0)) E240;
rechunk_off HS 70%nat 152 (SOff 240 0) ltac:(rewrite sv_denot_SOff0, E240; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join HS ss_T0 241%nat fl_T0_deads_bv ltac:(idtac;
ra_join_val HS 241%nat 0%nat Q23 E241; ra_join_val HS 241%nat 2%nat Q27 E243;
ra_join_fact HS 238%nat (mkAF 1 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E238, sv_denot_SOff0; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E40, unsigned_lit_small by (clear - R7 HW1; lia); clear - R7 HW1; lia);
ra_join_fact HS 239%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E239; rewrite Z.pow_0_r, Z.mod_1_r; rewrite (denot_lit_U _ (SLit 0)), U_lit, unsigned_lit_small by (clear; lia); clear; lia);
ra_join_fact HS 240%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E240; rewrite Z.pow_0_r, Z.mod_1_r; rewrite (denot_lit_U _ (SLit 0)), U_lit, unsigned_lit_small by (clear; lia); clear; lia);
ra_join_fact HS 243%nat (mkAF 1 65535 0) ltac:(rewrite E243; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E41, unsigned_lit_small by (clear - R8 HH1; lia); clear - R8 HH1; lia));
fl_hand RT HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; do 4 (apply fl_bef_havoc; [clear; lia|]); split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
exists 0, (cg_W s), (cg_H s), 0, 0. cbn [c_s c_ly c_S].
split; [rewrite E241; reflexivity|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E238, sv_denot_SOff0; exact E40|].
split; [rewrite E243; exact E41|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E240; reflexivity|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E239; reflexivity|].
split; [clear; lia|].
split; [exact HW1|]. split; [clear; lia|]. split; [clear; lia|]. split; [exact HH1|]. split; [clear; lia|]. split; [clear; lia|].
left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hk3 | exact Eab3].
Qed.
Lemma fl_C : fl_from B ss_R (INV_R B) -> fl_from B ss_T0 (INV_T0 B) -> fl_from B ss_DIFF (INV_DIFF B) -> fl_from B ss_B3 (INV_B3 B).
Proof. exact fl_C_aux. Qed.
End b.
End a.
