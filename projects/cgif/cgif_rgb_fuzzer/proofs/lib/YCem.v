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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCgl YCfu YCft YCrb YCez YCev YCf6 YCf2 YCf7 YCet YCf3 YCey YCf5 YCew YCf0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Ltac joinT1x RT1 :=
rebase_goal;
lazymatch goal with HS : st_ok _ ?Ev ?ssv _ |- _ =>
let rs := eval vm_compute in (ss_mem ssv) in
let i := idx_of_base rs 70%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let cs := eval vm_compute in (YQ0b.r_chunks r) in
let j := idx_of_off cs 184 in let j := eval vm_compute in j in
lazymatch (eval vm_compute in (nth_error cs j)) with Some (YQ0b.mkChunk 184 (CVal 8 ?e)) =>
let E300 := fresh "E300" in
add_atom HS 300%nat (sv_denot Ev e) E300;
rechunk HS i j (SOff 300 0) ltac:(rewrite sv_denot_SOff0, E300; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity);
ra_join HS ss_T1x 301%nat fl_T1x_deads_bv ltac:(idtac);
fl_hand RT1 HS end end.
Lemma fl_T1_aux : fl_from B ss_R (INV_R B) -> fl_from B ss_T1x (INV_T0 B) -> fl_from B ss_T0 (INV_T0 B).
Proof.
intros RR RT1. fl_prelude.
pose proof HINV as ((gen & E180 & Rgen) & E184 & (fb & Hfb & EB) & (pt & w & h & top & left & E241 & E242 & E243 & E240 & E244 & Hrpt & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & Hpt)).
cbn [c_i c_s] in Hfb. pose proof Hpt as Hpt0. unfold fl_tmpblk, fl_FP in Hpt. cbn [c_ly c_S c_regs c_f c_s] in Hpt.
pose proof (EB 0%nat _ eq_refl) as E210. pose proof (EB 1%nat _ eq_refl) as E211. pose proof (EB 2%nat _ eq_refl) as E212.
pose proof (EB 3%nat _ eq_refl) as E213. pose proof (EB 4%nat _ eq_refl) as E214. pose proof (EB 5%nat _ eq_refl) as E215.
pose proof (EB 6%nat _ eq_refl) as E216. pose proof (EB 7%nat _ eq_refl) as E217. pose proof (EB 8%nat _ eq_refl) as E218.
cbn [Nat.add] in E210, E211, E212, E213, E214, E215, E216, E217, E218.
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)).
{ intros x Hx. destruct Hpt as [(_ & _ & _ & _ & Eab3) | (_ & _ & (_ & _ & _ & Eab3 & _))]; rewrite Eab3; [exact Hx | apply in_app_iff; left; exact Hx]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
assert (Rnp : 0 <= fl_npal (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 E0) <= 65535) by (unfold fl_npal; cbn [c_f c_s]; destruct (fl_uselct _); [clear - Q5 | clear - R9]; lia).
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan.
all: try (oblG HJ3 E11n E32n Hcur3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
-
hc_bool Hc ltac:(fun H => lazymatch type of H with context [U ?Ev (SExt false 8 (SOff 180 0))] => rewrite (gen_test8 Ev 180 gen 1 ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E180) ltac:(clear - Rgen; lia) ltac:(clear; lia)) in H end).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan 0x8862c.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
rreg HS (24%bv : bv 5) QXp; rreg HS (21%bv : bv 5) QXw; rreg HS (23%bv : bv 5) QXh; rreg HS (22%bv : bv 5) QXl; rreg HS (6%bv : bv 5) QXt;
add_atom HS 400%nat (sv_denot Ev (SOff 240 0)) E400;
ws_pin HS (6%bv : bv 5) (SOff 400 0) QXt ltac:(rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E400; rewrite ?sv_denot_SOff0, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
add_atom HS 401%nat (sv_denot Ev (SOff 58 0)) E401;
rechunk_off HS 70%nat 184 (SOff 401 0) ltac:(rewrite sv_denot_SOff0, E401; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join HS ss_R 402%nat fl_R_deads_bv ltac:(idtac;
ra_join_val HS 402%nat 0%nat QXp E402; ra_join_val HS 402%nat 1%nat QXw E403; ra_join_val HS 402%nat 2%nat QXh E404; ra_join_val HS 402%nat 3%nat QXl E405;
ra_join_fact HS 400%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E400; rewrite Z.pow_0_r, Z.mod_1_r; rewrite sv_denot_SOff0, E240, unsigned_lit_small by (clear - Ht0 Hth Hh1 R8; lia); clear - Ht0 Hth Hh1 R8; lia);
ra_join_fact HS 403%nat (mkAF 1 65535 0) ltac:(rewrite E403; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E242, unsigned_lit_small by (clear - Hw1 Hlw Hl0 R7; lia); clear - Hw1 Hlw Hl0 R7; lia);
ra_join_fact HS 404%nat (mkAF 1 65535 0) ltac:(rewrite E404; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E243, unsigned_lit_small by (clear - Hh1 Hth Ht0 R8; lia); clear - Hh1 Hth Ht0 R8; lia);
ra_join_fact HS 405%nat (mkAF 0 65535 0) ltac:(rewrite E405; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E244, unsigned_lit_small by (clear - Hl0 Hlw Hw1 R7; lia); clear - Hl0 Hlw Hw1 R7; lia));
fl_hand RR HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
exists pt, w, h, top, left, (fr_tidx f). cbn [c_s c_ly c_S].
split; [rewrite E402; exact E241|].
split; [rewrite E403; exact E242|].
split; [rewrite E404; exact E243|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E400, sv_denot_SOff0; exact E240|].
split; [rewrite E405; exact E244|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E401, sv_denot_SOff0; rewrite !ew_havoc_old by (clear; lia); exact E58|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|]. split; [clear - Q8; lia|].
destruct Hpt as [(Hp0 & _ & _ & Hk0 & Eab3) | (Hp1 & Hk2 & Htb)]; [left | right].
+ split; [exact Hp0|]. split; [exact Hk0 | exact Eab3].
+ split; [exact Hp1|]. split; [exact Hk2 | exact Htb].
-
hc_bool Hc ltac:(fun H => lazymatch type of H with context [U ?Ev (SExt false 8 (SOff 180 0))] => rewrite (gen_test8 Ev 180 gen 1 ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E180) ltac:(clear - Rgen; lia) ltac:(clear; lia)) in H end).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan 0x883b8.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
clear_frames.
rreg HS (11%bv : bv 5) Ra1. rreg HS (10%bv : bv 5) Ra0. rreg HS (12%bv : bv 5) Ra2. rreg HS (13%bv : bv 5) Ra3. rreg HS (20%bv : bv 5) Rt6.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (fl_pow2 B LAWS 17 0 (fl_npal (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 E0)) W3 (ms_regs msX) (ms_mem msX) mdX
TFLUSH_STK (spZ regs) [(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s + 40, cg_raw s + 44)] ly S W mem md [(1, fpos)] ly3 S3 k eq_refl HJ3);
[ exact Ra1 | exact Ra0 | exact Ra2 | exact Ra3 | rewrite Rt6, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E184
| clear; lia | exact Rnp | right; reflexivity ] end. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & K & -> & HJ5 & HK11 & HK10 & HK14 & HKlo & HKs1 & HKs2 & Hav5 & Hpr5 & Hrg5).
clear Ra1 Ra0 Ra2 Ra3 Rt6.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch HS kk regs5 (mrestrict (w_H W3) mem5) FPOW_CLOB 0x883d0 HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5)) end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv.
lazymatch type of HEv with _ = havoc _ ?kk _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let k1 := eval vm_compute in (Datatypes.S kk) in let k2 := eval vm_compute in (Datatypes.S (Datatypes.S kk)) in
assert (EK0 : ew Ev kk = Z_to_bv 64 K) by (rewrite HEv; unfold FPOW_CLOB; cbn [map]; rewrite (ew_havoc_new _ kk _ 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK10);
assert (EK : ew Ev k1 = Z_to_bv 64 K) by (rewrite HEv; unfold FPOW_CLOB; cbn [map]; rewrite (ew_havoc_new _ kk _ 1 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK11);
assert (EK2 : ew Ev k2 = Z_to_bv 64 (2 ^ K)) by (rewrite HEv; unfold FPOW_CLOB; cbn [map]; rewrite (ew_havoc_new _ kk _ 2 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK14) end end.
clear HEv.
assert (HK2p : 1 <= 2 ^ K <= 65536) by (split; [pose proof (Z.pow_pos_nonneg 2 K); clear - HKlo H; lia | change 65536 with (2 ^ 16); apply Z.pow_le_mono_r; clear - HKlo; lia]).
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
lazymatch type of EK0 with ew _ ?nK0 = _ => lazymatch type of EK with ew _ ?nK = _ => lazymatch type of EK2 with ew _ ?nK2 = _ =>
pose proof (st_ok_add_fact trbsegs Ev ssv msv nK0 (mkAF 0 16 0) HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK0, unsigned_lit_small by (clear - HKlo; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HKlo; lia)) as HS4;
clear HS; pose proof (st_ok_add_fact trbsegs Ev _ msv nK (mkAF 0 16 0) HS4 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK, unsigned_lit_small by (clear - HKlo; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HKlo; lia)) as HS3;
clear HS4; pose proof (st_ok_add_fact trbsegs Ev _ msv nK2 (mkAF 1 65536 0) HS3 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK2, unsigned_lit_small by (clear - HK2p; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - HK2p; lia)) as HS;
clear HS3 end end end end.
norm_ss HS. relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_tok trbtbl_lib_ok HS HJ5 SHOK FLBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
+
aj_run_tok trbtbl_lib_ok HS HJ5 SHOK FLBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
* aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK FLBspan 0x8841c.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
joinT1x RT1.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
exists pt, w, h, top, left. cbn [c_s c_ly c_S]. rewrite !ew_havoc_old by (clear; lia).
split; [exact E241|]. split; [exact E242|]. split; [exact E243|]. split; [exact E240|]. split; [exact E244|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
exact Hpt0.
* aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK FLBspan 0x8841c.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
joinT1x RT1.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
exists pt, w, h, top, left. cbn [c_s c_ly c_S]. rewrite !ew_havoc_old by (clear; lia).
split; [exact E241|]. split; [exact E242|]. split; [exact E243|]. split; [exact E240|]. split; [exact E244|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
exact Hpt0.
+
aj_run_tok trbtbl_lib_ok HS HJ5 SHOK FLBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
* aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK FLBspan 0x8841c.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
joinT1x RT1.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
exists pt, w, h, top, left. cbn [c_s c_ly c_S]. rewrite !ew_havoc_old by (clear; lia).
split; [exact E241|]. split; [exact E242|]. split; [exact E243|]. split; [exact E240|]. split; [exact E244|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
exact Hpt0.
* aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK FLBspan 0x8841c.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
clear_frames.
joinT1x RT1.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; apply fl_bef_havoc; [clear; lia|]; apply fl_bef_havoc; [clear; lia|]; split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
exists pt, w, h, top, left. cbn [c_s c_ly c_S]. rewrite !ew_havoc_old by (clear; lia).
split; [exact E241|]. split; [exact E242|]. split; [exact E243|]. split; [exact E240|]. split; [exact E244|].
split; [exact Hrpt|]. split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
exact Hpt0.
Qed.
Lemma fl_T1 : fl_from B ss_R (INV_R B) -> fl_from B ss_T1x (INV_T0 B) -> fl_from B ss_T0 (INV_T0 B).
Proof. exact fl_T1_aux. Qed.
End d.
End c.
