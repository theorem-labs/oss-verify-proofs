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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCgl YCfu YCft YCfx YCex YCrb YCez YCev YCf6 YCf2 YCf7 YCet YCf3 YCf4 YCey YCf5 YCf0 YCf8 YCfp YCeu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac nat_side := first [ apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (Nat.eqb_neq _ _)); vm_compute; reflexivity
| cbn [length Nat.add]; apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity ].
Lemma denot_and_ffff : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v <= 65535 ->
sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 65535)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn), U_SLit by lia.
change (zcanon 65535) with (Z.ones 16). rewrite Z.land_ones by lia. change (2 ^ 16) with 65536. rewrite (Z.mod_small v) by lia.
apply zcanon_id. rewrite M64_val. lia.
Qed.
Ltac add_atom_win HS n w En :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win trbsegs n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
Ltac ra_join_win HS target N deads hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem trbsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win trbsegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 trbsegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
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
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma w_st_ok_add_chunk : forall E ss ms l1 nb lo hi wlo whi cs l2 c,
st_ok trbsegs E ss ms -> ss_mem ss = l1 ++ YQ0b.mkRegion nb lo hi wlo whi cs :: l2 ->
regions_wf (l1 ++ YQ0b.mkRegion nb lo hi wlo whi (c :: cs) :: l2) = true ->
YQ0b.chunk_ok trbsegs E (ms_mem ms) (base_val E nb) c ->
st_ok trbsegs E (mkSS (ss_pc ss) (ss_regs ss) (l1 ++ YQ0b.mkRegion nb lo hi wlo whi (c :: cs) :: l2) (ss_resv ss) (ss_facts ss)) ms.
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
Section m.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Ltac upd_aboveF HUP HFr AG ltac :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; ltac Hb Hrg|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Ltac add_fact HS n lo hi Hv tac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_fact trbsegs Ev ssx msx n (mkAF lo hi 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Hv, unsigned_lit_small by tac; rewrite Z.pow_0_r, Z.mod_1_r; split; [tac | split; [reflexivity | clear; lia]])) as HS3;
clear HS; rename HS3 into HS end.
Ltac seat152 HS na top E70 Ena V152 sptac ttac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 70%nat in let il := eval vm_compute in il in
let l1 := eval vm_compute in (firstn il rs) in
let rt := eval vm_compute in (nth il rs got_region) in
let l2 := eval vm_compute in (skipn (S il) rs) in
lazymatch rt with YQ0b.mkRegion ?nb ?lo ?hi ?wlo ?whi ?cs =>
let HS3 := fresh "HS3" in
pose proof (w_st_ok_add_chunk Ev ssx msv l1 nb lo hi wlo whi cs l2 (YQ0b.mkChunk 152 (CVal 8 (SOff na 0))) HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(cbn [base_val]; rewrite ?ew_havoc_old by nat_side; rewrite E70, unsigned_lit_small by sptac;
apply (chunk_ok_val trbsegs Ev _ _ 152 8 _ top);
[ cbn [sv_denot]; rewrite Ena, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn [Z.of_N Z.mul]; ttac | cbn; lia | exact V152 ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end end.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Ltac ws_pin HS r e Hr dtac :=
let HS3 := fresh "HS3" in
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv r e HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Hr; cbn [sv_denot]; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Lemma fl_D_aux : fl_from B ss_X (INV_X B) -> fl_from B ss_T0 (INV_T0 B) -> fl_from B ss_DIMS (INV_DIMS B).
Proof.
intros RX RT0. fl_prelude.
pose proof HINV as (Hk3 & Eab3 & (gen & E180 & Rgen) & E184 & (fb & Hfb & EB) & (w & h & top & left & E420 & E421 & E422 & V152 & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth)).
cbn [c_i c_s] in Hfb. cbn [c_s] in Hlw, Hth. cbn [c_sp1] in V152.
pose proof (EB 0%nat _ eq_refl) as E210. pose proof (EB 1%nat _ eq_refl) as E211. pose proof (EB 2%nat _ eq_refl) as E212.
pose proof (EB 3%nat _ eq_refl) as E213. pose proof (EB 4%nat _ eq_refl) as E214. pose proof (EB 5%nat _ eq_refl) as E215.
pose proof (EB 6%nat _ eq_refl) as E216. pose proof (EB 7%nat _ eq_refl) as E217. pose proof (EB 8%nat _ eq_refl) as E218.
cbn [Nat.add] in E210, E211, E212, E213, E214, E215, E216, E217, E218.
rewrite Hfb in E12. cbn [frame_ptr] in E12.
assert (HW65 : cg_W s <= 65535) by (clear - R7; lia).
assert (HH65 : cg_H s <= 65535) by (clear - R8; lia).
assert (Hw65 : w <= 65535) by (clear - Hw1 Hl0 Hlw HW65; lia). assert (Hh65 : h <= 65535) by (clear - Hh1 Ht0 Hth HH65; lia).
assert (Hwh1 : 1 <= w * h) by (clear - Hw1 Hh1; nia).
assert (HwhN : w * h <= N) by (rewrite HN; clear - Hw1 Hh1 Hl0 Hlw Ht0 Hth; nia).
assert (HWH : 1 <= w * h <= 100000000) by (clear - Hwh1 HwhN HNle; lia).
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
destruct (fl_bef_blocks B ly S g s N rest fb HPerm Hfbi) as (Hbef_in & Hbimg_in & Hblpal).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR Hbef_in) as (Hb16 & Hb4096 & Hbceil & [Hbh1 Hbh2] & _ & _). change (req_size FRAME_SIZE) with 40 in Hbceil, Hbh2.
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hcur_in).
assert (Himg3 : In (fr_img f, N) (ablocks B ly3 S3)) by (rewrite Eab3; exact Himg_in).
assert (Hbef3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hbef_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
add_fact HS 420%nat 1 65535 E420 ltac:(clear - Hw1 Hw65; lia).
add_fact HS 421%nat 1 65535 E421 ltac:(clear - Hh1 Hh65; lia).
add_fact HS 422%nat 0 65535 E422 ltac:(clear - Hw1 Hl0 Hlw HW65; lia).
norm_ss HS.
add_atom HS 446%nat (Z_to_bv 64 top) E446. add_fact HS 446%nat 0 65535 E446 ltac:(clear - Hh1 Ht0 Hth HH65; lia).
seat152 HS 446%nat top E70 E446 V152 ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia) ltac:(clear - Hh1 Ht0 Hth HH65; lia).
rebase_goal.
lazymatch goal with AGx : forall n, (n < 33)%nat -> ew ?Ecur n = _ |- _ => rename E into Eentry; rename Ecur into E end.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan 0x88260.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia). clear_frames.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 26 I) (Z_to_bv 64 w) (denot_and_ffff Ev 420 w ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E420) ltac:(clear - Hw1 Hw65; lia)) R23;
rreg_by HS (@BV 5 10 I) (Z_to_bv 64 h) (denot_and_ffff Ev 421 h ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E421) ltac:(clear - Hh1 Hh65; lia)) R18 end.
ws_pin HS (@BV 5 26 I) (SOff 420 0) R23 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E420).
ws_pin HS (@BV 5 10 I) (SOff 421 0) R18 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E421).
clear R23 R18. reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK FLBspan 0x533c8.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia). clear_frames.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x88268) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (@BV 5 10 I) (Z_to_bv 64 (h * w))
(denot_mul_hw Ev 421 420 h w ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E421) ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E420)
ltac:(clear - Hh1 Hh65; lia) ltac:(clear - Hw1 Hw65; lia)) Ra0 end.
replace (h * w) with (w * h) in Ra0 by (apply Z.mul_comm).
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview trbsegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem trbsegs _ _ _ _ Vra Qra) (rdword_of_val_mem trbsegs _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Htop32; lia) ltac:(clear - Hsp1; lia))
| ] end.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres3' & _).
assert (HEVc : vev S3 < VEV_MAX) by (rewrite HEV in Hev; clear - Hnev3 Hev Hk3; lia).
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340936 with (pc_wrap_malloc (as_code B)) by (rewrite HBcode; reflexivity).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_malloc_at trbsegs B LAWS trb_segs_low errno_low ML AMALLOC W3 (ms_regs msX) (ms_mem msX) TFLUSH_STK (spZ regs) _ ly S W mem md [(1, fpos)]
ly3 S3 mdX k (w * h) (sp1 - spZ regs) (Z_to_bv 64 0x88268) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ra0.
- unfold MALLOC_MAX. clear - HWH. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S). unfold LIVE_FLUSH in Hlive. clear - Hlive HWH. lia.
- rewrite EspX. clear; lia.
- rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
- clear - Hsp1; lia.
- rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
- rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
- rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
- exact Rra.
- apply ret_ok_even. vm_compute. reflexivity.
- exact HEVc.
- apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
- replace (pc_malloc_ra0 (as_code B)) with 0x53668 by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (fl_trace_in 0x53668 0x88268); [exact Hctx | exact EraX | right; left; split; reflexivity]. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hres by (clear; lia).
pose proof (proj1 HJ4) as HAR4.
clear HUP. assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W4) mem4 a = aview trbsegs (w_H W) mem a)
by (intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (1, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4. change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
destruct Hres as [(Hres0 & Eab4 & HK) | (Hres4096 & Eab4 & HK)].
+
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; exact Hing3).
assert (Hcur4 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; exact Hcur3).
assert (Hbef4 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; exact Hbef3).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trbsegs _); [exact HK | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear; lia); rewrite E12; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia
| exact Hbef3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; unfold SB; clear; lia
| intros a Ha Hn; exact Hn
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear; lia
| intros a Ha Hn; exact Hn
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trbsegs _); [exact HK | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trbsegs _); [exact HK | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trbsegs _); [exact HK | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs B LAWS); [exact HK | exact HAR4 | exact Hcur4 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; exact Hn ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rewrite Hres0 in Ha04.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pin_reg' trbsegs Ev ssv msv (@BV 5 10 I) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha04; reflexivity) eq_refl) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS. reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK FLBspan 0x887a4.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA4.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
rreg HS (@BV 5 19 I) Q19;
ra_join HS ss_X 520%nat fl_X_deads_bv ltac:(idtac; ra_join_val HS 520%nat 0%nat Q19 E520); fl_hand RX HS end.
split; [rewrite HEV; clear - Hk3; lia|].
split; [exists 2; split; [exact E520 | clear; lia]|].
cbn [c_ly c_S]. rewrite Eab4, Eab3. apply Permutation_refl.
+
assert (Hrq : req_size (w * h) = w * h) by (unfold req_size; destruct (Z.eqb_spec (w * h) 0); [exfalso; clear - HWH e; lia | reflexivity]).
assert (HrqN : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0); [exfalso; clear - HWH HwhN e; lia | reflexivity]).
assert (Hres_in : In (res, w * h) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hing3).
assert (Hcur4 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hcur3).
assert (Hbef4 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hbef3).
assert (Himg4 : In (fr_img f, N) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Himg3).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (w * h) HAR4 Hres_in) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph. rewrite Hrq in Hpceil, Hppres.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR4 Hres_in) as Hph_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N HAR4 Himg4) as (_ & _ & _ & _ & Hipres4 & _). rewrite HrqN in Hipres4.
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (w * h) HJ3 HAR4 Eab4 ltac:(clear - HWH; lia)) as Tres.
assert (Ares : forall blc lyq ownq i, In (res, w * h) blc -> 0 <= i < w * h ->
awr_byte TFLUSH_STK (spZ regs) [(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s + 40, cg_raw s + 44)] (ablocks B ly S) blc lyq ownq (res + i)).
{ intros blc lyq ownq ii Hbl Hiq. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (w * h) blc ii lyq ownq HJ3 HAR4 Eab4 ltac:(clear - HWH; lia) Hbl ltac:(rewrite Hrq; exact Hiq)). }
assert (HPerm4 : Permutation (ablocks B ly4 S4) (ablocks B ly S ++ [(res, w * h)])) by (rewrite Eab4, Eab3; apply Permutation_refl).
pose proof (sep_block_frame trbsegs B LAWS ly4 S4 _ _ _ res (w * h) 1 fpos HAR4 Hres_in Hfin4) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. rewrite Hrq in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA4 in HdPF. fold F in HdPF.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res (w * h) g CGIF_SIZE HAR4 HPerm4 Hing) as HdPG. change (req_size CGIF_SIZE) with 96 in HdPG. rewrite Hrq in HdPG.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res (w * h) (fr_ptr f) FRAME_SIZE HAR4 HPerm4 Hcur_in) as HdPC. change (req_size FRAME_SIZE) with 40 in HdPC. rewrite Hrq in HdPC.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res (w * h) (fr_ptr fb) FRAME_SIZE HAR4 HPerm4 Hbef_in) as HdPB. change (req_size FRAME_SIZE) with 40 in HdPB. rewrite Hrq in HdPB.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ res (w * h) (fr_img f) N HAR4 HPerm4 Himg_in) as HdPI. rewrite Hrq, HrqN in HdPI.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trbsegs _); [exact HK | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear; lia); rewrite E12; apply unsigned_lit_small; clear - Hbh1 Hbh2 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia
| exact Hbef3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPB Hrq; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; unfold SB; clear; lia
| intros a Ha Hn; clear - Ha Hn Hph Hph_ia Hrq HF8lo HF8c HFceil C1 C3; ceil; unfold SB in *; zone_lia
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trbsegs _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear; lia
| intros a Ha Hn; clear - Ha Hn HdPF Hrq; lia
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trbsegs _); [exact HK | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trbsegs _); [exact HK | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trbsegs _); [exact HK | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPG Hrq; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs B LAWS); [exact HK | exact HAR4 | exact Hcur4 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPC Hrq; lia ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rreg HS (@BV 5 10 I) Rres. rewrite Ha04 in Rres. symmetry in Rres.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ nx (HPTR 4) HS
ltac:(clear HS; unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rres; unfold w64; rewrite unsigned_lit_small by (clear - Hph Hpceil HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia);
change (2 ^ 4) with 16; clear - Hph Hpceil Hp16 HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK FLBspan 0x882bc.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA4.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia). clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HSx : st_ok _ _ _ _ |- _ => rename HSx into HS end.
rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 9 I) Rs1.
rreg HS (@BV 5 18 I) R18. rreg HS (@BV 5 19 I) R19. rreg HS (@BV 5 25 I) R25. rreg HS (@BV 5 26 I) R26. rreg HS (@BV 5 27 I) R27.
rewrite E420 in R26. rewrite E40 in R27. rewrite E70 in Rs1. unfold w64 in Rres.
lazymatch type of Rres with ew ?Ev ?nx = _ =>
assert (UN : U Ev (SAlu ALU_XOR (SOff nx 0) (SLit (-1))) = cplp res)
by (rewrite (U_not_gen Ev _ res (U_atom Ev nx res Rres ltac:(clear - Hph Hpceil HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia))
ltac:(clear - Hph Hpceil HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia)); unfold NMAX, cplp; reflexivity);
assert (UT : U Ev (SMd M_MUL (SAlu ALU_AND (SOff 446 0) (SLit 65535)) (SOff 40 0)) = top * cg_W s)
by (apply U_mul_small1; [apply U_and16; [apply (U_atom Ev 446 top E446); clear - Ht0 Hth Hh1 HH65; lia | clear - Ht0 Hth Hh1 HH65; lia]
| apply (U_atom Ev 40 (cg_W s) E40); clear - HW1 HW65; lia | exact Ht0 | clear - HW1; lia | clear - Ht0 Hth Hh1 HH65 HW1 HW65; nia]);
rreg_by HS (@BV 5 20 I) (Z_to_bv 64 (cplp res)) (denot_of_U2 Ev _ _ UN) R20;
rreg_by HS (@BV 5 21 I) (Z_to_bv 64 w) (denot_and_ffff Ev 420 w E420 ltac:(clear - Hw1 Hw65; lia)) R21;
rreg_by HS (@BV 5 22 I) (Z_to_bv 64 left) (denot_and_ffff Ev 422 left E422 ltac:(clear - Hl0 Hlw Hw1 HW65; lia)) R22;
rreg_by HS (@BV 5 23 I) (Z_to_bv 64 h) (denot_and_ffff Ev 421 h E421 ltac:(clear - Hh1 Hh65; lia)) R23;
rreg_by HS (@BV 5 24 I) (Z_to_bv 64 (top * cg_W s)) (denot_of_U2 Ev _ _ UT) R24 end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 70%nat in let il := eval vm_compute in il in
let rl := eval vm_compute in (nth il rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W4) msX) il rl HS ltac:(vm_compute; reflexivity)) as HRloc; cbn [ms_mem restrict] in HRloc;
lazymatch type of HRloc with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch type of Rres with ew _ ?nx = _ =>
let slot off e v dtac rtac Hn :=
pose proof (field_of_region Ex _ 70 sp1 cs lo hi wlo whi off 8%N e v HRloc
ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia)
ltac:(cbn; tauto) ltac:(dtac) ltac:(rtac) ltac:(cbn; lia)) as Hn in
slot 160 (SOff nx 0) res ltac:(cbn [sv_denot]; rewrite Rres, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; clear - Hph Hpceil HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) V160;
slot 168 (SOff 51 0) (fr_img f) ltac:(cbn [sv_denot]; rewrite E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; rewrite HrqN in Hiceil; clear - Hi4096 Hiceil C1 HWH HwhN; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) V168 end end;
clear HRloc end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V160, V168.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspL : spZ rg = sp1) by (unfold spZ; rewrite Rsp; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia) end.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (fl_cpy B LAWS AMEMCPY (Z.to_nat h) 0 W4 (ms_regs msX) (ms_mem msX) mdX (spZ regs) sp1 _ ly S W mem md ly4 S4 _ fpos
res (fr_img f) N w h top left (cg_W s) (cg_H s)) end.
- rewrite Z2Nat.id by (clear - Hh1; lia). clear; lia.
- clear - Hh1; lia.
- exact Hw1. - exact Hl0. - exact Hlw. - exact Hh1. - exact Ht0. - exact Hth.
- clear - HW1 HW65; lia. - exact HH65. - symmetry; exact HN. - exact HNle.
- exact HJ4.
- exact Hres_in. - exact Himg4.
- intros blc lyq ownq a Hbl Ha. replace a with (res + (a - res)) by (clear; lia). apply (Ares blc lyq ownq (a - res) Hbl). clear - Ha; lia.
- rewrite Hrq, HrqN. clear - HdPI; lia.
- exact EspL. - exact Hsp1. - exact Hsp1al16.
- exact Rs1.
- rewrite Rgp. rewrite (AG 3%nat) by (clear; lia). rewrite (EE 3%nat (@BV 5 3 I) eq_refl). exact Hgp.
- rewrite Rtp. rewrite (AG 4%nat) by (clear; lia). rewrite (EE 4%nat (@BV 5 4 I) eq_refl). exact Htp.
- first [exact R18 | rewrite R18; reflexivity | match goal with |- ?g => idtac "CPY-18" g end].
- first [exact R19 | rewrite R19; reflexivity | match goal with |- ?g => idtac "CPY-19" g end].
- exact R20.
- exact R21. - exact R22. - exact R23.
- rewrite R24. f_equal. clear; lia.
- first [exact R25 | rewrite R25; reflexivity | match goal with |- ?g => idtac "CPY-25" g end].
- exact R26. - exact R27.
- exact V160. - exact V168. }
cbv beta. intros W5 c5 Hwle5 (-> & regs5 & mem5 & md5 & -> & HJ5 & HK5 & Hout5 & Hpres5).
clear Rsp Rgp Rtp Rs1 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 EspL UN UT V160 V168.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
jafter_stretch_keep HS kk regs5 (mrestrict (w_H W4) mem5) CPY_CLOB 0x88314 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat HS2;
lazymatch type of HS2 with _ -> Forall _ ?rs -> _ =>
assert (HRK : Forall (fun r => 0 <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= res \/ res + w * h <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r) /\
(base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= sp1 - ESTACK \/ sp1 <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r)) rs);
[ repeat apply Forall_cons; try apply Forall_nil; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite ?RF, ?E70, ?E88; rewrite ?(AG 2%nat), ?(AG 10%nat), ?(AG 11%nat), ?(AG 12%nat), ?(AG 32%nat) by lia; rewrite ?Usp, ?E10, ?E11, ?E12, ?E32;
rewrite ?unsigned_lit_small by (unfold SB; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 C1 C3 HFceil HFhigh HF8lo HF8hi Hgh Hgceil Hcrh Hcceil Hbh1 Hbh2; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zone_lia);
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, CGIF_SIZE, FRAME_SIZE, SB, ESTACK;
clear - HFceil HFhigh HF8lo HF8hi HF8c Hceil Hslo Hstk0 Hshi H47 Hsp1 Hgh Hgceil Hcrh Hcceil Hbh1 Hbh2 Hbceil C1 C2 C3 C4 C5 FFS Hp4096 Hph Hph_img Hph_ia Hrq Hpceil HWH HdPG HdPC HdPB HdPF;
unbox; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; first [zone_lia | match goal with |- ?g => idtac "HRK-FAIL" g; fail end]
| specialize (HS2 HK5 (regions_kept_out2 Ev (w_H W4) (ms_mem msX) mem5 res (res + w * h) (sp1 - ESTACK) sp1 _ Hout5 Hpres5 HRK)) ] end end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv. clear HEv.
lazymatch type of HUP with forall a, _ -> aview _ _ ?m4 a = _ =>
assert (HUP5 : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W4) mem5 a = aview trbsegs (w_H W) mem a)
by (intros a Ha; rewrite (Hout5 a); [apply HUP; exact Ha | clear - Ha Hbot Hslo Hceil Hstk0 C1 FFS; lia | clear - Ha Hpceil HWH C1 Hceil Hslo Hstk0 FFS; lia | clear - Ha Hsp1; unfold ESTACK; lia]) end.
clear HUP. rename HUP5 into HUP.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
clear Kgot4 Kcell4 Kguar4 Kuar4. aconstsF HJ5 Kgot4 Kcell4 Kguar4 Kuar4.
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK FLBspan 0x8838c.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA4.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _, AG0 : forall n, (n < 33)%nat -> _ |- _ => let HEv0 := fresh "HEv" in rebaseE HS0 AG0 HEv0; clear HEv0 end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
rreg HS (24%bv : bv 5) QXp; rreg HS (21%bv : bv 5) QXw; rreg HS (23%bv : bv 5) QXh; rreg HS (22%bv : bv 5) QXl; rreg HS (6%bv : bv 5) QXt;
rewrite Rres in QXp; rewrite E420 in QXw; rewrite E421 in QXh; rewrite E422 in QXl; rewrite E446 in QXt;
add_atom_win HS 240%nat (Z_to_bv 64 top) E240 end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ws_pin HS (6%bv : bv 5) (SOff 240 0) QXt ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E240) end.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join_win HS ss_T0 241%nat fl_T0_deads_bv ltac:(idtac;
ra_join_val HS 241%nat 0%nat QXp E241; ra_join_val HS 241%nat 1%nat QXw E242; ra_join_val HS 241%nat 2%nat QXh E243; ra_join_val HS 241%nat 3%nat QXl E244;
ra_join_fact HS 240%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear; lia); rewrite E240; rewrite Z.pow_0_r, Z.mod_1_r, unsigned_lit_small by (clear - Ht0 Hth Hh1 HH65; lia); clear - Ht0 Hth Hh1 HH65; lia);
ra_join_fact HS 242%nat (mkAF 1 65535 0) ltac:(rewrite E242; rewrite Z.pow_0_r, Z.mod_1_r, unsigned_lit_small by (clear - Hw1 Hw65; lia); clear - Hw1 Hw65; lia);
ra_join_fact HS 243%nat (mkAF 1 65535 0) ltac:(rewrite E243; rewrite Z.pow_0_r, Z.mod_1_r, unsigned_lit_small by (clear - Hh1 Hh65; lia); clear - Hh1 Hh65; lia);
ra_join_fact HS 244%nat (mkAF 0 65535 0) ltac:(rewrite E244; rewrite Z.pow_0_r, Z.mod_1_r, unsigned_lit_small by (clear - Hl0 Hlw Hw1 HW65; lia); clear - Hl0 Hlw Hw1 HW65; lia));
fl_hand RT0 HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear; lia); assumption|].
split; [exists fb; repeat (apply fl_bef_havoc; [clear; lia|]); split; [exact Hfb|]; cbn [c_i c_s]; bef_EB|].
exists res, w, h, top, left. cbn [c_s c_ly c_S c_regs c_f].
split; [rewrite E241; reflexivity|].
split; [rewrite E242; reflexivity|].
split; [rewrite E243; reflexivity|].
split; [rewrite !ew_havoc_old by (clear; lia); rewrite E240; reflexivity|].
split; [rewrite E244; reflexivity|].
split; [clear - Hph Hpceil HWH C1 C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia|].
split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
right. split; [clear - Hph C3; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia|]. split; [first [clear - Hk3; lia | match goal with |- ?g => idtac "KGOAL" g end]|].
unfold fl_tmpblk, fl_FP. cbn [c_ly c_S c_regs c_f c_s].
split; [split; [exact Hph | rewrite <- Hrq; exact (zone2_of_app _ _ Hph_ia Hph_img)]|]. split; [clear - Hpceil HWH C1; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia|]. split; [exact Hp16|].
split; [first [rewrite Eab4, Eab3; reflexivity | match goal with |- ?g => idtac "D-ABL" g end]|].
split; [exact Ares | exact Tres].
Qed.
Lemma fl_D : fl_from B ss_X (INV_X B) -> fl_from B ss_T0 (INV_T0 B) -> fl_from B ss_DIMS (INV_DIMS B).
Proof. exact fl_D_aux. Qed.
End m.
End d.
