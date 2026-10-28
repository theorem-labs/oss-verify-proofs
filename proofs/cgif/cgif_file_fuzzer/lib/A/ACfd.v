(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YC20 YC7x YC21 YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI17 YE00 YE01 YE02 YE03 YO08 YI0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACfn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACel ACer ACfm ACf5 ACf9 ACf7 ACf8 ACf6 ACfh ACf4 ACey ACfk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Set Hyps Limit 8. Set Printing Depth 14. Set Printing Width 250.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable POST : rtcx -> rtxc -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Variable XN : xnums.
Variable XL : Z -> Z.
Variable wfn : Z.
Hypothesis AFREE4 : afree04_rule tfibsegs B MT.
Hypothesis AFREEN4 : afree_null04_rule tfibsegs B MT.
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
Hypothesis XApos : forall n, 0 <= n -> 0 <= xn_addframe XN n <= xm_addframe XN n.
Hypothesis XCpos : forall n, 0 <= n -> 0 <= xn_close XN n <= xm_close XN n.
Hypothesis HXL2 : forall cx xc, rt_base B MT cx -> rt_xbase2 B MT XL cx xc -> XROOM MT XN xc (c_T cx).
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_G2X_aux : forall cnt : Z, rt_fromX B MT XL POST ss_G3 (INV_G3X B MT XN wfn cnt) -> rt_fromX B MT XL POST ss_G2 (INV_G2X B MT XN wfn cnt).
Proof.
intros cnt RG3. rt_preludeX.
pose proof HINV as (Hk & Hacc & Hc & E400 & s & cur & lpal & lpa & img & fattr & fgen & delay & nlp & tidx & gs & HOBJ & HSTM & HFC & HREL & HLF).
pose proof HOBJ as (E195 & E194 & Hn14 & Hat & Hwf & HGs & HPerm3). cbn [c_n c_ly c_S] in Hn14, HPerm3. xcb.
pose proof HSTM as (Vp & Vn & Vc & Rcur). cbn [c_n c_sp1 c_p] in Vp, Vn, Vc, Rcur.
pose proof HFC as (E402 & E403 & E404 & E405 & E406 & E407 & E408 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & Hlp0 & Hlpa).
pose proof Hwf as (Hlen3 & HW1 & HH1 & HNWH & HNle & _).
pose proof (mo_malloc_nonneg MT MTL 196605 ltac:(clear; lia)) as Hm1. pose proof (mo_malloc_nonneg MT MTL N ltac:(clear - HN1; lia)) as Hm2.
pose proof (mo_free_nonneg MT MTL) as Hf1. pose proof (XApos N ltac:(clear - HN1; lia)) as HxA. pose proof (XCpos N ltac:(clear - HN1; lia)) as HxC.
assert (HITER : 0 <= ITER MT XN (mkRTXC pl aM Kl G rest0 g f N)) by (unfold ITER, RFC_COST; cbn [x_N]; clear - Hm1 Hm2 Hf1 HxA; lia).
pose proof (proj2 (HXL2 _ _ HBASE0 HXB0)) as HROOM. unfold ACC_H, ACC_F in HROOM. cbn [x_N x_G c_T] in HROOM.
assert (Hcg3 : forall x, In x (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) -> In x (ablocks B ly3 S3)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]. apply in_app_iff in Hx. destruct Hx as [Hx | [<- | []]].
- apply in_app_iff. left. exact Hx.
- apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
assert (Himg3 : In (img, N) (ablocks B ly3 S3))
by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
assert (HPerm3s : Permutation (ablocks B ly3 S3) ((cgif_blocks g s N ++ [(f, FILE_BLOCK)]) ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ ablocks B ly S)).
{ eapply Permutation_trans; [exact HPerm3|]. unfold rt_fblocks. rewrite <- app_assoc. apply Permutation_app_head.
change ((f, FILE_BLOCK) :: ablocks B ly S) with ([(f, FILE_BLOCK)] ++ ablocks B ly S). apply Permutation_app_swap_app. }
assert (Himgne : ~ In (img, N) (ablocks B ly S)).
{ intros Hxe. eapply (ablocks_perm_twice B LAWS _ _ _ _ _ ((cgif_blocks g s N ++ [(f, FILE_BLOCK)]) ++ [(img, N)]) ((if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ ablocks B ly S) (img, N) HAR3).
- eapply Permutation_trans; [exact HPerm3s|]. rewrite <- !app_assoc. cbn [app]. apply Permutation_refl.
- apply in_app_iff. right. left. reflexivity.
- apply in_app_iff. right. exact Hxe. }
assert (Hsep : forall b m i, In (b, m) (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) -> 0 <= i < req_size m -> ~ (img <= b + i < img + req_size N)).
{ intros b m i Hb Hi Hx.
assert (Hne : (b, m) <> (img, N)).
{ intros Ebm. rewrite Ebm in Hb.
eapply (ablocks_perm_twice B LAWS _ _ _ _ _ (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ ablocks B ly S) (img, N) HAR3 HPerm3s Hb).
left. reflexivity. }
pose proof (sep_blocks tfibsegs _ LAWS ly3 S3 _ _ _ b m img N HAR3 (Hcg3 _ Hb) Himg3 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hi Hx. lia. }
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (B70 : bv_unsigned (ew E 70) = sp1) by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia).
assert (B75 : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (HSPB : alloc_ceiling <= spZ regs - LLVMF_STK /\ spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ F <= a < F + 32 \/ F + 80 <= a < F + 256).
reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan.
{ awrRT AG fpos F EFA3. }
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 HF8hi; lia).
cgif_kept_run HFr Hcg3 HJ3 Hfin3 EFA3 AG KA.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img). rename Himgv into HimgvA.
unrunRD HFr Zsm Usp B70 Hsp1 UN1. clear_frames.
vkeepUN UN1 Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UN1.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0. rreg HS (@BV 5 10 I) Ra0.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (Ugp : ew Ev 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl));
assert (Utp : ew Ev 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)) end.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact B70);
assert (EraX : raZ rg = 0x80a3c) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
assert (Ra0v : getr (ms_regs ms) 10 = w64 img) by (rewrite Ra0; rewrite ?sv_denot_SOff0; ewpeel; exact E403).
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?Wx) ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wx) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview tfibsegs (w_H Wx) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| clear Vra Vs0 ] end.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (HEVc : st_nev S3 < EV_MAX) by (rewrite HEV in Hev; clear - Hnev3 Hev Hk Hc; lia).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 338220 with (pc_wrap_free (as_code B)) by (rewrite HBcode; reflexivity).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
pose proof (sep_block_frame tfibsegs _ LAWS ly3 S3 _ _ _ img N 2 fpos HAR3 Himg3 Hfin3) as HdFP.
unfold zdisjoint in HdFP; cbn [fst snd] in HdFP; change (fs_frame_bytes 2) with 256 in HdFP; rewrite EFA3 in HdFP. fold F in HdFP.
destruct (al_blocks _ _ LAWS _ _ _ _ _ img N HAR3 Himg3) as (_ & _ & _ & Hih_ia & _ & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_img _ _ _ _ _ _ img N HAR3 Himg3) as Hih_img.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ (ms_mem ?msX) _) ?mdX) _ =>
assert (HRELc : cgif_relA tfibsegs tfib_K (mrestrict (w_H W3) (ms_mem msX)) mdX s f N (YO07.g_gpal G) gs);
[ eapply (cgif_relA_keptX tfib_K); [| | destruct md3; reflexivity | destruct md3; reflexivity | exact (proj1 HREL)];
[ intros b sz i Hb Hi; apply (mbyte_of_aview tfibsegs); apply (KA b sz Hb); pose proof (le_req_size sz); clear - Hi H; lia
| intros a Ha; apply (mbyte_of_aview tfibsegs); apply HimgvA; exact (proj1 (ail_env _ _ _ AIL a Ha)) ]
| ] end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (afree04_sub tfibsegs B LAWS tfib_segs_low MT AFREE4 W3 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) RTFP ly S W mem md [(2, fpos)]
ly3 S3 mdX k img N (sp1 - spZ regs) (Z_to_bv 64 0x80a3c) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ3 Himg3) end.
+ exact Ra0v.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
+ exact Rra.
+ apply ret_ok_even. vm_compute. reflexivity.
+ exact HEVc.
+ apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
+ replace (pc_free_ra0 (as_code B)) with 0x52a6c by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (rt_trace_in 0x52a6c 0x80a3c); [exact Hra | exact EraX | right; right; left; split; reflexivity].
+ intros Hxe. exfalso. exact (Himgne Hxe).
+
apply (mok_station MT S S3 T acc (mo_free MT) MTL HMOK HMLE); [exact Hf1|].
unfold ACC_G2, ACC_G, ACC_F, ITER, RFC_COST in Hacc, HROOM, HITER |- *; cbn [x_G x_N] in Hacc, HROOM, HITER |- *. clear - Hacc HROOM HITER Hm1 Hm2 Hf1 HxA HxC Hc. nia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Ebl3 & Ebl4) & Hfrs4 & HK & HMLE4 & HJS4).
pose proof (mle_station MT S S3 S4 acc (mo_free MT) MTL HMLE HMLE4) as HMLE4c.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra0v Hch1 EspX EraX Es0X Usp3 Ugp Utp.
assert (HPerm4 : Permutation (ablocks B ly4 S4) ((cgif_blocks g s N ++ [(f, FILE_BLOCK)]) ++ (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ ablocks B ly S)).
{ rewrite Ebl4. apply (@Permutation_app_inv _ l1 l2 (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) ((if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ ablocks B ly S) (img, N)).
rewrite <- Ebl3. exact HPerm3s. }
pose proof (ajournal_closed_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sink_closed_ablocks_fp [(img, N)] ltac:(constructor; [cbn [fst]; destruct (al_blocks _ _ LAWS _ _ _ _ _ img N HAR3 Himg3) as (_ & Hi4096 & _); clear - Hi4096; lia | constructor])) HJS4) as [Efds4 Efs4].
lazymatch type of HRELc with cgif_relA _ _ (mrestrict _ (ms_mem ?msX)) ?mdX _ _ _ _ _ =>
assert (HREL4 : cgif_relA tfibsegs tfib_K (mrestrict (w_H W4) mem4) md4 s f N (YO07.g_gpal G) gs);
[ eapply (cgif_relA_keptX tfib_K); [| | exact Efds4 | exact Efs4 | exact HRELc];
[ intros b sz i Hb Hi; apply (mbyte_of_aview tfibsegs); apply (proj1 (proj2 HK) b sz i (Hcg3 _ Hb)); [pose proof (le_req_size sz); clear - Hi H; lia | exact (Hsep b sz i Hb ltac:(pose proof (le_req_size sz); clear - Hi H; lia))]
| intros a Ha; apply (mbyte_of_aview tfibsegs); destruct (ail_env _ _ _ AIL a Ha) as (Hi & Hns & He); exact (proj1 (proj2 (proj2 HK)) a Hi Hns He) ]
| ] end.
clear HRELc HJS4.
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(2, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (KF : forall b sz, In (b, sz) (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) -> blk_kept (w_H W3) (w_H W4) (ms_mem ms) mem4 b (req_size sz))
by (intros b sz Hb; exact (blk_kept_acall B _ _ _ _ _ _ _ _ _ b sz HK (Hcg3 _ Hb) (fun i Hi => Hsep b sz i Hb Hi))).
assert (Hcg4 : forall x, In x (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) -> In x (ablocks B ly4 S4))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; apply in_app_iff; left; exact Hx).
vkeep Vp (w_H W4) mem4 ltac:(apply (proj1 HK); [clear - Hi Hsp1 HSPB C1 FFS; lia | clear - Hi Hsp1; lia]).
vkeep Vn (w_H W4) mem4 ltac:(apply (proj1 HK); [clear - Hi Hsp1 HSPB C1 FFS; lia | clear - Hi Hsp1; lia]).
vkeep Vc (w_H W4) mem4 ltac:(apply (proj1 HK); [clear - Hi Hsp1 HSPB C1 FFS; lia | clear - Hi Hsp1; lia]).
reseatL HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hx; clear - Ha Hx Hih Hih_ia HF8c HF8lo HFceil C1 C3; unfold SB in *; zone_lia
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hx; clear - Ha Hx HdFP; lia
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ4 SHOK RTBspan.
{ awrRT AG fpos F EFA4. }
clear HUP.
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wq ?mq _ _ =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H Wq) mq a = aview tfibsegs (w_H W) mem a)
by (intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia) end.
cgif_kept_run HFr Hcg4 HJ4 Hfin4 EFA4 AG KB.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img). rename Himgv into HimgvB.
unrunRD HFr Zsm Usp B70 Hsp1 UN2. clear_frames.
vkeepUN UN2 Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UN2.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0. rreg HS (@BV 5 10 I) Ra0.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (Ugp : ew Ev 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl));
assert (Utp : ew Ev 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)) end.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact B70);
assert (EraX : raZ rg = 0x80a44) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
assert (Ra0v : getr (ms_regs ms0) 10 = w64 lpal) by (rewrite Ra0; rewrite ?sv_denot_SOff0; ewpeel; exact E402).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?Wx) ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wx) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly4 (aview tfibsegs (w_H Wx) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ4)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| clear Vra Vs0 ] end.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _).
assert (HEVd : st_nev S4 < EV_MAX) by (rewrite HEV in Hev; clear - Hnev4 Hev Hk Hc; lia).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 338220 with (pc_wrap_free (as_code B)) by (rewrite HBcode; reflexivity).
clear Kgot3 Kcell3 Kguar3 Kuar3 Kgot4 Kcell4 Kguar4 Kuar4. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ (ms_mem ?msX) _) ?mdX) _ =>
assert (HRELd : cgif_relA tfibsegs tfib_K (mrestrict (w_H W4) (ms_mem msX)) mdX s f N (YO07.g_gpal G) gs);
[ eapply (cgif_relA_keptX tfib_K); [| | destruct md4; reflexivity | destruct md4; reflexivity | exact HREL4];
[ intros b sz i Hb Hi; apply (mbyte_of_aview tfibsegs); apply (KB b sz Hb); pose proof (le_req_size sz); clear - Hi H; lia
| intros a Ha; apply (mbyte_of_aview tfibsegs); apply HimgvB; exact (proj1 (ail_env _ _ _ AIL a Ha)) ]
| ] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
apply (SRr_bind tfibsegs _ _
(fun W5 c5 => exists ly5 S5 regs5 mem5 md5,
c5 = mkCfg (mkst regs5 (Z_to_bv 64 0x80a44) mem5 (seg_rom tfibsegs)) md5 /\
ajournal tfibsegs B LLVMF_STK (spZ regs) RTFP ly S W mem md [(2, fpos)] ly5 S5 W5 mem5 md5 (k + 1 + 1) /\
aregs_preserved (ms_regs msX) regs5 /\ Permutation (ablocks B ly5 S5) ((cgif_blocks g s N ++ [(f, FILE_BLOCK)]) ++ ablocks B ly S) /\ frames S5 = frames S4 /\
(exists Er : Z -> Prop, acall_kept tfibsegs B ly4 S4 W4 (ms_mem msX) W5 mem5 (sp1 - ASTACK) sp1 Er /\
(forall a, F <= a < F + 256 -> ~ Er a) /\ (forall a, SB <= a < 17594333495296 -> ~ Er a) /\
(forall b m i, In (b, m) (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) -> 0 <= i < req_size m -> ~ Er (b + i))) /\
cgif_relA tfibsegs tfib_K (mrestrict (w_H W5) mem5) md5 s f N (YO07.g_gpal G) gs /\ mo_le MT S S5 (acc + mo_free MT + mo_free MT))) end.
{ destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hfa0 | Hfa1].
-
pose proof (Hlp0 Hfa0) as Hlpal0.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (afree_null04_sub tfibsegs B LAWS tfib_segs_low MT AFREEN4 W4 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) RTFP ly S W mem md [(2, fpos)]
ly4 S4 mdX (k + 1) (sp1 - spZ regs) (Z_to_bv 64 0x80a44) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ4)
| ] end.
+ rewrite Ra0v, Hlpal0. reflexivity.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
+ exact Rra.
+ apply ret_ok_even. vm_compute. reflexivity.
+ exact HEVd.
+ apply (achain_chain_pre ly4 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
+ replace (pc_free_ra0 (as_code B)) with 0x52a6c by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (rt_trace_in 0x52a6c 0x80a44); [exact Hra | exact EraX | right; right; right; left; split; reflexivity].
+   apply (mok_station MT S S4 T (acc + mo_free MT) (mo_free MT) MTL HMOK HMLE4c); [exact Hf1|].
unfold ACC_G2, ACC_G, ACC_F, ITER, RFC_COST in Hacc, HROOM, HITER |- *; cbn [x_G x_N] in Hacc, HROOM, HITER |- *. clear - Hacc HROOM HITER Hm1 Hm2 Hf1 HxA HxC Hc. nia.
+ cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HPerm5 & Hfrs5 & HK5 & HMLE5 & HJS5).
exists ly5, S5, regs5, mem5, md5. split; [reflexivity|]. split; [replace (k + 1 + 1) with (k + 1 + 1) by reflexivity; exact HJ5|]. split; [exact HP5|].
split; [eapply Permutation_trans; [exact HPerm5|]; rewrite app_nil_l in HPerm4 || idtac; exact HPerm4|]. split; [exact Hfrs5|].
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK5 by (clear; lia).
split; [exists (fun _ => False); split; [exact HK5|]; repeat split; intros; exact (fun HF : False => HF)|].
destruct (ajournal_nil_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJS5) as [Efds5 Efs5].
split; [|exact (mle_station MT S S4 S5 (acc + mo_free MT) (mo_free MT) MTL HMLE4c HMLE5)].
eapply (cgif_relA_keptX tfib_K); [| | exact Efds5 | exact Efs5 | exact HRELd].
* intros b sz i Hb Hi. apply (mbyte_of_aview tfibsegs). apply (proj1 (proj2 HK5) b sz i (Hcg4 _ Hb)); [pose proof (le_req_size sz); clear - Hi H; lia | exact (fun HF : False => HF)].
* intros a Ha. apply (mbyte_of_aview tfibsegs). destruct (ail_env _ _ _ AIL a Ha) as (Hi & Hns & He). exact (proj1 (proj2 (proj2 HK5)) a Hi Hns He).
-
assert (Hlp4 : In (lpa, 3 * nlp) (ablocks B ly4 S4))
by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
assert (Hlpne : ~ In (lpa, 3 * nlp) (ablocks B ly S)).
{ intros Hxe. eapply (ablocks_perm_twice B LAWS _ _ _ _ _ ((cgif_blocks g s N ++ [(f, FILE_BLOCK)]) ++ [(lpa, 3 * nlp)]) (ablocks B ly S) (lpa, 3 * nlp) (proj1 HJ4)).
- rewrite <- app_assoc. exact HPerm4.
- apply in_app_iff. right. left. reflexivity.
- exact Hxe. }
assert (Hsep2 : forall b m i, In (b, m) (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) -> 0 <= i < req_size m -> ~ (lpa <= b + i < lpa + req_size (3 * nlp))).
{ intros b m i Hb Hi Hx.
assert (Hne : (b, m) <> (lpa, 3 * nlp)).
{ intros Ebm. rewrite Ebm in Hb.
eapply (ablocks_perm_twice B LAWS _ _ _ _ _ (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) ([(lpa, 3 * nlp)] ++ ablocks B ly S) (lpa, 3 * nlp) (proj1 HJ4) HPerm4 Hb).
left. reflexivity. }
pose proof (sep_blocks tfibsegs _ LAWS ly4 S4 _ _ _ b m lpa (3 * nlp) (proj1 HJ4) (Hcg4 _ Hb) Hlp4 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hi Hx. lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ lpa (3 * nlp) (proj1 HJ4) Hlp4) as (_ & _ & _ & Hlh_ia & _ & _). pose proof (proj1 Hlh_ia) as Hlh.
pose proof (sep_block_frame tfibsegs _ LAWS ly4 S4 _ _ _ lpa (3 * nlp) 2 fpos (proj1 HJ4) Hlp4 Hfin4) as HdFL.
unfold zdisjoint in HdFL; cbn [fst snd] in HdFL; change (fs_frame_bytes 2) with 256 in HdFL; rewrite EFA4 in HdFL. fold F in HdFL.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (afree04_sub tfibsegs B LAWS tfib_segs_low MT AFREE4 W4 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) RTFP ly S W mem md [(2, fpos)]
ly4 S4 mdX (k + 1) lpa (3 * nlp) (sp1 - spZ regs) (Z_to_bv 64 0x80a44) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ4 Hlp4)
| ] end.
+ rewrite Ra0v. unfold w64. rewrite <- Hlpa. reflexivity.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
+ exact Rra.
+ apply ret_ok_even. vm_compute. reflexivity.
+ exact HEVd.
+ apply (achain_chain_pre ly4 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
+ replace (pc_free_ra0 (as_code B)) with 0x52a6c by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (rt_trace_in 0x52a6c 0x80a44); [exact Hra | exact EraX | right; right; right; left; split; reflexivity].
+ intros Hxe. exfalso. exact (Hlpne Hxe).
+   apply (mok_station MT S S4 T (acc + mo_free MT) (mo_free MT) MTL HMOK HMLE4c); [exact Hf1|].
unfold ACC_G2, ACC_G, ACC_F, ITER, RFC_COST in Hacc, HROOM, HITER |- *; cbn [x_G x_N] in Hacc, HROOM, HITER |- *. clear - Hacc HROOM HITER Hm1 Hm2 Hf1 HxA HxC Hc. nia.
+ cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (l1' & l2' & Ebl4' & Ebl5) & Hfrs5 & HK5 & HMLE5 & HJS5).
exists ly5, S5, regs5, mem5, md5. split; [reflexivity|]. split; [exact HJ5|]. split; [exact HP5|].
split.
{ rewrite Ebl5. apply (@Permutation_app_inv _ l1' l2' (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) (ablocks B ly S) (lpa, 3 * nlp)). rewrite <- Ebl4'. exact HPerm4. }
split; [exact Hfrs5|].
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK5 by (clear; lia).
split.
{ exists (fun a => lpa <= a < lpa + req_size (3 * nlp)). split; [exact HK5|].
split; [intros a Ha Hx; clear - Ha Hx HdFL; lia|]. split; [intros a Ha Hx; clear - Ha Hx Hlh_ia C3; unfold SB in *; zone_lia|]. exact Hsep2. }
destruct (ajournal_closed_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sink_closed_ablocks_fp [(lpa, 3 * nlp)] ltac:(constructor; [cbn [fst]; destruct (al_blocks _ _ LAWS _ _ _ _ _ lpa (3 * nlp) (proj1 HJ4) Hlp4) as (_ & Hl4096 & _); clear - Hl4096; lia | constructor])) HJS5) as [Efds5 Efs5].
split; [|exact (mle_station MT S S4 S5 (acc + mo_free MT) (mo_free MT) MTL HMLE4c HMLE5)].
eapply (cgif_relA_keptX tfib_K); [| | exact Efds5 | exact Efs5 | exact HRELd].
* intros b sz i Hb Hi. apply (mbyte_of_aview tfibsegs). apply (proj1 (proj2 HK5) b sz i (Hcg4 _ Hb)); [pose proof (le_req_size sz); clear - Hi H; lia | exact (Hsep2 b sz i Hb ltac:(pose proof (le_req_size sz); clear - Hi H; lia))].
* intros a Ha. apply (mbyte_of_aview tfibsegs). destruct (ail_env _ _ _ AIL a Ha) as (Hi & Hns & He). exact (proj1 (proj2 (proj2 HK5)) a Hi Hns He). }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HPerm5 & Hfrs5 & (Er & HK5 & HErF & HErLo & HErB) & HREL5 & HMLE5c).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra0v Hch1 EspX EraX Es0X.
pose proof (proj1 HJ5) as HAR5.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly5 HAR (proj1 (proj2 HJ5))) as (_ & EFA5 & _).
assert (Hfin5 : In (2, fpos) (frames S5)) by (rewrite Hfrs5; exact Hfin4).
assert (Hfrs5' : frames S5 = [(2, fpos)]) by (rewrite Hfrs5; exact Hfrs4').
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR5 Hfin5) as (_ & _ & HFpres5 & HFSpres5).
change (fs_frame_bytes 2) with 256 in HFpres5, HFSpres5. change (256 / 8) with 32 in HFSpres5. rewrite !EFA5 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5.
assert (KF2 : forall b sz, In (b, sz) (cgif_blocks g s N ++ [(f, FILE_BLOCK)]) -> blk_kept (w_H W4) (w_H W5) (ms_mem ms0) mem5 b (req_size sz))
by (intros b sz Hb; exact (blk_kept_acall B _ _ _ _ _ _ _ _ _ b sz HK5 (Hcg4 _ Hb) (fun i Hi => HErB b sz i Hb Hi))).
vkeep Vp (w_H W5) mem5 ltac:(apply (proj1 HK5); [clear - Hi Hsp1 HSPB C1 FFS; lia | clear - Hi Hsp1; lia]).
vkeep Vn (w_H W5) mem5 ltac:(apply (proj1 HK5); [clear - Hi Hsp1 HSPB C1 FFS; lia | clear - Hi Hsp1; lia]).
vkeep Vc (w_H W5) mem5 ltac:(apply (proj1 HK5); [clear - Hi Hsp1 HSPB C1 FFS; lia | clear - Hi Hsp1; lia]).
reseatL HS HJ5 HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK5 | evalE AG | exact Hfin4
| right; unfold shadow_addr; rewrite EFA4, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hx; exact (HErLo a ltac:(clear - Ha HF8c HF8lo HFceil C1; unfold SB in *; lia) Hx)
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK5 | evalE AG | exact Hfin4
| left; rewrite EFA4; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hx; exact (HErF a ltac:(clear - Ha; lia) Hx)
| intros a Ha; apply (proj1 (HFpres5 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK5 | exact HJ5 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot4 | exact Kgot5 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell4 | exact Kcell5 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar4 | exact Kguar5 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar4 | exact Kuar5 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
ra_join_win HS ss_G3 500%nat rt_G_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. rt_handX RG3 HS.
split; [clear - Hk; lia|].
split; [unfold ACC_G3, ACC_G2, ACC_G, ACC_F, ITER, RFC_COST in *; cbn [x_G x_N] in *; clear - Hacc Hc; nia|].
split; [exact Hc|]. split; [exact E400|].
exists s, cur, gs.
split.
{ unfold rt_objX. cbn [c_n c_ly c_S x_gp x_N x_f x_G].
split; [exact E195|]. split; [exact E194|]. split; [exact Hn14|].
split.
{ lazymatch goal with |- xcgif_at _ _ _ _ _ (mrestrict (w_H ?Wf) ?mf) _ _ => apply (xcgif_at_blocks_kept wfn _ _ _ (w_H W3) (w_H Wf) (ms_mem ms3) mf g s N Hat) end.
intros b sz Hb. assert (Hb' : In (b, sz) (cgif_blocks g s N ++ [(f, FILE_BLOCK)])) by (apply in_app_iff; left; exact Hb).
eapply blk_kept_trans; [exact (KA b sz Hb')|]. eapply blk_kept_trans; [exact (KF b sz Hb')|].
eapply blk_kept_trans; [exact (KB b sz Hb') | exact (KF2 b sz Hb')]. }
split; [exact Hwf|]. split; [exact HGs|]. cbn [app]. rewrite <- app_assoc in HPerm5. exact HPerm5. }
split.
{ unfold rt_stm. cbn [c_sp1 c_p c_n]. split; [exact Vp|]. split; [exact Vn|]. split; [exact Vc | exact Rcur]. }
split; [|exact HLF].
split; [exact HREL5|]. pose proof (proj2 HREL) as HLEN. cbn [x_N x_G] in *. clear - HLEN. lia.
Qed.
Lemma rt_G2X : forall cnt : Z, rt_fromX B MT XL POST ss_G3 (INV_G3X B MT XN wfn cnt) -> rt_fromX B MT XL POST ss_G2 (INV_G2X B MT XN wfn cnt).
Proof. exact rt_G2X_aux. Qed.
End d.
End c.
