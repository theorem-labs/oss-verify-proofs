(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC1b YC2u YC4o YC4q YC4h YC27 YC2r YC20 YC16 YC4u YC52 YCaq YCct YCce YCcd YCc6 YCcb YCc9 YCca YCc7 YCc5 YC4z YC50.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0t YG0r YG0q YC00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_G2_aux : forall cnt : Z, rt_from B ss_G3 (INV_G3 B cnt) -> rt_from B ss_G2 (INV_G2 B cnt).
Proof.
intros cnt RG3. rt_prelude.
pose proof HINV as (HBV & Hk & Hc & E400 & HnC & r & N & cur & img & fmt & E147 & E142 & HNmax & E401 & Rcur & E402 & E403 & R1 & R2 & Himg & HOBJ).
cbn [c_n] in HnC, Rcur.
pose proof HOBJ as (g & s & wfn & ctx & path & attr & gen & loops & Wd & Hd & bef & beffmt & cur0 & Hobj & Hat & Hwf & HW & HH & Hbef & HPerm3 & Hown).
cbn [c_ly c_S] in HPerm3, Hown.
pose proof Hwf as (Hlen3 & HW1 & HH1 & HNWH & HNle & _).
assert (HN1 : 1 <= N <= RGB_NMAX) by (split; [clear - HW1 HH1 HNWH; nia | exact HNmax]).
assert (Hown3 : forall x, In x (trgb_own r g s N bef beffmt) -> In x (ablocks B ly3 S3))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; apply in_app_iff; left; exact Hx).
assert (Eopt : timg_block img fmt N = optb img (fmt * N)).
{ unfold timg_block, optb. destruct Himg as [(Hf & Hnz) | (-> & ->)]; [|reflexivity].
replace (tfmt_okb fmt) with true by (destruct Hf as [-> | ->]; reflexivity). destruct (Z.eqb_spec img 0) as [He | _]; [exfalso; exact (Hnz He) | reflexivity]. }
assert (HPermO : Permutation (ablocks B ly3 S3) (optb img (fmt * N) ++ trgb_own r g s N bef beffmt ++ ablocks B ly S))
by (rewrite <- Eopt; eapply Permutation_trans; [exact HPerm3|]; apply Permutation_app_swap_app).
assert (Himg3 : img <> 0 -> In (img, fmt * N) (ablocks B ly3 S3)).
{ intros Hnz. eapply Permutation_in; [apply Permutation_sym; exact HPermO|]. apply in_app_iff. left. unfold optb.
destruct (Z.eqb_spec img 0) as [He | _]; [exfalso; exact (Hnz He) | left; reflexivity]. }
assert (Himgne : img <> 0 -> ~ In (img, fmt * N) (ablocks B ly S)).
{ intros Hnz Hxe. apply (tmp_not_entry B LAWS _ _ _ _ _ (optb img (fmt * N)) (trgb_own r g s N bef beffmt ++ ablocks B ly S) (img, fmt * N) HAR3 HPermO).
- unfold optb. destruct (Z.eqb_spec img 0) as [He | _]; [exfalso; exact (Hnz He) | left; reflexivity].
- apply in_app_iff. right. exact Hxe. }
assert (Hsep : forall b m i, In (b, m) (trgb_own r g s N bef beffmt) -> 0 <= i < req_size m -> ~ (img <> 0 /\ img <= b + i < img + req_size (fmt * N))).
{ intros b m i Hb Hi [Hnz Hx].
assert (Hne : (b, m) <> (img, fmt * N)).
{ intros Ebm. rewrite Ebm in Hb.
apply (tmp_not_entry B LAWS _ _ _ _ _ (optb img (fmt * N)) (trgb_own r g s N bef beffmt ++ ablocks B ly S) (img, fmt * N) HAR3 HPermO).
- unfold optb. destruct (Z.eqb_spec img 0) as [He | _]; [exfalso; exact (Hnz He) | left; reflexivity].
- apply in_app_iff. left. exact Hb. }
pose proof (sep_blocks trasegs _ LAWS ly3 S3 _ _ _ b m img (fmt * N) HAR3 (Hown3 _ Hb) (Himg3 Hnz) Hne) as Hdj. unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. clear - Hdj Hi Hx. lia. }
relowRT HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RTBspan 0x53100.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 HF8hi; lia).
cgif_kept_run HFr Hown3 HJ3 Hfin3 EFA3 AG KA.
clear_frames.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0. rreg HS (@BV 5 10 I) Ra0.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (Ugp : ew Ev 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl));
assert (Utp : ew Ev 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)) end.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x81370) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
assert (Ra0v : getr (ms_regs ms) 10 = w64 img) by (rewrite Ra0; rewrite ?sv_denot_SOff0; ewpeel; exact E402).
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?Wx) ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wx) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview trasegs (w_H Wx) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem trasegs _ _ _ _ Vra Qra) (rdword_of_val_mem trasegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| clear Vra Vs0 ] end.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (HEVc : vev S3 < VEV_MAX).
{ apply (rbv_room_lt S S3 _ _ Hbud HBV); [clear - Hc; unfold RGB_COARSE; lia | clear - Hc; lia]. }
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
assert (HdFP : img <> 0 -> img + req_size (fmt * N) <= F \/ F + 256 <= img).
{ intros Hnz. pose proof (sep_block_frame trasegs _ LAWS ly3 S3 _ _ _ img (fmt * N) 2 fpos HAR3 (Himg3 Hnz) Hfin3) as Q.
unfold zdisjoint in Q; cbn [fst snd] in Q; change (fs_frame_bytes 2) with 256 in Q; rewrite EFA3 in Q. fold F in Q. clear - Q. lia. }
assert (Hihz : img <> 0 -> in_app img (req_size (fmt * N))).
{ intros Hnz. destruct (al_blocks _ _ LAWS _ _ _ _ _ img (fmt * N) HAR3 (Himg3 Hnz)) as (_ & _ & _ & Q3 & _). exact Q3. }
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
eapply (rg_aj_free_optD B LAWS tra_segs_low errno_low ML AFREE W3 Ex ssX msX LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly3 S3 mdX k img (fmt * N) (sp1 - spZ regs) (ew Ex 2) (Z_to_bv 64 0x81370) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0))
(trgb_own r g s N bef beffmt ++ ablocks B ly S) HS) end end.
+ rewrite HBcode. vm_compute. reflexivity.
+ reflexivity.
+ exact HJ3.
+ exact HPermO.
+ exact Ra0v.
+ first [ rewrite Rsp; rewrite ?sv_denot_SOff0; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Usp3; f_equal; clear; lia | match goal with |- ?gg => idtac "FO1" gg end ].
+ reflexivity.
+ exact Usp3.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
+ exact Rra.
+ apply ret_ok_even. vm_compute. reflexivity.
+ exact HEVc.
+ apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
+ replace (pc_free_ra0 (as_code B)) with 0x53244 by (rewrite HBcode; reflexivity). apply (tl_universe B TL).
apply (rt_trace_in 0x53244 0x81370); [exact Hra | exact EraX | split; reflexivity].
+ intros Hnz Hxe. exfalso. exact (Himgne Hnz Hxe). }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPerm4 & Hfrs4 & HBD4 & HK).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra0v Hch1 EspX EraX Es0X Usp3 Ugp Utp.
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(2, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (KF : forall b sz, In (b, sz) (trgb_own r g s N bef beffmt) -> blk_kept (w_H W3) (w_H W4) (ms_mem ms) mem4 b (req_size sz))
by (intros b sz Hb; exact (blk_kept_acall B _ _ _ _ _ _ _ _ _ b sz HK (Hown3 _ Hb) (fun i Hi => Hsep b sz i Hb Hi))).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha [Hnz Hx]; pose proof (Hihz Hnz) as Hih_ia; pose proof (proj1 Hih_ia) as Hih; clear - Ha Hx Hih Hih_ia HF8c HF8lo HFceil C1 C3; unfold SB in *; zone_lia
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha [Hnz Hx]; specialize (HdFP Hnz); clear - Ha Hx HdFP; lia
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact HK | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact HK | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rt_hand RG3 HS.
split; [apply (rbv_mono S S4 ((16 + 3 * (16 - cnt)) + 1) (17 - cnt)); [apply (rbv_coarse_bud S S3 S4 _ _ 1 HBV); [eapply bud_le_mono; [exact HBD4 | clear; lia | clear; lia | clear; lia | unfold HULL_UNIT; clear; lia] | clear; lia] | clear; lia | clear; lia]|].
split; [clear - Hk; lia|]. split; [exact Hc|]. split; [ewpeel; exact E400|]. split; [cbn [c_n]; exact HnC|].
exists r, N, cur. split; [ewpeel; exact E147|]. split; [ewpeel; exact E142|]. split; [exact HNmax|].
split; [ewpeel; exact E401|]. split; [cbn [c_n]; exact Rcur|].
unfold rt_obj. cbn [c_ly c_S]. exists g, s, wfn, ctx, path, attr, gen, loops, Wd, Hd, bef, beffmt, cur0.
split.
{ apply (rg_obj_at_blk_kept (w_H W3) (w_H W4) (ms_mem ms3) mem4 r LAY_Rgb _ RGB_SIZE Hobj lay_inside_Rgb).
assert (Hb : In (r, RGB_SIZE) (trgb_own r g s N bef beffmt)) by (left; reflexivity).
eapply blk_kept_trans; [exact (KA _ _ Hb) | exact (KF _ _ Hb)]. }
split.
{ apply (tcgif_at_blocks_kept (w_H W3) (w_H W4) (ms_mem ms3) mem4 g s N Hat).
intros b sz Hb0. assert (Hb : In (b, sz) (trgb_own r g s N bef beffmt)) by (right; apply in_app_iff; left; exact Hb0).
eapply blk_kept_trans; [exact (KA _ _ Hb) | exact (KF _ _ Hb)]. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact Hbef|]. split; [exact HPerm4|].
intros b Hb. apply Hown. apply in_app_iff. left. exact Hb.
Qed.
Lemma rt_G2 : forall cnt : Z, rt_from B ss_G3 (INV_G3 B cnt) -> rt_from B ss_G2 (INV_G2 B cnt).
Proof. exact rt_G2_aux. Qed.
End d.
End c.
