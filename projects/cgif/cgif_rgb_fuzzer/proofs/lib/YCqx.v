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
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCfx YChv YChx YChn YCf6 YCft YCey YCe4 YCi1 YCie YCph YCpi YCrr YCrd YCrc YCr3 YCr9 YCr7 YCr8 YCr4 YCr2 YCib YCra YCr5.
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
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis TRGBADD : trgb_addframe_specV B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_G1_aux : forall cnt : Z, rt_fromA B ss_G2 (fun _ => INV_G2 B cnt) -> rt_from B ss_G (INV_G B cnt).
Proof.
intros cnt RG2. rt_prelude.
pose proof HINV as (HBV & Hk & Hc & E400 & HnC & r & N & cur & img & fmt & E147 & E142 & HNmax & E401 & Rcur & E402 & E403 & R1 & R2 & Himg & HOBJ). unfold rt_RGB in E147.
cbn [c_n] in HnC, Rcur.
pose proof HOBJ as (g & s & wfn & ctx & path & attr & gen & loops & Wd & Hd & bef & beffmt & cur0 & Hobj & Hat & Hwf & HW & HH & Hbef & HPerm3 & Hown).
cbn [c_ly c_S] in HPerm3, Hown.
pose proof Hwf as (Hlen3 & HW1 & HH1 & HNWH & HNle & _).
assert (HN1 : 1 <= N <= RGB_NMAX) by (split; [clear - HW1 HH1 HNWH; nia | exact HNmax]).
destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hn0 HnC; lia|].
assert (Hown3 : forall x, In x (trgb_own r g s N bef beffmt) -> In x (ablocks B ly3 S3))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; apply in_app_iff; left; exact Hx).
assert (Hownne : forall x, In x (trgb_own r g s N bef beffmt) -> ~ In x (ablocks B ly S)).
{ intros x Hx Hxe. apply (tmp_not_entry B LAWS _ _ _ _ _ _ _ x HAR3 HPerm3 Hx). apply in_app_iff. right. exact Hxe. }
relowRT HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RTBspan A_cgif_rgb_addframe.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
upd_aboveF2 HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 HF8hi; lia).
cgif_kept_run HFr Hown3 HJ3 Hfin3 EFA3 AG KA.
clear_frames.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0.
rreg HS (@BV 5 10 I) Ra0. rreg HS (@BV 5 11 I) Ra1.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
assert (UF : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (U70 : bv_unsigned (ew E 70) = sp1) by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact U70);
assert (EraX : raZ rg = 0x814c8) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
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
assert (Hch1 : achain ly3 (aview trbsegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem trbsegs _ _ _ _ Vra Qra) (rdword_of_val_mem trbsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iF := idx_of_base_off rs 75%nat 112 in let iF := eval vm_compute in iF in
let rF := eval vm_compute in (nth iF rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iF rF HS ltac:(vm_compute; reflexivity)) as HRF; cbn [ms_mem restrict] in HRF end.
Ltac fieldF HRF UF od w e V :=
lazymatch type of HRF with region_ok _ ?Ex _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region_any Ex _ 75 _ cs lo hi wlo whi od w e HRF UF ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
cbn [sv_denot] in V; rewrite ?ew_ewset_other, ?ew_havoc_old in V by nat_side;
try change (N.to_nat 8) with 8%nat in V; try change (N.to_nat 4) with 4%nat in V; try change (N.to_nat 2) with 2%nat in V; try change (N.to_nat 1) with 1%nat in V;
try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V; try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V;
try change (2 ^ (8 * Z.of_N 2)) with 65536 in V; try change (2 ^ (8 * Z.of_N 1)) with 256 in V end.
fieldF HRF UF 112 8%N (SOff 1002 0) V1. fieldF HRF UF 120 4%N (SOff 1003 0) V2.
rewrite (denot_atom_mod _ 1002 img _ E402 R1), Z.mod_small in V1 by (exact R1).
rewrite (denot_atom_mod _ 1003 fmt _ E403 ltac:(clear - R2; lia)), Z.mod_small in V2 by (exact R2).
clear HRF.
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ3) Hfin3) as (_ & _ & HFpN & _);
change (fs_frame_bytes 2) with 256 in HFpN; rewrite !EFA3 in HFpN; fold F in HFpN;
assert (PM : forall a, F <= a < F + 256 -> exists b, mbyte trbsegs (mrestrict (w_H Wx) (ms_mem msX)) a = Some b)
by (intros a Ha; destruct (proj1 (HFpN a Ha)) as [Hh [b Hb]]; exists b; unfold mbyte, mrestrict; rewrite Hh, Hb; reflexivity);
destruct (val_mem_of_present4 trbsegs (mrestrict (w_H Wx) (ms_mem msX)) (F + 124) ltac:(intros i Hi; apply PM; clear - Hi; lia)) as (fattr & R3 & V3);
destruct (val_mem_of_present4 trbsegs (mrestrict (w_H Wx) (ms_mem msX)) (F + 128) ltac:(intros i Hi; apply PM; clear - Hi; lia)) as (fgen & R4 & V4);
destruct (rt_val_mem_byte2 (w_H Wx) (ms_mem msX) (F + 132) (proj1 (HFpN (F + 132) ltac:(clear; lia))) (proj1 (HFpN (F + 132 + 1) ltac:(clear; lia)))) as (delay & R5 & V5);
assert (OcfgX : obj_at trbsegs (mrestrict (w_H Wx) (ms_mem msX)) (F + 112) LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay]) end.
{ cbn [obj_at LAY_RgbFrameConfig]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N Pos.to_nat].
rewrite <- !Z.add_assoc. cbn [Z.add Pos.add].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536.
split; [split; [first [rewrite Z.add_0_r; exact V1 | exact V1] | exact R1]|]. split; [split; [exact V2 | exact R2]|]. split; [split; [exact V3 | exact R3]|].
split; [split; [exact V4 | exact R4]|]. split; [split; [exact V5 | exact R5]|]. exact I. }
clear V1 V2 V3 V4 V5 PM HFpN.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iS := idx_of_base rs 88%nat in let iS := eval vm_compute in iS in
let rS := eval vm_compute in (nth iS rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iS rS HS ltac:(vm_compute; reflexivity)) as HRS; cbn [ms_mem restrict] in HRS;
assert (US : bv_unsigned (ew E 88) = SB + F / 8) by (rewrite E88; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia);
assert (ZS : forall od, In (YQ0b.mkChunk od (CVal 1 (SLit 0))) (YQ0b.r_chunks rS) -> aview trbsegs (w_H W3) (ms_mem msX) (SB + F / 8 + od) = Some 0);
[ let od := fresh "od" in let Hod := fresh "Hod" in intros od Hod;
lazymatch type of HRS with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 88 (SB + F / 8) cs lo hi wlo whi od 1%N (SLit 0) 0 HRS US Hod eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Vz end;
pose proof (Vz 0%nat ltac:(lia)) as Vz0; cbn [Z.of_nat] in Vz0; rewrite Z.add_0_r in Vz0;
unfold aview; rewrite Vz0; reflexivity
| clear HRS ] end.
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (AF : afobj B ly3 S3 Wx (ms_mem msX) (F + 112) RGBFC_SIZE) end.
{ change RGBFC_SIZE with 24. split; [|split].
- exists 2, fpos. split; [exact Hfin3|]. split; [clear; lia|]. rewrite EFA3. fold F. split; [rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); apply Z_mod_mult|].
change (fs_frame_bytes 2) with 256. clear; lia.
- rewrite HFq. replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by (clear; lia). apply Z_mod_mult.
- apply zero_shadow_of_bytes; [rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by (clear; lia); apply Z_mod_mult | reflexivity | clear; lia |].
intros j Hj. change (24 / 8) with 3 in Hj. rewrite <- SB_SHADOW_OFF.
replace ((F + 112) / 8) with (F / 8 + 14) by (rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia);
replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia); clear; lia).
replace (SB + (F / 8 + 14) + j) with (SB + F / 8 + (14 + j)) by (clear; lia).
assert (Hj4 : j = 0 \/ j = 1 \/ j = 2) by (clear - Hj; lia).
destruct Hj4 as [-> | [-> | ->]]; apply ZS; cbn; tauto. }
clear ZS.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _).
assert (HEVc : bud_ok S3 EV_FRAMEV CN_FRAME WT_FRAME HL_FRAME).
{ apply (rbv_room_frame S S3 _ _ Hbud HBV); [clear - Hc; unfold RGB_COARSE; lia | clear - Hc; lia]. }
assert (HOWNB : bsum (trgb_own r g s N bef beffmt) <= RGB_SIZE + CGB + 4 * RGB_NMAX).
{ unfold trgb_own. cbn [bsum fold_right snd]. rewrite bsum_app. pose proof (cgif_blocks_bsum _ g s N Hat Hwf) as Hcb.
assert (bsum (optb bef (beffmt * N)) <= 4 * RGB_NMAX).
{ unfold optb. destruct (bef =? 0) eqn:Eb; [cbn; unfold RGB_NMAX; clear; lia|]. cbn [bsum fold_right snd].
destruct Hbef as [-> | [-> | ->]]; [discriminate Eb | |]; clear - HN1; lia. }
clear - Hcb H. lia. }
assert (HIMGB : bsum (timg_block img fmt N) <= 4 * RGB_NMAX).
{ unfold timg_block. destruct Himg as [([-> | ->] & _) | (-> & _)]; [change (tfmt_okb 3) with true | change (tfmt_okb 4) with true | change (tfmt_okb 0) with false]; cbn [bsum fold_right snd]; clear - HN1; unfold RGB_NMAX in *; lia. }
assert (HLIVEc : blocks_bytes S3 + LIVE_RGBADD <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPerm3), !bsum_app, <- (blocks_bytes_bsum B ly S).
unfold LIVE_LIB in Hlive. unfold LIVE_RGBADD, CGB, RGB_SIZE, RGB_NMAX in *. clear - Hlive HOWNB HIMGB. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_callF B LAWS W3 Ex ssX msX LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)] ly3 S3 mdX k
TRGBADD_STK (ablocks_fp (trgb_own r g s N bef beffmt)) EV_RGBADD (sp1 - spZ regs) (ew Ex 2) (Z_to_bv 64 0x814c8) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0))
(fun ly2 S2 W2 regs2 mem2 md2 => exists (s' : cgif_st) (bef' beffmt' cur' : Z),
obj_at trbsegs (mrestrict (w_H W2) mem2) r LAY_Rgb [g; wfn; ctx; path; attr; gen; loops; Wd; Hd; bef'; beffmt'; cur'] /\
tcgif_at (mrestrict (w_H W2) mem2) g s' /\ cgif_wf s' N /\
cg_W s' = Wd /\ cg_H s' = Hd /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
(bef' = 0 \/ beffmt' = 3 \/ beffmt' = 4) /\
Permutation (ablocks B ly2 S2) (trgb_own r g s' N bef' beffmt' ++ timg_block img fmt N ++ ablocks B ly S) /\
(forall b, In b (trgb_own r g s' N bef' beffmt') ->
aftok (ablocks_fp (trgb_own r g s N bef beffmt)) (ablocks B ly3 S3) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TRGBADD_STK (spZ (ms_regs msX)) (ablocks_fp (trgb_own r g s N bef beffmt)) (ablocks B ly3 S3) blc ly2 [] (fst b + i)) /\
bud_le S3 S2 EV_FRAMEV CN_FRAME WT_FRAME HL_FRAME) HS eq_refl HJ3);
[ first [ rewrite Rsp; rewrite ?sv_denot_SOff0; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Usp3; f_equal; clear; lia | match goal with |- ?gg => idtac "AJ1" gg end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ exact Usp3 | idtac "AJ3" ]
| first [ rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity | match goal with |- ?gg => idtac "AJ4" gg end ]
| first [ clear - Hsp1; lia | idtac "AJ5" ]
| first [ apply Zle_bool_imp_le; vm_compute; reflexivity | idtac "AJ6" ]
| first [ assert (TRGBADD_STK + 176 <= LLVMF_STK) by (vm_compute; discriminate); clear - Hsp1 H; lia | match goal with |- ?gg => idtac "AJ7" gg end ]
| first [ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Ugp; exact Hgp | idtac "AJ8" ]
| first [ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Utp; exact Htp | idtac "AJ9" ]
| first [ exact Rra | idtac "AJ10" ]
| first [ apply ret_ok_even; vm_compute; reflexivity | idtac "AJ11" ]
| first [ rewrite unsigned_lit_small by (clear; lia); clear; lia | idtac "AJ12" ]
| first [ rewrite Es0X; replace (spZ regs + (sp1 - spZ regs)) with sp1 by (clear; lia); exact Hch1 | match goal with |- ?gg => idtac "AJ13" gg end ]
| first [ intros HPRE1; eapply SRr_mono;
[ first [ pose proof (TRGBADD ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0))
r (F + 112) g wfn ctx path attr gen loops Wd Hd bef beffmt cur0 s N img fmt fattr fgen delay (ablocks B ly S) HPRE1) as CALL | idtac "CALL-POSE" ];
unfold cfg_at, trgb_addframe_postV, apost_baseF in CALL; cbn [ss_pc]; change (w64 A_cgif_rgb_addframe) with (Z_to_bv 64 532040) in CALL;
first [ apply CALL | match goal with |- ?gg => idtac "CALL-APPLY" gg end; let t := type of CALL in idtac "CALL-TYPE" t ]; clear CALL;
[ first [ rewrite EspX; exact Hsp1al | idtac "CA1" ]
| first [ rewrite EraX; apply rt_ctx_in; [exact Hra | vm_compute; tauto | vm_compute; tauto] | match goal with |- ?gg => idtac "CA2" gg end ]
| first [ rewrite Hfrs3; cbn [length]; clear; lia | idtac "CA3" ]
| first [ rewrite EspX; pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); rewrite LT; clear - Hsp1 Htop; lia | match goal with |- ?g => idtac "CA3b" g end ]
| first [ eapply arodata_ok_journal; [exact HJ3 | exact HROD] | idtac "CA4" ]
| first [ exact HFZ | idtac "CA4b" ]
| first [ rewrite Ra0; rewrite ?sv_denot_SOff0; ewpeel; exact E147 | match goal with |- ?gg => idtac "CA5" gg end ]
| first [ rewrite Ra1, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite UF; reflexivity | match goal with |- ?gg => idtac "CA6" gg end ]
| first [ exact AF | idtac "CA7" ]
| first [ exact OcfgX | match goal with |- ?gg => idtac "CA8" gg end ]
| first [ apply (rg_obj_at_blk_kept _ _ _ _ r LAY_Rgb _ RGB_SIZE Hobj lay_inside_Rgb); exact (KA r RGB_SIZE ltac:(left; reflexivity)) | match goal with |- ?gg => idtac "CA8b" gg end ]
| first [ apply (tcgif_at_blocks_kept _ _ _ _ g s N Hat); intros b sz Hb; apply KA; right; apply in_app_iff; left; exact Hb | match goal with |- ?gg => idtac "CA9" gg end ]
| first [ exact Hwf | match goal with |- ?gg => idtac "CA10" gg end ]
| first [ exact HW | idtac "CA10b" ] | first [ exact HH | idtac "CA10c" ] | first [ exact HNmax | idtac "CA10d" ]
| first [ exact Hbef | match goal with |- ?gg => idtac "CA11" gg end ]
| first [ exact HPerm3 | match goal with |- ?gg => idtac "CA12" gg end ]
| first [ exact HEVc | match goal with |- ?gg => idtac "CA21" gg end ]
| first [ exact HLIVEc | match goal with |- ?gg => idtac "CA22" gg end ] ]
| first [ cbv beta; intros W4 c4 _ (fx' & ly4 & S4 & regs4 & mem4 & md4 & -> & HFZ' & HJc & HPc & Hpost);
exists fx', ly4, S4, regs4, mem4, md4; split; [rewrite Rra; reflexivity|]; split; [exact HFZ'|]; split; [exact HJc|];
split; [exact HPc|]; exact Hpost | match goal with |- ?g => idtac "CALL-POST" g end ] ]
| idtac "AJ14" ]
| first [ intros a Ha; right; destruct (inFP_ablocks_fp_inv _ a Ha) as (pb & nb & Hpb & Hab); exists pb, nb;
split; [exact (Hown3 _ Hpb) | split; [exact (Hownne _ Hpb) | exact Hab]]
| match goal with |- ?g => idtac "AJ15" g end ] ]
| ] end end.
cbv beta. intros W4 c4 Hwle4 (fx' & ly4 & S4 & regs4 & mem4 & md4 & -> & HFZ' & HJ4 & HJc & HP4 & s' & bef' & beffmt' & cur' & Hobj4 & Hat4 & Hwf4 & HW4 & HH4 & Hattr4 & Hraw4 & Hbef4 & HPerm4 & Hown4 & HBD4).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HJc by (clear; lia).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra1 Vra Vs0 Hch1 OcfgX AF EspX EraX Es0X.
pose proof (proj1 HJ4) as HAR4.
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs4 & _). cbn [app] in Hfrs4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(2, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (HnFPF : forall a, F <= a < F + 256 -> ~ inFP (ablocks_fp (trgb_own r g s N bef beffmt)) a).
{ intros a Ha Hin. destruct (inFP_ablocks_fp_inv _ a Hin) as (pb & nb & Hpb & Hab).
pose proof (sep_block_frame trbsegs _ LAWS ly3 S3 _ _ _ pb nb 2 fpos HAR3 (Hown3 _ Hpb) Hfin3) as Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. change (fs_frame_bytes 2) with 256 in Hdj. rewrite EFA3 in Hdj. fold F in Hdj. clear - Ha Hab Hdj. lia. }
assert (HnFPlo : forall a, SB <= a < 17594333495296 -> ~ inFP (ablocks_fp (trgb_own r g s N bef beffmt)) a).
{ intros a Ha Hin. destruct (inFP_ablocks_fp_inv _ a Hin) as (pb & nb & Hpb & Hab).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HAR3 (Hown3 _ Hpb)) as (_ & _ & _ & Hbh_ia & _). pose proof (proj1 Hbh_ia) as Hbh. clear - Ha Hab Hbh_ia C3. unfold SB in *. zone_lia. }
assert (HnFPhi : forall a, alloc_ceiling <= a -> ~ inFP (ablocks_fp (trgb_own r g s N bef beffmt)) a).
{ intros a Ha Hin. destruct (inFP_ablocks_fp_inv _ a Hin) as (pb & nb & Hpb & Hab).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HAR3 (Hown3 _ Hpb)) as (_ & _ & Hbc & _). clear - Ha Hab Hbc. lia. }
lazymatch type of HS with st_ok _ _ ?ssx _ => let l := eval vm_compute in (seq 0 (length (ss_mem ssx))) in
reseat HS HJ4 HP4 l AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFPlo; clear - Ha HF8c HF8lo HFceil C1; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFPF; clear - Ha; lia | intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub trbsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 70%nat); [exact HJc | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub trbsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJc | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]) end.
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
lazymatch goal with |- SRr _ ?W3x (mkCfg (@mkst ?fxp ?rg ?pcv ?mm ?romv) ?md3x) (rt_post _ ?cxv) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (RG2 fxp cxv Ev _ _ _ W3x (@mkst fxp rg pcv mm romv) md3x);
[ exact HBASE0
| repeat (lazymatch goal with |- rt_E _ (havoc _ _ _) => apply rt_E_havoc; [clear; cbn; lia|] | |- rt_E _ (ewset _ _ _) => apply rt_E_ewset; [clear; cbn; lia|] end);
unfold rt_E, rt_F, rt_FL; cbn [c_ly c_fpos c_E0 c_sp1];
split; [assumption|]; repeat (split; [eassumption|]); eassumption
| exact HFZ'
| first [exact HJ4 | cbn [ms_mem mkst]; exact HJ4 | idtac "HAND-J"]
| first [exact Hfrs4' | idtac "HAND-F"]
| red; cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0]
| apply (st_ok_to_fx fx fxp); exact HS ] end end.
split; [apply (rbv_mono S S4 (16 + 3 * (16 - cnt)) ((16 - cnt) + 1)); [exact (rbv_frame S S3 S4 _ _ HBV HBD4) | clear; lia | clear; lia]|].
split; [clear - Hk; lia|]. split; [exact Hc|]. split; [ewpeel; exact E400|]. split; [exact HnC|].
exists r, N, cur, img, fmt.
split; [ewpeel; exact E147|]. split; [ewpeel; exact E142|]. split; [exact HNmax|].
split; [ewpeel; exact E401|]. split; [exact Rcur|].
split; [ewpeel; exact E402|]. split; [ewpeel; exact E403|]. split; [exact R1|]. split; [exact R2|]. split; [exact Himg|].
unfold rt_objI. exists g, s', wfn, ctx, path, attr, gen, loops, Wd, Hd, bef', beffmt', cur'.
split; [exact Hobj4|]. split; [exact Hat4|]. split; [exact Hwf4|]. split; [exact HW4|]. split; [exact HH4|]. split; [exact Hbef4|].
split; [exact HPerm4|].
intros b Hb Hbe. exfalso. apply in_app_iff in Hb as [Hb | Hb].
- apply (tmp_not_entry B LAWS _ _ _ _ _ _ _ b HAR4 HPerm4 Hb). apply in_app_iff. right. exact Hbe.
- rewrite app_assoc in HPerm3. apply (tmp_not_entry B LAWS _ _ _ _ _ _ _ b HAR3 HPerm3 ltac:(apply in_app_iff; right; exact Hb) Hbe).
Qed.
Lemma rt_G1 : forall cnt : Z, rt_fromA B ss_G2 (fun _ => INV_G2 B cnt) -> rt_from B ss_G (INV_G B cnt).
Proof. exact rt_G1_aux. Qed.
End d.
End c.
