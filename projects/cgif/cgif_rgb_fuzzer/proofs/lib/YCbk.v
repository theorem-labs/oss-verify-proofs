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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas.
Ltac rga_cbn_cx H :=
cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_r c_cfp c_g c_wfn c_ctx c_path c_attr c_gen c_loops c_Wd c_Hd c_bef c_beffmt c_cur c_s c_N
c_img c_fmt c_fattr c_fgen c_delay c_rest c_cid c_pos c_fpos c_E0] in H.
Ltac rga_cbn_cx_goal :=
cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_r c_cfp c_g c_wfn c_ctx c_path c_attr c_gen c_loops c_Wd c_Hd c_bef c_beffmt c_cur c_s c_N
c_img c_fmt c_fattr c_fgen c_delay c_rest c_cid c_pos c_fpos c_E0].
Ltac rga_prelude :=
let LAWS := rnLAWS in let TL := rnTL in let FFL := rnFFL in
let B := lazymatch goal with L : AR_laws trasegs ?Bv |- _ => Bv end in
let cx := fresh "cx" in
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEE Hfrm HJ3 Hfrs3 HINV HS;
destruct cx as [ly S W regs mem md ch r cfp g wfn ctx path attr gen loops Wd Hd bef beffmt cur s N img fmt fattr fgen delay rest cid pos fpos E0];
pose proof HBASE as HBASE0; pose proof HEE as HEE0;
unfold rga_base in HBASE; unfold rga_E in HEE; red in HINV; unfold rgc_vals, rgc_FP, rgc_FPs, rga_F, rga_FL in HBASE, HEE, HJ3;
rga_cbn_cx HBASE; rga_cbn_cx HEE; rga_cbn_cx HJ3; rga_cbn_cx Hfrs3; rga_cbn_cx HINV;
destruct HBASE as (HPRE & Hal32 & Hctx & Hroom & Htop32 & HROD & H10 & H11 & (Hfin & Hcid0 & Hfal & Hflo & Hfhi & Hcal & HRA) & Hcfg & Hrgb & Hcg & Hwf
& HcW & HcH & HN & Hbef & HPerm & Hev & Hlive & EE & EX & Usp);
destruct HEE as (AG & EXE & RF & E66 & E67);
pose proof Hwx_tfa as Hwx; pose proof tra_segs_low as Hsegs;
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : TRGBADD_STK = 25088) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
assert (E10 : ew E0 10 = Z_to_bv 64 r) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10);
assert (E11 : ew E0 11 = Z_to_bv 64 cfp) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11);
assert (E2 : ew E0 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl));
pose proof (EX 0%nat ltac:(lia)) as E32;
pose proof (EXE 1%nat ltac:(lia)) as E33; pose proof (EXE 2%nat ltac:(lia)) as E34; pose proof (EXE 3%nat ltac:(lia)) as E35;
pose proof (EXE 4%nat ltac:(lia)) as E36; pose proof (EXE 5%nat ltac:(lia)) as E37; pose proof (EXE 6%nat ltac:(lia)) as E38;
pose proof (EXE 7%nat ltac:(lia)) as E39; pose proof (EXE 8%nat ltac:(lia)) as E40; pose proof (EXE 9%nat ltac:(lia)) as E41;
pose proof (EXE 10%nat ltac:(lia)) as E42; pose proof (EXE 11%nat ltac:(lia)) as E43; pose proof (EXE 12%nat ltac:(lia)) as E44;
pose proof (EXE 13%nat ltac:(lia)) as E45; pose proof (EXE 14%nat ltac:(lia)) as E46; pose proof (EXE 15%nat ltac:(lia)) as E47;
pose proof (EXE 16%nat ltac:(lia)) as E48; pose proof (EXE 17%nat ltac:(lia)) as E49;
cbn [Nat.add nth rga_vals] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49; clear EXE;
assert (Hrin : In (r, RGB_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity);
destruct (al_blocks _ _ LAWS ly S W mem md r RGB_SIZE HAR Hrin) as (Hr16 & Hr4096 & Hrceil & [Hrh Hrapp] & Hrpres & _);
pose proof (blk_off_img _ _ _ _ _ _ r RGB_SIZE HAR Hrin) as Hrh_img;
change (req_size RGB_SIZE) with 64 in Hrceil, Hrpres, Hrh, Hrapp, Hrh_img; unfold RGB_SIZE in Hrin;
gboxh Hrapp; gboxh Hrh_img;
lazymatch type of HJ3 with ajournal _ _ _ _ ?FPv _ _ _ _ _ _ _ _ _ _ _ _ =>
assert (Ar : forall blc (lyq : alayout) (ownq : list (Z * Z)) i, In (r, 64) blc -> 0 <= i < 64 ->
awr_byte TRGBADD_STK (spZ regs) FPv (ablocks B ly S) blc lyq ownq (r + i))
by (let blc := fresh "blc" in let lyq := fresh "lyq" in let ownq := fresh "ownq" in let i := fresh "i" in let Hb := fresh "Hb" in let Hi := fresh "Hi" in
intros blc lyq ownq i Hb Hi; right; left; split;
[ apply (inFP_ablocks_fp _ r RGB_SIZE); [left; reflexivity | change (req_size RGB_SIZE) with 64; exact Hi]
| exists r, 64; split; [exact Hb | change (req_size 64) with 64; lia] ]) end;
destruct (frames_bounds trasegs _ LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
gboxh Hfhigh; gboxh Hfhigh_img;
pose proof (proj1 HJ3) as HAR3;
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _);
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia);
assert (Hfin3 : In (7, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity);
assert (HfinS3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hfin);
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3);
destruct (frames_bounds trasegs _ LAWS _ _ _ _ _ 7 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img;
destruct (FFL ly3 S3 W3 (ms_mem ms3) md3 7 fpos HAR3 Hfin3) as (HFLpres & HFLown & HFLrng);
change (fs_frame_bytes 7) with 8192 in *; change (8192 / 8) with 1024 in HFSpres3; rewrite !EFA3 in *; rewrite ?EFL3 in *;
set (F := frame_addr ly 7 fpos) in *; set (FL := flag_addr ly 7 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia);
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
assert (HFrng : 0 <= F < 2 ^ 64) by (clear - HF4096 HFceil C1; lia);
gboxh HFhigh; gboxh HFhigh_img;
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl);
pose proof (sep_frames_pos trasegs _ LAWS ly3 S3 _ _ _ (7, fpos) (cid, pos) [] fl1 fl2 HAR3 ltac:(rewrite Hfrs3, Efl; reflexivity)) as HdFC;
unfold zdisjoint, frame_rng in HdFC; cbn [fst snd] in HdFC; change (fs_frame_bytes 7) with 8192 in HdFC; rewrite !EFA3 in HdFC; fold F in HdFC; gboxh HdFC;
clear fl1 fl2 Efl;
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trasegs (w_H W3) (ms_mem ms3) a = aview trasegs (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let F1 := fresh "F1" in intros a Ha;
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia);
let Kgot0 := fresh "Kgot0" in let Kcell0 := fresh "Kcell0" in let Kguar0 := fresh "Kguar0" in let Kuar0 := fresh "Kuar0" in let Vgr0 := fresh "Vgr0" in
ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
Ltac rga_hand RC HS HJx kx :=
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) (rga_post ?B ?cxv) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with fxv : YK11.FPState |- _ =>
eapply (RC fxv cxv Ev kx lyx Sx W3 ms3 md3) end;
[ lazymatch goal with H0 : rga_base _ _ |- _ => exact H0 end
| idtac
| first [eassumption | idtac]
| first [exact HJx | unfold rgc_FP, rgc_FPs; rga_cbn_cx_goal; cbn [ms_mem]; exact HJx | idtac]
| first [eassumption | idtac]
| red; rga_cbn_cx_goal
| exact HS ] end end end.
