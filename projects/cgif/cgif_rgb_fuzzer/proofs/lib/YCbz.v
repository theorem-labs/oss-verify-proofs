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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC1b YC2u YC4o YC4q YC4h YC27 YC2r YC20 YC16 YC4u YC52 YCaq YCct YCce YCcd YCc6 YCcb YCc9 YCca YCc7 YCc5 YC4z.
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
Hypothesis TRRFC : trrfc_spec B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_F_aux : rt_from B ss_H (INV_H B) -> rt_from B ss_G (INV_G B 16) -> rt_from B ss_F (INV_F B).
Proof.
intros RH RG. rt_prelude.
pose proof HINV as (Hk14 & HnC & r & N & E147 & E142 & HNmax & HOBJ). cbn [c_n] in HnC.
pose proof HOBJ as (g & s & wfn & ctx & path & attr & gen & loops & Wd & Hd & bef & beffmt & cur0 & Hobj & Hat & Hwf & HW & HH & Hbef & HPerm3 & Hown).
cbn [c_ly c_S] in HPerm3, Hown.
pose proof Hwf as (Hlen3 & HW1 & HH1 & HNWH & HNle & _).
assert (HN1 : 1 <= N <= RGB_NMAX) by (split; [clear - HW1 HH1 HNWH; nia | exact HNmax]).
destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hn0 HnC; lia|].
assert (Hown3 : forall x, In x (trgb_own r g s N bef beffmt) -> In x (ablocks B ly3 S3))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; apply in_app_iff; left; exact Hx).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
drop_nth HS 1%nat.
reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RTBspan A_rread_frameconfig.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 HF8hi; lia).
cgif_kept_run HFr Hown3 HJ3 Hfin3 EFA3 AG KA.
clear_frames.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp.
rreg HS (@BV 5 10 I) Ra0. rreg HS (@BV 5 11 I) Ra1. rreg HS (@BV 5 12 I) Ra2.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (UF : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (U70 : bv_unsigned (ew E 70) = sp1) by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact U70);
assert (EraX : raZ rg = 0x81354) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iL := idx_of_base rs 70%nat in let iL := eval vm_compute in iL in
let rL := eval vm_compute in (nth iL rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iL rL HS ltac:(vm_compute; reflexivity)) as HRL; cbn [ms_mem restrict] in HRL;
lazymatch type of HRL with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 70 sp1 cs lo hi wlo whi 24 8%N (SOff 10 0) p HRL U70 ltac:(cbn; tauto)
ltac:(rewrite sv_denot_SOff0; ewpeel; exact E10n) ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpin) as (_ & Q1 & Q2 & _); pose proof (req_size_pos n ltac:(clear - Hn26; lia)) as Q3; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Q1 Q2 Q3 C1; lia) ltac:(cbn; lia)) as Vp;
pose proof (field_of_region Ex _ 70 sp1 cs lo hi wlo whi 32 8%N (SOff 11 0) n HRL U70 ltac:(cbn; tauto)
ltac:(rewrite sv_denot_SOff0; ewpeel; exact E11n) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn26; lia) ltac:(cbn; lia)) as Vn;
pose proof (field_of_region Ex _ 70 sp1 cs lo hi wlo whi 40 8%N (SLit 14) 14 HRL U70 ltac:(cbn; tauto)
ltac:(reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear; lia) ltac:(cbn; lia)) as Vc end;
clear HRL end.
change (N.to_nat 8) with 8%nat in Vp, Vn, Vc.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iS := idx_of_base rs 88%nat in let iS := eval vm_compute in iS in
let rS := eval vm_compute in (nth iS rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iS rS HS ltac:(vm_compute; reflexivity)) as HRS; cbn [ms_mem restrict] in HRS;
assert (US : bv_unsigned (ew E 88) = SB + F / 8) by (rewrite E88; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia);
assert (ZS : forall od, In (YQ0b.mkChunk od (CVal 1 (SLit 0))) (YQ0b.r_chunks rS) -> aview trasegs (w_H W3) (ms_mem msX) (SB + F / 8 + od) = Some 0);
[ let od := fresh "od" in let Hod := fresh "Hod" in intros od Hod;
lazymatch type of HRS with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 88 (SB + F / 8) cs lo hi wlo whi od 1%N (SLit 0) 0 HRS US Hod eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Vz end;
pose proof (Vz 0%nat ltac:(lia)) as Vz0; cbn [Z.of_nat] in Vz0; rewrite Z.add_0_r in Vz0;
unfold aview; rewrite Vz0; reflexivity
| clear HRS ] end.
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (RAdst : range_addressable (aview trasegs (w_H Wx) (ms_mem msX)) SHADOW_OFF (F + 112) RGBFC_SIZE) end.
{ change RGBFC_SIZE with 24.
apply zero_shadow_of_bytes; [rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by (clear; lia); apply Z_mod_mult | reflexivity | clear; lia |].
intros j Hj. change (24 / 8) with 3 in Hj. rewrite <- SB_SHADOW_OFF.
replace ((F + 112) / 8) with (F / 8 + 14) by (rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia);
replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia); clear; lia).
replace (SB + (F / 8 + 14) + j) with (SB + F / 8 + (14 + j)) by (clear; lia).
assert (Hj4 : j = 0 \/ j = 1 \/ j = 2) by (clear - Hj; lia).
destruct Hj4 as [-> | [-> | ->]]; apply ZS; cbn; tauto. }
clear ZS.
pose proof (proj1 (proj2 HJ3)) as HLY3. pose proof HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & Eslo3 & Eshi3 & _).
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (RAst : range_addressable (aview trasegs (w_H Wx) (ms_mem msX)) SHADOW_OFF (sp1 + 24) 24)
by (apply (range_addressable_stack B LAWS ly3 S3 _ _ _ (sp1 + 24) 24 (proj1 HJ3)); [rewrite Eslo3; clear - Hsp1 Hslo FFS; lia | rewrite Eshi3; clear - Hsp1 Hshi; lia | clear; lia]) end.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (HOWNB : bsum (trgb_own r g s N bef beffmt) <= RGB_SIZE + CGB + 4 * RGB_NMAX).
{ unfold trgb_own. cbn [bsum fold_right snd]. rewrite bsum_app. pose proof (cgif_blocks_bsum _ g s N Hat Hwf) as Hcb.
assert (bsum (optb bef (beffmt * N)) <= 4 * RGB_NMAX).
{ unfold optb. destruct (bef =? 0) eqn:Eb; [cbn; unfold RGB_NMAX; clear; lia|]. cbn [bsum fold_right snd].
destruct Hbef as [-> | [-> | ->]]; [discriminate Eb | |]; clear - HN1; lia. }
clear - Hcb H. lia. }
assert (HLIVEc : blocks_bytes S3 + LIVE_RRFC <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPerm3), bsum_app, <- (blocks_bytes_bsum B ly S).
unfold LIVE_LIB in Hlive. unfold LIVE_RRFC, CGB, RGB_SIZE, RGB_NMAX in *. clear - Hlive HOWNB. lia. }
assert (HEVc : vev S3 + EV_RRFC <= VEV_MAX).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & HK0 & _). assert (H : EV_RGBNEWGIF + EV_RRFC <= RGB_COARSE) by (vm_compute; discriminate).
apply (jroom S S3 k EV_RRFC Hbud Hnev3 HK0); [vm_compute; discriminate | clear - Hk14 H; lia]. }
trim_nth HS 2%nat 136 256. trim_nth HS 3%nat 0 40.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl); cbn [ss_pc];
change (Z_to_bv 64 529836) with (w64 A_rread_frameconfig);
eapply SRr_bind;
[ eapply (TRRFC LLVMF_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
(trgb_own r g s N bef beffmt ++ ablocks B ly S) (sp1 + 24) (F + 112) N p n 14 2 fpos HJ3);
[ first [ intros b Hb; apply in_app_iff; right; exact Hb | idtac "RF1" ]
| first [ exact HPerm3 | idtac "RF2" ]
| first [ apply in_app_iff; right; exact Hpin | idtac "RF3" ]
| first [ rewrite Rra; apply ret_ok_even; vm_compute; reflexivity | idtac "RF4" ]
| first [ rewrite EraX; clear; lia | idtac "RF5" ]
| first [ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 3%nat) by (clear; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp | idtac "RF6" ]
| first [ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 4%nat) by (clear; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp | idtac "RF7" ]
| first [ rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite U70; reflexivity | match goal with |- ?gg => idtac "RF8" gg end ]
| first [ rewrite Ra1, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite UF; reflexivity | match goal with |- ?gg => idtac "RF9" gg end ]
| first [ rewrite Ra2; rewrite ?sv_denot_SOff0; ewpeel; exact E142 | match goal with |- ?gg => idtac "RF10" gg end ]
| first [ rewrite EspX; exact Hsp1al16 | idtac "RF13" ]
| first [ rewrite EspX; assert (TRRFC_STK + 144 <= LLVMF_STK) by (vm_compute; discriminate); clear - Hsp1 H; lia | match goal with |- ?gg => idtac "RF14" gg end ]
| first [ rewrite EspX; clear - Hsp1; lia | idtac "RF15" ]
| first [ left; reflexivity | idtac "RF16" ]
| first [ clear; lia | idtac "RF17" ]
| first [ rewrite EFA3; fold F; rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); apply Z_mod_mult | match goal with |- ?gg => idtac "RF18" gg end ]
| first [ rewrite EFA3; fold F; clear; lia | idtac "RF19" ]
| first [ rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; change RGBFC_SIZE with 24; clear; lia | idtac "RF20" ]
| first [ rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by (clear; lia); apply Z_mod_mult | idtac "RF21" ]
| first [ rewrite EspX; clear; lia | idtac "RF22" ]
| first [ clear - Hsp1; lia | idtac "RF23" ]
| first [ pose proof (Z.div_mod sp1 32 ltac:(clear; lia)) as D32; rewrite Hsp1al, Z.add_0_r in D32; rewrite D32; replace (32 * (sp1 / 32) + 24) with ((4 * (sp1 / 32) + 3) * 8) by (clear; lia); apply Z_mod_mult | match goal with |- ?gg => idtac "RF24" gg end ]
| first [ exact RAst | match goal with |- ?gg => idtac "RF25" gg end ]
| first [ exact RAdst | match goal with |- ?gg => idtac "RF26" gg end ]
| first [ exact HN1 | idtac "RF27" ]
| first [ clear - HnC; lia | idtac "RF28" ]
| first [ clear - Hnpos; lia | idtac "RF29" ]
| first [ exact Vp | match goal with |- ?gg => idtac "RF30" gg end ]
| first [ replace (sp1 + 24 + 8) with (sp1 + 32) by (clear; lia); exact Vn | match goal with |- ?gg => idtac "RF31" gg end ]
| first [ replace (sp1 + 24 + 16) with (sp1 + 40) by (clear; lia); exact Vc | match goal with |- ?gg => idtac "RF32" gg end ]
| first [ exact HXU | match goal with |- ?gg => idtac "RF32b" gg end ]
| first [ exact HEVc | match goal with |- ?gg => idtac "RF33" gg end ]
| first [ exact HLIVEc | idtac "RF34" ] ]
| ] end end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & cur2 & -> & HJ4 & HP4 & Hfrs4 & HJB4 & Ha04 & K1 & K2 & K3 & Vp4 & Vn4 & Vc4 & Hcur2 & Hres).
rewrite EspX in K1. rewrite Rra. change RGBFC_SIZE with 24 in K1, K3.
clear Rra Rsp Rgp Rtp Ra1 Ra2 RAst RAdst Vp Vn Vc HLIVEc.
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(2, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply rt_region_kept_eq; [ first [evalE AG | idtac "K88-0"]
| intros a Ha; first [apply (K3 2 fpos a Hfin3) | match goal with |- ?g => idtac "K88-APPLY" g end];
[ first [right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear - Ha; unfold SB in *; lia | match goal with |- ?g => match type of Ha with ?t => idtac "K88-1" t g end end]
| first [clear - Ha HF8c HF8lo HFhigh C3; unfold SB in *; zone_lia | match goal with |- ?g => match type of Ha with ?t => idtac "K88-2" t g end end]
| first [clear - Ha HF8hi Hsp1 Hceil Hslo FFS C1; unfold SB in *; lia | match goal with |- ?g => idtac "K88-3" g end] ]
| intros a Ha; first [exfalso; clear - Ha; lia | match goal with |- ?g => match type of Ha with ?t => idtac "K88-4" t g end end] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply rt_region_kept_eq; [ evalE AG
| intros a Ha; apply (K3 2 fpos a Hfin3);
[ left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear - Ha; lia
| clear - Ha; lia | clear - Ha HFceil Hsp1 Hceil Hslo FFS C1; lia ]
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply rt_region_kept_eq; [ evalE AG
| intros a Ha; apply K1; [clear - Ha Hsp1 Hceil Hslo Hshi H47 FFS C1; lia | clear - Ha; lia | clear - Ha HFceil Hsp1 Hceil Hslo FFS C1; lia | clear - Ha; lia]
| intros a Ha; apply Hpres4; clear - Ha Hsp1 FFS; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply rt_region_kept_eq; [ evalE AG
| intros a Ha; apply K1; [clear - Ha Hceil Hslo Hshi H47 FFS C1; lia | clear - Ha Hsp1; lia | clear - Ha HFceil Hceil Hslo FFS C1; lia | clear - Ha Hsp1; lia]
| intros a Ha; apply Hpres4; clear - Ha FFS; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rreg HS (10%bv : bv 5) Rres. rewrite Ha04 in Rres. symmetry in Rres.
assert (KR : forall b sz, In (b, sz) (trgb_own r g s N bef beffmt) -> blk_kept (w_H W3) (w_H W4) (ms_mem ms) mem4 b (req_size sz))
by (intros b sz Hb i Hi; apply (K2 b sz i); [apply in_app_iff; left; exact Hb | exact Hi]).
assert (Rres64 : 0 <= res < 2 ^ 64) by (clear - Hres; destruct Hres as [(-> & _) | [(-> & _) | (-> & _)]]; lia).
reshok HS.
srr_branch_tok tratbl_lib_ok HS SHOK RTBspan.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
lazymatch type of Rres with ew _ ?na = _ => hc_bool Hc ltac:(fun H => hc_atom H na res Rres ltac:(exact Rres64)) end. hc_prop Hc.
destruct Hres as [(Hr & _) | [(Hr0 & HPL) | (Hr1 & _)]]; [exfalso; clear - Hc Hr; lia | | exfalso; clear - Hc Hr1; lia].
assert (Hown4 : forall x, In x (trgb_own r g s N bef beffmt) -> In x (ablocks B ly4 S4))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPL|]; apply in_app_iff; left; exact Hx).
reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ4 SHOK RTBspan 0x8138c.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA4.
cgif_kept_run HFr Hown4 HJ4 Hfin4 EFA4 AG KB.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
ra_join_win HS ss_H 260%nat rt_H_deads_bv ltac:(idtac).
rt_hand RH HS.
split; [cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0]; lazymatch goal with |- rbv ?Sx ?S3x _ _ => match goal with HJx : ajournal _ _ _ _ _ _ Sx _ _ _ _ _ S3x _ _ _ _ |- _ => apply (rt_bv_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx) end end; [assert (HQ : EV_RGBNEWGIF + EV_RRFC <= 62) by (vm_compute; discriminate); clear - Hk14 HQ; lia | clear; lia]|].
split; [pose proof KH_newgif as HKH; clear - Hk14 HKH; lia|].
exists r, N. split; [ewpeel; exact E147|].
unfold rt_obj. cbn [c_ly c_S]. exists g, s, wfn, ctx, path, attr, gen, loops, Wd, Hd, bef, beffmt, cur0.
split.
{ lazymatch goal with |- obj_at _ (mrestrict (w_H ?Wf) ?mf) _ _ _ =>
apply (rg_obj_at_blk_kept (w_H W3) (w_H Wf) (ms_mem ms3) mf r LAY_Rgb _ RGB_SIZE Hobj lay_inside_Rgb) end.
assert (Hb : In (r, RGB_SIZE) (trgb_own r g s N bef beffmt)) by (left; reflexivity).
eapply blk_kept_trans; [exact (KA _ _ Hb)|]. eapply blk_kept_trans; [exact (KR _ _ Hb) | exact (KB _ _ Hb)]. }
split.
{ lazymatch goal with |- tcgif_at (mrestrict (w_H ?Wf) ?mf) _ _ => apply (tcgif_at_blocks_kept (w_H W3) (w_H Wf) (ms_mem ms3) mf g s N Hat) end.
intros b sz Hb0. assert (Hb : In (b, sz) (trgb_own r g s N bef beffmt)) by (right; apply in_app_iff; left; exact Hb0).
eapply blk_kept_trans; [exact (KA _ _ Hb)|]. eapply blk_kept_trans; [exact (KR _ _ Hb) | exact (KB _ _ Hb)]. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact Hbef|]. split; [exact HPL | exact Hown].
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
lazymatch type of Rres with ew _ ?na = _ => hc_bool Hc ltac:(fun H => hc_atom H na res Rres ltac:(exact Rres64)) end. hc_prop Hc.
assert (HG : exists img fmt fattr fgen delay, rt_imgok img fmt /\
obj_at trasegs (mrestrict (w_H W4) mem4) (F + 112) LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay] /\
Permutation (ablocks B ly4 S4) (timg_block img fmt N ++ trgb_own r g s N bef beffmt ++ ablocks B ly S) /\
(forall b, In b (timg_block img fmt N) -> aftok [] (ablocks B ly S) b)).
{ destruct Hres as [(Hr & HPL & fattr & fgen & delay & Ofc) | [(Hr0 & _) | (Hr1 & img & fmt & fattr & fgen & delay & Hfmt & Ofc & HPL & Htok & _)]].
- exists 0, 0, fattr, fgen, delay. split; [right; split; reflexivity|]. split; [exact Ofc|]. split; [exact HPL|]. intros b [].
- exfalso; exact (Hc Hr0).
- exists img, fmt, fattr, fgen, delay.
assert (Himg4 : In (img, fmt * N) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPL | left; reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ img (fmt * N) HAR4 Himg4) as (_ & Hi4096 & _).
split; [left; split; [exact Hfmt | clear - Hi4096; lia]|]. split; [exact Ofc|].
assert (Etb : timg_block img fmt N = [(img, fmt * N)]) by (unfold timg_block, tfmt_okb; destruct Hfmt as [-> | ->]; reflexivity).
rewrite Etb. split; [exact HPL|]. intros b [<- | []]. exact Htok. }
destruct HG as (img & fmt & fattr & fgen & delay & Himg & Ofc & HPL & Htok).
assert (Hown4 : forall x, In x (trgb_own r g s N bef beffmt) -> In x (ablocks B ly4 S4))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPL|]; apply in_app_iff; right; apply in_app_iff; left; exact Hx).
pose proof Ofc as Ofc'. cbn [obj_at LAY_RgbFrameConfig] in Ofc. unfold field_ok in Ofc. cbn [fst snd N.to_nat Z.of_N Pos.to_nat] in Ofc.
rewrite <- !Z.add_assoc in Ofc. cbn [Z.add Pos.add] in Ofc.
change (2 ^ (8 * 8)) with (2 ^ 64) in Ofc. change (2 ^ (8 * 4)) with (2 ^ 32) in Ofc. change (2 ^ (8 * 2)) with 65536 in Ofc.
destruct Ofc as ((V1 & R1) & (V2 & R2) & _).
add_atom_win HS 401%nat (Z_to_bv 64 cur2) E401.
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region trasegs Ev2 _ _ (rt_cur_region 401) HS eq_refl
ltac:(unfold rt_cur_region, region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_havoc_old, ?ew_ewset_other by nat_side; rewrite E70, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
split; [clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia|]; split; [clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); apply Hpres4; clear - Ho Hsp1 FFS; lia
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trasegs Ev2 _ sp1 40 8 (SOff 401 0) cur2); [rewrite sv_denot_SOff0; exact E401 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hcur2 Hn26; lia | clear; cbn; lia | replace (sp1 + 24 + 16) with (sp1 + 40) in Vc4 by (clear; lia); exact Vc4] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
unfold rt_cur_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
repeat split; first [clear - Hsp1 HFceil HFhigh HFhigh_img Hceil Hslo Hstk0 FFS C1 C3 Hshi H47 HF8c HF8lo; unfold SB in *; zone_lia | match goal with |- ?g => idtac "DISJ-CUR" g end])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
let WS := constr:([Z_to_bv 64 img; Z_to_bv 64 fmt] : list word) in
pose proof (st_ok_havoc_win trasegs 402 Ev ssv msv WS HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (E402 : ew (havoc Ev 402 WS) 402 = Z_to_bv 64 img) by (exact (ew_havoc_new Ev 402 WS 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E403 : ew (havoc Ev 402 WS) 403 = Z_to_bv 64 fmt) by (exact (ew_havoc_new Ev 402 WS 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
let HS3 := fresh "HS3" in
assert (UF2 : bv_unsigned (ew Ev2 75) = F) by (ewpeel; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia);
pose proof (ast_ok_add_region trasegs Ev2 _ _ rt_fconfig_region HS eq_refl
ltac:(unfold rt_fconfig_region, region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite UF2;
split; [clear - HF4096; lia|]; split; [clear - HFceil C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HFpres4 (F + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [apply (chunk_ok_val trasegs Ev2 _ F 112 8 (SOff 402 0) img); [rewrite sv_denot_SOff0; exact E402 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact R1 | clear; cbn; lia | exact V1]|];
apply Forall_cons; [apply (chunk_ok_val trasegs Ev2 _ F 120 4 (SOff 403 0) fmt); [rewrite sv_denot_SOff0; exact E403 | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact R2 | clear; cbn; lia | exact V2]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
unfold rt_fconfig_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
repeat split; first [clear - Hsp1 HFceil HF4096 HFhigh HFhigh_img Hceil Hslo Hstk0 FFS C1 C3 Hshi H47 HF8c HF8lo; unfold SB in *; zone_lia | match goal with |- ?g => idtac "DISJ-FC" g end])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
rebaseE HS AG HEvW; clear HEvW; relowRT HS AG E10 E11 E32 E10n E11n E32n.
reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ4 SHOK RTBspan 0x8135c.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA4.
cgif_kept_run HFr Hown4 HJ4 Hfin4 EFA4 AG KB.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
add_atom_win HS 400%nat (Z_to_bv 64 16) E400.
rreg HS (24%bv : bv 5) Q24.
ws_pin HS (@BV 5 24 I) (SOff 400 0) Q24 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; first [exact E400 | rewrite E400; reflexivity | match goal with |- ?g => idtac "PIN400" g end]).
norm_ss HS.
ra_join_win HS ss_G 410%nat rt_G_deads_bv ltac:(idtac).
rt_hand RG HS.
split; [cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0]; lazymatch goal with |- rbv ?Sx ?S3x _ _ => match goal with HJx : ajournal _ _ _ _ _ _ Sx _ _ _ _ _ S3x _ _ _ _ |- _ => apply (rt_bv_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx) end end; [assert (HQ : EV_RGBNEWGIF + EV_RRFC <= 16) by (vm_compute; discriminate); clear - Hk14 HQ; lia | clear; lia]|].
split; [rewrite <- kG_16; clear - Hk14; lia|]. split; [clear; lia|]. split; [ewpeel; exact E400|]. split; [cbn [c_n]; exact HnC|].
exists r, N, cur2, img, fmt.
split; [ewpeel; exact E147|]. split; [ewpeel; exact E142|]. split; [exact HNmax|].
split; [ewpeel; exact E401|]. split; [cbn [c_n]; clear - Hcur2; lia|].
split; [ewpeel; exact E402|]. split; [ewpeel; exact E403|]. split; [exact R1|]. split; [exact R2|]. split; [exact Himg|].
unfold rt_objI. cbn [c_ly c_S]. exists g, s, wfn, ctx, path, attr, gen, loops, Wd, Hd, bef, beffmt, cur0.
split.
{ lazymatch goal with |- obj_at _ (mrestrict (w_H ?Wf) ?mf) _ _ _ =>
apply (rg_obj_at_blk_kept (w_H W3) (w_H Wf) (ms_mem ms3) mf r LAY_Rgb _ RGB_SIZE Hobj lay_inside_Rgb) end.
assert (Hb : In (r, RGB_SIZE) (trgb_own r g s N bef beffmt)) by (left; reflexivity).
eapply blk_kept_trans; [exact (KA _ _ Hb)|]. eapply blk_kept_trans; [exact (KR _ _ Hb) | exact (KB _ _ Hb)]. }
split.
{ lazymatch goal with |- tcgif_at (mrestrict (w_H ?Wf) ?mf) _ _ => apply (tcgif_at_blocks_kept (w_H W3) (w_H Wf) (ms_mem ms3) mf g s N Hat) end.
intros b sz Hb0. assert (Hb : In (b, sz) (trgb_own r g s N bef beffmt)) by (right; apply in_app_iff; left; exact Hb0).
eapply blk_kept_trans; [exact (KA _ _ Hb)|]. eapply blk_kept_trans; [exact (KR _ _ Hb) | exact (KB _ _ Hb)]. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact Hbef|].
split; [eapply Permutation_trans; [exact HPL|]; apply Permutation_app_swap_app|].
intros b Hb. apply in_app_iff in Hb as [Hb | Hb]; [exact (Hown b Hb) | exact (Htok b Hb)].
Qed.
Lemma rt_F : rt_from B ss_H (INV_H B) -> rt_from B ss_G (INV_G B 16) -> rt_from B ss_F (INV_F B).
Proof. exact rt_F_aux. Qed.
End d.
End c.
