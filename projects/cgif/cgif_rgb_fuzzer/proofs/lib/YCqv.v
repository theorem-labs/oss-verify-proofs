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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCfx YChv YChx YChn YCf6 YCft YCey YCe4 YCi1 YCie YCph YCrr YCrd YCrc YCr3 YCr9 YCr7 YCr4 YCr2 YCib YCr5.
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
Hypothesis TRGBNEWGIF : trgb_newgif_spec B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_E_aux : rt_from B ss_X (INV_X B) -> rt_from B ss_F (INV_F B) -> rt_from B ss_E (INV_E B).
Proof.
intros RX RFF. rt_prelude.
pose proof HINV as (Hk0 & Eab3 & HnC & (curi & Ecur & Hcuri) & Wd & Hd & E540 & E541 & E542 & RW & RH & HNle). cbn [c_n] in HnC, Hcuri.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
drop_base HS 10%nat.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RTBspan A_cgif_rgb_newgif.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
upd_aboveF2 HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 HF8hi; lia). clear_frames.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0. rreg HS (@BV 5 10 I) Ra0.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
assert (UF : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x81498) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
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
let iF := idx_of_base_off rs 75%nat 32 in let iF := eval vm_compute in iF in
let rF := eval vm_compute in (nth iF rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iF rF HS ltac:(vm_compute; reflexivity)) as HRF; cbn [ms_mem restrict] in HRF end.
Ltac fieldF HRF UF od w e V :=
lazymatch type of HRF with region_ok _ ?Ex _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region_any Ex _ 75 _ cs lo hi wlo whi od w e HRF UF ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
try change (N.to_nat 8) with 8%nat in V; try change (N.to_nat 4) with 4%nat in V; try change (N.to_nat 2) with 2%nat in V; try change (N.to_nat 1) with 1%nat in V;
try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V; try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V;
try change (2 ^ (8 * Z.of_N 2)) with 65536 in V; try change (2 ^ (8 * Z.of_N 1)) with 256 in V end.
Ltac fieldFany HRF UF od w V :=
lazymatch type of HRF with region_ok _ _ _ (YQ0b.mkRegion _ _ _ _ _ ?cs) =>
lazymatch cs with context [YQ0b.mkChunk od (CVal w ?ea)] => fieldF HRF UF od w ea V end end.
fieldFany HRF UF 32 8%N V0. fieldFany HRF UF 40 8%N V1. fieldFany HRF UF 48 8%N V2.
change (bv_unsigned (sv_denot E (SLit 530008)) mod 2 ^ 64) with A_writecb in V0.
change (bv_unsigned (sv_denot E (SLit 0)) mod 2 ^ 64) with 0 in V1, V2.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iW := idx_of_base_off rs 75%nat 66 in let iW := eval vm_compute in iW in let rW := eval vm_compute in (nth iW rs got_region) in
let iH := idx_of_base_off rs 75%nat 68 in let iH := eval vm_compute in iH in let rH := eval vm_compute in (nth iH rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iW rW HS ltac:(vm_compute; reflexivity)) as HRW; cbn [ms_mem restrict] in HRW;
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iH rH HS ltac:(vm_compute; reflexivity)) as HRH; cbn [ms_mem restrict] in HRH end.
fieldFany HRW UF 66 2%N V6. fieldFany HRH UF 68 2%N V7.
cbn [sv_denot] in V6, V7. rewrite ?ew_ewset_other, ?ew_havoc_old in V6, V7 by nat_side.
rewrite (denot_atom_mod _ 540 Wd _ E540 ltac:(clear - RW; lia)), Z.mod_small in V6 by (clear - RW; lia).
rewrite (denot_atom_mod _ 541 Hd _ E541 ltac:(clear - RH; lia)), Z.mod_small in V7 by (clear - RH; lia).
clear HRW HRH.
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ3) Hfin3) as (_ & _ & HFpN & _);
change (fs_frame_bytes 2) with 256 in HFpN; rewrite !EFA3 in HFpN; fold F in HFpN;
assert (PM : forall a, F <= a < F + 256 -> exists b, mbyte trbsegs (mrestrict (w_H Wx) (ms_mem msX)) a = Some b)
by (intros a Ha; destruct (proj1 (HFpN a Ha)) as [Hh [b Hb]]; exists b; unfold mbyte, mrestrict; rewrite Hh, Hb; reflexivity);
destruct (val_mem_of_present4 trbsegs (mrestrict (w_H Wx) (ms_mem msX)) (F + 56) ltac:(intros i Hi; apply PM; clear - Hi; lia)) as (attr & Rattr & V3);
destruct (val_mem_of_present4 trbsegs (mrestrict (w_H Wx) (ms_mem msX)) (F + 60) ltac:(intros i Hi; apply PM; clear - Hi; lia)) as (gen & Rgen & V4);
destruct (rtb_val_mem_byte2 (w_H Wx) (ms_mem msX) (F + 64) (proj1 (HFpN (F + 64) ltac:(clear; lia))) (proj1 (HFpN (F + 64 + 1) ltac:(clear; lia)))) as (loops & Rloops & V5) end.
clear PM HFpN.
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (OcfgX : obj_at trbsegs (mrestrict (w_H Wx) (ms_mem msX)) (F + 32) LAY_RgbConfig [A_writecb; 0; 0; attr; gen; loops; Wd; Hd]) end.
{ cbn [obj_at LAY_RgbConfig]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N Pos.to_nat].
rewrite <- !Z.add_assoc. cbn [Z.add Pos.add].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536.
split; [split; [first [rewrite Z.add_0_r; exact V0 | exact V0 | match type of V0 with ?t => idtac "V0-SHAPE" t end; fail] | unfold A_writecb; clear; lia]|].
split; [split; [first [exact V1 | match type of V1 with ?t => idtac "V1-SHAPE" t end; fail] | clear; lia]|].
split; [split; [first [exact V2 | match type of V2 with ?t => idtac "V2-SHAPE" t end; fail] | clear; lia]|].
split; [split; [exact V3 | exact Rattr]|]. split; [split; [exact V4 | exact Rgen]|]. split; [split; [exact V5 | exact Rloops]|].
split; [split; [exact V6 | clear - RW; lia]|]. split; [split; [exact V7 | clear - RH; lia]|]. exact I. }
clear V0 V1 V2 V3 V4 V5 V6 V7 HRF.
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
assert (AF : afobj B ly3 S3 Wx (ms_mem msX) (F + 32) RGBCONFIG_SIZE) end.
{ change RGBCONFIG_SIZE with 40. split; [|split].
- exists 2, fpos. split; [exact Hfin3|]. split; [clear; lia|]. rewrite EFA3. fold F. split; [rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); apply Z_mod_mult|].
change (fs_frame_bytes 2) with 256. clear; lia.
- rewrite HFq. replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia). apply Z_mod_mult.
- apply zero_shadow_of_bytes; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia); apply Z_mod_mult | reflexivity | clear; lia |].
intros j Hj. change (40 / 8) with 5 in Hj. rewrite <- SB_SHADOW_OFF.
replace ((F + 32) / 8) with (F / 8 + 4) by (rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia);
replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia); clear; lia).
replace (SB + (F / 8 + 4) + j) with (SB + F / 8 + (4 + j)) by (clear; lia).
assert (Hj6 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by (clear - Hj; lia).
destruct Hj6 as [-> | [-> | [-> | [-> | ->]]]]; apply ZS; cbn; tauto. }
clear ZS.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _).
assert (HEVc : vev S3 + EV_RGBNEWGIF <= VEV_MAX).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & HK0 & _). assert (H : EV_RGBNEWGIF <= RGB_COARSE) by (vm_compute; discriminate).
apply (jroom S S3 k EV_RGBNEWGIF Hbud Hnev3 HK0); [vm_compute; discriminate | clear - Hk0 H; lia]. }
assert (HLIVEc : blocks_bytes S3 + LIVE_RGBNEWGIF <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S).
assert (LIVE_RGBNEWGIF <= LIVE_LIB) by (vm_compute; discriminate). clear - Hlive H. lia. }
assert (HNle8 : Wd * Hd <= 100000000) by (clear - HNle; lia).
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call trbsegs B LAWS trb_segs_low W3 Ex ssX msX LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)] ly3 S3 mdX k
TRGBNEWGIF_STK [] EV_RGBNEWGIF (sp1 - spZ regs) (ew Ex 2) (Z_to_bv 64 0x81498) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0))
(fun ly2 S2 W2 regs2 mem2 md2 => exists res : Z, getr regs2 10 = w64 res /\
((res = 0 /\ Permutation (ablocks B ly2 S2) (ablocks B ly3 S3)) \/
(res <> 0 /\ exists g s,
obj_at trbsegs (mrestrict (w_H W2) mem2) res LAY_Rgb [g; A_writecb; 0; 0; attr; gen; loops; Wd; Hd; 0; 0; R_PENDING] /\
tcgif_at (mrestrict (w_H W2) mem2) g s /\ cgif_wf s (Wd * Hd) /\
cg_frames s = [None; None; None] /\ cg_W s = Wd /\ cg_H s = Hd /\ cg_attr s = TRGB_GIFATTR /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\
Permutation (ablocks B ly2 S2) ((res, RGB_SIZE) :: cgif_blocks g s (Wd * Hd) ++ ablocks B ly3 S3) /\
(forall b, In b ((res, RGB_SIZE) :: cgif_blocks g s (Wd * Hd)) ->
aftok [] (ablocks B ly3 S3) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TRGBNEWGIF_STK (spZ (ms_regs msX)) [] (ablocks B ly3 S3) blc ly2 [] (fst b + i))))) HS eq_refl HJ3);
[ first [ rewrite Rsp; rewrite ?sv_denot_SOff0; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Usp3; f_equal; clear; lia | match goal with |- ?g => idtac "AJ1" g end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ exact Usp3 | idtac "AJ3" ]
| first [ rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity | match goal with |- ?g => idtac "AJ4" g end ]
| first [ clear - Hsp1; lia | idtac "AJ5" ]
| first [ apply Zle_bool_imp_le; vm_compute; reflexivity | idtac "AJ6" ]
| first [ assert (TRGBNEWGIF_STK + 176 <= LLVMF_STK) by (vm_compute; discriminate); clear - Hsp1 H; lia | match goal with |- ?g => idtac "AJ7" g end ]
| first [ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Ugp; exact Hgp | idtac "AJ8" ]
| first [ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Utp; exact Htp | idtac "AJ9" ]
| first [ exact Rra | idtac "AJ10" ]
| first [ apply ret_ok_even; vm_compute; reflexivity | idtac "AJ11" ]
| first [ rewrite unsigned_lit_small by (clear; lia); clear; lia | idtac "AJ12" ]
| first [ rewrite Es0X; replace (spZ regs + (sp1 - spZ regs)) with sp1 by (clear; lia); exact Hch1 | match goal with |- ?g => idtac "AJ13" g end ]
| first [ intros HPRE1; eapply SRr_mono;
[ first [ pose proof (TRGBNEWGIF ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0))
(F + 32) attr gen loops Wd Hd HPRE1) as CALL | idtac "CALL-POSE" ];
unfold cfg_at, trgb_newgif_post, apost_base in CALL; cbn [ss_pc]; change (w64 A_cgif_rgb_newgif) with (Z_to_bv 64 531104) in CALL;
first [ apply CALL | match goal with |- ?g => idtac "CALL-APPLY" g end; let t := type of CALL in idtac "CALL-TYPE" t ]; clear CALL;
[ first [ rewrite EspX; exact Hsp1al | idtac "CA1" ]
| first [ rewrite EraX; apply rt_ctx_in; [exact Hra | vm_compute; tauto | vm_compute; tauto] | match goal with |- ?g => idtac "CA2" g end ]
| first [ rewrite Hfrs3; cbn [length]; clear; lia | idtac "CA3" ]
| first [ rewrite EspX; pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); rewrite LT; clear - Hsp1 Htop; lia | match goal with |- ?g => idtac "CA3b" g end ]
| first [ eapply arodata_ok_journal; [exact HJ3 | exact HROD] | idtac "CA4" ]
| first [ rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite UF; reflexivity | match goal with |- ?g => idtac "CA5" g end ]
| first [ exact AF | idtac "CA7" ]
| first [ exact OcfgX | match goal with |- ?g => idtac "CA8" g end ]
| first [ exact HNle8 | match goal with |- ?g => idtac "CA9" g end ]
| first [ exact HEVc | match goal with |- ?g => idtac "CA21" g end ]
| first [ exact HLIVEc | match goal with |- ?g => idtac "CA22" g end ] ]
| first [ cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HPc & res & Hres & Hpost);
exists ly4, S4, regs4, mem4, md4; split; [rewrite Rra; reflexivity|]; split; [exact HJc|];
split; [exact HPc|]; exists res; split; [exact Hres | exact Hpost] | match goal with |- ?g => idtac "CALL-POST" g end ] ]
| idtac "AJ14" ]
| first [ intros a (r & Hr & Ha); destruct Hr | match goal with |- ?g => idtac "AJ15" g end ] ]
| ] end end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & res & Hres & Hpost).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HJc by (clear; lia).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1 OcfgX AF EspX EraX Es0X.
pose proof (proj1 HJ4) as HAR4.
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs4 & _). cbn [app] in Hfrs4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(2, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (HnFP : forall a : Z, ~ inFP [] a) by (intros a (r & Hr & _); exact Hr).
lazymatch type of HS with st_ok _ _ ?ssx _ => let l := eval vm_compute in (seq 0 (length (ss_mem ssx))) in
reseat HS HJ4 HP4 l AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFP | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFP | intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
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
rreg HS (10%bv : bv 5) Rres. rewrite Hres in Rres. symmetry in Rres.
clear Usp3 Ugp Utp UF.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
assert (HPX : exists pre, Permutation (ablocks B ly4 S4) (pre ++ ablocks B ly3 S3) /\
((res = 0 /\ pre = []) \/
(res <> 0 /\ exists g s, pre = (res, RGB_SIZE) :: cgif_blocks g s (Wd * Hd) /\
obj_at trbsegs (mrestrict (w_H W4) mem4) res LAY_Rgb [g; A_writecb; 0; 0; attr; gen; loops; Wd; Hd; 0; 0; R_PENDING] /\
tcgif_at (mrestrict (w_H W4) mem4) g s /\ cgif_wf s (Wd * Hd) /\ cg_W s = Wd /\ cg_H s = Hd /\
(forall b, In b ((res, RGB_SIZE) :: cgif_blocks g s (Wd * Hd)) -> aftok [] (ablocks B ly3 S3) b)))).
{ destruct Hpost as [(Hr0 & HP) | (Hr1 & g & s & Hobj & Hat & Hwf & Hfr & HW & HH & Hattr & Hcur & Hih & HP & Hown)].
- exists []. cbn [app]. split; [exact HP | left; split; [exact Hr0 | reflexivity]].
- exists ((res, RGB_SIZE) :: cgif_blocks g s (Wd * Hd)). split; [exact HP|]. right. split; [exact Hr1|]. exists g, s.
repeat (split; [first [reflexivity | assumption]|]). intros b Hb. exact (proj1 (Hown b Hb)). }
clear Hpost. destruct HPX as (pre & HPerm4 & Hpre).
assert (Hprein4 : forall x, In x pre -> In x (ablocks B ly4 S4))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; apply in_app_iff; left; exact Hx).
assert (Rres64 : 0 <= res < 2 ^ 64).
{ destruct Hpre as [(-> & _) | (_ & g & s & Epre & _)]; [clear; lia|].
assert (Hg4 : In (res, RGB_SIZE) (ablocks B ly4 S4)) by (apply Hprein4; rewrite Epre; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res RGB_SIZE HAR4 Hg4) as (_ & Hg4096 & Hgceil & _). change (req_size RGB_SIZE) with 64 in Hgceil. clear - Hg4096 Hgceil C1. lia. }
reshok HS.
srr_branch_tok trbtbl_lib_ok HS SHOK RTBspan.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
lazymatch type of Rres with ew _ ?K = _ => hc_bool Hc ltac:(fun H => hc_atom H K res Rres ltac:(exact Rres64)) end. hc_prop Hc.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK RTBspan 0x814f4.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA4.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
ra_join_win HS ss_X 2000%nat rt_X_deads_bv ltac:(idtac).
rt_hand RX HS.
split; [cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0]; lazymatch goal with |- rbv ?Sx ?S3x _ _ => match goal with HJx : ajournal _ _ _ _ _ _ Sx _ _ _ _ _ S3x _ _ _ _ |- _ => apply (rt_bv_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx) end end; [assert (HQ : EV_RGBNEWGIF <= RGB_COARSE) by (vm_compute; discriminate); clear - Hk0 HQ; lia | clear; lia]|].
split; [assert (EV_RGBNEWGIF <= EV_RLIB) by (vm_compute; discriminate); clear - Hk0 H; lia|].
cbn [c_ly c_S]. destruct Hpre as [(_ & ->) | (Hr1 & _)]; [cbn [app] in HPerm4; rewrite <- Eab3; exact HPerm4 | exfalso; exact (Hr1 Hc)].
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
lazymatch type of Rres with ew _ ?K = _ => hc_bool Hc ltac:(fun H => hc_atom H K res Rres ltac:(exact Rres64)) end. hc_prop Hc.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK RTBspan 0x8149c.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA4.
cgif_kept_run HFr Hprein4 HJ4 Hfin4 EFA4 AG KB.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
destruct Hpre as [(Hr0 & _) | (_ & g & s & Epre & Hobj & Hat & Hwf & HW & HH & Hown)]; [exfalso; exact (Hc Hr0)|].
rebaseE HS AG HEv; clear HEv.
rt_hand RFF HS.
split; [clear - Hk0; lia|]. split; [cbn [c_n]; exact HnC|]. split; [exists curi; cbn [c_n]; split; [ewpeel; exact Ecur | exact Hcuri]|].
exists res, (Wd * Hd). split; [ewpeel; exact Rres|]. split; [ewpeel; exact E542|]. split; [unfold RGB_NMAX; exact HNle|].
unfold rt_obj. cbn [c_ly c_S]. exists g, s, A_writecb, 0, 0, attr, gen, loops, Wd, Hd, 0, 0, R_PENDING.
split.
{ lazymatch goal with |- obj_at _ (mrestrict (w_H ?Wf) ?mf) _ _ _ =>
apply (rg_obj_at_blk_kept (w_H W4) (w_H Wf) mem4 mf res LAY_Rgb _ RGB_SIZE Hobj lay_inside_Rgb) end.
exact (KB res RGB_SIZE ltac:(rewrite Epre; left; reflexivity)). }
split.
{ lazymatch goal with |- tcgif_at (mrestrict (w_H ?Wf) ?mf) _ _ =>
apply (tcgif_at_blocks_kept (w_H W4) (w_H Wf) mem4 mf g s (Wd * Hd) Hat) end.
intros b sz Hb. apply KB. rewrite Epre. right. exact Hb. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [left; reflexivity|].
split.
{ unfold trgb_own, optb. cbn [Z.eqb]. rewrite app_nil_r, <- Eab3. rewrite <- Epre. exact HPerm4. }
intros b Hb. unfold trgb_own, optb in Hb. cbn [Z.eqb] in Hb. rewrite app_nil_r in Hb. rewrite <- Eab3. apply Hown. exact Hb.
Qed.
Lemma rt_E : rt_from B ss_X (INV_X B) -> rt_from B ss_F (INV_F B) -> rt_from B ss_E (INV_E B).
Proof. exact rt_E_aux. Qed.
End d.
End c.
