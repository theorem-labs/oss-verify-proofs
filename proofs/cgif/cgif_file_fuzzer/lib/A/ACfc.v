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
Variables (wfn rlo rhi : Z).
Hypothesis TADDFX : taddframe_specX tfibsegs tfib_K B MT XN A_cgif_addframe CTX_cgif_addframe wfn rlo rhi.
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
Hypothesis XApos : forall n, 0 <= n -> 0 <= xn_addframe XN n <= xm_addframe XN n.
Hypothesis XCpos : forall n, 0 <= n -> 0 <= xn_close XN n <= xm_close XN n.
Hypothesis HXL2 : forall cx xc, rt_base B MT cx -> rt_xbase2 B MT XL cx xc -> XROOM MT XN xc (c_T cx).
Hypothesis HRO : forall rd, arodata_ok B rd -> arodata_okP tfibsegs rlo rhi B rd.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_G1X_aux : forall cnt : Z, rt_fromX B MT XL POST ss_G2 (INV_G2X B MT XN wfn cnt) -> rt_fromX B MT XL POST ss_G (INV_G1X B MT XN wfn cnt).
Proof.
intros cnt RG2. rt_preludeX.
pose proof HINV as (Hk & Hacc & Hc & E400 & s & cur & lpal & lpa & img & fattr & fgen & delay & nlp & tidx & gs & IMGV & LPALV & HOBJ & HSTM & HFC & HREL & HIMG & HIMGn & HLP & HLF).
pose proof HOBJ as (E195 & E194 & Hn14 & Hat & Hwf & HGs & HPerm3). cbn [c_n c_ly c_S] in Hn14, HPerm3. xcb.
pose proof HSTM as (Vp & Vn & Vc & Rcur). cbn [c_n c_sp1 c_p] in Vp, Vn, Vc, Rcur.
pose proof HFC as (E402 & E403 & E404 & E405 & E406 & E407 & E408 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & Hlp0 & Hlpa).
pose proof Hwf as (Hlen3 & HW1 & HH1 & HNWH & HNle & _).
destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hn0 Hn14; lia|].
pose proof (mo_malloc_nonneg MT MTL 196605 ltac:(clear; lia)) as Hm1. pose proof (mo_malloc_nonneg MT MTL N ltac:(clear - HN1; lia)) as Hm2.
pose proof (mo_free_nonneg MT MTL) as Hf1. pose proof (XApos N ltac:(clear - HN1; lia)) as HxA. pose proof (XCpos N ltac:(clear - HN1; lia)) as HxC.
assert (HITER : 0 <= ITER MT XN (mkRTXC pl aM Kl G rest0 g f N)) by (unfold ITER, RFC_COST; cbn [x_N]; clear - Hm1 Hm2 Hf1 HxA; lia).
pose proof (proj1 (HXL2 _ _ HBASE0 HXB0)) as HROOM. unfold ACC_G, ACC_F in HROOM. cbn [x_N x_G c_T] in HROOM.
assert (Hcg3 : forall x, In x (cgif_blocks g s N ++ (f, FILE_BLOCK) :: rt_fblocks img N fattr lpa nlp) -> In x (ablocks B ly3 S3)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HPerm3|].
apply in_app_iff in Hx. destruct Hx as [Hx | [<- | Hx]].
- apply in_app_iff. left. exact Hx.
- apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
- apply in_app_iff. right. apply in_app_iff. left. exact Hx. }
assert (Hcgne : forall x, In x (cgif_blocks g s N ++ (f, FILE_BLOCK) :: rt_fblocks img N fattr lpa nlp) -> ~ In x (ablocks B ly S)).
{ intros x Hx Hxe.
assert (HP' : Permutation (ablocks B ly3 S3) ((cgif_blocks g s N ++ rt_fblocks img N fattr lpa nlp ++ [(f, FILE_BLOCK)]) ++ ablocks B ly S)).
{ eapply Permutation_trans; [exact HPerm3|]. rewrite <- !app_assoc. cbn [app]. apply Permutation_app_head.
apply Permutation_app_head. apply Permutation_refl. }
apply (tmp_not_entry B LAWS _ _ _ _ _ _ _ x HAR3 HP'); [|exact Hxe].
apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx | [<- | Hx]]; [left; exact Hx | right; apply in_app_iff; right; left; reflexivity | right; apply in_app_iff; left; exact Hx]. }
assert (HnFPs : forall a, 1 <= a -> ~ inFP RTFP a) by (intros a Ha (r & [<-|[]] & Hr); cbn in Hr; clear - Ha Hr; lia).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (B70 : bv_unsigned (ew E 70) = sp1) by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia).
assert (B75 : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (HSPB : alloc_ceiling <= spZ regs - LLVMF_STK /\ spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ F <= a < F + 32 \/ F + 80 <= a < F + 256).
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan A_cgif_addframe.
{ awrRT AG fpos F EFA3. }
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 HF8hi; lia).
cgif_kept_run HFr Hcg3 HJ3 Hfin3 EFA3 AG KA.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img). rename Himgv into HimgvA.
unrunRD HFr Zsm Usp B70 Hsp1 UN1. clear_frames.
vkeepUN UN1 Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UN1.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0.
rreg HS (@BV 5 10 I) Ra0. rreg HS (@BV 5 11 I) Ra1.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
assert (UF : bv_unsigned (ew E 75) = F) by (exact B75).
assert (U70 : bv_unsigned (ew E 70) = sp1) by (exact B70).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact U70);
assert (EraX : raZ rg = 0x80a34) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
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
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview tfibsegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iF := idx_of_base_off rs 75%nat 112 in let iF := eval vm_compute in iF in
let rF := eval vm_compute in (nth iF rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iF rF HS ltac:(vm_compute; reflexivity)) as HRF; cbn [ms_mem restrict] in HRF end.
Ltac fieldF HRF UF od w e V :=
lazymatch type of HRF with region_ok _ ?Ex _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region_any Ex _ 75 _ cs lo hi wlo whi od w e HRF UF ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
cbn [sv_denot] in V; rewrite ?ew_ewset_other, ?ew_havoc_old in V by nat_side;
try change (N.to_nat 8) with 8%nat in V; try change (N.to_nat 4) with 4%nat in V; try change (N.to_nat 2) with 2%nat in V; try change (N.to_nat 1) with 1%nat in V;
try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V; try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V;
try change (2 ^ (8 * Z.of_N 2)) with 65536 in V; try change (2 ^ (8 * Z.of_N 1)) with 256 in V end.
fieldF HRF UF 112 8%N (SOff 402 0) V1. fieldF HRF UF 120 8%N (SOff 403 0) V2. fieldF HRF UF 128 4%N (SOff 404 0) V3. fieldF HRF UF 132 4%N (SOff 405 0) V4.
fieldF HRF UF 136 2%N (SOff 406 0) V5. fieldF HRF UF 138 2%N (SOff 407 0) V6. fieldF HRF UF 140 1%N (SOff 408 0) V7.
rewrite (denot_atom_mod _ 402 lpal _ E402 R1), Z.mod_small in V1 by (exact R1).
rewrite (denot_atom_mod _ 403 img _ E403 R2), Z.mod_small in V2 by (exact R2).
rewrite (denot_atom_mod _ 404 fattr _ E404 ltac:(clear - R3; lia)), Z.mod_small in V3 by (exact R3).
rewrite (denot_atom_mod _ 405 fgen _ E405 ltac:(clear - R4; lia)), Z.mod_small in V4 by (exact R4).
rewrite (denot_atom_mod _ 406 delay _ E406 ltac:(clear - R5; lia)), Z.mod_small in V5 by (exact R5).
rewrite (denot_atom_mod _ 407 nlp _ E407 ltac:(clear - R6; lia)), Z.mod_small in V6 by (exact R6).
rewrite (denot_atom_mod _ 408 tidx _ E408 ltac:(clear - R7; lia)), Z.mod_small in V7 by (exact R7).
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (OcfgX : obj_at tfibsegs (mrestrict (w_H Wx) (ms_mem msX)) (F + 112) LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx]) end.
{ cbn [obj_at LAY_FrameConfig]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N Pos.to_nat].
rewrite <- !Z.add_assoc. cbn [Z.add Pos.add].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536. change (2 ^ (8 * 1)) with 256.
split; [split; [exact V1 | exact R1]|]. split; [split; [exact V2 | exact R2]|]. split; [split; [exact V3 | exact R3]|]. split; [split; [exact V4 | exact R4]|].
split; [split; [exact V5 | exact R5]|]. split; [split; [exact V6 | exact R6]|]. split; [split; [exact V7 | exact R7]|]. exact I. }
clear V1 V2 V3 V4 V5 V6 V7 HRF.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iS := idx_of_base rs 88%nat in let iS := eval vm_compute in iS in
let rS := eval vm_compute in (nth iS rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iS rS HS ltac:(vm_compute; reflexivity)) as HRS; cbn [ms_mem restrict] in HRS;
assert (US : bv_unsigned (ew E 88) = SB + F / 8) by (rewrite E88; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia);
assert (ZS : forall od, In (YP09.mkChunk od (CVal 1 (SLit 0))) (YP09.r_chunks rS) -> aview tfibsegs (w_H W3) (ms_mem msX) (SB + F / 8 + od) = Some 0);
[ let od := fresh "od" in let Hod := fresh "Hod" in intros od Hod;
lazymatch type of HRS with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 88 (SB + F / 8) cs lo hi wlo whi od 1%N (SLit 0) 0 HRS US Hod eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Vz end;
pose proof (Vz 0%nat ltac:(lia)) as Vz0; cbn [Z.of_nat] in Vz0; rewrite Z.add_0_r in Vz0;
unfold aview; rewrite Vz0; reflexivity
| clear HRS ] end.
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (AF : afobj B ly3 S3 Wx (ms_mem msX) (F + 112) 32) end.
{ split; [|split].
- exists 2, fpos. split; [exact Hfin3|]. split; [clear; lia|]. rewrite EFA3. fold F. split; [rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); apply Z_mod_mult|].
change (fs_frame_bytes 2) with 256. clear; lia.
- rewrite HFq. replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by (clear; lia). apply Z_mod_mult.
- apply zero_shadow_of_bytes; [rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by (clear; lia); apply Z_mod_mult | reflexivity | clear; lia |].
intros j Hj. change (32 / 8) with 4 in Hj. rewrite <- SB_SHADOW_OFF.
replace ((F + 112) / 8) with (F / 8 + 14) by (rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia);
replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia); clear; lia).
replace (SB + (F / 8 + 14) + j) with (SB + F / 8 + (14 + j)) by (clear; lia).
assert (Hj4 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia).
destruct Hj4 as [-> | [-> | [-> | ->]]]; apply ZS; cbn; tauto. }
clear ZS.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _).
assert (HEVc : st_nev S3 + EV_ADDFRAME <= EV_MAX) by (replace EV_ADDFRAME with 47 by reflexivity; rewrite HEV in Hev; clear - Hnev3 Hev Hk Hc; lia).
assert (HLIVEc : blocks_bytes S3 + LIVE_ADDFRAME <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPerm3), !bsum_app, bsum_cons, <- (blocks_bytes_bsum B ly S). cbn [snd].
pose proof (xcgif_blocks_bsum wfn _ _ _ _ g s N Hat Hwf) as Hcb. unfold CGB in Hcb. unfold LIVE_LIB in Hlive. unfold LIVE_ADDFRAME, FILE_BLOCK.
unfold rt_fblocks. rewrite bsum_cons. cbn [snd].
assert (Hfb : bsum (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) <= 3 * 65536) by (destruct (Z.land fattr 1 =? 0); cbn [bsum fold_right snd]; clear - R6; lia).
clear - Hlive Hcb Hfb HN1. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HRELc : cgif_relA tfibsegs tfib_K (mrestrict (w_H W3) (ms_mem msX)) mdX s f N (YO07.g_gpal G) gs);
[ eapply (cgif_relA_keptX tfib_K); [| | destruct md3; reflexivity | destruct md3; reflexivity | exact (proj1 HREL)];
[ intros b sz i Hb Hi; apply (mbyte_of_aview tfibsegs); apply (KA b sz); [apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|[Hb|[]]]; [left; exact Hb | right; left; exact Hb] | pose proof (le_req_size sz); clear - Hi H; lia]
| intros a Ha; apply (mbyte_of_aview tfibsegs); apply HimgvA; exact (proj1 (ail_env _ _ _ AIL a Ha)) ]
| assert (HIMGc : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msX)) img IMGV)
by (eapply garr8_frame; [exact HIMG|]; intros a Ha; apply (mbyte_of_aview tfibsegs); replace a with (img + (a - img)) by (clear; lia);
apply (KA img N); [apply in_app_iff; right; right; left; reflexivity | pose proof (le_req_size N ltac:(clear - HN1; lia)); clear - Ha HIMGn H; lia]);
assert (HLPc : Z.land fattr 1 <> 0 -> garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msX)) lpa LPALV /\ Z.of_nat (length LPALV) = 3 * nlp)
by (intros Hb1; destruct (HLP Hb1) as [Hg Hlen]; split; [|exact Hlen]; eapply garr8_frame; [exact Hg|]; intros a Ha; apply (mbyte_of_aview tfibsegs);
replace a with (lpa + (a - lpa)) by (clear; lia); apply (KA lpa (3 * nlp));
[ apply in_app_iff; right; right; unfold rt_fblocks; right; destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hz|Hz]; [exfalso; exact (Hb1 Hz) | left; reflexivity]
| pose proof (le_req_size (3 * nlp) ltac:(clear - R6; lia)); clear - Ha Hlen H; lia ]) ] end.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call_tok B LAWS W3 Ex ssX msX LLVMF_STK (spZ regs) RTFP ly S W mem md [(2, fpos)] ly3 S3 mdX k
TADDFRAME_STK (ablocks_fp (cgif_blocks g s N) ++ asink_fp f) EV_ADDFRAME (sp1 - spZ regs) (ew Ex 2) (Z_to_bv 64 0x80a34) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T))
(fun ly2 S2 W2 regs2 mem2 md2 => exists s' : cgif_st,
xcgif_at tfibsegs wfn (ak_path tfib_K) 0 f (mrestrict (w_H W2) mem2) g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
cg_gen s' = cg_gen s /\ cg_ngp s' = cg_ngp s /\ cg_pal s' = cg_pal s /\
Permutation (ablocks B ly2 S2) (cgif_blocks g s' N ++ rt_fblocks img N fattr lpa nlp ++ (f, FILE_BLOCK) :: ablocks B ly S) /\
(forall b, In b (cgif_blocks g s' N) ->
aftok (ablocks_fp (cgif_blocks g s N) ++ asink_fp f) (ablocks B ly3 S3) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TADDFRAME_STK (spZ (ms_regs msX)) (ablocks_fp (cgif_blocks g s N) ++ asink_fp f) (ablocks B ly3 S3) blc ly2 [] (fst b + i)) /\
cgif_relA tfibsegs tfib_K (mrestrict (w_H W2) mem2) md2 s' f N (YO07.g_gpal G) (YO07.add_frame (gcfg_of s (YO07.g_gpal G)) gs fattr fgen delay tidx nlp LPALV IMGV) /\
Z.of_nat (length (concat (YO07.s_out (YO07.add_frame (gcfg_of s (YO07.g_gpal G)) gs fattr fgen delay tidx nlp LPALV IMGV)))) <= Z.of_nat (length (concat (YO07.s_out gs))) + FRAME_OUT N /\
mo_le MT S3 S2 (xn_addframe XN N)) HS eq_refl HJ3);
[ first [ rewrite Rsp; rewrite ?sv_denot_SOff0; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Usp3; f_equal; clear; lia | match goal with |- ?gg => idtac "AJ1" gg end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ exact Usp3 | idtac "AJ3" ]
| first [ rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity | match goal with |- ?gg => idtac "AJ4" gg end ]
| first [ clear - Hsp1; lia | idtac "AJ5" ]
| first [ apply Zle_bool_imp_le; vm_compute; reflexivity | idtac "AJ6" ]
| first [ replace TADDFRAME_STK with 17664 by reflexivity; rewrite FFS; clear - Hsp1; lia | match goal with |- ?gg => idtac "AJ7" gg end ]
| first [ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Ugp; exact Hgp | idtac "AJ8" ]
| first [ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Utp; exact Htp | idtac "AJ9" ]
| first [ exact Rra | idtac "AJ10" ]
| first [ apply ret_ok_even; vm_compute; reflexivity | idtac "AJ11" ]
| first [ rewrite unsigned_lit_small by (clear; lia); clear; lia | idtac "AJ12" ]
| first [ rewrite Es0X; replace (spZ regs + (sp1 - spZ regs)) with sp1 by (clear; lia); exact Hch1 | match goal with |- ?gg => idtac "AJ13" gg end ]
| first [ intros HPRE1; eapply SRr_mono;
[ first [ pose proof (TADDFX ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T))
g (F + 112) s N lpal lpa img fattr fgen delay nlp tidx f (ak_path tfib_K) 0 (ablocks B ly S) (YO07.g_gpal G) IMGV LPALV gs HPRE1) as CALL | idtac "CALL-POSE" ];
unfold cfg_at, apost_base in CALL; cbn [ss_pc]; change (w64 A_cgif_addframe) with (Z_to_bv 64 531304) in CALL;
first [ apply CALL | match goal with |- ?gg => idtac "CALL-APPLY" gg end; let t := type of CALL in idtac "CALL-TYPE" t ]; clear CALL;
[ first [ rewrite EraX; apply rt_ctx_in; [exact Hra | vm_compute; tauto | vm_compute; tauto] | match goal with |- ?gg => idtac "CA2" gg end ]
| first [ rewrite Hfrs3; cbn [length]; clear; lia | idtac "CA3" ]
| first [ apply HRO; eapply arodata_ok_journal; [exact HJ3 | exact HROD] | idtac "CA4" ]
| first [ rewrite Ra0; rewrite ?sv_denot_SOff0; ewpeel; exact E195 | match goal with |- ?gg => idtac "CA5" gg end ]
| first [ rewrite Ra1, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite UF; reflexivity | match goal with |- ?gg => idtac "CA6" gg end ]
| first [ exact AF | idtac "CA7" ]
| first [ exact OcfgX | match goal with |- ?gg => idtac "CA8" gg end ]
| first [ apply (xcgif_at_blocks_kept wfn _ _ _ _ _ _ _ g s N Hat); intros b sz Hb; apply KA; apply in_app_iff; left; exact Hb | match goal with |- ?gg => idtac "CA9" gg end ]
| first [ exact Hwf | match goal with |- ?gg => idtac "CA10" gg end ]
| first [ exact Hf0 | match goal with |- ?gg => idtac "CA10b" gg end ]
| first [ exact Hlpa | match goal with |- ?gg => idtac "CA11" gg end ]
| first [ exact HPerm3 | match goal with |- ?gg => idtac "CA12" gg end ]
|   first [ exact HRELc | match goal with |- ?gg => idtac "CA13" gg end ]
| first [ pose proof (proj2 HREL) as HLEN; cbn [x_N x_G] in HLEN; unfold SINK_MAX, HDR_OUT, FRAME_OUT in *; clear - HLEN HN1 Hc; nia | match goal with |- ?gg => idtac "CA14" gg end ]
| first [ exact HIMGc | match goal with |- ?gg => idtac "CA15" gg end ]
| first [ exact HIMGn | match goal with |- ?gg => idtac "CA16" gg end ]
| first [ exact HLPc | match goal with |- ?gg => idtac "CA17" gg end ]
| first [ exact HEVc | match goal with |- ?gg => idtac "CA21" gg end ]
| first [ exact HLIVEc | match goal with |- ?gg => idtac "CA22" gg end ]
|   first [ apply (mok_station MT S S3 T acc (xm_addframe XN N) MTL HMOK HMLE); [clear - HxA; lia | unfold ACC_G, ACC_F, ITER, RFC_COST in *; cbn [x_G x_N] in Hacc, HROOM, HITER; clear - Hacc HROOM HITER Hm1 Hm2 Hf1 HxA HxC Hc; nia] | match goal with |- ?gg => idtac "CA23" gg end ] ]
| first [ cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HPc & s' & Hpost);
exists ly4, S4, regs4, mem4, md4; split; [rewrite Rra; reflexivity|]; split; [exact HJc|];
split; [exact HPc|]; exists s'; exact Hpost | match goal with |- ?g => idtac "CALL-POST" g end ] ]
| idtac "AJ14" ]
| first [ intros a Ha; apply inFP_app in Ha; destruct Ha as [Ha | Ha];
[ right; destruct (inFP_ablocks_fp_inv _ a Ha) as (pb & nb & Hpb & Hab); exists pb, nb;
split; [apply Hcg3; apply in_app_iff; left; exact Hpb | split; [apply Hcgne; apply in_app_iff; left; exact Hpb | exact Hab]]
| destruct (proj1 (in_asink_fp f a) Ha) as [Hab | Htok];
[ right; exists f, FILE_BLOCK; split; [apply Hcg3; apply in_app_iff; right; left; reflexivity | split; [apply Hcgne; apply in_app_iff; right; left; reflexivity | pose proof (le_req_size FILE_BLOCK ltac:(unfold FILE_BLOCK; clear; lia)); clear - Hab H; lia]]
| left; exists YI16.sink_token; split; [left; reflexivity | cbn; clear - Htok; lia] ] ]
| match goal with |- ?g => idtac "AJ15" g end ] ]
| ] end end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & s' & Hat4 & Hwf4 & HW4 & HH4 & Hattr4 & Hraw4 & Hgen4 & Hngp4 & Hpal4 & HPerm4 & Hown4 & HREL4 & HLEN4 & HMLE4).
pose proof (mle_station MT S S3 S4 acc (xn_addframe XN N) MTL HMLE HMLE4) as HMLE4c.
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
assert (HFPblk : forall a, 1 <= a -> inFP (ablocks_fp (cgif_blocks g s N) ++ asink_fp f) a -> exists pb nb, In (pb, nb) (cgif_blocks g s N ++ (f, FILE_BLOCK) :: rt_fblocks img N fattr lpa nlp) /\ pb <= a < pb + req_size nb).
{ intros a Ha1 Hin. apply inFP_app in Hin. destruct Hin as [Hin | Hin].
- destruct (inFP_ablocks_fp_inv _ a Hin) as (pb & nb & Hpb & Hab). exists pb, nb. split; [apply in_app_iff; left; exact Hpb | exact Hab].
- destruct (proj1 (in_asink_fp f a) Hin) as [Hab | Htok]; [|exfalso; clear - Ha1 Htok; lia].
exists f, FILE_BLOCK. split; [apply in_app_iff; right; left; reflexivity | pose proof (le_req_size FILE_BLOCK ltac:(unfold FILE_BLOCK; clear; lia)); clear - Hab H; lia]. }
assert (HnFPF : forall a, F <= a < F + 256 -> ~ inFP (ablocks_fp (cgif_blocks g s N) ++ asink_fp f) a).
{ intros a Ha Hin. destruct (HFPblk a ltac:(clear - Ha HF4096; lia) Hin) as (pb & nb & Hpb & Hab).
pose proof (sep_block_frame tfibsegs _ LAWS ly3 S3 _ _ _ pb nb 2 fpos HAR3 (Hcg3 _ Hpb) Hfin3) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 2) with 256 in Hd. rewrite EFA3 in Hd. fold F in Hd. clear - Ha Hab Hd. lia. }
assert (HnFPlo : forall a, SB <= a < 17594333495296 -> ~ inFP (ablocks_fp (cgif_blocks g s N) ++ asink_fp f) a).
{ intros a Ha Hin. destruct (HFPblk a ltac:(clear - Ha; unfold SB in *; lia) Hin) as (pb & nb & Hpb & Hab).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HAR3 (Hcg3 _ Hpb)) as (_ & _ & _ & Hbh_ia & _). pose proof (proj1 Hbh_ia) as Hbh. clear - Ha Hab Hbh_ia C3. unfold SB in *. zone_lia. }
assert (HnFPhi : forall a, alloc_ceiling <= a -> ~ inFP (ablocks_fp (cgif_blocks g s N) ++ asink_fp f) a).
{ intros a Ha Hin. destruct (HFPblk a ltac:(clear - Ha C1; lia) Hin) as (pb & nb & Hpb & Hab).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HAR3 (Hcg3 _ Hpb)) as (_ & _ & Hbc & _). clear - Ha Hab Hbc. lia. }
vkeep Vp (w_H W4) mem4 ltac:(pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Hi Hsp1 HSPB C1 FFS; lia).
vkeep Vn (w_H W4) mem4 ltac:(pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Hi Hsp1 HSPB C1 FFS; lia).
vkeep Vc (w_H W4) mem4 ltac:(pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Hi Hsp1 HSPB C1 FFS; lia).
reseatL HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFPlo; clear - Ha HF8c HF8lo HFceil C1; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFPF; clear - Ha; lia | intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJc | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
assert (Hcg4 : forall x, In x (cgif_blocks g s' N) -> In x (ablocks B ly4 S4))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; apply in_app_iff; left; exact Hx).
assert (HGs4 : gcfg_of s' (YO07.g_gpal G) = G) by (rewrite <- HGs; unfold gcfg_of; rewrite HW4, HH4, Hattr4, Hgen4, Hngp4; reflexivity).
rewrite HGs in HREL4, HLEN4.
ra_join_win HS ss_G2 450%nat rt_G_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. rt_handX RG2 HS.
split; [replace EV_ADDFRAME with 47 by reflexivity; clear - Hk; lia|].
split; [unfold ACC_G2, ACC_G, ACC_F, ITER, RFC_COST in *; cbn [x_G x_N] in *; clear - Hacc; lia|].
split; [exact Hc|]. split; [exact E400|].
exists s', cur, lpal, lpa, img, fattr, fgen, delay, nlp, tidx, (YO07.add_frame G gs fattr fgen delay tidx nlp LPALV IMGV).
split.
{ unfold rt_objX. cbn [c_n c_ly c_S x_gp x_N x_f x_G].
split; [exact E195|]. split; [exact E194|]. split; [exact Hn14|].
split; [exact Hat4|]. split; [exact Hwf4|]. split; [exact HGs4|].
exact HPerm4. }
split.
{ unfold rt_stm. cbn [c_sp1 c_p c_n]. split; [exact Vp|]. split; [exact Vn|]. split; [exact Vc | exact Rcur]. }
split.
{ unfold rt_fcfg.
split; [exact E402|]. split; [exact E403|]. split; [exact E404|]. split; [exact E405|].
split; [exact E406|]. split; [exact E407|]. split; [exact E408|].
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6|]. split; [exact R7|].
split; [exact Hlp0 | exact Hlpa]. }
split.
{ split; [exact HREL4|]. pose proof (proj2 HREL) as HLEN. cbn [x_N x_G] in *. clear - HLEN HLEN4 Hc. nia. }
exact HLF.
Qed.
Lemma rt_G1X : forall cnt : Z, rt_fromX B MT XL POST ss_G2 (INV_G2X B MT XN wfn cnt) -> rt_fromX B MT XL POST ss_G (INV_G1X B MT XN wfn cnt).
Proof. exact rt_G1X_aux. Qed.
End d.
End c.
