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
Hypothesis TRFCX : trfc_specX B MT.
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
Hypothesis XApos : forall n, 0 <= n -> 0 <= xn_addframe XN n <= xm_addframe XN n.
Hypothesis XCpos : forall n, 0 <= n -> 0 <= xn_close XN n <= xm_close XN n.
Hypothesis HXL2 : forall cx xc, rt_base B MT cx -> rt_xbase2 B MT XL cx xc -> XROOM MT XN xc (c_T cx).
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_FX_aux : rt_fromX B MT XL POST ss_H (INV_HX B MT XN wfn) -> rt_fromX B MT XL POST ss_G (INV_G1X B MT XN wfn 16) ->
rt_fromX B MT XL POST ss_F (INV_FX B MT XN wfn).
Proof.
intros RH RG. rt_preludeX.
pose proof HINV as (Hk14 & Hacc & s & cur & gs & HOBJ & HSTM & HREL & HLF).
pose proof HOBJ as (E195 & E194 & Hn14 & Hat & Hwf & HGs & HPerm3). cbn [c_n c_ly c_S] in Hn14, HPerm3. xcb.
pose proof HSTM as (Vp & Vn & Vc & Rcur). cbn [c_n c_sp1 c_p] in Rcur, Vp, Vn, Vc.
rewrite app_nil_l in HPerm3 || cbn [app] in HPerm3.
pose proof Hwf as (Hlen3 & HW1 & HH1 & HNWH & HNle & _).
destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hn0 Hn14; lia|].
pose proof (mo_malloc_nonneg MT MTL 196605 ltac:(clear; lia)) as Hm1. pose proof (mo_malloc_nonneg MT MTL N ltac:(clear - HN1; lia)) as Hm2.
pose proof (mo_free_nonneg MT MTL) as Hf1. pose proof (XApos N ltac:(clear - HN1; lia)) as HxA. pose proof (XCpos N ltac:(clear - HN1; lia)) as HxC.
assert (HITER : 0 <= ITER MT XN (mkRTXC pl aM Kl G rest0 g f N)) by (unfold ITER, RFC_COST; cbn [x_N]; clear - Hm1 Hm2 Hf1 HxA; lia).
pose proof (proj2 (HXL2 _ _ HBASE0 HXB0)) as HROOM. unfold ACC_H, ACC_F in HROOM. cbn [x_N x_G c_T] in HROOM.
assert (Hcg3 : forall x, In x (cgif_blocks g s N ++ [(f, FILE_BLOCK); (p, n)]) -> In x (ablocks B ly3 S3)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HPerm3|].
apply in_app_iff in Hx. destruct Hx as [Hx | [<- | [<- | []]]]; [apply in_app_iff; left; exact Hx | apply in_app_iff; right; left; reflexivity | apply in_app_iff; right; right; exact Hpin]. }
assert (HnFPs : forall a, 1 <= a -> ~ inFP RTFP a) by (intros a Ha (r & [<-|[]] & Hr); cbn in Hr; clear - Ha Hr; lia).
assert (HPL3 : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) p (zbytes pl)).
{ eapply (garr8_of_F2 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n (zbytes pl) HJ3 Hpin (Hcg3 _ ltac:(apply in_app_iff; right; right; left; reflexivity)));
[ intros i Hi; apply HnFPs; destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpin) as (_ & Hp4096 & _); clear - Hi Hp4096; lia
| unfold zbytes; rewrite length_map; clear - Hnpl; lia
| apply le_req_size; clear - Hnpos; lia
| exact HPL0 ]. }
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (B70 : bv_unsigned (ew E 70) = sp1) by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia).
assert (B75 : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (HSPB : alloc_ceiling <= spZ regs - LLVMF_STK /\ spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ F <= a < F + 32 \/ F + 80 <= a < F + 256).
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan A_read_frameconfig.
{ awrRT AG fpos F EFA3. }
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 HF8hi; lia).
cgif_kept_run HFr Hcg3 HJ3 Hfin3 EFA3 AG KA.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img). rename Himgv into HimgvA.
unrunRD HFr Zsm Usp B70 Hsp1 UN1. clear_frames.
vkeepUN UN1 Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UN1.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0.
rreg HS (@BV 5 10 I) Ra0. rreg HS (@BV 5 11 I) Ra1. rreg HS (@BV 5 12 I) Ra2.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (UF : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (U70 : bv_unsigned (ew E 70) = sp1) by (exact B70).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact U70);
assert (EraX : raZ rg = 0x80a20) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
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
assert (RAdst : range_addressable (aview tfibsegs (w_H Wx) (ms_mem msX)) SHADOW_OFF (F + 112) 32) end.
{ apply zero_shadow_of_bytes; [rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by (clear; lia); apply Z_mod_mult | reflexivity | clear; lia |].
intros j Hj. change (32 / 8) with 4 in Hj. rewrite <- SB_SHADOW_OFF.
replace ((F + 112) / 8) with (F / 8 + 14) by (rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia);
replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia); clear; lia).
replace (SB + (F / 8 + 14) + j) with (SB + F / 8 + (14 + j)) by (clear; lia).
assert (Hj4 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia).
destruct Hj4 as [-> | [-> | [-> | ->]]]; apply ZS; cbn; tauto. }
clear ZS.
pose proof (proj1 (proj2 HJ3)) as HLY3. pose proof HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & Eslo3 & Eshi3 & _).
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (RAst : range_addressable (aview tfibsegs (w_H Wx) (ms_mem msX)) SHADOW_OFF (sp1 + 8) 24)
by (apply (range_addressable_stack B LAWS ly3 S3 _ _ _ (sp1 + 8) 24 (proj1 HJ3)); [rewrite Eslo3; clear - Hsp1 Hslo FFS; lia | rewrite Eshi3; clear - Hsp1 Hshi; lia | clear; lia]) end.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
assert (HLIVEc : blocks_bytes S3 + LIVE_RFC <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPerm3), bsum_app, bsum_cons, <- (blocks_bytes_bsum B ly S). cbn [snd].
pose proof (xcgif_blocks_bsum wfn _ _ _ _ g s N Hat Hwf) as Hcb. unfold CGB in Hcb. unfold LIVE_LIB in Hlive. unfold LIVE_RFC, FILE_BLOCK. clear - Hlive Hcb. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HRELc : cgif_relA tfibsegs tfib_K (mrestrict (w_H W3) (ms_mem msX)) mdX s f N (YO07.g_gpal G) gs);
[ eapply (cgif_relA_keptX tfib_K); [| | destruct md3; reflexivity | destruct md3; reflexivity | exact (proj1 HREL)];
[ intros b sz i Hb Hi; apply (mbyte_of_aview tfibsegs); apply (KA b sz); [apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|[Hb|[]]]; [left; exact Hb | right; left; exact Hb] | pose proof (le_req_size sz); clear - Hi H; lia]
| intros a Ha; apply (mbyte_of_aview tfibsegs); apply HimgvA; exact (proj1 (ail_env _ _ _ AIL a Ha)) ]
| assert (HPLc : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msX)) p (zbytes pl))
by (eapply garr8_frame; [exact HPL3|]; intros a Ha; apply (mbyte_of_aview tfibsegs); replace a with (p + (a - p)) by (clear; lia);
apply (KA p n); [apply in_app_iff; right; right; left; reflexivity | unfold zbytes in Ha; rewrite length_map in Ha; pose proof (le_req_size n ltac:(clear - Hnpos; lia)); clear - Ha Hnpl H; lia]) ] end.
trim_nth HS 2%nat 144 256.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
change (Z_to_bv 64 527160) with (w64 A_read_frameconfig);
eapply SRr_bind;
[ eapply (TRFCX LLVMF_STK (spZ regs) RTFP ly S W mem md [(2, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
(cgif_blocks g s N ++ (f, FILE_BLOCK) :: ablocks B ly S) (sp1 + 8) (F + 112) N p n cur 2 fpos (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) (RFC_COST MT N) (zbytes pl) HJ3);
[ first [ intros b Hb; apply in_app_iff; right; right; exact Hb | idtac "RF1" ]
| first [ exact HPerm3 | idtac "RF2" ]
| first [ apply in_app_iff; right; right; exact Hpin | idtac "RF3" ]
| first [ rewrite Rra; apply ret_ok_even; vm_compute; reflexivity | idtac "RF4" ]
| first [ rewrite EraX; clear; lia | idtac "RF5" ]
| first [ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 3%nat) by (clear; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp | idtac "RF6" ]
| first [ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 4%nat) by (clear; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp | idtac "RF7" ]
| first [ rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite U70; reflexivity | match goal with |- ?gg => idtac "RF8" gg end ]
| first [ rewrite Ra1, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite UF; reflexivity | match goal with |- ?gg => idtac "RF9" gg end ]
| first [ rewrite Ra2; rewrite ?sv_denot_SOff0; ewpeel; exact E194 | match goal with |- ?gg => idtac "RF10" gg end ]
| first [ rewrite EspX, Es0X; exact Hch1 | match goal with |- ?gg => idtac "RF11" gg end ]
| first [ rewrite EraX; apply rt_ctx_in; [exact Hra | vm_compute; tauto | vm_compute; tauto] | match goal with |- ?gg => idtac "RF12" gg end ]
| first [ rewrite EspX; exact Hsp1al16 | idtac "RF13" ]
| first [ rewrite EspX; replace TRFC_STK with 16496 by reflexivity; rewrite FFS; clear - Hsp1; lia | match goal with |- ?gg => idtac "RF14" gg end ]
| first [ rewrite EspX; clear - Hsp1; lia | idtac "RF15" ]
| first [ left; reflexivity | idtac "RF16" ]
| first [ clear; lia | idtac "RF17" ]
| first [ rewrite EFA3; fold F; rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); apply Z_mod_mult | match goal with |- ?gg => idtac "RF18" gg end ]
| first [ rewrite EFA3; fold F; clear; lia | idtac "RF19" ]
| first [ rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia | idtac "RF20" ]
| first [ rewrite HFq; replace (32 * (F / 32) + 112) with ((4 * (F / 32) + 14) * 8) by (clear; lia); apply Z_mod_mult | idtac "RF21" ]
| first [ rewrite EspX; clear; lia | idtac "RF22" ]
| first [ clear - Hsp1; lia | idtac "RF23" ]
| first [ apply sp1_st8; exact Hsp1al | match goal with |- ?gg => idtac "RF24" gg end ]
| first [ exact RAst | match goal with |- ?gg => idtac "RF25" gg end ]
| first [ exact RAdst | match goal with |- ?gg => idtac "RF26" gg end ]
| first [ exact HN1 | idtac "RF27" ]
| first [ exact Rcur | idtac "RF28" ]
| first [ clear - Hnpos; lia | idtac "RF29" ]
| first [ exact Vp | match goal with |- ?gg => idtac "RF30" gg end ]
| first [ exact Vn | match goal with |- ?gg => idtac "RF31" gg end ]
| first [ exact Vc | match goal with |- ?gg => idtac "RF32" gg end ]
| first [ replace EV_RFC with 6 by reflexivity; rewrite HEV in Hev; clear - Hev Hk14; lia | match goal with |- ?gg => idtac "RF33" gg end ]
| first [ exact HLIVEc | idtac "RF34" ]
|   first [ exact HPLc | idtac "RF35" ]
| first [ unfold zbytes; rewrite length_map; clear - Hnpl; lia | idtac "RF36" ]
| first [ apply (mok_station MT S S3 T acc (RFC_COST MT N) MTL HMOK HMLE); [unfold RFC_COST; clear - Hm1 Hm2 Hf1; lia | unfold ITER, RFC_COST in *; unfold ACC_F in Hacc; cbn [x_G x_N] in Hacc, HROOM, HITER; clear - Hacc HROOM HITER Hm1 Hm2 Hf1 HxA HxC; nia] | match goal with |- ?gg => idtac "RF37" gg end ]
| first [ apply Z.le_refl | idtac "RF38" ] ]
| ] end end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & cur2 & -> & HJ4 & HP4 & Hfrs4 & Ha04 & K1 & K2 & K3 & K4 & HIO4 & Vp4 & Vn4 & Vc4 & Hcur2 & HMLE4 & Hres).
rewrite EspX in K1. rewrite Rra.
pose proof (mle_station MT S S3 S4 acc (RFC_COST MT N) MTL HMLE HMLE4) as HMLE4c.
lazymatch type of HRELc with cgif_relA _ _ (mrestrict _ (ms_mem ?msX)) ?mdX _ _ _ _ _ =>
assert (HREL4 : cgif_relA tfibsegs tfib_K (mrestrict (w_H W4) mem4) md4 s f N (YO07.g_gpal G) gs);
[ eapply (cgif_relA_keptX tfib_K); [| | | | exact HRELc];
[ intros b sz i Hb Hi; apply (mbyte_of_aview tfibsegs); apply (K2 b sz i); [apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|[Hb|[]]]; [left; exact Hb | right; left; exact Hb] | pose proof (le_req_size sz); clear - Hi H; lia]
| intros a Ha; apply (mbyte_of_aview tfibsegs); destruct (ail_env _ _ _ AIL a Ha) as (Hi & Hns & He); exact (K4 a Hi Hns He)
| destruct HIO4 as (Efd & _ & Efsys & _); unfold m_fds; rewrite Efd; reflexivity
| destruct HIO4 as (Efd & _ & Efsys & _); unfold m_fs; rewrite Efsys; reflexivity ]
| ] end.
clear Rra Rsp Rgp Rtp Rs0 Ra1 Ra2 Vra Vs0 Hch1 RAst RAdst Vp Vn Vc HLIVEc HRELc HPLc.
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(2, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
reseatL HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply rt_region_kept_eq; [ first [evalE AG | idtac "K88-0"]
| intros a Ha; first [apply (K3 2 fpos a Hfin3) | match goal with |- ?g => idtac "K88-APPLY" g end];
[ first [right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear - Ha; unfold SB in *; lia | match goal with |- ?g => match type of Ha with ?t => idtac "K88-1" t g end end]
| first [clear - Ha HF8c HF8lo HFhigh C3; unfold SB in *; zone_lia | match goal with |- ?g => match type of Ha with ?t => idtac "K88-2" t g end end]
| first [clear - Ha HF8hi Hsp1 Hceil Hslo FFS C1; unfold SB in *; lia | match goal with |- ?g => idtac "K88-3" g end] ]
| intros a Ha; first [exfalso; clear - Ha; lia | match goal with |- ?g => match type of Ha with ?t => idtac "K88-4" t g end end] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply rt_region_kept_eq; [ evalE AG
| intros a Ha; apply (K3 2 fpos a Hfin3);
[ left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear - Ha; lia
| clear - Ha; lia | clear - Ha HFceil Hsp1 Hceil Hslo FFS C1; lia ]
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply rt_region_kept_eq; [ evalE AG
| intros a Ha; apply K1; [clear - Ha Hceil Hslo Hshi H47 FFS C1; lia | clear - Ha Hsp1; lia | clear - Ha HFceil Hceil Hslo FFS C1; lia | clear - Ha Hsp1; lia]
| intros a Ha; apply Hpres4; clear - Ha FFS; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
rreg HS (10%bv : bv 5) Rres. rewrite Ha04 in Rres. symmetry in Rres.
assert (KR : forall b sz, In (b, sz) (cgif_blocks g s N ++ [(f, FILE_BLOCK); (p, n)]) -> blk_kept (w_H W3) (w_H W4) (ms_mem ms) mem4 b (req_size sz))
by (intros b sz Hb i Hi; apply (K2 b sz i); [apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|[Hb|[Hb|[]]]]; [left; exact Hb | right; left; exact Hb | right; right; rewrite <- Hb; exact Hpin] | exact Hi]).
reshok HS.
srr_branch_tok tfibtbl_lib_ok HS SHOK RTBspan.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
lazymatch type of Rres with ew _ ?na = _ => hc_bool Hc ltac:(fun H => hc_atom H na res Rres ltac:(clear - Hres; destruct Hres as [(-> & _) | (-> & _)]; lia)) end. hc_prop Hc.
destruct Hres as [(Hr0 & Hparse & HPL) | (Hr1 & _)]; [|exfalso; clear - Hc Hr1; lia].
assert (Hcg4 : forall x, In x (cgif_blocks g s N ++ [(f, FILE_BLOCK); (p, n)]) -> In x (ablocks B ly4 S4))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPL|]; apply in_app_iff in Hx; apply in_app_iff; destruct Hx as [Hx|[<-|[<-|[]]]]; [left; exact Hx | right; left; reflexivity | right; right; exact Hpin]).
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ4 SHOK RTBspan 0x80a60.
{ awrRT AG fpos F EFA4. }
cgif_kept_run HFr Hcg4 HJ4 Hfin4 EFA4 AG KB.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img). rename Himgv into HimgvB.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
ra_join_win HS ss_H 260%nat rt_H_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. rt_handX RH HS.
split; [replace EV_RFC with 6 by reflexivity; clear - Hk14; lia|].
split; [unfold ACC_H, ACC_F, ITER, RFC_COST in *; cbn [x_G x_N] in *; clear - Hacc HITER Hm1 Hm2 Hf1 HxA HxC; nia|].
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wf) ?msf) =>
assert (KALL : forall b sz, In (b, sz) (cgif_blocks g s N ++ [(f, FILE_BLOCK); (p, n)]) -> blk_kept (w_H W3) (w_H Wf) (ms_mem ms3) (ms_mem msf) b (req_size sz))
by (intros b sz Hb; eapply blk_kept_trans; [exact (KA b sz Hb)|]; eapply blk_kept_trans; [exact (KR b sz Hb) | exact (KB b sz Hb)]) end.
exists s, gs. split.
{ unfold rt_objX. cbn [c_n c_ly c_S x_gp x_N x_f x_G].
split; [exact E195|]. split; [exact E194|]. split; [exact Hn14|].
split.
{ lazymatch goal with |- xcgif_at _ _ _ _ _ (mrestrict (w_H ?Wf) ?mf) _ _ => apply (xcgif_at_blocks_kept wfn _ _ _ (w_H W3) (w_H Wf) (ms_mem ms3) mf g s N Hat) end.
intros b sz Hb. apply KALL. apply in_app_iff. left. exact Hb. }
split; [exact Hwf|]. split; [exact HGs|].
eapply Permutation_trans; [exact HPL|]. cbn [app]. apply Permutation_refl. }
split.
{   split.
- lazymatch goal with |- cgif_relA _ _ (mrestrict (w_H ?Wf) (ms_mem ?msf)) ?mdf _ _ _ _ _ =>
eapply (cgif_relA_keptX tfib_K); [| | destruct md4; reflexivity | destruct md4; reflexivity | exact HREL4] end.
+ intros b sz i Hb Hi. apply (mbyte_of_aview tfibsegs). apply (KB b sz); [apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|[Hb|[]]]; [left; exact Hb | right; left; exact Hb] | pose proof (le_req_size sz); clear - Hi H; lia].
+ intros a Ha. apply (mbyte_of_aview tfibsegs). apply HimgvB. exact (proj1 (ail_env _ _ _ AIL a Ha)).
- pose proof (proj2 HREL) as HLEN. assert (HFO : 0 <= FRAME_OUT N) by (unfold FRAME_OUT; clear - HN1; lia). cbn [x_N x_G] in *. clear - HLEN HFO. nia. }
eapply (LF_stop (mkRTXC pl aM Kl G rest0 g f N) 16 gs cur); [|exact HLF]. cbn [x_G x_pl]. unfold parse_frame. rewrite <- HNG. exact Hparse.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
lazymatch type of Rres with ew _ ?na = _ => hc_bool Hc ltac:(fun H => hc_atom H na res Rres ltac:(clear - Hres; destruct Hres as [(-> & _) | (-> & _)]; lia)) end. hc_prop Hc.
destruct Hres as [(Hr0 & _) | (Hr1 & lpal & lpa & img & fattr & fgen & delay & nlp & tidx & LPALV & IMGV & Ofc & Hlp0 & Hlpa & HPL & Hown & Hparse & HIMG & HIMGn & HLP)]; [exfalso; clear - Hc Hr0; lia|].
assert (Hcg4 : forall x, In x ((cgif_blocks g s N ++ [(f, FILE_BLOCK); (p, n)]) ++ rt_fblocks img N fattr lpa nlp) -> In x (ablocks B ly4 S4)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HPL|]. unfold rt_fblocks in Hx.
apply in_app_iff in Hx. destruct Hx as [Hx | Hx]; [apply in_app_iff in Hx; destruct Hx as [Hx|[<-|[<-|[]]]]|].
- right. apply in_app_iff. right. apply in_app_iff. left. exact Hx.
- right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
- right. apply in_app_iff. right. apply in_app_iff. right. right. exact Hpin.
- destruct Hx as [<- | Hx]; [left; reflexivity | right; apply in_app_iff; left; exact Hx]. }
pose proof Ofc as Ofc'. cbn [obj_at LAY_FrameConfig] in Ofc. unfold field_ok in Ofc. cbn [fst snd N.to_nat Z.of_N Pos.to_nat] in Ofc.
rewrite <- !Z.add_assoc in Ofc. cbn [Z.add Pos.add] in Ofc.
change (2 ^ (8 * 8)) with (2 ^ 64) in Ofc. change (2 ^ (8 * 4)) with (2 ^ 32) in Ofc. change (2 ^ (8 * 2)) with 65536 in Ofc. change (2 ^ (8 * 1)) with 256 in Ofc.
destruct Ofc as ((V1 & R1) & (V2 & R2) & (V3 & R3) & (V4 & R4) & (V5 & R5) & (V6 & R6) & (V7 & R7) & _).
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
let WS := constr:([Z_to_bv 64 lpal; Z_to_bv 64 img; Z_to_bv 64 fattr; Z_to_bv 64 fgen; Z_to_bv 64 delay; Z_to_bv 64 nlp; Z_to_bv 64 tidx] : list word) in
pose proof (st_ok_havoc_win tfibsegs 402 Ev ssv msv WS HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (E402 : ew (havoc Ev 402 WS) 402 = Z_to_bv 64 lpal) by (exact (ew_havoc_new Ev 402 WS 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E403 : ew (havoc Ev 402 WS) 403 = Z_to_bv 64 img) by (exact (ew_havoc_new Ev 402 WS 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E404 : ew (havoc Ev 402 WS) 404 = Z_to_bv 64 fattr) by (exact (ew_havoc_new Ev 402 WS 2 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E405 : ew (havoc Ev 402 WS) 405 = Z_to_bv 64 fgen) by (exact (ew_havoc_new Ev 402 WS 3 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E406 : ew (havoc Ev 402 WS) 406 = Z_to_bv 64 delay) by (exact (ew_havoc_new Ev 402 WS 4 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E407 : ew (havoc Ev 402 WS) 407 = Z_to_bv 64 nlp) by (exact (ew_havoc_new Ev 402 WS 5 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E408 : ew (havoc Ev 402 WS) 408 = Z_to_bv 64 tidx) by (exact (ew_havoc_new Ev 402 WS 6 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
let HS3 := fresh "HS3" in
assert (UF2 : bv_unsigned (ew Ev2 75) = F) by (ewpeel; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia);
pose proof (ast_ok_add_region tfibsegs Ev2 _ _ rt_fconfig_region HS eq_refl
ltac:(unfold rt_fconfig_region, region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite UF2;
split; [clear - HF4096; lia|]; split; [clear - HFceil C1; lia|]; split;
[ intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres4 (F + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev2 _ F 112 8 (SOff 402 0) lpal); [rewrite sv_denot_SOff0; exact E402 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact R1 | clear; cbn; lia | exact V1]|];
apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev2 _ F 120 8 (SOff 403 0) img); [rewrite sv_denot_SOff0; exact E403 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact R2 | clear; cbn; lia | exact V2]|];
apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev2 _ F 128 4 (SOff 404 0) fattr); [rewrite sv_denot_SOff0; exact E404 | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact R3 | clear; cbn; lia | exact V3]|];
apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev2 _ F 132 4 (SOff 405 0) fgen); [rewrite sv_denot_SOff0; exact E405 | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact R4 | clear; cbn; lia | exact V4]|];
apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev2 _ F 136 2 (SOff 406 0) delay); [rewrite sv_denot_SOff0; exact E406 | change (2 ^ (8 * Z.of_N 2)) with 65536; exact R5 | clear; cbn; lia | exact V5]|];
apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev2 _ F 138 2 (SOff 407 0) nlp); [rewrite sv_denot_SOff0; exact E407 | change (2 ^ (8 * Z.of_N 2)) with 65536; exact R6 | clear; cbn; lia | exact V6]|];
apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev2 _ F 140 1 (SOff 408 0) tidx); [rewrite sv_denot_SOff0; exact E408 | change (2 ^ (8 * Z.of_N 1)) with 256; exact R7 | clear; cbn; lia | exact V7]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
unfold rt_fconfig_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
repeat split; first [clear - Hsp1 HFceil HF4096 HFhigh HFhigh_img Hceil Hslo Hstk0 FFS C1 C3 Hshi H47 HF8c HF8lo; unfold SB in *; zone_lia | match goal with |- ?g => idtac "DISJ-FC" g end])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
rebaseE HS AG HEvW; clear HEvW; relowRT HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ4 SHOK RTBspan 0x80a28.
{ awrRT AG fpos F EFA4. }
cgif_kept_run HFr Hcg4 HJ4 Hfin4 EFA4 AG KB.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img). rename Himgv into HimgvB.
unrunRD HFr Zsm Usp B70 Hsp1 UN2. clear_frames.
vkeepUN UN2 Vp4 Vn4 Vc4 ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UN2.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
add_atom_win HS 400%nat (Z_to_bv 64 16) E400.
rreg HS (24%bv : bv 5) Q22.
ws_pin HS (@BV 5 24 I) (SOff 400 0) Q22 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; first [exact E400 | rewrite E400; reflexivity | match goal with |- ?g => idtac "PIN400" g end]).
ra_join_win HS ss_G 410%nat rt_G_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. rt_handX RG HS.
split; [replace EV_RFC with 6 by reflexivity; clear - Hk14; lia|].
split; [unfold ACC_G, ACC_F, ITER, RFC_COST in *; cbn [x_G x_N] in *; clear - Hacc Hm1 Hm2 Hf1 HxA HxC; nia|].
split; [clear; lia|]. split; [exact E400|].
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wf) ?msf) =>
assert (KALL : forall b sz, In (b, sz) (cgif_blocks g s N ++ [(f, FILE_BLOCK); (p, n)]) -> blk_kept (w_H W3) (w_H Wf) (ms_mem ms3) (ms_mem msf) b (req_size sz))
by (intros b sz Hb; eapply blk_kept_trans; [exact (KA b sz Hb)|]; eapply blk_kept_trans; [exact (KR b sz Hb) | apply (KB b sz); apply in_app_iff; left; exact Hb]) end.
exists s, cur2, lpal, lpa, img, fattr, fgen, delay, nlp, tidx, gs, IMGV, LPALV.
split.
{ unfold rt_objX. cbn [c_n c_ly c_S x_gp x_N x_f x_G].
split; [exact E195|]. split; [exact E194|]. split; [exact Hn14|].
split.
{ lazymatch goal with |- xcgif_at _ _ _ _ _ (mrestrict (w_H ?Wf) ?mf) _ _ => apply (xcgif_at_blocks_kept wfn _ _ _ (w_H W3) (w_H Wf) (ms_mem ms3) mf g s N Hat) end.
intros b sz Hb. apply KALL. apply in_app_iff. left. exact Hb. }
split; [exact Hwf|]. split; [exact HGs|].
eapply Permutation_trans; [exact HPL|]. unfold rt_fblocks.
change ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ cgif_blocks g s N ++ (f, FILE_BLOCK) :: ablocks B ly S)
with (((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) ++ (cgif_blocks g s N ++ (f, FILE_BLOCK) :: ablocks B ly S)).
rewrite <- ?app_assoc. apply Permutation_app_swap_app. }
split.
{ unfold rt_stm. cbn [c_sp1 c_p c_n]. split; [exact Vp4|]. split; [exact Vn4|]. split; [exact Vc4 | clear - Hcur2 Rcur; lia]. }
split.
{ unfold rt_fcfg.
split; [exact E402|]. split; [exact E403|]. split; [exact E404|]. split; [exact E405|].
split; [exact E406|]. split; [exact E407|]. split; [exact E408|].
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6|]. split; [exact R7|].
split; [exact Hlp0 | exact Hlpa]. }
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wf) ?msf) =>
assert (KB4 : forall b sz i, In (b, sz) ((cgif_blocks g s N ++ [(f, FILE_BLOCK); (p, n)]) ++ rt_fblocks img N fattr lpa nlp) -> 0 <= i < sz ->
mbyte tfibsegs (mrestrict (w_H Wf) (ms_mem msf)) (b + i) = mbyte tfibsegs (mrestrict (w_H W4) mem4) (b + i))
by (intros b sz i Hb Hi; apply (mbyte_of_aview tfibsegs); apply (KB b sz Hb); pose proof (le_req_size sz); clear - Hi H; lia) end.
split.
{ split.
- eapply (cgif_relA_keptX tfib_K); [| | destruct md4; reflexivity | destruct md4; reflexivity | exact HREL4].
+ intros b sz i Hb Hi. apply (KB4 b sz i); [|exact Hi]. apply in_app_iff. left. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|[Hb|[]]]; [left; exact Hb | right; left; exact Hb].
+ intros a Ha. apply (mbyte_of_aview tfibsegs). apply HimgvB. exact (proj1 (ail_env _ _ _ AIL a Ha)).
- pose proof (proj2 HREL) as HLEN. cbn [x_N x_G] in *. clear - HLEN. lia. }
split.
{ eapply garr8_frame; [exact HIMG|]. intros a Ha. replace a with (img + (a - img)) by (clear; lia). apply (KB4 img N); [apply in_app_iff; right; left; reflexivity | clear - Ha HIMGn; lia]. }
split; [exact HIMGn|].
split.
{ intros Hb1. destruct (HLP Hb1) as [Hg Hlen]. split; [|exact Hlen]. eapply garr8_frame; [exact Hg|]. intros a Ha. replace a with (lpa + (a - lpa)) by (clear; lia).
apply (KB4 lpa (3 * nlp)); [|clear - Ha Hlen; lia]. apply in_app_iff. right. unfold rt_fblocks. right.
destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hz|Hz]; [exfalso; exact (Hb1 Hz) | left; reflexivity]. }
change (Z.to_nat 16 - 1)%nat with 15%nat. eapply (LF_step (mkRTXC pl aM Kl G rest0 g f N) 15 gs cur cur2); [|exact HLF].
cbn [x_G x_pl]. unfold parse_frame. rewrite <- HNG. exact Hparse.
Qed.
Lemma rt_FX : rt_fromX B MT XL POST ss_H (INV_HX B MT XN wfn) -> rt_fromX B MT XL POST ss_G (INV_G1X B MT XN wfn 16) ->
rt_fromX B MT XL POST ss_F (INV_FX B MT XN wfn).
Proof. exact rt_FX_aux. Qed.
End d.
End c.
