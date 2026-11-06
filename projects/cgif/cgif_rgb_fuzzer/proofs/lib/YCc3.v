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
Hypothesis TRGBCLOSE : trgb_close_spec B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_H_aux : rt_from B ss_X (INV_X B) -> rt_from B ss_H (INV_H B).
Proof.
intros RX. rt_prelude.
pose proof HINV as (HBV & Hk & r & N & E147 & HOBJ).
pose proof HOBJ as (g & s & wfn & ctx & path & attr & gen & loops & Wd & Hgt & bef & beffmt & cur0 & Hobj & Hat & Hwf & HW & HH & Hbef & HPerm3 & Hown).
cbn [c_ly c_S] in HPerm3, Hown.
pose proof Hwf as (Hlen3 & HW1 & HH1 & HNWH & HNle & _).
assert (Hcg3 : forall x, In x (trgb_own r g s N bef beffmt) -> In x (ablocks B ly3 S3))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; apply in_app_iff; left; exact Hx).
assert (Hcgne : forall x, In x (trgb_own r g s N bef beffmt) -> ~ In x (ablocks B ly S)).
{ intros x Hx Hxe. apply (tmp_not_entry B LAWS _ _ _ _ _ _ _ x HAR3 HPerm3 Hx). exact Hxe. }
pose proof Hobj as Hobj'. cbn [obj_at LAY_Rgb] in Hobj'. unfold field_ok in Hobj'. cbn [fst snd N.to_nat Z.of_N Pos.to_nat] in Hobj'.
destruct Hobj' as ((Vg & _) & _ & _ & _ & _ & _ & _ & _ & _ & (Vbef & Rbef) & _).
rewrite Z.add_0_r in Vg. change (2 ^ (8 * 8)) with (2 ^ 64) in Rbef.
relowRT HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RTBspan A_cgif_rgb_close.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 HF8hi; lia).
cgif_kept_run HFr Hcg3 HJ3 Hfin3 EFA3 AG KA.
clear_frames.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0.
rreg HS (@BV 5 10 I) Ra0.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
assert (U70 : bv_unsigned (ew E 70) = sp1) by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact U70);
assert (EraX : raZ rg = 0x81394) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
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
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _).
assert (HEVc : vev S3 + EV_RGBCLOSE <= VEV_MAX) by (apply (rbv_room S S3 62 16 EV_RGBCLOSE Hbud HBV); [vm_compute; discriminate | vm_compute; discriminate | clear; lia]).
assert (HOWNB : bsum (trgb_own r g s N bef beffmt) <= RGB_SIZE + CGB + 4 * 100000000).
{ unfold trgb_own. cbn [bsum fold_right snd]. rewrite bsum_app. pose proof (cgif_blocks_bsum _ g s N Hat Hwf) as Hcb.
assert (bsum (optb bef (beffmt * N)) <= 4 * 100000000).
{ unfold optb. destruct (bef =? 0) eqn:Eb; [cbn; clear; lia|]. cbn [bsum fold_right snd].
assert (HN8 : 1 <= N <= 100000000) by (clear - HW1 HH1 HNWH HNle; nia).
destruct Hbef as [-> | [-> | ->]]; [discriminate Eb | |]; clear - HN8; lia. }
clear - Hcb H. lia. }
assert (HLIVEc : blocks_bytes S3 + LIVE_FLUSH <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPerm3), !bsum_app, <- (blocks_bytes_bsum B ly S).
unfold LIVE_LIB in Hlive. unfold LIVE_FLUSH, CGB, RGB_SIZE in *. clear - Hlive HOWNB. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
eapply SRr_bind;
[ eapply (aj_call trasegs B LAWS tra_segs_low W3 Ex ssX msX LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)] ly3 S3 mdX k
TRGBCLOSE_STK (ablocks_fp (trgb_own r g s N bef beffmt)) EV_RGBCLOSE (sp1 - spZ regs) (ew Ex 2) (Z_to_bv 64 0x81394) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0))
(fun ly2 S2 W2 regs2 mem2 md2 => Permutation (ablocks B ly2 S2) (ablocks B ly S)) HS eq_refl HJ3);
[ first [ rewrite Rsp; rewrite ?sv_denot_SOff0; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Usp3; f_equal; clear; lia | match goal with |- ?gg => idtac "AJ1" gg end ]
| first [ reflexivity | idtac "AJ2" ]
| first [ exact Usp3 | idtac "AJ3" ]
| first [ rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity | match goal with |- ?gg => idtac "AJ4" gg end ]
| first [ clear - Hsp1; lia | idtac "AJ5" ]
| first [ apply Zle_bool_imp_le; vm_compute; reflexivity | idtac "AJ6" ]
| first [ assert (TRGBCLOSE_STK + 144 <= LLVMF_STK) by (vm_compute; discriminate); clear - Hsp1 H; lia | match goal with |- ?gg => idtac "AJ7" gg end ]
| first [ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Ugp; exact Hgp | idtac "AJ8" ]
| first [ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Utp; exact Htp | idtac "AJ9" ]
| first [ exact Rra | idtac "AJ10" ]
| first [ apply ret_ok_even; vm_compute; reflexivity | idtac "AJ11" ]
| first [ rewrite unsigned_lit_small by (clear; lia); clear; lia | idtac "AJ12" ]
| first [ rewrite Es0X; replace (spZ regs + (sp1 - spZ regs)) with sp1 by (clear; lia); exact Hch1 | match goal with |- ?gg => idtac "AJ13" gg end ]
| first [ intros HPRE1; eapply SRr_mono;
[ first [ pose proof (TRGBCLOSE ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0))
r g s N bef (beffmt * N) (ablocks B ly S) HPRE1) as CALL | idtac "CALL-POSE" ];
unfold cfg_at, apost_base in CALL; cbn [ss_pc]; change (w64 A_cgif_rgb_close) with (Z_to_bv 64 543860) in CALL;
first [ apply CALL | match goal with |- ?gg => idtac "CALL-APPLY" gg end; let t := type of CALL in idtac "CALL-TYPE" t ]; clear CALL;
[ first [ rewrite EraX; apply rt_ctx_in; [exact Hra | vm_compute; tauto | vm_compute; tauto] | match goal with |- ?gg => idtac "CA2" gg end ]
| first [ rewrite Hfrs3; cbn [length]; clear; lia | idtac "CA3" ]
| first [ eapply arodata_ok_journal; [exact HJ3 | exact HROD] | idtac "CA4" ]
| first [ rewrite Ra0; rewrite ?sv_denot_SOff0; ewpeel; exact E147 | match goal with |- ?gg => idtac "CA5" gg end ]
| first [ apply (rg_val_mem_blk_kept _ _ _ _ r RGB_SIZE r 8 g Vg (KA r RGB_SIZE ltac:(left; reflexivity))); [clear; lia | unfold RGB_SIZE; cbn; clear; lia] | match goal with |- ?gg => idtac "CA6" gg end ]
| first [ apply (rg_val_mem_blk_kept _ _ _ _ r RGB_SIZE (r + 48) 8 bef Vbef (KA r RGB_SIZE ltac:(left; reflexivity))); [clear; lia | unfold RGB_SIZE; cbn; clear; lia] | match goal with |- ?gg => idtac "CA7" gg end ]
| first [ exact Rbef | match goal with |- ?gg => idtac "CA8" gg end ]
| first [ apply (tcgif_at_blocks_kept _ _ _ _ g s N Hat); intros b sz Hb; apply KA; right; apply in_app_iff; left; exact Hb | match goal with |- ?gg => idtac "CA9" gg end ]
| first [ exact Hwf | match goal with |- ?gg => idtac "CA10" gg end ]
| first [ unfold trgb_own in HPerm3; cbn [app] in HPerm3; rewrite <- app_assoc in HPerm3; exact HPerm3 | match goal with |- ?gg => idtac "CA12" gg end ]
| first [ exact HEVc | match goal with |- ?gg => idtac "CA21" gg end ]
| first [ exact HLIVEc | match goal with |- ?gg => idtac "CA22" gg end ] ]
| first [ cbv beta; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HPc & Hpost);
exists ly4, S4, regs4, mem4, md4; split; [rewrite Rra; reflexivity|]; split; [exact HJc|];
split; [exact HPc|]; exact Hpost | match goal with |- ?g => idtac "CALL-POST" g end ] ]
| idtac "AJ14" ]
| first [ intros a Ha; right; destruct (inFP_ablocks_fp_inv _ a Ha) as (pb & nb & Hpb & Hab); exists pb, nb;
split; [exact (Hcg3 _ Hpb) | split; [exact (Hcgne _ Hpb) | exact Hab]]
| match goal with |- ?g => idtac "AJ15" g end ] ]
| ] end end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & HPerm4).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HJc by (clear; lia).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Hch1 EspX EraX Es0X.
pose proof (proj1 HJ4) as HAR4.
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs4 & _). cbn [app] in Hfrs4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(2, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
assert (HnFPF : forall a, F <= a < F + 256 -> ~ inFP (ablocks_fp (trgb_own r g s N bef beffmt)) a).
{ intros a Ha Hin. destruct (inFP_ablocks_fp_inv _ a Hin) as (pb & nb & Hpb & Hab).
pose proof (sep_block_frame trasegs _ LAWS ly3 S3 _ _ _ pb nb 2 fpos HAR3 (Hcg3 _ Hpb) Hfin3) as Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. change (fs_frame_bytes 2) with 256 in Hdj. rewrite EFA3 in Hdj. fold F in Hdj. clear - Ha Hab Hdj. lia. }
assert (HnFPlo : forall a, SB <= a < 17594333495296 -> ~ inFP (ablocks_fp (trgb_own r g s N bef beffmt)) a).
{ intros a Ha Hin. destruct (inFP_ablocks_fp_inv _ a Hin) as (pb & nb & Hpb & Hab).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HAR3 (Hcg3 _ Hpb)) as (_ & _ & _ & Hbh_ia & _). pose proof (proj1 Hbh_ia) as Hbh. clear - Ha Hab Hbh_ia C3. unfold SB in *. zone_lia. }
reseat HS HJ4 HP4 [0; 1; 2; 3]%nat AG
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
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub trasegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJc | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ4 SHOK RTBspan 0x81394.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA4.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
ra_join_win HS ss_X 600%nat rt_X_deads_bv ltac:(idtac).
rt_hand RX HS.
split; [eapply rbv_mono; [eapply rbv_coarse_bud; [exact HBV | eapply ajournal_bud; exact HJc | vm_compute; discriminate] | vm_compute; discriminate | clear; lia]|].
split; [pose proof KH_RLIB as Q2; clear - Hk Q2; lia|].
cbn [c_ly c_S]. exact HPerm4.
Qed.
Lemma rt_H : rt_from B ss_X (INV_X B) -> rt_from B ss_H (INV_H B).
Proof. exact rt_H_aux. Qed.
End d.
End c.
