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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACer ACfm ACf5 ACf9 ACf7.
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
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FP0 : FP = [].
Hypothesis AFREE4 : afree04_rule tfibsegs B MT.
Hypothesis AFREEN4 : afree_null04_rule tfibsegs B MT.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_Dx_aux : rt_from B MT FP POST ss_X (INV_X B MT) -> rt_from B MT FP POST ss_Dx (INV_Dx B MT FP).
Proof.
intros RX. rt_prelude.
pose proof HINV as (HWHY & Hk1 & Hacc & attr & gen & w16 & h16 & ngp & cur & r & pal & HGC & E191 & Rpal & Hpal).
pose proof HGC as (E185 & E186 & E187 & E188 & E189 & E192 & Rattr & Rgen & Rw & Rh & Rngp & Rcur & Rr & Hr14 & Vp & Vn & Vc & Hprov & Hwhy).
cbn [c_n c_sp1 c_p] in Rcur, Hr14, Vp, Vn, Vc, Hwhy. cbn [c_ly c_S c_regs] in Hpal.
assert (HFAIL : hdr_fail (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)).
{ unfold hdr_fail. cbn [c_n]. destruct (Z.eq_dec r 0) as [Hr0|Hr0].
- right. exists attr, gen, w16, h16, ngp. split; [exact (Hprov Hr0)|]. right.
rewrite E192, E187, E188 in HWHY. rewrite !unsigned_lit_small in HWHY by (clear - Rr Rw Rh; lia). exact (HWHY Hr0).
- destruct (Hwhy Hr0) as [Hs | (Ha & Hpv & Hs)]; [left; exact Hs|]. right. exists attr, gen, w16, h16, ngp. split; [exact Hpv|]. left. split; [exact Ha | exact Hs]. }
clear HWHY.
relowRT HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan.
{ awrRT AG fpos F EFA3. }
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 HF8hi; lia). clear_frames.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0. rreg HS (@BV 5 10 I) Ra0.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x80878) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
assert (Ra0v : getr (ms_regs ms) 10 = w64 pal) by (rewrite Ra0; rewrite ?sv_denot_SOff0; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E191).
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
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _).
assert (HEVc : st_nev S3 < EV_MAX) by (rewrite HEV in Hev; clear - Hnev3 Hev Hk1; lia).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 338220 with (pc_wrap_free (as_code B)) by (rewrite HBcode; reflexivity).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
apply (SRr_bind tfibsegs _ _
(fun W4 c4 => exists ly4 S4 regs4 mem4 md4,
c4 = mkCfg (mkst regs4 (Z_to_bv 64 0x80878) mem4 (seg_rom tfibsegs)) md4 /\
ajournal tfibsegs B LLVMF_STK (spZ regs) FP ly S W mem md [(2, fpos)] ly4 S4 W4 mem4 md4 (k + 1) /\
aregs_preserved (ms_regs msX) regs4 /\ Permutation (ablocks B ly4 S4) (ablocks B ly S) /\ frames S4 = frames S3 /\
mo_le MT S S4 (acc + mo_free MT) /\
exists Er : Z -> Prop, acall_kept tfibsegs B ly3 S3 W3 (ms_mem msX) W4 mem4 (sp1 - ASTACK) sp1 Er /\
(forall a, F <= a < F + 256 -> ~ Er a) /\ (forall a, SB <= a < 17594333495296 -> ~ Er a))) end.
{ destruct Hpal as [(Ha4 & Hp0 & Eab3 & _) | (Ha4 & Hp1 & (Hbh1 & Hbh2 & Hb16 & Eab3 & Hawr & Haft) & _)].
-
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (AFREEN4 W3 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly3 S3 mdX k (sp1 - spZ regs) (Z_to_bv 64 0x80878) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ3)
| ] end.
+ rewrite Ra0v, Hp0. reflexivity.
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
apply (rt_trace_in 0x52a6c 0x80878); [exact Hra | exact EraX | left; split; reflexivity].
+
apply (mok_station MT S S3 T acc (mo_free MT) MTL HMOK HMLE); [apply (mo_free_nonneg MT MTL)|].
unfold ACC0, RT_NEED1, ACC_pal in *. pose proof (mo_malloc_nonneg MT MTL 196605 ltac:(clear; lia)) as Hnn. clear - Hacc HNEED Hnn; lia.
+ cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPerm4 & Hfrs4 & HK & HMLEc).
exists ly4, S4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
split; [eapply Permutation_trans; [exact HPerm4 | rewrite Eab3; apply Permutation_refl]|]. split; [exact Hfrs4|].
split; [exact (mle_station MT S S3 S4 acc (mo_free MT) MTL HMLE HMLEc)|].
exists (fun _ => False). replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia). split; [exact HK|].
repeat split; intros a _ Hx; exact Hx.
-
assert (Hpt3 : In (pal, 3 * ngp) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pal (3 * ngp) HAR3 Hpt3) as (_ & _ & _ & Hph_ia & _ & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR3 Hpt3) as Hph_img.
pose proof (sep_block_frame tfibsegs _ LAWS ly3 S3 _ _ _ pal (3 * ngp) 2 fpos HAR3 Hpt3 Hfin3) as HdFP.
unfold zdisjoint in HdFP; cbn [fst snd] in HdFP; change (fs_frame_bytes 2) with 256 in HdFP; rewrite EFA3 in HdFP. fold F in HdFP.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (AFREE4 W3 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly3 S3 mdX k pal (3 * ngp) (sp1 - spZ regs) (Z_to_bv 64 0x80878) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ3 Hpt3)
| ] end.
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
apply (rt_trace_in 0x52a6c 0x80878); [exact Hra | exact EraX | left; split; reflexivity].
+ exact Haft.
+
apply (mok_station MT S S3 T acc (mo_free MT) MTL HMOK HMLE); [apply (mo_free_nonneg MT MTL)|].
unfold ACC0, RT_NEED1, ACC_pal in *. pose proof (mo_malloc_nonneg MT MTL 196605 ltac:(clear; lia)) as Hnn. clear - Hacc HNEED Hnn; lia.
+ cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Ebl3 & Ebl4) & Hfrs4 & HK & HMLEc).
exists ly4, S4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
split; [rewrite Ebl4; pose proof (@Permutation_app_inv _ l1 l2 (ablocks B ly S) [] (pal, 3 * ngp)) as HPI; rewrite app_nil_r in HPI; apply HPI; rewrite <- Ebl3, Eab3; apply Permutation_refl|].
split; [exact Hfrs4|].
split; [exact (mle_station MT S S3 S4 acc (mo_free MT) MTL HMLE HMLEc)|].
exists (fun a => pal <= a < pal + req_size (3 * ngp)). replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia). split; [exact HK|].
split; [intros a Ha Hx; clear - Ha Hx HdFP; lia | intros a Ha Hx; clear - Ha Hx Hph_ia C3; unfold SB in *; zone_lia]. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPerm4 & Hfrs4 & HMLE4 & Er & HK & HErF & HErLo).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1.
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(2, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
reseatL HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hx; exact (HErLo a ltac:(clear - Ha HF8c HF8lo HFceil C1; unfold SB in *; lia) Hx)
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hx; exact (HErF a ltac:(clear - Ha; lia) Hx)
| intros a Ha; first [exfalso; clear - Ha; lia | apply (proj1 (HFpres4 a ltac:(clear - Ha; lia)))] ] end
| keptRT HK HJ4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 ltac:(idtac; fail) ltac:(idtac; fail)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
ra_join_win HS ss_X 600%nat rt_X_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. rt_hand RX HS.
split; [rewrite HEV; clear - Hk1; lia|]. split; [macc|].
cbn [c_ly c_S]. split; [exact HPerm4 | exact HFAIL].
Qed.
Lemma rt_Dx : rt_from B MT FP POST ss_X (INV_X B MT) -> rt_from B MT FP POST ss_Dx (INV_Dx B MT FP).
Proof. exact rt_Dx_aux. Qed.
Lemma rt_D_aux : rt_from B MT FP POST ss_Dx (INV_Dx B MT FP) -> rt_from B MT FP POST ss_E (INV_E B MT FP) -> rt_from B MT FP POST ss_D (INV_D B MT FP).
Proof.
intros RDX RE. rt_prelude.
pose proof HINV as (Hk1 & Hacc & attr & gen & w16 & h16 & ngp & cur & r & pal & HGC & E191 & Rpal & Hpal).
pose proof HGC as (E185 & E186 & E187 & E188 & E189 & E192 & Rattr & Rgen & Rw & Rh & Rngp & Rcur & Rr & Hr14 & Vp & Vn & Vc & Hprov & Hwhy).
cbn [c_n c_sp1 c_p] in Rcur, Hr14, Vp, Vn, Vc, Hwhy. cbn [c_ly c_S c_regs] in Hpal.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (B70 : bv_unsigned (ew E 70) = sp1) by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia).
assert (B75 : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (HSPB : alloc_ceiling <= spZ regs - LLVMF_STK /\ spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ F <= a < F + 32 \/ F + 80 <= a < F + 256).
reshok HS.
srr_branch_tok tfibtbl_lib_ok HS SHOK RTBspan.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
hc_bool Hc ltac:(fun H => hc_atom H 192%nat r E192 ltac:(exact Rr)). hc_prop Hc.
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan 0x80870.
{ awrRT AG fpos F EFA3. }
palv_run HFr Hpal AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096).
unrunRD HFr Zsm Usp B70 Hsp1 UN1. clear_frames.
vkeepUN UN1 Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UN1.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
ra_join_win HS ss_Dx 420%nat rt_Dx_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. rt_hand RDX HS.
split. { lazymatch goal with |- bv_unsigned (ew ?Ev 192) = 0 -> _ =>
assert (HE192 : ew Ev 192 = Z_to_bv 64 r) by (ewpeel; exact E192); rewrite HE192, unsigned_lit_small by (clear - Rr; lia) end.
intros H0. exfalso. clear - H0 Hc. lia. }
split; [exact Hk1|]. split; [macc|].
exists attr, gen, w16, h16, ngp, cur, r, pal. cbn [c_n c_ly c_S c_regs].
split; [unfold rt_gc; cbn [c_n c_sp1 c_p]; repeat match goal with |- _ /\ _ => split end; first [assumption | clear - Rattr Rgen Rw Rh Rngp Rcur Rr; lia]|].
split; [exact E191|]. split; [exact Rpal|]. exact (rt_palD_kept B FP _ _ _ _ _ _ _ _ _ _ _ Hpalv Hpal).
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
hc_bool Hc ltac:(fun H => hc_atom H 192%nat r E192 ltac:(exact Rr)). hc_prop Hc.
pose proof (Hr14 Hc) as Hn14.
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan 0x80718.
{ awrRT AG fpos F EFA3. }
palv_run HFr Hpal AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096). rename Hpalv into Hpalv0.
unrunRD HFr Zsm Usp B70 Hsp1 UN1. clear_frames.
pose proof (rt_palD_kept B FP _ _ _ _ _ _ _ _ _ _ _ Hpalv0 Hpal) as Hpal1. clear Hpal. rename Hpal1 into Hpal.
vkeepUN UN1 Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UN1.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E187n : ew Ev 187 = Z_to_bv 64 w16) by (ewpeel; exact E187);
assert (E188n : ew Ev 188 = Z_to_bv 64 h16) by (ewpeel; exact E188) end.
reshok HS.
srr_branch_tok tfibtbl_lib_ok HS SHOK RTBspan.
+
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc2 end.
hc_bool Hc2 ltac:(fun H => lazymatch type of H with context [U ?E' (SMd M_MUL (SOff ?a 0) (SOff ?b 0))] =>
first [ rewrite (U_mul16 E' 188 187 h16 w16 E188n E187n ltac:(clear - Rh; lia) ltac:(clear - Rw; lia)) in H
| rewrite (U_mul16 E' 187 188 w16 h16 E187n E188n ltac:(clear - Rw; lia) ltac:(clear - Rh; lia)) in H ] end).
hc_prop Hc2.
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan 0x809e4.
{ awrRT AG fpos F EFA3. }
palv_run HFr Hpal AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096).
unrunRD HFr Zsm Usp B70 Hsp1 UN2. clear_frames.
vkeepUN UN2 Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UN2.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
first [ rreg_by HS (@BV 5 19 I) (Z_to_bv 64 (w16 * h16))
(eq_trans (denot_mul16 Ev 188 187 h16 w16 ltac:(ewpeel; exact E188) ltac:(ewpeel; exact E187) ltac:(clear - Rh; lia) ltac:(clear - Rw; lia)) (f_equal (Z_to_bv 64) (Z.mul_comm h16 w16))) Q20
| rreg_by HS (@BV 5 19 I) (Z_to_bv 64 (w16 * h16))
(denot_mul16 Ev 187 188 w16 h16 ltac:(ewpeel; exact E187) ltac:(ewpeel; exact E188) ltac:(clear - Rw; lia) ltac:(clear - Rh; lia)) Q20
| rreg HS (19%bv : bv 5) Q20; match type of Q20 with ?t => idtac "E194-SHAPE" t end; fail ] end.
add_atom_win HS 194%nat (Z_to_bv 64 (w16 * h16)) E194.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_add_fact tfibsegs Ev ssx msx 194%nat (mkAF 0 100000000 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E194, unsigned_lit_small by (clear - Rw Rh Hc2; nia); rewrite Z.pow_0_r, Z.mod_1_r;
split; [clear - Rw Rh Hc2; nia | split; [clear - Rw Rh Hc2; nia | clear; lia]])) as HS3;
clear HS; rename HS3 into HS end.
ws_pin HS (@BV 5 19 I) (SOff 194 0) Q20 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E194).
rreg HS (24%bv : bv 5) Q24. add_atom_win HS 412%nat (Z_to_bv 64 r) E412.
ws_pin HS (24%bv : bv 5) (SOff 412 0) Q24 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E412; symmetry; ewpeel;
first [exact E192 | match goal with |- ?g => idtac "PIN24" g end; fail]).
ra_join_win HS ss_E 420%nat rt_E_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. rt_hand RE HS.
split; [exact Hk1|]. split; [macc|].
exists attr, gen, w16, h16, ngp, cur, pal. cbn [c_n c_ly c_S c_regs].
rewrite Hc in E192.
split; [unfold rt_gc; cbn [c_n c_sp1 c_p]; repeat match goal with |- _ /\ _ => split end; first [assumption | intros _; exact Hn14 | intros _; exact (Hprov Hc) | intros H0; exfalso; apply H0; reflexivity | clear - Rattr Rgen Rw Rh Rngp Rcur Rr; lia]|].
split; [exact E194|]. split; [clear - Hc2 Rw Rh; nia|].
split; [exact E191|]. split; [exact Rpal|]. exact (rt_palD_r0 B FP _ _ _ _ _ _ _ _ _ Hc (rt_palD_kept B FP _ _ _ _ _ _ _ _ _ _ _ Hpalv Hpal)).
+
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc2 end.
hc_bool Hc2 ltac:(fun H => lazymatch type of H with context [U ?E' (SMd M_MUL (SOff ?a 0) (SOff ?b 0))] =>
first [ rewrite (U_mul16 E' 188 187 h16 w16 E188n E187n ltac:(clear - Rh; lia) ltac:(clear - Rw; lia)) in H
| rewrite (U_mul16 E' 187 188 w16 h16 E187n E188n ltac:(clear - Rw; lia) ltac:(clear - Rh; lia)) in H ] end).
hc_prop Hc2.
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan 0x80870.
{ awrRT AG fpos F EFA3. }
palv_run HFr Hpal AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096).
unrunRD HFr Zsm Usp B70 Hsp1 UN2. clear_frames.
vkeepUN UN2 Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UN2.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
ra_join_win HS ss_Dx 420%nat rt_Dx_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. rt_hand RDX HS.
split. { lazymatch goal with |- bv_unsigned (ew ?Ev 192) = 0 -> 100000000 < bv_unsigned (ew _ 187) * bv_unsigned (ew _ 188) =>
assert (HE187 : ew Ev 187 = Z_to_bv 64 w16) by (ewpeel; exact E187); assert (HE188 : ew Ev 188 = Z_to_bv 64 h16) by (ewpeel; exact E188);
rewrite HE187, HE188, !unsigned_lit_small by (clear - Rw Rh; lia) end.
intros _. clear - Hc2 Rw Rh. nia. }
split; [exact Hk1|]. split; [macc|].
exists attr, gen, w16, h16, ngp, cur, r, pal. cbn [c_n c_ly c_S c_regs].
split; [unfold rt_gc; cbn [c_n c_sp1 c_p]; repeat match goal with |- _ /\ _ => split end; first [assumption | clear - Rattr Rgen Rw Rh Rngp Rcur Rr; lia]|].
split; [exact E191|]. split; [exact Rpal|]. exact (rt_palD_kept B FP _ _ _ _ _ _ _ _ _ _ _ Hpalv Hpal).
Qed.
Lemma rt_D : rt_from B MT FP POST ss_Dx (INV_Dx B MT FP) -> rt_from B MT FP POST ss_E (INV_E B MT FP) -> rt_from B MT FP POST ss_D (INV_D B MT FP).
Proof. exact rt_D_aux. Qed.
End d.
End c.
