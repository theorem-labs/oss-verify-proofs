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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCfu YCe9 YCgu YCgv.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac ng_prelude :=
let LAWS := rnLAWS in let B := lazymatch goal with L : AR_laws trbsegs ?Bv |- _ => Bv end in
intros ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops rest cid pos E0 E W3 ly3 S3 ms3 md3 k fpos HCTX HCFG HE0 HE HNOW HS;
pose proof Hwx_tfa as Hwx; pose proof trb_segs_low as Hsegs;
destruct HCTX as (HPRE & Hal32 & Hctx & Hroom & Htop32 & HROD & Hcfg & HWH & Hpala & HPerm & Hev & Hlive);
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : TNEWGIF_STK = 16768) by reflexivity;
assert (HEV : EV_NEWGIF = 12) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity; assert (Has : ASTACK = 16384) by reflexivity;
destruct HCFG as (Hfin & Hcid0 & Hfal & Hflo & Hfhi & Hcal & HRA);
destruct HE0 as (EE & E10 & E32 & Usp); destruct HE as (AG & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & RF & E57 & E58);
destruct (frames_bounds trbsegs _ LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
cbn [CTX_cgif_newgif In] in Hctx;
let Hq := fresh "Hq" in let Hr := fresh "Hr" in let Hs := fresh "Hs" in
assert (Hra88 : 0x81c9c = raZ regs) by (destruct Hctx as [Hq | [Hq | []]]; injection Hq as Hr Hs; exact Hr);
assert (Hspine : spine ch = [0x81498] \/ spine ch = [0x81498; 0x8116c])
by (destruct Hctx as [Hq | [Hq | []]]; injection Hq as Hr Hs; rewrite <- Hs; [left | right]; reflexivity);
let Hc' := fresh "Hc'" in
pose proof Hcfg as Hc'; cbn [obj_at LAY_Config] in Hc';
destruct Hc' as ([CV0 CR0] & [CV8 CR8] & [CV16 CR16] & [CV20 CR20] & [CV24 CR24] & [CV26 CR26] & [CV28 CR28] & [CV30 CR30] & [CV32 CR32] & [CV40 CR40] & HcT);
cbn [fst snd N.to_nat Z.of_N] in CV0, CV8, CV16, CV20, CV24, CV26, CV28, CV30, CV32, CV40, CR0, CR16, CR20, CR24, CR26, CR28, CR30;
change (2 ^ (8 * 8)) with (2 ^ 64) in CR0; change (2 ^ (8 * 4)) with (2 ^ 32) in CR16, CR20; change (2 ^ (8 * 2)) with 65536 in CR24, CR26, CR28, CR30.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Hypothesis ASF : astack_free_law trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Lemma ng_B : NG_M_stmt B -> NG_B_stmt B.
Proof.
intros NGM. ng_prelude.
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3).
pose proof (proj1 HJ3) as HAR3.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _).
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia).
assert (Hfin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (HfinS3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFapp_img.
destruct (frames_bounds trbsegs _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in HFSpres3. rewrite !EFA3 in *.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    .
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl).
pose proof (sep_frames_pos trbsegs _ LAWS ly3 S3 _ _ _ (1, fpos) (cid, pos) [] fl1 fl2 HAR3 ltac:(rewrite Hfrs3, Efl; reflexivity)) as HdFC.
unfold zdisjoint, frame_rng in HdFC. cbn [fst snd] in HdFC. change (fs_frame_bytes 1) with 128 in HdFC. rewrite !EFA3 in HdFC. fold F in HdFC.
nbox_seps.
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
reshok_bx HS 35%nat.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK NBspan.
all: try (oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (awrR AG fpos F EFA3).
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK NBspan.
-
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK NBspan 0x860c0; [awrR AG fpos F EFA3|]. clear_frames.
exitN HS HJ3 AG fpos F cfgp E57 E58 Hfin3 HfinS3 EE Hra HEV EFA3 EFL3.
exists 0. split; [reflexivity|]. left. split; [reflexivity|].
unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly3 S3). rewrite Eab3. apply Permutation_refl.
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into HW0.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK NBspan; [slim; oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | slim; awrR AG fpos F EFA3 |]. clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK NBspan.
+
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK NBspan 0x860c0; [awrR AG fpos F EFA3|]. clear_frames.
exitN HS HJ3 AG fpos F cfgp E57 E58 Hfin3 HfinS3 EE Hra HEV EFA3 EFL3.
exists 0. split; [reflexivity|]. left. split; [reflexivity|].
unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly3 S3). rewrite Eab3. apply Permutation_refl.
+
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into HH0.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK NBspan; [slim; oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | slim; awrR AG fpos F EFA3 |].
clear_frames.
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 KgotB KcellB KguarB KuarB VgrB.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp.
rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
assert (Qceil : alloc_ceiling <= spZ regs) by lia. assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
assert (Qtop : spZ regs < ly_top ly - 16) by lia. assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia. assert (Qsp : spZ regs - 192 + 16 <= spZ regs) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W3) (ms_mem msX) a = aview trbsegs (w_H W) mem a)
by (intros a Ha; pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; [clear - Ha Qceil; lia | clear - Ha; lia]) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview trbsegs (w_H W3) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 HUP
(rdword_of_val_mem trbsegs _ _ _ _ Vra Qra) (rdword_of_val_mem trbsegs _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp)
| ] end.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340936) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_at trbsegs B LAWS Hsegs errno_low ML AMALLOC _ (ms_regs msX) (ms_mem msX) TNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly3 S3 _ k 96 (-192) (Z_to_bv 64 0x85e58) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ra0.
- rewrite HMM. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S). unfold LIVE_NEWGIF, LIVE_MAX in *. lia.
- unfold spZ. rewrite Rsp. evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _). rewrite HEV in Hev. unfold VEV_MAX in *. lia.
- pose proof (proj1 (proj2 HJ3)) as HLY3. pose proof HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
apply (achain_chain_pre ly3 _ (spZ regs - 192) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; evalE AG
| unfold s0Z; rewrite Rs0; evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode, (tl_universe B TL). apply TRACES_cgif_newgif_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & g & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres4).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUP Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
unfold ASTACK in Hres4. replace (spZ regs + -192 - 16384) with (spZ regs - 16576) in Hres4 by lia. replace (spZ regs + -192) with (spZ regs - 192) in Hres4 by lia.
pose proof (proj1 HJ4) as HAR4. aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (EFL4 : forall c p, flag_addr ly4 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA4 c p) as X; unfold frame_addr in X; lia).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (HfinS4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; exact HfinS3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4.
change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
destruct Hres4 as [(Hres0 & Eab4 & HK4) | (Hg4096 & Eab4 & HK4)].
*
assert (HErF : forall a, F <= a < F + 128 -> ~ False) by (intros a Ha Hn; exact Hn).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first [ keptR HK4 HJ4 AG Usp E10 E32 HfinS3 I KgotB Kgot4 KcellB Kcell4 KguarB Kguar4 KuarB Kuar4 VgrB Vgr4 EFA3
| keptF HK4 AG RF E58 Hfin3 HFpres4 HFSpres4 HErF F EFA3 ]).
pose proof (st_ok_pin_reg' trbsegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha04, Hres0; reflexivity) eq_refl) as HS3.
clear HS. rename HS3 into HS. norm_ss HS. reshok_bx HS 35%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK NBspan 0x860c0; [awrR AG fpos F EFA4|]. clear_frames.
exitN HS HJ4 AG fpos F cfgp E57 E58 Hfin4 HfinS4 EE Hra HEV EFA4 EFL4.
exists 0. split; [reflexivity|]. left. split; [reflexivity|].
unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly4 S4). rewrite Eab4, Eab3. apply Permutation_refl.
*
assert (Hg_in : In (g, 96) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 HAR4 Hg_in) as (Hg16 & _ & Hgceil & Hgh_ia & Hgpres & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g 96 HAR4 Hg_in) as Hgh_img.
change (req_size 96) with 96 in Hgceil, Hgpres, Hgh_img.
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g 96 HJ3 HAR4 ltac:(rewrite Eab4, Eab3; reflexivity) ltac:(lia)) as Tg.
assert (Ag : forall blc lyq ownq i, In (g, 96) blc -> 0 <= i < 96 -> awr_byte TNEWGIF_STK (spZ regs) [] (ablocks B ly S) blc lyq ownq (g + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g 96 blc i lyq ownq HJ3 HAR4 ltac:(rewrite Eab4, Eab3; reflexivity) ltac:(lia) Hbl ltac:(change (req_size 96) with 96; lia)). }
pose proof (sep_block_frame trbsegs B LAWS ly4 S4 _ _ _ g 96 1 fpos HAR4 Hg_in Hfin4) as HdGF.
unfold zdisjoint in HdGF. cbn [fst snd] in HdGF. change (req_size 96) with 96 in HdGF. change (fs_frame_bytes 1) with 128 in HdGF. rewrite EFA4 in HdGF. fold F in HdGF.
pose proof (sep_block_frame trbsegs B LAWS ly4 S4 _ _ _ g 96 cid pos HAR4 Hg_in HfinS4) as HdGC.
unfold zdisjoint in HdGC. cbn [fst snd] in HdGC. change (req_size 96) with 96 in HdGC. rewrite EFA4 in HdGC.
assert (HErF : forall a, F <= a < F + 128 -> ~ (g <= a < g + req_size 96)) by (change (req_size 96) with 96; intros a Ha; clear - Ha HdGF; lia).
nbox HdGF.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first [ keptR HK4 HJ4 AG Usp E10 E32 HfinS3 I KgotB Kgot4 KcellB Kcell4 KguarB Kguar4 KuarB Kuar4 VgrB Vgr4 EFA3
| keptF HK4 AG RF E58 Hfin3 HFpres4 HFSpres4 HErF F EFA3 ]).
nbox HdGC.
rreg HS (10%bv : bv 5) Rg. cbn [ms_regs] in Rg. rewrite Ha04 in Rg. symmetry in Rg. unfold w64 in Rg.
lazymatch type of Rg with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rg, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some nx) 0 96 0 96 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Rg, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hgpres (g + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Rg; change (fs_frame_bytes 1) with 128; change (fs_frame_bytes 1 / 8) with 16; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_newgif; nunbox HdGF; nunbox HdGC; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NM in HS;
eapply (NGM ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops rest cid pos E0 Ev W4 ly4 S4 msv _ (k + 1) fpos g);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [exact AG | repeat (split; [eassumption|]); eassumption]
| exact Rg
| split; [exact HJ4 | split; [clear - Hk3; lia | split; [rewrite Hfrs4; exact Hfrs3 | split; [rewrite Eab4, Eab3; reflexivity | split; [exact Hg4096 | split; [exact Tg | exact Ag]]]]]]
| exact HW0 | exact HH0
| exact HS ] end.
rewrite <- Hra88. destruct Hspine as [Hs | Hs]; rewrite Hs; cbn; tauto.
Qed.
End d. End b.
