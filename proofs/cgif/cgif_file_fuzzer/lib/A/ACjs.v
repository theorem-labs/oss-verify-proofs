(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8a ACjr ACk4 ACk5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YC5d YC7z YC7x YC21 YC85 YC86 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI17 YE02 YC5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACk0 ACk2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {NP : ng_params}.
#[local] Notation hw := (@ngp_hw NP).
#[local] Notation CTX := (@ngp_ctx NP).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Ltac ng_preludeX :=
let LAWS := rnLAWS in let B := lazymatch goal with L : AR_laws SEGS ?Bv |- _ => Bv end in
intros ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 E W3 ly3 S3 ms3 md3 k fpos TA TB HCTX HXE HCONT HCFG HE0 HEX HNOW HS;
destruct HEX as [HE E42];
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
destruct HCTX as (HPRE & Hal32 & Hctx & Hroom & Htop32 & HROD & Hcfg & HWH & Hpala & HPerm & Hev & Hlive);
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : TNEWGIFX_STK = 18816) by reflexivity;
assert (HEV : EV_NEWGIF = 12) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity; assert (Has : ASTACK = 16384) by reflexivity;
destruct HCFG as (Hfin & Hcid0 & Hfal & Hflo & Hfhi & Hcal & HRA);
destruct HE0 as (EE & E10 & E32 & Usp); destruct HE as (AG & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & RF & E528 & E529 & E41 & ?HEI);
destruct (frames_bounds SEGS _ LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ => img_facts Ev end; img_hull_facts;
let Hc' := fresh "Hc'" in
pose proof Hcfg as Hc'; cbn [obj_at LAY_Config] in Hc';
destruct Hc' as ([CV0 CR0] & [CV8 CR8] & [CV16 CR16] & [CV20 CR20] & [CV24 CR24] & [CV26 CR26] & [CV28 CR28] & [CV30 CR30] & [CV32 CR32] & [CV40 CR40] & HcT);
cbn [fst snd N.to_nat Z.of_N] in CV0, CV8, CV16, CV20, CV24, CV26, CV28, CV30, CV32, CV40, CR0, CR16, CR20, CR24, CR26, CR28, CR30;
change (2 ^ (8 * 8)) with (2 ^ 64) in CR0; change (2 ^ (8 * 4)) with (2 ^ 32) in CR16, CR20; change (2 ^ (8 * 2)) with 65536 in CR24, CR26, CR28, CR30.
Section f.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis TLF : PALibF B.
Hypothesis Rhw : 0 <= hw < 2 ^ 64.
Hypothesis HGOT3 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 3)) 8 (BASE + 0).
Hypothesis HU : forall c t, In c CTX -> In t (ng_traces B c) -> In t (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Local Notation code := (as_code B).
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis AFM : afile_meter SEGS B MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Variable XN : xnums.
Hypothesis HXN : forall ngp, 0 <= ngp <= 65535 -> ng_msum MT ngp <= xn_newgif XN ngp.
Hypothesis HXM : forall ngp, 0 <= ngp <= 65535 -> ng_msum MT ngp <= xm_newgif XN ngp.
Variable ra_fo : Z.
Hypothesis AFOPENX : afopen_x SEGS B K (SIGMA AS_fopen) ra_fo pa_relro_lo pa_relro_hi.
Hypothesis HUfo : In [pc_malloc_ra0 code; ra_fo] (as_universe B).
Hypothesis HMODE : VAL (A_OBJ 4) = ak_mode K.
Hypothesis Hhw0 : hw = 0.
Lemma ng_BX : NG_M_stmtX B K MT XN -> NG_B_stmtX B K MT XN.
Proof.
intros NGM. ng_preludeX.
destruct HXE as (HGP & HSNK0 & HFD0 & HAM0 & HMOK). destruct HCONT as (KA & KB0 & KB1).
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3).
pose proof (proj1 HJ3) as HAR3.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _).
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia).
assert (Hfin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (HfinS3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFapp_img.
destruct (frames_bounds SEGS _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in HFSpres3. rewrite !EFA3 in *.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    .
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl).
pose proof (sep_frames_pos SEGS _ LAWS ly3 S3 _ _ _ (1, fpos) (cid, pos) [] fl1 fl2 HAR3 ltac:(rewrite Hfrs3, Efl; reflexivity)) as HdFC.
unfold zdisjoint, frame_rng in HdFC. cbn [fst snd] in HdFC. change (fs_frame_bytes 1) with 128 in HdFC. rewrite !EFA3 in HdFC. fold F in HdFC.
nbox_seps.
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
reshok_bx HS 35%nat.
assert (Rngp : 0 <= ngp <= 65535) by (clear - CR28; lia).
assert (Rpath : 0x10000 <= ak_path K < 0x5fb000).
{ apply (pa_img_range (ak_path K)). apply (proj1 (ail_env _ _ _ AIL (ak_path K) ltac:(unfold aenv_addr; right; right; right; left; lia))). }
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK NBspan.
all: try (oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (awrR AG fpos F EFA3).
clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK NBspan.
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into HW0.
assert (HT : ng_treeX md attr gen Wd Hd ngp GPAL TA TB = TA) by (unfold ng_treeX, g_opens, newgif_cfg; cbn [YO07.g_w YO07.g_h]; rewrite HW0; reflexivity).
rewrite HT. clear HT.
eapply SRr_mono; [| intros W' c' Hle HP HAI'; exact (KA W' c' (wle_trans _ _ _ _ (proj1 (proj2 (proj2 (proj2 HJ3)))) Hle) HAI' HP)].
paj_run_to_tok RUNTO HS HJ3 SHOK NBspan 0x418; [awrR AG fpos F EFA3|]. clear_frames.
exitN RET RUNF HS HJ3 AG fpos F cfgp E528 E529 Hfin3 HfinS3 EE Hra HEV EFA3 EFL3.
lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?mdx) ?matx ?mdx] =>
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mdx _ =>
pose proof (ajournal_materialize _ _ LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ matx HJ3) as HJF end end.
assert (Hk0 : k = 0) by (pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & Hk0' & _); clear - Hk0' Hk3; lia).
destruct (ajournal_nil_ioX SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF) as [EfdsF EfsF].
split; [reflexivity|].
split; [exact (proj2 (proj2 (ameta_inv_kept SEGS B K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF HAM0)))|].
split.
{ subst k. apply (mo_le_mono MT MLAW _ _ 0); [eapply afm_k0; [exact AFM | exact HJF]|].
pose proof (HXN ngp Rngp) as Hx. unfold ng_msum, ng_macc3, ng_macc2, ng_macc1 in Hx.
pose proof (mo_malloc_nonneg MT MLAW FILE_BLOCK ltac:(unfold FILE_BLOCK; lia)) as M1.
pose proof (mo_malloc_nonneg MT MLAW 96 ltac:(lia)) as M2.
pose proof (mo_malloc_nonneg MT MLAW (3 * ngp) ltac:(clear - Rngp; lia)) as M3.
pose proof (mo_malloc_nonneg MT MLAW RAW_SIZE ltac:(unfold RAW_SIZE; lia)) as M4.
pose proof (mo_free_nonneg MT MLAW) as M5. clear - Hx M1 M2 M3 M4 M5. lia. }
split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3); rewrite Eab3; apply Permutation_refl|].
split; [exact (asink_none_kept SEGS B K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF sink_closed_nil HSNK0)|].
split; [exact EfsF | intros _; exact EfdsF].
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into HW0.
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK NBspan; [slim; oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | slim; awrR AG fpos F EFA3 |]. clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK NBspan.
+
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into HH0.
assert (HT : ng_treeX md attr gen Wd Hd ngp GPAL TA TB = TA) by (unfold ng_treeX, g_opens, newgif_cfg; cbn [YO07.g_w YO07.g_h]; rewrite HH0, Bool.orb_true_r; reflexivity).
rewrite HT. clear HT.
eapply SRr_mono; [| intros W' c' Hle HP HAI'; exact (KA W' c' (wle_trans _ _ _ _ (proj1 (proj2 (proj2 (proj2 HJ3)))) Hle) HAI' HP)].
paj_run_to_tok RUNTO HS HJ3 SHOK NBspan 0x418; [awrR AG fpos F EFA3|]. clear_frames.
exitN RET RUNF HS HJ3 AG fpos F cfgp E528 E529 Hfin3 HfinS3 EE Hra HEV EFA3 EFL3.
lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?mdx) ?matx ?mdx] =>
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mdx _ =>
pose proof (ajournal_materialize _ _ LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ matx HJ3) as HJF end end.
assert (Hk0 : k = 0) by (pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & Hk0' & _); clear - Hk0' Hk3; lia).
destruct (ajournal_nil_ioX SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF) as [EfdsF EfsF].
split; [reflexivity|].
split; [exact (proj2 (proj2 (ameta_inv_kept SEGS B K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF HAM0)))|].
split.
{ subst k. apply (mo_le_mono MT MLAW _ _ 0); [eapply afm_k0; [exact AFM | exact HJF]|].
pose proof (HXN ngp Rngp) as Hx. unfold ng_msum, ng_macc3, ng_macc2, ng_macc1 in Hx.
pose proof (mo_malloc_nonneg MT MLAW FILE_BLOCK ltac:(unfold FILE_BLOCK; lia)) as M1.
pose proof (mo_malloc_nonneg MT MLAW 96 ltac:(lia)) as M2.
pose proof (mo_malloc_nonneg MT MLAW (3 * ngp) ltac:(clear - Rngp; lia)) as M3.
pose proof (mo_malloc_nonneg MT MLAW RAW_SIZE ltac:(unfold RAW_SIZE; lia)) as M4.
pose proof (mo_free_nonneg MT MLAW) as M5. clear - Hx M1 M2 M3 M4 M5. lia. }
split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3); rewrite Eab3; apply Permutation_refl|].
split; [exact (asink_none_kept SEGS B K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF sink_closed_nil HSNK0)|].
split; [exact EfsF | intros _; exact EfdsF].
+
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into HH0.
assert (HOPENS : g_opens (newgif_cfg Wd Hd attr gen ngp GPAL) = true).
{ unfold g_opens, newgif_cfg. cbn [YO07.g_w YO07.g_h]. rewrite (proj2 (Z.eqb_neq _ _) HW0), (proj2 (Z.eqb_neq _ _) HH0). reflexivity. }
hei_havoc HS; paj_run_tok RUN HS HJ3 SHOK NBspan; [slim; oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | slim; awrR AG fpos F EFA3 |].
clear_frames.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 KgotB KcellB KguarB KuarB VgrB.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
assert (Qceil : alloc_ceiling <= spZ regs) by lia. assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
assert (Qtop : spZ regs < ly_top ly - 16) by lia. assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia. assert (Qsp : spZ regs - 192 + 16 <= spZ regs) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msX) a = aview SEGS (w_H W) mem a)
by (intros a Ha; pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; [clear - Ha Qceil; lia | clear - Ha; lia]) | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msX) a = aview SEGS (w_H W) mem a)
by (intros a Ha; pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; [clear - Ha Qceil; lia | clear - Ha; lia])  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp)
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp)
| ]  end.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (EspX : spZ (ms_regs msX) = spZ regs + -192) by (unfold spZ at 1; rewrite Rsp; evalE AG);
assert (EraX : raZ (ms_regs msX) = BASE + 396) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; lia);
assert (Es0X : s0Z (ms_regs msX) = spZ regs) by (unfold s0Z; rewrite Rs0; evalE AG) end.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HPRE1 : afn_pre SEGS B AFOPEN_STK ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX ((spZ regs, raZ regs, s0Z regs) :: ch));
[ eapply (afn_pre_at SEGS B TNEWGIFX_STK (spZ regs) [] ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX) AFOPEN_STK (-192));
[ exact HJ3
| exact EspX
| reflexivity
| lia
| unfold AFOPEN_STK; lia
| rewrite FFS; unfold AFOPEN_STK; lia
| rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity]
| rewrite EraX; lia
| rewrite Rgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| rewrite EspX, Es0X; replace (spZ regs + -192) with (spZ regs - 192) by lia;
pose proof (proj1 (proj2 HJ3)) as HLY3; pose proof HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _);
exact (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1) ]
| ] end.
pose proof (asink_none_kept SEGS B K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 sink_closed_nil HSNK0) as HSNKc.
pose proof (ameta_inv_kept SEGS B K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HAM0) as HAMc.
destruct (ajournal_nil_ioX SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efds Efs].
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HRODc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem msX))) by (eapply arodata_ok_journalP; [apply pa_relro_img | exact RO | exact HJ3 | exact HROD]) end.
pose proof (img_env_atomP E (A_OBJ 4) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as E245.
pose proof (ajournal_fp_nilX SEGS B _ _ [sink_token] _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HJ3r.
assert (XF : xfacts (alloc_ceiling + TNEWGIFX_STK <= spZ regs /\ TNEWGIFX_STK = 18816 /\ 140735332483072 <= alloc_ceiling <= 140737479966720 /\
(F + 128 <= 65536 \/ 6270976 <= F) /\ 4096 <= F /\ F + 128 <= alloc_ceiling /\ 512 <= F / 8)).
{ apply xfacts_i. pose proof HFhigh_img as Hoff. unfold off_img in Hoff. clear - Hceil Hslo FFS C1 Hoff HF4096 HFceil HF8lo. lia. }
apply SRr_ret. intros HAIc. cbn [cfg_model] in HAIc.
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl). cbn [ss_pc setpc].
unfold ng_treeX. rewrite HOPENS. rewrite <- Efs.
lazymatch goal with |- srealizes _ (mkCfg (mkst ?rg _ ?mm _) ?mdX) _ =>
pose proof (AFOPENX W3 ly3 S3 rg mm mdX ((spZ regs, raZ regs, s0Z regs) :: ch) aM TA TB HAIc HPRE1) as CALL end.
unfold cfg_at in CALL. apply CALL; clear CALL.
{ rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite E42. reflexivity. }
{ rewrite Ra1. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. change 245%nat with (A_OBJ 4). rewrite E245, HMODE. reflexivity. }
{ exact HSNKc. }
{ exact HAMc. }
{ exact HRODc. }
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _). rewrite HEV in Hev. unfold EV_MAX in *. clear - Hnev3 Hev Hk3. lia. }
{ rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S). unfold LIVE_NEWGIF, LIVE_MAX, FILE_BLOCK in *. clear - Hlive. lia. }
{ exact HUfo. }
{ assert (XFD : forall mdq, m_fds mdq = m_fds md -> fd_lookup (m_fds mdq) (alloc_fd (m_fds mdq)) = None) by (intros mdq ->; exact HFD0).
apply XFD. exact Efds. }
{
intros W4 c4 Hwle4 HAI4 HpostA. unfold afopen_postA in HpostA.
destruct HpostA as (ly4 & S4 & regs4 & mem4 & md4 & e & -> & HJc & HP4 & Ha04 & Hfrs4 & Eab4 & HSNK4 & Efds4 & Efs4 & He & Verr).
eapply (srz_enterX SEGS W4); [exact HAI4|]. clear HAI4.
rewrite EspX in HJc. rewrite Rra.
pose proof (ajournal_sub_tok SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3r HJc
ltac:(rewrite FFS; unfold AFOPEN_STK; clear; lia) ltac:(clear; lia) ltac:(intros a Ha; left; exact Ha)) as HJ4. cbn [app] in HJ4.
clear Ra0 Ra1 Rra Rsp Rgp Rtp Rs0 Hch1 HUP Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
pose proof (proj1 HJ4) as HAR4. aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (EFL4 : forall c p, flag_addr ly4 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA4 c p) as X; unfold frame_addr in X; lia).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (HfinS4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; exact HfinS3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4.
change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR4 HfinS4) as (_ & _ & HCpres4 & _). rewrite EFA4 in HCpres4.
reseat_lo 48%nat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first [ keptJ HJc HJ4 AG Usp E10 RF E529 Hfin3 HfinS3 FFS KgotB Kgot4 KcellB Kcell4 KguarB Kguar4 KuarB Kuar4 VgrB Vgr4 EFA3 HFpres4 HFSpres4 HCpres4 F ltac:(fptok)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha04; reflexivity) eq_refl) as HS3.
clear HS. rename HS3 into HS. norm_ss HS. reshok_bx HS 35%nat.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ4 SHOK NBspan 0x418; [awrR AG fpos F EFA4|].
xnone_stretch HFr HSNK4. clear_frames.
eapply SRr_mono; [| intros W' c' Hle HP HAI'; exact (KA W' c' (wle_trans _ _ _ _ (wle_trans _ _ _ _ (proj1 (proj2 (proj2 (proj2 HJ3)))) Hwle4) Hle) HAI' HP)].
exitNX RET RUNF HS HJ4 AG fpos F cfgp E528 E529 Hfin4 HfinS4 EE Hra HEV EFA4 EFL4
ltac:(idtac; let HFr := lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => H end in xnone_stretch HFr HSNK4).
lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?mdx) ?matx ?mdx] =>
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mdx _ =>
pose proof (ajournal_materialize _ _ LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ matx HJ4) as HJF end end.
assert (Hk0 : k = 0) by (pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & Hk0' & _); clear - Hk0' Hk3; lia).
split; [reflexivity|].
split; [exact (proj2 (proj2 (ameta_inv_kept SEGS B K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF HAM0)))|].
split.
{ subst k. change (0 + 0) with 0 in HJF. apply (mo_le_mono MT MLAW _ _ 0); [eapply afm_k0; [exact AFM | exact HJF]|].
pose proof (HXN ngp Rngp) as Hx. unfold ng_msum, ng_macc3, ng_macc2, ng_macc1 in Hx.
pose proof (mo_malloc_nonneg MT MLAW FILE_BLOCK ltac:(unfold FILE_BLOCK; lia)) as M1.
pose proof (mo_malloc_nonneg MT MLAW 96 ltac:(lia)) as M2.
pose proof (mo_malloc_nonneg MT MLAW (3 * ngp) ltac:(clear - Rngp; lia)) as M3.
pose proof (mo_malloc_nonneg MT MLAW RAW_SIZE ltac:(unfold RAW_SIZE; lia)) as M4.
pose proof (mo_free_nonneg MT MLAW) as M5. clear - Hx M1 M2 M3 M4 M5. lia. }
split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly4 S4); rewrite Eab4, Eab3; apply Permutation_refl|].
split; [lazymatch goal with |- asink_none _ _ _ (with_vm_backing _ _ ?mdx) => apply (asink_none_model SEGS K _ mdx); [reflexivity | exact HSNK4] end|].
split; [transitivity (m_fs md4); [reflexivity | rewrite Efs4; exact Efs] | intros _; transitivity (m_fds md4); [reflexivity | rewrite Efds4; exact Efds]].   }
{
intros W4 c4 Hwle4 HAI4 HpostB. unfold afopen_postB in HpostB.
destruct HpostB as (ly4 & S4 & regs4 & mem4 & md4 & pf & -> & HJc & HP4 & Ha04 & Hfrs4 & Hpf4096 & Eab4 & HSINK & Hlk4 & Efs4).
eapply (srz_enterX SEGS W4); [exact HAI4|]. clear HAI4.
rewrite EspX in HJc. rewrite Rra.
eapply SRr_mono with (Q := ng_postXB B K MT XN regs ly S W mem md attr gen Wd Hd ngp loops aM GPAL);
[| intros W' c' Hle HP HAI';
pose proof (wle_trans _ _ _ _ (wle_trans _ _ _ _ (proj1 (proj2 (proj2 (proj2 HJ3)))) Hwle4) Hle) as Hle';
destruct (ng_postXB_arms B K MT XN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hhw0 HP) as [[Hsg HP0] | [Hsg HP1]];
[exact (KB0 HOPENS Hsg W' c' Hle' HAI' HP0) | exact (KB1 HOPENS Hsg W' c' Hle' HAI' HP1)]].
pose proof (ajournal_sub_tok SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3r HJc
ltac:(rewrite FFS; unfold AFOPEN_STK; clear; lia) ltac:(clear; lia) ltac:(intros a Ha; left; exact Ha)) as HJ4. cbn [app] in HJ4.
clear Ra0 Ra1 Rra Rsp Rgp Rtp Rs0 Hch1 HUP Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
pose proof (proj1 HJ4) as HAR4. aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (EFL4 : forall c p, flag_addr ly4 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA4 c p) as X; unfold frame_addr in X; lia).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (HfinS4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; exact HfinS3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4.
change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR4 HfinS4) as (_ & _ & HCpres4 & _). rewrite EFA4 in HCpres4.
assert (Hpf_in : In (pf, FILE_BLOCK) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pf FILE_BLOCK HAR4 Hpf_in) as (Hpf16 & _ & Hpfceil & Hp_ia & _ & _).
pose proof (blk_off_imgP _ _ _ _ _ _ pf FILE_BLOCK HAR4 Hpf_in) as Hph_img. change (req_size FILE_BLOCK) with 1264 in Hpfceil, Hph_img, Hp_ia. unfold off_img in Hph_img.
pose proof (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pf FILE_BLOCK HJ3r HAR4 Eab4 ltac:(unfold FILE_BLOCK; clear; lia)) as Tpf.
assert (Apf : forall blc lyq ownq i, In (pf, FILE_BLOCK) blc -> 0 <= i < req_size FILE_BLOCK -> awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc lyq ownq (pf + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pf FILE_BLOCK blc i lyq ownq HJ3r HAR4 Eab4 ltac:(unfold FILE_BLOCK; clear; lia) Hbl Hi). }
pose proof (sep_block_frame SEGS B LAWS ly4 S4 _ _ _ pf FILE_BLOCK 1 fpos HAR4 Hpf_in Hfin4) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (req_size FILE_BLOCK) with 1264 in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA4 in HdPF. fold F in HdPF.
pose proof (sep_block_frame SEGS B LAWS ly4 S4 _ _ _ pf FILE_BLOCK cid pos HAR4 Hpf_in HfinS4) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. change (req_size FILE_BLOCK) with 1264 in HdPC. rewrite EFA4 in HdPC.
lazymatch type of XF with xfacts ?P =>
assert (XF2 : xfacts (P /\ pf + 1264 <= alloc_ceiling /\ 4096 <= pf /\ (pf + 1264 <= 65536 \/ 6270976 <= pf) /\
(pf + 1264 <= cfgp \/ cfgp + 48 <= pf) /\ 4096 <= cfgp /\ (pf + 1264 <= F \/ F + 128 <= pf)))
by (apply xfacts_i; split; [exact XF | clear - Hpfceil Hpf4096 Hph_img HdPC HdPF Hflo Hfhi Hf4096; lia]);
clear XF HdPC HdPF Hph_img; rename XF2 into XF end.
change (in_app pf 1264) with (xfacts (in_app pf 1264)) in Hp_ia.
assert (Hk0 : k = 0) by (pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & Hk0' & _); clear - Hk0' Hk3; lia).
assert (MLE4 : mo_le MT S S4 (ng_macc1 MT)).
{ unfold ng_macc1. replace (mo_malloc MT FILE_BLOCK) with (0 + mo_malloc MT FILE_BLOCK) by (clear; lia).
apply (mle_station MT S S3 S4 0 _ MLAW); [pose proof HJ3 as HJ30; rewrite Hk0 in HJ30; eapply afm_k0; [exact AFM | exact HJ30] | eapply afm_open; [exact AFM | exact HJc | exact Eab4]]. }
reseat_lo 48%nat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first [ keptJ HJc HJ4 AG Usp E10 RF E529 Hfin3 HfinS3 FFS KgotB Kgot4 KcellB Kcell4 KguarB Kguar4 KuarB Kuar4 VgrB Vgr4 EFA3 HFpres4 HFSpres4 HCpres4 F ltac:(fptok)
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
prreg HS (10%bv : bv 5) Rpf. cbn [ms_regs] in Rpf. rewrite Ha04 in Rpf. symmetry in Rpf. unfold w64 in Rpf.
lazymatch type of Rpf with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rpf, unsigned_lit_small by (clear - Hpf4096 Hpfceil C1; lia); change (2 ^ 4) with 16; clear - Hpf4096 Hpfceil Hpf16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat.
hei_havoc HS; paj_run_tok RUN HS HJ4 SHOK NBspan; [slim; awrR AG fpos F EFA4 |].
xsink_stretch HFr HSINK. clear_frames.
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
clear KgotB KcellB KguarB KuarB VgrB. clear Kgot4 Kcell4 Kguar4 Kuar4 Vgr4. aconsts HROD HJ4 KgotC KcellC KguarC KuarC VgrC.
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
assert (Qceil : alloc_ceiling <= spZ regs) by lia. assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
assert (Qtop : spZ regs < ly_top ly - 16) by lia. assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia. assert (Qsp : spZ regs - 192 + 16 <= spZ regs) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msX) a = aview SEGS (w_H W) mem a)
by (intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; [clear - Ha Qceil; lia | clear - Ha; lia]) | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem msX) a = aview SEGS (w_H W) mem a)
by (intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; [clear - Ha Qceil; lia | clear - Ha; lia])  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W4) msX) i _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview SEGS (w_H W4) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp)
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W4) msX) i _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview SEGS (w_H W4) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp)
| ]  end.
pmkst HS.
ppcs.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (amalloc04_sub SEGS B LAWS Hsegs MT AMALLOC4 _ (ms_regs msX) (ms_mem msX) TNEWGIFX_STK (spZ regs) [sink_token] ly S W mem md [(1, fpos)]
ly4 S4 _ (k + 1) 96 (-192) (Z_to_bv 64 (BASE + 0x1a0)) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ4) end.
- exact Ra0.
- rewrite HMM. lia.
- rewrite (blocks_bytes_bsum B ly4 S4), Eab4, Eab3, bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd]. unfold LIVE_NEWGIF, LIVE_MAX, FILE_BLOCK in *. clear - Hlive. lia.
- unfold spZ. rewrite Rsp. evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _). rewrite HEV in Hev. unfold EV_MAX in *. clear - Hnev4 Hev Hk3. lia.
- pose proof (proj1 (proj2 HJ4)) as HLY4. pose proof HLY4 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & _).
apply (achain_chain_pre ly4 _ (spZ regs - 192) (spZ regs) _ _ (achain_ly_top ly ly4 _ _ _ _ Etop4 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; evalE AG
| unfold s0Z; rewrite Rs0; evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia.
apply (HU _ _ Hctx); cbn [ng_traces In]; repeat (first [left; reflexivity | right]).
-
apply (mok_station MT S S4 (xm_newgif XN ngp) (ng_macc1 MT) _ MLAW HMOK MLE4); [apply (mo_malloc_nonneg MT MLAW); clear; lia|].
pose proof (HXM ngp Rngp) as Hx. unfold ng_msum, ng_macc3, ng_macc2 in Hx.
pose proof (mo_malloc_nonneg MT MLAW (3 * ngp) ltac:(clear - Rngp; lia)) as M3.
pose proof (mo_malloc_nonneg MT MLAW RAW_SIZE ltac:(unfold RAW_SIZE; lia)) as M4.
pose proof (mo_free_nonneg MT MLAW) as M5. clear - Hx M3 M4 M5. lia. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & g & -> & HJ5 & HP5 & Ha05 & Hfrs5 & Hg4096 & Eab5 & HK5 & MLE5 & HJt5).
assert (Hpf_in5 : In (pf, FILE_BLOCK) (ablocks B ly5 S5)) by (rewrite Eab5; apply in_app_iff; left; exact Hpf_in).
xsink_sub HJt5 HSINK Hpf_in Hpf_in5. clear HJt5.
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUP Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
unfold ASTACK in HK5. replace (spZ regs + -192 - 16384) with (spZ regs - 16576) in HK5 by lia. replace (spZ regs + -192) with (spZ regs - 192) in HK5 by lia.
pose proof (proj1 HJ5) as HAR5. aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly5 HAR (proj1 (proj2 HJ5))) as (_ & EFA5 & _).
assert (EFL5 : forall c p, flag_addr ly5 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA5 c p) as X; unfold frame_addr in X; lia).
assert (Hfin5 : In (1, fpos) (frames S5)) by (rewrite Hfrs5; exact Hfin4).
assert (HfinS5 : In (cid, pos) (frames S5)) by (rewrite Hfrs5; exact HfinS4).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR5 Hfin5) as (_ & _ & HFpres5 & HFSpres5). change (fs_frame_bytes 1) with 128 in HFpres5, HFSpres5.
change (128 / 8) with 16 in HFSpres5. rewrite !EFA5 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
assert (Hg_in : In (g, 96) (ablocks B ly5 S5)) by (rewrite Eab5; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 HAR5 Hg_in) as (Hg16 & _ & Hgceil & Hgh_ia & Hgpres & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g 96 HAR5 Hg_in) as Hgh_img.
change (req_size 96) with 96 in Hgceil, Hgpres, Hgh_img.
pose proof (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g 96 HJ4 HAR5 Eab5 ltac:(lia)) as Tg.
assert (Ag : forall blc lyq ownq i, In (g, 96) blc -> 0 <= i < 96 -> awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc lyq ownq (g + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g 96 blc i lyq ownq HJ4 HAR5 Eab5 ltac:(lia) Hbl ltac:(change (req_size 96) with 96; lia)). }
pose proof (sep_block_frame SEGS B LAWS ly5 S5 _ _ _ g 96 1 fpos HAR5 Hg_in Hfin5) as HdGF.
unfold zdisjoint in HdGF. cbn [fst snd] in HdGF. change (req_size 96) with 96 in HdGF. change (fs_frame_bytes 1) with 128 in HdGF. rewrite EFA5 in HdGF. fold F in HdGF.
pose proof (sep_block_frame SEGS B LAWS ly5 S5 _ _ _ g 96 cid pos HAR5 Hg_in HfinS5) as HdGC.
unfold zdisjoint in HdGC. cbn [fst snd] in HdGC. change (req_size 96) with 96 in HdGC. rewrite EFA5 in HdGC.
pose proof (sep_blocks SEGS B LAWS ly5 S5 _ _ _ pf FILE_BLOCK g 96 HAR5 Hpf_in5 Hg_in ltac:(unfold FILE_BLOCK; intros X; injection X; lia)) as HdPG.
unfold zdisjoint in HdPG. cbn [fst snd] in HdPG. change (req_size 96) with 96 in HdPG. change (req_size FILE_BLOCK) with 1264 in HdPG.
pose proof Hgh_img as HGoff. unfold off_img in HGoff.
lazymatch type of XF with xfacts ?P =>
assert (XF2 : xfacts (P /\ (pf + 1264 <= g \/ g + 96 <= pf) /\ 4096 <= g /\ g + 96 <= alloc_ceiling /\ (g + 96 <= 65536 \/ 6270976 <= g)))
by (apply xfacts_i; split; [exact XF | clear - HdPG Hg4096 Hgceil HGoff; lia]); clear XF HGoff HdPG; rename XF2 into XF end.
assert (HErF : forall a, F <= a < F + 128 -> ~ (g <= a < g + req_size 96)) by (change (req_size 96) with 96; intros a Ha; clear - Ha HdGF; lia).
nbox HdGF.
reseat_k 546%nat HS HJ5 HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first [ keptR HK5 HJ5 AG Usp E10 E32 HfinS4 I KgotC Kgot5 KcellC Kcell5 KguarC Kguar5 KuarC Kuar5 VgrC Vgr5 EFA4
| keptF HK5 AG RF E529 Hfin4 HFpres5 HFSpres5 HErF F EFA4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
nbox HdGC.
prreg HS (10%bv : bv 5) Rg. cbn [ms_regs] in Rg. rewrite Ha05 in Rg. symmetry in Rg. unfold w64 in Rg.
lazymatch type of Rg with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rg, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some nx) 0 96 0 96 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Rg, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hgpres (g + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Rg; change (fs_frame_bytes 1) with 128; change (fs_frame_bytes 1 / 8) with 16; evalE AG;
nunbox HdGF; nunbox HdGC; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NMX in HS;
eapply (NGM ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E0 Ev W5 ly5 S5 msv _ (k + 1 + 1) fpos pf g);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| split; [exact HGP | split; [exact HSNK0 | split; [exact HFD0 | split; [exact HAM0 | exact HMOK]]]]
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [split; [exact AG | repeat (split; [eassumption|]); eassumption] | exact E42]
| exact Rpf
| exact Rg
| split; [exact HJ5 | split; [clear - Hk3; lia | split; [rewrite Hfrs5, Hfrs4; exact Hfrs3 | split; [rewrite Eab5, Eab4, Eab3; reflexivity | split; [exact Hg4096 | split; [exact Hpf4096 |
split; [exact Tg | split; [exact Ag | split; [exact Tpf | split; [exact Apf | split; [exact HSINK |]]]]]]]]]]]
| exact HW0 | exact HH0
| exact HS ] end.
{ exact Hctx. }
{   unfold ng_macc2. exact (mle_station MT S S4 S5 _ _ MLAW MLE4 MLE5). } }
Qed.
End f. End d.
End b.
