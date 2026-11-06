(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_grant_build_sweep's contract, adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v (the entry state and its region_ok facts), lib/A/AChf.v (the side-stack frame: aj_stack_malloc_atS, the realigned sp, reseat, the frame and shadow regions, the shadow_decl_ok alias), lib/A/ACb8.v (the chain pushed at a call, the flag store and the return) and lib/A/ACh1.v (a callee in afn_pre form through cl_callS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proof speed only, no statement change: lia's case splits are hidden at the hot steps (rs_hide_all) and the exit paths drop the facts they do not need. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantBuildSweepWalk.v, with its module paths, module names and numbers changed; 643 of its 705 lines of code are new or changed and 591 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaStep DiscoSyms DiscoList DiscoAddr DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import TjSpec TjBase DiscoRo TjCuts TjEntry TjLoopCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef ConstsViewDef StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec ReacBoxName TjBoxRom.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac notw AG :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; unfold boxed in *; lia|]);
destruct Hin.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) (@pa_relro_lo _ disco_listing PI) (@pa_relro_hi _ disco_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma tj_garr8_u1 : forall (m : word -> option byte) (a k : Z) (T : list byte),
garr8 SEGS m a (map bv_unsigned T) -> 0 <= k -> k + 1 <= Z.of_nat (length T) ->
val_mem SEGS m (a + k) 1 (disco_table_c.u_at T k 1) /\ 0 <= disco_table_c.u_at T k 1 < 256.
Proof.
intros m a k T HG Hk HkT.
assert (Hlen : length (disco_table_c.sub T k 1) = 1%nat) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn; lia).
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k 1)) as H0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k 1)) as H1. rewrite Hlen in H1.
split; [|unfold disco_table_c.u_at; change (2 ^ (8 * Z.of_nat 1)) with 256 in H1; lia].
intros j Hj.
assert (Hlt : (Z.to_nat k + j < length (map bv_unsigned T))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte SEGS m a _ (Z.to_nat k + j) HG Hlt) as Hb.
replace (a + Z.of_nat (Z.to_nat k + j)) with (a + k + Z.of_nat j) in Hb by lia.
rewrite Hb. f_equal.
assert (Hnth : nth_error (disco_table_c.sub T k 1) j = Some (nth (Z.to_nat k + j) T (Z_to_bv 8 0))).
{ unfold disco_table_c.sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec j 1); [|lia].
rewrite nth_error_skipn. apply nth_error_nth'. lia. }
pose proof (YA0j.nth_error_le_byte _ _ _ Hnth) as Hv.
rewrite (nth_indep (map bv_unsigned T) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite map_nth. rewrite Hv. unfold disco_table_c.u_at, YO0f.le_byte.
assert (Ej : j = 0%nat) by lia. subst j.
rewrite ?Z.shiftr_div_pow2 by lia. f_equal. cbn [Z.of_nat]. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * 0)) with 1. lia.
Qed.
Lemma tjb_aview0 : forall H (m : word -> option byte) a, val_mem SEGS (mrestrict H m) a 1 0 -> aview SEGS H m a = Some 0.
Proof.
intros H m a Hv. unfold aview. pose proof (Hv 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0.
rewrite H0. reflexivity.
Qed.
Lemma tjb_vis : forall H (m : word -> option byte) a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma tjb_ra : forall H (m : word -> option byte) a n,
(forall x, a <= x < a + n -> aview SEGS H m (SHADOW_OFF + x / 8) = Some 0) ->
range_addressable (aview SEGS H m) SHADOW_OFF a n.
Proof. intros H m a n Hz x Hx. exists 0. split; [unfold shadow_of_addr; exact (Hz x Hx) | left; reflexivity]. Qed.
Lemma tjb_rbn_wr_rng : forall f sd i o nm nl tk tl dp dl a,
rbn_wr f sd i o nm nl tk tl dp dl a -> nm <= a < nm + nl \/ tk <= a < tk + tl \/ dp <= a < dp + dl.
Proof.
intros f sd i o nm nl tk tl dp dl a (Hacc & Hr). unfold reac_box_name_c.bn_accept in Hacc.
repeat rewrite andb_true_iff in Hacc. destruct Hacc as ((((_ & _) & H1) & H2) & H3).
apply Z.ltb_lt in H1, H2, H3. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis RBR : tj_rbn_rom.
Hypothesis RBN : treac_box_name_spec B.
Variables STK EV EVB : Z.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Hypothesis HSTK : TJ_FRAME + SnprintfDef.SNPRINTF_STK <= STK.
Hypothesis HEVB : 0 <= EVB.
Theorem pb_tj_box : tj_seg_box B STK EV EVB IMG.
Proof.
unfold tj_seg_box. intros i FU FK.
unfold tj_fromR, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
pose proof HBASE as HBX.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
unfold INV_tjR, tj_lbody, tj_split, tj_wrote, tj_e, tj_age, tj_after2 in HINV.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
pose proof HB0 as (HPRE & Hfrm0 & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hev & Hsp1b & HE0 & HE032 & HE02).
pose proof HX0 as (AG & E60 & E516 & E528 & E529 & HEI).
destruct HINV as (Hk0 & (Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E723 & E734 & E740 & E741) & acc & (o1 & o2 & E793 & E784 & Ho1 & Ho2 & Ho12) & Hacc & Htxt & Hgarr).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SnprintfDef.SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= STK) by (unfold TJ_FRAME in HSTK; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *. set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact (HE0 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (AG 2%nat ltac:(lia)); exact (HE0 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact HE02).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite (AG n ltac:(lia)); exact (HE0 n r Hn)).
img_factsF E.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Hob242. pose proof (pa_obj_img 0 ltac:(unfold disco_nobj; lia)) as Hob241.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Hob307. pose proof (pa_obj_img 67 ltac:(unfold disco_nobj; lia)) as Hob308.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob307, Hob308.
pose proof (palf_uar_img B TL) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob307, Hob308, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres. fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & HNb).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR3 Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hinb Hfin) as Hbsep.
rewrite EFA0 in Hbsep. fold F in Hbsep. change (fs_frame_bytes 2) with 256 in Hbsep. unfold zdisjoint in Hbsep. cbn [fst snd] in Hbsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
box Hbapp. box Hbimg. box Hbsep.
paj_run_shc RUNP RUNC HS HJ. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict (w_H _) ?m0) (mrestrict _ ?m1) =>
assert (HKB1 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
assert (HK1 : tj_keep B (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) W3 (ms_mem ms))
by (eapply tj_keep_journal; eassumption).
unfold tj_keep in HK1. cbn [c_t c_T c_ly c_S] in HK1. destruct HK1 as (HROD1 & Hgt1 & Hobj1).
pose proof Hobj1 as ((tcid & tpos & Htin & Htcid & HTF8 & HTFlo & HTFhi) & Ht8 & Htra).
pose proof (proj1 HJ) as HARr.
assert (Htin3 : In (tcid, tpos) (frames S3)) by (rewrite HFR; right; exact Htin).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ tcid tpos HARr Htin3) as (HT4096 & HTceil & HTapp).
rewrite EFA in HT4096, HTceil, HTapp.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HARr Htin3) as HTimg. rewrite EFA in HTimg.
set (TF := frame_addr ly tcid tpos) in *.
assert (HdTF : zdisjoint (frame_rng ly3 (2, fpos)) (frame_rng ly3 (tcid, tpos))).
{ destruct (in_split _ _ Htin) as (l2 & l3 & Hsp).
eapply (sep_frames_pos SEGS B LAWS _ _ _ _ _ (2, fpos) (tcid, tpos) [] l2 l3 HARr). rewrite HFR, Hsp. reflexivity. }
unfold zdisjoint, frame_rng in HdTF. cbn [fst snd] in HdTF. rewrite !EFA in HdTF. fold F TF in HdTF. change (fs_frame_bytes 2) with 256 in HdTF.
destruct Hok as (Hn8 & Hok2). unfold disco_table_c.tbl_T1 in Hn8.
set (e := t + 48 * i) in *.
destruct (tj_garr8_u1 _ t (48 * i + 12) T Hgt1 ltac:(lia) ltac:(rewrite HlenT; lia)) as (Vhd & Rhd).
destruct (tj_garr8_u1 _ t (48 * i + 13) T Hgt1 ltac:(lia) ltac:(rewrite HlenT; lia)) as (Vdin & Rdin).
destruct (tj_garr8_u1 _ t (48 * i + 14) T Hgt1 ltac:(lia) ltac:(rewrite HlenT; lia)) as (Vdout & Rdout).
destruct (tj_garr8_u1 _ t (48 * i + 15) T Hgt1 ltac:(lia) ltac:(rewrite HlenT; lia)) as (Vfam & Rfam).
replace (t + (48 * i + 12)) with (e + 12) in Vhd by (unfold e; lia).
replace (t + (48 * i + 13)) with (e + 13) in Vdin by (unfold e; lia).
replace (t + (48 * i + 14)) with (e + 14) in Vdout by (unfold e; lia).
replace (t + (48 * i + 15)) with (e + 15) in Vfam by (unfold e; lia).
set (hd := disco_table_c.u_at T (48 * i + 12) 1) in *.
set (din := disco_table_c.u_at T (48 * i + 13) 1) in *.
set (dout := disco_table_c.u_at T (48 * i + 14) 1) in *.
set (fam := disco_table_c.u_at T (48 * i + 15) 1) in *.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 900 Ev ssv msv [Z_to_bv 64 hd; Z_to_bv 64 din; Z_to_bv 64 dout; Z_to_bv 64 fam] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 900%nat [Z_to_bv 64 hd; Z_to_bv 64 din; Z_to_bv 64 dout; Z_to_bv 64 fam] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E900 : ew Ev 900 = Z_to_bv 64 hd) by (rewrite HEv; exact (ew_havoc_new _ 900 [Z_to_bv 64 hd; Z_to_bv 64 din; Z_to_bv 64 dout; Z_to_bv 64 fam] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E901 : ew Ev 901 = Z_to_bv 64 din) by (rewrite HEv; exact (ew_havoc_new _ 900 [Z_to_bv 64 hd; Z_to_bv 64 din; Z_to_bv 64 dout; Z_to_bv 64 fam] 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E902 : ew Ev 902 = Z_to_bv 64 dout) by (rewrite HEv; exact (ew_havoc_new _ 900 [Z_to_bv 64 hd; Z_to_bv 64 din; Z_to_bv 64 dout; Z_to_bv 64 fam] 2 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E903 : ew Ev 903 = Z_to_bv 64 fam) by (rewrite HEv; exact (ew_havoc_new _ 900 [Z_to_bv 64 hd; Z_to_bv 64 din; Z_to_bv 64 dout; Z_to_bv 64 fam] 3 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 740 (mkAF 4096 140737479966720 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E740; unfold w64; rewrite unsigned_lit_small by lia; change (2 ^ 3) with 8; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 900 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E900, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 901 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E901, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 902 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E902, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 903 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E903, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
assert (HF8hi' : F / 8 <= 17592184995808) by (apply Z.div_le_upper_bound; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 740%nat) 12 16 0 0 [YP09.mkChunk 12 (CVal 1 (SOff 900 0)); YP09.mkChunk 13 (CVal 1 (SOff 901 0)); YP09.mkChunk 14 (CVal 1 (SOff 902 0)); YP09.mkChunk 15 (CVal 1 (SOff 903 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E740; unfold w64; rewrite unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 12 1 _ hd); [cbn [sv_denot]; rewrite E900, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Vhd]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 13 1 _ din); [cbn [sv_denot]; rewrite E901, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Vdin]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 14 1 _ dout); [cbn [sv_denot]; rewrite E902, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Vdout]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 15 1 _ fam); [cbn [sv_denot]; rewrite E903, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Vfam]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E740; unfold w64; evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi' Hob241 Hob242 Hob307 Hob308 Huar
HT4096 HTceil HTapp HTimg HTFlo HTFhi HdTF Hi Hn8;
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) (-16) 0 (-16) 0 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 HSK C1 Hshi H47; lia); split; [clear - Hsp1 Hceil Hslo Hstk0 HSK C1; lia|]; split; [clear - Hsp1 Hshi H47; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJpres; clear - Ho Hsp1 HSK; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?E740; unfold w64; evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi' Hob241 Hob242 Hob307 Hob308 Huar
HT4096 HTceil HTapp HTimg HTFlo HTFhi Hi Hn8;
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
clear HJpres.
norm_ss HS.
fs_roF HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
shok_auto_with SHOK (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem ms)) [mkSHE 740 0 48]
ltac:(idtac; lazymatch goal with |- shent_ok _ _ _ _ (mkSHE 740 _ _) =>
apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms) Ev (SOff 32 0) 740 t 400 e 0 48 Htra);
[ rewrite (U_atom Ev 32 SB) by (first [rewrite (AG 32%nat) by lia; exact HE032 | unfold SB; lia]); reflexivity
| apply U_atom; [rewrite E740; reflexivity | lia]
| lia | lia
| intros x Hx; clear - Hx HTapp HTFlo HTFhi Hi Hn8; unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg in *; cbn [Z.min Z.max] in Hx; lia ] end) end.
clear HTapp HTimg HdTF.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict (w_H _) ?m0) (mrestrict _ ?m1) =>
assert (HKB2 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK Bspan.
-
rename Hc into Hc0.
rewrite branch_eq_U, (U_atom _ 900 hd E900 ltac:(lia)), U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK Bspan 24368. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict (w_H _) ?m0) (mrestrict _ ?m1) =>
assert (HKB3 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
pose proof (proj1 HJ) as HARq.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARq Hfin) as (_ & _ & _ & HFSx).
rewrite EFA in HFSx. fold F in HFSx. change (fs_frame_bytes 2 / 8) with 32 in HFSx.
fs_rwF HS E529 HFSx.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rregU HS (26%bv : bv 5) (Z.of_nat (length acc))
ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom Ev 784 o2 E784), (U_atom Ev 793 o1 E793) by lia; rewrite zcanon_id by (unfold M64; lia); lia) R26 end.
ra_join HS ss_tjU 800%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 800%nat 13%nat R26 E813.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (FU (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k _ _ Wg msF mdF) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia].
+ exact HJ.
+ exact HFR.
+ unfold INV_tjU, tj_lbody, tj_wrote, tj_e, tj_age, tj_after2. cbn [c_ly c_S c_cap c_T c_now c_buf c_t].
rewrite !ew_havoc_old by (cbn; lia).
split; [nia|].
split; [split; [exact Hperm|]; split; [eapply tj_keep_journal; eassumption|];
split; [exact Hcap3|]; split; [exact Hi|]; repeat (split; [assumption|]); assumption|].
split; [unfold model_of; replace (e_has_decl (reac_disco_table_json_c.tj_entry T i)) with hd by reflexivity; rewrite Hc0; reflexivity|].
exists acc. split; [exact E813|]. split; [exact Hacc|]. split; [exact Htxt|].
assert (HLacc : Z.of_nat (length (acc ++ [0])) <= cap) by (rewrite length_app; cbn [length]; lia).
eapply garr8_aview_kept; [|exact Hgarr].
intros a Ha. rewrite HKB3, HKB2, HKB1 by lia. reflexivity.
+ exact HS.
-
rename Hc into Hc0.
rewrite branch_eq_U, (U_atom _ 900 hd E900 ltac:(lia)), U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict (w_H _) ?m0) (mrestrict _ ?m1) =>
assert (HKB3 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
prreg HS (1%bv : bv 5) Qra. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (8%bv : bv 5) Qs0.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rregU HS (2%bv : bv 5) (sp1 - 16) ltac:(rewrite (U_atom_off Ev 60 sp1 (-16) E60) by lia; lia) Rsp;
rregU HS (10%bv : bv 5) fam ltac:(exact (U_atom Ev 903 fam E903 ltac:(lia))) Ra0;
rregU HS (11%bv : bv 5) 0 ltac:(rewrite U_lit by lia; reflexivity) Ra1;
rregU HS (12%bv : bv 5) din ltac:(exact (U_atom Ev 901 din E901 ltac:(lia))) Ra2;
rregU HS (13%bv : bv 5) dout ltac:(exact (U_atom Ev 902 dout E902 ltac:(lia))) Ra3;
rregU HS (14%bv : bv 5) (F + 32) ltac:(exact (U_atom_off Ev 516 F 32 E516 ltac:(lia) ltac:(lia))) Ra4;
rregU HS (15%bv : bv 5) 24 ltac:(rewrite U_lit by lia; reflexivity) Ra5;
rregU HS (16%bv : bv 5) (F + 96) ltac:(exact (U_atom_off Ev 516 F 96 E516 ltac:(lia) ltac:(lia))) Ra6;
rregU HS (17%bv : bv 5) 24 ltac:(rewrite U_lit by lia; reflexivity) Ra7 end.
pmkst HS. rewrite pa_sigma_reac_box_name.
pose proof (proj1 HJ) as HARc.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARc Hfin) as (_ & _ & HFPc & HFSc).
rewrite EFA in HFPc, HFSc. fold F in HFPc, HFSc. change (fs_frame_bytes 2 / 8) with 32 in HFSc. change (fs_frame_bytes 2) with 256 in HFPc.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_region_nth Ev _ _ 0 _ HS eq_refl) as RG0;
pose proof (st_ok_region_nth Ev _ _ 2 _ HS eq_refl) as RG2;
pose proof (st_ok_region_nth Ev _ _ 5 _ HS eq_refl) as RG5 end.
cbn [ms_mem restrict] in RG0, RG2, RG5.
assert (Hspc : spZ (ms_regs ms1) = sp1 - 16) by (unfold spZ; rewrite Rsp; apply unsigned_lit_small; lia).
assert (Hs0c : s0Z (ms_regs ms1) = spZ regs) by (unfold s0Z; rewrite Qs0, (AG 2%nat) by lia; exact HE02).
assert (Vdisp : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms1)) (sp1 - 16) 8 (F + 160)).
{ replace (sp1 - 16) with (sp1 + -16) by lia.
lazymatch type of RG0 with region_ok _ ?Ev _ _ =>
exact (field_of_region Ev _ 60 sp1 _ _ _ _ _ (-16) 8 (SOff 516 160) (F + 160) RG0
ltac:(rewrite E60; apply unsigned_lit_small; lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
ltac:(cbn [sv_denot]; rewrite E516, unsigned_lit_small by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) end. }
assert (Vdlen : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms1)) (sp1 - 16 + 8) 8 48).
{ replace (sp1 - 16 + 8) with (sp1 + -8) by lia.
lazymatch type of RG0 with region_ok _ ?Ev _ _ =>
exact (field_of_region Ev _ 60 sp1 _ _ _ _ _ (-8) 8 (SLit 48) 48 RG0
ltac:(rewrite E60; apply unsigned_lit_small; lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) end. }
assert (Z0 : forall j, (4 <= j < 7 \/ 12 <= j < 15 \/ 20 <= j < 26) ->
aview SEGS (w_H W3) (ms_mem ms1) (SB + F / 8 + j) = Some 0).
{ intros j Hj. apply tjb_aview0.
assert (Hj' : j = 4 \/ j = 5 \/ j = 6 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/ False) by lia.
lazymatch type of RG2 with region_ok _ ?Ev _ _ =>
repeat (destruct Hj' as [-> | Hj']; [lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
exact (field_of_region Ev _ 529 (SB + F / 8) _ _ _ _ _ od 1 (SLit 0) 0 RG2
ltac:(rewrite E529; apply unsigned_lit_small; unfold SB; lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) end |]) end.
destruct Hj'. }
assert (RAn : range_addressable (aview SEGS (w_H W3) (ms_mem ms1)) SHADOW_OFF (F + 32) 24).
{ apply tjb_ra. intros x Hx. replace (SHADOW_OFF + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by (unfold SB, SHADOW_OFF; lia). apply Z0. lia. }
assert (RAt : range_addressable (aview SEGS (w_H W3) (ms_mem ms1)) SHADOW_OFF (F + 96) 24).
{ apply tjb_ra. intros x Hx. replace (SHADOW_OFF + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by (unfold SB, SHADOW_OFF; lia). apply Z0. lia. }
assert (RAd : range_addressable (aview SEGS (w_H W3) (ms_mem ms1)) SHADOW_OFF (F + 160) 48).
{ apply tjb_ra. intros x Hx. replace (SHADOW_OFF + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by (unfold SB, SHADOW_OFF; lia). apply Z0. lia. }
assert (HVA : forall b n, F + 32 <= b -> b + n <= F + 208 -> 0 < n -> shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms1)) b n).
{ intros b n Hb1 Hb2 Hn s Hs. unfold shadow_addr in Hs. apply tjb_vis.
replace s with (shadow_addr F + (s - shadow_addr F)) by lia.
apply (proj1 (HFSc (s - shadow_addr F) ltac:(unfold shadow_addr, SHADOW_OFF in *; lia))). }
assert (WRF : forall a, F <= a < F + 256 ->
awr_byte STK (spZ regs) (tj_fp buf cap) (ablocks B ly S) (ablocks B ly3 S3) ly3 [(2, fpos)] a /\ apresent (w_H W3) (ms_mem ms1) a).
{ intros a Ha. split; [|exact (proj1 (HFPc a Ha))].
right; right; right. exists 2, fpos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EFA0. change (fs_frame_bytes 2) with 256. fold F. lia. }
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
assert (Hchc : exists chX, achain ly3 (aview SEGS (w_H W3) (ms_mem ms1)) (sp1 - 16) (spZ regs) chX).
{ destruct (Z_lt_ge_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch). apply (achain_ly_top ly ly3 _ _ _ _ Etop3).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & HJup & _).
pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hr1. pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hr8.
change (bv_modulus 64) with (2 ^ 64) in Hr1, Hr8.
lazymatch type of RG5 with region_ok _ ?Ev _ _ =>
eapply (achain_push ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) (raZ regs) ch (sp1 - 16) Hch);
[ lia
| intros a Ha; apply HJup; lia
| apply rdword_of_val_mem; [replace (spZ regs - 8) with (spZ regs + -8) by lia;
exact (field_of_region Ev _ 2 (spZ regs) _ _ _ _ _ (-8) 8 (SOff 1 0) (raZ regs) RG5
ltac:(rewrite (AG 2%nat) by lia; exact HE02) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
ltac:(cbn [sv_denot]; rewrite (AG 1%nat), (HE0 1%nat 1%bv eq_refl) by lia; unfold raZ; rewrite Z.add_0_r; reflexivity)
ltac:(cbn; unfold raZ; lia) ltac:(cbn; lia))
| unfold raZ; lia]
| apply rdword_of_val_mem; [replace (spZ regs - 16) with (spZ regs + -16) by lia;
exact (field_of_region Ev _ 2 (spZ regs) _ _ _ _ _ (-16) 8 (SOff 8 0) (s0Z regs) RG5
ltac:(rewrite (AG 2%nat) by lia; exact HE02) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
ltac:(cbn [sv_denot]; rewrite (AG 8%nat), (HE0 8%nat 8%bv eq_refl) by lia; unfold s0Z; rewrite Z.add_0_r; reflexivity)
ltac:(cbn; unfold s0Z; lia) ltac:(cbn; lia))
| unfold s0Z; lia]
| exact Hra4 | lia | lia | lia | lia ] end.
- exists []. left. split; [right; left; rewrite Etop3; lia | reflexivity]. }
destruct Hchc as (chX & Hchc).
pose proof HFhigh as HFhU. unfold in_app, kLowShadowBeg, kHighMemBeg in HFhU. box HFhU.
set (FLv := bv_unsigned (Z_to_bv 64 FLg)).
assert (VFL : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms1)) (F + 248) 8 FLv).
{ lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_region_nth Ev _ _ 3 _ HS eq_refl) as RG3; cbn [ms_mem restrict] in RG3;
exact (field_of_region Ev _ 516 F _ _ _ _ _ 248 8 (SOff 528 0) FLv RG3
ltac:(rewrite E516; apply unsigned_lit_small; lia) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
ltac:(cbn [sv_denot]; rewrite E528, Z.add_0_r; reflexivity)
ltac:(cbn; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 FLg)) as Hfl; change (bv_modulus 64) with (2 ^ 64) in Hfl; unfold FLv; lia) ltac:(cbn; lia)) end. }
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
eapply SRr_bind.
{ eapply (RBN fq STK (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 W3 (ms_mem ms1) _ k (ms_regs ms1) chX
fam 0 din dout (F + 32) 24 (F + 96) 24 (F + 160) 48 []).
- exact HJ.
- exact HRODc.
- exact (tj_mc_consts B DRO _ _ HRODc).
- rewrite Qra. apply ret_ok_codeptr_v; [lia | reflexivity].
- unfold raZ. rewrite Qra, unsigned_lit_small by lia. lia.
- rewrite Qgp, (AG 3%nat), (HE0 3%nat 3%bv eq_refl) by lia. exact Hgp.
- rewrite Qtp, (AG 4%nat), (HE0 4%nat 4%bv eq_refl) by lia. exact Htp.
- rewrite Hspc, Hs0c. exact Hchc.
- rewrite Hspc. lia.
- rewrite Hspc. unfold REAC_BOX_NAME_STK, ESTACK. lia.
- rewrite Hspc. lia.
- rewrite HFR. cbn [length]. lia.
- exact Ra0.
- lia.
- exact Ra1.
- lia.
- exact Ra2.
- lia.
- exact Ra3.
- lia.
- exact Ra4.
- lia.
- exact Ra5.
- lia.
- exact Ra6.
- lia.
- exact Ra7.
- lia.
- rewrite Hspc. exact Vdisp.
- lia.
- rewrite Hspc. exact Vdlen.
- lia.
- eapply tj_rbn_img; eassumption.
- intros _. split; [left; split; reflexivity|].
unfold rbn_bufs, rbn_buf. rewrite Hspc. change (Z.min 24 24) with 24. change (Z.min 48 48) with 48.
assert (Hsep : F + 256 <= sp1 - 16 - REAC_BOX_NAME_STK) by (unfold REAC_BOX_NAME_STK, ESTACK; lia).
split; [split; [lia|]; split; [lia|]; split; [apply (amem_range_sub_app F 256); [exact HFhigh | lia | lia | lia | lia]|];
split; [right; lia|]; split; [exact RAn|]; split; [apply HVA; lia|]; intros a Ha; apply WRF; lia|].
split; [split; [lia|]; split; [lia|]; split; [apply (amem_range_sub_app F 256); [exact HFhigh | lia | lia | lia | lia]|];
split; [right; lia|]; split; [exact RAt|]; split; [apply HVA; lia|]; intros a Ha; apply WRF; lia|].
split; [split; [lia|]; split; [lia|]; split; [apply (amem_range_sub_app F 256); [exact HFhigh | lia | lia | lia | lia]|];
split; [right; lia|]; split; [exact RAd|]; split; [apply HVA; lia|]; intros a Ha; apply WRF; lia|].
lia. }
cbv beta. intros W2 c2 HWle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HfrS2 & HPerm2 & Ha0' & K1 & K2 & K3 & K4 & K5 & K6 & HACC).
rewrite Hspc in K1, K5, K6. rewrite Qra.
assert (HKc : acall_kept SEGS B ly3 S3 W3 (ms_mem ms1) W2 mem2 (sp1 - 16 - REAC_BOX_NAME_STK) (sp1 - 16)
(rbn_wr fam [] din dout (F + 32) 24 (F + 96) 24 (F + 160) 48)).
{ split; [intros a Ha Hn; apply K1; [exact Ha | exact Hn | intros HW; apply tjb_rbn_wr_rng in HW; lia]|].
split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5 | exact K6]. }
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite HfrS2; exact Hfin).
destruct (al_layout _ _ LAWS ly S W mem md ly2 HAR (proj1 (proj2 HJ2))) as (_ & EFA2 & _).
assert (HKF2 : forall a, (F <= a < F + 256 /\ ~ (F + 32 <= a < F + 208)) \/ (SB + F / 8 <= a < SB + F / 8 + 32) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms1) a).
{ intros a Ha. apply (K4 2 fpos a Hfin).
- destruct Ha as [Ha | Ha]; [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA0; change (fs_frame_bytes 2) with 256; fold F; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA0; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB, SHADOW_OFF in *; lia].
- intros HW. apply tjb_rbn_wr_rng in HW. unfold boxed in HFhU. unfold SB in *. lia. }
assert (Z2 : forall j, 12 <= j < 15 -> aview SEGS (w_H W2) mem2 (SB + F / 8 + j) = Some 0).
{ intros j Hj. rewrite HKF2 by (right; lia). apply Z0. lia. }
assert (VFL2 : val_mem SEGS (mrestrict (w_H W2) mem2) (F + 248) 8 FLv).
{ eapply val_mem_aview_kept_x; [|exact VFL]. intros x Hx. apply HKF2. left. cbn in Hx. lia. }
reseat HS HJ2 HP2 [4; 5; 6; 7; 8; 9]%nat AG ltac:(idtac; keptFL HKc HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0' in RF. symmetry in RF.
destruct (reac_box_name_c.bn_accept fam [] din dout (F + 32) 24 (F + 96) 24 (F + 160) 48) eqn:Eacc; cbv beta iota in RF.
+
pose proof Eacc as Eacc'. unfold reac_box_name_c.bn_accept in Eacc'. repeat rewrite andb_true_iff in Eacc'.
destruct Eacc' as ((((_ & Hret) & Hlnm) & Hltk) & Hldp). apply Z.eqb_eq in Hret. apply Z.ltb_lt in Hlnm, Hltk, Hldp.
destruct (HACC eq_refl) as (_ & Gtk & _).
hei_havoc HS; paj_run_shc RUNP RUNC HS HJ2. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict (w_H _) ?m0) (mrestrict _ ?m1) =>
assert (HKB4 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W2) m1 a = aview SEGS (w_H W2) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]);
assert (HKF4 : forall a, F <= a < F + 256 \/ SB + F / 8 <= a < SB + F / 8 + 32 -> aview SEGS (w_H W2) m1 a = aview SEGS (w_H W2) m0 a)
by (intros a Ha; unfold SB in Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
*
hei_havoc HS; paj_run_to_shc RUNTOP HS HJ2 24440. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict (w_H _) ?m0) (mrestrict _ ?m1) =>
assert (HKB5 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W2) m1 a = aview SEGS (w_H W2) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]);
assert (HKF5 : forall a, F <= a < F + 256 \/ SB + F / 8 <= a < SB + F / 8 + 32 -> aview SEGS (w_H W2) m1 a = aview SEGS (w_H W2) m0 a)
by (intros a Ha; unfold SB in Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
pose proof (proj1 HJ2) as HARf.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARf Hfin2) as (_ & _ & HFPf & HFSf).
rewrite EFA2 in HFPf, HFSf. fold F in HFPf, HFSf. change (fs_frame_bytes 2 / 8) with 32 in HFSf. change (fs_frame_bytes 2) with 256 in HFPf.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
assert (HKFt : forall a, F <= a < F + 256 \/ SB + F / 8 <= a < SB + F / 8 + 32 -> aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha; rewrite HKF5, HKF4 by exact Ha; reflexivity) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E516, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFPf (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 248 8 _ FLv);
[ cbn [sv_denot]; rewrite E528, Z.add_0_r; reflexivity
| cbn; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 FLg)) as Hfl; change (bv_modulus 64) with (2 ^ 64) in Hfl; unfold FLv; lia
| cbn; lia
| eapply val_mem_aview_kept_x; [|exact VFL2]; intros x Hx; cbn in Hx; apply HKFt; lia ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi' Hob241 Hob242 Hob307 Hob308 Huar;
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 529%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSf; rewrite <- SB_SHADOW_OFF in HFSf; apply (proj1 (HFSf o ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi' Hob241 Hob242 Hob307 Hob308 Huar HFhU;
unfold boxed in *; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
assert (TKra : forall n, 0 < n <= 24 -> range_addressable (aview SEGS (w_H W2) (ms_mem msF)) SHADOW_OFF (F + 96) n)
by (intros n Hn; apply tjb_ra; intros x Hx; replace (SHADOW_OFF + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by (unfold SB, SHADOW_OFF; lia);
rewrite HKFt by (right; unfold SB; lia); apply Z2; lia);
assert (TKhv : forall n, 0 < n <= 24 -> shadow_hull_vis (aview SEGS (w_H W2) (ms_mem msF)) (F + 96) n)
by (intros n Hn s Hs; unfold shadow_addr in Hs; apply tjb_vis; replace s with (shadow_addr F + (s - shadow_addr F)) by lia;
apply (proj1 (HFSf (s - shadow_addr F) ltac:(unfold shadow_addr, SHADOW_OFF in *; lia)))) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E32v : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact HE032);
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 (SB + (e + 14) / 8)) (denot_shx Ev 740 32 14 e SB E740 E32v ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) R21;
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (SB + (e + 13) / 8)) (denot_shx Ev 740 32 13 e SB E740 E32v ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) R27;
rregU HS (26%bv : bv 5) (Z.of_nat (length acc))
ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom Ev 784 o2 E784), (U_atom Ev 793 o1 E793) by lia; rewrite zcanon_id by (unfold M64; lia); lia) R26 end.
ra_join HS ss_tjK 820%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 820%nat 12%nat R21 E832.
ra_join_val HS 820%nat 13%nat R26 E833.
ra_join_val HS 820%nat 14%nat R27 E834.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (FK (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k _ _ Wg msF mdF) end end.
-- exact HBASE.
-- unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia].
-- exact HJ2.
-- rewrite HfrS2. exact HFR.
-- unfold INV_tjK, tj_lbody, tj_wrote, tj_e, tj_age, tj_after2, tj_F. cbn [c_ly c_S c_cap c_T c_now c_buf c_t c_fpos].
rewrite !ew_havoc_old by (cbn; lia).
split; [nia|].
split; [split; [eapply Permutation_trans; [exact HPerm2 | exact Hperm]|]; split; [eapply tj_keep_journal; eassumption|];
split; [exact Hcap3|]; split; [exact Hi|]; repeat (split; [assumption|]); assumption|].
split; [exact E834|]. split; [exact E832|].
split.
{ exists (bn_TK (bn_NM fam [] din dout)).
split.
{ unfold model_of. replace (e_has_decl (reac_disco_table_json_c.tj_entry T i)) with hd by reflexivity.
rewrite (proj2 (Z.eqb_neq hd 0) Hc0).
replace (e_family (reac_disco_table_json_c.tj_entry T i)) with fam by reflexivity.
replace (e_decl_in (reac_disco_table_json_c.tj_entry T i)) with din by reflexivity.
replace (e_decl_out (reac_disco_table_json_c.tj_entry T i)) with dout by reflexivity.
unfold reac_disco_table_json_c.box_tok. rewrite Hret. reflexivity. }
fold F. split; [|split; [apply TKra; lia | apply TKhv; lia]].
eapply garr8_aview_kept; [|exact Gtk]. intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply HKFt. lia. }
exists acc. split; [exact E833|]. split; [exact Hacc|]. split; [exact Htxt|].
assert (HLacc : Z.of_nat (length (acc ++ [0])) <= cap) by (rewrite length_app; cbn [length]; lia).
eapply garr8_aview_kept; [|exact Hgarr].
intros a Ha. rewrite HKB5, HKB4 by lia.
replace a with (buf + (a - buf)) by lia.
rewrite (K2 buf Nb (a - buf) Hinb ltac:(lia) ltac:(intros HW; apply tjb_rbn_wr_rng in HW; unfold boxed in Hbsep; lia)).
replace (buf + (a - buf)) with a by lia. rewrite HKB3, HKB2, HKB1 by lia. reflexivity.
-- exact HS.
* exfalso.
lazymatch type of RF with ew ?Ex ?n = _ =>
rewrite branch_eq_U, (U_atom Ex n 0 RF), U_lit in Hc by lia end. discriminate Hc.
+
assert (Hret : disco_box_name_model.bn_ret fam [] din dout <> 0).
{ intros Hr. pose proof (tj_lemmas.tj_accept fam din dout (F + 32) (F + 96) (F + 160) Hr ltac:(lia) ltac:(lia) ltac:(lia)) as Ht.
rewrite Ht in Eacc. discriminate Eacc. }
hei_havoc HS; paj_run_shc RUNP RUNC HS HJ2. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict (w_H _) ?m0) (mrestrict _ ?m1) =>
assert (HKB4 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W2) m1 a = aview SEGS (w_H W2) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]);
assert (HKF4 : forall a, F <= a < F + 256 \/ SB + F / 8 <= a < SB + F / 8 + 32 -> aview SEGS (w_H W2) m1 a = aview SEGS (w_H W2) m0 a)
by (intros a Ha; unfold SB in Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
* exfalso.
lazymatch type of RF with ew ?Ex ?n = _ =>
assert (RF' : ew Ex n = Z_to_bv 64 (2 ^ 64 - 1)) by (rewrite RF; apply bv_eq; reflexivity);
rewrite branch_eq_U, (U_atom Ex n (2 ^ 64 - 1) RF'), U_lit in Hc by lia end. discriminate Hc.
*
hei_havoc HS; paj_run_to_shc RUNTOP HS HJ2 24368. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict (w_H _) ?m0) (mrestrict _ ?m1) =>
assert (HKB5 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W2) m1 a = aview SEGS (w_H W2) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]);
assert (HKF5 : forall a, F <= a < F + 256 \/ SB + F / 8 <= a < SB + F / 8 + 32 -> aview SEGS (w_H W2) m1 a = aview SEGS (w_H W2) m0 a)
by (intros a Ha; unfold SB in Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
pose proof (proj1 HJ2) as HARf.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARf Hfin2) as (_ & _ & HFPf & HFSf).
rewrite EFA2 in HFPf, HFSf. fold F in HFPf, HFSf. change (fs_frame_bytes 2 / 8) with 32 in HFSf. change (fs_frame_bytes 2) with 256 in HFPf.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
assert (HKFt : forall a, F <= a < F + 256 \/ SB + F / 8 <= a < SB + F / 8 + 32 -> aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha; rewrite HKF5, HKF4 by exact Ha; reflexivity) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E516, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFPf (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 248 8 _ FLv);
[ cbn [sv_denot]; rewrite E528, Z.add_0_r; reflexivity
| cbn; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 FLg)) as Hfl; change (bv_modulus 64) with (2 ^ 64) in Hfl; unfold FLv; lia
| cbn; lia
| eapply val_mem_aview_kept_x; [|exact VFL2]; intros x Hx; cbn in Hx; apply HKFt; lia ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi' Hob241 Hob242 Hob307 Hob308 Huar;
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 529%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSf; rewrite <- SB_SHADOW_OFF in HFSf; apply (proj1 (HFSf o ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi' Hob241 Hob242 Hob307 Hob308 Huar HFhU;
unfold boxed in *; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rregU HS (26%bv : bv 5) (Z.of_nat (length acc))
ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom Ev 784 o2 E784), (U_atom Ev 793 o1 E793) by lia; rewrite zcanon_id by (unfold M64; lia); lia) R26 end.
ra_join HS ss_tjU 800%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 800%nat 13%nat R26 E813.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (FU (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k _ _ Wg msF mdF) end end.
-- exact HBASE.
-- unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia].
-- exact HJ2.
-- rewrite HfrS2. exact HFR.
-- unfold INV_tjU, tj_lbody, tj_wrote, tj_e, tj_age, tj_after2. cbn [c_ly c_S c_cap c_T c_now c_buf c_t].
rewrite !ew_havoc_old by (cbn; lia).
split; [nia|].
split; [split; [eapply Permutation_trans; [exact HPerm2 | exact Hperm]|]; split; [eapply tj_keep_journal; eassumption|];
split; [exact Hcap3|]; split; [exact Hi|]; repeat (split; [assumption|]); assumption|].
split.
{ unfold model_of. replace (e_has_decl (reac_disco_table_json_c.tj_entry T i)) with hd by reflexivity.
rewrite (proj2 (Z.eqb_neq hd 0) Hc0).
replace (e_family (reac_disco_table_json_c.tj_entry T i)) with fam by reflexivity.
replace (e_decl_in (reac_disco_table_json_c.tj_entry T i)) with din by reflexivity.
replace (e_decl_out (reac_disco_table_json_c.tj_entry T i)) with dout by reflexivity.
unfold reac_disco_table_json_c.box_tok. rewrite (proj2 (Z.eqb_neq _ 0) Hret). reflexivity. }
exists acc. split; [exact E813|]. split; [exact Hacc|]. split; [exact Htxt|].
assert (HLacc : Z.of_nat (length (acc ++ [0])) <= cap) by (rewrite length_app; cbn [length]; lia).
eapply garr8_aview_kept; [|exact Hgarr].
intros a Ha. rewrite HKB5, HKB4 by lia.
replace a with (buf + (a - buf)) by lia.
rewrite (K2 buf Nb (a - buf) Hinb ltac:(lia) ltac:(intros HW; apply tjb_rbn_wr_rng in HW; unfold boxed in Hbsep; lia)).
replace (buf + (a - buf)) with a by lia. rewrite HKB3, HKB2, HKB1 by lia. reflexivity.
-- exact HS.
Qed.
End h.
End f.
End d.
