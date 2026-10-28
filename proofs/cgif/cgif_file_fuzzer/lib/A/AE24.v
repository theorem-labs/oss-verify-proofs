(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI00 YI16 YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0p.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE2y AE3i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2h AE2f AE2e AE2d AE29 AE28 AE27.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbq YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition TFIB_RELRO_LO : Z := 0x9da38.
Definition TFIB_RELRO_HI : Z := 0x9eca8.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ffc_ro_chunks_unowned :
forallb (fun c => forallb (fun r => (fst r + snd r <=? YP09.c_off c) || (YP09.c_off c + c_len c <=? fst r)) Tfib_owned_static) img_ro_chunks = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ffc_ro_img_of_arodata : forall (B : asyms) (H : word -> bool) m (rlo rhi : Z), TfibSyms B ->
arodata_okS tfibsegs B rlo rhi (aview tfibsegs H m) -> ro_img (mrestrict H m).
Proof.
intros B H m rlo rhi TB HRO E. unfold img_ro_region.
split; [cbn; unfold IMG_RO_LO; lia|]. split; [cbn; unfold IMG_RO_HI; lia|]. split; [intros o Ho; cbn in Ho; lia|].
cbn [YP09.r_chunks YP09.r_base base_val]. apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & n & Hv).
pose proof (proj1 (forallb_forall _ _) ffc_ro_chunks_unowned c Hc) as Hown. cbn beta in Hown.
pose proof (proj1 (forallb_forall _ _) img_ro_bytes_ok c Hc) as Hz. cbn beta in Hz.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Hv. subst cv. cbn [YP09.c_off YP09.c_val c_len cv_len] in *. rewrite !Z.add_0_l.
pose proof (zallb_sound _ _ _ (co + i) Hz ltac:(lia)) as Hb.
unfold img_byte_ok, img_byte in Hb.
assert (Hro : (exists s, In s tfibsegs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= co + i < Z.of_N (seg_base s) + Z.of_N (seg_size s)) \/ (rlo <= co + i < rhi)).
{ left. exists Asan.Asan_segment_000. split; [left; reflexivity|]. split; [reflexivity|]. cbn. unfold IMG_RO_LO, IMG_RO_HI in *. lia. }
assert (Hns : ~ Exists (in_zr (co + i)) (as_owned_static B)).
{ rewrite (ts_owned B TB). intros HX. apply Exists_exists in HX as (r & Hr & [Hin1 Hin2]). rewrite forallb_forall in Hown.
specialize (Hown r Hr). cbn beta in Hown. apply Bool.orb_prop in Hown. destruct Hown as [Ho|Ho]; apply Z.leb_le in Ho; lia. }
assert (Hne : ~ (as_errno B <= co + i < as_errno B + 4)) by (rewrite (ts_errno B TB); unfold TFIB_ERRNO; unfold IMG_RO_LO, IMG_RO_HI in *; lia).
pose proof (HRO (co + i) Hro Hns Hne) as Hrd. unfold aview in Hrd.
destruct (seg_rom tfibsegs (Z_to_bv 64 (co + i))) as [b|] eqn:Eb; [|discriminate Hb].
exists b. split; [cbn [cbyte]; unfold img_byte; exact Eb|].
destruct (mbyte tfibsegs (mrestrict H m) (co + i)) as [b'|] eqn:Em; [|discriminate Hrd]. cbn in Hrd. injection Hrd as Hrd.
f_equal. apply bv_eq. exact Hrd.
Qed.
Lemma fd_lookup_remove_same : forall fds (fd : word), fd_lookup (fd_remove fds fd) fd = None.
Proof.
intros fds fd. unfold fd_remove. induction fds as [|[k e] r IH]; [reflexivity|]. cbn [List.filter fst].
destruct (bv_eqb k fd) eqn:Ek; cbn [negb]; [exact IH|]. cbn [fd_lookup]. rewrite Ek. exact IH.
Qed.
Section S.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
Hypothesis ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes tfibsegs B.
Lemma ffc_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. intros a Ha. pose proof (ffa_img_range a Ha). unfold kLowMemEnd. lia. Qed.
Theorem tfib_afclose_spec : afclose_spec tfibsegs B tfib_K IC_ENTRY FC_FREE1_RA FC_JOIN TFIB_RELRO_LO TFIB_RELRO_HI.
Proof.
intros W ly S regs mem md ch f M Sg rest HPRE G10 Hperm HSINK HMI HRO Hev Hu1 Hu2.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HSINK as (fd & Wb & P & ESg & Hok & Hmax & Henv & Hfile & Hhead & Hfnz & Hfs & Hfd & Huniq).
pose proof HMI as (HX & HMimg & HMptr & HMmem & HM0 & HM47 & HMal & HMZ).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (FB : FILE_BLOCK = 1264) by reflexivity. assert (FS : AFCLOSE_STK = 16528) by reflexivity. assert (FW : FCL_WIN = 400) by reflexivity.
assert (FT : FCL_T = 144) by reflexivity. assert (HAS : AMETA_SIZE = 3727360) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
assert (HO : A_ofl_head = 0x5f9688) by reflexivity.
rewrite FS in Hslo, Hpres, Hstk0, Hbot.
set (sp0 := spZ regs) in *.
assert (Hblk : In (f, FILE_BLOCK) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md f FILE_BLOCK HAR Hblk) as (Hf16 & Hf0 & Hfceil & Hfapp & Hfbytes & Hfdisj & Hfrange).
assert (RQ : req_size FILE_BLOCK = FILE_BLOCK) by reflexivity. rewrite RQ in *.
pose proof (ffa_blk_off_img B ly S W mem md f FILE_BLOCK HAR Hblk) as HBimg. rewrite RQ in HBimg.
assert (HBam : amem_range f FILE_BLOCK).
{ clear - Hfapp Hf0 C1. unfold in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
assert (Hfhi : f + FILE_BLOCK <= 2 ^ 47) by (clear - Hfceil C1; lia).
pose proof Hfile as [HST HWIN]. pose proof HST as (Hfdr & _).
pose proof (astdio_env_canary tfibsegs tfib_K _ Henv) as (cval & Hcv & Hcan2).
pose proof (acan_got_of_AR tfibsegs B tfib_K AIL ly S W mem md HAR) as Hcan1.
assert (HBstk : f + FILE_BLOCK <= sp0 - FCL_WIN \/ sp0 <= f) by (left; rewrite FW; clear - Hfceil Hceil Hslo; lia).
assert (HSmax' : Z.of_nat (length Wb) + Z.of_nat (length P) <= SINK_MAX) by (rewrite ESg, length_app, Nat2Z.inj_add in Hmax; lia).
assert (XIN : forall a, M <= a < M + AMETA_SIZE -> Exists (in_zr a) (ly_extra ly)).
{ intros a Ha. apply Exists_exists. exists (M, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia]. }
assert (HBmeta : f + FILE_BLOCK <= M \/ M + AMETA_SIZE <= f).
{ destruct (Z_lt_le_dec f M) as [L|L].
- left. destruct (Z_lt_le_dec M (f + FILE_BLOCK)) as [L2|L2]; [exfalso | lia].
destruct (AR_extra_law_ok tfibsegs B ly S W mem md M HAR (XIN M ltac:(rewrite HAS; lia))) as (_ & Xb & _). exact (Xb f FILE_BLOCK Hblk ltac:(rewrite RQ; lia)).
- right. destruct (Z_lt_le_dec f (M + AMETA_SIZE)) as [L2|L2]; [exfalso | lia].
destruct (AR_extra_law_ok tfibsegs B ly S W mem md f HAR (XIN f ltac:(lia))) as (_ & Xb & _). exact (Xb f FILE_BLOCK Hblk ltac:(rewrite RQ; lia)). }
assert (HMlo : TFIB_IMG_END <= M).
{ assert (Hin : in_img tfibsegs (0x5fb000 - 1)).
{ exists Asan.Asan_segment_003. split; [do 3 right; left; reflexivity | cbn; lia]. }
pose proof (HMimg _ Hin) as HM1. unfold TFIB_IMG_END. clear - HM1 HMal. lia. }
assert (HMhi : M + AMETA_SIZE <= sp0 - FCL_WIN).
{ pose proof (lo_extra ly HLY) as (_ & HEX & _). pose proof (proj1 (Forall_forall _ _) HEX _ HX) as (_ & _ & _ & HMc & _). cbn [fst snd] in HMc.
pose proof (lo_stk_ceil ly HLY) as Hsc. rewrite FW. clear - HMc Hsc Hslo. lia. }
assert (I1 : val_mem tfibsegs (mrestrict (w_H W) mem) FF_got_fflush 8 FF_real_fflush).
{ apply (icell_of_AR tfibsegs B tfib_K AIL ly S W mem md _ _ HAR); [cbn; left; reflexivity | unfold FF_real_fflush; lia]. }
assert (I2 : val_mem tfibsegs (mrestrict (w_H W) mem) FF_got_fclose 8 FF_real_fclose).
{ apply (icell_of_AR tfibsegs B tfib_K AIL ly S W mem md _ _ HAR); [cbn; right; left; reflexivity | unfold FF_real_fclose; lia]. }
assert (I6 : val_mem tfibsegs (mrestrict (w_H W) mem) FF_mask 8 FF_mask_val).
{ apply (icell_of_AR tfibsegs B tfib_K AIL ly S W mem md _ _ HAR); [cbn; do 5 right; left; reflexivity | unfold FF_mask_val; lia]. }
pose proof (ameta_ptr_of_AR tfibsegs B tfib_K AIL ly S W mem md HAR) as IP.
assert (HCELLS : cells_hold (mrestrict (w_H W) mem) ic_cells).
{ unfold cells_hold, ic_cells, AE2e.A_META_PTR, AE2e.A_META_MEM.
repeat (apply Forall_cons; [cbn [fst snd]; split; [lia|]; split; [lia|];
repeat (apply Forall_cons; [cbn [fst snd]; split; [| cbn; lia] |]); try apply Forall_nil |]); try apply Forall_nil.
- rewrite Z.add_0_r. exact I1.
- exact I2.
- rewrite Z.add_0_r. exact IP.
- rewrite Z.add_0_r. exact I6. }
assert (HIMG : ro_img (mrestrict (w_H W) mem)) by (exact (ffc_ro_img_of_arodata B (w_H W) mem _ _ TB HRO)).
pose proof Henv as (Ethr & Enl & Elock & Epath & Emode & Erwa & Etrl & _).
assert (HOFLown : forall a, A_ofl_head <= a < A_ofl_head + 8 -> ~ aowned B ly S a).
{ intros a Ha Hown. rewrite HO in Ha.
destruct (ail_env _ _ _ AIL a ltac:(unfold aenv_addr; cbn [ak_threaded ak_need_locks ak_ofl_lock ak_path ak_mode ak_rwa ak_trailer ak_canary tfib_K]; unfold A_ofl_lock; lia)) as (Hi & Hns & _).
apply Hns. exact (proj1 (al_owned_image _ _ LAWS ly S W mem md a HAR Hi) Hown). }
unfold cfg_at. change (Z_to_bv 64 IC_ENTRY) with (w64 IC_ENTRY).
eapply SRr_bind.
{ apply (fclose_L1 B LAWS TB ly S W regs mem md f fd cval M P Wb HAR Hal16); rewrite ?FW.
- lia.
- exact Hshi.
- intros a Ha. apply Hpres. lia.
- exact G10.
- exact Hfile.
- exact Hf0.
- exact Hfhi.
- exact Hf16.
- exact Hfbytes.
- exact HBstk.
- exact HBimg.
- exact HBam.
- exact HBmeta.
- exact Hcan1.
- exact Hcan2.
- exact Hcv.
- exact HCELLS.
- exact HIMG.
- exact Enl.
- exact Elock.
- exact Hhead.
- exact HOFLown.
- exact HMmem.
- exact HMZ.
- exact HMlo.
- exact HMal.
- rewrite <- FW. exact HMhi.
- exact Hfd.
- exact Hfs.
- exact HSmax'. }
cbv beta. intros W1 c1 _ (-> & regsT & memT & mdT & v9 & v18 & mdw & -> & HART & T10 & T1 & T2 & T8 & T9 & T18 & TK & TV & TL & TOK & TFS & TSO & TFD & TOTH & Hv9 & Hv18 &
C40 & C32 & C24 & C16 & C8 & CS & Hmdw & THDR & TOFL & TAV & TPRS & TPM).
fold sp0 in T2, C40, C32, C24, C16, C8, CS, TAV, TPRS. rewrite FT in T2, C40, C32, C24, C16, C8. rewrite FW in TAV, TPRS.
assert (OFLimg : forall a, 0x5f9688 <= a < 0x5f9688 + 8 -> in_img tfibsegs a).
{ intros a Ha. exact (proj1 (ail_env _ _ _ AIL a ltac:(unfold aenv_addr; cbn [ak_threaded ak_need_locks ak_ofl_lock ak_path ak_mode ak_rwa ak_trailer ak_canary tfib_K]; unfold A_ofl_lock; lia))). }
unfold oflW in TAV, TPM. rewrite HO in TAV, TPM, TOFL.
assert (J1 : ajournal tfibsegs B AFCLOSE_STK sp0 (asink_fp f) ly S W mem md [] ly S W memT mdT 0).
{ split; [exact HART|]. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|].
split.
{
pose proof TOK as (Oio & Opipes & Oproc).
split; [exact Oio|]. split; [exact Opipes|].
split.
{ intros fd0. rewrite TFD. destruct (bv_eq_dec _ fd0 (Z_to_bv 64 fd)) as [->|Hne].
- right. split; [right; eexists; exact Hfd | left; apply fd_lookup_remove_same].
- left. apply fd_lookup_remove_neq. exact Hne. }
split; [intros q Hq; exact (TOTH q Hq)|]. split; [exact TSO|]. split; [exact Oproc|].
intros Hc. exfalso. exact (Hc (asink_fp_open f)). }
split; [reflexivity|]. split; [lia|]. split; [lia|].
split.
{   intros a Ha Hs. rewrite FS in Hs. apply TAV; [clear - Ha C1; lia | clear - Ha Hs; lia | clear - Ha Hfceil FB; lia | clear - Ha C1; lia]. }
split.
{   intros p0 n0 i Hin _ Hi Hnf.
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin) as (_ & Hq0 & Hq0c & _).
apply TAV; [clear - Hq0 Hq0c Hi C1; lia | clear - Hq0c Hi Hceil Hslo; lia | |].
- intros Hr. apply Hnf. apply (proj2 (in_asink_fp f (p0 + i))). left. rewrite FB. lia.
- intros Hr. exact (blk_img tfibsegs B LAWS ly S W mem md p0 n0 (p0 + i) HAR Hin ltac:(lia) (OFLimg _ Hr)). }
split.
{   intros a Hi Hns He Hsp. pose proof (ffa_img_range a Hi) as Ra.
apply TAV; [lia | clear - Ra Hslo Hceil C1; lia | | ].
- intros Hr. exact (blk_img tfibsegs B LAWS ly S W mem md f FILE_BLOCK a HAR Hblk ltac:(rewrite RQ; lia) Hi).
- intros Hr. apply (Hsp (asink_fp_open f)). unfold AOFL_HEAD. cbn. lia. }
split.
{   intros cid pos a Hin Hr Hnf.
destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (Hf0' & Hfc & Hfapp').
pose proof (sep_block_frame tfibsegs B LAWS ly S W mem md f FILE_BLOCK cid pos HAR Hblk Hin) as Hd. rewrite RQ in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (fs_frame_bytes_nonneg cid) as Hnn. unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
destruct Hr as [Hr | Hr].
- apply TAV; [clear - Hr Hf0' Hfc C1; lia | clear - Hr Hfc Hceil Hslo; lia | clear - Hr Hd FB; lia |].
intros Ho. exact (frm_img tfibsegs B LAWS ly S W mem md cid pos a HAR Hin ltac:(lia) (OFLimg _ Ho)).
- pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [B1 B2].
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as Hse.
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [U1 U2].
apply TAV; [clear - Hr B1 U2 Hse; unfold kLowMemEnd, kHighShadowEnd in *; lia | clear - Hr B1 U2 Hse Lbeg Hslo; unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *; lia | |].
+ clear - Hr B1 U2 Hse HBam Hfhi FB. unfold amem_range, kLowMemEnd, kHighShadowEnd, kHighMemBeg, kHighMemEnd in *. rewrite FB in *. lia.
+ clear - Hr B1 U2 Hse. unfold kLowMemEnd, kHighShadowEnd in *. lia. }
split; [intros p0 n0 i H1 H2; exfalso; exact (H2 H1)|].
split; [intros a Ha; rewrite FS in Ha; apply TPM; [clear - Ha Hslo Hceil C1 Hshi H47; lia | clear - Ha Hslo Hceil C1; lia | apply Hpres; exact Ha]|].
split; [exact Hstk|].
split.
{   intros a HXa He. destruct (AR_extra_law_ok tfibsegs B ly S W mem md a HAR HXa) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
apply TAV; [clear - Xapp C1; unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; lia | | |].
- intros Hs. apply Xs. clear - Hs Hslo Hshi. lia.
- intros Hr. exact (Xb f FILE_BLOCK Hblk ltac:(rewrite RQ; lia)).
- intros Ho. exact (Xi (OFLimg _ Ho)). }
exact HQT. }
assert (RTsp : spZ regsT = sp0 + -144) by (unfold spZ; rewrite T2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (RTgp : getr regsT 3 = w64 (as_gp B)) by (etransitivity; [exact (TK 3 ltac:(unfold KEPT7; cbn; tauto)) | exact Hgp]).
assert (RTtp : getr regsT 4 = w64 (as_tp B)) by (etransitivity; [exact (TK 4 ltac:(unfold KEPT7; cbn; tauto)) | exact Htp]).
pose proof (ts_code B TB) as TC.
assert (CHT : chain_pre ly (aview tfibsegs (w_H W) memT) regsT []).
{ unfold chain_pre. split; [unfold raZ; rewrite T1; unfold w64; rewrite unsigned_lit_small; unfold FC_FREE1_RA; lia|].
destruct (frame0_ok ly regsT); [|reflexivity].
assert (Hbad : bad_next (spZ regsT) (ly_top ly) (s0Z regsT) = true).
{ unfold bad_next, s0Z. rewrite T8, RTsp. unfold w64; rewrite unsigned_lit_small by lia.
destruct (Z.leb_spec f (sp0 + -144)) as [L|L]; [reflexivity | exfalso; clear - L Hfceil Hceil Hslo FB; lia]. }
rewrite Hbad. reflexivity. }
assert (TRT : In (call_trace0 (pc_free_ra0 (as_code B)) regsT []) (as_universe B)).
{ unfold call_trace0, unwind_of_chain. unfold raZ. rewrite T1. unfold w64. rewrite unsigned_lit_small by (unfold FC_FREE1_RA; lia).
rewrite TC in *. cbn. exact Hu1. }
unfold cfg_at. replace (w64 PC_FREE) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite TC; reflexivity).
eapply SRr_bind.
{ apply (aj_free_null_at_io tfibsegs B LAWS ffc_segs_low ENV ML AFREE W regsT memT AFCLOSE_STK sp0 (asink_fp f) ly S W mem md [] ly S mdT 0 (-144) (w64 FC_FREE1_RA) [] J1 T10 RTsp).
- reflexivity.
- lia.
- rewrite FS, Has. lia.
- exact RTgp.
- exact RTtp.
- exact T1.
- apply AE2y.ret_ok_lit; [unfold FC_FREE1_RA; lia | reflexivity].
- lia.
- exact CHT.
- exact TRT. }
cbv beta. intros W2 c2 Hwle2 (ly1 & S1 & regs1 & mem1 & md1 & -> & J2 & AP1 & Hperm1 & Hfr1 & AK1 & IO1).
assert (E18 : getr regs1 8 = getr regsT 8) by exact (AP1 8 ltac:(unfold acallee_saved; lia)).
eapply SRr_bind.
{ apply (fclose_L2 W2 regs1 mem1 md1 f); [rewrite E18; exact T8 | lia]. }
cbv beta. intros W3 c3 _ (-> & regs2 & md2 & -> & MF2 & U10 & U1 & UK).
assert (J2' : ajournal tfibsegs B AFCLOSE_STK sp0 (asink_fp f) ly S W mem md [] ly1 S1 W2 mem1 md2 (0 + 1)).
{ eapply (ajournal_exec tfibsegs B LAWS ffc_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem1 md2 (fun _ => False) J2);
[intros; reflexivity | apply mem_grows_refl | intros; reflexivity | exact MF2 | intros a Ha; destruct Ha]. }
assert (E22 : getr regs2 2 = getr regsT 2).
{ etransitivity; [exact (UK 2 ltac:(unfold KEPTL2; cbn; tauto)) | exact (AP1 2 ltac:(unfold acallee_saved; lia))]. }
assert (E28 : getr regs2 8 = w64 f).
{ etransitivity; [exact (UK 8 ltac:(unfold KEPTL2; cbn; tauto)) |]. etransitivity; [exact E18 | exact T8]. }
assert (R2sp : spZ regs2 = sp0 + -144) by (unfold spZ; rewrite E22; exact RTsp).
assert (R2gp : getr regs2 3 = w64 (as_gp B)).
{ etransitivity; [exact (UK 3 ltac:(unfold KEPTL2; cbn; tauto)) |]. etransitivity; [exact (AP1 3 ltac:(unfold acallee_saved; lia)) | exact RTgp]. }
assert (R2tp : getr regs2 4 = w64 (as_tp B)).
{ etransitivity; [exact (UK 4 ltac:(unfold KEPTL2; cbn; tauto)) |]. etransitivity; [exact (AP1 4 ltac:(unfold acallee_saved; lia)) | exact RTtp]. }
pose proof J2' as (_ & Hly1 & _ & _ & _ & _ & Hnev1 & _).
assert (CH2 : chain_pre ly1 (aview tfibsegs (w_H W2) mem1) regs2 []).
{ unfold chain_pre. split; [unfold raZ; rewrite U1; unfold w64; rewrite unsigned_lit_small; unfold FC_JOIN; lia|].
destruct (frame0_ok ly1 regs2); [|reflexivity].
assert (Hbad : bad_next (spZ regs2) (ly_top ly1) (s0Z regs2) = true).
{ unfold bad_next, s0Z. rewrite E28, R2sp. unfold w64; rewrite unsigned_lit_small by lia.
destruct (Z.leb_spec f (sp0 + -144)) as [L|L]; [reflexivity | exfalso; clear - L Hfceil Hceil Hslo FB; lia]. }
rewrite Hbad. reflexivity. }
assert (TR2 : In (call_trace0 (pc_free_ra0 (as_code B)) regs2 []) (as_universe B)).
{ unfold call_trace0, unwind_of_chain. unfold raZ. rewrite U1. unfold w64. rewrite unsigned_lit_small by (unfold FC_JOIN; lia).
rewrite TC in *. cbn. exact Hu2. }
assert (Hblk1 : In (f, FILE_BLOCK) (ablocks B ly1 S1)) by (apply (Permutation_in _ (Permutation_sym Hperm1)); exact Hblk).
unfold cfg_at. replace (w64 PC_FREE) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite TC; reflexivity).
eapply SRr_bind.
{ apply (aj_free_at_io tfibsegs B LAWS ffc_segs_low ENV ML AFREE W2 regs2 mem1 AFCLOSE_STK sp0 (asink_fp f) ly S W mem md [] ly1 S1 md2 (0 + 1) f FILE_BLOCK (-144) (w64 FC_JOIN) [] J2' Hblk1 U10 R2sp).
- reflexivity.
- lia.
- rewrite FS, Has. lia.
- exact R2gp.
- exact R2tp.
- exact U1.
- apply AE2y.ret_ok_lit; [unfold FC_JOIN; lia | reflexivity].
- lia.
- exact CH2.
- exact TR2.
- intros _ i Hi. apply (proj2 (in_asink_fp f (f + i))). left. rewrite RQ in Hi. lia. }
cbv beta. intros W4 c4 Hwle4 (ly2 & S2 & regs3 & mem3 & md3 & -> & J3 & AP3 & (l1 & l2 & Hspl & Habl2) & Hfr3 & AK3 & IO3).
assert (E38 : getr regs3 8 = w64 f) by (etransitivity; [exact (AP3 8 ltac:(unfold acallee_saved; lia)) | exact E28]).
assert (E39 : getr regs3 9 = w64 0).
{ etransitivity; [exact (AP3 9 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact (UK 9 ltac:(unfold KEPTL2; cbn; tauto))|].
etransitivity; [exact (AP1 9 ltac:(unfold acallee_saved; lia)) | exact T9]. }
assert (E318 : getr regs3 18 = w64 0).
{ etransitivity; [exact (AP3 18 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact (UK 18 ltac:(unfold KEPTL2; cbn; tauto))|].
etransitivity; [exact (AP1 18 ltac:(unfold acallee_saved; lia)) | exact T18]. }
assert (E32 : getr regs3 2 = getr regs2 2) by exact (AP3 2 ltac:(unfold acallee_saved; lia)).
assert (R3sp : spZ regs3 = sp0 + -144) by (unfold spZ; rewrite E32; exact R2sp).
assert (AVK : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + -144 - ASTACK <= a < sp0 + -144) ->
aview tfibsegs (w_H W4) mem3 a = aview tfibsegs (w_H W) memT a).
{ intros a Ha Hs. rewrite (proj1 AK3 a Ha Hs). exact (proj1 AK1 a Ha Hs). }
assert (IMK : forall a, in_img tfibsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview tfibsegs (w_H W4) mem3 a = aview tfibsegs (w_H W) memT a).
{ intros a Hi Hns He. rewrite (proj1 (proj2 (proj2 AK3)) a Hi Hns He). exact (proj1 (proj2 (proj2 AK1)) a Hi Hns He). }
assert (VT2 : forall (ma mb : word -> option byte) (Ha Hb : word -> bool) a (nn : nat) v, val_mem tfibsegs (mrestrict Ha ma) a nn v ->
(forall b, a <= b < a + Z.of_nat nn -> aview tfibsegs Hb mb b = aview tfibsegs Ha ma b) -> val_mem tfibsegs (mrestrict Hb mb) a nn v).
{ intros ma mb Ha Hb a nn v Hv Hf'. apply (AF0x.val_mem_ext (mrestrict Ha ma)); [|exact Hv]. intros j Hj. apply AE2y.mbyte_of_aview. apply Hf'. lia. }
assert (Heven : bv_unsigned (getr regs 1) mod 2 = 0).
{ pose proof (u64_range (getr regs 1)) as Hu. pose proof (f_equal bv_unsigned Hra) as E. unfold v_jalr, jalr_tgtZ in E.
rewrite Z.add_0_r, Z_to_bv_unsigned in E.
assert (Hld : Z.land (bv_unsigned (getr regs 1)) (-2) = Z.shiftl (Z.shiftr (bv_unsigned (getr regs 1)) 1) 1).
{ change (-2) with (Z.lnot (Z.ones 1)). rewrite <- Z.ldiff_land. apply Z.ldiff_ones_r. lia. }
rewrite Hld, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 in E by lia. change (2 ^ 1) with 2 in E.
unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
pose proof (Z.mul_div_le (bv_unsigned (getr regs 1)) 2 ltac:(lia)) as Hm1. assert (Hm2 : 0 <= bv_unsigned (getr regs 1) / 2) by (apply Z.div_pos; lia).
rewrite Z.mod_small in E by lia. rewrite <- E. apply Z_mod_mult. }
set (vra := bv_unsigned (getr regs 1)) in *.
set (c8 := bv_unsigned (getr regs (Z_to_bv 5 8))). set (c9 := bv_unsigned (getr regs (Z_to_bv 5 9))).
set (c18 := bv_unsigned (getr regs (Z_to_bv 5 18))). set (c19 := bv_unsigned (getr regs (Z_to_bv 5 19))).
pose proof (u64_range (getr regs (Z_to_bv 5 8))) as Hc8. pose proof (u64_range (getr regs (Z_to_bv 5 9))) as Hc9.
pose proof (u64_range (getr regs (Z_to_bv 5 18))) as Hc18. pose proof (u64_range (getr regs (Z_to_bv 5 19))) as Hc19. pose proof (u64_range (getr regs 1)) as Hvra.
unfold cfg_at.
eapply SRr_bind.
{ apply (fclose_L3 W4 regs3 mem3 md3 f v9 v18 vra c8 c9 c18 c19 E38 E39 E318); rewrite ?R3sp; try lia.
all: try (replace (sp0 + -144) with (sp0 + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16).
all: try (apply (VT2 memT mem3 (w_H W) (w_H W4)); [| intros b Hb; apply AVK; [clear - Hb Hceil Hslo C1 Hshi H47; lia | clear - Hb Has; lia]]).
- replace (sp0 + -144 + 40) with (sp0 - 144 + 40) by lia. exact C40.
- replace (sp0 + -144 + 32) with (sp0 - 144 + 32) by lia. exact C32.
- replace (sp0 + -144 + 24) with (sp0 - 144 + 24) by lia. exact C24.
- replace (sp0 + -144 + 16) with (sp0 - 144 + 16) by lia. exact C16.
- replace (sp0 + -144 + 8) with (sp0 - 144 + 8) by lia. exact C8.
- replace (sp0 + -144 + 136) with (sp0 + -8) by lia. exact (CS 0%nat 1 (-8) eq_refl).
- replace (sp0 + -144 + 128) with (sp0 + -16) by lia. exact (CS 1%nat 8 (-16) eq_refl).
- replace (sp0 + -144 + 120) with (sp0 + -24) by lia. exact (CS 2%nat 9 (-24) eq_refl).
- replace (sp0 + -144 + 112) with (sp0 + -32) by lia. exact (CS 3%nat 18 (-32) eq_refl).
- replace (sp0 + -144 + 104) with (sp0 + -40) by lia. exact (CS 4%nat 19 (-40) eq_refl). }
cbv beta. intros W5 c5 _ (-> & regs4 & md4 & -> & MF4 & V10 & V1 & V2 & V8 & V9 & V18 & V19 & VK).
Ltac KC := cbn [ak_threaded ak_need_locks ak_ofl_lock ak_path ak_mode ak_rwa ak_trailer ak_canary tfib_K length app YI16.sink_path_Z YI16.sink_mode_Z sink_rwa_Z sink_trailer_Z Z.of_nat Nat.add Pos.of_succ_nat Pos.succ] in *;
unfold A_threaded, A_need_locks, A_ofl_lock, A_PATH, A_WB, A_RWA, A_TRAILER, FF_canary in *.
assert (J4 : ajournal tfibsegs B AFCLOSE_STK sp0 (asink_fp f) ly S W mem md [] ly2 S2 W4 mem3 md4 2).
{ eapply (ajournal_exec tfibsegs B LAWS ffc_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3 md4 (fun _ => False) J3);
[intros; reflexivity | apply mem_grows_refl | intros; reflexivity | exact MF4 | intros a Ha; destruct Ha]. }
pose proof (same_but_materialized_frame md1 md2 MF2) as (_ & _ & _ & _ & _ & _ & _ & _ & FD12 & _ & _ & FS12 & _).
pose proof (same_but_materialized_frame md3 md4 MF4) as (_ & _ & _ & _ & _ & _ & _ & _ & FD34 & _ & _ & FS34 & _).
pose proof IO1 as (Ifd1 & _ & Ifs1 & _). pose proof IO3 as (Ifd3 & _ & Ifs3 & _).
assert (Efds : m_fds md4 = fd_remove (m_fds md) (Z_to_bv 64 fd)).
{ rewrite FD34. unfold m_fds. rewrite Ifd3. fold (m_fds md2). rewrite FD12. unfold m_fds. rewrite Ifd1. fold (m_fds mdT). exact TFD. }
assert (Efs : m_fs md4 = m_fs mdT).
{ rewrite FS34. unfold m_fs. rewrite Ifs3. fold (m_fs md2). rewrite FS12. unfold m_fs. rewrite Ifs1. reflexivity. }
assert (ENVK : forall a, aenv_addr tfib_K a -> ~ (0x5f9688 <= a < 0x5f9688 + 8) -> mbyte tfibsegs (mrestrict (w_H W4) mem3) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha Ho. destruct (ail_env _ _ _ AIL a Ha) as (Hi & Hns & He). pose proof (ffa_img_range a Hi) as Ra.
apply AE2y.mbyte_of_aview. rewrite (IMK a Hi Hns He). apply TAV; [lia | clear - Ra Hslo Hceil C1; lia | | exact Ho].
intros Hr. exact (blk_img tfibsegs B LAWS ly S W mem md f FILE_BLOCK a HAR Hblk ltac:(rewrite RQ; lia) Hi). }
apply SRr_ret. exists ly2, S2, regs4, mem3, md4.
split. { unfold vra, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [exact J4|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ In r KEPT7) by (unfold KEPT7; cbn [In]; lia).
destruct Hc as [-> | [-> | [-> | [-> | [-> | Hk]]]]].
- etransitivity; [exact V2|]. rewrite R3sp. replace (sp0 + -144 + 144) with sp0 by lia. unfold sp0, spZ, w64. apply Z_to_bv_bv_unsigned.
- etransitivity; [exact V8|]. unfold c8, w64. apply Z_to_bv_bv_unsigned.
- etransitivity; [exact V9|]. unfold c9, w64. apply Z_to_bv_bv_unsigned.
- etransitivity; [exact V18|]. unfold c18, w64. apply Z_to_bv_bv_unsigned.
- etransitivity; [exact V19|]. unfold c19, w64. apply Z_to_bv_bv_unsigned.
- assert (Hr32 : 0 <= r < 32) by (unfold KEPT7 in Hk; cbn in Hk; lia). pose proof Hk as Hk7. unfold KEPT7 in Hk. cbn [In] in Hk.
etransitivity; [exact (VK r Hk7)|]. etransitivity; [exact (AP3 r ltac:(unfold acallee_saved; lia))|].
etransitivity; [exact (UK r ltac:(unfold KEPTL2; cbn [In]; lia))|]. etransitivity; [exact (AP1 r ltac:(unfold acallee_saved; lia))|].
exact (TK r Hk7). }
split; [exact V10|].
split.
{ rewrite Habl2. apply Permutation_sym. apply (Permutation_cons_app_inv _ _ (a := (f, FILE_BLOCK))). rewrite <- Hspl.
apply (Permutation_trans (Permutation_sym Hperm)). apply Permutation_sym. exact Hperm1. }
split; [rewrite Hfr3; exact Hfr1|].
split.
{
split.
{ pose proof Henv as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & (cv & Xcv & X8)). unfold astdio_env.
assert (NOF : forall a, a = ak_threaded tfib_K \/ a = ak_need_locks tfib_K \/ (ak_ofl_lock tfib_K <= a < ak_ofl_lock tfib_K + 4) \/
(ak_path tfib_K <= a < ak_path tfib_K + 13) \/ (ak_mode tfib_K <= a < ak_mode tfib_K + 3) \/ (ak_rwa tfib_K <= a < ak_rwa tfib_K + 4) \/
(ak_trailer tfib_K <= a < ak_trailer tfib_K + 2) \/ (ak_canary tfib_K <= a < ak_canary tfib_K + 8) ->
mbyte tfibsegs (mrestrict (w_H W4) mem3) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
{ intros a Ha. apply ENVK.
- unfold aenv_addr. clear - Ha. lia.
- pose proof (ail_env_static _ _ _ AIL a Ha) as Hno. unfold AOFL_HEAD in Hno. cbn in Hno. exact Hno. }
assert (LP : length sink_path_Z = 12%nat) by reflexivity.
split; [eapply val_mem_frame; [|exact X1]; intros x Hx; apply NOF; KC; lia|].
split; [eapply val_mem_frame; [|exact X2]; intros x Hx; apply NOF; KC; lia|].
split; [eapply val_mem_frame; [|exact X3]; intros x Hx; apply NOF; KC; lia|].
split; [eapply garr8_frame; [exact X4|]; intros x Hx; apply NOF; KC; lia|].
split; [eapply garr8_frame; [exact X5|]; intros x Hx; apply NOF; KC; lia|].
split; [eapply garr8_frame; [exact X6|]; intros x Hx; apply NOF; KC; lia|].
split; [eapply garr8_frame; [exact X7|]; intros x Hx; apply NOF; KC; lia|].
exists cv. split; [exact Xcv|]. eapply val_mem_frame; [|exact X8]; intros x Hx; apply NOF; KC; lia. }
split.
{ apply (VT2 memT mem3 (w_H W) (w_H W4)); [exact TOFL|]. intros b Hb. unfold ak_ofl_head in Hb. cbn [ak_ofl_lock tfib_K Z.of_nat Pos.of_succ_nat Pos.succ] in Hb. unfold A_ofl_lock in Hb.
destruct (ail_env _ _ _ AIL b ltac:(unfold aenv_addr; cbn [ak_threaded ak_need_locks ak_ofl_lock ak_path ak_mode ak_rwa ak_trailer ak_canary tfib_K]; unfold A_ofl_lock; lia)) as (Hi & Hns & He).
exact (IMK b Hi Hns He). }
rewrite Efds. exact Huniq. }
rewrite Efs, ESg. exact TFS.
Qed.
End S.
End d.
