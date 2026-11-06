(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg2.v, with its module paths and module names changed; 415 of its 482 lines of code are new or changed and 696 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/SbDecSeg2.v; 152 of its 342 lines of code are new or changed and 292 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec SbDecLib SbDecCut SbDecLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma sbd3_lsd_len : forall v, (1 <= length (sb_dec_c.sb_dec_lsd v 3) <= 3)%nat.
Proof.
intros v. cbn [sb_dec_c.sb_dec_lsd].
destruct (v <? 10), (v / 10 <? 10), (v / 10 / 10 <? 10); cbn [length]; lia.
Qed.
Ltac sbd3_nin := cbn [In]; intros HH; repeat (destruct HH as [HH | HH]; [lia |]); exact HH.
Ltac sbd3_kp KP n rb :=
  rewrite (KP n rb ltac:(lia) ltac:(sbd3_nin) ltac:(apply bv_eq; vm_compute; reflexivity)).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis L1 : sbd_L1_spec B.
Lemma sbd3_fresh : forall lyc Sc lyc1 S2 W2 mem2 md2 cid pos slo shi (Er : Z -> Prop) a,
  AR SEGS B lyc1 S2 W2 mem2 md2 -> frames S2 = (cid, pos) :: frames Sc -> ablocks B lyc1 S2 = ablocks B lyc Sc ->
  (forall c p, frame_addr lyc1 c p = frame_addr lyc c p) -> 0 <= cid ->
  (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) ->
  sbd_wr B lyc Sc slo shi Er a.
Proof.
intros lyc Sc lyc1 S2 W2 mem2 md2 cid pos slo shi Er a HAR2 Hfrs2 Eab HFeq Hcid Ha.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR2 Hin2) as (HF4096 & HFc & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR2 Hin2) as (HFa & HFb & HF64).
rewrite HFeq in HF4096, HFc, HFapp, HFa.
pose proof asan_consts as (C1 & _).
set (F := frame_addr lyc cid pos) in *.
destruct (shadow_cell_bound F (fs_frame_bytes cid) ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2'].
split.
{ intros Himg. destruct Ha as [Ha | Ha].
  - assert (Ha' : frame_addr lyc1 cid pos <= a < frame_addr lyc1 cid pos + fs_frame_bytes cid)
      by (rewrite HFeq; exact Ha).
    apply (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR2
      (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin2 Ha'))))))). exact Himg.
  - pose proof (pa_segs_low a Himg). unfold kLowMemEnd, SHADOW_OFF in *. lia. }
right. right. split; [unfold in_app, SHADOW_OFF, kHighMemBeg in *; destruct Ha as [Ha | Ha]; lia|].
split.
- intros b m Hb Hr. rewrite <- Eab in Hb.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid pos HAR2 Hb Hin2) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & _ & _ & Hbapp & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFeq in Hd. fold F in Hd.
  destruct Ha as [Ha | Ha]; [lia|].
  apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia | unfold in_app in *; lia | exact Ha].
- intros cid' pos' Hin'.
  assert (Hin2' : In (cid', pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin').
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (_ & HGapp & _ & _).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (HG4096 & HGc & _).
  destruct (frame_al64 SEGS B _ _ _ _ _ cid' pos' HAR2 Hin2') as (HGa & HGb & HG64).
  rewrite HFeq in HGapp, HG4096, HGc, HGa.
  apply in_split in Hin' as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (cid, pos) (cid', pos') [] l2 l3 HAR2
    ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !HFeq in Hd. fold F in Hd.
  set (G := frame_addr lyc cid' pos') in *.
  unfold in_zr, frame_rng. cbn [fst snd]. fold G.
  destruct Ha as [Ha | Ha].
  + split; [lia|]. intros Hs.
    apply (app_not_shadow a G (fs_frame_bytes cid')); [lia | lia | lia | unfold in_app in *; lia | exact Hs].
  + split; [intros Hf; apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia | unfold in_app in *; lia | exact Ha]|].
    intros Hs. exact (shadow_disj F G _ _ HFa HGa HFb HGb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd a Ha Hs).
Qed.
Lemma sbd3_not_new : forall STK sp0 FP ly S own lyc Sc lyc1 S2 W2 mem2 md2 cid pos a,
  frames Sc = own ++ frames S -> alloc_ceiling <= sp0 - STK ->
  AR SEGS B lyc1 S2 W2 mem2 md2 -> frames S2 = (cid, pos) :: frames Sc -> ablocks B lyc1 S2 = ablocks B lyc Sc ->
  (forall c p, frame_addr lyc1 c p = frame_addr lyc c p) -> 0 <= cid ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid) /\
  ~ (shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8).
Proof.
intros STK sp0 FP ly S own lyc Sc lyc1 S2 W2 mem2 md2 cid pos a Hfrs Hc HAR2 Hfrs2 Eab HFeq Hcid Haw.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR2 Hin2) as (HF4096 & HFc & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR2 Hin2) as (HFa & HFb & HF64).
rewrite HFeq in HF4096, HFc, HFapp, HFa.
pose proof asan_consts as (C1 & _).
set (F := frame_addr lyc cid pos) in *.
destruct (shadow_cell_bound F (fs_frame_bytes cid) ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2'].
destruct Haw as [Hs | [[_ (b & m & Hb & Hr)] | [(b & m & Hb & _ & Hr) | (cid' & pos' & Hown & Hr)]]].
- unfold SHADOW_OFF, kHighMemBeg in *. split; lia.
- rewrite <- Eab in Hb. pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid pos HAR2 Hb Hin2) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & _ & _ & Hbapp & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFeq in Hd. fold F in Hd.
  split; [lia|].
  apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia |]. unfold in_app in *. lia.
- rewrite <- Eab in Hb. pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m cid pos HAR2 Hb Hin2) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & _ & _ & Hbapp & _).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFeq in Hd. fold F in Hd.
  split; [lia|].
  apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia |]. unfold in_app in *. lia.
- assert (Hin' : In (cid', pos') (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  assert (Hin2' : In (cid', pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin').
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (_ & HGapp & _ & _).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid' pos' HAR2 Hin2') as (HG4096 & HGc & _).
  destruct (frame_al64 SEGS B _ _ _ _ _ cid' pos' HAR2 Hin2') as (HGa & HGb & HG64).
  rewrite HFeq in HGapp, HG4096, HGc, HGa.
  apply in_split in Hin' as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (cid, pos) (cid', pos') [] l2 l3 HAR2
    ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !HFeq in Hd. fold F in Hd.
  set (G := frame_addr lyc cid' pos') in *.
  destruct Hr as [Hr | Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr.
  + split; [lia|].
    apply (app_not_shadow a F (fs_frame_bytes cid)); [lia | lia | lia |]. unfold in_app in *. lia.
  + pose proof (fs_frame_bytes_nonneg cid') as Hb'.
    split; [intros Hf; apply (app_not_shadow a G (fs_frame_bytes cid')); [lia | lia | lia | unfold in_app in *; lia | lia]|].
    intros Hs. exact (shadow_disj F G _ _ HFa HGa HFb HGb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hd a Hs Hr).
Qed.
Lemma sbd3_kept_step : forall lyc Sc (W : world SEGS) memc mem1 mem2 mdc slo shi Er (Wr : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc ->
  sbd_kept B lyc Sc W memc mem1 slo shi Er ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem1 a) ->
  (forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem2 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> Wr a -> sbd_wr B lyc Sc slo shi Er a) ->
  sbd_kept B lyc Sc W memc mem2 slo shi Er.
Proof.
intros lyc Sc W memc mem1 mem2 mdc slo shi Er Wr HAR (K1 & K2 & K3 & K4 & K5 & K6) EQ HP Hwr.
pose proof asan_consts as (C1 & _).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hs He. rewrite <- (K1 a Ha Hs He). apply EQ; [lia|]. intros Hw.
  destruct (Hwr a ltac:(lia) Hw) as (_ & [[_ Hs'] | [He' | [Hl _]]]); [exact (Hs Hs') | exact (He He') | lia].
- intros b m i Hin Hi He. rewrite <- (K2 b m i Hin Hi He).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hbc & _).
  apply EQ; [lia|]. intros Hw.
  destruct (Hwr (b + i) ltac:(lia) Hw) as (_ & [[Hc _] | [He' | [_ [Hnb _]]]]);
  [lia | exact (He He') | exact (Hnb b m Hin ltac:(lia))].
- intros a Himg Hno Herr. rewrite <- (K3 a Himg Hno Herr). pose proof (pa_segs_low a Himg) as Hlo.
  apply EQ; [unfold kLowMemEnd in Hlo; lia|].
  intros Hw. exact (proj1 (Hwr a ltac:(unfold kLowMemEnd in Hlo; lia) Hw) Himg).
- intros cid pos a Hin Hr He. rewrite <- (K4 cid pos a Hin Hr He).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (H4096 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hb0.
  destruct (shadow_cell_bound (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(lia) Hb0 ltac:(lia)) as [S1 S2].
  assert (Ha : 0 <= a < alloc_ceiling).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr;
    unfold SHADOW_OFF, kHighMemBeg in *; lia. }
  apply EQ; [lia|]. intros Hw.
  destruct (Hwr a ltac:(lia) Hw) as (_ & [[Hc _] | [He' | [_ [_ Hnf]]]]); [lia | exact (He He') |].
  destruct (Hnf cid pos Hin) as [N1 N2]. destruct Hr; contradiction.
- intros a Ha Hs Hp. apply HP. exact (K5 a Ha Hs Hp).
- intros a Ha. apply HP. exact (K6 a Ha).
Qed.
Lemma sbd3_geom : forall X pos lyc1 Sc1 memc1 mdc1 sh,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 memc1 mdc1 sh ->
  4096 <= sbd_F X pos /\ sbd_F X pos + 64 <= alloc_ceiling /\ sbd_F X pos mod 64 = 0 /\
  (sbd_F X pos + 64 <= kLowShadowBeg \/ kHighMemBeg <= sbd_F X pos) /\
  sbd_SH X pos = SHADOW_OFF + sbd_F X pos / 8 /\
  SHADOW_OFF <= sbd_SH X pos /\ sbd_SH X pos + 8 < kHighMemBeg /\
  (forall a, sbd_F X pos <= a < sbd_F X pos + 64 -> apresent (w_H (si_W X)) memc1 a) /\
  (forall i, 0 <= i < 8 -> apresent (w_H (si_W X)) memc1 (sbd_SH X pos + i)) /\
  alloc_ceiling <= sbd_SP X - SB_DEC_STK /\ sbd_SP X <= 2 ^ 47 /\
  sbd_SP X - 112 <= sbd_SP1 X <= sbd_SP X - 96 /\ sbd_SP1 X mod 32 = 0 /\
  si_sp0 X - si_STK X <= sbd_SP X - SB_DEC_STK /\ sbd_SP X <= si_sp0 X /\
  alloc_ceiling <= si_sp0 X - si_STK X /\ si_sp0 X <= 2 ^ 47.
Proof.
intros X pos lyc1 Sc1 memc1 mdc1 sh HX HM.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (HSPdef : sbd_SP X = spZ (si_regs X)) by reflexivity.
pose proof HX as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hbud & Hsp & _).
pose proof HJX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & HFLeq & HK1 & _).
pose proof (proj1 HJ1) as HAR1.
assert (Hin0 : In (0, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR1 Hin0) as (HFlo & HFhi & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 pos HAR1 Hin0) as (HFa & _ & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR1 Hin0) as (_ & _ & HFpres & HSHpres).
rewrite HFeq in HFlo, HFhi, HFapp, HFa, HFpres, HSHpres.
change (fs_frame_bytes 0) with 64 in HFhi, HFapp, HFpres, HSHpres.
change (64 / 8) with 8 in HSHpres.
fold (sbd_F X pos) in HFlo, HFhi, HFapp, HFa, HFpres, HSHpres.
fold (sbd_SH X pos) in HSHpres.
assert (HSH : sbd_SH X pos = SHADOW_OFF + sbd_F X pos / 8) by reflexivity.
destruct (shadow_cell_bound (sbd_F X pos) 64 ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2].
change (64 / 8) with 8 in S2. fold (sbd_SH X pos) in S1, S2.
assert (Hsp96 : (sbd_SP X + -96) mod 16 = 0) by (rewrite Zplus_mod, HSPdef, Hal; reflexivity).
destruct (sp1_facts (sbd_SP X + -96) ltac:(lia) Hsp96) as (Hsp1 & Hsp1a & _).
fold (sbd_SP1 X) in Hsp1, Hsp1a.
split; [lia|]. split; [lia|]. split; [exact HFa|].
split; [unfold in_app, ASAN_CEIL in HFapp; lia|].
split; [exact HSH|]. split; [lia|]. split; [lia|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
split; [intros i Hi; exact (proj1 (HSHpres i Hi))|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hsp1a|].
split; [lia|]. split; [lia|]. split; lia.
Qed.
Theorem sbd_seg3 : sbd_seg3_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS3.
pose proof HS3 as (HM & (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R10 & R2427) &
  R19 & R20 & R16 & R17 & R14 & R15 & R11 & R5 & RT12 & RT13 & R6 & Hrec).
destruct (sbd3_geom X pos lyc1 Sc1 memc1 mdc1 _ HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (CSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & HFLeq & HK1 & HFr1 & HFL1 & HSh1).
pose proof HX as (HJX & _).
pose proof (proj1 HJX) as HARX.
pose proof HJX as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAapp & HA63 & _).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & HAwr & _).
assert (HAlo : 0 <= si_A X) by (destruct HAapp as [HAapp' | HAapp']; [unfold in_app in HAapp'|]; lia).
pose proof (sbd3_lsd_len (si_v X)) as HLen.
set (DD := sbd_F X pos + 32) in *.
set (LL := Z.of_nat (length (sb_dec_c.sb_dec_lsd (si_v X) 3))) in *.
assert (HLL : 1 <= LL <= 3) by (unfold LL; lia).
assert (HAnw : forall a, si_A X <= a < si_A X + 28 -> ~ (DD <= a < DD + LL)).
{ intros a Ha.
  destruct (sbd3_not_new (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_own X) (si_lyc X) (si_Sc X)
    lyc1 Sc1 (si_W X) memc1 mdc1 0 pos a Hfrs Hc0 (proj1 HJ1) Hfrs1 Eab1 HFeq ltac:(lia) (HAwr a Ha)) as [N1 N2].
  change (fs_frame_bytes 0) with 64 in N1. fold (sbd_F X pos) in N1. unfold DD. lia. }
unfold sbd_cfg, cfg_at.
replace (BASE + AF_sb_dec + SBD_P3) with (BASE + AF_sb_dec + SBD_L1)
  by (unfold SBD_P3, SBD_L1; lia).
eapply SRr_mono.
{ change (mkCfg (mkst regs1 (w64 (BASE + AF_sb_dec + SBD_L1)) memc1 (seg_rom SEGS)) mdc1)
    with (cfg_at (fx := si_fq X) SEGS (BASE + AF_sb_dec + SBD_L1) regs1 memc1 mdc1).
  apply (L1 (si_fq X) (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 (si_W X) memc1 mdc1 (si_k X) regs1 (si_v X) DD).
  - exact HJ1.
  - exact Hv.
  - unfold DD. lia.
  - unfold DD. lia.
  - intros a Ha. split.
    + right. right. right. exists 0, pos. split; [left; reflexivity|]. left.
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFeq.
      change (fs_frame_bytes 0) with 64. fold (sbd_F X pos). unfold DD in Ha. lia.
    + apply HFpres. unfold DD in Ha. lia.
  - exact R20.
  - exact R15.
  - exact R11.
  - exact R14.
  - exact R5.
  - exact RT12.
  - exact RT13.
  - exact R6. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HKP & G11 & G15 & HOUT & HPR & HGA).
assert (KP : forall r (rb : bv 5), 0 <= r < 32 -> ~ In r [7; 11; 15; 20; 28; 29; 30; 31] ->
  Z_to_bv 5 r = rb -> getr regs2 rb = getr regs1 rb)
  by (intros r rb Hr Hn Heq; rewrite <- Heq; apply HKP; assumption).
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (DD <= a < DD + LL) ->
  aview SEGS (w_H (si_W X)) mem2 a = aview SEGS (w_H (si_W X)) memc1 a)
  by (intros a Ha Hn; apply HOUT; [exact Ha | exact Hn]).
split; [reflexivity|].
exists pos, regs2, lyc1, Sc1, mem2, md2.
split.
{ unfold sbd_cfg, cfg_at.
  replace (BASE + AF_sb_dec + SBD_P4) with (BASE + AF_sb_dec + SBD_L1X)
    by (unfold SBD_P4, SBD_L1X; lia). reflexivity. }
unfold sbd_st4.
split.
{ split; [exact HJ2|]. split; [exact Hfrs1|]. split; [exact Eab1|]. split; [exact HFeq|]. split; [exact HFLeq|].
  split.
  { unfold sbd_kept_at.
    eapply (sbd3_kept_step (si_lyc X) (si_Sc X) (si_W X) (si_memc X) memc1 mem2 (si_mdc X) _ _ _
      (fun a => DD <= a < DD + LL));
    [exact HARX | exact HK1 | exact KA | exact HPR |].
    intros a _ Hw.
    apply (sbd3_fresh (si_lyc X) (si_Sc X) lyc1 Sc1 (si_W X) memc1 mdc1 0 pos _ _ _ a
      (proj1 HJ1) Hfrs1 Eab1 HFeq ltac:(lia)).
    left. change (fs_frame_bytes 0) with 64. fold (sbd_F X pos). unfold DD in Hw. lia. }
  split.
  { intros j r Hj.
    assert (Hjr : (j < 9)%nat)
      by (apply (proj1 (nth_error_Some sbd_saved_regs j)); rewrite Hj; discriminate).
    apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 mem2); [| exact (HFr1 j r Hj)].
    intros kk Hkk. apply KA; [lia | unfold DD; lia]. }
  split.
  { apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 mem2); [| exact HFL1].
    intros kk Hkk. apply KA; [lia | unfold DD; lia]. }
  intros jj Hjj. change (Z.of_nat (length sbd_sh_hdr)) with 8 in Hjj.
  rewrite (KA (sbd_SH X pos + jj) ltac:(lia)
    ltac:(intros Hbad; unfold DD in Hbad; destruct HFapp as [Hf | Hf];
          unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)).
  exact (HSh1 jj Hjj). }
split.
{ split; [sbd3_kp KP 2 (2%bv : bv 5); exact R2|].
  split; [sbd3_kp KP 3 (3%bv : bv 5); exact R3|].
  split; [sbd3_kp KP 4 (4%bv : bv 5); exact R4|].
  split; [sbd3_kp KP 8 (8%bv : bv 5); exact R8|].
  split; [sbd3_kp KP 9 (9%bv : bv 5); exact R9|].
  split; [sbd3_kp KP 18 (18%bv : bv 5); exact R18|].
  split; [sbd3_kp KP 21 (21%bv : bv 5); exact R21|].
  split; [sbd3_kp KP 10 (10%bv : bv 5); exact R10|].
  intros r Hr. rewrite (HKP r ltac:(lia) ltac:(sbd3_nin)). exact (R2427 r Hr). }
split; [sbd3_kp KP 19 (19%bv : bv 5); exact R19|].
split; [sbd3_kp KP 16 (16%bv : bv 5); exact R16|].
split; [sbd3_kp KP 17 (17%bv : bv 5); exact R17|].
split; [sbd3_kp KP 14 (14%bv : bv 5); exact R14|].
split; [unfold sbm_lsd; exact G11|].
split; [unfold sbm_lsd; exact G15|].
split; [unfold sbm_lsd; exact HGA|].
destruct Hrec as (Mp & Mcap & Mn & Mover).
split; [|split; [|split]].
- apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 mem2);
  [intros kk Hkk; apply KA; [lia | apply HAnw; lia] | exact Mp].
- apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 mem2);
  [intros kk Hkk; apply KA; [lia | apply HAnw; lia] | exact Mcap].
- apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 mem2);
  [intros kk Hkk; apply KA; [lia | apply HAnw; lia] | exact Mn].
- apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 mem2);
  [intros kk Hkk; apply KA; [lia | apply HAnw; lia] | exact Mover].
Qed.
End h.
End f.
End d.
