(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg2.v, with its module paths and module names changed; 415 of its 482 lines of code are new or changed and 696 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec SbDecLib SbDecCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma sbd2_uoff : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof.
intros E n v Hn. unfold U. rewrite denot_SOff, Hn, Z_to_bv_unsigned, Z.add_0_r.
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Zmod_mod.
Qed.
Lemma sbd2_eqb_false : forall E a b, U E a <> U E b -> bv_eqb (sv_denot E a) (sv_denot E b) = false.
Proof.
intros E a b H. destruct (bv_eqb _ _) eqn:He; [|reflexivity].
apply bv_eqb_eq in He. exfalso. apply H. unfold U. rewrite He. reflexivity.
Qed.
Lemma sbd2_c_ne : forall E n v, ew E n = Z_to_bv 64 v -> 0 < v < 2 ^ 64 ->
  acond_ok E (mkAC BC_NE (SOff n 0) (SLit 0)).
Proof.
intros E n v Hn Hv. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
rewrite (sbd2_eqb_false E (SOff n 0) (SLit 0)); [reflexivity|].
rewrite (sbd2_uoff E n v Hn), U_SLit. replace (zcanon 0) with 0 by reflexivity.
rewrite Z.mod_small by lia. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).

Definition sbd2_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 16 24 16 24 [];
    YP09.mkRegion (Some 10%nat) 0 24 0 24 [];
    YP09.mkRegion (Some 32%nat) 0 8 0 8 [] ].
Definition sbd2_facts : facts :=
  mkFacts [] [mkAC BC_NE (SOff 10 0) (SLit 0)]
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 21 0), SOff 32 0)].
Definition ss_sbd2 : sstate := mkSS 16812 sr_atoms sbd2_regions None sbd2_facts.
Definition ESD2 (regs : bvmap 5 word) (sh : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [sh])).
Lemma regs_ok_ESD2 : forall regs sh, regs_ok (ESD2 regs sh) sr_atoms regs.
Proof.
intros. unfold ESD2. apply (regs_ok_agree 32 (Ereg regs (map (Z_to_bv 64) [sh]))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Definition sbd2_shchunk (l : list YP09.chunk) (j v : Z) : bool :=
  existsb (fun c => (YP09.c_off c =? j) &&
    match YP09.c_val c with CVal w e => (N.eqb w 1) && match e with SLit z => z mod 2 ^ 64 mod 256 =? v | _ => false end
    | _ => false end) l.
Lemma sbd2_shbyte : forall E (H : word -> bool) (mem : word -> option byte) n base lo hi wlo whi cs j v,
  region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = base -> sbd2_shchunk cs j v = true ->
  aview SEGS H mem (base + j) = Some v.
Proof.
intros E H mem n base lo hi wlo whi cs j v HR Hb Hc.
unfold sbd2_shchunk in Hc. apply existsb_exists in Hc as (c & Hin & Hc).
apply andb_true_iff in Hc as (Hoff & Hc). apply Z.eqb_eq in Hoff.
destruct c as [od cv]. cbn [YP09.c_off YP09.c_val] in Hoff, Hc. subst od.
destruct cv as [w e| | |]; try discriminate.
apply andb_true_iff in Hc as (Hw & Hc). apply N.eqb_eq in Hw. subst w.
destruct e as [z| | | | | | | | | |]; try discriminate. apply Z.eqb_eq in Hc.
destruct HR as (_ & _ & _ & HF). cbn [YP09.r_chunks YP09.r_base base_val] in HF.
rewrite Forall_forall in HF. specialize (HF _ Hin). unfold chunk_ok in HF.
cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val] in HF. rewrite Hb in HF.
destruct (HF 0 ltac:(cbn; lia)) as (b & Hcb & Hmb).
cbn [cbyte byte_of_word sv_denot YP09.c_off YP09.c_val] in Hcb, Hmb. rewrite Z.add_0_r in Hmb.
injection Hcb as <-. unfold aview. rewrite Hmb. cbn [option_map].
f_equal. rewrite <- Hc, ?Z.mul_0_r, ?Z.shiftr_0_r, ?Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma sbd2_fresh : forall lyc Sc lyc1 S2 W2 mem2 md2 cid pos slo shi (Er : Z -> Prop) a,
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

Lemma sbd2_not_new : forall STK sp0 FP ly S own lyc Sc lyc1 S2 W2 mem2 md2 cid pos a,
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

Lemma sbd2_geom : forall X pos lyc1 Sc1 memc1 mdc1 sh,
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

Definition sbd2_wz (X : sbd_in) (pos : Z) (a : Z) : Prop :=
  (sbd_SP1 X + 16 <= a < sbd_SP1 X + 24) \/ (sbd_F X pos <= a < sbd_F X pos + 24) \/
  (sbd_SH X pos <= a < sbd_SH X pos + 8).

Lemma sbd2_wz_wr : forall X pos lyc1 Sc1 memc1 mdc1 sh a,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 memc1 mdc1 sh -> sbd2_wz X pos a ->
  sbd_wr B (si_lyc X) (si_Sc X) (sbd_SP X - SB_DEC_STK) (sbd_SP X)
    (sbd_Er (si_A X) (si_v X) (si_md X) (si_p X) (si_cap X) (si_n X)) a.
Proof.
intros X pos lyc1 Sc1 memc1 mdc1 sh a HX HM Hw.
destruct (sbd2_geom X pos lyc1 Sc1 memc1 mdc1 sh HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & _).
pose proof (proj1 HJ1) as HAR1.
unfold sbd2_wz in Hw. destruct Hw as [Hw | [Hw | Hw]].
- split; [intros Himg; pose proof (pa_segs_low a Himg); unfold kLowMemEnd in *; lia | left; split; lia].
- apply (sbd2_fresh (si_lyc X) (si_Sc X) lyc1 Sc1 (si_W X) memc1 mdc1 0 pos _ _ _ a HAR1 Hfrs1 Eab1 HFeq ltac:(lia)).
  left. change (fs_frame_bytes 0) with 64. fold (sbd_F X pos). lia.
- apply (sbd2_fresh (si_lyc X) (si_Sc X) lyc1 Sc1 (si_W X) memc1 mdc1 0 pos _ _ _ a HAR1 Hfrs1 Eab1 HFeq ltac:(lia)).
  right. change (fs_frame_bytes 0 / 8) with 8. fold (sbd_F X pos). fold (sbd_SH X pos). lia.
Qed.

Lemma sbd2_rec_nwz : forall X pos lyc1 Sc1 memc1 mdc1 sh a,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 memc1 mdc1 sh -> si_A X <= a < si_A X + 28 -> ~ sbd2_wz X pos a.
Proof.
intros X pos lyc1 Sc1 memc1 mdc1 sh a HX HM Ha.
destruct (sbd2_geom X pos lyc1 Sc1 memc1 mdc1 sh HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (HSPdef : sbd_SP X = spZ (si_regs X)) by reflexivity.
pose proof HX as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAsp &
  _ & _ & _ & _ & _ & _ & _ & _ & HAwr & _).
pose proof HJX as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & _).
pose proof (proj1 HJ1) as HAR1.
destruct (sbd2_not_new (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_own X) (si_lyc X) (si_Sc X)
  lyc1 Sc1 (si_W X) memc1 mdc1 0 pos a Hfrs Hc0 HAR1 Hfrs1 Eab1 HFeq ltac:(lia) (HAwr a Ha)) as [N1 N2].
change (fs_frame_bytes 0) with 64 in N1. change (fs_frame_bytes 0 / 8) with 8 in N2.
fold (sbd_F X pos) in N1, N2. fold (sbd_SH X pos) in N2.
unfold sbd2_wz. lia.
Qed.

Lemma sbd2_mid_write : forall X pos lyc1 Sc1 memc1 mdc1 memc2 mdc2 sh sh2,
  sbd_cx B X -> sbd_mid B X pos lyc1 Sc1 memc1 mdc1 sh ->
  ajournal SEGS B (si_STK X) (si_sp0 X) (si_FP X) (si_ly X) (si_S X) (si_W0 X) (si_mem0 X) (si_md0 X)
    ((0, pos) :: si_own X) lyc1 Sc1 (si_W X) memc2 mdc2 (si_k X) ->
  (forall x : word, ~ sbd2_wz X pos (bv_unsigned x) ->
     mrestrict (w_H (si_W X)) memc2 x = mrestrict (w_H (si_W X)) memc1 x) ->
  mem_grows (mrestrict (w_H (si_W X)) memc1) (mrestrict (w_H (si_W X)) memc2) ->
  sbd_shadow_at (si_W X) memc2 (sbd_SH X pos) sh2 ->
  sbd_mid B X pos lyc1 Sc1 memc2 mdc2 sh2.
Proof.
intros X pos lyc1 Sc1 memc1 mdc1 memc2 mdc2 sh sh2 HX HM HJ2 Hfr Hgr Hsh.
destruct (sbd2_geom X pos lyc1 Sc1 memc1 mdc1 sh HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (CSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof HX as (HJX & _).
pose proof (proj1 HJX) as HARX.
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & HFLeq & HK1 & HFr1 & HFL1 & _).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ sbd2_wz X pos a ->
  aview SEGS (w_H (si_W X)) memc2 a = aview SEGS (w_H (si_W X)) memc1 a).
{ intros a Ha Hn. apply aview_eq_of. apply Hfr. rewrite unsigned_lit_small by lia. exact Hn. }
split; [exact HJ2|]. split; [exact Hfrs1|]. split; [exact Eab1|]. split; [exact HFeq|]. split; [exact HFLeq|].
split.
{ unfold sbd_kept_at.
  eapply (sbd_kept_run B LAWS (si_lyc X) (si_Sc X) (si_W X) (si_memc X) memc1 memc2 (si_mdc X) _ _ _ (sbd2_wz X pos));
  [exact HARX | exact HK1 | exact Hfr | exact Hgr |].
  intros a _ Hw. exact (sbd2_wz_wr X pos lyc1 Sc1 memc1 mdc1 sh a HX HM Hw). }
split.
{ intros j r Hj.
  assert (Hjr : (j < 9)%nat)
    by (apply (proj1 (nth_error_Some sbd_saved_regs j)); rewrite Hj; discriminate).
  apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 memc2); [| exact (HFr1 j r Hj)].
  intros k Hk. apply KW; [lia | unfold sbd2_wz; lia]. }
split; [|exact Hsh].
apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 memc2); [| exact HFL1].
intros k Hk. apply KW; [lia | unfold sbd2_wz; lia].
Qed.

Lemma sbd2_entry : forall (fq : YK11.FPState) X pos regs1 lyc1 Sc1 memc1 mdc1,
  sbd_cx B X -> sbd_st2 B X pos regs1 lyc1 Sc1 memc1 mdc1 ->
  st_ok_pi SEGS VAL (ESD2 regs1 (sbd_SH X pos)) ss_sbd2
    (restrict (w_H (si_W X)) (mkst (fx := fq) regs1 (Z_to_bv 64 (BASE + 16812)) memc1 (seg_rom SEGS))).
Proof.
intros fq X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS2.
pose proof HS2 as (HM & (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R10 & R2427) & R19 & R20 & Hrec).
destruct (sbd2_geom X pos lyc1 Sc1 memc1 mdc1 _ HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (CSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & HFLeq & (K1 & K2 & K3 & K4 & K5 & K6) & _).
rewrite restrict_mkst_fx.
set (E := ESD2 regs1 (sbd_SH X pos)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ESD2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (B9 : bv_unsigned (ew E 9%nat) = sbd_SP1 X)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E10 : ew E 10%nat = Z_to_bv 64 (sbd_F X pos)) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (B10 : bv_unsigned (ew E 10%nat) = sbd_F X pos) by (rewrite E10; apply unsigned_lit_small; lia).
assert (E21 : ew E 21%nat = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E32 : ew E 32%nat = Z_to_bv 64 (sbd_SH X pos))
  by (subst E; unfold ESD2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (B32 : bv_unsigned (ew E 32%nat) = sbd_SH X pos) by (rewrite E32; apply unsigned_lit_small; lia).
unfold ss_sbd2, sbd2_regions. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_ESD2.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  + rewrite B9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply K6. lia.
  + rewrite B10. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply HFpres. lia.
  + rewrite B32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply HSHpres. lia.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite B9, B10, B32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold sbd2_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [exact I|]. split; [split; [exact (sbd2_c_ne E 10%nat (sbd_F X pos) E10 ltac:(lia)) | exact I]|].
  split; [|exact I].
  exact (shadow_decl_ok E 10%nat 21%nat 32%nat (sbd_F X pos) SHADOW_OFF E10 ltac:(lia) E21
    ltac:(rewrite E32, HSH; reflexivity)).
Qed.

Theorem sbd_seg2 : sbd_seg2_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS2.
pose proof HS2 as (HM & (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R10 & R2427) & R19 & R20 & Hrec).
destruct (sbd2_geom X pos lyc1 Sc1 memc1 mdc1 _ HX HM) as
  (HFlo & HFhi & HFa & HFapp & HSH & S1 & S2 & HFpres & HSHpres & Hc1 & H47 & Hsp1 & Hsp1a & Hbud & Hsp & Hc0 & Hsp0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : SB_DEC_STK = 4208) by reflexivity.
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (CSO : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof HM as (HJ1 & Hfrs1 & Eab1 & HFeq & HFLeq & HK1 & HFr1 & HFL1 & HSh1).
pose proof (sbd2_entry (si_fq X) X pos regs1 lyc1 Sc1 memc1 mdc1 HX HS2) as HS.
pose proof (@SRr_run_to_pi_AJ (si_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
set (E := ESD2 regs1 (sbd_SH X pos)) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ESD2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (B9 : bv_unsigned (ew E 9%nat) = sbd_SP1 X)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E10 : ew E 10%nat = Z_to_bv 64 (sbd_F X pos)) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (B10 : bv_unsigned (ew E 10%nat) = sbd_F X pos) by (rewrite E10; apply unsigned_lit_small; lia).
assert (E32 : ew E 32%nat = Z_to_bv 64 (sbd_SH X pos))
  by (subst E; unfold ESD2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (B32 : bv_unsigned (ew E 32%nat) = sbd_SH X pos) by (rewrite E32; apply unsigned_lit_small; lia).
unfold sbd_cfg, cfg_at.
replace (BASE + AF_sb_dec + SBD_P2) with (BASE + 16812) by (unfold AF_sb_dec, SBD_P2; lia).
change (w64 (BASE + 16812)) with (Z_to_bv 64 (BASE + 16812)).
paj_run_to_sh RUNTOP HS HJ1 16980.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sbd_SP1 X - si_sp0 X));
    [reflexivity | cbn [base_val]; rewrite B9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat (sbd_F X pos)); [reflexivity | exact B10 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 0, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite HFeq.
    change (fs_frame_bytes 0) with 64. fold (sbd_F X pos). lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (sbd_SH X pos)); [reflexivity | exact B32 | | apply awr_ok_nil].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 0, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite HFeq.
    change (fs_frame_bytes 0 / 8) with 8. fold (sbd_F X pos). fold (sbd_SH X pos). lia. } }
cbn [ms_mem mkst] in HF, HFr, HG.
assert (HWZ : forall x : word, ~ sbd2_wz X pos (bv_unsigned x) ->
  mrestrict (w_H (si_W X)) (ms_mem ms) x = mrestrict (w_H (si_W X)) memc1 x).
{ intros x Hx. apply HFr. intros (r & Hr & Hw). apply Hx.
  unfold ss_sbd2, sbd2_regions in Hr. cbn [ss_mem In] in Hr.
  repeat (destruct Hr as [<- | Hr]); try destruct Hr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
  rewrite ?B9, ?B10, ?B32 in Hw; unfold sbd2_wz; lia. }
pose proof (st_ok_pi_region_nth E _ _ 2 _ HS eq_refl) as HR2. cbn [ms_mem restrict] in HR2.
lazymatch type of HR2 with
| region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
    assert (HSHall : forallb (fun k => sbd2_shchunk cs (Z.of_nat k) (nth k sbd_sh_hdr 0)) (seq 0 8) = true)
      by (vm_compute; reflexivity)
end.
assert (HAr : 0 <= si_A X).
{ pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAapp & _).
  destruct HAapp as [HAapp | HAapp]; [unfold in_app in HAapp|]; lia. }
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HA63 & _).
apply SRr_ret.
pmkst HS.
prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4.
prreg HS (8%bv : bv 5) G8. prreg HS (9%bv : bv 5) G9. prreg HS (18%bv : bv 5) G18.
prreg HS (21%bv : bv 5) G21. prreg HS (10%bv : bv 5) G10. prreg HS (19%bv : bv 5) G19.
prreg HS (20%bv : bv 5) G20. prreg HS (16%bv : bv 5) G16. prreg HS (17%bv : bv 5) G17.
prreg HS (14%bv : bv 5) G14. prreg HS (15%bv : bv 5) G15. prreg HS (11%bv : bv 5) G11.
prreg HS (5%bv : bv 5) G5. prreg HS (12%bv : bv 5) G12. prreg HS (13%bv : bv 5) G13.
prreg HS (6%bv : bv 5) G6.
rewrite (EE 2%nat 2%bv eq_refl) in G2. rewrite (EE 3%nat 3%bv eq_refl) in G3.
rewrite (EE 4%nat 4%bv eq_refl) in G4. rewrite (EE 8%nat 8%bv eq_refl) in G8.
rewrite (EE 9%nat 9%bv eq_refl) in G9. rewrite (EE 18%nat 18%bv eq_refl) in G18.
rewrite (EE 21%nat 21%bv eq_refl) in G21. rewrite (EE 10%nat 10%bv eq_refl) in G10.
rewrite (EE 19%nat 19%bv eq_refl) in G19. rewrite (EE 20%nat 20%bv eq_refl) in G20.
unfold sbd_at3. split; [reflexivity|].
exists pos, (ms_regs ms), lyc1, Sc1, (ms_mem ms), (with_vm_backing (m_vm_lazy mdc1) mat mdc1).
split.
{ unfold sbd_cfg, cfg_at, w64.
  replace (BASE + AF_sb_dec + SBD_P3) with (BASE + 16980) by (unfold AF_sb_dec, SBD_P3; lia).
  reflexivity. }
unfold sbd_st3. split.
{ apply (sbd2_mid_write X pos lyc1 Sc1 memc1 mdc1 (ms_mem ms) _ (repeat 0 8) _ HX HM HJ1 HWZ HG).
  intros j Hj. change (Z.of_nat (length sbd_sh_hdr)) with 8 in Hj.
  assert (Hk : exists k, (k < 8)%nat /\ j = Z.of_nat k) by (exists (Z.to_nat j); split; lia).
  destruct Hk as (k & Hk & ->). rewrite Nat2Z.id.
  eapply sbd2_shbyte; [exact HR2 | exact B32 |].
  apply (proj1 (forallb_forall _ _) HSHall). apply in_seq. lia. }
split.
{ split; [rewrite G2; exact R2|]. split; [rewrite G3; exact R3|]. split; [rewrite G4; exact R4|].
  split; [rewrite G8; exact R8|]. split; [rewrite G9; exact R9|]. split; [rewrite G18; exact R18|].
  split; [rewrite G21; exact R21|]. split; [rewrite G10; exact R10|].
  intros r Hr. rewrite <- (R2427 r Hr).
  assert (Hc : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]].
  - prreg HS (Z_to_bv 5 24) G. rewrite G. apply EE. vm_compute. reflexivity.
  - prreg HS (Z_to_bv 5 25) G. rewrite G. apply EE. vm_compute. reflexivity.
  - prreg HS (Z_to_bv 5 26) G. rewrite G. apply EE. vm_compute. reflexivity.
  - prreg HS (Z_to_bv 5 27) G. rewrite G. apply EE. vm_compute. reflexivity. }
split; [rewrite G19; exact R19|]. split; [rewrite G20; exact R20|].
split; [rewrite G16, E10; reflexivity|].
split; [rewrite G17, E32; reflexivity|].
split; [rewrite G14, B10; reflexivity|].
split; [rewrite G15; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite G11; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite G5; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite G12; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite G13; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite G6; apply bv_eq; vm_compute; reflexivity|].
destruct Hrec as (Mp & Mcap & Mn & Mover).
assert (KA : forall a, si_A X <= a < si_A X + 28 ->
  aview SEGS (w_H (si_W X)) (ms_mem ms) a = aview SEGS (w_H (si_W X)) memc1 a).
{ intros a Ha. apply aview_eq_of. apply HWZ. rewrite unsigned_lit_small by lia.
  exact (sbd2_rec_nwz X pos lyc1 Sc1 memc1 mdc1 _ a HX HM Ha). }
split; [|split; [|split]].
- apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 (ms_mem ms)); [intros k Hk; apply KA; lia | exact Mp].
- apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 (ms_mem ms)); [intros k Hk; apply KA; lia | exact Mcap].
- apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 (ms_mem ms)); [intros k Hk; apply KA; lia | exact Mn].
- apply (val_mem_kept SEGS (w_H (si_W X)) (w_H (si_W X)) memc1 (ms_mem ms)); [intros k Hk; apply KA; lia | exact Mover].
Qed.
End h.
End f.
End d.
