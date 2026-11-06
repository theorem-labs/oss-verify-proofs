(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh5.v:99 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-117
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-369 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8w.v:289-290 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:156-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v, with its module paths and module names changed; 1279 of its 1357 lines of code are new or changed and 927 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_K.v from a working branch
   60d0985773d, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_K.v; 388 of its 479 lines of code are new or changed and 1266 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_K3.v from a working branch
   2767db174a0, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* fs walk kit, the FP-keyed core's static arm (RELOC's YCbq, a working branch 4aa3d96b823 on, whose
   ajournal_sub admits a third callee-footprint case `inFP FP a /\ in_img segs a`: a callee writing an image
   static that is also in the caller's FP, e.g. fuzz_alloc_live / fuzz_alloc_fail at FS_PSTAT_FP inside a
   FS_PSTAT_FP caller). S0 carries that core since a working branch 400b2a240b3; the walk lanes import this
   file by name, so its lemmas stay here.
   fsw_ajournal_sub3: ajournal_sub at tfibsegs with the laws discharged, for any after-call lemma (FSW_frame.v's
   own-carrying after-call too). fsw_rt_atU3: fsw_rt_atU with the three-arm premise. fsw_ajournal_sub5: the composition
   with a fourth arm, the callee's footprint inside the caller's OWN fake frames (in_frames lyc own), e.g. a callee
   posting into a slot of the caller's frame, and a fifth, the callee's footprint inside a frame of the caller's ENTRY
   frames S (awr_byte's frame arm, Reusable/YCbq.v:465-467), e.g. a callee writing a pj object the caller holds in its
   own live fake frame. fsw_ajournal_sub4 is the four-arm statement, a corollary. fsw_fp_sub names the five-arm
   premise once.
   fsw_after_callFPU / fsw_after_callFPU_args: FSW_K's fsw_after_callU / FSW_ret's fsw_after_callU_args with the caller's
   FP and own generic and the callee's FP1 under fsw_fp_sub; they also return ARU after the call. The saved-register
   chunks in [sp0 - f, sp0) are read through the callee journal's frames clause (it keeps every byte at or above
   alloc_ceiling outside the callee's stack window [sp0 - f - STKc, sp0 - f), whatever FP1 is). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSW_rres.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section e3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

Lemma fsw_ajournal_sub3 : forall B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2
  md2 k1,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
  (forall a, inFP FP1 a ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (inFP FP a /\ in_img tfibsegs a)) ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof.
intros B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1 HJ HJc Hlo Hhi HF.
exact (ajournal_sub tfibsegs B (AR_laws_ok tfibsegs B) fs_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k
  STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1 HJ HJc Hlo Hhi HF).
Qed.

(* fsw_ajournal_sub3 with a fourth callee-footprint arm, in_frames lyc own: bytes of the caller's own fake frames or
   of their shadow, and a fifth, the callee's footprint inside a frame of the caller's ENTRY frames S (awr_byte's
   frame arm, Reusable/YCbq.v:465-467). RELOC's ajournal_sub has no such arm, so this is YCbq.v ajournal_sub's
   composition re-proved at tfibsegs; each clause discharges the fourth arm by the separation of the own frames
   (frames Sc = own ++ frames S) from the blocks (sep_block_frame, the blocks' app range), the image (frm_img,
   fs_segs_low) and the frames of frames S (sep_frames_pos, shadow_mono), and the fifth exactly as it discharges the
   image arm, out of its inFP FP conjunct alone. fsw_ajournal_sub4 is the four-arm statement its users take, below. *)
Lemma fsw_ajournal_sub5 : forall B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2
  md2 k1,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
  (forall a, inFP FP1 a ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (inFP FP a /\ in_img tfibsegs a) \/
     in_frames lyc own a \/
     (inFP FP a /\ exists cid pos, In (cid, pos) (frames S) /\ in_zr a (frame_rng ly (cid, pos)))) ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof.
intros B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1
  (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT)
  (HAR2 & Hly2 & Hsecs2 & Hwle2 & Hio2 & Hfrs2 & Hnev2 & Hk2 & G1 & G2 & G3 & G4 & Hgone2 & Hpres2 & Hstatic2 & G5 & HQT2)
  Hlo Hhi HF.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* an own frame: in frames Sc, in the app range, its shadow inside [kLowMemEnd, kHighShadowEnd) *)
assert (OWN : forall cid pos, In (cid, pos) own ->
  In (cid, pos) (frames Sc) /\ 4096 <= frame_addr lyc cid pos /\
  frame_addr lyc cid pos + fs_frame_bytes cid <= alloc_ceiling /\ in_app (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
  kLowMemEnd <= shadow_addr (frame_addr lyc cid pos) /\
  shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 < kHighShadowEnd).
{ intros cid pos Hown.
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (frames_bounds tfibsegs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hs1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hs2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
  split; [exact HinC|]. split; [exact Hf0|]. split; [exact Hfc|]. split; [exact Hfh|]. split; [exact (proj1 Hs1)|]. lia. }
(* a byte of an own frame: in the frame's app range, or in its shadow *)
assert (OWNA : forall a, in_frames lyc own a -> exists cid pos, In (cid, pos) own /\ In (cid, pos) (frames Sc) /\
  ((frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid /\ app_addr a) \/
   (kLowMemEnd <= a < kHighShadowEnd /\
    shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8))).
{ intros a (cid & pos & Hown & Hr). exists cid, pos.
  destruct (OWN cid pos Hown) as (HinC & Hf0 & Hfc & Hfh & Hs1 & Hs2).
  split; [exact Hown|]. split; [exact HinC|].
  unfold in_zr in Hr; cbn [fst snd] in Hr. destruct Hr as [Hr | Hr].
  - left. split; [exact Hr | exact (in_app_addr _ _ _ Hfh Hr)].
  - right. split; [lia | exact Hr]. }
(* no byte of a block of Sc is in an own frame *)
assert (OFB : forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> ~ in_frames lyc own (p + i)).
{ intros p n i Hc Hi Hof.
  destruct (OWNA _ Hof) as (cid & pos & _ & HinC & [[Hr _] | [Hr _]]).
  - pose proof (sep_block_frame tfibsegs B LAWS lyc Sc Wc memc mdc p n cid pos HAR Hc HinC) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR Hc) as (_ & _ & _ & [Hh1 Hh2] & _). zlia. }
split; [exact HAR2|].
split; [eapply layout_le_trans; first [ solve [exact Hsecs] | solve [exact Hly] | solve [exact Hly2] ]|].
split; [zlia|]. split; [eapply wle_trans; eassumption|].
assert (HFo : YI16.sink_open_fp FP1 -> YI16.sink_open_fp FP).
{ intros (r & Hr & H0).
  destruct (HF 0 (ex_intro _ r (conj Hr H0)))
    as [((r' & Hr' & H0') & _) | [(b & n & Hin & _ & Hb) | [((r' & Hr' & H0') & _) |
        [Hof | ((r' & Hr' & H0') & _)]]]].
  - exists r'. split; [exact Hr' | exact H0'].
  - exfalso. pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & _). zlia.
  - exists r'. split; [exact Hr' | exact H0'].
  - exfalso. destruct (OWNA _ Hof) as (cid & pos & _ & _ & [[_ Happ] | [Hr0 _]]); zlia.
  - exists r'. split; [exact Hr' | exact H0']. }
split; [eapply aos_step_trans_fp; first [ solve [exact HFo] | solve [exact Hio] | solve [exact Hio2] ]|].
split; [rewrite Hfrs2, Hfrs, app_assoc; reflexivity|]. split; [zlia|]. split; [zlia|].
split.
{ intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply G1; [exact Ha | zlia]. }
split.
{ intros p n i H1 H2 Hi Hnf.
  assert (Hc2 : In (p, n) (ablocks B lyc Sc)).
  { destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc];
      [exact Hc|].
    exfalso. exact (Hnf (Hgone p n i H1 Hc Hi)). }
  rewrite <- (F2 p n i H1 Hc2 Hi Hnf). apply (G2 p n i Hc2); [exact H2 | exact Hi |].
  intros Hf1. destruct (HF _ Hf1) as [[Hf _] | [(b & m & Hbin & Hb0 & Hr) | [[Hf _] | [Hof | [Hf _]]]]];
    [exact (Hnf Hf) | | exact (Hnf Hf) | exact (OFB p n i Hc2 Hi Hof) | exact (Hnf Hf)].
  assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
  pose proof (sep_blocks tfibsegs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin Hc2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
split.
{ intros a Hi Hns He Hps Hsp. rewrite <- (F3 a Hi Hns He Hps Hsp). apply (G3 a Hi Hns He).
  { intros Hf1. destruct (HF _ Hf1) as [[Hf _] | [(b & m & Hbin & _ & Hr) | [[Hf _] | [Hof | [Hf _]]]]];
      [exact (Hps Hf) | exact (blk_img tfibsegs B LAWS lyc Sc Wc memc mdc b m a HAR Hbin Hr Hi) | exact (Hps Hf) |
       | exact (Hps Hf)].
    destruct (OWNA _ Hof) as (cid & pos & _ & HinC & [[Hr _] | [Hr _]]).
    - exact (frm_img tfibsegs B LAWS lyc Sc Wc memc mdc cid pos a HAR HinC Hr Hi).
    - pose proof (fs_segs_low a Hi). lia. }
  intros Ho1. exact (Hsp (HFo Ho1)). }
split.
{ intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  assert (Efr : frame_addr lyc cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  apply (G4 cid pos a HinC).
  - unfold frame_rng in *. cbn [fst snd] in *. rewrite Efr. exact Hr.
  - destruct (frames_bounds tfibsegs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
    pose proof (fs_frame_bytes_nonneg cid) as Hnn.
    pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hs1.
    pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hs2.
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. rewrite <- Efr in Hr.
    intros Hf1. destruct (HF _ Hf1) as [[Hf _] | [(b & m & Hbin & Hb0 & Hrb) | [[Hf _] | [Hof | [Hf _]]]]];
      [exact (Hnf Hf) | | exact (Hnf Hf) | | exact (Hnf Hf)].
    + destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
      pose proof (sep_block_frame tfibsegs B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      destruct Hr as [Hr|Hr]; zlia.
    + destruct (OWNA _ Hof) as (c' & p' & Hown & HinC' & Hr').
      destruct (OWN c' p' Hown) as (_ & Hf0' & Hfc' & Hfh' & Hs1' & Hs2').
      pose proof (shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
      apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
      assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
      { eapply (sep_frames_pos tfibsegs B LAWS lyc Sc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
        rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
      destruct Hr' as [[Hr' Happ] | [Hsh' Hr']]; destruct Hr as [Hr | Hr].
      * lia.
      * zlia.
      * zlia.
      * destruct Hd as [Hd | Hd]; pose proof (shadow_mono _ _ Hd); lia. }
split.
{ intros p n i H1 H2 Hi.
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B lyc Sc)) as [Hc|Hc];
    [|exact (Hgone p n i H1 Hc Hi)].
  assert (Hf1 : inFP FP1 (p + i)) by (apply (Hgone2 p n i Hc); [exact H2 | exact Hi]).
  destruct (HF _ Hf1) as [[Hf _] | [(b & m & Hbin & Hb0 & Hr) | [[Hf _] | [Hof | [Hf _]]]]];
    [exact Hf | | exact Hf | exfalso; exact (OFB p n i Hc Hi Hof) | exact Hf].
  assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hb0; exact (Hb0 H1)).
  pose proof (sep_blocks tfibsegs B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin Hc Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia. }
split.
{ intros a Ha.
  destruct (Z_lt_le_dec a (sp1 - STK1)) as [Hb|Hb];
    [|destruct (Z_lt_le_dec a sp1) as [Hb2|Hb2]; [apply Hpres2; zlia|]].
  - eapply (apresent_transfer tfibsegs);
      first [ solve [zlia] | solve [intros Him; pose proof (fs_segs_low a Him); zlia] | solve [apply G1; zlia]
            | solve [apply Hpres; exact Ha] ].
  - eapply (apresent_transfer tfibsegs);
      first [ solve [zlia] | solve [intros Him; pose proof (fs_segs_low a Him); zlia] | solve [apply G1; zlia]
            | solve [apply Hpres; exact Ha] ]. }
split; [exact Hstatic|]. split; [|exact HQT2].
{ intros a HXa He. rewrite <- (F5 a HXa He).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
  apply G5; [rewrite Eextra; exact HXa | exact He]. }
Qed.

(* the four-arm statement, for the users that do not write into a frame of frames S (FSW_frame3's after-calls) *)
Lemma fsw_ajournal_sub4 : forall B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2
  md2 k1,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
  (forall a, inFP FP1 a ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (inFP FP a /\ in_img tfibsegs a) \/
     in_frames lyc own a) ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Proof.
intros B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1 HJ HJc Hlo Hhi HF.
apply (fsw_ajournal_sub5 B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1
  HJ HJc Hlo Hhi).
intros a Ha. destruct (HF a Ha) as [H1 | [H1 | [H1 | H1]]];
  [left; exact H1 | right; left; exact H1 | right; right; left; exact H1 | right; right; right; left; exact H1].
Qed.

Lemma fsw_rt_atU3 : forall B STK sp0 FP ly S W mem md own lyc Sc Uc W1 memc mdc k STK1 sp1 FP1 nf ly2 S2 U2 W2 mem2
  md2 k1,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc W1 (unpoison Uc memc) mdc k ->
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W1 (unpoison Uc memc) mdc nf ly2 S2 W2 (unpoison U2 mem2) md2 k1 ->
  upoison_ok B ly2 S2 U2 -> upoisoned tfibsegs W2 mem2 U2 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
  (forall a, inFP FP1 a ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (inFP FP a /\ in_img tfibsegs a)) ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 (unpoison U2 mem2) md2 (k + k1) /\
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2.
Proof.
intros B STK sp0 FP ly S W mem md own lyc Sc Uc W1 memc mdc k STK1 sp1 FP1 nf ly2 S2 U2 W2 mem2 md2 k1
  HJ HJc OK2 PO2 Hlo Hhi HF.
assert (HJ2 : ajournal tfibsegs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 (unpoison U2 mem2) md2 (k + k1))
  by exact (fsw_ajournal_sub3 B STK sp0 FP ly S W mem md own lyc Sc W1 (unpoison Uc memc) mdc k
              STK1 sp1 FP1 nf ly2 S2 W2 (unpoison U2 mem2) md2 k1 HJ HJc Hlo Hhi HF).
split; [exact HJ2|].
split; [exact (proj1 HJ2)|]. split; [exact OK2 | exact PO2].
Qed.

(* the five-arm premise of fsw_ajournal_sub5, named once: the callee's footprint is an FP byte of a live block, a
   temporary block, an FP image byte, a byte of the caller's own frames, or an FP byte of a frame of the caller's
   entry frames S (awr_byte's frame arm, Reusable/YCbq.v:465-467) *)
Definition fsw_fp_sub (B : asyms) (ly : alayout) (S : astate) (lyc : alayout) (Sc : astate) own
    (FP FP1 : list (Z * Z)) : Prop :=
  forall a, inFP FP1 a ->
    (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
    in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
    (inFP FP a /\ in_img tfibsegs a) \/
    in_frames lyc own a \/
    (inFP FP a /\ exists cid pos, In (cid, pos) (frames S) /\ in_zr a (frame_rng ly (cid, pos))).

(* plain resumed state (uninstrumented caller, extra atoms from 32) *)
Lemma fsw_after_callFPU : forall B STK sp0 FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 f regsC
  ly' S' U' W' regs' mem' md' kc extra cs r,
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs B lyc Sc Uc W memC mdC ->
  ajournal tfibsegs B STKc (spZ regsC) FP1 lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  fsw_fp_sub B ly S lyc Sc own FP FP1 ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved regsC regs' ->
  spZ regsC = sp0 - f -> 0 < f -> 0 <= STKc -> STKc + f <= STK -> f mod 16 = 0 ->
  regions_wf [fstk_ret f cs] = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) (mrestrict (w_H W) memC) (sp0 - f)) cs ->
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc) /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  st_ok tfibsegs (Ereg regs' extra) (fss_ret r f cs)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros B STK sp0 FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 f regsC ly' S' U' W' regs' mem' md' kc extra cs r
  HJ HARUc HJc HF OK' PO' HP Hsp Hf HSc Hbud Hal Hwf Hin Hcs.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HJ2 : ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc))
  by exact (fsw_ajournal_sub5 B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k
              STKc (spZ regsC) FP1 [] ly' S' W' (unpoison U' mem') md' kc HJ HJc ltac:(lia) ltac:(lia) HF).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
split; [exact HJ2|]. split; [exact HARU'|].
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
(* the callee journal's frames clause: bytes at or above alloc_ceiling outside its stack window are kept *)
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
assert (Esp : getr regs' 2 = getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regs' = sp0 - f) by (unfold spZ; rewrite Esp; exact Hsp).
assert (E2 : bv_unsigned (ew (Ereg regs' extra) 2) = sp0 - f) by (rewrite (ew_Ereg_nat regs' extra 2 2%bv eq_refl); exact Usp).
rewrite restrict_mkst_fx. unfold fss_ret. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor]. unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
  + apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hin c Hc) as Hci.
    pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
    apply (chunk_ok_mbyte _ (mrestrict (w_H W) memC)); [|exact Hck].
    destruct Hci as [Hc0 Hc1]. intros i Hi. apply (mbyte_of_aview tfibsegs).
    rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' _ HARU') by lia.
    rewrite <- (fsw_aview_unpoison_high B lyc Sc Uc W memC mdC _ HARUc) by lia.
    apply F1; [lia | intros Hx; lia].
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [|lia].
  rewrite Zminus_mod, Hal16. assert (f mod 16 = 0) as -> by exact Hal. reflexivity.
Qed.

(* T resumed state (instrumented caller: shadow base atom 32, extras by xatom 33+; FSW_ret's fss_retT) *)
Lemma fsw_after_callFPU_args : forall B STK sp0 FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 f regsC
  ly' S' U' W' regs' mem' md' kc xs cs rs gf r,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs B lyc Sc Uc W memC mdC ->
  ajournal tfibsegs B STKc (spZ regsC) FP1 lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  fsw_fp_sub B ly S lyc Sc own FP FP1 ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved regsC regs' ->
  spZ regsC = sp0 - f -> 0 < f -> 0 <= STKc -> STKc + f <= STK -> f mod 16 = 0 ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W) memC) (sp0 - f)) cs ->
  Forall (region_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W') mem')) rs ->
  pairwise_disjoint (Ereg regs' (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regs' (fs_extraT ++ xs)) gf ->
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc) /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros B STK sp0 FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 f regsC ly' S' U' W' regs' mem' md' kc xs cs rs gf
  r Hgot Hcell HJ HARUc HJc HF OK' PO' HP Hsp Hf HSc Hbud Hal Hwf Hin Hcs Hrs Hpd Hgf.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HJ2 : ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc))
  by exact (fsw_ajournal_sub5 B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k
              STKc (spZ regsC) FP1 [] ly' S' W' (unpoison U' mem') md' kc HJ HJc ltac:(lia) ltac:(lia) HF).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
split; [exact HJ2|]. split; [exact HARU'|].
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
(* the callee journal's frames clause: bytes at or above alloc_ceiling outside its stack window are kept *)
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
assert (Esp : getr regs' 2 = getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regs' = sp0 - f) by (unfold spZ; rewrite Esp; exact Hsp).
assert (E2 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 2) = sp0 - f)
  by (rewrite (ew_Ereg_nat regs' (fs_extraT ++ xs) 2 2%bv eq_refl); exact Usp).
assert (E32 : ew (Ereg regs' (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 32) = SHADOW_OFF) by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
(* the two image cells of AR after the call, carried to the machine's own memory mem' (below the shadow: U' cannot
   touch them), as FSW_ret's fsw_after_callU_args *)
destruct (fsw_got_shadow B ly' S' W' (unpoison U' mem') md' Hgot Hcell HAR2) as [Kgot Kcell].
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W') (unpoison U' mem')) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B ly' S' U' W' mem' md' (Z_to_bv 64 x) HARU'
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W') (unpoison U' mem')) a 8 v -> val_mem tfibsegs (mrestrict (w_H W') mem') a 8 v).
{ intros a v Ha Hb Hv k0 Hk0. rewrite (MB (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W') mem') tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W') (unpoison U' mem') _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W') mem') tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W') (unpoison U' mem') _ _ Kcell)]. }
rewrite restrict_mkst_fx. unfold fss_retT, fsT_ret_regions in *. cbn [app] in *. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor; [|constructor; [|exact Hrs]]].
  + (* the frame, as fsw_after_callFPU *)
    unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
    * apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hin c Hc) as Hci.
      pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
      apply (chunk_ok_mbyte _ (mrestrict (w_H W) memC)); [|exact Hck].
      destruct Hci as [Hc0 Hc1]. intros i Hi. apply (mbyte_of_aview tfibsegs).
      rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' _ HARU') by lia.
      rewrite <- (fsw_aview_unpoison_high B lyc Sc Uc W memC mdC _ HARUc) by lia.
      apply F1; [lia | intros Hx; lia].
  + (* the GOT word of the shadow base, as fsw_entryT *)
    unfold fs_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
      (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
      [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
  + (* the shadow-base cell, as fsw_entryT *)
    unfold fs_bcell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
      [rewrite fsw_SOff0, E32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
- exact Hpd.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok at 1 2. cbn [af_lo af_hi af_al2].
  rewrite E2, U32. split; [|split; [|exact Hgf]].
  + change (2 ^ 4) with 16. split; [lia|]. split; [|lia].
    rewrite Zminus_mod, Hal16. assert (f mod 16 = 0) as -> by exact Hal. reflexivity.
  + rewrite Z.pow_0_r. split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.

End e3.

(* ---- resume after a PROGRAM call whose post is at a RAISED window top ot (FSH_Fn_FORM.md 3a: pj_write's callees
   write the caller's pj_out, so their journal runs the window [spC - STKc, ot) with spC the caller's sp at the call
   and ot = sp - 16). The kit's fsw_after_callFPU takes the callee's own sp as the top and reads the frame chunks at
   the CALL. Both halves are kit lemmas over the FP-keyed core: FSW_K3.fsw_ajournal_sub5 composes the journals (it is
   generic in the callee's window), and the frame region is built on the composed journal's window presence.
   fsw_after_callFPU_win: the resumed frame [spC, spC + f) lies ANYWHERE in the caller journal's window
   [sp0 - STK, sp0) (indent's frame [sp - 32, sp) ends at sp < ot; pj_write's pj_out, pj_parse's struct pj_in,
   parse_string's hex4 slot sit above the caller's frame). The chunks cs are read on a memory memk of world Wk whose
   frame bytes equal the memory's after the call (Hkeep, mbyte of the raw memory): the call's (W, memC) with Hkeep from
   the callee's keep clause (FSH_Gen.wkeep), as FSW_indent's ind_after_callU (a working branch
   fcc7188ba36) reads put's; or the return's (W', mem') with Hkeep by reflexivity. The chunks lie in [0, f) by
   regions_wf (fstk_ret's chunk_inside).
   fsw_after_callFPU_ot: the frame ends at the window top (spZ regsC = sp0 - f), the chunks read on the memory AFTER
   the call (the caller's saved s1 at sp - 24 is INSIDE the callee's window); fsw_after_callFPU_win at
   (Wk, memk) = (W', mem'). ---- *)
Section e3ot. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

Lemma fsw_after_callFPU_win :
  forall Bx STK sp0 FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 ot f regsC
    ly' S' U' W' regs' mem' md' kc extra cs r (Wk : world tfibsegs) memk,
  ajournal tfibsegs Bx STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs Bx lyc Sc Uc W memC mdC ->
  ajournal tfibsegs Bx (STKc + (ot - spZ regsC)) ot FP1 lyc Sc W (unpoison Uc memC) mdC []
    ly' S' W' (unpoison U' mem') md' kc ->
  fsw_fp_sub Bx ly S lyc Sc own FP FP1 ->
  upoison_ok Bx ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved regsC regs' ->
  0 < f -> 0 <= STKc -> spZ regsC mod 16 = 0 ->
  sp0 - STK <= spZ regsC - STKc -> spZ regsC + f <= sp0 ->
  spZ regsC <= ot -> ot <= sp0 ->
  regions_wf [fstk_ret f cs] = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) (mrestrict (w_H Wk) memk) (spZ regsC)) cs ->
  (forall a, spZ regsC <= a < spZ regsC + f ->
     mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H Wk) memk) a) ->
  ajournal tfibsegs Bx STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc) /\
  ARU tfibsegs Bx ly' S' U' W' mem' md' /\
  st_ok tfibsegs (Ereg regs' extra) (fss_ret r f cs)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros Bx STK sp0 FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 ot f regsC
  ly' S' U' W' regs' mem' md' kc extra cs r Wk memk HJ HARU HJc HFP OK' PO' HP Hf HSc Hal Hlo Hhi Hot1 Hot2
  Hwf Hcs Hkeep.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HJ2 : ajournal tfibsegs Bx STK sp0 FP ly S W0 (unpoison U mem) md ([] ++ own)
  ly' S' W' (unpoison U' mem') md' (k + kc)).
{ apply (fsw_ajournal_sub5 Bx STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k
    (STKc + (ot - spZ regsC)) ot FP1 [] ly' S' W' (unpoison U' mem') md' kc HJ HJc); [lia | lia | exact HFP]. }
cbn [app] in HJ2.
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HARU' : ARU tfibsegs Bx ly' S' U' W' mem' md') by (split; [exact HAR2 | split; [exact OK' | exact PO']]).
split; [exact HJ2|]. split; [exact HARU'|].
(* the chunks lie in the frame [0, f): fstk_ret's chunk_inside, out of regions_wf *)
assert (Hin : forall c, In c cs -> 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f).
{ pose proof Hwf as Hw. cbn [regions_wf] in Hw. rewrite andb_true_r in Hw. unfold YP09.region_wf in Hw.
  apply andb_prop in Hw as [_ Hfa]. rewrite forallb_forall in Hfa.
  intros c Hc. pose proof (Hfa c Hc) as Hci. unfold YP09.chunk_inside, fstk_ret in Hci.
  cbn [YP09.r_lo YP09.r_hi] in Hci. apply andb_prop in Hci as [Hci _]. apply andb_prop in Hci as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. split; [exact H1 | exact H2]. }
assert (Esp : getr regs' 2 = getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regs' = spZ regsC) by (unfold spZ; rewrite Esp; reflexivity).
assert (E2 : bv_unsigned (ew (Ereg regs' extra) 2) = spZ regsC)
  by (rewrite (ew_Ereg_nat regs' extra 2 2%bv eq_refl); exact Usp).
rewrite restrict_mkst_fx. unfold fss_ret. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor]. unfold region_ok, fstk_ret.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison Bx ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
  + apply Forall_forall. intros c Hc. destruct (Hin c Hc) as [Hc0 Hc1].
    pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
    apply (chunk_ok_mbyte _ (mrestrict (w_H Wk) memk)); [|exact Hck].
    intros i Hi. apply Hkeep. lia.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia | split; [exact Hal | lia]].
Qed.

Lemma fsw_after_callFPU_ot :
  forall Bx STK sp0 FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 ot f regsC
    ly' S' U' W' regs' mem' md' kc extra cs r,
  ajournal tfibsegs Bx STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs Bx lyc Sc Uc W memC mdC ->
  ajournal tfibsegs Bx (STKc + (ot - spZ regsC)) ot FP1 lyc Sc W (unpoison Uc memC) mdC []
    ly' S' W' (unpoison U' mem') md' kc ->
  fsw_fp_sub Bx ly S lyc Sc own FP FP1 ->
  upoison_ok Bx ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved regsC regs' ->
  spZ regsC = sp0 - f -> 0 < f -> 0 <= STKc -> STKc + f <= STK -> f mod 16 = 0 ->
  spZ regsC <= ot -> ot <= sp0 ->
  regions_wf [fstk_ret f cs] = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) (mrestrict (w_H W') mem') (sp0 - f)) cs ->
  ajournal tfibsegs Bx STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc) /\
  ARU tfibsegs Bx ly' S' U' W' mem' md' /\
  st_ok tfibsegs (Ereg regs' extra) (fss_ret r f cs)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros Bx STK sp0 FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 ot f regsC
  ly' S' U' W' regs' mem' md' kc extra cs r HJ HARU HJc HFP OK' PO' HP Hsp Hf HSc Hbud Hal Hot1 Hot2 Hwf Hcs.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & _) & _).
assert (Hal' : spZ regsC mod 16 = 0)
  by (rewrite Hsp, Zminus_mod, Hal16; assert (f mod 16 = 0) as -> by exact Hal; reflexivity).
rewrite <- Hsp in Hcs.
exact (fsw_after_callFPU_win Bx STK sp0 FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 ot f regsC
  ly' S' U' W' regs' mem' md' kc extra cs r W' mem' HJ HARU HJc HFP OK' PO' HP Hf HSc Hal' ltac:(lia) ltac:(lia)
  Hot1 Hot2 Hwf Hcs (fun a _ => eq_refl)).
Qed.

End e3ot.
