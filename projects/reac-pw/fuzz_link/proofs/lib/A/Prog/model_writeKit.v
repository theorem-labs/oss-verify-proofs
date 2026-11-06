(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v, with its module paths and module names changed; 132 of its 171 lines of code are new or changed and 300 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100) on image A: the facts the segments of its walk share (cut interface
   lib/A/Prog/model_writeDefs.v): the projections of a cut's `mw_base`, the place of the contract's write set (the
   model block) relative to the side frame the call takes and to the image, its writability at every later journal
   state, and the move of the model block's view to a later memory that keeps its bytes.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB13.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide LinkWalkCall LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* a word of a reader is the word it was, when its eight bytes are *)
Lemma mw_rdword_ext : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  rewrite H0, (H 1 ltac:(lia)), (H 2 ltac:(lia)), (H 3 ltac:(lia)), (H 4 ltac:(lia)),
    (H 5 ltac:(lia)), (H 6 ltac:(lia)), (H 7 ltac:(lia)).
  reflexivity.
Qed.

(* every writable segment of image A lies in the read-write window [0xa1000, pcap_img_end) *)
Lemma mw_segs_rw_b : forallb (fun s => negb (seg_writable s) ||
    ((0xa1000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? pcap_img_end))) tfibsegs
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mw_img_rw : forall rlo rhi a, in_img tfibsegs a -> ~ in_roP tfibsegs rlo rhi a -> 0xa1000 <= a < pcap_img_end.
Proof.
  intros rlo rhi a (s & Hin & Hr) Hro. pose proof mw_segs_rw_b as H. rewrite forallb_forall in H.
  specialize (H s Hin). destruct (seg_writable s) eqn:Ew.
  - cbn [negb orb] in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  - exfalso. apply Hro. left. exists s. split; [exact Hin|]. split; [exact Ew | exact Hr].
Qed.

(* a byte of the read-write window is writable in every memory *)
Lemma mw_rw_writable : forall (m : word -> option byte) a, 0xa1000 <= a < pcap_img_end -> writable_at tfibsegs m a.
Proof.
  intros m a Ha. unfold writable_at. apply AB13.tfib_rw_window.
  rewrite unsigned_lit_small by (unfold pcap_img_end, YImgTop.IMG_TOP in *; lia). exact Ha.
Qed.
Lemma mw_rw_writable_s : forall segs (m : word -> option byte) a, segs = tfibsegs ->
  0xa1000 <= a < pcap_img_end -> writable_at segs m a.
Proof. intros segs m a -> Ha. exact (mw_rw_writable m a Ha). Qed.

(* the view of the model block at a later memory that keeps its bytes and its writability *)
Lemma mw_amodel_move : forall segs (m m' : word -> option byte) p bs,
  amodel_at segs m p bs ->
  (forall x, p <= x < p + MD_SIZE -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, p <= x < p + MD_SIZE -> writable_at segs m' x) -> amodel_at segs m' p bs.
Proof.
  intros segs m m' p bs ((Hb & Hw) & Hl) HK HW. split; [split|exact Hl].
  - destruct Hb as (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite HK by lia. exact (H2 i Hi).
  - intros i Hi. apply HW. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.

(* ---- the contract's premises, by name ---- *)
Lemma mw_pre_jc : forall cx, mw_pre SK B cx ->
  ajournal_gx SEGS B (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) (mw_own cx)
    (mw_lyc cx) (mw_Sc cx) (mw_W cx) (mw_memc cx) (mw_mdc cx) (mw_k cx).
Proof. intros cx (HA & _ & _). unfold apre in HA. tauto. Qed.

Lemma mw_pre_gx : forall cx, mw_pre SK B cx -> gx_ok SEGS B (mw_G cx).
Proof. intros cx (HA & _ & _). unfold apre in HA. tauto. Qed.

(* every byte of the model block: the caller lets a callee write it, it is not read-only, it is application memory *)
Lemma mw_blk_facts : forall cx a, mw_pre SK B cx -> mw_E cx a ->
  ajw B (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx) (mw_ly cx) (mw_S cx)
    (mw_lyc cx) (mw_Sc cx) (mw_own cx) a /\
  ~ in_roP SEGS (mw_rlo cx) (mw_rhi cx) a /\ mw_m cx <= a < mw_m cx + MD_SIZE /\
  (a < kLowMemEnd \/ kHighMemBeg <= a) /\ 0 <= a < 2 ^ 47.
Proof.
  intros cx a (HA & _ & HP) HE.
  destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & Hro).
  split; [exact (Hajw a HE)|]. split; [exact (Hro a HE)|].
  unfold mw_E, mw_wr, model_write_awr in HE. destruct HE as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
  unfold mw_m. split; [exact Hr|].
  destruct HP as (mbs & kbs & tab & nm & al & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  unfold amem_range in HMR. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (H0 : 0 <= aarg (mw_regs cx) 0)
    by (unfold aarg, argZ; pose proof (bv_unsigned_in_range 64 (getr (mw_regs cx) (Z_to_bv 5 (10 + 0)))); lia).
  lia.
Qed.

(* a byte of the model block is no byte of the side frame the call takes (free at the call) *)
Lemma mw_blk_not_side : forall cx fpos a, mw_pre SK B cx ->
  0 <= fpos < fs_frames MW_CID -> ~ In (MW_CID, fpos) (frames (mw_Sc cx)) ->
  mw_E cx a -> ~ aside_rng (mw_lyc cx) MW_CID fpos a.
Proof.
  intros cx fpos a HPX Hp Hn HE.
  destruct (mw_blk_facts cx a HPX HE) as (Hw & _ & _ & Happ & _).
  pose proof (@pa_img_range _ link_listing PI) as HIMG.
  eapply (ajw_not_side SK SEGS B); try eassumption.
  - exact (mw_pre_gx cx HPX).
  - exact (mw_pre_jc cx HPX).
  - unfold MW_CID; lia.
Qed.

(* a byte of the model block is writable at every later state of the journal whose owned frames, blocks and frame
   addresses include the call's *)
Lemma mw_blk_writable : forall cx own' ly' S' W' m' md' k' a, mw_pre SK B cx ->
  ajournal_gx SEGS B (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) own' ly' S' W' m' md' k' ->
  (forall x, In x (mw_own cx) -> In x own') ->
  (forall b m, In (b, m) (ablocks B (mw_lyc cx) (mw_Sc cx)) -> In (b, m) (ablocks B ly' S')) ->
  (forall c q, frame_addr ly' c q = frame_addr (mw_lyc cx) c q) ->
  mw_E cx a -> writable_at SEGS (rdW W' m') a.
Proof.
  intros cx own' ly' S' W' m' md' k' a HPX HJ' Hown Hbl Hfa HE.
  destruct (mw_blk_facts cx a HPX HE) as (Hw & Hro & _ & _).
  pose proof (ajw_mono B _ _ _ _ _ _ _ _ _ _ _ ly' S' own' a Hw Hbl Hown Hfa) as Hw'.
  destruct Hw' as [Haw | [HGa | Hout]].
  - eapply (proj1 (aj_gx_dest_byte SK SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a
      (mw_pre_gx cx HPX) HJ' (or_introl Haw))).
  - destruct (mw_pre_gx cx HPX a HGa) as [Hi _]. rewrite HSEGS in Hi, Hro.
    exact (mw_rw_writable_s SEGS (rdW W' m') a HSEGS (mw_img_rw _ _ a Hi Hro)).
  - eapply (proj1 (aj_gx_dest_byte SK SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a
      (mw_pre_gx cx HPX) HJ' (or_intror (or_intror Hout)))).
Qed.

(* the model block is apart from errno and from the call's window (the Pre's last two conjuncts) *)
Lemma mw_pre_apart : forall cx, mw_pre SK B cx ->
  apart_frame (mw_regs cx) MODEL_WRITE_AK (mw_m cx) MD_SIZE /\ apart (as_errno B) 4 (mw_m cx) MD_SIZE.
Proof.
  intros cx (_ & _ & HP).
  destruct HP as (mbs & kbs & tab & nm & al & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & HAF & HE).
  split; [exact HAF | exact HE].
Qed.

(* a byte of the model block is one akept keeps (akb at the call): it is a byte the caller lets a callee write,
   outside the call's window, application memory, and not errno *)
Lemma mw_blk_akb : forall cx a, mw_pre SK B cx -> mw_E cx a ->
  akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) a.
Proof.
  intros cx a HPX HE.
  destruct (mw_blk_facts cx a HPX HE) as (Hw & _ & Ha & Happ & Hb47).
  destruct (mw_pre_apart cx HPX) as (HAF & HER).
  unfold apart_frame, apart in HAF, HER. unfold mw_sp, mw_m in *.
  eapply (ajw_akb SK SEGS B LAWS); try eassumption.
  - exact (mw_pre_gx cx HPX).
  - exact (mw_pre_jc cx HPX).
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros b m H; exact H.
  - intros c q H; exact H.
  - intros c q; reflexivity.
Qed.

(* ---- a cut's base, one clause at a time ---- *)
Lemma mw_base_jx : forall cx fpos X ly3 S3 W3 ms3 md3, mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  ajournal_gx SEGS B (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx)
    ly3 S3 W3 (ms_mem ms3) md3 (mw_k cx).
Proof. intros cx fpos X ly3 S3 W3 ms3 md3 H. unfold mw_base in H. cbv zeta in H. tauto. Qed.

About aj_gx_dest_byte. About ajw_not_side. About ajw_mono.

Lemma mw_base_kept : forall cx fpos X ly3 S3 W3 ms3 md3, mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  akept SEGS B (mw_lyc cx) (mw_Sc cx) (mw_W cx) (mw_memc cx) W3 (ms_mem ms3)
    (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) (fun a => X a \/ aside_rng (mw_lyc cx) MW_CID fpos a).
Proof. intros cx fpos X ly3 S3 W3 ms3 md3 H. unfold mw_base in H. cbv zeta in H. tauto. Qed.

End b.
End a.
