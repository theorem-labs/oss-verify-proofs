(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 361 of its 425 lines of code are new or changed and 340 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputDec.v, with its module paths and module names changed; 784 of its 888 lines of code are new or changed and 321 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/mark_quietlyOrsm.v, with its module names changed; 367 of its 448 lines of code are new or changed and 807 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the lemmas the walk of mark_quietly's OPENING arm (0x883d4, g_sink = 0; listing
   (internal path) (internal record, sha256 83bb83545bf3)) uses to carry
   mark_quietlyDefs.v `mqo_rel` (what it knows of a later state relative to its entry) along the arm, and the premises
   of its callees that hold at every such state.
   - ajw_mono, layout_le0_of_gx (any segments): a journal's grant at a state is one at a later state of a layout
     with the same fixed fields and more blocks; two states of one journal have the same fixed layout fields.
   - mqo_rel_refl, mqo_rel_akept, mqo_rel_agree: mqo_rel at the entry; across a callee's kept clause whose write
     set is in mqo_E or speaks only of bytes no clause of the entry's kept clause speaks of (LinkWalkMkTail.v
     `akept_out`); across a step that changes only mqo_E, the window and blocks allocated since the entry. A byte
     of such a block is `akept_out` (mqo_fresh_out): below the ceiling and off the image (AR at the later state),
     apart from the entry's blocks and side frames (AR_sep there; the frames sit where the entry's do, ly_F), and
     not a frame's shadow (a block is application memory).
   - mqo_say_pre, mqo_buf_ok: g_say writable; g_said as rewind's copy destination. Writability of an image rw byte
     is a segment fact at any memory (link_ajkit.v writable_at_of_wseg); g_said is no owned static; its shadow is
     the image's, which AR pins at every state (LinkWalkShadow.v img_sh_eq).
   - mqo_arodata: `arodata_okP` at every later state, by akept's image clause: a read-only byte is an image byte
     (the relro window lies in a segment, PcapRelroA.v) and no mqo_E byte is read-only (link_aro.v LA_G_not_ro).
   - mqo_amf_dyn_agree, mqo_amf_pend_nil: the FILE's seven changing words under agreement on its first
     AMF_ZEROED bytes; the empty pending list.
   - mqo_fm_args: fmemopen's argument premises (LinkFoSpec.v afm_w_args). The mode word, "rwa\0" and __strchrnul's
     window [0x10360, 0x10380) lie in a non-writable segment, off the owned statics and errno (computed), so
     arodata_okP gives their image bytes (computed as in LinkFoWitness.v).
   - mqo_blk_not_ro: a heap byte is never read-only (off the image).
   - mqo_univ0_pcapb, mqo_univ1_pcapb: the two universe premises of afm_w_pre at PcapB and CTX =
     link_afmemopen_ctx (the computation of LinkFoWitness.v afm_w_rest_sat).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI00 YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFileSink AMemFile AB1v AF0l AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AD2l ACej ACejUniv AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkFoSpec LinkFoInst LinkFoWitness.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit link_aro PcapRelro PcapRelroA LinkWalkErrno LinkWalkSide LinkWalkZsh LinkWalkShadow
LinkWalkMkTail.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c mark_quietlyDefs mark_quietlyRsm
mark_quietlyArg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   0. Closed facts: lists, image bytes, the trace universe at PcapB
   ========================================================================== *)

(* two different members of a list whose images are pairwise disjoint have disjoint images *)
Lemma mqoh_pw_in : forall (f : Z * Z -> Z * Z) (l : list (Z * Z)) x y,
  pairwise zdisjoint (map f l) -> In x l -> In y l -> x <> y -> zdisjoint (f x) (f y).
Proof.
  intros f l. induction l as [|h t IH]; intros x y P Hx Hy Hne; [destruct Hx|].
  cbn [map pairwise] in P. destruct P as [F P].
  destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - exfalso. exact (Hne eq_refl).
  - exact (proj1 (Forall_forall _ _) F (f y) (in_map f t y Hy)).
  - pose proof (proj1 (Forall_forall _ _) F (f x) (in_map f t x Hx)) as D.
    unfold zdisjoint in *. lia.
  - exact (IH x y P Hx Hy Hne).
Qed.

(* a member of the left part and a member of the right part of a pairwise disjoint list are disjoint *)
Lemma mqoh_pw_app : forall (l1 l2 : list (Z * Z)) x y,
  pairwise zdisjoint (l1 ++ l2) -> In x l1 -> In y l2 -> zdisjoint x y.
Proof.
  intros l1. induction l1 as [|h t IH]; intros l2 x y P Hx Hy; [destruct Hx|].
  cbn [app pairwise] in P. destruct P as [F P]. destruct Hx as [<-|Hx].
  - exact (proj1 (Forall_forall _ _) F y (in_or_app _ _ _ (or_intror Hy))).
  - exact (IH l2 x y P Hx Hy).
Qed.

(* a byte read as the image's value is the image's byte *)
Lemma mqoh_rom_eq : forall (m : word -> option byte) a,
  amf_rd tfibsegs m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)) ->
  mbyte tfibsegs m a = seg_rom tfibsegs (Z_to_bv 64 a).
Proof.
  intros m a E. unfold amf_rd in E.
  destruct (mbyte tfibsegs m a) as [b'|], (seg_rom tfibsegs (Z_to_bv 64 a)) as [b|]; cbn in E;
    try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* [lo, hi) inside one non-writable segment *)
Lemma mqoh_ro_seg : forall lo hi,
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo) &&
                    (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true ->
  forall a, lo <= a < hi -> in_roP tfibsegs PCAP_RLO PCAP_RHI a.
Proof.
  intros lo hi H a Ha. left. apply existsb_exists in H as (s & Hin & Hs).
  apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply negb_true_iff in H1.
  apply Z.leb_le in H2. apply Z.leb_le in H3. exists s. split; [exact Hin|]. split; [exact H1 | lia].
Qed.

(* [lo, hi) apart from every owned static range *)
Lemma mqoh_not_static : forall lo hi,
  forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) Tfib_owned_static = true ->
  forall a, lo <= a < hi -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros lo hi Hb a Ha HE. apply Exists_exists in HE as (r & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) Hb r Hin) as H. apply orb_true_iff in H.
  unfold in_zr in Hr. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

(* the image's bytes of a read-only range off the owned statics and errno, at a memory arodata_okP holds of *)
Lemma mqoh_rom_lit : forall (m : word -> option byte) lo hi,
  (forall a, in_roP tfibsegs PCAP_RLO PCAP_RHI a -> ~ Exists (in_zr a) Tfib_owned_static ->
     ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) ->
     amf_rd tfibsegs m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a))) ->
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo) &&
                    (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true ->
  forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) Tfib_owned_static = true ->
  hi <= TFIB_ERRNO ->
  forall a, lo <= a < hi ->
    amf_rd tfibsegs m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Proof.
  intros m lo hi RO Hs Ho He a Ha. apply RO.
  - exact (mqoh_ro_seg lo hi Hs a Ha).
  - exact (mqoh_not_static lo hi Ho a Ha).
  - lia.
Qed.

(* (A12) afm_w_pre's two universe premises at PcapB and CTX = link_afmemopen_ctx *)
Lemma mqo_univ0_pcapb : In [pc_malloc_ra0 (as_code AD2l.PcapB)] (as_universe AD2l.PcapB).
Proof.
  rewrite AD2l.PcapB_universe, ACejUniv.Tfib_univ_fix. apply ACej.memZL_In. vm_compute. reflexivity.
Qed.

Lemma mqo_univ1_pcapb : forall c, In c link_afmemopen_ctx -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code AD2l.PcapB) ::
  flat_map (fun r => if r =? pc_malloc_ra0 (as_code AD2l.PcapB) then [] else [r]) (LA_FM_MALLOC_RA :: c)))
  (as_universe AD2l.PcapB).
Proof.
  intros c Hc. unfold link_afmemopen_ctx in Hc. destruct Hc as [<- | []].
  rewrite AD2l.PcapB_universe, ACejUniv.Tfib_univ_fix. apply ACej.memZL_In. vm_compute. reflexivity.
Qed.

(* ==========================================================================
   1. At any segments: the journal's grants and its layouts
   ========================================================================== *)

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.

(* (A5) *)
Lemma ajw_mono : forall G XO OUT STK sp0 FP ly S lyc Sc lyx Sx own a,
  ajw B G XO OUT STK sp0 FP ly S lyc Sc own a -> layout_le 0 lyc lyx ->
  (forall b n, In (b, n) (ablocks B lyc Sc) -> In (b, n) (ablocks B lyx Sx)) ->
  ajw B G XO OUT STK sp0 FP ly S lyx Sx own a.
Proof.
  intros G XO OUT STK sp0 FP ly S lyc Sc lyx Sx own a Ha Hly Hbl.
  assert (HF : ly_F lyx = ly_F lyc) by (destruct Hly as (_ & _ & _ & _ & _ & HF & _); exact HF).
  unfold ajw in *. destruct Ha as [[Haw Hno] | Ha]; [left; split; [|exact Hno] | right; exact Ha].
  unfold awr_byte in *.
  destruct Haw as [Hs | [(Hfp & b & n & Hin & Hr) | [(b & n & Hin & Hn & Hr) | (cid & pos & Hown & Hr)]]].
  - left. exact Hs.
  - right; left. split; [exact Hfp|]. exists b, n. split; [exact (Hbl b n Hin) | exact Hr].
  - right; right; left. exists b, n. split; [exact (Hbl b n Hin)|]. split; [exact Hn | exact Hr].
  - right; right; right. exists cid, pos. split; [exact Hown|].
    unfold frame_addr in Hr |- *. rewrite HF. exact Hr.
Qed.

(* (A6) *)
Lemma layout_le0_of_gx : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 k2,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k2 ->
  layout_le 0 lyc ly2.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ly2 S2 W2 mem2 md2 k2
    (_ & _ & (m1 & HJ1 & _) & _) (_ & _ & (m2 & HJ2 & _) & _).
  destruct HJ1 as (_ & L1 & _). destruct HJ2 as (_ & L2 & _). unfold layout_le in *.
  destruct L1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & _).
  destruct L2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & _).
  repeat split; try congruence. intros r Hr. lia.
Qed.

End g.

(* ==========================================================================
   2. At link's image
   ========================================================================== *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.

(* ---- mqo_rel at the entry, across a callee, across a step ---- *)

(* (A1) *)
Lemma mqo_rel_refl : forall sp lyc Sc (W : world SEGS) memc mdc,
  AR SEGS B lyc Sc W memc mdc -> (forall a, sp - MARK_QUIETLY_AK <= a < sp -> apresent (w_H W) memc a) ->
  mqo_rel SEGS B sp lyc Sc W memc lyc Sc W memc mdc.
Proof.
  intros sp lyc Sc W memc mdc HAR Hp.
  split; [exact HAR|]. split; [apply wle_refl|]. split; [apply layout_le_refl|].
  split; [reflexivity|]. split; [intros b n H; exact H|].
  split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
  split; [intros; reflexivity|]. split; [intros a _ _ Ha; exact Ha | exact Hp].
Qed.

(* (A2) *)
Lemma mqo_rel_akept : forall sp lyc Sc (W : world SEGS) memc lyx Sx Wx memx mdx lyy Sy Wy memy mdy lo hi
    (E : Z -> Prop),
  alloc_ceiling <= sp - MARK_QUIETLY_AK -> sp <= 2 ^ 47 ->
  mqo_rel SEGS B sp lyc Sc W memc lyx Sx Wx memx mdx ->
  AR SEGS B lyy Sy Wy memy mdy -> wle Wx Wy -> layout_le 0 lyc lyy -> frames Sy = frames Sx ->
  (forall b n, In (b, n) (ablocks B lyx Sx) -> In (b, n) (ablocks B lyy Sy)) ->
  sp - MARK_QUIETLY_AK <= lo -> hi <= sp ->
  (forall a, E a -> mqo_E B a \/ akept_out SEGS B lyc Sc a) ->
  akept SEGS B lyx Sx Wx memx Wy memy lo hi E ->
  mqo_rel SEGS B sp lyc Sc W memc lyy Sy Wy memy mdy.
Proof.
  intros sp lyc Sc W memc lyx Sx Wx memx mdx lyy Sy Wy memy mdy lo hi E Hc H47
    (HARx & Hwx & Hlyx & Hfrx & Hblx & HKx) HARy Hwy Hlyy Hfry Hbly Hlo Hhi HE HK.
  assert (HF : ly_F lyx = ly_F lyc) by (destruct Hlyx as (_ & _ & _ & _ & _ & HF & _); exact HF).
  split; [exact HARy|]. split; [exact (wle_trans _ _ _ _ Hwx Hwy)|]. split; [exact Hlyy|].
  split; [rewrite Hfry; exact Hfrx|]. split; [intros b n H; exact (Hbly b n (Hblx b n H))|].
  exact (akept_tail_ly SEGS B lyc Sc lyx Sx W memc Wx memx Wy memy (sp - MARK_QUIETLY_AK) sp lo hi (mqo_E B) E
    Hlo Hhi Hc ltac:(lia) HF Hfrx Hblx HE HKx HK).
Qed.

(* (A4) *)
Lemma mqo_fresh_out : forall lyc Sc lyx Sx (Wx : world SEGS) memx mdx b n a,
  AR SEGS B lyx Sx Wx memx mdx -> layout_le 0 lyc lyx -> frames Sx = frames Sc ->
  (forall b' n', In (b', n') (ablocks B lyc Sc) -> In (b', n') (ablocks B lyx Sx)) ->
  In (b, n) (ablocks B lyx Sx) -> ~ In (b, n) (ablocks B lyc Sc) -> b <= a < b + req_size n ->
  akept_out SEGS B lyc Sc a.
Proof.
  intros lyc Sc lyx Sx Wx memx mdx b n a HAR Hly Hfr Hbl Hin Hnin Ha.
  assert (HF : ly_F lyx = ly_F lyc) by (destruct Hly as (_ & _ & _ & _ & _ & HF & _); exact HF).
  destruct (al_blocks _ _ LAWS lyx Sx Wx memx mdx b n HAR Hin) as (_ & H4 & Hbc & Happ & _ & Hpw & _).
  destruct (al_sep _ _ LAWS lyx Sx Wx memx mdx HAR) as [Hsep _].
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  split; [lia|]. split.
  { exact (proj2 (al_client_img _ _ LAWS lyx Sx Wx memx mdx a HAR
      (or_introl (ex_intro _ b (ex_intro _ n (conj Hin Ha)))))). }
  split.
  { intros b' m Hb' Hr.
    assert (Hne : (b', m) <> (b, n)) by (intros E; rewrite E in Hb'; exact (Hnin Hb')).
    pose proof (mqoh_pw_in (fun x : Z * Z => (fst x, req_size (snd x))) _ _ _ Hpw (Hbl b' m Hb') Hin Hne) as D.
    cbv beta in D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
  intros cid pos Hf.
  assert (Hfx : In (cid, pos) (frames Sx)) by (rewrite Hfr; exact Hf).
  destruct (frames_bounds SEGS B LAWS lyx Sx Wx memx mdx cid pos HAR Hfx) as (Hf4 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  split.
  - unfold in_zr, frame_rng. cbn [fst snd]. intros Hr.
    pose proof (mqoh_pw_app _ _ (b, req_size n) (frame_addr lyx cid pos, fs_frame_bytes cid) Hsep
      (in_map (fun x : Z * Z => (fst x, req_size (snd x))) _ _ Hin)
      (in_map (fun f : Z * Z => (frame_addr lyx (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hfx)) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. unfold frame_addr in Hr, D. rewrite HF in D. lia.
  - unfold in_zr. cbn [fst snd]. intros Hr.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    unfold frame_addr in Hr, Hf4, Hfc. rewrite HF in Hf4, Hfc.
    unfold shadow_addr, SHADOW_OFF in Hr. lia.
Qed.

(* (A3) *)
Lemma mqo_rel_agree : forall sp lyc Sc (W : world SEGS) memc lyx Sx Wx memx mdx memy mdy (X : Z -> Prop),
  alloc_ceiling <= sp - MARK_QUIETLY_AK -> sp <= 2 ^ 47 ->
  mqo_rel SEGS B sp lyc Sc W memc lyx Sx Wx memx mdx ->
  AR SEGS B lyx Sx Wx memy mdy ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H Wx) memy a = aview SEGS (w_H Wx) memx a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H Wx) memx a -> apresent (w_H Wx) memy a) ->
  (forall a, X a -> mqo_E B a \/ (sp - MARK_QUIETLY_AK <= a < sp) \/
     exists b n, In (b, n) (ablocks B lyx Sx) /\ ~ In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) ->
  mqo_rel SEGS B sp lyc Sc W memc lyx Sx Wx memy mdy.
Proof.
  intros sp lyc Sc W memc lyx Sx Wx memx mdx memy mdy X Hc H47
    (HARx & Hwx & Hlyx & Hfrx & Hblx & K1 & K2 & K3 & K4 & K5 & K6) HARy UN Hpr HX.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HX' : forall a, X a -> mqo_E B a \/ (sp - MARK_QUIETLY_AK <= a < sp) \/ akept_out SEGS B lyc Sc a).
  { intros a Ha. destruct (HX a Ha) as [H|[H|(b & n & Hin & Hnin & Hr)]]; [left; exact H | right; left; exact H|].
    right; right. exact (mqo_fresh_out lyc Sc lyx Sx Wx memx mdx b n a HARx Hlyx Hfrx Hblx Hin Hnin Hr). }
  split; [exact HARy|]. split; [exact Hwx|]. split; [exact Hlyx|]. split; [exact Hfrx|]. split; [exact Hblx|].
  split.
  { intros a Ha Hw HnE. rewrite <- (K1 a Ha Hw HnE). apply UN; [lia|]. intros HXa.
    destruct (HX' a HXa) as [H|[H|(H & _)]]; [exact (HnE H) | exact (Hw H) | lia]. }
  split.
  { intros b m i Hb Hi HnE. rewrite <- (K2 b m i Hb Hi HnE).
    destruct (al_blocks _ _ LAWS lyx Sx Wx memx mdx b m HARx (Hblx b m Hb)) as (_ & H4 & Hbc & _).
    apply UN; [lia|]. intros HXa.
    destruct (HX' _ HXa) as [H|[H|(_ & _ & H & _)]]; [exact (HnE H) | lia | exact (H b m Hb ltac:(lia))]. }
  split.
  { intros a Hi Hns He HnE. rewrite <- (K3 a Hi Hns He HnE). pose proof (pa_segs_low a Hi) as Hal.
    apply UN; [lia|]. intros HXa.
    destruct (HX' a HXa) as [H|[H|(_ & H & _)]]; [exact (HnE H) | lia | exact (H Hi)]. }
  split.
  { intros c p a Hin Hr HnE. rewrite <- (K4 c p a Hin Hr HnE).
    assert (Hinx : In (c, p) (frames Sx)) by (rewrite Hfrx; exact Hin).
    destruct (frames_bounds SEGS B LAWS lyx Sx Wx memx mdx c p HARx Hinx) as (Hf4 & Hfc & _).
    assert (HF : ly_F lyx = ly_F lyc) by (destruct Hlyx as (_ & _ & _ & _ & _ & HF & _); exact HF).
    pose proof (fs_frame_bytes_nonneg c) as Hnn.
    assert (Hrng : 0 <= a < alloc_ceiling).
    { unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. unfold frame_addr in Hr, Hf4, Hfc.
      rewrite HF in Hf4, Hfc. unfold shadow_addr, SHADOW_OFF in Hr. destruct Hr as [Hr|Hr]; lia. }
    apply UN; [lia|]. intros HXa.
    destruct (HX' a HXa) as [H|[H|(_ & _ & _ & H)]]; [exact (HnE H) | lia |].
    destruct (H c p Hin) as [N1 N2]. destruct Hr as [Hr|Hr]; [exact (N1 Hr) | exact (N2 Hr)]. }
  split.
  { intros a Ha Hw Hp. apply Hpr; [exact Ha | exact (K5 a Ha Hw Hp)]. }
  intros a Ha. apply Hpr; [lia | exact (K6 a Ha)].
Qed.

(* ---- image bytes: writability, ownership, shadow ---- *)

Lemma mqoh_say_wr : forall (m : word -> option byte) a, LA_G_SAY <= a < LA_G_SAY + 8 -> writable_at SEGS m a.
Proof.
  intros m. rewrite HSEGS.
  apply writable_at_of_wseg; [unfold LA_G_SAY; lia | unfold LA_G_SAY; lia | vm_compute; reflexivity].
Qed.

Lemma mqoh_said_wr : forall (m : word -> option byte) a,
  LA_G_SAID <= a < LA_G_SAID + SAID_SIZE -> writable_at SEGS m a.
Proof.
  intros m. rewrite HSEGS.
  apply writable_at_of_wseg; [unfold LA_G_SAID; lia | unfold LA_G_SAID, SAID_SIZE; lia | vm_compute; reflexivity].
Qed.

Lemma mqoh_said_img : forall a, LA_G_SAID <= a < LA_G_SAID + SAID_SIZE -> in_img SEGS a.
Proof. intros a Ha. rewrite HSEGS. exact (mqa_said_in_img a Ha). Qed.

(* g_said's shadow is the image's: the same at every AR state *)
Lemma mqoh_said_shadow : forall ly1 S1 (W1 : world SEGS) m1 md1 ly2 S2 (W2 : world SEGS) m2 md2,
  AR SEGS B ly1 S1 W1 m1 md1 -> AR SEGS B ly2 S2 W2 m2 md2 ->
  range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF LA_G_SAID SAID_SIZE ->
  shadow_hull_vis (aview SEGS (w_H W1) m1) LA_G_SAID SAID_SIZE ->
  range_addressable (aview SEGS (w_H W2) m2) SHADOW_OFF LA_G_SAID SAID_SIZE /\
  shadow_hull_vis (aview SEGS (w_H W2) m2) LA_G_SAID SAID_SIZE.
Proof.
  intros ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 (M1 & _) (M2 & _) HR HH. split.
  - intros x Hx. destruct (HR x Hx) as (v & Hv & Hok). exists v. split; [|exact Hok].
    assert (Hs : SHADOW_OFF + 0x2000 <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 0xca800)
      by (unfold shadow_of_addr, SHADOW_OFF, LA_G_SAID, SAID_SIZE in *; lia).
    destruct (img_sh_eq B TB ly1 S1 _ ly2 S2 _ _ M1 M2 Hs) as [E _]. rewrite E. exact Hv.
  - intros s Hs.
    assert (Hs' : SHADOW_OFF + 0x2000 <= s < SHADOW_OFF + 0xca800)
      by (unfold shadow_addr, SHADOW_OFF, LA_G_SAID, SAID_SIZE in *; lia).
    destruct (img_sh_eq B TB ly1 S1 _ ly2 S2 _ _ M1 M2 Hs') as [E N]. rewrite E. exact N.
Qed.

(* (A7) *)
Lemma mqo_say_pre : forall sp lyc Sc (W : world SEGS) memc mdc (regs : bvmap 5 word) lyx Sx Wx memx mdx,
  AR SEGS B lyc Sc W memc mdc -> mark_quietly_apre_open SEGS B (ablocks B lyc Sc) regs (rdW W memc) ->
  mqo_rel SEGS B sp lyc Sc W memc lyx Sx Wx memx mdx -> awrange SEGS (rdW Wx memx) LA_G_SAY 8.
Proof.
  intros sp lyc Sc W memc mdc regs lyx Sx Wx memx mdx _ _ _ i Hi. apply mqoh_say_wr. lia.
Qed.

(* (A9) *)
Lemma mqo_buf_ok : forall lyc Sc (W : world SEGS) memc mdc (regs regsT : bvmap 5 word) lyx Sx Wx memx mdx,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= spZ regs - MARK_QUIETLY_AK ->
  mark_quietly_apre_open SEGS B (ablocks B lyc Sc) regs (rdW W memc) ->
  mqo_rel SEGS B (spZ regs) lyc Sc W memc lyx Sx Wx memx mdx -> spZ regsT = spZ regs - 32 ->
  amf_buf_ok SEGS B link_amf ARW_STK lyx Sx Wx regsT memx.
Proof.
  intros lyc Sc W memc mdc regs regsT lyx Sx Wx memx mdx HAR Hc HP (HARx & _) HspT.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & HmrS & HraS & HshS & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  rewrite MARK_QUIETLY_AK_val in Hc.
  destruct (mqoh_said_shadow lyc Sc W memc mdc lyx Sx Wx memx mdx HAR HARx HraS HshS) as [HR HH].
  unfold amf_buf_ok. change (amf_buf link_amf) with LA_G_SAID. change (amf_size link_amf) with SAID_SIZE.
  split; [unfold LA_G_SAID; lia|]. split; [unfold LA_G_SAID, SAID_SIZE; lia|]. split; [unfold SAID_SIZE; lia|].
  split; [|split; [exact HmrS | split; [exact HR | exact HH]]].
  intros a Ha. split; [exact (mqoh_said_wr _ a Ha)|]. split.
  - intros Ho. apply (proj1 (al_owned_image _ _ LAWS lyx Sx Wx memx mdx a HARx (mqoh_said_img a Ha))) in Ho.
    rewrite (ts_owned B TB) in Ho. exact (mqa_said_not_static a Ha Ho).
  - rewrite HspT. unfold ARW_STK, ESTACK, LA_G_SAID, SAID_SIZE in *. lia.
Qed.

(* ---- read-only bytes ---- *)

Lemma mqoh_relro_img : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Proof.
  intros a Ha. rewrite HSEGS. destruct pcap_relro_in_image as (s & Hin & H1 & H2 & H3).
  exists s. split; [exact Hin | lia].
Qed.

(* the bytes the opening arm writes (but errno) are program globals of LA_G, none read-only *)
Lemma mqoh_E_not_ro : forall a, mqo_E B a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof.
  intros a HE Herr. rewrite HSEGS. apply LA_G_not_ro. unfold inG. apply Exists_exists.
  unfold mqo_E in HE. destruct HE as [H|[H|[H|[H|H]]]]; [| | | | exfalso; exact (Herr H)].
  - exists (LA_G_SINK, 8). split; [unfold LA_G; cbn [In]; do 4 right; left; reflexivity|].
    unfold in_zr. cbn [fst snd]. lia.
  - exists (LA_G_SAID, 4096). split; [unfold LA_G; cbn [In]; do 5 right; left; reflexivity|].
    unfold in_zr, SAID_SIZE in *. cbn [fst snd]. lia.
  - exists (LA_G_SAY, 8). split; [unfold LA_G; cbn [In]; do 6 right; left; reflexivity|].
    unfold in_zr. cbn [fst snd]. lia.
  - exists (LA_OFL_HEAD, 8). split; [unfold LA_G; cbn [In]; do 7 right; left; reflexivity|].
    unfold in_zr. cbn [fst snd]. lia.
Qed.

(* (A8) *)
Lemma mqo_arodata : forall sp lyc Sc (W : world SEGS) memc mdc lyx Sx Wx memx mdx,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= sp - MARK_QUIETLY_AK ->
  mqo_rel SEGS B sp lyc Sc W memc lyx Sx Wx memx mdx ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) memc) ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H Wx) memx).
Proof.
  intros sp lyc Sc W memc mdc lyx Sx Wx memx mdx _ _ (_ & _ & _ & _ & _ & _ & _ & K3 & _) HRO a Hro Hno Herr.
  rewrite <- (HRO a Hro Hno Herr).
  apply K3; [| exact Hno | exact Herr | exact (fun HE => mqoh_E_not_ro a HE Herr Hro)].
  destruct Hro as [(s & Hin & _ & Hr) | Hr]; [exists s; split; [exact Hin | exact Hr] | exact (mqoh_relro_img a Hr)].
Qed.

(* (A13) *)
Lemma mqo_blk_not_ro : forall lyx Sx (Wx : world SEGS) memx mdx b n a,
  AR SEGS B lyx Sx Wx memx mdx -> In (b, n) (ablocks B lyx Sx) -> b <= a < b + req_size n ->
  ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof.
  intros lyx Sx Wx memx mdx b n a HAR Hin Ha. apply not_ro_off_img; [exact mqoh_relro_img|].
  exact (proj2 (al_client_img _ _ LAWS lyx Sx Wx memx mdx a HAR
    (or_introl (ex_intro _ b (ex_intro _ n (conj Hin Ha)))))).
Qed.

(* ---- the FILE ---- *)

(* (A10) *)
Lemma mqo_amf_dyn_agree : forall (m m' : word -> option byte) f fl om wend wpos wbase pos len,
  (forall a, f <= a < f + AMF_ZEROED -> mbyte SEGS m' a = mbyte SEGS m a) ->
  amf_dyn SEGS link_amf m f fl om wend wpos wbase pos len -> amf_dyn SEGS link_amf m' f fl om wend wpos wbase pos len.
Proof.
  intros m m' f fl om wend wpos wbase pos len HE H.
  assert (T : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= AMF_ZEROED ->
            val_mem SEGS m (f + off) n v -> val_mem SEGS m' (f + off) n v).
  { intros off n v H0 H1 Hv k Hk. rewrite HE by lia. exact (Hv k Hk). }
  unfold amf_dyn in *. destruct H as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & V1 & V2 & V3 & V4 & V5 & V6 & V7).
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
  split; [exact R6|]. split; [exact R7|].
  split; [apply T; [lia | cbv [AMF_ZEROED]; lia | exact V1]|].
  split; [apply T; [lia | cbv [AMF_ZEROED]; lia | exact V2]|].
  split; [apply T; [lia | cbv [AMF_ZEROED]; lia | exact V3]|].
  split; [apply T; [lia | cbv [AMF_ZEROED]; lia | exact V4]|].
  split; [apply T; [lia | cbv [AMF_ZEROED]; lia | exact V5]|].
  split; [apply T; [cbv [AMF_COOKIE]; lia | cbv [AMF_ZEROED AMF_COOKIE]; lia | exact V6]|].
  apply T; [cbv [AMF_COOKIE]; lia | cbv [AMF_ZEROED AMF_COOKIE]; lia | exact V7].
Qed.

Lemma mqo_amf_pend_nil : forall m f, amf_pend SEGS m f [].
Proof. intros m f i Hi. cbn [length] in Hi. lia. Qed.

(* ---- fmemopen's arguments ---- *)

(* "w\0", "rwa\0" and __strchrnul's window, at a memory arodata_okP holds of (the mode word's other six bytes are
   an owned-static redzone, AF0m.v row (0x21262, 0x1e): mqoh_mode_word reads them off AR's const cells) *)
Lemma mqoh_ro_lits : forall (m : word -> option byte),
  (forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) ->
     amf_rd SEGS m a = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 a))) ->
  (forall a, LA_MODE_W <= a < LA_MODE_W + 2 ->
     amf_rd SEGS m a = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 a))) /\
  garr8 SEGS m LA_RWA rwa_Z /\
  (forall a, 0x10360 <= a < 0x10380 ->
     amf_rd SEGS m a = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 a))).
Proof.
  intros m RO. rewrite (ts_owned B TB), (ts_errno B TB) in RO. rewrite HSEGS in RO |- *.
  pose proof (mqoh_rom_lit m LA_MODE_W (LA_MODE_W + 2) RO ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(unfold LA_MODE_W, TFIB_ERRNO; lia)) as L1.
  pose proof (mqoh_rom_lit m LA_RWA (LA_RWA + 4) RO ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(unfold LA_RWA, TFIB_ERRNO; lia)) as L2.
  pose proof (mqoh_rom_lit m 0x10360 0x10380 RO ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(unfold TFIB_ERRNO; lia)) as L3.
  split; [exact L1|]. split; [|exact L3].
  intros j Hj. cbn [length rwa_Z] in Hj.
  split; [| do 4 (destruct j as [|j]; [cbn; lia|]); lia].
  intros k Hk. assert (k = 0%nat) by lia. subst k.
  rewrite (mqoh_rom_eq m (LA_RWA + Z.of_nat j + Z.of_nat 0)
    (L2 (LA_RWA + Z.of_nat j + Z.of_nat 0) ltac:(unfold LA_RWA; lia))).
  do 4 (destruct j as [|j]; [apply fo_rom_byte; vm_compute; reflexivity|]). lia.
Qed.

(* the mode word 77 00 00 00 00 00 00 00: "w\0" the image's, the rest AR's const cells z2 0x21262 and z4 0x21264 *)
Lemma mqoh_mode_word : forall ly S (H : word -> bool) (mem : word -> option byte),
  ARm B ly S (aview SEGS H mem) ->
  (forall a, LA_MODE_W <= a < LA_MODE_W + 2 ->
     amf_rd SEGS (mrestrict H mem) a = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 a))) ->
  val_mem SEGS (mrestrict H mem) LA_MODE_W 8 119.
Proof.
  intros ly S H mem M L. rewrite HSEGS in M, L |- *.
  pose proof (AF0x.tfib_const_lookup B TB ly S H mem 0x21262 2 0 M ltac:(vm_compute; reflexivity)) as C2.
  pose proof (AF0x.tfib_const_lookup B TB ly S H mem 0x21264 4 0 M ltac:(vm_compute; reflexivity)) as C4.
  intros k Hk.
  destruct (Nat.lt_ge_cases k 2) as [K | K].
  - rewrite (mqoh_rom_eq _ (LA_MODE_W + Z.of_nat k) (L (LA_MODE_W + Z.of_nat k) ltac:(unfold LA_MODE_W; lia))).
    do 2 (destruct k as [|k]; [apply fo_rom_byte; vm_compute; reflexivity|]). lia.
  - destruct (Nat.lt_ge_cases k 4) as [K' | K'].
    + replace (LA_MODE_W + Z.of_nat k) with (0x21262 + Z.of_nat (k - 2)) by (unfold LA_MODE_W; lia).
      rewrite (C2 (k - 2)%nat ltac:(lia)).
      do 2 (destruct k as [|k]; [lia|]). do 2 (destruct k as [|k]; [first [reflexivity | vm_compute; reflexivity]|]).
      lia.
    + replace (LA_MODE_W + Z.of_nat k) with (0x21264 + Z.of_nat (k - 4)) by (unfold LA_MODE_W; lia).
      rewrite (C4 (k - 4)%nat ltac:(lia)).
      do 4 (destruct k as [|k]; [lia|]). do 4 (destruct k as [|k]; [first [reflexivity | vm_compute; reflexivity]|]).
      lia.
Qed.

(* (A11) one premise more than the walk's draft: AR at the call state (for the mode word's redzone bytes) *)
Lemma mqo_fm_args : forall ly S (W : world SEGS) mem md (regsT : bvmap 5 word),
  AR SEGS B ly S W mem md ->
  getr regsT 10 = w64 LA_G_SAID -> getr regsT 11 = w64 4096 -> getr regsT 12 = w64 LA_MODE_W ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  amf_env SEGS link_amf (rdW W mem) -> val_mem SEGS (rdW W mem) (amf_ofl_head link_amf) 8 0 ->
  afm_w_args SEGS link_amf 0x10360 0x10380 regsT (rdW W mem).
Proof.
  intros ly S W mem md regsT (M & _) G10 G11 G12 HRO Henv Hhead.
  destruct (mqoh_ro_lits (rdW W mem) HRO) as (Hmode & Hrwa & Hmc).
  unfold afm_w_args. split; [exact G10|]. split; [exact G11|]. split; [exact G12|].
  split; [exact (mqoh_mode_word ly S (w_H W) mem M Hmode)|].
  split; [exact Hrwa|]. split; [exact Hmc|]. split; [exact Henv | exact Hhead].
Qed.

End s.

Print Assumptions ajw_mono.
Print Assumptions layout_le0_of_gx.
Print Assumptions mqo_rel_refl.
Print Assumptions mqo_rel_akept.
Print Assumptions mqo_rel_agree.
Print Assumptions mqo_fresh_out.
Print Assumptions mqo_say_pre.
Print Assumptions mqo_arodata.
Print Assumptions mqo_buf_ok.
Print Assumptions mqo_amf_dyn_agree.
Print Assumptions mqo_amf_pend_nil.
Print Assumptions mqo_fm_args.
Print Assumptions mqo_univ0_pcapb.
Print Assumptions mqo_univ1_pcapb.
Print Assumptions mqo_blk_not_ro.
