(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed. *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed; 778 of its 849 lines of code are new or changed and 69 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnTransportCg.v, with its module paths and module names changed; 457 of its 549 lines of code are new or changed and 757 lines of the source are left out. *)
(* diginet_session_submit_segs: the cut layer of the image-B walk of diginet_session_submit (fuzz_transport.asan-ubsan
   0x89aec, lib/B/Prog/diginet_session_submit_cg.v). Definitions and the facts every segment shares; no run.

   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []) from the entry to the
   return. A cut is a concrete state at one pc, as libdiginet/fuzz_decode's diginet_decoder_next_cut.v states its
   cuts: the segment that starts at a cut re-enters the position-abstract engine from the concrete registers and
   memory (DgnTransportBPaLib.v pa_entry_st_ok_full). Two cuts:
   - APP (+0xdc, 0x89bc8): the append (diginet_session.c:345-348), reached from the kind tests, from an empty
     queue and from the end of the search; the model's search answered Some None.
   - LOOP (+0x19c, 0x89c88): the head of the search over the queue at index j (:337-343), with the down-counter
     a6 = 512 - j of image B's index check.

   The pieces:
   - ssw_ctx: the contract's universally quantified values; ssw_ok: its premises at them; ssw_rt: the runtime
     premises of the holds statement; ssw_post: the contract's post.
   - ssw_lite: what every point of the walk keeps of the caller (acall_kept_g over the written range ssubmit_wr),
     of the command's 32 bytes (garr8, decode_rd_ok) and of the world (tw_at at a model world Bc).
   - ssw_saved: the five words the prologue saved (s3, s2, s1, s0, ra at sp - 40 .. sp - 8).
   - ssw_cur / ssw_rg: the facts of a cut (journal, frames, blocks, meter, lite, saved words) and the registers
     every cut holds (sp - 48, gp, tp, s0 = c, s1 = s, s2 = s + 18144, s3 = the shadow base, a2 = s2 >> 3, s4 .. s11
     as at the entry).
   - ssw_app_cut / ssw_loop_at / ssw_loop_cut: the two cuts.
   - the steps every run takes on ssw_lite: ssw_lite_step (a run that writes only its frame), ssw_lite_store (a run
     that also stores into one field of g_s inside ssubmit_wr), ssw_lite_cpy (__asan_memcpy of the command into
     one queue entry); ssw_kept_step (acall_kept_g carried over a step at any world); ssw_close (the post).
   - the call of diginet_body_check: ssw_garr8_u (the command's bytes as the model's u_at), ssw_src_rd and
     ssw_src_acall (the command placed and kept across the call, outside G and TRANS_RO_RD), ssw_ly_same (the
     frames and the machine stack at the same addresses after the call). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg diginet_session_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_session_submit_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module PBC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_body_check_cg.
Module SSK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_submit_seg_kit.

(* ------------------------------------------------------------------ *)
(* The addresses                                                       *)
(* ------------------------------------------------------------------ *)

(* The cut points and the return addresses, as offsets of the listing (lib/B/Prog/DgnTransportBList.v). *)
Definition SSW_APP : Z := AF_diginet_session_submit + 0xdc.    (* 0x89bc8, the append *)
Definition SSW_LOOP : Z := AF_diginet_session_submit + 0x19c.  (* 0x89c88, the search's head *)
Definition SSW_RET_BC : Z := AF_diginet_session_submit + 0x78.  (* 0x89b64, after diginet_body_check *)
Definition SSW_RET_CA : Z := AF_diginet_session_submit + 0x13c. (* 0x89c28, after the append's memcpy *)
Definition SSW_RET_CC : Z := AF_diginet_session_submit + 0x1fc. (* 0x89ce8, after the coalescing memcpy *)

(* g_s's base, s2 = s + 18144 (&g_s.queued) and a2 = s2 >> 3, as the code computes them. *)
Definition SSW_S2 : Z := TB_g_s + 18144.
Definition SSW_A2 : Z := SSW_S2 / 8.

(* ------------------------------------------------------------------ *)
(* The context                                                         *)
(* ------------------------------------------------------------------ *)

Record ssw_ctx : Type := mkSSW {
  cx_STK : Z; cx_sp0 : Z; cx_FP : list (Z * Z); cx_ly : alayout; cx_S : astate;
  cx_W0 : world tfibsegs; cx_mem0 : word -> option byte; cx_md0 : Model; cx_own : list (Z * Z);
  cx_lyc : alayout; cx_Sc : astate; cx_W : world tfibsegs; cx_memc : word -> option byte; cx_mdc : Model;
  cx_k : Z; cx_regs : bvmap 5 word; cx_cp : Z; cx_r : Z; cx_C : list byte; cx_Bw : list byte; cx_Bw' : list byte }.

Section ssw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS_B.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The entry sp, the queue length and the command's key of the context. *)
Definition ssw_SP (c : ssw_ctx) : Z := spZ (cx_regs c).
Definition ssw_q (c : ssw_ctx) : Z := TW.S_queued (cx_Bw c).
Definition ssw_key (c : ssw_ctx) : Z := TS0.cmd_key_of (cx_C c).
Definition ssw_len (c : ssw_ctx) : Z := TS0.cmd_len_of (cx_C c).

(* The runtime premises of the holds statement (diginet_session_submit_cg.v:199-204). *)
Definition ssw_rt : Prop :=
  transport_cells B /\ trans_ssubmit_cells B /\ AR_laws segs B /\ ameter_laws MT /\
  gx_ok segs B G /\ gx_noerrno B G /\
  (forall fx' : YK11.FPState,
     @PBC.transport_diginet_body_check_cg fx' rc B MT (transportb_sigma TB_diginet_body_check)) /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)).

(* The contract's premises at the context (diginet_session_submit_cg.v:176-190). *)
Definition ssw_ok (c : ssw_ctx) : Prop :=
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    (cx_own c) (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) (cx_k c) /\
  YK0s.ret_ok (YK11.getr (cx_regs c) 1) /\ 4096 <= raZ (cx_regs c) /\
  YK11.getr (cx_regs c) 3 = w64 (as_gp B) /\ YK11.getr (cx_regs c) 4 = w64 (as_tp B) /\
  YK11.getr (cx_regs c) 10 = w64 SSUBMIT_S /\ YK11.getr (cx_regs c) 11 = w64 (cx_cp c) /\
  spZ (cx_regs c) mod 16 = 0 /\ cx_sp0 c - cx_STK c <= spZ (cx_regs c) - SSUBMIT_STK /\
  spZ (cx_regs c) <= cx_sp0 c /\
  tw_at TMAP_B (aview segs (w_H (cx_W c)) (cx_memc c)) (cx_Bw c) /\
  TS0.diginet_session_submit_m (cx_Bw c) (cx_C c) = Some (cx_Bw' c, cx_r c) /\
  length (cx_C c) = 32%nat /\
  cx_cp c <> 0 /\ cx_cp c mod 4 = 0 /\
  trans_src_ok B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_cp c) SSUBMIT_CMD_LEN /\
  garr8 segs (mrestrict (w_H (cx_W c)) (cx_memc c)) (cx_cp c) (TW.zs (cx_C c)) /\
  decode_off_win (cx_regs c) SSUBMIT_STK (cx_cp c) SSUBMIT_CMD_LEN /\
  (forall x, cx_cp c <= x < cx_cp c + SSUBMIT_CMD_LEN -> ~ inG G x /\ ~ trans_in_ro_rd x) /\
  count_cid PBC.TRANS_BC_CID (frames (cx_Sc c)) < fs_frames PBC.TRANS_BC_CID /\
  st_nev (cx_S c) + cx_k c + SSUBMIT_EV <= EV_MAX.

(* The contract's post at the context. *)
Definition ssw_post (c : ssw_ctx) : world segs -> config -> Prop :=
  @transport_ssubmit_post fx rc B MT (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c)
    (cx_md0 c) (cx_own c) (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_k c) (cx_regs c) (cx_Bw' c) (cx_r c).

(* What every point of the walk keeps: the caller's bytes (acall_kept_g over ssubmit_wr), the command's 32 bytes
   and their shadow, and the world relation at a model world Bc. *)
Definition ssw_lite (c : ssw_ctx) (WX : world segs) (m : word -> option byte) (Bc : list byte) : Prop :=
  acall_kept_g segs B G (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) WX m
    (ssw_SP c - SSUBMIT_STK) (ssw_SP c) ssubmit_wr /\
  garr8 segs (mrestrict (w_H WX) m) (cx_cp c) (TW.zs (cx_C c)) /\
  decode_rd_ok WX m (cx_cp c) 32 /\
  tw_at TMAP_B (aview segs (w_H WX) m) Bc.

(* The five words of the prologue (0x89af0 .. 0x89b00): s3, s2, s1, s0, ra at sp - 40 .. sp - 8. *)
Definition ssw_saved (c : ssw_ctx) (WX : world segs) (m : word -> option byte) : Prop :=
  val_mem segs (mrestrict (w_H WX) m) (ssw_SP c - 40) 8 (bv_unsigned (YK11.getr (cx_regs c) 19)) /\
  val_mem segs (mrestrict (w_H WX) m) (ssw_SP c - 32) 8 (bv_unsigned (YK11.getr (cx_regs c) 18)) /\
  val_mem segs (mrestrict (w_H WX) m) (ssw_SP c - 24) 8 (bv_unsigned (YK11.getr (cx_regs c) 9)) /\
  val_mem segs (mrestrict (w_H WX) m) (ssw_SP c - 16) 8 (bv_unsigned (YK11.getr (cx_regs c) 8)) /\
  val_mem segs (mrestrict (w_H WX) m) (ssw_SP c - 8) 8 (bv_unsigned (YK11.getr (cx_regs c) 1)).

(* The facts of a cut, at the state (lyX, SX, WX, m, md): the caller's journal, the frames and blocks of the call
   state, no meter charge, the kept facts at the entry world Bw, the saved words. *)
Definition ssw_cur (c : ssw_ctx) (lyX : alayout) (SX : astate) (WX : world segs) (m : word -> option byte)
    (md : Model) : Prop :=
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    (cx_own c) lyX SX WX m md (cx_k c) /\
  frames SX = frames (cx_Sc c) /\ Permutation (ablocks B lyX SX) (ablocks B (cx_lyc c) (cx_Sc c)) /\
  mo_le MT (cx_Sc c) SX 0 /\
  ssw_lite c WX m (cx_Bw c) /\ ssw_saved c WX m.

(* The registers every cut holds. *)
Definition ssw_rg (c : ssw_ctx) (regs' : bvmap 5 word) : Prop :=
  YK11.getr regs' 2 = w64 (ssw_SP c - 48) /\
  YK11.getr regs' 3 = w64 (as_gp B) /\ YK11.getr regs' 4 = w64 (as_tp B) /\
  YK11.getr regs' 8 = w64 (cx_cp c) /\ YK11.getr regs' 9 = w64 TB_g_s /\
  YK11.getr regs' 12 = w64 SSW_A2 /\ YK11.getr regs' 18 = w64 SSW_S2 /\ YK11.getr regs' 19 = w64 SHADOW_OFF /\
  (forall r, 20 <= r <= 27 -> YK11.getr regs' (Z_to_bv 5 r) = YK11.getr (cx_regs c) (Z_to_bv 5 r)).

Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The append cut: the model's search answered Some None. *)
Definition ssw_app_cut (c : ssw_ctx) : Prop :=
  forall lyX SX (WX : world segs) regs' m md,
    ssw_rt -> ssw_ok c -> ssw_cur c lyX SX WX m md -> ssw_rg c regs' ->
    SSK.ssk_k (cx_Bw c) (cx_C c) (Some None) = Some (cx_Bw' c, cx_r c) ->
    SRr segs WX (@cfg_at fx segs (BASE + SSW_APP) regs' m md) (ssw_post c).

(* The search's head at index j: a3 = 32 j, a4 = &s->queue[0] (s + 1760), a5 = 32 queued, a6 = 512 - j (the
   down-counter of the index check), a7 = the key (sign-extended); j < queued and the model's search from j has the
   rest of the queue to scan. *)
Definition ssw_loop_at (c : ssw_ctx) (j : Z) (WX : world segs) (cf : config) : Prop :=
  exists lyX SX regs' m md, cf = @cfg_at fx segs (BASE + SSW_LOOP) regs' m md /\
    ssw_cur c lyX SX WX m md /\ ssw_rg c regs' /\
    YK11.getr regs' 13 = w64 (32 * j) /\ YK11.getr regs' 14 = w64 (TB_g_s + 1760) /\
    YK11.getr regs' 15 = w64 (32 * ssw_q c) /\ YK11.getr regs' 16 = w64 (512 - j) /\
    YK11.getr regs' 17 = Z_to_bv 64 (bv_swrap 32 (ssw_key c)) /\
    0 <= j < ssw_q c /\
    SSK.ssk_k (cx_Bw c) (cx_C c)
      (TS0.submit_find_m (cx_Bw c) (ssw_key c) j (Z.to_nat (ssw_q c - j))) = Some (cx_Bw' c, cx_r c).

Definition ssw_loop_cut (c : ssw_ctx) : Prop :=
  ssw_rt -> ssw_ok c -> forall j (WX : world segs) cf, ssw_loop_at c j WX cf -> SRr segs WX cf (ssw_post c).

(* ------------------------------------------------------------------ *)
(* Facts of the context                                                *)
(* ------------------------------------------------------------------ *)

(* What the journal at the entry gives: the stack window, its presence, AR at the call state. *)
Lemma ssw_ok_stack : forall c, ssw_ok c ->
  @AR rc segs B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) /\
  2 ^ 46 <= ssw_SP c <= 2 ^ 47 /\ alloc_ceiling <= ssw_SP c - SSUBMIT_STK /\
  (forall a, ssw_SP c - SSUBMIT_STK <= a < ssw_SP c -> apresent (w_H (cx_W c)) (cx_memc c) a).
Proof.
  intros c HOK. destruct HOK as (HJ & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & _).
  pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (ESS : SSUBMIT_STK = 4320) by reflexivity.
  unfold ssw_SP. split; [exact HAR|]. split; [lia|]. split; [lia|].
  intros a Ha. apply Hpres0. lia.
Qed.

(* The stack pointer's arithmetic facts: 16-aligned, its window inside the caller's, the memcpy's offset. *)
Lemma ssw_ok_sp : forall c, ssw_ok c ->
  ssw_SP c mod 16 = 0 /\ cx_sp0 c mod 16 = 0 /\ cx_sp0 c - cx_STK c <= ssw_SP c - SSUBMIT_STK /\
  ssw_SP c <= cx_sp0 c /\ (ssw_SP c - 48 - cx_sp0 c) mod 16 = 0 /\ SSUBMIT_STK = 4320.
Proof.
  intros c HOK. destruct HOK as (HJ & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & _).
  pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
  pose proof Hstk as (Hsp0a & _).
  unfold ssw_SP. split; [exact Hsp16|]. split; [exact Hsp0a|]. split; [exact Hlo|]. split; [exact Hhi|].
  split; [|reflexivity].
  replace (spZ (cx_regs c) - 48 - cx_sp0 c) with (spZ (cx_regs c) - cx_sp0 c + (-3) * 16) by lia.
  rewrite Z_mod_plus_full, Zminus_mod, Hsp16, Hsp0a. reflexivity.
Qed.

(* The command's range: where trans_src_ok places it, and away from the stack window and from G. *)
Lemma ssw_ok_cp : forall c, ssw_rt -> ssw_ok c ->
  4096 <= cx_cp c /\ cx_cp c + 32 <= 2 ^ 47 /\
  (cx_cp c + 32 <= ssw_SP c - SSUBMIT_STK \/ ssw_SP c <= cx_cp c) /\
  decode_rd_ok (cx_W c) (cx_memc c) (cx_cp c) 32.
Proof.
  intros c HRT HOK.
  destruct HRT as (_ & _ & LAWS & _).
  pose proof (ssw_ok_stack c HOK) as (HAR & _).
  destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSRC & _ & HOFF & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold SSUBMIT_CMD_LEN in *.
  destruct (trans_src_ok_place B LAWS _ _ _ _ _ _ _ HAR HSRC ltac:(lia)) as [P | P]; unfold decode_off_win in HOFF;
    (split; [lia|]); (split; [lia|]); (split; [unfold ssw_SP; lia|]);
    exact (trans_src_ok_rd B LAWS _ _ _ _ _ _ _ HAR HSRC ltac:(lia)).
Qed.

(* ------------------------------------------------------------------ *)
(* Bytes                                                               *)
(* ------------------------------------------------------------------ *)

(* val_mem read through aview at two memories that agree on its bytes. *)
Lemma ssw_vm_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> aview segs H' m' (a + Z.of_nat k) = aview segs H m (a + Z.of_nat k)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
  intros H H' m m' a n v HA Hv k Hk. rewrite (mbyte_of_aview segs H H' m m' (a + Z.of_nat k) (HA k Hk)).
  exact (Hv k Hk).
Qed.

(* The bytes of a val_mem, read through aview. *)
Lemma ssw_vm_aview : forall (H : word -> bool) m a (n : nat) v k, val_mem segs (mrestrict H m) a n v -> (k < n)%nat ->
  aview segs H m (a + Z.of_nat k) = Some (YG0f.le_byte v n k).
Proof.
  intros H m a n v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256.
  unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* garr8 read through aview. *)
Lemma ssw_garr8_aview : forall (H : word -> bool) m a (l : list Z) i, garr8 segs (mrestrict H m) a l ->
  0 <= i < Z.of_nat (length l) -> aview segs H m (a + i) = Some (nth (Z.to_nat i) l 0).
Proof.
  intros H m a l i Hg Hi. destruct (Hg (Z.to_nat i) ltac:(lia)) as [Hv Hr].
  pose proof (ssw_vm_aview H m (a + Z.of_nat (Z.to_nat i)) 1 _ 0 Hv ltac:(lia)) as E.
  rewrite Z2Nat.id in E by lia. cbn [Z.of_nat] in E. rewrite Z.add_0_r in E. rewrite E. f_equal.
  unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite (Z.mod_small (nth (Z.to_nat i) l 0) (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(* garr8 at two memories that agree on its bytes. *)
Lemma ssw_garr8_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a (l : list Z),
  (forall i, a <= i < a + Z.of_nat (length l) -> aview segs H' m' i = aview segs H m i) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
  intros H H' m m' a l HA Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (ssw_vm_xfer H H' m m' _ 1 _); [|exact Hv]. intros k Hk. apply HA. lia.
Qed.

(* The saved words at another memory that agrees on the frame's top 40 bytes. *)
Lemma ssw_saved_xfer : forall c (W1 W2 : world segs) m1 m2,
  (forall a, ssw_SP c - 40 <= a < ssw_SP c -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  ssw_saved c W1 m1 -> ssw_saved c W2 m2.
Proof.
  intros c W1 W2 m1 m2 HA (V1 & V2 & V3 & V4 & V5).
  assert (X : forall off v, 8 <= off <= 40 -> val_mem segs (mrestrict (w_H W1) m1) (ssw_SP c - off) 8 v ->
    val_mem segs (mrestrict (w_H W2) m2) (ssw_SP c - off) 8 v).
  { intros off v Hoff Hv. apply (ssw_vm_xfer (w_H W1) (w_H W2) m1 m2 _ 8 v); [|exact Hv].
    intros k Hk. apply HA. lia. }
  split; [exact (X 40 _ ltac:(lia) V1)|]. split; [exact (X 32 _ ltac:(lia) V2)|].
  split; [exact (X 24 _ ltac:(lia) V3)|]. split; [exact (X 16 _ ltac:(lia) V4) | exact (X 8 _ ltac:(lia) V5)].
Qed.

(* A region of a symbolic state whose bytes and write window are kept across a change of world. *)
Lemma ssw_region_kept2 : forall E (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview segs H2 m2 a = aview segs H m a) ->
  (forall a, b + wlo <= a < b + whi -> writable_at segs (mrestrict H2 m2) a) ->
  region_kept segs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
  intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hw.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
  - apply (mbyte_of_aview segs). apply Hav. exact Ha.
  - intros _. apply Hw. exact Ha.
Qed.

(* ------------------------------------------------------------------ *)
(* g_s and G                                                           *)
(* ------------------------------------------------------------------ *)

Lemma ssw_gs_inG : forall a, TB_g_s <= a < TB_g_s + TW.SZ_g_s -> inG G a.
Proof.
  intros a Ha. unfold inG, TG.G_HARNESS_B. apply Exists_exists. exists (0x5df640, 18264).
  split; [cbn; tauto | unfold in_zr; cbn [fst snd]; unfold TB_g_s, TW.SZ_g_s in Ha; lia].
Qed.

Lemma ssw_wr_gs : forall a, ssubmit_wr a -> TB_g_s <= a < TB_g_s + TW.SZ_g_s.
Proof.
  intros a [H | [H | [H | (j & Hj & H)]]]; unfold twb_fld in H;
    unfold TW.A_S_queued, TW.A_S_stats_coalesced, TW.A_S_stats_refused, TW.A_S_queue_bytes, TW.S_queue_ESZ,
      TW.S_queue_N, TW.OFF_g_s, TW.SZ_g_s, TB_g_s in *; lia.
Qed.

Lemma ssw_wr_inG : forall a, ssubmit_wr a -> inG G a.
Proof. intros a H. exact (ssw_gs_inG a (ssw_wr_gs a H)). Qed.

(* A payload byte of the world table is a byte of G. *)
Lemma ssw_tw_in_G : forall x, tw_in TMAP_B x -> inG G x.
Proof.
  intros x (o & b & n & Hin & Hx).
  assert (HG : In (b, n) G)
    by exact (tw_in_G_of TMAP_B G ltac:(vm_compute; reflexivity) o b n Hin).
  unfold inG. apply Exists_exists. exists (b, n). split; [exact HG | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* g_s's 18264 bytes (2283 whole granules) are addressable at every AR state. *)
Lemma ssw_gs_ra : forall ly S (W : world segs) mem md,
  trans_ssubmit_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF TB_g_s 18264.
Proof.
  intros ly S W mem md HZ HAR x Hx.
  assert (EC : TB_g_s = 6157888) by reflexivity.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  unfold shadow_of_addr. exists 0. split; [|left; reflexivity].
  assert (Hz := decode_zshadow_rd B ly S W mem md TB_g_s (TB_g_s + TW.SZ_g_s) (8 * (x / 8)) HAR
    ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(rewrite EC in *; lia)
    ltac:(unfold TW.SZ_g_s; rewrite EC in *; lia) HZ).
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The memcpy's destination, one queue entry: addressable, with its shadow hull visible. *)
Lemma ssw_entry_ra : forall ly S (W : world segs) mem md j,
  trans_ssubmit_cells B -> @AR rc segs B ly S W mem md -> 0 <= j < 512 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (TB_g_s + 1760 + 32 * j) 32 /\
  shadow_hull_vis (aview segs (w_H W) mem) (TB_g_s + 1760 + 32 * j) 32.
Proof.
  intros ly S W mem md j HZ HAR Hj.
  assert (EC : TB_g_s = 6157888) by reflexivity.
  apply (decode_zshadow_ra B ly S W mem md TB_g_s (TB_g_s + TW.SZ_g_s) _ 32 HAR HZ ltac:(lia));
    unfold TW.SZ_g_s; rewrite EC; Z.div_mod_to_equations; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* acall_kept_g over a step, at any world                              *)
(* ------------------------------------------------------------------ *)

(* TransportGCg.v dk_kept_step_g with the step taken at a world WX, not the call's: the bytes the step may change
   lie in the call's stack window [slo, shi) (above alloc_ceiling) or in the written range Eo, a range of G. *)
Lemma ssw_kept_step : forall lyc Sc (W : world segs) memc mdc (WX : world segs) memX memY slo shi (Eo : Z -> Prop),
  AR_laws segs B -> gx_ok segs B G ->
  @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= slo -> (forall a, Eo a -> inG G a) ->
  acall_kept_g segs B G lyc Sc W memc WX memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ Eo a ->
     aview segs (w_H WX) memY a = aview segs (w_H WX) memX a) ->
  (forall a, apresent (w_H WX) memX a -> apresent (w_H WX) memY a) ->
  acall_kept_g segs B G lyc Sc W memc WX memY slo shi Eo.
Proof.
  intros lyc Sc W memc mdc WX memX memY slo shi Eo LAWS HGX HAR Hce HEG (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (GLOW : forall a, inG G a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite Hkp; [apply K1; assumption | lia | exact Hw |].
    intros HE. pose proof (GLOW a (HEG a HE)). lia.
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia | lia | exact Hn].
  - intros a Hi HnG Hno He. pose proof (transportb_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    rewrite Hkp; [apply K3; assumption | lia | lia | intros HE; exact (HnG (HEG a HE))].
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
    rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | lia | lia | exact Hn].
  - intros a Ha Hw Hp. apply Hgr. apply K5; assumption.
  - intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.

(* ------------------------------------------------------------------ *)
(* ssw_lite over a step                                                *)
(* ------------------------------------------------------------------ *)

(* A step that changes only its frame [sp - 48, sp) keeps ssw_lite at the same world Bc. *)
Lemma ssw_lite_step : forall c (WX : world segs) m m' Bc,
  ssw_rt -> ssw_ok c -> ssw_lite c WX m Bc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ssw_SP c - 48 <= a < ssw_SP c) ->
     aview segs (w_H WX) m' a = aview segs (w_H WX) m a) ->
  (forall a, apresent (w_H WX) m a -> apresent (w_H WX) m' a) ->
  ssw_lite c WX m' Bc.
Proof.
  intros c WX m m' Bc HRT HOK (KA & Hc & Hrd & Htw) Hkp Hgr.
  pose proof HRT as (_ & _ & LAWS & _ & HGX & _).
  pose proof (ssw_ok_stack c HOK) as (HAR & Hsp & Hce & _).
  pose proof (ssw_ok_cp c HRT HOK) as (Hc0 & Hc47 & Hcoff & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (ES : SSUBMIT_STK = 48 + Z.max ESTACK PBC.TRANS_BC_STK) by reflexivity.
  assert (EST : ESTACK = 4096) by reflexivity.
  assert (HSTK : 48 <= SSUBMIT_STK) by (rewrite ES; lia).
  assert (KC : forall a, cx_cp c <= a < cx_cp c + 32 -> aview segs (w_H WX) m' a = aview segs (w_H WX) m a)
    by (intros a Ha; apply Hkp; lia).
  split; [|split; [|split]].
  - apply (ssw_kept_step (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) WX m m' _ _ ssubmit_wr LAWS HGX HAR Hce
      ssw_wr_inG KA); [|exact Hgr].
    intros a Ha Hw _. apply Hkp; [exact Ha | lia].
  - apply (ssw_garr8_xfer (w_H WX) (w_H WX) m m'); [|exact Hc].
    intros i Hi. unfold TW.zs in Hi. rewrite List.length_map in Hi. destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
    rewrite HL in Hi. apply KC. lia.
  - apply (trans_rd_ok_view WX WX m m' _ _ Hrd KC). intros s Hs. apply Hkp; [unfold kLowMemEnd, kHighShadowEnd in *; lia|].
    unfold kLowMemEnd, kHighShadowEnd in *. lia.
  - apply (tw_kept TMAP_B (aview segs (w_H WX) m)); [exact Htw|].
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply Hkp; lia.
Qed.

(* A step that changes its frame and one field [s + off, s + off + n) of g_s inside ssubmit_wr, leaving there the
   n bytes of v: ssw_lite at the model world with the field written (TWorldG.v tw_write). *)
Lemma ssw_lite_store : forall c (WX : world segs) m m' Bc off (n : nat) v,
  ssw_rt -> ssw_ok c -> ssw_lite c WX m Bc ->
  0 <= off -> off + Z.of_nat n <= TW.SZ_g_s ->
  (forall a, TB_g_s + off <= a < TB_g_s + off + Z.of_nat n -> ssubmit_wr a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (ssw_SP c - 48 <= a < ssw_SP c) -> ~ (TB_g_s + off <= a < TB_g_s + off + Z.of_nat n) ->
     aview segs (w_H WX) m' a = aview segs (w_H WX) m a) ->
  (forall a, apresent (w_H WX) m a -> apresent (w_H WX) m' a) ->
  (forall j, (j < n)%nat -> aview segs (w_H WX) m' (TB_g_s + off + Z.of_nat j) = Some (YO0f.le_byte v n j)) ->
  ssw_lite c WX m' (TW.upd Bc (TW.OFF_g_s + off) (TW.put n v)).
Proof.
  intros c WX m m' Bc off n v HRT HOK (KA & Hc & Hrd & Htw) Hoff Hn Hwr Hkp Hgr Hval.
  pose proof HRT as (_ & _ & LAWS & _ & HGX & _).
  pose proof (ssw_ok_stack c HOK) as (HAR & Hsp & Hce & _).
  pose proof (ssw_ok_cp c HRT HOK) as (Hc0 & Hc47 & Hcoff & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (ES : SSUBMIT_STK = 48 + Z.max ESTACK PBC.TRANS_BC_STK) by reflexivity.
  assert (EST : ESTACK = 4096) by reflexivity.
  assert (HSTK : 48 <= SSUBMIT_STK) by (rewrite ES; lia).
  assert (EC : TB_g_s = 6157888) by reflexivity.
  assert (ESZ : TW.SZ_g_s = 18264) by reflexivity.
  assert (HnotG : forall x, cx_cp c <= x < cx_cp c + 32 -> ~ inG G x)
    by (intros x Hx; destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNG & _);
        exact (proj1 (HNG x ltac:(unfold SSUBMIT_CMD_LEN; lia)))).
  assert (KC : forall a, cx_cp c <= a < cx_cp c + 32 -> aview segs (w_H WX) m' a = aview segs (w_H WX) m a).
  { intros a Ha. apply Hkp; [lia | lia |]. intros Hf. apply (HnotG a Ha). apply ssw_gs_inG. lia. }
  split; [|split; [|split]].
  - apply (ssw_kept_step (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) WX m m' _ _ ssubmit_wr LAWS HGX HAR Hce
      ssw_wr_inG KA); [|exact Hgr].
    intros a Ha Hw Hnw. apply Hkp; [exact Ha | lia |]. intros Hf. exact (Hnw (Hwr a Hf)).
  - apply (ssw_garr8_xfer (w_H WX) (w_H WX) m m'); [|exact Hc].
    intros i Hi. unfold TW.zs in Hi. rewrite List.length_map in Hi. destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
    rewrite HL in Hi. apply KC. lia.
  - apply (trans_rd_ok_view WX WX m m' _ _ Hrd KC). intros s Hs.
    apply Hkp; unfold kLowMemEnd, kHighShadowEnd in *; lia.
  - apply (tw_write TMAP_B (aview segs (w_H WX) m) (aview segs (w_H WX) m') Bc TW.OFF_g_s TB_g_s TW.SZ_g_s off n v
      TMAP_B_ok Htw TMAP_B_g_s Hoff Hn).
    + exact Hval.
    + intros x Hx Hnx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply Hkp; [lia | lia | exact Hnx].
Qed.

(* __asan_memcpy of the command's 32 bytes into the queue entry j (gx_intrin_at's post): ssw_lite at the model world
   with the entry written (TWorldG.v tw_fill). The memcpy runs from sp - 48 with its ESTACK window below. *)
Lemma ssw_lite_cpy : forall c (WX : world segs) m m' Bc j,
  ssw_rt -> ssw_ok c -> ssw_lite c WX m Bc -> 0 <= j < 512 ->
  (forall i, 0 <= i < 32 -> aview segs (w_H WX) m' (TB_g_s + 1760 + 32 * j + i) =
     aview segs (w_H WX) m (cx_cp c + i)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_s + 1760 + 32 * j <= a < TB_g_s + 1760 + 32 * j + 32) ->
     ~ (ssw_SP c - 48 - ESTACK <= a < ssw_SP c - 48) ->
     aview segs (w_H WX) m' a = aview segs (w_H WX) m a) ->
  (forall a, apresent (w_H WX) m a -> apresent (w_H WX) m' a) ->
  ssw_lite c WX m' (TW.upd Bc (TW.OFF_g_s + (1760 + 32 * j)) (cx_C c)).
Proof.
  intros c WX m m' Bc j HRT HOK (KA & Hc & Hrd & Htw) Hj Hcpy Hkp Hgr.
  pose proof HRT as (_ & _ & LAWS & _ & HGX & _).
  pose proof (ssw_ok_stack c HOK) as (HAR & Hsp & Hce & _).
  pose proof (ssw_ok_cp c HRT HOK) as (Hc0 & Hc47 & Hcoff & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (ES : SSUBMIT_STK = 48 + Z.max ESTACK PBC.TRANS_BC_STK) by reflexivity.
  assert (EST : ESTACK = 4096) by reflexivity.
  assert (HSTK : 48 + ESTACK <= SSUBMIT_STK) by (rewrite ES; lia).
  assert (EC : TB_g_s = 6157888) by reflexivity.
  assert (HL : length (cx_C c) = 32%nat)
    by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _); exact HL).
  assert (HnotG : forall x, cx_cp c <= x < cx_cp c + 32 -> ~ inG G x)
    by (intros x Hx; destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNG & _);
        exact (proj1 (HNG x ltac:(unfold SSUBMIT_CMD_LEN; lia)))).
  assert (KC : forall a, cx_cp c <= a < cx_cp c + 32 -> aview segs (w_H WX) m' a = aview segs (w_H WX) m a).
  { intros a Ha. apply Hkp; [lia | | lia]. intros Hf. apply (HnotG a Ha). apply ssw_gs_inG. unfold TW.SZ_g_s. lia. }
  assert (Hwr : forall a, TB_g_s + 1760 + 32 * j <= a < TB_g_s + 1760 + 32 * j + 32 -> ssubmit_wr a).
  { intros a Ha. right. right. right. exists j. split; [unfold TW.S_queue_N; lia|].
    unfold twb_fld, TW.A_S_queue_bytes, TW.S_queue_ESZ, TW.OFF_g_s. lia. }
  split; [|split; [|split]].
  - apply (ssw_kept_step (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) WX m m' _ _ ssubmit_wr LAWS HGX HAR Hce
      ssw_wr_inG KA); [|exact Hgr].
    intros a Ha Hw Hnw. apply Hkp; [exact Ha | intros Hf; exact (Hnw (Hwr a Hf)) | lia].
  - apply (ssw_garr8_xfer (w_H WX) (w_H WX) m m'); [|exact Hc].
    intros i Hi. unfold TW.zs in Hi. rewrite List.length_map, HL in Hi. apply KC. lia.
  - apply (trans_rd_ok_view WX WX m m' _ _ Hrd KC). intros s Hs.
    apply Hkp; unfold kLowMemEnd, kHighShadowEnd in *; lia.
  - apply (tw_fill TMAP_B (aview segs (w_H WX) m) (aview segs (w_H WX) m') Bc TW.OFF_g_s TB_g_s TW.SZ_g_s
      (1760 + 32 * j) (cx_C c) TMAP_B_ok Htw TMAP_B_g_s ltac:(lia) ltac:(rewrite HL; unfold TW.SZ_g_s; lia)).
    + intros i Hi. rewrite HL in Hi. replace (TB_g_s + (1760 + 32 * j) + i) with (TB_g_s + 1760 + 32 * j + i) by lia.
      rewrite (Hcpy i ltac:(lia)). rewrite (ssw_garr8_aview (w_H WX) m (cx_cp c) (TW.zs (cx_C c)) i Hc)
        by (unfold TW.zs; rewrite List.length_map, HL; lia).
      unfold TW.zs. rewrite (map_nth (fun b : byte => bv_unsigned b) (cx_C c) (Z_to_bv 8 0)). reflexivity.
    + intros x Hx Hnx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      rewrite HL in Hnx. apply Hkp; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The post                                                            *)
(* ------------------------------------------------------------------ *)

(* aregs_preserved from the fifteen callee-saved registers one by one. *)
Lemma ssw_aregs_of : forall regs regsF,
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
     YK11.getr regsF (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  aregs_preserved regs regsF.
Proof.
  intros regs regsF H r Hr. apply H. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; cbn [In]; [tauto | tauto | tauto | tauto | tauto |].
  assert (E : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct E as [-> | E]; [tauto |]). subst r. tauto.
Qed.

(* The post at the return, from the walk's last facts. *)
Lemma ssw_close : forall c lyX SX (WX : world segs) regsF mF mdF,
  ssw_rt -> ssw_ok c ->
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    (cx_own c) lyX SX WX mF mdF (cx_k c) ->
  frames SX = frames (cx_Sc c) -> Permutation (ablocks B lyX SX) (ablocks B (cx_lyc c) (cx_Sc c)) ->
  mo_le MT (cx_Sc c) SX 0 ->
  acall_kept_g segs B G (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) WX mF
    (ssw_SP c - SSUBMIT_STK) (ssw_SP c) ssubmit_wr ->
  aregs_preserved (cx_regs c) regsF -> YK11.getr regsF 1 = YK11.getr (cx_regs c) 1 ->
  YK11.getr regsF 10 = w64 (cx_r c) ->
  tw_at TMAP_B (aview segs (w_H WX) mF) (cx_Bw' c) ->
  forall mat, ssw_post c WX
    (mkCfg (@YK11.mkst fx regsF (v_jalr (YK11.getr regsF 1) 0) mF (YK11.seg_rom segs))
      (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
  intros c lyX SX WX regsF mF mdF HRT HOK HJF Hfr Hperm Hmo KA HP RF1 RF10 Htw mat.
  pose proof HRT as (_ & _ & LAWS & _).
  assert (Hra : YK0s.ret_ok (YK11.getr (cx_regs c) 1)) by (destruct HOK as (_ & Hra & _); exact Hra).
  unfold ssw_post, transport_ssubmit_post, transport_cg_post.
  exists lyX, SX, regsF, mF, (with_vm_backing (m_vm_lazy mdF) mat mdF), 0.
  split.
  { rewrite RF1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [unfold SSUBMIT_EV; lia|].
  split; [rewrite Z.add_0_r; apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJF|].
  split; [exact HP|].
  split; [exact Hfr|].
  split; [exact Hperm|].
  split; [exact KA|].
  split; [exact Hmo|].
  split; [exact RF10 | exact Htw].
Qed.

(* ------------------------------------------------------------------ *)
(* The command's bytes and the call of diginet_body_check             *)
(* ------------------------------------------------------------------ *)

(* n bytes of the command at offset k, as its little-endian value (TWorld.v u_at). *)
Lemma ssw_garr8_u : forall (mm : word -> option byte) b (C : list byte) k (n : nat),
  garr8 segs mm b (TW.zs C) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length C) ->
  val_mem segs mm (b + k) n (TW.u_at C k n).
Proof.
  intros mm b C k n Hg Hk Hkn kk Hkk.
  assert (Hl : (Z.to_nat k + kk < length C)%nat) by lia.
  pose proof (garr8_mbyte segs mm b (TW.zs C) (Z.to_nat k + kk) Hg ltac:(unfold TW.zs; rewrite List.length_map; exact Hl)) as Hm.
  replace (b + Z.of_nat (Z.to_nat k + kk)) with (b + k + Z.of_nat kk) in Hm by lia. rewrite Hm. f_equal. f_equal.
  unfold TW.u_at. assert (LS : length (TW.sub C k n) = n) by (apply TWL.length_sub; lia).
  rewrite <- LS at 2. rewrite (tw_le_byte_ble (TW.sub C k n) kk (Z_to_bv 8 0)) by lia.
  rewrite (tw_nth_sub C k n kk (Z_to_bv 8 0) Hk Hkk Hl).
  unfold TW.zs. rewrite (map_nth (fun x : byte => bv_unsigned x) C (Z_to_bv 8 0)). reflexivity.
Qed.

Lemma ssw_garr8_firstn : forall (mm : word -> option byte) b (l : list Z) n,
  garr8 segs mm b l -> garr8 segs mm b (firstn n l).
Proof.
  intros mm b l n Hg j Hj. rewrite length_firstn in Hj.
  rewrite nth_firstn. destruct (Nat.ltb_spec j n) as [_|]; [|lia]. apply Hg. lia.
Qed.

(* trans_src_ok at another memory of the same state: the placements do not read memory, decode_rd_ok does. *)
Lemma ssw_src_rd : forall lyc Sc (W : world segs) memc m q n,
  trans_src_ok B lyc Sc W memc q n -> decode_rd_ok W m q n -> trans_src_ok B lyc Sc W m q n.
Proof.
  intros lyc Sc W memc m q n [Hb | (HL & _)] Hrd; [left; exact Hb | right; exact (conj HL Hrd)].
Qed.

(* DgnTransportBCg.v trans_src_ok_acall_g for a range outside G and outside TRANS_RO_RD (so without the record
   facts trans_ro_rd_unowned / trans_rom_no_errno): a heap block by the block clause, a side-stack frame by the
   frame clause, the machine stack by the clause above alloc_ceiling outside the callee's window. *)
Lemma ssw_src_acall : AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) ->
  (forall a, q <= a < q + n -> ~ inG G a /\ ~ trans_in_ro_rd a) ->
  trans_src_ok B lyc Sc W memc q n -> 0 < n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hperm Hfr Hfa Elo Ehi
    (K1 & K2 & K3 & K4 & _) HnE HnEs Hoff HnGR Hs Hn.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
  { intros cid pos s Hin Hs'. apply (K4 cid pos s Hin (or_intror Hs')). apply HnEs.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs'. cbn [fst snd] in Hs'.
    unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
    - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
      + apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
      + exfalso. exact (proj1 (HnGR a Ha) (HG a Ha)).
      + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2]. apply K1; lia.
      + exfalso. exact (proj2 (HnGR a Ha) (HR a Ha)). }
  split; [|exact KV].
  exact (trans_src_ok_kept B LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q n HAR HAR2 Hperm Hfr Hfa Elo Ehi KV KS Hs Hn).
Qed.

(* Two journals from the same start: the frames and the machine stack of their call states are at the same
   addresses (YG0f.v layout_le fixes ly_F, ly_stk_lo, ly_stk_hi). *)
Lemma ssw_ly_same : forall c lyX SX (WX : world segs) m md k',
  ssw_ok c ->
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    (cx_own c) lyX SX WX m md k' ->
  (forall cid pos, frame_addr lyX cid pos = frame_addr (cx_lyc c) cid pos) /\
  ly_stk_lo lyX = ly_stk_lo (cx_lyc c) /\ ly_stk_hi lyX = ly_stk_hi (cx_lyc c).
Proof.
  intros c lyX SX WX m md k' HOK HJX. destruct HOK as (HJ & _).
  destruct HJ as (_ & _ & (memS & HJi & _) & _). destruct HJX as (_ & _ & (memS' & HJi' & _) & _).
  pose proof HJi as (_ & Hly & _). pose proof HJi' as (_ & Hly' & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
  destruct Hly' as (_ & _ & _ & _ & _ & EF' & _ & _ & _ & Elo' & Ehi' & _).
  split; [|split; [congruence | congruence]].
  intros cid pos. unfold frame_addr. rewrite EF, EF'. reflexivity.
Qed.

End ssw.
