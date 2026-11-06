(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module paths, module names and numbers changed; 259 of its 315 lines of code are new or changed and 387 lines of the source are left out. *)
(* receive_seg_cut: the cuts of the walk of receive (fuzz_transport.asan 0x837d0 = transport_sigma TS_receive,
   AF_receive = 0x256c of lib/A/Prog/DgnTransportList.v, 281 words), as STATEMENTS only, and the composition
   recv_holds_of: the walk from the entry (recv_entry_at) from the piece Props. The walk holds the CALLER's G journal
   (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS 0 []) from the entry to the tail jump; from the malloc's return on, the
   journal is at k + 1 events and the blocks are the caller's with the frame's block (a, max (n, 1)) added. Offsets
   are from the listing's base (BASE + 0x256c = 0x837d0); every cut is at an instruction that is not a call. The
   pieces, in pc order:
     head  +0x000 .. +0x044  `addi sp, sp, -64`, the seven saves (ra, s0 .. s5 at sp + 56 .. sp + 8), s1 = a3, s3 = a2,
                             s2 = a1 = n, s4 = a0 = p, s5 = the shadow base through its GOT word and cell
                             (transport_cells), a0 = n + (n = 0) = max (n, 1), `jal` the malloc wrapper (+0x044;
                             YC5d.v amalloc04_rule inside the G journal: YC85.v amalloc04_sub, TransportGCg.v gx_open /
                             gx_pack0; the trace of receive_cg.v trans_recv_uctx's first conjunct, the entry chain).
                             Ends at the mal cut. Prop: recv_head_stmt.
     cpy   +0x048 .. +0x060  `beqz a0` not taken (4096 <= a), s0 = a, `beqz s2` (n = 0 skips the copy), the arguments
                             and `jal __asan_memcpy` (+0x060; TransportGCg.v gx_intrin_at OCpy: the destination is the
                             new block, the source [p, p + n) by trans_src_ok at the call state). Ends at the opb cut.
                             Prop: recv_cpy_stmt.
     opb   +0x064 .. +0x0a8  s4 = &OW, the two `jal __asan_memset` (+0x078: OW, 0, 304; +0x08c: GOT, 0, 224;
                             gx_intrin_at OSet into G), the load of g_fail_next, the stores of -1 at OW + 232 and of
                             g_fail_next at M + 88 (op_begin, TCb.v op_begin_m). Ends at the rf cut. Prop: recv_opb_stmt.
     rf    +0x0ac .. +0x148, +0x2a4 .. +0x31c
                             the tests of spec_read_frame on the frame's bytes (the instrumented checks of the 1-byte
                             loads at a + 12 .. a + 15 and a + 18 .. a + 21: the block's first n bytes are usable), the
                             store of the send value at g_rx_send (recv_send), `beqz s3` (+0x148): by_poll <> 0 goes to
                             the poll cut, by_poll = 0 to the mrx cut. Prop: recv_rf_stmt.
     poll  +0x14c .. +0x244, +0x320 .. +0x398
                             got = min (n, 1514), the same tests on the first got bytes, the stores of the send value,
                             got, a, the times and fails values (recv_w2c), `jal diginet_session_poll` (+0x238), the
                             stores of 0 at g_rx and g_rx_fail, `j` the set cut. Prop: recv_poll_stmt.
     mrx   +0x248 .. +0x270  `jal m_rx` (+0x250), s1 = its result, the load of g_now, `jal diginet_session_rx`
                             (+0x270), the set cut. Prop: recv_mrx_stmt.
     set   +0x274 .. +0x2a0  a0 = s1, `jal settle` (+0x278; a donor-form callee through TransportGCg.v gx_call_cg),
                             a0 = a, the seven reloads, `addi sp, sp, 64`, the tail jump to the free wrapper (+0x2a0;
                             YC5d.v afree04_rule inside the G journal: YC85.v afree04_sub; the trace of
                             trans_recv_uctx's second conjunct, the entry chain), whose return is receive's. The post.
                             Prop: recv_set_stmt.
     inv   no code: the model facts that the run invariants hold at the worlds the code hands its callees and at the
                     world it hands settle (recv_inv_stmt).
   Each cut holds the caller's facts (recv_fix: the premises of receive_cg.v transport_receive_cg at the entry, the
   bounds g_ncmd <= CMDS_MAX and S_queued <= QUEUE_MAX that keep invariants (2) and (4) inside their arrays, and the
   two trace facts of the context), what every cut after the malloc carries (recv_cur: the journal, the frames, the
   blocks, the meter, what the call kept so far over the statement's window and written range, the seven saved words,
   4096 <= a), the model's result at the malloc's address (recv_res), the per-cut facts (the world relation at the
   cut's model world, the frame's bytes in the block, the path) and the registers the code after the cut reads
   (recv_regs_keep and its extensions: s6 .. s11 are never saved, so every cut keeps them). *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_inflight_settle_cg check_latest_queue_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import settle_cg diginet_session_poll_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TOps TRunInv.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The cut points, the saved words                                     *)
(* ------------------------------------------------------------------ *)

(* The cut points, as offsets from the listing's base: mal `beqz a0` (+0x048, the malloc's return), opb the PHi of
   &OW (+0x064, the memcpy's return or the skip), rf `bltu s2, a2` (+0x0ac, after op_begin), poll `addi a0, zero,
   0x5ea` (+0x14c, by_poll <> 0), mrx `mv a0, s0` (+0x248, by_poll = 0), set `mv a0, s1` (+0x274, the join). *)
Definition RECV_MAL : Z := AF_receive + 0x48.
Definition RECV_OPB : Z := AF_receive + 0x64.
Definition RECV_RF : Z := AF_receive + 0xac.
Definition RECV_POLL : Z := AF_receive + 0x14c.
Definition RECV_MRX : Z := AF_receive + 0x248.
Definition RECV_SET : Z := AF_receive + 0x274.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2, s3, s4, s5 (sd at sp + 56
   .. sp + 8 after `addi sp, sp, -64`). *)
Definition RECV_SAVED : list (Z * Z) := [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21)].
(* a2 at the poll cut: the PHi of g_rx_send (+0x140), whose low part -0x530 the by-poll store at +0x1fc adds again. *)
Definition RECV_RXS_HI : Z := TA_g_rx_send + 0x530.

(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma recv_some_inv : forall (Bx By : list byte) (x y : Z), Some (Bx, x) = Some (By, y) -> Bx = By /\ x = y.
Proof.
  intros Bx By x y H. split.
  - exact (f_equal (fun o : option (list byte * Z) => match o with Some (b, _) => b | None => Bx end) H).
  - exact (f_equal (fun o : option (list byte * Z) => match o with Some (_, v) => v | None => x end) H).
Qed.
Lemma recv_some_inv_u : forall (Bx By : list byte), Some (Bx, tt) = Some (By, tt) -> Bx = By.
Proof.
  intros Bx By H. exact (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bx end) H).
Qed.

(* ------------------------------------------------------------------ *)
(* The model piece                                                    *)
(* ------------------------------------------------------------------ *)

(* The run invariants the callees ask for (receive_cg.v's premises (1), (2), (4), (5)) with the two index bounds
   that keep (2) and (4) inside g_s.queue[] and g_cmd[] are lib/TModel/TRunInv.v run_inv. The model piece: they hold
   at the world receive hands diginet_session_poll (recv_w2c) and m_rx (recv_w2), at the world m_rx_m leaves
   (diginet_session_rx's), and at the world settle is handed on each path (after diginet_session_rx_m, and after
   diginet_session_poll_m and the two stores of 0 at g_rx and g_rx_fail). *)
Definition recv_inv_stmt : Prop :=
  (forall Bw bytes, length Bw = Z.to_nat TW.W_LEN -> TRunInv.run_inv Bw -> TRunInv.run_inv (recv_w2 Bw bytes)) /\
  (forall Bw bytes a pf, length Bw = Z.to_nat TW.W_LEN -> TRunInv.run_inv Bw ->
     TRunInv.run_inv (recv_w2c Bw bytes a pf)) /\
  (forall Bw bytes F n Bx t, length Bw = Z.to_nat TW.W_LEN -> TRunInv.run_inv Bw ->
     TC.m_rx_m timg_A F (recv_w2 Bw bytes) n = Some (Bx, t) -> TRunInv.run_inv Bx) /\
  (forall F Bx b now By r, length Bx = Z.to_nat TW.W_LEN -> TRunInv.run_inv Bx ->
     TSS.diginet_session_rx_m timg_A F Bx b now = Some (By, r) -> TRunInv.run_inv By) /\
  (forall Bw bytes a pf F B2d r, length Bw = Z.to_nat TW.W_LEN -> TRunInv.run_inv Bw ->
     TSS.diginet_session_poll_m timg_A F (recv_w2c Bw bytes a pf) 0 = Some (B2d, r) ->
     TRunInv.run_inv (TW.set_g_rx_fail (TW.set_g_rx B2d 0) 0)).

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma recv_cut_pcs :
  BASE + AF_receive = transport_sigma TS_receive /\
  BASE + RECV_MAL = 0x83818 /\ BASE + RECV_OPB = 0x83834 /\ BASE + RECV_RF = 0x8387c /\
  BASE + RECV_POLL = 0x8391c /\ BASE + RECV_MRX = 0x83a18 /\ BASE + RECV_SET = 0x83a44.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_receive_cg_holds_stmt that are not callee
   contracts and not the context's trace facts, with gx_ok / gx_noerrno (DgnTransportCg.v G_HARNESS_gx_ok /
   G_HARNESS_gx_noerrno from trans_g_unowned / trans_g_no_errno). *)
Definition recv_laws : Prop :=
  pc_wrap_malloc (as_code B) = transport_sigma TS___interceptor_trampoline_malloc /\
  pc_wrap_free (as_code B) = transport_sigma TS___interceptor_trampoline_free /\
  transport_cells B /\ trans_recv_cells B /\
  trans_g_unowned B /\ trans_g_no_errno B /\ trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\
  gx_ok segs B TG.G_HARNESS /\ gx_noerrno B TG.G_HARNESS.

(* The callee contracts of the holds statement, in its order. *)
Definition recv_calls : Prop :=
  (forall fx' : YK11.FPState, @amalloc04_rule fx' rc tfib_sink_head segs B MT) /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) /\
  (forall fx' : YK11.FPState,
     @transport_diginet_session_poll_cg fx' rc B MT (transport_sigma TS_diginet_session_poll)) /\
  (forall fx' : YK11.FPState, @transport_m_rx_cg fx' rc B MT (transport_sigma TS_m_rx)) /\
  (forall fx' : YK11.FPState,
     @transport_diginet_session_rx_cg fx' rc B MT (transport_sigma TS_diginet_session_rx)) /\
  (forall fx' : YK11.FPState, @transport_settle_cg fx' rc B MT (transport_sigma TS_settle)) /\
  (forall fx' : YK11.FPState, @afree04_rule fx' rc tfib_sink_head segs B MT).

(* The caller's facts: the premises of transport_receive_cg at the entry registers regs, the run invariants with the
   two index bounds (TRunInv.v run_inv) in place of the statement's invariant premises, and the trace facts of the
   context raZ regs :: spine ch (receive_cg.v trans_recv_uctx at it). *)
Definition recv_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (p by_poll pf T : Z) (bytes Bw : list byte) (ch : list (Z * Z * Z)) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 p /\ YK11.getr regs 11 = w64 (Z.of_nat (length bytes)) /\
  YK11.getr regs 12 = w64 by_poll /\ bv_unsigned (YK11.getr regs 13) mod 2 ^ 32 = pf /\
  @achain rc lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - RECV_STK /\ spZ regs <= sp0 /\
  - 2 ^ 31 <= by_poll < 2 ^ 31 /\ 0 <= pf < 2 ^ 32 /\ Z.of_nat (length bytes) <= 65535 /\
  garr8 segs (mrestrict (w_H W) memc) p (TW.zs bytes) /\
  ((0 < length bytes)%nat ->
     trans_src_ok B lyc Sc W memc p (Z.of_nat (length bytes)) /\
     decode_off_win regs RECV_STK p (Z.of_nat (length bytes))) /\
  tw_at TMAP_A (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  (forall a, recv_addr_ok a -> TOP.receive_m timg_A Bw a bytes by_poll pf <> None) /\
  trans_rom_view_rd W memc /\
  TRunInv.run_inv Bw /\
  recv_dn_each timg_A Bw bytes by_poll pf /\
  count_cid POLL_CID (frames Sc) + 1 < fs_frames POLL_CID /\
  count_cid SRX_CID (frames Sc) < fs_frames SRX_CID /\
  count_cid ONANN_CID (frames Sc) < fs_frames ONANN_CID /\
  count_cid SENDDATA_CID (frames Sc) < fs_frames SENDDATA_CID /\
  count_cid ONDATA_CID (frames Sc) + 2 < fs_frames ONDATA_CID /\
  st_nev S + k + RECV_EV <= EV_MAX /\ blocks_bytes Sc + RECV_LIVE <= LIVE_MAX /\
  mo_ok MT Sc T /\ recv_cost MT (Z.of_nat (length bytes)) <= T /\
  In (decode_utrace (pc_malloc_ra0 (as_code B)) (RECV_RA_MALLOC :: spine ch)) (as_universe B) /\
  In (decode_utrace (pc_free_ra0 (as_code B)) (raZ regs :: spine ch)) (as_universe B).

(* What every cut after the malloc carries, at the current state (ly2, S2, W2, mem2, md2): the caller's G journal at
   k + 1 events (the malloc's; the callees record none); the caller's frames; the caller's blocks with the frame's
   block (a, max (n, 1)) added; the meter charged the malloc; what the call has kept so far (acall_kept_g over the
   statement's window and written range recv_wr bytes); the seven saved words below the entry sp; 4096 <= a. *)
Definition recv_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (bytes : list byte) (a : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + 1) /\
  frames S2 = frames Sc /\
  Permutation (ablocks B ly2 S2) ((a, Z.max 1 (Z.of_nat (length bytes))) :: ablocks B lyc Sc) /\
  mo_le MT Sc S2 (mo_malloc MT (Z.max 1 (Z.of_nat (length bytes)))) /\
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 (spZ regs - RECV_STK) (spZ regs) (recv_wr bytes) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) RECV_SAVED /\
  4096 <= a.

(* The model's result at the address the malloc returned. *)
Definition recv_res (Bw : list byte) (bytes : list byte) (by_poll pf a : Z) (Bw' : list byte) : Prop :=
  recv_addr_ok a /\ TOP.receive_m timg_A Bw a bytes by_poll pf = Some (Bw', tt).

(* The bytes at p, read through the current memory, and their placement at the current state, apart from the block. *)
Definition recv_src (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte)
    (p : Z) (bytes : list byte) (a : Z) : Prop :=
  garr8 segs (mrestrict (w_H W2) mem2) p (TW.zs bytes) /\
  ((0 < length bytes)%nat ->
     trans_src_ok B ly2 S2 W2 mem2 p (Z.of_nat (length bytes)) /\
     (p + Z.of_nat (length bytes) <= a \/ a + Z.max 1 (Z.of_nat (length bytes)) <= p)).

(* The frame's bytes in the block, after the copy. *)
Definition recv_blk (W2 : world segs) (mem2 : word -> option byte) (a : Z) (bytes : list byte) : Prop :=
  garr8 segs (mrestrict (w_H W2) mem2) a (TW.zs bytes).

(* The registers every cut keeps: sp = the entry sp - 64, gp, tp, and s6 .. s11 (never saved, so kept to the end). *)
Definition recv_regs_keep (regs regs2 : bvmap 5 word) : Prop :=
  YK11.getr regs2 2 = w64 (spZ regs - RECV_FRAME) /\
  YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 22 = YK11.getr regs 22 /\ YK11.getr regs2 23 = YK11.getr regs 23 /\
  YK11.getr regs2 24 = YK11.getr regs 24 /\ YK11.getr regs2 25 = YK11.getr regs 25 /\
  YK11.getr regs2 26 = YK11.getr regs 26 /\ YK11.getr regs2 27 = YK11.getr regs 27.
(* The mal cut: s0 still the caller's, s1 = a3, s2 = n, s3 = by_poll, s4 = p, s5 = the shadow base, a0 = a. *)
Definition recv_regs_mal (regs regs2 : bvmap 5 word) (p by_poll a : Z) (bytes : list byte) : Prop :=
  recv_regs_keep regs regs2 /\
  YK11.getr regs2 8 = YK11.getr regs 8 /\ YK11.getr regs2 9 = YK11.getr regs 13 /\
  YK11.getr regs2 18 = w64 (Z.of_nat (length bytes)) /\ YK11.getr regs2 19 = w64 by_poll /\
  YK11.getr regs2 20 = w64 p /\ YK11.getr regs2 21 = w64 SHADOW_OFF /\ YK11.getr regs2 10 = w64 a.
(* The opb and rf cuts: s0 = a, s1 = a3, s2 = n, s3 = by_poll, s5 = the shadow base. *)
Definition recv_regs_opb (regs regs2 : bvmap 5 word) (by_poll a : Z) (bytes : list byte) : Prop :=
  recv_regs_keep regs regs2 /\
  YK11.getr regs2 8 = w64 a /\ YK11.getr regs2 9 = YK11.getr regs 13 /\
  YK11.getr regs2 18 = w64 (Z.of_nat (length bytes)) /\ YK11.getr regs2 19 = w64 by_poll /\
  YK11.getr regs2 21 = w64 SHADOW_OFF.
(* The rf cut adds a2 = 30 (`addi a2, zero, 0x1e` at +0x0a4, read by `bltu s2, a2` at the cut). *)
Definition recv_regs_rf (regs regs2 : bvmap 5 word) (by_poll a : Z) (bytes : list byte) : Prop :=
  recv_regs_opb regs regs2 by_poll a bytes /\ YK11.getr regs2 12 = w64 30.
(* The poll cut adds a2 = the PHi of g_rx_send. *)
Definition recv_regs_poll (regs regs2 : bvmap 5 word) (by_poll a : Z) (bytes : list byte) : Prop :=
  recv_regs_opb regs regs2 by_poll a bytes /\ YK11.getr regs2 12 = w64 RECV_RXS_HI.
(* The mrx cut: s0 = a, s2 = n. *)
Definition recv_regs_mrx (regs regs2 : bvmap 5 word) (a : Z) (bytes : list byte) : Prop :=
  recv_regs_keep regs regs2 /\
  YK11.getr regs2 8 = w64 a /\ YK11.getr regs2 18 = w64 (Z.of_nat (length bytes)).
(* The set cut: s0 = a, s1 = ticked. *)
Definition recv_regs_set (regs regs2 : bvmap 5 word) (a ticked : Z) : Prop :=
  recv_regs_keep regs regs2 /\ YK11.getr regs2 8 = w64 a /\ YK11.getr regs2 9 = w64 ticked.

(* The post of the call, at the entry registers regs. *)
Local Abbreviation POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf :=
  (@transport_recv_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).
(* The machine state at a cut pc. *)
Local Abbreviation CFG pc regs2 mem2 md2 :=
  (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + pc)) mem2 (YK11.seg_rom segs)) md2).

(* The entry: from the caller's facts, the post. *)
Definition recv_entry_at : Prop :=
  recv_laws -> recv_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p by_poll pf T : Z)
         (bytes Bw : list byte) (ch : list (Z * Z * Z)),
    recv_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
    SRr segs W (@cfg_at fx segs (transport_sigma TS_receive) regs memc mdc)
      (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).

(* The mal cut, +0x048: the malloc returned a; the bytes at p and their placement at the current state; the memory
   relates to Bw. *)
Definition recv_mal_at : Prop :=
  recv_laws -> recv_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p by_poll pf T : Z)
         (bytes Bw : list byte) (ch : list (Z * Z * Z)) (a : Z) (Bw' : list byte)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
         (regs2 : bvmap 5 word),
    recv_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
    recv_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
    recv_res Bw bytes by_poll pf a Bw' ->
    recv_src ly2 S2 W2 mem2 p bytes a ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) Bw ->
    recv_regs_mal regs regs2 p by_poll a bytes ->
    SRr segs W2 (CFG RECV_MAL regs2 mem2 md2)
      (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).

(* The opb cut, +0x064: the frame's bytes are in the block; the memory relates to Bw. *)
Definition recv_opb_at : Prop :=
  recv_laws -> recv_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p by_poll pf T : Z)
         (bytes Bw : list byte) (ch : list (Z * Z * Z)) (a : Z) (Bw' : list byte)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
         (regs2 : bvmap 5 word),
    recv_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
    recv_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
    recv_res Bw bytes by_poll pf a Bw' ->
    recv_blk W2 mem2 a bytes ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) Bw ->
    recv_regs_opb regs regs2 by_poll a bytes ->
    SRr segs W2 (CFG RECV_OPB regs2 mem2 md2)
      (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).

(* The rf cut, +0x0ac: after op_begin, the memory relates to recv_w1 Bw. *)
Definition recv_rf_at : Prop :=
  recv_laws -> recv_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p by_poll pf T : Z)
         (bytes Bw : list byte) (ch : list (Z * Z * Z)) (a : Z) (Bw' : list byte)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
         (regs2 : bvmap 5 word),
    recv_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
    recv_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
    recv_res Bw bytes by_poll pf a Bw' ->
    recv_blk W2 mem2 a bytes ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) (recv_w1 Bw) ->
    recv_regs_rf regs regs2 by_poll a bytes ->
    SRr segs W2 (CFG RECV_RF regs2 mem2 md2)
      (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).

(* The poll cut, +0x14c: by_poll <> 0; the memory relates to recv_w2 Bw bytes (g_rx_send stored). *)
Definition recv_poll_at : Prop :=
  recv_laws -> recv_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p by_poll pf T : Z)
         (bytes Bw : list byte) (ch : list (Z * Z * Z)) (a : Z) (Bw' : list byte)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
         (regs2 : bvmap 5 word),
    recv_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
    recv_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
    recv_res Bw bytes by_poll pf a Bw' ->
    recv_blk W2 mem2 a bytes ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) (recv_w2 Bw bytes) ->
    by_poll <> 0 ->
    recv_regs_poll regs regs2 by_poll a bytes ->
    SRr segs W2 (CFG RECV_POLL regs2 mem2 md2)
      (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).

(* The mrx cut, +0x248: by_poll = 0; the memory relates to recv_w2 Bw bytes. *)
Definition recv_mrx_at : Prop :=
  recv_laws -> recv_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p by_poll pf T : Z)
         (bytes Bw : list byte) (ch : list (Z * Z * Z)) (a : Z) (Bw' : list byte)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
         (regs2 : bvmap 5 word),
    recv_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
    recv_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
    recv_res Bw bytes by_poll pf a Bw' ->
    recv_blk W2 mem2 a bytes ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) (recv_w2 Bw bytes) ->
    by_poll = 0 ->
    recv_regs_mrx regs regs2 a bytes ->
    SRr segs W2 (CFG RECV_MRX regs2 mem2 md2)
      (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).

(* The set cut, +0x274: the memory relates to B3, the world settle is handed (on the by-poll path the world after
   diginet_session_poll_m and the two stores of 0, else the world diginet_session_rx_m leaves), the invariants and
   g_fail_next <= 1 at B3, settle_m at B3 and ticked is the model's last step, and ticked is 0 or 1. *)
Definition recv_set_at : Prop :=
  recv_laws -> recv_calls ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p by_poll pf T : Z)
         (bytes Bw : list byte) (ch : list (Z * Z * Z)) (a : Z) (Bw' : list byte)
         (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
         (regs2 : bvmap 5 word) (B3 : list byte) (ticked : Z),
    recv_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch ->
    recv_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bytes a ly2 S2 W2 mem2 md2 ->
    recv_res Bw bytes by_poll pf a Bw' ->
    tw_at TMAP_A (aview segs (w_H W2) mem2) B3 -> TW.g_fail_next B3 <= 1 -> TRunInv.run_inv B3 ->
    TC.settle_m B3 ticked = Some (Bw', tt) -> 0 <= ticked <= 1 ->
    recv_regs_set regs regs2 a ticked ->
    SRr segs W2 (CFG RECV_SET regs2 mem2 md2)
      (POST STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw bytes by_poll pf).

(* Each piece: the cut Props it ends in give its own cut (or, for the head, the entry). *)
Definition recv_head_stmt : Prop := recv_mal_at -> recv_entry_at.
Definition recv_cpy_stmt : Prop := recv_opb_at -> recv_mal_at.
Definition recv_opb_stmt : Prop := recv_rf_at -> recv_opb_at.
Definition recv_rf_stmt : Prop := recv_poll_at -> recv_mrx_at -> recv_rf_at.
Definition recv_poll_stmt : Prop := recv_inv_stmt -> recv_set_at -> recv_poll_at.
Definition recv_mrx_stmt : Prop := recv_inv_stmt -> recv_set_at -> recv_mrx_at.
Definition recv_set_stmt : Prop := recv_set_at.

(* The walk from its pieces. *)
Theorem recv_holds_of :
  recv_head_stmt -> recv_cpy_stmt -> recv_opb_stmt -> recv_rf_stmt -> recv_poll_stmt -> recv_mrx_stmt ->
  recv_set_stmt -> recv_inv_stmt -> recv_entry_at.
Proof.
  intros HEAD CPY OPB RF POLL MRX SET INV.
  exact (HEAD (CPY (OPB (RF (POLL INV SET) (MRX INV SET))))).
Qed.

(* The statement from the entry walk: the record facts give recv_laws (gx_ok / gx_noerrno by G_HARNESS_gx_ok /
   G_HARNESS_gx_noerrno), the callee contracts recv_calls, and the contract's premises with trans_recv_uctx at the
   context raZ regs :: spine ch give recv_fix. *)
Lemma recv_top : recv_entry_at -> forall CTX : list (list Z), @transport_receive_cg_holds_stmt fx rc B MT CTX.
Proof.
  intros ENTRY CTX HMPC HFPC HCELLS HRC HGU HGE HRU HRE LAWS MTL HU AM MCPY MSET POLL MRX RX SET AF.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch
    HJ Hret Hra4 Hgp Htp H10 H11 H12 H13 Hch HinC Hal Hwlo Hwhi Hbp Hpf Hn Hgarr Hsrc Htw Hgf Hmodel Hrom
    I1 I2 I2b I4 I4b I5a I5b Hdn C1 C2 C3 C4 C5 Hnev Hlive Hmo Hcost.
  destruct (HU _ HinC) as [Htm Htf].
  apply (ENTRY
    (conj HMPC (conj HFPC (conj HCELLS (conj HRC (conj HGU (conj HGE (conj HRU (conj HRE (conj LAWS (conj MTL
      (conj (G_HARNESS_gx_ok B HGU) (G_HARNESS_gx_noerrno B HGE))))))))))))
    (conj AM (conj MCPY (conj MSET (conj POLL (conj MRX (conj RX (conj SET AF)))))))
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch).
  unfold recv_fix.
  split; [exact HJ|]. split; [exact Hret|]. split; [exact Hra4|]. split; [exact Hgp|]. split; [exact Htp|].
  split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13|]. split; [exact Hch|].
  split; [exact Hal|]. split; [exact Hwlo|]. split; [exact Hwhi|]. split; [exact Hbp|]. split; [exact Hpf|].
  split; [exact Hn|]. split; [exact Hgarr|]. split; [exact Hsrc|]. split; [exact Htw|]. split; [exact Hgf|].
  split; [exact Hmodel|]. split; [exact Hrom|].
  split; [unfold TRunInv.run_inv; split; [exact I1|]; split; [exact I2|]; split; [exact I4|]; split; [exact I5a|];
          split; [exact I5b|]; split; [exact I4b | exact I2b]|].
  split; [exact Hdn|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
  split; [exact C5|]. split; [exact Hnev|]. split; [exact Hlive|]. split; [exact Hmo|]. split; [exact Hcost|].
  split; [exact Htm | exact Htf].
Qed.
End cut.
