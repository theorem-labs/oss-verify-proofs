(* diginet_session_poll_segs: the cut layer of the image-A walk of diginet_session_poll (fuzz_transport.asan 0x8ad88 =
   transport_sigma TS_diginet_session_poll, AF_diginet_session_poll = 0x9b24 of lib/A/Prog/DgnTransportList.v, 250
   words; statement lib/A/Prog/diginet_session_poll_cg.v). Definitions, the cut statements, the piece statements and
   their composition; no run.

   The walk holds the CALLER's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 []) from the entry to the
   return, with (POLL_CID, pos) :: own while the class-5 frame is live. A cut is a concrete state at one pc. The pieces
   (offsets from the entry; each cut is the first instruction of its block):
     head   +0x000 .. +0x1b8  the frame, the 13 saves, s0, the realign into s1, s9 = max_wait_ms, the two runtime
                              cells, s5 = the shadow base, s3 = s, `jal __asan_stack_malloc_5` (+0x070), the frame
                              word at s1 + 48, the frame's header, its shadow bytes 0 .. 3, `jal __asan_set_shadow_f8`
                              (+0x0f4), shadow bytes 194 .. 211, `jal __asan_set_shadow_00` (+0x14c), shadow byte 193,
                              s10 = -1, the slots s1 + 16 and s1 + 8, `beqz s3` (not taken), the checked loads of
                              io.recv (s + 80), io.now_us (s + 88, the slot s1 + 24 = its shadow address) and io.ctx
                              (s + 64): a NULL pointer goes to rel (:508-509), else to now1.
     now1   +0x1bc .. +0x230  `jalr a1` = io_now, `jal diginet_session_deadline` (+0x1cc), the wait (:512-515: a3 only,
                              which io_recv does not read), the checks of s + 80 and s + 64, the recv arguments, to recv1.
     recv1  +0x234 .. +0x27c  `jalr a4` = io_recv (:516); a negative result to rel (:517-518); the checks of s + 88 and
                              s + 64, `jalr a1` = io_now (+0x25c, :519); a result 0 to tick (:520), else `jal
                              diginet_session_rx` (+0x278, :521), to tick.
     tick   +0x280 .. +0x298  `jal diginet_session_tick` (+0x288, :522), the checks of s + 80 and s + 64, to loop.
     loop   +0x29c .. +0x300  the drain (:523-526): `jalr a4` = io_recv (+0x2b0); r <= 0 to rel; the checks of s + 88 and
                              s + 64, `jalr a1` = io_now (+0x2dc), `jal diginet_session_rx` (+0x2f0), the checks of
                              s + 80 and s + 64, back to loop (one less fuel, poll_drain_m).
     rel    +0x30c .. +0x384  `jal __asan_set_shadow_f8` (+0x314), the header word 0x45e0360e, `beqz` on the slot
                              s1 + 16 (not taken), `jal __asan_stack_free_5` (+0x330), a0 = s10, sp = s0 - 160, the 13
                              reloads, sp = sp + 160, `ret`.
   Each cut holds the context's facts (pw_ok), the journal and the facts carried while the frame is live (pw_cur;
   pw_run adds what the head stores for the run after it: buf's shadow bytes and the slot s1 + 24), the registers the
   code after the cut reads (the pw_rg_ predicates), and the model's remaining computation at the cut's world. Every
   cut concludes
   pw_post, the statement's post with the run invariants added to X (pw_X); the statement's post follows by
   TransportGCg.v transport_cg_post_X_mono.
   The run invariants are SrxCut.v srx_inv (the statement's (1), (2), (4), (5) and the bounds g_ncmd <= CMDS_MAX,
   S_queued <= QUEUE_MAX). The model facts that the callees' model calls keep them and keep g_rx are pw_keep: six
   statements whose proofs are lib/TModel/TRunInv.v's (named here by their texts; the top file takes them as named
   Section hypotheses until TRunInv.v lands). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg take_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_tick_cg m_rx_cg io_recv_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require io_now_cg diginet_session_deadline_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_cg SrxCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
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
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LIN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.io_now_cg.
Module LSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_deadline_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The addresses                                                       *)
(* ------------------------------------------------------------------ *)

(* The cut points, as offsets of the listing: now1 `jalr a1` (+0x1bc, the fall-through of `beqz a0` at +0x1b4, the
   check of io.ctx); recv1 `jalr a4` (+0x234); tick `mv a0, s3` (+0x280, the target of `beqz s10` at +0x264 and the
   fall-through of the rx return's `mv a3, s10`); loop `ld a0, 0(s8)` (+0x29c, the fall-through of `bnez a0` at +0x298
   and the target of `beqz a0` at +0x300); rel `addi a1, zero, 0xbe` (+0x30c, the join of every return: +0x164,
   +0x180, +0x1a0, +0x23c, +0x2b8). *)
Definition PW_NOW1 : Z := AF_diginet_session_poll + 0x1bc.
Definition PW_RECV1 : Z := AF_diginet_session_poll + 0x234.
Definition PW_TICK : Z := AF_diginet_session_poll + 0x280.
Definition PW_LOOP : Z := AF_diginet_session_poll + 0x29c.
Definition PW_REL : Z := AF_diginet_session_poll + 0x30c.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11 (sd at sp + 152 ..
   sp + 56 after `addi sp, sp, -160`). *)
Definition POLL_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26); (104, 27)].
(* The class-5 frame's size; its last word (frame + 2040) holds the address of its flag byte. *)
Definition POLL_FBYTES : Z := 2048.
Lemma poll_fbytes : fs_frame_bytes POLL_CID = POLL_FBYTES.
Proof. reflexivity. Qed.
(* The shadow addresses of the three g_s fields the code checks: s + 64 (io.ctx, s5 from +0x1ac), s + 80 (io.recv,
   s11) and s + 88 (io.now_us, the slot s1 + 24). *)
Definition PW_SH64 : Z := SHADOW_OFF + (POLL_S + 64) / 8.
Definition PW_SH80 : Z := SHADOW_OFF + (POLL_S + 80) / 8.
Definition PW_SH88 : Z := SHADOW_OFF + (POLL_S + 88) / 8.

(* ------------------------------------------------------------------ *)
(* The model                                                           *)
(* ------------------------------------------------------------------ *)

(* What remains of diginet_session_poll_m after the first recv (TPoll.v poll_cases): its negative result returned
   (:517-518), else now, rx when it handed over a frame, tick and the drain (:519-526). *)
Definition pw_rest1 (I : TI.timg) (F : option TI.tframe) (B1 : list byte) (r1 : Z) (got : list byte)
    (Bw' : list byte) (r : Z) : Prop :=
  (r1 < 0 /\ Bw' = B1 /\ r = r1) \/
  (0 <= r1 /\ exists now2 B2 B3 r3,
     TSS.call_now I B1 = Some now2 /\
     ((r1 = 0 /\ B2 = B1) \/ (0 < r1 /\ exists r2, TSS.diginet_session_rx_m I F B1 got now2 = Some (B2, r2))) /\
     TSS.diginet_session_tick_m I F B2 now2 = Some (B3, r3) /\
     TSS.poll_drain_m I F B3 (Z.to_nat (TW.g_rx_times B3)) = Some (Bw', r)).

(* The model facts the walk takes about the callees' model calls (lib/TModel/TRunInv.v, at any timg; run_inv there is
   srx_inv's seven conjuncts): diginet_session_rx_m, diginet_session_tick_m and io_recv_m keep the run invariants and
   change no byte of g_rx. *)
Definition rx_m_run_inv_stmt : Prop :=
  forall (I : TI.timg) (F : option TI.tframe) (Bx b : list byte) (now : Z) (B2 : list byte) (r : Z),
    length Bx = Z.to_nat TW.W_LEN -> srx_inv Bx ->
    TSS.diginet_session_rx_m I F Bx b now = Some (B2, r) -> srx_inv B2.
Definition tick_m_run_inv_stmt : Prop :=
  forall (I : TI.timg) (F : option TI.tframe) (Bx : list byte) (now : Z) (B2 : list byte) (r : Z),
    length Bx = Z.to_nat TW.W_LEN -> srx_inv Bx ->
    TSS.diginet_session_tick_m I F Bx now = Some (B2, r) -> srx_inv B2.
Definition rx_m_g_rx_stmt : Prop :=
  forall (I : TI.timg) (F : option TI.tframe) (Bx b : list byte) (now : Z) (B2 : list byte) (r : Z),
    length Bx = Z.to_nat TW.W_LEN ->
    TSS.diginet_session_rx_m I F Bx b now = Some (B2, r) -> TW.g_rx B2 = TW.g_rx Bx.
Definition tick_m_g_rx_stmt : Prop :=
  forall (I : TI.timg) (F : option TI.tframe) (Bx : list byte) (now : Z) (B2 : list byte) (r : Z),
    length Bx = Z.to_nat TW.W_LEN ->
    TSS.diginet_session_tick_m I F Bx now = Some (B2, r) -> TW.g_rx B2 = TW.g_rx Bx.
Definition iorecv_m_run_inv_stmt : Prop :=
  forall (I : TI.timg) (F : option TI.tframe) (Bx : list byte) (cap : Z) (B1 : list byte) (r : Z) (got : list byte),
    length Bx = Z.to_nat TW.W_LEN -> srx_inv Bx ->
    TC.io_recv_m I F Bx cap = Some (B1, r, got) -> srx_inv B1.
Definition iorecv_m_g_rx_stmt : Prop :=
  forall (I : TI.timg) (F : option TI.tframe) (Bx : list byte) (cap : Z) (B1 : list byte) (r : Z) (got : list byte),
    length Bx = Z.to_nat TW.W_LEN ->
    TC.io_recv_m I F Bx cap = Some (B1, r, got) -> TW.g_rx B1 = TW.g_rx Bx.
Definition pw_keep : Prop :=
  rx_m_run_inv_stmt /\ tick_m_run_inv_stmt /\ rx_m_g_rx_stmt /\ tick_m_g_rx_stmt /\
  iorecv_m_run_inv_stmt /\ iorecv_m_g_rx_stmt.

(* ------------------------------------------------------------------ *)
(* The context                                                         *)
(* ------------------------------------------------------------------ *)

Record pw_ctx : Type := mkPW {
  cx_STK : Z; cx_sp0 : Z; cx_FP : list (Z * Z); cx_ly : alayout; cx_S : astate;
  cx_W0 : world tfibsegs; cx_mem0 : word -> option byte; cx_md0 : Model; cx_own : list (Z * Z);
  cx_lyc : alayout; cx_Sc : astate; cx_W : world tfibsegs; cx_memc : word -> option byte; cx_mdc : Model;
  cx_k : Z; cx_regs : bvmap 5 word; cx_w : Z; cx_r : Z; cx_TF : option TI.tframe;
  cx_Bw : list byte; cx_Bw' : list byte }.

Section pw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma pw_cut_pcs :
  BASE + AF_diginet_session_poll = transport_sigma TS_diginet_session_poll /\
  BASE + PW_NOW1 = 0x8af44 /\ BASE + PW_RECV1 = 0x8afbc /\ BASE + PW_TICK = 0x8b008 /\
  BASE + PW_LOOP = 0x8b024 /\ BASE + PW_REL = 0x8b094.
Proof. repeat split; reflexivity. Qed.

(* The entry sp, the realigned sp (`addi sp, sp, -160`, `andi sp, sp, -32`) and the frame's address. *)
Definition pw_SP (c : pw_ctx) : Z := spZ (cx_regs c).
Definition pw_sp1 (c : pw_ctx) : Z := 32 * ((pw_SP c - POLL_FRAME) / 32).
Definition pw_F (c : pw_ctx) (pos : Z) : Z := frame_addr (cx_lyc c) POLL_CID pos.

(* The record facts and the callee contracts: the premises of transport_diginet_session_poll_cg_holds_stmt, with gx_ok
   and gx_noerrno of G_HARNESS (DgnTransportCg.v G_HARNESS_gx_ok, G_HARNESS_gx_noerrno). *)
Definition pw_rt : Prop :=
  pc_stack_malloc (as_code B) POLL_CID = transport_sigma TS___asan_stack_malloc_5 /\
  transport_cells B /\ trans_poll_cells B /\
  trans_g_unowned B /\ trans_g_no_errno B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ frame_flag_lawP segs B /\
  gx_ok segs B G /\ gx_noerrno B G /\
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B POLL_CID) /\
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transport_sigma TS___asan_set_shadow_f8) 0xf8) /\
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transport_sigma TS___asan_set_shadow_00) 0) /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LIN.transport_io_now_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSD.transport_diginet_session_deadline_cg) fx') /\
  (forall fx' : YK11.FPState, @transport_io_recv_cg fx' rc B MT (TI.ti_io_recv timg_A)) /\
  (forall fx' : YK11.FPState,
     @transport_diginet_session_rx_cg fx' rc B MT (transport_sigma TS_diginet_session_rx)) /\
  (forall fx' : YK11.FPState,
     @transport_diginet_session_tick_cg fx' rc B MT (transport_sigma TS_diginet_session_tick)) /\
  (forall fx' : YK11.FPState,
     @astack_free_cls_realizes fx' rc segs B (transport_sigma TS___asan_stack_free_5) POLL_CID).

(* The contract's premises at the context (diginet_session_poll_cg.v transport_diginet_session_poll_cg), with the
   five invariant premises and the two bounds of the statement as srx_inv Bw. *)
Definition pw_ok (c : pw_ctx) : Prop :=
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    (cx_own c) (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_mdc c) (cx_k c) /\
  YK0s.ret_ok (YK11.getr (cx_regs c) 1) /\ 4096 <= raZ (cx_regs c) /\
  YK11.getr (cx_regs c) 3 = w64 (as_gp B) /\ YK11.getr (cx_regs c) 4 = w64 (as_tp B) /\
  YK11.getr (cx_regs c) 10 = w64 POLL_S /\ YK11.getr (cx_regs c) 11 = w64 (cx_w c) /\
  pw_SP c mod 16 = 0 /\ cx_sp0 c - cx_STK c <= pw_SP c - POLL_STK /\ pw_SP c <= cx_sp0 c /\
  - 2 ^ 31 <= cx_w c < 2 ^ 31 /\
  tw_at TMAP_A (aview segs (w_H (cx_W c)) (cx_memc c)) (cx_Bw c) /\ TW.g_fail_next (cx_Bw c) <= 1 /\
  TSS.diginet_session_poll_m timg_A (cx_TF c) (cx_Bw c) (cx_w c) = Some (cx_Bw' c, cx_r c) /\
  trans_tframe_at B (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_regs c) POLL_STK (cx_TF c) /\
  trans_tf_off_g (cx_TF c) /\
  trans_rom_view_rd (cx_W c) (cx_memc c) /\
  poll_apart (cx_TF c) /\
  iorecv_rx_in (cx_TF c) (cx_Bw c) /\
  srx_inv (cx_Bw c) /\
  poll_rx_each timg_A (cx_TF c) (poll_dn_in (cx_TF c)) (cx_Bw c) /\
  count_cid POLL_CID (frames (cx_Sc c)) + 1 < fs_frames POLL_CID /\
  count_cid SRX_CID (frames (cx_Sc c)) < fs_frames SRX_CID /\
  count_cid ONANN_CID (frames (cx_Sc c)) < fs_frames ONANN_CID /\
  count_cid SENDDATA_CID (frames (cx_Sc c)) < fs_frames SENDDATA_CID /\
  count_cid ONDATA_CID (frames (cx_Sc c)) + 2 < fs_frames ONDATA_CID /\
  st_nev (cx_S c) + cx_k c + POLL_EV <= EV_MAX.

(* The post's X with the run invariants at the model's world Bw' (they give the bounds g_ncmd <= CMDS_MAX and
   S_queued <= QUEUE_MAX). *)
Definition pw_X (r : Z) (Bw' : list byte) : bvmap 5 word -> world segs -> (word -> option byte) -> Prop :=
  fun regs2 W2 mem2 =>
    YK11.getr regs2 10 = w64 r /\
    tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1 /\ srx_inv Bw'.

(* The contract's post at the context, with X = pw_X. *)
Definition pw_post (c : pw_ctx) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT G (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c)
    (cx_W0 c) (cx_mem0 c) (cx_md0 c) (cx_own c) (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) (cx_k c) (cx_regs c)
    POLL_STK POLL_EV 0 poll_wr (pw_X (cx_r c) (cx_Bw' c)).

(* What every cut carries while the frame is live, at the current state (ly2, S2, W2, mem2, md2) and model world Bx
   (no event: POLL_EV = 0): the caller's G journal with the frame owned; the frame on top of the call's frames, the
   call's blocks, the frames where the call's layout puts them, the meter; what the call has kept so far
   (acall_kept_g over the statement's window and written range poll_wr); the 13 saved words below the entry sp; the
   frame's last word (the address of its flag byte; __asan_stack_free_5's premise); the slots s1 + 8 (the shadow
   address of buf, +0x160) and s1 + 16 (the frame, +0x15c), which rel reads; the world relation at Bx, g_fail_next,
   the run invariants, and g_rx as at the entry (io_recv's iorecv_rx_in). *)
Definition pw_cur (c : pw_ctx) (pos : Z) (ly2 : alayout) (S2 : astate) (W2 : world segs)
    (mem2 : word -> option byte) (md2 : Model) (Bx : list byte) : Prop :=
  ajournal_gx G 0 [] (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c)
    ((POLL_CID, pos) :: cx_own c) ly2 S2 W2 mem2 md2 (cx_k c) /\
  frames S2 = (POLL_CID, pos) :: frames (cx_Sc c) /\
  Permutation (ablocks B ly2 S2) (ablocks B (cx_lyc c) (cx_Sc c)) /\
  ly_F ly2 = ly_F (cx_lyc c) /\
  mo_le MT (cx_Sc c) S2 0 /\
  acall_kept_g segs B G (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) W2 mem2 (pw_SP c - POLL_STK) (pw_SP c) poll_wr /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (pw_SP c - fst o) =
      Some (bv_unsigned (YK11.getr (cx_regs c) (Z_to_bv 5 (snd o))))) POLL_SAVED /\
  rdword (aview segs (w_H W2) mem2) (pw_F c pos + POLL_FBYTES - 8) = Some (flag_addr (cx_lyc c) POLL_CID pos) /\
  rdword (aview segs (w_H W2) mem2) (pw_sp1 c + 8) = Some (SHADOW_OFF + pw_F c pos / 8 + 4) /\
  rdword (aview segs (w_H W2) mem2) (pw_sp1 c + 16) = Some (pw_F c pos) /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bx /\ TW.g_fail_next Bx <= 1 /\ srx_inv Bx /\
  TW.g_rx Bx = TW.g_rx (cx_Bw c).

(* The run after the head also carries buf's shadow (bytes 4 .. 192 of the frame's shadow are 0 and byte 193 is 2:
   buf's 1514 bytes at frame + 32 are usable) and the slot s1 + 24 (the shadow address of s + 88, +0x190). *)
Definition pw_run (c : pw_ctx) (pos : Z) (ly2 : alayout) (S2 : astate) (W2 : world segs)
    (mem2 : word -> option byte) (md2 : Model) (Bx : list byte) : Prop :=
  pw_cur c pos ly2 S2 W2 mem2 md2 Bx /\
  (forall i, 4 <= i < 193 -> aview segs (w_H W2) mem2 (SHADOW_OFF + pw_F c pos / 8 + i) = Some 0) /\
  aview segs (w_H W2) mem2 (SHADOW_OFF + pw_F c pos / 8 + 193) = Some 2 /\
  rdword (aview segs (w_H W2) mem2) (pw_sp1 c + 24) = Some PW_SH88.

(* ---- the registers at the cuts ---- *)

(* What every cut holds and rel reads: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s2 = the frame. *)
Definition pw_rg_base (c : pw_ctx) (pos : Z) (regs2 : bvmap 5 word) : Prop :=
  YK11.getr regs2 2 = w64 (pw_sp1 c) /\ YK11.getr regs2 3 = w64 (as_gp B) /\ YK11.getr regs2 4 = w64 (as_tp B) /\
  YK11.getr regs2 8 = w64 (pw_SP c) /\ YK11.getr regs2 9 = w64 (pw_sp1 c) /\ YK11.getr regs2 18 = w64 (pw_F c pos).
(* The run's cuts also hold s3 = s, s4 = the frame's shadow address, s5 = the shadow address of s + 64, s6 = s + 80,
   s7 = s + 88, s8 = s + 64, s11 = the shadow address of s + 80. *)
Definition pw_rg_run (c : pw_ctx) (pos : Z) (regs2 : bvmap 5 word) : Prop :=
  pw_rg_base c pos regs2 /\
  YK11.getr regs2 19 = w64 POLL_S /\ YK11.getr regs2 20 = w64 (SHADOW_OFF + pw_F c pos / 8) /\
  YK11.getr regs2 21 = w64 PW_SH64 /\ YK11.getr regs2 22 = w64 (POLL_S + 80) /\
  YK11.getr regs2 23 = w64 (POLL_S + 88) /\ YK11.getr regs2 24 = w64 (POLL_S + 64) /\
  YK11.getr regs2 27 = w64 PW_SH80.
(* From +0x224 on, s9 = buf = frame + 32. *)
Definition pw_rg_buf (c : pw_ctx) (pos : Z) (regs2 : bvmap 5 word) : Prop :=
  pw_rg_run c pos regs2 /\ YK11.getr regs2 25 = w64 (pw_F c pos + 32).

(* ---- the cuts: from the cut's state, the post ---- *)

(* rel (+0x30c): s10 = the result; the frame live; the world is the model's final one. *)
Definition pw_rel_at (c : pw_ctx) : Prop :=
  pw_rt -> pw_ok c ->
  forall pos ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word),
    pw_cur c pos ly2 S2 W2 mem2 md2 (cx_Bw' c) -> pw_rg_base c pos regs2 -> YK11.getr regs2 26 = w64 (cx_r c) ->
    SRr segs W2 (@cfg_at fx segs (BASE + PW_REL) regs2 mem2 md2) (pw_post c).

(* loop (+0x29c) with fuel: the model's drain from the world Bx (:523-526), and (3) at each of its rx calls. *)
Definition pw_loop_at (c : pw_ctx) (fuel : nat) : Prop :=
  pw_rt -> pw_keep -> pw_ok c ->
  forall pos ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) (Bx : list byte),
    pw_run c pos ly2 S2 W2 mem2 md2 Bx -> pw_rg_buf c pos regs2 ->
    TSS.poll_drain_m timg_A (cx_TF c) Bx fuel = Some (cx_Bw' c, cx_r c) ->
    poll_drain_rx timg_A (cx_TF c) (poll_dn_in (cx_TF c)) Bx fuel ->
    SRr segs W2 (@cfg_at fx segs (BASE + PW_LOOP) regs2 mem2 md2) (pw_post c).

(* tick (+0x280): a3 = now2; the model's tick at the world B2, then the drain from its world B3 with the fuel
   g_rx_times B3 (:522-523). *)
Definition pw_tick_at (c : pw_ctx) : Prop :=
  pw_rt -> pw_keep -> pw_ok c ->
  forall pos ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) (B2 : list byte) (now2 : Z)
         (B3 : list byte) (r3 : Z),
    pw_run c pos ly2 S2 W2 mem2 md2 B2 -> pw_rg_buf c pos regs2 -> YK11.getr regs2 13 = w64 now2 ->
    0 <= now2 < 2 ^ 64 ->
    TSS.diginet_session_tick_m timg_A (cx_TF c) B2 now2 = Some (B3, r3) ->
    TSS.poll_drain_m timg_A (cx_TF c) B3 (Z.to_nat (TW.g_rx_times B3)) = Some (cx_Bw' c, cx_r c) ->
    poll_drain_rx timg_A (cx_TF c) (poll_dn_in (cx_TF c)) B3 (Z.to_nat (TW.g_rx_times B3)) ->
    SRr segs W2 (@cfg_at fx segs (BASE + PW_TICK) regs2 mem2 md2) (pw_post c).

(* recv1 (+0x234): a1 = buf, a2 = 1514, a4 = io_recv (the pointer the code loaded, the image's io_recv: the model's
   call_recv tested it, kit pw_m_go); the world is the entry's; the model's first recv and what remains after it. *)
Definition pw_recv1_at (c : pw_ctx) : Prop :=
  pw_rt -> pw_keep -> pw_ok c ->
  forall pos ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word) (B1 : list byte) (r1 : Z) (got : list byte),
    pw_run c pos ly2 S2 W2 mem2 md2 (cx_Bw c) -> pw_rg_buf c pos regs2 ->
    YK11.getr regs2 11 = w64 (pw_F c pos + 32) -> YK11.getr regs2 12 = w64 TS0.DIGINET_MAX_FRAME_LEN ->
    YK11.getr regs2 14 = w64 (TI.ti_io_recv timg_A) -> TW.S_io_recv (cx_Bw c) = TI.ti_io_recv timg_A ->
    TC.io_recv_m timg_A (cx_TF c) (cx_Bw c) TS0.DIGINET_MAX_FRAME_LEN = Some (B1, r1, got) ->
    pw_rest1 timg_A (cx_TF c) B1 r1 got (cx_Bw' c) (cx_r c) ->
    SRr segs W2 (@cfg_at fx segs (BASE + PW_RECV1) regs2 mem2 md2) (pw_post c).

(* now1 (+0x1bc): a1 = io.now_us as loaded; s9 = max_wait_ms; neither pointer is NULL. *)
Definition pw_now1_at (c : pw_ctx) : Prop :=
  pw_rt -> pw_keep -> pw_ok c ->
  forall pos ly2 S2 (W2 : world segs) mem2 md2 (regs2 : bvmap 5 word),
    pw_run c pos ly2 S2 W2 mem2 md2 (cx_Bw c) -> pw_rg_run c pos regs2 ->
    YK11.getr regs2 25 = w64 (cx_w c) -> YK11.getr regs2 11 = w64 (TW.S_io_now_us (cx_Bw c)) ->
    TW.S_io_recv (cx_Bw c) <> 0 -> TW.S_io_now_us (cx_Bw c) <> 0 ->
    SRr segs W2 (@cfg_at fx segs (BASE + PW_NOW1) regs2 mem2 md2) (pw_post c).

(* The walk from the entry. *)
Definition pw_entry (c : pw_ctx) : Prop :=
  pw_rt -> pw_keep -> pw_ok c ->
  SRr segs (cx_W c) (@cfg_at fx segs (transport_sigma TS_diginet_session_poll) (cx_regs c) (cx_memc c) (cx_mdc c))
    (pw_post c).

(* ---- the six pieces, in continuation form: the cuts a piece can reach, then its own cut ---- *)
Definition pw_rel_stmt : Prop := forall c, pw_rel_at c.
Definition pw_loop_stmt : Prop :=
  forall c, pw_rel_at c -> forall fuel, (forall f, (f < fuel)%nat -> pw_loop_at c f) -> pw_loop_at c fuel.
Definition pw_tick_stmt : Prop := forall c, (forall fuel, pw_loop_at c fuel) -> pw_tick_at c.
Definition pw_recv1_stmt : Prop := forall c, pw_rel_at c -> pw_tick_at c -> pw_recv1_at c.
Definition pw_now1_stmt : Prop := forall c, pw_recv1_at c -> pw_now1_at c.
Definition pw_head_stmt : Prop := forall c, pw_now1_at c -> pw_rel_at c -> pw_entry c.

(* The loop at every fuel, by strong induction. *)
Lemma pw_loop_all : pw_loop_stmt -> forall c, pw_rel_at c -> forall fuel, pw_loop_at c fuel.
Proof.
  intros LOOP c REL fuel.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf).
  exact (LOOP c REL fuel IH).
Qed.

(* The walk from its pieces. *)
Lemma pw_walk : pw_head_stmt -> pw_now1_stmt -> pw_recv1_stmt -> pw_tick_stmt -> pw_loop_stmt -> pw_rel_stmt ->
  forall c, pw_entry c.
Proof.
  intros HEAD NOW1 RECV1 TICK LOOP REL c.
  pose proof (REL c) as R.
  pose proof (TICK c (pw_loop_all LOOP c R)) as T.
  exact (HEAD c (NOW1 c (RECV1 c R T)) R).
Qed.

End pw.
