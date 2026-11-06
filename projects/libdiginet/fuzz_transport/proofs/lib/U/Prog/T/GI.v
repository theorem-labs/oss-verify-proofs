(* libdiginet/fuzz_transport, ubsan build: the slot's G and GI, and the frame's obligations for them.

   G = frame_G = [(W_BASE_UBSAN, W_LEN)] (U/FrameAPI.v): the world, the one .bss region of the harness's writable
   globals (TModel/TWorld.v). GI, the invariant carried from one call of LLVMFuzzerTestOneInput to the next, is True:
   each call writes every global before it reads it, so nothing a call reads comes from the call before.
   fuzz/fuzz_transport.c, global (ubsan address): where each call first writes it.
     g_cfg (0x43100)           :1134 diginet_session_config_default (transport/src/diginet_session.c: memset, then fields)
     g_raw (0x430cc)           :1150
     g_now (0x430e8)           :1151
     g_fail_next (0x430c8)     :1152
     g_last_counter (0x430d0)  :1153
     M (0x33300)               :1154 memset(&M, 0, sizeof M)
     g_ncmd, g_nq (0x430d8, 0x430d4)  :1157
     g_rx (0x430f0)            :1158
     g_s (0x33970)             :1165 diginet_session_init, memset(s, 0, sizeof *s) at transport/src/diginet_session.c:64
                               (init calls no io or notice callback)
     OW, GOT (0x43220, 0x4313c)  op_begin :388-394 (memset both), the first statement of every operation that reaches
                               them (receive :1001, op_submit :1074, tick :1183, wake :1194, close :1201); op_frame and
                               op_announce reach them through build_and_receive -> receive
     g_cmd (0x380c8)           element g_cmd[g_ncmd] at :1087 (memset) and :1108-1112 before g_ncmd++ (:1120); every
                               read is of an element below g_ncmd (:614) or named by g_q[i], i < g_nq (:789, :808, :1100)
     g_q (0x420c8)             element g_q[i], i < g_nq, at :1115 / :1117 (and the compaction :620-623); every read is of
                               an index below g_nq
     g_rx_send (0x430dc)       receive :1003 / :1008; read only in check_ack_frame (:428), from io_send on an ACK, which the
                               session sends only in on_data (transport/src/diginet_session.c:242), reached only from
                               diginet_session_rx / _poll, which the harness calls only in receive after :1003
     g_rx_len, g_rx_times, g_rx_fail (0x430f8, 0x430e4, 0x430e0)  receive :1013-1015; read only in io_recv (:906-929),
                               which only diginet_session_poll calls (transport/src/diginet_session.c:516, :524), which
                               the harness calls only at :1016 *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YO0f YO0d YL0g.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem.
Import ListNotations.
Local Open Scope Z_scope.

Definition GI (j : nat) (m : word -> option byte) : Prop := True.

(* G_local_c (U/Contract.v:291): GI reads no byte, so a run that keeps frame_G's bytes keeps it. *)
Lemma GI_local : forall B, G_local_c B frame_G GI.
Proof. intros B j m m' _ _. exact I. Qed.

(* G_img_c (U/Contract.v:294): GI holds of the image at call 0. *)
Lemma GI_img : forall B mem, G_img_c B frame_G mem -> GI 0%nat mem.
Proof. intros B mem _. exact I. Qed.

(* frame_G is exactly the world. *)
Lemma frame_G_world : forall a, in_globals frame_G a <-> W_BASE_UBSAN <= a < W_BASE_UBSAN + W_LEN.
Proof.
  intros a. unfold in_globals, frame_G. split.
  - intros (lo & len & [E|[]] & H). injection E as <- <-. exact H.
  - intros H. exists W_BASE_UBSAN, W_LEN. split; [left; reflexivity | exact H].
Qed.

(* frame_ubsan's global clause (U/FrameAPI.v:45-46) for every B that has the frame's symbol values: the world is in
   the image (wmem_in_img, U/Prog/T/WMem.v), and below every allocator-static range, the malloc context and errno. *)
Lemma frame_G_clause : forall B : malloc_syms,
  ms_segs B = rsegs -> ms_guard B = 0x63690 -> ms_got_guard B = 0x22050 ->
  ms_ctx B = 0x63728 -> ms_lock B = 0x63720 -> ms_libc B = 0x636b0 -> ms_size_classes B = 0x10520 ->
  ms_small_cnt B = 0x10580 -> ms_med_cnt B = 0x1059b -> ms_debruijn B = 0x10500 -> ms_tp B = 0x43420 ->
  ms_errno_off B = -164 -> ms_vmlock B = None -> ms_debruijn_len B = 32 ->
  forall a, in_globals frame_G a ->
    in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
    ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros B SEG GU GG CX LK LC SC SM MD DB TP EO VM DL a Ha.
  apply frame_G_world in Ha.
  split; [exact (wmem_in_img B a SEG Ha)|].
  unfold W_BASE_UBSAN, W_LEN in Ha.
  unfold static_owned, errno_addr, vml_lo, vml_len, CTX_SIZE.
  rewrite GU, GG, CX, LK, LC, SC, SM, MD, DB, TP, EO, VM, DL. cbv beta iota.
  split; [intros X; repeat (destruct X as [X|X]; [lia|]); lia|].
  split; lia.
Qed.
