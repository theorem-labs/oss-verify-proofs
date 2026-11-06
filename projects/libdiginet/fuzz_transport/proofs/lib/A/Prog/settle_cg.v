(* settle_cg: the ASan walk contract of settle (fuzz/fuzz_transport.c:980-991; model lib/TModel/TCb.v settle_m) on
   fuzz_transport.asan (e89be137db17) at 0x83cac = transport_sigma TS_settle, size 84, as STATEMENTS only (no proof).
   It stores into no harness global and calls six harness check functions, so it takes decode's caller-journal form
   (lib/A/Prog/DgnTransportCg.v decode_cg_post over the caller's donor journal ajournal); a G-form caller lifts it
   with lib/A/Prog/TransportGCg.v gx_call_cg.

   The contract. a0 = ticked (an int, sign-extended). The memory relates to the world Bw by image A's world relation
   (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview), and settle_m Bw ticked = Some (Bw', tt). The function
   returns to ra with the callee-saved registers kept, no allocator event, no meter charge, every byte outside its
   stack window kept (it stores nothing outside its own frame and the callees store nothing outside theirs: E is
   empty), and Bw' = Bw. This is what the plain contract (lib/Prog/T/settle_c.v) says: void; B' = B and
   wmem rsegs m' B; munch of the frame only. Its wmem premise becomes tw_at, and mem_inv and w_off_stack are dropped
   (the journal's window premises keep the frame off the world).
   The one premise the plain contract does not have: check_latest_queue's run invariant, every entry of the session's
   queue below g_s.queued has len <= 24 (DIGINET_CMD_MAX_LEN), stated on settle's own Bw (a caller
   carries it). settle calls check_latest_queue when g_raw is 0, and every check before it returns the world it was
   given (each model returns its own B), so check_latest_queue is handed Bw. settle does not establish it.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   84 code bytes are equal in both files), 21 words:
     0x83cac - 0x83cb4 sp = sp - 16; ra at sp + 8, s0 at sp + 0, loaded back at 0x83cd8 - 0x83cdc (the return at
                      0x83ce4, sp = sp + 16 at 0x83ce0) and at 0x83cf0 - 0x83cf4 (before the tail jump, sp = sp + 16
                      at 0x83cf8). These two 8-byte stores into its own frame are its only stores. No side-stack frame,
                      no frame pointer.
     0x83cb8          s0 = ticked (a0, kept to 0x83cec).
     0x83cbc          call of check_ack_settle (0x85b04 = transport_sigma TS_check_ack_settle), return address 0x83cc0.
     0x83cc0          call of check_state_settle (0x85b34), return address 0x83cc4.
     0x83cc4          call of check_inflight_settle (0x85d50), return address 0x83cc8.
     0x83cc8          call of check_keepalive_settle (0x85e14), return address 0x83ccc.
     0x83ccc - 0x83cd4 a0 = the 4-byte signed load of g_raw (0x5df0e0, pc-relative, no instrumented check); g_raw = 0
                      goes to 0x83ce8; else ra and s0 loaded back, sp = sp + 16, return (a0 not stated: void).
     0x83ce8          call of check_latest_queue (0x85e70), return address 0x83cec.
     0x83cec          ticked = 0 (s0, 64 bits) goes to 0x83cd8 (the return).
     0x83cf0 - 0x83cfc ra and s0 loaded back, sp = sp + 16; jump (no link) to check_latest_drain (0x85fdc) at 0x83cfc,
                      from settle's entry sp with settle's ra: its return is settle's return.
   The tests are settle_m's: truth (g_raw B4) and truth ticked, read through tw_at, with B4 = Bw: each check's model
   returns the world it was given, and the world relation at Bw holds again after each call. A leaf's post
   (LeafCgKit.v dleaf_post) keeps every byte outside its stack window, and the harness globals lie in the image, far
   below the stack. A donor callee's post (check_inflight_settle, check_latest_queue: DgnTransportCg.v
   decode_cg_post, YCbq.v acall_kept) keeps the image bytes that are not owned statics and not errno, and every byte
   of G is such a byte (gx_ok, gx_noerrno): TransportGCg.v gx_kept_of_acall_kept, then TWorldG.v tw_kept_G.
   The traps are the callees': each is ruled out by its statement's model premise, which settle_m's let* chain
   supplies (check_ack_settle_m, check_state_settle_m, check_inflight_settle_m, check_keepalive_settle_m,
   check_latest_queue_m, check_latest_drain_m, each at Bw).
   Error paths: none. settle's own load of g_raw carries no instrumented check, and its code calls no
   __asan_report_* entry, no __asan_handle_no_return and no abort.
   Callee texts assumed (pc order):
     check_ack_settle as check_ack_settle_cg.v transport_check_ack_settle_cg (a leaf, read at this unit's model by
       DgnTransportCg.v transport_leaf_at; call at 0x83cbc);
     check_state_settle as check_state_settle_cg.v transport_check_state_settle_cg (leaf; call at 0x83cc0); it asks
       the 192 bytes of GOT.t[] and of OW.t[] addressable: trans_settle_cells (GOT's and OW's zero shadow);
     check_inflight_settle as check_inflight_settle_cg.v transport_check_inflight_settle_cg at transport_sigma
       TS_check_inflight_settle (donor form, the same journal; call at 0x83cc4);
     check_keepalive_settle as check_keepalive_settle_cg.v transport_check_keepalive_settle_cg (leaf; call at
       0x83cc8);
     check_latest_queue as check_latest_queue_cg.v transport_check_latest_queue_cg at transport_sigma
       TS_check_latest_queue (donor form; call at 0x83ce8), with its queue-length premise (settle's own);
     check_latest_drain as check_latest_drain_cg.v transport_check_latest_drain_cg (leaf; tail jump at 0x83cfc); it
       asks g_q's and g_cmd's payloads addressable: trans_settle_cells (their zero shadow).
   Each leaf's other premises (asan_cells, the runtime cells' and the harness globals' places off its stack window,
   its footprint ranges) come from transport_cells, the journal's window and the world relation at the call state.
   No runtime entry is called.
   Stack: 16 bytes of its own; the calls run from sp - 16, and the largest window among them is check_latest_queue's
   CLQ_STK (check_inflight_settle's CIS_STK and a leaf's ESTACK are smaller); the tail jump runs from the entry sp
   (a leaf's ESTACK): SETTLE_STK = 16 + CLQ_STK.

   The callers: LLVMFuzzerTestOneInput (0x81bec with a0 = 1, 0x82280 and 0x82530 with a0 = 0) and receive (0x83a48).
   Each is a G-form walk; it lifts this statement with gx_call_cg and supplies the journal, the world relation, the
   model call and the queue-length invariant from its own walk. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_inflight_settle_cg check_latest_queue_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  check_ack_settle_cg check_state_settle_cg check_keepalive_settle_cg check_latest_drain_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TSess0.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module LAS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_ack_settle_cg.
Module LSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_state_settle_cg.
Module LKS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_keepalive_settle_cg.
Module LLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_latest_drain_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* settle's frame (`sp = sp - 16` at its entry; no realignment). The calls run from sp - 16: the leaves' ESTACK,
   check_inflight_settle's CIS_STK, check_latest_queue's CLQ_STK; the tail jump to check_latest_drain runs from the
   entry sp (a leaf's ESTACK). *)
Definition SETTLE_FRAME : Z := 16.
Definition SETTLE_STK : Z := Z.max ESTACK (SETTLE_FRAME + Z.max (Z.max ESTACK CIS_STK) CLQ_STK).
Lemma settle_stk_eq : SETTLE_STK = SETTLE_FRAME + CLQ_STK.
Proof. reflexivity. Qed.
(* No allocator event: neither settle nor a callee calls malloc or free or takes a side-stack frame. *)
Definition SETTLE_EV : Z := 0.

(* The shadow of the payloads of GOT (224 bytes), OW (304), g_q (4096) and g_cmd (40960), all whole granules, is 0:
   ranges of the record's as_zero_shadow. check_state_settle's statement asks GOT.t[] and OW.t[] addressable,
   check_latest_drain's asks g_q's and g_cmd's payloads addressable. *)
Definition trans_settle_cells (B : asyms) : Prop :=
  decode_zshadow_at B TA_GOT (TA_GOT + TW.SZ_GOT) /\
  decode_zshadow_at B TA_OW (TA_OW + TW.SZ_OW) /\
  decode_zshadow_at B TA_g_q (TA_g_q + TW.SZ_g_q) /\
  decode_zshadow_at B TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd).

Section settle. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportCg.v decode_cg_post with no event, no written range, no meter charge, and X: the
   model's world is the world it was given. *)
Definition transport_settle_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs SETTLE_STK SETTLE_EV 0
    (fun _ => False) (fun _ _ _ => Bw' = Bw).

(* The contract at entry address a, in the caller-journal form. *)
Definition transport_settle_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (ticked : Z) (Bw Bw' : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 ticked -> -2 ^ 31 <= ticked < 2 ^ 31 ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SETTLE_STK -> spZ regs <= sp0 ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TC.settle_m Bw ticked = Some (Bw', tt) ->
    (forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN) ->
    st_nev S + k + SETTLE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_settle_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells, the shadow of GOT, OW, g_q and g_cmd (trans_settle_cells),
   the allocator and meter laws, G inside the image, outside the allocator's statics and outside errno (a donor
   callee keeps every byte of G, so the world relation holds after it: gx_kept_of_acall_kept), and the statements of
   the six callees give the contract at TS_settle. *)
Definition transport_settle_cg_holds_stmt : Prop :=
  transport_cells B -> trans_settle_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS -> gx_noerrno B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LAS.transport_check_ack_settle_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSS.transport_check_state_settle_cg) fx') ->
  (forall fx' : YK11.FPState,
     @transport_check_inflight_settle_cg fx' rc B MT (transport_sigma TS_check_inflight_settle)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LKS.transport_check_keepalive_settle_cg) fx') ->
  (forall fx' : YK11.FPState,
     @transport_check_latest_queue_cg fx' rc B MT (transport_sigma TS_check_latest_queue)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLD.transport_check_latest_drain_cg) fx') ->
  transport_settle_cg (transport_sigma TS_settle).
End settle.
