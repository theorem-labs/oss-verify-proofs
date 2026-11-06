(* settle_cg (image B): the ASan walk contract of settle (fuzz/fuzz_transport.c:980-991; model lib/TModel/TCb.v
   settle_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x838c0 = DgnTransportBAddr.v transportb_sigma TB_settle,
   size 84, as STATEMENTS only (no proof). It stores into no harness global and calls six harness check functions, so
   it takes decode's caller-journal form (lib/B/Prog/DgnTransportBCg.v decode_cg_post over the caller's donor journal
   ajournal); a G-form caller lifts it with lib/A/Prog/TransportGCg.v gx_call_cg (image-free). Form:
   lib/A/Prog/settle_cg.v (the same definitions, premises, post and holds statement, at image B's addresses).

   The contract. a0 = ticked (an int, sign-extended). The memory relates to the world Bw by image B's world relation
   (lib/A/Prog/TWorldG.v tw_at at lib/B/Prog/TWorldB.v TMAP_B, read through aview), and settle_m Bw ticked =
   Some (Bw', tt). The function returns to ra with the callee-saved registers kept, no allocator event, no meter
   charge, every byte outside its stack window kept (it stores nothing outside its own frame and the callees store
   nothing outside theirs: E is empty), and Bw' = Bw. This is what the plain contract (lib/Prog/T/settle_c.v) says:
   void; B' = B and wmem rsegs m' B; munch of the frame only. Its wmem premise becomes tw_at, and mem_inv and
   w_off_stack are dropped (the journal's window premises keep the frame off the world).
   The one premise the plain contract does not have: check_latest_queue's run invariant, every entry of the session's
   queue below g_s.queued has len <= 24 (DIGINET_CMD_MAX_LEN), stated on settle's own Bw (a caller
   carries it). settle calls check_latest_queue when g_raw is 0, and every check before it returns the world it was
   given (each model returns its own B), so check_latest_queue is handed Bw. settle does not establish it.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 84 code bytes are equal in both files), symbol
   settle, value 0x838c0, size 84, 21 words:
     0x838c0 - 0x838c8 sp = sp - 16; ra at sp + 8, s0 at sp + 0, loaded back at 0x838ec - 0x838f0 (the return at
                      0x838f8, sp = sp + 16 at 0x838f4) and at 0x83904 - 0x83908 (before the tail jump, sp = sp + 16
                      at 0x8390c). These two 8-byte stores into its own frame are its only stores. No side-stack
                      frame, no frame pointer, no realignment.
     0x838cc          s0 = ticked (a0, kept to 0x83900).
     0x838d0          call of check_ack_settle (0x85d88 = transportb_sigma TB_check_ack_settle), return address
                      0x838d4.
     0x838d4          call of check_state_settle (0x85dbc), return address 0x838d8.
     0x838d8          call of check_inflight_settle (0x85fdc), return address 0x838dc.
     0x838dc          call of check_keepalive_settle (0x860a4), return address 0x838e0.
     0x838e0 - 0x838e8 a0 = the 4-byte signed load of g_raw (0x5ded60, pc-relative, no instrumented check); g_raw = 0
                      goes to 0x838fc; else ra and s0 loaded back, sp = sp + 16, return (a0 not stated: void).
     0x838fc          call of check_latest_queue (0x86104), return address 0x83900.
     0x83900          ticked = 0 (s0, 64 bits) goes to 0x838ec (the return).
     0x83904 - 0x83910 ra and s0 loaded back, sp = sp + 16; jump (no link) to check_latest_drain (0x862b8) at
                      0x83910, from settle's entry sp with settle's ra: its return is settle's return.
   The tests are settle_m's: truth (g_raw B4) and truth ticked, read through tw_at, with B4 = Bw: each check's model
   returns the world it was given, and the world relation at Bw holds again after each call. A leaf's post
   (lib/B/Prog/LeafCgKit.v dleaf_post) keeps every byte outside its stack window, and the harness globals lie in the
   image, far below the stack. A donor callee's post (check_inflight_settle, check_latest_queue:
   DgnTransportBCg.v decode_cg_post, YCbq.v acall_kept) keeps the image bytes that are not owned statics and not
   errno, and every byte of G is such a byte (gx_ok, gx_noerrno): TransportGCg.v gx_kept_of_acall_kept, then
   TWorldG.v tw_kept_G.
   The traps are the callees': each is ruled out by its statement's model premise, which settle_m's let* chain
   supplies (check_ack_settle_m, check_state_settle_m, check_inflight_settle_m, check_keepalive_settle_m,
   check_latest_queue_m, check_latest_drain_m, each at Bw).
   Error paths: none. settle's own load of g_raw carries no instrumented check, and its code calls no
   __asan_report_* entry, no __asan_handle_no_return and no abort.
   Image B against image A's code (lib/A/Prog/settle_cg.v, 0x83cac, 84 bytes, 21 words): the same 21 words in the
   same order with image B's addresses and branch offsets. Image B adds no UBSan check (the function has no unimp
   word) and no trap: the premise list is image A's.
   Callee texts assumed (pc order):
     check_ack_settle as check_ack_settle_cg.v transport_check_ack_settle_cg (a leaf, read at this unit's model by
       DgnTransportBCg.v transport_leaf_at; call at 0x838d0);
     check_state_settle as check_state_settle_cg.v transport_check_state_settle_cg (leaf; call at 0x838d4); it asks
       the 192 bytes of GOT.t[] and of OW.t[] addressable: trans_settle_cells (GOT's and OW's zero shadow);
     check_inflight_settle as check_inflight_settle_cg.v transport_check_inflight_settle_cg at transportb_sigma
       TB_check_inflight_settle (donor form, the same journal; call at 0x838d8);
     check_keepalive_settle as check_keepalive_settle_cg.v transport_check_keepalive_settle_cg (leaf; call at
       0x838dc);
     check_latest_queue as check_latest_queue_cg.v transport_check_latest_queue_cg at transportb_sigma
       TB_check_latest_queue (donor form; call at 0x838fc), with its queue-length premise (settle's own);
     check_latest_drain as check_latest_drain_cg.v transport_check_latest_drain_cg (leaf; tail jump at 0x83910); it
       asks g_q's and g_cmd's payloads addressable: trans_settle_cells (their zero shadow).
   Each leaf's other premises (asan_cells, the runtime cells' and the harness globals' places off its stack window,
   its footprint ranges) come from transport_cells, the journal's window and the world relation at the call state.
   No runtime entry is called.
   Stack: 16 bytes of its own; the calls run from sp - 16, and the largest window among them is check_latest_queue's
   CLQ_STK (check_inflight_settle's CIS_STK and a leaf's ESTACK are smaller); the tail jump runs from the entry sp
   (a leaf's ESTACK): SETTLE_STK = 16 + CLQ_STK. Image B's CLQ_FRAME is 112 (image A's 80), so SETTLE_STK is 8320
   (image A's 8288).

   The callers: LLVMFuzzerTestOneInput (0x81ba4 with a0 = 0, after its call of diginet_session_close at 0x81b9c;
   0x81fac with a0 = 1, after its call of diginet_session_tick at 0x81fa4; 0x828f8 with a0 = 0) and receive (0x83804,
   with a0 = s2, the result of its call of m_rx at 0x837dc or the value it computed at 0x837ac). Image A's three
   calls in LLVMFuzzerTestOneInput are at 0x81bec (a0 = 1, after diginet_session_tick), 0x82280 and 0x82530 (a0 = 0),
   and receive's at 0x83a48: the pcs and the order of the two arms differ, the arguments do not.
   Each caller is a G-form walk; it lifts this statement with gx_call_cg and supplies the journal, the world
   relation, the model call and the queue-length invariant from its own walk. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_inflight_settle_cg check_latest_queue_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  check_ack_settle_cg check_state_settle_cg check_keepalive_settle_cg check_latest_drain_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TSess0.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module LAS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_ack_settle_cg.
Module LSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_settle_cg.
Module LKS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_keepalive_settle_cg.
Module LLD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_drain_cg.
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
   ranges of the record's as_zero_shadow (the rows (0x5e4f60, 0x5e5040 - 0x5e4f60), (0x5f2ce0, 0x5f2e10 - 0x5f2ce0),
   (0x5f1880, 0x5f2880 - 0x5f1880) and (0x5e5080, 0x5ef080 - 0x5e5080) of lib/B/YF0m.v Tfib_zero_shadow).
   check_state_settle's statement asks GOT.t[] and OW.t[] addressable, check_latest_drain's asks g_q's and g_cmd's
   payloads addressable. *)
Definition trans_settle_cells (B : asyms) : Prop :=
  decode_zshadow_at B TB_GOT (TB_GOT + TW.SZ_GOT) /\
  decode_zshadow_at B TB_OW (TB_OW + TW.SZ_OW) /\
  decode_zshadow_at B TB_g_q (TB_g_q + TW.SZ_g_q) /\
  decode_zshadow_at B TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd).

Section settle. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportBCg.v decode_cg_post with no event, no written range, no meter charge, and X: the
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
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TC.settle_m Bw ticked = Some (Bw', tt) ->
    (forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN) ->
    st_nev S + k + SETTLE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_settle_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells, the shadow of GOT, OW, g_q and g_cmd (trans_settle_cells),
   the allocator and meter laws, G inside the image, outside the allocator's statics and outside errno (a donor
   callee keeps every byte of G, so the world relation holds after it: gx_kept_of_acall_kept), and the statements of
   the six callees give the contract at TB_settle. *)
Definition transport_settle_cg_holds_stmt : Prop :=
  transport_cells B -> trans_settle_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS_B -> gx_noerrno B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LAS.transport_check_ack_settle_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSS.transport_check_state_settle_cg) fx') ->
  (forall fx' : YK11.FPState,
     @transport_check_inflight_settle_cg fx' rc B MT (transportb_sigma TB_check_inflight_settle)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LKS.transport_check_keepalive_settle_cg) fx') ->
  (forall fx' : YK11.FPState,
     @transport_check_latest_queue_cg fx' rc B MT (transportb_sigma TB_check_latest_queue)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLD.transport_check_latest_drain_cg) fx') ->
  transport_settle_cg (transportb_sigma TB_settle).
End settle.
