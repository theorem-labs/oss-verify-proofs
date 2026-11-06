(* check_inflight_settle_cg: the ASan walk contract of check_inflight_settle (fuzz/fuzz_transport.c:744-771; model
   lib/TModel/TCb.v check_inflight_settle_m) on fuzz_transport.asan (e89be137db17) at 0x85d50 =
   transport_sigma TS_check_inflight_settle, size 196, as STATEMENTS only (no proof). It stores into no harness global
   and calls a program function, diginet_session_deadline, so it takes decode's caller-journal form
   (lib/A/Prog/DgnTransportCg.v decode_cg_post over the caller's donor journal ajournal); a G-form caller lifts it
   with lib/A/Prog/TransportGCg.v gx_call_cg.

   The contract. No argument. The memory relates to the world Bw by image A's world relation (TWorldG.v tw_at at
   TWorldA.v TMAP_A, read through aview), and check_inflight_settle_m Bw = Some (Bw', tt). The function returns to
   ra with the callee-saved registers kept, no allocator event, no meter charge, every byte outside its stack window
   kept (it stores nothing outside its own frame: E is empty), and Bw' = Bw. This is what the plain contract
   (lib/Prog/T/check_inflight_settle_c.v) says: void; B' = B and wmem rsegs m' B; munch of the frame only. Its wmem
   premise becomes tw_at, and mem_inv and w_off_stack are dropped (the journal's window premises
   keep the frame off the world).

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's), 49 words:
     0x85d50          sp = sp - 32; ra, s0, s1, s2 at sp + 24 .. sp + 0 (0x85d54 - 0x85d60), loaded back at 0x85df4 -
                      0x85e00; sp = sp + 32 at 0x85e04, the return at 0x85e08. No side-stack frame, no frame pointer.
                      These four 8-byte stores into its own frame are its only stores.
     0x85d64 - 0x85d74  the 4-byte loads of GOT.acked (GOT + 216 = 0x5e53b8) and OW.acked (OW + 216 = 0x5f3138);
                      they differ: the trap.
     0x85d78 - 0x85d8c  s0 = &M (0x5df160); the 4-byte load of M.fly_on (M + 96); s2 / s1 = the pc-relative bases of
                      g_now (0x5df100) and g_cfg (0x5df080); M.fly_on = 0 goes to 0x85dac.
     0x85d90 - 0x85da8  the 8-byte loads of g_now and M.fly_sent (M + 112), the 4-byte unsigned load of
                      g_cfg.ack_timeout_ms (g_cfg + 28 = 0x5df09c); g_now - M.fly_sent (mod 2^64) >= ack_timeout_ms *
                      1000 (unsigned): the trap.
     0x85dac - 0x85db8  a1 = the 8-byte load of g_now, a0 = &g_s (0x5df9c0); the call of diginet_session_deadline
                      (0x8a9d4 = transport_sigma TS_diginet_session_deadline); a0 = its result d.
     0x85dbc - 0x85dd0  a1 = the 8-byte load of g_now again; d < g_now (unsigned): the trap; g_now + 1000000
                      (mod 2^64) < d (unsigned): the trap.
     0x85dd4 - 0x85df0  the 4-byte load of M.fly_on again; 0 returns; else the 4-byte unsigned load of
                      g_cfg.ack_timeout_ms and the 8-byte load of M.fly_sent; ack_timeout_ms * 1000 + M.fly_sent
                      (mod 2^64) < d (unsigned): the trap; else the return (a0 = d, not stated: void).
   The trap: 0x85e0c call of __asan_handle_no_return (0x5a4c4), 0x85e10 call of abort (0x93734); every branch to it is
   ruled out by check_inflight_settle_m Bw = Some _: its tests are the code's tests in the code's order, read through
   tw_at (TWorld.v GOT_acked, OW_acked, M_fly_on, M_fly_sent, g_now, Cfg_ack_timeout_ms), with h_ms_m v = v * 1000
   mod 2^64 and u64 the 64-bit sum or difference, and d is diginet_session_deadline_m Bw (g_now Bw) (the model's
   let*, whose value the callee's statement returns). The loads after the call read the same bytes: the callee keeps
   every byte outside its stack window [sp - 32 - ESTACK, sp - 32) (the leaf post, LeafCgKit.v dleaf_post), and the
   harness globals lie in the image, far below the stack.
   Error paths: none. Its own loads of M, GOT, OW, g_now and g_cfg carry no instrumented check, and the code calls no
   __asan_report_* entry.
   Callee texts assumed: diginet_session_deadline as its leaf statement (diginet_session_deadline_cg.v
   transport_diginet_session_deadline_cg, read at this unit's model by DgnTransportCg.v transport_leaf_at) at
   transport_sigma TS_diginet_session_deadline, entered with a0 = &g_s, a1 = g_now. What it asks besides the
   journal's facts: tw_at at csw_view of the call memory (the same world Bw), diginet_session_deadline_m Bw (g_now Bw)
   = Some d (from the model premise), asan_cells (transport_cells rows 1-2), and g_s's payload [0x5df9c0,
   0x5df9c0 + 18264) addressable: trans_cis_cells B, the record's zero shadow of those 2283 whole granules (the
   Tfib_zero_shadow row (0x5df9c0, 0x5e4118 - 0x5df9c0), lib/A/AF0m.v:3105), read at the call state through
   DgnTransportCg.v decode_zshadow_rd. No runtime entry is called.
   Stack: 32 bytes of its own and the ESTACK window of the leaf call below sp - 32: CIS_STK.

   The caller is settle (the call at 0x83cc4, return address 0x83cc8), with no argument. It supplies the journal, the
   world relation and the model call from its own walk. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_session_deadline_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module LSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_deadline_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_inflight_settle's frame (`sp = sp - 32` at its entry; no realignment) and the ESTACK window its one callee,
   the leaf diginet_session_deadline, uses below sp - 32 (LeafCgKit.v ecall_pre, dleaf_post). *)
Definition CIS_FRAME : Z := 32.
Definition CIS_STK : Z := CIS_FRAME + ESTACK.
(* No allocator event: neither it nor diginet_session_deadline calls malloc or free or takes a side-stack frame. *)
Definition CIS_EV : Z := 0.

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow. The
   instrumented loads of diginet_session_deadline read g_s's fields. *)
Definition trans_cis_cells (B : asyms) : Prop := decode_zshadow_at B TA_g_s (TA_g_s + TW.SZ_g_s).

Section cis. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportCg.v decode_cg_post with no event, no written range, no meter charge, and X: the
   model's world is the world it was given. *)
Definition transport_cis_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs CIS_STK CIS_EV 0
    (fun _ => False) (fun _ _ _ => Bw' = Bw).

(* The contract at entry address a, in the caller-journal form. *)
Definition transport_check_inflight_settle_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bw Bw' : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CIS_STK -> spZ regs <= sp0 ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TC.check_inflight_settle_m Bw = Some (Bw', tt) ->
    st_nev S + k + CIS_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_cis_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells, g_s's shadow (trans_cis_cells), the allocator and meter
   laws, and the leaf statement of diginet_session_deadline give the contract at TS_check_inflight_settle. *)
Definition transport_check_inflight_settle_cg_holds_stmt : Prop :=
  transport_cells B -> trans_cis_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSD.transport_diginet_session_deadline_cg) fx') ->
  transport_check_inflight_settle_cg (transport_sigma TS_check_inflight_settle).
End cis.
