(* m_tick_cg: the ASan walk contract of m_tick (fuzz/fuzz_transport.c:246-252; model lib/TModel/TCb.v m_tick_m) on
   fuzz_transport.asan (e89be137db17) at 0x83c34 = transport_sigma TS_m_tick, size 120, as STATEMENTS only (no
   proof). It is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over
   G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v
   transport_cg_post (acall_kept_g over G_HARNESS). m_tick stores nothing itself; its one callee, m_lost, is a G-form
   walk (m_lost_cg.v), which it reaches by a tail jump, so the two share the caller's journal.

   The contract. No argument. The memory relates to the world Bw by the world relation of image A (TWorldG.v tw_at
   at TWorldA.v TMAP_A, read through aview), and Bw' is the model's world after the call (m_tick_m Bw =
   Some (Bw', tt)). The function returns to ra with the callee-saved registers kept, no allocator event and no meter
   charge, the caller's side-stack frames and blocks exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at or
   above alloc_ceiling outside the call's stack window [sp - 16, sp), the image bytes outside G, the owned statics and
   errno, the caller's block and frame bytes outside mtick_wr Bw), and the world relation at Bw'. This is what the
   plain contract (lib/Prog/T/m_tick_c.v) says: void; wmem rsegs m' B' with B' the model's world; munch of the frame
   and the world only.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this
   function's 120 code bytes are equal in both files):
     0x83c34 - 0x83c3c a0 = &M = 0x5df160 (TA_M); a1 = the 4-byte signed load of M.state (M + 12). No frame: sp,
                      ra and every callee-saved register are untouched; no store.
     0x83c40 - 0x83c44 M.state = 2 (S_ONLINE) goes to 0x83c7c.
     0x83c48 - 0x83c4c M.state <> 1 (S_WAKING) goes to 0x83ca0 and returns.
     0x83c50 - 0x83c70 (S_WAKING, :248) a0 = the 8-byte load of M.wake_sent (M + 40); a1 = the 8-byte load of g_now
                      (0x5df100); a2 = the 4-byte unsigned load of g_cfg.wake_timeout_ms (0x5df0ac); a1 = a1 - a0
                      (mod 2^64), a0 = a2 * 1000; a1 < a0 (unsigned) goes to 0x83ca0 and returns.
     0x83c74 - 0x83c78 a0 = 6 (R_WAKE_TIMEOUT); jump (no link) to m_lost at 0x85004 (:249).
     0x83c7c - 0x83c9c (S_ONLINE, :250) a0 = the 8-byte load of M.last_rx (M + 32); a1 = the 8-byte load of g_now;
                      a2 = the 4-byte unsigned load of g_cfg.offline_ms (0x5df0a8); a1 = a1 - a0 (mod 2^64),
                      a0 = a2 * 1000; a1 >= a0 (unsigned) goes to 0x83ca4.
     0x83ca0          return (a0 .. a2 not stated: void).
     0x83ca4 - 0x83ca8 a0 = 4 (R_SILENCE); jump (no link) to m_lost at 0x85004 (:251).
   Each test is the model's: h_ms_m v = v * 1000 mod 2^64 (v < 2^32, so no wrap), u64 (g_now - t) = the 64-bit
   difference. m_lost is entered with ra, sp and the callee-saved registers of m_tick's entry and a0 = why, and
   returns to m_tick's ra: its post is m_tick's post (the same journal, the same stack window, mlost_wr Bw inside
   mtick_wr Bw on these two paths).
   Error paths: none (no instrumented check, no call of an error path, no trap).
   Callee texts assumed: m_lost as m_lost_cg.v transport_m_lost_cg at transport_sigma TS_m_lost (0x85004).
   Stack: none of its own; m_lost's 16 bytes below the entry sp: MTICK_STK = MLOST_STK.

   The callers: LLVMFuzzerTestOneInput (0x81bd4), io_recv (0x8353c) and m_rx (0x84e1c). Each supplies the G journal
   of its own walk and the world relation. *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TCb.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* m_tick takes no frame; both calls of m_lost are tail jumps from m_tick's entry sp, so its stack window is
   m_lost's. *)
Definition MTICK_FRAME : Z := 0.
Definition MTICK_STK : Z := MLOST_STK.
(* No allocator event: neither m_tick nor m_lost calls malloc or free or takes a side-stack frame. *)
Definition MTICK_EV : Z := MLOST_EV.
(* The model's test for a call of m_lost (TCb.v m_tick_m, :248 and :250). *)
Definition mtick_lost (Bw : list byte) : bool :=
  ((TW.M_state Bw =? TCB.S_WAKING) &&
     (TCB.h_ms_m (TW.Cfg_wake_timeout_ms Bw) <=? TS0.u64 (TW.g_now Bw - TW.M_wake_sent Bw))) ||
  ((TW.M_state Bw =? TCB.S_ONLINE) &&
     (TCB.h_ms_m (TW.Cfg_offline_ms Bw) <=? TS0.u64 (TW.g_now Bw - TW.M_last_rx Bw))).
(* The bytes the call stores into G, exactly: m_lost's when the test holds, none otherwise. *)
Definition mtick_wr (Bw : list byte) (a : Z) : Prop := mtick_lost Bw = true /\ mlost_wr Bw a.

Section mtick. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range mtick_wr Bw,
   no meter charge, and X: the world relation at the model's world Bw'. *)
Definition transport_mtick_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    MTICK_STK MTICK_EV 0 (mtick_wr Bw)
    (fun regs2 W2 mem2 => tw_at TMAP_A (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_m_tick_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MTICK_STK -> spZ regs <= sp0 ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TCB.m_tick_m Bw = Some (Bw', tt) ->
    st_nev S + k + MTICK_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_mtick_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells, the allocator and meter laws, G inside the image and
   outside the allocator's statics, and the contract of m_lost give the contract at TS_m_tick. (transport_cells B is
   the premise every statement of the unit takes; m_tick's own code reads no runtime cell.) *)
Definition transport_m_tick_cg_holds_stmt : Prop :=
  transport_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @transport_m_lost_cg fx' rc B MT (transport_sigma TS_m_lost)) ->
  transport_m_tick_cg (transport_sigma TS_m_tick).
End mtick.
