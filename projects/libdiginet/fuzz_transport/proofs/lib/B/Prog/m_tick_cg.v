(* m_tick_cg: image B's m_tick (fuzz/fuzz_transport.c:246-252, with m_lost :210-215 inlined; model
   lib/TModel/TCb.v m_tick_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x8383c = DgnTransportBAddr.v
   transportb_sigma TB_m_tick, size 132, as STATEMENTS only (no proof). It is a G-form caller-journal walk: the
   caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/B/TransportGB.v G_HARNESS_B with no out cell
   (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS_B).
   Form: lib/A/Prog/m_tick_cg.v. The difference from image A: on A m_tick stores nothing and tail-jumps to m_lost
   (which inlines m_set); here image B has no m_lost function: m_tick makes m_lost's two stores itself (M.fly.on and
   M.desk_counter_valid) and tail-jumps to m_set, a G-form walk (m_set_cg.v), which shares the caller's journal.

   The contract. No argument. The memory relates to the world Bw by the world relation of image B (TWorldG.v tw_at
   at TWorldB.v TMAP_B, read through aview), and Bw' is the model's world after the call (m_tick_m Bw =
   Some (Bw', tt)). The function returns to ra with the callee-saved registers kept, no allocator event and no meter
   charge, the caller's side-stack frames and blocks exactly, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at
   or above alloc_ceiling outside the call's stack window [sp - 16, sp), the image bytes outside G, the owned statics
   and errno, the caller's block and frame bytes outside mtick_wr Bw), and the world relation at Bw'. This is what
   the plain contract (lib/Prog/T/m_tick_c.v) says: void; wmem rsegs m' B' with B' the model's world; munch of the
   frame and the world only.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded segments equal the pin's, and this
   function's 132 code bytes are equal in both files):
     0x8383c - 0x83844 a0 = &M = 0x5dede0 (TB_M); a1 = the 4-byte signed load of M.state (M + 12). No frame: sp, ra and
                      every callee-saved register are untouched.
     0x83848 - 0x8384c M.state = 2 (S_ONLINE) goes to 0x83884.
     0x83850 - 0x83854 M.state <> 1 (S_WAKING) goes to 0x838a8 and returns.
     0x83858 - 0x83878 (S_WAKING, :248) a1 = the 8-byte load of g_now (0x5ded80 = TB_g_now); a2 = the 8-byte load of
                      M.wake_sent (M + 40); a3 = the 4-byte unsigned load of g_cfg.wake_timeout_ms (0x5ded2c = TB_g_cfg
                      + 44); a1 = a1 - a2 (mod 2^64), a2 = a3 * 1000; a1 < a2 (unsigned) goes to 0x838a8 and returns.
     0x8387c - 0x83880 a1 = 6 (R_WAKE_TIMEOUT); jump to 0x838b0 (:249).
     0x83884 - 0x838a4 (S_ONLINE, :250) a1 = the 8-byte load of g_now; a2 = the 8-byte load of M.last_rx (M + 32);
                      a3 = the 4-byte unsigned load of g_cfg.offline_ms (0x5ded28 = TB_g_cfg + 40); a1 = a1 - a2
                      (mod 2^64), a2 = a3 * 1000; a1 >= a2 (unsigned) goes to 0x838ac.
     0x838a8          return (a0 .. a3 not stated: void).
     0x838ac          a1 = 4 (R_SILENCE) (:251).
     0x838b0 - 0x838b4 (m_lost inlined, :212-213) the 4-byte stores of 0 at M + 76 (desk_counter_valid) and at M + 96
                      (fly.on). No instrumented check guards a store or load at a constant offset of M, g_now or
                      g_cfg; m_tick reads no runtime cell.
     0x838b8 - 0x838bc a0 = 0 (S_IDLE); jump (no link) to m_set at 0x85224 = transportb_sigma TB_m_set (:214), with
                      a1 = why (6 or 4), ra, sp and the callee-saved registers of m_tick's entry.
   Each test is the model's: h_ms_m v = v * 1000 mod 2^64 (v < 2^32, so no wrap), u64 (g_now - t) = the 64-bit
   difference. m_set is entered at the world B1 = m_lost_m's set_M_desk_counter_valid (set_M_fly_on Bw 0) 0 (M.state
   and OW.n as in Bw), and returns to m_tick's ra: its post is m_tick's post (the same journal, the same stack window;
   on these two paths M.state is S_WAKING or S_ONLINE, never S_IDLE, so m_set changes the state, and its written range
   mset_st_wr B1 S_IDLE lies inside mtick_wr Bw).
   Error paths: none in m_tick's own code (no instrumented check, no call of an error function). m_set's are ruled out
   inside m_set's statement.
   Trap paths: none in m_tick's own code (no UBSan check: the arithmetic is unsigned). m_set's are ruled out inside
   m_set's statement (its model premise m_set_m B1 S_IDLE why = Some _ is m_lost_m's, the model's last step).
   Callee texts assumed: m_set as m_set_cg.v transport_m_set_cg at transportb_sigma TB_m_set (0x85224).
   Stack: none of its own; m_set's 16 bytes below the entry sp: MTICK_STK = MSET_STK.

   The callers: LLVMFuzzerTestOneInput (call at 0x81f94), io_recv (call at 0x833e0) and m_rx (call at 0x84fc0). Each
   supplies the G journal of its own walk and the world relation.

   Names this file reads from lib/B/Prog/DgnTransportBCg.v (image B's twin of lib/A/Prog/DgnTransportCg.v), at the A
   name: transport_cells. *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TCb.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* m_tick takes no frame; its one call of m_set is a tail jump from m_tick's entry sp, so its stack window is
   m_set's. *)
Definition MTICK_FRAME : Z := 0.
Definition MTICK_STK : Z := MSET_STK.
(* No allocator event: neither m_tick nor m_set calls malloc or free or takes a side-stack frame. *)
Definition MTICK_EV : Z := MSET_EV.
(* The model's test for a call of m_lost (TCb.v m_tick_m, :248 and :250). *)
Definition mtick_lost (Bw : list byte) : bool :=
  ((TW.M_state Bw =? TCB.S_WAKING) &&
     (TCB.h_ms_m (TW.Cfg_wake_timeout_ms Bw) <=? TS0.u64 (TW.g_now Bw - TW.M_wake_sent Bw))) ||
  ((TW.M_state Bw =? TCB.S_ONLINE) &&
     (TCB.h_ms_m (TW.Cfg_offline_ms Bw) <=? TS0.u64 (TW.g_now Bw - TW.M_last_rx Bw))).
(* The stores of m_lost (fuzz_transport.c:210-215; image B inlines it into m_tick, which makes its two stores and
   tail-jumps to m_set): M.desk_counter_valid and M.fly.on; when M.state is not S_IDLE also m_set's stores. Image
   B's twin of lib/A/Prog/m_lost_cg.v mlost_wr. *)
Definition mlost_wr (Bw : list byte) (a : Z) : Prop :=
  twb_fld TW.OFF_M TB_M TW.A_M_desk_counter_valid 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_fly_on 4 a \/
  mset_st_wr Bw TCB.S_IDLE a.
(* The bytes the call stores into G, exactly: m_lost's when the test holds, none otherwise. *)
Definition mtick_wr (Bw : list byte) (a : Z) : Prop := mtick_lost Bw = true /\ mlost_wr Bw a.

Section mtick. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range
   mtick_wr Bw, no meter charge, and X: the world relation at the model's world Bw'. *)
Definition transport_mtick_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    MTICK_STK MTICK_EV 0 (mtick_wr Bw)
    (fun regs2 W2 mem2 => tw_at TMAP_B (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_m_tick_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bw Bw' : list byte),
    ajournal_gx G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MTICK_STK -> spZ regs <= sp0 ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TCB.m_tick_m Bw = Some (Bw', tt) ->
    st_nev S + k + MTICK_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_mtick_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells, the allocator and meter laws, G inside the image and
   outside the allocator's statics, and the contract of m_set give the contract at TB_m_tick. (transport_cells B is
   the premise every statement of the unit takes; m_tick's own code reads no runtime cell.) *)
Definition transport_m_tick_cg_holds_stmt : Prop :=
  transport_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B G_HARNESS_B ->
  (forall fx' : YK11.FPState, @transport_m_set_cg fx' rc B MT (transportb_sigma TB_m_set)) ->
  transport_m_tick_cg (transportb_sigma TB_m_tick).
End mtick.
