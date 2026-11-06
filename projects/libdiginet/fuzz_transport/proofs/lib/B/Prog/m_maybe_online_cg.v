(* m_maybe_online_cg: image B's m_maybe_online (fuzz/fuzz_transport.c:237-243; model lib/TModel/TCb.v
   m_maybe_online_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x851d4 = DgnTransportBAddr.v transportb_sigma
   TB_m_maybe_online, size 80, as STATEMENTS only (no proof). It is a G-form caller-journal walk: the caller's journal
   is lib/A/W_journalG.v ajournal_gx over G = lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0, OUT = []),
   and the post is lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS_B). m_maybe_online stores
   into M, a harness global, and tail-jumps to m_set, a G-form walk (m_set_cg.v), so it takes this form and not the
   footprint-leaf form (m_set_cg.v says why). Form: lib/A/Prog/m_maybe_online_cg.v. The difference from image A:
   on A m_set is inlined and m_maybe_online has a 16-byte frame; here m_maybe_online takes no frame and tail-jumps to
   m_set, so m_set's statement is a callee premise and m_set's 16 bytes are its stack window.

   The contract. No argument. The memory relates to the world Bw by the world relation of image B (TWorldG.v tw_at
   at TWorldB.v TMAP_B, read through aview), and Bw' is the model's world after the call (m_maybe_online_m Bw =
   Some (Bw', tt)). The function returns to ra with the callee-saved registers kept, no allocator event and no meter
   charge, the caller's side-stack frames and blocks exactly, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at
   or above alloc_ceiling outside the call's stack window [sp - 16, sp), the image bytes outside G, the owned statics
   and errno, the caller's block and frame bytes outside monline_wr Bw), and the world relation at Bw'. This is what
   the plain contract (lib/Prog/T/m_maybe_online_c.v) says: void; wmem rsegs m' B' with B' the model's world; munch
   of the frame and the world only.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded segments equal the pin's, and this
   function's 80 code bytes are equal in both files):
     0x851d4 - 0x851e4 a2 = &M = 0x5dede0 (TB_M); a0 = M.state (the 4-byte signed load at M + 12); a1 = 1; M.state <> 1
                      (S_WAKING) goes to 0x85220 and returns (:239). No frame: sp, ra and every callee-saved register
                      are untouched.
     0x851e8 - 0x851f4 M.e2_acked (the 4-byte signed load at M + 16) = 0, or M.e1_us (M + 20) = 0, goes to 0x85220 and
                      returns (:239).
     0x851f8 - 0x85218 a0 = the 4-byte unsigned load of g_cfg.keepalive_ms (0x5ded18 = TB_g_cfg + 24); a1 = the 8-byte
                      load of M.last_rx (M + 32); a3 = a0 * 1000; a0 = 2 (S_ONLINE); a3 = a3 + a1 (mod 2^64);
                      a1 = 2 (R_ONLINE); the 8-byte store of a3 at M + 48 (next_ka, :240; h_ms_m v = v * 1000 with
                      v < 2^32 does not wrap). No instrumented check guards a store or load at a constant offset of M
                      or g_cfg; m_maybe_online reads no runtime cell.
     0x8521c          jump (no link) to m_set at 0x85224 = transportb_sigma TB_m_set (:241), with a0 = 2, a1 = 2, ra, sp
                      and the callee-saved registers of m_maybe_online's entry.
     0x85220          return (a0 .. a1 not stated: void).
   m_set is entered at the world B1 = set_M_next_ka Bw (u64 (M.last_rx + h_ms_m keepalive_ms)) (M.state = S_WAKING
   and OW.n as in Bw), and returns to m_maybe_online's ra: its post is m_maybe_online's post (the same journal, the
   same stack window; M.state is S_WAKING, never S_ONLINE, so m_set changes the state, and its written range
   mset_st_wr B1 S_ONLINE lies inside monline_wr Bw).
   Error paths: none in m_maybe_online's own code (no instrumented check, no call of an error function). m_set's are
   ruled out inside m_set's statement.
   Trap paths: none in m_maybe_online's own code (no UBSan check: the arithmetic is unsigned). m_set's are ruled out
   inside m_set's statement (its model premise m_set_m B1 S_ONLINE R_ONLINE = Some _ is the model's last step, :241).
   Callee texts assumed: m_set as m_set_cg.v transport_m_set_cg at transportb_sigma TB_m_set (0x85224).
   Stack: none of its own; m_set's 16 bytes below the entry sp: MONLINE_STK = MSET_STK.

   The caller: m_rx (call at 0x84fbc). It supplies the G journal of its own walk and the world relation.

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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* m_maybe_online takes no frame; its one call of m_set is a tail jump from its entry sp, so its stack window is
   m_set's. *)
Definition MONLINE_FRAME : Z := 0.
Definition MONLINE_STK : Z := MSET_STK.
(* No allocator event: neither m_maybe_online nor m_set calls malloc or free or takes a side-stack frame. *)
Definition MONLINE_EV : Z := MSET_EV.
(* The bytes the call stores into G, exactly: when M.state = S_WAKING, M.e2_acked <> 0 and M.e1_us <> 0, M.next_ka
   and m_set's stores (m_set_cg.v mset_wr; M.state is S_WAKING, so m_set changes the state); none otherwise. *)
Definition monline_wr (Bw : list byte) (a : Z) : Prop :=
  TW.M_state Bw = TCB.S_WAKING /\ TCB.truth (TW.M_e2_acked Bw) = true /\ TCB.truth (TW.M_e1_us Bw) = true /\
  (twb_fld TW.OFF_M TB_M TW.A_M_next_ka 8 a \/ mset_wr Bw a).

Section monline. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range
   monline_wr Bw, no meter charge, and X: the world relation at the model's world Bw'. *)
Definition transport_monline_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    MONLINE_STK MONLINE_EV 0 (monline_wr Bw)
    (fun regs2 W2 mem2 => tw_at TMAP_B (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_m_maybe_online_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bw Bw' : list byte),
    ajournal_gx G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MONLINE_STK -> spZ regs <= sp0 ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TCB.m_maybe_online_m Bw = Some (Bw', tt) ->
    st_nev S + k + MONLINE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_monline_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells, the allocator and meter laws, G inside the image and
   outside the allocator's statics, and the contract of m_set give the contract at TB_m_maybe_online.
   (transport_cells B is the premise every statement of the unit takes; m_maybe_online's own code reads no runtime
   cell, and the shadow of OW that m_set's checks read is m_set's own premise, trans_ow_cells.) *)
Definition transport_m_maybe_online_cg_holds_stmt : Prop :=
  transport_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B G_HARNESS_B ->
  (forall fx' : YK11.FPState, @transport_m_set_cg fx' rc B MT (transportb_sigma TB_m_set)) ->
  transport_m_maybe_online_cg (transportb_sigma TB_m_maybe_online).
End monline.
