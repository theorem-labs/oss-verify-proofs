(* m_maybe_online_cg: the ASan walk contract of m_maybe_online (fuzz/fuzz_transport.c:237-243, with m_set :196-207
   inlined; model lib/TModel/TCb.v m_maybe_online_m) on fuzz_transport.asan (e89be137db17) at 0x850f0 =
   transport_sigma TS_m_maybe_online, size 284, as STATEMENTS only (no proof). It is a G-form caller-journal walk: the
   caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0,
   OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS).
   m_maybe_online calls no function but stores into M and OW, two harness globals, so it takes this form and not the
   footprint-leaf form (m_lost_cg.v says why). twa_fld, mset_wr and trans_ow_cells are m_lost_cg.v's (m_set is
   inlined into both).

   The contract. No argument. The memory relates to the world Bw by the world relation of image A (TWorldG.v tw_at
   at TWorldA.v TMAP_A, read through aview), and Bw' is the model's world after the call (m_maybe_online_m Bw =
   Some (Bw', tt)). The function returns to ra with the callee-saved registers kept, no allocator event and no meter
   charge, the caller's side-stack frames and blocks exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at or
   above alloc_ceiling outside the call's stack window [sp - 16, sp), the image bytes outside G, the owned statics and
   errno, the caller's block and frame bytes outside monline_wr Bw), and the world relation at Bw'. This is what the
   plain contract (lib/Prog/T/m_maybe_online_c.v) says: void; wmem rsegs m' B' with B' the model's world; munch of
   the frame and the world only.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this
   function's 284 code bytes are equal in both files):
     0x850f0 - 0x850f4 sp = sp - 16: the frame is 16 bytes; ra at sp + 8, loaded back at 0x851cc. No side-stack frame,
                      no frame pointer, no other register saved.
     0x850f8 - 0x85118 a2 = &M = 0x5df160 (TA_M); M.state (the 4-byte signed load at M + 12) <> 1 (S_WAKING), or
                      M.e2_acked (M + 16) = 0, or M.e1_us (M + 20) = 0 goes to 0x851cc and returns (:239).
     0x8511c - 0x85150 a1 = the 8-byte load of M.last_rx (M + 32); a5 = the 4-byte unsigned load of
                      g_cfg.keepalive_ms (0x5df098); a0 = the 8-byte load of the GOT word 0xa4090 (it holds
                      0xac9f8); a3 = &OW = 0x5f3060 (TA_OW); a6 = a5 * 1000; a4 = OW.n (the 4-byte signed load at
                      OW + 0); a5 = the 8-byte load at 0xac9f8 (0x7fff8000, the shadow base): transport_cells rows 1-2;
                      the 8-byte store of a6 + a1 (mod 2^64) at M + 48 (next_ka, :240; h_ms_m v = v * 1000 with
                      v < 2^32 does not wrap). No instrumented check guards a store or load at a constant offset of M,
                      OW or g_cfg.
     0x85154          15 < OW.n (signed) goes to 0x851bc (the log is full, :200). m_set's early return (:198-199) is
                      not in the code: M.state is S_WAKING here, never S_ONLINE.
     0x85158 - 0x851b8 for p = OW + 4 + 12 * OW.n (= &OW.t[OW.n]): the instrumented check of the 4-byte store at p
                      (the shadow byte k at (p >> 3) + 0x7fff8000; k = 0 goes on; else (p & 7) + 3 < k (signed) goes
                      on; else the error path), the store of 2 (S_ONLINE) at p; the same check and the store of 1 (the
                      old state, S_WAKING) at p + 4; the same check and the store of 2 (R_ONLINE) at p + 8
                      (:201-203).
     0x851bc - 0x851c8 the 4-byte stores of OW.n + 1 at OW + 0 (:205) and of 2 at M + 12 (M.state = S_ONLINE, :206).
     0x851cc - 0x851d4 ra loaded back, sp = sp + 16, return. a0 .. a7 at the return are not stated (void).
   Error paths (3 calls of errpath_store4, 0x59928; no trap path) and the fact that rules them out:
     0x851e4, 0x851f8, 0x85208 (the stores at p, p + 4, p + 8 in that order). On this path the model premise gives
     0 <= OW.n < 16 (m_set_m is None when OW.n < 0), so [p, p + 12) lies in [OW + 4, OW + 196), inside OW's payload,
     each store 4-byte aligned inside one granule; trans_ow_cells B (m_lost_cg.v; a fact of the record, decided by the
     closing file): the shadow bytes of OW's 38 whole granules are 0, re-read at every state by AR (YG0n.v ARm
     am_zshadow), so k = 0. The model's None for OW.n++ at INT_MAX (:205) is excluded by the same premise.
   Callee texts assumed: none (no function is called on a path the walk takes).
   Stack: 16 bytes of its own: MONLINE_STK.

   The caller: m_rx (0x84e18). It supplies the G journal of its own walk and the world relation. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* m_maybe_online's frame (`sp = sp - 16` at its entry; no realignment). It calls no function on a path the walk
   takes. *)
Definition MONLINE_FRAME : Z := 16.
Definition MONLINE_STK : Z := MONLINE_FRAME.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition MONLINE_EV : Z := 0.
(* The bytes the code stores into G, exactly: when M.state = S_WAKING, M.e2_acked <> 0 and M.e1_us <> 0, M.next_ka
   and m_set's stores (m_lost_cg.v mset_wr; M.state is S_WAKING, so m_set changes the state); none otherwise. *)
Definition monline_wr (Bw : list byte) (a : Z) : Prop :=
  TW.M_state Bw = TCB.S_WAKING /\ TCB.truth (TW.M_e2_acked Bw) = true /\ TCB.truth (TW.M_e1_us Bw) = true /\
  (twa_fld TW.OFF_M TA_M TW.A_M_next_ka 8 a \/ mset_wr Bw a).

Section monline. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range
   monline_wr Bw, no meter charge, and X: the world relation at the model's world Bw'. *)
Definition transport_monline_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    MONLINE_STK MONLINE_EV 0 (monline_wr Bw)
    (fun regs2 W2 mem2 => tw_at TMAP_A (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_m_maybe_online_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MONLINE_STK -> spZ regs <= sp0 ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TCB.m_maybe_online_m Bw = Some (Bw', tt) ->
    st_nev S + k + MONLINE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_monline_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of OW's
   payload, the allocator and meter laws, and G inside the image and outside the allocator's statics give the
   contract at TS_m_maybe_online. *)
Definition transport_m_maybe_online_cg_holds_stmt : Prop :=
  transport_cells B -> trans_ow_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS ->
  transport_m_maybe_online_cg (transport_sigma TS_m_maybe_online).
End monline.
