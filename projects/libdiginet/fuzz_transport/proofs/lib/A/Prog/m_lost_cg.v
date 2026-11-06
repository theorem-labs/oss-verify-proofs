(* m_lost_cg: the ASan walk contract of m_lost (fuzz/fuzz_transport.c:210-215, with m_set :196-207 inlined; model
   lib/TModel/TCb.v m_lost_m) on fuzz_transport.asan (e89be137db17) at 0x85004 = transport_sigma TS_m_lost, size 236,
   as STATEMENTS only (no proof). It is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v
   ajournal_gx over G = lib/A/TransportG.v G_HARNESS (the payloads of the 18 harness globals) with no out cell
   (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS).
   m_lost calls no function but stores into M and OW, two harness globals, so it takes this form and not the
   footprint-leaf form (that form keeps the world relation only for writes outside G's hull: TWorldAKept.v csw_kept).

   This file also holds the three definitions the walks of the functions that inline m_set share (m_lost, m_wake,
   m_maybe_online_cg.v Require it): twa_fld (the image-A bytes of a world field), mset_wr (m_set's stores) and
   trans_ow_cells (the shadow of OW's payload).

   The contract. a0 = why, a 32-bit int (its callers pass 3, 4, 5, 6 or 7). The memory relates to the world Bw by the
   world relation of image A (TWorldG.v tw_at at the table TWorldA.v TMAP_A, read through the walk's view aview), and
   Bw' is the model's world after the call (m_lost_m Bw why = Some (Bw', tt)). The function returns to ra with the
   callee-saved registers kept, no allocator event and no meter charge, the caller's side-stack frames and blocks
   exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at or above alloc_ceiling outside the call's stack window
   [sp - 16, sp), the image bytes outside G, the owned statics and errno, the caller's block and frame bytes outside
   mlost_wr Bw), and the world relation at Bw' (M.desk_counter_valid, M.fly.on, and when the state changes M.state,
   OW.n and OW.t[OW.n] as the model sets them; every other payload byte as before). This is what the plain contract
   (lib/Prog/T/m_lost_c.v) says: void; wmem rsegs m' B' with B' the model's world; munch of the frame and the world
   only.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this
   function's 236 code bytes are equal in both files):
     0x85004 - 0x85008 sp = sp - 16: the frame is 16 bytes; ra at sp + 8, loaded back at 0x850a8. No side-stack frame,
                      no frame pointer, no other register saved.
     0x8500c - 0x85020 a1 = the 8-byte load of the GOT word 0xa4090 (it holds 0xac9f8); a3 = &M = 0x5df160 (TA_M);
                      a7 = the 4-byte signed load of M.state (M + 12); a6 = the 8-byte load at 0xac9f8 (0x7fff8000,
                      the shadow base): transport_cells rows 1-2.
     0x85024 - 0x85028 the 4-byte stores of 0 at M + 76 (desk_counter_valid) and M + 96 (fly.on), :212-213. No
                      instrumented check guards a store or load at a constant offset of M, OW or g_cfg.
     0x8502c          M.state = 0 (S_IDLE, m_set's `if (M.state == st) return`, :198-199) goes to 0x850a8 and returns.
     0x85030 - 0x85040 a4 = &OW = 0x5f3060 (TA_OW); a5 = the 4-byte signed load of OW.n (OW + 0); 15 < OW.n (signed)
                      goes to 0x8509c (the log is full, :200).
     0x85044 - 0x85098 for p = OW + 4 + 12 * OW.n (= &OW.t[OW.n]): the instrumented check of the 4-byte store at p
                      (the shadow byte k at (p >> 3) + 0x7fff8000; k = 0 goes on; else (p & 7) + 3 < k (signed) goes
                      on; else the error path), the store of 0 (S_IDLE) at p; the same check and the store of a7 (the
                      old state) at p + 4; the same check and the store of a0 (why) at p + 8 (:201-203).
     0x8509c - 0x850a4 the 4-byte store of OW.n + 1 at OW + 0 (:205) and of 0 at M + 12 (M.state = S_IDLE, :206).
     0x850a8 - 0x850b0 ra loaded back, sp = sp + 16, return. a0 .. a7 at the return are not stated (void).
   Error paths (3 calls of errpath_store4, 0x59928; no trap path) and the fact that rules them out:
     0x850c4, 0x850d8, 0x850ec (the stores at p, p + 4, p + 8 in that order). On this path the model premise gives
     0 <= OW.n < 16 (m_set_m is None when OW.n < 0), so [p, p + 12) lies in [OW + 4, OW + 196), inside OW's payload,
     and each store is 4-byte aligned inside one granule. trans_ow_cells B (a fact of the record, decided by the
     closing file): the shadow bytes of OW's 38 whole granules [0x5f3060, 0x5f3190) are 0 (a range of
     as_zero_shadow B; the record's Tfib_zero_shadow row (0x5f3060, 0x5f3190 - 0x5f3060)); AR re-reads them at every
     state (YG0n.v ARm am_zshadow), so k = 0. The model's None for OW.n++ at INT_MAX (:205) is excluded by the same
     premise.
   Callee texts assumed: none (no function is called on a path the walk takes).
   Stack: 16 bytes of its own: MLOST_STK.

   The callers: m_tick (tail jumps at 0x83c78 with a0 = 6 and 0x83ca8 with a0 = 4, at m_tick's entry sp) and m_rx
   (calls at 0x84c80 with a0 = 7, or a0 = 5 when m_rx reaches it by its jump at 0x84e48, and 0x84de8 with a0 = 3).
   Each supplies the G journal of its own walk and the world relation. *)
From Stdlib Require Import ZArith List Lia Permutation.
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

(* ---- shared by the walks of m_lost, m_wake and m_maybe_online ---- *)

(* The image-A bytes of a world field: the n bytes at world offset A of the harness global whose world offset is o
   and whose image-A base is b (the row (o, b, _) of TWorldA.v TMAP_A). *)
Definition twa_fld (o b A n a : Z) : Prop := b + (A - o) <= a < b + (A - o) + n.

(* m_set's stores (fuzz_transport.c:196-207, inlined into m_lost, m_wake and m_maybe_online) when the state changes:
   the 12 bytes of OW.t[OW.n] when 0 <= OW.n < TRANS_MAX, OW.n, and M.state. None of the stores before m_set in the
   three functions changes OW.n, so OW.n is the value in Bw, the world at the function's entry. *)
Definition mset_wr (Bw : list byte) (a : Z) : Prop :=
  (0 <= TW.OW_n Bw < TCB.TRANS_MAX /\ twa_fld TW.OFF_OW TA_OW (TW.A_OW_t_state (TW.OW_n Bw)) TW.OW_t_ESZ a) \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_n 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_state 4 a.

(* The shadow of OW's payload, as a fact of the record B: the shadow bytes of its 38 whole granules are 0 (a range
   of as_zero_shadow B). m_set's instrumented checks of the stores at OW.t[OW.n] read them. *)
Definition trans_ow_cells (B : asyms) : Prop := decode_zshadow_at B TA_OW (TA_OW + TW.SZ_OW).

(* ---- m_lost ---- *)

(* m_lost's frame (`sp = sp - 16` at its entry; no realignment). It calls no function on a path the walk takes. *)
Definition MLOST_FRAME : Z := 16.
Definition MLOST_STK : Z := MLOST_FRAME.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition MLOST_EV : Z := 0.
(* The bytes the code stores into G, exactly: M.desk_counter_valid and M.fly.on; when M.state is not S_IDLE also
   m_set's stores. *)
Definition mlost_wr (Bw : list byte) (a : Z) : Prop :=
  twa_fld TW.OFF_M TA_M TW.A_M_desk_counter_valid 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_fly_on 4 a \/
  (TW.M_state Bw <> TCB.S_IDLE /\ mset_wr Bw a).

Section mlost. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range mlost_wr Bw,
   no meter charge, and X: the world relation at the model's world Bw'. *)
Definition transport_mlost_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    MLOST_STK MLOST_EV 0 (mlost_wr Bw)
    (fun regs2 W2 mem2 => tw_at TMAP_A (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_m_lost_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (why : Z) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 why ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MLOST_STK -> spZ regs <= sp0 ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TCB.m_lost_m Bw why = Some (Bw', tt) ->
    - 2 ^ 31 <= why < 2 ^ 31 ->
    st_nev S + k + MLOST_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_mlost_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of OW's
   payload, the allocator and meter laws, and G inside the image and outside the allocator's statics give the
   contract at TS_m_lost. *)
Definition transport_m_lost_cg_holds_stmt : Prop :=
  transport_cells B -> trans_ow_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS ->
  transport_m_lost_cg (transport_sigma TS_m_lost).
End mlost.
