(* m_wake_cg: the ASan walk contract of m_wake (fuzz/fuzz_transport.c:218-233, with m_set :196-207 inlined; model
   lib/TModel/TCb.v m_wake_m) on fuzz_transport.asan (e89be137db17) at 0x83d00 = transport_sigma TS_m_wake, size
   328, as STATEMENTS only (no proof). It is a G-form caller-journal walk: the caller's journal is
   lib/A/W_journalG.v ajournal_gx over G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0, OUT = []), and the
   post is lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS). m_wake calls no function but
   stores into M and OW, two harness globals, so it takes this form and not the footprint-leaf form (m_lost_cg.v
   says why). twa_fld, mset_wr and trans_ow_cells are m_lost_cg.v's (m_set is inlined into both).

   The contract. No argument. The memory relates to the world Bw by the world relation of image A (TWorldG.v tw_at
   at TWorldA.v TMAP_A, read through aview), and (Bw', r) is the model's result (m_wake_m Bw = Some (Bw', r)). The
   function returns to ra with a0 = r (sign-extended: -1, -10, -5 or 0), the callee-saved registers kept, no
   allocator event and no meter charge, the caller's side-stack frames and blocks exactly, the bytes acall_kept_g
   G_HARNESS keeps (the bytes at or above alloc_ceiling outside the call's stack window [sp - 16, sp), the image bytes
   outside G, the owned statics and errno, the caller's block and frame bytes outside mwake_wr Bw), and the world
   relation at Bw'. This is what the plain contract (lib/Prog/T/m_wake_c.v) says: a0 = r; wmem rsegs m' B' with B'
   the model's world; munch of the frame and the world only.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this
   function's 328 code bytes are equal in both files):
     0x83d00 - 0x83d04 sp = sp - 16: the frame is 16 bytes; ra at sp + 8, loaded back at 0x83e08. No side-stack frame,
                      no frame pointer, no other register saved.
     0x83d08 - 0x83d14 a2 = &M = 0x5df160 (TA_M); M.desk_known (the 4-byte signed load at M + 0) = 0 goes to 0x83d28:
                      a0 = -1 (SPEC_E_ARG), return (:220-221).
     0x83d18 - 0x83d24 M.foreign (M + 24) <> 0: a0 = -10 (SPEC_E_REFUSED), return (:222-223).
     0x83d30 - 0x83d64 a3 = &OW = 0x5f3060 (TA_OW); a1 = OW.e2 (the 4-byte load at OW + 196); a0 = the 8-byte load of
                      the GOT word 0xa4090 (it holds 0xac9f8); a4 = the 8-byte load of g_now (0x5df100); the 4-byte
                      store of a1 + 1 at OW + 196 (:226); a1 = M.fail (M + 88); a5 = the 8-byte load at 0xac9f8
                      (0x7fff8000, the shadow base): transport_cells rows 1-2; the 8-byte store of 0 at M + 16
                      (e2_acked and e1_us, :224), the 8-byte store of a4 at M + 40 (wake_sent = g_now, :225), the
                      4-byte store of 0 at M + 88 (fail, :228). No instrumented check guards a store or load at a
                      constant offset of M, OW or g_now.
     0x83d68 - 0x83d70 the old M.fail <> 0: a0 = -5 (-EIO), return (:229-230).
     0x83d74 - 0x83d84 a6 = M.state (M + 12); M.state = 1 (S_WAKING, m_set's early return, :198-199): a0 = 0, return.
     0x83d88 - 0x83d90 a4 = OW.n (the 4-byte signed load at OW + 0); 15 < OW.n (signed) goes to 0x83df4 (:200).
     0x83d94 - 0x83df0 for p = OW + 4 + 12 * OW.n (= &OW.t[OW.n]): the instrumented check of the 4-byte store at p
                      (the shadow byte k at (p >> 3) + 0x7fff8000; k = 0 goes on; else (p & 7) + 3 < k (signed) goes
                      on; else the error path), the store of 1 (S_WAKING) at p; the same check and the store of a6 (the
                      old state) at p + 4; the same check and the store of 1 (R_WAKE) at p + 8 (:201-203).
     0x83df4 - 0x83e04 a0 = 0 (SPEC_OK); the 4-byte stores of OW.n + 1 at OW + 0 (:205) and of 1 at M + 12 (M.state =
                      S_WAKING, :206).
     0x83e08 - 0x83e10 ra loaded back, sp = sp + 16, return. a1 .. a7 at the return are not stated.
   Error paths (3 calls of errpath_store4, 0x59928; no trap path) and the fact that rules them out:
     0x83e20, 0x83e34, 0x83e44 (the stores at p, p + 4, p + 8 in that order). On this path the model premise gives
     0 <= OW.n < 16 (m_set_m is None when OW.n < 0), so [p, p + 12) lies in [OW + 4, OW + 196), inside OW's payload,
     each store 4-byte aligned inside one granule; trans_ow_cells B (m_lost_cg.v; a fact of the record, decided by the
     closing file): the shadow bytes of OW's 38 whole granules are 0, re-read at every state by AR (YG0n.v ARm
     am_zshadow), so k = 0. The model's None for OW.e2++ and OW.n++ at INT_MAX (:226, :205) is excluded by the same
     premise.
   Callee texts assumed: none (no function is called on a path the walk takes).
   Stack: 16 bytes of its own: MWAKE_STK.

   The callers: LLVMFuzzerTestOneInput (0x818bc) and m_rx (0x84e00). Each supplies the G journal of its own walk and
   the world relation. *)
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

(* m_wake's frame (`sp = sp - 16` at its entry; no realignment). It calls no function on a path the walk takes. *)
Definition MWAKE_FRAME : Z := 16.
Definition MWAKE_STK : Z := MWAKE_FRAME.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition MWAKE_EV : Z := 0.
(* The bytes the code stores into G, exactly. When M.desk_known <> 0 and M.foreign = 0: M.e2_acked with M.e1_us (one
   8-byte store), M.wake_sent, OW.e2 and M.fail; when moreover the old M.fail = 0 and M.state <> S_WAKING, also
   m_set's stores (m_lost_cg.v mset_wr). *)
Definition mwake_wr (Bw : list byte) (a : Z) : Prop :=
  TCB.truth (TW.M_desk_known Bw) = true /\ TCB.truth (TW.M_foreign Bw) = false /\
  (twa_fld TW.OFF_M TA_M TW.A_M_e2_acked 8 a \/
   twa_fld TW.OFF_M TA_M TW.A_M_wake_sent 8 a \/
   twa_fld TW.OFF_OW TA_OW TW.A_OW_e2 4 a \/
   twa_fld TW.OFF_M TA_M TW.A_M_fail 4 a \/
   (TCB.truth (TW.M_fail Bw) = false /\ TW.M_state Bw <> TCB.S_WAKING /\ mset_wr Bw a)).

Section mwake. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range mwake_wr Bw,
   no meter charge, and X: a0 = r (sign-extended) and the world relation at the model's world Bw'. *)
Definition transport_mwake_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    MWAKE_STK MWAKE_EV 0 (mwake_wr Bw)
    (fun regs2 W2 mem2 => YK11.getr regs2 10 = w64 r /\ tw_at TMAP_A (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_m_wake_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bw Bw' : list byte) (r : Z),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MWAKE_STK -> spZ regs <= sp0 ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TCB.m_wake_m Bw = Some (Bw', r) ->
    st_nev S + k + MWAKE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_mwake_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of OW's
   payload, the allocator and meter laws, and G inside the image and outside the allocator's statics give the
   contract at TS_m_wake. *)
Definition transport_m_wake_cg_holds_stmt : Prop :=
  transport_cells B -> trans_ow_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS ->
  transport_m_wake_cg (transport_sigma TS_m_wake).
End mwake.
