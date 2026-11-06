(* m_wake_cg: image B's m_wake (fuzz/fuzz_transport.c:218-233; model lib/TModel/TCb.v m_wake_m) on
   fuzz_transport.asan-ubsan (41113a03c82f) at 0x83914 = DgnTransportBAddr.v transportb_sigma TB_m_wake, size 136, as
   STATEMENTS only (no proof). It is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v
   ajournal_gx over G = lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0, OUT = []), and the post is
   lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS_B). m_wake stores into M and OW, two
   harness globals, and calls m_set, a G-form walk (m_set_cg.v), so it takes this form and not the footprint-leaf form
   (m_set_cg.v says why). Form: lib/A/Prog/m_wake_cg.v. The difference from image A: on A m_set is inlined; here
   m_wake calls it (a call with link from m_wake's own frame), so m_set's statement is a callee premise and m_set's 16
   bytes are part of m_wake's stack window; and the asan-ubsan build traps OW.e2++ at INT_MAX.

   The contract. No argument. The memory relates to the world Bw by the world relation of image B (TWorldG.v tw_at
   at TWorldB.v TMAP_B, read through aview), and (Bw', r) is the model's result (m_wake_m Bw = Some (Bw', r)). The
   function returns to ra with a0 = r (sign-extended: -1, -10, -5 or 0), the callee-saved registers kept, no
   allocator event and no meter charge, the caller's side-stack frames and blocks exactly, the bytes acall_kept_g
   G_HARNESS_B keeps (the bytes at or above alloc_ceiling outside the call's stack window [sp - 32, sp), the image
   bytes outside G, the owned statics and errno, the caller's block and frame bytes outside mwake_wr Bw), and the
   world relation at Bw'. This is what the plain contract (lib/Prog/T/m_wake_c.v) says: a0 = r; wmem rsegs m' B' with
   B' the model's world; munch of the frame and the world only.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded segments equal the pin's, and this
   function's 136 code bytes are equal in both files):
     0x83914 - 0x83918 sp = sp - 16: the frame is 16 bytes; ra at sp + 8, loaded back at 0x8398c. No side-stack frame,
                      no frame pointer, no other register saved.
     0x8391c - 0x83928 a0 = &M = 0x5dede0 (TB_M); a1 = M.desk_known (the 4-byte signed load at M + 0); 0 goes to
                      0x8393c: a0 = -1 (SPEC_E_ARG), jump to 0x8398c and return (:220-221).
     0x8392c - 0x83938 a1 = M.foreign (M + 24); 0 goes to 0x83944; else a0 = -10 (SPEC_E_REFUSED), jump to 0x8398c and
                      return (:222-223).
     0x83944 - 0x8395c a1 = 0x5f2944 (auipc; OW.e2's address OW + 196 = 0x5f2da4 is a1 + 0x460, OW = 0x5f2ce0 =
                      TB_OW); a3 = OW.e2 (the 4-byte signed load at OW + 196); a4 = the 8-byte load of g_now (0x5ded80
                      = TB_g_now); a2 = OW.e2 + 1 (32-bit add, sign-extended); the 8-byte store of 0 at M + 16
                      (e2_acked and e1_us, :224) and the 8-byte store of a4 at M + 40 (wake_sent = g_now, :225).
     0x83960          a2 < OW.e2 (signed), that is OW.e2 = INT_MAX, goes to the trap 0x83998 (UBSan's signed-overflow
                      check of OW.e2++, :226).
     0x83964 - 0x8396c a3 = M.fail (the 4-byte signed load at M + 88); the 4-byte store of a2 at OW + 196 (OW.e2 =
                      OW.e2 + 1, :226) and of 0 at M + 88 (fail, :228). No instrumented check guards a store or load
                      at a constant offset of M, OW or g_now; m_wake reads no runtime cell.
     0x83970 - 0x83978 the old M.fail <> 0: a0 = -5 (-EIO), jump to 0x8398c and return (:229-230).
     0x8397c - 0x83984 a0 = 1 (S_WAKING), a1 = 1 (R_WAKE); call of m_set (0x85224 = transportb_sigma TB_m_set) at
                      0x83984, return address 0x83988, sp = m_wake's entry sp - 16 (:231). m_set returns at once when
                      M.state = S_WAKING (m_set_cg.v, :198-199); else it makes its stores (m_set_cg.v mset_wr).
     0x83988          a0 = 0 (SPEC_OK, :232).
     0x8398c - 0x83994 ra loaded back, sp = sp + 16, return. a1 .. a7 at the return are not stated.
     0x83998          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that traps):
                      the trap path.
   Error paths: none in m_wake's own code (no instrumented check, no call of an error function). m_set's are ruled out
   inside m_set's statement.
   Trap paths (the one unimp word at 0x83998) and the premise that refutes the branch to it:
     0x83960 (OW.e2 = INT_MAX): the model premise; int_inc (OW_e2 B2) is None at INT_MAX (:226), so m_wake_m is None
     (B2 = Bw with e2_acked, e1_us and wake_sent set, OW.e2 unchanged).
   Callee texts assumed: m_set as m_set_cg.v transport_m_set_cg at transportb_sigma TB_m_set (0x85224), entered at
   0x83984 with ra = 0x83988, sp = m_wake's entry sp - 16, a0 = 1, a1 = 1 and the callee-saved registers of m_wake's
   entry, at the world B4 of m_wake_m (Bw with e2_acked, e1_us, wake_sent, OW.e2 and fail set: M.state and OW.n as
   in Bw). m_set_m B4 S_WAKING R_WAKE is the model's last step (:231), so its premise holds on this path.
   Stack: 16 bytes of its own and m_set's 16 below them: MWAKE_STK = MWAKE_FRAME + MSET_STK.

   The callers: LLVMFuzzerTestOneInput (call at 0x81ad8) and m_rx (call at 0x84fa4). Each supplies the G journal of
   its own walk and the world relation.

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

(* m_wake's frame (`sp = sp - 16` at its entry; no realignment) and, below it, the stack of its one callee m_set. *)
Definition MWAKE_FRAME : Z := 16.
Definition MWAKE_STK : Z := MWAKE_FRAME + MSET_STK.
(* No allocator event: neither m_wake nor m_set calls malloc or free or takes a side-stack frame. *)
Definition MWAKE_EV : Z := MSET_EV.
(* The bytes the call stores into G, exactly. When M.desk_known <> 0 and M.foreign = 0: M.e2_acked with M.e1_us (one
   8-byte store), M.wake_sent, OW.e2 and M.fail; when moreover the old M.fail = 0 and M.state <> S_WAKING, also
   m_set's stores (m_set_cg.v mset_wr). *)
Definition mwake_wr (Bw : list byte) (a : Z) : Prop :=
  TCB.truth (TW.M_desk_known Bw) = true /\ TCB.truth (TW.M_foreign Bw) = false /\
  (twb_fld TW.OFF_M TB_M TW.A_M_e2_acked 8 a \/
   twb_fld TW.OFF_M TB_M TW.A_M_wake_sent 8 a \/
   twb_fld TW.OFF_OW TB_OW TW.A_OW_e2 4 a \/
   twb_fld TW.OFF_M TB_M TW.A_M_fail 4 a \/
   (TCB.truth (TW.M_fail Bw) = false /\ TW.M_state Bw <> TCB.S_WAKING /\ mset_wr Bw a)).

Section mwake. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range
   mwake_wr Bw, no meter charge, and X: a0 = r (sign-extended) and the world relation at the model's world Bw'. *)
Definition transport_mwake_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    MWAKE_STK MWAKE_EV 0 (mwake_wr Bw)
    (fun regs2 W2 mem2 => YK11.getr regs2 10 = w64 r /\ tw_at TMAP_B (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_m_wake_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bw Bw' : list byte) (r : Z),
    ajournal_gx G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MWAKE_STK -> spZ regs <= sp0 ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TCB.m_wake_m Bw = Some (Bw', r) ->
    st_nev S + k + MWAKE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_mwake_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).

(* The statement the walk will prove: the runtime cells, the allocator and meter laws, G inside the image and
   outside the allocator's statics, and the contract of m_set give the contract at TB_m_wake. (transport_cells B is
   the premise every statement of the unit takes; m_wake's own code reads no runtime cell, and the shadow of OW that
   m_set's checks read is m_set's own premise, trans_ow_cells, in m_set_cg.v transport_m_set_cg_holds_stmt.) *)
Definition transport_m_wake_cg_holds_stmt : Prop :=
  transport_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B G_HARNESS_B ->
  (forall fx' : YK11.FPState, @transport_m_set_cg fx' rc B MT (transportb_sigma TB_m_set)) ->
  transport_m_wake_cg (transportb_sigma TB_m_wake).
End mwake.
