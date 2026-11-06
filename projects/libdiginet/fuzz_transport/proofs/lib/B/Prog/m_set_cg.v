(* m_set_cg: image B's m_set (fuzz/fuzz_transport.c:196-207; model lib/TModel/TCb.v m_set_m) on
   fuzz_transport.asan-ubsan (41113a03c82f) at 0x85224 = DgnTransportBAddr.v transportb_sigma TB_m_set, size 252, as
   STATEMENTS only (no proof). On image A m_set has no code of its own: it is inlined into m_lost, m_wake and
   m_maybe_online (lib/A/Prog/m_lost_cg.v, m_wake_cg.v, m_maybe_online_cg.v), so this file has no image-A twin; its
   contract is the G form of those files, at image B's values. It is a G-form caller-journal walk: the caller's
   journal is lib/A/W_journalG.v ajournal_gx over G = lib/B/TransportGB.v G_HARNESS_B (the payloads of the 18 harness
   globals) with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post
   (acall_kept_g over G_HARNESS_B). m_set calls no function on a path the walk takes but stores into M and OW, two
   harness globals, so it takes this form and not the footprint-leaf form (that form keeps the world relation only for
   writes outside G's hull: TWorldB.v TMAP_B_kept).

   This file also holds image B's twins of the three definitions lib/A/Prog/m_lost_cg.v gives the image-A walks that
   inline m_set: twb_fld (twa_fld: the image-B bytes of a world field), mset_wr (m_set's stores) and trans_ow_cells
   (the shadow of OW's payload). Image B has no m_lost function (m_tick and m_rx inline it), so they live here, and
   m_wake_cg.v, m_tick_cg.v and m_maybe_online_cg.v Require this file.

   The contract. a0 = st, a1 = why, two 32-bit ints, sign-extended in the registers (its callers pass constants:
   (st, why) = (0, 4) or (0, 6) from m_tick, (1, 1) from m_wake, (2, 2) from m_maybe_online, (0, 7), (0, 5) and
   (0, 3) from m_rx, (3, 8) from LLVMFuzzerTestOneInput). The memory relates to the world Bw by the world relation of
   image B (lib/A/Prog/TWorldG.v tw_at at the table lib/B/Prog/TWorldB.v TMAP_B, read through the walk's view aview),
   and Bw' is the model's world after the call (m_set_m Bw st why = Some (Bw', tt)). The function returns to ra with the
   callee-saved registers kept, no allocator event and no meter charge, the caller's side-stack frames and blocks
   exactly, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at or above alloc_ceiling outside the call's stack
   window [sp - 16, sp), the image bytes outside G, the owned statics and errno, the caller's block and frame bytes
   outside mset_st_wr Bw st), and the world relation at Bw' (when M.state <> st: OW.t[OW.n] when 0 <= OW.n < 16,
   OW.n and M.state as the model sets them; every other payload byte as before). There is no plain contract of
   m_set (the plain image inlines it too); the model m_set_m is the text the plain contracts of its callers
   (lib/Prog/T/m_lost_c.v, m_wake_c.v, m_maybe_online_c.v) reach through their models.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded segments equal the pin's, and this
   function's 252 code bytes are equal in both files):
     0x85224 - 0x85228 sp = sp - 16: the frame is 16 bytes; ra at sp + 8, loaded back at 0x852d4. No side-stack frame,
                      no frame pointer, no other register saved.
     0x8522c - 0x85234 a4 = 0x5df22c (auipc; M.state's address M + 12 = 0x5dedec is a4 - 0x440, M = 0x5dede0 =
                      TB_M); a7 = M.state (the 4-byte signed load at M + 12); M.state = a0 (st) goes to 0x852d4 and
                      returns (:198-199).
     0x85238 - 0x85240 a5 = &OW = 0x5f2ce0 (TB_OW); a6 = OW.n (the 4-byte signed load at OW + 0).
     0x85244 - 0x85248 15 < OW.n (signed) goes to 0x852c4 (the log is full, :200).
     0x8524c - 0x85250 OW.n >= 16 (unsigned), that is OW.n < 0 here, goes to the trap 0x852e0 (UBSan's index check of
                      OW.t[OW.n], :201).
     0x85254 - 0x85268 a2 = 16 * OW.n - 4 * OW.n = 12 * OW.n; a3 = not (OW + 4) = 2^64 - 1 - (OW + 4); a3 < a2
                      (unsigned), that is OW + 4 + 12 * OW.n >= 2^64, goes to the trap 0x852e0 (UBSan's
                      pointer-overflow check of &OW.t[OW.n]).
     0x8526c - 0x85274 a3 = the 8-byte load of the GOT word 0xa3cf0 (it holds 0xac678); t0 = the 8-byte load at 0xac678
                      (0x7fff8000, the shadow base): transport_cells rows 1-2 (lib/B/AsanCells.v GOT_CELL_K, CELL_K).
     0x85278 - 0x852c0 for p = OW + 4 + 12 * OW.n (= &OW.t[OW.n]): the instrumented check of the 4-byte store at p (the
                      shadow byte k, the signed 1-byte load at (p >> 3) + 0x7fff8000; k = 0 goes on; else 0x852e4:
                      (p & 7) + 3 < k (signed) goes back to the store; else the error path), the store of a0 (st) at
                      p; the same check (slow path 0x852f8) and the store of a7 (the old state) at p + 4; the same
                      check (slow path 0x8530c) and the store of a1 (why) at p + 8 (:201-203).
     0x852c4 - 0x852c8 a1 = OW.n + 1 (32-bit add, sign-extended); a1 < OW.n (signed), that is OW.n = INT_MAX, goes to
                      the trap 0x852e0 (UBSan's signed-overflow check of OW.n++, :205).
     0x852cc - 0x852d0 the 4-byte stores of a1 (OW.n + 1) at OW + 0 (:205) and of a0 (st) at M + 12 (M.state = st,
                      :206).
     0x852d4 - 0x852dc ra loaded back, sp = sp + 16, return. a0 .. a7 at the return are not stated (void).
     0x852e0          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that traps):
                      the trap path.
     0x852e4 - 0x8531c the three slow paths of the checks and the three error calls.
   Error paths (3 calls of __asan_report_store4, 0x59964) and the fact that rules them out:
     0x852f4 (a0 = p), 0x85308 (a0 = p + 4), 0x8531c (a0 = p + 8). On this path M.state <> st and
     0 <= OW.n < 16 (the model premise: m_set_m is None when OW.n < 0), so [p, p + 12) lies in [OW + 4, OW + 196),
     inside OW's payload, and each store is 4-byte aligned inside one granule (OW = 0x5f2ce0 is 8-aligned).
     trans_ow_cells B (a fact of image B's record, decided by the closing file): the shadow bytes of OW's 38 whole
     granules [0x5f2ce0, 0x5f2e10), the 38 bytes [0x800b659c, 0x800b65c2), are 0 (a range of as_zero_shadow B); AR
     re-reads them at every state (YG0n.v ARm am_zshadow), so k = 0.
   Trap paths (the one unimp word at 0x852e0) and the premise that refutes each branch to it:
     0x85250 (OW.n < 0): the model premise; m_set_m Bw st why is None when M.state <> st and OW.n < 0 (:201-203).
     0x85268 (OW + 4 + 12 * OW.n >= 2^64): reached only with 0 <= OW.n <= 15 (the two branches before it), where
       OW + 4 + 12 * OW.n <= 0x5f2da0 < 2^64; never taken.
     0x852c8 (OW.n = INT_MAX): the model premise; int_inc OW.n is None at INT_MAX (:205), so m_set_m is None.
   Callee texts assumed: none (no function is called on a path the walk takes).
   Stack: 16 bytes of its own: MSET_STK.

   The callers: LLVMFuzzerTestOneInput (call at 0x81b88), m_tick (tail jump at 0x838bc, at m_tick's entry sp), m_wake
   (call at 0x83984), m_rx (calls at 0x84dec with a1 = 7, or a1 = 5 when m_rx reaches it by its jump at 0x84ffc, and
   0x84f8c with a1 = 3) and m_maybe_online (tail jump at 0x8521c, at its entry sp). Each supplies the G journal of its
   own walk and the world relation.

   Names this file reads from lib/B/Prog/DgnTransportBCg.v (image B's twin of lib/A/Prog/DgnTransportCg.v), at the A
   names: transport_cells and decode_zshadow_at. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TCB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- shared by the walks of m_set and of its callers m_wake, m_tick and m_maybe_online ---- *)

(* The image-B bytes of a world field: the n bytes at world offset A of the harness global whose world offset is o
   and whose image-B base is b (the row (o, b, _) of TWorldB.v TMAP_B). Image B's twin of
   lib/A/Prog/m_lost_cg.v twa_fld. *)
Definition twb_fld (o b A n a : Z) : Prop := b + (A - o) <= a < b + (A - o) + n.

(* m_set's stores (fuzz_transport.c:196-207) when the state changes: the 12 bytes of OW.t[OW.n] when
   0 <= OW.n < TRANS_MAX, OW.n, and M.state. Bw is the world at m_set's entry; none of the stores its callers make
   before the call or tail jump changes OW.n or M.state, so in a caller's walk OW.n and M.state are also the values
   at the caller's entry. Image B's twin of lib/A/Prog/m_lost_cg.v mset_wr. *)
Definition mset_wr (Bw : list byte) (a : Z) : Prop :=
  (0 <= TW.OW_n Bw < TCB.TRANS_MAX /\ twb_fld TW.OFF_OW TB_OW (TW.A_OW_t_state (TW.OW_n Bw)) TW.OW_t_ESZ a) \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_n 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_state 4 a.

(* The shadow of OW's payload, as a fact of the record B: the shadow bytes of its 38 whole granules are 0 (a range
   of as_zero_shadow B). m_set's instrumented checks of the stores at OW.t[OW.n] read them. Image B's twin of
   lib/A/Prog/m_lost_cg.v trans_ow_cells. *)
Definition trans_ow_cells (B : asyms) : Prop := decode_zshadow_at B TB_OW (TB_OW + TW.SZ_OW).

(* ---- m_set ---- *)

(* m_set's frame (`sp = sp - 16` at its entry; no realignment). It calls no function on a path the walk takes. *)
Definition MSET_FRAME : Z := 16.
Definition MSET_STK : Z := MSET_FRAME.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition MSET_EV : Z := 0.
(* The bytes the code stores into G, exactly: m_set's stores when M.state is not st; none otherwise. *)
Definition mset_st_wr (Bw : list byte) (st a : Z) : Prop := TW.M_state Bw <> st /\ mset_wr Bw a.

Section mset. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range
   mset_st_wr Bw st, no meter charge, and X: the world relation at the model's world Bw'. *)
Definition transport_mset_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw : list byte) (st : Z) (Bw' : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    MSET_STK MSET_EV 0 (mset_st_wr Bw st)
    (fun regs2 W2 mem2 => tw_at TMAP_B (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_m_set_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (st why : Z) (Bw Bw' : list byte),
    ajournal_gx G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 st -> YK11.getr regs 11 = w64 why ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MSET_STK -> spZ regs <= sp0 ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TCB.m_set_m Bw st why = Some (Bw', tt) ->
    - 2 ^ 31 <= st < 2 ^ 31 -> - 2 ^ 31 <= why < 2 ^ 31 ->
    st_nev S + k + MSET_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_mset_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw st Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of OW's
   payload, the allocator and meter laws, and G inside the image and outside the allocator's statics give the
   contract at TB_m_set. *)
Definition transport_m_set_cg_holds_stmt : Prop :=
  transport_cells B -> trans_ow_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B G_HARNESS_B ->
  transport_m_set_cg (transportb_sigma TB_m_set).
End mset.
