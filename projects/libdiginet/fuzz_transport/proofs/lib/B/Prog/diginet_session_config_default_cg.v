(* diginet_session_config_default_cg: image B's ASan walk contract of diginet_session_config_default
   (transport/src/diginet_session.c:11-27; model lib/TModel/TSess0.v diginet_session_config_default_m) on
   fuzz_transport.asan-ubsan (41113a03c82f) at 0x865f4 = transportb_sigma TB_diginet_session_config_default, size 536,
   as STATEMENTS only (no proof). It is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v
   ajournal_gx (image-free) over G = lib/B/TransportGB.v G_HARNESS_B (the payloads of the 18 harness globals) with no
   out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post (image-free; acall_kept_g
   over G_HARNESS_B).

   The contract. a0 = &g_cfg = 0x5ded00 (TWorldB.v TB_g_cfg; the harness's one call, fuzz_transport.c:1134, at
   0x815f4 in LLVMFuzzerTestOneInput, return address 0x815f8). The memory relates to the world Bw by the world
   relation of image B (TWorldG.v tw_at at the table TWorldB.v TMAP_B, read through the walk's view aview), and Bw'
   is the model's world after the call (diginet_session_config_default_m Bw = Some (Bw', tt)). The function returns
   to ra with the callee-saved registers kept, no allocator event and no meter charge, the caller's side-stack frames
   and blocks exactly, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at or above alloc_ceiling outside the
   call's stack window [sp - 32 - ESTACK, sp), the image bytes outside G, the owned statics and errno, the caller's
   block and frame bytes outside the 60 bytes of g_cfg), the world relation at Bw' (the 60 bytes of g_cfg as the model
   sets them, the other 17 globals' payloads as before). This is what the plain contract
   (lib/Prog/T/diginet_session_config_default_c.v) says: void; wmem rsegs m' B' with B' the model's world; munch of
   the frame and the world only.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; this function's 536 code bytes are equal in the pin
   and the twin), 134 words:
     0x865f4          sp = sp - 32: the frame is 32 bytes; ra at sp + 24, s0 at sp + 16, s1 at sp + 8 (0x865f8 -
                      0x86600), loaded back at 0x86754 - 0x8675c; sp = sp + 32 at 0x86760, the return at 0x86764. No
                      side-stack frame, no frame pointer.
     0x86604          a0 = 0 goes to 0x86754 and returns having written nothing outside its frame (the three
                      prologue stores come first; the C test `if (!c)`, :13-14): kept unreached, a0 = 0x5ded00.
     0x86608 - 0x86614 s0 = c; a0 = the 8-byte load of the GOT word 0xa3cf0 (AsanCells.v GOT_CELL_K; it holds 0xac678,
                      CELL_K, the cell of the shadow base); s1 = the 8-byte load at 0xac678 (0x7fff8000):
                      DgnTransportBCg.v transport_cells rows 1-2.
     0x86618 - 0x86624 a2 = 60, a0 = c, a1 = 0; call of __asan_memset (0x52888 = transportb_sigma TB___asan_memset) at
                      0x86624, return address 0x86628: the 60 bytes [c, c + 60) (all of :15's memset) set to 0.
     0x86628 - 0x8662c the UBSan alignment check of c: c & 3 <> 0 goes to the trap 0x86768.
     then 10 times, for off = 16, 24, 28, ..., 56: the instrumented check of the 4-byte store at c + off (the shadow
                      byte k at ((c + off) >> 3) + 0x7fff8000; k = 0 goes on; else ((c + off) & 7) + 3 < k
                      (signed) goes on; else the error path), then the 4-byte store at c + off of v_off (stores at
                      0x8664c, 0x8666c, 0x86688, 0x866a4, 0x866c0, 0x866e0, 0x86700, 0x8671c, 0x86734, 0x86750):
                      +16 1 (auto_wake), +24 10000 (keepalive_ms), +28 100 (ack_timeout_ms), +32 5 (max_retries),
                      +36 300 (backoff_ms), +40 25000 (offline_ms), +44 3000 (wake_timeout_ms), +48 2000
                      (display_gap_us), +52 48 (max_cmds), +56 314 (max_body): the values of TSess0.v:84-94, at the
                      offsets of TWorld.v A_Cfg_* - OFF_g_cfg. sum_mode (+20, DIGINET_SUM_BODY = 0) has no store: the
                      memset wrote its 0.
     0x86754 - 0x86764 ra, s0, s1 reloaded, sp = sp + 32, return. a0 at the return is c + 56 (not stated: void).
   The differences from image A's code (lib/A/Prog/diginet_session_config_default_cg.v): the memset sets all 60 bytes
   (A: 16) and the sum_mode store is gone (A: 11 stores, here 10); the UBSan alignment check of c and its trap are
   new. Neither changes the contract: the written range is g_cfg's 60 bytes on both, and the trap is refuted by the
   argument premise a0 = SCFG_C, which A's form has.
   The trap: 0x86768 (`unimp`, the UBSan trap), reached only from 0x8662c; ruled out by c = TB_g_cfg = 0x5ded00,
   c mod 4 = 0.
   Error paths (10 calls of __asan_report_store4, 0x59964 = transportb_sigma TB___asan_report_store4) and the fact that
   rules them out:
     0x86778, 0x86788, 0x86798, 0x867a8, 0x867b8, 0x867c8, 0x867d8, 0x867e8, 0x867f8, 0x86808 (the stores at c + 16,
     c + 24, ..., c + 56 in that order). trans_scfg_cells B (a fact of the record, decided by the closing file): the
     shadow bytes of g_cfg's 7 whole granules [0x5ded00, 0x5ded38) are 0 (a range of as_zero_shadow B; the record's
     Tfib_zero_shadow row (0xa8fc0, 0x5ded38 - 0xa8fc0), lib/B/YF0m.v:3112) and the shadow byte 0x800b3da7 of its last
     granule (4 payload bytes of 8) is 4 (a constant cell of the record; Tfib_const_shadow, lib/B/YF0m.v:1023). AR
     re-reads both at every state (YG0n.v ARm am_zshadow, am_const). The stores at c + 16 .. c + 52 lie in granules
     2 .. 6 (k = 0); the store at c + 56 lies in granule 7, where (c + 56) & 7 = 0 and 0 + 3 < 4. The memset's own
     check of [c, c + 60) (granules 0 .. 7) needs the same rows (range_addressable, shadow_hull_vis of
     aintrin_realizes' pre).
   Callee texts assumed: __asan_memset as aintrin_realizes ... OSet (transportb_sigma TB___asan_memset), which the
   walk applies from its G journal through TransportGCg.v gx_intrin_at (destination [c, c + 60), each byte a byte of
   G: transport_twr_ok_g_intro; gx_rw of G is TransportGRwB.v G_HARNESS_B_rw). No program function is called.
   Stack: 32 bytes of its own and the ESTACK __asan_memset uses below sp - 32 (YG0d.v aintrin_realizes'
   ecall_pre): SCFG_STK.

   The caller is LLVMFuzzerTestOneInput (0x815f4). It supplies the G journal of its own walk, the world relation,
   and c = TB_g_cfg (the auipc / addi pair at 0x815e8 / 0x815ec, the listing's PAddHi of A_OBJ 5 = 0x5ded00, kept in
   s5 and moved to a0 at 0x815f0).
   Form: lib/A/Prog/diginet_session_config_default_cg.v (the names are image A's, so the B statement of
   diginet_session_init imports trans_scfg_cells as A's does). *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_session_config_default's frame (`sp = sp - 32` at its entry; no realignment) and the ESTACK its only
   callee, __asan_memset, uses below sp - 32. *)
Definition SCFG_FRAME : Z := 32.
Definition SCFG_STK : Z := SCFG_FRAME + ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition SCFG_EV : Z := 0.
(* Its argument: g_cfg's base in image B. *)
Definition SCFG_C : Z := TB_g_cfg.
Lemma scfg_c_at : SCFG_C = 0x5ded00 /\ TW.SZ_g_cfg = 60.
Proof. split; reflexivity. Qed.
(* The bytes the code stores: g_cfg's 60-byte payload, [c, c + 60) by __asan_memset and 10 of its 4-byte fields
   again by the 4-byte stores. *)
Definition scfg_wr (a : Z) : Prop := SCFG_C <= a < SCFG_C + TW.SZ_g_cfg.

(* The shadow of g_cfg's payload, as facts of the record B (the rows' form of DgnTransportBCg.v transport_cells rows
   18-43): the shadow bytes of its 7 whole granules [c, c + 56) are 0 (a range of as_zero_shadow B), and the shadow
   byte of its last granule, which holds 4 payload bytes, is 4 (a constant cell of the record). *)
Definition trans_scfg_cells (B : asyms) : Prop :=
  decode_zshadow_at B SCFG_C (SCFG_C + 56) /\
  forall ly, In (z1 (ANum (ACells.shadow_addr (SCFG_C + 56))) 4) (as_const B ly).

Section scfg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range scfg_wr,
   no meter charge, and X: the world relation at the model's world Bw'. *)
Definition transport_scfg_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw' : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs SCFG_STK SCFG_EV 0 scfg_wr
    (fun regs2 W2 mem2 => tw_at TMAP_B (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_diginet_session_config_default_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 SCFG_C ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SCFG_STK -> spZ regs <= sp0 ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TS0.diginet_session_config_default_m Bw = Some (Bw', tt) ->
    st_nev S + k + SCFG_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_scfg_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of
   g_cfg, the allocator and meter laws, G inside the image and outside the allocator's statics, and the contract of
   __asan_memset give the contract at TB_diginet_session_config_default. *)
Definition transport_diginet_session_config_default_cg_holds_stmt : Prop :=
  transport_cells B -> trans_scfg_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset)) ->
  transport_diginet_session_config_default_cg (transportb_sigma TB_diginet_session_config_default).
End scfg.
