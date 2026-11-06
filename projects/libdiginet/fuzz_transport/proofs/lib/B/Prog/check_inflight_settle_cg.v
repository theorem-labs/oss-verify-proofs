(* check_inflight_settle_cg: image B's ASan walk contract of check_inflight_settle (fuzz/fuzz_transport.c:744-771;
   model lib/TModel/TCb.v check_inflight_settle_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x85fdc =
   transportb_sigma TB_check_inflight_settle, size 200, as STATEMENTS only (no proof). It stores into no harness
   global and calls a program function, diginet_session_deadline, so it takes decode's caller-journal form
   (lib/B/Prog/DgnTransportBCg.v decode_cg_post over the caller's donor journal ajournal); a G-form caller lifts it
   with lib/A/Prog/TransportGCg.v gx_call_cg (image-free).

   The contract. No argument. The memory relates to the world Bw by image B's world relation (TWorldG.v tw_at at
   TWorldB.v TMAP_B, read through aview), and check_inflight_settle_m Bw = Some (Bw', tt). The function returns to
   ra with the callee-saved registers kept, no allocator event, no meter charge, every byte outside its stack window
   kept (it stores nothing outside its own frame: E is empty), and Bw' = Bw. This is what the plain contract
   (lib/Prog/T/check_inflight_settle_c.v) says: void; B' = B and wmem rsegs m' B; munch of the frame only. Its wmem
   premise becomes tw_at, and mem_inv and w_off_stack are dropped (the journal's window premises
   keep the frame off the world).

   The code, measured on the symbol-bearing twin (e217cb0a84f1; this function's 200 code bytes are equal in the pin
   and the twin), 50 words:
     0x85fdc          sp = sp - 32; ra, s0, s1, s2 at sp + 24 .. sp + 0 (0x85fe0 - 0x85fec), loaded back at 0x86080 -
                      0x8608c; sp = sp + 32 at 0x86090, the return at 0x86094. No side-stack frame, no frame pointer.
                      These four 8-byte stores into its own frame are its only stores.
     0x85ff0 - 0x86000 the 4-byte loads of GOT.acked (GOT + 216 = 0x5e5038) and OW.acked (OW + 216 = 0x5f2db8);
                      they differ: the trap.
     0x86004 - 0x86018 s0 = &M (0x5dede0); the 4-byte load of M.fly_on (M + 96 = 0x5dee40); s2 = 0x5df010 and
                      s1 = 0x5df014, the pc-relative bases of g_now (s2 - 0x290 = 0x5ded80) and of g_cfg.ack_timeout_ms
                      (s1 - 0x2f8 = 0x5ded1c); M.fly_on = 0 goes to 0x86038.
     0x8601c - 0x86034 the 8-byte loads of g_now and M.fly_sent (M + 112 = 0x5dee50), the 4-byte unsigned load of
                      g_cfg.ack_timeout_ms (g_cfg + 28 = 0x5ded1c); g_now - M.fly_sent (mod 2^64) >= ack_timeout_ms *
                      1000 (unsigned): the trap.
     0x86038 - 0x86044 a1 = the 8-byte load of g_now, a0 = &g_s (0x5df640); the call of diginet_session_deadline
                      (0x8a6c0 = transportb_sigma TB_diginet_session_deadline) at 0x86044, return address 0x86048;
                      a0 = its result d.
     0x86048 - 0x8605c a1 = the 8-byte load of g_now again; d < g_now (unsigned): the trap; g_now + 1000000
                      (mod 2^64) < d (unsigned): the trap.
     0x86060 - 0x8607c the 4-byte load of M.fly_on again; 0 goes to the return; else the 4-byte unsigned load of
                      g_cfg.ack_timeout_ms and the 8-byte load of M.fly_sent; ack_timeout_ms * 1000 + M.fly_sent
                      (mod 2^64) < d (unsigned): the trap; else the return (a0 = d, not stated: void).
   The trap: 0x86098 call of __asan_handle_no_return (0x5a500 = transportb_sigma TB___asan_handle_no_return),
   0x8609c call of abort (0x93390 = transportb_sigma TB_abort); every branch to it is ruled out by
   check_inflight_settle_m Bw = Some _: its tests are the code's tests in the code's order, read through tw_at
   (TWorld.v GOT_acked, OW_acked, M_fly_on, M_fly_sent, g_now, Cfg_ack_timeout_ms), with h_ms_m v = v * 1000 mod 2^64
   and u64 the 64-bit sum or difference, and d is diginet_session_deadline_m Bw (g_now Bw) (the model's let*, whose
   value the callee's statement returns). The loads after the call read the same bytes: the callee keeps every byte
   outside its stack window [sp - 32 - ESTACK, sp - 32) (the leaf post, LeafCgKit.v dleaf_post), and the harness
   globals lie in the image, far below the stack. The word 0x860a0 after the call of abort (`unimp`, inside the
   symbol's 200 bytes) is reached by no branch.
   The difference from image A's code (lib/A/Prog/check_inflight_settle_cg.v): the addresses, and the unreached
   `unimp` word after the call of abort (A's symbol ends at that call). The tests, their order and the call are A's,
   and no UBSan check is in the code: the contract is A's.
   Error paths: none. Its own loads of M, GOT, OW, g_now and g_cfg carry no instrumented check, and the code calls no
   __asan_report_* entry.
   Callee texts assumed: diginet_session_deadline as its leaf statement (lib/B/Prog/diginet_session_deadline_cg.v
   transport_diginet_session_deadline_cg, image B's leaf statement, read at this unit's model by DgnTransportBCg.v
   transport_leaf_at) at transportb_sigma TB_diginet_session_deadline, entered with a0 = &g_s, a1 = g_now. As image A's
   leaf statement asks, it takes besides the journal's facts: tw_at at csw_view of the call memory (the same world
   Bw), diginet_session_deadline_m Bw (g_now Bw) = Some d (from the model premise), asan_cells (transport_cells rows
   1-2), and g_s's payload [0x5df640, 0x5df640 + 18264) addressable: trans_cis_cells B, the record's zero shadow of
   those 2283 whole granules (the Tfib_zero_shadow row (0x5df640, 0x5e3d98 - 0x5df640), lib/B/YF0m.v:3112), read at
   the call state through DgnTransportBCg.v decode_zshadow_rd. No runtime entry is called.
   Stack: 32 bytes of its own and the ESTACK window of the leaf call below sp - 32: CIS_STK.

   The caller is settle (the call at 0x838d8, return address 0x838dc), with no argument. It supplies the journal, the
   world relation and the model call from its own walk.
   Form: lib/A/Prog/check_inflight_settle_cg.v. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_session_deadline_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module LSD := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_session_deadline_cg.
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
Definition trans_cis_cells (B : asyms) : Prop := decode_zshadow_at B TB_g_s (TB_g_s + TW.SZ_g_s).

Section cis. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportBCg.v decode_cg_post with no event, no written range, no meter charge, and X: the
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
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TC.check_inflight_settle_m Bw = Some (Bw', tt) ->
    st_nev S + k + CIS_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_cis_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells, g_s's shadow (trans_cis_cells), the allocator and meter
   laws, and the leaf statement of diginet_session_deadline give the contract at TB_check_inflight_settle. *)
Definition transport_check_inflight_settle_cg_holds_stmt : Prop :=
  transport_cells B -> trans_cis_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSD.transport_diginet_session_deadline_cg) fx') ->
  transport_check_inflight_settle_cg (transportb_sigma TB_check_inflight_settle).
End cis.
