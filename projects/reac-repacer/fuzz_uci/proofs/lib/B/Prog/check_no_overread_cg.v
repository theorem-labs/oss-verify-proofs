(* Modified by Theorem Labs: copied from this unit's lib/A/Prog/check_no_overread_cg.v (commit ba35beec1417; itself in the caller-journal form of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v at recipes commit 88154566652a; cgif_file_fuzzer lib/A/ACey.v trfc_specX, lib/YC20.v tlzw_spec) for reac-repacer/fuzz_uci's image B: the B core's names (lib/B/YB1v.v, lib/B/YE2k.v, lib/B/YCbq.v / YC5d.v), the listing modules lib/B/Prog's; the three return addresses and every address in the comments measured on fuzz_uci.asan-ubsan. *)
(* check_no_overread_cg: the ASan walk contract of check_no_overread (fuzz_uci.asan-ubsan 0x7f56c =
   uci_sigma US_check_no_overread, AF_check_no_overread = 0x284 of lib/B/Prog/UciPList.v), as STATEMENTS only (no
   proof). The caller's journal is the premise, the post extends it by the call's events, the allocations are metered,
   and the blocks the call allocates are all freed.

   The C (fuzz_uci.c check_no_overread): two copies of the n reply bytes, each malloc(n + 1) with a different byte at
   [n] ('0' and ' '), rp_uci_int on each, abort unless the two results are equal, free both (the last a tail call).
   The code (DIS of image B): `addi sp, sp, -0x40` (frame 0x40); +0x20 `mv s0, a2` (s0 = cur from here on, so no frame
   pointer); malloc trampoline 0x51788 at +0x40 and +0x4c; __asan_memcpy 0x50674 at +0x6c and +0x7c (skipped when
   n = 0, `beqz s1` at +0x5c); the two terminator stores at +0xa4 / +0xc4, each guarded by __asan_report_store1 (+0x134 /
   +0x140); rp_uci_int at +0xd4 and +0xe8; `bne s4, a0` at +0xec to __asan_handle_no_return / abort (+0x120 / +0x124),
   also reached when a malloc returns NULL (+0x50, +0x58); free trampoline 0x51784 at +0xf4; the epilogue, then `j` to
   the free trampoline at +0x11c (the listing's PTail): that free returns to this function's caller. Its two UBSan
   checks (+0x84, +0xa8: the copy's base + n wraps) branch to `unimp` at +0x128; the malloc rule's fresh blocks refute
   both.
   The aborts are refuted by the malloc rule (it never returns NULL, YC5d.v amalloc04_rule) and by rp_uci_int_m being a
   function of the n bytes alone (lib/Prog/rp_uci_int_c.v), which rp_uci_int_cg's post states; the report branches by
   the shadow of the fresh blocks. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import UciPSyms UciPAddr UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require rp_uci_int_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module PR := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog.rp_uci_int_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_no_overread's own frame (`addi sp, sp, -0x40` at US_check_no_overread). Its allocator calls use ASTACK below
   their sp, as the malloc rule asks (YC5d.v amalloc04_rule); rp_uci_int's frame and memchr's ESTACK lie within it. *)
Definition CNO_FRAME : Z := 0x40.
Definition CNO_STK : Z := CNO_FRAME + ASTACK.
(* malloc, malloc, free, free: one model event each (YC5d.v). *)
Definition CNO_EV : Z := 4.
(* Live bytes it adds: two blocks of n + 1 <= REPLY_MAX + 1 bytes (blocks_bytes counts the requested sizes). *)
Definition CNO_LIVE : Z := 2 * (PR.REPLY_MAX + 1).

(* The return addresses of its allocator calls, as offsets from its entry (the jal is 4 bytes before): malloc at +0x40
   and +0x4c, free at +0xf4 (0x7f5b0, 0x7f5bc, 0x7f664). The tail free (`j` at +0x11c) returns to the caller. *)
Definition UCI_CNO_RA_MALLOC1 : Z := uci_sigma US_check_no_overread + 0x44.
Definition UCI_CNO_RA_MALLOC2 : Z := uci_sigma US_check_no_overread + 0x50.
Definition UCI_CNO_RA_FREE1 : Z := uci_sigma US_check_no_overread + 0xf8.

Section cno. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* The meter cost of one call: its two allocations of n + 1 bytes and two frees (cgif lib/A/ACey.v RFC_COST form). *)
Definition uci_cno_cost (n : Z) : Z :=
  mo_malloc MT (n + 1) + mo_malloc MT (n + 1) + (mo_free MT + mo_free MT).

(* What a call leaves: the caller's journal extended by CNO_EV events, callee-saved registers kept, no fake frame
   added, the caller's blocks exactly (both copies freed), every byte outside the call's stack window kept (YCbq.v
   acall_kept with no written range: the caller's reply bytes too), and the meter charged uci_cno_cost. *)
Definition uci_cno_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (n : Z) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CNO_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CNO_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 (uci_cno_cost n).

(* The contract at entry address a, for call contexts CTX (cgif lib/YC20.v tlzw_spec's (a, CTX) parameters; the
   context is the entry's return address followed by the frame-pointer chain's, as the tail free records it). r (a0)
   holds the n (a1) reply bytes bs, inside one of the caller's blocks when n > 0; cur (a2) is an int. The read-only
   view is asked only at the bytes the walks read (uci_rom_view_rd: musl memchr's constant window, which rp_uci_int's
   memchr call needs). *)
Definition uci_check_no_overread_cg (a : Z) (CTX : list (list Z)) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (r n cur T : Z) (bs : list byte) ch,
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 r -> YK11.getr regs 11 = w64 n -> YK11.getr regs 12 = w64 cur ->
    @achain rc lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CNO_STK -> spZ regs <= sp0 ->
    INT_MIN <= cur <= INT_MAX ->
    0 <= n <= PR.REPLY_MAX -> Z.of_nat (length bs) = n ->
    (0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= r /\ r + n <= bA + nA) ->
    garr8 segs (mrestrict (w_H W) memc) r (map (fun b : byte => bv_unsigned b) bs) ->
    uci_rom_view_rd W memc ->
    st_nev S + k + CNO_EV <= EV_MAX -> blocks_bytes Sc + CNO_LIVE <= LIVE_MAX ->
    mo_ok MT Sc T -> uci_cno_cost n <= T ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (uci_cno_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n).

(* The traces its allocator calls record, which the call rules ask to be in the trace universe (YC5d.v). s0 holds cur
   from +0x20 on, and an int is either below sp or, negative, at or above ly_top, so the chain at the two mallocs and
   the first free is empty (YCbq.v achain / YG00.v bad_next) and those traces are fixed: [pc0; return address]
   (lib/B/YCej.v TRACES_check_no_overread rows [0x51a24; 0x7f5b0], [0x51a24; 0x7f5bc], [0x518c4; 0x7f664]). The tail
   free runs after the epilogue restored ra and s0: its trace is the free's pc0 followed by the entry context c itself
   (YCej.v row [0x518c4; 0x7f478] at c = [0x7f478]). *)
Definition uci_cno_uctx (CTX : list (list Z)) : Prop :=
  forall c, In c CTX -> In (uci_utrace (pc_free_ra0 (as_code B)) c) (as_universe B).
Definition uci_cno_ufix : Prop :=
  In (uci_utrace (pc_malloc_ra0 (as_code B)) [UCI_CNO_RA_MALLOC1]) (as_universe B) /\
  In (uci_utrace (pc_malloc_ra0 (as_code B)) [UCI_CNO_RA_MALLOC2]) (as_universe B) /\
  In (uci_utrace (pc_free_ra0 (as_code B)) [UCI_CNO_RA_FREE1]) (as_universe B).

(* The statement the walk will prove: the call rules' code addresses (the listing's trampolines), the runtime cells,
   the two read-only facts of the record, the allocator and meter laws, the trace facts, and the callee contracts give
   the contract at US_check_no_overread for the contexts CTX. *)
Definition uci_check_no_overread_cg_holds_stmt (CTX : list (list Z)) : Prop :=
  pc_wrap_malloc (as_code B) = uci_sigma US___interceptor_trampoline_malloc ->
  pc_wrap_free (as_code B) = uci_sigma US___interceptor_trampoline_free ->
  uci_cells B ->
  uci_ro_rd_unowned B -> uci_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  uci_cno_uctx CTX -> uci_cno_ufix ->
  (forall fx' : YK11.FPState, @amalloc04_rule fx' rc tfib_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @afree04_rule fx' rc tfib_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (uci_sigma US___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @PR.uci_rp_uci_int_cg fx' rc B (uci_sigma US_rp_uci_int)) ->
  uci_check_no_overread_cg (uci_sigma US_check_no_overread) CTX.
End cno.
