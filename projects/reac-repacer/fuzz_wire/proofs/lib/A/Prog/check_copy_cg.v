(* Modified by Theorem Labs: reac-repacer/fuzz_uci's check_no_overread in the caller-journal form of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a; cgif_file_fuzzer lib/A/ACey.v trfc_specX, lib/YC20.v tlzw_spec), at this unit's core names and image A. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/reac-repacer/fuzz_uci/proofs/lib/A/Prog/check_no_overread_cg.v for reac-repacer/fuzz_wire's check_copy on image A: names uci_* / US_* / Uci* changed to wire_* / WS_* / Wire*; no call-context row and the result in a0 as that unit's check_value_cg.v states them (check_copy frees with a jal, not a tail call); the read-only-view premises (uci_rom_view_rd, uci_ro_rd_unowned, uci_rom_no_errno) removed, as no callee reads the read-only image through the view (the template's memchr did); the premises on the two frames c and f and on the bytes of c the call writes, the depot premise st_depot Sc <> [] (this unit's depot starts empty), the __asan_memcpy / bcmp / rp_copy_untag premises and the post's written range and result are check_copy's; every number measured on fuzz_wire.asan. *)
(* check_copy_cg: the ASan walk contract of check_copy (fuzz_wire.asan 0x80c38 = wire_sigma WS_check_copy,
   AF_check_copy = 0xde0 of lib/A/Prog/WirePList.v), as STATEMENTS only (no proof). The caller's journal is the
   premise, the post extends it by the call's events, the allocation is metered, and the block the call allocates is
   freed.

   The C (fuzz_wire.c check_copy, with untagged and fuzz.h's fuzz_dup inlined): got = rp_copy_untag (c, n);
   u = malloc (n ? n : 1), abort on NULL, memcpy (u, f, n) when n > 0; when n >= 18 and f[12..13] = 81 00 and
   f[16..17] = 88 19, memcpy (u + 12, f + 16, n - 16) and ulen = n - 4, else ulen = n; want = ulen when n >= 50,
   u[12..13] = 88 19 and u[16..17] = 00 00, else 0; abort unless got = want; when got > 0, abort unless
   bcmp (c, u, got) = 0; free (u); return got.
   The code (the listing of image A; offsets from entry):
     +0x0   `addi sp, sp, -0x40` (frame 0x40), then ra, s0..s5 stored at sp + 0x38 .. sp + 0x8; s3 = n, s4 = f, s1 = c;
     +0x28 / +0x2c / +0x30 `auipc` / `ld` of the GOT word 0x987e8, then `ld s5` of the shadow base through it (a
            runtime cell, wire_cells);
     +0x3c  `jal rp_copy_untag` (0x813e0) with a0 = c, a1 = n; s0 = its result from +0x40 on;
     +0x4c  `jal` to the malloc trampoline 0x522f8 with a0 = n + (n == 0) (+0x44 `seqz`, +0x48 `add`); `beqz a0` at
            +0x50 to the error path __asan_handle_no_return 0x590b8 / abort 0x88038 (+0x1e8 / +0x1ec); s2 = u;
     +0x58  `beqz s3` (n = 0) to +0x174; +0x68 `jal __asan_memcpy` (0x50c34) with a0 = u, a1 = f, a2 = n;
     +0x70  `bltu s3, 18` to +0x174; four 1-byte loads of f[12], f[13], f[16], f[17] (+0x88, +0xac, +0xcc, +0xf0), each
            after the instrumented check of its shadow byte (report calls of __asan_report_load1 0x580bc at +0x1f8,
            +0x204, +0x22c, +0x244); on 81 00 88 19, +0x108 `jal __asan_memcpy` with a0 = u + 12, a1 = f + 16,
            a2 = n - 16, and a2 = n - 4 (+0x10c), else a2 = n;
     +0x114 `bltu s3, 50` to +0x174; four checked 1-byte loads of u[12], u[13], u[16], u[17] (+0x12c, +0x14c, +0x16c,
            +0x1d4; reports at +0x210, +0x21c, +0x238, +0x250); +0x1e4 `beq s0, a0` (want) else the error path;
     +0x174 `bnez s0` (want = 0) to the error path; +0x178 `beqz s0` skips the compare; +0x188 `jal` to the bcmp
            trampoline 0x4157c with a0 = c, a1 = u, a2 = got; +0x18c `bnez a0` to the error path;
     +0x194 `jal` to the free trampoline 0x522f4 with a0 = u; +0x198 `mv a0, s0`; the epilogue; `ret` at +0x1bc.
   s0 holds got from +0x40 on, and 0 <= got <= n <= 1600 is below sp, so the frame-pointer chain at the malloc and
   the free is empty (YCbq.v achain / YG00.v bad_next) and both traces are fixed (lib/A/ACej.v TRACES_check_copy rows
   [0x52594; 0x80c88] and [0x52434; 0x80dd0]); the free is a `jal`, not a tail call, so the contract takes no call
   context. The error path is refuted: by the malloc rule (it never returns NULL, YC5d.v amalloc04_rule) and by
   rp_copy_untag's contract against the bytes of f, which c holds at entry (got = want, and c's got bytes equal u's).
   check_copy's own report branches follow loads of f and u: the shadow of f's block and of the fresh block u refutes
   them; c's shadow is read only by rp_copy_untag and the bcmp trampoline, whose premises the block premise on c
   gives. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require rp_copy_untag_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module PRU := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_copy_untag_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_copy's own frame (`addi sp, sp, -0x40` at +0x0). Its allocator calls use ASTACK below their sp, as the malloc
   rule asks (YC5d.v amalloc04_rule); rp_copy_untag's frame (0x20, `addi sp, sp, -0x20` at its entry) with the ESTACK
   of its callees, __asan_memcpy's ESTACK and the bcmp trampoline's 2 * ESTACK (YG0d.v abcmp_realizes) lie within it. *)
Definition CC_FRAME : Z := 0x40.
Definition CC_STK : Z := CC_FRAME + ASTACK.
(* malloc, free: one model event each (YC5d.v). *)
Definition CC_EV : Z := 2.
(* A frame is at most W_RECV_MAX = 1600 bytes (fuzz.h; LLVMFuzzerTestOneInput cuts n to it, fuzz_wire.c:261-262: its
   `li a0, 1600` at +0x58, `bltu s6, a0` at +0x60 and `li s1, 1600` at +0x64, 0x7feb0 .. 0x7febc). *)
Definition CC_RECV_MAX : Z := 1600.
(* Live bytes it adds: one block of max(n, 1) <= CC_RECV_MAX bytes (blocks_bytes counts the requested sizes). *)
Definition CC_LIVE : Z := CC_RECV_MAX.

(* The return addresses of its allocator calls, as offsets from its entry (the jal is 4 bytes before): malloc at +0x4c,
   free at +0x194 (0x80c88, 0x80dd0). *)
Definition WIRE_CC_RA_MALLOC : Z := wire_sigma WS_check_copy + 0x50.
Definition WIRE_CC_RA_FREE : Z := wire_sigma WS_check_copy + 0x198.

Section cc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* The meter cost of one call: its allocation of max(n, 1) bytes and one free. *)
Definition wire_check_copy_cost (n : Z) : Z := mo_malloc MT (Z.max n 1) + mo_free MT.

(* What a call leaves: the caller's journal extended by CC_EV events, callee-saved registers kept, no fake frame
   added, the caller's blocks exactly (u freed), the bytes YCbq.v acall_kept keeps with written range [c, c + n) (high
   memory outside the call's stack window, the caller's blocks outside [c, c + n): f's too, the image's unowned bytes
   and the live fake frames), the meter charged wire_check_copy_cost, the result len in a0 with 0 <= len <= n, and the
   n bytes c holds after the call. *)
Definition wire_cc_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (c n : Z) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (len : Z) (bs' : list byte),
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CC_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CC_STK) (spZ regs) (fun x => c <= x < c + n) /\
    mo_le MT Sc S2 (wire_check_copy_cost n) /\
    YK11.getr regs2 10 = w64 len /\ 0 <= len <= n /\
    Z.of_nat (length bs') = n /\ garr8 segs (mrestrict (w_H W2) mem2) c (map (fun b : byte => bv_unsigned b) bs').

(* The contract at entry address a. c (a0) and f (a1) each hold the same n (a2) bytes bs (c = fuzz_dup (f, n) in
   LLVMFuzzerTestOneInput, fuzz_wire.c:274-275), each inside one of the caller's blocks when n > 0, the two ranges
   disjoint. The call writes c's bytes (rp_copy_untag's memmove), so the caller's journal must let them change: each
   byte of [c, c + n) is in the journal's footprint FP or in a block allocated after the journal's start (YCbq.v
   in_tmp_block; the same condition the kernel's call rule asks of a callee's footprint). The depot already holds a
   trace (the caller's earlier mallocs): fuzz_wire's DepotCfg.depot_has_trace is false, so the malloc rule asks
   st_depot <> [] at the call. *)
Definition wire_check_copy_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (c f n T : Z) (bs : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 c -> YK11.getr regs 11 = w64 f -> YK11.getr regs 12 = w64 n ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CC_STK -> spZ regs <= sp0 ->
    0 <= n <= CC_RECV_MAX -> Z.of_nat (length bs) = n ->
    (0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= c /\ c + n <= bA + nA) ->
    (0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA) ->
    (0 < n -> c + n <= f \/ f + n <= c) ->
    (forall x, c <= x < c + n -> inFP FP x \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) x) ->
    garr8 segs (mrestrict (w_H W) memc) c (map (fun b : byte => bv_unsigned b) bs) ->
    garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs) ->
    st_depot Sc <> [] ->
    st_nev S + k + CC_EV <= EV_MAX -> blocks_bytes Sc + CC_LIVE <= LIVE_MAX ->
    mo_ok MT Sc T -> wire_check_copy_cost n <= T ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (wire_cc_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs c n).

(* Its two traces (lib/A/ACej.v TRACES_check_copy rows [0x52594; 0x80c88] and [0x52434; 0x80dd0]). *)
Definition wire_cc_ufix : Prop :=
  In (wire_utrace (pc_malloc_ra0 (as_code B)) [WIRE_CC_RA_MALLOC]) (as_universe B) /\
  In (wire_utrace (pc_free_ra0 (as_code B)) [WIRE_CC_RA_FREE]) (as_universe B).

(* The statement the walk will prove: the call rules' code addresses (the listing's trampolines), the runtime cells,
   the allocator and meter laws, the trace facts, and the contracts of __asan_memcpy, the bcmp trampoline and
   rp_copy_untag give the contract at WS_check_copy. *)
Definition wire_check_copy_holds_stmt : Prop :=
  pc_wrap_malloc (as_code B) = wire_sigma WS___interceptor_trampoline_malloc ->
  pc_wrap_free (as_code B) = wire_sigma WS___interceptor_trampoline_free ->
  wire_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  wire_cc_ufix ->
  (forall fx' : YK11.FPState, @amalloc04_rule fx' rc tfib_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @afree04_rule fx' rc tfib_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (wire_sigma WS___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (wire_sigma WS___interceptor_trampoline_bcmp)) ->
  (forall fx' : YK11.FPState, @PRU.wire_rp_copy_untag_cg fx' rc B (wire_sigma WS_rp_copy_untag)) ->
  wire_check_copy_cg (wire_sigma WS_check_copy).
End cc.
