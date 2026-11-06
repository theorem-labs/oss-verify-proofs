(* In the form of reac-repacer/fuzz_uci's lib/B/Prog/check_clamp_cg.v (recipes commit 0295462466b2; the caller-journal form, its leaf callee taken through the kit's wrapper), for reac-repacer/fuzz_wire's check_counter in image B: the B core's names (lib/B/YB1v.v, lib/B/YE2k.v, lib/B/YCbq.v / YC5d.v), the kit lib/B/Prog/WirePSyms.v / WirePAddr.v / WireCg.v, and every address in the comments measured on fuzz_wire.asan-ubsan. The frame f is fuzz_dup's heap block (LLVMFuzzerTestOneInput's malloc call at 0x7fc7c), not a struct on the real stack, so check_clamp's premises on its struct (`spZ regs <= pin`, `pin + RP_HOT_SIZE < sp0`, range_addressable, shadow_hull_vis, the alignment premise) are replaced by the heap-block premise of reac-repacer/fuzz_uci's lib/B/Prog/check_value_cg.v (recipes commit 0295462466b2) with its length and garr8 rows (the length row `0 <= n < 2 ^ 64`: check_value's REPLY_MAX bound serves its callee rp_uci_int, which has no twin here); check_counter calls neither __asan_stack_malloc_* nor __asan_memcpy and keeps no fake frame, so those contracts, the stack-malloc entry and the fake-stack laws go; its leaf callee rp_counter writes no byte outside its own frame, so it is taken through the non-writing wrapper wire_leaf_at. *)
(* check_counter_cg: the ASan walk contract of check_counter (fuzz_wire.asan-ubsan 0x804c0 = wire_sigma WS_check_counter,
   lib/B/Prog/WirePAddr.v), as STATEMENTS only (no proof).

   The C (fuzz_wire.c:133-144 check_counter): return when n < 18; abort unless rp_counter (f) equals
   (unsigned)(f[14] | f[15] << 8).
   The code (DIS of image B, 47 instructions, 0x804c0 .. 0x80578):
     +0x0   `addi sp, sp, -0x20` (frame 0x20), +0x4 `sd ra, 24(sp)`, +0x8 `sd s0, 16(sp)`, +0xc `sd s1, 8(sp)`: its only
            stores, all in its own frame;
     +0x10  `addi a2, zero, 0x12`, +0x14 `bltu a1, a2` to +0x78 (n < 18: return; nothing read, nothing called);
     +0x18  `mv s0, a0`; +0x1c `auipc a0, 0x18`, +0x20 `ld a0, 0x39c(a0)`: the GOT word 0x98878, +0x24 `ld s1, 0(a0)`:
            the shadow base in the cell 0xa07f8 (__asan_shadow_memory_dynamic_address);
     +0x2c  `jal rp_counter` (0x81314) with a0 = f; return address +0x30 (0x804f0);
     +0x30  `addi a1, zero, -0xf`, +0x34 `bltu a1, s0` and +0x38 `bgeu s0, a1` to `unimp` at +0x8c (0x8054c): UBSan's
            pointer-overflow checks of f + 14 / f + 15 (taken iff f >= 2 ^ 64 - 15);
     +0x48  `lb a2, 0(a2)`: the shadow byte of f + 14, +0x4c `bnez a2` to the slow check +0x90 / +0x94, which calls
            __asan_report_load1 (0x57e5c) at +0x9c;
     +0x5c  `lb a2, 0(a2)`: the shadow byte of f + 15, +0x64 `bnez a2` to the slow check +0xa0 / +0xa4, which calls
            __asan_report_load1 at +0xac;
     +0x60  `lbu a1, 0(a1)` (f[14]), +0x68 `lbu a2, 0(s0)` (f[15]), +0x6c `slli a2, a2, 8`, +0x70 `or a1, a2, a1`;
     +0x74  `bne a0, a1` to +0xb0 `jal __asan_handle_no_return` (0x58e58) and +0xb4 `jal abort` (0x880cc); `unimp` at
            +0xb8 follows the abort;
     +0x78 .. +0x88  `ld ra / s0 / s1`, `addi sp, sp, 0x20`, `ret` (0x80548): its only return.
   It allocates nothing and charges the meter nothing; it writes no byte outside its own frame, and its callee writes
   none outside its own. The traps and the report branches are refuted by the block premise (f's n bytes inside one of
   the caller's blocks when n > 0), the abort by rp_counter's leaf contract (a0 = lib/Prog/rp_counter_c.v
   counter_result of the bytes, f[14] + 256 * f[15], the value it computes). Its two calls of the runtime
   (__asan_handle_no_return, abort) lie on the abort path only, so no runtime contract is a premise. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms WirePAddr WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_counter_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_counter_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_counter's frame (`addi sp, sp, -0x20` at WS_check_counter) and the ESTACK its leaf callee rp_counter uses below
   its sp. *)
Definition CCN_FRAME : Z := 0x20.
Definition CCN_STK : Z := CCN_FRAME + ESTACK.
(* No allocator event: it calls no allocator. *)
Definition CCN_EV : Z := 0.

Section ccn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: the caller's journal extended by CCN_EV events, callee-saved registers kept, the caller's
   frames and blocks exactly, every byte outside the call's stack window kept (YCbq.v acall_kept with no written
   range: f's n bytes are intact for the next check), and no meter charge. *)
Definition wire_ccn_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CCN_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CCN_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 0.

(* The contract at entry address a, in the caller-journal form. f (a0) holds the n (a1) bytes bs; when n > 0 they lie
   inside one of the caller's blocks (fuzz_dup's heap copy). *)
Definition wire_check_counter_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (f n : Z) (bs : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 n ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CCN_STK -> spZ regs <= sp0 ->
    0 <= n < 2 ^ 64 -> Z.of_nat (length bs) = n ->
    (* the block premise: refutes the traps 0x804f4 / 0x804f8 (unimp at 0x8054c), the report branches 0x8055c /
       0x8056c, and rp_counter's trap 0x8131c (f == NULL) *)
    (0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA) ->
    garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs) ->
    st_nev S + k + CCN_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (wire_ccn_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).

(* The statement the walk will prove: the runtime cells (the shadow base and its GOT word, read at +0x20 / +0x24 and
   by the leaf), the allocator and meter laws, and the leaf contract of rp_counter (through the non-writing wrapper)
   give the contract at WS_check_counter. *)
Definition wire_check_counter_holds_stmt : Prop :=
  wire_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @wire_leaf_at rc B (@LRC.wire_rp_counter_cg) fx') ->
  wire_check_counter_cg (wire_sigma WS_check_counter).
End ccn.
