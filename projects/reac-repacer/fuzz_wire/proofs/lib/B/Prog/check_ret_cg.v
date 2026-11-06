(* In the form of reac-repacer/fuzz_uci's lib/B/Prog/check_clamp_cg.v (recipes commit 0295462466b2; the caller-journal form, its leaf callee taken through the kit's wrapper), for reac-repacer/fuzz_wire's check_ret in image B: the B core's names (lib/B/YB1v.v, lib/B/YE2k.v, lib/B/YCbq.v / YC5d.v), the kit lib/B/Prog/WirePSyms.v / WirePAddr.v / WireCg.v, and every address in the comments measured on fuzz_wire.asan-ubsan. The frame f is fuzz_dup's heap block (LLVMFuzzerTestOneInput's malloc call at 0x7fc7c), not a struct on the real stack, so check_clamp's premises on its struct (`spZ regs <= pin`, `pin + RP_HOT_SIZE < sp0`, range_addressable, shadow_hull_vis, the alignment premise) are replaced by the heap-block premise of reac-repacer/fuzz_uci's lib/B/Prog/check_value_cg.v (recipes commit 0295462466b2) with its length and garr8 rows (the length row `0 <= n < 2 ^ 64`: check_value's REPLY_MAX bound serves its callee rp_uci_int, which has no twin here); check_ret calls neither __asan_stack_malloc_* nor __asan_memcpy and keeps no fake frame, so those contracts, the stack-malloc entry and the fake-stack laws go; its leaf callee rp_ret_accept writes no byte outside its own frame, so it is taken through the non-writing wrapper wire_leaf_at. *)
(* check_ret_cg: the ASan walk contract of check_ret (fuzz_wire.asan-ubsan 0x7ff2c = wire_sigma WS_check_ret,
   lib/B/Prog/WirePAddr.v), as STATEMENTS only (no proof).

   The C (fuzz_wire.c:72-84 check_ret): want = n >= 14 && w_is_reac (f, 12) (fuzz.h: f[12] == 0x88 && f[13] == 0x19);
   abort unless rp_ret_accept (f, n) equals want.
   The code (DIS of image B, 47 instructions, 0x7ff2c .. 0x7ffe4):
     +0x0   `addi sp, sp, -0x10` (frame 0x10), +0x4 `sd ra, 8(sp)`, +0x8 `sd s0, 0(sp)`: its only stores, all in its own
            frame;
     +0xc   `addi a2, zero, 0xe`, +0x10 `bltu a1, a2` to +0x74 `mv s0, zero` (n < 14: want = 0, f not read);
     +0x14  `addi a2, zero, -0xc`, +0x18 `bgeu a0, a2` to `unimp` at +0x98 (0x7ffc4): UBSan's pointer-overflow check of
            f + 12 (taken iff f >= 2 ^ 64 - 12);
     +0x1c  `auipc a2, 0x19`, +0x20 `ld a2, -0x6d0(a2)`: the GOT word 0x98878, +0x24 `ld a3, 0(a2)`: the shadow base in
            the cell 0xa07f8 (__asan_shadow_memory_dynamic_address);
     +0x34  `lb a4, 0(a4)`: the shadow byte of f + 12, +0x38 `bnez a4` to the slow check +0x9c / +0xa0, which calls
            __asan_report_load1 (0x57e5c) at +0xa8;
     +0x3c  `lbu a2, 0(a2)` (f[12]), +0x40 `addi a4, zero, 0x88`, +0x44 `bne a2, a4` to +0x74 (want = 0);
     +0x48  `addi a2, zero, -0xe`, +0x4c `bltu a2, a0` to `unimp` at +0x98: UBSan's pointer-overflow check of f + 13
            (taken iff f > 2 ^ 64 - 14);
     +0x5c  `lb a3, 0(a3)`: the shadow byte of f + 13, +0x60 `bnez a3` to the slow check +0xac / +0xb0, which calls
            __asan_report_load1 at +0xb8;
     +0x64  `lbu a2, 0(a2)` (f[13]), +0x68 `addi a2, a2, -0x19`, +0x6c `seqz s0, a2` (want), +0x70 `j` +0x78;
     +0x78  `jal rp_ret_accept` (0x80ee0) with a0 = f, a1 = n (neither written before it); return address +0x7c
            (0x7ffa8);
     +0x7c  `bne a0, s0` to +0x90 `jal __asan_handle_no_return` (0x58e58) and +0x94 `jal abort` (0x880cc);
     +0x80 .. +0x8c  `ld ra / s0`, `addi sp, sp, 0x10`, `ret` (0x7ffb8): its only return.
   It allocates nothing and charges the meter nothing; it writes no byte outside its own frame, and its callee writes
   none outside its own. The traps and the report branches are refuted by the block premise (f's n bytes inside one of
   the caller's blocks when n > 0), the abort by rp_ret_accept's leaf contract (a0 = lib/Prog/rp_ret_accept_c.v
   ret_accept_result n of the bytes, which is want). Its two calls of the runtime (__asan_handle_no_return, abort) lie
   on the abort path only, so no runtime contract is a premise. *)
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
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_ret_accept_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module LRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog.rp_ret_accept_cg.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_ret's frame (`addi sp, sp, -0x10` at WS_check_ret) and the ESTACK its leaf callee rp_ret_accept uses below its
   sp. *)
Definition CR_FRAME : Z := 0x10.
Definition CR_STK : Z := CR_FRAME + ESTACK.
(* No allocator event: it calls no allocator. *)
Definition CR_EV : Z := 0.

Section cr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: the caller's journal extended by CR_EV events, callee-saved registers kept, the caller's frames
   and blocks exactly, every byte outside the call's stack window kept (YCbq.v acall_kept with no written range: f's n
   bytes are intact for the next check), and no meter charge. *)
Definition wire_cr_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CR_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CR_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 0.

(* The contract at entry address a, in the caller-journal form. f (a0) holds the n (a1) bytes bs; when n > 0 they lie
   inside one of the caller's blocks (fuzz_dup's heap copy). *)
Definition wire_check_ret_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (f n : Z) (bs : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 n ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CR_STK -> spZ regs <= sp0 ->
    0 <= n < 2 ^ 64 -> Z.of_nat (length bs) = n ->
    (* the block premise: refutes the traps 0x7ff44 / 0x7ff78 (unimp at 0x7ffc4), the report branches 0x7ffd4 /
       0x7ffe4, and rp_ret_accept's trap 0x80ef0 (f == NULL when 14 <= n) *)
    (0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= f /\ f + n <= bA + nA) ->
    garr8 segs (mrestrict (w_H W) memc) f (map (fun b : byte => bv_unsigned b) bs) ->
    st_nev S + k + CR_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (wire_cr_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs).

(* The statement the walk will prove: the runtime cells (the shadow base and its GOT word, read at +0x20 / +0x24 and
   by the leaf), the allocator and meter laws, and the leaf contract of rp_ret_accept (through the non-writing
   wrapper) give the contract at WS_check_ret. *)
Definition wire_check_ret_holds_stmt : Prop :=
  wire_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @wire_leaf_at rc B (@LRA.wire_rp_ret_accept_cg) fx') ->
  wire_check_ret_cg (wire_sigma WS_check_ret).
End cr.
