(* In the form of reac-repacer/fuzz_uci's lib/B/Prog/rp_hot_clamp_c.v (recipes commit 0295462466b2), for reac-repacer/fuzz_wire's rp_counter in image B: Img0 / AsanCells / AsanKA are lib/B's, the entry and every address in the comments are fuzz_wire.asan-ubsan's, the result is lib/Prog/rp_counter_c.v's counter_result (repace_wire.c:69-72), and image B's UBSan premise `bv_unsigned a0 <> 0` (the trap at +0x8, unimp at +0x68) is stated as uci's B text states its traps; rp_counter reads and writes no struct, so the premises and the post that name the struct (hot_int, rw_cells, the struct's munch range) are absent, the premises on the two bytes it reads are those of libreac/fuzz_decode's released lib/B/Prog/reac_frame_counter_c.v (the same two reads), and the post gives a0. That released text is NOT copied: its code is this code plus `slli a0, a0, 0x30` / `srli a0, a0, 0x30` (its uint16_t return) before the return, two instructions more. *)
(* rp_counter_c: rp_counter of fuzz_wire.asan-ubsan (0x81314 = wire_sigma WS_rp_counter, lib/B/Prog/WirePAddr.v), a
   leaf. The code (DIS of image B, 35 instructions, 0x81314 .. 0x8139c):
     +0x0  `addi sp, sp, -0x10`, +0x4 `sd ra, 8(sp)` ... +0x5c `ld ra, 8(sp)`, +0x60 `addi sp, sp, 0x10`, +0x64 `ret`
           (frame [sp - 16, sp); its only store is ra's, the only return is +0x64);
     +0x8  `beqz a0` to `unimp` at +0x68 (0x8137c): UBSan's null check of f;
     +0xc  `addi a1, zero, -0xf`, +0x10 `bltu a1, a0` and +0x14 `bgeu a0, a1`, both to `unimp` at +0x68: UBSan's
           pointer-overflow checks of f + 14 / f + 15 (taken iff f >= 2 ^ 64 - 15);
     +0x18 `auipc a1, 0x17`, +0x1c `ld a1, 0x54c(a1)`: the GOT word GOT_CELL_K (0x98878), then +0x20 `ld a2, 0(a1)`:
           the shadow base in CELL_K (0xa07f8, __asan_shadow_memory_dynamic_address);
     +0x30 `lb a3, 0(a3)`: the shadow byte of f + 14, +0x34 `bnez a3` to the slow check +0x6c / +0x70, which calls
           __asan_report_load1 (0x57e5c) at +0x78 when the byte is not addressable;
     +0x44 `lb a2, 0(a2)`: the shadow byte of f + 15, +0x4c `bnez a2` to the slow check +0x7c / +0x80, which calls
           __asan_report_load1 at +0x88;
     +0x48 `lbu a0, 0xe(a0)` (f[14]), +0x50 `lbu a1, 0(a1)` (f[15]), +0x54 `slli a1, a1, 8`, +0x58 `or a0, a1, a0`.
   It writes a0 .. a4 only, and calls nothing but the two report sinks. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_counter_c.

Definition RP_COUNTER : Z := 0x81314.
Definition RP_COUNTER_FRAME : Z := 16.

Definition rp_counter_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (16 <= length bs)%nat ->
    (* Image B's UBSan premise: 0x8131c `beqz a0, 0x8137c` traps (unimp at 0x8137c) on f == NULL. The overflow traps
       0x81324 / 0x81328 (f >= 2 ^ 64 - 15) are refuted by `addressable` below (f + 16 <= APPMEM_END). *)
    bv_unsigned a0 <> 0 ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_COUNTER_FRAME <= bv_unsigned sp ->
    off_stk sp RP_COUNTER_FRAME (bv_unsigned a0) 16 ->
    app_mem (bv_unsigned sp - RP_COUNTER_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp RP_COUNTER_FRAME GOT_CELL_K 8 ->
    off_stk sp RP_COUNTER_FRAME CELL_K 8 ->
    (* the two bytes it reads are addressable: refutes the report branches 0x8138c and 0x8139c *)
    addressable m (bv_unsigned a0 + 14) 2 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (PRC.counter_result bs)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_COUNTER_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_COUNTER) fc None m (seg_rom rsegs)).
