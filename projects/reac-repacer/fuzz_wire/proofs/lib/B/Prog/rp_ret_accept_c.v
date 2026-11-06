(* In the form of reac-repacer/fuzz_uci's lib/B/Prog/rp_hot_clamp_c.v (recipes commit 0295462466b2), for reac-repacer/fuzz_wire's rp_ret_accept in image B: Img0 / AsanCells / AsanKA are lib/B's, the entry and every address in the comments are fuzz_wire.asan-ubsan's, the result is lib/Prog/rp_ret_accept_c.v's ret_accept_result (repace_wire.c:45-48 with is_reac of :17-20), and image B's UBSan premise `bv_unsigned a0 <> 0` (the trap at +0x10, unimp at +0x84) is stated as uci's B text states its traps; rp_ret_accept reads and writes no struct, so the premises and the post that name the struct (hot_int, rw_cells, the struct's munch range) are absent and the post gives a0; as the function reads the frame only past its own early exit (n < 14 at +0xc), every premise on f holds under `14 <= n`, as libreac/fuzz_decode's released lib/B/Prog/reac_frame_is_reac_F_c.v states them. That released text is NOT copied: reac_frame_is_reac tests f == NULL first and RETURNS 0 there, and tests n < 14 second; rp_ret_accept tests n < 14 first and TRAPS on f == NULL (`beqz a0` to `unimp`), one instruction less. *)
(* rp_ret_accept_c: rp_ret_accept of fuzz_wire.asan-ubsan (0x80ee0 = wire_sigma WS_rp_ret_accept,
   lib/B/Prog/WirePAddr.v), a leaf. The code (DIS of image B, 41 instructions, 0x80ee0 .. 0x80f80):
     +0x0  `addi sp, sp, -0x10`, +0x4 `sd ra, 8(sp)` ... +0x78 `ld ra, 8(sp)`, +0x7c `addi sp, sp, 0x10`, +0x80 `ret`
           (frame [sp - 16, sp); its only store is ra's, the only return is +0x80);
     +0x8  `addi a2, zero, 0xe`, +0xc `bltu a1, a2` to +0x74 `mv a0, zero` (n < 14: 0, f not read);
     +0x10 `beqz a0` to `unimp` at +0x84 (0x80f64): UBSan's null check of f;
     +0x14 `addi a1, zero, -0xc`, +0x18 `bgeu a0, a1` to `unimp` at +0x84: UBSan's pointer-overflow check of f + 12
           (taken iff f >= 2 ^ 64 - 12);
     +0x1c `auipc a1, 0x18`, +0x20 `ld a1, -0x684(a1)`: the GOT word GOT_CELL_K (0x98878), then +0x24 `ld a2, 0(a1)`:
           the shadow base in CELL_K (0xa07f8, __asan_shadow_memory_dynamic_address);
     +0x34 `lb a3, 0(a3)`: the shadow byte of f + 12, +0x38 `bnez a3` to the slow check +0x88 / +0x8c, which calls
           __asan_report_load1 (0x57e5c) at +0x94 when the byte is not addressable;
     +0x3c `lbu a1, 0(a1)` (f[12]), +0x40 `addi a3, zero, 0x88`, +0x44 `bne a1, a3` to +0x74 (0);
     +0x48 `addi a1, zero, -0xe`, +0x4c `bltu a1, a0` to `unimp` at +0x84: UBSan's pointer-overflow check of f + 13
           (taken iff f > 2 ^ 64 - 14);
     +0x5c `lb a1, 0(a1)`: the shadow byte of f + 13, +0x60 `bnez a1` to the slow check +0x98 / +0x9c, which calls
           __asan_report_load1 at +0xa0;
     +0x64 `lbu a0, 0(a0)` (f[13]), +0x68 `addi a0, a0, -0x19`, +0x6c `seqz a0, a0`, +0x70 `j` +0x78.
   It writes a0 .. a4 only, and calls nothing but the two report sinks. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ret_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module PRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ret_accept_c.

Definition RP_RET_ACCEPT : Z := 0x80ee0.
Definition RP_RET_ACCEPT_FRAME : Z := 16.

Definition rp_ret_accept_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_RET_ACCEPT_FRAME <= bv_unsigned sp ->
    app_mem (bv_unsigned sp - RP_RET_ACCEPT_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    (* past the early exit 0x80eec (n < 14) only *)
    (14 <= bv_unsigned a1 ->
       (14 <= length bs)%nat /\
       (* Image B's UBSan premise: 0x80ef0 `beqz a0, 0x80f64` traps (unimp at 0x80f64) on f == NULL. The overflow
          traps 0x80ef8 (f >= 2 ^ 64 - 12) and 0x80f2c (f > 2 ^ 64 - 14) are refuted by `addressable` below
          (f + 14 <= APPMEM_END). *)
       bv_unsigned a0 <> 0 /\
       bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp RP_RET_ACCEPT_FRAME (bv_unsigned a0) 14 /\
       asan_cells m /\
       off_stk sp RP_RET_ACCEPT_FRAME GOT_CELL_K 8 /\
       off_stk sp RP_RET_ACCEPT_FRAME CELL_K 8 /\
       (* the two bytes it may read are addressable: refutes the report branches 0x80f74 and 0x80f80 *)
       addressable m (bv_unsigned a0 + 12) 2) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (PRA.ret_accept_result (bv_unsigned a1) bs))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_RET_ACCEPT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_RET_ACCEPT) fc None m (seg_rom rsegs)).
