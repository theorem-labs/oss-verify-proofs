From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** check_cells(out, rc, x) (fuzz_headamp.c:239-259 with cells_equal :172-181 inlined; 164 bytes, 41 instructions at
    0x149e4 in the UBSan image; frame 16 bytes, saves ra at sp - 8):
      0x149e4 addi sp,sp,-16; sd ra,8(sp); andi a3,a2,3; bnez a3,0x14a7c; lw a3,0(a2); bne a1,a3,0x14a80;
              blez a1,0x14a70; mv a3,zero; mv a4,zero; not a5,a0; addi a6,a2,4; slli a7,a1,2; slli t0,a1,4;
              addi a0,a0,1; addi a2,a2,8; not a1,a6; sub a6,t0,a7; addi a7,zero,0x1e;
      0x14a2c bltu a5,a3,0x14a7c; beq a3,a7,0x14a7c; bltu a1,a4,0x14a7c; lbu t1,-1(a0); add t0,a2,a4;
              lw t2,-4(t0); bne t2,t1,0x14a80; lbu t1,0(a0); lw t2,0(t0); bne t2,t1,0x14a80; lbu t1,1(a0);
              lw t0,4(t0); bne t0,t1,0x14a80; addi a4,a4,12; addi a0,a0,3; addi a3,a3,3; bne a6,a4,0x14a2c;
      0x14a70 ld ra,8(sp); addi sp,sp,16; ret;
      0x14a7c unimp; 0x14a80 jal abort (0x16364); unimp.
    The plain tests (lib/Prog/check_cells_c.v) with four UBSan checks to the trap 0x14a7c: x & 3 (alignment of
    struct expect), and per cell i (a3 = 3i, a4 = 12i): ~out <u 3i (pointer overflow of out + 3i), 3i = 30 (the
    index i = CAP_MAX = 10 of x->cell[], out of bounds), ~(x + 4) <u 12i (pointer overflow of x->cell + i).
    Discharged by x mod 4 = 0, rc <= 10 and the bounds of bytes_at (out + 3 rc, x + 4 + 12 rc <= 2^64). On the path
    that returns it writes a0-a7, t0-t2, stores ra at sp - 8 (its frame [sp - 16, sp)) and loads it back; out lies
    below the stack region and x at or above sp.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x147a0 `jal check_cells` (the only one), reached when
    pp->corrupt = 0, just after check_object returned, with sp = S - 608 and
      a0 = s3 = out (0x14798), a1 = s6 = rc (0x1479c), a2 = sp + 0xb8 = &x (0x14794).
    Why the premises hold there: as in the plain file; rc <= cap <= 9 (answer_ok) and x = S - 608 + 0xb8 is
    4-aligned: U/Prog/HeadSites.v [site_cells]. *)
Definition CHECK_CELLS : Z := 0x149e4.
Definition CHECK_CELLS_FRAME : Z := 16.

Definition check_cells_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo rc : Z) (cs : list cell),
    a1 = Z_to_bv 64 rc -> - 2 ^ 31 <= rc <= 10 ->
    bv_unsigned a2 mod 4 = 0 ->
    bytes_at rsegs m (bv_unsigned a2) (le4 (Z_to_bv 64 rc)) -> bv_unsigned sp <= bv_unsigned a2 ->
    (0 < rc ->
       Z.of_nat (length cs) = rc /\ Forall cell_bytes_ok cs /\
       bytes_at rsegs m (bv_unsigned a0) (ha_cells_bytes cs) /\ bv_unsigned a0 + 3 * rc <= lo /\
       bytes_at rsegs m (bv_unsigned a2 + 4) (x_cells_bytes cs)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_CELLS_FRAME <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_CELLS_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_CELLS) fc None m (seg_rom rsegs)).
