From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_plain(plain, rc, out, first) (fuzz_headamp.c:297-309 with cells_same :288-295 inlined; 116 bytes, 29
    instructions at 0x14ae8 in the UBSan image; frame 16 bytes, saves ra at sp - 8):
      0x14ae8 addi sp,sp,-16; sd ra,8(sp); bne a0,a1,0x14b54; blez a0,0x14b48; mv a1,zero; not a4,a2;
              not a5,a3; addi a3,a3,2;
      0x14b08 bltu a4,a1,0x14b58; bltu a5,a1,0x14b58; lbu a6,0(a2); lbu a7,-2(a3); bne a6,a7,0x14b54;
              lbu a6,1(a2); lbu a7,-1(a3); bne a6,a7,0x14b54; lbu a6,2(a2); lbu a7,0(a3); bne a6,a7,0x14b54;
              addi a0,a0,-1; addi a2,a2,3; addi a3,a3,3; addi a1,a1,3; bnez a0,0x14b08;
      0x14b48 ld ra,8(sp); addi sp,sp,16; ret;
      0x14b54 jal abort (0x16364); 0x14b58 unimp.
    The plain tests (lib/Prog/check_plain_c.v) with two UBSan checks per cell i (a1 = 3i) to the trap 0x14b58:
    ~out <u 3i and ~first <u 3i (the pointer overflow of out + 3i, first + 3i), false when out + 3 rc and
    first + 3 rc are at most 2^64 (bytes_at's bounds). On the path that returns it writes a0-a7, stores ra at
    sp - 8 (its frame [sp - 16, sp)) and loads it back; both blocks lie below the stack region.

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x14828 `jal check_plain` (the only one), with sp = S - 608 and
      a0 = plain, the value reac_headamp_prop_parse returned at 0x14818 (a0 = s5, a1 = s3, a2 = s2, 0x1480c-0x14814);
      a1 = s6 = rc (0x1481c), a2 = s3 = out (0x14820), a3 = s7 = first (0x14824; 0x147e4 `mv s7,a0` after
           malloc at 0x147dc).
    Why the premises hold there: as in the plain file (memcpy(first, out, 3rc) at 0x147f8 when rc > 0, memset(out,
    0xa5) at 0x14808, the two parses on the same pod bytes): U/Prog/HeadSites.v [site_plain]. *)
Definition CHECK_PLAIN : Z := 0x14ae8.
Definition CHECK_PLAIN_FRAME : Z := 16.

Definition check_plain_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo rc : Z) (w : list byte),
    a0 = a1 -> a1 = Z_to_bv 64 rc -> - 2 ^ 31 <= rc < 2 ^ 31 ->
    (0 < rc ->
       Z.of_nat (length w) = 3 * rc /\
       bytes_at rsegs m (bv_unsigned a2) w /\ bv_unsigned a2 + 3 * rc <= lo /\
       bytes_at rsegs m (bv_unsigned a3) w /\ bv_unsigned a3 + 3 * rc <= lo) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_PLAIN_FRAME <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_PLAIN_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_PLAIN) fc None m (seg_rom rsegs)).
