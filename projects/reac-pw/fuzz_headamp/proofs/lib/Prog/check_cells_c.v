From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** check_cells(out, rc, x) (fuzz_headamp.c:239-259 with cells_equal :172-181 inlined; 96 bytes, 24 instructions at
    0x14780 in the plain image; frame 16 bytes, saves ra at sp - 8):
      0x14780 addi sp,sp,-16; sd ra,8(sp); lw a3,0(a2); bne a1,a3,0x147dc; blez a1,0x147d0;
              addi a0,a0,2; addi a2,a2,8;
      0x1479c lbu a3,-2(a0); lw a4,-4(a2); bne a4,a3,0x147dc; lbu a3,-1(a0); lw a4,0(a2); bne a4,a3,0x147dc;
              lbu a3,0(a0); lw a4,4(a2); bne a4,a3,0x147dc; addi a1,a1,-1; addi a0,a0,3; addi a2,a2,12;
              bnez a1,0x1479c;
      0x147d0 ld ra,8(sp); addi sp,sp,16; ret;
      0x147dc jal abort (0x15e64).
    It aborts unless rc = x->rc (64-bit rc against the sign-extended x->rc) and, for i < rc, out[i]'s three bytes
    (lbu) equal x->cell[i]'s three ints (lw) field by field. It returns exactly when the C condition of :257 is
    false; the premises state that on the bytes it reads: x->rc = rc, and for rc > 0 a list cs of rc cells whose
    fields fit a byte (cell_bytes_ok), held as bytes at out (ha_cells_bytes cs) and as ints at x + 4
    (x_cells_bytes cs). On that path it writes a0-a4, stores ra at sp - 8 (its frame [sp - 16, sp)) and loads it
    back; out lies below the stack region and x at or above sp, so the frame store meets neither.

    Call site (LLVMFuzzerTestOneInput, plain): 0x14128 `jal check_cells` (the only one), reached when
    pp->corrupt = 0, just after check_object returned, with sp = S - 560 and
      a0 = s3 = out (0x14120), a1 = s6 = rc (0x14124), a2 = sp + 0x90 = &x (0x1411c).
    Why the premises hold there: x = x_bytes (expect_model null cap r) (M03's walk), parse_props props cap =
    expect_model null cap r (parse_props_build), so x->rc = rc and x's first rc cells are the parse's cells, which
    the parse contract stored as ha_cells_bytes at out; parse_props_total gives rc = |cells| and cell_valid, hence
    cell_bytes_ok (Spec/HeadBytes.v cell_valid_bytes_ok): Prog/HeadSites.v [site_cells]. x = sp + 0x90 >= sp. *)
Definition CHECK_CELLS : Z := 0x14780.
Definition CHECK_CELLS_FRAME : Z := 16.

Definition check_cells_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo rc : Z) (cs : list cell),
    a1 = Z_to_bv 64 rc -> - 2 ^ 31 <= rc < 2 ^ 31 ->
    bytes_at rsegs m (bv_unsigned a2) (le4 (Z_to_bv 64 rc)) -> bv_unsigned sp <= bv_unsigned a2 ->
    (0 < rc ->
       Z.of_nat (length cs) = rc /\ Forall cell_bytes_ok cs /\
       bytes_at rsegs m (bv_unsigned a0) (ha_cells_bytes cs) /\ bv_unsigned a0 + 3 * rc <= lo /\
       bytes_at rsegs m (bv_unsigned a2 + 4) (x_cells_bytes cs)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_CELLS_FRAME <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_CELLS_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_CELLS) fc None m (seg_rom rsegs)).
