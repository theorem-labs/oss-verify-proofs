From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** check_cells_valid(out, rc) (fuzz_headamp.c:207-219 with cells_valid :161-169 inlined; 92 bytes, 23 instructions
    at 0x146e0 in the plain image; frame 16 bytes, saves ra at sp - 8):
      0x146e0 addi sp,sp,-16; sd ra,8(sp); blez a1,0x1472c; addi a0,a0,2; addi a2,zero,0x2f; addi a3,zero,2;
      0x146f8 lbu a4,-2(a0); bltu a2,a4,0x14738; lbu a4,-1(a0); bltu a3,a4,0x14738; beq a4,a3,0x14714;
              addi a4,zero,1; j 0x14718; 0x14714 addi a4,zero,0x37;
      0x14718 lbu a5,0(a0); bltu a4,a5,0x14738; addi a1,a1,-1; addi a0,a0,3; bnez a1,0x146f8;
      0x1472c ld ra,8(sp); addi sp,sp,16; ret;
      0x14738 jal abort (0x15e64).
    The loop runs rc times (signed `blez`, then the count down) over the 3-byte cells at out, tests each cell's ch, param
    and value bytes unsigned (ch > 47, param > 2, value > (param = 2 ? 0x37 : 1) abort), and returns exactly when the
    C condition of :217 is false: rc <= 0, or every one of the rc cells is valid (Pod/Headamp.v's cell_valid, on
    values that are their own bytes). The premises state that on the 3 rc bytes it reads (ha_cells_bytes cs, with
    |cs| = rc). On that path it writes a0-a5 (a2, a3 only when rc > 0), stores ra at sp - 8 (its frame
    [sp - 16, sp)) and loads it back, and reads the cells; the cells lie below the stack region, so the frame store
    does not meet them.

    Call site (LLVMFuzzerTestOneInput, plain): 0x140e4 `jal check_cells_valid` (the only one), on every run past the
    first three mallocs, with sp = S - 560 and
      a0 = s3 = out (0x140dc `mv a0,s3`; 0x14084 `mv s3,a0` after malloc(3cap + 3) at 0x1407c);
      a1 = s6 = rc (0x140e0; 0x140c0 `mv s6,a0` after reac_headamp_prop_parse_result at 0x140bc).
    Why the premises hold there: the parse contract stores ha_cells_bytes cells at out and returns rc, for
    (rc, cells, _) = parse_props props cap; parse_props_total (answer_ok) gives rc = |cells| when rc >= 0 and
    Forall cell_valid cells; out is a heap block below the stack region [lo, sp) (lo = S - 65536), and check_count
    returned at 0x140d8 with s3, s6 kept: Prog/HeadSites.v [site_cells_valid]. The stack region is the frame's
    (FR's stk), writable and outside the image, lo + 16 <= S - 560; mem_inv holds of the memory the cut runs on and
    every callee since keeps it. *)
Definition CHECK_CELLS_VALID : Z := 0x146e0.
Definition CHECK_CELLS_VALID_FRAME : Z := 16.

Definition check_cells_valid_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo rc : Z) (cs : list cell),
    a1 = Z_to_bv 64 rc -> - 2 ^ 31 <= rc < 2 ^ 31 ->
    (0 < rc ->
       bytes_at rsegs m (bv_unsigned a0) (ha_cells_bytes cs) /\ Z.of_nat (length cs) = rc /\
       Forall cell_valid cs /\ bv_unsigned a0 + 3 * rc <= lo) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_CELLS_VALID_FRAME <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_CELLS_VALID_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_CELLS_VALID) fc None m (seg_rom rsegs)).
