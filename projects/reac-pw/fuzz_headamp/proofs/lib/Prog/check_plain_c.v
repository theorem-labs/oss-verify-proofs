From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(** check_plain(plain, rc, out, first) (fuzz_headamp.c:297-309 with cells_same :288-295 inlined; 92 bytes, 23
    instructions at 0x14818 in the plain image; frame 16 bytes, saves ra at sp - 8):
      0x14818 addi sp,sp,-16; sd ra,8(sp); bne a0,a1,0x14870; blez a0,0x14864; addi a3,a3,2; addi a2,a2,2;
      0x14830 lbu a1,-2(a2); lbu a4,-2(a3); bne a1,a4,0x14870; lbu a1,-1(a2); lbu a4,-1(a3); bne a1,a4,0x14870;
              lbu a1,0(a2); lbu a4,0(a3); bne a1,a4,0x14870; addi a0,a0,-1; addi a3,a3,3; addi a2,a2,3;
              bnez a0,0x14830;
      0x14864 ld ra,8(sp); addi sp,sp,16; ret;
      0x14870 jal abort (0x15e64).
    It aborts unless plain = rc (64-bit) and, for rc > 0, the 3 rc bytes at out equal the 3 rc bytes at first. It
    returns exactly when the C condition of :307 is false; the premises state it as a0 = a1 and one byte list w of
    length 3 rc at both out and first. On that path it writes a0-a4, stores ra at sp - 8 (its frame [sp - 16, sp))
    and loads it back; both blocks lie below the stack region, so the frame store meets neither.

    Call site (LLVMFuzzerTestOneInput, plain): 0x141b0 `jal check_plain` (the only one), on every run past the four
    mallocs, with sp = S - 560 and
      a0 = plain, the value reac_headamp_prop_parse returned at 0x141a0 (a0 = s5, a1 = s3, a2 = s2 as for the first
           parse, 0x14194-0x1419c);
      a1 = s6 = rc (0x141a4), a2 = s3 = out (0x141a8), a3 = s7 = first (0x141ac; 0x1416c `mv s7,a0` after
           malloc(3 max(rc, 0) or 1) at 0x14164).
    Why the premises hold there: between the two parses main writes only first (memcpy(first, out, 3rc) at 0x14180
    when rc > 0), out (memset 0xa5 at 0x14190), x, res and the stack, never the pod block, so both parses read the
    same bytes with the same cap, and both contracts (Prog/reac_headamp_prop_parse_result_c.v,
    Prog/reac_headamp_prop_parse_c.v) answer parse_props props cap: plain = rc, and out holds
    ha_cells_bytes cells after each; first holds the copy of the first: w = ha_cells_bytes cells, |w| = 3 rc for
    rc > 0 (answer_ok): Prog/HeadSites.v [site_plain]. *)
Definition CHECK_PLAIN : Z := 0x14818.
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
      (fun ms' => exists (a0' a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_PLAIN_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_PLAIN) fc None m (seg_rom rsegs)).
