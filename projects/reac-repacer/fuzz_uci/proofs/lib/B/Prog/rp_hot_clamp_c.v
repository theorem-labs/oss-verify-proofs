(* Modified by Theorem Labs: copied from this unit's lib/A/Prog/rp_hot_clamp_c.v (commit ba35beec1417; itself in the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_c.v at recipes commit 88154566652a) for reac-repacer/fuzz_uci's rp_hot_clamp in image B: Img0 / AsanCells / AsanKA are lib/B's, the entry and every address in the comments are fuzz_uci.asan-ubsan's, and TWO premises more than image A's text, image B's UBSan premises `bv_unsigned a0 <> 0` and `bv_unsigned a0 mod 4 = 0` (the traps 0x7fd40 `beq a0, zero` and 0x7fd44 / 0x7fd48 `andi a2, a0, 3` / `bne a2, zero`, unimp at 0x7feb4), in the shape of the UBSan image's lib/U/Prog/rp_hot_clamp_c.v (its traps 0x1317c / 0x13184). *)
(* rp_hot_clamp_c: rp_hot_clamp of fuzz_uci.asan-ubsan (0x7fd38 = uci_sigma US_rp_hot_clamp, lib/B/Prog/UciPAddr.v), a
   leaf. The code (DIS of image B): `addi sp, sp, -0x10`, `sd ra, 8(sp)` ... `ld ra, 8(sp)` (frame [sp - 16, sp)); its
   UBSan checks of p (+0x8 `beq a0, zero`, +0xc / +0x10 `andi a2, a0, 3` / `bne a2, zero`) branch to `unimp` at +0x17c
   (0x7feb4); it loads the shadow base through its GOT word (`auipc a2`; `ld a2, 0x3dc(a2)` = 0x97128, then
   `ld a4, 0(a2)` = the cell 0x9f0f8), and before each 4-byte load or store of a field of *p it loads the shadow byte
   of that field's address,
   (a >> 3) + base, branching to __asan_report_load4 / __asan_report_store4 when it is not addressable. It calls nothing
   else. The struct is rp_hot of lib/Spec/UciModel.v: five ints, 20 bytes (lib/Prog/rp_hot_clamp_c.v hot_cells). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_hot_clamp_c.
Import ListNotations.
Open Scope Z_scope.
Module PHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_hot_clamp_c.

Definition RP_HOT_CLAMP : Z := 0x7fd38.
Definition RP_HOT_CLAMP_FRAME : Z := 16.

Definition rp_hot_clamp_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : rp_hot) (mm lo : Z),
    (* Image B's UBSan premises: 0x7fd40 `beq a0, zero, 0x7feb4` traps (unimp at 0x7feb4) on p == NULL, and 0x7fd44
       `andi a2, a0, 3` / 0x7fd48 `bne a2, zero, 0x7feb4` trap on a misaligned p. *)
    bv_unsigned a0 <> 0 ->
    bv_unsigned a0 mod 4 = 0 ->
    PHC.hot_int p ->
    0 <= mm <= INT_MAX ->
    bv_unsigned a1 = mm ->
    rw_cells rsegs m (bv_unsigned a0) (PHC.hot_cells p) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_HOT_CLAMP_FRAME <= bv_unsigned sp ->
    off_stk sp RP_HOT_CLAMP_FRAME (bv_unsigned a0) PHC.RP_HOT_SIZE ->
    app_mem (bv_unsigned sp - RP_HOT_CLAMP_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp RP_HOT_CLAMP_FRAME GOT_CELL_K 8 ->
    off_stk sp RP_HOT_CLAMP_FRAME CELL_K 8 ->
    addressable m (bv_unsigned a0) PHC.RP_HOT_SIZE ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_HOT_CLAMP_FRAME, bv_unsigned sp);
                (bv_unsigned a0, bv_unsigned a0 + PHC.RP_HOT_SIZE)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (bv_unsigned a0) (PHC.hot_cells (rp_hot_clamp_m p mm)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_HOT_CLAMP) fc None m (seg_rom rsegs)).
