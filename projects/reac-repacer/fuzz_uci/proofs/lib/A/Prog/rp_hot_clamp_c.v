(* Modified by Theorem Labs: the evt contract of reac-repacer/fuzz_uci's rp_hot_clamp in image A, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_c.v (origin/ossv/recipes 88154566652a: entry, frame, the ASan runtime cells and addressability premises) over the plain contract's cells and model (lib/Prog/rp_hot_clamp_c.v hot_cells / hot_int, lib/Spec/UciModel.v rp_hot_clamp_m). *)
(* rp_hot_clamp_c: rp_hot_clamp of fuzz_uci.asan (0x7fc64 = uci_sigma US_rp_hot_clamp, lib/A/Prog/UciPAddr.v), a leaf.
   The code (DIS of image A): `addi sp, sp, -0x10`, `sd ra, 8(sp)` ... `ld ra, 8(sp)` (frame [sp - 16, sp)); it loads the
   shadow base through its GOT word (`auipc a2`; `ld a2, 0x3b4(a2)` = 0x97020, then `ld a4, 0(a2)` = the cell
   0x9eff8), and before each 4-byte load or store of a field of *p it loads the shadow byte of that field's address,
   (a >> 3) + base, branching to __asan_report_load4 / __asan_report_store4 when it is not addressable. It calls nothing
   else. The struct is rp_hot of lib/Spec/UciModel.v: five ints, 20 bytes (lib/Prog/rp_hot_clamp_c.v hot_cells). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_hot_clamp_c.
Import ListNotations.
Open Scope Z_scope.
Module PHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_hot_clamp_c.

Definition RP_HOT_CLAMP : Z := 0x7fc64.
Definition RP_HOT_CLAMP_FRAME : Z := 16.

Definition rp_hot_clamp_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : rp_hot) (mm lo : Z),
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
