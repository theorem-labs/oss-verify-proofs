(* Modified by Theorem Labs: the footprint form of lib/A/Prog/rp_hot_clamp_c.v rp_hot_clamp_contract, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F_c.v (origin/ossv/recipes 88154566652a) without its shadow_rw premise (as that unit's _F_nosh contracts state it), so that its cgif-form translation (lib/A/Prog/rp_hot_clamp_cg.v) takes no premise a caller cannot discharge. *)
(* Footprint form of rp_hot_clamp_contract (A image, entry 0x7fc64). The run is an ExecF.evtF run under a footprint
   RNG: every data access of every step lies in RNG. The code (DIS of image A)
     - stores ra at sp - 8 and loads it back (stack frame [sp - 16, sp));
     - loads 8 bytes at GOT_CELL_K (0x97020) and 8 bytes at CELL_K (0x9eff8), the shadow base;
     - loads and stores the five 4-byte fields of [p, p + 20) (p = a0), and before each of these accesses loads the
       shadow byte of the field's address, (a >> 3) + ASAN_K, all of which lie in [shadow_addr p, shadow_addr (p + 19)].
   So RNG holds the stack frame, the two cells, the struct and the shadow bytes of the struct. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import AsanKA rp_hot_clamp_c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_hot_clamp_c.
Import ListNotations.
Open Scope Z_scope.
Module PHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_hot_clamp_c.

Definition rp_hot_clamp_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
    ExecF.rng RNG (bv_unsigned sp - RP_HOT_CLAMP_FRAME) RP_HOT_CLAMP_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (bv_unsigned a0) PHC.RP_HOT_SIZE ->
    ExecF.rng RNG (shadow_addr (bv_unsigned a0))
      (shadow_addr (bv_unsigned a0 + PHC.RP_HOT_SIZE - 1) - shadow_addr (bv_unsigned a0) + 1) ->
    ExecF.evtF rsegs RNG
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
