(* The footprint form of lib/A/Prog/rp_ret_accept_c.v rp_ret_accept_contract, in the form of reac-repacer/fuzz_uci's lib/A/Prog/rp_hot_clamp_F_c.v (the footprint contract of a leaf, without a shadow_rw premise) with the conditional footprint of libreac/fuzz_decode's released lib/A/Prog/reac_frame_is_reac_F_c.v, so that its cgif-form translation (lib/A/Prog/rp_ret_accept_cg.v) takes no premise a caller cannot discharge. *)
(* Footprint form of rp_ret_accept_contract (A image, entry 0x80fe0). The run is an ExecF.evtF run under a footprint
   RNG: every data access of every step lies in RNG. The code (DIS of image A)
     - stores ra at sp - 8 and loads it back (stack frame [sp - 16, sp));
     - only when a1 >= 14: loads 8 bytes at GOT_CELL_K (0x987e8) and 8 bytes at CELL_K (0xa0778), the shadow base;
       loads the byte at a0 + 12 and, when it is 0x88, the byte at a0 + 13 (the buffer [a0 + 12, a0 + 14)), and
       before each of these loads it loads the shadow byte of that address, (a >> 3) + ASAN_K.
   So RNG holds the stack frame, and, when a1 >= 14, the two cells, the buffer and its shadow bytes
   [shadow_addr (a0 + 12), shadow_addr (a0 + 13)]. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA rp_ret_accept_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ret_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module PRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ret_accept_c.

Definition rp_ret_accept_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_RET_ACCEPT_FRAME <= bv_unsigned sp ->
    (14 <= bv_unsigned a1 ->
       (14 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp RP_RET_ACCEPT_FRAME (bv_unsigned a0) 14 /\
       app_mem (bv_unsigned sp - RP_RET_ACCEPT_FRAME) /\ app_mem (bv_unsigned sp - 1) /\
       asan_cells m /\
       off_stk sp RP_RET_ACCEPT_FRAME GOT_CELL_K 8 /\
       off_stk sp RP_RET_ACCEPT_FRAME CELL_K 8 /\
       addressable m (bv_unsigned a0 + 12) 2) ->
    ExecF.rng RNG (bv_unsigned sp - RP_RET_ACCEPT_FRAME) RP_RET_ACCEPT_FRAME ->
    (14 <= bv_unsigned a1 -> ExecF.rng RNG GOT_CELL_K 8) ->
    (14 <= bv_unsigned a1 -> ExecF.rng RNG CELL_K 8) ->
    (14 <= bv_unsigned a1 -> ExecF.rng RNG (bv_unsigned a0 + 12) 2) ->
    (14 <= bv_unsigned a1 ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
         (shadow_addr (bv_unsigned a0 + 12 + 2 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (PRA.ret_accept_result (bv_unsigned a1) bs)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_RET_ACCEPT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_RET_ACCEPT) fc None m (seg_rom rsegs)).

(* The statement a footprint walk of image A's rp_ret_accept proves (the closing file's row H_PROG_RRET_F). *)
Definition wire_rp_ret_accept_holds_stmt : Prop := rp_ret_accept_contract_F.
