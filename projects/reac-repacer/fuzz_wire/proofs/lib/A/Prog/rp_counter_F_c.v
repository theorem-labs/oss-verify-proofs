(* The footprint form of lib/A/Prog/rp_counter_c.v rp_counter_contract, in the form of reac-repacer/fuzz_uci's lib/A/Prog/rp_hot_clamp_F_c.v (the footprint contract of a leaf, without a shadow_rw premise) with the footprint of libreac/fuzz_decode's released lib/A/Prog/reac_frame_counter_F_c.v, so that its cgif-form translation (lib/A/Prog/rp_counter_cg.v) takes no premise a caller cannot discharge. *)
(* Footprint form of rp_counter_contract (A image, entry 0x812f4). The run is an ExecF.evtF run under a footprint RNG:
   every data access of every step lies in RNG. The code (DIS of image A)
     - stores ra at sp - 8 and loads it back (stack frame [sp - 16, sp));
     - loads 8 bytes at GOT_CELL_K (0x987e8) and 8 bytes at CELL_K (0xa0778), the shadow base;
     - loads the bytes at a0 + 14 and a0 + 15 (the buffer [a0 + 14, a0 + 16)), and before each of these loads it
       loads the shadow byte of that address, (a >> 3) + ASAN_K.
   So RNG holds the stack frame, the two cells, the buffer and its shadow bytes
   [shadow_addr (a0 + 14), shadow_addr (a0 + 15)]. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA rp_counter_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_counter_c.

Definition rp_counter_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (16 <= length bs)%nat ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_COUNTER_FRAME <= bv_unsigned sp ->
    off_stk sp RP_COUNTER_FRAME (bv_unsigned a0) 16 ->
    app_mem (bv_unsigned sp - RP_COUNTER_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp RP_COUNTER_FRAME GOT_CELL_K 8 ->
    off_stk sp RP_COUNTER_FRAME CELL_K 8 ->
    addressable m (bv_unsigned a0 + 14) 2 ->
    ExecF.rng RNG (bv_unsigned sp - RP_COUNTER_FRAME) RP_COUNTER_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (bv_unsigned a0 + 14) 2 ->
    ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 14))
      (shadow_addr (bv_unsigned a0 + 14 + 2 - 1) - shadow_addr (bv_unsigned a0 + 14) + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (PRC.counter_result bs)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_COUNTER_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_COUNTER) fc None m (seg_rom rsegs)).

(* The statement a footprint walk of image A's rp_counter proves (the closing file's row H_PROG_RCNT_F). *)
Definition wire_rp_counter_holds_stmt : Prop := rp_counter_contract_F.
