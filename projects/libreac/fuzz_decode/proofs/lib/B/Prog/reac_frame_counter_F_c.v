From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA reac_frame_counter_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
Open Scope Z_scope.

(* Footprint twin of reac_frame_counter_contract (reac_frame_counter_c.v): the same premises and postcondition,
   with the run an ExecF.evtF run whose data accesses lie in RNG. RNG holds the ranges the run reads or writes:
     - [sp-16, sp): the stack frame the run stores to and loads from;
     - GOT_CELL_K 8 and CELL_K 8: the two 8-byte loads that fetch ASAN_K;
     - [a0+14, a0+16): the two byte loads at a0+14 and a0+15;
     - the shadow bytes of [a0+14, a0+16): the instrumented check of a0+14 loads (a0+14)/8 + ASAN_K and the
       check of a0+15 loads (a0+15)/8 + ASAN_K. *)
Definition reac_frame_counter_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    (16 <= length bs)%nat ->
    bv_unsigned a0 <> 0 ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_FRAME_COUNTER_FRAME <= bv_unsigned sp ->
    off_stk sp REAC_FRAME_COUNTER_FRAME (bv_unsigned a0) 16 ->
    app_mem (bv_unsigned sp - REAC_FRAME_COUNTER_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m -> shadow_rw m ->
    off_stk sp REAC_FRAME_COUNTER_FRAME GOT_CELL_K 8 ->
    off_stk sp REAC_FRAME_COUNTER_FRAME CELL_K 8 ->
    addressable m (bv_unsigned a0 + 14) 2 ->
    ExecF.rng RNG (bv_unsigned sp - REAC_FRAME_COUNTER_FRAME) REAC_FRAME_COUNTER_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (bv_unsigned a0 + 14) 2 ->
    ExecF.rng RNG ((bv_unsigned a0 + 14) / 8 + ASAN_K) ((bv_unsigned a0 + 15) / 8 - (bv_unsigned a0 + 14) / 8 + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (counter_result bs)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_FRAME_COUNTER_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_FRAME_COUNTER) fc None m (seg_rom rsegs)).
