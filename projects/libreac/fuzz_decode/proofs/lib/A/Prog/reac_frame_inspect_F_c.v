From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA reac_frame_inspect_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
Open Scope Z_scope.

(* Footprint form of reac_frame_inspect_contract (A image, entry 0x812dc). The run is an ExecF.evtF run under a
   footprint RNG: every data access of every step lies in RNG. The code
     - stores ra at sp - 8 and loads it back (stack frame [sp - 16, sp));
     - only when a1 = 1492: loads 8 bytes at GOT_CELL_K and 8 bytes at CELL_K, loads the bytes at a0 + 12, 13,
       1490, 1491, 14 and 15 of the buffer [a0, a0 + 1492), and before each of these loads it loads the shadow
       byte of that address, at (a >> 3) + ASAN_K.
   So RNG holds the stack frame, and, under the condition of the old buffer premise (a1 = 1492), the two cells,
   the buffer and its shadow bytes [shadow_addr a0, shadow_addr (a0 + 1491)]. *)

Definition reac_frame_inspect_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_FRAME_INSPECT_FRAME <= bv_unsigned sp ->
    (bv_unsigned a1 = 1492 ->
       length bs = 1492%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       off_stk sp REAC_FRAME_INSPECT_FRAME (bv_unsigned a0) 1492 /\
       app_mem (bv_unsigned sp - REAC_FRAME_INSPECT_FRAME) /\ app_mem (bv_unsigned sp - 1) /\
       asan_cells m /\ shadow_rw m /\
       off_stk sp REAC_FRAME_INSPECT_FRAME GOT_CELL_K 8 /\
       off_stk sp REAC_FRAME_INSPECT_FRAME CELL_K 8 /\
       addressable m (bv_unsigned a0) 1492) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_FRAME_INSPECT_FRAME) REAC_FRAME_INSPECT_FRAME ->
    (bv_unsigned a1 = 1492 -> ExecF.rng RNG GOT_CELL_K 8) ->
    (bv_unsigned a1 = 1492 -> ExecF.rng RNG CELL_K 8) ->
    (bv_unsigned a1 = 1492 -> ExecF.rng RNG (bv_unsigned a0) 1492) ->
    (bv_unsigned a1 = 1492 ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a0))
         (shadow_addr (bv_unsigned a0 + 1492 - 1) - shadow_addr (bv_unsigned a0) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (inspect_result (bv_unsigned a1) bs)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_FRAME_INSPECT_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_FRAME_INSPECT) fc None m (seg_rom rsegs)).
