From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA reac_frame_inspect_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
Open Scope Z_scope.

(* Footprint twin of reac_frame_inspect_contract (B image, entry 0x815fc, frame 16 bytes): the same premises and
   postcondition, the run is an ExecF.evtF run under the footprint RNG, and RNG holds each range the run reads or
   writes:
     - [sp-16, sp): sd ra,8(sp) at 0x81600 and ld ra,8(sp) at 0x8171c (on every path);
   and, only when a1 = 1492 (the other path returns at 0x81608 before any other access):
     - [GOT_CELL_K, +8): ld a1,-0x330(a1) at 0x8161c;
     - [CELL_K, +8): ld a2,0(a1) at 0x81620;
     - [a0+12, a0+16): lbu of a0+12, a0+13, a0+14, a0+15 (0x81638, 0x81660, 0x816f0, 0x816f8);
     - [a0+1490, a0+1492): lbu of a0+1490, a0+1491 (0x81688, 0x816b0);
     - the shadow bytes of [a0+12, a0+16): lb of (a0+i)/8 + ASAN_K, i = 12, 13, 14, 15 (0x81630, 0x81658, 0x816d8,
       0x816ec);
     - the shadow bytes of [a0+1490, a0+1492): lb of (a0+i)/8 + ASAN_K, i = 1490, 1491 (0x81680, 0x816a8). *)
Definition reac_frame_inspect_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REAC_FRAME_INSPECT_FRAME <= bv_unsigned sp ->
    (bv_unsigned a1 = 1492 ->
       length bs = 1492%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\ bv_unsigned a0 <> 0 /\
       off_stk sp REAC_FRAME_INSPECT_FRAME (bv_unsigned a0) 1492 /\
       app_mem (bv_unsigned sp - REAC_FRAME_INSPECT_FRAME) /\ app_mem (bv_unsigned sp - 1) /\
       asan_cells m /\ shadow_rw m /\
       off_stk sp REAC_FRAME_INSPECT_FRAME GOT_CELL_K 8 /\
       off_stk sp REAC_FRAME_INSPECT_FRAME CELL_K 8 /\
       addressable m (bv_unsigned a0) 1492) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_FRAME_INSPECT_FRAME) REAC_FRAME_INSPECT_FRAME ->
    (bv_unsigned a1 = 1492 ->
       ExecF.rng RNG GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8 /\
       ExecF.rng RNG (bv_unsigned a0 + 12) 4 /\ ExecF.rng RNG (bv_unsigned a0 + 1490) 2 /\
       ExecF.rng RNG ((bv_unsigned a0 + 12) / 8 + ASAN_K)
         ((bv_unsigned a0 + 15) / 8 - (bv_unsigned a0 + 12) / 8 + 1) /\
       ExecF.rng RNG ((bv_unsigned a0 + 1490) / 8 + ASAN_K)
         ((bv_unsigned a0 + 1491) / 8 - (bv_unsigned a0 + 1490) / 8 + 1)) ->
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
