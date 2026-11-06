From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA reac_frame_inspect_c reac_decode_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_frame_inspect_F_c.
Import ListNotations.
Open Scope Z_scope.

(* Footprint twin of reac_decode_contract (B image, entry 0x81788, frame 112 bytes): the same premises and
   postcondition, the run is an ExecF.evtF run under the footprint RNG, and RNG holds each range the run reads or
   writes:
     - [sp-112, sp): the 96-byte frame of reac_decode (saves of ra, s0..s7 and their reloads at the exit) and the
       16-byte frame of the callee reac_frame_inspect below it;
     - [GOT_CELL_K, +8) and [CELL_K, +8): the loads of the GOT cell and of the shadow offset before the call (on
       every path), and the same two loads in reac_frame_inspect when a1 = 1492;
   only when a1 = 1492 (else reac_frame_inspect returns 0 at once and reac_decode returns -1):
     - [raw, raw+1492) and its shadow bytes: the loads of reac_frame_inspect (raw+12..raw+15, raw+1490, raw+1491)
       and the source loads of the braid loop (raw+50 ..), each after a load of its shadow byte;
   only when inspect_wf holds (the loads of nch and ns are on that path only):
     - [mode+4, mode+12) and its shadow bytes: lw of mode+4 and mode+8, each after a load of its shadow byte;
   only when decode_ok holds (the braid loop runs on that path only):
     - [out, out+3*nch*ns) and its shadow bytes: the byte stores of the braid loop, each after a load of its
       shadow byte. *)
Definition reac_decode_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte)
         (raw mode out nch ns lo : Z),
    a0 = Z_to_bv 64 raw -> a2 = Z_to_bv 64 mode -> a3 = Z_to_bv 64 out ->
    0 <= raw < 2^64 -> 0 <= mode < 2^64 -> 0 <= out < 2^64 ->
    (bv_unsigned a1 = 1492 -> length bs = 1492%nat /\ bytes_at rsegs m raw bs) ->
    -2^31 <= nch < 2^31 -> -2^31 <= ns < 2^31 ->
    bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_DECODE_D <= bv_unsigned sp ->
    (bv_unsigned a1 = 1492 -> off_stk sp REAC_DECODE_D raw 1492) ->
    off_stk sp REAC_DECODE_D (mode + 4) 8 ->
    (decode_ok (bv_unsigned a1) bs nch ns = true ->
       wr_at rsegs m out (3 * nch * ns) /\ out + 3 * nch * ns < 2^64 /\
       (out + 3 * nch * ns <= raw \/ raw + 1492 <= out) /\
       off_stk sp REAC_DECODE_D out (3 * nch * ns)) ->
    app_mem (bv_unsigned sp - REAC_DECODE_D) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m -> shadow_rw m ->
    off_stk sp REAC_DECODE_D GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    (bv_unsigned a1 = 1492 -> addressable m raw 1492) ->
    (inspect_wf (bv_unsigned a1) bs = true -> addressable m (mode + 4) 8) ->
    (decode_ok (bv_unsigned a1) bs nch ns = true -> addressable m out (3 * nch * ns)) ->
    (bv_unsigned a1 = 1492 -> raw <> 0) ->
    (inspect_wf (bv_unsigned a1) bs = true -> mode <> 0 /\ mode mod 4 = 0) ->
    (decode_ok (bv_unsigned a1) bs nch ns = true -> out <> 0) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_DECODE_D) REAC_DECODE_D ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (bv_unsigned a1 = 1492 ->
       ExecF.rng RNG raw 1492 /\ ExecF.rng RNG (raw / 8 + ASAN_K) ((raw + 1491) / 8 - raw / 8 + 1)) ->
    (inspect_wf (bv_unsigned a1) bs = true ->
       ExecF.rng RNG (mode + 4) 8 /\
       ExecF.rng RNG ((mode + 4) / 8 + ASAN_K) ((mode + 11) / 8 - (mode + 4) / 8 + 1)) ->
    (decode_ok (bv_unsigned a1) bs nch ns = true ->
       ExecF.rng RNG out (3 * nch * ns) /\
       ExecF.rng RNG (out / 8 + ASAN_K) ((out + 3 * nch * ns - 1) / 8 - out / 8 + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if decode_ok (bv_unsigned a1) bs nch ns then ns else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (if decode_ok (bv_unsigned a1) bs nch ns
          then munch [(bv_unsigned sp - REAC_DECODE_D, bv_unsigned sp); (out, out + 3 * nch * ns)] m m' /\
               bytes_at rsegs m' out (braid_out bs nch ns)
          else munch [(bv_unsigned sp - REAC_DECODE_D, bv_unsigned sp)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_DECODE) fc None m (seg_rom rsegs)).
