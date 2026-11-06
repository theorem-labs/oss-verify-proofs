From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA reac_frame_inspect_c reac_frame_inspect_F_c reac_decode_plain_le_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

(* Footprint form of reac_decode_plain_le_contract (A image, entry 0x816b0, frame 64 bytes). The run is an
   ExecF.evtF run under a footprint RNG: every data access of every step lies in RNG. The code
     - saves ra and s0..s3 in its own frame [sp - 48, sp) and loads them back at the end; the callee
       reac_frame_inspect uses the 16 bytes under it, so the whole stack window is [sp - 64, sp);
     - loads 8 bytes at GOT_CELL_K and 8 bytes at CELL_K (asan_cells) before the call;
     - calls reac_frame_inspect(raw, a1), which, when a1 = 1492, reads six bytes of [raw, raw + 1492) and the
       shadow byte of each, and the two cells again;
     - when inspect_wf holds: loads the two 4-byte fields at mode + 4 and mode + 8 and, before each, the shadow
       byte of that address;
     - when plain_ok holds: reads one byte of [raw, raw + 1492) and writes one byte of [out, out + 3*nch*ns)
       per output byte, and before each of those loads the shadow byte of that address.
   So RNG holds: the stack window; the two cells; and, under exactly the condition under which the old contract
   states that buffer's facts, each buffer and the shadow bytes of that buffer. *)

Definition reac_decode_plain_le_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte)
         (raw mode out nch ns lo : Z),
    a0 = Z_to_bv 64 raw -> a2 = Z_to_bv 64 mode -> a3 = Z_to_bv 64 out ->
    0 <= raw < 2^64 -> 0 <= mode < 2^64 -> 0 <= out < 2^64 ->
    (bv_unsigned a1 = 1492 -> length bs = 1492%nat /\ bytes_at rsegs m raw bs) ->
    -2^31 <= nch < 2^31 -> -2^31 <= ns < 2^31 ->
    bytes_at rsegs m (mode + 4) (le4 (Z_to_bv 64 nch) ++ le4 (Z_to_bv 64 ns)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_DECODE_PLAIN_LE_D <= bv_unsigned sp ->
    (bv_unsigned a1 = 1492 -> off_stk sp REAC_DECODE_PLAIN_LE_D raw 1492) ->
    off_stk sp REAC_DECODE_PLAIN_LE_D (mode + 4) 8 ->
    (plain_ok (bv_unsigned a1) bs nch ns = true ->
       wr_at rsegs m out (3 * nch * ns) /\ out + 3 * nch * ns < 2^64 /\
       (out + 3 * nch * ns <= raw \/ raw + 1492 <= out) /\
       off_stk sp REAC_DECODE_PLAIN_LE_D out (3 * nch * ns)) ->
    app_mem (bv_unsigned sp - REAC_DECODE_PLAIN_LE_D) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m -> shadow_rw m ->
    off_stk sp REAC_DECODE_PLAIN_LE_D GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    (bv_unsigned a1 = 1492 -> addressable m raw 1492) ->
    (inspect_wf (bv_unsigned a1) bs = true -> addressable m (mode + 4) 8) ->
    (plain_ok (bv_unsigned a1) bs nch ns = true -> addressable m out (3 * nch * ns)) ->
    (* the stack window of this frame and of reac_frame_inspect's frame under it *)
    ExecF.rng RNG (bv_unsigned sp - REAC_DECODE_PLAIN_LE_D) REAC_DECODE_PLAIN_LE_D ->
    (* the two asan_cells cells, loaded before the call and by the callee *)
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (* the input buffer and its shadow bytes, read by the callee and by the copy loop *)
    (bv_unsigned a1 = 1492 -> ExecF.rng RNG raw 1492) ->
    (bv_unsigned a1 = 1492 ->
       ExecF.rng RNG (shadow_addr raw) (shadow_addr (raw + 1492 - 1) - shadow_addr raw + 1)) ->
    (* the two 4-byte fields at mode + 4 and their shadow bytes *)
    (inspect_wf (bv_unsigned a1) bs = true -> ExecF.rng RNG (mode + 4) 8) ->
    (inspect_wf (bv_unsigned a1) bs = true ->
       ExecF.rng RNG (shadow_addr (mode + 4)) (shadow_addr (mode + 4 + 8 - 1) - shadow_addr (mode + 4) + 1)) ->
    (* the output buffer and its shadow bytes *)
    (plain_ok (bv_unsigned a1) bs nch ns = true -> ExecF.rng RNG out (3 * nch * ns)) ->
    (plain_ok (bv_unsigned a1) bs nch ns = true ->
       ExecF.rng RNG (shadow_addr out) (shadow_addr (out + 3 * nch * ns - 1) - shadow_addr out + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if plain_ok (bv_unsigned a1) bs nch ns then ns else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (if plain_ok (bv_unsigned a1) bs nch ns
          then munch [(bv_unsigned sp - REAC_DECODE_PLAIN_LE_D, bv_unsigned sp); (out, out + 3 * nch * ns)] m m' /\
               bytes_at rsegs m' out (plain_out bs nch ns)
          else munch [(bv_unsigned sp - REAC_DECODE_PLAIN_LE_D, bv_unsigned sp)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_DECODE_PLAIN_LE) fc None m (seg_rom rsegs)).
