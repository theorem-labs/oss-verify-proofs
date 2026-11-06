From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA reac_frame_inspect_c reac_decode_c reac_upstream_decode_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

(* Footprint twin of reac_upstream_decode_contract (B image, entry 0x82038, frame 96 bytes): the same run as an
   ExecF.evtF run, where each data access of each step lies in the footprint RNG. RNG holds:
   - the stack window [sp - 96, sp): the saved registers and the loop's scratch slots sp-88, sp-80, sp-72;
   - the 8-byte constant DIV36_MAGIC at DIV36_MAGIC_AT;
   - the GOT cell GOT_CELL_K and the cell CELL_K of asan_cells (8 bytes each): the code loads the shadow base;
   - when raw <> 0, out <> 0 and 0 <= up_nch len (the condition of the input facts): the input [raw, raw + len)
     and its shadow bytes, which the instrumented checks before each input load read;
   - when up_ok holds (the condition of the output facts): the output [out, out + 36 * up_nch len) and its shadow
     bytes, which the instrumented checks before each output store read. *)
Definition reac_upstream_decode_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw out lo : Z),
    a0 = Z_to_bv 64 raw -> a2 = Z_to_bv 64 out ->
    0 <= raw < 2^64 -> 0 <= out < 2^64 -> bv_unsigned a1 < 2^32 ->
    bytes_at rsegs m DIV36_MAGIC_AT (le8 (Z_to_bv 64 DIV36_MAGIC)) ->
    (raw <> 0 -> out <> 0 -> 0 <= up_nch (bv_unsigned a1) ->
       length bs = Z.to_nat (bv_unsigned a1) /\ bytes_at rsegs m raw bs) ->
    (up_ok raw out (bv_unsigned a1) bs = true ->
       wr_at rsegs m out (36 * up_nch (bv_unsigned a1)) /\ out + 36 * up_nch (bv_unsigned a1) < 2^64 /\
       (out + 36 * up_nch (bv_unsigned a1) <= raw \/ raw + bv_unsigned a1 <= out)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_UPSTREAM_DECODE_D <= bv_unsigned sp ->
    (raw <> 0 -> out <> 0 -> 0 <= up_nch (bv_unsigned a1) ->
       off_stk sp REAC_UPSTREAM_DECODE_D raw (bv_unsigned a1)) ->
    (up_ok raw out (bv_unsigned a1) bs = true ->
       off_stk sp REAC_UPSTREAM_DECODE_D out (36 * up_nch (bv_unsigned a1))) ->
    off_stk sp REAC_UPSTREAM_DECODE_D DIV36_MAGIC_AT 8 ->
    app_mem (bv_unsigned sp - REAC_UPSTREAM_DECODE_D) -> app_mem (bv_unsigned sp - 1) ->
    asan_cells m ->
    off_stk sp REAC_UPSTREAM_DECODE_D GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    (raw <> 0 -> out <> 0 -> 0 <= up_nch (bv_unsigned a1) -> addressable m raw (bv_unsigned a1)) ->
    (up_ok raw out (bv_unsigned a1) bs = true -> addressable m out (36 * up_nch (bv_unsigned a1))) ->
    ExecF.rng RNG (bv_unsigned sp - REAC_UPSTREAM_DECODE_D) REAC_UPSTREAM_DECODE_D ->
    ExecF.rng RNG DIV36_MAGIC_AT 8 ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (raw <> 0 -> out <> 0 -> 0 <= up_nch (bv_unsigned a1) -> ExecF.rng RNG raw (bv_unsigned a1)) ->
    (raw <> 0 -> out <> 0 -> 0 <= up_nch (bv_unsigned a1) ->
       ExecF.rng RNG (raw / 8 + ASAN_K) ((raw + bv_unsigned a1 - 1) / 8 - raw / 8 + 1)) ->
    (up_ok raw out (bv_unsigned a1) bs = true -> ExecF.rng RNG out (36 * up_nch (bv_unsigned a1))) ->
    (up_ok raw out (bv_unsigned a1) bs = true ->
       ExecF.rng RNG (out / 8 + ASAN_K) ((out + 36 * up_nch (bv_unsigned a1) - 1) / 8 - out / 8 + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if up_ok raw out (bv_unsigned a1) bs then 12 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (if up_ok raw out (bv_unsigned a1) bs
          then munch [(bv_unsigned sp - REAC_UPSTREAM_DECODE_D, bv_unsigned sp);
                      (out, out + 36 * up_nch (bv_unsigned a1))] m m' /\
               bytes_at rsegs m' out (braid_out bs (up_nch (bv_unsigned a1)) 12)
          else munch [(bv_unsigned sp - REAC_UPSTREAM_DECODE_D, bv_unsigned sp)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_UPSTREAM_DECODE) fc None m (seg_rom rsegs)).
