From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA reac_frame_inspect_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_DECODE_PLAIN_LE : Z := 0x81a8c.
Definition REAC_DECODE_PLAIN_LE_D : Z := 64.

Definition plain_ok (len : Z) (bs : list byte) (nch ns : Z) : bool :=
  inspect_wf len bs && (0 <? nch) && (0 <? ns) && (nch * ns <=? 480).

Definition plain_byte (bs : list byte) (nch ns i : Z) : byte :=
  nth (Z.to_nat (50 + 3 * ((i / 3) mod ns * nch + i / 3 / ns) + i mod 3)) bs (Z_to_bv 8 0).

Definition plain_out (bs : list byte) (nch ns : Z) : list byte :=
  map (plain_byte bs nch ns) (map Z.of_nat (seq 0 (Z.to_nat (3 * nch * ns)))).

Definition reac_decode_plain_le_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
    (bv_unsigned a1 = 1492 -> raw <> 0) ->
    (inspect_wf (bv_unsigned a1) bs = true -> mode <> 0 /\ mode mod 4 = 0) ->
    (plain_ok (bv_unsigned a1) bs nch ns = true -> out <> 0) ->
    evt rsegs
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
