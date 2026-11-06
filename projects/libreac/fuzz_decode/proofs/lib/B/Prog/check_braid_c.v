From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_BRAID : Z := 0x81070.
Definition CHECK_BRAID_FRAME : Z := 128.

Definition braid_off (ch j : Z) : Z :=
  if Z.even ch
  then (if j =? 0 then 3 else if j =? 1 then 0 else 1)
  else (if j =? 0 then 4 else if j =? 1 then 5 else 2).

Definition braid_map (m : word -> option byte) (audio pcm nch ns : Z) : Prop :=
  forall ch s j, 0 <= ch < nch -> 0 <= s < ns -> 0 <= j < 3 ->
    exists b : byte,
      mrd rsegs m (wa (pcm + 3 * (ch * ns + s) + j)) = Some b /\
      mrd rsegs m (wa (audio + 3 * (s * nch + 2 * (ch / 2)) + braid_off ch j)) = Some b.

Definition check_braid_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (audio pcm nch ns lo : Z),
    1 <= nch <= 127 ->
    1 <= ns <= 127 ->
    0 < audio < 2^63 ->
    0 <= pcm < 2^63 ->
    braid_map m audio pcm nch ns ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_BRAID_FRAME <= bv_unsigned sp ->
    audio + 3 * nch * ns + 3 * (nch mod 2) <= bv_unsigned sp - CHECK_BRAID_FRAME \/ bv_unsigned sp <= audio ->
    pcm + 3 * nch * ns <= bv_unsigned sp - CHECK_BRAID_FRAME \/ bv_unsigned sp <= pcm ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_BRAID_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_BRAID_FRAME GOT_CELL_K (MIDEND + 8 - GOT_CELL_K) ->
    addressable m audio (3 * nch * ns + 3 * (nch mod 2)) ->
    addressable m pcm (3 * nch * ns) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_BRAID_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 audio) (Z_to_bv 64 pcm) (Z_to_bv 64 nch) (Z_to_bv 64 ns)
               a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_BRAID) fc None m (seg_rom rsegs)).
