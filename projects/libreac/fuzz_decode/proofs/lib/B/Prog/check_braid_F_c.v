From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import AsanKA check_braid_c.
Import ListNotations.
Open Scope Z_scope.

(* Footprint form of check_braid_contract (B image, entry 0x81070): the same premises, then one rng premise per
   memory range the code reads or writes, and the run as an ExecF.evtF run under RNG:
     - the frame [sp - CHECK_BRAID_FRAME, sp): the saved registers and three 8-byte locals are stored and loaded there;
     - the GOT cell GOT_CELL_K and the cell CELL_K (8 bytes each): the code loads the shadow offset through them;
     - the audio buffer [audio, audio + 3 * nch * ns + 3 * (nch mod 2)) and the pcm buffer [pcm, pcm + 3 * nch * ns):
       the code loads bytes of both;
     - the shadow bytes of the audio buffer and of the pcm buffer: each byte load is preceded by an instrumented
       check that loads the shadow byte at a / 8 + ASAN_K. *)
Definition check_braid_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
    ExecF.rng RNG (bv_unsigned sp - CHECK_BRAID_FRAME) CHECK_BRAID_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG audio (3 * nch * ns + 3 * (nch mod 2)) ->
    ExecF.rng RNG pcm (3 * nch * ns) ->
    ExecF.rng RNG (audio / 8 + ASAN_K) ((audio + (3 * nch * ns + 3 * (nch mod 2)) - 1) / 8 - audio / 8 + 1) ->
    ExecF.rng RNG (pcm / 8 + ASAN_K) ((pcm + 3 * nch * ns - 1) / 8 - pcm / 8 + 1) ->
    ExecF.evtF rsegs RNG
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
