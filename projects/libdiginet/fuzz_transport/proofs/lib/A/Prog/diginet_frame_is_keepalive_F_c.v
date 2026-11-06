(* Modified by Theorem Labs, 2026-10: the footprint form of proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F_c.v (and check_braid_F_c.v), restated for diginet_frame_is_keepalive of libdiginet/fuzz_frame's image A; module paths changed; no shadow_rw premise. *)
(* Footprint form of diginet_frame_is_keepalive_contract (image A, entry 0x8b63c, frame 16), RELOCATED from
   libdiginet/fuzz_frame lib/A/Prog/diginet_frame_is_keepalive_F_c.v (file sha256 c679057b5958; donor not released)
   with the numbers of diginet_frame_is_keepalive_c.v changed: the same premises, then one ExecF.rng premise per
   memory range the code reads or writes, each under the condition under which the code touches it, and the run as an
   ExecF.evtF run under the footprint RNG: every data access of every step lies in RNG. The code
     - stores ra at sp - 8 (0x8b640) and loads it back (0x8b6c8): the frame [sp - 16, sp);
     - loads the 8 bytes at GOT_CELL_K (0x8b64c) and the 8 bytes at CELL_K (0x8b650);
     - loads the shadow byte of f + 30 at ((f + 30) >> 3) + 0x7fff8000 (0x8b660) and the byte at f + 30 (0x8b668);
     - only when cmd = 0: the shadow byte of f + 40 (0x8b67c) and the 8 bytes at f + 40 (0x8b684);
     - only when cmd = 0 and blen = 1: the shadow byte of f + 32 (0x8b69c), the 8 bytes at f + 32 (0x8b6a4), the
       shadow byte of body (0x8b6b0) and the byte at body (0x8b6b8).
   Each 8-byte load is checked by the one shadow byte of its first address, so every shadow range is one byte. The
   error path calls (__asan_report_load1 at 0x8b6e0 and 0x8b6ec, __asan_report_load8 at 0x8b6f4 and 0x8b6f8) are not
   reached under the addressable premises, and the compares at 0x8b6d4-0x8b6d8 and 0x8b6e4-0x8b6e8 touch only
   registers, so they add no range.
   Form: fuzz_frame's diginet_frame_is_keepalive_F_c.v (conditional ranges, arguments as Z values). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA diginet_frame_is_keepalive_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_frame_is_keepalive_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f cmd body lo : Z) (bb : list byte),
    0 < f < 2^64 ->
    0 <= cmd < 2^8 -> 0 <= body < 2^64 ->
    bytes_at rsegs m (f + 30) [b8 cmd] ->
    bytes_at rsegs m (f + 32) (le8 (Z_to_bv 64 body) ++ le8 (Z_to_bv 64 (Z.of_nat (length bb)))) ->
    bytes_at rsegs m body bb ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + DIGINET_FRAME_IS_KEEPALIVE_FRAME <= bv_unsigned sp ->
    asan_cells m ->
    app_mem (bv_unsigned sp - DIGINET_FRAME_IS_KEEPALIVE_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME GOT_CELL_K 8 ->
    off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME CELL_K 8 ->
    off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME (f + 30) 1 ->
    addressable m (f + 30) 1 ->
    (cmd = 0 ->
       off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME (f + 40) 8 /\ addressable m (f + 40) 8) ->
    (cmd = 0 -> Z.of_nat (length bb) = 1 ->
       off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME (f + 32) 8 /\ addressable m (f + 32) 8 /\
       off_stk sp DIGINET_FRAME_IS_KEEPALIVE_FRAME body 1 /\ addressable m body 1) ->
    ExecF.rng RNG (bv_unsigned sp - DIGINET_FRAME_IS_KEEPALIVE_FRAME) DIGINET_FRAME_IS_KEEPALIVE_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (f + 30) 1 ->
    ExecF.rng RNG (shadow_addr (f + 30)) 1 ->
    (cmd = 0 -> ExecF.rng RNG (f + 40) 8) ->
    (cmd = 0 -> ExecF.rng RNG (shadow_addr (f + 40)) 1) ->
    (cmd = 0 -> Z.of_nat (length bb) = 1 -> ExecF.rng RNG (f + 32) 8) ->
    (cmd = 0 -> Z.of_nat (length bb) = 1 -> ExecF.rng RNG (shadow_addr (f + 32)) 1) ->
    (cmd = 0 -> Z.of_nat (length bb) = 1 -> ExecF.rng RNG body 1) ->
    (cmd = 0 -> Z.of_nat (length bb) = 1 -> ExecF.rng RNG (shadow_addr body) 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (if keepalive_of cmd (Z.of_nat (length bb)) bb then 1 else 0)) a1' a2' a3' a4'
                       a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_FRAME_IS_KEEPALIVE_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_FRAME_IS_KEEPALIVE) fc None m (seg_rom rsegs)).
