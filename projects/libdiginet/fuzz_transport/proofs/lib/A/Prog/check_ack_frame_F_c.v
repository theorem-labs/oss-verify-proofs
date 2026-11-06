(* Footprint form of check_ack_frame_contract (check_ack_frame_c.v; image A, entry 0x8415c): the same premises, then
   one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under the footprint
   RNG (every data access of every step lies in RNG). The code touches every range below on its one return path, so
   no rng premise has a condition; in the order the code touches them:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x84160) and its load (0x841cc);
     - GOT_CELL_K 0xa4090: one 8-byte load (0x84168); CELL_K 0xac9f8: one 8-byte load (0x8416c);
     - the shadow byte of fp + 36, shadow_addr (fp + 36) = ((fp + 36) >> 3) + 0x7fff8000 (0x8417c), and
       [fp + 36, + 4): the 4-byte load of f->ack (0x84184);
     - [CHECK_ACK_FRAME_RX_SEND, + 4) = [0x5e53e0, 0x5e53e4): the 4-byte load of g_rx_send (0x8418c);
     - the shadow byte of fp + 56 (0x841a0) and [fp + 56, + 8): the 8-byte load of f->body_len (0x841a8);
     - the shadow byte of fp + 30 (0x841bc) and [fp + 30, + 2): the 2-byte load of f->retry (0x841c4).
   Each check loads the one shadow byte of the first address of its access, so every shadow range is one byte. The
   error-path calls (0x841f0, 0x84200, 0x84208) are not reached under the addressable premises, and the compares at
   0x841e0-0x841e8 and 0x841f4-0x841fc touch only registers, so they add no range. There is no shadow_rw premise:
   the shadow bytes the checks load are given by the addressable premises.
   Form: lib/A/Prog/check_state_wake_F_c.v with fuzz_frame's image-A diginet_frame_is_keepalive_F_c.v (one-byte
   shadow ranges, the cell ranges). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA TWorldG TWorldA check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_ack_frame_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
Import ListNotations.
Open Scope Z_scope.

Definition check_ack_frame_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fp lo : Z) (frame : list byte)
         (Bw Bw' : list byte),
    0 < fp ->
    fp mod 8 = 0 ->
    bytes_at rsegs m (fp + 36) (TW.put 4 (sf_ack (TC.rf frame))) ->
    bytes_at rsegs m (fp + 56) (TW.put 8 (sf_body_len (TC.rf frame))) ->
    bytes_at rsegs m (fp + 30) (TW.put 2 (sf_retry (TC.rf frame))) ->
    tw_at TMAP_A (csw_view m) Bw ->
    TC.check_ack_frame_m Bw frame = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_ACK_FRAME_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_ACK_FRAME_FRAME TG.G_HARNESS_LO (TG.G_HARNESS_HI - TG.G_HARNESS_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - CHECK_ACK_FRAME_FRAME) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp CHECK_ACK_FRAME_FRAME GOT_CELL_K 8 ->
    off_stk sp CHECK_ACK_FRAME_FRAME CELL_K 8 ->
    off_stk sp CHECK_ACK_FRAME_FRAME (fp + 36) 4 -> addressable m (fp + 36) 4 ->
    off_stk sp CHECK_ACK_FRAME_FRAME (fp + 56) 8 -> addressable m (fp + 56) 8 ->
    off_stk sp CHECK_ACK_FRAME_FRAME (fp + 30) 2 -> addressable m (fp + 30) 2 ->
    ExecF.rng RNG (bv_unsigned sp - CHECK_ACK_FRAME_FRAME) CHECK_ACK_FRAME_FRAME ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (shadow_addr (fp + 36)) 1 ->
    ExecF.rng RNG (fp + 36) 4 ->
    ExecF.rng RNG CHECK_ACK_FRAME_RX_SEND 4 ->
    ExecF.rng RNG (shadow_addr (fp + 56)) 1 ->
    ExecF.rng RNG (fp + 56) 8 ->
    ExecF.rng RNG (shadow_addr (fp + 30)) 1 ->
    ExecF.rng RNG (fp + 30) 2 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a3' a4' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_ACK_FRAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw' = Bw /\
         tw_at TMAP_A (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fp) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ACK_FRAME) fc None m (seg_rom rsegs)).
