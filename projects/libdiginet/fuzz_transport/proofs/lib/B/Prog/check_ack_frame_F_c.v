(* Footprint form of check_ack_frame_contract (check_ack_frame_c.v; image B, entry 0x843d4): the same premises, then
   one rng premise per memory range the code reads or writes, and the run as an ExecF.evtF run under the footprint
   RNG (every data access of every step lies in RNG). The code touches every range below on its one return path, so
   no rng premise has a condition; in the order the code touches them:
     - the frame [sp - 16, sp): the 8-byte store of ra at sp - 8 (0x843d8) and its load (0x8444c);
     - GOT_CELL_K 0xa3cf0: one 8-byte load (0x843e8); CELL_K 0xac678: one 8-byte load (0x843ec);
     - the shadow byte of fp + 36, shadow_addr (fp + 36) = ((fp + 36) >> 3) + 0x7fff8000 (0x843fc), and
       [fp + 36, + 4): the 4-byte load of f->ack (0x84404);
     - [CHECK_ACK_FRAME_RX_SEND, + 4) = [0x5e5060, 0x5e5064): the 4-byte load of g_rx_send (0x8440c);
     - the shadow byte of fp + 56 (0x84420) and [fp + 56, + 8): the 8-byte load of f->body_len (0x84428);
     - the shadow byte of fp + 30 (0x8443c) and [fp + 30, + 2): the 2-byte load of f->retry (0x84444).
   Each check loads the one shadow byte of the first address of its access, so every shadow range is one byte. The
   test of fp & 7 (0x843dc-0x843e0) touches only registers. The error-path calls (0x84474, 0x84484, 0x8448c) are
   not reached under the addressable premises, and the compares at 0x84464-0x8446c and 0x84478-0x84480 touch only
   registers, so they add no range. The trap path (0x84458 - 0x84460) makes no data access of this function's own.
   There is no shadow_rw premise: the shadow bytes the checks load are given by the addressable premises.
   Form: lib/A/Prog/check_ack_frame_F_c.v (image A's footprint form: the rng premises after the contract's
   premises, the same post). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_ack_frame_c.
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
    tw_at TMAP_B (csw_view m) Bw ->
    TC.check_ack_frame_m Bw frame = Some (Bw', tt) ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_ACK_FRAME_FRAME <= bv_unsigned sp ->
    off_stk sp CHECK_ACK_FRAME_FRAME TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
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
         tw_at TMAP_B (csw_view m') Bw)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fp) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ACK_FRAME) fc None m (seg_rom rsegs)).
