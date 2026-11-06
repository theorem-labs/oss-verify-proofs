(* The machine contract of io_send (fuzz/fuzz_transport.c:823-899) in the ubsan image. *)
(* g_fail_next is one byte (TWorld.v:475-478) and the binary tests only its bit 0 (plain 0x1482c-0x14834, 0x148ec;
   ubsan 0x14948, 0x14ad8-0x14ae0), while io_send_m tests it against 0: hence the premise g_fail_next B <= 1, which
   every reachable world meets (the harness stores 0 and 1 only, fuzz_transport.c:829, :1152, :1207). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract.
Import ListNotations.
Open Scope Z_scope.

Definition io_send_ENTRY : Z := 0x1482c.
(* addi sp,sp,-160 at 0x1482c (ra, s0-s6 saved, struct spec_frame f at sp + 16); callees (all jal): memcpy (kit, 0),
   spec_read_frame (32), tagged_of (0), check_sent_frame (32), check_ack_frame, check_latest_control,
   check_state_wake, check_inflight_new, check_latest_frame, check_keepalive_due, check_latest_display (16 each),
   check_inflight_retry (48), check_latest_sent (128), U/Prog/T/<g>_c.v: 160 + 128. *)
Definition io_send_FRAME : Z := 288.

(* Where the frame lies: send_control's stack buffer (diginet_session.c:99), off the world, or g_s.inflight_frame
   (diginet_session.c:400, :411), inside g_s; io_send writes M, GOT, g_fail_next, g_last_counter (and its checks
   g_cmd / g_q), none of them in g_s. *)
Definition io_send_frame_at (p n : Z) : Prop :=
  off_world p n \/ (W_BASE_UBSAN + OFF_g_s <= p /\ p + n <= W_BASE_UBSAN + OFF_g_s + SZ_g_s).

Definition io_send_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte) (p r : Z) (frame : list byte),
    a1 = Z_to_bv 64 p ->
    a2 = Z_to_bv 64 (Z.of_nat (length frame)) ->
    0 < p ->
    bytes_at rsegs m p frame ->
    io_send_frame_at p (Z.of_nat (length frame)) ->
    p + Z.of_nat (length frame) < 2 ^ 64 ->   (* passed on to spec_read_frame's no-wrap premise *)
    off_window sp io_send_FRAME p (Z.of_nat (length frame)) ->
    g_fail_next B <= 1 ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + io_send_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp io_send_FRAME ->
    mem_inv rsegs m ->
    wmem rsegs m B ->
    io_send_m timg_ubsan B frame = Some (B', r) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - io_send_FRAME, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ wmem rsegs m' B')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 io_send_ENTRY) fc None m (seg_rom rsegs)).
