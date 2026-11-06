(* diginet_session_poll (transport/src/diginet_session.c:505-527) at 0x17dc0, 336 bytes. The binary calls
   diginet_session_deadline (:511), diginet_session_rx (:521, :525), diginet_session_tick (:522) and, through
   g_s.io.now_us and g_s.io.recv, io_now (:510, :519, :525) and io_recv (:516, :524). FRAME 3824 = its own 1568
   (addi sp,sp,-1568 at 0x17dc0) + 2256, the deepest callee window (diginet_session_rx; diginet_session_deadline
   0, diginet_session_tick 2144, io_now 0, io_recv 16). Every callee window counted is that callee's full
   transitive stack depth, abort() paths included, so it bounds the window any callee contract asks for. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_session_poll_ENTRY : Z := 0x17dc0.
Definition diginet_session_poll_FRAME : Z := 3824.

(* a0 = s = &g_s, a1 = max_wait_ms (int). Result: the int diginet_session_poll_m gives. *)
Definition diginet_session_poll_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (w r : Z) (B B' : list byte) (TF : option tframe),
    a0 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) ->
    a1 = Z_to_bv 64 w ->
    - 2^31 <= w < 2^31 ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    diginet_session_poll_m timg_ubsan TF B w = Some (B', r) ->
    tframe_at m sp diginet_session_poll_FRAME TF ->
    tframe_ok TF ->
    relro_img m ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + diginet_session_poll_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp diginet_session_poll_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - diginet_session_poll_FRAME, bv_unsigned sp);
                (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 diginet_session_poll_ENTRY) fc None m (seg_rom rsegs)).
