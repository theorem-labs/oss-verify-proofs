(* diginet_session_wake (transport/src/diginet_session.c:119-145) at 0x16358, 296 bytes. The binary inlines
   inflight_start and set_state; it calls send_control (:136), memcpy (:139), memset (the notice of set_state)
   and, through g_s.notify, notice. FRAME 848 = its own 192 (addi sp,sp,-192 at 0x16358) + 656, the deepest
   callee window (send_control; memcpy 0, memset 0, notice 272). Every callee window counted is that callee's
   full transitive stack depth, abort() paths included, so it bounds the window any callee contract asks for. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_session_wake_ENTRY : Z := 0x16358.
Definition diginet_session_wake_FRAME : Z := 848.

(* a0 = s = &g_s, a1 = now_us (uint64_t). Result: the int diginet_session_wake_m gives. *)
Definition diginet_session_wake_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (now r : Z) (B B' : list byte) (TF : option tframe),
    a0 = Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s) ->
    a1 = Z_to_bv 64 now ->
    0 <= now < 2^64 ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    diginet_session_wake_m timg_plain TF B now = Some (B', r) ->
    tframe_at m sp diginet_session_wake_FRAME TF ->
    relro_img m ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + diginet_session_wake_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_PLAIN sp diginet_session_wake_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - diginet_session_wake_FRAME, bv_unsigned sp);
                (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 diginet_session_wake_ENTRY) fc None m (seg_rom rsegs)).
