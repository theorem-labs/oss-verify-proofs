(* diginet_session_close (transport/src/diginet_session.c:147-158) at 0x16558, 212 bytes. The binary inlines
   set_state; it calls send_control (:154), memset (the notice) and, through g_s.notify, notice. FRAME 768 = its
   own 112 (addi sp,sp,-112 at 0x16558) + 656, the deepest callee window (send_control; memset 0, notice 272).
   Every callee window counted is that callee's full transitive stack depth, abort() paths included, so it bounds
   the window any callee contract asks for. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_session_close_ENTRY : Z := 0x16558.
Definition diginet_session_close_FRAME : Z := 768.

(* a0 = s = &g_s, a1 = now_us (uint64_t, unused). Result: the int diginet_session_close_m gives. *)
Definition diginet_session_close_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (now r : Z) (B B' : list byte) (TF : option tframe),
    a0 = Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s) ->
    a1 = Z_to_bv 64 now ->
    0 <= now < 2^64 ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    diginet_session_close_m timg_plain TF B now = Some (B', r) ->
    tframe_at m sp diginet_session_close_FRAME TF ->
    relro_img m ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + diginet_session_close_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_PLAIN sp diginet_session_close_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - diginet_session_close_FRAME, bv_unsigned sp);
                (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 diginet_session_close_ENTRY) fc None m (seg_rom rsegs)).
