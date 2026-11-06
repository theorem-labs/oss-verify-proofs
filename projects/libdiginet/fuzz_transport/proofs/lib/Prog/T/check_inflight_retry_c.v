(* check_inflight_retry (fuzz/fuzz_transport.c:450-474; model TCb.v check_inflight_retry_m), entry 0x15070, 50
   instructions. Compares the frame (but its two retry bytes 26, 27) with M.fly.frame (two bcmp calls), checks len =
   M.fly.len, f->retry = M.fly.retries + 1 <= g_cfg.max_retries and g_now - M.fly.sent >= ms(ack_timeout_ms).
   Arguments: a0 = frame (the len bytes at fa; may lie in the world: g_s.inflight_frame), a1 = len = length frame,
   a2 = f, the struct spec_frame of the parse rf frame of fa.
   FRAME 48: the prologue `addi sp,sp,-48`; the callee bcmp (two calls) uses no stack (Prog/bcmp_c.v: munch []).
   Callee contracts its walk uses: bcmp_contract (lib/Prog/bcmp_c.v).
   The world: not written (the model returns its B on Some); post B' = B and wmem rsegs m' B, no world interval in
   munch. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract.
Import ListNotations.
Open Scope Z_scope.

Definition check_inflight_retry_ENTRY : Z := 0x15070.
Definition check_inflight_retry_FRAME : Z := 48.

Definition check_inflight_retry_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte) (fa fp : Z) (frame : list byte),
    a0 = Z_to_bv 64 fa ->
    a1 = Z_to_bv 64 (Z.of_nat (length frame)) ->
    a2 = Z_to_bv 64 fp ->
    0 < fa ->
    fa + 28 < 2 ^ 64 ->      (* frame + RETRY_AT + 2 (:460) does not wrap: the ubsan pointer-overflow check *)
    bytes_at rsegs m fa frame ->
    off_window sp check_inflight_retry_FRAME fa (Z.of_nat (length frame)) ->
    sframe_at m fp fa (rf frame) ->
    off_window sp check_inflight_retry_FRAME fp 80 ->
    wmem rsegs m B ->
    check_inflight_retry_m B frame = Some (B', tt) ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + check_inflight_retry_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_PLAIN sp check_inflight_retry_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - check_inflight_retry_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         B' = B /\
         wmem rsegs m' B)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 check_inflight_retry_ENTRY) fc None m (seg_rom rsegs)).
