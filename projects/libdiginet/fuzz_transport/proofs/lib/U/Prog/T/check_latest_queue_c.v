(* check_latest_queue (fuzz/fuzz_transport.c:804-819; model TCb.v check_latest_queue_m), entry 0x16680, 69
   instructions. Checks g_s.queued = g_nq and that g_s.queue[i] holds the bytes of g_cmd[g_q[i]] for every i < g_nq
   (bcmp per element).
   Arguments: none.
   FRAME 80: the prologue `addi sp,sp,-80`; the callee bcmp uses no stack.
   Callee contracts its walk uses: bcmp_contract (lib/U/Prog/bcmp_c.v).
   The world: not written (the model returns its B on Some); post B' = B and wmem rsegs m' B, no world interval in
   munch. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract.
Import ListNotations.
Open Scope Z_scope.

Definition check_latest_queue_ENTRY : Z := 0x16680.
Definition check_latest_queue_FRAME : Z := 80.

Definition check_latest_queue_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte),
    wmem rsegs m B ->
    check_latest_queue_m B = Some (B', tt) ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + check_latest_queue_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp check_latest_queue_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - check_latest_queue_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         B' = B /\
         wmem rsegs m' B)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 check_latest_queue_ENTRY) fc None m (seg_rom rsegs)).
