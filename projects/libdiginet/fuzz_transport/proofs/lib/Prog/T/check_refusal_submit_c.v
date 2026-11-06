(* check_refusal_submit (fuzz/fuzz_transport.c:656-665; model TCb.v check_refusal_submit_m), entry 0x1614c, 30
   instructions. spec_system_at (inlined) over c->bytes for c->len: a command with the system family must be refused
   (rc = SPEC_E_REFUSED) and leave g_s.queued at queued_before; any other must not be refused.
   Arguments: a0 = c, the 32 bytes of a struct diginet_cmd (4-aligned), a1 = rc (int), a2 = queued_before (unsigned
   int, sign-extended).
   FRAME 16: the bytes the abort path's prologue allocates (`addi sp,sp,-16` before `jal abort`); the paths that
   return use no stack, and abort is unreachable under the model premise.
   Callee contracts its walk uses: none (abort, the only callee, is unreachable: every abort / trap branch is closed
   by exfalso from the model premise).
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

Definition check_refusal_submit_ENTRY : Z := 0x1614c.
Definition check_refusal_submit_FRAME : Z := 16.

Definition check_refusal_submit_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte) (cp : Z) (c : list byte) (rc before : Z),
    a0 = Z_to_bv 64 cp ->
    a1 = Z_to_bv 64 rc ->
    a2 = Z_to_bv 64 (bv_swrap 32 before) ->
    -2 ^ 31 <= rc < 2 ^ 31 ->
    0 <= before < 2 ^ 32 ->
    0 < cp ->
    cp mod 4 = 0 ->
    bytes_at rsegs m cp c ->
    length c = 32%nat ->
    off_window sp check_refusal_submit_FRAME cp 32 ->
    wmem rsegs m B ->
    check_refusal_submit_m B c rc before = Some (B', tt) ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + check_refusal_submit_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_PLAIN sp check_refusal_submit_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - check_refusal_submit_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         B' = B /\
         wmem rsegs m' B)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 check_refusal_submit_ENTRY) fc None m (seg_rom rsegs)).
