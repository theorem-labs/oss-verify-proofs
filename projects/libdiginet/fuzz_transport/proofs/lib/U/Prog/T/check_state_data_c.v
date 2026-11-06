(* check_state_data (fuzz/fuzz_transport.c:559-569; model TCb.v check_state_data_m), entry 0x160f8, 45 instructions.
   Checks GOT.ndata < OW.ndata, GOT.ndata < 2, and the notice's body_len / body bytes (bcmp against
   OW.dn[GOT.ndata].body in the current frame) / counter / retry against OW.dn[GOT.ndata].
   Arguments: a0 = n, a struct diginet_notice (ntc_at); the current heap frame Fr (tframe_at), into which
   OW.dn[].body points.
   FRAME 32: the prologue `addi sp,sp,-32`; the callee bcmp uses no stack.
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

Definition check_state_data_ENTRY : Z := 0x160f8.
Definition check_state_data_FRAME : Z := 32.

Definition check_state_data_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte) (p : Z) (n : ntc) (Fr : option tframe),
    a0 = Z_to_bv 64 p ->
    ntc_at m p n sp check_state_data_FRAME ->
    tframe_at m sp check_state_data_FRAME Fr ->
    wmem rsegs m B ->
    check_state_data_m Fr B n = Some (B', tt) ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + check_state_data_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp check_state_data_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - check_state_data_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         B' = B /\
         wmem rsegs m' B)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 check_state_data_ENTRY) fc None m (seg_rom rsegs)).
