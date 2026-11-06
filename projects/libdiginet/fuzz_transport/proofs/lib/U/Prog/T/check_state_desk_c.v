(* check_state_desk (fuzz/fuzz_transport.c:527-557; model TCb.v check_state_desk_m), entry 0x15f68, 100
   instructions. Checks GOT.desk <= OW.desk, the MAC offset, that the notice's personality and OW.desk_p are both
   NULL or name the same device / strips (read from personalities[] and SPEC_C24 / SPEC_PC in .data.rel.ro), that
   the announce is there, and that its version / name equal the strz fields at OW.desk_body + 15 / + 24 in the
   current frame.
   Arguments: a0 = n, a struct diginet_notice (ntc_at); the current heap frame Fr (tframe_at); .data.rel.ro as in
   the image (relro_img).
   FRAME 48: the prologue `addi sp,sp,-48`; the callee bcmp (two calls) uses no stack; spec_strz_len is inlined.
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

Definition check_state_desk_ENTRY : Z := 0x15f68.
Definition check_state_desk_FRAME : Z := 48.

Definition check_state_desk_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte) (p : Z) (n : ntc) (Fr : option tframe),
    a0 = Z_to_bv 64 p ->
    ntc_at m p n sp check_state_desk_FRAME ->
    tframe_at m sp check_state_desk_FRAME Fr ->
    relro_img m ->
    wmem rsegs m B ->
    check_state_desk_m timg_ubsan Fr B n = Some (B', tt) ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + check_state_desk_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp check_state_desk_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - check_state_desk_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         B' = B /\
         wmem rsegs m' B)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 check_state_desk_ENTRY) fc None m (seg_rom rsegs)).
