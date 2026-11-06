(* The machine contract of desk_named (fuzz/fuzz_transport.c:265-273, spec_strz_len inlined) in the plain image. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract.
Import ListNotations.
Open Scope Z_scope.

Definition desk_named_ENTRY : Z := 0x15818.
(* addi sp,sp,-16 at 0x15818 (ra, s0 saved); the only callee is bcmp (jal 0x1f8dc), whose kit contract uses no
   stack: 16 + 0. *)
Definition desk_named_FRAME : Z := 16.

Definition desk_named_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte) (p r : Z) (body : list byte),
    a0 = Z_to_bv 64 p ->
    0 < p ->
    bytes_at rsegs m p body ->
    off_window sp desk_named_FRAME p (Z.of_nat (length body)) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + desk_named_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_PLAIN sp desk_named_FRAME ->
    mem_inv rsegs m ->
    wmem rsegs m B ->
    desk_named_m timg_plain B body = Some (B', r) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - desk_named_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ B' = B /\ wmem rsegs m' B)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 desk_named_ENTRY) fc None m (seg_rom rsegs)).
