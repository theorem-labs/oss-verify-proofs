(* The machine contract of spec_read_frame (fuzz/spec.h:199-223, the out-of-line copy) in the ubsan image. *)
(* The model is the shared DgnSpec.spec_read_frame (a total function: no world, no None); the result struct is
   TContract.sf_bytes. The traps of the binary (misaligned f at 0x1503c / 0x15060, NULL b at 0x1504c, b + k overflow)
   are excluded by the premises 0 < p, fp mod 8 = 0 and p + len < 2^64 (bytes_at alone allows p + length fr = 2^64). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract.
Import ListNotations.
Open Scope Z_scope.

Definition spec_read_frame_ENTRY : Z := 0x15004.
(* addi sp,sp,-32 at 0x15004 (ra, s0-s2 saved); the only callee is memset (jal 0x20844), whose kit contract uses no
   stack: 32 + 0. *)
Definition spec_read_frame_FRAME : Z := 32.

Definition spec_read_frame_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B : list byte) (p len fp : Z) (fr junk : list byte),
    a0 = Z_to_bv 64 p ->
    a1 = Z_to_bv 64 len ->
    a2 = Z_to_bv 64 fp ->
    0 < p ->
    bytes_at rsegs m p fr ->
    0 <= len <= Z.of_nat (length fr) ->
    p + len < 2 ^ 64 ->        (* b + 30 (f->body, spec.h) does not wrap: the ubsan pointer-overflow check at 0x151c4-0x151cc *)
    fp mod 8 = 0 ->
    bv_unsigned sp <= fp ->
    rw_cells rsegs m fp [CB 80 junk] ->
    p + Z.of_nat (length fr) <= fp \/ fp + 80 <= p ->
    off_window sp spec_read_frame_FRAME p (Z.of_nat (length fr)) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + spec_read_frame_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp spec_read_frame_FRAME ->
    mem_inv rsegs m ->
    wmem rsegs m B ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (sf_code (spec_read_frame (zs fr) len)))
                       a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - spec_read_frame_FRAME, bv_unsigned sp); (fp, fp + 80)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ wmem rsegs m' B /\
         rw_cells rsegs m' fp [CB 80 (sf_bytes p (spec_read_frame (zs fr) len))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 spec_read_frame_ENTRY) fc None m (seg_rom rsegs)).
