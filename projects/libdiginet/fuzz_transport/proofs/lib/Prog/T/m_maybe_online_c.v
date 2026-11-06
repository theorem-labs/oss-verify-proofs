(* The machine contract of m_maybe_online (fuzz/fuzz_transport.c:237-243, m_set inlined) in the plain image. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract.
Import ListNotations.
Open Scope Z_scope.

Definition m_maybe_online_ENTRY : Z := 0x15904.
(* A leaf with no prologue (0x15904-0x15988): the function uses no stack. *)
Definition m_maybe_online_FRAME : Z := 0.

Definition m_maybe_online_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte),
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + m_maybe_online_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_PLAIN sp m_maybe_online_FRAME ->
    mem_inv rsegs m ->
    wmem rsegs m B ->
    m_maybe_online_m B = Some (B', tt) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - m_maybe_online_FRAME, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ wmem rsegs m' B')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 m_maybe_online_ENTRY) fc None m (seg_rom rsegs)).
