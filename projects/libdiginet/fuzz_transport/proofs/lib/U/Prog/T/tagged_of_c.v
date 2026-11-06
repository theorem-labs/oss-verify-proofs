(* The machine contract of tagged_of (fuzz/fuzz_transport.c:609-615) in the ubsan image. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract.
Import ListNotations.
Open Scope Z_scope.

Definition tagged_of_ENTRY : Z := 0x155f4.
(* A leaf with no prologue (0x155f4-0x15664): the function uses no stack and stores nothing. *)
Definition tagged_of_FRAME : Z := 0.

(* the pointer tagged_of returns: &g_cmd[i] (struct tagged is 40 bytes, TWorld.v A_Cmd_st) or NULL *)
Definition tagged_of_ret (t : option Z) : Z :=
  match t with Some i => W_BASE_UBSAN + A_Cmd_st i | None => 0 end.

Definition tagged_of_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte) (p n : Z) (b : list byte) (t : option Z),
    a0 = Z_to_bv 64 p ->
    a1 = Z_to_bv 64 n ->
    0 <= n < 2^64 ->
    0 < p ->
    bytes_at rsegs m p b ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + tagged_of_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp tagged_of_FRAME ->
    mem_inv rsegs m ->
    wmem rsegs m B ->
    tagged_of_m B b n = Some (B', t) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (tagged_of_ret t)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - tagged_of_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ B' = B /\ wmem rsegs m' B)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 tagged_of_ENTRY) fc None m (seg_rom rsegs)).
