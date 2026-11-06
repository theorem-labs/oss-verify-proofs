(* set_state (transport/src/diginet_session.c:79-86) at 0x16ce0, 140 bytes. The binary calls memset (the notice of
   :83) and, through g_s.notify, notice (:85). FRAME 384 = its own 112 (addi sp,sp,-112 at 0x16ce0) + 272, the
   deepest callee window (notice; memset 0). Every callee window counted is that callee's full transitive stack
   depth, abort() paths included, so it bounds the window any callee contract asks for. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition set_state_ENTRY : Z := 0x16ce0.
Definition set_state_FRAME : Z := 384.

(* a0 = s = &g_s, a1 = st (enum diginet_session_state), a2 = why (enum diginet_reason). void. *)
Definition set_state_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (st why : Z) (B B' : list byte) (TF : option tframe),
    a0 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) ->
    a1 = Z_to_bv 64 st ->
    a2 = Z_to_bv 64 why ->
    0 <= st < 2^31 ->
    0 <= why < 2^31 ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    set_state_m timg_ubsan TF B st why = Some (B', tt) ->
    tframe_at m sp set_state_FRAME TF ->
    relro_img m ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + set_state_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp set_state_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - set_state_FRAME, bv_unsigned sp);
                (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 set_state_ENTRY) fc None m (seg_rom rsegs)).
