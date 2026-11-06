(* diginet_session_deadline (transport/src/diginet_session.c:476-503) at 0x17c5c, 356 bytes. The binary inlines ms
   and min64; it calls nothing. FRAME 0 = its own 0 (no stack adjustment); it calls nothing. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_session_deadline_ENTRY : Z := 0x17c5c.
Definition diginet_session_deadline_FRAME : Z := 0.

(* a0 = s = &g_s, a1 = now (uint64_t). Result: the uint64_t diginet_session_deadline_m gives. It writes no world
   byte. *)
Definition diginet_session_deadline_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (now r : Z) (B : list byte),
    a0 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) ->
    a1 = Z_to_bv 64 now ->
    0 <= now < 2^64 ->
    wmem rsegs m B ->
    diginet_session_deadline_m B now = Some r ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + diginet_session_deadline_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp diginet_session_deadline_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - diginet_session_deadline_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 diginet_session_deadline_ENTRY) fc None m (seg_rom rsegs)).
