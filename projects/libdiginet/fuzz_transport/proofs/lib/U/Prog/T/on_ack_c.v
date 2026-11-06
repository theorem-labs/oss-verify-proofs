(* on_ack (transport/src/diginet_session.c:223-237) at 0x1728c, 204 bytes. The binary calls memset (the notice),
   maybe_online (:235) and, through g_s.notify, notice (:232). FRAME 480 = its own 96 (addi sp,sp,-96 at 0x1728c)
   + 384, the deepest callee window (maybe_online; memset 0, notice 272). Every callee window counted is that
   callee's full transitive stack depth, abort() paths included, so it bounds the window any callee contract asks
   for. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition on_ack_ENTRY : Z := 0x1728c.
Definition on_ack_FRAME : Z := 480.

(* a0 = s = &g_s, a1 = f = rx's struct diginet_frame, parsed (code 0) from the frame bytes b at buf (dframe_at).
   void. *)
Definition on_ack_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (fp buf : Z) (b fj : list byte) (B B' : list byte) (TF : option tframe),
    a0 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) ->
    a1 = Z_to_bv 64 fp ->
    dframe_at m sp on_ack_FRAME fp buf b fj ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    on_ack_m timg_ubsan TF B b = Some (B', tt) ->
    tframe_at m sp on_ack_FRAME TF ->
    relro_img m ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + on_ack_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp on_ack_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - on_ack_FRAME, bv_unsigned sp);
                (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 on_ack_ENTRY) fc None m (seg_rom rsegs)).
