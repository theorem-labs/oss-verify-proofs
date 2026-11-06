(* diginet_session_submit (transport/src/diginet_session.c:328-349) at 0x16fb4, 280 bytes. The binary inlines
   coalescable; it calls diginet_body_check (:332) and memcpy (the struct copies of :339, :347). FRAME 176 = its
   own 32 (addi sp,sp,-32 at 0x16fb4) + 144, the deepest callee window (diginet_body_check; memcpy 0). Every
   callee window counted is that callee's full transitive stack depth, abort() paths included, so it bounds the
   window any callee contract asks for. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition diginet_session_submit_ENTRY : Z := 0x16fb4.
Definition diginet_session_submit_FRAME : Z := 176.

(* a0 = s = &g_s, a1 = c = the address of the caller's struct diginet_cmd, whose 32 bytes are C (op_submit's local,
   fuzz_transport.c:1070-1081). Result: the int diginet_session_submit_m gives. *)
Definition diginet_session_submit_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (cp r : Z) (C : list byte) (B B' : list byte),
    a0 = Z_to_bv 64 (W_BASE_PLAIN + OFF_g_s) ->
    a1 = Z_to_bv 64 cp ->
    bytes_at rsegs m cp C ->
    length C = 32%nat ->
    arg_blk sp diginet_session_submit_FRAME cp 32 ->
    cp mod 4 = 0 ->
    wmem rsegs m B ->
    diginet_session_submit_m B C = Some (B', r) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + diginet_session_submit_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_PLAIN sp diginet_session_submit_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - diginet_session_submit_FRAME, bv_unsigned sp);
                (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 diginet_session_submit_ENTRY) fc None m (seg_rom rsegs)).
