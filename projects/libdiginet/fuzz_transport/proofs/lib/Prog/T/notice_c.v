(* notice (fuzz/fuzz_transport.c:937-973; model TCb.v notice_m), entry 0x149e4, 70 instructions. Dispatches on
   n->kind (jump table in .rodata): STATE records the transition in GOT.t[GOT.n] (when GOT.n < 16), GOT.n++, and
   checks ONLINE (check_state_online); ACKED: GOT.acked++, check_inflight_acked; ACK_LOST: check_inflight_lost,
   M.fly.on = 0; DESK: GOT.desk++, check_state_desk; DATA: check_state_data, GOT.ndata++; FOREIGN: GOT.foreign++.
   Writes GOT and M.fly.on.
   Arguments: a0 = ctx, not read; a1 = n, a struct diginet_notice (ntc_at); the current heap frame Fr (tframe_at);
   .data.rel.ro as in the image (relro_img).
   FRAME 48: own prologue 16; tail calls (frame popped first) of check_state_desk (48), check_inflight_acked (16),
   check_state_online (16) from the entry sp; jal of check_inflight_lost (16 + 16) and check_state_data (16 + 32)
   inside the frame; max 48.
   Callee contracts its walk uses: check_state_online_contract, check_inflight_acked_contract,
   check_inflight_lost_contract, check_state_desk_contract, check_state_data_contract.
   The world: written; post wmem rsegs m' B', the world interval in munch. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem TImgP TContract.
Import ListNotations.
Open Scope Z_scope.

Definition notice_ENTRY : Z := 0x149e4.
Definition notice_FRAME : Z := 48.

Definition notice_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte) (p : Z) (n : ntc) (Fr : option tframe),
    a1 = Z_to_bv 64 p ->
    ntc_at m p n sp notice_FRAME ->
    tframe_at m sp notice_FRAME Fr ->
    relro_img m ->
    wmem rsegs m B ->
    notice_m timg_plain Fr B n = Some (B', tt) ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + notice_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_PLAIN sp notice_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - notice_FRAME, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 notice_ENTRY) fc None m (seg_rom rsegs)).
