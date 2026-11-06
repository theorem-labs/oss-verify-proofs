From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel sup_reply_code_c.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_REFUSAL : Z := 0x14efc.
Definition CHECK_REFUSAL_K : Z := 64.

Definition check_refusal_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (reply state : word) (quit : Z) (x : list byte),
    let S := bv_unsigned sp in
    mem_inv rsegs m ->
    stk rsegs m lo S -> lo + CHECK_REFUSAL_K <= S -> IMG_END <= lo ->
    bytes_at rsegs m GOT_GREC (le8 (Z_to_bv 64 G_REC)) ->
    bytes_at rsegs m (G_REC + REC_REPLY) (le8 reply) ->
    bytes_at rsegs m (G_REC + REC_STATE) (le8 state) ->
    bytes_at rsegs m GOT_GQUIT (le8 (Z_to_bv 64 G_QUIT)) ->
    0 <= quit < 2^32 -> bytes_at rsegs m G_QUIT (le4 (Z_to_bv 64 quit)) ->
    (bv_unsigned reply <> 0 ->
       cstr_at m (bv_unsigned reply) x /\ outside_stack lo S (bv_unsigned reply) (Z.of_nat (length x) + 1)) ->
    (bv_unsigned reply <> 0 -> reply_code x < 0 -> state = a0 /\ quit = 0) ->
    evt rsegs (void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_REFUSAL) fc None m (seg_rom rsegs)).
