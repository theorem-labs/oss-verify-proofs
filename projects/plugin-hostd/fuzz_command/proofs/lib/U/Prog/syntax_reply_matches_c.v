From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel.
Import ListNotations.
Open Scope Z_scope.

Definition SYNTAX_REPLY_MATCHES : Z := 0x15164.
Definition SYNTAX_REPLY_MATCHES_K : Z := 208.

Definition syntax_reply_matches_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (shape reply slack : list byte) (can : word),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + SYNTAX_REPLY_MATCHES_K <= bv_unsigned sp -> IMG_END <= lo ->
    bv_unsigned a0 <> 0 -> cstr_at m (bv_unsigned a0) shape ->
    outside_stack lo (bv_unsigned sp) (bv_unsigned a0) (Z.of_nat (length shape) + 1) ->
    bv_unsigned a1 <> 0 -> bytes_at rsegs m (bv_unsigned a1) (reply ++ NUL :: slack) -> ~ In NUL reply ->
    (- (bv_unsigned a1 + Z.of_nat (length reply) + 1)) mod 8 <= Z.of_nat (length slack) ->
    outside_stack lo (bv_unsigned sp) (bv_unsigned a1) (Z.of_nat (length reply) + 1 + Z.of_nat (length slack)) ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 can) ->
    Z.of_nat (length shape) < 2^31 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if reply_matches shape reply then 1 else 0))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SYNTAX_REPLY_MATCHES) fc None m (seg_rom rsegs)).
