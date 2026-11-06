From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Export RecFacts.
Import ListNotations.
Open Scope Z_scope.

Definition MIX_CALL : Z := 0x15ccc.
Definition MIX_CALL_FRAME : Z := 80.
Definition FNV_B0_ADDR : Z := 0x10ab0.

Definition mc_arg (m : word -> option byte) (lo hi c : Z) (k : nat) (p : word * list byte) : Prop :=
  bytes_at rsegs m (c + 8 + 8 * Z.of_nat k) (le8 (fst p)) /\
  ~ In (Z_to_bv 8 0) (snd p) /\
  Z.of_nat (length (snd p)) <= LMAX /\
  exists slack : list byte,
    bytes_at rsegs m (bv_unsigned (fst p)) (snd p ++ Z_to_bv 8 0 :: slack) /\
    (- (bv_unsigned (fst p) + Z.of_nat (length (snd p)) + 1)) mod 8 <= Z.of_nat (length slack) /\
    (bv_unsigned (fst p) + Z.of_nat (length (snd p)) + 1 + Z.of_nat (length slack) <= lo \/
     hi <= bv_unsigned (fst p)).

Definition mix_call_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo fn : Z) (args : list (word * list byte)),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + MIX_CALL_FRAME <= bv_unsigned sp ->
    -2^31 <= fn < 2^31 ->
    (length args <= 6)%nat ->
    bytes_at rsegs m (bv_unsigned a1) (le4 (Z_to_bv 64 fn) ++ le4 (Z_to_bv 64 (Z.of_nat (length args)))) ->
    bv_unsigned a1 + 56 <= bv_unsigned sp - MIX_CALL_FRAME \/ bv_unsigned sp <= bv_unsigned a1 ->
    (forall k p, nth_error args k = Some p ->
       mc_arg m (bv_unsigned sp - MIX_CALL_FRAME) (bv_unsigned sp) (bv_unsigned a1) k p) ->
    bytes_at rsegs m FNV_B0_ADDR (le8 (Z_to_bv 64 FNV_B0)) ->
    FNV_B0_ADDR + 8 <= bv_unsigned sp - MIX_CALL_FRAME \/ bv_unsigned sp <= FNV_B0_ADDR ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (mixcall (bv_unsigned a0) fn (map snd args)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - MIX_CALL_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MIX_CALL) fc None m (seg_rom rsegs)).
