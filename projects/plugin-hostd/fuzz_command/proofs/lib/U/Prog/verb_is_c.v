From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import VerbsMem.
Import ListNotations.
Open Scope Z_scope.

Definition VERB_IS : Z := 0x17c94.
Definition VERB_IS_K : Z := 128.
Definition DS_STR : Z := 0x1034c.
Definition DT_STR : Z := 0x1064c.

Definition verb_is_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (can : word) (tb fb fs : list byte),
    cstr0_at m (bv_unsigned a0) tb ->
    cstr_at m (bv_unsigned a1) fb fs ->
    Z.of_nat (length tb) + 1 < 2^62 -> Z.of_nat (length fb) + 1 < 2^62 ->
    bytes_at rsegs m DS_STR (map (Z_to_bv 8) [32; 0]) ->
    bytes_at rsegs m DT_STR (map (Z_to_bv 8) [32; 9; 0]) ->
    ssp_at m can ->
    off_lo lo sp SSP_GOT 8 -> off_lo lo sp SSP_GUARD 8 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + VERB_IS_K <= bv_unsigned sp ->
    off_lo lo sp (bv_unsigned a0) (Z.of_nat (length tb + 1)) ->
    off_lo lo sp (bv_unsigned a1) (Z.of_nat (length fb + 1 + length fs)) ->
    off_lo lo sp DS_STR 2 -> off_lo lo sp DT_STR 3 ->
    evt rsegs
      (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo VERB_IS_K m []
         (fun r => r = Z_to_bv 64 (if verb_is_m tb fb then 1 else 0)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 VERB_IS) fc None m (seg_rom rsegs)).
