From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import VerbsMem.
Import ListNotations.
Open Scope Z_scope.

Definition IS_INSTANCE_VERB : Z := 0x17db0.
Definition IS_INSTANCE_VERB_K : Z := 160.
Definition IV_TABLE : Z := 0x22928.
Definition DS_STR : Z := 0x1034c.
Definition DT_STR : Z := 0x1064c.
Definition iv_ptrs : list Z :=
  [0x108e8; 0x108fa; 0x10a20; 0x10545; 0x1071e; 0x1083b; 0x109bc; 0x1074c; 0x1034e;
   0x10360; 0x10855; 0x10331; 0x104cf; 0x107f2; 0x107a5; 0x103ee; 0x102dd; 0x107b4].

Definition is_instance_verb_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (can : word) (tb : list byte),
    cstr0_at m (bv_unsigned a0) tb ->
    Z.of_nat (length tb) + 1 < 2^62 ->
    bytes_at rsegs m IV_TABLE (concat (map (fun p => le8 (Z_to_bv 64 p)) iv_ptrs)) ->
    Forall2 (fun p f => exists fs, cstr_at m p f fs /\
                         off_lo lo sp p (Z.of_nat (length f + 1 + length fs)))
            iv_ptrs instance_verb_formats ->
    bytes_at rsegs m DS_STR (map (Z_to_bv 8) [32; 0]) ->
    bytes_at rsegs m DT_STR (map (Z_to_bv 8) [32; 9; 0]) ->
    ssp_at m can ->
    off_lo lo sp SSP_GOT 8 -> off_lo lo sp SSP_GUARD 8 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + IS_INSTANCE_VERB_K <= bv_unsigned sp ->
    off_lo lo sp (bv_unsigned a0) (Z.of_nat (length tb + 1)) ->
    off_lo lo sp IV_TABLE 144 ->
    off_lo lo sp DS_STR 2 -> off_lo lo sp DT_STR 3 ->
    evt rsegs
      (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo IS_INSTANCE_VERB_K m []
         (fun r => r = Z_to_bv 64 (if existsb (verb_is_m tb) instance_verb_formats then 1 else 0)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IS_INSTANCE_VERB) fc None m (seg_rom rsegs)).
