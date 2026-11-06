From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem.
Import ListNotations.
Open Scope Z_scope.

Definition PLAIN : Z := 0x13994.
Definition PLAIN_K : Z := 16.

Definition plain_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs slack : list byte),
    cstr_at m (bv_unsigned a0) bs slack ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PLAIN_K <= bv_unsigned sp ->
    off_stack sp PLAIN_K (bv_unsigned a0) (Z.of_nat (length bs + 1 + length slack)) ->
    evt rsegs
      (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo PLAIN_K m []
         (fun r => r = Z_to_bv 64 (if plain_name (zbytes bs) then 1 else 0)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PLAIN) fc None m (seg_rom rsegs)).
