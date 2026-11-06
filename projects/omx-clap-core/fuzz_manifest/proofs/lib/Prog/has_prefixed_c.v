From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem.
Import ListNotations.
Open Scope Z_scope.

Definition HAS_PREFIXED : Z := 0x13f9c.
Definition HAS_PREFIXED_K : Z := 112 + 2256.

Definition has_prefixed_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo q : Z) (tb ts lb ls : list byte),
    cstr_at m (bv_unsigned a0) tb ts ->
    cstr_at m (bv_unsigned a3) lb ls ->
    lb <> [] ->
    bytes_at rsegs m 0x1e0b8 (le8 (Z_to_bv 64 0x4f6c8)) -> (exists g, bytes_at rsegs m 0x4f6c8 (le8 g)) ->
    0x4f6c8 + 8 <= bv_unsigned sp - HAS_PREFIXED_K -> 0x1e0b8 + 8 <= bv_unsigned sp - HAS_PREFIXED_K ->
    4096 <= bv_unsigned a0 ->
    Z.of_nat (length tb) + 1 < 2^63 ->
    0 <= q -> q + bv_unsigned a2 <= Z.of_nat (length tb) ->
    bv_unsigned a1 = bv_unsigned a0 + q ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + HAS_PREFIXED_K <= bv_unsigned sp ->
    off_stack sp HAS_PREFIXED_K (bv_unsigned a0) (Z.of_nat (length tb + 1 + length ts)) ->
    off_stack sp HAS_PREFIXED_K (bv_unsigned a3) (Z.of_nat (length lb + 1 + length ls)) ->
    evt rsegs
      (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo HAS_PREFIXED_K m []
         (fun r => r = Z_to_bv 64
                        (if token (zbytes tb)
                                  (firstn (Z.to_nat (bv_unsigned a2)) (skipn (Z.to_nat q) (zbytes tb)))
                                  (zbytes lb)
                         then 1 else 0)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HAS_PREFIXED) fc None m (seg_rom rsegs)).
