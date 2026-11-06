From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem expected_c.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_AS_WRITTEN : Z := 0x13234.
Definition CHECK_AS_WRITTEN_K : Z := 16 + EXPECTED_K.

Definition check_as_written_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (tb ts ub us : list byte),
    cstr_at m (bv_unsigned a0) tb ts ->
    cstr_at m (bv_unsigned a1) ub us ->
    4096 <= bv_unsigned a0 -> 4096 <= bv_unsigned a1 ->
    Z.of_nat (length tb) + 1 < 2^62 -> Z.of_nat (length ub) + 1 < 2^62 ->
    a2 = Z_to_bv 64 (names (zbytes tb) (zbytes ub)) ->
    bytes_at rsegs m PREFIX_LC_STR (map (Z_to_bv 8) (prefix_lc ++ [0])) ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_AS_WRITTEN_K <= bv_unsigned sp ->
    off_stack sp CHECK_AS_WRITTEN_K (bv_unsigned a0) (Z.of_nat (length tb + 1 + length ts)) ->
    off_stack sp CHECK_AS_WRITTEN_K (bv_unsigned a1) (Z.of_nat (length ub + 1 + length us)) ->
    off_stack sp CHECK_AS_WRITTEN_K PREFIX_LC_STR 7 ->
    evt rsegs
      (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo CHECK_AS_WRITTEN_K m [] (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_AS_WRITTEN) fc None m (seg_rom rsegs)).
