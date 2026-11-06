From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem has_prefixed_c.
Import ListNotations.
Open Scope Z_scope.

Definition READINGS_SCAN : Z := 0x13ce0.
Definition READINGS_FRAME : Z := 176.
Definition READINGS_K : Z := READINGS_FRAME + HAS_PREFIXED_K.
Definition PREFIX_LC_AT : Z := 0x10416.
Definition PREFIX_UC_AT : Z := 0x1038a.
Definition prefix_uc : list Z := [80; 82; 69; 70; 73; 88].

Definition readings_scan_contract : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (ra1 sp1 t0 t1 t2 rp uri a0 a1 a2 a3 a4 a5 a6 a7 txt un x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6 v : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (junk tb ts ub us : list byte),
    sp1 = Z_to_bv 64 (bv_unsigned sp - READINGS_FRAME) ->
    rw_cells rsegs m (bv_unsigned sp - READINGS_FRAME)
      [CB 72 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp - READINGS_FRAME) ->
    lo + HAS_PREFIXED_K <= bv_unsigned sp - READINGS_FRAME ->
    cstr_at m (bv_unsigned txt) tb ts ->
    cstr_at m (bv_unsigned uri) ub us ->
    ub <> [] ->
    un = Z_to_bv 64 (Z.of_nat (length ub)) ->
    4096 <= bv_unsigned txt ->
    Z.of_nat (length tb) + 1 < 2^63 ->
    4096 <= bv_unsigned uri ->
    bytes_at rsegs m (bv_unsigned rp) (le8 v) ->
    wr_at rsegs m (bv_unsigned rp) 8 ->
    bytes_at rsegs m PREFIX_LC_AT (map (Z_to_bv 8) (prefix_lc ++ [0])) ->
    bytes_at rsegs m PREFIX_UC_AT (map (Z_to_bv 8) (prefix_uc ++ [0])) ->
    bytes_at rsegs m 0x1e0b8 (le8 (Z_to_bv 64 0x4f6c8)) -> (exists g, bytes_at rsegs m 0x4f6c8 (le8 g)) ->
    0x4f6c8 + 8 <= bv_unsigned sp - READINGS_K -> 0x1e0b8 + 8 <= bv_unsigned sp - READINGS_K ->
    off_stack sp READINGS_K (bv_unsigned txt) (Z.of_nat (length tb + 1 + length ts)) ->
    off_stack sp READINGS_K (bv_unsigned uri) (Z.of_nat (length ub + 1 + length us)) ->
    off_stack sp READINGS_K (bv_unsigned rp) 8 ->
    off_stack sp READINGS_K PREFIX_LC_AT 7 ->
    off_stack sp READINGS_K PREFIX_UC_AT 7 ->
    disjoint_from [(bv_unsigned txt, bv_unsigned txt + Z.of_nat (length tb + 1 + length ts));
                   (bv_unsigned uri, bv_unsigned uri + Z.of_nat (length ub + 1 + length us));
                   (PREFIX_LC_AT, PREFIX_LC_AT + 7); (PREFIX_UC_AT, PREFIX_UC_AT + 7);
                   (0x1e0b8, 0x1e0b8 + 8); (0x4f6c8, 0x4f6c8 + 8)]
                  (bv_unsigned rp) 8 ->
    evt rsegs
      (kretm ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo READINGS_K m
         [(bv_unsigned rp, bv_unsigned rp + 8)]
         (fun r m' =>
            r = Z_to_bv 64 (scan (zbytes tb) (zbytes ub) 0 0 (S (length tb))) /\
            bytes_at rsegs m' (bv_unsigned rp)
              (le8 (Z_to_bv 64 (bv_unsigned v + Z.of_nat (readings (zbytes tb) (zbytes ub) 0 0 (S (length tb))))))))
      (MS (mkR ra1 sp1 gp tp t0 t1 t2 rp uri a0 a1 a2 a3 a4 a5 a6 a7 txt un x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
          F (Z_to_bv 64 READINGS_SCAN) fc None m (seg_rom rsegs)).
