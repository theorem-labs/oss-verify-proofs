From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0.
Open Scope Z_scope.

Definition REAC_UPSTREAM_CHANNELS : Z := 0x81ad0.
Definition UPSTREAM_DIV36_AT : Z := 0x10338.
Definition UPSTREAM_DIV36 : Z := 0xe38e38e38e38e38f.

Definition upstream_width (len : Z) : Z := ((len - 52) / 36) mod 2^32.

Definition upstream_ok (len : Z) : bool :=
  (52 <=? len) && ((len - 52) mod 36 =? 0) && Z.even (upstream_width len)
  && (2 <=? upstream_width len) && (upstream_width len <=? 40).

Definition upstream_result (len : Z) : Z := if upstream_ok len then upstream_width len else -1.

Definition reac_upstream_channels_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m UPSTREAM_DIV36_AT (le8 (Z_to_bv 64 UPSTREAM_DIV36)) ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (upstream_result (bv_unsigned a0))) a1' a2' a3'
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_UPSTREAM_CHANNELS) fc None m (seg_rom rsegs)).
