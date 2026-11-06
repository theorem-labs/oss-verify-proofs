From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_RATE_SNAP : Z := 0x16914.
Definition A_P6000 : Z := 0x104f0.
Definition A_P3837 : Z := 0x10558.
Definition D6000 : Z := 0x40b7700000000000.
Definition D3837 : Z := 0x40adfb0000000000.

Definition reac_rate_snap_model (x : word) : Z :=
  if flt_d x (Z_to_bv 64 D3837) then 44100 else if flt_d x (Z_to_bv 64 D6000) then 48000 else 96 * 1000.

Definition reac_rate_snap_fcsr (x : word) (fc : bv 32) : bv 32 :=
  Z_to_bv 32 (Z.lor (bv_unsigned fc) (if fp_is_nan fmt_double (bv_unsigned x) then 16 else 0)).

Definition reac_rate_snap_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bytes_at rsegs m A_P6000 (le8 (Z_to_bv 64 D6000)) ->
    bytes_at rsegs m A_P3837 (le8 (Z_to_bv 64 D3837)) ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (reac_rate_snap_model (Sem.reg_get F (Z_to_bv 5 10))))
                       a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  (bvmap_set (Z_to_bv 5 14) (Z_to_bv 64 D3837) (bvmap_set (Z_to_bv 5 15) (Z_to_bv 64 D6000) F))
                  (ret_pc ra) (reac_rate_snap_fcsr (Sem.reg_get F (Z_to_bv 5 10)) fc) None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_RATE_SNAP) fc None m (seg_rom rsegs)).
