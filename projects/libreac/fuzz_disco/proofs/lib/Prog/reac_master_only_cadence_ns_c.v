From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_rate_snap_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_MASTER_ONLY_CADENCE_NS : Z := 0x16508.
Definition RT : Z := 0x10598.

Definition RATES : list byte := le4 (Z_to_bv 64 44100) ++ le4 (Z_to_bv 64 48000) ++ le4 (Z_to_bv 64 (96 * 1000)).

Definition freg_kept (F F' : bvmap 5 word) : Prop :=
  forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> Sem.reg_get F' k = Sem.reg_get F k.

Definition reac_master_only_cadence_ns_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fps lo : Z),
    a0 = Z_to_bv 64 fps -> -2^31 <= fps < 2^31 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp -> RT + 12 <= lo ->
    bytes_at rsegs m RT RATES ->
    bytes_at rsegs m A_P6000 (le8 (Z_to_bv 64 D6000)) ->
    bytes_at rsegs m A_P3837 (le8 (Z_to_bv 64 D3837)) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' : word) (F' : bvmap 5 word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (10^9)) a1' a2' a3' a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F' (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\ freg_kept F F')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_MASTER_ONLY_CADENCE_NS) fc None m (seg_rom rsegs)).
