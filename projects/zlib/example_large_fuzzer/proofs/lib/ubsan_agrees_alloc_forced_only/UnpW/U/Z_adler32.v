(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_adler32.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dkit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_ADLER32 : Z := 0x1b2c8.
Definition Z_ADLER32_Z : Z := 0x1ad98.
Definition ADLER32_FRAME : Z := 128.

(* [comment removed for export] *)
Definition adler32_postU (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (v lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adler32_null_spec : forall (lo adler len : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  0 <= adler < 2^64 -> 0 <= len < 2^32 -> len <> 1 -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ADLER32_FRAME ->
  evt usegs (adler32_postU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz 0) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_ADLER32) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HA HL HN MI STK LO. unfold Z_ADLER32, ADLER32_FRAME in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (proj1 STK) as LO0.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 3 zstep.
  carve_frame 128%nat STK.
  do 14 zs.
  do 5 zstep.
  if_cases K; zify_cond K.
  2:{ exfalso. rewrite ?Z.mod_small in K by lia. lia. }
  zstep. if_true.
  do 14 zs. release_frame FR STK (bv_unsigned sp). zs.
  apply evt_done. unfold adler32_postU. do 14 eexists. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact STK].
Qed.
