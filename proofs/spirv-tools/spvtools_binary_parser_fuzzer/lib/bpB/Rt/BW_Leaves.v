(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BllocWalkKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition getcurthread_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section GetCurThread.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo TSD CTX T : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 16 <= bv_unsigned sp.
  Hypothesis TPR : 4096 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP.
  Hypothesis RNG : 0 < TSD /\ TSD + 8 <= aceil /\ 0 < CTX /\ CTX + 160 <= aceil /\ 0 < T < aceil.
  Hypothesis CTSDI : rw_cells asegs m ATSDINIT [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)].
  Hypothesis CTP : rw_cells asegs m (bv_unsigned tp + -88) [C8 (wz TSD)].
  Hypothesis CTSD : rw_cells asegs m TSD [C8 (wz CTX)].
  Hypothesis CCTX : rw_cells asegs m (CTX + 152) [C8 (wz T)].

  Theorem getcurthread_spec :
    evt asegs (getcurthread_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo T)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc41d4) fc None m (seg_rom asegs)).
  Proof.
    unfold wz, ATSDINIT, AIMG_TOP in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. carve_frame 16%nat ST. step.

    step. step. step. step. rewrite zxb_b8 by lia.
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. rewrite sx32_wz by lia. step.

    step. step. step. step.
    replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (wz 0)) 32))) 29)) with (wz 0) by (apply bv_eq; vm_compute; reflexivity).
    step. step. step.

    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End GetCurThread.

Definition getcurthreadstats_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (T + 2800)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section GetCurThreadStats.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo TSD CTX T : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 32 <= bv_unsigned sp.
  Hypothesis TPR : 4096 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP.
  Hypothesis RNG : 0 < TSD /\ TSD + 8 <= aceil /\ 0 < CTX /\ CTX + 160 <= aceil /\ 0 < T < aceil.
  Hypothesis CTSDI : rw_cells asegs m ATSDINIT [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)].
  Hypothesis CTP : rw_cells asegs m (bv_unsigned tp + -88) [C8 (wz TSD)].
  Hypothesis CTSD : rw_cells asegs m TSD [C8 (wz CTX)].
  Hypothesis CCTX : rw_cells asegs m (CTX + 152) [C8 (wz T)].

  Theorem getcurthreadstats_spec :
    evt asegs (getcurthreadstats_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo T)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc33a0) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof LO as LO'. pose proof RNG as RNG'. acb. unfold ATSDINIT, AIMG_TOP in *.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. carve_frame 16%nat ST. step.
    step. callN getcurthread_spec. all: rewrite ?unsigned_lit by lia. all: try eassumption; try lia.

    step. if_cases K; zify_cond K. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K by lia. lia. } clear K.
    step. step. rewrite (wz_unsigned T) by lia. replace (T + 2047 + 753) with (T + 2800) by lia.
    step. step. step. lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end. finish.
  Qed.
End GetCurThreadStats.

Section Tiny.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Hypothesis MI : mem_inv asegs m.

  Definition leaf_post (v : Z) : machine_state -> Prop :=
    fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m (seg_rom asegs)
               /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

  Hypothesis CINIT : rw_cells asegs m AINITED [C1 (b8 1)].
  Theorem asan_inited_spec :
    evt asegs (leaf_post 1) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0xc0ac4) fc None m (seg_rom asegs)).
  Proof.
    unfold AINITED in *. step. step. step. step. step. step.
    replace (v_sltiu (Z_to_bv 64 (bv_unsigned (sxb (b8 1)) + -1)) 1) with (wz 1) by (apply bv_eq; vm_compute; reflexivity).
    apply evt_done. unfold leaf_post. split; [reflexivity| split; [apply munch_refl| split; [apply wmono_refl| exact MI]]].
  Qed.

  Hypothesis CAFL : rw_cells asegs m AALLOCFLAGS [C1 (b8 0); C1 (b8 1); C1 (b8 0)].
  Theorem rss_exceeded_spec :
    evt asegs (leaf_post 0) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0xc678c) fc None m (seg_rom asegs)).
  Proof.
    unfold AALLOCFLAGS in *. step. step. step. step.
    apply evt_done. unfold leaf_post. split; [reflexivity| split; [apply munch_refl| split; [apply wmono_refl| exact MI]]].
  Qed.

  Hypothesis CCAN : rw_cells asegs m ACANPOISON [C1 (b8 1)].
  Theorem can_poison_spec :
    evt asegs (leaf_post 1) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0xbb414) fc None m (seg_rom asegs)).
  Proof.
    unfold ACANPOISON in *. step. step. step. step. step.
    apply evt_done. unfold leaf_post. split; [reflexivity| split; [apply munch_refl| split; [apply wmono_refl| exact MI]]].
  Qed.

  Hypothesis GOT2 : rw_cells asegs m 0x185d00 [C8 (wz 0x10)].
  Hypothesis CLSAN : rw_cells asegs m (bv_unsigned tp + 16) [C4 (wz 0)].
  Theorem lsan_disabled_spec :
    evt asegs (leaf_post 0) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0xe7db4) fc None m (seg_rom asegs)).
  Proof.
    step. step. step. unfold wz at 1. rewrite (unsigned_lit 16), (Z.add_comm 16 (bv_unsigned tp)) by lia. step. rewrite sx32_wz by lia. step. step.
    apply evt_done. unfold leaf_post. split; [reflexivity| split; [apply munch_refl| split; [apply wmono_refl| exact MI]]].
  Qed.
End Tiny.

Definition rzlog_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo r : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section RZLog.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 16 <= bv_unsigned sp.

  Theorem rzlog16_spec : a0 = wz 16 ->
    evt asegs (rzlog_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo 0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x97abc) fc None m (seg_rom asegs)).
  Proof.
    intros ->. unfold wz.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. carve_frame 16%nat ST. step.
    step. step. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. step. step. step. step. step. step. step.

    step. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: try (apply bv_eq; vm_compute; reflexivity).
  Qed.

  Theorem rzlog2048_spec : a0 = wz 2048 ->
    evt asegs (rzlog_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo 7)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x97abc) fc None m (seg_rom asegs)).
  Proof.
    intros ->. unfold wz.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. carve_frame 16%nat ST. step.
    step. step. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. step. step. step. step. step. step. step.

    step. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: try (apply bv_eq; vm_compute; reflexivity).
  Qed.
End RZLog.

Definition hooks_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (a0 a1 a2 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Section Hooks.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 32 <= bv_unsigned sp.
  Hypothesis CHOOKS : rw_cells asegs m AHOOKS (repeat (C8 (wz 0)) 10).

  Theorem run_malloc_hooks_spec :
    evt asegs (hooks_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc89a8) fc None m (seg_rom asegs)).
  Proof.
    unfold AHOOKS in *. cbn [repeat] in CHOOKS.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. carve_frame 32%nat ST. step. step. step. step. step. step.

    step. step. replace (ret_pc (Z_to_bv 64 0xc89c8)) with (Z_to_bv 64 0xc89c8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    step. step. step. step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?wz_unsigned, ?unsigned_lit by lia. lia. } clear K.
    step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End Hooks.

End HCW.

