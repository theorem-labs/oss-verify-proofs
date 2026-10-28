(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoff.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import MainExport MainFactsAsan MainEntryAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import PrimaryShadow0.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes ALayout ARep AHeapP AQConst ARepQ ARepInit_kit ARepInit_A.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section C.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Let L := mkALayout (LV V) w U.

  (* [comment removed for export] *)
  Lemma top_eq : al_top L = 32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat.
  Proof.
    pf V HP (PVar 344 0 1) P344. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10. pf V HP (PVar 0 4294901760 4294967295) P0.
    pf V HP (PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4095) R.
    unfold two64 in R.
    assert (R' : 0 <= 16 * V 6%nat + -4096 * V 344%nat + 3935 <= 4095).
    { destruct (Z.lt_ge_cases (16 * V 6%nat + -4096 * V 344%nat + 3935) 0) as [NEG|NN].
      - exfalso. rewrite <- (Z.mod_add _ 1) in R by lia. rewrite Z.mod_small in R by lia. lia.
      - rewrite Z.mod_small in R by lia. exact R. }
    unfold al_top, L. rewrite LV_sp0. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia.
  Qed.

  Lemma t_eq : al_t L = 4096 * V 227%nat. Proof. reflexivity. Qed.
  Lemma ctx_eq : al_ctx L = 4096 * V 228%nat. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma t_zero : forall i, 80 <= i < 3168 -> m (wa (al_t L + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros i Hi. mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088) ZR.
    rewrite t_eq. replace (4096 * V 227%nat + i) with (4096 * V 227%nat + 80 + (i - 80)) by lia. apply ZR. lia.
  Qed.
  Lemma t_wr : wr_at bsegs m (al_t L) 4096.
  Proof. mwr V m HM (ZMul (ZLit 4096) (ZV 227)) 4096 W. rewrite t_eq. exact W. Qed.
  Lemma t_pos : 4096 <= al_t L /\ al_t L + 4096 <= ATOP.     (* [comment removed for export] *)
  Proof. pose proof (ao_t _ (alayout_ok_init V w U HP HU HAT)) as (_ & A & B & _). exact (conj A B). Qed.

  Theorem athread_init : athread L (ST0 V) X0 m.
  Proof.
    pose proof t_pos as [T1 T2]. atop_facts.
    unfold athread. split.
    { mf V m HM (MCell (ZMul (ZLit 4096) (ZV 227)) 8 (ZMul (ZLit 4096) (ZV 228))) F0.
      mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 8)) 8 (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344))))) F8.
      mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 16)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344)))) (ZLit (-8388608)))) F16.
      unfold al_bot. rewrite top_eq, t_eq.
      replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat)) with (32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat) in F8 by lia.
      replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat) + -8388608) with (32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat - 8388608) in F16 by lia.
      apply rw_cells_cons; [exact F0|]. apply rw_cells_cons; [exact F8|].
      replace (4096 * V 227%nat + Z.of_nat (csize (C8 (Z_to_bv 64 (al_ctx L)))) + Z.of_nat (csize (C8 (Z_to_bv 64 (32768 * V 0%nat + 4096 * V 10%nat + 4096 * V 344%nat)))))
        with (4096 * V 227%nat + 16) by (cbn; lia).
      exact F16. }
    split.
    { mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 40)) 1 (ZLit 0)) F40. rewrite t_eq. exact F40. }
    split.
    { intros c Hc. unfold acache_cells, acache_addr. rewrite get_cls_ST0, max_count_ST0. cbn [c_count aclass0 a_cinit ST0 ainit x_cls X0 xc_cache app length map].
      exists (repeat (Z_to_bv 64 0) 16). unfold K_NUM_CLASSES in Hc.
      split; [| split; [| rewrite repeat_length; reflexivity]].
      - apply zcells; [reflexivity| |].
        + cbn [cells_size csize Nat.add]. intros i Hi. replace (al_t L + 208 + c * 80 + i) with (al_t L + (208 + c * 80 + i)) by lia. apply t_zero. lia.
        + eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia].
      - apply u32arr_zero.
        + intros i Hi. cbn in Hi. replace (al_t L + 208 + c * 80 + 16 + i) with (al_t L + (224 + c * 80 + i)) by lia. apply t_zero. lia.
        + eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia]. }
    split.
    { exists (repeat (Z_to_bv 8 0) 32). apply zcells; [reflexivity| |].
      + cbn [cells_size csize Nat.add]. intros i Hi. replace (al_t L + 2768 + i) with (al_t L + (2768 + i)) by lia. apply t_zero. lia.
      + eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia]. }
    split.
    { exists (repeat (Z_to_bv 64 0) 46). split; [| rewrite repeat_length; reflexivity]. apply u64arr_zero.
      + intros i Hi. cbn in Hi. replace (al_t L + 2800 + i) with (al_t L + (2800 + i)) by lia. apply t_zero. lia.
      + eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia]. }
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)) F3168. rewrite t_eq. exact F3168.
  Qed.

  (* [comment removed for export] *)
  Theorem aqcache_loc_init : aqcache L m (aq_tcache L) [] [] 0.
  Proof.
    pose proof t_pos as [T1 T2]. atop_facts.
    unfold aqcache, aq_tcache. split; [| exact I].
    apply zcells; [reflexivity| |].
    - cbn [cells_size csize Nat.add]. intros i Hi. replace (al_t L + 80 + i) with (al_t L + (80 + i)) by lia. apply t_zero. lia.
    - eapply wr_at_sub; [exact t_wr| lia| lia| cbn; lia].
  Qed.
End C.
End CANSEC1.
