(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.FO Require Import FOCore.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.Prelim. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KLink. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01. Import SM01.KStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KEv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* Tier-2b port: a refusal is a node step only where the model forces it (premise [Hns]). *)
Lemma nstep_mmap_refuse : forall len prot mo,
  0 < len < 2^64 -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  ~ spurious_refusal_cfg alloc_forced_cfg
      (pure_input 222 [Z_to_bv 64 0; Z_to_bv 64 len; Z_to_bv 64 prot; Z_to_bv 64 MAPF;
                       Z_to_bv 64 (-1); Z_to_bv 64 0]) mo (efferr ENOMEM) ->
  nstep (NMmap 0 len prot MAPF) mo (efferr ENOMEM) mo [].
Proof.
  intros len prot mo Hlen Hprot Hns. apply nstep_mmap_iff. split; [|exact Hns]. split; [reflexivity|].
  unfold check_mmap.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true. change (mmap_anon_b (Z_to_bv 64 MAPF)) with true. cbn [negb].
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct Hprot as [-> | ->].
  - change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with false.
    change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true.
    cbv iota beta. unfold efferr, eff0. reflexivity.
  - change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true.
    cbv iota beta. unfold efferr, eff0. reflexivity.
Qed.

Lemma brk_zeros_same : forall req b : word, brk_zeros req b b = [].
Proof. intros. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, !andb_false_r. reflexivity. Qed.
Lemma brk_unmaps_same : forall b : word, brk_unmaps b b = [].
Proof. intros. unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? bv_unsigned b); reflexivity. Qed.
Lemma brk_r_ok_same : forall mo req, brk_r_ok mo req (vm_brk (m_vmmaps mo)) = true.
Proof.
  intros mo req. unfold brk_r_ok.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps mo)))); [apply bv_eqb_refl|].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps mo))); rewrite bv_eqb_refl, orb_true_r; [reflexivity|].
  cbn [andb]. unfold brk_grow_ok. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma nstep_brk_same : forall req mo,
  ~ spurious_refusal_cfg alloc_forced_cfg (pure_input 214 [Z_to_bv 64 req]) mo (eff0 (vm_brk (m_vmmaps mo))) ->
  nstep (NBrk req) mo (eff0 (vm_brk (m_vmmaps mo))) (with_brk_next mo (Z_to_bv 64 req) (vm_brk (m_vmmaps mo))) [].
Proof.
  intros req mo Hns. apply nstep_brk_iff. split; [|exact Hns]. unfold check_brk, eff0.
  rewrite brk_r_ok_same, brk_zeros_same, brk_unmaps_same. reflexivity.
Qed.

Lemma nstep_mprotect_refuse : forall a mo,
  0 < a -> a + PGSZ < 2^64 -> a mod 4096 = 0 ->
  map_contains (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  (* port727 (), as in rows 15 / 16's MrKRefuse: check_mprotect answers unmodeled for a range that
     meets the vDSO pair. *)
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  ~ spurious_refusal_cfg alloc_forced_cfg
      (pure_input 226 [Z_to_bv 64 a; Z_to_bv 64 PGSZ; Z_to_bv 64 PROT_RW]) mo (efferr ENOMEM) ->
  nstep (NMprotect a PGSZ PROT_RW) mo (efferr ENOMEM) mo [].
Proof.
  intros a mo Ha Hhi Hal Hcn Hcm Hvd Hns. apply nstep_mprotect_iff. split; [|exact Hns]. unfold check_mprotect.
  change (mprotect_grows_conflict_b (Z_to_bv 64 PROT_RW)) with false. change (mprotect_modeled_b (Z_to_bv 64 PROT_RW)) with true.
  rewrite (unsigned_lit a) by (unfold PGSZ in *; lia). rewrite page_size_eq, Hal. cbn [Z.eqb negb].
  change (w_is0 (Z_to_bv 64 PGSZ)) with false. cbv iota.
  rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia). change (page_round_up_Z PGSZ) with PGSZ.
  replace (two_pow_64 <=? a + PGSZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  cbv zeta. rewrite Hvd, Hcn, Hcm. cbn [andb negb]. unfold efferr, eff0. reflexivity.
Qed.
