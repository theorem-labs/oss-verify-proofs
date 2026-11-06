(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_art RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.

Section CeilWrap.
Context {ACEIL : Ceil}.

Lemma grant_vs_image : forall mo (a : word) k, LOK bsegs mo -> mmap_grant mo a k -> 0 < k < 2^64 ->
  bv_unsigned a + k <= AIMG_LO \/ AIMG_HI <= bv_unsigned a.
Proof.
  intros mo a k HO (AL & POS & CE & RF) Hk. rewrite region_free_app in RF. apply andb_true_iff in RF as [RF _].
  rewrite (lok_resv _ _ HO), bsegs_reserved_sec in RF. cbn [region_free] in RF. unfold iv_overlap in RF.
  rewrite !unsigned_lit in RF by lia.
  repeat (apply andb_true_iff in RF as [?X RF]; apply negb_true_iff in X; apply andb_false_iff in X; destruct X as [X|X]; apply Z.ltb_ge in X);
  unfold AIMG_LO, AIMG_HI; lia.
Qed.

Lemma grant_vs_entry : forall mo (a : word) k lo sz, mmap_grant mo a k -> 0 < k < 2^64 -> zin lo sz (vm_maps (m_vmmaps mo)) ->
  0 <= lo -> 0 < sz -> lo + sz < 2^64 ->
  bv_unsigned a + k <= lo \/ lo + sz <= bv_unsigned a.
Proof.
  intros mo a k lo sz (_ & _ & _ & RF) Hk Hin H0 H1 H2. rewrite region_free_app in RF. apply andb_true_iff in RF as [_ RF].
  assert (U1 : bv_unsigned (wz lo) = lo) by (unfold wz; apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (wz sz) = sz) by (unfold wz; apply unsigned_lit; lia).
  assert (U3 : bv_unsigned (Z_to_bv 64 k : word) = k) by (apply unsigned_lit; lia).
  pose proof (region_free_elim _ a (Z_to_bv 64 k) (wz lo) (wz sz) RF Hin ltac:(rewrite U3; lia) ltac:(rewrite U2; lia)) as D.
  rewrite U1, U2, U3 in D. exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SHBAND (mo : Model) : Prop :=
  zin KHIGHSHADOW_BEG HIGHSHADOW_SIZE (vm_maps (m_vmmaps mo))
  /\ zin KLOWSHADOW_BEG LOWSHADOW_SIZE (vm_maps (m_vmmaps mo))
  /\ zin KLOWSHADOW_END (KHIGHSHADOW_BEG - KLOWSHADOW_END) (vm_maps (m_vmmaps mo)).

Lemma shband_of_model : forall st mo, RTMODEL st mo -> SHBAND mo.
Proof. intros st mo (_ & _ & M3 & M4 & _ & M6 & _). exact (conj M3 (conj M4 M6)). Qed.

Lemma shband_mono : forall mo mo', (forall e, In e (vm_maps (m_vmmaps mo)) -> In e (vm_maps (m_vmmaps mo'))) -> SHBAND mo -> SHBAND mo'.
Proof. intros mo mo' H (M3 & M4 & M6). unfold SHBAND, zin in *. repeat split; apply H; assumption. Qed.

Lemma shband_add_map : forall mo a n, SHBAND mo -> SHBAND (mm_add_map a n mo).
Proof. intros mo a n. apply shband_mono. intros e He. rewrite mm_add_map_vmmaps. cbn [vm_maps]. right. exact He. Qed.

Theorem grant_oclr_b : forall mo (a : word) k, LOK bsegs mo -> SHBAND mo -> 0 < k < 2^64 -> mmap_grant mo a k ->
  oclr (bv_unsigned a) (bv_unsigned a + k).
Proof.
  intros mo a k HO (M3 & M4 & M6) Hk GR.
  pose proof GR as (AL & POS & CE & _).
  pose proof (grant_vs_image mo a k HO GR Hk) as DI.
  pose proof (grant_vs_entry mo a k _ _ GR Hk M3 ltac:(unfold KHIGHSHADOW_BEG; lia) ltac:(unfold HIGHSHADOW_SIZE, KHIGHSHADOW_BEG, KHIGHMEM_BEG; lia) ltac:(unfold HIGHSHADOW_SIZE, KHIGHSHADOW_BEG, KHIGHMEM_BEG; lia)) as D3.
  pose proof (grant_vs_entry mo a k _ _ GR Hk M4 ltac:(unfold KLOWSHADOW_BEG; lia) ltac:(unfold LOWSHADOW_SIZE, KLOWSHADOW_BEG, KLOWSHADOW_END; lia) ltac:(unfold LOWSHADOW_SIZE, KLOWSHADOW_BEG, KLOWSHADOW_END; lia)) as D4.
  pose proof (grant_vs_entry mo a k _ _ GR Hk M6 ltac:(unfold KLOWSHADOW_END; lia) ltac:(unfold KHIGHSHADOW_BEG, KLOWSHADOW_END; lia) ltac:(unfold KHIGHSHADOW_BEG, KLOWSHADOW_END; lia)) as D6.
  assert (P4 : 4096 <= bv_unsigned a) by (change page_size with 4096 in AL; Z.div_mod_to_equations; lia).
  apply oclr_of_disjoint; [exact P4| lia| exact DI| | |];
    unfold HIGHSHADOW_SIZE, LOWSHADOW_SIZE, KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHSHADOW_END, KHIGHMEM_BEG in *; lia.
Qed.

Theorem grant_oclr : forall st mo (a : word) k, LOK bsegs mo -> RTMODEL st mo -> 0 < k < 2^64 -> mmap_grant mo a k ->
  oclr (bv_unsigned a) (bv_unsigned a + k).
Proof. intros st mo a k HO HM. exact (grant_oclr_b mo a k HO (shband_of_model st mo HM)). Qed.

Theorem grant_ablk_b : forall mo (a : word) k, LOK bsegs mo -> SHBAND mo -> 0x10000 <= k < 2^64 -> mmap_grant mo a k ->
  ablk (bv_unsigned a) (bv_unsigned a + k).
Proof.
  intros mo a k HO HM Hk GR. pose proof GR as (_ & _ & CE & _).
  apply oclr_ablk; [exact (grant_oclr_b mo a k HO HM ltac:(lia) GR)| lia| exact CE].
Qed.

(* [comment removed for export] *)
Theorem grant_ablk : forall st mo (a : word) k, LOK bsegs mo -> RTMODEL st mo -> 0x10000 <= k < 2^64 -> mmap_grant mo a k ->
  ablk (bv_unsigned a) (bv_unsigned a + k).
Proof.
  intros st mo a k HO HM Hk GR. pose proof GR as (_ & _ & CE & _).
  apply oclr_ablk; [exact (grant_oclr st mo a k HO HM ltac:(lia) GR)| lia| exact CE].
Qed.

End CeilWrap.
