(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.leptonica.edge_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.ASB9 Require Import AsanTablesA AsanStartup StartupHSAsan StartupPlanAsan AsanStartupCert.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_rep D_libiface TopA_iodefs RT_io TopA_start TopA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Top Require Import TopLevelA.
Import ListNotations. Import AX2. Import AP.

(* [comment removed for export] *)
Lemma hs_ok_0 : hs_all_ok HS_asan_0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_1000 : hs_all_ok HS_asan_1000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_2000 : hs_all_ok HS_asan_2000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_3000 : hs_all_ok HS_asan_3000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma hs_if_some_ok : forall (P : acs -> Prop) (b : bool) (s : acs) (r : option acs) (ch : acs),
  P s -> (r = Some ch -> P ch) -> (if b then Some s else r) = Some ch -> P ch.
Proof. intros P b s r ch Ps Pr H. destruct b; [injection H as <-; exact Ps | exact (Pr H)]. Qed.

Lemma HS_asan_ok : forall h ch, HS_asan h = Some ch -> hs_all_ok ch = true.
Proof.
  intros h ch. unfold HS_asan.
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_3000|].
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_2000|].
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_1000|].
  apply (hs_if_some_ok (fun c => hs_all_ok c = true)); [exact hs_ok_0| discriminate].
Qed.

(* [comment removed for export] *)
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem s3s_A : fuzz_one_cps RTA LIB_A -> rt_contracts RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) ->
  S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  intros FZ RC IOC.
  exact (s3s_A_of IT0 IT0_ok HS_asan startup_plan startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_asan_ok FZ RC IOC).
Qed.


(* [comment removed for export] *)
Theorem s3s_A_rc : fuzz_one_cps RTA LIB_A -> rt_contracts RTA ->
  S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof. intros FZ RC. exact (s3s_A FZ RC rta_io). Qed.


(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_state RT_rep RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_malsec RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin RT_freeFin RT_dsec.
Theorem s3s_B9_of_cone : fuzz_one_cps RTA LIB_A ->
  S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  intros FZ. exact (s3s_A_rc FZ (rta_contracts (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
                   (rta_free (drain_ok fixed_commit_ok ((fun MN AN p HOK => item_sec_ok p MN AN HOK) munmap_ok madvise_ok)) fixed_commit_ok))).
Qed.
