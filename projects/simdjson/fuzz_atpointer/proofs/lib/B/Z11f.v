(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up per CONFIG_RSEQ value and the new auxv layout). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import AsanUbsan.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z2z Z2y Z3h Z3e
  Z10h PlanRegen Z10s Z10sr Z7d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Zks Zkt RT_rep Z7w Z11d RT_io Z11e TopA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib Require Import TopLevelA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib Require Import ProofBase.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib Require Spec.Zg1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.

(* ONE EVALUATION PER CLOSED FLAG VALUE, joined by [destruct b]; image B's twin of A/Z11a.v.

   The hand-off states are computed in the build, once per value [r] of the launch's
   CONFIG_RSEQ flag ([AS/Z10sr.v]: [HS_both_r r], listed by [HS_list_rB r]), and [hs_all_ok r]
   reads the flag too: the auxv's size is [AUXSZ r = 432 + 32 * r].  [vm_cast_no_check]
   casts an [eq_refl] through [vm_compute], so each evaluation is at one closed [r]; both are
   made, so a caller at whatever [kb_rseq] the run's kernel gives has its evaluation. *)
Lemma hs_ok_r0 : forallb (hs_all_ok 0) (HS_list_rB 0) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_ok_r1 : forallb (hs_all_ok 1) (HS_list_rB 1) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma HS_both_ok : forall (b : bool) h ch, HS_both_r (rseq_z b) h = Some ch -> hs_all_ok (rseq_z b) ch = true.
Proof.
  intros b h ch H. apply HS_both_r_In in H.
  assert (F : forallb (hs_all_ok (rseq_z b)) (HS_list_rB (rseq_z b)) = true)
    by (destruct b; [exact hs_ok_r1 | exact hs_ok_r0]).
  exact (proj1 (forallb_forall _ _) F ch H).
Qed.

Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. reflexivity. Qed.

Section Client.

Variable CL : client_B.
Hypothesis HS_cl : forall (b : bool) h ch, HS_both_r (rseq_z b) h = Some ch -> cl_hs_ok CL ch = true.

Theorem s3s_B : rt_contracts2 RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) ->
  S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof using HS_cl.
  intros RC IOC.
  exact (s3s_A_of IT0 IT0_ok HS_both_r startup_plan_rB startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_both_ok CL HS_cl RC IOC).
Qed.

Theorem base_both_of : rt_contracts2 RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) -> impl_P_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof using HS_cl.
  intros RC IOC HP.
  exact (base_asan_of_cert IT0 IT0_ok HS_both_r startup_plan_rB startup_shape KC0 BFUEL FUEL startup_cert startup_shape_holes HS_both_ok CL HS_cl
           RC IOC HP Spec.Zg1.prog_no_enomem_P).
Qed.

Theorem s3s_B_rc : rt_contracts2 RTA ->
  S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof using HS_cl. intros RC. exact (s3s_B RC rta_io). Qed.

Theorem base_both_rc : rt_contracts2 RTA -> impl_P_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof using HS_cl. intros RC HP. exact (base_both_of RC rta_io HP). Qed.
End Client.
