(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import ClassifierRows.
From OSSVerify.Proofs.openssl.bignum.lib Require Import TopE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Rows.
  Variable cfg : SpuriousCfg.
  Variable Tc : ProcInput -> list event -> Prop.
  Variables (imgS imgT : Image).
  Hypothesis HS : side_canon_off cfg Tc imgS source_alloc_limit.
  Hypothesis HT : side_canon_off cfg Tc imgT target_alloc_limit.

  Theorem row_ca_iff : forall O1 O2 C, O1 = imgS -> O2 = imgT -> accepts_all C ->
    classifies_good_inputs_T_s cfg O1 O2 C.
  Proof.
    intros O1 O2 C E1 E2 HC.
    exact (ca_iff_of_base_eq cfg imgS imgT O1 O2 C E1 E2 (glue_scfg cfg Tc imgS imgT HS HT) HC).
  Qed.

  Theorem row_cb_iff : forall O1 O2 C, O1 = imgS -> O2 = imgT ->
    image_brk_satisfiable (img_segments imgS) = true ->
    image_brk_satisfiable (img_segments imgT) = true ->
    accepts_all C ->
    classifies_patch_diff_T_s cfg O1 imgS O2 imgT C.
  Proof.
    intros O1 O2 C E1 E2 B1 B2 HC.
    exact (cb_iff_of_base_eq cfg imgS imgT O1 O2 C E1 E2 (glue_scfg cfg Tc imgS imgT HS HT) B1 B2 HC).
  Qed.
End Rows.

Theorem row_total : forall C, accepts_all C -> classifier_total_T_fo C.
Proof. exact total_of_accepts_all. Qed.
