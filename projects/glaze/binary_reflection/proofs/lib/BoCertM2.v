(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the certificates at both CONFIG_RSEQ values, over the plans renumbered for this revision and the hand-off states computed from them). *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupPlanS2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Twin of AsCertM2.v:17-62, with cert_okB for cert_okS.  The checker takes
   r: cert_okB (r : Z) (IT) (HS) (cs) (p) at BoStartupTabs.v:602, over
   chkB r (:600), over XN_B r (:584), whose 207 and 208 arms are
   node_pnscan AT_B NXS r and node_layout r.  The As copy's change
   (AsCertM2.v:17:24-27) is carried here as well: a build that stops
   before this file names only the As copy, and this twin left unchanged
   fails the same way once it is reached, as BoStartupTabs.v:841 does
   without AsSDefs's import.

   TWO CLOSED INSTANTIATIONS, not one -- see AsCertM2.v:25-33 for why a
   pinned r narrows and a free r : Z stops vm_compute.

   WHICH ARGUMENTS TAKE r, read off BoStartupTabs.v and not assumed from
   the As side: s1_q5 (:1143) and s1_q7 (:1102) are
   `Definition _ (r : Z) : plan`; s1_q17 (:842), s1_q18r (:763),
   s1_q18g (:766) and s1_q11b (:1095) take NONE.  IT1 (:1434),
   T902/T903 (:1442,:1443), T11_13b (:1446), T0 (:1451), T5bJ (:1453) and
   every HS_* are r-free. *)
Lemma cert_2 : forall b : bool, cert_okB (rseq_z b) IT1 (T902 (rseq_z b)) (HS_901 (rseq_z b)) (s1_q5 (rseq_z b)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_3 : forall b : bool, cert_okB (rseq_z b) IT1 (T903 (rseq_z b)) (HS_902 (rseq_z b)) (s1_q7 (rseq_z b)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_5b : forall b : bool, cert_okB (rseq_z b) IT1 (T5bJ (rseq_z b)) (HS_916J (rseq_z b)) s1_q17 = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_5c : forall b : bool, cert_okB (rseq_z b) IT1 (T0 (rseq_z b)) (HS_917J (rseq_z b)) s1_q18r = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_5d : forall b : bool, cert_okB (rseq_z b) IT1 (T0 (rseq_z b)) (HS_918J (rseq_z b)) s1_q18g = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Lemma cert_4b : forall b : bool, cert_okB (rseq_z b) IT1 (T11_13b (rseq_z b)) (HS_904 (rseq_z b)) s1_q11b = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
