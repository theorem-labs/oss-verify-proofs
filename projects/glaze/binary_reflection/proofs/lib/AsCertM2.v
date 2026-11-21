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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupPlanS2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupPlanS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupPlanS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSa OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSb OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [r] threads in because the CHECKER itself takes it, not only the plans:
   cert_okS (r : Z) (IT) (HS) (cs) (p) at AsStartupTabs.v:158, over
   chkS r (:140), over XN_S r (:120), whose 207 and 208 arms are
   node_pnscan AT_A NXS r and node_layout r.  Without r the checker fails at
   AsCertM2.v:17:24-27 -- four columns, counted against the line, exactly
   the identifier IT1 -- "The term IT1 has type itab while it is expected
   to have type Z".

   TWO CLOSED INSTANTIATIONS, not one.  Run.valid_input leaves kb_rseq
   free, so pinning r to a single value would narrow the published claim
   (the no-narrowing ruling recorded on issue OSSV-142);
   quantifying over a free r : Z would leave the term open and vm_compute
   would not reduce it.  rseq_z is `if b then 1 else 0`
   (AzPlanCore.v:3603), so `intros [|]` leaves two CLOSED goals, each
   decided by the same reflective computation -- the shape rule 12
   licenses for an rseq-dependent layout, and the one AzPlanCore's own
   AUXSZ_of and rseq_z_range use.

   WHICH ARGUMENTS TAKE r, read off AsStartupTabs.v rather than applied
   uniformly: s1_q5 (:716), s1_q7 (:675) and s1_q11 (:619) are
   `Definition _ (r : Z) : plan`; s1_q17 (:415), s1_q18r (:336),
   s1_q18g (:339) and s1_q11b (:668) are `Definition _ : plan` and take
   NONE.  IT1 (:1007), T0 (:1024), T5bJ (:1026), T11_13b (:1019),
   T902/T903 (:1015,:1016) and every HS_* are r-free.

   COST: each lemma now runs its reflective check TWICE.  AsCertM2's whole
   build is measured at 483868 KiB / 1 s, so this file stays small; the same
   doubling on AsStartup.v's heavier certificates is the one to watch. *)
Lemma cert_2 : forall b : bool, cert_okS (rseq_z b) IT1 (T902 (rseq_z b)) (HS_901 (rseq_z b)) (s1_q5 (rseq_z b)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_3 : forall b : bool, cert_okS (rseq_z b) IT1 (T903 (rseq_z b)) (HS_902 (rseq_z b)) (s1_q7 (rseq_z b)) = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_5b : forall b : bool, cert_okS (rseq_z b) IT1 (T5bJ (rseq_z b)) (HS_916J (rseq_z b)) s1_q17 = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_5c : forall b : bool, cert_okS (rseq_z b) IT1 (T0 (rseq_z b)) (HS_917J (rseq_z b)) s1_q18r = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cert_5d : forall b : bool, cert_okS (rseq_z b) IT1 (T0 (rseq_z b)) (HS_918J (rseq_z b)) s1_q18g = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Lemma cert_4b : forall b : bool, cert_okS (rseq_z b) IT1 (T11_13b (rseq_z b)) (HS_904 (rseq_z b)) s1_q11b = true.
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
