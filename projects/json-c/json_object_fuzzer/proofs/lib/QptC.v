(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the stage-2B certificate per CONFIG_RSEQ value, from the computed stage-1 hand-off state at 6 to the computed main-entry states, for the renumbered recorded plan; its shape computed by the collecting run). *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7Cy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7Cy.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyaF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyaF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXVi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFMt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFMt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0qZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0qZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJQc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJQc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cert Require Import S1BothH.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".

Definition IT2 : itab := mk_itab_ranges JOB6SEGS job6_stage2b_ranges.
Definition NX1 (r : Z) : nat := match HS1s r 6%nat with Some c => nxt c | None => 0%nat end.
Definition CS1 (r : Z) : acs := match HS1s r 6%nat with Some c => c | None => bjo_init r end.
Definition job6_stage2sB_shape : shape := Eval vm_compute in job6_s2b_shape.

Lemma job6_stage2sB_cert_0 :
check JOB6SEGS IT2 BJO6 (NX1 0) LIMIT 0 (XNjob6 JOB6SEGS (NX1 0)) XE0 XB0 (HS2sB 0) KC0 BFUEL FUEL None (CS1 0) job6_stage2b = COk job6_stage2sB_shape.
Proof. ltac2:(cert_refl_vm constr:(COk job6_stage2sB_shape)). Qed.
Lemma job6_stage2sB_cert_1 :
check JOB6SEGS IT2 BJO6 (NX1 1) LIMIT 1 (XNjob6 JOB6SEGS (NX1 1)) XE0 XB0 (HS2sB 1) KC0 BFUEL FUEL None (CS1 1) job6_stage2b = COk job6_stage2sB_shape.
Proof. ltac2:(cert_refl_vm constr:(COk job6_stage2sB_shape)). Qed.

Lemma job6_stage2sB_cert : forall b : bool,
check JOB6SEGS IT2 BJO6 (NX1 (rseq_z b)) LIMIT (rseq_z b) (XNjob6 JOB6SEGS (NX1 (rseq_z b))) XE0 XB0 (HS2sB (rseq_z b)) KC0 BFUEL FUEL None (CS1 (rseq_z b)) job6_stage2b = COk job6_stage2sB_shape.
Proof. intros [|]; [exact job6_stage2sB_cert_1 | exact job6_stage2sB_cert_0]. Qed.
