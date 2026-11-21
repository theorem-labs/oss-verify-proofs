(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the stage-2A certificate per CONFIG_RSEQ value, from the computed stage-1 hand-off state at 0 to the computed main-entry states, for the renumbered recorded plan; its shape computed by the collecting run). *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7Cy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7Cy.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqQB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqQB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0qZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0qZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cert Require Import S1AsanH.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".

Definition IT2 : itab := mk_itab_ranges JO6SEGS jo6_stage2_ranges.
Definition NX1 (r : Z) : nat := match HS1s r 0%nat with Some c => nxt c | None => 0%nat end.
Definition CS1 (r : Z) : acs := match HS1s r 0%nat with Some c => c | None => ajo_init r end.
Definition jo6_stage2sA_shape : shape := Eval vm_compute in jo6_s2a_shape.

Lemma jo6_stage2sA_cert_0 :
check JO6SEGS IT2 AJO6 (NX1 0) LIMIT 0 (XNjo6 JO6SEGS (NX1 0)) XE0 XB0 (HS2sA 0) KC0 BFUEL FUEL None (CS1 0) jo6_stage2 = COk jo6_stage2sA_shape.
Proof. ltac2:(cert_refl_vm constr:(COk jo6_stage2sA_shape)). Qed.
Lemma jo6_stage2sA_cert_1 :
check JO6SEGS IT2 AJO6 (NX1 1) LIMIT 1 (XNjo6 JO6SEGS (NX1 1)) XE0 XB0 (HS2sA 1) KC0 BFUEL FUEL None (CS1 1) jo6_stage2 = COk jo6_stage2sA_shape.
Proof. ltac2:(cert_refl_vm constr:(COk jo6_stage2sA_shape)). Qed.

Lemma jo6_stage2sA_cert : forall b : bool,
check JO6SEGS IT2 AJO6 (NX1 (rseq_z b)) LIMIT (rseq_z b) (XNjo6 JO6SEGS (NX1 (rseq_z b))) XE0 XB0 (HS2sA (rseq_z b)) KC0 BFUEL FUEL None (CS1 (rseq_z b)) jo6_stage2 = COk jo6_stage2sA_shape.
Proof. intros [|]; [exact jo6_stage2sA_cert_1 | exact jo6_stage2sA_cert_0]. Qed.
