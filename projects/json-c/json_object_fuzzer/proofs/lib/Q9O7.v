(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the stage-1 certificate for every CONFIG_RSEQ value, joined from Cert/S1BothR0.v and Cert/S1BothR1.v and stated over their own instruction table and shape: the recorded plan renumbered where it is checked, its hand-off states and shape computed in the build). *)

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0qZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cert Require Export S1BothD S1BothH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cert Require Import S1BothR0 S1BothR1.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
(* the instruction table and shape of the certificates Cert/S1BothR0.v and Cert/S1BothR1.v themselves, so the
   lemma below is stated in exactly their form: its proof applies them with no conversion that unfolds the table *)
Abbreviation IT1 := job6_IT1c.
Abbreviation job6_startup1s_shape := job6_s1_shape.
Lemma job6_startup1s_cert : forall b : bool,
check JOB6SEGS IT1 BJO6 NX0 LIMIT (rseq_z b) (XNjob6 JOB6SEGS NX0) XE0 XB0 (HS1s (rseq_z b)) KC0 BFUEL FUEL None (bjo_init (rseq_z b)) (job6_startup1s (rseq_z b)) = COk job6_startup1s_shape.
Proof. intros [|]; [exact job6_s1_cert_1 | exact job6_s1_cert_0]. Qed.
