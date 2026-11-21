(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the stage-1 certificate for every CONFIG_RSEQ value, joined from Cert/S1AsanR0.v and Cert/S1AsanR1.v and stated over their own instruction table and shape: the recorded plan renumbered where it is checked, its hand-off states and shape computed in the build). *)

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0qZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0qZ.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cert Require Export S1AsanD S1AsanH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cert Require Import S1AsanR0 S1AsanR1.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
(* the instruction table and shape of the certificates Cert/S1AsanR0.v and Cert/S1AsanR1.v themselves, so the
   lemma below is stated in exactly their form: its proof applies them with no conversion that unfolds the table *)
Abbreviation IT1 := jo6_IT1c.
Abbreviation jo6_startup1s_shape := jo6_s1_shape.
Lemma jo6_startup1s_cert : forall b : bool,
check JO6SEGS IT1 AJO6 NX0 LIMIT (rseq_z b) (XNjo6 JO6SEGS NX0) XE0 XB0 (HS1s (rseq_z b)) KC0 BFUEL FUEL None (ajo_init (rseq_z b)) (jo6_startup1s (rseq_z b)) = COk jo6_startup1s_shape.
Proof. intros [|]; [exact jo6_s1_cert_1 | exact jo6_s1_cert_0]. Qed.
