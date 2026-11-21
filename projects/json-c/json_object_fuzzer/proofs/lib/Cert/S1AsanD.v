(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from QwDM.v: the ASan stage-1 check's instruction table and its collecting run of the renumbered recorded plan (Q0qZ.v), split from the per-CONFIG_RSEQ certificates so they build in parallel. *)
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVWI Q0qZ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cert Require Import PlanRegen.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition jo6_IT1c : itab := mk_itab_ranges JO6SEGS Q0qZ.Mq3.jo6_startup1s_ranges.
(* the stage-1 check of the renumbered plan at CONFIG_RSEQ value [r], run with no hand-off table:
   [QOTP.AP.collect] hands every state it reaches at a hand-off to its list *)
Definition jo6_s1_col (r : Z) : cres2 :=
  collect JO6SEGS jo6_IT1c AJO6 NX0 QVWI.Mq0.LIMIT r (XNjo6 JO6SEGS NX0) QVWI.Mq0.XE0 QVWI.Mq0.XB0 (fun _ => None)
    QVWI.Mq0.KC0 QVWI.Mq0.BFUEL QVWI.Mq0.FUEL None (ajo_init r) (Q0qZ.Mq4.jo6_startup1s r).
