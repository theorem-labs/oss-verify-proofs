(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from QS9D.v and Q72M.v: the ASan stage-2B collecting runs per CONFIG_RSEQ value, from the computed stage-1 hand-off state at 6 (Cert/S1AsanH.v), of the renumbered recorded plan (Q0qZ.v). *)
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cert Require Import S1AsanH.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* stage 2B starts at the stage-1 hand-off state at 6, with its counter as the first fresh variable *)
Definition jo6_s2b_nx (r : Z) : nat := match HS1s r 6%nat with Some c => nxt c | None => 0%nat end.
Definition jo6_s2b_cs (r : Z) : acs := match HS1s r 6%nat with Some c => c | None => ajo_init r end.
Definition jo6_IT2bc : itab := mk_itab_ranges JO6SEGS Q0qZ.Mq2.jo6_stage2b_ranges.
(* the stage-2B check at CONFIG_RSEQ value [r], run with no hand-off table *)
Definition jo6_s2b_col (r : Z) : cres2 :=
  collect JO6SEGS jo6_IT2bc AJO6 (jo6_s2b_nx r) QVWI.Mq0.LIMIT r (XNjo6 JO6SEGS (jo6_s2b_nx r)) QVWI.Mq0.XE0 QVWI.Mq0.XB0
    (fun _ => None) QVWI.Mq0.KC0 QVWI.Mq0.BFUEL QVWI.Mq0.FUEL None (jo6_s2b_cs r) Q0qZ.Mq2.jo6_stage2b.
(* the meets of the states each run reaches at hand-offs 3 and 4, and its shape, at CONFIG_RSEQ 0 and 1 *)
Definition jo6_s2b_coll_0 : option acs * option acs * shape := Eval vm_compute in coll2 (jo6_s2b_col 0) 3 4.
Definition jo6_s2b_coll_1 : option acs * option acs * shape := Eval vm_compute in coll2 (jo6_s2b_col 1) 3 4.
