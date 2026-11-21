(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Q9O7.v and the recorded hand-off table of Q0qZ.v: the ASan+UBSan stage-1 hand-off states per CONFIG_RSEQ value, computed in the build (S1BothC0.v, S1BothC1.v) in place of the recorded ones, and the run's shape. *)
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVWI Q0qZ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cert Require Import PlanRegen.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cert Require Import S1BothC0 S1BothC1.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* the stage-1 hand-off states at 0 and 6 per CONFIG_RSEQ value, as the collecting runs computed them;
   written as a case on [h] first, so a proof about [HS1s r h] splits on [h], then on [Z.eqb r 1] *)
Definition HS1s (r : Z) (h : nat) : option acs :=
  match h with
  | 0%nat => if Z.eqb r 1 then fst (fst job6_s1_coll_1) else fst (fst job6_s1_coll_0)
  | 6%nat => if Z.eqb r 1 then snd (fst job6_s1_coll_1) else snd (fst job6_s1_coll_0)
  | _ => None
  end.

Lemma HS1s_dom : forall r h ch, HS1s r h = Some ch -> h = 0%nat \/ h = 6%nat.
Proof.
  intros r h ch H. destruct h as [|[|[|[|[|[|[|h]]]]]]]; cbv beta iota delta [HS1s] in H; try discriminate H;
  [left | right]; reflexivity.
Qed.

(* the run's shape at CONFIG_RSEQ value 0; the certificate at 1 is proved against the same shape *)
Definition job6_s1_shape : shape := Eval vm_compute in snd job6_s1_coll_0.
