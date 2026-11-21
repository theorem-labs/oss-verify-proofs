(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  TreeModel FillWinModel SendModel BitsModel RefFlushPend1 .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition dstatus_ok (st : Z) : Prop :=
  st = 42 \/ st = 57 \/ st = 69 \/ st = 73 \/ st = 91 \/ st = 103 \/ st = 113 \/ st = 666.

Lemma deflateStateCheck_ok : forall s, deflateStateCheck s = false <-> dstatus_ok (ds_status s).
Proof.
  intros s. unfold deflateStateCheck, dstatus_ok, INIT_STATE, GZIP_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE, BUSY_STATE, FINISH_STATE.
  rewrite Bool.negb_false_iff, !Bool.orb_true_iff, !Z.eqb_eq. tauto.
Qed.


