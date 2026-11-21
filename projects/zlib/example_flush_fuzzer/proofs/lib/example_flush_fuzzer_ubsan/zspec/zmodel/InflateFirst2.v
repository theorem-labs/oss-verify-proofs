(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb ModelRel
  InflateInv InflateInvRun InflateInvTab InflateInvKit InflateInvApi InflateInvLoop InflateInvCall
  HarnessKit HarnessFacts InflateLeave InflateCall.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma NEEDBITS16_2 : forall s c po lf o,
  NEEDBITS 16 (mkW s c (mkIR 0 2 po lf 0 0 2 o Z_OK))
  = ARun tt (mkW s c (mkIR 2 0 po lf (wrap64 (wrap64 (0 + shl64 (arr_get (ic_input c) 0) 0) + shl64 (arr_get (ic_input c) 1) 8)) 16 2 o Z_OK)).
Proof. intros. unfold NEEDBITS. cbv -[wrap64 shl64 arr_get]. reflexivity. Qed.
Lemma NEEDBITS_noinput : forall n s c ni po lf h b i o rt, b < n ->
  NEEDBITS n (mkW s c (mkIR ni 0 po lf h b i o rt)) = ALeave (mkW s c (mkIR ni 0 po lf h b i o rt)).
Proof. intros. unfold NEEDBITS. cbn [NEEDBITS_k]. unfold abind, gr. cbn [w_r ir_bits]. replace (b <? n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Section S.
  Variable iv : ivariant.


  Ltac modesel :=
    cbn [Z.eqb Pos.eqb BAD HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE
         LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE MEM SYNC].
  Ltac next_dispatch :=
    rewrite (iterK_gstep_S iv Z_NO_FLUSH); unfold dispatch; wred; modesel.
  Ltac bad_tail := wred; next_dispatch; unfold arm_BAD; wred; split; [reflexivity | lia].


End S.

From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import HarnessSmallInfl.

