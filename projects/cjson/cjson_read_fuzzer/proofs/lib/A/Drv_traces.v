(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs CJ_conv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition S_DRIVER : list (list Z) :=
  [[PC0_MALLOC; 0x81f0c]; [PC0_MALLOC; 0x81f60]; [PC0_MALLOC; 0x821ec];
   [PC0_FREE; 0x81f84]; [PC0_FREE; 0x820b4]; [PC0_FREE; 0x82280];
   [PC0_MALLOC]; [PC0_FREE]].

(* [comment removed for export] *)
Definition drv_traces_ok (TI : trs_iface) : Prop := forall tr, In tr S_DRIVER -> STAT TI tr.

(* [comment removed for export] *)
Lemma drv_ra_ok : forall pc0 ra, In [pc0; ra] S_DRIVER -> 4096 <= ra /\ ra <> PC0_MALLOC /\ ra <> PC0_FREE.
Proof.
  intros pc0 ra H. unfold S_DRIVER, PC0_MALLOC, PC0_FREE in *. cbn in H.
  repeat (destruct H as [H|H]; [first [injection H as <- <-; lia| discriminate H]|]). destruct H.
Qed.
