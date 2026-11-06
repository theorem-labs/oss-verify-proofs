(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegCall.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import PA2_surv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Section T.
Variable segs : list Segment.

Lemma know_transport : forall (kn knD EXTRA : list kentry) (sg : list expr) (PR : option (list SC.wn)) (E : env) (m m' : word -> option byte),
  know_ok segs E m kn ->
  (forall x : word, SC.in_PR E PR (bv_unsigned x) -> m' x = m x) ->
  know_ok segs E m' EXTRA ->
  incl_kn (map (ST.ksub sg) knD) (List.filter (survivesQ kn PR) kn ++ EXTRA) = true ->
  know_ok segs (ST.senv E sg) m' knD.
Proof.
  intros kn knD EXTRA sg PR E m m' HK FR HX HI.
  apply ST.know_ok_ksub. eapply know_ok_incl; [| exact HI].
  unfold know_ok. apply Forall_app. split; [exact (survivesQ_all_ok segs E m m' kn PR HK FR) | exact HX].
Qed.
End T.
