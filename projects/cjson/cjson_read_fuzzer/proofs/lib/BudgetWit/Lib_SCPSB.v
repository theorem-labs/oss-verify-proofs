(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Lib/SCPS.v: rz_rt_msteps and rz_evt restated over BudgetWit.Rzb.rzb, with their released proofs. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import MState Mem Exec SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.BudgetWit Require Import Rzb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.

Section WithSegs.
Variable segs : list Segment.

Lemma rzb_rt_msteps : forall ms ms' mo T,
  MOK mo ->
  Exec.msteps segs ms ms' ->
  rzb segs (mkCfg ms' mo) T ->
  rzb segs (mkCfg ms mo) T.
Proof.
  intros ms ms' mo T [Hh Hl] Hms.
  induction Hms as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH]; intro Hc; [exact Hc|].
  eapply rzb_step; [exact Hh | exact Hl | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

Lemma rzb_evt : forall (Q : machine_state -> Prop) ms mo T,
  MOK mo ->
  evt segs Q ms ->
  (forall ms', Q ms' -> rzb segs (mkCfg ms' mo) T) ->
  rzb segs (mkCfg ms mo) T.
Proof.
  intros Q ms mo T HM (ms' & Hms & HQ) K.
  eapply rzb_rt_msteps; [exact HM | exact Hms | apply K; exact HQ].
Qed.

End WithSegs.
