(** * Bridge.Infl.ILoop — pair I3 of PAIRS.md: the [for (;;)] of [inflate], in lockstep.

    If RT's loop leaves with [Z_STREAM_END] after [k] trips, S5's loop run with any fuel of
    at least [k] leaves too, in a state related to RT's by [ifin].  A trip into BAD cannot
    be on the way: BAD's own trip leaves with [Z_DATA_ERROR].  S5's actual fuel is
    reconciled with [k] by [IFuelInfl.fuel_inf_loop] (group R) in [ITop]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl IRelInfl14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IStep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition is_bad (q : RI.InfSt) : bool :=
  match RI.q_mode q with RI.M_BAD => true | _ => false end.

Lemma bad_leaves : forall k c q r,
  is_bad q = true -> RI14.inf_loop14 k c q = Some r ->
  exists q', r = RI.InfLeave q' /\ RI.q_ret q' = RI.Z_DATA_ERROR.
Proof.
  intros [|k] c q r Hb Hl; [discriminate Hl|].
  rewrite RI14.inf_loop14_S in Hl. unfold RI14.inf_step14 in Hl. unfold is_bad in Hb.
  destruct (RI.q_mode q); try discriminate Hb.
  unfold RI.inf_BAD in Hl. injection Hl as <-. eexists. split; [reflexivity|]. reflexivity.
Qed.

Theorem loop_ok : forall k c q w qf,
  ctx_rel FL c -> inv w q ->
  RI14.inf_loop14 k c q = Some (RI.InfLeave qf) -> RI.q_ret qf = RBa.Z_STREAM_END ->
  forall n, Z.of_nat k <= n ->
  exists wf, inf_loop_n IS.ivar_ref FL n w = (IA.SLeave, wf) /\ ifin wf qf.
Proof.
  induction k as [|k IH]; intros c q w qf Hc Hi Hl Hret n Hn; [discriminate Hl|].
  pose proof (trip_ok c w q Hc Hi) as T.
  rewrite RI14.inf_loop14_S in Hl.
  unfold inf_loop_n. rewrite iterZ_step by lia.
  destruct (RI14.inf_step14 c q) as [q'|q'|q' rc|m|] eqn:Es; cbn [step_ok] in T.
  - destruct (is_bad q') eqn:Eb.
    + destruct (bad_leaves k c q' _ Eb Hl) as (q'' & Eq & Hr). injection Eq as <-.
      rewrite Hret in Hr. discriminate Hr.
    + assert (Hnb : RI.q_mode q' <> RI.M_BAD) by (unfold is_bad in Eb; intros E; rewrite E in Eb; discriminate Eb).
      destruct (T Hnb) as (w' & Ew & Hi').
      rewrite Ew.
      destruct (IH c q' w' qf Hc Hi' Hl Hret (n - 1) ltac:(lia)) as (wf & Ef & Hf).
      exists wf. split; [exact Ef | exact Hf].
  - injection Hl as <-. destruct (T Hret) as (w' & Ew & Hf).
    rewrite Ew. exists w'. split; [reflexivity | exact Hf].
  - discriminate Hl.
  - discriminate Hl.
  - discriminate Hl.
Qed.

(** A run from a related state never returns [Z_STREAM_END] past the epilogue. *)
Theorem loop_ret : forall k c q w q' rc,
  ctx_rel FL c -> inv w q -> RI14.inf_loop14 k c q = Some (RI.InfRet q' rc) -> rc <> RBa.Z_STREAM_END.
Proof.
  induction k as [|k IH]; intros c q w q' rc Hc Hi Hl; [discriminate Hl|].
  pose proof (trip_ok c w q Hc Hi) as T.
  rewrite RI14.inf_loop14_S in Hl.
  destruct (RI14.inf_step14 c q) as [q1|q1|q1 rc1|m|] eqn:Es; cbn [step_ok] in T.
  - destruct (is_bad q1) eqn:Eb.
    + destruct (bad_leaves k c q1 _ Eb Hl) as (q'' & Eq & _). discriminate Eq.
    + assert (Hnb : RI.q_mode q1 <> RI.M_BAD) by (unfold is_bad in Eb; intros E; rewrite E in Eb; discriminate Eb).
      destruct (T Hnb) as (w' & _ & Hi').
      exact (IH c q1 w' q' rc Hc Hi' Hl).
  - discriminate Hl.
  - injection Hl as <- <-. exact T.
  - discriminate Hl.
  - discriminate Hl.
Qed.
