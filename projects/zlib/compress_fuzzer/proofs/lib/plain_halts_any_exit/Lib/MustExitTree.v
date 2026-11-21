(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import List ZArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Exec ITree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section MustExitTree.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Hypothesis NS : node_sound node segs at_node nstep nexit minv nsafe.
Variable S : list word.

Definition exits_ok : Prop :=
  forall n ms mo code mo', at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
    nexit n mo code mo' -> In code S /\ m_killed mo' = None.
Hypothesis EX : exits_ok.

Local Notation ME c := (must_exit_in_at segs S c).
Local Notation tree_at := (ITree.tree_at segs at_node nstep minv nsafe).

Lemma msteps_must_exit : forall ms ms1 mo,
  m_halted mo = None -> minv mo ->
  msteps segs ms ms1 -> ME (mkCfg ms1 mo) -> ME (mkCfg ms mo).
Proof.
  intros ms ms1 mo Hh Hinv Hm. induction Hm as [ms|ms msa msb Hstep Hrest IH]; intros Hend; [exact Hend|].
  pose proof (ns_lazy _ _ _ _ _ _ _ NS mo Hinv) as Hlz.
  apply must_exit_in_at_running.
  - exact Hh.
  - exists [], (SNext (mkCfg msa mo)). exact (mstep_sstep segs ms msa mo Hh Hlz Hstep).
  - intros evs Herr. destruct (sstep_mstep_inv segs ms mo msa evs SError Hlz Hstep Herr) as [_ H]. discriminate H.
  - intros evs c' Hss. destruct (sstep_mstep_inv segs ms mo msa evs (SNext c') Hlz Hstep Hss) as [_ H].
    injection H as ->. apply IH. exact Hend.
Qed.

Theorem tree_at_must_exit_in : forall (R : Type) (t : itree node R) Q ms mo,
  tree_at t Q ms mo -> ME (mkCfg ms mo).
Proof.
  intros R t. induction t as [r|n k IH]; intros Q ms mo HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret _ nstep r mo Hl).
  - pose proof HT as (Himpl & Hl & Hh & Hinv & Hsf).
    cbn [ITree.impl] in Himpl. destruct Himpl as (ms1 & Hrun & Hat & Hk).
    apply (msteps_must_exit ms ms1 mo Hh Hinv Hrun).

    apply must_exit_in_at_running.
    + exact Hh.
    + destruct (ns_progress _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hinv (proj1 Hsf)) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
      * destruct (ns_sound _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (_ & _ & Hss). eexists _, _. exact Hss.
      * destruct (ns_exit _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as [_ Hss]. eexists _, _. exact Hss.
    + intros evs Herr.
      destruct (ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs SError Hat Hh Hinv (proj1 Hsf) Herr)
        as [(rsp & mo' & HX & _)|(code & mo' & HX & _ & _)]; discriminate HX.
    + intros evs c' Hss.
      destruct (ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs (SNext c') Hat Hh Hinv (proj1 Hsf) Hss)
        as [(rsp & mo' & HX & Hst)|(code & mo' & HX & Hex & _)].
      * injection HX as ->.
        destruct (tree_at_step _ _ _ _ _ _ _ NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
        exact (IH rsp Q (nret ms1 rsp) mo' HT').
      * injection HX as ->.
        destruct (ns_exit _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as [Hh' _].
        destruct (EX n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as [Hin Hk0].
        apply (must_exit_in_at_halted segs S (mkCfg ms1 mo') code); [exact Hh'| exact Hin| exact Hk0].
Qed.
End MustExitTree.
