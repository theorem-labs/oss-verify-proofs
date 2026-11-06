(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem3Run06config79OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach8WithSegs~~~~~~j46sreach37Corelib4Init9Datatypesnf3nil3h5LinuxProcessSemanticsfLinuxProcessSem5Statepd5event69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~t37node_oknf4unit37Corelib7Numbers7BinNumshhf4Npos35stdpp9bitvectorbdefinitionshk02bv37Corelib4Init5Logichm32eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshnddmachine_statenf4Nonenf6optionnf4prod05mkCfgnf4listhnd9MachineOkhndemachine_resulthndems_svc_pendinghnd4steppd5Modelpd8m_haltedpd9m_vm_lazy69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~ik26mstepst38realizest34TSet3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeip77Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hu3!isc@1$0$1").
Context {SC : StepCfg}.
(* [comment removed for export] *)
Let sstepc := sstep_cfg segs the_scfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sreach (Q : config -> Prop) : config -> Prop :=
| sr_done : forall c, Q c -> sreach Q c
| sr_step : forall c,
    (exists c', sstepc c [] (SNext c')) ->
    (forall evs X, sstepc c evs X -> evs = [] /\ exists c', X = SNext c') ->
    (forall evs c', sstepc c evs (SNext c') -> sreach Q c') ->
    sreach Q c.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sreach_done : ltac2:(zQ "20!ic!n6>1Q>0$0P>1c$0>0@1^2^1@2$1^3^2").
Proof. intros Q c H. apply sr_done. exact H. Qed.

Lemma sreach_mono : ltac2:(zQ "20!ic!n6>1Q>0$0P>2Q'>0$0P>1c$0>0@2$1^3^1>0>2c'$0>0@1^5^1@1^5^2@2$1^4^3").
Proof.
  intros Q Q' c H HQ. induction H as [c Hc | c Hprog Hall Hk IH].
  - apply sr_done. apply HQ. exact Hc.
  - apply sr_step; [exact Hprog | exact Hall |].
    intros evs c' Hss. exact (IH evs c' Hss).
Qed.

(* [comment removed for export] *)
Lemma sreach_seq : ltac2:(zQ "20!ic!n6>2Q1>0$0P>2Q2>0$0P>1c$0>0@2$1^3^1>0>2c'$0>0@1^5^1@2$1^5^2@2$1^4^3").
Proof.
  intros Q1 Q2 c H K. induction H as [c Hc | c Hprog Hall Hk IH].
  - apply K. exact Hc.
  - apply sr_step; [exact Hprog | exact Hall |].
    intros evs c' Hss. exact (IH evs c' Hss).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sreach_node : ltac2:(zQ "50!ic!n6!p7!sb!hge>1c$0>1IT>2nx>0^1$0>2i0^2>1Q>0$0P>0@6$4?4segs?2SC^5^4\0^4@1$2$3^3>0>1i^5@2$1^3@1^5^1@2$1^3^7").
Proof.
  intros c I nx i0 Q [Hcomp Hsound] Hk.
  apply sr_step.
  - exists (nx i0). apply (Hcomp i0).
  - intros evs X Hss. ndestruct (Hsound evs X Hss) as (i & -> & ->).
    split; [reflexivity|]. exists (nx i). reflexivity.
  - intros evs c' Hss. ndestruct (Hsound evs (SNext c') Hss) as (i & _ & E).
    injection E as ->. apply Hk.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sreach_silent1 : ltac2:(zQ "60!hh8!ic!n6!p7!sb!hge>1c$1>2c'$1>1Q>0$1P>0@6$5?4segs?2SC^3$0\0$0@1$3$4\0$0^3>0@2$2^2^3@2$2^3^5").
Proof. intros c c' Q Hn Hc. apply (sreach_node c unit (fun _ => c') tt Q Hn). intros []; exact Hc. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sreach_step1 : ltac2:(zQ "h31!hj8!hld!hn7!hr4!hs5!hsc!ht5!htc!n6!hu3!p7!hua!hv7!ig9!ihb!ic!ii3!iib!ij6&@2$6@1$1@1$0#k0@1$1@1$0#k0>2ms$3>5model$h0>3ms'$3>1Q>0$fP>0@3$2@1$5@1$1@1$0#k0@1$h1^3@1$4@1$1@1$0#k0>0@3$2@1$9~0@1$h2^4@1$a~0>0@3$2@1$5@1$1@1$0#k0@1$d^6@1$4@1$1@1$0#k0>0@3$2@1$c$3@2$e?4segs^7@2$b$3^5>0@2$8^5@2$7^6^7@2$8^6@2$7^9^8").
Proof.
  intros ms model ms' Q Hh Hlazy Hsvc Hstep Hc.
  eapply sreach_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma sreach_msteps : ltac2:(zQ "h01!hj8!hld!ht5!hn7!hr4!htc!n6!hs5!hu3!p7!hsc!ic!ii3!iib!ij6!inb&@2$2@1$1@1$0#k0@1$1@1$0#k0>2ms$4>3ms'$4>5model$c>1Q>0$bP>0@3$3@1$a@1$1@1$0#k0@1$d^2@1$7@1$1@1$0#k0>0@3$3@1$8~0@1$e^3@1$9~0>0@3$f?4segs^6^5>0@2$6^4@2$5^6^5@2$6^5@2$5^8^6").
Proof.
  intros ms ms' model Q Hh Hlazy Hms.
  induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intros Hc; [exact Hc|].
  eapply sreach_step1; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem sreach_realizes : ltac2:(zQ "40!ic!io5!n6!ip0>1Q>0$0P>1c$0>1T$3>0@2$2^3^2>0>2c'$0>0@1^5^1@4$1?4segs?2SC^2^4@4$1?4segs?2SC^4^3").
Proof.
  intros Q c T H K. induction H as [c Hc | c Hprog Hall Hk IH].
  - apply K. exact Hc.
  - destruct Hprog as [c1 Hc1].
    pose (I := {c' : config | sstepc c [] (SNext c')}).
    assert (Hnode : node_ok segs c I (fun _ => []) (fun i => proj1_sig i)).
    { split.
      - intros [c' Hc']. cbn. exact Hc'.
      - intros e st Hss. destruct (Hall e st Hss) as [-> (c' & ->)].
        exists (exist _ c' Hss). split; reflexivity. }
    assert (HT : forall i : I, realizes segs (proj1_sig i) T).
    { intros [c' Hc']. cbn. apply (IH [] c' Hc'). }
    assert (HT0 : T []) by (eapply realizes_nonempty; apply (HT (exist _ c1 Hc1))).
    apply (rz_conseq segs c (t_alt (fun _ : I => t_emit [] T))).
    + apply (rz_node segs c I (fun _ => []) (fun i => proj1_sig i) (fun _ => T) (exist _ c1 Hc1) Hnode HT).
    + intros tr. split.
      * intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
      * intros Htr. exists (exist _ c1 Hc1). exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

Arguments sreach segs {SC} Q c.
(* [comment removed for export] *)
