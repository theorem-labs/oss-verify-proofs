(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape AEvt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import DivergeSim SpinAlg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import SRz.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Export SRz.

Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AEvtS () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "WithSegs.aevtS"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "Corelib.Init.Logic.eq"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Run.SError"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.LibA.SRz.spinningJ"; "OSSVerify.KrLib.Lib.Shape.TSet"; "LinuxProcessSemantics.LinuxProcessSem.Run.is_prefix"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.Lib.Shape.t_emit"; "OSSVerify.KrLib.ABoot.SpinAlg.srealizes"; "OSSVerify.KrLib.LibA.SRz.srealizesJ"].


Section WithSegs.
Variable segs : list Segment.

Abbreviation spinningS := (spinningJ segs).

Inductive aevtS (Q : config -> Prop) : config -> Prop :=
| aevtS_now : forall c, Q c -> aevtS Q c
| aevtS_step : forall c,
    (exists c', sstep segs c [] (SNext c') /\ aevtS Q c') ->
    (forall e st, sstep segs c e st -> e = [] /\ st <> SError) ->
    (forall e c', sstep segs c e (SNext c') -> aevtS Q c' \/ (spinningS c' /\ fo_excusedJ segs c e c')) ->
    aevtS Q c.

(* [comment removed for export] *)
#[using="Type"] Lemma aevtS_ind2 : forall (Q : config -> Prop) (P : config -> Prop),
  (forall c, Q c -> P c) ->
  (forall c,
      (exists c', sstep segs c [] (SNext c') /\ aevtS Q c' /\ P c') ->
      (forall e st, sstep segs c e st -> e = [] /\ st <> SError) ->
      (forall e c', sstep segs c e (SNext c') -> (aevtS Q c' /\ P c') \/ (spinningS c' /\ fo_excusedJ segs c e c')) ->
      P c) ->
  forall c, aevtS Q c -> P c.
Proof.
  intros Q P Hnow Hstep.
  fix IH 2. intros c H. destruct H as [c HQ | c Hw Hsil Hall].
  - apply Hnow. exact HQ.
  - apply Hstep.
    + destruct Hw as (c' & Hs & Ha). exists c'. split; [exact Hs|]. split; [exact Ha|]. exact (IH c' Ha).
    + exact Hsil.
    + intros e c' Hs. destruct (Hall e c' Hs) as [Ha | Hsp]; [left | right; exact Hsp].
      split; [exact Ha | exact (IH c' Ha)].
Qed.

#[using="Type"] Lemma aevtS_mono : forall (P Q : config -> Prop) c,
  aevtS P c -> (forall c', P c' -> Q c') -> aevtS Q c.
Proof.
  intros P Q c H K. revert c H. apply aevtS_ind2.
  - intros c HP. apply aevtS_now. apply K, HP.
  - intros c (c' & Hs & _ & IH') Hsil Hall. apply aevtS_step; [exists c'; split; assumption | exact Hsil |].
    intros e c'' Hs''. destruct (Hall e c'' Hs'') as [[_ IH''] | Hsp]; [left; exact IH'' | right; exact Hsp].
Qed.

#[using="Type"] Lemma aevtS_bind : forall (P Q : config -> Prop) c,
  aevtS P c -> (forall c', P c' -> aevtS Q c') -> aevtS Q c.
Proof.
  intros P Q c H K. revert c H. apply aevtS_ind2.
  - intros c HP. apply K, HP.
  - intros c (c' & Hs & _ & IH') Hsil Hall. apply aevtS_step; [exists c'; split; assumption | exact Hsil |].
    intros e c'' Hs''. destruct (Hall e c'' Hs'') as [[_ IH''] | Hsp]; [left; exact IH'' | right; exact Hsp].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aevtS_of_aevt : forall Q c, aevt segs Q c -> aevtS Q c.
Proof.
  intros Q c H. induction H as [c HQ | c Hprog Hsil Hk IH].
  - apply aevtS_now. exact HQ.
  - destruct Hprog as [c' Hs]. apply aevtS_step; [ | exact Hsil |].
    + exists c'. split; [exact Hs | exact (IH _ _ Hs)].
    + intros e c'' Hs''. left. exact (IH _ _ Hs'').
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aevtS_step_spin : forall Q c c1,
  sstep segs c [] (SNext c1) -> aevtS Q c1 ->
  (forall e st, sstep segs c e st -> e = [] /\ st <> SError) ->
  (forall e c', sstep segs c e (SNext c') -> aevtS Q c' \/ (spinningS c' /\ fo_excusedJ segs c e c')) ->
  aevtS Q c.
Proof. intros Q c c1 Hs H1 Hsil Hall. apply aevtS_step; [exists c1; split; assumption | exact Hsil | exact Hall]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma t_emit_nil_l : ltac2:(CDefT.buildp (gd_tbl_AEvtS ()) "PT,$?.Ptr,(8.$5.)P,A1.R2.(4.$5.)P,Ptr,(8.$5.)Ptr',(8.$5.)P,A1.R5.R2.P,(10.$5.R2.R3.)A1.R7.R3.(11.(12.(4.$5.)R4.R3.)A1.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros T tr Hnil Hpc. unfold t_emit. split.
  - intros [Hp | (tr0 & -> & H0)]; [| exact H0].
    apply is_prefix_nil_inv in Hp. subst tr. exact Hnil.
  - intros H. right. exists tr. split; [reflexivity | exact H].
Qed.

#[using="Type"] Theorem srz_of_aevtS : ltac2:(CDefT.buildp (gd_tbl_AEvtS ()) "PQ,P,$0.SpPc,$0.PT,$?.P,(7.R3.R2.)P,A1.R2.(4.$5.)P,Pc',$0.P,A1.R6.R1.(13.Vsegs,R2.R5.)(13.Vsegs,R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros Q c T H Hnil K. revert c H. apply aevtS_ind2.
  - intros c HQ. apply K, HQ.
  - intros c (c1 & Hs1 & _ & IH1) Hsil Hall.
    set (I := { c' : config | sstep segs c [] (SNext c') }).
    assert (Hnode : ShapeAlg.node_ok segs c I (fun _ => []) (fun i => proj1_sig i)).
    { split.
      - intros [c' Hc']. exact Hc'.
      - intros e st Hs. destruct (Hsil e st Hs) as [-> Hne].
        destruct st as [c'|]; [|congruence].
        exists (exist _ c' Hs). split; reflexivity. }
    (* [comment removed for export] *)
    set (Ti := fun (i : I) (tr : list event) => (srealizes segs (proj1_sig i) T /\ T tr) \/ tr = []).
    assert (PC : forall tr tr', T tr -> is_prefix tr' tr -> T tr').
    { intros tr tr' Htr Hp. eapply (srealizes_pclosed segs c1 T IH1); eauto. }
    eapply srz_conseq.
    + apply (srz_node_sp segs c I (fun _ => []) (fun i => proj1_sig i) Ti (exist _ c1 Hs1) Hnode).
      intros [c' Hc']. cbn [proj1_sig].
      destruct (Hall [] c' Hc') as [[_ IH'] | [Hsp Hex]].
      * (* [comment removed for export] *)
        left. eapply srz_conseq; [exact IH'|]. intros tr. unfold Ti. cbn [proj1_sig]. split.
        -- intros Htr. left. split; [exact IH' | exact Htr].
        -- intros [[_ Htr] | ->]; [exact Htr | exact Hnil].
      * (* [comment removed for export] *)
        right. split; [| exact (fo_excusedJ_not_fo_step segs _ _ _ Hex)].
        eapply srz0_conseq; [apply srzJ0_srz0; apply srzJ0_spin; exact Hsp|]. intros tr. unfold Ti, ShapeAlg.t_nil. cbn [proj1_sig]. split.
        -- intros ->. right. reflexivity.
        -- intros [[Hsr Htr] | ->]; [| reflexivity].
           pose proof (proj2 (srealizes_obs_iff segs _ _ Hsr tr) Htr) as OB.
           pose proof (proj1 (srealizes0_obs_iff segs _ _ (srzJ0_srz0 segs _ _ (srzJ0_spin segs _ Hsp)) tr) OB) as NT. exact NT.
    + (* [comment removed for export] *)
      intros tr. unfold ShapeAlg.t_alt, Ti. split.
      * intros ([c' Hc'] & Hem). cbn [proj1_sig] in Hem.
        unfold ShapeAlg.t_emit in Hem. destruct Hem as [Hp | (tr0 & -> & [[_ Htr] | ->])].
        -- apply is_prefix_nil_inv in Hp. subst tr. exact Hnil.
        -- exact Htr.
        -- exact Hnil.
      * intros Htr. exists (exist _ c1 Hs1). cbn [proj1_sig]. unfold ShapeAlg.t_emit. right. exists tr. split; [reflexivity|].
        left. split; [exact IH1 | exact Htr].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Theorem srzJ_of_aevtS : ltac2:(CDefT.buildp (gd_tbl_AEvtS ()) "PQ,P,$0.SpPc,$0.PT,$?.P,(7.R3.R2.)P,A1.R2.(4.$5.)P,Pc',$0.P,A1.R6.R1.(14.Vsegs,R2.R5.)(14.Vsegs,R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros Q c T H Hnil K. revert c H. apply aevtS_ind2.
  - intros c HQ. apply K, HQ.
  - intros c (c1 & Hs1 & _ & IH1) Hsil Hall.
    set (I := { c' : config | sstep segs c [] (SNext c') }).
    assert (Hnode : node_ok segs c I (fun _ => []) (fun i => proj1_sig i)).
    { split.
      - intros [c' Hc']. exact Hc'.
      - intros e st Hs. destruct (Hsil e st Hs) as [-> Hne].
        destruct st as [c'|]; [|congruence].
        exists (exist _ c' Hs). split; reflexivity. }
    set (Ti := fun (i : I) (tr : list event) => (srealizesJ segs (proj1_sig i) T /\ T tr) \/ tr = []).
    eapply srzJ_conseq.
    + apply (srzJ_node_sp segs c I (fun _ => []) (fun i => proj1_sig i) Ti (exist _ c1 Hs1) Hnode).
      intros [c' Hc']. cbn [proj1_sig].
      destruct (Hall [] c' Hc') as [[_ IH'] | [Hsp Hex]].
      * left. eapply srzJ_conseq; [exact IH'|]. intros tr. unfold Ti. cbn [proj1_sig]. split.
        -- intros Htr. left. split; [exact IH' | exact Htr].
        -- intros [[_ Htr] | ->]; [exact Htr | exact Hnil].
      * right. split; [| exact Hex]. eapply srzJ0_conseq; [apply srzJ0_spin; exact Hsp|]. intros tr. unfold Ti, t_nil. cbn [proj1_sig]. split.
        -- intros ->. right. reflexivity.
        -- intros [[Hsr Htr] | ->]; [| reflexivity].
           pose proof (proj2 (srzJ_obs_iff segs _ _ Hsr tr) Htr) as OB.
           exact (proj1 (srzJ0_obs_iff segs _ _ (srzJ0_spin segs _ Hsp) tr) OB).
    + intros tr. unfold t_alt, Ti. split.
      * intros ([c' Hc'] & Hem). cbn [proj1_sig] in Hem.
        unfold t_emit in Hem. destruct Hem as [Hp | (tr0 & -> & [[_ Htr] | ->])].
        -- apply is_prefix_nil_inv in Hp. subst tr. exact Hnil.
        -- exact Htr.
        -- exact Hnil.
      * intros Htr. exists (exist _ c1 Hs1). cbn [proj1_sig]. unfold t_emit. right. exists tr. split; [reflexivity|].
        left. split; [exact IH1 | exact Htr].
Qed.

End WithSegs.
