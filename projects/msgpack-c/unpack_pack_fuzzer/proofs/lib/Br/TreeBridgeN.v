(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes NodesM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue TreeBridge NodeSound.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Import ShapeAlg(TSet, t_eq, t_alt, t_alt2, t_emit, t_nil, realizes, node_ok).
Open Scope bv_scope.
Unset Lia Cache.

Section WithSegs.
Variable segs : list Segment.

Definition NmodelM := mm_model.
Definition NsoundM := mm_sound segs.
Definition NcompleteM := mm_complete segs.
Definition NprogressM := mm_progress.

Lemma twf_TB : forall {R} (t : itree node R) mo P, MSafe.twf t mo P -> TreeBridge.twf nstep nsafe t mo P.
Proof.
  intros R t. induction t as [r | n k IH]; intros mo P H; cbn in *; [exact H|].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk. exact Hst.
Qed.

Definition mpath {St A} (c : M St A) (s : St) (mo : Model) (a : A) (s' : St) (mo' : Model) : Prop :=
  tpath nstep (c s) mo [] (Ok (a, s')) mo'.

Theorem implM_mspec_realizes {St A} : forall (c : M St A) (s : St) POST (Pm : assn St) Qm ms mo (Kof : A -> St -> TSet),
  implM segs c s POST ms ->
  mspec Pm c Qm -> Pm s mo ->
  mo_ok mo ->
  (forall a s' ms' mo', POST a s' ms' -> Qm a s' mo' -> mpath c s mo a s' mo' -> mo_ok mo' -> vm_agree mo mo' ->
     realizes segs (mkCfg ms' mo') (Kof a s')) ->
  realizes segs (mkCfg ms mo) (fun tr => exists a s' mo', mpath c s mo a s' mo' /\ Kof a s' tr).
Proof.
  intros c s POST Pm Qm ms mo Kof Himpl Hspec HP Hmo HK.
  pose proof (twf_TB _ _ _ (Hspec s mo HP)) as Htwf.
  eapply ShapeAlg.rz_conseq.
  - apply (impl_twf_realizes' segs (at_node segs) nstep nsafe NmodelM NsoundM NcompleteM NprogressM
             (c s) _ _ ms mo
             (fun r => match r with Ok p => Kof (fst p) (snd p) | Unr => t_nil end) Himpl Htwf Hmo).
    intros [|[a s']] ms' mo' HQ HPm Hp Hmo' Hva; cbn in HQ, HPm; [destruct HPm|].
    cbn. apply (HK a s' ms' mo' HQ HPm Hp Hmo' Hva).
  - intros tr. unfold t_paths, mpath. split.
    + intros (r & mo' & Hp & Htr). destruct r as [|[a s']].
      * exfalso.
        revert Hp. generalize (c s) Htwf. clear. intros t Ht Hp.
        assert (G : forall R (t : itree node R) mo P tr r mo', TreeBridge.twf nstep nsafe t mo P -> tpath nstep t mo tr r mo' -> P r mo').
        { intros R t0. induction t0 as [r0 | n k IH]; intros mo0 P tr0 r mo0' H Hq; cbn in *.
          - destruct Hq as (<- & -> & _). exact H.
          - destruct H as [_ Hk]. destruct Hq as (rsp & mo1 & evs & tr' & Hst & Hq & _). eapply IH; [eapply Hk; exact Hst | exact Hq]. }
        exact (G _ _ _ _ _ _ _ Ht Hp).
      * exists a, s', mo'. split; [exact Hp | exact Htr].
    + intros (a & s' & mo' & Hp & Htr). exists (Ok (a, s')), mo'. split; [exact Hp | exact Htr].
Qed.

Theorem implM_mspec_realizes_silent {St A} : forall (c : M St A) (s : St) POST (Pm : assn St) Qm ms mo (K : TSet),
  implM segs c s POST ms ->
  mspec Pm c Qm -> Pm s mo ->
  mo_ok mo ->
  (forall a s' ms' mo', POST a s' ms' -> Qm a s' mo' -> mpath c s mo a s' mo' -> mo_ok mo' -> vm_agree mo mo' ->
     realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros c s POST Pm Qm ms mo K Himpl Hspec HP Hmo HK.
  pose proof (twf_TB _ _ _ (Hspec s mo HP)) as Htwf.
  apply (impl_twf_realizes_silent segs (at_node segs) nstep nsafe NmodelM NsoundM NcompleteM NprogressM
           (c s) _ _ ms mo K Himpl Htwf Hmo).
  intros [|[a s']] ms' mo' HQ HPm Hp Hmo' Hva; cbn in HQ, HPm; [destruct HPm|].
  apply (HK a s' ms' mo' HQ HPm Hp Hmo' Hva).
Qed.

Theorem implM_mspec_realizes_alt2 {St A} : forall (c : M St A) (s : St) POST (Pm : assn St) Qm ms mo
    (cls : A -> bool) (KA KB : TSet),
  implM segs c s POST ms ->
  mspec Pm c Qm -> Pm s mo ->
  mo_ok mo ->
  (exists a s' mo', mpath c s mo a s' mo' /\ cls a = false) ->
  (exists a s' mo', mpath c s mo a s' mo' /\ cls a = true) ->
  (forall a s' ms' mo', POST a s' ms' -> Qm a s' mo' -> mpath c s mo a s' mo' -> mo_ok mo' -> vm_agree mo mo' ->
     realizes segs (mkCfg ms' mo') (if cls a then KB else KA)) ->
  realizes segs (mkCfg ms mo) (t_alt2 KA KB).
Proof.
  intros c s POST Pm Qm ms mo cls KA KB Himpl Hspec HP Hmo (a1 & s1 & mo1 & Hp1 & Hc1) (a2 & s2 & mo2 & Hp2 & Hc2) HK.
  pose proof (twf_TB _ _ _ (Hspec s mo HP)) as Htwf.
  apply (impl_twf_realizes_alt2 segs (at_node segs) nstep nsafe NmodelM NsoundM NcompleteM NprogressM
           (c s) _ _ ms mo (fun r => match r with Ok p => cls (fst p) | Unr => false end) KA KB Himpl Htwf Hmo).
  - exists (Ok (a1, s1)), mo1. split; [exact Hp1 | exact Hc1].
  - exists (Ok (a2, s2)), mo2. split; [exact Hp2 | exact Hc2].
  - intros [|[a s']] ms' mo' HQ HPm Hp Hmo' Hva; cbn in HQ, HPm; [destruct HPm|].
    cbn. apply (HK a s' ms' mo' HQ HPm Hp Hmo' Hva).
Qed.

End WithSegs.
