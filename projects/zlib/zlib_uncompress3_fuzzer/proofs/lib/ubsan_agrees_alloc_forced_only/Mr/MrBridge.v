(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Exec ITree Nodes ITreeFO.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO Require FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Module B.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.ITree.

Section Bridge.
Variable segs : list Segment.
Variable node : Type.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Hypothesis NS : ITreeFO.node_sound_cfg FOCore.alloc_forced_cfg node segs at_node nstep nexit minv nsafe.

Lemma msteps_ut_ours : forall ms ms', Exec.msteps segs ms ms' -> CatSim.msteps segs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] _ IH].
  - apply mst_refl.
  - eapply mst_step; eassumption.
Qed.

Fixpoint tshape {R} (t : itree node R) (mo : Model) (K : R -> Model -> TSet) : TSet :=
  match t with
  | Ret r => K r mo
  | Vis n k => fun tr =>
      (exists rsp mo' evs, nstep n mo rsp mo' evs /\ t_emit evs (tshape (k rsp) mo' K) tr)
      \/ (exists code mo', nexit n mo code mo' /\ t_emit [ExitEv code (m_fs mo')] t_nil tr)
  end.

Fixpoint twf {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> twf (k rsp) mo' P
  end.

Theorem impl_realizes : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop)
    (K : R -> Model -> TSet) ms mo,
  @impl node segs at_node R t Q ms ->
  twf t mo P ->
  m_halted mo = None -> minv mo ->
  (forall r ms' mo', Q r ms' -> P r mo' -> m_halted mo' = None -> minv mo' ->
     realizes segs (mkCfg ms' mo') (K r mo')) ->
  realizes segs (mkCfg ms mo) (tshape t mo K).
Proof.
  intros R t. induction t as [r | n k IH]; intros Q P K ms mo Himpl Hwf Hh Hinv HK.
  - cbn in Himpl, Hwf |- *. destruct Himpl as (ms' & Hms & HQ).
    eapply rz_msteps; [exact Hh | exact (ITreeFO.nsc_nolazy _ _ _ _ _ _ _ _ NS mo Hinv) | apply msteps_ut_ours; exact Hms |].
    apply (HK r ms' mo HQ Hwf Hh Hinv).
  - cbn [impl] in Himpl. cbn [twf] in Hwf. destruct Hwf as [Hsafe Hwfk].
    destruct Himpl as (ms1 & Hms & Hat & Hk).
    eapply rz_msteps; [exact Hh | exact (ITreeFO.nsc_nolazy _ _ _ _ _ _ _ _ NS mo Hinv) | apply msteps_ut_ours; exact Hms |].
    pose (IA := { x : resp * Model * list event | nstep n mo (fst (fst x)) (snd (fst x)) (snd x) }).
    pose (IB := { y : word * Model | nexit n mo (fst y) (snd y) }).
    pose (evs := fun i : IA + IB => match i with
                                   | inl (exist _ x _) => snd x
                                   | inr (exist _ y _) => [ExitEv (fst y) (m_fs (snd y))]
                                   end).
    pose (nx := fun i : IA + IB => match i with
                                  | inl (exist _ x _) => mkCfg (nret ms1 (fst (fst x))) (snd (fst x))
                                  | inr (exist _ y _) => mkCfg ms1 (snd y)
                                  end).
    pose (T := fun i : IA + IB => match i with
                                 | inl (exist _ x _) => tshape (k (fst (fst x))) (snd (fst x)) K
                                 | inr _ => t_nil
                                 end).
    assert (Hi0 : exists i : IA + IB, True).
    { destruct (ITreeFO.nsc_progress _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hinv Hsafe) as [(rsp & mo' & e & Hst) | (code & mo' & Hex)].
      - exists (inl (exist _ (rsp, mo', e) Hst)). exact I.
      - exists (inr (exist _ (code, mo') Hex)). exact I. }
    destruct Hi0 as [Hi0 _].
    eapply rz_conseq.
    + apply (rz_node segs (mkCfg ms1 mo) (IA + IB) evs nx T Hi0).
      * split.
        -- intros [[[[rsp mo'] e] Hst] | [[code mo'] Hex]]; cbn in *.
           ++ exact (proj2 (proj2 (ITreeFO.nsc_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' e Hat Hh Hinv Hsafe Hst))).
           ++ exact (proj2 (ITreeFO.nsc_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv Hsafe Hex)).
        -- intros e st Hss.
           destruct (ITreeFO.nsc_complete _ _ _ _ _ _ _ _ NS n ms1 mo e st Hat Hh Hinv Hsafe Hss)
             as [(rsp & mo' & -> & Hst) | (code & mo' & -> & Hex & ->)].
           ++ exists (inl (exist _ (rsp, mo', e) Hst)). split; reflexivity.
           ++ exists (inr (exist _ (code, mo') Hex)). split; reflexivity.
      * intros [[[[rsp mo'] e] Hst] | [[code mo'] Hex]]; cbn in *.
        -- destruct (ITreeFO.nsc_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' e Hat Hh Hinv Hsafe Hst) as (Hh' & Hinv' & _).
           eapply (IH rsp Q P K); [apply Hk | eapply Hwfk; exact Hst | exact Hh' | exact Hinv' | exact HK].
        -- apply rz_halt. cbn.
           rewrite (proj1 (ITreeFO.nsc_exit _ _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv Hsafe Hex)). discriminate.
    +
      intros tr. cbn [tshape]. unfold t_alt. split.
      * intros [[[[[rsp mo'] e] Hst] | [[code mo'] Hex]] Htr]; cbn in Htr.
        -- left. exists rsp, mo', e. split; [exact Hst | exact Htr].
        -- right. exists code, mo'. split; [exact Hex | exact Htr].
      * intros [(rsp & mo' & e & Hst & Htr) | (code & mo' & Hex & Htr)].
        -- exists (inl (exist _ (rsp, mo', e) Hst)). exact Htr.
        -- exists (inr (exist _ (code, mo') Hex)). exact Htr.
Qed.

Fixpoint tsilent {R} (t : itree node R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => (forall code mo', ~ nexit n mo code mo')
               /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> evs = [] /\ tsilent (k rsp) mo'
  end.

Fixpoint tfeas {R} (t : itree node R) (mo : Model) (S : R -> Prop) : Prop :=
  match t with
  | Ret r => S r
  | Vis n k => exists rsp mo' evs, nstep n mo rsp mo' evs /\ tfeas (k rsp) mo' S
  end.

Lemma tshape_sub : forall {R} (t : itree node R) mo (K : R -> Model -> TSet) (T : TSet),
  tsilent t mo -> T [] ->
  (forall r mo' tr, K r mo' tr -> T tr) ->
  (forall tr, tshape t mo K tr -> T tr).
Proof.
  intros R t. induction t as [r | n k IH]; intros mo K T Hs HT0 HK tr Htr; cbn in *.
  - eapply HK. exact Htr.
  - destruct Hs as [Hnx Hk]. destruct Htr as [(rsp & mo' & e & Hst & Htr) | (code & mo' & Hex & _)].
    + destruct (Hk rsp mo' e Hst) as [-> Hs']. destruct Htr as [Hp | (tr' & -> & Htr')].
      * destruct tr; [exact HT0 | destruct Hp].
      * cbn. eapply IH; eauto.
    + exfalso. eapply Hnx; eauto.
Qed.

Lemma tshape_sup : forall {R} (t : itree node R) mo (K : R -> Model -> TSet) (S : R -> Prop) (T : TSet),
  tsilent t mo -> tfeas t mo S ->
  (forall r mo' tr, S r -> T tr -> K r mo' tr) ->
  (forall tr, T tr -> tshape t mo K tr).
Proof.
  intros R t. induction t as [r | n k IH]; intros mo K S T Hs Hf HK tr Htr; cbn in *.
  - eapply HK; eauto.
  - destruct Hs as [_ Hk]. destruct Hf as (rsp & mo' & e & Hst & Hf).
    destruct (Hk rsp mo' e Hst) as [-> Hs'].
    left. exists rsp, mo', []. split; [exact Hst|]. right. exists tr. split; [reflexivity|].
    eapply IH; eauto.
Qed.

Theorem impl_realizes_any : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop)
    (T : TSet) ms mo,
  @impl node segs at_node R t Q ms -> twf t mo P -> tsilent t mo ->
  m_halted mo = None -> minv mo ->
  (forall r ms' mo', Q r ms' -> P r mo' -> m_halted mo' = None -> minv mo' -> realizes segs (mkCfg ms' mo') T) ->
  realizes segs (mkCfg ms mo) T.
Proof.
  intros R t. induction t as [r | n k IH]; intros Q P T ms mo Himpl Hwf Hs Hh Hinv HK.
  - cbn in Himpl, Hwf. destruct Himpl as (ms' & Hms & HQ).
    eapply rz_msteps; [exact Hh | exact (ITreeFO.nsc_nolazy _ _ _ _ _ _ _ _ NS mo Hinv) | apply msteps_ut_ours; exact Hms |].
    apply (HK r ms' mo HQ Hwf Hh Hinv).
  - cbn [impl] in Himpl. cbn [twf] in Hwf. cbn [tsilent] in Hs. destruct Hwf as [Hsafe Hwfk]. destruct Hs as [Hnx Hsk].
    destruct Himpl as (ms1 & Hms & Hat & Hk).
    eapply rz_msteps; [exact Hh | exact (ITreeFO.nsc_nolazy _ _ _ _ _ _ _ _ NS mo Hinv) | apply msteps_ut_ours; exact Hms |].
    pose (Ix := { x : resp * Model | nstep n mo (fst x) (snd x) [] }).
    pose (nx := fun i : Ix => match i with exist _ x _ => mkCfg (nret ms1 (fst x)) (snd x) end).
    assert (Hi0 : exists i : Ix, True).
    { destruct (ITreeFO.nsc_progress _ _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hinv Hsafe) as [(rsp & mo' & e & Hst) | (code & mo' & Hex)].
      - destruct (Hsk rsp mo' e Hst) as [-> _]. exists (exist _ (rsp, mo') Hst). exact I.
      - exfalso. eapply Hnx; eauto. }
    destruct Hi0 as [i0 _].
    assert (Hcont : forall i : Ix, realizes segs (nx i) T).
    { intros [[rsp mo'] Hst]; cbn in *.
      destruct (ITreeFO.nsc_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' [] Hat Hh Hinv Hsafe Hst) as (Hh' & Hinv' & _).
      eapply (IH rsp Q P T); [apply Hk | eapply Hwfk; exact Hst | exact (proj2 (Hsk rsp mo' [] Hst)) | exact Hh' | exact Hinv' | exact HK]. }
    assert (HT0 : T []) by (eapply realizes_nonempty; apply (Hcont i0)).
    eapply rz_conseq.
    + apply (rz_node segs (mkCfg ms1 mo) Ix (fun _ => []) nx (fun _ => T) i0); [|exact Hcont].
      split.
      * intros [[rsp mo'] Hst]; cbn in *.
        exact (proj2 (proj2 (ITreeFO.nsc_sound _ _ _ _ _ _ _ _ NS n ms1 mo rsp mo' [] Hat Hh Hinv Hsafe Hst))).
      * intros e st Hss.
        destruct (ITreeFO.nsc_complete _ _ _ _ _ _ _ _ NS n ms1 mo e st Hat Hh Hinv Hsafe Hss)
          as [(rsp & mo' & -> & Hst) | (code & mo' & -> & Hex & ->)].
        -- destruct (Hsk rsp mo' e Hst) as [-> _]. exists (exist _ (rsp, mo') Hst). split; reflexivity.
        -- exfalso. eapply Hnx; eauto.
    + intros tr. unfold t_alt. split.
      * intros [_ Htr]. exact (proj1 (t_emit_nil_eq T HT0 tr) Htr).
      * intros Htr. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.

Theorem impl_realizes_alt2 : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop)
    (cls : R -> bool) (A B : TSet) ms mo,
  @impl node segs at_node R t Q ms -> twf t mo P -> tsilent t mo ->
  tfeas t mo (fun r => cls r = true) -> tfeas t mo (fun r => cls r = false) ->
  m_halted mo = None -> minv mo -> A [] -> B [] ->
  (forall r ms' mo', Q r ms' -> P r mo' -> m_halted mo' = None -> minv mo' ->
     realizes segs (mkCfg ms' mo') (if cls r then A else B)) ->
  realizes segs (mkCfg ms mo) (t_alt2 A B).
Proof.
  intros R t Q P cls A B ms mo Himpl Hwf Hs HfA HfB Hh Hinv HA0 HB0 HK.
  eapply rz_conseq; [apply (impl_realizes t Q P (fun r _ => if cls r then A else B) ms mo Himpl Hwf Hh Hinv HK)|].
  intros tr. split.
  - apply (tshape_sub t mo _ (t_alt2 A B) Hs); [left; exact HA0|].
    intros r mo' tr0 H. unfold t_alt2. destruct (cls r); auto.
  - intros [HA | HB].
    + apply (tshape_sup t mo _ (fun r => cls r = true) A Hs HfA); [|exact HA]. intros r mo' tr0 -> H. exact H.
    + apply (tshape_sup t mo _ (fun r => cls r = false) B Hs HfB); [|exact HB]. intros r mo' tr0 -> H. exact H.
Qed.

End Bridge.
End B.
