(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes AEvt Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Monad MSafe ImplAevt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.

Section BridgeRz.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma msteps_shape : forall ms ms', Exec.msteps segs ms ms' -> Shape.msteps segs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 [Hsvc Hst] H IH].
  - apply mst_refl.
  - eapply mst_step; eauto.
Qed.

(* [comment removed for export] *)
Fixpoint tsh {R} (t : itree node R) (mo : Model) (TT : R -> Model -> TSet) : TSet :=
  match t with
  | Ret r => TT r mo
  | Vis n k => t_alt (fun i : { x : resp * Model | nstep n mo (fst x) (snd x) [] } =>
                 t_emit [] (tsh (k (fst (proj1_sig i))) (snd (proj1_sig i)) TT))
  end.

#[using="Type"] Theorem impl_twf_realizes {R} : forall (t : itree node R) (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop)
    (TT : R -> Model -> TSet) ms mo,
  tmm t ->
  impl segs (at_node segs) t Q ms ->
  twf t mo P ->
  minv mo -> m_halted mo = None ->
  (forall r ms' mo', Q r ms' -> P r mo' -> minv mo' -> m_halted mo' = None -> vm_only mo mo' ->
     realizes segs (mkCfg ms' mo') (TT r mo')) ->
  realizes segs (mkCfg ms mo) (tsh t mo TT).
Proof.
  induction t as [r|n k IH]; intros Q P TT ms mo Ht Hi Hw Hm Hh HL; cbn in Ht, Hi, Hw |- *.
  - ddestruct Hi as (ms' & Hs & HQ).
    eapply rz_msteps; [exact Hh | exact Hm | apply msteps_shape; exact Hs |].
    apply (HL r ms' mo HQ Hw Hm Hh (vm_only_refl mo)).
  - destruct Ht as [Hn Hk]. destruct Hw as [Hs Hwk]. ddestruct Hi as (ms1 & Hrun & [Hat Hik]).
    eapply rz_msteps; [exact Hh | exact Hm | apply msteps_shape; exact Hrun |].
    ddestruct (mm_node_facts segs n ms1 mo ltac:(destruct n; first [exact I|destruct Hn]) Hat Hm Hh Hs) as (Hc & Hsnd & Hp).
    ddestruct Hp as (eff0 & mo0 & evs0 & Hst0). pose proof (nstep_nil _ _ _ _ _ Hst0) as E0. subst evs0.
    set (I := { x : resp * Model | nstep n mo (fst x) (snd x) [] }).
    set (nx := fun i : I => mkCfg (nret ms1 (fst (proj1_sig i))) (snd (proj1_sig i))).
    change (t_alt (fun i : I => t_emit [] (tsh (k (fst (proj1_sig i))) (snd (proj1_sig i)) TT)))
      with (t_alt (fun i : I => t_emit ((fun _ : I => @nil event) i) ((fun i : I => tsh (k (fst (proj1_sig i))) (snd (proj1_sig i)) TT) i))).
    apply (rz_node segs (mkCfg ms1 mo) I (fun _ => []) nx _ (exist _ (eff0, mo0) Hst0)).
    + split.
      * intros [[eff mo'] Hst]. cbn. exact (proj2 (proj2 (Hsnd _ _ _ Hst))).
      * intros e st Hss. destruct (Hc _ _ Hss) as (eff & mo' & -> & Hst).
        pose proof (nstep_nil _ _ _ _ _ Hst) as ->. exists (exist _ (eff, mo') Hst). split; reflexivity.
    + intros [[eff mo'] Hst]. cbn.
      pose proof (Hsnd _ _ _ Hst) as (Hh' & Hm' & _).
      pose proof (nstep_mm_vm_only n mo eff mo' [] Hm Hs Hst) as [Hvo _].
      apply (IH eff Q P TT (nret ms1 eff) mo' (Hk eff) (Hik eff) (Hwk _ _ _ Hst) Hm' Hh').
      intros r ms' mo'' HQ HP M1 M2 M3. apply (HL r ms' mo'' HQ HP M1 M2). eapply vm_only_trans; eauto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma tsh_spec {R} : forall (t : itree node R) mo TT tr,
  (forall r mo', TT r mo' []) ->
  tsh t mo TT tr <->
  match t with
  | Ret r => TT r mo tr
  | Vis n k => (tr = [] /\ exists eff mo', nstep n mo eff mo' [])
               \/ exists r mo', tpath nstep t mo [] r mo' /\ TT r mo' tr
  end.
Proof.
  induction t as [r0|n k IH]; intros mo TT tr HT; cbn.
  - tauto.
  - split.
    + (intros dd_H; ddestruct dd_H as [[[eff mo'] Hst] Hem]). cbn in Hem. destruct Hem as [Hp | (tr' & -> & Hsub)].
      * left. split; [| dexists eff, mo'; exact Hst]. apply is_prefix_nil_r. exact Hp.
      * cbn. pose proof (proj1 (IH eff mo' TT tr' HT) Hsub) as K.
        destruct (k eff) as [r1|n1 k1] eqn:Ek.
        -- right. dexists r1, mo'. split; [|exact K]. dexists eff, mo', [], []. rewrite Ek. cbn. repeat split; auto.
        -- destruct K as [[-> (eff1 & mo1 & Hst1)] | (r & mo'' & Hpath & Htr)].
           ++ left. split; [reflexivity|]. dexists eff, mo'. exact Hst.
           ++ right. dexists r, mo''. split; [|exact Htr]. dexists eff, mo', [], []. rewrite Ek. repeat split; auto.
    + intros [[-> (eff & mo' & Hst)] | (r & mo'' & (eff & mo1 & evs & tr' & Hst & Hpath & Htr') & Htr)].
      * exists (exist _ (eff, mo') Hst). cbn. left. exact I.
      * pose proof (nstep_nil _ _ _ _ _ Hst) as ->. cbn in Htr'. subst tr'.
        assert (Hst' : nstep n mo (fst (eff, mo1)) (snd (eff, mo1)) []) by exact Hst.
        exists (exist _ (eff, mo1) Hst'). cbn. right. exists tr. split; [reflexivity|].
        apply (proj2 (IH eff mo1 TT tr HT)).
        destruct (k eff) as [r1|n1 k1] eqn:Ek; cbn in Hpath.
        -- ddestruct Hpath as (-> & -> & _). exact Htr.
        -- right. dexists r, mo''. split; [exact Hpath | exact Htr].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition splits {R} (t : itree node R) (mo : Model) (isA : R -> bool) : Prop :=
  (exists r mo', tpath nstep t mo [] r mo' /\ isA r = true)
  /\ (exists r mo', tpath nstep t mo [] r mo' /\ isA r = false).

#[using="Type"] Lemma tsh_t_alt2 {R} : forall (t : itree node R) mo (isA : R -> bool) (A B : TSet),
  A [] -> B [] -> splits t mo isA ->
  t_eq (tsh t mo (fun r _ => if isA r then A else B)) (t_alt2 A B).
Proof.
  (intros t mo isA A B HA HB dd_H; ddestruct dd_H as [(ra & moa & Pa & Ea) (rb & mob & Pb & Eb)]; intros tr).
  assert (HT : forall (r : R) (mo' : Model), (fun r _ => if isA r then A else B) r mo' []).
  { intros r mo'. cbn. destruct (isA r); assumption. }
  rewrite (tsh_spec t mo _ tr HT). unfold t_alt2.
  destruct t as [r0|n k]; cbn in Pa, Pb |- *.
  - ddestruct Pa as (-> & -> & _). rewrite Ea. ddestruct Pb as (E & _ & _). subst rb. rewrite Ea in Eb. discriminate.
  - split.
    + intros [[-> _] | (r & mo' & Hp & Htr)]; [left; exact HA|].
      destruct (isA r); [left|right]; exact Htr.
    + intros [Htr|Htr].
      * right. dexists ra, moa. split; [exact Pa|]. rewrite Ea. exact Htr.
      * right. dexists rb, mob. split; [exact Pb|]. rewrite Eb. exact Htr.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Theorem impl_realizes_alt2 {R} : forall (t : itree node R) (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop)
    (isA : R -> bool) (A B : TSet) ms mo,
  tmm t ->
  impl segs (at_node segs) t Q ms ->
  twf t mo P ->
  minv mo -> m_halted mo = None ->
  splits t mo isA -> A [] -> B [] ->
  (forall r ms' mo', isA r = true -> Q r ms' -> P r mo' -> minv mo' -> m_halted mo' = None -> vm_only mo mo' ->
     realizes segs (mkCfg ms' mo') A) ->
  (forall r ms' mo', isA r = false -> Q r ms' -> P r mo' -> minv mo' -> m_halted mo' = None -> vm_only mo mo' ->
     realizes segs (mkCfg ms' mo') B) ->
  realizes segs (mkCfg ms mo) (t_alt2 A B).
Proof.
  intros t Q P isA A B ms mo Ht Hi Hw Hm Hh SP HA HB KA KB.
  eapply rz_conseq; [| apply (tsh_t_alt2 t mo isA A B HA HB SP)].
  apply (impl_twf_realizes t Q P _ ms mo Ht Hi Hw Hm Hh).
  intros r ms' mo' HQ HP M1 M2 M3. cbn. destruct (isA r) eqn:E; [eapply KA | eapply KB]; eauto.
Qed.

End BridgeRz.
