(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Exec ITree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ShapeAlg(TSet, t_eq, t_alt, t_alt2, t_emit, t_nil, realizes, node_ok).
Open Scope bv_scope.
Unset Lia Cache.

Section TreeBridge.
Context {node : Type}.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nsafe : node -> Model -> Prop.

Hypothesis Nmodel : forall n mo rsp mo' evs,
  nsafe n mo -> mo_ok mo -> nstep n mo rsp mo' evs -> evs = [] /\ mo_ok mo' /\ vm_agree mo mo'.
Hypothesis Nsound : forall n ms mo rsp mo' evs,
  at_node n ms -> nsafe n mo -> mo_ok mo -> nstep n mo rsp mo' evs ->
  sstep_cfg segs fcfg (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo')).
Hypothesis Ncomplete : forall n ms mo evs X,
  at_node n ms -> nsafe n mo -> mo_ok mo -> sstep_cfg segs fcfg (mkCfg ms mo) evs X ->
  exists rsp mo', X = SNext (mkCfg (nret ms rsp) mo') /\ nstep n mo rsp mo' evs.
Hypothesis Nprogress : forall n mo, nsafe n mo -> mo_ok mo -> exists rsp mo' evs, nstep n mo rsp mo' evs.

Fixpoint twf {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> twf (k rsp) mo' P
  end.

Lemma twf_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  twf t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twf t mo P'.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH; eauto.
Qed.

Lemma twf_strengthen : forall {R} (t : itree node R) mo P,
  twf t mo P -> mo_ok mo ->
  twf t mo (fun r mo' => P r mo' /\ tpath nstep t mo [] r mo' /\ mo_ok mo' /\ vm_agree mo mo').
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P H Hmo; cbn in *.
  - split; [exact H|]. split; [repeat split; reflexivity|]. split; [exact Hmo | apply vm_agree_refl].
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst.
    destruct (Nmodel n mo rsp mo' evs Hs Hmo Hst) as (-> & Hmo' & Hva).
    eapply twf_mono; [apply IH; [eapply Hk; exact Hst | exact Hmo']|].
    cbn. intros r mo1 (HP & Hp & Hmo1 & Hva1). split; [exact HP|]. split; [| split; [exact Hmo1 | eapply vm_agree_trans; eassumption]].
    exists rsp, mo', [], []. split; [exact Hst|]. split; [exact Hp | reflexivity].
Qed.

Lemma twf_path_exists : forall {R} (t : itree node R) mo P,
  twf t mo P -> mo_ok mo -> exists r mo', tpath nstep t mo [] r mo' /\ P r mo' /\ mo_ok mo' /\ vm_agree mo mo'.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo P H Hmo; cbn in *.
  - exists r, mo. split; [repeat split; reflexivity|]. split; [exact H|]. split; [exact Hmo | apply vm_agree_refl].
  - destruct H as [Hs Hk]. destruct (Nprogress n mo Hs Hmo) as (rsp & mo' & evs & Hst).
    destruct (Nmodel n mo rsp mo' evs Hs Hmo Hst) as (-> & Hmo' & Hva).
    destruct (IH rsp mo' P (Hk _ _ _ Hst) Hmo') as (r & mo'' & Hp & HP & Hmo'' & Hva').
    exists r, mo''. split; [| split; [exact HP | split; [exact Hmo'' | eapply vm_agree_trans; eassumption]]].
    exists rsp, mo', [], []. split; [exact Hst|]. split; [exact Hp | reflexivity].
Qed.

Definition t_paths {R} (t : itree node R) (mo : Model) (Kof : R -> TSet) : TSet :=
  fun tr => exists r mo', tpath nstep t mo [] r mo' /\ Kof r tr.

Lemma t_paths_ret : forall {R} (r : R) mo Kof, t_eq (Kof r) (t_paths (Ret r) mo Kof).
Proof.
  intros R r mo Kof tr. unfold t_paths. cbn. split.
  - intros H. exists r, mo. split; [repeat split; reflexivity | exact H].
  - intros (r0 & mo' & (<- & -> & _) & H). exact H.
Qed.

Definition nidx (n : node) (mo : Model) : Type := { x : resp * Model | nstep n mo (fst x) (snd x) [] }.

Lemma t_paths_vis : forall {R} n (k : resp -> itree node R) mo Kof,
  (forall x : nidx n mo, t_paths (k (fst (proj1_sig x))) (snd (proj1_sig x)) Kof []) ->
  t_eq (t_alt (fun x : nidx n mo => t_emit [] (t_paths (k (fst (proj1_sig x))) (snd (proj1_sig x)) Kof)))
       (t_paths (Vis n k) mo Kof).
Proof.
  intros R n k mo Kof Hne tr. unfold t_alt, t_paths. split.
  - intros [[[rsp mo1] Hst] Htr]. cbn in Htr, Hst.
    apply (proj1 (ShapeAlg.t_emit_nil_eq _ (Hne (exist _ (rsp, mo1) Hst)) tr)) in Htr.
    destruct Htr as (r & mo' & Hp & HK). exists r, mo'. split; [| exact HK].
    cbn. exists rsp, mo1, [], []. repeat split; assumption.
  - intros (r & mo' & Hp & HK). cbn in Hp. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & Hnil).
    destruct evs; [| discriminate Hnil]. destruct tr'; [| discriminate Hnil].
    exists (exist _ (rsp, mo1) Hst). cbn.
    apply (proj2 (ShapeAlg.t_emit_nil_eq _ (Hne (exist _ (rsp, mo1) Hst)) tr)).
    exists r, mo'. split; assumption.
Qed.

Theorem impl_twf_realizes : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop)
    (P : R -> Model -> Prop) ms mo (Kof : R -> TSet),
  impl segs at_node t Q ms ->
  twf t mo P ->
  mo_ok mo ->
  (forall r ms' mo', Q r ms' -> P r mo' -> realizes segs (mkCfg ms' mo') (Kof r)) ->
  realizes segs (mkCfg ms mo) (t_paths t mo Kof).
Proof.
  intros R t. induction t as [r|n k IH]; intros Q P ms mo Kof Himpl Htwf Hmo HK; cbn in Himpl, Htwf.
  - eapply ShapeAlg.rz_conseq; [| apply t_paths_ret].
    eapply evt_realizes; [exact Himpl | apply (mo_ok_halted _ Hmo) | apply (mo_ok_lazy _ Hmo) |].
    intros ms' HQ. apply HK; assumption.
  - destruct Htwf as [Hs Hk].
    eapply evt_realizes; [exact Himpl | apply (mo_ok_halted _ Hmo) | apply (mo_ok_lazy _ Hmo) |].
    intros ms1 [Hat Hkids].

    assert (Hsub : forall x : nidx n mo,
      realizes segs (mkCfg (nret ms1 (fst (proj1_sig x))) (snd (proj1_sig x)))
               (t_paths (k (fst (proj1_sig x))) (snd (proj1_sig x)) Kof)).
    { intros [[rsp mo1] Hst]; cbn in Hst |- *.
      destruct (Nmodel n mo rsp mo1 [] Hs Hmo Hst) as (_ & Hmo1 & Hva).
      apply (IH rsp Q P); [apply Hkids | eapply Hk; exact Hst | exact Hmo1 | exact HK]. }

    destruct (Nprogress n mo Hs Hmo) as (rsp0 & mo0 & evs0 & Hst0).
    destruct (Nmodel n mo rsp0 mo0 evs0 Hs Hmo Hst0) as (-> & _ & _).
    eapply ShapeAlg.rz_conseq.
    + apply (ShapeAlg.rz_node segs (mkCfg ms1 mo) (nidx n mo) (fun _ => [])
               (fun x => mkCfg (nret ms1 (fst (proj1_sig x))) (snd (proj1_sig x)))
               (fun x => t_paths (k (fst (proj1_sig x))) (snd (proj1_sig x)) Kof)
               (exist _ (rsp0, mo0) Hst0)).
      * split.
        -- intros [[rsp mo1] Hst]; cbn. apply (Nsound n); assumption.
        -- intros e st Hss. destruct (Ncomplete n ms1 mo e st Hat Hs Hmo Hss) as (rsp & mo1 & -> & Hst).
           destruct (Nmodel n mo rsp mo1 e Hs Hmo Hst) as (-> & _ & _).
           exists (exist _ (rsp, mo1) Hst). cbn. split; reflexivity.
      * exact Hsub.
    + apply t_paths_vis. intros x. eapply ShapeAlg.realizes_nonempty. apply Hsub.
Qed.

Theorem impl_twf_realizes' : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop)
    (P : R -> Model -> Prop) ms mo (Kof : R -> TSet),
  impl segs at_node t Q ms ->
  twf t mo P ->
  mo_ok mo ->
  (forall r ms' mo', Q r ms' -> P r mo' -> tpath nstep t mo [] r mo' -> mo_ok mo' -> vm_agree mo mo' ->
     realizes segs (mkCfg ms' mo') (Kof r)) ->
  realizes segs (mkCfg ms mo) (t_paths t mo Kof).
Proof.
  intros R t Q P ms mo Kof Himpl Htwf Hmo HK.
  apply (impl_twf_realizes t Q _ ms mo Kof Himpl (twf_strengthen t mo P Htwf Hmo) Hmo).
  intros r ms' mo' HQ (HP & Hp & Hmo' & Hva). apply HK; assumption.
Qed.

Theorem impl_twf_realizes_silent : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop)
    (P : R -> Model -> Prop) ms mo (K : TSet),
  impl segs at_node t Q ms ->
  twf t mo P ->
  mo_ok mo ->
  (forall r ms' mo', Q r ms' -> P r mo' -> tpath nstep t mo [] r mo' -> mo_ok mo' -> vm_agree mo mo' ->
     realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros R t Q P ms mo K Himpl Htwf Hmo HK.
  eapply ShapeAlg.rz_conseq; [apply (impl_twf_realizes' t Q P ms mo (fun _ => K)); assumption|].
  intros tr. unfold t_paths. split.
  - intros (_ & _ & _ & H). exact H.
  - intros H. destruct (twf_path_exists t mo P Htwf Hmo) as (r & mo' & Hp & _). exists r, mo'. split; assumption.
Qed.

Theorem impl_twf_realizes_alt2 : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop)
    (P : R -> Model -> Prop) ms mo (cls : R -> bool) (KA KB : TSet),
  impl segs at_node t Q ms ->
  twf t mo P ->
  mo_ok mo ->
  (exists r mo', tpath nstep t mo [] r mo' /\ cls r = false) ->
  (exists r mo', tpath nstep t mo [] r mo' /\ cls r = true) ->
  (forall r ms' mo', Q r ms' -> P r mo' -> tpath nstep t mo [] r mo' -> mo_ok mo' -> vm_agree mo mo' ->
     realizes segs (mkCfg ms' mo') (if cls r then KB else KA)) ->
  realizes segs (mkCfg ms mo) (t_alt2 KA KB).
Proof.
  intros R t Q P ms mo cls KA KB Himpl Htwf Hmo (ra & moa & Hpa & Ha) (rb & mob & Hpb & Hb) HK.
  eapply ShapeAlg.rz_conseq; [apply (impl_twf_realizes' t Q P ms mo (fun r => if cls r then KB else KA)); assumption|].
  intros tr. unfold t_paths, t_alt2. split.
  - intros (r & mo' & _ & H). destruct (cls r); [right | left]; exact H.
  - intros [H|H].
    + exists ra, moa. rewrite Ha. split; assumption.
    + exists rb, mob. rewrite Hb. split; assumption.
Qed.

End TreeBridge.

Arguments twf {node} nstep nsafe {R} t mo P.
Arguments t_paths {node} nstep {R} t mo Kof.
Arguments nidx {node} nstep n mo.
