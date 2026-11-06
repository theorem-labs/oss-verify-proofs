(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import SimInv ExitSim CatSim MmapSim AllocSim AllocSim2 WallSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common Require Import CfgStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

Lemma is_prefix_app_r {A} : forall (l m a : list A),
  is_prefix a l -> is_prefix a (l ++ m).
Proof.
  induction l as [|x l IH]; intros m a H.
  - destruct a; [apply is_prefix_nil | cbn in H; contradiction].
  - destruct a as [|y a]; cbn in *; [exact I|].
    destruct H as [-> H]. split; [reflexivity | apply IH; exact H].
Qed.

Lemma is_prefix_app_split {A} : forall (l a b : list A),
  is_prefix b (l ++ a) ->
  is_prefix b l \/ exists b', b = l ++ b' /\ is_prefix b' a.
Proof.
  induction l as [|x l IH]; intros a b H.
  - right. exists b. split; [reflexivity | exact H].
  - destruct b as [|y b]; cbn in H; [left; exact I|].
    destruct H as [-> H]. destruct (IH a b H) as [Hp | (b' & -> & Hp)].
    + left. cbn. split; [reflexivity | exact Hp].
    + right. exists b'. split; [reflexivity | exact Hp].
Qed.

Lemma is_prefix_nil_r {A} : forall (a : list A), is_prefix a [] -> a = [].
Proof. destruct a; cbn; [reflexivity | contradiction]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TSet := list event -> Prop.

Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.

Lemma t_eq_refl : forall T, t_eq T T. Proof. firstorder. Qed.
Lemma t_eq_sym : forall T T', t_eq T T' -> t_eq T' T. Proof. firstorder. Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof. firstorder. Qed.

(* [comment removed for export] *)
Definition t_nil : TSet := fun tr => tr = [].

(* [comment removed for export] *)
Definition t_emit (evs : list event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.

(* [comment removed for export] *)
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.

(* [comment removed for export] *)
Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.

(* [comment removed for export] *)
Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
  t_emit [ExitEv code fs] t_nil.

(* [comment removed for export] *)
Definition wr_index (buf : list byte) : Type :=
  {n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.

Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
    : wr_index buf :=
  exist _ (length buf) (conj Hnb (Nat.le_refl _)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_nil_eq : forall T, T [] -> t_eq (t_emit [] T) T.
Proof.
  intros T H0 tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)];
      [apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
  - intro HT. right. exists tr. split; [reflexivity | exact HT].
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
Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.

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

(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs kit_cfg c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs kit_cfg c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Lemma node_ok_is_c : forall c I evs nx, node_ok c I evs nx = node_ok_c segs kit_cfg c I evs nx.
Proof. reflexivity. Qed.

Lemma node_ok_of_u : forall c (I : Type) evs nx,
  pending_on segs kit_cfg c -> node_ok_u segs c I evs nx -> node_ok c I evs nx.
Proof. intros c I evs nx Hon H. exact (node_transfer_on segs kit_cfg c I evs nx Hon H). Qed.

Lemma node_ok_grants_r : forall c (IA IB : Type) evs nx (b0 : IB),
  pending_off segs kit_cfg c ->
  node_ok_u segs c (IA + IB) evs nx ->
  (forall a, child_refusal_b segs c (nx (inl a)) = true) ->
  (forall b, child_refusal_b segs c (nx (inr b)) = false) ->
  m_halted (cfg_model (nx (inr b0))) = None ->
  node_ok c IB (fun b => evs (inr b)) (fun b => nx (inr b)).
Proof.
  intros c IA IB evs nx b0 Hoff H HA HB Hh0.
  exact (node_transfer_sum_r segs kit_cfg c IA IB evs nx b0 H Hoff HA HB Hh0).
Qed.

Lemma node_ok_forced : forall c (I : Type) evs nx,
  node_ok_u segs c I evs nx ->
  (forall i, m_halted (cfg_model (nx i)) = None) ->
  (forall i, child_refusal_b segs c (nx i) = true) ->
  node_ok c I evs nx.
Proof.
  intros c I evs nx H Hunh Hall.
  exact (node_transfer_all_refusals segs kit_cfg c I evs nx H Hunh Hall).
Qed.

Lemma node_ok_sub : forall c (I J : Type) evs nx (f : J -> I) (j0 : J),
  node_ok_u segs c I evs nx ->
  pending_off segs kit_cfg c ->
  (forall j, child_refusal_b segs c (nx (f j)) = false) ->
  m_halted (cfg_model (nx (f j0))) = None ->
  (forall i, child_refusal_b segs c (nx i) = false ->
     exists j, evs (f j) = evs i /\ nx (f j) = nx i) ->
  node_ok c J (fun j => evs (f j)) (fun j => nx (f j)).
Proof.
  intros c I J evs nx f j0 H Hoff Hkeep Hh0 Hsurj.
  exact (node_transfer_sub segs kit_cfg c I J evs nx f j0 H Hoff Hkeep Hh0 Hsurj).
Qed.

Lemma node_ok_no_refusals : forall c (I : Type) evs nx,
  node_ok_u segs c I evs nx ->
  (forall i, child_refusal_b segs c (nx i) = false) ->
  node_ok c I evs nx.
Proof.
  intros c I evs nx H Hnr. exact (node_transfer_no_refusals segs kit_cfg c I evs nx H Hnr).
Qed.

Lemma node_ok_exact : forall c (I : Type) evs nx,
  node_ok_u segs c I evs nx ->
  pending_off segs kit_cfg c ->
  (forall i, m_halted (cfg_model (nx i)) = None) ->
  node_ok c {i : I | child_refusal_b segs c (nx i) = false
                     \/ (forall j, child_refusal_b segs c (nx j) = true)}
          (fun k => evs (proj1_sig k)) (fun k => nx (proj1_sig k)).
Proof.
  intros c I evs nx H Hoff Hunh. exact (node_transfer_exact segs kit_cfg c I evs nx H Hoff Hunh).
Qed.

Lemma node_ok_gen : forall c (I J : Type) evs nx (f : J -> I),
  node_ok_u segs c I evs nx ->
  (forall j, ~ spurious_child segs kit_cfg c (nx (f j))) ->
  (forall i, ~ spurious_child segs kit_cfg c (nx i) ->
     exists j, evs (f j) = evs i /\ nx (f j) = nx i) ->
  node_ok c J (fun j => evs (f j)) (fun j => nx (f j)).
Proof.
  intros c I J evs nx f H Hk Hs. exact (node_transfer_gen segs kit_cfg c I J evs nx f H Hk Hs).
Qed.

Lemma node_ok_ext : forall c (I : Type) evs nx evs' nx',
  node_ok c I evs nx ->
  (forall i, evs' i = evs i) -> (forall i, nx' i = nx i) ->
  node_ok c I evs' nx'.
Proof. intros c I evs nx evs' nx' H He Hn. exact (node_ok_c_ext segs kit_cfg c I evs nx evs' nx' H He Hn). Qed.

Lemma node_ok_sub_step : forall c e st,
  sstep_cfg segs kit_cfg c e st -> sstep segs c e st.
Proof. intros c e st H. exact (sstep_cfg_sub segs kit_cfg c e st H). Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs kit_cfg c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar.
  exact (star_halted_nil segs c tr c' Hh (star_cfg_sub segs kit_cfg _ _ _ Hstar)).
Qed.

Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs kit_cfg c evs (SNext c') -> star_cfg segs kit_cfg c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs).
  econstructor; [exact H | apply star_cfg_refl].
Qed.

Lemma obs_trace_cfg_nil : forall c, obs_trace_cfg segs kit_cfg c [].
Proof. intros c. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil]. Qed.

Lemma star_cfg_inv (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs kit_cfg c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star_cfg segs kit_cfg c tr c' -> Inv c'.
Proof.
  intros c tr c' HInv Hstar. induction Hstar; [exact HInv |].
  apply IHHstar. eapply Hstep; eauto.
Qed.

Lemma inv_no_reaches_error_cfg (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs kit_cfg c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep_cfg segs kit_cfg c evs SError) :
  forall c, Inv c -> ~ reaches_error_cfg segs kit_cfg c.
Proof.
  intros c HInv (tr & c' & evs & Hstar & Hss).
  eapply Hnoerr; [| exact Hss]. eapply star_cfg_inv; eauto.
Qed.

(* [comment removed for export] *)
Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok c I evs nx ->
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes c t_nil
| rz_conseq : forall c T T',
    realizes c T -> t_eq T T' -> realizes c T'.

(* [comment removed for export] *)

Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma sstep_halted_none : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs kit_cfg c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H. exact (sstep_halted_none c e st (sstep_cfg_sub segs kit_cfg _ _ _ H)). Qed.

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
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
  intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

(* [comment removed for export] *)
Lemma rz_silent1 : forall c c' T,
  node_ok c unit (fun _ => []) (fun _ => c') ->
  realizes c' T ->
  realizes c T.
Proof.
  intros c c' T Hnode Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
Lemma rz_emit1 : forall c c' e T,
  node_ok c unit (fun _ => e) (fun _ => c') ->
  realizes c' T ->
  realizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
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
Lemma rz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - apply node_ok_of_u.
    { apply (kit_pending_on_sysno segs ms model x8 (bv_unsigned x8) Hsvc eq_refl).
      destruct Hx8 as [E | E]; rewrite E; reflexivity. }
    split.
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
  - apply rz_halt. cbn. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs.

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

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
