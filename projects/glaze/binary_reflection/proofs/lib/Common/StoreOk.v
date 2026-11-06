(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AllocSim2.
(* [comment removed for export] *)

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.



End AllocSim2.
Module Footprint.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record region : Type := Rg { rg_lo : Z; rg_hi : Z }.













End Footprint.
Module RunLim.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition LMIN : Z := source_alloc_limit.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma LMIN_val : LMIN = 17179869184.
Proof. reflexivity. Qed.


(* [comment removed for export] *)
Lemma LMIN_le_target : LMIN <= target_alloc_limit.
Proof. unfold LMIN, source_alloc_limit, target_alloc_limit. lia. Qed.
Lemma LMIN_le_source : LMIN <= source_alloc_limit.
Proof. apply Z.le_refl. Qed.

End RunLim.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CfgStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module ShapeAlg.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim AllocSim2 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.WallSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CfgStep.
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
Lemma t_emit_nil_eq : forall T, T [] -> t_eq (t_emit [] T) T.
Proof.
  intros T H0 tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)];
      [apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
  - intro HT. right. exists tr. split; [reflexivity | exact HT].
Qed.








(* [comment removed for export] *)
Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.




(* [comment removed for export] *)
Lemma t_alt_wall : forall (ch : word) (rest : list byte) (T : TSet),
  T [] -> (1 <= length rest)%nat ->
  t_eq (t_alt (fun i : wr_index rest =>
          t_emit (map (WriteEv ch) (firstn (proj1_sig i) rest))
                 (t_emit (map (WriteEv ch) (skipn (proj1_sig i) rest)) T)))
       (t_emit (map (WriteEv ch) rest) T).
Proof.
  intros ch rest T HT Hnb tr. split.
  - intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
    destruct Hi as [Hp | (tr1 & -> & Hi)].
    + left. eapply is_prefix_trans; [exact Hp|].
      rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
      apply is_prefix_app_r. apply is_prefix_refl.
    + destruct Hi as [Hp | (tr2 & -> & Ht)].
      * left.
        rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
        apply is_prefix_app_mono. exact Hp.
      * right. exists tr2. split; [|exact Ht].
        rewrite app_assoc, <- map_app, firstn_skipn. reflexivity.
  - intros [Hp | (tr' & -> & Ht)].
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all. left. exact Hp.
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all, skipn_all. right.
      exists tr'. split; [reflexivity|].
      cbn [map]. right. exists tr'. split; [reflexivity | exact Ht].
Qed.




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

Lemma node_ok_sub_step : forall c e st,
  sstep_cfg segs kit_cfg c e st -> sstep segs c e st.
Proof. intros c e st H. exact (sstep_cfg_sub segs kit_cfg c e st H). Qed.

Lemma node_ok_of_u_unit : forall c evs0 c0,
  node_ok_u segs c unit (fun _ => evs0) (fun _ => c0) ->
  m_halted (cfg_model c0) = None ->
  node_ok c unit (fun _ => evs0) (fun _ => c0).
Proof.
  intros c evs0 c0 H Hh0.
  destruct (child_refusal_b segs c c0) eqn:E.
  - apply node_ok_forced; [exact H | intros []; exact Hh0 | intros []; exact E].
  - apply node_ok_no_refusals; [exact H | intros []; exact E].
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

Lemma realizes_pclosed : forall c T, realizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

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

(* [comment removed for export] *)

Lemma realizes_star_only : forall c T, realizes c T ->
  forall tr c', star_cfg segs kit_cfg c tr c' -> T tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil c tr c' Hh Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

Lemma realizes_admits : forall c T, realizes c T ->
  forall tr, T tr -> obs_trace_cfg segs kit_cfg c tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
Theorem realizes_obs_iff : forall c T, realizes c T ->
  forall tr, obs_trace_cfg segs kit_cfg c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
  - apply realizes_admits; exact H.
Qed.

(* [comment removed for export] *)

Lemma sstep_halted_none : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs kit_cfg c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H. exact (sstep_halted_none c e st (sstep_cfg_sub segs kit_cfg _ _ _ H)). Qed.

Lemma realizes_step : forall c T e c',
  realizes c T -> sstep_cfg segs kit_cfg c e (SNext c') -> exists T', realizes c' T'.
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Lemma realizes_no_sserror : forall c T e,
  realizes c T -> ~ sstep_cfg segs kit_cfg c e SError.
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Definition rz_path (c : config) : Prop := exists T, realizes c T.

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

Theorem realizes_no_error : forall c T, realizes c T -> ~ reaches_error_cfg segs kit_cfg c.
Proof.
  intros c T H.
  apply (inv_no_reaches_error_cfg rz_path).
  - intros c1 e c2 (T1 & H1) Hss. eapply realizes_step; eauto.
  - intros c1 e (T1 & H1) Hss. eapply realizes_no_sserror; eauto.
  - exists T; exact H.
Qed.









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
Lemma rz_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                       (a0 : IA) (b0 : IB),
  node_ok c (IA + IB) (fun _ => []) nx ->
  (forall i, realizes (nx (inl i)) A) ->
  (forall i, realizes (nx (inr i)) B) ->
  realizes c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply realizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply realizes_nonempty; apply (HB b0)).
  apply (rz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (rz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)

Lemma node_instr_u : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  node_ok_u segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep. split.
  - intros []. apply (sstep_instr segs ms model ms' model);
      [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros e st Hss.
    destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss) as [-> ->].
    exists tt. split; reflexivity.
Qed.

Lemma node_instr : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  node_ok (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep.
  apply node_ok_of_u; [kit_pending_on |]. apply node_instr_u; assumption.
Qed.

Lemma rz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

Lemma rz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                  | apply IH; exact Hc].
Qed.



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
  - apply node_ok_of_u;
      [destruct Hx8 as [Hx8' | Hx8'];
       apply (kit_pending_on_sysno segs ms model x8 _ Hsvc Hx8'); reflexivity |].
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




End WithSegs.


































End ShapeAlg.
Require Stdlib.Strings.PrimString Stdlib.Numbers.Cyclic.Int63.Uint63 Stdlib.Numbers.Cyclic.Int63.PrimInt63.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module WsegFast.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.

Import Stdlib.Numbers.Cyclic.Int63.PrimInt63.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition wf_hexc (c : PrimString.char63) : bool :=
  ((Uint63.leb 48%uint63 c && Uint63.leb c 57%uint63) || (Uint63.leb 97%uint63 c && Uint63.leb c 102%uint63))%bool.
(* [comment removed for export] *)
Fixpoint wf_hex_ok (s : PrimString.string) (j : Uint63.int) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => (Uint63.ltb (Uint63.add j 1%uint63) (PrimString.length s) && wf_hexc (PrimString.get s j)
             && wf_hexc (PrimString.get s (Uint63.add j 1%uint63)) && wf_hex_ok s (Uint63.add j 2%uint63) n')%bool
  end.

Definition wf_chunk_bytes (c : PrimString.string) : N := Z.to_N (Uint63.to_Z (PrimString.length c) / 2).

Fixpoint wf_chunks_ok (cs : list PrimString.string) (off : N) (n : nat) : bool :=
  match n with
  | O => true
  | S _ =>
      match cs with
      | [] => false
      | c :: rest =>
          let cb := wf_chunk_bytes c in
          if (off <? cb)%N then
            let k := N.to_nat (cb - off) in
            if Nat.leb n k then wf_hex_ok c (Uint63.of_Z (Z.of_N (2 * off))) n
            else (wf_hex_ok c (Uint63.of_Z (Z.of_N (2 * off))) k && wf_chunks_ok rest 0 (n - k))%bool
          else wf_chunks_ok rest (off - cb) n
      end
  end.

Fixpoint wf_first_seg (segs : list Segment) (lo hi : Z) : option Segment :=
  match segs with
  | [] => None
  | s :: rest =>
      let base := Z.of_N (seg_base s) in
      let top := (base + Z.of_N (seg_size s))%Z in
      if (Z.leb base lo && Z.leb hi top)%bool then Some s
      else if (Z.leb hi base || Z.leb top lo)%bool then wf_first_seg rest lo hi
      else None
  end.

Definition wseg_fast (segs : list Segment) (a : word) (n : nat) : bool :=
  (Z.ltb (bv_unsigned a + Z.of_nat n) (2 ^ 64) &&
   match wf_first_seg segs (bv_unsigned a) (bv_unsigned a + Z.of_nat n) with
   | Some seg => seg_writable seg && wf_chunks_ok (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) n
   | None => false
   end)%bool.

Lemma wf_hexc_lt : forall c, wf_hexc c = true -> (hex_nybble c <? 16)%N = true.
Proof.
  intros c H. unfold wf_hexc in H. unfold hex_nybble. apply N.ltb_lt.
  destruct (Uint63.leb 48%uint63 c && Uint63.leb c 57%uint63)%bool eqn:E1.
  - apply andb_true_iff in E1 as [E1 E2]. apply Uint63.leb_spec in E1, E2.
    change (Uint63.to_Z 48%uint63) with 48%Z in E1. change (Uint63.to_Z 57%uint63) with 57%Z in E2. lia.
  - cbn [orb] in H. rewrite H. apply andb_true_iff in H as [E3 E4]. apply Uint63.leb_spec in E3, E4.
    change (Uint63.to_Z 97%uint63) with 97%Z in E3. change (Uint63.to_Z 102%uint63) with 102%Z in E4. lia.
Qed.

Lemma wf_hex_ok_spec : forall n s j off,
  Uint63.to_Z j = (2 * Z.of_N off)%Z -> (2 * Z.of_N off + 2 * Z.of_nat n < Uint63.wB)%Z ->
  wf_hex_ok s j n = true -> forall i, (i < n)%nat -> exists b, hex_byte_at s (off + N.of_nat i)%N = Some b.
Proof.
  induction n as [|n IH]; intros s j off Hj Hw H i Hi; [lia|].
  cbn [wf_hex_ok] in H. apply andb_true_iff in H as [H Hrec]. apply andb_true_iff in H as [H Hlo].
  apply andb_true_iff in H as [Hlen Hhi]. pose proof (N2Z.is_nonneg off) as Hoff.
  destruct i as [|i].
  - rewrite N.add_0_r. unfold hex_byte_at. cbv zeta.
    assert (Ec : Uint63.of_Z (Z.of_N (2 * off)) = j).
    { apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec, Hj, N2Z.inj_mul. apply Z.mod_small. lia. }
    assert (Ec1 : Uint63.of_Z (Z.of_N (2 * off + 1)) = Uint63.add j 1%uint63).
    { apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec, Uint63.add_spec, Hj. change (Uint63.to_Z 1%uint63) with 1%Z.
      rewrite N2Z.inj_add, N2Z.inj_mul. change (Z.of_N 2) with 2%Z. change (Z.of_N 1) with 1%Z.
      rewrite (Z.mod_small (2 * Z.of_N off + 1)%Z) by lia. reflexivity. }
    rewrite Ec, Ec1, Hlen. cbn [orb]. apply wf_hexc_lt in Hhi. apply wf_hexc_lt in Hlo. rewrite Hhi, Hlo. cbn [andb].
    eexists; reflexivity.
  - destruct (IH s (Uint63.add j 2%uint63) (off + 1)%N) with (i := i) as [b Hb]; [ | lia | exact Hrec | lia | ].
    + rewrite Uint63.add_spec, Hj. change (Uint63.to_Z 2%uint63) with 2%Z. rewrite N2Z.inj_add. rewrite Z.mod_small by lia. lia.
    + exists b. replace (off + N.of_nat (S i))%N with (off + 1 + N.of_nat i)%N by lia. exact Hb.
Qed.

Lemma wf_chunk_hex : forall c off k, (off + N.of_nat k <= wf_chunk_bytes c)%N ->
  wf_hex_ok c (Uint63.of_Z (Z.of_N (2 * off))) k = true -> forall i, (i < k)%nat -> exists b, hex_byte_at c (off + N.of_nat i)%N = Some b.
Proof.
  intros c off k Hk H. pose proof (Uint63.to_Z_bounded (PrimString.length c)) as HL. unfold wf_chunk_bytes in Hk.
  pose proof (N2Z.is_nonneg off) as Hoff.
  assert (Hk' : (Z.of_N off + Z.of_nat k <= Uint63.to_Z (PrimString.length c) / 2)%Z).
  { apply N2Z.inj_le in Hk. rewrite N2Z.inj_add, nat_N_Z, Z2N.id in Hk; [exact Hk|]. apply Z.div_pos; lia. }
  assert (H2 : (2 * (Uint63.to_Z (PrimString.length c) / 2) <= Uint63.to_Z (PrimString.length c))%Z) by (apply Z.mul_div_le; lia).
  apply (wf_hex_ok_spec k c (Uint63.of_Z (Z.of_N (2 * off))) off); [ | lia | exact H].
  rewrite Uint63.of_Z_spec, N2Z.inj_mul. apply Z.mod_small. change (Z.of_N 2) with 2%Z. lia.
Qed.

Lemma wf_chunks_ok_spec : forall cs off n, wf_chunks_ok cs off n = true ->
  forall i, (i < n)%nat -> exists b, segment_byte_at cs (off + N.of_nat i)%N = Some b.
Proof.
  induction cs as [|c rest IH]; intros off n H i Hi.
  - destruct n; [lia | discriminate H].
  - destruct n as [|n0]; [lia|]. cbn [wf_chunks_ok] in H. fold (wf_chunks_ok rest) in H.
    cbn [segment_byte_at]. fold (wf_chunk_bytes c).
    destruct (off <? wf_chunk_bytes c)%N eqn:Eo.
    + apply N.ltb_lt in Eo.
      destruct (Nat.leb (S n0) (N.to_nat (wf_chunk_bytes c - off))) eqn:El.
      * apply Nat.leb_le in El.
        assert (Ei : (off + N.of_nat i < wf_chunk_bytes c)%N) by lia.
        apply N.ltb_lt in Ei. rewrite Ei. exact (wf_chunk_hex c off (S n0) ltac:(lia) H i Hi).
      * apply Nat.leb_gt in El. apply andb_true_iff in H as [H1 H2].
        destruct (Nat.lt_ge_cases i (N.to_nat (wf_chunk_bytes c - off))) as [Hlt|Hge].
        -- assert (Ei : (off + N.of_nat i < wf_chunk_bytes c)%N) by lia.
           apply N.ltb_lt in Ei. rewrite Ei. exact (wf_chunk_hex c off (N.to_nat (wf_chunk_bytes c - off)) ltac:(lia) H1 i Hlt).
        -- assert (Ei : (off + N.of_nat i <? wf_chunk_bytes c)%N = false) by (apply N.ltb_ge; lia).
           rewrite Ei.
           destruct (IH 0%N (S n0 - N.to_nat (wf_chunk_bytes c - off))%nat H2 (i - N.to_nat (wf_chunk_bytes c - off))%nat ltac:(lia)) as [b Hb].
           exists b. replace (off + N.of_nat i - wf_chunk_bytes c)%N with (0 + N.of_nat (i - N.to_nat (wf_chunk_bytes c - off)))%N by lia. exact Hb.
    + apply N.ltb_ge in Eo.
      assert (Ei : (off + N.of_nat i <? wf_chunk_bytes c)%N = false) by (apply N.ltb_ge; lia).
      rewrite Ei. destruct (IH (off - wf_chunk_bytes c)%N (S n0) H i Hi) as [b Hb]. exists b.
      replace (off + N.of_nat i - wf_chunk_bytes c)%N with (off - wf_chunk_bytes c + N.of_nat i)%N by lia. exact Hb.
Qed.

Lemma wf_first_seg_find : forall segs lo hi seg, wf_first_seg segs lo hi = Some seg ->
  forall z, (lo <= z)%Z -> (z + 1 <= hi)%Z -> find_segment segs z 1 = Some seg.
Proof.
  induction segs as [|s rest IH]; intros lo hi seg H z H1 H2; [discriminate H|].
  cbn [wf_first_seg] in H. cbn [find_segment].
  destruct (Z.leb (Z.of_N (seg_base s)) lo && Z.leb hi (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
  - injection H as <-. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    assert (F : (Z.leb (Z.of_N (seg_base s)) z && Z.leb (z + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool = true)
      by (apply andb_true_iff; split; apply Z.leb_le; lia).
    rewrite F. reflexivity.
  - destruct (Z.leb hi (Z.of_N (seg_base s)) || Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) lo)%bool eqn:E2; [|discriminate H].
    assert (F : (Z.leb (Z.of_N (seg_base s)) z && Z.leb (z + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool = false).
    { apply orb_true_iff in E2 as [E2|E2]; apply Z.leb_le in E2; apply andb_false_iff; [left | right]; apply Z.leb_gt; lia. }
    rewrite F. exact (IH lo hi seg H z H1 H2).
Qed.

Lemma wseg_ok_of_seg : forall segs seg n (a : word),
  (bv_unsigned a + Z.of_nat n < 2 ^ 64)%Z ->
  (forall z, (bv_unsigned a <= z)%Z -> (z < bv_unsigned a + Z.of_nat n)%Z -> find_segment segs z 1 = Some seg) ->
  seg_writable seg = true ->
  (forall i, (i < n)%nat -> exists b, segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)) + N.of_nat i)%N = Some b) ->
  (Z.of_N (seg_base seg) <= bv_unsigned a)%Z ->
  wseg_ok segs a n = true.
Proof.
  intros segs seg n. induction n as [|n IH]; intros a Hr Hf Hw Hb Hbase; [reflexivity|].
  cbn [wseg_ok]. rewrite (Hf (bv_unsigned a) ltac:(lia) ltac:(lia)).
  destruct (Hb 0%nat ltac:(lia)) as [b0 Hb0]. rewrite N.add_0_r in Hb0. rewrite Hb0, Hw. cbn [andb].
  assert (Ua : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z).
  { rewrite bv_add_unsigned. rewrite bv_wrap_small; [reflexivity|]. pose proof (bv_unsigned_in_range 64 a).
    change (bv_unsigned (1%bv : bv 64)) with 1%Z. unfold bv_modulus. lia. }
  apply IH; rewrite ?Ua.
  - lia.
  - intros z H1 H2. apply Hf; lia.
  - exact Hw.
  - intros i Hi. destruct (Hb (S i) ltac:(lia)) as [b Hbi]. exists b.
    replace (Z.to_N (bv_unsigned a + 1 - Z.of_N (seg_base seg)) + N.of_nat i)%N
      with (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)) + N.of_nat (S i))%N by lia. exact Hbi.
  - lia.
Qed.

Lemma wseg_fast_ok : forall segs a n, wseg_fast segs a n = true -> wseg_ok segs a n = true.
Proof.
  intros segs a n H. unfold wseg_fast in H. apply andb_true_iff in H as [Hr H]. apply Z.ltb_lt in Hr.
  destruct (wf_first_seg segs (bv_unsigned a) (bv_unsigned a + Z.of_nat n)) as [seg|] eqn:E; [|discriminate H].
  apply andb_true_iff in H as [Hw Hc].
  destruct n as [|n0]; [reflexivity|].
  assert (Hbase : (Z.of_N (seg_base seg) <= bv_unsigned a)%Z).
  { clear - E. revert E. generalize (bv_unsigned a + Z.of_nat (S n0))%Z as hi. intros hi E.
    induction segs as [|s rest IH]; [discriminate E|]. cbn [wf_first_seg] in E.
    destruct (Z.leb (Z.of_N (seg_base s)) (bv_unsigned a) && Z.leb hi (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:F.
    - injection E as <-. apply andb_true_iff in F as [F1 _]. apply Z.leb_le in F1. exact F1.
    - destruct (_ || _)%bool; [exact (IH E) | discriminate E]. }
  apply (wseg_ok_of_seg segs seg); [exact Hr | | exact Hw | | exact Hbase].
  - intros z H1 H2. apply (wf_first_seg_find segs _ _ seg E z); lia.
  - exact (wf_chunks_ok_spec _ _ _ Hc).
Qed.
End WsegFast.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout State Run.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim Footprint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition mem_grows (m m' : word -> option byte) : Prop :=
  forall x, m x <> None -> m' x <> None.

Lemma mem_grows_refl : forall m, mem_grows m m.
Proof. intros m x H. exact H. Qed.

Lemma mem_grows_trans : forall m1 m2 m3,
  mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H12 H23 x Hx. apply H23, H12, Hx. Qed.

(* [comment removed for export] *)
Lemma wview_grows : forall segs m m' x,
  mem_grows m m' ->
  wview segs m x <> None -> wview segs m' x <> None.
Proof.
  intros segs m m' x Hg Hx. unfold wview in *.
  destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
  destruct (m x) as [b|] eqn:Hm.
  - exfalso. apply (Hg x); [rewrite Hm; discriminate|exact Hm'].
  - exact Hx.
Qed.

Lemma store_ok_mono : forall segs n m m' a,
  mem_grows m m' ->
  store_ok segs m a n = true -> store_ok segs m' a n = true.
Proof.
  intros segs n; induction n as [|n IH]; intros m m' a Hg H; [reflexivity|].
  cbn [store_ok] in *.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  destruct (wview segs m' a) as [b'|] eqn:Hv'.
  - apply (IH m m'); assumption.
  - exfalso. apply (wview_grows segs m m' a Hg); [rewrite Hv; discriminate|exact Hv'].
Qed.

(* [comment removed for export] *)

Lemma wbytes_grows : forall bs m a, mem_grows m (wbytes m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [wbytes]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_zeros_grows : forall zs m, mem_grows m (apply_zeros m zs).
Proof.
  intros zs m x Hx. unfold apply_zeros.
  destruct zs as [|z zs']; [exact Hx|].
  destruct (zeros_cover (z :: zs') x); [discriminate|exact Hx].
Qed.

Lemma zmem_grows : forall m b l, mem_grows m (zmem m b l).
Proof.
  intros m b l x Hx. unfold zmem.
  destruct (Z.leb _ _ && Z.ltb _ _)%bool; [discriminate|exact Hx].
Qed.

Lemma write_to_mem_grows : forall bs m a, mem_grows m (write_to_mem m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [write_to_mem]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_writes_grows : forall ws m, mem_grows m (apply_writes m ws).
Proof.
  induction ws as [|w ws' IH]; intros m x Hx.
  - exact Hx.
  - destruct w as [a bs]. cbn [apply_writes].
    apply IH. apply write_to_mem_grows. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_all : forall segs n m a,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      wview segs m x <> None) ->
  store_ok segs m a n = true.
Proof.
  intros segs n; induction n as [|n IH]; intros m a Hnw Hall; [reflexivity|].
  cbn [store_ok].
  destruct (wview segs m a) as [b|] eqn:Hv.
  2: { exfalso. refine (Hall a _ Hv). rewrite Nat2Z.inj_succ. lia. }
  (* [comment removed for export] *)
  destruct n as [|n']; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hnw.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
    by (apply u_add1; rewrite Nat2Z.inj_succ in Hnw; lia).
  apply IH.
  - rewrite Hu1. lia.
  - intros x Hx. rewrite Hu1 in Hx. apply Hall.
    rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Lemma wrap_mem_window_defined : forall ph sp argv envp (x : word) uid hw rnd,
  bv_unsigned sp - stack_max_size <= bv_unsigned x ->
  bv_unsigned x < bv_unsigned sp ->
  wrap_mem ph sp argv envp uid hw rnd x <> None.
Proof.
  intros ph sp argv envp x uid hw rnd Hlo Hhi. unfold wrap_mem.
  destruct (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x) as [b|];
    [discriminate|].
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  cbn. discriminate.
Qed.

Lemma store_ok_wrap_window : forall segs ph sp argv envp a n uid hw rnd,
  bv_unsigned sp - stack_max_size <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
  store_ok segs (wrap_mem ph sp argv envp uid hw rnd) a n = true.
Proof.
  intros segs ph sp argv envp a n uid hw rnd Hlo Hhi.
  assert (Hsp : bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
  apply store_ok_of_all; [lia|].
  intros x Hx. unfold wview.
  destruct (wrap_mem ph sp argv envp uid hw rnd x) as [b|] eqn:Hw; [discriminate|].
  exfalso. revert Hw. apply wrap_mem_window_defined; lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_zeros_hit : forall segs m zs a n,
  zs <> [] ->
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      zeros_cover zs x = true) ->
  store_ok segs (apply_zeros m zs) a n = true.
Proof.
  intros segs m zs a n Hne Hnw Hcov.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, apply_zeros.
  destruct zs as [|z zs']; [contradiction|].
  rewrite (Hcov x Hx). discriminate.
Qed.

(* [comment removed for export] *)
Lemma store_ok_zmem : forall segs m (b l a : word) (n : nat),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
  store_ok segs (zmem m b l) a n = true.
Proof.
  intros segs m b l a n Hnw Hlo Hhi.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  cbn. discriminate.
Qed.






(* [comment removed for export] *)
Lemma store_ok_wseg : forall segs m a n,
  wseg_ok segs a n = true -> store_ok segs m a n = true.
Proof.
  intros segs m a n; revert a m; induction n as [|n IH]; intros a m H; [reflexivity|].
  cbn [wseg_ok] in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
  apply andb_true_iff in H as [H Hrec].
  apply andb_true_iff in H as [Hwr Hbyte].
  destruct (segment_byte_at (seg_bytes seg)
              (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
    [|discriminate].
  cbn [store_ok]. unfold wview at 1.
  destruct (m a) as [b0|]; [apply IH, Hrec|].
  rewrite Hseg, Hwr, Hb. apply IH, Hrec.
Qed.

(* [comment removed for export] *)
Lemma store_ok_all : forall segs m n a,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok segs m a n = true ->
  forall x : word,
    bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
    wview segs m x <> None.
Proof.
  intros segs m n; induction n as [|n IH]; intros a Hnw H x Hx;
    [cbn in Hx; lia|].
  cbn [store_ok] in H.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  rewrite Nat2Z.inj_succ in Hnw, Hx.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  { assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Hv. discriminate. }
  (* [comment removed for export] *)
  assert (Hn : (1 <= Z.of_nat n)%Z) by lia.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
  (* [comment removed for export] *)
  eapply IH; [ | exact H | ]; lia.
Qed.

Lemma store_ok_sub : forall segs m (lo a : word) (N n : nat),
  bv_unsigned lo + Z.of_nat N <= 2 ^ 64 ->
  store_ok segs m lo N = true ->
  bv_unsigned lo <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned lo + Z.of_nat N ->
  store_ok segs m a n = true.
Proof.
  intros segs m lo a N n Hnw Hok Hl Hh.
  apply store_ok_of_all; [lia|].
  intros x Hx. apply (store_ok_all segs m N lo Hnw Hok). lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_window : forall segs m (lo a : word) (N n : nat) (base hi : Z),
  bv_unsigned lo = base ->
  base + Z.of_nat N = hi ->
  hi <= 2 ^ 64 ->
  wseg_ok segs lo N = true ->
  base <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= hi ->
  store_ok segs m a n = true.
Proof.
  intros segs m lo a N n base hi Hbase Htop Hnw Hw Hl Hh.
  eapply store_ok_sub; [ | apply store_ok_wseg, Hw | | ]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_read_aux : forall segs m n (a : word),
  store_ok segs m a n = true ->
  exists w, read_bytes_aux (wview segs m) a n = Some w.
Proof.
  intros segs m n; induction n as [|n IH]; intros a H.
  - exists []. reflexivity.
  - cbn [store_ok] in H. cbn [read_bytes_aux].
    destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
    destruct (IH (a + 1)%bv H) as [w Hw]. rewrite Hw. exists (b :: w). reflexivity.
Qed.







(* [comment removed for export] *)
Ltac store_ok_peel :=
  repeat first
    [ eapply store_ok_mono; [apply wbytes_grows|]
    | eapply store_ok_mono; [apply write_to_mem_grows|]
    | eapply store_ok_mono; [apply apply_zeros_grows|]
    | eapply store_ok_mono; [apply apply_writes_grows|] ].

(* [comment removed for export] *)
Ltac store_ok_base :=
  first
    [ apply store_ok_wrap_window; unfold stack_max_size; u_norm; lia
    | eapply store_ok_zeros_hit;
      [ discriminate | u_norm; lia | intros; u_norm; lia ]
    | apply store_ok_zmem; u_norm; lia ].

(* [comment removed for export] *)
Ltac solve_store_ok :=
  store_ok_peel;
  first [ store_ok_base
        | eapply store_ok_mono; [apply zmem_grows|];
          store_ok_peel; store_ok_base ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Create HintDb store_ok_db.

Ltac store_ok_grows := solve [ eauto with store_ok_db ].

Ltac solve_store_ok_inv :=
  first [ solve_store_ok
        | store_ok_peel;
          eapply store_ok_mono; [ store_ok_grows | ]; solve_store_ok ].

(* [comment removed for export] *)
Ltac solve_mem_grows :=
  repeat first
    [ solve [ eauto with store_ok_db ]
    | apply mem_grows_refl
    | eapply mem_grows_trans; [ | apply wbytes_grows ]
    | eapply mem_grows_trans; [ | apply zmem_grows ]
    | eapply mem_grows_trans; [ | apply write_to_mem_grows ]
    | eapply mem_grows_trans; [ | apply apply_zeros_grows ]
    | eapply mem_grows_trans; [ | apply apply_writes_grows ] ].
