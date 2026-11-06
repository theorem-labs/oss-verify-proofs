(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section ImplRz.

Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Hypothesis NS : node_sound node segs at_node nstep nexit minv nsafe.

Local Notation itreeN := (itree node).
Local Notation implN := (impl segs at_node).
Local Notation realizesS := (realizes segs).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ans_idx (n : node) (mo : Model) : Type :=
  ({ p : resp * Model * list event | nstep n mo (fst (fst p)) (snd (fst p)) (snd p) }
   + { q : word * Model | nexit n mo (fst q) (snd q) })%type.

Definition ans_evs (n : node) (mo : Model) (i : ans_idx n mo) : list event :=
  match i with
  | inl (exist _ p _) => snd p
  | inr (exist _ q _) => [ExitEv (fst q) (m_fs (snd q))]
  end.

Inductive trz {R : Type} : itreeN R -> Model -> (R -> Model -> TSet) -> TSet -> Prop :=
| trz_ret : forall r mo K,
    trz (Ret r) mo K (K r mo)
| trz_vis : forall n (k : resp -> itreeN R) mo K (TT : ans_idx n mo -> TSet) (i0 : ans_idx n mo),
    minv mo -> nsafe n mo ->
    (forall rsp mo' evs (H : nstep n mo rsp mo' evs),
        trz (k rsp) mo' K (TT (inl (exist _ (rsp, mo', evs) H)))) ->
    (forall code mo' (H : nexit n mo code mo'),
        TT (inr (exist _ (code, mo') H)) = t_nil) ->
    trz (Vis n k) mo K (t_alt (fun i => t_emit (ans_evs n mo i) (TT i)))
| trz_conseq : forall t mo K T T',
    trz t mo K T -> t_eq T T' -> trz t mo K T'.

(* [comment removed for export] *)

Lemma rz_msteps_lib : forall ms ms' mo T,
  m_halted mo = None -> m_vm_lazy mo = [] ->
  Exec.msteps segs ms ms' ->
  realizesS (mkCfg ms' mo) T -> realizesS (mkCfg ms mo) T.
Proof.
  intros ms ms' mo T Hh Hl Hms. induction Hms as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH]; intros Hc.
  - exact Hc.
  - eapply rz_step; [exact Hh | exact Hl | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)
Definition nxcfg (n : node) (mo : Model) (ms1 : machine_state) (i : ans_idx n mo) : config :=
  match i with
  | inl (exist _ p _) => mkCfg (nret ms1 (fst (fst p))) (snd (fst p))
  | inr (exist _ q _) => mkCfg ms1 (snd q)
  end.

Lemma node_ok_at : forall n ms1 mo,
  at_node n ms1 -> m_halted mo = None -> minv mo -> nsafe n mo ->
  node_ok segs (mkCfg ms1 mo) (ans_idx n mo) (ans_evs n mo) (nxcfg n mo ms1).
Proof.
  intros n ms1 mo Hat Hh Hmi Hsafe. split.
  - intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn.
    + destruct (ns_sound _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hmi Hsafe Hst) as (_ & _ & Hss). exact Hss.
    + destruct (ns_exit _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hmi Hsafe Hxt) as (_ & Hss). exact Hss.
  - intros e st Hss.
    destruct (ns_complete _ _ _ _ _ _ _ NS n ms1 mo e st Hat Hh Hmi Hsafe Hss)
      as [(rsp & mo' & -> & Hst) | (code & mo' & -> & Hxt & ->)].
    + exists (inl (exist _ (rsp, mo', e) Hst)). split; reflexivity.
    + exists (inr (exist _ (code, mo') Hxt)). split; reflexivity.
Qed.

Lemma ans_idx_inh : forall n ms1 mo,
  at_node n ms1 -> m_halted mo = None -> minv mo -> nsafe n mo -> inhabited (ans_idx n mo).
Proof.
  intros n ms1 mo Hat Hh Hmi Hsafe.
  destruct (ns_progress _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hmi Hsafe)
    as [(rsp & mo' & evs & H) | (code & mo' & H)].
  - exact (inhabits (inl (exist _ (rsp, mo', evs) H))).
  - exact (inhabits (inr (exist _ (code, mo') H))).
Qed.

Theorem impl_trz_realizes : forall {R} (t : itreeN R) Q ms mo K T,
  implN t Q ms ->
  trz t mo K T ->
  m_halted mo = None -> minv mo ->
  (forall r ms' mo', Q r ms' -> m_halted mo' = None -> minv mo' ->
     realizesS (mkCfg ms' mo') (K r mo')) ->
  realizesS (mkCfg ms mo) T.
Proof.
  intros R t Q ms mo K T Himpl Htrz. revert ms Himpl.
  induction Htrz as [r mo K | n k mo K TT i0 Hminv Hsafe Hk IH Hex | t mo K T T' Ht IH Heq];
    intros ms Himpl Hh Hmi HK.
  - (* [comment removed for export] *)
    cbn in Himpl. destruct Himpl as (ms' & Hms & HQ).
    eapply rz_msteps_lib; [exact Hh | apply (ns_lazy _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    apply HK; assumption.
  - (* [comment removed for export] *)
    cbn in Himpl. destruct Himpl as (ms1 & Hms & Hat & Hcont).
    eapply rz_msteps_lib; [exact Hh | apply (ns_lazy _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    apply (rz_node segs (mkCfg ms1 mo) (ans_idx n mo) (ans_evs n mo) (nxcfg n mo ms1) TT i0).
    + apply node_ok_at; assumption.
    + (* [comment removed for export] *)
      intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn.
      * destruct (ns_sound _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hmi Hsafe Hst) as (Hh' & Hmi' & _).
        apply (IH rsp mo' evs Hst (nret ms1 rsp) (Hcont rsp) Hh' Hmi' HK).
      * rewrite (Hex code mo' Hxt).
        apply rz_halt. cbn.
        destruct (ns_exit _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hmi Hsafe Hxt) as (Hh' & _).
        rewrite Hh'. discriminate.
  - (* [comment removed for export] *)
    eapply rz_conseq; [apply IH; assumption | exact Heq].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma trz_vis_silent : forall {R} n (k : resp -> itreeN R) mo K T,
  minv mo -> nsafe n mo ->
  (exists rsp mo' evs, nstep n mo rsp mo' evs) ->
  (forall rsp mo' evs, nstep n mo rsp mo' evs -> evs = [] /\ trz (k rsp) mo' K T) ->
  (forall code mo', ~ nexit n mo code mo') ->
  T [] ->
  trz (Vis n k) mo K T.
Proof.
  intros R n k mo K T Hmi Hsafe (rsp0 & mo0 & evs0 & H0) Hk Hnx HT0.
  eapply trz_conseq.
  - apply (trz_vis n k mo K (fun _ => T) (inl (exist _ (rsp0, mo0, evs0) H0)) Hmi Hsafe).
    + intros rsp mo' evs H. destruct (Hk rsp mo' evs H) as [_ Ht]. exact Ht.
    + intros code mo' H. exfalso. exact (Hnx code mo' H).
  - intros tr. split.
    + intros [i Hi]. destruct i as [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn in Hi.
      * destruct (Hk rsp mo' evs Hst) as [-> _].
        destruct Hi as [Hp | (tr' & -> & Ht)]; [| exact Ht].
        apply is_prefix_nil_r in Hp. subst tr. exact HT0.
      * exfalso. exact (Hnx code mo' Hxt).
    + intros Ht. exists (inl (exist _ (rsp0, mo0, evs0) H0)). cbn.
      destruct (Hk rsp0 mo0 evs0 H0) as [-> _]. right. exists tr. split; [reflexivity | exact Ht].
Qed.

(* [comment removed for export] *)
Lemma trz_bind : forall {A B} (t : itreeN A) (f : A -> itreeN B) mo (K1 : A -> Model -> TSet) K T,
  trz t mo K1 T ->
  (forall a mo', trz (f a) mo' K (K1 a mo')) ->
  trz (bind node t f) mo K T.
Proof.
  intros A B t f mo K1 K T Ht. induction Ht as [r mo K1 | n k mo K1 TT i0 Hmi Hsafe Hk IH Hex | t mo K1 T T' Ht IH Heq];
    intros Hf.
  - cbn. apply Hf.
  - cbn. apply (trz_vis n (fun x => bind node (k x) f) mo K TT i0 Hmi Hsafe).
    + intros rsp mo' evs H. apply (IH rsp mo' evs H). exact Hf.
    + exact Hex.
  - eapply trz_conseq; [apply IH; exact Hf | exact Heq].
Qed.

(* [comment removed for export] *)
Lemma trz_ebind : forall {A B} (t : itreeN (Exc.exc A)) (f : A -> itreeN (Exc.exc B)) mo
                         (K1 : Exc.exc A -> Model -> TSet) K T,
  trz t mo K1 T ->
  (forall a mo', trz (f a) mo' K (K1 (Exc.Ok a) mo')) ->
  (forall mo', K1 Exc.Unr mo' = K Exc.Unr mo') ->
  trz (ebind t f) mo K T.
Proof.
  intros A B t f mo K1 K T Ht Hf Hunr. unfold ebind. eapply trz_bind; [exact Ht|].
  intros [|a] mo'; cbn.
  - rewrite Hunr. apply trz_ret.
  - apply Hf.
Qed.


(* [comment removed for export] *)
Fixpoint tsil {R : Type} (t : itreeN R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo
      /\ (forall code mo', ~ nexit n mo code mo')
      /\ (forall rsp mo' evs, nstep n mo rsp mo' evs -> evs = [] /\ tsil (k rsp) mo' P)
  end.

Lemma tsil_mono : forall {R} (t : itreeN R) mo (P P' : R -> Model -> Prop),
  tsil t mo P -> (forall r mo', P r mo' -> P' r mo') -> tsil t mo P'.
Proof.
  intros R t; induction t as [r | n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as (Hsafe & Hnx & Hk).
    split; [exact Hsafe|]. split; [exact Hnx|].
    intros rsp mo' evs Hst. split; [exact (proj1 (Hk rsp mo' evs Hst))|].
    eapply IH; [exact (proj2 (Hk rsp mo' evs Hst)) | exact HP].
Qed.

Lemma tsil_bind : forall {A B} (t : itreeN A) (f : A -> itreeN B) mo (P1 : A -> Model -> Prop) P,
  tsil t mo P1 ->
  (forall a mo', P1 a mo' -> tsil (f a) mo' P) ->
  tsil (bind node t f) mo P.
Proof.
  intros A B t; induction t as [r | n k IH]; intros f mo P1 P H Hf; cbn in *.
  - apply Hf. exact H.
  - destruct H as (Hsafe & Hnx & Hk).
    split; [exact Hsafe|]. split; [exact Hnx|].
    intros rsp mo' evs Hst. split; [exact (proj1 (Hk rsp mo' evs Hst))|].
    eapply IH; [exact (proj2 (Hk rsp mo' evs Hst)) | exact Hf].
Qed.

Lemma tsil_ebind : forall {A B} (t : itreeN (Exc.exc A)) (f : A -> itreeN (Exc.exc B)) mo
                          (P1 : A -> Model -> Prop) (P : Exc.exc B -> Model -> Prop),
  tsil t mo (fun r mo' => match r with Exc.Unr => False | Exc.Ok a => P1 a mo' end) ->
  (forall a mo', P1 a mo' -> tsil (f a) mo' P) ->
  tsil (ebind t f) mo P.
Proof.
  intros A B t f mo P1 P H Hf. unfold ebind. eapply tsil_bind; [exact H|].
  intros [|a] mo'; cbn; [intros []| apply Hf].
Qed.

Lemma tsil_ret : forall {R} (r : R) mo (P : R -> Model -> Prop), P r mo -> tsil (Ret r) mo P.
Proof. intros; cbn; assumption. Qed.

(* [comment removed for export] *)
Theorem impl_tsil_realizes : forall {R} (t : itreeN R) Q ms mo P (T : TSet),
  implN t Q ms ->
  tsil t mo P ->
  m_halted mo = None -> minv mo ->
  T [] ->
  (forall r ms' mo', Q r ms' -> P r mo' -> m_halted mo' = None -> minv mo' ->
     realizesS (mkCfg ms' mo') T) ->
  realizesS (mkCfg ms mo) T.
Proof.
  intros R t; induction t as [r | n k IH]; intros Q ms mo P T Himpl Hsil Hh Hmi HT0 HK; cbn in Himpl, Hsil.
  - destruct Himpl as (ms' & Hms & HQ).
    eapply rz_msteps_lib; [exact Hh | apply (ns_lazy _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    apply (HK r ms' mo HQ Hsil Hh Hmi).
  - destruct Himpl as (ms1 & Hms & Hat & Hcont).
    destruct Hsil as (Hsafe & Hnx & Hk).
    assert (Hex : exists rsp0 mo0 evs0, nstep n mo rsp0 mo0 evs0).
    { destruct (ns_progress _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hmi Hsafe)
        as [(rsp0 & mo0 & evs0 & H0) | (code & mo' & H)]; [exists rsp0, mo0, evs0; exact H0|].
      exfalso. exact (Hnx code mo' H). }
    destruct Hex as (rsp0 & mo0 & evs0 & H0).
    eapply rz_msteps_lib; [exact Hh | apply (ns_lazy _ _ _ _ _ _ _ NS); exact Hmi | exact Hms |].
    eapply rz_conseq.
    + apply (rz_node segs (mkCfg ms1 mo) (ans_idx n mo) (ans_evs n mo) (nxcfg n mo ms1) (fun _ => T)
               (inl (exist _ (rsp0, mo0, evs0) H0))).
      * apply node_ok_at; assumption.
      * intros [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn.
        -- destruct (ns_sound _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hmi Hsafe Hst) as (Hh' & Hmi' & _).
           destruct (Hk rsp mo' evs Hst) as [_ Hsil'].
           apply (IH rsp Q (nret ms1 rsp) mo' P T (Hcont rsp) Hsil' Hh' Hmi' HT0 HK).
        -- exfalso. exact (Hnx code mo' Hxt).
    + intros tr. split.
      * intros [i Hi]. destruct i as [[[[rsp mo'] evs] Hst] | [[code mo'] Hxt]]; cbn in Hi.
        -- destruct (Hk rsp mo' evs Hst) as [-> _].
           destruct Hi as [Hp | (tr' & -> & Ht)]; [| exact Ht].
           apply is_prefix_nil_r in Hp. subst tr. exact HT0.
        -- exfalso. exact (Hnx code mo' Hxt).
      * intros Ht. exists (inl (exist _ (rsp0, mo0, evs0) H0)). cbn.
        destruct (Hk rsp0 mo0 evs0 H0) as [-> _]. right. exists tr. split; [reflexivity | exact Ht].
Qed.

End ImplRz.
