(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SReach LazyRestrict LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Exec MState.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Generic.
  (* [comment removed for export] *)
  Variable St : Type.
  Variables aL aS aZr : St -> list (word * word).
  (* [comment removed for export] *)
  Variable K : St -> Model -> Prop.
  Variable MPRES : Model -> Model -> Prop.

  (* [comment removed for export] *)
  Hypothesis K_mat : forall s mo mo',
    K s mo -> same_but_materialized mo mo' -> K s mo'.
  Hypothesis MPRES_mat : forall mo mo',
    same_but_materialized mo mo' -> MPRES mo mo'.

  Definition AKREL (s : St) (c : config) : Prop :=
    lzok asegs (aL s) (aS s) (aZr s) c /\ K s (cfg_model c).

  Definition VIS (s : St) (msF : machine_state) : machine_state :=
    restrict (aL s) (aS s) msF.

  Definition SR : (config -> Prop) -> config -> Prop := sreach asegs.

  (* [comment removed for export] *)
  Lemma ASR_done : forall (Q : config -> Prop) c, Q c -> SR Q c.
  Proof. intros Q c H. apply sreach_done. exact H. Qed.

  Lemma ASR_mono : forall (Q Q' : config -> Prop) c,
    SR Q c -> (forall c', Q c' -> Q' c') -> SR Q' c.
  Proof. intros Q Q' c H HQ. eapply sreach_mono; eassumption. Qed.

  Lemma ASR_seq : forall (Q1 Q2 : config -> Prop) c,
    SR Q1 c -> (forall c', Q1 c' -> SR Q2 c') -> SR Q2 c.
  Proof. intros Q1 Q2 c H K'. eapply sreach_seq; eassumption. Qed.

  (* [comment removed for export] *)
  Theorem ASR_lift : forall (P : machine_state -> Prop) (Q : config -> Prop) s msF mo,
    AKREL s (mkCfg msF mo) ->
    Exec.evt asegs P (VIS s msF) ->
    (forall msF' mo', AKREL s (mkCfg msF' mo') -> MPRES mo mo' -> P (VIS s msF') ->
                      SR Q (mkCfg msF' mo')) ->
    SR Q (mkCfg msF mo).
  Proof.
    intros P Q s msF mo [Hok HK] Hevt Hk. unfold SR, VIS in *.
    eapply (evt_sreach_lazy_k asegs (aL s) (aS s) (aZr s) P msF mo Q Hok Hevt).
    intros msF' mo' Hok' Hsame _ HP. apply Hk; [| apply MPRES_mat; exact Hsame | exact HP].
    split; [exact Hok' |]. cbn. eapply K_mat; [exact HK | exact Hsame].
  Qed.

  (* [comment removed for export] *)
  Corollary ASR_lift_at : forall (P : machine_state -> Prop) (Q : config -> Prop) s msF ms mo,
    AKREL s (mkCfg msF mo) ->
    VIS s msF = ms ->
    Exec.evt asegs P ms ->
    (forall msF' mo', AKREL s (mkCfg msF' mo') -> MPRES mo mo' -> P (VIS s msF') ->
                      SR Q (mkCfg msF' mo')) ->
    SR Q (mkCfg msF mo).
  Proof. intros P Q s msF ms mo HA <- He Hk. eapply ASR_lift; eassumption. Qed.

  (* [comment removed for export] *)
  Lemma AKREL_halted : forall s c, AKREL s c -> m_halted (cfg_model c) = None.
  Proof. intros s c [Hok _]. exact (lzok_halted Hok). Qed.

  Lemma AKREL_lzok : forall s c, AKREL s c -> lzok asegs (aL s) (aS s) (aZr s) c.
  Proof. intros s c [Hok _]. exact Hok. Qed.

  (* [comment removed for export] *)
  Lemma VIS_MS : forall s R F pc fc rv m ro,
    exists m', VIS s (MState.MS R F pc fc rv m ro) = MState.MS R F pc fc rv m' ro.
  Proof. intros. exists (restrict_mem (aL s) (aS s) m). apply restrict_MS. Qed.

  (* [comment removed for export] *)
  Theorem ASR_SR_laws :
       (forall (Q : config -> Prop) c, Q c -> SR Q c)
    /\ (forall (Q Q' : config -> Prop) c, SR Q c -> (forall c', Q c' -> Q' c') -> SR Q' c)
    /\ (forall (Q1 Q2 : config -> Prop) c, SR Q1 c -> (forall c', Q1 c' -> SR Q2 c') -> SR Q2 c)
    /\ (forall (P : machine_state -> Prop) (Q : config -> Prop) s msF ms mo,
          AKREL s (mkCfg msF mo) -> VIS s msF = ms -> Exec.evt asegs P ms ->
          (forall msF' mo', AKREL s (mkCfg msF' mo') -> MPRES mo mo' -> P (VIS s msF') -> SR Q (mkCfg msF' mo')) ->
          SR Q (mkCfg msF mo)).
  Proof.
    split; [exact ASR_done|]. split; [exact ASR_mono|]. split; [exact ASR_seq|]. exact ASR_lift_at.
  Qed.

  Theorem ASR_AKREL_laws :
       (forall s c, AKREL s c -> m_halted (cfg_model c) = None)
    /\ (forall s R F pc fc rv m ro, exists m', VIS s (MState.MS R F pc fc rv m ro) = MState.MS R F pc fc rv m' ro).
  Proof. split; [exact AKREL_halted | exact VIS_MS]. Qed.

  (* [comment removed for export] *)
  Lemma ASR_realizes : forall (Q : config -> Prop) c T,
    SR Q c -> (forall c', Q c' -> ShapeAlg.realizes asegs c' T) -> ShapeAlg.realizes asegs c T.
  Proof. intros Q c T H Hk. eapply sreach_realizes; eassumption. Qed.
End Generic.
