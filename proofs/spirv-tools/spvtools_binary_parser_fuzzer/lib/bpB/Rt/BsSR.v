(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BReach BazyRestrict BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BExec BMState.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Generic.

  Variable St : Type.
  Variables aL aS aZr : St -> list (word * word).

  Variable K : St -> Model -> Prop.
  Variable MPRES : Model -> Model -> Prop.

  Hypothesis K_mat : forall s mo mo',
    K s mo -> same_but_materialized mo mo' -> K s mo'.
  Hypothesis MPRES_mat : forall mo mo',
    same_but_materialized mo mo' -> MPRES mo mo'.

  Definition AKREL (s : St) (c : config) : Prop :=
    lzok asegs (aL s) (aS s) (aZr s) c /\ K s (cfg_model c).

  Definition VIS (s : St) (msF : machine_state) : machine_state :=
    restrict (aL s) (aS s) msF.

  Definition SR : (config -> Prop) -> config -> Prop := sreach asegs.

  Lemma ASR_done : forall (Q : config -> Prop) c, Q c -> SR Q c.
  Proof. intros Q c H. apply sreach_done. exact H. Qed.

  Lemma ASR_mono : forall (Q Q' : config -> Prop) c,
    SR Q c -> (forall c', Q c' -> Q' c') -> SR Q' c.
  Proof. intros Q Q' c H HQ. eapply sreach_mono; eassumption. Qed.

  Lemma ASR_seq : forall (Q1 Q2 : config -> Prop) c,
    SR Q1 c -> (forall c', Q1 c' -> SR Q2 c') -> SR Q2 c.
  Proof. intros Q1 Q2 c H K'. eapply sreach_seq; eassumption. Qed.

  Theorem ASR_lift : forall (P : machine_state -> Prop) (Q : config -> Prop) s msF mo,
    AKREL s (mkCfg msF mo) ->
    BExec.evt asegs P (VIS s msF) ->
    (forall msF' mo', AKREL s (mkCfg msF' mo') -> MPRES mo mo' -> P (VIS s msF') ->
                      SR Q (mkCfg msF' mo')) ->
    SR Q (mkCfg msF mo).
  Proof.
    intros P Q s msF mo [Hok HK] Hevt Hk. unfold SR, VIS in *.
    eapply (evt_sreach_lazy_k asegs (aL s) (aS s) (aZr s) P msF mo Q Hok Hevt).
    intros msF' mo' Hok' Hsame _ HP. apply Hk; [| apply MPRES_mat; exact Hsame | exact HP].
    split; [exact Hok' |]. cbn. eapply K_mat; [exact HK | exact Hsame].
  Qed.

  Corollary ASR_lift_at : forall (P : machine_state -> Prop) (Q : config -> Prop) s msF ms mo,
    AKREL s (mkCfg msF mo) ->
    VIS s msF = ms ->
    BExec.evt asegs P ms ->
    (forall msF' mo', AKREL s (mkCfg msF' mo') -> MPRES mo mo' -> P (VIS s msF') ->
                      SR Q (mkCfg msF' mo')) ->
    SR Q (mkCfg msF mo).
  Proof. intros P Q s msF ms mo HA <- He Hk. eapply ASR_lift; eassumption. Qed.

  Lemma AKREL_halted : forall s c, AKREL s c -> m_halted (cfg_model c) = None.
  Proof. intros s c [Hok _]. exact (lzok_halted Hok). Qed.

  Lemma VIS_MS : forall s R F pc fc rv m ro,
    exists m', VIS s (BMState.MS R F pc fc rv m ro) = BMState.MS R F pc fc rv m' ro.
  Proof. intros. exists (restrict_mem (aL s) (aS s) m). apply restrict_MS. Qed.

  Theorem ASR_SR_laws :
       (forall (Q : config -> Prop) c, Q c -> SR Q c)
    /\ (forall (Q Q' : config -> Prop) c, SR Q c -> (forall c', Q c' -> Q' c') -> SR Q' c)
    /\ (forall (Q1 Q2 : config -> Prop) c, SR Q1 c -> (forall c', Q1 c' -> SR Q2 c') -> SR Q2 c)
    /\ (forall (P : machine_state -> Prop) (Q : config -> Prop) s msF ms mo,
          AKREL s (mkCfg msF mo) -> VIS s msF = ms -> BExec.evt asegs P ms ->
          (forall msF' mo', AKREL s (mkCfg msF' mo') -> MPRES mo mo' -> P (VIS s msF') -> SR Q (mkCfg msF' mo')) ->
          SR Q (mkCfg msF mo)).
  Proof.
    split; [exact ASR_done|]. split; [exact ASR_mono|]. split; [exact ASR_seq|]. exact ASR_lift_at.
  Qed.

  Theorem ASR_AKREL_laws :
       (forall s c, AKREL s c -> m_halted (cfg_model c) = None)
    /\ (forall s R F pc fc rv m ro, exists m', VIS s (BMState.MS R F pc fc rv m ro) = BMState.MS R F pc fc rv m' ro).
  Proof. split; [exact AKREL_halted | exact VIS_MS]. Qed.

  Lemma ASR_realizes : forall (Q : config -> Prop) c T,
    SR Q c -> (forall c', Q c' -> BShapeAlg.realizes asegs c' T) -> BShapeAlg.realizes asegs c T.
  Proof. intros Q c T H Hk. eapply sreach_realizes; eassumption. Qed.
End Generic.
