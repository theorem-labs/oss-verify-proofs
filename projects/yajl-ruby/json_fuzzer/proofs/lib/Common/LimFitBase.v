(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase LimMonad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition PR {A : Type} (i : SyscallInput) (m : Model) (c : Sys A) : Prop :=
  forall x m' evs, c i m (Ok x m' evs) -> fits m -> fits m'.

Lemma PR_iff {A} : forall i m (c c' : Sys A),
  (forall o, c i m o <-> c' i m o) -> PR i m c' -> PR i m c.
Proof. intros i m c c' E H x m' evs Hc. apply (H x m' evs). apply E. exact Hc. Qed.

Lemma PR_pure {A} : forall i m (x : A), PR i m (pure x).
Proof. intros i m x y m' evs H. unfold pure in H. injection H as -> -> ->. exact (fun F => F). Qed.

Lemma PR_unmodeled {A} : forall i m, PR i m (@unmodeled A).
Proof. intros i m y m' evs H. discriminate H. Qed.

Lemma PR_choose {A} : forall i m (P : A -> Prop), PR i m (choose P).
Proof. intros i m P y m' evs (x & _ & H). injection H as -> -> ->. exact (fun F => F). Qed.

Lemma PR_emit : forall i m evs, PR i m (emit evs).
Proof. intros i m evs y m' e H. unfold emit in H. injection H as -> -> ->. exact (fun F => F). Qed.

Lemma PR_input : forall i m, PR i m input.
Proof. intros i m y m' e H. unfold input in H. injection H as -> -> ->. exact (fun F => F). Qed.

Lemma PR_sysno : forall i m, PR i m sysno.
Proof. intros i m y m' e H. unfold sysno in H. injection H as -> -> ->. exact (fun F => F). Qed.

Lemma PR_arg : forall i m k, PR i m (arg k).
Proof. intros i m k y m' e H. unfold arg in H. injection H as -> -> ->. exact (fun F => F). Qed.

Lemma PR_get_fds : forall i m, PR i m get_fds.
Proof. intros i m y m' e H. unfold get_fds in H. injection H as -> -> ->. exact (fun F => F). Qed.

Lemma PR_get_vmmaps : forall i m, PR i m get_vmmaps.
Proof. intros i m y m' e H. unfold get_vmmaps in H. injection H as -> -> ->. exact (fun F => F). Qed.

Lemma PR_get_model0 : forall i m, PR i m get_model.
Proof. intros i m y m' e H. unfold get_model in H. injection H as -> -> ->. exact (fun F => F). Qed.

Lemma PR_modify : forall i m (f : Model -> Model),
  (fits m -> fits (f m)) -> PR i m (modify f).
Proof. intros i m f Hf y m' e H. unfold modify in H. injection H as -> -> ->. exact Hf. Qed.

Lemma PR_alt {A} : forall i m (c1 c2 : Sys A), PR i m c1 -> PR i m c2 -> PR i m (alt c1 c2).
Proof. intros i m c1 c2 H1 H2 x m' evs [H | H]; [exact (H1 _ _ _ H) | exact (H2 _ _ _ H)]. Qed.

Lemma PR_bind {A B} : forall i m (c : Sys A) (k : A -> Sys B),
  PR i m c ->
  (forall x m1 evs1, c i m (Ok x m1 evs1) -> PR i m1 (k x)) ->
  PR i m (bind c k).
Proof.
  intros i m c k Hc Hk y m2 evs H HF. cbn [bind] in H.
  destruct H as (x & m1 & evs1 & evs2 & H1 & H2 & _).
  exact (Hk x m1 evs1 H1 y m2 evs2 H2 (Hc x m1 evs1 H1 HF)).
Qed.

Lemma PR_get_model {A} : forall i m (k : Model -> Sys A),
  PR i m (k m) -> PR i m (bind get_model k).
Proof. intros i m k H. apply (PR_iff i m _ (k m)); [intros o; apply bind_get_model | exact H]. Qed.

Lemma PR_get_vmmaps_k {A} : forall i m (k : VmMaps -> Sys A),
  PR i m (k (m_vmmaps m)) -> PR i m (bind get_vmmaps k).
Proof.
  intros i m k H x m' evs Hb. cbn [bind] in Hb.
  destruct Hb as (h & m1 & evs1 & evs2 & H1 & H2 & _).
  unfold get_vmmaps in H1. injection H1 as -> -> ->. exact (H x m' evs2 H2).
Qed.

Ltac pr_step :=
  lazymatch goal with
  | |- PR _ _ (pure _) => apply PR_pure
  | |- PR _ _ unmodeled => apply PR_unmodeled
  | |- PR _ _ (emit _) => apply PR_emit
  | |- PR _ _ input => apply PR_input
  | |- PR _ _ sysno => apply PR_sysno
  | |- PR _ _ (arg _) => apply PR_arg
  | |- PR _ _ get_fds => apply PR_get_fds
  | |- PR _ _ get_vmmaps => apply PR_get_vmmaps
  | |- PR _ _ get_model => apply PR_get_model0
  | |- PR _ _ (choose _) => apply PR_choose
  | |- PR _ _ (bind get_model _) => apply PR_get_model; cbv beta
  | |- PR _ _ (bind get_vmmaps _) => apply PR_get_vmmaps_k; cbv beta
  | |- PR _ _ (bind _ _) => apply PR_bind; [| intros ? ? ? ?]
  | |- PR _ _ (alt _ _) => apply PR_alt
  | |- PR _ _ (modify _) => apply PR_modify; try exact (fun F => F)
  | |- PR _ _ (let _ := _ in _) => cbv zeta
  | |- PR _ _ ((fun _ => _) _) => cbv beta
  | |- PR _ _ (match ?x with _ => _ end) =>
      first [ progress cbv beta zeta | destruct_inner_eq x; cbv beta iota ]
  | |- PR _ _ (if ?b then _ else _) =>
      first [ progress cbv beta zeta | destruct_inner_eq b; cbv beta iota ]
  | |- PR _ _ ?c => let h := head_of c in progress (unfold h)
  end.

Ltac pr := repeat pr_step.
