(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimDefs LimFrame LimInv.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition vpres {A} (c : Sys A) : Prop :=
  forall i m x m' evs, c i m (Ok x m' evs) -> m_vmmaps m' = m_vmmaps m.

Lemma vpres_inv {A} (c : Sys A) : vpres c -> forall i m x m' evs, c i m (Ok x m' evs) -> Inv m -> Inv m'.
Proof. intros Hc i m x m' evs H HI. unfold Inv in *. rewrite (Hc i m x m' evs H). exact HI. Qed.

(* [comment removed for export] *)

Lemma vpres_pure {A} (x : A) : vpres (pure x).
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma vpres_unmodeled {A} : vpres (@unmodeled A).
Proof. intros i m y m' evs H. discriminate H. Qed.
Lemma vpres_choose {A} (P : A -> Prop) : vpres (choose P).
Proof. intros i m y m' evs (x & _ & H). injection H as _ -> _. reflexivity. Qed.
Lemma vpres_emit evs : vpres (emit evs).
Proof. intros i m y m' evs' H. injection H as _ -> _. reflexivity. Qed.
Lemma vpres_input : vpres input.
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma vpres_sysno : vpres sysno.
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma vpres_arg k : vpres (arg k).
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma vpres_get_model : vpres get_model.
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma vpres_get_fds : vpres get_fds.
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma vpres_get_vmmaps : vpres get_vmmaps.
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma vpres_alt {A} (c1 c2 : Sys A) : vpres c1 -> vpres c2 -> vpres (alt c1 c2).
Proof. intros H1 H2 i m y m' evs [H | H]; [exact (H1 _ _ _ _ _ H) | exact (H2 _ _ _ _ _ H)]. Qed.
Lemma vpres_bind {A B} (c : Sys A) (k : A -> Sys B) :
  vpres c -> (forall x, vpres (k x)) -> vpres (bind c k).
Proof.
  intros Hc Hk i m y m2 evs H. unfold bind in H.
  destruct H as (x & m1 & evs1 & evs2 & H1 & H2 & _).
  rewrite (Hk x _ _ _ _ _ H2). exact (Hc _ _ _ _ _ H1).
Qed.
Lemma vpres_modify (f : Model -> Model) :
  (forall m, m_vmmaps (f m) = m_vmmaps m) -> vpres (modify f).
Proof. intros Hf i m y m' evs H. injection H as _ -> _. apply Hf. Qed.
Lemma vpres_raw_modify {A} (x : A) (f : Model -> Model) evs0 :
  (forall m, m_vmmaps (f m) = m_vmmaps m) -> vpres (fun _ m o => o = Ok x (f m) evs0).
Proof. intros Hf i m y m' evs H. injection H as _ -> _. apply Hf. Qed.


Ltac vpres_step :=
  lazymatch goal with
  | |- vpres (pure _) => apply vpres_pure
  | |- vpres unmodeled => apply vpres_unmodeled
  | |- vpres (choose _) => apply vpres_choose
  | |- vpres (emit _) => apply vpres_emit
  | |- vpres input => apply vpres_input
  | |- vpres sysno => apply vpres_sysno
  | |- vpres (arg _) => apply vpres_arg
  | |- vpres get_model => apply vpres_get_model
  | |- vpres get_fds => apply vpres_get_fds
  | |- vpres get_vmmaps => apply vpres_get_vmmaps
  | |- vpres (alt _ _) => apply vpres_alt
  | |- vpres (bind _ _) => apply vpres_bind; [| intros ?x]
  | |- vpres (modify _) => apply vpres_modify; intros ?m; reflexivity
  | |- vpres (fun _ m o => o = Ok _ _ _) => apply vpres_raw_modify; intros ?m; reflexivity
  | |- vpres (match ?s with _ => _ end) => split_on s
  | |- vpres (if ?s then _ else _) => split_on s
  | |- vpres (let _ := _ in _) => cbv zeta
  end.
Ltac vpres_unfold :=
  lazymatch goal with
  | |- vpres ?c =>
      let h := head_of c in
      first [ is_const h | fail 1 "head is not a constant" ];
      unfold h
  end.
Ltac vpres_go := repeat first [ vpres_step | vpres_unfold ].


(* [comment removed for export] *)
Ltac vm_fin :=
  repeat first
    [ reflexivity
    | match goal with |- context[match ?s with _ => _ end] => let s' := inner_scrut s in destruct s' end
    | match goal with |- m_vmmaps ?t = _ => let h := head_of t in first [ is_const h | fail 1 ]; unfold h end ].
Ltac vpres_brute :=
  let H := fresh "H" in
  intros ?i ?m ?x ?m' ?evs H; sys_inv_hyp H; vm_fin.
