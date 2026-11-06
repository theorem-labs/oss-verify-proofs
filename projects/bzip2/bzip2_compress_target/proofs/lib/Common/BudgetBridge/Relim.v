(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* [comment removed for export] *)
Definition relim_maps (l : Z) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) l
               (vm_mmap_base h) (vm_init_sp h).

Definition relim (l : Z) (m : Model) : Model :=
  mkModelOf (m_fd m)
    (mkVmState (relim_maps l (vmst_maps (m_vm m))) (vmst_lazy (m_vm m)) (vmst_materialized (m_vm m)))
    (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).

Definition relimo {A} (l : Z) (o : outcome A) : outcome A :=
  match o with
  | Ok x m evs => Ok x (relim l m) evs
  | Unmodeled => Unmodeled
  end.

Definition mlim (m : Model) : Z := vm_limit (m_vmmaps m).

Lemma relim_relim : forall l l' m, relim l (relim l' m) = relim l m.
Proof. reflexivity. Qed.

Lemma relim_id : forall m, relim (mlim m) m = m.
Proof. intros [fd [[a b c d e f g h] lz mt] io fs pr li ti]. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma m_vmmaps_relim : forall l m, m_vmmaps (relim l m) = relim_maps l (m_vmmaps m).
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_backing_used_relim : forall l m, vm_backing_used (relim l m) = vm_backing_used m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition ofr (m : Model) {A} (o : outcome A) : Prop :=
  match o with Ok _ m' _ => m_vmmaps m' = m_vmmaps m | Unmodeled => True end.

Definition LI {A} (c : Sys A) : Prop :=
  forall i m o, c i m o -> ofr m o /\ forall l, c i (relim l m) (relimo l o).

(* [comment removed for export] *)
Definition LIk {A} (k : Model -> Sys A) : Prop :=
  forall i m o, k m i m o -> ofr m o /\ forall l, k (relim l m) i (relim l m) (relimo l o).

Lemma LI_ret {A} (c : Sys A) (r : SyscallInput -> Model -> A) :
  (forall l i m, r i (relim l m) = r i m) ->
  (forall i m o, c i m o <-> o = Ok (r i m) m []) -> LI c.
Proof.
  intros R E i m o H. apply E in H as ->. split; [reflexivity|]. intros l. apply E. cbn. rewrite R. reflexivity.
Qed.

Lemma LI_pure {A} (x : A) : LI (pure x).
Proof. apply (LI_ret _ (fun _ _ => x)); [reflexivity|]. intros i m o. reflexivity. Qed.

Lemma LI_unmodeled {A} : LI (@unmodeled A).
Proof. intros i m o H. unfold unmodeled in *. subst o. split; [exact I| reflexivity]. Qed.

Lemma LI_choose {A} (P : A -> Prop) : LI (choose P).
Proof. intros i m o (x & HP & ->). split; [reflexivity|]. intros l. exists x. split; [exact HP| reflexivity]. Qed.

Lemma LI_alt {A} (c1 c2 : Sys A) : LI c1 -> LI c2 -> LI (alt c1 c2).
Proof.
  intros H1 H2 i m o [H|H]; [destruct (H1 _ _ _ H) as [F S]| destruct (H2 _ _ _ H) as [F S]];
    split; try exact F; intros l; [left| right]; apply S.
Qed.

Lemma LI_emit evs : LI (emit evs).
Proof. intros i m o H. unfold emit in *. subst o. split; reflexivity. Qed.

Lemma LI_input : LI input.
Proof. apply (LI_ret _ (fun i _ => i)); [reflexivity|]. intros i m o. reflexivity. Qed.

Lemma LI_sysno : LI sysno.
Proof. apply (LI_ret _ (fun i _ => in_sysno i)); [reflexivity|]. intros i m o. reflexivity. Qed.

Lemma LI_arg k : LI (arg k).
Proof. apply (LI_ret _ (fun i _ => in_arg i k)); [reflexivity|]. intros i m o. reflexivity. Qed.

Lemma LI_get_fds : LI get_fds.
Proof. apply (LI_ret _ (fun _ m => m_fds m)); [reflexivity|]. intros i m o. reflexivity. Qed.

Lemma LI_get_vmmaps_k {A} (k : VmMaps -> Sys A) :
  (forall l h, k (relim_maps l h) = k h) -> (forall h, LI (k h)) -> LI (bind get_vmmaps k).
Proof.
  intros E H i m o H1.
  assert (B : forall m' o', bind get_vmmaps k i m' o' <-> k (m_vmmaps m') i m' o').
  { intros m' o'. unfold bind, get_vmmaps. destruct o' as [y m2 evs|]; split.
    - intros (x & m1 & e1 & e2 & H0 & H2 & ->). injection H0 as -> -> ->. exact H2.
    - intros H2. exists (m_vmmaps m'), m', [], evs. repeat split; auto.
    - intros [H0|(x & m1 & e1 & H0 & H2)]; [discriminate H0|]. injection H0 as -> -> ->. exact H2.
    - intros H2. right. exists (m_vmmaps m'), m', []. split; [reflexivity| exact H2]. }
  apply B in H1. destruct (H _ _ _ _ H1) as [F S]. split; [exact F|].
  intros l. apply B. rewrite m_vmmaps_relim, E. apply S.
Qed.

Lemma LI_bind {A B} (c : Sys A) (k : A -> Sys B) : LI c -> (forall x, LI (k x)) -> LI (bind c k).
Proof.
  intros Hc Hk i m o H. destruct o as [y m2 evs|]; cbn in *.
  - destruct H as (x & m1 & e1 & e2 & H1 & H2 & ->).
    destruct (Hc _ _ _ H1) as [F1 S1]. destruct (Hk x _ _ _ H2) as [F2 S2]. cbn in F1, F2.
    split; [congruence|]. intros l.
    exists x, (relim l m1), e1, e2. split; [exact (S1 l)|]. split; [exact (S2 l)| reflexivity].
  - split; [exact I|]. intros l. destruct H as [H|(x & m1 & e1 & H1 & H2)].
    + left. exact (proj2 (Hc _ _ _ H) l).
    + right. exists x, (relim l m1), e1. split; [exact (proj2 (Hc _ _ _ H1) l)| exact (proj2 (Hk x _ _ _ H2) l)].
Qed.

Lemma LI_bind_get_model {A} (k : Model -> Sys A) : LIk k -> LI (bind get_model k).
Proof.
  intros Hk i m o H. apply bind_get_model in H. destruct (Hk _ _ _ H) as [F S].
  split; [exact F|]. intros l. apply bind_get_model. exact (S l).
Qed.

(* [comment removed for export] *)
Lemma LIk_of {A} (k : Model -> Sys A) :
  (forall l m, k (relim l m) = k m) -> (forall m, LI (k m)) -> LIk k.
Proof. intros E H i m o H1. destruct (H m _ _ _ H1) as [F S]. split; [exact F|]. intros l. rewrite E. apply S. Qed.

Lemma LI_modify (f : Model -> Model) :
  (forall m, m_vmmaps (f m) = m_vmmaps m) ->
  (forall l m, f (relim l m) = relim l (f m)) -> LI (modify f).
Proof. intros F E i m o H. unfold modify in *. subst o. split; [apply F|]. intros l. cbn [relimo]. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)

Lemma LI_if {A} (b : bool) (c1 c2 : Sys A) : LI c1 -> LI c2 -> LI (if b then c1 else c2).
Proof. intros; destruct b; assumption. Qed.

(* [comment removed for export] *)
Ltac li_head c :=
  lazymatch c with
  | ?f _ _ _ _ _ _ _ _ _ _ _ _ => li_head f
  | ?f _ _ _ _ _ _ _ _ _ _ _ => li_head f
  | ?f _ _ _ _ _ _ _ _ _ _ => li_head f
  | ?f _ _ _ _ _ _ _ _ _ => li_head f
  | ?f _ _ _ _ _ _ _ _ => li_head f
  | ?f _ _ _ _ _ _ _ => li_head f
  | ?f _ _ _ _ _ _ => li_head f
  | ?f _ _ _ _ _ => li_head f
  | ?f _ _ _ _ => li_head f
  | ?f _ _ _ => li_head f
  | ?f _ _ => li_head f
  | ?f _ => li_head f
  | _ => c
  end.

Ltac li_destruct x :=
  lazymatch x with
  | match ?y with _ => _ end => li_destruct y
  | _ => destruct x; cbv beta iota
  end.

(* [comment removed for export] *)
Ltac li_modify :=
  apply LI_modify; intros;
  [ reflexivity || (progress repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity)
  | reflexivity || (progress repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity) ].

Ltac li_step :=
  lazymatch goal with
  | |- LI (pure _) => apply LI_pure
  | |- LI unmodeled => apply LI_unmodeled
  | |- LI (choose _) => apply LI_choose
  | |- LI (emit _) => apply LI_emit
  | |- LI input => apply LI_input
  | |- LI sysno => apply LI_sysno
  | |- LI (arg _) => apply LI_arg
  | |- LI get_fds => apply LI_get_fds
  | |- LI (alt _ _) => apply LI_alt
  | |- LI (bind get_model _) => apply LI_bind_get_model; apply LIk_of; [intros; reflexivity | intro]
  | |- LI (bind get_vmmaps _) => apply LI_get_vmmaps_k; [intros; reflexivity | intro]
  | |- LI (bind _ _) => apply LI_bind; [| intro]
  | |- LI (modify _) => li_modify
  | |- LI (match ?x with _ => _ end) => li_destruct x
  | |- LI (let _ := _ in _) => cbv zeta
  | |- LI ((fun _ => _) _) => cbv beta
  | |- LI (fun _ => _) => fail "lambda"
  | |- LI ?c => let h := li_head c in unfold h
  end.

Ltac li := repeat li_step.
