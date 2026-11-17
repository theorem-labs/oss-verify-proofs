(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

Definition setvl (L : Z) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) L (vm_mmap_base h) (vm_init_sp h).
Definition setL (L : Z) (m : Model) : Model := with_vmmaps (setvl L (m_vmmaps m)) m.
Definition omap {A} (L : Z) (o : outcome A) : outcome A :=
  match o with Ok x m evs => Ok x (setL L m) evs | Unmodeled => Unmodeled end.
Definition mlim (m : Model) : Z := vm_limit (m_vmmaps m).
Definition opres {A} (m : Model) (o : outcome A) : Prop :=
  match o with Ok _ m' _ => mlim m' = mlim m | Unmodeled => True end.

Lemma setL_setL : forall L1 L2 m, setL L2 (setL L1 m) = setL L2 m.
Proof. intros. reflexivity. Qed.
Lemma setL_id : forall m, setL (mlim m) m = m.
Proof. intros [fd [[r mp na sb b l mb sp] lz mt] io fs pr lm tm]. reflexivity. Qed.
Lemma mlim_setL : forall L m, mlim (setL L m) = L.
Proof. intros. reflexivity. Qed.
Lemma setL_eq_of_mlim : forall L m, mlim m = L -> setL L m = m.
Proof. intros L m <-. apply setL_id. Qed.
Lemma omap_omap {A} : forall L1 L2 (o : outcome A), omap L2 (omap L1 o) = omap L2 o.
Proof. intros L1 L2 [x m evs|]; reflexivity. Qed.
Lemma m_halted_setL : forall L m, m_halted (setL L m) = m_halted m.
Proof. reflexivity. Qed.
Lemma m_killed_setL : forall L m, m_killed (setL L m) = m_killed m.
Proof. reflexivity. Qed.
Lemma m_fs_setL : forall L m, m_fs (setL L m) = m_fs m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lim_blind {A} (c : Sys A) : Prop :=
  forall i m o, c i m o -> (forall L, c i (setL L m) (omap L o)) /\ opres m o.

Ltac blind_base := let H := fresh in intros ? ? ? H; hnf in H; subst; split; [intros ?; reflexivity | first [reflexivity | exact I]].
Lemma lim_blind_pure {A} (x : A) : lim_blind (pure x).
Proof. blind_base. Qed.
Lemma lim_blind_unmodeled {A} : lim_blind (@unmodeled A).
Proof. blind_base. Qed.
Lemma lim_blind_choose {A} (P : A -> Prop) : lim_blind (choose P).
Proof. intros i m o (x & Hx & ->). split; [intros L; exists x; split; [exact Hx | reflexivity] | reflexivity]. Qed.
Lemma lim_blind_emit evs : lim_blind (emit evs).
Proof. blind_base. Qed.
Lemma lim_blind_input : lim_blind input.
Proof. blind_base. Qed.
Lemma lim_blind_sysno : lim_blind sysno.
Proof. blind_base. Qed.
Lemma lim_blind_arg k : lim_blind (arg k).
Proof. blind_base. Qed.
Lemma lim_blind_get_fds : lim_blind get_fds.
Proof. blind_base. Qed.
Lemma lim_blind_alt {A} (c1 c2 : Sys A) : lim_blind c1 -> lim_blind c2 -> lim_blind (alt c1 c2).
Proof.
  intros H1 H2 i m o [H|H].
  - destruct (H1 i m o H) as [Ha Hb]. split; [intros L; left; apply Ha | exact Hb].
  - destruct (H2 i m o H) as [Ha Hb]. split; [intros L; right; apply Ha | exact Hb].
Qed.
Lemma lim_blind_bind {A B} (c : Sys A) (k : A -> Sys B) : lim_blind c -> (forall x, lim_blind (k x)) -> lim_blind (bind c k).
Proof.
  intros Hc Hk i m [y m2 evs|].
  - intros (x & m1 & evs1 & evs2 & H1 & H2 & ->).
    destruct (Hc i m _ H1) as [Ha Hb]. destruct (Hk x i m1 _ H2) as [Hc' Hd]. cbn [opres] in *.
    split; [| congruence]. intros L. cbn [omap].
    exists x, (setL L m1), evs1, evs2. split; [exact (Ha L)|]. split; [exact (Hc' L) | reflexivity].
  - intros [H | (x & m1 & evs1 & H1 & H2)]; (split; [| exact I]); intros L; cbn [omap].
    + left. exact (proj1 (Hc i m _ H) L).
    + right. exists x, (setL L m1), evs1. split; [exact (proj1 (Hc i m _ H1) L) | exact (proj1 (Hk x i m1 _ H2) L)].
Qed.
(* [comment removed for export] *)
Lemma lim_blind_get_model {A} (k : Model -> Sys A) :
  (forall L m, k (setL L m) = k m) -> (forall m, lim_blind (k m)) -> lim_blind (bind get_model k).
Proof.
  intros Hinv Hk i m o H. apply bind_get_model in H. destruct (Hk m i m o H) as [Ha Hb].
  split; [| exact Hb]. intros L. apply bind_get_model. rewrite Hinv. exact (Ha L).
Qed.
Lemma lim_blind_modify (f : Model -> Model) :
  (forall L m, f (setL L m) = setL L (f m)) -> (forall m, mlim (f m) = mlim m) -> lim_blind (modify f).
Proof. intros Hf Hp i m o H. hnf in H. subst o. split; [intros L; unfold modify; cbn [omap]; rewrite Hf; reflexivity | apply Hp]. Qed.
Lemma lim_blind_arm {A} (F : SyscallInput -> Sys A) : (forall j, lim_blind (F j)) -> lim_blind (fun i => F i i).
Proof. intros H i m o Ho. exact (H i i m o Ho). Qed.

(* [comment removed for export] *)
Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.
(* [comment removed for export] *)
Ltac lim_unsetL :=
  repeat match goal with |- context [?p (setL ?L ?m)] => progress change (p (setL L m)) with (p m) end.
Ltac lim_fun_side_with h :=
  intros;
  first [ reflexivity
        | unfold h; cbv beta iota zeta; lim_unsetL;
          repeat (match goal with
                  | |- context [if ?b then _ else _] => destruct b
                  | |- context [match ?s with _ => _ end] => destruct s
                  end; cbv beta iota zeta);
          reflexivity ].
Ltac lim_modify :=
  lazymatch goal with |- lim_blind (modify ?f) =>
    let h := head_of f in
    apply lim_blind_modify; [lim_fun_side_with h | lim_fun_side_with h] end.
Ltac deep_destruct s :=
  lazymatch s with
  | match ?s' with _ => _ end => deep_destruct s'
  | if ?s' then _ else _ => deep_destruct s'
  | _ => destruct s
  end.
Ltac lim_head c :=
  lazymatch c with
  | ?f _ _ _ _ _ _ _ _ _ _ => unfold f
  | ?f _ _ _ _ _ _ _ _ _ => unfold f
  | ?f _ _ _ _ _ _ _ _ => unfold f
  | ?f _ _ _ _ _ _ _ => unfold f
  | ?f _ _ _ _ _ _ => unfold f
  | ?f _ _ _ _ _ => unfold f
  | ?f _ _ _ _ => unfold f
  | ?f _ _ _ => unfold f
  | ?f _ _ => unfold f
  | ?f _ => unfold f
  | ?f => unfold f
  end.
Ltac lim_step :=
  cbv beta zeta iota;
  lazymatch goal with
  | |- lim_blind (bind get_model ?k) => apply lim_blind_get_model; [intros; reflexivity | intros ?m]
  | |- lim_blind (bind _ _) => apply lim_blind_bind; [| intros ?x]
  | |- lim_blind (pure _) => apply lim_blind_pure
  | |- lim_blind unmodeled => apply lim_blind_unmodeled
  | |- lim_blind (choose _) => apply lim_blind_choose
  | |- lim_blind (emit _) => apply lim_blind_emit
  | |- lim_blind input => apply lim_blind_input
  | |- lim_blind sysno => apply lim_blind_sysno
  | |- lim_blind (arg _) => apply lim_blind_arg
  | |- lim_blind (alt _ _) => apply lim_blind_alt
  | |- lim_blind get_fds => apply lim_blind_get_fds
  | |- lim_blind (modify _) => lim_modify
  | |- lim_blind (match ?s with _ => _ end) => deep_destruct s
  | |- lim_blind (if ?s then _ else _) => deep_destruct s
  | |- lim_blind (fun i => ?c) => idtac
  | |- lim_blind ?c => lim_head c
  end.
Ltac lim_auto := repeat lim_step.
