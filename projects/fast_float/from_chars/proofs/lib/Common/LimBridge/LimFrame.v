(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimDefs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Frame.
Variable L : Z.

Definition lrel {A} (c c' : Sys A) : Prop :=
  forall i m o, c i m o -> c' i (m_relim L m) (o_relim L o).

Lemma lrel_pure {A} (x : A) : lrel (pure x) (pure x).
Proof. intros i m o ->. reflexivity. Qed.
Lemma lrel_unmodeled {A} : lrel (@unmodeled A) (@unmodeled A).
Proof. intros i m o ->. reflexivity. Qed.
Lemma lrel_choose {A} (P : A -> Prop) : lrel (choose P) (choose P).
Proof. intros i m o (x & HP & ->). exists x. split; [exact HP | reflexivity]. Qed.
Lemma lrel_choose_imp {A} (P P' : A -> Prop) : (forall x, P x -> P' x) -> lrel (choose P) (choose P').
Proof. intros HI i m o (x & HP & ->). exists x. split; [exact (HI x HP) | reflexivity]. Qed.
Lemma lrel_emit evs : lrel (emit evs) (emit evs).
Proof. intros i m o ->. reflexivity. Qed.
Lemma lrel_input : lrel input input.
Proof. intros i m o ->. reflexivity. Qed.
Lemma lrel_sysno : lrel sysno sysno.
Proof. intros i m o ->. reflexivity. Qed.
Lemma lrel_arg k : lrel (arg k) (arg k).
Proof. intros i m o ->. reflexivity. Qed.
Lemma lrel_get_fds : lrel get_fds get_fds.
Proof. intros i m o ->. reflexivity. Qed.
Lemma lrel_alt {A} (c1 c2 c1' c2' : Sys A) :
  lrel c1 c1' -> lrel c2 c2' -> lrel (alt c1 c2) (alt c1' c2').
Proof. intros H1 H2 i m o [H | H]; [left; exact (H1 _ _ _ H) | right; exact (H2 _ _ _ H)]. Qed.
Lemma lrel_bind {A B} (c c' : Sys A) (k k' : A -> Sys B) :
  lrel c c' -> (forall x, lrel (k x) (k' x)) -> lrel (bind c k) (bind c' k').
Proof.
  intros Hc Hk i m o H. unfold bind in *. destruct o as [y m2 evs |]; cbn [o_relim].
  - destruct H as (x & m1 & evs1 & evs2 & H1 & H2 & ->).
    exists x, (m_relim L m1), evs1, evs2. split; [exact (Hc _ _ _ H1) |].
    split; [exact (Hk x _ _ _ H2) | reflexivity].
  - destruct H as [H | (x & m1 & evs1 & H1 & H2)].
    + left. exact (Hc _ _ _ H).
    + right. exists x, (m_relim L m1), evs1. split; [exact (Hc _ _ _ H1) | exact (Hk x _ _ _ H2)].
Qed.
(* [comment removed for export] *)
Lemma lrel_bind_get_model {B} (k k' : Model -> Sys B) :
  (forall m, lrel (k m) (k' (m_relim L m))) -> lrel (bind get_model k) (bind get_model k').
Proof.
  intros Hk i m o H. unfold bind, get_model in *. destruct o as [y m2 evs |]; cbn [o_relim].
  - destruct H as (x & m1 & evs1 & evs2 & H1 & H2 & ->).
    injection H1 as -> -> ->.
    exists (m_relim L m), (m_relim L m), [], evs2. split; [reflexivity |].
    split; [exact (Hk _ _ _ _ H2) | reflexivity].
  - destruct H as [H | (x & m1 & evs1 & H1 & H2)]; [discriminate H |].
    injection H1 as -> -> ->.
    right. exists (m_relim L m), (m_relim L m), []. split; [reflexivity | exact (Hk _ _ _ _ H2)].
Qed.
Lemma lrel_bind_get_vmmaps {B} (k k' : VmMaps -> Sys B) :
  (forall h, lrel (k h) (k' (vm_relim L h))) -> lrel (bind get_vmmaps k) (bind get_vmmaps k').
Proof.
  intros Hk i m o H. unfold bind, get_vmmaps in *. destruct o as [y m2 evs |]; cbn [o_relim].
  - destruct H as (x & m1 & evs1 & evs2 & H1 & H2 & ->).
    injection H1 as -> -> ->.
    exists (vm_relim L (m_vmmaps m)), (m_relim L m), [], evs2. split; [reflexivity |].
    split; [exact (Hk _ _ _ _ H2) | reflexivity].
  - destruct H as [H | (x & m1 & evs1 & H1 & H2)]; [discriminate H |].
    injection H1 as -> -> ->.
    right. exists (vm_relim L (m_vmmaps m)), (m_relim L m), []. split; [reflexivity | exact (Hk _ _ _ _ H2)].
Qed.
Lemma lrel_modify (f f' : Model -> Model) :
  (forall m, f' (m_relim L m) = m_relim L (f m)) -> lrel (modify f) (modify f').
Proof. intros Hf i m o ->. unfold modify. cbn [o_relim]. rewrite Hf. reflexivity. Qed.
(* [comment removed for export] *)
Lemma lrel_raw_modify {A} (x : A) (f f' : Model -> Model) evs :
  (forall m, f' (m_relim L m) = m_relim L (f m)) ->
  lrel (fun _ m o => o = Ok x (f m) evs) (fun _ m o => o = Ok x (f' m) evs).
Proof. intros Hf i m o ->. cbn [o_relim]. rewrite Hf. reflexivity. Qed.

End Frame.

(* [comment removed for export] *)
Definition lpres {A} (c : Sys A) : Prop :=
  forall i m x m' evs, c i m (Ok x m' evs) -> m_limit m' = m_limit m.

Lemma lpres_pure {A} (x : A) : lpres (pure x).
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma lpres_unmodeled {A} : lpres (@unmodeled A).
Proof. intros i m y m' evs H. discriminate H. Qed.
Lemma lpres_choose {A} (P : A -> Prop) : lpres (choose P).
Proof. intros i m y m' evs (x & _ & H). injection H as _ -> _. reflexivity. Qed.
Lemma lpres_emit evs : lpres (emit evs).
Proof. intros i m y m' evs' H. injection H as _ -> _. reflexivity. Qed.
Lemma lpres_input : lpres input.
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma lpres_sysno : lpres sysno.
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma lpres_arg k : lpres (arg k).
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma lpres_get_model : lpres get_model.
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma lpres_get_fds : lpres get_fds.
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma lpres_get_vmmaps : lpres get_vmmaps.
Proof. intros i m y m' evs H. injection H as _ -> _. reflexivity. Qed.
Lemma lpres_alt {A} (c1 c2 : Sys A) : lpres c1 -> lpres c2 -> lpres (alt c1 c2).
Proof. intros H1 H2 i m y m' evs [H | H]; [exact (H1 _ _ _ _ _ H) | exact (H2 _ _ _ _ _ H)]. Qed.
Lemma lpres_bind {A B} (c : Sys A) (k : A -> Sys B) :
  lpres c -> (forall x, lpres (k x)) -> lpres (bind c k).
Proof.
  intros Hc Hk i m y m2 evs H. unfold bind in H.
  destruct H as (x & m1 & evs1 & evs2 & H1 & H2 & _).
  rewrite (Hk x _ _ _ _ _ H2). exact (Hc _ _ _ _ _ H1).
Qed.
Lemma lpres_modify (f : Model -> Model) :
  (forall m, m_limit (f m) = m_limit m) -> lpres (modify f).
Proof. intros Hf i m y m' evs H. injection H as _ -> _. apply Hf. Qed.
Lemma lpres_raw_modify {A} (x : A) (f : Model -> Model) evs0 :
  (forall m, m_limit (f m) = m_limit m) -> lpres (fun _ m o => o = Ok x (f m) evs0).
Proof. intros Hf i m y m' evs H. injection H as _ -> _. apply Hf. Qed.

(* [comment removed for export] *)
Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.

(* [comment removed for export] *)
Ltac inner_scrut s :=
  lazymatch s with
  | match ?s' with _ => _ end => inner_scrut s'
  | if ?s' then _ else _ => inner_scrut s'
  | _ => s
  end.
Ltac split_on s := let s' := inner_scrut s in destruct s' eqn:?; cbv beta iota.

Ltac lrel_red := autorewrite with relim.

(* [comment removed for export] *)
Ltac comm_fin :=
  cbv beta;
  repeat first
    [ reflexivity
    | progress autorewrite with relim
    | match goal with |- context[match ?s with _ => _ end] => let s' := inner_scrut s in destruct s' end
    | match goal with |- ?l = m_relim _ ?r => let h := head_of r in first [ is_const h | fail 1 ];
                                                lazymatch h with @m_relim => fail | _ => unfold h end end ].

Ltac lrel_step :=
  lazymatch goal with
  | |- lrel _ (pure _) (pure _) => apply lrel_pure
  | |- lrel _ unmodeled unmodeled => apply lrel_unmodeled
  | |- lrel _ (choose ?P) (choose ?P) => apply lrel_choose
  | |- lrel _ (choose _) (choose _) => apply lrel_choose_imp; intros ?x ?HP
  | |- lrel _ (emit _) (emit _) => apply lrel_emit
  | |- lrel _ input input => apply lrel_input
  | |- lrel _ sysno sysno => apply lrel_sysno
  | |- lrel _ (arg _) (arg _) => apply lrel_arg
  | |- lrel _ get_fds get_fds => apply lrel_get_fds
  | |- lrel _ (alt _ _) (alt _ _) => apply lrel_alt
  | |- lrel _ (bind get_model _) (bind get_model _) => apply lrel_bind_get_model; intros ?m
  | |- lrel _ (bind get_vmmaps _) (bind get_vmmaps _) => apply lrel_bind_get_vmmaps; intros ?h
  | |- lrel _ (bind _ _) (bind _ _) => apply lrel_bind; [| intros ?x]
  | |- lrel _ (modify _) (modify _) => apply lrel_modify; intros ?m; comm_fin
  | |- lrel ?L (fun _ m o => o = Ok ?x (@?f m) ?e) (fun _ m' o' => o' = Ok ?x (@?f' m') ?e) => apply (lrel_raw_modify L x f f' e); intros ?m; comm_fin
  | |- lrel _ (match ?s with _ => _ end) (match ?s with _ => _ end) => split_on s
  | |- lrel _ (if ?s then _ else _) (if ?s then _ else _) => split_on s
  | |- lrel _ (let _ := _ in _) _ => cbv zeta
  end.

Ltac lrel_unfold :=
  lazymatch goal with
  | |- lrel _ ?c ?c' =>
      let h := head_of c in
      let h' := head_of c' in
      first [ is_const h | fail 1 "head is not a constant" ];
      constr_eq h h';
      lazymatch h with
      | @bind => fail | @choose => fail | @alt => fail | @modify => fail | @pure => fail | @unmodeled => fail
      | @emit => fail | @get_model => fail | @get_vmmaps => fail | @get_fds => fail
      | _ => unfold h
      end
  end.

(* [comment removed for export] *)
Ltac lrel_open :=
  match goal with
  | |- lrel _ _ ?c' =>
      match c' with
      | context[?g (m_relim ?L ?m)] =>
          let h := head_of g in
          first [ is_const h | fail 1 ];
          lazymatch h with
          | @lrel => fail
          | @m_relim => fail
          | _ => unfold h
          end
      | context[?g (vm_relim ?L ?m)] =>
          let h := head_of g in
          first [ is_const h | fail 1 ];
          lazymatch h with
          | @lrel => fail
          | @vm_relim => fail
          | @with_vmmaps => fail
          | _ => unfold h
          end
      end
  end.
Ltac lrel_go := repeat first [ lrel_step | progress lrel_red | lrel_unfold | lrel_open ].

Ltac lpres_step :=
  lazymatch goal with
  | |- lpres (pure _) => apply lpres_pure
  | |- lpres unmodeled => apply lpres_unmodeled
  | |- lpres (choose _) => apply lpres_choose
  | |- lpres (emit _) => apply lpres_emit
  | |- lpres input => apply lpres_input
  | |- lpres sysno => apply lpres_sysno
  | |- lpres (arg _) => apply lpres_arg
  | |- lpres get_model => apply lpres_get_model
  | |- lpres get_fds => apply lpres_get_fds
  | |- lpres get_vmmaps => apply lpres_get_vmmaps
  | |- lpres (alt _ _) => apply lpres_alt
  | |- lpres (bind _ _) => apply lpres_bind; [| intros ?x]
  | |- lpres (modify _) => apply lpres_modify; intros ?m; reflexivity
  | |- lpres (fun _ m o => o = Ok _ _ _) => apply lpres_raw_modify; intros ?m; reflexivity
  | |- lpres (match ?s with _ => _ end) => split_on s
  | |- lpres (if ?s then _ else _) => split_on s
  | |- lpres (let _ := _ in _) => cbv zeta
  end.
Ltac lpres_unfold :=
  lazymatch goal with
  | |- lpres ?c =>
      let h := head_of c in
      first [ is_const h | fail 1 "head is not a constant" ];
      unfold h
  end.
Ltac lpres_go := repeat first [ lpres_step | lpres_unfold ].

(* [comment removed for export] *)
Lemma bind_ok_inv {A B} : forall (c : Sys A) (k : A -> Sys B) i m y m2 evs,
  bind c k i m (Ok y m2 evs) ->
  exists x m1 evs1 evs2, c i m (Ok x m1 evs1) /\ k x i m1 (Ok y m2 evs2) /\ evs = evs1 ++ evs2.
Proof. intros c k i m y m2 evs H. exact H. Qed.
Lemma alt_inv {A} : forall (c1 c2 : Sys A) i m o, alt c1 c2 i m o -> c1 i m o \/ c2 i m o.
Proof. intros c1 c2 i m o H. exact H. Qed.
Lemma choose_ok_inv {A} : forall (P : A -> Prop) i m y m2 evs,
  choose P i m (Ok y m2 evs) -> P y /\ m2 = m /\ evs = [].
Proof. intros P i m y m2 evs (x & HP & H). injection H as -> -> ->. auto. Qed.

Ltac ok_inj H := first [ discriminate H | injection H as -> -> -> | (injection H; intros; subst) ].
Ltac sys_inv_hyp H :=
  let c := lazymatch type of H with ?c _ _ _ => c | ?T => fail 1 "sys_inv: not an outcome hypothesis" T end in
  lazymatch c with
  | bind _ _ =>
      let x := fresh "x" in let m1 := fresh "m1" in let e1 := fresh "evs" in let e2 := fresh "evs" in
      let H1 := fresh "H" in let H2 := fresh "H" in let He := fresh "He" in
      apply bind_ok_inv in H; destruct H as (x & m1 & e1 & e2 & H1 & H2 & He);
      sys_inv_hyp H1; sys_inv_hyp H2
  | alt _ _ => let H1 := fresh "H" in apply alt_inv in H; destruct H as [H1 | H1]; sys_inv_hyp H1
  | choose _ => let HP := fresh "HP" in let Hm := fresh "Hm" in let Hx := fresh "Hx" in
                apply choose_ok_inv in H; destruct H as (HP & Hm & Hx); subst
  | unmodeled => discriminate H
  | pure _ => ok_inj H
  | emit _ => ok_inj H
  | input => ok_inj H
  | sysno => ok_inj H
  | arg _ => ok_inj H
  | get_model => ok_inj H
  | get_fds => ok_inj H
  | get_vmmaps => ok_inj H
  | modify _ => ok_inj H
  | (fun _ _ _ => _ = _) => cbv beta in H; ok_inj H
  | (match ?s with _ => _ end) => revert H; split_on s; intros H; sys_inv_hyp H
  | (if ?s then _ else _) => revert H; split_on s; intros H; sys_inv_hyp H
  | (let _ := _ in _) => cbv zeta in H; sys_inv_hyp H
  | (fun _ => _) _ => cbv beta in H; sys_inv_hyp H
  | _ => let h := head_of c in
         first [ is_const h | fail 1 "sys_inv: stuck at" c ];
         unfold h in H; sys_inv_hyp H
  end.
(* [comment removed for export] *)
Ltac lim_fin :=
  repeat first
    [ reflexivity
    | match goal with |- context[match ?s with _ => _ end] => let s' := inner_scrut s in destruct s' end
    | match goal with |- m_limit ?t = _ => let h := head_of t in first [ is_const h | fail 1 ]; unfold h end ].
Ltac lpres_brute :=
  let H := fresh "H" in
  intros ?i ?m ?x ?m' ?evs H; sys_inv_hyp H; lim_fin.
