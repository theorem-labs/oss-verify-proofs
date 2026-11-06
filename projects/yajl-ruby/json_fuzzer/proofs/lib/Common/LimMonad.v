(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section FR.
Variable L : Z.

Definition FR {A : Type} (i : SyscallInput) (m : Model) (cb cs : Sys A) : Prop :=
  (forall x mL' evs, cs i (sl L m) (Ok x mL' evs) ->
     exists m', cb i m (Ok x m' evs) /\ mL' = sl L m' /\ mlim m' = mlim m)
  /\ (forall x m' evs, cb i m (Ok x m' evs) ->
        cs i (sl L m) (Ok x (sl L m') evs) /\ mlim m' = mlim m)
  /\ (cs i (sl L m) Unmodeled <-> cb i m Unmodeled).

(* [comment removed for export] *)
Definition FRU {A : Type} (c : Sys A) : Prop := forall i m, FR i m c c.

Lemma FR_iff {A} : forall i m (cb cb' cs cs' : Sys A),
  (forall o, cb i m o <-> cb' i m o) ->
  (forall o, cs i (sl L m) o <-> cs' i (sl L m) o) ->
  FR i m cb' cs' -> FR i m cb cs.
Proof.
  intros i m cb cb' cs cs' Hb Hs (F1 & F2 & F3). split; [| split].
  - intros x mL' evs H. pose proof (proj1 (Hs _) H) as H1.
    destruct (F1 _ _ _ H1) as (m' & H' & E & El).
    exists m'. split; [exact (proj2 (Hb _) H') | auto].
  - intros x m' evs H. pose proof (proj1 (Hb _) H) as H1.
    destruct (F2 _ _ _ H1) as [H' El].
    split; [exact (proj2 (Hs _) H') | exact El].
  - split; intros H.
    + exact (proj2 (Hb _) (proj1 F3 (proj1 (Hs _) H))).
    + exact (proj2 (Hs _) (proj2 F3 (proj1 (Hb _) H))).
Qed.

Lemma FR_pure {A} : forall i m (x : A), FR i m (pure x) (pure x).
Proof.
  intros i m x. unfold FR, pure. split; [| split].
  - intros y mL' evs H. injection H as -> -> ->. exists m. auto.
  - intros y m' evs H. injection H as -> -> ->. auto.
  - split; intros H; discriminate H.
Qed.

Lemma FR_unmodeled {A} : forall i m, FR i m (@unmodeled A) (@unmodeled A).
Proof.
  intros i m. unfold FR, unmodeled. split; [| split].
  - intros y mL' evs H. discriminate H.
  - intros y m' evs H. discriminate H.
  - split; intros _; reflexivity.
Qed.

Lemma FR_choose {A} : forall i m (Pb Ps : A -> Prop),
  (forall x, Ps x <-> Pb x) -> FR i m (choose Pb) (choose Ps).
Proof.
  intros i m Pb Ps HP. unfold FR, choose. split; [| split].
  - intros y mL' evs (x & Hx & H). injection H as -> -> ->. exists m.
    split; [exists x; split; [apply HP; exact Hx | reflexivity] | auto].
  - intros y m' evs (x & Hx & H). injection H as -> -> ->.
    split; [exists x; split; [apply HP; exact Hx | reflexivity] | reflexivity].
  - split; intros (x & _ & H); discriminate H.
Qed.

Lemma FR_emit : forall i m evs, FR i m (emit evs) (emit evs).
Proof.
  intros i m evs. unfold FR, emit. split; [| split].
  - intros y mL' e H. injection H as -> -> ->. exists m. auto.
  - intros y m' e H. injection H as -> -> ->. auto.
  - split; intros H; discriminate H.
Qed.

Lemma FR_input : forall i m, FR i m input input.
Proof.
  intros i m. unfold FR, input. split; [| split].
  - intros y mL' e H. injection H as -> -> ->. exists m. auto.
  - intros y m' e H. injection H as -> -> ->. auto.
  - split; intros H; discriminate H.
Qed.

Lemma FR_sysno : forall i m, FR i m sysno sysno.
Proof.
  intros i m. unfold FR, sysno. split; [| split].
  - intros y mL' e H. injection H as -> -> ->. exists m. auto.
  - intros y m' e H. injection H as -> -> ->. auto.
  - split; intros H; discriminate H.
Qed.

Lemma FR_arg : forall i m k, FR i m (arg k) (arg k).
Proof.
  intros i m k. unfold FR, arg. split; [| split].
  - intros y mL' e H. injection H as -> -> ->. exists m. auto.
  - intros y m' e H. injection H as -> -> ->. auto.
  - split; intros H; discriminate H.
Qed.

(* [comment removed for export] *)
Lemma FR_modify : forall i m (fb fs : Model -> Model),
  fs (sl L m) = sl L (fb m) -> mlim (fb m) = mlim m ->
  FR i m (modify fb) (modify fs).
Proof.
  intros i m fb fs Hc Hl. unfold FR, modify. split; [| split].
  - intros y mL' e H. injection H as -> -> ->. exists (fb m). rewrite Hc. auto.
  - intros y m' e H. injection H as -> -> ->. rewrite Hc. auto.
  - split; intros H; discriminate H.
Qed.

Lemma FR_alt {A} : forall i m (cb1 cb2 cs1 cs2 : Sys A),
  FR i m cb1 cs1 -> FR i m cb2 cs2 -> FR i m (alt cb1 cb2) (alt cs1 cs2).
Proof.
  intros i m cb1 cb2 cs1 cs2 (F1 & F2 & F3) (G1 & G2 & G3). unfold FR, alt. split; [| split].
  - intros x mL' evs [H | H].
    + destruct (F1 _ _ _ H) as (m' & H' & E). exists m'. split; [left; exact H' | exact E].
    + destruct (G1 _ _ _ H) as (m' & H' & E). exists m'. split; [right; exact H' | exact E].
  - intros x m' evs [H | H].
    + destruct (F2 _ _ _ H) as [H' E]. split; [left; exact H' | exact E].
    + destruct (G2 _ _ _ H) as [H' E]. split; [right; exact H' | exact E].
  - split; intros [H | H]; [left; apply F3 | right; apply G3 | left; apply F3 | right; apply G3]; exact H.
Qed.

(* [comment removed for export] *)
Lemma FR_bind {A B} : forall i m (cb cs : Sys A) (kb ks : A -> Sys B),
  FR i m cb cs ->
  (forall x m1 evs1, cb i m (Ok x m1 evs1) -> FR i m1 (kb x) (ks x)) ->
  FR i m (bind cb kb) (bind cs ks).
Proof.
  intros i m cb cs kb ks (F1 & F2 & F3) HK. unfold FR. split; [| split].
  - intros y mL2 evs H. cbn [bind] in H.
    destruct H as (x & mL1 & evs1 & evs2 & Hc & Hk & ->).
    destruct (F1 _ _ _ Hc) as (m1 & Hc' & -> & El1).
    destruct (HK x m1 evs1 Hc') as (K1 & _ & _).
    destruct (K1 _ _ _ Hk) as (m2 & Hk' & -> & El2).
    exists m2. split; [| split; [reflexivity | rewrite El2; exact El1]].
    cbn [bind]. exists x, m1, evs1, evs2. auto.
  - intros y m2 evs H. cbn [bind] in H.
    destruct H as (x & m1 & evs1 & evs2 & Hc & Hk & ->).
    destruct (F2 _ _ _ Hc) as [Hc' El1].
    destruct (HK x m1 evs1 Hc) as (_ & K2 & _).
    destruct (K2 _ _ _ Hk) as [Hk' El2].
    split; [| rewrite El2; exact El1].
    cbn [bind]. exists x, (sl L m1), evs1, evs2. auto.
  - cbn [bind]. split.
    + intros [H | (x & mL1 & evs1 & Hc & Hk)].
      * left. apply F3. exact H.
      * destruct (F1 _ _ _ Hc) as (m1 & Hc' & -> & El1).
        destruct (HK x m1 evs1 Hc') as (_ & _ & K3).
        right. exists x, m1, evs1. split; [exact Hc' | apply K3; exact Hk].
    + intros [H | (x & m1 & evs1 & Hc & Hk)].
      * left. apply F3. exact H.
      * destruct (F2 _ _ _ Hc) as [Hc' El1].
        destruct (HK x m1 evs1 Hc) as (_ & _ & K3).
        right. exists x, (sl L m1), evs1. split; [exact Hc' | apply K3; exact Hk].
Qed.

(* [comment removed for export] *)
Lemma FR_get_model {A} : forall i m (kb ks : Model -> Sys A),
  FR i m (kb m) (ks (sl L m)) ->
  FR i m (bind get_model kb) (bind get_model ks).
Proof.
  intros i m kb ks H.
  apply (FR_iff i m _ (kb m) _ (ks (sl L m))); [| | exact H].
  - intros o. apply bind_get_model.
  - intros o. apply bind_get_model.
Qed.

(* [comment removed for export] *)
Lemma FR_get_fds : forall i m, FR i m get_fds get_fds.
Proof.
  intros i m. unfold FR, get_fds. split; [| split].
  - intros y mL' e H. injection H as -> -> ->. exists m. auto.
  - intros y m' e H. injection H as -> -> ->. auto.
  - split; intros H; discriminate H.
Qed.

(* [comment removed for export] *)
Lemma FR_get_vmmaps {A} : forall i m (kb ks : VmMaps -> Sys A),
  FR i m (kb (m_vmmaps m)) (ks (vml L (m_vmmaps m))) ->
  FR i m (bind get_vmmaps kb) (bind get_vmmaps ks).
Proof.
  intros i m kb ks H.
  apply (FR_iff i m _ (kb (m_vmmaps m)) _ (ks (vml L (m_vmmaps m)))); [| | exact H].
  - intros o. unfold bind, get_vmmaps. destruct o as [x m2 evs |]; split.
    + intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3). injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
    + intros H0. exists (m_vmmaps m), m, [], evs. auto.
    + intros [H0 | (x0 & m1 & evs1 & H1 & H2)]; [discriminate |]. injection H1 as -> -> ->. exact H2.
    + intros H0. right. exists (m_vmmaps m), m, []. auto.
  - intros o. unfold bind, get_vmmaps. destruct o as [x m2 evs |]; split.
    + intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3). injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
    + intros H0. exists (m_vmmaps (sl L m)), (sl L m), [], evs. auto.
    + intros [H0 | (x0 & m1 & evs1 & H1 & H2)]; [discriminate |]. injection H1 as -> -> ->. exact H2.
    + intros H0. right. exists (m_vmmaps (sl L m)), (sl L m), []. auto.
Qed.

(* [comment removed for export] *)
Lemma FRU_bind {A B} : forall (c : Sys A) (k : A -> Sys B),
  FRU c -> (forall x, FRU (k x)) -> FRU (bind c k).
Proof. intros c k Hc Hk i m. apply FR_bind; [apply Hc |]. intros x m1 evs1 _. apply Hk. Qed.

End FR.

(* [comment removed for export] *)
Ltac fr_modify := apply FR_modify; [reflexivity | reflexivity].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fr_same :=
  lazymatch goal with
  | |- FR ?L ?i ?m ?cb ?cs => change (FR L i m cb cb)
  end.

Ltac head_of t :=
  lazymatch t with
  | ?f _ => head_of f
  | _ => t
  end.

(* [comment removed for export] *)
Ltac destruct_inner x :=
  lazymatch x with
  | match ?y with _ => _ end => destruct_inner y
  | if ?b then _ else _ => destruct_inner b
  | ?f (match ?y with _ => _ end) => destruct_inner y
  | ?f (if ?b then _ else _) => destruct_inner b
  | _ => destruct x
  end.

(* [comment removed for export] *)
Ltac fr_step :=
  lazymatch goal with
  | |- FR _ _ _ (pure _) (pure _) => apply FR_pure
  | |- FR _ _ _ unmodeled unmodeled => apply FR_unmodeled
  | |- FR _ _ _ (emit _) (emit _) => apply FR_emit
  | |- FR _ _ _ input input => apply FR_input
  | |- FR _ _ _ sysno sysno => apply FR_sysno
  | |- FR _ _ _ (arg _) (arg _) => apply FR_arg
  | |- FR _ _ _ get_fds get_fds => apply FR_get_fds
  | |- FR _ _ _ (bind get_model _) (bind get_model _) => apply FR_get_model; cbv beta; try fr_same
  | |- FR _ _ _ (bind get_vmmaps _) (bind get_vmmaps _) => apply FR_get_vmmaps; cbv beta; try fr_same
  | |- FR _ _ _ (bind _ _) (bind _ _) => apply FR_bind; [| intros ? ? ? ?]
  | |- FR _ _ _ (alt _ _) (alt _ _) => apply FR_alt
  | |- FR _ _ _ (choose _) (choose _) => apply FR_choose; intros ?; try reflexivity
  | |- FR _ _ _ (modify _) (modify _) => apply FR_modify; try reflexivity
  | |- FR _ _ _ (let _ := _ in _) _ => cbv zeta
  | |- FR _ _ _ _ (let _ := _ in _) => cbv zeta
  | |- FR _ _ _ ((fun _ => _) _) _ => cbv beta
  | |- FR _ _ _ _ ((fun _ => _) _) => cbv beta
  | |- FR _ _ _ (match ?xb with _ => _ end) (match ?xs with _ => _ end) =>
      first [ progress cbv beta zeta
            | first [constr_eq xb xs | change xs with xb]; destruct_inner xb; cbv beta iota ]
  | |- FR _ _ _ (if ?bb then _ else _) (if ?bs then _ else _) =>
      first [ progress cbv beta zeta
            | first [constr_eq bb bs | change bs with bb]; destruct_inner bb; cbv beta iota ]
  | |- FR _ _ _ ?c ?c => let h := head_of c in progress (unfold h)
  | |- FR _ _ _ ?cb ?cs =>
      let hb := head_of cb in let hs := head_of cs in constr_eq hb hs; progress (unfold hb)
  end.

Ltac fr := repeat fr_step.

(* [comment removed for export] *)
Ltac destruct_inner_eq x :=
  lazymatch x with
  | match ?y with _ => _ end => destruct_inner_eq y
  | if ?b then _ else _ => destruct_inner_eq b
  | ?f (match ?y with _ => _ end) => destruct_inner_eq y
  | ?f (if ?b then _ else _) => destruct_inner_eq b
  | _ => destruct x eqn:?
  end.

Ltac frE_step :=
  lazymatch goal with
  | |- FR _ _ _ (match ?xb with _ => _ end) (match ?xs with _ => _ end) =>
      first [ progress cbv beta zeta
            | first [constr_eq xb xs | change xs with xb]; destruct_inner_eq xb; cbv beta iota ]
  | |- FR _ _ _ (if ?bb then _ else _) (if ?bs then _ else _) =>
      first [ progress cbv beta zeta
            | first [constr_eq bb bs | change bs with bb]; destruct_inner_eq bb; cbv beta iota ]
  | |- _ => fr_step
  end.

Ltac frE := repeat frE_step.

(* [comment removed for export] *)
Ltac sl_norm_in H :=
  cbv zeta in H;
  repeat match type of H with
         | context [m_vmmaps (sl ?L ?m)] => change (m_vmmaps (sl L m)) with (vml L (m_vmmaps m)) in H
         end;
  cbn [vml vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp] in H.

(* [comment removed for export] *)
Ltac rew_bools_in H :=
  repeat match goal with
         | E : ?b = true |- _ =>
             lazymatch E with H => fail | _ => idtac end;
             lazymatch type of H with context [b] => rewrite E in H end
         | E : ?b = false |- _ =>
             lazymatch E with H => fail | _ => idtac end;
             lazymatch type of H with context [b] => rewrite E in H end
         end.

(* [comment removed for export] *)
Ltac fr_inv :=
  repeat match goal with
         | H : choose _ _ _ (Ok _ _ _) |- _ =>
             let x := fresh "x" in let Hx := fresh "Hx" in let E := fresh "E" in
             destruct H as (x & Hx & E); injection E as -> -> ->
         | H : errno_from _ _ _ (Ok _ _ _) |- _ => unfold errno_from in H
         | H : input _ _ (Ok _ _ _) |- _ => unfold input in H; injection H as -> -> ->
         | H : pure _ _ _ (Ok _ _ _) |- _ => unfold pure in H; injection H as -> -> ->
         | H : get_model _ _ (Ok _ _ _) |- _ => unfold get_model in H; injection H as -> -> ->
         end.

(* [comment removed for export] *)
Ltac fq_step :=
  lazymatch goal with
  | |- FR _ _ _ (pure _) (pure _) => apply FR_pure
  | |- FR _ _ _ unmodeled unmodeled => apply FR_unmodeled
  | |- FR _ _ _ (emit _) (emit _) => apply FR_emit
  | |- FR _ _ _ input input => apply FR_input
  | |- FR _ _ _ sysno sysno => apply FR_sysno
  | |- FR _ _ _ (arg _) (arg _) => apply FR_arg
  | |- FR _ _ _ get_fds get_fds => apply FR_get_fds
  | |- FR _ _ _ (bind get_model _) (bind get_model _) => apply FR_get_model; cbv beta
  | |- FR _ _ _ (bind get_vmmaps _) (bind get_vmmaps _) => apply FR_get_vmmaps; cbv beta
  | |- FR _ _ _ (bind _ _) (bind _ _) => apply FR_bind; [| intros ? ? ? ?]
  | |- FR _ _ _ (alt _ _) (alt _ _) => apply FR_alt
  | |- FR _ _ _ (choose _) (choose _) => apply FR_choose; intros ?; try reflexivity
  | |- FR _ _ _ (modify _) (modify _) => apply FR_modify; try reflexivity
  | |- FR _ _ _ (let _ := _ in _) _ => cbv zeta
  | |- FR _ _ _ _ (let _ := _ in _) => cbv zeta
  | |- FR _ _ _ ((fun _ => _) _) _ => cbv beta
  | |- FR _ _ _ _ ((fun _ => _) _) => cbv beta
  | |- FR _ _ _ (match ?xb with _ => _ end) (match ?xs with _ => _ end) =>
      first [ progress cbv beta zeta
            | first [constr_eq xb xs | change xs with xb]; destruct_inner xb; cbv beta iota ]
  | |- FR _ _ _ (if ?bb then _ else _) (if ?bs then _ else _) =>
      first [ progress cbv beta zeta
            | first [constr_eq bb bs | change bs with bb]; destruct_inner bb; cbv beta iota ]
  | |- FR _ _ _ ?c ?c => let h := head_of c in progress (unfold h)
  | |- FR _ _ _ ?cb ?cs =>
      let hb := head_of cb in let hs := head_of cs in constr_eq hb hs; progress (unfold hb)
  end.
Ltac fq := repeat fq_step.
