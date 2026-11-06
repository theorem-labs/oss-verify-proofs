(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimDefs LimFrame.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition lrelg {A} (L : Z) (G : Model -> Prop) (c c' : Sys A) : Prop :=
  forall i m o, G m -> c i m o -> c' i (m_relim L m) (o_relim L o).

Lemma lrelg_of_lrel {A} L G (c c' : Sys A) : lrel L c c' -> lrelg L G c c'.
Proof. intros H i m o _ Hc. exact (H i m o Hc). Qed.
Lemma bind_get_model_iff {B} (k : Model -> Sys B) : forall i m o,
  bind get_model k i m o <-> k m i m o.
Proof. intros i m o. apply bind_get_model. Qed.

(* [comment removed for export] *)
Lemma forget_vm_ranges_relim : forall L rs m,
  forget_vm_ranges rs (m_relim L m) = m_relim L (forget_vm_ranges rs m).
Proof.
  intros L rs. induction rs as [| [a n] rs IH]; intros m; [reflexivity |].
  cbn [forget_vm_ranges]. rewrite <- IH. reflexivity.
Qed.
Lemma forget_vm_ranges_limit : forall rs m, m_limit (forget_vm_ranges rs m) = m_limit m.
Proof.
  intros rs. induction rs as [| [a n] rs IH]; intros m; [reflexivity |].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma brk_lpres : forall req, lpres (brk_spec req).
Proof.
  intros req i m x m' evs H. unfold brk_spec in H. sys_inv_hyp H.
  unfold with_brk_next. rewrite forget_vm_ranges_limit. reflexivity.
Qed.

Lemma brk_r_ok_relim : forall L m req r,
  brk_budget_refused_b (m_relim L m) req = false ->
  brk_r_ok m req r = true -> brk_r_ok (m_relim L m) req r = true.
Proof.
  intros L m req r HG H.
  unfold brk_r_ok, brk_budget_refused_b, brk_grow_ok, brk_budget_ok, min_brk, alloc_top in *.
  autorewrite with relim in *. cbv zeta in *.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (vm_start_brk (m_vmmaps m)))%Z) eqn:E1; [exact H |].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m)))%Z eqn:E2; [exact H |].
  apply andb_true_iff in H. destruct H as [Hr Hgrow]. apply andb_true_iff. split; [exact Hr |].
  destruct ((0 <? bv_unsigned (vm_brk (m_vmmaps m)))%Z && (bv_unsigned (vm_brk (m_vmmaps m)) <? bv_unsigned r)%Z) eqn:E3; [| reflexivity].
  apply andb_true_iff in Hgrow. destruct Hgrow as [Hfree _]. apply andb_true_iff. split; [exact Hfree |].
  apply andb_true_iff in E3. destruct E3 as [E3a E3b].
  apply orb_true_iff in Hr. destruct Hr as [Hr | Hr]; apply bv_eqb_eq in Hr; subst r.
  - cbn [negb andb] in HG. rewrite E3a, E3b in HG. cbn [andb] in HG.
    apply negb_false_iff in HG. exact HG.
  - apply Z.ltb_lt in E3b. lia.
Qed.

Lemma with_brk_next_relim : forall L m req r,
  with_brk_next (m_relim L m) req r = m_relim L (with_brk_next m req r).
Proof. intros L m req r. unfold with_brk_next. autorewrite with relim. rewrite <- forget_vm_ranges_relim. reflexivity. Qed.

(* [comment removed for export] *)
Ltac to_lrel L H :=
  lazymatch type of H with
  | ?c ?i ?m ?o =>
      lazymatch goal with
      | |- ?c' _ _ _ => let HL := fresh "HL" in enough (HL : lrel L c c') by exact (HL i m o H); clear H
      end
  end.

Lemma brk_frame : forall L req i m o,
  brk_spec req i m o ->
  brk_budget_refused_b (m_relim L m) req = false ->
  brk_spec req i (m_relim L m) (o_relim L o).
Proof.
  intros L req i m o H HG. unfold brk_spec in *.
  apply bind_get_model_iff in H. apply bind_get_model_iff. cbv zeta in *.
  to_lrel L H.
  apply lrel_bind; [apply lrel_choose_imp; intros r Hr; exact (brk_r_ok_relim L m req r HG Hr) |].
  intros r. apply lrel_bind; [apply lrel_modify; intros m1; apply with_brk_next_relim |].
  intros []. autorewrite with relim. apply lrel_pure.
Qed.

(* [comment removed for export] *)
Lemma lrelg_alt {A} L G (c1 c2 c1' c2' : Sys A) :
  lrelg L G c1 c1' -> lrelg L G c2 c2' -> lrelg L G (alt c1 c2) (alt c1' c2').
Proof. intros H1 H2 i m o HG [H | H]; [left; exact (H1 _ _ _ HG H) | right; exact (H2 _ _ _ HG H)]. Qed.
Lemma lrelg_bind_get_model {B} L G (k k' : Model -> Sys B) :
  (forall m, G m -> lrel L (k m) (k' (m_relim L m))) -> lrelg L G (bind get_model k) (bind get_model k').
Proof.
  intros Hk i m o HG H. apply bind_get_model_iff in H. apply bind_get_model_iff.
  exact (Hk m HG i m o H).
Qed.

Ltac lrelg_step :=
  lazymatch goal with
  | |- lrelg _ _ (alt _ _) (alt _ _) => apply lrelg_alt
  | |- lrelg _ _ (bind get_model _) (bind get_model _) => apply lrelg_bind_get_model; intros ?m ?HG
  | |- lrelg _ _ (match ?s with _ => _ end) (match ?s with _ => _ end) => split_on s
  | |- lrelg _ _ (if ?s then _ else _) (if ?s then _ else _) => split_on s
  | |- lrelg _ _ (let _ := _ in _) _ => cbv zeta
  | |- lrelg _ _ ?c ?c => apply lrelg_of_lrel; solve [ lrel_go ]
  end.
Ltac lrelg_go := repeat lrelg_step.

(* [comment removed for export] *)
Ltac use_paths HG :=
  repeat match goal with
  | E : ?b = true |- _ => lazymatch E with HG => fail | _ => idtac end;
                           lazymatch type of HG with context[b] => rewrite E in HG end
  | E : ?b = false |- _ => lazymatch E with HG => fail | _ => idtac end;
                            lazymatch type of HG with context[b] => rewrite E in HG end
  end; cbv iota beta in HG; cbn [negb andb orb] in HG.
Ltac gate_fin :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : _ && _ = true |- _ => apply andb_true_iff in H
  | |- _ && _ = true => apply andb_true_iff
  end; try assumption; try reflexivity.

Lemma mprotect_lpres : forall addr len prot, lpres (mprotect_spec addr len prot).
Proof. intros addr len prot. lpres_brute. Qed.

Lemma mprotect_frame : forall L addr len prot i m o,
  mprotect_spec addr len prot i m o ->
  mprotect_budget_refused_b addr len prot (m_relim L m) = false ->
  mprotect_spec addr len prot i (m_relim L m) (o_relim L o).
Proof.
  intros L addr len prot i m o H HG0.
  enough (HL : lrelg L (fun m => mprotect_budget_refused_b addr len prot (m_relim L m) = false)
                 (mprotect_spec addr len prot) (mprotect_spec addr len prot)) by exact (HL i m o HG0 H).
  clear. unfold mprotect_spec. lrelg_go. lrel_go.
  all: unfold mprotect_budget_refused_b in HG; cbv zeta in HG; autorewrite with relim in HG; use_paths HG; gate_fin.
Qed.

(* [comment removed for export] *)
Lemma mmap_lpres : forall addr len prot flags fd off, lpres (mmap_spec addr len prot flags fd off).
Proof. intros. lpres_brute. Qed.

Lemma mmap_frame : forall L addr len prot flags fd off i m o,
  mmap_spec addr len prot flags fd off i m o ->
  mmap_budget_refused_b addr len prot flags fd off m = false ->
  mmap_budget_refused_b addr len prot flags fd off (m_relim L m) = false ->
  mmap_spec addr len prot flags fd off i (m_relim L m) (o_relim L o).
Proof.
  intros L addr len prot flags fd off i m o H HG0 HG1.
  enough (HL : lrelg L (fun m => mmap_budget_refused_b addr len prot flags fd off m = false
                              /\ mmap_budget_refused_b addr len prot flags fd off (m_relim L m) = false)
                 (mmap_spec addr len prot flags fd off) (mmap_spec addr len prot flags fd off)) by exact (HL i m o (conj HG0 HG1) H).
  clear. unfold mmap_spec. lrelg_go. all: try (lrel_go; fail).
  all: lrel_go.
  all: destruct HG as [HG0 HG]; unfold mmap_budget_refused_b in HG0, HG; cbv zeta in HG0, HG; unfold alloc_top in *; autorewrite with relim in *; use_paths HG; use_paths HG0.
  all: gate_fin.
  all: try exact HG.
Qed.
