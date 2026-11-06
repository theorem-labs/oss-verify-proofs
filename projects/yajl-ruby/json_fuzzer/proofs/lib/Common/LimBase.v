(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vml (L : Z) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h)
               L (vm_mmap_base h) (vm_init_sp h).

Definition sl (L : Z) (m : Model) : Model := with_vmmaps (vml L (m_vmmaps m)) m.

Definition slc (L : Z) (c : config) : config := mkCfg (cfg_ms c) (sl L (cfg_model c)).

Definition slst (L : Z) (X : step_to) : step_to :=
  match X with SNext c => SNext (slc L c) | SError => SError end.

(* [comment removed for export] *)
Definition mlim (m : Model) : Z := vm_limit (m_vmmaps m).

Lemma vml_limit : forall L h, vm_limit (vml L h) = L.
Proof. reflexivity. Qed.

Lemma vml_id : forall h, vml (vm_limit h) h = h.
Proof. intros [r mp na sb b l mb sp]. reflexivity. Qed.

Lemma vml_vml : forall L L' h, vml L (vml L' h) = vml L h.
Proof. reflexivity. Qed.

Lemma mlim_sl : forall L m, mlim (sl L m) = L.
Proof. reflexivity. Qed.

Lemma sl_id : forall m, sl (mlim m) m = m.
Proof.
  intros [fd [h lz mt] io fs pr lm tm]. unfold sl, mlim, with_vmmaps. cbn.
  rewrite vml_id. reflexivity.
Qed.

Lemma sl_id_eq : forall L m, mlim m = L -> sl L m = m.
Proof. intros L m <-. apply sl_id. Qed.

Lemma sl_sl : forall L L' m, sl L (sl L' m) = sl L m.
Proof. reflexivity. Qed.

Lemma slc_id_eq : forall L c, mlim (cfg_model c) = L -> slc L c = c.
Proof. intros L [ms m] H. unfold slc. cbn in *. rewrite (sl_id_eq L m H). reflexivity. Qed.

Lemma slc_slc : forall L L' c, slc L (slc L' c) = slc L c.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sl_fd : forall L m, m_fd (sl L m) = m_fd m. Proof. reflexivity. Qed.
Lemma sl_io : forall L m, m_io (sl L m) = m_io m. Proof. reflexivity. Qed.
Lemma sl_fsys : forall L m, m_fsys (sl L m) = m_fsys m. Proof. reflexivity. Qed.
Lemma sl_proc : forall L m, m_proc (sl L m) = m_proc m. Proof. reflexivity. Qed.
Lemma sl_lim : forall L m, m_lim (sl L m) = m_lim m. Proof. reflexivity. Qed.
Lemma sl_time : forall L m, m_time (sl L m) = m_time m. Proof. reflexivity. Qed.
Lemma sl_vm_lazy : forall L m, m_vm_lazy (sl L m) = m_vm_lazy m. Proof. reflexivity. Qed.
Lemma sl_vm_materialized : forall L m, m_vm_materialized (sl L m) = m_vm_materialized m. Proof. reflexivity. Qed.
Lemma sl_vmmaps : forall L m, m_vmmaps (sl L m) = vml L (m_vmmaps m). Proof. reflexivity. Qed.
Lemma sl_halted : forall L m, m_halted (sl L m) = m_halted m. Proof. reflexivity. Qed.
Lemma sl_killed : forall L m, m_killed (sl L m) = m_killed m. Proof. reflexivity. Qed.
Lemma sl_fs : forall L m, m_fs (sl L m) = m_fs m. Proof. reflexivity. Qed.
Lemma sl_fds : forall L m, m_fds (sl L m) = m_fds m. Proof. reflexivity. Qed.

Lemma sl_backing_used : forall L m, vm_backing_used (sl L m) = vm_backing_used m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sl_inj_limit : forall L m m', sl L m = sl L m' -> mlim m = mlim m' -> m = m'.
Proof.
  intros L m m' H Hl. rewrite <- (sl_id m), <- (sl_id m'). rewrite <- Hl.
  rewrite <- (sl_sl (mlim m) L m), <- (sl_sl (mlim m) L m'). rewrite H. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition entry_fits (e : word * word) : Prop :=
  bv_unsigned (fst e) + bv_unsigned (snd e) <= two_pow_64.

Definition fits (m : Model) : Prop := Forall entry_fits (vm_maps (m_vmmaps m)).

Lemma fits_sl : forall L m, fits (sl L m) <-> fits m.
Proof. intros L m. unfold fits. reflexivity. Qed.

Lemma fits_vmmaps_eq : forall m m', m_vmmaps m' = m_vmmaps m -> fits m -> fits m'.
Proof. intros m m' E H. unfold fits in *. rewrite E. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma materialize_accesses_mono : forall lz mt used L L' acc pages,
  L <= L' ->
  materialize_accesses lz mt used L acc = Some pages ->
  materialize_accesses lz mt used L' acc = Some pages.
Proof.
  intros lz mt used L L' acc pages HL. unfold materialize_accesses.
  destruct (newly_materialized_pages lz mt acc) as [| p new]; [exact (fun H => H) |].
  destruct (used + Z.of_nat (length (p :: new)) * page_size <=? L) eqn:E; [| discriminate].
  apply Z.leb_le in E.
  replace (used + Z.of_nat (length (p :: new)) * page_size <=? L') with true
    by (symmetry; apply Z.leb_le; lia).
  exact (fun H => H).
Qed.

(* [comment removed for export] *)
Lemma materialize_sl_fwd : forall L m acc mL',
  L <= mlim m ->
  materialize_model_accesses (sl L m) acc = Some mL' ->
  exists m', materialize_model_accesses m acc = Some m' /\ mL' = sl L m' /\ mlim m' = mlim m.
Proof.
  intros L m acc mL' HL H. unfold materialize_model_accesses in *.
  rewrite sl_vm_lazy, sl_vm_materialized, sl_backing_used, sl_vmmaps, vml_limit in H.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) L acc)
    as [pages |] eqn:E; [| discriminate].
  rewrite (materialize_accesses_mono _ _ _ L (vm_limit (m_vmmaps m)) acc pages HL E).
  exists (with_vm_backing (m_vm_lazy m) pages m). split; [reflexivity |].
  injection H as <-. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma materialize_sl_bwd : forall L m acc m',
  materialize_model_accesses m acc = Some m' ->
  materialize_model_accesses (sl L m) acc = Some (sl L m')
  \/ materialize_model_accesses (sl L m) acc = None.
Proof.
  intros L m acc m' H. unfold materialize_model_accesses in *.
  rewrite sl_vm_lazy, sl_vm_materialized, sl_backing_used, sl_vmmaps, vml_limit.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m)
              (vm_limit (m_vmmaps m)) acc) as [pages |] eqn:E; [| discriminate].
  injection H as <-.
  unfold materialize_accesses in *.
  destruct (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) acc) as [| p new].
  - injection E as <-. left. reflexivity.
  - destruct (vm_backing_used m + Z.of_nat (length (p :: new)) * page_size <=? L);
      [| right; reflexivity].
    destruct (vm_backing_used m + Z.of_nat (length (p :: new)) * page_size <=? vm_limit (m_vmmaps m));
      [| discriminate].
    injection E as <-. left. reflexivity.
Qed.

Lemma materialize_fits : forall m acc m',
  materialize_model_accesses m acc = Some m' -> fits m -> fits m'.
Proof.
  intros m acc m' H. apply fits_vmmaps_eq.
  destruct (materialize_model_accesses_frame m acc m' H) as (_ & E & _). exact E.
Qed.

Lemma materialize_mlim : forall m acc m',
  materialize_model_accesses m acc = Some m' -> mlim m' = mlim m.
Proof.
  intros m acc m' H. unfold mlim.
  destruct (materialize_model_accesses_frame m acc m' H) as (_ & -> & _). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refusal_b_sl : forall L i m r, refusal_b i (sl L m) r = refusal_b i m r.
Proof. reflexivity. Qed.

Lemma injected_family_off_sl : forall cfg i, injected_family_off cfg i = injected_family_off cfg i.
Proof. reflexivity. Qed.
