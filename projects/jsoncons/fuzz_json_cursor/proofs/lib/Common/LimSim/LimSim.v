(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Open Scope bv_scope.
Open Scope sys_scope.

Definition relimV (L : Z) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) L
               (vm_mmap_base h) (vm_init_sp h).
Definition relimS (L : Z) (v : VmState) : VmState :=
  mkVmState (relimV L (vmst_maps v)) (vmst_lazy v) (vmst_materialized v).
Definition relim (L : Z) (m : Model) : Model :=
  mkModelOf (m_fd m) (relimS L (m_vm m)) (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).
Definition relim_cfg (L : Z) (c : config) : config := mkCfg (cfg_ms c) (relim L (cfg_model c)).

Lemma relim_limit : forall L m, vm_limit (m_vmmaps (relim L m)) = L.
Proof. reflexivity. Qed.
Lemma relim_id : forall m, relim (vm_limit (m_vmmaps m)) m = m.
Proof. intros [fd [[r mp na sb b l mb isp] lz mt] io fsys pr li ti]; reflexivity. Qed.
Lemma relim_relim : forall L L' m, relim L (relim L' m) = relim L m.
Proof. reflexivity. Qed.

Lemma relim_vm_backing_used : forall L m, vm_backing_used (relim L m) = vm_backing_used m.
Proof. reflexivity. Qed.
Lemma relim_halted : forall L m, m_halted (relim L m) = m_halted m.
Proof. reflexivity. Qed.
Lemma relim_killed : forall L m, m_killed (relim L m) = m_killed m.
Proof. reflexivity. Qed.
Lemma relim_fs : forall L m, m_fs (relim L m) = m_fs m.
Proof. reflexivity. Qed.

Lemma materialize_accesses_mono : forall lazy mat used L L0 acc pages,
  L <= L0 ->
  materialize_accesses lazy mat used L acc = Some pages ->
  materialize_accesses lazy mat used L0 acc = Some pages.
Proof.
  intros lazy mat used L L0 acc pages HLE. unfold materialize_accesses.
  destruct (newly_materialized_pages lazy mat acc) as [|p ps]; [intros H; exact H|].
  intros H. destruct (Z.leb_spec (used + Z.of_nat (length (p :: ps)) * page_size) L); [|discriminate].
  destruct (Z.leb_spec (used + Z.of_nat (length (p :: ps)) * page_size) L0); [exact H | lia].
Qed.

Lemma materialize_accesses_down : forall lazy mat used L L0 acc pages,
  materialize_accesses lazy mat used L0 acc = Some pages ->
  materialize_accesses lazy mat used L acc <> None ->
  materialize_accesses lazy mat used L acc = Some pages.
Proof.
  intros lazy mat used L L0 acc pages. unfold materialize_accesses.
  destruct (newly_materialized_pages lazy mat acc) as [|p ps]; [intros H _; exact H|].
  destruct (Z.leb (used + Z.of_nat (length (p :: ps)) * page_size) L0); [|discriminate].
  destruct (Z.leb (used + Z.of_nat (length (p :: ps)) * page_size) L); [intros H _; exact H | intros _ H; exfalso; apply H; reflexivity].
Qed.

Lemma materialize_relim_up : forall L m acc m1,
  L <= vm_limit (m_vmmaps m) ->
  materialize_model_accesses (relim L m) acc = Some m1 ->
  exists m0, materialize_model_accesses m acc = Some m0 /\ m1 = relim L m0.
Proof.
  intros L m acc m1 HLE. unfold materialize_model_accesses.
  change (m_vm_lazy (relim L m)) with (m_vm_lazy m). change (m_vm_materialized (relim L m)) with (m_vm_materialized m).
  rewrite relim_vm_backing_used, relim_limit.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) L acc) as [pages|] eqn:E; [|discriminate].
  rewrite (materialize_accesses_mono _ _ _ _ _ _ _ HLE E). intros H; injection H as <-.
  eexists; split; [reflexivity|]. destruct m as [fd [h lz mt] io fsys pr li ti]; reflexivity.
Qed.

Lemma materialize_relim_down : forall L m acc m0,
  materialize_model_accesses m acc = Some m0 ->
  materialize_model_accesses (relim L m) acc <> None ->
  materialize_model_accesses (relim L m) acc = Some (relim L m0).
Proof.
  intros L m acc m0. unfold materialize_model_accesses.
  change (m_vm_lazy (relim L m)) with (m_vm_lazy m). change (m_vm_materialized (relim L m)) with (m_vm_materialized m).
  rewrite relim_vm_backing_used, relim_limit.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) (vm_limit (m_vmmaps m)) acc) as [pages|] eqn:E; [|discriminate].
  intros H HN; injection H as <-.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) L acc) as [pages'|] eqn:E'; [|exfalso; apply HN; reflexivity].
  pose proof (materialize_accesses_down _ _ _ L _ _ _ E) as E''. rewrite E' in E''.
  assert (E3 : Some pages' = Some pages) by (apply E''; discriminate). injection E3 as ->.
  reflexivity.
Qed.

Lemma materialize_limit : forall m acc m0,
  materialize_model_accesses m acc = Some m0 -> vm_limit (m_vmmaps m0) = vm_limit (m_vmmaps m).
Proof.
  intros m acc m0 H. destruct (materialize_model_accesses_frame m acc m0 H) as (_ & E & _). rewrite E. reflexivity.
Qed.

Section Dir.
Variable L0 L : Z.

Definition MOK (m : Model) : Prop := vm_limit (m_vmmaps m) = L0.

Definition orel {A} (o : outcome A) (o0 : outcome A) : Prop :=
  match o, o0 with
  | Ok x m1 e, Ok x0 m0 e0 => x = x0 /\ m1 = relim L m0 /\ e = e0 /\ MOK m0
  | Unmodeled, Unmodeled => True
  | _, _ => False
  end.

Definition DIR {A} (d : bool) (i : SyscallInput) (m : Model) (c c' : Sys A) : Prop :=
  if d then forall o, c i (relim L m) o -> exists o0, c' i m o0 /\ orel o o0
  else forall o0, c' i m o0 -> exists o, c i (relim L m) o /\ orel o o0.

Lemma orel_refl_ok {A} : forall (x : A) m e, MOK m -> orel (Ok x (relim L m) e) (Ok x m e).
Proof. intros; cbn; repeat split; auto. Qed.

Lemma dir_pure {A} : forall (d : bool) (i : SyscallInput) (m : Model) (x x' : A), x = x' -> MOK m -> DIR d i m (pure x) (pure x').
Proof.
  intros d i m x x' <- HM; destruct d; cbn; intros o ->.
  - eexists; split; [reflexivity|]. apply orel_refl_ok; exact HM.
  - eexists; split; [reflexivity|]. apply orel_refl_ok; exact HM.
Qed.

Lemma dir_unmodeled {A} : forall (d : bool) (i : SyscallInput) (m : Model), DIR d i m (@unmodeled A) (@unmodeled A).
Proof. intros d i m; destruct d; cbn; intros o ->; eexists; split; [reflexivity| exact I | reflexivity | exact I]. Qed.

Lemma dir_emit : forall (d : bool) (i : SyscallInput) (m : Model) e, MOK m -> DIR d i m (emit e) (emit e).
Proof. intros d i m e HM; destruct d; cbn; intros o ->; eexists; split; [reflexivity| |reflexivity|]; apply orel_refl_ok; exact HM. Qed.

Lemma dir_modify : forall (d : bool) (i : SyscallInput) (m : Model) f f',
  f (relim L m) = relim L (f' m) -> MOK (f' m) -> DIR d i m (modify f) (modify f').
Proof.
  intros d i m f f' E HM; destruct d; cbn; intros o ->; eexists; split; [reflexivity| |reflexivity|]; rewrite E; apply orel_refl_ok; exact HM.
Qed.

Lemma dir_choose {A} : forall (d : bool) (i : SyscallInput) (m : Model) (P P' : A -> Prop),
  (if d then forall x, P x -> P' x else forall x, P' x -> P x) -> MOK m -> DIR d i m (choose P) (choose P').
Proof.
  intros d i m P P' HP HM; destruct d; cbn; intros o (x & Hx & ->); eexists; (split; [exists x; split; [apply HP; exact Hx|reflexivity]|]);
    apply orel_refl_ok; exact HM.
Qed.

Lemma dir_choose_same {A} : forall (d : bool) (i : SyscallInput) (m : Model) (P : A -> Prop), MOK m -> DIR d i m (choose P) (choose P).
Proof. intros d i m P HM. apply dir_choose; [destruct d; intros x H; exact H | exact HM]. Qed.

Lemma dir_input : forall (d : bool) (i : SyscallInput) (m : Model), MOK m -> DIR d i m input input.
Proof. intros d i m HM; destruct d; cbn; intros o ->; eexists; split; [reflexivity| |reflexivity|]; apply orel_refl_ok; exact HM. Qed.
Lemma dir_sysno : forall (d : bool) (i : SyscallInput) (m : Model), MOK m -> DIR d i m sysno sysno.
Proof. intros d i m HM; destruct d; cbn; intros o ->; eexists; split; [reflexivity| |reflexivity|]; apply orel_refl_ok; exact HM. Qed.
Lemma dir_arg : forall (d : bool) (i : SyscallInput) (m : Model) k, MOK m -> DIR d i m (arg k) (arg k).
Proof. intros d i m k HM; destruct d; cbn; intros o ->; eexists; split; [reflexivity| |reflexivity|]; apply orel_refl_ok; exact HM. Qed.
Lemma dir_get_fds : forall (d : bool) (i : SyscallInput) (m : Model), MOK m -> DIR d i m get_fds get_fds.
Proof. intros d i m HM; destruct d; cbn; intros o ->; eexists; split; [reflexivity| |reflexivity|]; apply orel_refl_ok; exact HM. Qed.

Lemma dir_alt {A} : forall (d : bool) (i : SyscallInput) (m : Model) (c1 c2 c1' c2' : Sys A),
  DIR d i m c1 c1' -> DIR d i m c2 c2' -> DIR d i m (alt c1 c2) (alt c1' c2').
Proof.
  intros d i m c1 c2 c1' c2' H1 H2; destruct d; cbn in *; intros o [Ho|Ho].
  - destruct (H1 o Ho) as (o0 & ? & ?). exists o0; split; [left|]; assumption.
  - destruct (H2 o Ho) as (o0 & ? & ?). exists o0; split; [right|]; assumption.
  - destruct (H1 o Ho) as (o0 & ? & ?). exists o0; split; [left|]; assumption.
  - destruct (H2 o Ho) as (o0 & ? & ?). exists o0; split; [right|]; assumption.
Qed.

Lemma dir_bind {A B} : forall (d : bool) (i : SyscallInput) (m : Model) (c c' : Sys A) (k k' : A -> Sys B),
  DIR d i m c c' -> (forall x m1, MOK m1 -> DIR d i m1 (k x) (k' x)) -> DIR d i m (bind c k) (bind c' k').
Proof.
  intros d i m c c' k k' Hc Hk; destruct d; cbn in *.
  - intros [y m2 e|] Hb; cbn in Hb.
    + destruct Hb as (x & m1 & e1 & e2 & H1 & H2 & ->).
      destruct (Hc _ H1) as ([x0 m10 e10|] & H1' & R1); cbn in R1; [|contradiction].
      destruct R1 as (<- & -> & <- & M1).
      destruct (Hk x m10 M1 _ H2) as ([y0 m20 e20|] & H2' & R2); cbn in R2; [|contradiction].
      destruct R2 as (<- & -> & <- & M2).
      exists (Ok y m20 (e1 ++ e2)). split; [apply (bind_ok _ _ _ _ _ _ _ _ _ _ H1' H2') | cbn; repeat split; auto].
    + destruct Hb as [H1 | (x & m1 & e1 & H1 & H2)].
      * destruct (Hc _ H1) as ([|] & H1' & R1); cbn in R1; [contradiction|].
        exists Unmodeled. split; [apply bind_unmodeled1; exact H1' | exact I].
      * destruct (Hc _ H1) as ([x0 m10 e10|] & H1' & R1); cbn in R1; [|contradiction].
        destruct R1 as (<- & -> & <- & M1).
        destruct (Hk x m10 M1 _ H2) as ([|] & H2' & R2); cbn in R2; [contradiction|].
        exists Unmodeled. split; [eapply bind_unmodeled2; [exact H1' | exact H2'] | exact I].
  - intros [y m2 e|] Hb; cbn in Hb.
    + destruct Hb as (x & m1 & e1 & e2 & H1 & H2 & ->).
      destruct (Hc _ H1) as ([x0 m10 e10|] & H1' & R1); cbn in R1; [|contradiction].
      destruct R1 as (-> & -> & -> & M1).
      destruct (Hk x m1 M1 _ H2) as ([y0 m20 e20|] & H2' & R2); cbn in R2; [|contradiction].
      destruct R2 as (-> & -> & -> & M2).
      exists (Ok y (relim L m2) (e1 ++ e2)). split; [apply (bind_ok _ _ _ _ _ _ _ _ _ _ H1' H2') | cbn; repeat split; auto].
    + destruct Hb as [H1 | (x & m1 & e1 & H1 & H2)].
      * destruct (Hc _ H1) as ([|] & H1' & R1); cbn in R1; [contradiction|].
        exists Unmodeled. split; [apply bind_unmodeled1; exact H1' | exact I].
      * destruct (Hc _ H1) as ([x0 m10 e10|] & H1' & R1); cbn in R1; [|contradiction].
        destruct R1 as (-> & -> & -> & M1).
        destruct (Hk x m1 M1 _ H2) as ([|] & H2' & R2); cbn in R2; [contradiction|].
        exists Unmodeled. split; [eapply bind_unmodeled2; [exact H1' | exact H2'] | exact I].
Qed.

Lemma dir_bind_get_model {B} : forall (d : bool) (i : SyscallInput) (m : Model) (k k' : Model -> Sys B),
  DIR d i m (k (relim L m)) (k' m) -> DIR d i m (bind get_model k) (bind get_model k').
Proof.
  intros d i m k k' Hk; destruct d; cbn in Hk |- *; intros o Ho.
  - apply bind_get_model in Ho. destruct (Hk _ Ho) as (o0 & H & R). exists o0. split; [apply bind_get_model; exact H | exact R].
  - apply bind_get_model in Ho. destruct (Hk _ Ho) as (o0 & H & R). exists o0. split; [apply bind_get_model; exact H | exact R].
Qed.

Lemma bind_get_vmmaps {A} (k : VmMaps -> Sys A) : forall i m o, bind get_vmmaps k i m o <-> k (m_vmmaps m) i m o.
Proof.
  intros i m o. unfold bind, get_vmmaps. destruct o as [x m2 evs|]; split.
  - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3). injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
  - intros H. exists (m_vmmaps m), m, [], evs. split; [reflexivity|]. split; [exact H | reflexivity].
  - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|]. injection H1 as -> -> ->. exact H2.
  - intros H. right. exists (m_vmmaps m), m, []. split; [reflexivity | exact H].
Qed.

Lemma dir_bind_get_vmmaps {B} : forall (d : bool) (i : SyscallInput) (m : Model) (k k' : VmMaps -> Sys B),
  DIR d i m (k (relimV L (m_vmmaps m))) (k' (m_vmmaps m)) -> DIR d i m (bind get_vmmaps k) (bind get_vmmaps k').
Proof.
  intros d i m k k' Hk; destruct d; cbn in Hk |- *; intros o Ho.
  - apply bind_get_vmmaps in Ho. destruct (Hk _ Ho) as (o0 & H & R). exists o0. split; [apply bind_get_vmmaps; exact H | exact R].
  - apply bind_get_vmmaps in Ho. destruct (Hk _ Ho) as (o0 & H & R). exists o0. split; [apply bind_get_vmmaps; exact H | exact R].
Qed.

Lemma dir_bind_reader {A B} : forall (d : bool) (i : SyscallInput) (m : Model) (c c' : Sys A) (v v' : SyscallInput -> Model -> A) (k k' : A -> Sys B),
  (forall i0 m0 o, c i0 m0 o <-> o = Ok (v i0 m0) m0 []) ->
  (forall i0 m0 o, c' i0 m0 o <-> o = Ok (v' i0 m0) m0 []) ->
  DIR d i m (k (v i (relim L m))) (k' (v' i m)) -> DIR d i m (bind c k) (bind c' k').
Proof.
  intros d i m c c' v v' k k' Hc Hc' Hk.
  assert (E : forall (cc : Sys A) vv (kk : A -> Sys B) i0 m0 o, (forall i1 m1 o1, cc i1 m1 o1 <-> o1 = Ok (vv i1 m1) m1 []) -> (bind cc kk i0 m0 o <-> kk (vv i0 m0) i0 m0 o)).
  { intros cc vv kk i0 m0 o Hcc. unfold bind. destruct o as [x m2 evs|]; split.
    - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3). apply Hcc in H1. injection H1 as -> -> ->. cbn in H3. subst evs. exact H2.
    - intros H. exists (vv i0 m0), m0, [], evs. split; [apply Hcc; reflexivity|]. split; [exact H | reflexivity].
    - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [apply Hcc in H; discriminate|]. apply Hcc in H1. injection H1 as -> -> ->. exact H2.
    - intros H. right. exists (vv i0 m0), m0, []. split; [apply Hcc; reflexivity | exact H]. }
  destruct d; cbn in Hk |- *; intros o Ho.
  - apply (E _ _ _ _ _ _ Hc) in Ho. destruct (Hk _ Ho) as (o0 & H & R). exists o0. split; [apply (E _ _ _ _ _ _ Hc'); exact H | exact R].
  - apply (E _ _ _ _ _ _ Hc') in Ho. destruct (Hk _ Ho) as (o0 & H & R). exists o0. split; [apply (E _ _ _ _ _ _ Hc); exact H | exact R].
Qed.

Lemma dir_bind_input {B} : forall (d : bool) (i : SyscallInput) (m : Model) (k k' : SyscallInput -> Sys B),
  DIR d i m (k i) (k' i) -> DIR d i m (bind input k) (bind input k').
Proof. intros. apply (dir_bind_reader d i m input input (fun i0 _ => i0) (fun i0 _ => i0)); [intros; unfold input; reflexivity | intros; unfold input; reflexivity | exact H]. Qed.
Lemma dir_bind_sysno {B} : forall (d : bool) (i : SyscallInput) (m : Model) (k k' : word -> Sys B),
  DIR d i m (k (in_sysno i)) (k' (in_sysno i)) -> DIR d i m (bind sysno k) (bind sysno k').
Proof. intros. apply (dir_bind_reader d i m sysno sysno (fun i0 _ => in_sysno i0) (fun i0 _ => in_sysno i0)); [intros; unfold sysno; reflexivity | intros; unfold sysno; reflexivity | exact H]. Qed.
Lemma dir_bind_arg {B} : forall (d : bool) (i : SyscallInput) (m : Model) n (k k' : word -> Sys B),
  DIR d i m (k (in_arg i n)) (k' (in_arg i n)) -> DIR d i m (bind (arg n) k) (bind (arg n) k').
Proof. intros. apply (dir_bind_reader d i m (arg n) (arg n) (fun i0 _ => in_arg i0 n) (fun i0 _ => in_arg i0 n)); [intros; unfold arg; reflexivity | intros; unfold arg; reflexivity | exact H]. Qed.
Lemma dir_bind_get_fds {B} : forall (d : bool) (i : SyscallInput) (m : Model) (k k' : list (word * FdEntry) -> Sys B),
  DIR d i m (k (m_fds m)) (k' (m_fds m)) -> DIR d i m (bind get_fds k) (bind get_fds k').
Proof. intros. apply (dir_bind_reader d i m get_fds get_fds (fun _ m0 => m_fds m0) (fun _ m0 => m_fds m0)); [intros; unfold get_fds; reflexivity | intros; unfold get_fds; reflexivity | exact H]. Qed.
Lemma dir_bind_get_model' {B} : forall (d : bool) (i : SyscallInput) (m : Model) (k k' : Model -> Sys B),
  DIR d i m (k (relim L m)) (k' m) -> DIR d i m (bind get_model k) (bind get_model k').
Proof. intros. apply (dir_bind_reader d i m get_model get_model (fun _ m0 => m0) (fun _ m0 => m0)); [intros; unfold get_model; reflexivity | intros; unfold get_model; reflexivity | exact H]. Qed.
Lemma dir_bind_get_vmmaps' {B} : forall (d : bool) (i : SyscallInput) (m : Model) (k k' : VmMaps -> Sys B),
  DIR d i m (k (relimV L (m_vmmaps m))) (k' (m_vmmaps m)) -> DIR d i m (bind get_vmmaps k) (bind get_vmmaps k').
Proof. intros. apply (dir_bind_reader d i m get_vmmaps get_vmmaps (fun _ m0 => m_vmmaps m0) (fun _ m0 => m_vmmaps m0)); [intros; unfold get_vmmaps; reflexivity | intros; unfold get_vmmaps; reflexivity | exact H]. Qed.

Lemma dir_bind_choose {A B} : forall (d : bool) (i : SyscallInput) (m : Model) (P P' : A -> Prop) (k k' : A -> Sys B),
  (if d then forall x, P x -> P' x else forall x, P' x -> P x) ->
  (forall x, (if d then P x else P' x) -> DIR d i m (k x) (k' x)) ->
  DIR d i m (bind (choose P) k) (bind (choose P') k').
Proof.
  intros d i m P P' k k' HP Hk.
  assert (E : forall (PP : A -> Prop) (kk : A -> Sys B) i0 m0 o, bind (choose PP) kk i0 m0 o <-> exists x, PP x /\ kk x i0 m0 o).
  { intros PP kk i0 m0 o. unfold bind, choose. destruct o as [y m2 evs|]; split.
    - intros (x0 & m1 & evs1 & evs2 & (x & Px & H1) & H2 & H3). injection H1 as -> -> ->. cbn in H3. subst evs. exists x; split; assumption.
    - intros (x & Px & H). exists x, m0, [], evs. split; [exists x; split; [exact Px|reflexivity]|]. split; [exact H|reflexivity].
    - intros [(x & Px & H) | (x0 & m1 & evs1 & (x & Px & H1) & H2)]; [discriminate|]. injection H1 as -> -> ->. exists x; split; assumption.
    - intros (x & Px & H). right. exists x, m0, []. split; [exists x; split; [exact Px|reflexivity] | exact H]. }
  destruct d; cbn in Hk |- *; intros o Ho.
  - apply E in Ho. destruct Ho as (x & Px & Ho). destruct (Hk x Px _ Ho) as (o0 & H & R). exists o0. split; [apply E; exists x; split; [apply HP; exact Px | exact H] | exact R].
  - apply E in Ho. destruct Ho as (x & Px & Ho). destruct (Hk x Px _ Ho) as (o0 & H & R). exists o0. split; [apply E; exists x; split; [apply HP; exact Px | exact H] | exact R].
Qed.

Lemma dir_bind_choose_same {A B} : forall (d : bool) (i : SyscallInput) (m : Model) (P : A -> Prop) (k k' : A -> Sys B),
  (forall x, P x -> DIR d i m (k x) (k' x)) -> DIR d i m (bind (choose P) k) (bind (choose P) k').
Proof. intros d i m P k k' Hk. apply dir_bind_choose; [destruct d; intros x H; exact H | intros x Hx; apply Hk; destruct d; exact Hx]. Qed.

Lemma dir_bind_emit {B} : forall (d : bool) (i : SyscallInput) (m : Model) e (k k' : unit -> Sys B),
  DIR d i m (k tt) (k' tt) -> DIR d i m (bind (emit e) k) (bind (emit e) k').
Proof.
  intros d i m e k k' Hk.
  assert (E : forall (kk : unit -> Sys B) i0 m0 o, bind (emit e) kk i0 m0 o <->
             match o with Ok y m2 evs => exists evs2, kk tt i0 m0 (Ok y m2 evs2) /\ evs = e ++ evs2 | Unmodeled => kk tt i0 m0 Unmodeled end).
  { intros kk i0 m0 o. unfold bind, emit. destruct o as [y m2 evs|]; split.
    - intros (x0 & m1 & evs1 & evs2 & H1 & H2 & H3). injection H1 as -> -> ->. exists evs2; split; assumption.
    - intros (evs2 & H & ->). exists tt, m0, e, evs2. repeat split; assumption.
    - intros [H | (x0 & m1 & evs1 & H1 & H2)]; [discriminate|]. injection H1 as -> -> ->. exact H2.
    - intros H. right. exists tt, m0, e. split; [reflexivity | exact H]. }
  destruct d; cbn in Hk |- *; intros o Ho; apply E in Ho.
  - destruct o as [y m2 evs|].
    + destruct Ho as (evs2 & Ho & ->). destruct (Hk _ Ho) as ([y0 m0 e0|] & H & R); cbn in R; [|contradiction]. destruct R as (<- & -> & <- & M).
      exists (Ok y m0 (e ++ evs2)). split; [apply E; exists evs2; split; [exact H|reflexivity] | cbn; repeat split; auto].
    + destruct (Hk _ Ho) as ([|] & H & R); cbn in R; [contradiction|]. exists Unmodeled. split; [apply E; exact H | exact I].
  - destruct o as [y m2 evs|].
    + destruct Ho as (evs2 & Ho & ->). destruct (Hk _ Ho) as ([y0 m0 e0|] & H & R); cbn in R; [|contradiction]. destruct R as (-> & -> & -> & M).
      exists (Ok y (relim L m2) (e ++ evs2)). split; [apply E; exists evs2; split; [exact H|reflexivity] | cbn; repeat split; auto].
    + destruct (Hk _ Ho) as ([|] & H & R); cbn in R; [contradiction|]. exists Unmodeled. split; [apply E; exact H | exact I].
Qed.

Lemma dir_table_form {A} : forall (d : bool) (i : SyscallInput) (m : Model) (F F' : SyscallInput -> Sys A),
  DIR d i m (F i) (F' i) -> DIR d i m (fun i0 => F i0 i0) (fun i0 => F' i0 i0).
Proof. intros d i m F F' H. destruct d; exact H. Qed.

End Dir.

Lemma rr_m_fds : forall L m, m_fds (relim L m) = m_fds m. Proof. reflexivity. Qed.
Lemma rr_m_pipes : forall L m, m_pipes (relim L m) = m_pipes m. Proof. reflexivity. Qed.
Lemma rr_m_vm_lazy : forall L m, m_vm_lazy (relim L m) = m_vm_lazy m. Proof. reflexivity. Qed.
Lemma rr_m_vm_materialized : forall L m, m_vm_materialized (relim L m) = m_vm_materialized m. Proof. reflexivity. Qed.
Lemma rr_m_stdin : forall L m, m_stdin (relim L m) = m_stdin m. Proof. reflexivity. Qed.
Lemma rr_m_urandom : forall L m, m_urandom (relim L m) = m_urandom m. Proof. reflexivity. Qed.
Lemma rr_m_net : forall L m, m_net (relim L m) = m_net m. Proof. reflexivity. Qed.
Lemma rr_m_conn_ix : forall L m, m_conn_ix (relim L m) = m_conn_ix m. Proof. reflexivity. Qed.
Lemma rr_m_fs : forall L m, m_fs (relim L m) = m_fs m. Proof. reflexivity. Qed.
Lemma rr_m_halted : forall L m, m_halted (relim L m) = m_halted m. Proof. reflexivity. Qed.
Lemma rr_m_tid : forall L m, m_tid (relim L m) = m_tid m. Proof. reflexivity. Qed.
Lemma rr_m_setsid_succeeded : forall L m, m_setsid_succeeded (relim L m) = m_setsid_succeeded m. Proof. reflexivity. Qed.
Lemma rr_m_has_children : forall L m, m_has_children (relim L m) = m_has_children m. Proof. reflexivity. Qed.
Lemma rr_m_sigaltstack_installed : forall L m, m_sigaltstack_installed (relim L m) = m_sigaltstack_installed m. Proof. reflexivity. Qed.
Lemma rr_m_sigmask : forall L m, m_sigmask (relim L m) = m_sigmask m. Proof. reflexivity. Qed.
Lemma rr_m_killed : forall L m, m_killed (relim L m) = m_killed m. Proof. reflexivity. Qed.
Lemma rr_m_sigabrt_pending : forall L m, m_sigabrt_pending (relim L m) = m_sigabrt_pending m. Proof. reflexivity. Qed.
Lemma rr_m_abort_terminal : forall L m, m_abort_terminal (relim L m) = m_abort_terminal m. Proof. reflexivity. Qed.
Lemma rr_m_utsname : forall L m, m_utsname (relim L m) = m_utsname m. Proof. reflexivity. Qed.
Lemma rr_m_statpins : forall L m, m_statpins (relim L m) = m_statpins m. Proof. reflexivity. Qed.
Lemma rr_m_rlimit_core : forall L m, m_rlimit_core (relim L m) = m_rlimit_core m. Proof. reflexivity. Qed.
Lemma rr_m_nofile : forall L m, m_nofile (relim L m) = m_nofile m. Proof. reflexivity. Qed.
Lemma rr_m_clock : forall L m, m_clock (relim L m) = m_clock m. Proof. reflexivity. Qed.
Lemma rr_m_creds : forall L m, m_creds (relim L m) = m_creds m. Proof. reflexivity. Qed.
Lemma rr_m_fd : forall L m, m_fd (relim L m) = m_fd m. Proof. reflexivity. Qed.
Lemma rr_m_io : forall L m, m_io (relim L m) = m_io m. Proof. reflexivity. Qed.
Lemma rr_m_fsys : forall L m, m_fsys (relim L m) = m_fsys m. Proof. reflexivity. Qed.
Lemma rr_m_proc : forall L m, m_proc (relim L m) = m_proc m. Proof. reflexivity. Qed.
Lemma rr_m_lim : forall L m, m_lim (relim L m) = m_lim m. Proof. reflexivity. Qed.
Lemma rr_m_time : forall L m, m_time (relim L m) = m_time m. Proof. reflexivity. Qed.
Lemma rr_m_vmmaps : forall L m, m_vmmaps (relim L m) = relimV L (m_vmmaps m). Proof. reflexivity. Qed.
Lemma rr_m_vm : forall L m, m_vm (relim L m) = relimS L (m_vm m). Proof. reflexivity. Qed.
Lemma rr_vmst_maps : forall L v, vmst_maps (relimS L v) = relimV L (vmst_maps v). Proof. reflexivity. Qed.
Lemma rr_vmst_lazy : forall L v, vmst_lazy (relimS L v) = vmst_lazy v. Proof. reflexivity. Qed.
Lemma rr_vmst_materialized : forall L v, vmst_materialized (relimS L v) = vmst_materialized v. Proof. reflexivity. Qed.
Lemma rr_vm_reserved : forall L h, vm_reserved (relimV L h) = vm_reserved h. Proof. reflexivity. Qed.
Lemma rr_vm_maps : forall L h, vm_maps (relimV L h) = vm_maps h. Proof. reflexivity. Qed.
Lemma rr_vm_noaccess : forall L h, vm_noaccess (relimV L h) = vm_noaccess h. Proof. reflexivity. Qed.
Lemma rr_vm_start_brk : forall L h, vm_start_brk (relimV L h) = vm_start_brk h. Proof. reflexivity. Qed.
Lemma rr_vm_brk : forall L h, vm_brk (relimV L h) = vm_brk h. Proof. reflexivity. Qed.
Lemma rr_vm_mmap_base : forall L h, vm_mmap_base (relimV L h) = vm_mmap_base h. Proof. reflexivity. Qed.
Lemma rr_vm_init_sp : forall L h, vm_init_sp (relimV L h) = vm_init_sp h. Proof. reflexivity. Qed.
Lemma rr_vm_limit : forall L h, vm_limit (relimV L h) = L. Proof. reflexivity. Qed.
Lemma rr_alloc_top : forall L h, alloc_top (relimV L h) = alloc_top h. Proof. reflexivity. Qed.
Lemma rr_vm_backed_maps : forall L h, vm_backed_maps (relimV L h) = vm_backed_maps h. Proof. reflexivity. Qed.
Lemma rr_vm_backing_used : forall L m, vm_backing_used (relim L m) = vm_backing_used m. Proof. reflexivity. Qed.
#[export] Hint Rewrite rr_m_fds rr_m_pipes rr_m_vm_lazy rr_m_vm_materialized rr_m_stdin rr_m_urandom rr_m_net rr_m_conn_ix rr_m_fs rr_m_halted rr_m_tid rr_m_setsid_succeeded rr_m_has_children rr_m_sigaltstack_installed rr_m_sigmask rr_m_killed rr_m_sigabrt_pending rr_m_abort_terminal rr_m_utsname rr_m_statpins rr_m_rlimit_core rr_m_nofile rr_m_clock rr_m_creds rr_m_fd rr_m_io rr_m_fsys rr_m_proc rr_m_lim rr_m_time rr_m_vmmaps rr_m_vm rr_vmst_maps rr_vmst_lazy rr_vmst_materialized rr_vm_reserved rr_vm_maps rr_vm_noaccess rr_vm_start_brk rr_vm_brk rr_vm_mmap_base rr_vm_init_sp rr_vm_limit rr_alloc_top rr_vm_backed_maps rr_vm_backing_used : relim_rw.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac2 rec lz_head (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => lz_head f
  | _ => c
  end.
Ltac2 lz_unfold_head (c : constr) : unit :=
  let h := lz_head c in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant cst _ =>
      Std.unfold [(Std.ConstRef cst, Std.AllOccurrences)] { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }
  | _ => Control.zero (Tactic_failure (Some (Message.of_string "lz_unfold_head: head is not a constant")))
  end.
Ltac unfold_head c := let tac := ltac2:(c1 |- lz_unfold_head (Option.get (Ltac1.to_constr c1))) in tac c.

Ltac red_proj_in_goal :=
  lazy beta iota zeta delta [relim relimS relimV
    vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp fdst_table fdst_pipes vmst_maps vmst_lazy vmst_materialized
    iost_stdin iost_urandom iost_net iost_conn_ix fsst_image cr_uid cr_euid cr_suid cr_gid cr_egid cr_sgid cr_groups procst_halted procst_tid procst_creds
    procst_setsid_succeeded procst_sigmask procst_children procst_utsname procst_sigaltstack_installed procst_killed procst_sigabrt_pending
    procst_abort_terminal procst_statpins limst_core limst_nofile timest_clock m_fd m_vm m_io m_fsys m_proc m_lim m_time
    m_fds m_pipes m_vmmaps m_vm_lazy m_vm_materialized m_stdin m_urandom m_net m_conn_ix m_fs m_halted m_tid m_setsid_succeeded m_has_children
    m_sigaltstack_installed m_sigmask m_killed m_sigabrt_pending m_abort_terminal m_utsname m_statpins m_rlimit_core m_nofile m_clock m_creds].
Ltac red_proj_in H :=
  lazy beta iota zeta delta [relim relimS relimV
    vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp fdst_table fdst_pipes vmst_maps vmst_lazy vmst_materialized
    iost_stdin iost_urandom iost_net iost_conn_ix fsst_image cr_uid cr_euid cr_suid cr_gid cr_egid cr_sgid cr_groups procst_halted procst_tid procst_creds
    procst_setsid_succeeded procst_sigmask procst_children procst_utsname procst_sigaltstack_installed procst_killed procst_sigabrt_pending
    procst_abort_terminal procst_statpins limst_core limst_nofile timest_clock m_fd m_vm m_io m_fsys m_proc m_lim m_time
    m_fds m_pipes m_vmmaps m_vm_lazy m_vm_materialized m_stdin m_urandom m_net m_conn_ix m_fs m_halted m_tid m_setsid_succeeded m_has_children
    m_sigaltstack_installed m_sigmask m_killed m_sigabrt_pending m_abort_terminal m_utsname m_statpins m_rlimit_core m_nofile m_clock m_creds] in H.

Ltac rw_proj :=
  lazy beta zeta; autorewrite with relim_rw;
  repeat match goal with H : vm_limit (m_vmmaps ?mm) = _ |- context [vm_limit (m_vmmaps ?mm)] => rewrite !H end.

Ltac destruct_model m :=
  first [ match goal with HM : vm_limit (m_vmmaps m) = _ |- _ =>
            destruct m as [?fd [[?vr ?vmp ?vna ?vsb ?vb ?vl ?vmb ?visp] ?vlz ?vmt] ?io ?fsy ?pr ?li ?ti]; red_proj_in HM; subst vl
          | |- _ => destruct m as [?fd [[?vr ?vmp ?vna ?vsb ?vb ?vl ?vmb ?visp] ?vlz ?vmt] ?io ?fsy ?pr ?li ?ti] end;
          red_proj_in_goal ].
Ltac destruct_models := repeat match goal with m : Model |- _ => destruct_model m end.

Ltac model_norm_step :=
  first
    [ progress red_proj_in_goal
    | match goal with |- context [match ?e with _ => _ end] =>
        lazymatch e with
        | match _ with _ => _ end => fail
        | _ => let T := type of e in
               lazymatch eval hnf in T with
               | Model => unfold_head e | VmMaps => unfold_head e | VmState => unfold_head e | FdState => unfold_head e
               | ProcState => unfold_head e | IoState => unfold_head e | LimState => unfold_head e | Creds => unfold_head e
               | _ => destruct e
               end
        end
      end ].
Ltac mok := unfold MOK; destruct_models; repeat first [ reflexivity | assumption | model_norm_step ].
Ltac commute := destruct_models; repeat first [ reflexivity | model_norm_step | lazymatch goal with |- ?l = _ => unfold_head l end ].
Ltac sim_leaf_modify := apply dir_modify; [ commute | mok ].

Ltac sim_destruct e := destruct e.

Ltac sim_scrut e e' :=
  lazymatch e with
  | match ?e2 with _ => _ end =>
      lazymatch e' with
      | match ?e2' with _ => _ end => sim_scrut e2 e2'
      | _ => fail "sim_scrut: shapes differ" e e'
      end
  | _ => first [ constr_eq e e'; sim_destruct e | unfold_head e; rw_proj ]
  end.

Ltac sim_hook := fail.

Ltac sim_step :=
  lazymatch goal with
  | |- DIR _ _ _ _ _ ?c ?c' =>
    first [ sim_hook |
    lazymatch c with
    | bind get_model _ => apply dir_bind_get_model; rw_proj
    | bind get_vmmaps _ => apply dir_bind_get_vmmaps'; rw_proj
    | bind get_fds _ => apply dir_bind_get_fds; rw_proj
    | bind input _ => apply dir_bind_input
    | bind sysno _ => apply dir_bind_sysno
    | bind (arg _) _ => apply dir_bind_arg
    | bind (emit _) _ => apply dir_bind_emit
    | bind (choose _) _ => first [ apply dir_bind_choose_same; intros ? ? | apply dir_bind_choose; [ | intros ? ?] ]
    | bind _ _ => apply dir_bind; [ | let x := fresh "x" in let m1 := fresh "m" in let HM1 := fresh "HM" in intros x m1 HM1; unfold MOK in HM1 ]
    | alt _ _ => apply dir_alt
    | pure _ => apply dir_pure; [ reflexivity | mok ]
    | unmodeled => apply dir_unmodeled
    | emit _ => apply dir_emit; mok
    | modify _ => sim_leaf_modify
    | choose _ => first [ apply dir_choose_same; mok | apply dir_choose; [ | mok ] ]
    | input => apply dir_input; mok
    | sysno => apply dir_sysno; mok
    | arg _ => apply dir_arg; mok
    | get_fds => apply dir_get_fds; mok
    | match ?e with _ => _ end =>
        lazymatch c' with
        | match ?e' with _ => _ end => sim_scrut e e'
        | _ => fail "sim: match vs non-match" c c'
        end
    | _ => unfold_head c; rw_proj
    end ]
  end.

Ltac sim := repeat sim_step.

Ltac sim_arm m HM := unfold MOK in HM; lazy beta zeta; sim.
