(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11-05: copied whole from projects/cgif/cgif_rgb_fuzzer/proofs/lib/LimSimMm.v at theorem-labs/oss-verify-proofs@c5665593c2d8, with
   every occurrence of the module path OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib replaced by
   OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus and that file lead comment replaced by this line; no other change. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the brk budget reads brk_grow_bytes, which brk_budget_ok_mono unfolds, and the mremap grow is simulated through its one budget gate: mremap_grow_marks takes the TASK_SIZE gate as a premise and gives each budget fact under the answer of the room test mremap_inplace_room_b that makes the mark read it, and sim_mremap proves its room and move side conditions with mremap_prep, a tactic this file adds, so dir_fwd_alt_r, dir_bwd_alt_r, mremap_inplace_grow_b_mono and the mremap sim_hook, which nothing here uses, are removed, this file's own comments explain the brk and mremap changes in place of the source's comment above mremap_grow_marks and its three comments in the proof of sim_mremap, and the cited source commit is named by its public id. *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus Require Import LimSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope. Open Scope bv_scope. Open Scope sys_scope.
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Ltac sim_destruct e ::= destruct e eqn:?.

Section Mm.
Variable L0 L : Z.
Hypothesis HLE : L <= L0.

Lemma within_limit_mono : forall m, vm_limit (m_vmmaps m) = L0 ->
  vm_backing_within_limit (relim L m) = true -> vm_backing_within_limit m = true.
Proof.
  intros m HM. unfold vm_backing_within_limit. rewrite rr_vm_backing_used, rr_m_vmmaps, rr_vm_limit, HM.
  intros H. apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.


(* [comment removed for export] *)
Ltac crunch_guard G :=
  autorewrite with relim_rw in G; lazy beta zeta in G;
  repeat match goal with
         | H : ?x = true |- _ => lazymatch x with true => fail | _ => rewrite H in G end
         | H : ?x = false |- _ => tryif constr_eq H G then fail else (lazymatch x with false => fail | _ => rewrite H in G end)
         | H : ?x = Some _ |- _ => rewrite H in G
         | H : ?x = None |- _ => lazymatch x with None => fail | _ => rewrite H in G end
         end;
  lazy beta iota zeta in G.

(* [comment removed for export] *)
Lemma mprotect_model_next_relim : forall m a n, mprotect_model_next (relim L m) a n = relim L (mprotect_model_next m a n).
Proof. intros m a n. unfold mprotect_model_next. commute. Qed.

Lemma mprotect_budget_ok_relim : forall m a n, vm_limit (m_vmmaps m) = L0 ->
  mprotect_budget_ok (relim L m) a n = true -> mprotect_budget_ok m a n = true.
Proof.
  intros m a n HM. unfold mprotect_budget_ok. rewrite mprotect_model_next_relim. apply within_limit_mono.
  unfold mprotect_model_next. mok.
Qed.

Lemma sim_mprotect : forall (d : bool) i m, MOK L0 m ->
  (d = false -> mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (relim L m) = false) ->
  DIR L0 L d i m (mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) (mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)).
Proof.
  intros d i m HM GD. sim_arm m HM.
  destruct d.
  - intros _ H. exact (mprotect_budget_ok_relim _ _ _ HM H).
  - specialize (GD eq_refl). intros _ H.
    destruct (mprotect_budget_ok (relim L m) (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))) eqn:E; [reflexivity| exfalso].
    unfold mprotect_budget_refused_b in GD. crunch_guard GD.
    discriminate GD.
Qed.
(* [comment removed for export] *)
Lemma forget_vm_ranges_relim : forall rs m, forget_vm_ranges rs (relim L m) = relim L (forget_vm_ranges rs m).
Proof. induction rs as [|[a n] rs IH]; intros m; [reflexivity|]. cbn [forget_vm_ranges]. rewrite <- IH. reflexivity. Qed.
Lemma forget_vm_ranges_limit : forall rs m, vm_limit (m_vmmaps (forget_vm_ranges rs m)) = vm_limit (m_vmmaps m).
Proof. induction rs as [|[a n] rs IH]; intros m; [reflexivity|]. cbn [forget_vm_ranges]. rewrite IH. reflexivity. Qed.
Lemma with_brk_next_relim : forall m req r, with_brk_next (relim L m) req r = relim L (with_brk_next m req r).
Proof. intros. unfold with_brk_next. rewrite <- forget_vm_ranges_relim. reflexivity. Qed.
Lemma with_brk_next_limit : forall m req r, vm_limit (m_vmmaps (with_brk_next m req r)) = vm_limit (m_vmmaps m).
Proof. intros. unfold with_brk_next. rewrite forget_vm_ranges_limit. reflexivity. Qed.

Lemma brk_budget_ok_mono : forall m r, vm_limit (m_vmmaps m) = L0 -> brk_budget_ok (relim L m) r = true -> brk_budget_ok m r = true.
Proof.
  (* LPS 08b1429: [brk_budget_ok] reads the grant through [brk_grow_bytes h r]
     ([c0dd863a:theories/LinuxProcessSem/Sys/Mm/Mmap.v:372]), which hides the [vm_brk] the rewrite below names; unfold it. *)
  intros m r HM. unfold brk_budget_ok, brk_grow_bytes. rewrite rr_vm_backing_used, rr_m_vmmaps, rr_vm_limit, rr_vm_brk, HM.
  intros H. apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.

Lemma brk_r_ok_fwd : forall m req r, vm_limit (m_vmmaps m) = L0 -> brk_r_ok (relim L m) req r = true -> brk_r_ok m req r = true.
Proof.
  intros m req r HM. unfold brk_r_ok, brk_grow_ok, min_brk. autorewrite with relim_rw.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (vm_start_brk (m_vmmaps m))))%bool; [intros H; exact H|].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m))); [intros H; exact H|].
  destruct ((0 <? bv_unsigned (vm_brk (m_vmmaps m))) && (bv_unsigned (vm_brk (m_vmmaps m)) <? bv_unsigned r))%bool; [|intros H; exact H].
  rewrite !andb_true_iff. intros (H1 & H2 & H3). repeat split; try assumption. exact (brk_budget_ok_mono _ _ HM H3).
Qed.

Lemma brk_r_ok_bwd : forall m req r, vm_limit (m_vmmaps m) = L0 -> brk_budget_refused_b (relim L m) req = false ->
  brk_r_ok m req r = true -> brk_r_ok (relim L m) req r = true.
Proof.
  intros m req r HM GD. unfold brk_r_ok, brk_grow_ok, min_brk. unfold brk_budget_refused_b, min_brk in GD. autorewrite with relim_rw in GD. autorewrite with relim_rw.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (vm_start_brk (m_vmmaps m))))%bool eqn:E1; [intros H; exact H|]. cbn [negb andb] in GD.
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m))) eqn:E2; [intros H; exact H|].
  destruct ((0 <? bv_unsigned (vm_brk (m_vmmaps m))) && (bv_unsigned (vm_brk (m_vmmaps m)) <? bv_unsigned r))%bool eqn:E3; [|intros H; exact H].
  rewrite !andb_true_iff. intros (H1 & H2 & H3). repeat split; try assumption.
  (* [comment removed for export] *)
  apply andb_true_iff in E3. destruct E3 as [E3a E3b]. rewrite E3a in GD. cbn [andb] in GD.
  apply orb_true_iff in H1.
  destruct H1 as [H1|H1]; [apply bv_eqb_eq in H1; subst r | apply bv_eqb_eq in H1; subst r; rewrite Z.ltb_irrefl in E3b; discriminate].
  rewrite E3b in GD; cbn [andb] in GD; destruct (brk_budget_ok (relim L m) req); [reflexivity | discriminate].
Qed.

Lemma sim_brk : forall (d : bool) i m, MOK L0 m ->
  (d = false -> brk_budget_refused_b (relim L m) (in_arg i 0) = false) ->
  DIR L0 L d i m (brk_spec (in_arg i 0)) (brk_spec (in_arg i 0)).
Proof.
  intros d i m HM GD. unfold MOK in HM. unfold brk_spec.
  apply dir_bind_get_model; rw_proj.
  apply dir_bind_choose.
  { destruct d; intros x; [apply brk_r_ok_fwd; exact HM | apply brk_r_ok_bwd; [exact HM | exact (GD eq_refl)]]. }
  intros x Hx. apply dir_bind.
  { apply dir_modify; [apply with_brk_next_relim | unfold MOK; rewrite with_brk_next_limit; exact HM]. }
  intros u m1 HM1. apply dir_pure; [reflexivity | exact HM1].
Qed.

(* [comment removed for export] *)
Lemma vm_forget_range_relim : forall lo hi m, vm_forget_range lo hi (relim L m) = relim L (vm_forget_range lo hi m).
Proof. reflexivity. Qed.
Lemma vm_add_lazy_relim : forall a n m, vm_add_lazy a n (relim L m) = relim L (vm_add_lazy a n m).
Proof. reflexivity. Qed.
Lemma with_mmap_backing_relim : forall f a n m, with_mmap_backing f a n (relim L m) = relim L (with_mmap_backing f a n m).
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b f); reflexivity. Qed.
Lemma with_mmap_replacement_relim : forall f a n m, with_mmap_replacement f a n (relim L m) = relim L (with_mmap_replacement f a n m).
Proof. intros. unfold with_mmap_replacement. rewrite vm_forget_range_relim. apply with_mmap_backing_relim. Qed.
Lemma with_vmmaps_relim : forall h m, with_vmmaps (relimV L h) (relim L m) = relim L (with_vmmaps h m).
Proof. reflexivity. Qed.
Lemma mmap_fixed_rw_next_relim : forall h a n, mmap_fixed_rw_next (relimV L h) a n = relimV L (mmap_fixed_rw_next h a n).
Proof. reflexivity. Qed.
Lemma mmap_fixed_rw_span_next_relim : forall h a n, mmap_fixed_rw_span_next (relimV L h) a n = relimV L (mmap_fixed_rw_span_next h a n).
Proof. reflexivity. Qed.
Lemma with_mmap_backing_limit : forall f a n m, vm_limit (m_vmmaps (with_mmap_backing f a n m)) = vm_limit (m_vmmaps m).
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b f); reflexivity. Qed.
Lemma with_mmap_replacement_limit : forall f a n m, vm_limit (m_vmmaps (with_mmap_replacement f a n m)) = vm_limit (m_vmmaps m).
Proof. intros. unfold with_mmap_replacement. rewrite with_mmap_backing_limit. reflexivity. Qed.

Lemma mmap_noreserve_backed_ok_mono : forall f m nZ, vm_limit (m_vmmaps m) = L0 ->
  mmap_noreserve_backed_ok f (relim L m) nZ = true -> mmap_noreserve_backed_ok f m nZ = true.
Proof.
  intros f m nZ HM. unfold mmap_noreserve_backed_ok. rewrite rr_vm_backing_used, rr_m_vmmaps, rr_vm_limit, HM.
  destruct (mmap_noreserve_b f); [intros H; exact H|]. intros H. apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.
Lemma mmap_fixed_rw_budget_ok_mono : forall f m a n, vm_limit (m_vmmaps m) = L0 ->
  mmap_fixed_rw_budget_ok f (relim L m) a n = true -> mmap_fixed_rw_budget_ok f m a n = true.
Proof.
  intros f m a n HM. unfold mmap_fixed_rw_budget_ok. rewrite rr_m_vmmaps, mmap_fixed_rw_next_relim, with_vmmaps_relim, with_mmap_replacement_relim.
  apply within_limit_mono. rewrite with_mmap_replacement_limit. exact HM.
Qed.
Lemma mmap_fixed_rw_span_budget_ok_mono : forall f m a n, vm_limit (m_vmmaps m) = L0 ->
  mmap_fixed_rw_span_budget_ok f (relim L m) a n = true -> mmap_fixed_rw_span_budget_ok f m a n = true.
Proof.
  intros f m a n HM. unfold mmap_fixed_rw_span_budget_ok. rewrite rr_m_vmmaps, mmap_fixed_rw_span_next_relim, with_vmmaps_relim, with_mmap_replacement_relim.
  apply within_limit_mono. rewrite with_mmap_replacement_limit. exact HM.
Qed.

(* [comment removed for export] *)
Ltac gate_fwd mono HM := intros ? Hx; repeat match type of Hx with _ /\ _ => destruct Hx as [? Hx] end; repeat split; try assumption; exact (mono Hx) || (eapply mono; [exact HM | exact Hx]).
Ltac gate_bwd GD mark := intros ? Hx; repeat match type of Hx with _ /\ _ => destruct Hx as [? Hx] end; repeat split; try assumption;
  lazymatch goal with |- ?g = true => destruct g eqn:?; [reflexivity | exfalso; unfold mark in GD; crunch_guard GD; try discriminate GD] end.

Lemma sim_mmap : forall (d : bool) i m, MOK L0 m ->
  (d = false -> mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) (relim L m) = false) ->
  DIR L0 L d i m (mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))
                 (mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)).
Proof.
  intros d i m HM GD. sim_arm m HM.
  all: destruct d; [ first [ gate_fwd (mmap_noreserve_backed_ok_mono (in_arg i 3) m) HM
                           | gate_fwd (mmap_fixed_rw_budget_ok_mono (in_arg i 3) m) HM
                           | gate_fwd (mmap_fixed_rw_span_budget_ok_mono (in_arg i 3) m) HM ]
                   | specialize (GD eq_refl); gate_bwd GD mmap_budget_refused_b ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MV_OK (m : Model) : Prop :=
  forall old old_size new_size dst : word,
    let h := m_vmmaps m in
    let old_nZ := page_round_up_Z (bv_unsigned old_size) in
    let new_nZ := page_round_up_Z (bv_unsigned new_size) in
    let old_n := Z_to_bv 64 old_nZ in
    let new_n := Z_to_bv 64 new_nZ in
    (mremap_source_b h old old_n old_nZ && mremap_backing_uniform_b m old old_n)%bool = true ->
    (old_nZ < new_nZ)%Z ->
    negb (bv_eqb dst old) = true -> (bv_unsigned dst mod page_size = 0)%Z -> (0 < bv_unsigned dst)%Z ->
    (bv_unsigned dst + new_nZ <= alloc_top h)%Z -> region_free (vm_reserved h ++ vm_maps h) dst new_n = true ->
    (vm_backing_used (mremap_model_next m old old_n dst new_n) <= mremap_move_charge m old old_n new_n)%Z.

Lemma mremap_model_next_relim : forall m old old_n dst new_n,
  mremap_model_next (relim L m) old old_n dst new_n = relim L (mremap_model_next m old old_n dst new_n).
Proof. intros. reflexivity. Qed.
Lemma mremap_model_next_limit : forall m old old_n dst new_n,
  vm_limit (m_vmmaps (mremap_model_next m old old_n dst new_n)) = vm_limit (m_vmmaps m).
Proof. intros. reflexivity. Qed.
Lemma mremap_move_charge_relim : forall m old old_n new_n,
  mremap_move_charge (relim L m) old old_n new_n = mremap_move_charge m old old_n new_n.
Proof. intros. reflexivity. Qed.
Lemma mremap_final_budget_b_mono : forall m old old_n dst new_n, vm_limit (m_vmmaps m) = L0 ->
  mremap_final_budget_b (relim L m) old old_n dst new_n = true -> mremap_final_budget_b m old old_n dst new_n = true.
Proof.
  intros m old old_n dst new_n HM. unfold mremap_final_budget_b. rewrite mremap_model_next_relim. apply within_limit_mono.
  rewrite mremap_model_next_limit. exact HM.
Qed.
Lemma mremap_fresh_b_mono : forall m oz nz old old_n dst new_n, vm_limit (m_vmmaps m) = L0 ->
  mremap_fresh_b (relim L m) oz nz old old_n dst new_n = true -> mremap_fresh_b m oz nz old old_n dst new_n = true.
Proof.
  intros m oz nz old old_n dst new_n HM. unfold mremap_fresh_b. autorewrite with relim_rw.
  rewrite !andb_true_iff. intros (((((H1 & H2) & H3) & H4) & H5) & H6). repeat split; try assumption. exact (mremap_final_budget_b_mono _ _ _ _ _ HM H6).
Qed.

(* LPS 75d69e00: a grow has ONE resolution chosen by the room test ([mremap_inplace_room_b],
   [c0dd863a:theories/LinuxProcessSem/Sys/Mm/Mremap.v:320]), and the mremap budget mark reads that
   resolution's gate only ([c0dd863a:theories/LinuxProcessSem/Sys/Mm/Mremap.v:1016]): with room,
   [negb (final budget in place)]; without room, [negb (mremap_move_budget_b ..)]. A [TASK_SIZE]
   gate precedes the old-size gate. So this lemma returns each fact under the room answer that
   makes the mark read it (with room, the move's charge is unconstrained by the mark).
   Its only consumer is [sim_mremap] below. *)
Lemma mremap_grow_marks : forall m old old_size new_size flags,
  mremap_budget_refused_b old old_size new_size flags (relim L m) = false ->
  negb (bv_unsigned flags =? MREMAP_MAYMOVE) = false ->
  negb (bv_unsigned old mod page_size =? 0) = false ->
  page_align_is0_b new_size = false ->
  (TASK_SIZE <? page_round_up_Z (bv_unsigned new_size)) = false ->
  page_align_is0_b old_size = false ->
  (mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (page_round_up_Z (bv_unsigned old_size))
   && mremap_backing_uniform_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))%bool = true ->
  (page_round_up_Z (bv_unsigned new_size) <=? page_round_up_Z (bv_unsigned old_size)) = false ->
  (mremap_inplace_room_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
     (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) = true ->
   mremap_final_budget_b (relim L m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = true)
  /\ (mremap_inplace_room_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
        (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) = false ->
      mremap_move_charge m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) <= L).
Proof.
  intros m old old_size new_size flags GD E1 E2 E3 ET E4 E5 E6.
  unfold mremap_budget_refused_b in GD. rewrite E1, E2, E3, ET, E4 in GD. lazy zeta in GD.
  replace (mremap_source_b (m_vmmaps (relim L m))) with (mremap_source_b (m_vmmaps m)) in GD by reflexivity.
  replace (mremap_backing_uniform_b (relim L m)) with (mremap_backing_uniform_b m) in GD by reflexivity.
  rewrite E5 in GD. cbn [negb] in GD. rewrite E6 in GD.
  replace (mremap_inplace_room_b (relim L m)) with (mremap_inplace_room_b m) in GD by reflexivity.
  split; intros RM; rewrite RM in GD; apply negb_false_iff in GD; [exact GD|].
  unfold mremap_move_budget_b in GD. rewrite mremap_move_charge_relim, rr_m_vmmaps, rr_vm_limit in GD. apply Z.leb_le in GD. exact GD.
Qed.

(* The gate facts [sim_mremap]'s two side conditions need, gathered from the hypotheses [sim]
   destructed. A tactic over [i]/[m] rather than an [all:] block: under [all:] a pattern naming
   [i] is interned with no goal context and rejected. *)
Ltac mremap_prep i m :=
  lazymatch goal with FL : negb (bv_unsigned (in_arg i 3) =? MREMAP_MAYMOVE) = false |- _ =>
  lazymatch goal with AL : negb (bv_unsigned (in_arg i 0) mod page_size =? 0) = false |- _ =>
  lazymatch goal with NZ : page_align_is0_b (in_arg i 2) = false |- _ =>
  lazymatch goal with TS : (TASK_SIZE <? page_round_up_Z (bv_unsigned (in_arg i 2))) = false |- _ =>
  lazymatch goal with OZ : page_align_is0_b (in_arg i 1) = false |- _ =>
  lazymatch goal with SRC : context [map_has _ _ _] |- _ =>
  lazymatch goal with UNI : context [map_contains (m_vm_lazy m) _ _] |- _ =>
  lazymatch goal with NEQ : (page_round_up_Z (bv_unsigned (in_arg i 1)) =? page_round_up_Z (bv_unsigned (in_arg i 2))) = false |- _ =>
  lazymatch goal with NLT : (page_round_up_Z (bv_unsigned (in_arg i 2)) <? page_round_up_Z (bv_unsigned (in_arg i 1))) = false |- _ =>
  assert (SU : (mremap_source_b (m_vmmaps m) (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) (page_round_up_Z (bv_unsigned (in_arg i 1)))
                && mremap_backing_uniform_b m (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))))%bool = true)
    by (unfold mremap_source_b, mremap_backing_uniform_b; rewrite SRC; exact UNI);
  assert (NLE : (page_round_up_Z (bv_unsigned (in_arg i 2)) <=? page_round_up_Z (bv_unsigned (in_arg i 1))) = false)
    by (apply Z.leb_gt; apply Z.eqb_neq in NEQ; apply Z.ltb_ge in NLT; lia);
  assert (LT : (page_round_up_Z (bv_unsigned (in_arg i 1)) < page_round_up_Z (bv_unsigned (in_arg i 2)))%Z)
    by (apply Z.eqb_neq in NEQ; apply Z.ltb_ge in NLT; lia);
  pose proof FL as gFL; pose proof AL as gAL; pose proof NZ as gNZ; pose proof TS as gTS; pose proof OZ as gOZ;
  clear SRC UNI
  end end end end end end end end end.

Lemma sim_mremap : forall (d : bool) i m, MOK L0 m -> (d = false -> MV_OK m) ->
  (d = false -> mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (relim L m) = false) ->
  DIR L0 L d i m (mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof.
  intros d i m HM MV GD. sim_arm m HM.
  (* LPS 75d69e00: the grow is [if room then (choose budget ;; in place) else (dst <- choose
     (mremap_dst_ok ..) ;; move)], so [sim] runs to the end and leaves exactly two
     [dir_bind_choose] side conditions: the in-place budget (room = true) and the move
     destination (room = false). *)
  - (* room = true: the in-place budget gate. Forward is monotonicity; backward is the mark. *)
    mremap_prep i m.
    destruct d; intros _ H.
    + exact (mremap_final_budget_b_mono _ _ _ _ _ HM H).
    + specialize (GD eq_refl).
      assert (RM : mremap_inplace_room_b m (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))
                     (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 2))))
                     (page_round_up_Z (bv_unsigned (in_arg i 1))) (page_round_up_Z (bv_unsigned (in_arg i 2))) = true)
        by assumption.
      exact (proj1 (mremap_grow_marks m (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) GD gFL gAL gNZ gTS gOZ SU NLE) RM).
  - (* room = false: the move destination. Its [linux_place] half reads only limit-free ledger
       fields and [m_kernel], so it is the same proposition on both sides by conversion; the
       [mremap_fresh_b] half is monotonicity forward and [MV_OK] plus the mark backward. *)
    mremap_prep i m.
    destruct d; intros x [Hpl Hfr]; split; [exact Hpl | | exact Hpl | ].
    + exact (mremap_fresh_b_mono _ _ _ _ _ _ _ HM Hfr).
    + specialize (GD eq_refl). specialize (MV eq_refl).
      assert (RM : mremap_inplace_room_b m (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))
                     (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 2))))
                     (page_round_up_Z (bv_unsigned (in_arg i 1))) (page_round_up_Z (bv_unsigned (in_arg i 2))) = false)
        by assumption.
      pose proof (proj2 (mremap_grow_marks m (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) GD gFL gAL gNZ gTS gOZ SU NLE) RM) as GM.
      unfold mremap_fresh_b in Hfr |- *. autorewrite with relim_rw.
      rewrite !andb_true_iff in Hfr. destruct Hfr as (((((H1 & H2) & H3) & H4) & H5) & H6).
      rewrite H1, H2, H3, H4, H5. cbn [andb].
      unfold mremap_final_budget_b, vm_backing_within_limit. rewrite mremap_model_next_relim, rr_vm_backing_used, rr_m_vmmaps, rr_vm_limit.
      apply Z.leb_le. etransitivity; [|exact GM].
      apply (MV (in_arg i 0) (in_arg i 1) (in_arg i 2) x SU LT); try assumption.
      * apply Z.eqb_eq in H2. exact H2.
      * apply Z.ltb_lt in H3. exact H3.
      * apply Z.leb_le in H4. exact H4.
Qed.
End Mm.
