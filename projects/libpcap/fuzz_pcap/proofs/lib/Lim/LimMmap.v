(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimMmap.v at commit 874e3397a35, with its module paths changed to libpcap/fuzz_pcap. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lim Require Import LimBase LimMm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

(* [comment removed for export] *)
Ltac norm_setL :=
  repeat match goal with
  | |- context [m_vmmaps (setL ?L ?m)] => change (m_vmmaps (setL L m)) with (setvl L (m_vmmaps m))
  | |- context [alloc_top (setvl ?L ?h)] => change (alloc_top (setvl L h)) with (alloc_top h)
  | |- context [vm_reserved (setvl ?L ?h)] => change (vm_reserved (setvl L h)) with (vm_reserved h)
  | |- context [vm_maps (setvl ?L ?h)] => change (vm_maps (setvl L h)) with (vm_maps h)
  | |- context [vm_noaccess (setvl ?L ?h)] => change (vm_noaccess (setvl L h)) with (vm_noaccess h)
  | |- context [vm_start_brk (setvl ?L ?h)] => change (vm_start_brk (setvl L h)) with (vm_start_brk h)
  | |- context [vm_brk (setvl ?L ?h)] => change (vm_brk (setvl L h)) with (vm_brk h)
  | |- context [vm_mmap_base (setvl ?L ?h)] => change (vm_mmap_base (setvl L h)) with (vm_mmap_base h)
  | |- context [vm_init_sp (setvl ?L ?h)] => change (vm_init_sp (setvl L h)) with (vm_init_sp h)
  | |- context [vm_limit (setvl ?L ?h)] => change (vm_limit (setvl L h)) with L
  end.

Ltac at_mod_side :=
  cbv beta;
  first [ reflexivity
        | cbv beta delta [with_mmap_replacement with_mmap_backing with_mmap_destroyed];
          repeat match goal with |- context [if ?b then _ else _] => destruct b end;
          reflexivity ].
Ltac at_choose_side :=
  let x := fresh "x" in let H := fresh "H" in
  intros x H;
  first [ exact H
        | repeat match type of H with _ /\ _ => let H1 := fresh "H" in destruct H as [H1 H] end;
          repeat split; first [assumption | eassumption] ].
Lemma errno_from_inv es i m x m1 evs : errno_from es i m (Ok x m1 evs) -> List.In x es /\ m1 = m /\ evs = [].
Proof. exact (choose_inv (fun e => List.In e es) i m x m1 evs). Qed.
Ltac at_step :=
  cbv beta zeta;
  lazymatch goal with
  | |- lim_at _ _ _ (if ?b1 then _ else _) (if ?b2 then _ else _) =>
        change b2 with b1; destruct b1
  | |- lim_at _ _ _ (alt _ _) (alt _ _) => apply at_alt
  | |- lim_at _ _ _ (bind get_model _) (bind get_model _) => apply at_get_model; cbv beta zeta; norm_setL
  | |- lim_at _ _ _ (bind (errno_from _) (fun e => err_ret e)) _ => apply at_blind; apply blind_errno_alt
  | |- lim_at _ _ _ (bind (errno_from _) _) (bind (errno_from _) _) =>
        apply at_bind; [apply at_blind; apply blind_errno_from
                       | let H := fresh "Hc" in let Hm := fresh "Hm" in let He := fresh "He" in let m1 := fresh "m1" in let ev := fresh "ev" in intros ? m1 ev H; apply errno_from_inv in H; destruct H as (? & Hm & He); subst m1 ev]
  | |- lim_at _ _ _ (bind (choose _) _) (bind (choose _) _) =>
        apply at_bind; [apply at_choose; at_choose_side
                       | let H := fresh "Hc" in let Hm := fresh "Hm" in let He := fresh "He" in let m1 := fresh "m1" in let ev := fresh "ev" in intros ? m1 ev H; apply choose_inv in H; destruct H as (? & Hm & He); subst m1 ev]
  | |- lim_at _ _ _ (bind (modify _) _) (bind (modify _) _) =>
        apply at_bind; [apply at_modify; at_mod_side | intros [] ? ? _]
  | |- lim_at _ _ _ _ _ => at_leaf
  end.
Ltac at_auto := repeat at_step.

Lemma mmap_noreserve_backed_ok_setL : forall L flags m nZ,
  mmap_noreserve_backed_ok flags (setL L m) nZ = (if mmap_noreserve_b flags then true else (vm_backing_used m + nZ <=? L)%Z).
Proof. reflexivity. Qed.

Lemma mmap_at : forall L i m addr len prot flags fd off,
  mmap_budget_refused_b addr len prot flags fd off m = false ->
  mmap_budget_refused_b addr len prot flags fd off (setL L m) = false ->
  lim_at L i m (mmap_spec addr len prot flags fd off) (mmap_spec addr len prot flags fd off).
Proof.
  intros L i m addr len prot flags fd off R1 R2.
  unfold mmap_spec, mmap_budget_refused_b in *. cbv zeta in *.
  revert R1 R2. norm_setL.
  set (nZ := page_round_up_Z (bv_unsigned len)). set (n := Z_to_bv 64 nZ). set (h := m_vmmaps m).
  destruct (negb (mmap_off_aligned_b off)); [intros _ _; at_auto|].
  destruct (negb (mmap_anon_b flags)); [intros _ _; at_auto|].
  destruct (w_is0 len); [intros _ _; at_auto|].
  destruct (mmap_modeled_b prot flags off).
  { intros R1 R2. apply negb_false_iff in R1, R2. at_auto. }
  destruct (mmap_noaccess_b prot flags off); [intros _ _; at_auto|].
  destruct (mmap_fixed_noaccess_b prot flags off); [intros _ _; at_auto|].
  destruct (mmap_fixed_rw_b prot flags off).
  { destruct (two_pow_64 <=? bv_unsigned addr + nZ)%Z; [intros _ _; at_auto|].
    intros R1 R2. apply at_get_model. cbv beta zeta. norm_setL. fold h. revert R1 R2.
    destruct (negb (bv_unsigned addr + nZ <=? alloc_top h)%Z); [intros _ _; at_auto|].
    destruct (negb (bv_unsigned addr mod page_size =? 0)%Z); [intros _ _; at_auto|].
    destruct (negb (0 <? bv_unsigned addr)%Z); [intros _ _; at_auto|].
    destruct (region_free (vm_reserved h) addr n && map_contains (vm_maps h) addr n).
    { intros R1 R2. apply negb_false_iff in R1, R2. at_auto. }
    destruct (region_free (vm_reserved h ++ vm_maps h) addr n).
    { intros R1 R2. apply negb_false_iff in R1, R2. at_auto. }
    destruct (region_free (vm_reserved h) addr n).
    { intros R1 R2. apply negb_false_iff in R1, R2. at_auto. }
    intros _ _. at_auto. }
  destruct (mmap_noreplace_noaccess_b prot flags off); [intros _ _; at_auto|].
  destruct (mmap_noreplace_rw_b prot flags off).
  { destruct (two_pow_64 <=? bv_unsigned addr + nZ)%Z; [intros _ _; at_auto|].
    intros R1 R2. apply at_get_model. cbv beta zeta. norm_setL. fold h. revert R1 R2.
    destruct (negb (bv_unsigned addr + nZ <=? alloc_top h)%Z); [intros _ _; at_auto|].
    destruct (negb (bv_unsigned addr mod page_size =? 0)%Z); [intros _ _; at_auto|].
    destruct (negb (0 <? bv_unsigned addr)%Z); [intros _ _; at_auto|].
    destruct (region_free (vm_reserved h ++ vm_maps h) addr n).
    { intros R1 R2. apply negb_false_iff in R1, R2. at_auto. }
    intros _ _. at_auto. }
  intros _ _. at_auto.
Qed.
