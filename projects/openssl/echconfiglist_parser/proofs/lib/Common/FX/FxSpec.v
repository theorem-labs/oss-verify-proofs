(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector bitvector.tactics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition aoff (a : word) (j : nat) : word := bv_add a (Z_to_bv 64 (Z.of_nat j)).

Lemma aoff_0 : forall a, aoff a 0 = a.
Proof. intros. unfold aoff. bv_solve. Qed.

Lemma aoff_S : forall a j, aoff (a + 1)%bv j = aoff a (S j).
Proof. intros. unfold aoff. bv_solve. Qed.

Lemma aoff_inj : forall a i j, (Z.of_nat i < 2^64) -> (Z.of_nat j < 2^64) -> aoff a i = aoff a j -> i = j.
Proof.
  intros a i j Hi Hj H. unfold aoff in H.
  apply (f_equal bv_unsigned) in H. rewrite !bv_add_unsigned in H.
  rewrite !Z_to_bv_small in H by (unfold bv_modulus; lia).
  unfold bv_wrap in H. change (bv_modulus 64) with (2^64) in H.
  pose proof (bv_unsigned_in_range _ a) as Ha. change (bv_modulus 64) with (2^64) in Ha.
  assert (Z.of_nat i = Z.of_nat j); [|lia].
  assert (E : (bv_unsigned a + Z.of_nat i - (bv_unsigned a + Z.of_nat j)) mod 2^64 = 0).
  { rewrite Zminus_mod, H, Z.sub_diag. reflexivity. }
  replace (bv_unsigned a + Z.of_nat i - (bv_unsigned a + Z.of_nat j)) with (Z.of_nat i - Z.of_nat j) in E by lia.
  apply Z.mod_divide in E; [|lia]. destruct E as [k Hk].
  assert (k = 0) by nia. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition rview (m : word -> option byte) (a : word) : option byte :=
  match m a with
  | Some b => Some b
  | None => match memory_read segs a 1 with
            | Some (b :: _) => Some b
            | _ => None
            end
  end.

Lemma ov_read_bytes_intro : forall n m a bs,
  length bs = n ->
  (forall j, (j < n)%nat -> rview m (aoff a j) = nth_error bs j) ->
  ov_read_bytes segs m a n = Some bs.
Proof.
  induction n as [|n IH]; intros m a bs Hlen H.
  - destruct bs; [reflexivity | discriminate].
  - destruct bs as [|b bs]; [discriminate|]. cbn [ov_read_bytes].
    pose proof (H 0%nat ltac:(lia)) as H0. cbn [nth_error] in H0. rewrite aoff_0 in H0.
    unfold rview in H0. rewrite H0.
    rewrite (IH m (a + 1)%bv bs); [reflexivity | cbn in Hlen; lia |].
    intros j Hj. specialize (H (S j) ltac:(lia)). cbn [nth_error] in H. rewrite <- H.
    f_equal. apply aoff_S.
Qed.

Lemma store_ok_intro : forall n m a,
  (forall j, (j < n)%nat -> wview segs m (aoff a j) <> None) ->
  store_ok segs m a n = true.
Proof.
  induction n as [|n IH]; intros m a H; [reflexivity|]. cbn [store_ok].
  pose proof (H 0%nat ltac:(lia)) as H0. rewrite aoff_0 in H0.
  destruct (wview segs m a); [|congruence].
  apply IH. intros j Hj. rewrite aoff_S. apply H. lia.
Qed.

Lemma write_to_mem_out : forall bs m a a',
  (forall j, (j < length bs)%nat -> a' <> aoff a j) ->
  write_to_mem m a bs a' = m a'.
Proof.
  induction bs as [|b bs IH]; intros m a a' H; [reflexivity|]. cbn [write_to_mem].
  rewrite IH.
  - pose proof (H 0%nat ltac:(cbn; lia)) as H0. rewrite aoff_0 in H0.
    unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned a') (bv_unsigned a)) as [E|E]; [|reflexivity].
    exfalso. apply H0. apply bv_eq. exact E.
  - intros j Hj. rewrite aoff_S. apply H. cbn. lia.
Qed.

Lemma write_to_mem_in : forall bs m a j,
  (Z.of_nat (length bs) <= 2^64) -> (j < length bs)%nat ->
  write_to_mem m a bs (aoff a j) = nth_error bs j.
Proof.
  induction bs as [|b bs IH]; intros m a j Hlen Hj; [cbn in Hj; lia|]. cbn [write_to_mem].
  destruct j as [|j].
  - rewrite aoff_0. rewrite write_to_mem_out.
    + unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
    + intros j Hj' E. rewrite aoff_S in E. rewrite <- (aoff_0 a) in E at 1.
      apply aoff_inj in E; [discriminate | lia | cbn [length] in Hlen; lia].
  - rewrite <- aoff_S. cbn [nth_error]. apply IH; cbn [length] in *; lia.
Qed.

(* [comment removed for export] *)
Lemma rview_write_out : forall bs m a a',
  (forall j, (j < length bs)%nat -> a' <> aoff a j) ->
  rview (write_to_mem m a bs) a' = rview m a'.
Proof. intros. unfold rview. rewrite write_to_mem_out by assumption. reflexivity. Qed.

Lemma rview_write_in : forall bs m a j b,
  (Z.of_nat (length bs) <= 2^64) -> nth_error bs j = Some b ->
  rview (write_to_mem m a bs) (aoff a j) = Some b.
Proof.
  intros bs m a j b Hlen Hn. unfold rview.
  rewrite write_to_mem_in; [rewrite Hn; reflexivity | exact Hlen |].
  apply nth_error_Some. congruence.
Qed.

Lemma wview_write : forall bs m a a',
  wview segs m a' <> None -> wview segs (write_to_mem m a bs) a' <> None.
Proof.
  induction bs as [|b bs IH]; intros m a a' H; [exact H|]. cbn [write_to_mem].
  apply IH. unfold wview in *. destruct (bv_eqb a' a); [discriminate | exact H].
Qed.

(* [comment removed for export] *)
Definition core_of (ms : machine_state) : core :=
  {| c_regs := ms_regs ms; c_fregs := ms_fregs ms; c_pc := ms_pc_val ms;
     c_fcsr := ms_fcsr ms; c_resv := ms_resv ms |}.

Definition ms_of (ms : machine_state) (c : core) (m' : word -> option byte) : machine_state :=
  {| ms_regs := c_regs c; ms_fregs := c_fregs c; ms_pc_val := c_pc c;
     ms_svc_pending := None; ms_resv := c_resv c; ms_fcsr := c_fcsr c;
     ms_mem := m'; ms_rom := ms_rom ms |}.

Definition ms_pend (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

Lemma step_decode : forall ms w i,
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
  step segs ms =
    match interp_eff segs (exec (Z_to_bv 64 4) i (core_of ms)) (ms_mem ms) with
    | MachineOk (c, m') => MachineOk (ms_of ms c m')
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof.
  intros ms w i Hf He Hd. unfold step, step_accesses. rewrite Hf.
  unfold decode_exec_accesses. rewrite He, Hd. unfold interp_eff, core_of.
  destruct (interp_eff_accesses segs _ _) as [[[c m'] acc]| |]; reflexivity.
Qed.

Lemma step_ecall : forall ms w,
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = true ->
  step segs ms = MachineOk (ms_pend ms).
Proof.
  intros ms w Hf He. unfold step, step_accesses. rewrite Hf.
  unfold decode_exec_accesses. rewrite He. reflexivity.
Qed.

Lemma interp_done : forall c m, interp_eff segs (EDone c) m = MachineOk (c, m).
Proof. reflexivity. Qed.

Lemma interp_load : forall n a k m bs,
  ov_read_bytes segs m a (width_bytes n) = Some bs ->
  interp_eff segs (ELoad n a k) m = interp_eff segs (k (bv_extract 0 n (le_bytes_to_word bs))) m.
Proof.
  intros n a k m bs H. unfold interp_eff. cbn [interp_eff_accesses]. rewrite H.
  destruct (interp_eff_accesses segs _ m) as [[v acc]| |]; reflexivity.
Qed.

Lemma interp_store : forall n a v k m,
  store_ok segs m a (width_bytes n) = true ->
  interp_eff segs (EStore n a v k) m =
  interp_eff segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))).
Proof.
  intros n a v k m H. unfold interp_eff. cbn [interp_eff_accesses]. rewrite H.
  destruct (interp_eff_accesses segs k _) as [[v' acc]| |]; reflexivity.
Qed.
End WithSegs.
