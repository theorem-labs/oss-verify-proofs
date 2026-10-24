(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition MS (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
           (m ro : word -> option byte) : machine_state :=
  {| ms_regs := R; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := None;
     ms_resv := rv; ms_fcsr := fc; ms_mem := m; ms_rom := ro |}.

Definition MSsvc (R F : bvmap 5 word) (pc : word) (x8 : word) (fc : bv 32) (rv : option word)
           (m ro : word -> option byte) : machine_state :=
  {| ms_regs := R; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := Some x8;
     ms_resv := rv; ms_fcsr := fc; ms_mem := m; ms_rom := ro |}.

(* [comment removed for export] *)
Definition MS_of_core (c : core) (m ro : word -> option byte) : machine_state :=
  MS (c_regs c) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c) m ro.

(* [comment removed for export] *)

(* [comment removed for export] *)

Definition lift_result (ro : word -> option byte) (r : machine_result (core * (word -> option byte)))
  : machine_result machine_state :=
  match r with
  | MachineOk (c, m') => MachineOk (MS_of_core c m' ro)
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

(* [comment removed for export] *)
Fixpoint interp_eff0 (segs : list Segment) (t : eff) (m : word -> option byte)
    : machine_result (core * (word -> option byte)) :=
  match t with
  | EDone c => MachineOk (c, m)
  | EEbreak _ | EFault _ | EDefinedIllegal _ => MachineFault
  | EIllegal _ | EEcall _ => MachineUnmodeled
  | ELoad n a k =>
      match ov_read_bytes segs m a (width_bytes n) with
      | Some bs => interp_eff0 segs (k (bv_extract 0 n (le_bytes_to_word bs))) m
      | None => MachineFault
      end
  | EStore n a v k =>
      if store_ok segs m a (width_bytes n)
      then interp_eff0 segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))
      else MachineFault
  end.

Lemma interp_eff0_eq : forall segs t m, interp_eff segs t m = interp_eff0 segs t m.
Proof.
  intros segs t; induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m; cbn; try reflexivity.
  - unfold interp_eff. cbn. destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|reflexivity].
    rewrite <- IH. unfold interp_eff.
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [[[c m'] acc]| |]; reflexivity.
  - unfold interp_eff. cbn. destruct (store_ok segs m a (width_bytes n)); [|reflexivity].
    rewrite <- IH. unfold interp_eff.
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [[[c m'] acc]| |]; reflexivity.
Qed.

Lemma step_gen : forall segs R F pc fc rv m ro w i sz,
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, sz) ->
  RiscvSemantics.step segs (MS R F pc fc rv m ro) =
  lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m).
Proof.
  intros segs R F pc fc rv m ro w i sz Hf He Hd.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold decode_exec_accesses. rewrite He, Hd. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom MS].
  rewrite <- interp_eff0_eq.
  unfold interp_eff. destruct (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i _) m) as [[[c m'] acc]| |]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_ecall_gen : forall segs R F pc fc rv m ro w,
  fetch_word segs pc = Some w ->
  is_ecall w = true ->
  RiscvSemantics.step segs (MS R F pc fc rv m ro) =
  MachineOk (MSsvc R F pc (if is_x0 17 then w0 else reg_get R 17) fc rv m ro).
Proof.
  intros segs R F pc fc rv m ro w Hf He.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold drop_access_report, decode_exec_accesses. rewrite He. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma reg_get_set_same : forall (R : bvmap 5 word) (r : reg) v,
  reg_get (bvmap_set r v R) r = v.
Proof. intros. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.

Lemma reg_get_set_other : forall (R : bvmap 5 word) (r r' : reg) v,
  r <> r' -> reg_get (bvmap_set r v R) r' = reg_get R r'.
Proof. intros. unfold reg_get. rewrite bvmap_get_set_other by assumption. reflexivity. Qed.

(* [comment removed for export] *)

Lemma w0_lit : w0 = Z_to_bv 64 0. Proof. reflexivity. Qed.
Lemma w1_lit : w1 = Z_to_bv 64 1. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lit_add_lit : forall a b, (Z_to_bv 64 a + Z_to_bv 64 b : word) = Z_to_bv 64 (a + b).
Proof.
  intros. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma Z_to_bv_bv_unsigned : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma Z_to_bv_plus0 : forall (x : word), Z_to_bv 64 (bv_unsigned x + 0) = x.
Proof. intros. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma unsigned_lit : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact H. Qed.

Lemma unsigned_lit_wrap : forall z, bv_unsigned (Z_to_bv 64 z) = (z mod 2^64)%Z.
Proof. intros. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Definition ret_pc (ra : word) : word := bv_and ra (bv_not (Z_to_bv 64 1)).

Lemma ret_pc_fold : forall ra, bv_and ra (bv_not (Z_to_bv 64 1)) = ret_pc ra.
Proof. reflexivity. Qed.

Lemma ret_pc_even : forall z, (0 <= z < 2^64)%Z -> (z mod 2 = 0)%Z -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz He. unfold ret_pc. apply bv_eq. rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  rewrite !(bv_wrap_small 64 z) by (unfold bv_modulus; lia).
  change (bv_wrap 64 (Z.lnot (bv_wrap 64 1))) with (Z.ones 64 - 1)%Z.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0).
  - subst i. rewrite (Z.bit0_eqb z). replace (z mod 2)%Z with 0%Z by lia. cbn. reflexivity.
  - destruct (Z.ltb_spec0 i 64).
    + replace (Z.testbit (Z.ones 64 - 1) i) with true. { apply andb_true_r. }
      symmetry. change (Z.ones 64 - 1)%Z with (Z.shiftl (Z.ones 63) 1). rewrite Z.shiftl_spec by lia. apply Z.ones_spec_low. lia.
    + rewrite (Z.bits_above_log2 z i); [reflexivity| lia |].
      destruct (Z.eq_dec z 0). { subst. cbn. lia. }
      apply Z.lt_le_trans with 64%Z; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
