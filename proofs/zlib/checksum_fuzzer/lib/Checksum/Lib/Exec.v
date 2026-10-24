(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem.

Module DA_Myrk.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

Definition SYSCALL_ECALL : Z := 0xa2e94.     (* [comment removed for export] *)

Lemma bv_modulus_32 : bv_modulus 32 = 2^32. Proof. reflexivity. Qed.
Lemma bv_half_modulus_32 : bv_half_modulus 32 = 2^31. Proof. reflexivity. Qed.
Lemma swrap32_small0 : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 (z + 0) = z.
Proof. intros z Hz. rewrite Z.add_0_r. apply bv_swrap_small. rewrite bv_half_modulus_32. lia. Qed.
Lemma swrap32_neg : forall r, 1 <= r <= 2^31 -> bv_swrap 32 (18446744073709551616 - r + 0) = - r.
Proof.
  intros r Hr. unfold bv_swrap, bv_wrap. rewrite bv_half_modulus_32, bv_modulus_32.
  replace (2^32) with 4294967296 by reflexivity. replace (2^31) with 2147483648 by reflexivity.
  Z.div_mod_to_equations. nia.
Qed.
Lemma swrap32_negneg : forall r, 1 <= r < 2^31 -> bv_swrap 32 (0 - - r mod 18446744073709551616) = r.
Proof.
  intros r Hr. unfold bv_swrap, bv_wrap. rewrite bv_half_modulus_32, bv_modulus_32.
  replace (2^32) with 4294967296 by reflexivity. replace (2^31) with 2147483648 by reflexivity.
  Z.div_mod_to_equations. nia.
Qed.

Lemma swrap32_negneg2 : forall r, 1 <= r < 2^31 -> bv_swrap 32 (0 - (18446744073709551616 - r)) = r.
Proof.
  intros r Hr. unfold bv_swrap, bv_wrap. rewrite bv_half_modulus_32, bv_modulus_32.
  replace (2^32) with 4294967296 by reflexivity. replace (2^31) with 2147483648 by reflexivity.
  Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma zx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite Z_to_bv_unsigned. unfold bv_wrap. replace (bv_modulus 64) with (2^64) by reflexivity. rewrite (Z.mod_small z (2^64)) by lia. f_equal. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma errno_ret_neg : forall er, 1 <= er <= 4095 -> errno_ret er = Z_to_bv 64 (18446744073709551616 - er).
Proof.
  intros er Her. unfold errno_ret. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. replace (bv_modulus 64) with 18446744073709551616 by reflexivity.
  Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Ltac is_Zlit' a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac lit_addrs_goal :=
  repeat match goal with
  | |- context [Z.add ?a ?b] => is_Zlit' a; is_Zlit' b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  end.

(* [comment removed for export] *)
Ltac blia := first [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; nia ].
End DA_Myrk.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Definition mstep (ms ms' : machine_state) : Prop :=
  ms_svc_pending ms = None /\ RiscvSemantics.step segs ms = MachineOk ms'.

Inductive msteps : machine_state -> machine_state -> Prop :=
| msteps_refl : forall ms, msteps ms ms
| msteps_cons : forall ms ms1 ms2, mstep ms ms1 -> msteps ms1 ms2 -> msteps ms ms2.

(* [comment removed for export] *)

Lemma msteps_trans : forall a b c, msteps a b -> msteps b c -> msteps a c.
Proof. intros a b c H; induction H; intros; [assumption|]. eapply msteps_cons; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition evt (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
  exists ms', msteps ms ms' /\ Q ms'.

Lemma evt_done : forall (Q : machine_state -> Prop) ms, Q ms -> evt Q ms.
Proof. intros Q ms H. exists ms. split; [apply msteps_refl|exact H]. Qed.

Lemma evt_step : forall Q ms ms1, mstep ms ms1 -> evt Q ms1 -> evt Q ms.
Proof. intros Q ms ms1 H (ms' & Hs & HQ). exists ms'. split; [eapply msteps_cons; eauto|exact HQ]. Qed.

(* [comment removed for export] *)
Lemma evt_cut : forall (P Q : machine_state -> Prop) ms,
  evt P ms -> (forall ms', P ms' -> evt Q ms') -> evt Q ms.
Proof.
  intros P Q ms (ms1 & H1 & HP) K. destruct (K ms1 HP) as (ms2 & H2 & HQ).
  exists ms2. split; [eapply msteps_trans; eauto| exact HQ].
Qed.

Lemma evt_mono : forall (P Q : machine_state -> Prop) ms,
  evt P ms -> (forall ms', P ms' -> Q ms') -> evt Q ms.
Proof. intros P Q ms H K. eapply evt_cut; [exact H|]. intros ms' HP. apply evt_done, K, HP. Qed.

(* [comment removed for export] *)
Lemma evt_eq : forall Q ms ms', ms = ms' -> evt Q ms' -> evt Q ms.
Proof. intros; subst; assumption. Qed.

End WithSegs.

Arguments mstep segs ms ms' /.
