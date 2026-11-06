(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
Local Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Class ACeil : Type := mkACeil { aceil_q : Z (* [comment removed for export] *) }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition alloc_ceiling {AC : ACeil} : Z :=
  16 * Z.max 0x7fff7f80000 (Z.min 0x7fffff80000 aceil_q).

(* [comment removed for export] *)
Definition aceil_of_sp (sp0 : Z) : ACeil := mkACeil ((sp0 - stack_max_size) / 16).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Facts.
Context {AC : ACeil}.

Lemma alloc_ceiling_val :
  alloc_ceiling = 16 * Z.max 0x7fff7f80000 (Z.min 0x7fffff80000 aceil_q).
Proof. reflexivity. Qed.

Lemma alloc_ceiling_range : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. unfold alloc_ceiling. lia. Qed.
Lemma alloc_ceiling_ge : 0x7fff7f800000 <= alloc_ceiling.
Proof. pose proof alloc_ceiling_range. lia. Qed.
Lemma alloc_ceiling_le : alloc_ceiling <= 0x7fffff800000.
Proof. pose proof alloc_ceiling_range. lia. Qed.
Lemma alloc_ceiling_lt47 : alloc_ceiling < 2^47.
Proof. pose proof alloc_ceiling_range. lia. Qed.
Lemma alloc_ceiling_lt63 : alloc_ceiling < 2^63.
Proof. pose proof alloc_ceiling_range. lia. Qed.
Lemma alloc_ceiling_lt : alloc_ceiling < 2^63.
Proof. exact alloc_ceiling_lt63. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition atop_ok (h : VmMaps) : Prop := alloc_top h = alloc_ceiling.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma atop_ok_grant : forall h a n, atop_ok h -> a + n <= alloc_top h -> a + n <= alloc_ceiling.
Proof. intros h a n H G. rewrite <- H. exact G. Qed.
Lemma atop_ok_leb : forall h x, atop_ok h -> (x <=? alloc_top h) = (x <=? alloc_ceiling).
Proof. intros h x H. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma atop_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> atop_ok h -> atop_ok h'.
Proof. intros h h' E H. unfold atop_ok, alloc_top in *. rewrite E. exact H. Qed.
Lemma atop_ok_mkVmMapsFull : forall h r m na sb b l mb,
  atop_ok h -> atop_ok (mkVmMapsFull r m na sb b l mb (vm_init_sp h)).
Proof. intros. eapply atop_ok_same; [|eassumption]. reflexivity. Qed.
(* [comment removed for export] *)

End Facts.

(* [comment removed for export] *)
Lemma aceil_of_sp_exact : forall sp0,
  sp_window_lo <= sp0 <= sp_window_hi -> sp0 mod 16 = 0 ->
  @alloc_ceiling (aceil_of_sp sp0) = sp0 - stack_max_size.
Proof.
  intros sp0 W A. unfold alloc_ceiling, aceil_of_sp, aceil_q, sp_window_lo, sp_window_hi, stack_max_size in *.
  pose proof (Z_div_mod_eq_full sp0 16). pose proof (Z_div_mod_eq_full (sp0 - 8388608) 16).
  pose proof (Z.mod_pos_bound (sp0 - 8388608) 16 ltac:(lia)). nia.
Qed.

Lemma aceil_of_sp_valid : forall sp0 : word, valid_sp sp0 ->
  @alloc_ceiling (aceil_of_sp (bv_unsigned sp0)) = bv_unsigned sp0 - stack_max_size.
Proof. (intros sp0; cps_intros (W1 & W2 & A)). apply aceil_of_sp_exact; [lia|exact A]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
