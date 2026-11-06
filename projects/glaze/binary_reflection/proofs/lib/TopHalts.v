(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ShapeHalts OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.TopProof4 OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsImg OSSVerify.Proofs.glaze.binary_reflection.lib.BoImg. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRoot OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ShapeHalts OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.Spec4KF OSSVerify.Proofs.glaze.binary_reflection.lib.TopProof4 OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs.RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsImg OSSVerify.Proofs.glaze.binary_reflection.lib.BoImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)

Lemma exit_code_in_any : forall z, (0 <= z < 256)%Z -> In (exit_code z) AnyExit.codes.
Proof. intros z Hz. unfold exit_code. apply in_any_exit_small. exact Hz. Qed.

Lemma ec_die : forall msg fs, exit_codes_in AnyExit.codes (t_die msg fs).
Proof.
  intros. unfold t_die, W. apply exit_codes_in_t_emit; [intros c f H; exfalso; exact (writes_no_exit _ _ _ _ H) |].
  apply exit_codes_in_t_exit. apply exit_code_in_any. lia.
Qed.

Lemma ec_success : forall calls fs, exit_codes_in AnyExit.codes (t_success calls fs).
Proof.
  intros. unfold t_success, W. apply exit_codes_in_t_emit; [intros c f H; exfalso; exact (writes_no_exit _ _ _ _ H) |].
  apply exit_codes_in_t_exit. apply exit_code_in_any. lia.
Qed.

Lemma ec_payload : forall cm pl calls fs, exit_codes_in AnyExit.codes (t_payload cm pl calls fs).
Proof. intros. unfold t_payload. apply ec_success. Qed.

Lemma ec_body : forall data fs, exit_codes_in AnyExit.codes (t_body data fs).
Proof.
  intros. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply ec_die|].
  destruct (Z.of_nat (length data) <? 6)%Z; [apply ec_die|].
  destruct (Z.of_nat (length data) <? 6 + hdr_cfglen data)%Z; [apply ec_die|].
  apply ec_payload.
Qed.

Lemma ec_opened : forall data fs, exit_codes_in AnyExit.codes (t_opened data fs).
Proof. intros. unfold t_opened. apply ec_body. Qed.

Lemma ec_opened_dir : forall path fs, exit_codes_in AnyExit.codes (t_opened_dir path fs).
Proof. intros. unfold t_opened_dir. apply ec_die. Qed.

Lemma ec_spec : forall argv fs0, exit_codes_in AnyExit.codes (spec argv fs0).
Proof.
  intros argv fs0. unfold spec.
  destruct argv as [|a0 [|path [|x l]]]; try apply ec_die.
  destruct (4096 <=? length path)%nat; [apply ec_die|].
  destruct (path_eqb path []); [apply ec_die|].
  destruct (path_is_dirref path); [apply exit_codes_in_t_alt2; [apply ec_die | apply ec_opened_dir]|].
  destruct (fs_lookup fs0 path); [apply exit_codes_in_t_alt2; [apply ec_die | apply ec_opened] | apply ec_die].
Qed.

Theorem spec_of_exit_codes : exit_codes_allowed AnyExit.codes spec_of.
Proof. intros inp tr code fs _ H. exact (ec_spec _ _ _ _ _ H). Qed.

(* [comment removed for export] *)

Definition P_root_f : Prop := root_obligation_core_f PIMG source_alloc_limit spec_of.
Definition U_root_f : Prop := root_obligation_core_f UIMG source_alloc_limit spec_of.
Definition A_root_f : Prop := root_obligation_core_f AIMG source_alloc_limit spec_of.
Definition B_root_f : Prop := root_obligation_core_f BIMG source_alloc_limit spec_of.




(* [comment removed for export] *)

Theorem halts_plain_of : P_root_f ->
  halts_allowed_T_scfg (alloc_only_cfg false) AnyExit.codes
    (mkImage OSSVerify.glaze.binary_reflection.images.Plain.M.loaded_segments OSSVerify.glaze.binary_reflection.images.Plain.M.init_pc OSSVerify.glaze.binary_reflection.images.Plain.M.phdrs).
Proof. intros H. exact (halts_of_root_f AnyExit.codes PIMG spec_of H spec_of_kill_free spec_of_exit_codes). Qed.

Theorem halts_ubsan_of : U_root_f ->
  halts_allowed_T_scfg (alloc_only_cfg false) AnyExit.codes
    (mkImage OSSVerify.glaze.binary_reflection.images.Ubsan.M.loaded_segments OSSVerify.glaze.binary_reflection.images.Ubsan.M.init_pc OSSVerify.glaze.binary_reflection.images.Ubsan.M.phdrs).
Proof. intros H. exact (halts_of_root_f AnyExit.codes UIMG spec_of H spec_of_kill_free spec_of_exit_codes). Qed.

Theorem halts_asan_of : A_root_f ->
  halts_allowed_T_scfg (alloc_only_cfg false) AnyExit.codes
    (mkImage OSSVerify.glaze.binary_reflection.images.Asan.M.loaded_segments OSSVerify.glaze.binary_reflection.images.Asan.M.init_pc OSSVerify.glaze.binary_reflection.images.Asan.M.phdrs).
Proof. intros H. exact (halts_of_root_f AnyExit.codes AIMG spec_of H spec_of_kill_free spec_of_exit_codes). Qed.

Theorem halts_both_of : B_root_f ->
  halts_allowed_T_scfg (alloc_only_cfg false) AnyExit.codes
    (mkImage OSSVerify.glaze.binary_reflection.images.AsanUbsan.M.loaded_segments OSSVerify.glaze.binary_reflection.images.AsanUbsan.M.init_pc OSSVerify.glaze.binary_reflection.images.AsanUbsan.M.phdrs).
Proof. intros H. exact (halts_of_root_f AnyExit.codes BIMG spec_of H spec_of_kill_free spec_of_exit_codes). Qed.
