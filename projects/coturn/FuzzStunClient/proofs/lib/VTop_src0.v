(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import FContract.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VParamsCheck VCert VContract VDriver VGenv_src0
     VSound VSoundCall VTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma fp_genv_ok_src0 : fp_genv_prop P0_src0 0x367b0 0x3670c FP_src0.
Proof. apply fp_genv_ok_sound. vm_compute. reflexivity. Qed.

Lemma segs_wr_readable_src0 : segs_wr_readable SEGS_src0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Theorem F_contract_src0_of_units (C : vcert) :
  (forall rom, Forall (unit_okS SEGS_src0 (genv_src0 true) rom) C) ->
  roots_ok FP_src0 C = true ->
  F_contract Plain.M.loaded_segments FP_src0.
Proof.
  intros UNITS ROK.
  apply (F_contract_of_roots SEGS_src0 (genv_src0 true) FP_src0 fp_genv_ok_src0 segs_wr_readable_src0 C); [|exact ROK].
  intros rom U HU _. pose proof (UNITS rom) as F. rewrite Forall_forall in F. exact (proj2 (F U HU)).
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VSoundAll VSoundAll_src0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem F_contract_src0_of (C : vcert) :
  (forall rom, ctab_ok Plain.M.loaded_segments (genv_src0 true) rom) ->
  check_cert (genv_src0 true) C = ROk ->
  roots_ok FP_src0 C = true ->
  F_contract Plain.M.loaded_segments FP_src0.
Proof.
  intros CT CHK ROK. apply (F_contract_src0_of_units C); [|exact ROK].
  intros rom. exact (check_cert_sound_src0 rom C (CT rom) CHK).
Qed.

(* [comment removed for export] *)
Theorem F_contract_src0_of_certs (CS : list vcert) :
  (forall rom, ctab_ok Plain.M.loaded_segments (genv_src0 true) rom) ->
  Forall (fun C => check_cert (genv_src0 true) C = ROk) CS ->
  roots_ok FP_src0 (concat CS) = true ->
  F_contract Plain.M.loaded_segments FP_src0.
Proof.
  intros CT CHK ROK. apply (F_contract_src0_of_units (concat CS)); [|exact ROK].
  intros rom. rewrite Forall_forall. intros U HU. apply in_concat in HU as (C & HC & HU).
  rewrite Forall_forall in CHK.
  pose proof (check_cert_sound_src0 rom C (CT rom) (CHK C HC)) as F. rewrite Forall_forall in F. exact (F U HU).
Qed.
