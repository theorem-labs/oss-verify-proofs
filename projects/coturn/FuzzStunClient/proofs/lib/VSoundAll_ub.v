(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VStepMemSound VParamsCheck VCert VItab VItab_ub
     VContract VDriver VGenv_src0 VGenv_ub VSound VSoundCall VSoundContract VSoundAll.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VParamsCheckFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma P0_ub_ok : params_ok Ubsan.M.loaded_segments P0_ub.
Proof. apply VParamsCheckFast.params_check_soundF'. vm_cast_no_check (@eq_refl bool true).  (* [comment removed for export] *) Qed.

Lemma genv_ub_ok rom :
  ctab_ok Ubsan.M.loaded_segments (genv_ub true) rom ->
  genv_ok Ubsan.M.loaded_segments (genv_ub true) rom.
Proof.
  intros CT. split; [reflexivity|]. split; [exact itab_ub_ok|]. split; [exact P0_ub_ok|exact CT].
Qed.

Theorem check_cert_sound_ub rom C :
  ctab_ok Ubsan.M.loaded_segments (genv_ub true) rom ->
  check_cert (genv_ub true) C = ROk ->
  Forall (unit_okS Ubsan.M.loaded_segments (genv_ub true) rom) C.
Proof. intros CT CHK. exact (check_cert_sound _ _ _ _ (genv_ub_ok rom CT) CHK). Qed.
