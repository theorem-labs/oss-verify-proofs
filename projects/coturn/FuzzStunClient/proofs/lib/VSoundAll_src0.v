(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VStepMemSound VParamsCheck VCert VItab VItab_src0
     VContract VDriver VGenv_src0 VSound VSoundCall VSoundContract VSoundAll.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VParamsCheckFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma P0_src0_ok : params_ok Plain.M.loaded_segments P0_src0.
Proof. apply VParamsCheckFast.params_check_soundF'. vm_cast_no_check (@eq_refl bool true).  (* [comment removed for export] *) Qed.

Lemma genv_src0_ok rom :
  ctab_ok Plain.M.loaded_segments (genv_src0 true) rom -> genv_ok Plain.M.loaded_segments (genv_src0 true) rom.
Proof.
  intros CT. split; [reflexivity|]. split; [exact itab_src0_ok|]. split; [exact P0_src0_ok|exact CT].
Qed.

Theorem check_cert_sound_src0 rom C :
  ctab_ok Plain.M.loaded_segments (genv_src0 true) rom ->
  check_cert (genv_src0 true) C = ROk ->
  Forall (unit_okS Plain.M.loaded_segments (genv_src0 true) rom) C.
Proof. intros CT CHK. exact (check_cert_sound _ _ _ _ (genv_src0_ok rom CT) CHK). Qed.
