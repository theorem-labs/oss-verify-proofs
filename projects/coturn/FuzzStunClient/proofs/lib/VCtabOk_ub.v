(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMemSound VCert VContract VDriver VGenv_src0 VGenv_ub VContractSound VContractSound2 VContractSound5 VContractTab VContractSound_ub VStrtoul_ub VSound VSoundCall VSoundContract VSoundAll VSoundAll_ub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Lemma strtoul_ok_ub U E mem0 rom :
  params_ok SEGSU (unit_params (genv_ub true) U) ->
  VContractSound2.contract_post SEGSU (unit_params (genv_ub true) U) E mem0 rom CI_ub C_strtoul A_STRTOUL_ub
  /\ VContractSound2.contract_dead SEGSU (unit_params (genv_ub true) U) E mem0 CI_ub C_strtoul.
Proof.
  intros PO. split; [|apply strtoul_dead].
  apply (strtoul_post SEGSU (unit_params (genv_ub true) U) E mem0 rom CI_ub PO
           A_STRTOUL_ub A_GOT_ub A_GUARD_ub RO1_LO_ub RO1_HI_ub RO2_LO_ub RO2_HI_ub RO_MIN_ub).
  - exists 0x257a0, 0x257a8. split; [cbn; tauto|]. unfold A_GOT_ub. lia.
  - exact GOT_BYTES_ub.
  - exists 0x10000, 0x58000. split; [cbn; tauto|]. unfold A_GUARD_ub. lia.
  - exists 0x10000, 0x24724. split; [cbn; tauto|]. unfold RO1_LO_ub, RO1_HI_ub. lia.
  - exists 0x10000, 0x24724. split; [cbn; tauto|]. unfold RO2_LO_ub, RO2_HI_ub. lia.
  - reflexivity.
  - unfold RO_MIN_ub. cbn [ci_tp CI_ub]. lia.
  - unfold RO_MIN_ub. cbn [vp_splo vp_frame unit_params genv_ub ge_P0 P0_ub]. lia.
  - right. unfold A_GUARD_ub. cbn [ci_errno CI_ub]. lia.
  - cbn [vp_sphi unit_params genv_ub ge_P0 P0_ub]. lia.
  - exact (STRTOUL_ub rom).
Qed.

Theorem ctab_ok_ub : forall rom, ctab_ok SEGSU (genv_ub true) rom.
Proof.
  intros rom U E mem0 PO.
  change (VContractTab.ctab_sound SEGSU (unit_params (genv_ub true) U) E mem0 rom CI_ub ctab_ub).
  apply (ctab_sound_ub_nostrtoul (unit_params (genv_ub true) U) E mem0 rom CI_ub ctab_ub PO).
  - reflexivity.
  - vm_compute. reflexivity.
  - exact (strtoul_ok_ub U E mem0 rom PO).
Qed.

(* [comment removed for export] *)
Theorem check_cert_sound_ub_closed rom C :
  check_cert (genv_ub true) C = ROk ->
  Forall (unit_okS SEGSU (genv_ub true) rom) C.
Proof. exact (check_cert_sound_ub rom C (ctab_ok_ub rom)). Qed.
