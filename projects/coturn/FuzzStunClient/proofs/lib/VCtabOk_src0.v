(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMemSound VCert VContract VDriver VGenv_src0 VContractSound VContractSound2 VContractSound5 VContractTab VContractSound_src0 VStrtoul_src0 VSound VSoundCall VSoundContract VSoundAll VSoundAll_src0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Lemma strtoul_ok_src0 U E mem0 rom :
  params_ok SEGS0 (unit_params (genv_src0 true) U) ->
  VContractSound2.contract_post SEGS0 (unit_params (genv_src0 true) U) E mem0 rom CI_src0 C_strtoul A_STRTOUL_src0
  /\ VContractSound2.contract_dead SEGS0 (unit_params (genv_src0 true) U) E mem0 CI_src0 C_strtoul.
Proof.
  intros PO. split; [|apply strtoul_dead].
  apply (strtoul_post SEGS0 (unit_params (genv_src0 true) U) E mem0 rom CI_src0 PO
           A_STRTOUL_src0 A_GOT_src0 A_GUARD_src0 RO1_LO_src0 RO1_HI_src0 RO2_LO_src0 RO2_HI_src0 RO_MIN_src0).
  - exists 0x252f8, 0x25300. split; [cbn; tauto|]. unfold A_GOT_src0. lia.
  - exact GOT_BYTES_src0.
  - exists 0x10000, 0x58000. split; [cbn; tauto|]. unfold A_GUARD_src0. lia.
  - exists 0x10000, 0x2427c. split; [cbn; tauto|]. unfold RO1_LO_src0, RO1_HI_src0. lia.
  - exists 0x10000, 0x2427c. split; [cbn; tauto|]. unfold RO2_LO_src0, RO2_HI_src0. lia.
  - reflexivity.
  - unfold RO_MIN_src0. cbn [ci_tp CI_src0]. lia.
  - unfold RO_MIN_src0. cbn [vp_splo vp_frame unit_params genv_src0 ge_P0 P0_src0]. lia.
  - right. unfold A_GUARD_src0. cbn [ci_errno CI_src0]. lia.
  - cbn [vp_sphi unit_params genv_src0 ge_P0 P0_src0]. lia.
  - exact (STRTOUL_src0 rom).
Qed.

Theorem ctab_ok_src0 : forall rom, ctab_ok SEGS0 (genv_src0 true) rom.
Proof.
  intros rom U E mem0 PO.
  change (VContractTab.ctab_sound SEGS0 (unit_params (genv_src0 true) U) E mem0 rom CI_src0 ctab_src0).
  apply (ctab_sound_src0_nostrtoul (unit_params (genv_src0 true) U) E mem0 rom CI_src0 ctab_src0 PO).
  - reflexivity.
  - vm_compute. reflexivity.
  - exact (strtoul_ok_src0 U E mem0 rom PO).
Qed.

(* [comment removed for export] *)
Theorem check_cert_sound_src0_closed rom C :
  check_cert (genv_src0 true) C = ROk ->
  Forall (unit_okS SEGS0 (genv_src0 true) rom) C.
Proof. exact (check_cert_sound_src0 rom C (ctab_ok_src0 rom)). Qed.
