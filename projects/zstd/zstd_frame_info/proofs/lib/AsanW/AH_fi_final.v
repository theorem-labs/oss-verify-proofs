(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import ABase AMalloc_iface AHeapP AFake_iface AFake_arep AFake_stmtk
     ADepot_iface F_adepot ARepQ ARepQP ASec ASecFrame AInstance AInstanceM AInstanceF AFreeAll AHarness_iface AH_fi_iface
     AF_fi_gfha_iface AF_fi_ffsi_iface AF_fi_gfcsA AF_fi_gdsA AF_fi_gdidA AF_fi_fdsA AF_fi_gfha2A AF_fi_ffsiA AF_fi_wrap AF_fi_small AH_fi_ltoi.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Theorem fuzz_client_closed : forall rc : runConstT, fuzz_oneA_stmt (AI_of (@AHI_free rc)) afake_rng.
Proof.
  intros rc.
  set (AI := AI_of (@AHI_free rc)).
  assert (E : AHEAP AI = AHEAP_P (AH adepot_iface AQUAR ASEC_of)) by reflexivity.
  assert (EC : aci AI = aci_I) by reflexivity.
  assert (GIMG : In (0x20d40, 0x20dc0)%Z (aci AI)) by (rewrite EC; unfold aci_I; cbn; tauto).
  pose proof (fake_flag_AI adepot_iface AQUAR ASEC_of aci_I aci_ok1 AI E EC) as FFLAG.
  pose proof (fake_release_AI adepot_iface AQUAR ASEC_of AH_laws AI E) as FREL.
  pose proof (stack_malloc_0_AI' adepot_iface AQUAR ASEC_of AH_laws aci_I aci_ok1 AI E EC) as SM0.
  pose proof (stack_malloc_1_AI' adepot_iface AQUAR ASEC_of AH_laws aci_I aci_ok1 AI E EC 0%nat ltac:(cbn; lia)) as SM10.
  pose proof (stack_malloc_1_AI' adepot_iface AQUAR ASEC_of AH_laws aci_I aci_ok1 AI E EC 1%nat ltac:(cbn; lia)) as SM11.
  pose proof (stack_malloc_2_AI' adepot_iface AQUAR ASEC_of AH_laws aci_I aci_ok1 AI E EC) as SM2.
  pose proof (gfhaA AI AFake_iface.fflag afake_rng FFLAG FREL SM0 GIMG) as GFHA.
  pose proof (gfhA AI AFake_iface.fflag afake_rng FFLAG FREL SM0 GIMG) as GFH.
  pose proof (gfcsA AI AFake_iface.fflag afake_rng FFLAG FREL SM11 GFHA GIMG) as GFCS.
  pose proof (gdsA AI AFake_iface.fflag afake_rng FFLAG FREL SM11 GFHA GIMG) as GDS.
  pose proof (gdidA AI AFake_iface.fflag afake_rng FFLAG FREL SM11 GFHA GIMG) as GDID.
  pose proof (ffsiA AI AFake_iface.fflag afake_rng FFLAG FREL SM2 GFHA GIMG) as FFSI.
  pose proof (fdsA AI AFake_iface.fflag afake_rng FFLAG FREL SM11 GFHA FFSI GIMG) as FDS.
  pose proof (ffcsA AI afake_rng FFSI) as FFCS.
  pose proof (dboundA AI afake_rng FFSI GIMG) as DBOUND.
  pose proof (fhsizeA AI) as FHSIZE. pose proof (isframeA AI) as ISFRAME.
  apply (fuzz_oneA_of_ltoiA AI afake_rng).
  exact (ltoiA_proof AI AFake_iface.fflag afake_rng FFLAG FREL SM10 GFCS GDS FFCS GDID FDS DBOUND FHSIZE ISFRAME GFH GFHA GIMG).
Qed.
