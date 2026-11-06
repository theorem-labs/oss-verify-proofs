(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA IcptIfaceA HeapIfaceAJx L5Defs PmSpecsAa JatIfaceInst JatIfaceLayoutPM PmALayFacts UbjsonPmFinal
PmAOpnew PmAOpdel PmAErr PmAEmb PmAEmm PmAEms PmASrcXsgetn PmASrcFill PmASrcRead PmASrcPeek PmASrcIgnore PmAGetLen PmABa7 PmABo7 UbjsonPmAsanRows.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma leaves_ab : UbjsonPmAsanRows.leaves_stmt.
Proof.
intros ar HIR OK IC EX GP.
pose proof (@PMAOPN.opnew_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK) as OPN.
pose proof (@PMAOPD.opdel_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK) as OPD.
pose proof (@PMAERR.make_ec_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK EX) as MKE.
pose proof (@PMAXG.xsgetn_ok ScfgP_cfg0 art_L ar art_C art_IL HIR art_pma_layout OK IC art_IL_ok) as XG.
pose proof (@PMASFB.fill_buffer_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK art_IL IC art_IL_ok XG) as FB.
pose proof (@PMASRD.src_read_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK art_IL IC art_IL_ok FB XG) as SR.
pose proof (@PMAGLN.get_length_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK SR MKE) as GL.
pose proof (@PMASPK.peek_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK FB) as PK.
pose proof (@PMASIG.ignore_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK FB) as IG.
pose proof (@PMAEB.push_mi_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK EX OPN OPD) as PMI.
pose proof (@PMAEM.push_ms_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK EX OPN OPD) as PMS.
pose proof (@PMAES.push_msu_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK EX OPN OPD) as PMSU.
split.
- exact (@PMABA7.begin_array_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK art_IL IC art_IL_ok PK IG SR GL MKE PMI PMS PMSU).
- exact (@PMABO7.begin_object_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK art_IL IC art_IL_ok PK IG SR GL MKE PMI PMS PMSU).
Qed.
Definition ubjson_pm_asan_base := UbjsonPmAsanRows.ubjson_pm_asan_base leaves_ab.
Definition ubjson_pm_asan_base_abort := UbjsonPmAsanRows.ubjson_pm_asan_base_abort leaves_ab.
