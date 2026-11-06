(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA IcptIfaceAB0 HeapIfaceAJx L5Defs PmSpecsAb PmSpecsBX JbtIfaceInst JbtIfaceLayoutPM PmBLayFacts UbjsonPmFinal
PmBOpnew PmBOpdel PmBErr PmBSrcXsgetn PmBSrcFill PmBSrcRead PmBSrcPeek PmBSrcIgnore PmBGetLen
PmBConeMi PmBConeMs PmBConeMsu PmBSlowMi PmBSlowMs PmBSlowMsu PmBBa7 PmBBo7 PmBImgGap UbjsonPmBothRows.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma leaves_ab : UbjsonPmBothRows.leaves_stmt.
Proof.
intros ar HIR OK IC EX GP.
pose proof (@PMBOPN.opnew_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK) as OPN.
pose proof (@PMBOPD.opdel_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK) as OPD.
pose proof (@PMBERR.make_ec_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK EX) as MKE.
pose proof (@PMBXG.xsgetn_ok ScfgP_cfg0 art_L ar art_C art_IL HIR art_pma_layout OK IC art_IL_ok) as XG.
pose proof (@PMBSFB.fill_buffer_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK art_IL IC art_IL_ok XG) as FB.
pose proof (@PMBSRD.src_read_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK art_IL IC art_IL_ok FB XG) as SR.
pose proof (@PMBGLN.get_length_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK SR MKE) as GL.
pose proof (@PMBSPK.peek_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK FB) as PK.
pose proof (@PMBSIG.ignore_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK FB) as IG.
pose proof (@PMBCOMI.cone_mi_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK EX) as CMI.
pose proof (@PMBCOMS.cone_ms_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK EX) as CMS.
pose proof (@PMBCOMSU.cone_msu_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK EX) as CMSU.
pose proof (@PMBSLMI.slow_mi_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK EX OPN OPD) as SMI.
pose proof (@PMBSLMS.slow_ms_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK EX OPN OPD) as SMS.
pose proof (@PMBSLMSU.slow_msu_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK EX OPN OPD) as SMSU.
split.
- exact (@PMBBA7.begin_array_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK art_IL IC art_IL_ok PK IG SR GL MKE CMI SMI CMS SMS CMSU SMSU).
- exact (@PMBBO7.begin_object_ok ScfgP_cfg0 art_L ar art_C HIR art_pma_layout OK art_IL IC art_IL_ok PK IG SR GL MKE CMI SMI CMS SMS CMSU SMSU).
Qed.
Definition ubjson_pm_both_base := UbjsonPmBothRows.ubjson_pm_both_base leaves_ab.
Definition ubjson_pm_both_base_abort := UbjsonPmBothRows.ubjson_pm_both_base_abort leaves_ab.
