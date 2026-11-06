(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "list"; "option"; "Some"; "pair"; "prod"; "false"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ss_next"; "swf"; "sprop"; "SLit"; "ss_facts"; "sobj"; "reg_sv"; "ss_lenient"; "SVar"; "sprop_eqb"; "SAlu"; "sprop_below"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "sD_of"; "CASX"; "DEPE"; "BIGX"; "PSE"; "leaves_at"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "OFF_PUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC"; "NVN"; "VFN"; "rd_okG"; "BIGF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cN0"; "ED_N0_1"; "ED_N0_2"; "C2_N0_1"; "C2_N0_2"; "Ebg_N0"; "P0_N0"; "CD_N0"; "Erc_N0"; "PMID_N0"; "RD_N0_1"; "RD_N0_2"; "S1c_N0_1"; "S1c_N0_2"; "exits1_N0"; "run3_N0"; "TD_N0_1"; "TD_N0_2"; "run2_N0_1"; "run2_N0_2"; "EfD_N0_1"; "EfD_N0_2"; "Eps_N0"; "TDr_N0_1"; "TDr_N0_2"; "W_N0"; "run1_N0"; "st_N0"; "run4_N0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln"; "RCYE"; "Erc_of"; "small_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG"; "P0_g"; "XIg"; "sa_g"; "FACTSg"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_N0 : list ulink := Wcan 0.
Definition st_N0 : ustop := UStopLe.
Definition P0_N0 : axst := ltac2:(tb__ "0|0|
S6eS2S51S53S5S19A1S30A5").

Definition run1_N0 : list leafA := ltac2:(tb__ "0|0|
S59S21S4SdS23S5SdA1A3S3eA3").

Definition S1c_N0_1 : axst := ltac2:(tb__ "0|0|
S29S5aU0S52A2S18S10S3eA1A1Z1A3").
Definition C2_N0_1 : axst := C2_of S1c_N0_1.
Definition run2_N0_1 : list leafA := ltac2:(tb__ "0|0|
S59S21S4SdS24S5SdA1A3S3bA3").
Definition EfD_N0_1 : axst := leaf 0 run2_N0_1.
Definition ED_N0_1 : axst := ED_of EfD_N0_1.
Definition RD_N0_1 : list sobj := RD_of ED_N0_1 1.
Definition TD_N0_1 : axst := TD_of ED_N0_1 1.
Definition TDr_N0_1 : axst := TDr_of TD_N0_1.
Definition S1c_N0_2 : axst := ltac2:(tb__ "0|0|
S29S5aU0S52A2S18S10S3eA1A1Z2A3").
Definition C2_N0_2 : axst := C2_of S1c_N0_2.
Definition run2_N0_2 : list leafA := ltac2:(tb__ "0|0|
S59S21S4SdS24S5SdA1A3S3cA3").
Definition EfD_N0_2 : axst := leaf 0 run2_N0_2.
Definition ED_N0_2 : axst := ED_of EfD_N0_2.
Definition RD_N0_2 : list sobj := RD_of ED_N0_2 2.
Definition TD_N0_2 : axst := TD_of ED_N0_2 2.
Definition TDr_N0_2 : axst := TDr_of TD_N0_2.
Definition exits1_N0 : list axst := ltac2:(tb__ "0|0|
S4SfS44S4SfS45S5SfA1A3A3").

Definition CD_N0 : axst := CD_of TDr_N0_1.
Definition run3_N0 : list leafA := ltac2:(tb__ "0|0|
S59S21S4SdS26S4SdS25S5SdA1A3A3S3fA3").
Definition Eps_N0 : axst := leaf 0 run3_N0.
Definition Ebg_N0 : axst := leaf 1 run3_N0.
Definition run4_N0 : list leafA := ltac2:(tb__ "0|0|
S59S21S4SdS60S5SdA1A3S3dA3").
Definition Erc_N0 : axst := ltac2:(tb__ "0|0|
S61S5aU0S54A2S18S10S3dA1A1A2").

Definition PMID_N0 : axst := ltac2:(tb__ "0|0|
S76S2S51S53S5S19A1S30A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_N0 : ltac2:(tb__ "0|0|
S0S3S5eS37S14S10S3eA1A1A2S2A3"). Proof. vmr. Qed.
Lemma Cert1_N0 : ltac2:(tb__ "0|0|
S0S3S57S38S21S4SdS23S5SdA1A3S37S4SfS3eS5SfA1A3S46A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_N0 exits1_N0 run1_N0); [unfold run1_N0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_N0 : ltac2:(tb__ "0|2|
S0S3S58S38S21S4SdS23S5SdA1A3S37S4S55S56S3eZ1S17Z0M0A1M1A3S5S55A1A3S5fSfS55SfS56R1G0G1A3LE;S46A4A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_N0 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_N0) run1_N0); [unfold run1_N0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_N0_1 : ltac2:(tb__ "0|4|
S0S7SaS6SaS13S13A2M0A1M1S6S16A1M2A2M3A1S65S10S44A1S10S3bA1A2S8G3S9G1G2S4G0S9S13S13S2cS2dA4S5G0A1A3S28A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_N0_1 : ltac2:(tb__ "0|1|
S1S0S3S15S10S3bA1M0A1S2A3S1S0SeS14G0A1S14S10S44A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_N0_1 : ltac2:(tb__ "0|0|
S0S3S5eS37S14S10S3bA1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_N0_1 : ltac2:(tb__ "0|0|
S0SfS12S44S10S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_N0_1 : ltac2:(tb__ "0|0|
S0S6S11A1S59S21S4SdS24S5SdA1A3S3bA3S4aA3"). Proof. unfold run2_N0_1; reflexivity. Qed.
Lemma L2_N0_1 : ltac2:(tb__ "0|0|
S1S0S3S27S4aS4SdS24S5SdA1A3A2S2A3S0SfS5aU0S4aA2S4cA3A2"). Proof. Time (split; [vmr | unfold EfD_N0_1; reflexivity]). Qed.
Lemma AXD_N0_1 : ltac2:(tb__ "0|0|
S0S7SfA1S5bS4cS2aA2S8SfS39A2A3"). Proof. Time vmr. Qed.
Lemma HeD_N0_1 : ltac2:(tb__ "0|2|
S0S7S6S19A1M0A1S6bS39S5cZ1M1A1S22S39G1A2A3S8G0S42A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_N0_1 : ltac2:(tb__ "0|1|
S0S3S6aS39S5cZ1M0A1S22S39G0A2S42S4SfS5dG0A1S5SfA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_N0_1 : ltac2:(tb__ "0|1|
S0SfS48S69S6cS22S39Z1M0A2S5cG0A1S5dG0A1S39S42A5S18S10S39A1A1A2A3").
Proof. unfold TD_N0_1, TD_of, RD_N0_1; reflexivity. Qed.
Lemma DCHK_N0_1 : ltac2:(tb__ "0|2|
S0S3S6dU0M0S31S2fG0A2Z1M1S39S48S22S39G1A2S42A7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_N0_1 : ltac2:(tb__ "0|0|
S0S7SfA1S5bS48S2bA2S8SfS4fA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_N0_1 : ltac2:(tb__ "0|0|
S0S3S7bS4fS3fA2S2A3"). Proof. Time vmr. Qed.
Lemma D2_N0_2 : ltac2:(tb__ "0|4|
S0S7SaS6SaS13S13A2M0A1M1S6S16A1M2A2M3A1S65S10S45A1S10S3cA1A2S8G3S9G1G2S4G0S9S13S13S2cS2dA4S5G0A1A3S28A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_N0_2 : ltac2:(tb__ "0|1|
S1S0S3S15S10S3cA1M0A1S2A3S1S0SeS14G0A1S14S10S45A1A1A3S0S3S1bG0A1SbA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_N0_2 : ltac2:(tb__ "0|0|
S0S3S5eS37S14S10S3cA1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_N0_2 : ltac2:(tb__ "0|0|
S0SfS12S45S10S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_N0_2 : ltac2:(tb__ "0|0|
S0S6S11A1S59S21S4SdS24S5SdA1A3S3cA3S4bA3"). Proof. unfold run2_N0_2; reflexivity. Qed.
Lemma L2_N0_2 : ltac2:(tb__ "0|0|
S1S0S3S27S4bS4SdS24S5SdA1A3A2S2A3S0SfS5aU0S4bA2S4dA3A2"). Proof. Time (split; [vmr | unfold EfD_N0_2; reflexivity]). Qed.
Lemma AXD_N0_2 : ltac2:(tb__ "0|0|
S0S7SfA1S5bS4dS2aA2S8SfS3aA2A3"). Proof. Time vmr. Qed.
Lemma HeD_N0_2 : ltac2:(tb__ "0|2|
S0S7S6S19A1M0A1S6bS3aS5cZ2M1A1S22S3aG1A2A3S8G0S43A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_N0_2 : ltac2:(tb__ "0|1|
S0S3S6aS3aS5cZ2M0A1S22S3aG0A2S43S4SfS5dG0A1S5SfA1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma HTD_N0_2 : ltac2:(tb__ "0|1|
S0SfS49S69S6cS22S3aZ2M0A2S5cG0A1S5dG0A1S3aS43A5S18S10S3aA1A1A2A3").
Proof. unfold TD_N0_2, TD_of, RD_N0_2; reflexivity. Qed.
Lemma DCHK_N0_2 : ltac2:(tb__ "0|2|
S0S3S6dU0M0S31S2fG0A2Z2M1S3aS49S22S3aG1A2S43A7S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_N0_2 : ltac2:(tb__ "0|0|
S0S7SfA1S5bS49S2bA2S8SfS50A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_N0_2 : ltac2:(tb__ "0|0|
S0S3S7bS50S3fA2S2A3"). Proof. Time vmr. Qed.
Lemma RUN3_N0 : ltac2:(tb__ "0|0|
S0S6S11A1S59S21S4SdS26S4SdS25S5SdA1A3A3S3fA3S47A3"). Proof. unfold run3_N0; reflexivity. Qed.
Lemma L3_N0 : ltac2:(tb__ "0|0|
S1S0S3S27S47S4SdS26S4SdS25S5SdA1A3A3A2S2A3S1S0SfS5aU0S47A2S4eA3S0SfS5aU1S47A2S3dA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_N0 | unfold Ebg_N0]; reflexivity]). Qed.
Lemma NX3_N0 : ltac2:(tb__ "0|1|
S1S0S3S5eS37S14S10S3fA1M0A1A2S2A3S0S3S1bG0A1SbA3A2"). Proof. split; vmr. Qed.

Lemma SMF_N0 : ltac2:(tb__ "0|0|
S0S3S66S16S1dS62A1S18S10S4eA1A1A3S2A3"). Proof. vmr. Qed.
Lemma BGF_N0 : ltac2:(tb__ "0|1|
S1S0S3S66S16S1dS7fA1S18S10S40A1A1M0A3S2A3S0S3S66S16S1dS32A1G0A3S2A3A2"). Proof. split; vmr. Qed.
Lemma NXB_N0 : ltac2:(tb__ "0|0|
S0S3S5eS37S14S10S3dA1A1A2S2A3"). Proof. vmr. Qed.
Lemma CertR_N0 : ltac2:(tb__ "0|1|
S0S3S57S38S21S4SdS60S5SdA1A3S37S4SfS3dS5SfA1M0A3S4SfS40G0A3A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [RCYE] GW Ebg_N0 [Erc_N0] run4_N0); [unfold run4_N0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECertR_N0 : ltac2:(tb__ "0|3|
S0S3S58S38S21S4SdS60S5SdA1A3S37S4S55S56S3dZ1S17Z0M0A1M1A3S5S55A1M2A3S4S55S56S40G0G1A3G2A3A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [RCYE] GW (mkVNA Ebg_N0 1 (SLit 0)) [mkVNA Erc_N0 0 (SLit 0)] run4_N0); [unfold run4_N0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma LEAF_N0 : ltac2:(tb__ "0|2|
S1S0SdS20S10S40A1M0A1S60A3S1S0S13S1aG0Z1A2S17Z40744A1A3S1S0S13S1aG0Z2A2S1eS68S1cPaA1S17S2eA1A3M1A3S1S0S13S1aG0ZaA2G1A3S1S0S13S1aG0ZbA2S1eS68S1cPcA1S17N10A1A3A3S0S3S1bG0A1SbA3A2A2A2A2A2").
Proof. split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]. Qed.

Lemma Wa_N0 : ltac2:(tb__ "0|0|
S0S3S15S70S34U0A1S33A2A1S2A3"). Proof. vmr. Qed.
Lemma Da_N0 : ltac2:(tb__ "0|5|
S0S7SaS6SaS13S13A2M0A1M1S6S16A1M2A2M3A1S65S10S36S35S34U0A1M4S33A3A1S70G4S33A2A2S8G3S9G1G2S4G0S9S13S13S1cP18A1S17S7eA1A4S5G0A1A3S5S16A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_N0 : ltac2:(tb__ "0|0|
S0S3S15S72S34U0A1S33S2fA3A1S2A3"). Proof. vmr. Qed.
Lemma Wc_N0 : ltac2:(tb__ "0|0|
S0S3S15S73S34U0A1S33S2fA3A1S2A3"). Proof. vmr. Qed.
Lemma Wd_N0 : ltac2:(tb__ "0|0|
S0S3S15S74S34U0A1S33S2fA3A1S2A3"). Proof. vmr. Qed.
Lemma Fb_N0 : ltac2:(tb__ "0|0|
S0S3S67S16S1fS7dA1S71S2S34U0A1S33S30A4A3S2A3"). Proof. vmr. Qed.
Lemma XI_N0 : ltac2:(tb__ "0|2|
S0S7SfA1S5bS75S2S34U0M0A1M1S33S2fS30A5S6fG0ScS63S2fA2A2A2S8SfS6eS2G1S33S5fS63S19S64S2fA4S30A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_N0 : ltac2:(tb__ "0|0|
S0S3S5eS37S14S10S41A1A1A2S2A3"). Proof. vmr. Qed.
Definition Cert1m_N0__runs : ltac2:(tb__ "0|0|
S6S7S6S11A1A1A1") := ltac2:(tb__ "0|0|
S7cS38S21S4SdS23S5SdA1A3S4SfS41S5SfA1A3A4").
Lemma Cert1m_N0 : ltac2:(tb__ "0|0|
S0S3S57S38S21S4SdS23S5SdA1A3S37S4SfS41S5SfA1A3S46A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_N0] exits1_N0 Cert1m_N0__runs); [unfold Cert1m_N0__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_N0 : ltac2:(tb__ "0|2|
S0S3S58S38S21S4SdS23S5SdA1A3S37S4S55S56S41Z1S17Z0M0A1M1A3S5S55A1A3S5fSfS55SfS56R1G0G1A3LE;S46A4A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_N0 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_N0) Cert1m_N0__runs); [unfold Cert1m_N0__runs; reflexivity | vmr]. Qed.
Lemma Wbm_N0 : ltac2:(tb__ "0|0|
S0S3S15S77S34U0A1S33S2fA3A1S2A3"). Proof. vmr. Qed.
Lemma Wcm_N0 : ltac2:(tb__ "0|0|
S0S3S15S78S34U0A1S33S2fA3A1S2A3"). Proof. vmr. Qed.
Lemma Wdm_N0 : ltac2:(tb__ "0|0|
S0S3S15S79S34U0A1S33S2fA3A1S2A3"). Proof. vmr. Qed.
Lemma XIm_N0 : ltac2:(tb__ "0|2|
S0S7SfA1S5bS7aS2S34U0M0A1M1S33S2fS30A5S6fG0ScS63S2fA2A2A2S8SfS76S2G1S33S5fS63S19S64S2fA4S30A5A2A3"). Proof. vmr. Qed.
