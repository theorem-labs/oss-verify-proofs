(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "list"; "option"; "Some"; "false"; "pair"; "prod"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ss_next"; "swf"; "sprop"; "SLit"; "ss_facts"; "sobj"; "reg_sv"; "ss_lenient"; "SVar"; "sprop_eqb"; "SAlu"; "sprop_below"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "sD_of"; "CASX"; "DEPE"; "BIGX"; "PSE"; "leaves_at"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "OFF_PUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVN"; "VFN"; "rd_okG"; "BIGF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cLN0"; "ED_LN0_1"; "ED_LN0_2"; "C2_LN0_1"; "C2_LN0_2"; "Ebg_LN0"; "P0_LN0"; "CD_LN0"; "Erc_LN0"; "PMID_LN0"; "RD_LN0_1"; "RD_LN0_2"; "S1c_LN0_1"; "S1c_LN0_2"; "exits1_LN0"; "run3_LN0"; "TD_LN0_1"; "TD_LN0_2"; "run2_LN0_1"; "run2_LN0_2"; "EfD_LN0_1"; "EfD_LN0_2"; "Eps_LN0"; "TDr_LN0_1"; "TDr_LN0_2"; "W_LN0"; "run1_LN0"; "st_LN0"; "run4_LN0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "RCYE"; "Erc_of"; "small_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "P0_g"; "XIg"; "sa_g"; "FACTSg"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.

Definition W_LN0 : list ulink := Wcan 0.
Definition st_LN0 : ustop := UStopLe.
Definition P0_LN0 : axst := ltac2:(tb__ "0|0|
S6eSfS51S53SaS19A1S30A5").

Definition run1_LN0 : list leafA := ltac2:(tb__ "0|0|
S59S21S9S2S23SaS2A1A3S3eA3").

Definition S1c_LN0_1 : axst := ltac2:(tb__ "0|0|
S29S5aU0S52A2S18S5S3eA1A1Z1A3").
Definition C2_LN0_1 : axst := C2_of S1c_LN0_1.
Definition run2_LN0_1 : list leafA := ltac2:(tb__ "0|0|
S59S21S9S2S24SaS2A1A3S3bA3").
Definition EfD_LN0_1 : axst := leaf 0 run2_LN0_1.
Definition ED_LN0_1 : axst := ED_of EfD_LN0_1.
Definition RD_LN0_1 : list sobj := RD_of ED_LN0_1 1.
Definition TD_LN0_1 : axst := TD_of ED_LN0_1 1.
Definition TDr_LN0_1 : axst := TDr_of TD_LN0_1.
Definition S1c_LN0_2 : axst := ltac2:(tb__ "0|0|
S29S5aU0S52A2S18S5S3eA1A1Z2A3").
Definition C2_LN0_2 : axst := C2_of S1c_LN0_2.
Definition run2_LN0_2 : list leafA := ltac2:(tb__ "0|0|
S59S21S9S2S24SaS2A1A3S3cA3").
Definition EfD_LN0_2 : axst := leaf 0 run2_LN0_2.
Definition ED_LN0_2 : axst := ED_of EfD_LN0_2.
Definition RD_LN0_2 : list sobj := RD_of ED_LN0_2 2.
Definition TD_LN0_2 : axst := TD_of ED_LN0_2 2.
Definition TDr_LN0_2 : axst := TDr_of TD_LN0_2.
Definition exits1_LN0 : list axst := ltac2:(tb__ "0|0|
S9S4S44S9S4S45SaS4A1A3A3").

Definition CD_LN0 : axst := CD_of TDr_LN0_1.
Definition run3_LN0 : list leafA := ltac2:(tb__ "0|0|
S59S21S9S2S26S9S2S25SaS2A1A3A3S3fA3").
Definition Eps_LN0 : axst := leaf 0 run3_LN0.
Definition Ebg_LN0 : axst := leaf 1 run3_LN0.
Definition run4_LN0 : list leafA := ltac2:(tb__ "0|0|
S59S21S9S2S62SaS2A1A3S3dA3").
Definition Erc_LN0 : axst := ltac2:(tb__ "0|0|
S63S5aU0S54A2S18S5S3dA1A1A2").

Definition PMID_LN0 : axst := ltac2:(tb__ "0|0|
S76SfS51S53SaS19A1S30A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_LN0 : ltac2:(tb__ "0|0|
S0S8S5eS37S14S5S3eA1A1A2SbA3"). Proof. vmr. Qed.
Lemma Cert1_LN0 : ltac2:(tb__ "0|0|
S0S8S57S38S21S9S2S23SaS2A1A3S37S9S4S3eSaS4A1A3S46A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_LN0 exits1_LN0 run1_LN0); [unfold run1_LN0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_LN0 : ltac2:(tb__ "0|2|
S0S8S58S38S21S9S2S23SaS2A1A3S37S9S55S56S3eZ1S17Z0M0A1M1A3SaS55A1A3S5fS4S55S4S56R1G0G1A3LE;S46A4A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_LN0 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_LN0) run1_LN0); [unfold run1_LN0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_LN0_1 : ltac2:(tb__ "0|4|
S0SdS11ScS11S13S13A2M0A1M1ScS16A1M2A2M3A1S65S5S44A1S5S3bA1A2SeG3S10G1G2S9G0S10S13S13S2cS2dA4SaG0A1A3S28A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LN0_1 : ltac2:(tb__ "0|1|
S1S0S8S15S5S3bA1M0A1SbA3S1S0S3S14G0A1S14S5S44A1A1A3S0S8S1bG0A1SfA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LN0_1 : ltac2:(tb__ "0|0|
S0S8S5eS37S14S5S3bA1A1A2SbA3"). Proof. vmr. Qed.
Lemma EQ2_LN0_1 : ltac2:(tb__ "0|0|
S0S4S7S44S5S3bA1A2S3bA3"). Proof. vmr. Qed.
Lemma RUN2_LN0_1 : ltac2:(tb__ "0|0|
S0ScS6A1S59S21S9S2S24SaS2A1A3S3bA3S4aA3"). Proof. unfold run2_LN0_1; reflexivity. Qed.
Lemma L2_LN0_1 : ltac2:(tb__ "0|0|
S1S0S8S27S4aS9S2S24SaS2A1A3A2SbA3S0S4S5aU0S4aA2S4cA3A2"). Proof. Time (split; [vmr | unfold EfD_LN0_1; reflexivity]). Qed.
Lemma AXD_LN0_1 : ltac2:(tb__ "0|0|
S0SdS4A1S5bS4cS2aA2SeS4S39A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LN0_1 : ltac2:(tb__ "0|2|
S0SdScS19A1M0A1S6bS39S5cZ1M1A1S22S39G1A2A3SeG0S42A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LN0_1 : ltac2:(tb__ "0|1|
S0S8S6aS39S5cZ1M0A1S22S39G0A2S42S9S4S5dG0A1SaS4A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma HTD_LN0_1 : ltac2:(tb__ "0|1|
S0S4S48S69S6cS22S39Z1M0A2S5cG0A1S5dG0A1S39S42A5S18S5S39A1A1A2A3").
Proof. unfold TD_LN0_1, TD_of, RD_LN0_1; reflexivity. Qed.
Lemma DCHK_LN0_1 : ltac2:(tb__ "0|2|
S0S8S6dU0M0S31S2fG0A2Z1M1S39S48S22S39G1A2S42A7SbA3"). Proof. Time vmr. Qed.
Lemma AXDr_LN0_1 : ltac2:(tb__ "0|0|
S0SdS4A1S5bS48S2bA2SeS4S4fA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LN0_1 : ltac2:(tb__ "0|0|
S0S8S7bS4fS3fA2SbA3"). Proof. Time vmr. Qed.
Lemma D2_LN0_2 : ltac2:(tb__ "0|4|
S0SdS11ScS11S13S13A2M0A1M1ScS16A1M2A2M3A1S65S5S45A1S5S3cA1A2SeG3S10G1G2S9G0S10S13S13S2cS2dA4SaG0A1A3S28A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LN0_2 : ltac2:(tb__ "0|1|
S1S0S8S15S5S3cA1M0A1SbA3S1S0S3S14G0A1S14S5S45A1A1A3S0S8S1bG0A1SfA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LN0_2 : ltac2:(tb__ "0|0|
S0S8S5eS37S14S5S3cA1A1A2SbA3"). Proof. vmr. Qed.
Lemma EQ2_LN0_2 : ltac2:(tb__ "0|0|
S0S4S7S45S5S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_LN0_2 : ltac2:(tb__ "0|0|
S0ScS6A1S59S21S9S2S24SaS2A1A3S3cA3S4bA3"). Proof. unfold run2_LN0_2; reflexivity. Qed.
Lemma L2_LN0_2 : ltac2:(tb__ "0|0|
S1S0S8S27S4bS9S2S24SaS2A1A3A2SbA3S0S4S5aU0S4bA2S4dA3A2"). Proof. Time (split; [vmr | unfold EfD_LN0_2; reflexivity]). Qed.
Lemma AXD_LN0_2 : ltac2:(tb__ "0|0|
S0SdS4A1S5bS4dS2aA2SeS4S3aA2A3"). Proof. Time vmr. Qed.
Lemma HeD_LN0_2 : ltac2:(tb__ "0|2|
S0SdScS19A1M0A1S6bS3aS5cZ2M1A1S22S3aG1A2A3SeG0S43A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LN0_2 : ltac2:(tb__ "0|1|
S0S8S6aS3aS5cZ2M0A1S22S3aG0A2S43S9S4S5dG0A1SaS4A1A3A5SbA3"). Proof. Time vmr. Qed.
Lemma HTD_LN0_2 : ltac2:(tb__ "0|1|
S0S4S49S69S6cS22S3aZ2M0A2S5cG0A1S5dG0A1S3aS43A5S18S5S3aA1A1A2A3").
Proof. unfold TD_LN0_2, TD_of, RD_LN0_2; reflexivity. Qed.
Lemma DCHK_LN0_2 : ltac2:(tb__ "0|2|
S0S8S6dU0M0S31S2fG0A2Z2M1S3aS49S22S3aG1A2S43A7SbA3"). Proof. Time vmr. Qed.
Lemma AXDr_LN0_2 : ltac2:(tb__ "0|0|
S0SdS4A1S5bS49S2bA2SeS4S50A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LN0_2 : ltac2:(tb__ "0|0|
S0S8S7bS50S3fA2SbA3"). Proof. Time vmr. Qed.
Lemma RUN3_LN0 : ltac2:(tb__ "0|0|
S0ScS6A1S59S21S9S2S26S9S2S25SaS2A1A3A3S3fA3S47A3"). Proof. unfold run3_LN0; reflexivity. Qed.
Lemma L3_LN0 : ltac2:(tb__ "0|0|
S1S0S8S27S47S9S2S26S9S2S25SaS2A1A3A3A2SbA3S1S0S4S5aU0S47A2S4eA3S0S4S5aU1S47A2S3dA3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LN0 | unfold Ebg_LN0]; reflexivity]). Qed.
Lemma NX3_LN0 : ltac2:(tb__ "0|1|
S1S0S8S5eS37S14S5S3fA1M0A1A2SbA3S0S8S1bG0A1SfA3A2"). Proof. split; vmr. Qed.

Lemma SMF_LN0 : ltac2:(tb__ "0|0|
S0S8S66S16S1dS64A1S18S5S4eA1A1A3SbA3"). Proof. vmr. Qed.
Lemma BGF_LN0 : ltac2:(tb__ "0|1|
S1S0S8S66S16S1dS7fA1S18S5S40A1A1M0A3SbA3S0S8S66S16S1dS32A1G0A3SbA3A2"). Proof. split; vmr. Qed.
Lemma NXB_LN0 : ltac2:(tb__ "0|0|
S0S8S5eS37S14S5S3dA1A1A2SbA3"). Proof. vmr. Qed.
Lemma CertR_LN0 : ltac2:(tb__ "0|1|
S0S8S57S38S21S9S2S62SaS2A1A3S37S9S4S3dSaS4A1M0A3S9S4S40G0A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [RCYE] GW Ebg_LN0 [Erc_LN0] run4_LN0); [unfold run4_LN0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECertR_LN0 : ltac2:(tb__ "0|3|
S0S8S58S38S21S9S2S62SaS2A1A3S37S9S55S56S3dZ1S17Z0M0A1M1A3SaS55A1M2A3S9S55S56S40G0G1A3G2A3A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [RCYE] GW (mkVNA Ebg_LN0 1 (SLit 0)) [mkVNA Erc_LN0 0 (SLit 0)] run4_LN0); [unfold run4_LN0, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma LEAF_LN0 : ltac2:(tb__ "0|2|
S1S0S2S20S5S40A1M0A1S62A3S1S0S13S1aG0Z1A2S17Z408d8A1A3S1S0S13S1aG0Z2A2S1eS68S1cPaA1S17S2eA1A3M1A3S1S0S13S1aG0ZaA2G1A3S1S0S13S1aG0ZbA2S1eS68S1cPcA1S17N10A1A3A3S0S8S1bG0A1SfA3A2A2A2A2A2").
Proof. split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]. Qed.

Lemma Wa_LN0 : ltac2:(tb__ "0|0|
S0S8S15S70S34U0A1S33A2A1SbA3"). Proof. vmr. Qed.
Lemma Da_LN0 : ltac2:(tb__ "0|5|
S0SdS11ScS11S13S13A2M0A1M1ScS16A1M2A2M3A1S65S5S36S35S34U0A1M4S33A3A1S70G4S33A2A2SeG3S10G1G2S9G0S10S13S13S1cP18A1S17S7eA1A4SaG0A1A3SaS16A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LN0 : ltac2:(tb__ "0|0|
S0S8S15S72S34U0A1S33S2fA3A1SbA3"). Proof. vmr. Qed.
Lemma Wc_LN0 : ltac2:(tb__ "0|0|
S0S8S15S73S34U0A1S33S2fA3A1SbA3"). Proof. vmr. Qed.
Lemma Wd_LN0 : ltac2:(tb__ "0|0|
S0S8S15S74S34U0A1S33S2fA3A1SbA3"). Proof. vmr. Qed.
Lemma Fb_LN0 : ltac2:(tb__ "0|0|
S0S8S67S16S1fS7dA1S71SfS34U0A1S33S30A4A3SbA3"). Proof. vmr. Qed.
Lemma XI_LN0 : ltac2:(tb__ "0|2|
S0SdS4A1S5bS75SfS34U0M0A1M1S33S2fS30A5S6fG0S12S60S2fA2A2A2SeS4S6eSfG1S33S5fS60S19S61S2fA4S30A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_LN0 : ltac2:(tb__ "0|0|
S0S8S5eS37S14S5S41A1A1A2SbA3"). Proof. vmr. Qed.
Definition Cert1m_LN0__runs : ltac2:(tb__ "0|0|
ScSdScS6A1A1A1") := ltac2:(tb__ "0|0|
S7cS38S21S9S2S23SaS2A1A3S9S4S41SaS4A1A3A4").
Lemma Cert1m_LN0 : ltac2:(tb__ "0|0|
S0S8S57S38S21S9S2S23SaS2A1A3S37S9S4S41SaS4A1A3S46A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_LN0] exits1_LN0 Cert1m_LN0__runs); [unfold Cert1m_LN0__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_LN0 : ltac2:(tb__ "0|2|
S0S8S58S38S21S9S2S23SaS2A1A3S37S9S55S56S41Z1S17Z0M0A1M1A3SaS55A1A3S5fS4S55S4S56R1G0G1A3LE;S46A4A6SbA3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_LN0 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_LN0) Cert1m_LN0__runs); [unfold Cert1m_LN0__runs; reflexivity | vmr]. Qed.
Lemma Wbm_LN0 : ltac2:(tb__ "0|0|
S0S8S15S77S34U0A1S33S2fA3A1SbA3"). Proof. vmr. Qed.
Lemma Wcm_LN0 : ltac2:(tb__ "0|0|
S0S8S15S78S34U0A1S33S2fA3A1SbA3"). Proof. vmr. Qed.
Lemma Wdm_LN0 : ltac2:(tb__ "0|0|
S0S8S15S79S34U0A1S33S2fA3A1SbA3"). Proof. vmr. Qed.
Lemma XIm_LN0 : ltac2:(tb__ "0|2|
S0SdS4A1S5bS7aSfS34U0M0A1M1S33S2fS30A5S6fG0S12S60S2fA2A2A2SeS4S76SfG1S33S5fS60S19S61S2fA4S30A5A2A3"). Proof. vmr. Qed.
