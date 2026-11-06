(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "list"; "option"; "Some"; "pair"; "prod"; "false"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ss_next"; "swf"; "sprop"; "ss_facts"; "SLit"; "sobj"; "ss_lenient"; "reg_sv"; "SVar"; "sprop_eqb"; "SAlu"; "sprop_below"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "sD_of"; "DEPE"; "CASX"; "leaves_at"; "BIGX"; "F_typ"; "PSE"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "OFF_PUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVN"; "VFN"; "rd_okG"; "BIGF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cN1"; "ED_N1_1"; "ED_N1_2"; "ED_N1_3"; "C2_N1_1"; "C2_N1_2"; "C2_N1_3"; "P0_N1"; "CD_N1"; "Ebg_N1"; "Erc_N1"; "PMID_N1"; "RD_N1_1"; "RD_N1_2"; "RD_N1_3"; "S1c_N1_1"; "S1c_N1_2"; "S1c_N1_3"; "exits1_N1"; "run3_N1"; "TD_N1_1"; "TD_N1_2"; "TD_N1_3"; "run1_N1"; "run2_N1_1"; "run2_N1_2"; "run2_N1_3"; "EfD_N1_1"; "EfD_N1_2"; "EfD_N1_3"; "Eps_N1"; "TDr_N1_1"; "TDr_N1_2"; "TDr_N1_3"; "W_N1"; "st_N1"; "run4_N1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "RCYE"; "Erc_of"; "small_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "P0_g"; "XIg"; "sa_g"; "FACTSg"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"].
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

Definition W_N1 : list ulink := Wcan 1.
Definition st_N1 : ustop := UStopLe.
Definition P0_N1 : axst := ltac2:(tb__ "0|0|
S77S6S5aS5bS9S19A1S30A5").

Definition run1_N1 : list leafA := ltac2:(tb__ "0|0|
S5dS21S8S11S24S9S11A1A3S3fA3").

Definition S1c_N1_1 : axst := ltac2:(tb__ "0|0|
S29S5eU0S4fA2S17S3S3fA1A1Z1A3").
Definition C2_N1_1 : axst := C2_of S1c_N1_1.
Definition run2_N1_1 : list leafA := ltac2:(tb__ "0|0|
S5dS21S8S11S23S9S11A1A3S3cA3").
Definition EfD_N1_1 : axst := leaf 0 run2_N1_1.
Definition ED_N1_1 : axst := ED_of EfD_N1_1.
Definition RD_N1_1 : list sobj := RD_of ED_N1_1 1.
Definition TD_N1_1 : axst := TD_of ED_N1_1 1.
Definition TDr_N1_1 : axst := TDr_of TD_N1_1.
Definition S1c_N1_2 : axst := ltac2:(tb__ "0|0|
S29S5eU0S4fA2S17S3S3fA1A1Z2A3").
Definition C2_N1_2 : axst := C2_of S1c_N1_2.
Definition run2_N1_2 : list leafA := ltac2:(tb__ "0|0|
S5dS21S8S11S23S9S11A1A3S3dA3").
Definition EfD_N1_2 : axst := leaf 0 run2_N1_2.
Definition ED_N1_2 : axst := ED_of EfD_N1_2.
Definition RD_N1_2 : list sobj := RD_of ED_N1_2 2.
Definition TD_N1_2 : axst := TD_of ED_N1_2 2.
Definition TDr_N1_2 : axst := TDr_of TD_N1_2.
Definition S1c_N1_3 : axst := ltac2:(tb__ "0|0|
S29S5eU0S4fA2S17S3S3fA1A1Z3A3").
Definition C2_N1_3 : axst := C2_of S1c_N1_3.
Definition run2_N1_3 : list leafA := ltac2:(tb__ "0|0|
S5dS21S8S11S23S9S11A1A3S3eA3").
Definition EfD_N1_3 : axst := leaf 0 run2_N1_3.
Definition ED_N1_3 : axst := ED_of EfD_N1_3.
Definition RD_N1_3 : list sobj := RD_of ED_N1_3 3.
Definition TD_N1_3 : axst := TD_of ED_N1_3 3.
Definition TDr_N1_3 : axst := TDr_of TD_N1_3.
Definition exits1_N1 : list axst := ltac2:(tb__ "0|0|
S8S2S47S8S2S48S8S2S49S9S2A1A3A3A3").

Definition CD_N1 : axst := CD_of TDr_N1_1.
Definition run3_N1 : list leafA := ltac2:(tb__ "0|0|
S5dS21S8S11S28S8S11S26S9S11A1A3A3S40A3").
Definition Eps_N1 : axst := leaf 0 run3_N1.
Definition Ebg_N1 : axst := leaf 1 run3_N1.
Definition run4_N1 : list leafA := ltac2:(tb__ "0|0|
S5dS21S8S11S6bS9S11A1A3S41A3").
Definition Erc_N1 : axst := ltac2:(tb__ "0|0|
S6cS5eU0S5cA2S17S3S41A1A1A2").

Definition PMID_N1 : axst := ltac2:(tb__ "0|0|
S7fS6S5aS5bS9S19A1S30A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_N1 : ltac2:(tb__ "0|0|
S0S7S66S37S14S3S3fA1A1A2S6A3"). Proof. vmr. Qed.
Lemma Cert1_N1 : ltac2:(tb__ "0|0|
S0S7S61S38S21S8S11S24S9S11A1A3S37S8S2S3fS9S2A1A3S4aA6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_N1 exits1_N1 run1_N1); [unfold run1_N1, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_N1 : ltac2:(tb__ "0|2|
S0S7S62S38S21S8S11S24S9S11A1A3S37S8S5fS60S3fZ1S18Z0M0A1M1A3S9S5fA1A3S67S2S5fS2S60R1G0G1A3LE;S4aA4A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_N1 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_N1) run1_N1); [unfold run1_N1, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_N1_1 : ltac2:(tb__ "0|4|
S0SbSeSaSeS13S13A2M0A1M1SaS16A1M2A2M3A1S68S3S47A1S3S3cA1A2ScG3SdG1G2S8G0SdS13S13S2cS2dA4S9G0A1A3S27A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_N1_1 : ltac2:(tb__ "0|1|
S1S0S7S15S3S3cA1M0A1S6A3S1S0S12S14G0A1S14S3S47A1A1A3S0S7S1aG0A1SfA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_N1_1 : ltac2:(tb__ "0|0|
S0S7S66S37S14S3S3cA1A1A2S6A3"). Proof. vmr. Qed.
Lemma EQ2_N1_1 : ltac2:(tb__ "0|0|
S0S2S5S47S3S3cA1A2S3cA3"). Proof. vmr. Qed.
Lemma RUN2_N1_1 : ltac2:(tb__ "0|0|
S0SaS4A1S5dS21S8S11S23S9S11A1A3S3cA3S50A3"). Proof. unfold run2_N1_1; reflexivity. Qed.
Lemma L2_N1_1 : ltac2:(tb__ "0|0|
S1S0S7S25S50S8S11S23S9S11A1A3A2S6A3S0S2S5eU0S50A2S53A3A2"). Proof. Time (split; [vmr | unfold EfD_N1_1; reflexivity]). Qed.
Lemma AXD_N1_1 : ltac2:(tb__ "0|0|
S0SbS2A1S65S53S2aA2ScS2S39A2A3"). Proof. Time vmr. Qed.
Lemma HeD_N1_1 : ltac2:(tb__ "0|2|
S0SbSaS19A1M0A1S70S39S63Z1M1A1S22S39G1A2A3ScG0S44A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_N1_1 : ltac2:(tb__ "0|1|
S0S7S6fS39S63Z1M0A1S22S39G0A2S44S8S2S64G0A1S9S2A1A3A5S6A3"). Proof. Time vmr. Qed.
Lemma HTD_N1_1 : ltac2:(tb__ "0|1|
S0S2S4cS6eS71S22S39Z1M0A2S63G0A1S64G0A1S39S44A5S17S3S39A1A1A2A3").
Proof. unfold TD_N1_1, TD_of, RD_N1_1; reflexivity. Qed.
Lemma DCHK_N1_1 : ltac2:(tb__ "0|2|
S0S7S72U1M0S31S2fG0A2Z1M1S39S4cS22S39G1A2S44A7S6A3"). Proof. Time vmr. Qed.
Lemma AXDr_N1_1 : ltac2:(tb__ "0|0|
S0SbS2A1S65S4cS2bA2ScS2S57A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_N1_1 : ltac2:(tb__ "0|0|
S0S7S73S57S40A2S6A3"). Proof. Time vmr. Qed.
Lemma D2_N1_2 : ltac2:(tb__ "0|4|
S0SbSeSaSeS13S13A2M0A1M1SaS16A1M2A2M3A1S68S3S48A1S3S3dA1A2ScG3SdG1G2S8G0SdS13S13S2cS2dA4S9G0A1A3S27A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_N1_2 : ltac2:(tb__ "0|1|
S1S0S7S15S3S3dA1M0A1S6A3S1S0S12S14G0A1S14S3S48A1A1A3S0S7S1aG0A1SfA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_N1_2 : ltac2:(tb__ "0|0|
S0S7S66S37S14S3S3dA1A1A2S6A3"). Proof. vmr. Qed.
Lemma EQ2_N1_2 : ltac2:(tb__ "0|0|
S0S2S5S48S3S3dA1A2S3dA3"). Proof. vmr. Qed.
Lemma RUN2_N1_2 : ltac2:(tb__ "0|0|
S0SaS4A1S5dS21S8S11S23S9S11A1A3S3dA3S51A3"). Proof. unfold run2_N1_2; reflexivity. Qed.
Lemma L2_N1_2 : ltac2:(tb__ "0|0|
S1S0S7S25S51S8S11S23S9S11A1A3A2S6A3S0S2S5eU0S51A2S54A3A2"). Proof. Time (split; [vmr | unfold EfD_N1_2; reflexivity]). Qed.
Lemma AXD_N1_2 : ltac2:(tb__ "0|0|
S0SbS2A1S65S54S2aA2ScS2S3aA2A3"). Proof. Time vmr. Qed.
Lemma HeD_N1_2 : ltac2:(tb__ "0|2|
S0SbSaS19A1M0A1S70S3aS63Z2M1A1S22S3aG1A2A3ScG0S45A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_N1_2 : ltac2:(tb__ "0|1|
S0S7S6fS3aS63Z2M0A1S22S3aG0A2S45S8S2S64G0A1S9S2A1A3A5S6A3"). Proof. Time vmr. Qed.
Lemma HTD_N1_2 : ltac2:(tb__ "0|1|
S0S2S4dS6eS71S22S3aZ2M0A2S63G0A1S64G0A1S3aS45A5S17S3S3aA1A1A2A3").
Proof. unfold TD_N1_2, TD_of, RD_N1_2; reflexivity. Qed.
Lemma DCHK_N1_2 : ltac2:(tb__ "0|2|
S0S7S72U1M0S31S2fG0A2Z2M1S3aS4dS22S3aG1A2S45A7S6A3"). Proof. Time vmr. Qed.
Lemma AXDr_N1_2 : ltac2:(tb__ "0|0|
S0SbS2A1S65S4dS2bA2ScS2S58A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_N1_2 : ltac2:(tb__ "0|0|
S0S7S73S58S40A2S6A3"). Proof. Time vmr. Qed.
Lemma D2_N1_3 : ltac2:(tb__ "0|4|
S0SbSeSaSeS13S13A2M0A1M1SaS16A1M2A2M3A1S68S3S49A1S3S3eA1A2ScG3SdG1G2S8G0SdS13S13S2cS2dA4S9G0A1A3S27A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_N1_3 : ltac2:(tb__ "0|1|
S1S0S7S15S3S3eA1M0A1S6A3S1S0S12S14G0A1S14S3S49A1A1A3S0S7S1aG0A1SfA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_N1_3 : ltac2:(tb__ "0|0|
S0S7S66S37S14S3S3eA1A1A2S6A3"). Proof. vmr. Qed.
Lemma EQ2_N1_3 : ltac2:(tb__ "0|0|
S0S2S5S49S3S3eA1A2S3eA3"). Proof. vmr. Qed.
Lemma RUN2_N1_3 : ltac2:(tb__ "0|0|
S0SaS4A1S5dS21S8S11S23S9S11A1A3S3eA3S52A3"). Proof. unfold run2_N1_3; reflexivity. Qed.
Lemma L2_N1_3 : ltac2:(tb__ "0|0|
S1S0S7S25S52S8S11S23S9S11A1A3A2S6A3S0S2S5eU0S52A2S55A3A2"). Proof. Time (split; [vmr | unfold EfD_N1_3; reflexivity]). Qed.
Lemma AXD_N1_3 : ltac2:(tb__ "0|0|
S0SbS2A1S65S55S2aA2ScS2S3bA2A3"). Proof. Time vmr. Qed.
Lemma HeD_N1_3 : ltac2:(tb__ "0|2|
S0SbSaS19A1M0A1S70S3bS63Z3M1A1S22S3bG1A2A3ScG0S46A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_N1_3 : ltac2:(tb__ "0|1|
S0S7S6fS3bS63Z3M0A1S22S3bG0A2S46S8S2S64G0A1S9S2A1A3A5S6A3"). Proof. Time vmr. Qed.
Lemma HTD_N1_3 : ltac2:(tb__ "0|1|
S0S2S4eS6eS71S22S3bZ3M0A2S63G0A1S64G0A1S3bS46A5S17S3S3bA1A1A2A3").
Proof. unfold TD_N1_3, TD_of, RD_N1_3; reflexivity. Qed.
Lemma DCHK_N1_3 : ltac2:(tb__ "0|2|
S0S7S72U1M0S31S2fG0A2Z3M1S3bS4eS22S3bG1A2S46A7S6A3"). Proof. Time vmr. Qed.
Lemma AXDr_N1_3 : ltac2:(tb__ "0|0|
S0SbS2A1S65S4eS2bA2ScS2S59A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_N1_3 : ltac2:(tb__ "0|0|
S0S7S73S59S40A2S6A3"). Proof. Time vmr. Qed.
Lemma RUN3_N1 : ltac2:(tb__ "0|0|
S0SaS4A1S5dS21S8S11S28S8S11S26S9S11A1A3A3S40A3S4bA3"). Proof. unfold run3_N1; reflexivity. Qed.
Lemma L3_N1 : ltac2:(tb__ "0|0|
S1S0S7S25S4bS8S11S28S8S11S26S9S11A1A3A3A2S6A3S1S0S2S5eU0S4bA2S56A3S0S2S5eU1S4bA2S41A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_N1 | unfold Ebg_N1]; reflexivity]). Qed.
Lemma NX3_N1 : ltac2:(tb__ "0|1|
S1S0S7S66S37S14S3S40A1M0A1A2S6A3S0S7S1aG0A1SfA3A2"). Proof. split; vmr. Qed.

Lemma SMF_N1 : ltac2:(tb__ "0|0|
S0S7S74S16S1dS6dA1S17S3S56A1A1A3S6A3"). Proof. vmr. Qed.
Lemma BGF_N1 : ltac2:(tb__ "0|1|
S1S0S7S74S16S1dS87A1S17S3S42A1A1M0A3S6A3S0S7S74S16S1dS32A1G0A3S6A3A2"). Proof. split; vmr. Qed.
Lemma NXB_N1 : ltac2:(tb__ "0|0|
S0S7S66S37S14S3S41A1A1A2S6A3"). Proof. vmr. Qed.
Lemma CertR_N1 : ltac2:(tb__ "0|1|
S0S7S61S38S21S8S11S6bS9S11A1A3S37S8S2S41S9S2A1M0A3S8S2S42G0A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [RCYE] GW Ebg_N1 [Erc_N1] run4_N1); [unfold run4_N1, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECertR_N1 : ltac2:(tb__ "0|3|
S0S7S62S38S21S8S11S6bS9S11A1A3S37S8S5fS60S41Z1S18Z0M0A1M1A3S9S5fA1M2A3S8S5fS60S42G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [RCYE] GW (mkVNA Ebg_N1 1 (SLit 0)) [mkVNA Erc_N1 0 (SLit 0)] run4_N1); [unfold run4_N1, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma LEAF_N1 : ltac2:(tb__ "0|2|
S1S0S11S20S3S42A1M0A1S6bA3S1S0S13S1bG0Z1A2S18Z408d8A1A3S1S0S13S1bG0Z2A2S1eS76S1cPaA1S18S2eA1A3M1A3S1S0S13S1bG0ZaA2G1A3S1S0S13S1bG0ZbA2S1eS76S1cPcA1S18N10A1A3A3S0S7S1aG0A1SfA3A2A2A2A2A2").
Proof. split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]. Qed.

Lemma Wa_N1 : ltac2:(tb__ "0|0|
S0S7S15S79S34U1A1S33A2A1S6A3"). Proof. vmr. Qed.
Lemma Da_N1 : ltac2:(tb__ "0|5|
S0SbSeSaSeS13S13A2M0A1M1SaS16A1M2A2M3A1S68S3S36S35S34U1A1M4S33A3A1S79G4S33A2A2ScG3SdG1G2S8G0SdS13S13S1cP18A1S18S86A1A4S9G0A1A3S9S16A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_N1 : ltac2:(tb__ "0|0|
S0S7S15S7bS34U1A1S33S2fA3A1S6A3"). Proof. vmr. Qed.
Lemma Wc_N1 : ltac2:(tb__ "0|0|
S0S7S15S7cS34U1A1S33S2fA3A1S6A3"). Proof. vmr. Qed.
Lemma Wd_N1 : ltac2:(tb__ "0|0|
S0S7S15S7dS34U1A1S33S2fA3A1S6A3"). Proof. vmr. Qed.
Lemma Fb_N1 : ltac2:(tb__ "0|0|
S0S7S75S16S1fS85A1S7aS6S34U1A1S33S30A4A3S6A3"). Proof. vmr. Qed.
Lemma XI_N1 : ltac2:(tb__ "0|2|
S0SbS2A1S65S7eS6S34U1M0A1M1S33S2fS30A5S78G0S10S69S2fA2A2A2ScS2S77S6G1S33S67S69S19S6aS2fA4S30A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_N1 : ltac2:(tb__ "0|0|
S0S7S66S37S14S3S43A1A1A2S6A3"). Proof. vmr. Qed.
Definition Cert1m_N1__runs : ltac2:(tb__ "0|0|
SaSbSaS4A1A1A1") := ltac2:(tb__ "0|0|
S84S38S21S8S11S24S9S11A1A3S8S2S43S9S2A1A3A4").
Lemma Cert1m_N1 : ltac2:(tb__ "0|0|
S0S7S61S38S21S8S11S24S9S11A1A3S37S8S2S43S9S2A1A3S4aA6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_N1] exits1_N1 Cert1m_N1__runs); [unfold Cert1m_N1__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_N1 : ltac2:(tb__ "0|2|
S0S7S62S38S21S8S11S24S9S11A1A3S37S8S5fS60S43Z1S18Z0M0A1M1A3S9S5fA1A3S67S2S5fS2S60R1G0G1A3LE;S4aA4A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_N1 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_N1) Cert1m_N1__runs); [unfold Cert1m_N1__runs; reflexivity | vmr]. Qed.
Lemma Wbm_N1 : ltac2:(tb__ "0|0|
S0S7S15S80S34U1A1S33S2fA3A1S6A3"). Proof. vmr. Qed.
Lemma Wcm_N1 : ltac2:(tb__ "0|0|
S0S7S15S81S34U1A1S33S2fA3A1S6A3"). Proof. vmr. Qed.
Lemma Wdm_N1 : ltac2:(tb__ "0|0|
S0S7S15S82S34U1A1S33S2fA3A1S6A3"). Proof. vmr. Qed.
Lemma XIm_N1 : ltac2:(tb__ "0|2|
S0SbS2A1S65S83S6S34U1M0A1M1S33S2fS30A5S78G0S10S69S2fA2A2A2ScS2S7fS6G1S33S67S69S19S6aS2fA4S30A5A2A3"). Proof. vmr. Qed.
