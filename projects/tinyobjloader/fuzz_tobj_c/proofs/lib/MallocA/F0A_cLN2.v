(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "nil"; "list"; "option"; "Some"; "false"; "pair"; "prod"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ss_next"; "ss_facts"; "swf"; "sprop"; "sobj"; "SLit"; "ss_lenient"; "reg_sv"; "SVar"; "sprop_eqb"; "SAlu"; "sprop_below"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "FUELF"; "sD_of"; "DEPE"; "CASX"; "leaves_at"; "F_typ"; "S1c_of"; "XD"; "XDr"; "casx"; "vH3"; "BIGX"; "PSE"; "OFF_PUT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.F0A_instokC"; "NVN"; "VFN"; "rd_okG"; "BIGF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states"; "PreD"; "PostD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "runA"; "leaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN2"; "ED_LN2_1"; "ED_LN2_2"; "ED_LN2_3"; "ED_LN2_4"; "P0_LN2"; "C2_LN2_1"; "C2_LN2_2"; "C2_LN2_3"; "C2_LN2_4"; "CD_LN2"; "Ebg_LN2"; "Erc_LN2"; "PMID_LN2"; "RD_LN2_1"; "RD_LN2_2"; "RD_LN2_3"; "RD_LN2_4"; "S1c_LN2_1"; "S1c_LN2_2"; "S1c_LN2_3"; "S1c_LN2_4"; "exits1_LN2"; "run1_LN2"; "run3_LN2"; "TD_LN2_1"; "TD_LN2_2"; "TD_LN2_3"; "TD_LN2_4"; "run2_LN2_1"; "run2_LN2_2"; "run2_LN2_3"; "run2_LN2_4"; "EfD_LN2_1"; "EfD_LN2_2"; "EfD_LN2_3"; "EfD_LN2_4"; "Eps_LN2"; "TDr_LN2_1"; "TDr_LN2_2"; "TDr_LN2_3"; "TDr_LN2_4"; "W_LN2"; "st_LN2"; "run4_LN2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_depotG"; "dchkbG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln"; "RCYE"; "Erc_of"; "small_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instG"; "P0_g"; "XIg"; "sa_g"; "FACTSg"; "sb_g"; "sc_g"; "sd_g"; "se_g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"].
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

Definition W_LN2 : list ulink := Wcan 2.
Definition st_LN2 : ustop := UStopLe.
Definition P0_LN2 : axst := ltac2:(tb__ "0|0|
S7fSdS67S68S9S18A1S30A5").

Definition run1_LN2 : list leafA := ltac2:(tb__ "0|0|
S3bS21S7S11S24S9S11A1A3S42A3").

Definition S1c_LN2_1 : axst := ltac2:(tb__ "0|0|
S27S3cU0S54A2S15S3S42A1A1Z1A3").
Definition C2_LN2_1 : axst := C2_of S1c_LN2_1.
Definition run2_LN2_1 : list leafA := ltac2:(tb__ "0|0|
S3bS21S7S11S23S9S11A1A3S43A3").
Definition EfD_LN2_1 : axst := leaf 0 run2_LN2_1.
Definition ED_LN2_1 : axst := ED_of EfD_LN2_1.
Definition RD_LN2_1 : list sobj := RD_of ED_LN2_1 1.
Definition TD_LN2_1 : axst := TD_of ED_LN2_1 1.
Definition TDr_LN2_1 : axst := TDr_of TD_LN2_1.
Definition S1c_LN2_2 : axst := ltac2:(tb__ "0|0|
S27S3cU0S54A2S15S3S42A1A1Z2A3").
Definition C2_LN2_2 : axst := C2_of S1c_LN2_2.
Definition run2_LN2_2 : list leafA := ltac2:(tb__ "0|0|
S3bS21S7S11S23S9S11A1A3S44A3").
Definition EfD_LN2_2 : axst := leaf 0 run2_LN2_2.
Definition ED_LN2_2 : axst := ED_of EfD_LN2_2.
Definition RD_LN2_2 : list sobj := RD_of ED_LN2_2 2.
Definition TD_LN2_2 : axst := TD_of ED_LN2_2 2.
Definition TDr_LN2_2 : axst := TDr_of TD_LN2_2.
Definition S1c_LN2_3 : axst := ltac2:(tb__ "0|0|
S27S3cU0S54A2S15S3S42A1A1Z3A3").
Definition C2_LN2_3 : axst := C2_of S1c_LN2_3.
Definition run2_LN2_3 : list leafA := ltac2:(tb__ "0|0|
S3bS21S7S11S23S9S11A1A3S45A3").
Definition EfD_LN2_3 : axst := leaf 0 run2_LN2_3.
Definition ED_LN2_3 : axst := ED_of EfD_LN2_3.
Definition RD_LN2_3 : list sobj := RD_of ED_LN2_3 3.
Definition TD_LN2_3 : axst := TD_of ED_LN2_3 3.
Definition TDr_LN2_3 : axst := TDr_of TD_LN2_3.
Definition S1c_LN2_4 : axst := ltac2:(tb__ "0|0|
S27S3cU0S54A2S15S3S42A1A1Z4A3").
Definition C2_LN2_4 : axst := C2_of S1c_LN2_4.
Definition run2_LN2_4 : list leafA := ltac2:(tb__ "0|0|
S3bS21S7S11S23S9S11A1A3S46A3").
Definition EfD_LN2_4 : axst := leaf 0 run2_LN2_4.
Definition ED_LN2_4 : axst := ED_of EfD_LN2_4.
Definition RD_LN2_4 : list sobj := RD_of ED_LN2_4 4.
Definition TD_LN2_4 : axst := TD_of ED_LN2_4 4.
Definition TDr_LN2_4 : axst := TDr_of TD_LN2_4.
Definition exits1_LN2 : list axst := ltac2:(tb__ "0|0|
S7S2S4fS7S2S50S7S2S51S7S2S52S9S2A1A3A3A3A3").

Definition CD_LN2 : axst := CD_of TDr_LN2_1.
Definition run3_LN2 : list leafA := ltac2:(tb__ "0|0|
S3bS21S7S11S2dS7S11S2cS9S11A1A3A3S47A3").
Definition Eps_LN2 : axst := leaf 0 run3_LN2.
Definition Ebg_LN2 : axst := leaf 1 run3_LN2.
Definition run4_LN2 : list leafA := ltac2:(tb__ "0|0|
S3bS21S7S11S76S9S11A1A3S48A3").
Definition Erc_LN2 : axst := ltac2:(tb__ "0|0|
S77S3cU0S69A2S15S3S48A1A1A2").

Definition PMID_LN2 : axst := ltac2:(tb__ "0|0|
S87SdS67S68S9S18A1S30A5").

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Lemma NX0_LN2 : ltac2:(tb__ "0|0|
S0S6S6eS33S14S3S42A1A1A2S8A3"). Proof. vmr. Qed.
Lemma Cert1_LN2 : ltac2:(tb__ "0|0|
S0S6S6cS34S21S7S11S24S9S11A1A3S33S7S2S42S9S2A1A3S53A6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [CASX] GW P0_LN2 exits1_LN2 run1_LN2); [unfold run1_LN2, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECert1_LN2 : ltac2:(tb__ "0|2|
S0S6S6dS34S21S7S11S24S9S11A1A3S33S7S6aS6bS42Z1S19Z0M0A1M1A3S9S6aA1A3S70S2S6aS2S6bR1G0G1A3LE;S53A4A6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [CASX] GW (mkVNA P0_LN2 1 (SLit 0)) (map (fun E => mkVNA E 0 (SLit 0)) exits1_LN2) run1_LN2); [unfold run1_LN2, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma D2_LN2_1 : ltac2:(tb__ "0|4|
S0SbSfSaSfS13S13A2M0A1M1SaS17A1M2A2M3A1S6fS3S4fA1S3S43A1A2ScG3SeG1G2S7G0SeS13S13S2aS2bA4S9G0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LN2_1 : ltac2:(tb__ "0|1|
S1S0S6S16S3S43A1M0A1S8A3S1S0S12S14G0A1S14S3S4fA1A1A3S0S6S1aG0A1SdA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LN2_1 : ltac2:(tb__ "0|0|
S0S6S6eS33S14S3S43A1A1A2S8A3"). Proof. vmr. Qed.
Lemma EQ2_LN2_1 : ltac2:(tb__ "0|0|
S0S2S5S4fS3S43A1A2S43A3"). Proof. vmr. Qed.
Lemma RUN2_LN2_1 : ltac2:(tb__ "0|0|
S0SaS4A1S3bS21S7S11S23S9S11A1A3S43A3S5aA3"). Proof. unfold run2_LN2_1; reflexivity. Qed.
Lemma L2_LN2_1 : ltac2:(tb__ "0|0|
S1S0S6S25S5aS7S11S23S9S11A1A3A2S8A3S0S2S3cU0S5aA2S5eA3A2"). Proof. Time (split; [vmr | unfold EfD_LN2_1; reflexivity]). Qed.
Lemma AXD_LN2_1 : ltac2:(tb__ "0|0|
S0SbS2A1S3dS5eS28A2ScS2S3eA2A3"). Proof. Time vmr. Qed.
Lemma HeD_LN2_1 : ltac2:(tb__ "0|2|
S0SbSaS18A1M0A1S73S3eS39Z1M1A1S22S3eG1A2A3ScG0S4bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LN2_1 : ltac2:(tb__ "0|1|
S0S6S72S3eS39Z1M0A1S22S3eG0A2S4bS7S2S3aG0A1S9S2A1A3A5S8A3"). Proof. Time vmr. Qed.
Lemma HTD_LN2_1 : ltac2:(tb__ "0|1|
S0S2S56S71S74S22S3eZ1M0A2S39G0A1S3aG0A1S3eS4bA5S15S3S3eA1A1A2A3").
Proof. unfold TD_LN2_1, TD_of, RD_LN2_1; reflexivity. Qed.
Lemma DCHK_LN2_1 : ltac2:(tb__ "0|2|
S0S6S75U2M0S31S2fG0A2Z1M1S3eS56S22S3eG1A2S4bA7S8A3"). Proof. Time vmr. Qed.
Lemma AXDr_LN2_1 : ltac2:(tb__ "0|0|
S0SbS2A1S3dS56S29A2ScS2S63A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LN2_1 : ltac2:(tb__ "0|0|
S0S6S7bS63S47A2S8A3"). Proof. Time vmr. Qed.
Lemma D2_LN2_2 : ltac2:(tb__ "0|4|
S0SbSfSaSfS13S13A2M0A1M1SaS17A1M2A2M3A1S6fS3S50A1S3S44A1A2ScG3SeG1G2S7G0SeS13S13S2aS2bA4S9G0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LN2_2 : ltac2:(tb__ "0|1|
S1S0S6S16S3S44A1M0A1S8A3S1S0S12S14G0A1S14S3S50A1A1A3S0S6S1aG0A1SdA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LN2_2 : ltac2:(tb__ "0|0|
S0S6S6eS33S14S3S44A1A1A2S8A3"). Proof. vmr. Qed.
Lemma EQ2_LN2_2 : ltac2:(tb__ "0|0|
S0S2S5S50S3S44A1A2S44A3"). Proof. vmr. Qed.
Lemma RUN2_LN2_2 : ltac2:(tb__ "0|0|
S0SaS4A1S3bS21S7S11S23S9S11A1A3S44A3S5bA3"). Proof. unfold run2_LN2_2; reflexivity. Qed.
Lemma L2_LN2_2 : ltac2:(tb__ "0|0|
S1S0S6S25S5bS7S11S23S9S11A1A3A2S8A3S0S2S3cU0S5bA2S5fA3A2"). Proof. Time (split; [vmr | unfold EfD_LN2_2; reflexivity]). Qed.
Lemma AXD_LN2_2 : ltac2:(tb__ "0|0|
S0SbS2A1S3dS5fS28A2ScS2S3fA2A3"). Proof. Time vmr. Qed.
Lemma HeD_LN2_2 : ltac2:(tb__ "0|2|
S0SbSaS18A1M0A1S73S3fS39Z2M1A1S22S3fG1A2A3ScG0S4cA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LN2_2 : ltac2:(tb__ "0|1|
S0S6S72S3fS39Z2M0A1S22S3fG0A2S4cS7S2S3aG0A1S9S2A1A3A5S8A3"). Proof. Time vmr. Qed.
Lemma HTD_LN2_2 : ltac2:(tb__ "0|1|
S0S2S57S71S74S22S3fZ2M0A2S39G0A1S3aG0A1S3fS4cA5S15S3S3fA1A1A2A3").
Proof. unfold TD_LN2_2, TD_of, RD_LN2_2; reflexivity. Qed.
Lemma DCHK_LN2_2 : ltac2:(tb__ "0|2|
S0S6S75U2M0S31S2fG0A2Z2M1S3fS57S22S3fG1A2S4cA7S8A3"). Proof. Time vmr. Qed.
Lemma AXDr_LN2_2 : ltac2:(tb__ "0|0|
S0SbS2A1S3dS57S29A2ScS2S64A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LN2_2 : ltac2:(tb__ "0|0|
S0S6S7bS64S47A2S8A3"). Proof. Time vmr. Qed.
Lemma D2_LN2_3 : ltac2:(tb__ "0|4|
S0SbSfSaSfS13S13A2M0A1M1SaS17A1M2A2M3A1S6fS3S51A1S3S45A1A2ScG3SeG1G2S7G0SeS13S13S2aS2bA4S9G0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LN2_3 : ltac2:(tb__ "0|1|
S1S0S6S16S3S45A1M0A1S8A3S1S0S12S14G0A1S14S3S51A1A1A3S0S6S1aG0A1SdA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LN2_3 : ltac2:(tb__ "0|0|
S0S6S6eS33S14S3S45A1A1A2S8A3"). Proof. vmr. Qed.
Lemma EQ2_LN2_3 : ltac2:(tb__ "0|0|
S0S2S5S51S3S45A1A2S45A3"). Proof. vmr. Qed.
Lemma RUN2_LN2_3 : ltac2:(tb__ "0|0|
S0SaS4A1S3bS21S7S11S23S9S11A1A3S45A3S5cA3"). Proof. unfold run2_LN2_3; reflexivity. Qed.
Lemma L2_LN2_3 : ltac2:(tb__ "0|0|
S1S0S6S25S5cS7S11S23S9S11A1A3A2S8A3S0S2S3cU0S5cA2S60A3A2"). Proof. Time (split; [vmr | unfold EfD_LN2_3; reflexivity]). Qed.
Lemma AXD_LN2_3 : ltac2:(tb__ "0|0|
S0SbS2A1S3dS60S28A2ScS2S40A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LN2_3 : ltac2:(tb__ "0|2|
S0SbSaS18A1M0A1S73S40S39Z3M1A1S22S40G1A2A3ScG0S4dA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LN2_3 : ltac2:(tb__ "0|1|
S0S6S72S40S39Z3M0A1S22S40G0A2S4dS7S2S3aG0A1S9S2A1A3A5S8A3"). Proof. Time vmr. Qed.
Lemma HTD_LN2_3 : ltac2:(tb__ "0|1|
S0S2S58S71S74S22S40Z3M0A2S39G0A1S3aG0A1S40S4dA5S15S3S40A1A1A2A3").
Proof. unfold TD_LN2_3, TD_of, RD_LN2_3; reflexivity. Qed.
Lemma DCHK_LN2_3 : ltac2:(tb__ "0|2|
S0S6S75U2M0S31S2fG0A2Z3M1S40S58S22S40G1A2S4dA7S8A3"). Proof. Time vmr. Qed.
Lemma AXDr_LN2_3 : ltac2:(tb__ "0|0|
S0SbS2A1S3dS58S29A2ScS2S65A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LN2_3 : ltac2:(tb__ "0|0|
S0S6S7bS65S47A2S8A3"). Proof. Time vmr. Qed.
Lemma D2_LN2_4 : ltac2:(tb__ "0|4|
S0SbSfSaSfS13S13A2M0A1M1SaS17A1M2A2M3A1S6fS3S52A1S3S46A1A2ScG3SeG1G2S7G0SeS13S13S2aS2bA4S9G0A1A3S26A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LN2_4 : ltac2:(tb__ "0|1|
S1S0S6S16S3S46A1M0A1S8A3S1S0S12S14G0A1S14S3S52A1A1A3S0S6S1aG0A1SdA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LN2_4 : ltac2:(tb__ "0|0|
S0S6S6eS33S14S3S46A1A1A2S8A3"). Proof. vmr. Qed.
Lemma EQ2_LN2_4 : ltac2:(tb__ "0|0|
S0S2S5S52S3S46A1A2S46A3"). Proof. vmr. Qed.
Lemma RUN2_LN2_4 : ltac2:(tb__ "0|0|
S0SaS4A1S3bS21S7S11S23S9S11A1A3S46A3S5dA3"). Proof. unfold run2_LN2_4; reflexivity. Qed.
Lemma L2_LN2_4 : ltac2:(tb__ "0|0|
S1S0S6S25S5dS7S11S23S9S11A1A3A2S8A3S0S2S3cU0S5dA2S61A3A2"). Proof. Time (split; [vmr | unfold EfD_LN2_4; reflexivity]). Qed.
Lemma AXD_LN2_4 : ltac2:(tb__ "0|0|
S0SbS2A1S3dS61S28A2ScS2S41A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LN2_4 : ltac2:(tb__ "0|2|
S0SbSaS18A1M0A1S73S41S39Z4M1A1S22S41G1A2A3ScG0S4eA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LN2_4 : ltac2:(tb__ "0|1|
S0S6S72S41S39Z4M0A1S22S41G0A2S4eS7S2S3aG0A1S9S2A1A3A5S8A3"). Proof. Time vmr. Qed.
Lemma HTD_LN2_4 : ltac2:(tb__ "0|1|
S0S2S59S71S74S22S41Z4M0A2S39G0A1S3aG0A1S41S4eA5S15S3S41A1A1A2A3").
Proof. unfold TD_LN2_4, TD_of, RD_LN2_4; reflexivity. Qed.
Lemma DCHK_LN2_4 : ltac2:(tb__ "0|2|
S0S6S75U2M0S31S2fG0A2Z4M1S41S59S22S41G1A2S4eA7S8A3"). Proof. Time vmr. Qed.
Lemma AXDr_LN2_4 : ltac2:(tb__ "0|0|
S0SbS2A1S3dS59S29A2ScS2S66A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LN2_4 : ltac2:(tb__ "0|0|
S0S6S7bS66S47A2S8A3"). Proof. Time vmr. Qed.
Lemma RUN3_LN2 : ltac2:(tb__ "0|0|
S0SaS4A1S3bS21S7S11S2dS7S11S2cS9S11A1A3A3S47A3S55A3"). Proof. unfold run3_LN2; reflexivity. Qed.
Lemma L3_LN2 : ltac2:(tb__ "0|0|
S1S0S6S25S55S7S11S2dS7S11S2cS9S11A1A3A3A2S8A3S1S0S2S3cU0S55A2S62A3S0S2S3cU1S55A2S48A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LN2 | unfold Ebg_LN2]; reflexivity]). Qed.
Lemma NX3_LN2 : ltac2:(tb__ "0|1|
S1S0S6S6eS33S14S3S47A1M0A1A2S8A3S0S6S1aG0A1SdA3A2"). Proof. split; vmr. Qed.

Lemma SMF_LN2 : ltac2:(tb__ "0|0|
S0S6S7cS17S1dS78A1S15S3S62A1A1A3S8A3"). Proof. vmr. Qed.
Lemma BGF_LN2 : ltac2:(tb__ "0|1|
S1S0S6S7cS17S1dS8fA1S15S3S49A1A1M0A3S8A3S0S6S7cS17S1dS32A1G0A3S8A3A2"). Proof. split; vmr. Qed.
Lemma NXB_LN2 : ltac2:(tb__ "0|0|
S0S6S6eS33S14S3S48A1A1A2S8A3"). Proof. vmr. Qed.
Lemma CertR_LN2 : ltac2:(tb__ "0|1|
S0S6S6cS34S21S7S11S76S9S11A1A3S33S7S2S48S9S2A1M0A3S7S2S49G0A3A6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [RCYE] GW Ebg_LN2 [Erc_LN2] run4_LN2); [unfold run4_LN2, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECertR_LN2 : ltac2:(tb__ "0|3|
S0S6S6dS34S21S7S11S76S9S11A1A3S33S7S6aS6bS48Z1S19Z0M0A1M1A3S9S6aA1M2A3S7S6aS6bS49G0G1A3G2A3A6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [RCYE] GW (mkVNA Ebg_LN2 1 (SLit 0)) [mkVNA Erc_LN2 0 (SLit 0)] run4_LN2); [unfold run4_LN2, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.

Lemma LEAF_LN2 : ltac2:(tb__ "0|2|
S1S0S11S20S3S49A1M0A1S76A3S1S0S13S1bG0Z1A2S19Z40744A1A3S1S0S13S1bG0Z2A2S1eS7eS1cPaA1S19S2eA1A3M1A3S1S0S13S1bG0ZaA2G1A3S1S0S13S1bG0ZbA2S1eS7eS1cPcA1S19N10A1A3A3S0S6S1aG0A1SdA3A2A2A2A2A2").
Proof. split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]. Qed.

Lemma Wa_LN2 : ltac2:(tb__ "0|0|
S0S6S16S81S36U2A1S35A2A1S8A3"). Proof. vmr. Qed.
Lemma Da_LN2 : ltac2:(tb__ "0|5|
S0SbSfSaSfS13S13A2M0A1M1SaS17A1M2A2M3A1S6fS3S38S37S36U2A1M4S35A3A1S81G4S35A2A2ScG3SeG1G2S7G0SeS13S13S1cP18A1S19S8eA1A4S9G0A1A3S9S17A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LN2 : ltac2:(tb__ "0|0|
S0S6S16S83S36U2A1S35S2fA3A1S8A3"). Proof. vmr. Qed.
Lemma Wc_LN2 : ltac2:(tb__ "0|0|
S0S6S16S84S36U2A1S35S2fA3A1S8A3"). Proof. vmr. Qed.
Lemma Wd_LN2 : ltac2:(tb__ "0|0|
S0S6S16S85S36U2A1S35S2fA3A1S8A3"). Proof. vmr. Qed.
Lemma Fb_LN2 : ltac2:(tb__ "0|0|
S0S6S7dS17S1fS8dA1S82SdS36U2A1S35S30A4A3S8A3"). Proof. vmr. Qed.
Lemma XI_LN2 : ltac2:(tb__ "0|2|
S0SbS2A1S3dS86SdS36U2M0A1M1S35S2fS30A5S80G0S10S79S2fA2A2A2ScS2S7fSdG1S35S70S79S18S7aS2fA4S30A5A2A3"). Proof. vmr. Qed.

Lemma NX0m_LN2 : ltac2:(tb__ "0|0|
S0S6S6eS33S14S3S4aA1A1A2S8A3"). Proof. vmr. Qed.
Definition Cert1m_LN2__runs : ltac2:(tb__ "0|0|
SaSbSaS4A1A1A1") := ltac2:(tb__ "0|0|
S8cS34S21S7S11S24S9S11A1A3S7S2S4aS9S2A1A3A4").
Lemma Cert1m_LN2 : ltac2:(tb__ "0|0|
S0S6S6cS34S21S7S11S24S9S11A1A3S33S7S2S4aS9S2A1A3S53A6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_LN2] exits1_LN2 Cert1m_LN2__runs); [unfold Cert1m_LN2__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_LN2 : ltac2:(tb__ "0|2|
S0S6S6dS34S21S7S11S24S9S11A1A3S33S7S6aS6bS4aZ1S19Z0M0A1M1A3S9S6aA1A3S70S2S6aS2S6bR1G0G1A3LE;S53A4A6S8A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_LN2 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_LN2) Cert1m_LN2__runs); [unfold Cert1m_LN2__runs; reflexivity | vmr]. Qed.
Lemma Wbm_LN2 : ltac2:(tb__ "0|0|
S0S6S16S88S36U2A1S35S2fA3A1S8A3"). Proof. vmr. Qed.
Lemma Wcm_LN2 : ltac2:(tb__ "0|0|
S0S6S16S89S36U2A1S35S2fA3A1S8A3"). Proof. vmr. Qed.
Lemma Wdm_LN2 : ltac2:(tb__ "0|0|
S0S6S16S8aS36U2A1S35S2fA3A1S8A3"). Proof. vmr. Qed.
Lemma XIm_LN2 : ltac2:(tb__ "0|2|
S0SbS2A1S3dS8bSdS36U2M0A1M1S35S2fS30A5S80G0S10S79S2fA2A2A2ScS2S87SdG1S35S70S79S18S7aS2fA4S30A5A2A3"). Proof. vmr. Qed.
