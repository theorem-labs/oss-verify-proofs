(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "cons"; "list"; "nat"; "bool"; "nil"; "true"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "SAlu"; "SLit"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopEf"; "ndE0f"; "ndXEf"; "ndLf"; "cutsE2f"; "exitsE2f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "uval"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "AHead"; "JA"; "NDA"; "am_eqb"; "am_subst"; "nd_below"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tblL"; "tblB"; "s_loop"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "z0"; "LAX"; "LAXK"; "RL"; "VLA"; "ndL"; "ndXE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loopE"; "K_afterE2"; "X_bodyE2"; "X_latchE2"; "K_loopE2"; "ndE0"; "PhisE"; "X_errxE2"; "X_latchE2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "pI"; "xLC"; "HNEXT"; "cps_loop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "JAF"; "bud_le2"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition ndLf (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S21S2aS29Vbd;S1fS3cS8A2A4").
Definition ndXEf : ndesc := ltac2:(tb__ "0|1|
S16S2S1bS2eZ0M0A1S2S1bS2fG0A1S6S1bA1A3A3A1").
Definition ndE0f : ndesc := ndLf [].

Definition cutsE2f : list efnode := ltac2:(tb__ "0|5|
S2S1S1S1S19S1eA2M0S4A2M1S1S9ScA2M2A2M3S0G1G2S0G0S4S0S19S1eS37S14A4U0M4A4S0S9ScS30S31Z1aS2dA2A4A4S2G3S0G1G2S0G0S4S0S19S1eS35S14A4G4A4S0S9ScS30S31Z19S2dA2A4A4S6G3A1A3A3").
Definition exitsE2f : list efnode := ltac2:(tb__ "0|6|
S2S1S1S1S19S1eA2M0S4A2M1S1S9ScA2M2A2M3S0G1G2S0G0S4S0S19S1eS34S14A4U0M4A4S0S9ScZ190S2dA4M5A4S2G3S0G1G2S0G0S4S0S19S1eS3aS14A4G4A4G5A4S6G3A1A3A3").
Lemma ecertE2f_ok : ltac2:(tb__ "0|0|
S12S5S4aSaS2cS39U96S40S2cS17S18A8S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma loopEf_checks : ltac2:(tb__ "0|3|
S11S12S5S24S3fS15A2S7A3S11S12S5S49SfS1aS3bA1A1S1dS28S6S1bA1M0A2S2S1bS2eZ0M1A1S2S1bS2fG1A1G0A3A3A3S7A3S12S5S22S23S28S1fS3cS8A2M2A2G2A2S7A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S4cSbS3S25Q40A1A1S45OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S4bSaVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S9S42VCST;R1A2S11S43Z0R2A2S44R2S41A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S9S42VXGL;R1A2S11S43Z0R2A2S44R2S41A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S1S1S9S9A2S9A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable PA : AA -> Prop.
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
SbOFr;") := ltac2:(tb__ "0|0|
S47VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S20VAInv;VCST;VXGL;S2cVKc;Vrho0;VP0;VFB;VFF;VBX;VPA;Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S48VAInv;VCST;VXGL;S2cVKc;Vrho0;VP0;VFB;VFF;VBX;VPA;VPhi;Vnd;Ad").

Lemma pot_dropF : ltac2:(tb__ "0|0|
SbOF_;S3S1bA1S19SbS3S25Q40A1A1S2bS10SaVJAFv;R6S32R5A1A2R4R3R2R1A6S10SaVJAFv;R7S16R6A1A2R5R4R3R2A6F_;Fw;Ftp;Frho;FA;Fbd;FPhi;").
Proof.
  intros Phi bd A rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA Phi (ndL bd) A rho tp w Hw) as [HS HP].
  apply (SPA_JAF_intro segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA Phi (ndLf bd) A rho tp w); [|exact HP].
  exact (JA_pot_drop segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA HBX tvL frL bd pH A rho tp w HS).
Qed.
Lemma relaxF_latchE2 : ltac2:(tb__ "0|0|
SbS3S25Q40A1A1S2bS10SaVJAFv;S27S33A2S36R3R2R1A6S10SaVJAFv;S27S15A2S36R4R3R2A6F_;Fw;Ftp;Frho;").
Proof. intros rho tp w. exact (pot_dropF tblB [LAX 0; LAXK 0] X_latchE2 rho tp w). Qed.
Lemma relaxF_bodyE2 : ltac2:(tb__ "0|0|
SbS3S25Q40A1A1S2bS10SaVJAFv;S26S38A2S35R3R2R1A6S10SaVJAFv;S26S14A2S35R4R3R2A6F_;Fw;Ftp;Frho;").
Proof. intros rho tp w. exact (pot_dropF tblL [] X_bodyE2 rho tp w). Qed.
Lemma relaxF_afterE2 : ltac2:(tb__ "0|0|
SbS3S25Q40A1A1S2bS10SaVJAFv;S26S38A2S34R3R2R1A6S10SaVJAFv;S26S14A2S34R4R3R2A6F_;Fw;Ftp;Frho;").
Proof. intros rho tp w. exact (pot_dropF tblL [] K_afterE2 rho tp w). Qed.

Lemma latch_absorbE2f : ltac2:(tb__ "0|0|
SbS3S25Q40A1A1S2bS27R3A1S10SaVJAv;S15A1S36R4R3R2A6S13SbSbS11S26R1A1S11S10SaVJAv;S14A1S37R1R5R4A6S11S12S9S1cR1S3eA2S1cR6S3eA2A3S12S9S1cR1S3dA2S1cR6SdS46S3dSeZ1A1A3A2A3A2A2A2Lrho2;A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w HP HS. pose proof loopEf_checks as (Cnb & Cbud & Cam).
  exact (latch_absorbE2 AInv CST XGL ALA HCST HXGL Kc HKc FB FF BX PA rho0 [LAX 0; LAXK 0] [] (AHead pH false) rho tp w Cnb Cbud Cam HP HS).
Qed.
End Sum.
