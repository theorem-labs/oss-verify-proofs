(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "cons"; "nil"; "prod"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "assn"; "world"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "pow"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exitsR"; "ldefR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Init.Logic"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface"; "al48_cells"; "memcpy48_contractA"; "memcpy48_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface"; "white_lo"; "memcpyR_contractA"; "memcpyR_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "K_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_eqs"; "nd_d0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS1"; "nd_s0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2"; "K_rp"; "nd_rp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epi_pf.IF"; "P_err"; "P_ok"; "nd_lo_err"; "nd_lo_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_exits"; "K_after0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "ldef"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "JA"; "PTrue"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJA TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_exitsR Lib_load_obj_epiD1 Lib_load_obj_epiD_eqs Lib_load_obj_epiS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_epiS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_epiD_pf Lib_load_obj_epiS5_pf Lib_load_obj_epiS_pf Lib_load_obj_epiCF_pf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module IF. Include Lib_load_obj_iface. End IF.
Module DP. Include Lib_load_obj_epiD_pf. End DP.
Module DK. Include Lib_load_obj_epiS5_pf. End DK.
Module SP. Include Lib_load_obj_epiS_pf. End SP.
Module CF. Include Lib_load_obj_epiCF_pf. End CF.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S35S7S2S6Q40A1A1S2cOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
ScS0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S1S17VCST;R1A2S18S13Z0R2A2S14R2S2aA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S1S17VXGL;R1A2S18S13Z0R2A2S14R2S2aA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S1S2fR1A1S17VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S5S5S1S1A2S1A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
S7OFr;") := ltac2:(tb__ "0|0|
S31VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S32VAInv;VCST;VXGL;S30VKc;Vrho0;VP0;VFB;VFF;VBX;S33Vnd;Ac").

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S34S0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
SaS0S9VAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S1S2bS1R1S3S1Z0S3S1Zf5S3S1Zf8S4S1A1A3A3A3A3S2dS0S9VAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48 : ltac2:(tb__ "0|0|
S1aS0S9VAInv;VCST;VXGL;S19A6").
Hypothesis MCROML : ltac2:(tb__ "0|0|
S1dS0S9VAInv;VCST;VXGL;S1cZcA7").
Variable FAMQ : list word -> assn.
Hypothesis XPK_T : ltac2:(tb__ "0|1|
S7S2S6Q40A1A1M0G0SeS0Vok;S8S0VJAv;S27A1S25R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XPE_T : ltac2:(tb__ "0|1|
S7S2S6Q40A1A1M0G0SeS0Vok;S8S0VJAv;S26A1S24R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Theorem epiDE_T : ltac2:(tb__ "0|1|
S7S2S6Q40A1A1M0G0S29R3A1SeS0Vok;S8S0VJAv;S20A1S1fR4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof.
  exact (DK.epiDK_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC MC48 FAMQ XPK_T XPE_T).
Qed.

Lemma epiRP_T : ltac2:(tb__ "0|1|
S7S2S6Q40A1A1M0G0S16R3A1SeS0Vok;S8S0VJAv;S23A1S22R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof.
  exact (SP.epiS_RP_T AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC FAMQ epiDE_T).
Qed.

Theorem epi_T : ltac2:(tb__ "0|1|
S7S2S6Q40A1A1M0G0S16R3A1SeS0Vok;S8S0VJAv;S21A1S28R4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof.
  exact (SP.epiS_T AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC MCROML FAMQ epiDE_T
           (CF.epiCF_TF AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BX HBX rho0 ok Hok AC FAMQ epiRP_T)).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
SbS0S9VAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S1S2bS1R1S3S1Z0S3S1Zf5S3S1Zf8S4S1A1A3A3A3A3S2eS0S9VAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48X : ltac2:(tb__ "0|0|
S1bS0S9VAInv;VCST;VXGL;S19A6").
Hypothesis MCROMLX : ltac2:(tb__ "0|0|
S1eS0S9VAInv;VCST;VXGL;S1cZcA7").
Variable FAM : ltac2:(tb__ "0|0|
S1S2S6Q40A1A1SfF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S1S1S2S6Q40A1A1S10S13R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XPK_E : ltac2:(tb__ "0|1|
S7S2S6Q40A1A1M0G0SdS0S8S0VJAv;S27A1S25R3R2A5VFAM;S11Z158S12Z2Z40A2A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XPE_E : ltac2:(tb__ "0|1|
S7S2S6Q40A1A1M0G0SdS0S8S0VJAv;S26A1S24R3R2A5VFAM;S11Zd1S12Z2Z40A2A2R1A2A3Ftp0;Ftp;Frho;").

Theorem epiDE_E : ltac2:(tb__ "0|1|
S7S2S6Q40A1A1M0G0S29R3A1SdS0S8S0VJAv;S20A1S1fR4R3A5VFAM;S11Z186S12Z2Z40A2A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0 HL.
  rewrite <- (DP.efmeas_z0 K_disp nd_d0 0%nat 390 rho).
  exact (DK.epiDK_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX MC48X FAM FAM_mono XPK_E XPE_E rho tp tp0 HL).
Qed.

Lemma epiRP_E : ltac2:(tb__ "0|1|
S7S2S6Q40A1A1M0G0S16R3A1SdS0S8S0VJAv;S23A1S22R4R3A5VFAM;S15S11Z187S12Z2Z40A2A2Z37fA2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof.
  exact (SP.epiS_RP_E AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 ACX FAM FAM_mono epiDE_E).
Qed.

Theorem epi_E : ltac2:(tb__ "0|1|
S7S2S6Q40A1A1M0G0S16R3A1SdS0S8S0VJAv;S21A1S28R4R3A5VFAM;S11Z18fS12Z2Z40A2A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0 HL.
  rewrite <- (DP.efmeas_z0 K_after0 nd_s0 0%nat 399 rho).
  exact (SP.epiS_E AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 ACX MCROMLX FAM FAM_mono epiDE_E
           (CF.epiCF_EF AInv CST XGL ALA HCST HXGL HXlits Kc HKc FB FF BX HBX rho0 ACX FAM FAM_mono epiRP_E) rho tp tp0 HL).
Qed.
End Existence.
End Sum.
