(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_062.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf cu.
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dq SegQIF_mdefs.

(* [comment removed for export] *)
Module CallocHitTail0E.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "SVar"; "SLit"; "SPUle"; "rw"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "pair"; "prod"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "prim_room"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "V_RZ"; "C9"; "C9p"; "E3p"; "C10a"; "C10b"; "C10pa"; "C10pb"; "C9ma"; "C9mb"; "C9mpa"; "C9mpb"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Logic"; "not"; "eq"; "or"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "JLc_ok"; "Lc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocE9"; "es9c_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocEi"; "ECert10a_0"; "ECert10b_0"; "ECert10pa_0"; "ECert10pb_0"; "ECert9a_0"; "ECert9b_0"; "ECert9pa_0"; "ECert9pb_0"; "NX10a_0"; "NX10b_0"; "NX10pa_0"; "NX10pb_0"; "NX9fa_0"; "NX9fb_0"; "NX9fpa_0"; "NX9fpb_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9i"; "D9ma_0"; "D9mb_0"; "D9mpa_0"; "D9mpb_0"; "ENT10a_0"; "ENT10b_0"; "ENT10pa_0"; "ENT10pb_0"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"; "FBCma_0"; "FBCmb_0"; "FBCmpa_0"; "FBCmpb_0"; "FBTma_0"; "FBTmb_0"; "FBTmpa_0"; "FBTmpb_0"; "FH_a_0"; "FH_b_0"; "FH_pa_0"; "FH_pb_0"; "HCC9ma_0"; "HCC9mb_0"; "HCC9mpa_0"; "HCC9mpb_0"; "HTma_0"; "HTmb_0"; "HTmpa_0"; "HTmpb_0"; "Hchkma_0"; "Hchkmb_0"; "Hchkmpa_0"; "Hchkmpb_0"; "Hema_0"; "Hemb_0"; "Hempa_0"; "Hempb_0"; "NX9ma_0"; "NX9mb_0"; "NX9mpa_0"; "NX9mpb_0"; "NXCma_0"; "NXCmb_0"; "NXCmpa_0"; "NXCmpb_0"; "Rma_0"; "Rmb_0"; "Rmpa_0"; "Rmpb_0"; "SID10a_0"; "SID10b_0"; "SID10pa_0"; "SID10pb_0"; "T9a_0"; "T9b_0"; "T9pa_0"; "T9pb_0"; "W9ma_0"; "W9mb_0"; "W9mpa_0"; "W9mpb_0"; "hcells_a"; "hcells_b"; "hcells_pa";
"hcells_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "sdma_0"; "sdmb_0"; "sdmpa_0"; "sdmpb_0"; "sf_a"; "sf_b"; "sf_pa"; "sf_pb"; "sma_0"; "smb_0"; "smpa_0"; "smpb_0"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS5i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.SpineCallocS6i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS7i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.CallocHitTail0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocE9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocEi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.CDepotCallH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineCallocS5t OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section EARMS.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SdS39VCST;R1A2S39S45R2A2S35F_;F_;Fa;").
Let law_die : forall A rho tp md, AInvA segsA A rho tp md -> cell_ok (view segsA (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Definition earm_a : ltac2:(tb__ "0|6|
S1aS1aS2S8S8SdOF_;SfS2dQ40M0A1A1M1SfS14S17S18A2M2A1S3aG2S13S17S18S37S1U0A1M3S0A2S36VCST;VXGL;R8R6A4A4R1A3S3cG3S0A2S42G3S0A2S3R9A1S3fRcRbA2S40R8RaR9A3SdS34S4VCST;RfR1A3S5VCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S43Z1S41ReS2cG0ScRbPcM4A2A2A2A2S1bRfA1S10OLpartial;S15S32S33SdS44S2cG0ScRdG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S2eSeS31SeS3eG3S0R13R12R10A5S3bS11S7SbSaZ20A1S9S1cA1A2S12S7A1A3S1dG3S0Z2A3A2R2R1A5S19SeS30R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;") := ltac2:(tb__ "0|3|
S3dU0M0S0Z2M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S15S11S7SbSaZ20A1S9S1cA1A2S12S7A1A3S1dS1G0A1M2S0G1A3S28G2S0G1A3S24G2S0G1A3S90S20G2S0G1A3S60S70S94S58S80Sa8Sa0S88S7cS78S74S64S68S5cS8cS84S54S50S4cS48SacS9cS98Sa4S6cA29").
Definition earm_b : ltac2:(tb__ "0|6|
S1aS1aS2S8S8SdOF_;SfS2dQ40M0A1A1M1SfS14S17S18A2M2A1S3aG2S13S17S18S37S1U0A1M3S0A2S36VCST;VXGL;R8R6A4A4R1A3S3cG3S0A2S42G3S0A2S3R9A1S3fRcRbA2S40R8RaR9A3SdS34S4VCST;RfR1A3S5VCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S43Z1S41ReS2cG0ScRbPcM4A2A2A2A2S1bRfA1S10OLpartial;S15S32S33SdS44S2cG0ScRdG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S2eSeS31SeS3eG3S0R13R12R10A5S3bS11S7SbS9S1cA1SaZ10A1A2S12S7A1A3S1dG3S0Z2A3A2R2R1A5S19SeS30R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;") := ltac2:(tb__ "0|3|
S3dU0M0S0Z2M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S15S11S7SbS9S1cA1SaZ10A1A2S12S7A1A3S1dS1G0A1M2S0G1A3S29G2S0G1A3S25G2S0G1A3S91S21G2S0G1A3S61S71S95S59S81Sa9Sa1S89S7dS79S75S65S69S5dS8dS85S55S51S4dS49SadS9dS99Sa5S6dA29").
Definition earm_pa : ltac2:(tb__ "0|6|
S1aS1aS2S8S8SdOF_;SfS2dQ40M0A1A1M1SfS14S17S18A2M2A1S3aG2S13S17S18S37S1U0A1M3S0A2S36VCST;VXGL;R8R6A4A4R1A3S3cG3S0A2S42G3S0A2S3R9A1S3fRcRbA2S40R8RaR9A3SdS34S4VCST;RfR1A3S5VCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S43Z1S41ReS2cG0ScRbPcM4A2A2A2A2S1bRfA1S10OLpartial;S16S32S33SdS44S2cG0ScRdG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S2eSeS31SeS3eG3S0R13R12R10A5S3bS11S7SbSaZ20A1S9S1cA1A2S12S7A1A3S1eG3S0Z2A3A2R2R1A5S19SeS30R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;") := ltac2:(tb__ "0|3|
S3dU0M0S0Z2M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S16S11S7SbSaZ20A1S9S1cA1A2S12S7A1A3S1eS1G0A1M2S0G1A3S2aG2S0G1A3S26G2S0G1A3S92S22G2S0G1A3S62S72S96S5aS82SaaSa2S8aS7eS7aS76S66S6aS5eS8eS86S56S52S4eS4aSaeS9eS9aSa6S6eA29").
Definition earm_pb : ltac2:(tb__ "0|6|
S1aS1aS2S8S8SdOF_;SfS2dQ40M0A1A1M1SfS14S17S18A2M2A1S3aG2S13S17S18S37S1U0A1M3S0A2S36VCST;VXGL;R8R6A4A4R1A3S3cG3S0A2S42G3S0A2S3R9A1S3fRcRbA2S40R8RaR9A3SdS34S4VCST;RfR1A3S5VCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S43Z1S41ReS2cG0ScRbPcM4A2A2A2A2S1bRfA1S10OLpartial;S16S32S33SdS44S2cG0ScRdG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S2eSeS31SeS3eG3S0R13R12R10A5S3bS11S7SbS9S1cA1SaZ10A1A2S12S7A1A3S1eG3S0Z2A3A2R2R1A5S19SeS30R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;") := ltac2:(tb__ "0|3|
S3dU0M0S0Z2M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S16S11S7SbS9S1cA1SaZ10A1A2S12S7A1A3S1eS1G0A1M2S0G1A3S2bG2S0G1A3S27G2S0G1A3S93S23G2S0G1A3S63S73S97S5bS83SabSa3S8bS7fS7bS77S67S6bS5fS8fS87S57S53S4fS4bSafS9fS9bSa7S6fA29").
End EARMS.

Section HIT0TE.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SdS39VCST;R1A2S39S45R2A2S35F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
SdS39VCST;R1A2S32S47R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S6VAInv;VW;Vst;VA;VKc;S9PcA1A6").
Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Let law_inv3 : forall A rho tp md, AInv A rho tp md -> inv3 A := AInvA_inv3.
Let W0 : list ulink := Wcan 0.
Let st0 : ustop := UStopLe.

Theorem ecalloc_hit_tail_0_P : ltac2:(tb__ "0|1|
S1aS2S8SfS2dQ40A1A1SfS14S17S18A2M0A1S19Vsegs;S30R3R2R1A5S2fS3aG0S13S17S18S37VW0;Vst0;A2S36VCST;VXGL;R6R5A4A4R2A3S3R6A1S8S2eVsegs;S31Vsegs;S46VW0;Vst0;R9R8R7A5S1fVW0;Vst0;Z2A3R1R6A5R4A3FrhoX;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Posts Q HPin HKc.
  pose proof (depot_call_HDE_0 CST XGL HCST HXGL HCSTD A Kc rho Q HKc) as HD.
  assert (HUS : stopJ_stable W0 st0) by (exact HUS_shape).
  assert (HW : stopJ_w W0 st0) by (hw_discharge).
  set (nv := bv_unsigned (rw rho 12%positive)).
  apply (espine_s3p_tail 0%nat st0 2 SKY_0 YX_0 YF_0 YP_0 WY1_0 WY2_0 WY3_0 WY4_0 WY5_0 WY6_0 WY7_0 s3_0 ENT3_0 SID3_0 A Kc rho tp Q HW HUS HKc).
  intros Hcnt HSEP HPRM0 rhoE3.
  apply (espine_s4 0%nat st0 2 NXC3_0 s4_ecert_0 (KEEP CST XGL A) A Kc rho tp Q HUS HKc HD).
  intros A' rho' rhoX5 tp' HDO HL.
  assert (Enu : bv_unsigned (rw rho' 12%positive) = nv) by (destruct HL as [HLw _]; rewrite (HLw 12%positive); reflexivity).
  assert (HPRM' : prim_room A') by exact (prim_room_same A A' (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HDO)))))) HPRM0).
  assert (Hcnt' : 1 <= cnt_of A' (bv_unsigned (rw rho' 12%positive))).
  { rewrite Enu. unfold cnt_of, cst_of. rewrite (proj1 (proj2 HDO)). exact Hcnt. }
  assert (K7 : forall tpY rhoY, etriple segs (SPA segs (JGb W0 st0 A' Kc rho') (C7 W0 st0 2) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (espine_s7 0%nat st0 2 OV7a_0 OV7b_0 TAB7a_0 TAB7b_0 W7a_0 W7b_0 D7a_0 D7b_0 NX7a_0 NX7b_0 G7a_0 G7b_0 F7a_0 F7b_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8i.s8a_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8i.s8b_0
             ENT8a_0 ENT8b_0 SID8a_0 SID8b_0 G7p_0 F7p_0 W7p_0 D7p_0 NX7p_0 F7an_0 F7bn_0 NXC7_0 s7_ecert_0 A' Kc rho' tpY Q HUS HKc Hcnt').
    - intros Hm0 rhoY8.
      apply (espine_s8c 0%nat st0 (C8 W0 st0 2) (C9 W0 st0 2) (E8n W0 st0 2) s9e_0 ENT9e_0 SID9e_0 NXCC8_0 ECert8_0 A' Kc rho' tpY Q HUS HKc).
      intros rhoY9 tpY9.
      exact (espine_s9c_P 0%nat st0 CST XGL false (C9 W0 st0 2) NX9_0 FGC_0 (earm_a CST XGL HCST HXGL HCSTM) (earm_b CST XGL HCST HXGL HCSTM)
               A A' Kc rho rho' (KEEP CST XGL A) tp Posts HPin HW HUS HKc HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm0 rhoY9 tpY9).
    - intros Hm8 rhoY7.
      apply (espine_s7p 0%nat st0 2 OV7c_0 OV7d_0 TAB7c_0 TAB7d_0 W7c_0 W7d_0 D7c_0 D7d_0 NX7c_0 NX7d_0 G7c_0 G7d_0 F7c_0 F7d_0 s8c_0 s8d_0
               ENT8c_0 ENT8d_0 SID8c_0 SID8d_0 NXC7p_0 s7p_ecert_0 A' Kc rho' tpY Q HUS HKc).
      intros rhoY8.
      apply (espine_s8c 0%nat st0 (C8p W0 st0 2) (C9p W0 st0 2) (E8pn W0 st0 2) s9ep_0 ENT9ep_0 SID9ep_0 NXCC8p_0 ECert8p_0 A' Kc rho' tpY Q HUS HKc).
      intros rhoY9 tpY9.
      exact (espine_s9c_P 0%nat st0 CST XGL true (C9p W0 st0 2) NX9p_0 FGCp_0 (earm_pa CST XGL HCST HXGL HCSTM) (earm_pb CST XGL HCST HXGL HCSTM)
               A A' Kc rho rho' (KEEP CST XGL A) tp Posts HPin HW HUS HKc HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm8 rhoY9 tpY9). }
  assert (K6 : forall tpY rhoY, etriple segs (SPA segs (JGb W0 st0 A' Kc rho') (C6 W0 st0 2) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (espine_s6 0%nat st0 2 k6_0 NTH6s_0 ZC6s_0 s7s_0 ENT7s_0 SID7s_0 G6l_0 W6l_0 D6l_0 NX6l_0 NXC6_0 s6_ecert_0 A' Kc rho' tpY Q HUS HKc Hcnt'); [exact (K7 tpY)|].
    intros rhoY6l.
    assert (NXC6m_f : (GW <= ss_next (ax_S (C6m W0 st0 2)))%positive) by (apply Pos.leb_le; vm_cast_no_check (eq_refl true)).
    apply (espine_s6l 0%nat st0 2 W6m_0 D6m_0 NX6m_0 s6_0 sd6_0 R6_0 T6_0 He6_0 Hchk6_0 HT6_0 FBC6_0 FBT6_0 ENT6_0 SID6_0 NXC6m_f NXC6l_0 s6l_ecert_0 A' Kc rho' tpY Q HUS HKc).
    intros rhoY6b tpY6b.
    apply (espine_s6b 0%nat st0 2 s7j_0 ENT7j_0 SID7j_0 NXC6b_0 s6b_ecert_0 A' Kc rho' tpY6b Q HUS HKc). exact (K7 tpY6b). }
  apply (espine_s5 0%nat st0 2 s6n_0 ENT6n_0 SID6n_0 W5b_0 D5b_0 NX5b_0 F5f64_0 NXC5_0 s5_ecert_0 A' Kc rho' tp' Q HUS HKc Hcnt'); [exact (K6 tp')|].
  intros rhoX5b.
  apply (espine_s5b 0%nat st0 2 OV1_0 OV2_0 TAB1_0 TAB2_0 W1'_0 W2'_0 D1'_0 D2'_0 NX1'_0 NX2'_0 F1gt_0 F2le_0 F1_64_0 F2_64_0 s1_0 s2_0 ENT1_0 ENT2_0 SID1_0 SID2_0 NXC5b_0 s5b_ecert_0
           A' Kc rho' tp' Q HUS HKc).
  intros rhoX5c.
  apply (espine_s5c 0%nat st0 2 G5m1_0 W5m1_0 D5m1_0 NX5m1_0 s51_0 sd51_0 R51_0 T51_0 He51_0 Hchk51_0 HT51_0 FBC51_0 FBT51_0 ENT51_0 SID51_0 NXC51_0 NXC5c_0 s5c_ecert_0
           A' Kc rho' tp' Q HUS HKc Hcnt').
  intros rhoX5d tp5d.
  apply (espine_s5d 0%nat st0 2 G5m2_0 W5m2_0 D5m2_0 NX5m2_0 s52_0 sd52_0 R52_0 T52_0 He52_0 Hchk52_0 HT52_0 FBC52_0 FBT52_0 ENT52_0 SID52_0 NXC52_0 NXC5d_0 s5d_ecert_0
           A' Kc rho' tp5d Q HUS HKc Hcnt').
  intros rhoX5e tp5e.
  apply (espine_s5e 0%nat st0 2 s6j_0 ENT6j_0 SID6j_0 NXC5e_0 s5e_ecert_0 A' Kc rho' tp5e Q HUS HKc). exact (K6 tp5e).
Qed.

Theorem ecalloc_hit_tail_0 : ltac2:(tb__ "0|0|
S1aS2S8SfS2dQ40A1A1S19Vsegs;S30R2R1S38VCST;VXGL;VW0;Vst0;R4R3A6A5S2fS3R4A1S8S2eVsegs;S31Vsegs;S46VW0;Vst0;R7R6R5A5S1fVW0;Vst0;Z2A3R1R4A5R3A3FrhoX;F_;TQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp. exact (ecalloc_hit_tail_0_P A Kc rho tp (PFc CST XGL W0 st0 A Kc) (or_intror (or_introl eq_refl))).
Qed.
End HIT0TE.
End CallocHitTail0E.

(* [comment removed for export] *)
Module CallocHitTail1E.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLeOrPc"; "Wcan"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "SVar"; "SLit"; "SPUle"; "rw"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "pair"; "prod"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "prim_room"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "V_RZ"; "C9"; "C9p"; "E3p"; "C10a"; "C10b"; "C10pa"; "C10pb"; "C9ma"; "C9mb"; "C9mpa"; "C9mpb"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Logic"; "not"; "eq"; "or"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "JLc_ok"; "Lc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocE9"; "es9c_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocEiW1"; "ECert10a_0"; "ECert10b_0"; "ECert10pa_0"; "ECert10pb_0"; "ECert9a_0"; "ECert9b_0"; "ECert9pa_0"; "ECert9pb_0"; "NX10a_0"; "NX10b_0"; "NX10pa_0"; "NX10pb_0"; "NX9fa_0"; "NX9fb_0"; "NX9fpa_0"; "NX9fpb_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9iW1"; "D9ma_0"; "D9mb_0"; "D9mpa_0"; "D9mpb_0"; "ENT10a_0"; "ENT10b_0"; "ENT10pa_0"; "ENT10pb_0"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"; "FBCma_0"; "FBCmb_0"; "FBCmpa_0"; "FBCmpb_0"; "FBTma_0"; "FBTmb_0"; "FBTmpa_0"; "FBTmpb_0"; "FH_a_0"; "FH_b_0"; "FH_pa_0"; "FH_pb_0"; "HCC9ma_0"; "HCC9mb_0"; "HCC9mpa_0"; "HCC9mpb_0"; "HTma_0"; "HTmb_0"; "HTmpa_0"; "HTmpb_0"; "Hchkma_0"; "Hchkmb_0"; "Hchkmpa_0"; "Hchkmpb_0"; "Hema_0"; "Hemb_0"; "Hempa_0"; "Hempb_0"; "NX9ma_0"; "NX9mb_0"; "NX9mpa_0"; "NX9mpb_0"; "NXCma_0"; "NXCmb_0"; "NXCmpa_0"; "NXCmpb_0"; "Rma_0"; "Rmb_0"; "Rmpa_0"; "Rmpb_0"; "SID10a_0"; "SID10b_0"; "SID10pa_0"; "SID10pb_0"; "T9a_0"; "T9b_0"; "T9pa_0"; "T9pb_0"; "W9ma_0"; "W9mb_0"; "W9mpa_0"; "W9mpb_0"; "hcells_a"; "hcells_b"; "hcells_pa";
"hcells_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "sdma_0"; "sdmb_0"; "sdmpa_0"; "sdmpb_0"; "sf_a"; "sf_b"; "sf_pa"; "sf_pb"; "sma_0"; "smb_0"; "smpa_0"; "smpb_0"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS5iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS6iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.SpineCallocS7iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.CallocHitTail1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocE9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocEiW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cs.CDepotCallHW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineCallocS5t OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section EARMS.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SdS39VCST;R1A2S39S45R2A2S35F_;F_;Fa;").
Let law_die : forall A rho tp md, AInvA segsA A rho tp md -> cell_ok (view segsA (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Definition earm_a : ltac2:(tb__ "0|6|
S1aS1aS2S8S8SdOF_;SfS2dQ40M0A1A1M1SfS14S17S18A2M2A1S3aG2S13S17S18S37S1U1A1M3S0A2S36VCST;VXGL;R8R6A4A4R1A3S3cG3S0A2S42G3S0A2S3R9A1S3fRcRbA2S40R8RaR9A3SdS34S4VCST;RfR1A3S5VCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S43Z1S41ReS2cG0ScRbPcM4A2A2A2A2S1bRfA1S10OLpartial;S15S32S33SdS44S2cG0ScRdG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S2eSeS31SeS3eG3S0R13R12R10A5S3bS11S7SbSaZ20A1S9S1cA1A2S12S7A1A3S1dG3S0Z3A3A2R2R1A5S19SeS30R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;") := ltac2:(tb__ "0|3|
S3dU1M0S0Z3M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S15S11S7SbSaZ20A1S9S1cA1A2S12S7A1A3S1dS1G0A1M2S0G1A3S28G2S0G1A3S24G2S0G1A3S90S20G2S0G1A3S60S70S94S58S80Sa8Sa0S88S7cS78S74S64S68S5cS8cS84S54S50S4cS48SacS9cS98Sa4S6cA29").
Definition earm_b : ltac2:(tb__ "0|6|
S1aS1aS2S8S8SdOF_;SfS2dQ40M0A1A1M1SfS14S17S18A2M2A1S3aG2S13S17S18S37S1U1A1M3S0A2S36VCST;VXGL;R8R6A4A4R1A3S3cG3S0A2S42G3S0A2S3R9A1S3fRcRbA2S40R8RaR9A3SdS34S4VCST;RfR1A3S5VCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S43Z1S41ReS2cG0ScRbPcM4A2A2A2A2S1bRfA1S10OLpartial;S15S32S33SdS44S2cG0ScRdG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S2eSeS31SeS3eG3S0R13R12R10A5S3bS11S7SbS9S1cA1SaZ10A1A2S12S7A1A3S1dG3S0Z3A3A2R2R1A5S19SeS30R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;") := ltac2:(tb__ "0|3|
S3dU1M0S0Z3M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S15S11S7SbS9S1cA1SaZ10A1A2S12S7A1A3S1dS1G0A1M2S0G1A3S29G2S0G1A3S25G2S0G1A3S91S21G2S0G1A3S61S71S95S59S81Sa9Sa1S89S7dS79S75S65S69S5dS8dS85S55S51S4dS49SadS9dS99Sa5S6dA29").
Definition earm_pa : ltac2:(tb__ "0|6|
S1aS1aS2S8S8SdOF_;SfS2dQ40M0A1A1M1SfS14S17S18A2M2A1S3aG2S13S17S18S37S1U1A1M3S0A2S36VCST;VXGL;R8R6A4A4R1A3S3cG3S0A2S42G3S0A2S3R9A1S3fRcRbA2S40R8RaR9A3SdS34S4VCST;RfR1A3S5VCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S43Z1S41ReS2cG0ScRbPcM4A2A2A2A2S1bRfA1S10OLpartial;S16S32S33SdS44S2cG0ScRdG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S2eSeS31SeS3eG3S0R13R12R10A5S3bS11S7SbSaZ20A1S9S1cA1A2S12S7A1A3S1eG3S0Z3A3A2R2R1A5S19SeS30R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;") := ltac2:(tb__ "0|3|
S3dU1M0S0Z3M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S16S11S7SbSaZ20A1S9S1cA1A2S12S7A1A3S1eS1G0A1M2S0G1A3S2aG2S0G1A3S26G2S0G1A3S92S22G2S0G1A3S62S72S96S5aS82SaaSa2S8aS7eS7aS76S66S6aS5eS8eS86S56S52S4eS4aSaeS9eS9aSa6S6eA29").
Definition earm_pb : ltac2:(tb__ "0|6|
S1aS1aS2S8S8SdOF_;SfS2dQ40M0A1A1M1SfS14S17S18A2M2A1S3aG2S13S17S18S37S1U1A1M3S0A2S36VCST;VXGL;R8R6A4A4R1A3S3cG3S0A2S42G3S0A2S3R9A1S3fRcRbA2S40R8RaR9A3SdS34S4VCST;RfR1A3S5VCST;VXGL;RfR1A4A2RbR2A1F_;Fa;S43Z1S41ReS2cG0ScRbPcM4A2A2A2A2S1bRfA1S10OLpartial;S16S32S33SdS44S2cG0ScRdG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S2eSeS31SeS3eG3S0R13R12R10A5S3bS11S7SbS9S1cA1SaZ10A1A2S12S7A1A3S1eG3S0Z3A3A2R2R1A5S19SeS30R11ReRdA5A3FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;") := ltac2:(tb__ "0|3|
S3dU1M0S0Z3M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S16S11S7SbS9S1cA1SaZ10A1A2S12S7A1A3S1eS1G0A1M2S0G1A3S2bG2S0G1A3S27G2S0G1A3S93S23G2S0G1A3S63S73S97S5bS83SabSa3S8bS7fS7bS77S67S6bS5fS8fS87S57S53S4fS4bSafS9fS9bSa7S6fA29").
End EARMS.

Section HIT0TE.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SdS39VCST;R1A2S39S45R2A2S35F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
SdS39VCST;R1A2S32S47R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S6VAInv;VW;Vst;VA;VKc;S9PcA1A6").
Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Let law_inv3 : forall A rho tp md, AInv A rho tp md -> inv3 A := AInvA_inv3.
Let W0 : list ulink := Wcan 1.
Let st0 : ustop := UStopLeOrPc.

Theorem ecalloc_hit_tail_1_P : ltac2:(tb__ "0|1|
S1aS2S8SfS2dQ40A1A1SfS14S17S18A2M0A1S19Vsegs;S30R3R2R1A5S2fS3aG0S13S17S18S37VW0;Vst0;A2S36VCST;VXGL;R6R5A4A4R2A3S3R6A1S8S2eVsegs;S31Vsegs;S46VW0;Vst0;R9R8R7A5S1fVW0;Vst0;Z3A3R1R6A5R4A3FrhoX;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Posts Q HPin HKc.
  pose proof (depot_call_HDE_1 CST XGL HCST HXGL HCSTD A Kc rho Q HKc) as HD.
  assert (HUS : stopJ_stable W0 st0) by (exact HUS_shape).
  assert (HW : stopJ_w W0 st0) by (hw_discharge).
  set (nv := bv_unsigned (rw rho 12%positive)).
  apply (espine_s3p_tail 1%nat st0 3 SKY_0 YX_0 YF_0 YP_0 WY1_0 WY2_0 WY3_0 WY4_0 WY5_0 WY6_0 WY7_0 s3_0 ENT3_0 SID3_0 A Kc rho tp Q HW HUS HKc).
  intros Hcnt HSEP HPRM0 rhoE3.
  apply (espine_s4 1%nat st0 3 NXC3_0 s4_ecert_0 (KEEP CST XGL A) A Kc rho tp Q HUS HKc HD).
  intros A' rho' rhoX5 tp' HDO HL.
  assert (Enu : bv_unsigned (rw rho' 12%positive) = nv) by (destruct HL as [HLw _]; rewrite (HLw 12%positive); reflexivity).
  assert (HPRM' : prim_room A') by exact (prim_room_same A A' (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HDO)))))) HPRM0).
  assert (Hcnt' : 1 <= cnt_of A' (bv_unsigned (rw rho' 12%positive))).
  { rewrite Enu. unfold cnt_of, cst_of. rewrite (proj1 (proj2 HDO)). exact Hcnt. }
  assert (K7 : forall tpY rhoY, etriple segs (SPA segs (JGb W0 st0 A' Kc rho') (C7 W0 st0 3) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (espine_s7 1%nat st0 3 OV7a_0 OV7b_0 TAB7a_0 TAB7b_0 W7a_0 W7b_0 D7a_0 D7b_0 NX7a_0 NX7b_0 G7a_0 G7b_0 F7a_0 F7b_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8iW1.s8a_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8iW1.s8b_0
             ENT8a_0 ENT8b_0 SID8a_0 SID8b_0 G7p_0 F7p_0 W7p_0 D7p_0 NX7p_0 F7an_0 F7bn_0 NXC7_0 s7_ecert_0 A' Kc rho' tpY Q HUS HKc Hcnt').
    - intros Hm0 rhoY8.
      apply (espine_s8c 1%nat st0 (C8 W0 st0 3) (C9 W0 st0 3) (E8n W0 st0 3) s9e_0 ENT9e_0 SID9e_0 NXCC8_0 ECert8_0 A' Kc rho' tpY Q HUS HKc).
      intros rhoY9 tpY9.
      exact (espine_s9c_P 1%nat st0 CST XGL false (C9 W0 st0 3) NX9_0 FGC_0 (earm_a CST XGL HCST HXGL HCSTM) (earm_b CST XGL HCST HXGL HCSTM)
               A A' Kc rho rho' (KEEP CST XGL A) tp Posts HPin HW HUS HKc HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm0 rhoY9 tpY9).
    - intros Hm8 rhoY7.
      apply (espine_s7p 1%nat st0 3 OV7c_0 OV7d_0 TAB7c_0 TAB7d_0 W7c_0 W7d_0 D7c_0 D7d_0 NX7c_0 NX7d_0 G7c_0 G7d_0 F7c_0 F7d_0 s8c_0 s8d_0
               ENT8c_0 ENT8d_0 SID8c_0 SID8d_0 NXC7p_0 s7p_ecert_0 A' Kc rho' tpY Q HUS HKc).
      intros rhoY8.
      apply (espine_s8c 1%nat st0 (C8p W0 st0 3) (C9p W0 st0 3) (E8pn W0 st0 3) s9ep_0 ENT9ep_0 SID9ep_0 NXCC8p_0 ECert8p_0 A' Kc rho' tpY Q HUS HKc).
      intros rhoY9 tpY9.
      exact (espine_s9c_P 1%nat st0 CST XGL true (C9p W0 st0 3) NX9p_0 FGCp_0 (earm_pa CST XGL HCST HXGL HCSTM) (earm_pb CST XGL HCST HXGL HCSTM)
               A A' Kc rho rho' (KEEP CST XGL A) tp Posts HPin HW HUS HKc HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm8 rhoY9 tpY9). }
  assert (K6 : forall tpY rhoY, etriple segs (SPA segs (JGb W0 st0 A' Kc rho') (C6 W0 st0 3) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (espine_s6 1%nat st0 3 k6_0 NTH6s_0 ZC6s_0 s7s_0 ENT7s_0 SID7s_0 G6l_0 W6l_0 D6l_0 NX6l_0 NXC6_0 s6_ecert_0 A' Kc rho' tpY Q HUS HKc Hcnt'); [exact (K7 tpY)|].
    intros rhoY6l.
    assert (NXC6m_f : (GW <= ss_next (ax_S (C6m W0 st0 3)))%positive) by (apply Pos.leb_le; vm_cast_no_check (eq_refl true)).
    apply (espine_s6l 1%nat st0 3 W6m_0 D6m_0 NX6m_0 s6_0 sd6_0 R6_0 T6_0 He6_0 Hchk6_0 HT6_0 FBC6_0 FBT6_0 ENT6_0 SID6_0 NXC6m_f NXC6l_0 s6l_ecert_0 A' Kc rho' tpY Q HUS HKc).
    intros rhoY6b tpY6b.
    apply (espine_s6b 1%nat st0 3 s7j_0 ENT7j_0 SID7j_0 NXC6b_0 s6b_ecert_0 A' Kc rho' tpY6b Q HUS HKc). exact (K7 tpY6b). }
  apply (espine_s5 1%nat st0 3 s6n_0 ENT6n_0 SID6n_0 W5b_0 D5b_0 NX5b_0 F5f64_0 NXC5_0 s5_ecert_0 A' Kc rho' tp' Q HUS HKc Hcnt'); [exact (K6 tp')|].
  intros rhoX5b.
  apply (espine_s5b 1%nat st0 3 OV1_0 OV2_0 TAB1_0 TAB2_0 W1'_0 W2'_0 D1'_0 D2'_0 NX1'_0 NX2'_0 F1gt_0 F2le_0 F1_64_0 F2_64_0 s1_0 s2_0 ENT1_0 ENT2_0 SID1_0 SID2_0 NXC5b_0 s5b_ecert_0
           A' Kc rho' tp' Q HUS HKc).
  intros rhoX5c.
  apply (espine_s5c 1%nat st0 3 G5m1_0 W5m1_0 D5m1_0 NX5m1_0 s51_0 sd51_0 R51_0 T51_0 He51_0 Hchk51_0 HT51_0 FBC51_0 FBT51_0 ENT51_0 SID51_0 NXC51_0 NXC5c_0 s5c_ecert_0
           A' Kc rho' tp' Q HUS HKc Hcnt').
  intros rhoX5d tp5d.
  apply (espine_s5d 1%nat st0 3 G5m2_0 W5m2_0 D5m2_0 NX5m2_0 s52_0 sd52_0 R52_0 T52_0 He52_0 Hchk52_0 HT52_0 FBC52_0 FBT52_0 ENT52_0 SID52_0 NXC52_0 NXC5d_0 s5d_ecert_0
           A' Kc rho' tp5d Q HUS HKc Hcnt').
  intros rhoX5e tp5e.
  apply (espine_s5e 1%nat st0 3 s6j_0 ENT6j_0 SID6j_0 NXC5e_0 s5e_ecert_0 A' Kc rho' tp5e Q HUS HKc). exact (K6 tp5e).
Qed.

Theorem ecalloc_hit_tail_1 : ltac2:(tb__ "0|0|
S1aS2S8SfS2dQ40A1A1S19Vsegs;S30R2R1S38VCST;VXGL;VW0;Vst0;R4R3A6A5S2fS3R4A1S8S2eVsegs;S31Vsegs;S46VW0;Vst0;R7R6R5A5S1fVW0;Vst0;Z3A3R1R4A5R3A3FrhoX;F_;TQ;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp. exact (ecalloc_hit_tail_1_P A Kc rho tp (PFc CST XGL W0 st0 A Kc) (or_intror (or_introl eq_refl))).
Qed.
End HIT0TE.
End CallocHitTail1E.

(* [comment removed for export] *)
Module SegQCF_top.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "list"; "bool"; "nil"; "prod"; "nat"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "eval"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "qbatch"; "budget_bound"; "class_fresh"; "@Corelib.Init.Logic"; "eq"; "True"; "not"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "QP"; "JRD"; "JRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "clsB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.SegQCF_call"; "ENVC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "JOK"; "TRP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel"; "drainA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.SegQ3D_qcs"; "QC_full_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.SegQCF_states"; "PostD"; "PreD"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d9.SegQCF_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dg.SegQCF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.SegQCF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SegQF_ri OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.SegQ3D_qcs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dq.SegQCF_exit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma clsB_keep : ltac2:(tb__ "0|3|
SbSbS12S15Q40A1M0SaR1Pa6M1A2SaR2G1A2A3S12G0SaR2P9bM2A2SaR3G2A2A3S12G0ScR3S1fA2ScR4S1fA2A3F_;F_;Fr';Fr;").
Proof. intros r r' E1 E2. unfold clsB, vB, vSB. cbn [eval]. rewrite E1, E2. reflexivity. Qed.
Lemma ENVC_keep : ltac2:(tb__ "0|0|
SeSbSbS0S2bS0R1S2S0P9bS2S0Pa6S2S0Pc9S2S0Pd0S2S0PddS2S0PdeS2S0PdfS2S0Pe0S2S0Pe1S2S0Pe7S5S0A1A3A3A3A3A3A3A3A3A3A3A3S12S15Q40A1SaR3R2A2SaR4R2A2A3F_;Fv;S20R4R3A2S20R5R3A2F_;F_;Fr';Fr;FA;").
Proof.
  intros A r r' HV (EC & E201 & E208 & E221 & E222 & E223 & E224 & E225 & E231). unfold ENVC. cbv zeta.
  rewrite (clsB_keep r r') by (apply HV; cbn; tauto). rewrite !HV by (cbn; tauto). repeat split; assumption.
Qed.
Lemma QP_drain : ltac2:(tb__ "0|1|
SeSeS1cR2R1A2S14S11R3Z18M0A2A1S1cR4S25R3G0A2A2F_;F_;FA;FA0;").
Proof.
  intros A0 A (E & EL & EF) NF. split; [|split].
  - unfold same_but_qcs in *. rewrite E. unfold drainA. cbn. reflexivity.
  - unfold drainA. cbn [aa_cls]. rewrite length_list_upd. exact EL.
  - intros c Hc. unfold drainA. cbn [aa_cls]. rewrite nth_list_upd_other; [exact (EF c Hc)|].
    intros X0. apply NF. unfold class_fresh in *. rewrite X0. exact Hc.
Qed.

Section QCFTop.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Context {Q : assn} (X : trk Q).
Hypothesis HJD : ltac2:(tb__ "0|1|
SeS3SfA1M0G0S21VQ;VX;S1dS16VKc;A1VA0;Vrho0;R3R2R1A6A3Frest;Ftmp;FA;").
Hypothesis HJI : ltac2:(tb__ "0|1|
SeS1S1S7S3S6S1S1A2A1S3SfA1M0G0S21VQ;VX;S1eS16VKc;A1VA0;Vrho0;R7R6R5R4R3R2R1AaA3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA;").
Variable rest : list qbatch.
Hypothesis HDC : ltac2:(tb__ "0|3|
S4SeSbS3S15Q40A1A1S12S4R4S9A3S2cS10R4A1S24A2F_;S22VQ;VX;S23S1bS26Z1R5R4VKc;Z18M0A5S2aR5A1M1R3R2A5S1aS1bSdS18G1A1A1R3R2S2S6S17S19A2M2S8S17S19S29R5A1S27R4VKc;G0A3A4S5G2A1A3A5A4F_;Ftp1;Frho1;FA;Fg;").
Hypothesis HBUD : budget_bound A0 <= LIMIT.

Theorem qc_full_step : ltac2:(tb__ "0|0|
S28S16VKc;A1VA0;Vrho0;VQ;VX;Vrest;S3S15Q40A1A1S13L_;A7").
Proof.
  intros A a n0 nd tmp' rho tp _ HI HVx E166 HFL HC.
  pose proof HI as (I1 & I2 & I3 & I4 & (s & I5) & I6). pose proof (K0_laws Kc HKc) as HL.
  set (J := JRI (K0 Kc) A0 rho0 A a n0 nd [] tmp' rest).
  apply (tr_pure X _ (~ class_fresh A0 24 /\ Z.of_nat (length (cs_cache (SegQ_wf2.cls_of A 24))) = 2)).
  { intros [tr [ms md]] Hw. destruct (proj2 Hw) as (HK & _). cbn [w_tr w_cfg cfg_model fst snd] in HK. split.
    - apply (cls24_not_fresh (K0 Kc) HL A0 A (mkQB a [] s) rho tp tr md I2 I4 HK). rewrite (qall_A1 A I1), I5. left. reflexivity.
    - destruct (kq_facts segsA (K0 Kc) HL A rho tp _ _ HK) as [_ _ _ _ _ _ HCLS _ _ _ _ _ _]. pose proof (cv_len _ _ _ _ _ (HCLS I2 24 ltac:(lia))) as KL.
      change (max_count 24) with 2 in *. unfold SegQ_wf2.cls_of in *. lia. }
  intros (NFR & HFULL). set (g := drain_grows 24 (SegQ_wf2.cls_of A 24)).
  assert (HBG : g = true -> budget_bound A <= LIMIT).
  { intros _. destruct I4 as (ESB & _). unfold same_but_qcs in ESB. unfold budget_bound. rewrite ESB. cbn [aa_V aa_Km aa_Kf]. exact HBUD. }

  apply (tr_glue X _ J (S0F g) tp (fun r => ENVC A r /\ HVX r tmp' /\ rw r 166%positive = Z_to_bv 64 a)).
  { intros w Hw. destruct (qcf_entry Kc HKc A0 rho0 g A a s n0 nd tmp' rest rho tp w I1 I2 I3 I4 I5 HFULL eq_refl Hw E166) as (rho2 & H2 & HE & K2). exists rho2. split; [exact H2|].
    destruct HVx as (E184 & E185 & E186 & E187 & E208).
    destruct HE as (EC & st & _ & _ & E201 & _ & E221 & E222 & E223 & E224 & E225 & E231).
    split; [|split; [unfold HVX; rewrite !K2 by (cbn; tauto); tauto | rewrite K2 by (cbn; tauto); exact E166]].
    unfold ENVC. cbv zeta. rewrite (K2 208%positive) by (cbn; tauto). repeat split; assumption. }
  intros r2 (HE2 & HV2 & E2).

  apply (seg_F1 X g J r2 tp (HJI _ _ _ _ _ _ _)). intros Tx M r3 HIN HKp. cbn [TsF1 In] in HIN. destruct HIN as [E|[]]. injection E as <- <-.
  assert (KV3 : forall v, In v [155; 166; 201; 208; 221; 222; 223; 224; 225; 231]%positive -> rw r3 v = rw r2 v).
  { intros v Hv. destruct Hv as [<-|Hv]; [symmetry; apply (proj1 (proj1 HKp)); reflexivity|]. apply (keepsM_id VSF r2 r3 v HKp). unfold VSF. cbn in Hv |- *. tauto. }
  pose proof (ENVC_keep A r2 r3 KV3 HE2) as HE3.
  pose proof (HVX_keep VSF r2 r3 tmp' HKp ltac:(unfold VSF; cbn; tauto) HV2) as HV3.
  assert (E3 : rw r3 166%positive = Z_to_bv 64 a) by (rewrite KV3 by (cbn; tauto); exact E2).
  apply (tr_conseq X _ (SPA segsA J (C1 g) r3 tp)); [intros w Hw; exact (SPA_axforms segsA J _ r3 _ _ tp w (C1_eq g) Hw)|].

  apply (qcf_call Kc HKc A0 rho0 X HDC g A a s n0 nd tmp' rest r3 tp I1 I2 I4 I5 HFULL eq_refl HBG HE3).
  intros r5 tpL Hag5. set (J1 := JRI (K0 Kc) A0 rho0 (drainA A 24) a n0 nd [] tmp' rest).
  destruct (XF0 g) as (_ & _ & _ & _ & NXC).
  assert (KV5 : forall v, (v < 260)%positive -> rw r5 v = rw r3 v) by (intros v Hv; symmetry; apply (proj1 Hag5); rewrite NXC; exact Hv).
  pose proof (ENVC_keep A r3 r5 ltac:(intros v Hv; apply KV5; cbn in Hv; intuition (subst; reflexivity)) HE3) as HE5.
  assert (HV5 : HVX r5 tmp') by (destruct HV3 as (E184 & E185 & E186 & E187 & E208); unfold HVX; rewrite !KV5 by reflexivity; tauto).
  assert (E5 : rw r5 166%positive = Z_to_bv 64 a) by (rewrite KV5 by reflexivity; exact E3).

  apply (seg_F2 X g J1 r5 tpL (HJI _ _ _ _ _ _ _)). intros Tx M r6 HIN HKp6. cbn [TsF2 In] in HIN. destruct HIN as [E|[]]. injection E as <- <-.
  assert (KV6 : forall v, In v [155; 166; 201; 208; 221; 222; 223; 224; 225; 231]%positive -> rw r6 v = rw r5 v).
  { intros v Hv. destruct Hv as [<-|Hv]; [symmetry; apply (proj1 (proj1 HKp6)); reflexivity|]. apply (keepsM_id VSF r5 r6 v HKp6). unfold VSF. cbn in Hv |- *. tauto. }
  pose proof (ENVC_keep A r5 r6 KV6 HE5) as HE6.
  pose proof (HVX_keep VSF r5 r6 tmp' HKp6 ltac:(unfold VSF; cbn; tauto) HV5) as HV6.
  assert (E6 : rw r6 166%positive = Z_to_bv 64 a) by (rewrite KV6 by (cbn; tauto); exact E5).
  apply (tr_conseq X _ (SPA segsA J1 (Lx g) r6 tpL)).
  { intros w Hw. apply (SPA_axforms segsA J1 _ r6 _ _ tpL w (Lx_eq g)). exact (SPA_axforms segsA J1 _ r6 _ _ tpL w (Lm_eq g) Hw). }

  apply (tr_glue X _ J1 (Ly g) tpL (fun r => forall i, rw r i = rw r6 i)).
  { intros w Hw. exact (qcf_x1 Kc HKc A0 rho0 g A a s n0 nd tmp' rest r6 tpL w I1 I2 I4 I5 HFULL eq_refl HE6 Hw). }
  intros r7 RW7.
  set (A' := push_cache (set_q (drainA A 24) [] (tmp' ++ rest)) 24 (qb_id (aa_geom A) (mkQB a [] s))).
  apply (tr_glue X _ (JRD (K0 Kc) A0 rho0 A' tmp' rest) (Lz g) tpL (fun r => (forall i, rw r i = rw r7 i) /\ eval r clsB = Z_to_bv 64 24)).
  { intros w Hw. exact (qcf_x2a Kc HKc A0 rho0 g A a s n0 nd tmp' rest r7 tpL w I1 I2 I4 I5 HFULL Hw ltac:(rewrite RW7; exact E6)). }
  intros r8 (RW8 & EC8).
  assert (EGA : aa_geom A = aa_geom A0) by (destruct I4 as (ESB & _); unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  assert (HQW' : forall z, QW A' z -> QW A0 z).
  { intros z Hz. apply I3. exact (QW_push_batch (drainA A 24) (mkQB a [] s) (tmp' ++ rest) _ z I1 I5 Hz). }
  apply (tr_glue X _ (JRD (K0 Kc) A0 rho0 A' tmp' rest) RCr tpL (fun r => HVX r tmp')).
  { intros w Hw. apply (qcf_x2b Kc HKc A0 rho0 g A' tmp' rest r8 tpL w HQW' I2 EGA Hw EC8).
    - rewrite RW8, RW7. destruct HE6 as (_ & E201 & _). exact E201.
    - destruct HV6 as (E184 & E185 & E186 & E187 & E208). unfold HVX. rewrite !RW8, !RW7. tauto. }
  intros r9 HV9. apply (seg_D_CrM X _ r9 tpL (HJD _ _ _)). intros Tx M r10 HIN HKp10. cbn [In] in HIN. destruct HIN as [E|[]]. injection E as <- <-.
  apply (HC A' r10 tpL I); [|exact (HVX_keep _ r9 r10 tmp' HKp10 ltac:(cbn; tauto) HV9)].
  split; [reflexivity|]. split; [exact I2|]. split; [exact HQW'|]. split; [|split; [reflexivity|]].
  - apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv.QP_push; [exact (QP_drain A0 A I4 NFR) | lia | exact NFR].
  - intros z Hz. apply I6. exact (SF_push_batch (drainA A 24) (mkQB a [] s) (tmp' ++ rest) _ z I1 I5 Hz).
Qed.
End QCFTop.
End SegQCF_top.

(* [comment removed for export] *)
Module SegQIF_m1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQIF_m1"; "N"; "D_fa"; "D_fb"; "D_ga"; "D_gb"; "C1_fa"; "C1_fb"; "C1_ga"; "C1_gb"; "D_of"; "L1_fa"; "L1_fb"; "L1_ga"; "L1_gb"; "Lx_fa"; "Lx_fb"; "Lx_ga"; "Lx_gb"; "RF_fa"; "RF_fb"; "RF_ga"; "RF_gb"; "S0_fa"; "S0_fb"; "S0_ga"; "S0_gb"; "T1f_fa"; "T1f_fb"; "T1f_ga"; "T1f_gb"; "XC_fa"; "XC_fb"; "XC_ga"; "XC_gb"; "XX_fa"; "XX_fb"; "XX_ga"; "XX_gb"; "sF_fa"; "sF_fb"; "sF_ga"; "sF_gb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs"; "mcert"; "mkMD"; "mdata"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQS_lib RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQIF_env SegQIF_mdefs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition N : Z := 1.

Definition S0_fa : axst := Eval vm_compute in (bumpM (S0M_of N false false) NXM).
Definition L1_fa : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_fa)).
Definition XC_fa : list axform := Eval vm_compute in (XC_of false false L1_fa).
Definition C1_fa : axst := Eval vm_compute in (optA L1_fa (apply_axforms L1_fa XC_fa)).
Definition sF_fa : wsub := Eval vm_compute in (sF_of N false C1_fa).
Definition RF_fa : list sobj := Eval vm_compute in (optR (entails_frA C1_fa (PreD N false) sF_fa)).
Definition T1f_fa : axst := Eval vm_compute in (T1f_of N false C1_fa sF_fa RF_fa).
Definition XX_fa : list axform := Eval vm_compute in (XX_of N false false T1f_fa).
Definition Lx_fa : axst := Eval vm_compute in (optA T1f_fa (apply_axforms T1f_fa XX_fa)).
Definition D_fa : mdata := ltac2:(tb__ "0|0|
S2eS19SdS21S8S29S15S1dS25S11A9").
Lemma cert_fa : ltac2:(tb__ "0|0|
S2dS3S1S1S4A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_fb : axst := Eval vm_compute in (bumpM (S0M_of N false true) NXM).
Definition L1_fb : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_fb)).
Definition XC_fb : list axform := Eval vm_compute in (XC_of false true L1_fb).
Definition C1_fb : axst := Eval vm_compute in (optA L1_fb (apply_axforms L1_fb XC_fb)).
Definition sF_fb : wsub := Eval vm_compute in (sF_of N false C1_fb).
Definition RF_fb : list sobj := Eval vm_compute in (optR (entails_frA C1_fb (PreD N false) sF_fb)).
Definition T1f_fb : axst := Eval vm_compute in (T1f_of N false C1_fb sF_fb RF_fb).
Definition XX_fb : list axform := Eval vm_compute in (XX_of N false true T1f_fb).
Definition Lx_fb : axst := Eval vm_compute in (optA T1f_fb (apply_axforms T1f_fb XX_fb)).
Definition D_fb : mdata := ltac2:(tb__ "0|0|
S2eS1aSeS22S9S2aS16S1eS26S12A9").
Lemma cert_fb : ltac2:(tb__ "0|0|
S2dS3S1S2S5A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_ga : axst := Eval vm_compute in (bumpM (S0M_of N true false) NXM).
Definition L1_ga : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_ga)).
Definition XC_ga : list axform := Eval vm_compute in (XC_of true false L1_ga).
Definition C1_ga : axst := Eval vm_compute in (optA L1_ga (apply_axforms L1_ga XC_ga)).
Definition sF_ga : wsub := Eval vm_compute in (sF_of N true C1_ga).
Definition RF_ga : list sobj := Eval vm_compute in (optR (entails_frA C1_ga (PreD N true) sF_ga)).
Definition T1f_ga : axst := Eval vm_compute in (T1f_of N true C1_ga sF_ga RF_ga).
Definition XX_ga : list axform := Eval vm_compute in (XX_of N true false T1f_ga).
Definition Lx_ga : axst := Eval vm_compute in (optA T1f_ga (apply_axforms T1f_ga XX_ga)).
Definition D_ga : mdata := ltac2:(tb__ "0|0|
S2eS1bSfS23SaS2bS17S1fS27S13A9").
Lemma cert_ga : ltac2:(tb__ "0|0|
S2dS3S2S1S6A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_gb : axst := Eval vm_compute in (bumpM (S0M_of N true true) NXM).
Definition L1_gb : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_gb)).
Definition XC_gb : list axform := Eval vm_compute in (XC_of true true L1_gb).
Definition C1_gb : axst := Eval vm_compute in (optA L1_gb (apply_axforms L1_gb XC_gb)).
Definition sF_gb : wsub := Eval vm_compute in (sF_of N true C1_gb).
Definition RF_gb : list sobj := Eval vm_compute in (optR (entails_frA C1_gb (PreD N true) sF_gb)).
Definition T1f_gb : axst := Eval vm_compute in (T1f_of N true C1_gb sF_gb RF_gb).
Definition XX_gb : list axform := Eval vm_compute in (XX_of N true true T1f_gb).
Definition Lx_gb : axst := Eval vm_compute in (optA T1f_gb (apply_axforms T1f_gb XX_gb)).
Definition D_gb : mdata := ltac2:(tb__ "0|0|
S2eS1cS10S24SbS2cS18S20S28S14A9").
Lemma cert_gb : ltac2:(tb__ "0|0|
S2dS3S2S2S7A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition D_of (g vb : bool) : mdata := ltac2:(tb__ "0|1|
S0S2fLg;Vg;S0S2fLvb;M0Vvb;S7S6X0x2G0Vvb;S5S4X0x2X0x2").
Lemma cert_of : ltac2:(tb__ "0|0|
S0S0S2dS3R2R1ScR2R1A2A4Fvb;Fg;").
Proof. intros [|] [|]; [exact cert_gb | exact cert_ga | exact cert_fb | exact cert_fa]. Qed.
End SegQIF_m1.

(* [comment removed for export] *)
Module SegQIF_m2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQIF_m2"; "N"; "D_fa"; "D_fb"; "D_ga"; "D_gb"; "C1_fa"; "C1_fb"; "C1_ga"; "C1_gb"; "D_of"; "L1_fa"; "L1_fb"; "L1_ga"; "L1_gb"; "Lx_fa"; "Lx_fb"; "Lx_ga"; "Lx_gb"; "RF_fa"; "RF_fb"; "RF_ga"; "RF_gb"; "S0_fa"; "S0_fb"; "S0_ga"; "S0_gb"; "T1f_fa"; "T1f_fb"; "T1f_ga"; "T1f_gb"; "XC_fa"; "XC_fb"; "XC_ga"; "XC_gb"; "XX_fa"; "XX_fb"; "XX_ga"; "XX_gb"; "sF_fa"; "sF_fb"; "sF_ga"; "sF_gb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs"; "mcert"; "mkMD"; "mdata"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQS_lib RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQIF_env SegQIF_mdefs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition N : Z := 2.

Definition S0_fa : axst := Eval vm_compute in (bumpM (S0M_of N false false) NXM).
Definition L1_fa : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_fa)).
Definition XC_fa : list axform := Eval vm_compute in (XC_of false false L1_fa).
Definition C1_fa : axst := Eval vm_compute in (optA L1_fa (apply_axforms L1_fa XC_fa)).
Definition sF_fa : wsub := Eval vm_compute in (sF_of N false C1_fa).
Definition RF_fa : list sobj := Eval vm_compute in (optR (entails_frA C1_fa (PreD N false) sF_fa)).
Definition T1f_fa : axst := Eval vm_compute in (T1f_of N false C1_fa sF_fa RF_fa).
Definition XX_fa : list axform := Eval vm_compute in (XX_of N false false T1f_fa).
Definition Lx_fa : axst := Eval vm_compute in (optA T1f_fa (apply_axforms T1f_fa XX_fa)).
Definition D_fa : mdata := ltac2:(tb__ "0|0|
S2eS19SdS21S8S29S15S1dS25S11A9").
Lemma cert_fa : ltac2:(tb__ "0|0|
S2dS3S1S1S4A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_fb : axst := Eval vm_compute in (bumpM (S0M_of N false true) NXM).
Definition L1_fb : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_fb)).
Definition XC_fb : list axform := Eval vm_compute in (XC_of false true L1_fb).
Definition C1_fb : axst := Eval vm_compute in (optA L1_fb (apply_axforms L1_fb XC_fb)).
Definition sF_fb : wsub := Eval vm_compute in (sF_of N false C1_fb).
Definition RF_fb : list sobj := Eval vm_compute in (optR (entails_frA C1_fb (PreD N false) sF_fb)).
Definition T1f_fb : axst := Eval vm_compute in (T1f_of N false C1_fb sF_fb RF_fb).
Definition XX_fb : list axform := Eval vm_compute in (XX_of N false true T1f_fb).
Definition Lx_fb : axst := Eval vm_compute in (optA T1f_fb (apply_axforms T1f_fb XX_fb)).
Definition D_fb : mdata := ltac2:(tb__ "0|0|
S2eS1aSeS22S9S2aS16S1eS26S12A9").
Lemma cert_fb : ltac2:(tb__ "0|0|
S2dS3S1S2S5A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_ga : axst := Eval vm_compute in (bumpM (S0M_of N true false) NXM).
Definition L1_ga : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_ga)).
Definition XC_ga : list axform := Eval vm_compute in (XC_of true false L1_ga).
Definition C1_ga : axst := Eval vm_compute in (optA L1_ga (apply_axforms L1_ga XC_ga)).
Definition sF_ga : wsub := Eval vm_compute in (sF_of N true C1_ga).
Definition RF_ga : list sobj := Eval vm_compute in (optR (entails_frA C1_ga (PreD N true) sF_ga)).
Definition T1f_ga : axst := Eval vm_compute in (T1f_of N true C1_ga sF_ga RF_ga).
Definition XX_ga : list axform := Eval vm_compute in (XX_of N true false T1f_ga).
Definition Lx_ga : axst := Eval vm_compute in (optA T1f_ga (apply_axforms T1f_ga XX_ga)).
Definition D_ga : mdata := ltac2:(tb__ "0|0|
S2eS1bSfS23SaS2bS17S1fS27S13A9").
Lemma cert_ga : ltac2:(tb__ "0|0|
S2dS3S2S1S6A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_gb : axst := Eval vm_compute in (bumpM (S0M_of N true true) NXM).
Definition L1_gb : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_gb)).
Definition XC_gb : list axform := Eval vm_compute in (XC_of true true L1_gb).
Definition C1_gb : axst := Eval vm_compute in (optA L1_gb (apply_axforms L1_gb XC_gb)).
Definition sF_gb : wsub := Eval vm_compute in (sF_of N true C1_gb).
Definition RF_gb : list sobj := Eval vm_compute in (optR (entails_frA C1_gb (PreD N true) sF_gb)).
Definition T1f_gb : axst := Eval vm_compute in (T1f_of N true C1_gb sF_gb RF_gb).
Definition XX_gb : list axform := Eval vm_compute in (XX_of N true true T1f_gb).
Definition Lx_gb : axst := Eval vm_compute in (optA T1f_gb (apply_axforms T1f_gb XX_gb)).
Definition D_gb : mdata := ltac2:(tb__ "0|0|
S2eS1cS10S24SbS2cS18S20S28S14A9").
Lemma cert_gb : ltac2:(tb__ "0|0|
S2dS3S2S2S7A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition D_of (g vb : bool) : mdata := ltac2:(tb__ "0|1|
S0S2fLg;Vg;S0S2fLvb;M0Vvb;S7S6X0x2G0Vvb;S5S4X0x2X0x2").
Lemma cert_of : ltac2:(tb__ "0|0|
S0S0S2dS3R2R1ScR2R1A2A4Fvb;Fg;").
Proof. intros [|] [|]; [exact cert_gb | exact cert_ga | exact cert_fb | exact cert_fa]. Qed.
End SegQIF_m2.

(* [comment removed for export] *)
Module SegQIF_m3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.SegQIF_m3"; "N"; "D_fa"; "D_fb"; "D_ga"; "D_gb"; "C1_fa"; "C1_fb"; "C1_ga"; "C1_gb"; "D_of"; "L1_fa"; "L1_fb"; "L1_ga"; "L1_gb"; "Lx_fa"; "Lx_fb"; "Lx_ga"; "Lx_gb"; "RF_fa"; "RF_fb"; "RF_ga"; "RF_gb"; "S0_fa"; "S0_fb"; "S0_ga"; "S0_gb"; "T1f_fa"; "T1f_fb"; "T1f_ga"; "T1f_gb"; "XC_fa"; "XC_fb"; "XC_ga"; "XC_gb"; "XX_fa"; "XX_fb"; "XX_ga"; "XX_gb"; "sF_fa"; "sF_fb"; "sF_ga"; "sF_gb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs"; "mcert"; "mkMD"; "mdata"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SysCallA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQS_lib RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQIF_env SegQIF_mdefs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition N : Z := 3.

Definition S0_fa : axst := Eval vm_compute in (bumpM (S0M_of N false false) NXM).
Definition L1_fa : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_fa)).
Definition XC_fa : list axform := Eval vm_compute in (XC_of false false L1_fa).
Definition C1_fa : axst := Eval vm_compute in (optA L1_fa (apply_axforms L1_fa XC_fa)).
Definition sF_fa : wsub := Eval vm_compute in (sF_of N false C1_fa).
Definition RF_fa : list sobj := Eval vm_compute in (optR (entails_frA C1_fa (PreD N false) sF_fa)).
Definition T1f_fa : axst := Eval vm_compute in (T1f_of N false C1_fa sF_fa RF_fa).
Definition XX_fa : list axform := Eval vm_compute in (XX_of N false false T1f_fa).
Definition Lx_fa : axst := Eval vm_compute in (optA T1f_fa (apply_axforms T1f_fa XX_fa)).
Definition D_fa : mdata := ltac2:(tb__ "0|0|
S2eS19SdS21S8S29S15S1dS25S11A9").
Lemma cert_fa : ltac2:(tb__ "0|0|
S2dS3S1S1S4A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_fb : axst := Eval vm_compute in (bumpM (S0M_of N false true) NXM).
Definition L1_fb : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_fb)).
Definition XC_fb : list axform := Eval vm_compute in (XC_of false true L1_fb).
Definition C1_fb : axst := Eval vm_compute in (optA L1_fb (apply_axforms L1_fb XC_fb)).
Definition sF_fb : wsub := Eval vm_compute in (sF_of N false C1_fb).
Definition RF_fb : list sobj := Eval vm_compute in (optR (entails_frA C1_fb (PreD N false) sF_fb)).
Definition T1f_fb : axst := Eval vm_compute in (T1f_of N false C1_fb sF_fb RF_fb).
Definition XX_fb : list axform := Eval vm_compute in (XX_of N false true T1f_fb).
Definition Lx_fb : axst := Eval vm_compute in (optA T1f_fb (apply_axforms T1f_fb XX_fb)).
Definition D_fb : mdata := ltac2:(tb__ "0|0|
S2eS1aSeS22S9S2aS16S1eS26S12A9").
Lemma cert_fb : ltac2:(tb__ "0|0|
S2dS3S1S2S5A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_ga : axst := Eval vm_compute in (bumpM (S0M_of N true false) NXM).
Definition L1_ga : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_ga)).
Definition XC_ga : list axform := Eval vm_compute in (XC_of true false L1_ga).
Definition C1_ga : axst := Eval vm_compute in (optA L1_ga (apply_axforms L1_ga XC_ga)).
Definition sF_ga : wsub := Eval vm_compute in (sF_of N true C1_ga).
Definition RF_ga : list sobj := Eval vm_compute in (optR (entails_frA C1_ga (PreD N true) sF_ga)).
Definition T1f_ga : axst := Eval vm_compute in (T1f_of N true C1_ga sF_ga RF_ga).
Definition XX_ga : list axform := Eval vm_compute in (XX_of N true false T1f_ga).
Definition Lx_ga : axst := Eval vm_compute in (optA T1f_ga (apply_axforms T1f_ga XX_ga)).
Definition D_ga : mdata := ltac2:(tb__ "0|0|
S2eS1bSfS23SaS2bS17S1fS27S13A9").
Lemma cert_ga : ltac2:(tb__ "0|0|
S2dS3S2S1S6A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition S0_gb : axst := Eval vm_compute in (bumpM (S0M_of N true true) NXM).
Definition L1_gb : axst := Eval vm_compute in (leaf 0 (runA 300 [DH_ENT] S0_gb)).
Definition XC_gb : list axform := Eval vm_compute in (XC_of true true L1_gb).
Definition C1_gb : axst := Eval vm_compute in (optA L1_gb (apply_axforms L1_gb XC_gb)).
Definition sF_gb : wsub := Eval vm_compute in (sF_of N true C1_gb).
Definition RF_gb : list sobj := Eval vm_compute in (optR (entails_frA C1_gb (PreD N true) sF_gb)).
Definition T1f_gb : axst := Eval vm_compute in (T1f_of N true C1_gb sF_gb RF_gb).
Definition XX_gb : list axform := Eval vm_compute in (XX_of N true true T1f_gb).
Definition Lx_gb : axst := Eval vm_compute in (optA T1f_gb (apply_axforms T1f_gb XX_gb)).
Definition D_gb : mdata := ltac2:(tb__ "0|0|
S2eS1cS10S24SbS2cS18S20S28S14A9").
Lemma cert_gb : ltac2:(tb__ "0|0|
S2dS3S2S2S7A4").
Proof.
  constructor; cbn [m_S0 m_L1 m_XC m_C1 m_sF m_RF m_T1f m_XX m_Lx].
  - vm_cast_no_check (eq_refl true).
  - split; [reflexivity | vm_cast_no_check (eq_refl true)].
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vmr.
  - vm_cast_no_check (eq_refl true).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - intros pce. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
Qed.

Definition D_of (g vb : bool) : mdata := ltac2:(tb__ "0|1|
S0S2fLg;Vg;S0S2fLvb;M0Vvb;S7S6X0x2G0Vvb;S5S4X0x2X0x2").
Lemma cert_of : ltac2:(tb__ "0|0|
S0S0S2dS3R2R1ScR2R1A2A4Fvb;Fg;").
Proof. intros [|] [|]; [exact cert_gb | exact cert_ga | exact cert_fb | exact cert_fa]. Qed.
End SegQIF_m3.

