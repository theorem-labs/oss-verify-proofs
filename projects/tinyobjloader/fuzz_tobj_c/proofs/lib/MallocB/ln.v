(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ks.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rzone le.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_mdefs.

(* [comment removed for export] *)
Module CallocHitTail0E.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "SVar"; "SLit"; "SPUle"; "rw"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "pair"; "prod"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "prim_room"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "V_RZ"; "C9"; "C9p"; "E3p"; "C10a"; "C10b"; "C10pa"; "C10pb"; "C9ma"; "C9mb"; "C9mpa"; "C9mpb"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Logic"; "not"; "eq"; "or"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "JLc_ok"; "Lc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineCallocE9"; "es9c_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineCallocEi"; "ECert10a_0"; "ECert10b_0"; "ECert10pa_0"; "ECert10pb_0"; "ECert9a_0"; "ECert9b_0"; "ECert9pa_0"; "ECert9pb_0"; "NX10a_0"; "NX10b_0"; "NX10pa_0"; "NX10pb_0"; "NX9fa_0"; "NX9fb_0"; "NX9fpa_0"; "NX9fpb_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS9i"; "D9ma_0"; "D9mb_0"; "D9mpa_0"; "D9mpb_0"; "ENT10a_0"; "ENT10b_0"; "ENT10pa_0"; "ENT10pb_0"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"; "FBCma_0"; "FBCmb_0"; "FBCmpa_0"; "FBCmpb_0"; "FBTma_0"; "FBTmb_0"; "FBTmpa_0"; "FBTmpb_0"; "FH_a_0"; "FH_b_0"; "FH_pa_0"; "FH_pb_0"; "HCC9ma_0"; "HCC9mb_0"; "HCC9mpa_0"; "HCC9mpb_0"; "HTma_0"; "HTmb_0"; "HTmpa_0"; "HTmpb_0"; "Hchkma_0"; "Hchkmb_0"; "Hchkmpa_0"; "Hchkmpb_0"; "Hema_0"; "Hemb_0"; "Hempa_0"; "Hempb_0"; "NX9ma_0"; "NX9mb_0"; "NX9mpa_0"; "NX9mpb_0"; "NXCma_0"; "NXCmb_0"; "NXCmpa_0"; "NXCmpb_0"; "Rma_0"; "Rmb_0"; "Rmpa_0"; "Rmpb_0"; "SID10a_0"; "SID10b_0"; "SID10pa_0"; "SID10pb_0"; "T9a_0"; "T9b_0"; "T9pa_0"; "T9pb_0"; "W9ma_0"; "W9mb_0"; "W9mpa_0"; "W9mpb_0"; "hcells_a"; "hcells_b"; "hcells_pa";
"hcells_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "sdma_0"; "sdmb_0"; "sdmpa_0"; "sdmpb_0"; "sf_a"; "sf_b"; "sf_pa"; "sf_pb"; "sma_0"; "smb_0"; "smpa_0"; "smpb_0"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ks.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocS5i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocS6i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocS7i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.SpineCallocS8i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS9i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.CallocHitTail0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineCallocE9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineCallocEi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.CDepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kn.CDepotCallH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineCallocS5t OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
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
Let law_die : forall A rho tp md, AInvA segsA A rho tp md -> cell_ok (view segsA (rm rho)) (mkACell 0x17fbdc 4 0) := AInvA_die.
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
Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x17fbdc 4 0) := AInvA_die.
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
    apply (espine_s7 0%nat st0 2 OV7a_0 OV7b_0 TAB7a_0 TAB7b_0 W7a_0 W7b_0 D7a_0 D7b_0 NX7a_0 NX7b_0 G7a_0 G7b_0 F7a_0 F7b_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.SpineCallocS8i.s8a_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.SpineCallocS8i.s8b_0
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
Module F0T_hbN_exit.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "iff"; "False"; "@Corelib.Init.Datatypes"; "prod"; "cons"; "list"; "pair"; "bool"; "fst"; "nat"; "nil"; "snd"; "app"; "false"; "option"; "true"; "None"; "andb"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "modulo"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "rw"; "sv"; "rm"; "valuation"; "odefault"; "ob_dflt"; "rl"; "ss_objs"; "DUnknown"; "SVar"; "eval"; "obj_range"; "smatch"; "tfact"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.F0T_hbN_exit"; "ROSh"; "TZh"; "Prosh"; "STSH"; "XKh"; "XRh"; "qsz_spec"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "client_addrA"; "client_shadowA"; "AE_A"; "JL_free"; "UStopLe"; "Wcan"; "mem_keptA"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue"; "spec_range"; "coverb"; "spec_covered"; "spec_small"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_unmap"; "DUZh"; "JH2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "ag_ctx"; "ag_spacebeg"; "ag_pab"; "ag_thread"; "aa_live"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "sobj_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "SEC_INST"; "IA_BEG"; "IA_END"; "fs_footb"; "fs_inv"; "geom_ok"; "live_sep"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states"; "XM_hb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "kSpaceSize"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "in_rangesZ"; "restrictv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "QRD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "chunk_zone"; "chunk_sh_zone"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "vmd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_in_view"; "rd_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit"; "sv_varsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "nocellsF"; "NRTX"; "REST_of"; "XK_of"; "XR_of"; "nkeep"; "sX_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_entry"; "N_hb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "O_stQ"; "O_stT1"; "O_stT2"; "cQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.F0T_hbN_exit.ExitH"; "EXPIN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.InvQ11"; "freeBigA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundW SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv ReprGlue Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 RebuildM InvLaws SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_exit.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_exit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2 SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rzone F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require le.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.InvQ10b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.InvQ11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_rebuildW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_unmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j1.UnwT_pres OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition qsz_spec : carve_spec := ltac2:(tb__ "0|4|
ScS9S9S23S0A2M0S0A2SbS9S9S0SfA2M1S23A2M2A1ScG0S0ScS23S0S8bZ18M3A4Z20A4SaG2ScG1S23ScS0SfG3U8A4S2bP7bA1A4S10G2A1A3A4").

Definition ROSh : list carve_spec := ltac2:(tb__ "0|0|
S12S19S7cS12S19S71S19U3S85A3SaS19S3bS10S19A1A3A3A3").

Definition STSH : list sobj := ltac2:(tb__ "0|0|
S72S21S21S7bSaS21S89SaS21S88SaS21S8aS10S21A1A3A3A3A4").
Definition rclshb (R : list sobj) : bool := ltac2:(tb__ "0|0|
S3dS21S21S18S3eS21S57R1A1S72S19S21S1aS35A4A3S3eS21S57S7bR1A1A1S38A3A2Lo;VR;A3").
Definition rcivhb (R : list sobj) : bool := ltac2:(tb__ "0|0|
S3dS19S19S3eS21S57S1aR1A1A1VR;A3Lk;S35A3").
Definition runkb (R : list sobj) : bool := ltac2:(tb__ "0|1|
S3dS21S21S26SdLx;S27R1A1S15S13S13S1S13Ll;M0G0S0S23SbS9S0S0A2A1SbS2fA1S13Ltmpl;Lflds;Lcnt;Lesz;X26x6Lo;VR;A3").

Definition XKh (nW : nat) (XF : axst) : axst := ltac2:(tb__ "0|0|
S7eVnW;S66VXF;A1A2").
Definition KEPTh (nW : nat) (XF : axst) : list sobj := ltac2:(tb__ "0|0|
S71S21S80VnW;A1S29S56S66VXF;A1A1A1A3").
Definition RESTh (nW : nat) (XF : axst) : list sobj := ltac2:(tb__ "0|0|
S7dVnW;S66VXF;A1A2").
Definition XRh (nW : nat) (XF : axst) : axst := ltac2:(tb__ "0|0|
S7fS39VnW;VXF;A2A1").
Definition sXh (nW : nat) (XF : axst) : wsub := ltac2:(tb__ "0|0|
S81S3aVnW;VXF;A2S44VnW;A1S43A3").
Record hbexit_ok (nW : nat) (XF : axst) : Prop := mkHBX {
  x_AXE : apply_axforms XF (XEX_hb XF) = Some (XM_hb XF);
  x_WXR : swf (ax_S (XRh nW XF)) = true;
  x_DXR : state_diff (ax_S (XKh nW XF)) (ax_S (XRh nW XF)) = Some ([(SLit TP_A, SVar 24)], []);
  x_NXR : ss_next (ax_S (XRh nW XF)) = ss_next (ax_S (XKh nW XF));
  x_EQR : ax_setS (XKh nW XF) (ax_S (XRh nW XF)) = XRh nW XF;
  x_ENT : entailsA (XRh nW XF) (L_free_tol AE_A) (sXh nW XF) = true;
  x_SID : wsub_id_below (sXh nW XF) NF = true;
  x_RCLS : rclshb (RESTh nW XF) = true;
  x_RCIV : rcivhb (RESTh nW XF) = true;
  x_RUNK : runkb (RESTh nW XF) = true
}.

Lemma ROSh_small : Forall spec_small ROSh.
Proof.
  unfold ROSh. apply Forall_app. split; [exact NRTX_small|].
  unfold N_hb, qsz_spec, spec_small, SEC_INST. cbn [firstn app].
  repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.
Lemma ROSh_coverb : ltac2:(tb__ "0|0|
S3SdS3dS19S49S35A3S15A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Prosh (i : positive) : bool := ltac2:(tb__ "0|0|
S3eS1S8fVi;A1SaS1PcSaS1P88SaS1P97SaS1P98SaS1P99SaS1P9aSaS1P9bSaS1P7bSaS1Pc3SaS1Pc8S10S1A1A3A3A3A3A3A3A3A3A3A3A3").
Lemma ROSh_varsb : ltac2:(tb__ "0|5|
S3SdS3dS19S19S9S9S9S23S0A2M0S0A2M1SbS9S9S0SfA2M2S23A2M3A1M4A2SdLk;R1G1G4G1SdLp;R2G0S0G0SdLp0;R2S23S0S17S7aS37R2A2S3dG3G3G3SdLc;R1G2S23G2SdLp;R2S0SfS7aS37R3A2Ln;Lz;X9x1Le;Lp;X9x1Lc;R5A3A2Lz0;Lb;X9x1Lz;Lp0;X9x1Lcs;Lp;X9x1Lk;S35A3S15A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma ROSh_zone : ltac2:(tb__ "0|8|
S53S25S19S0S60R4A1S3S30Q40M0A1M1S22R4P97A2S31G0S51R5A1A2A3S3G1S22R5P98A2S31G0S4eR6A1A2A3S2S1bZ0M2S32G0S22R6PcA2A2M3A2S1cG3S1eZ2Z2fA2A2A2S3cS19R6S35A3S2S1bSeS0S0S48R8R7A2M4A3R6A2S1cR6S11S0S0G4A3A2A2S5S2S2S1bG2R7A2S1cR7S67A2A2S4S2S1bS1dS5bZ38A2R7A2S1cR7Zead30A2A2A1A2S5S2S1bS51RaA1M5R7A2S1cR7S1dG5Z1000M6A2A2A2S2S1bS4eRaA1M7R7A2S1cR7S1dG7G6A2A2A2A2A2F_;F_;F_;F_;F_;F_;Fa;Fk;Frho;FG;").
Proof.
  intros G rho k a HG E151 E152 B12 Hk Ha.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range G) as TG.
  assert (LITOK : forallb (fun k : carve_spec => let '(b, lo, hi, _) := k in
             negb (sv_eqb b (SLit 0)) || ((0 <=? lo) && (hi <=? IMG_HI) && ((hi <=? SEC_INST + 56) || (0xead30 <=? lo)))) ROSh = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (proj1 (forallb_forall _ _) LITOK k Hk) as LK.
  destruct k as [[[b lo] hi] cs]. destruct (sv_eqb b (SLit 0)) eqn:EB.
  - apply sv_eqb_sound in EB. subst b. cbn [negb orb] in LK. apply andb_prop in LK as [LK L3]. apply andb_prop in LK as [L1 L2].
    apply Z.leb_le in L1. apply Z.leb_le in L2. apply orb_prop in L3.
    cbn [spec_range fst snd eval] in Ha. unfold IMG_HI in *. rewrite u64_lit in Ha by lia. left.
    destruct L3 as [L3|L3]; apply Z.leb_le in L3; lia.
  - clear LK LITOK. unfold ROSh, NRTX, N_rest, N_fn, N_hb, qsz_spec in Hk. cbn [tl app In firstn] in Hk. unfold cQ, vT, vCTX, vTOP, vBOT, vSB, vMINq, iam_base, vRISh, vPAB in Hk.
    repeat (destruct Hk as [E|Hk]; [injection E as <- <- <- <-; cbn in EB; try discriminate; cbn [spec_range fst snd eval] in Ha; rewrite ?E151, ?E152, ?add_val, ?u64_lit in Ha by lia |]).
    all: try (right; lia).
    all: try (right; left; rewrite Z.mod_small in Ha by lia; lia).
    all: try (destruct Hk).

    left. rewrite sll_val, srl_val in Ha. change (32 mod 64) with 32 in Ha. change (3 mod 64) with 3 in Ha.
      rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 in Ha by lia.
      pose proof (Z.div_lt_upper_bound (bv_unsigned (rw rho 12%positive)) (2 ^ 32) (2 ^ 15) ltac:(lia) ltac:(lia)).
      pose proof (Z.div_pos (bv_unsigned (rw rho 12%positive)) (2 ^ 32) ltac:(lia) ltac:(lia)).
      rewrite Z.mod_small in Ha by lia. unfold IMG_HI, SEC_INST. lia.
Qed.

Definition TZh (A : AA) (ch : sec_chunk) (z : Z) : Prop := ltac2:(tb__ "0|0|
S5S6eVA;Vz;A2S5S6fVch;Vz;A2S70Vch;Vz;A2A2A2").

Section ExitH.
Local Notation segs := segsA (only parsing).
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0S6cVCST;R1A2S5S6cS87R2A2S2S1bS5cR2A2S1cR2S5dA2A2A2S8F_;F_;Fa;").
Variable nW : nat.
Let W : list ulink := Wcan nW.
Variable XF : axst.
Hypothesis XOK : hbexit_ok nW XF.
Variables (A : AA) (Kc : KcA) (rho : valuation) (tp : list word) (p n t : Z) (jv : junkF) (keep : Z -> Prop).
Variables (A' : AA) (rho1' : valuation) (l1 l2 : list (Z * Z)) (i : nat) (ch : sec_chunk).
Let rho1 : valuation := ltac2:(tb__ "0|0|
S86VA;Vrho;Vp;Vn;Vt;Vjv;A6").
Let A2 : AA := ltac2:(tb__ "0|0|
S8dVA';Vl1;Vl2;Vi;A4").
Let G : ageom := aa_geom A'.
Let T : Z := ag_thread G.
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Let XM : axst := XM_hb XF.
Let XK : axst := XKh nW XF.
Let XR : axst := XRh nW XF.
Let KEPT : list sobj := KEPTh nW XF.
Let REST : list sobj := RESTh nW XF.
Let sX : wsub := sXh nW XF.
Hypothesis HKc : Kc_ok Kc.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S3S0S32Q40S22Vrho;PcA2A2Vp;A3").
Hypothesis Hn13 : ltac2:(tb__ "0|0|
S3S0S32Q40S22Vrho;PdA2A2Vn;A3").
Hypothesis HR : rigF rho rho1.
Hypothesis HDO : depot_onlyKf A A'.
Hypothesis HLK : ltac2:(tb__ "0|0|
S8eVkeep;Vrho1;Vrho1';A3").
Hypothesis HKEEP : ltac2:(tb__ "0|0|
S0S5S3fVCST;VA;R1A3S40VCST;VXGL;VA;R1A4A2Vkeep;R2A1F_;Fa;").
Hypothesis HLV : ltac2:(tb__ "0|1|
S3SbS9S0S0A2M0A1S52VA';A1S12G0Vl1;SaG0ScS0S0Vp;Vn;A4Vl2;A3A3A3").

Hypothesis HPIN : ltac2:(tb__ "0|2|
S2S3S30Q40M0A1M1S22Vrho1';P97A2S31G0VT;A2A3S2S3G1S22Vrho1';P98A2S31G0S4eVG;A1A2A3S2S3G1S22Vrho1';P9bA2S31G0S4fVG;A1A2A3S2S3G1S22Vrho1';PcA2S31G0Vp;A2A3S2S1bZ0Vp;A2S1cVp;S1eZ2Z2fA2A2A2A2A2A2A2").

Hypothesis HZ_T : ltac2:(tb__ "0|0|
S0S2S1bVT;R1A2S1cR1S1dVT;Z1000A2A2A2S4S4cVA';Vi;Vch;R2A4A1F_;Fz;").
Hypothesis HZ_C : ltac2:(tb__ "0|1|
S0S2S1bS4eVG;A1M0R1A2S1cR1S1dG0Z1000A2A2A2S4S4cVA';Vi;Vch;R2A4A1F_;Fz;").
Hypothesis HZ_L : ltac2:(tb__ "0|0|
S0S2S1bZ0R1A2S1cR1S67A2A2S4S2S1bS1dS5bZ38A2R2A2S1cR2Zead30A2A2A1S4S4cVA';Vi;Vch;R3A4A1F_;F_;Fz;").
Hypothesis CHB : ltac2:(tb__ "0|3|
S2S3S0S1fVh;Z8M0A2Z0M1A3S2S3S0S1fVmsz;G0A2G1A3S2S1bS67Vh;A2S2S1bG1Vmsz;A2S2S1cS1dVh;Vmsz;A2M2S1eZ2Z2fA2A2S5S1bG2S6aA2S1bS69Vh;A2A2A2A2A2A2A2").

Hypothesis HNQ : ltac2:(tb__ "0|0|
S0S3fVCST;VA';R1A3S4S6eVA';R2A2A1F_;Fa;").
Hypothesis HNQS : ltac2:(tb__ "0|0|
S0S40VCST;VXGL;VA';R1A4S4S6eVA';R2A2A1F_;Fa;").
Hypothesis HNOC : ltac2:(tb__ "0|0|
S0S3fVCST;VA2;R1A3S4S6fVch;R2A2A1F_;Fy;").

Definition EXPIN (r : valuation) : Prop := ltac2:(tb__ "0|2|
S2S1S90R1S34A2S3S30Q40M0A1M1S22Vr;R2A2S22Vrho1';R2A2A3F_;Fv;S2S1S3SbS30Q8A1A1S28Vr;R1A2S28Vrho1';R1A2A3Fl;S2S3G1S22Vr;Pc3A2S31G0S1dS4fVG;A1S68A2A2A3S3G1S22Vr;Pc8A2S31G0S50VG;A1A2A3A2A2A2").
Hypothesis LFRO : ltac2:(tb__ "0|4|
S25S8cR1A1S19S3cS19R1S35A3S78R4S79S33S24Vrho1';A1A2S20SeS0S0S48R4R2A2A3S9S9S9S23S0A2M0S0A2M1SbS9S9S0SfA2S23A2A1M2A2M3S0Lk;R2G1G2G1S0Lp0;R2G0S0G0S0Lp1;R2S23S0R1Llo;Ls;X9x1Lz;Lp1;X9x1Ll;Lp0;X9x1A2G3G2Lk;R2G1G2G1G2Lp0;R2G0S0G0G2Lp1;R2S23S0R5Lz0;Ls;X9x1Lz;Lp1;X9x1Lcs;Lp0;X9x1A4F_;Fk;F_;Fr;").

Section FINH.
Variables (r : valuation) (tpX : list word) (tr : list event) (ms : machine_state) (md : Model).
Let w : world := ltac2:(tb__ "0|0|
ScSbS62A1S73Vtr;S74Vms;Vmd;A2A4").
Hypothesis HEP : EXPIN r.
Hypothesis H : ltac2:(tb__ "0|0|
S54S33S4dVKc;VA';Vrho1';Vl1;Vl2;Vi;Vch;S36VA';Vch;A2A8VXF;Vr;VtpX;Vw;A6").
Let KJ : jpredA := ltac2:(tb__ "0|0|
S25SbS30Q40A1A1SbS62A1S63VKc;R2R1A2Lm0;Lt0;L_;L_;").
Let rho3 : valuation := ltac2:(tb__ "0|0|
S65Vr;VREST;S76Vmd;VtpX;Vms;A3A3").
Let v3 : bview := ltac2:(tb__ "0|0|
S6bS33S24Vrho3;A1A2").
Let vr : bview := ltac2:(tb__ "0|0|
S6bS33S24Vr;A1A2").

Lemma J2 : ltac2:(tb__ "0|5|
S2S5aS33VA2;Vr;VtpX;Vmd;A5S2VKc;Vtr;Vmd;A2S2S47VA2;Vr;A2S2S46VA2;Vr;A2S2S30Q40M0A1S4S36VA';Vch;S32G0R1A2A3A1S3S14S30Q8A1M1A1M2S24Vr;R2A2S24Vrho1';R2A2A3F_;Fa;S2S0S4S4cVA';Vi;Vch;R1A4A1S3G2Vvr;R2A1S6bS33S24Vrho1';A1R2A3M3A3F_;Fz;S0S4S6fVch;R1A2A1S4S3G2G3S16G1A1M4A3A1S4S3G2Vvr;R3A1G4A3A1F_;F_;Fz;A2A2A2A2A2A2").
Proof. destruct H as [_ (X1 & X2 & X3 & X4 & _ & _ & X7 & X8 & X9)]. exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X7 (conj X8 X9)))))). Qed.
Lemma E151 : ltac2:(tb__ "0|1|
S3S30Q40M0A1S22Vr;P97A2S31G0VT;A2A3"). Proof. rewrite (proj1 HEP) by (unfold GW; lia). exact (proj1 HPIN). Qed.
Lemma E152 : ltac2:(tb__ "0|1|
S3S30Q40M0A1S22Vr;P98A2S31G0S4eVG;A1A2A3"). Proof. rewrite (proj1 HEP) by (unfold GW; lia). exact (proj1 (proj2 HPIN)). Qed.
Lemma B12 : ltac2:(tb__ "0|1|
S2S1bZ0S32Q40S22Vr;PcA2A2M0A2S1cG0S1eZ2Z2fA2A2A2").
Proof. rewrite (proj1 HEP) by (unfold GW; lia). destruct HPIN as (_ & _ & _ & E & B). rewrite E, u64_lit by lia. exact B. Qed.
Lemma E155 : ltac2:(tb__ "0|1|
S3S30Q40M0A1S22Vr;P9bA2S31G0S4fVG;A1A2A3"). Proof. rewrite (proj1 HEP) by (unfold GW; lia). exact (proj1 (proj2 (proj2 HPIN))). Qed.
Lemma HG2 : geom_ok G. Proof. pose proof (proj1 J2) as (HG & _). exact HG. Qed.

Lemma Ha : ltac2:(tb__ "0|0|
S54S33VKJ;VXM;Vr;VtpX;Vw;A6").
Proof.
  destruct (SPA_axforms segs KJ (XEX_hb XF) r XF XM tpX w (x_AXE nW XF XOK) ltac:(split; [exact (proj1 H) | exact (proj1 (proj2 J2))])) as [X Y]. split; assumption.
Qed.
Lemma Hsm1 : ltac2:(tb__ "0|0|
S2eS33Vr;S56VXM;A1ScSbS62A1S73Vtr;S74S76Vmd;VtpX;Vms;A3S77Vmd;A1A2A4A4").
Proof. pose proof (proj1 (proj1 Ha)) as X. unfold virt in X. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in X. exact X. Qed.
Lemma OBJS : ltac2:(tb__ "0|0|
S3SbS21A1S29S56VXM;A1A1S12S21VKEPT;VREST;A3A3").
Proof. unfold KEPT, REST, KEPTh, RESTh, REST_of. symmetry. apply firstn_skipn. Qed.
Lemma Hb : ltac2:(tb__ "0|0|
S54S33VKJ;VXK;Vrho3;VtpX;Vw;A6").
Proof. exact (SPA_unobj segs KJ r XM KEPT REST tpX tr ms md OBJS Ha (fun k => k)). Qed.

Lemma RCIV' : ltac2:(tb__ "0|0|
S19S3cS19R1S35A3S3cS21S1aR2A1VREST;A3F_;Fk;").
Proof.
  intros k Hk. pose proof (proj1 (forallb_forall _ _) (x_RCIV nW XF XOK) k Hk) as X. apply existsb_exists in X as (o & Ho & E).
  apply sobj_eqb_sound in E. subst o. exact Ho.
Qed.
Lemma RUNK' : ltac2:(tb__ "0|0|
S21S3cS21R1VREST;A3S3S26S27R2A1S2aA3F_;Fo;").
Proof. intros o Ho. pose proof (proj1 (forallb_forall _ _) (x_RUNK nW XF XOK) o Ho) as Y. cbv beta in Y. destruct (ob_dflt o); first [reflexivity | discriminate Y]. Qed.
Lemma EvT : ltac2:(tb__ "0|0|
S3S0S32Q40S2cVr;S84A2A2VT;A3").
Proof. pose proof (geom_numsS _ HG2) as (_ & _ & _ & G4 & G5 & _). pose proof (topG_range G). unfold vT. cbn [eval]. rewrite E151. apply u64_lit. fold T in G4, G5. lia. Qed.
Lemma RCLS' : ltac2:(tb__ "0|2|
S21S0S3cS21R2VREST;A3S2S1bSeS0S0S2dVr;R3A2M0A3R2A2S1cR2S11S0S0G0A3A2A2S5S6S19S19S2S3cS19R1S35A3S2S1bSeS0S0S48Vr;R1A2M1A3R4A2S1cR4S11S0S0G1A3A2A2A2Lk;A2S2S1bS1dVT;Zad0A2R3A2S1cR3S1dVT;Zc60A2A2A2A2F_;F_;Fa;Fo;").
Proof.
  intros o a Ho Ha0. pose proof (proj1 (forallb_forall _ _) (x_RCLS nW XF XOK) o Ho) as X. cbv beta in X. apply orb_prop in X as [X|X].
  - apply existsb_exists in X as (o' & Ho' & E). apply sobj_eqb_sound in E. subst o'. apply in_map_iff in Ho' as (k & <- & Hk). left. exists k. split; [exact Hk|].
    rewrite (carve_range XK XK eq_refl A r k (proj1 (Forall_forall _ _) ROSh_small k Hk)) in Ha0. exact Ha0.
  - right. apply existsb_exists in X as (s & Hs & E). apply sobj_eqb_sound in E. rewrite <- (nocells_range r o), E in Ha0.
    pose proof (geom_numsS _ HG2) as (_ & _ & _ & G4 & G5 & _). pose proof (topG_range G) as TG. fold T in G4, G5. pose proof EvT as ET.
    unfold STSH in Hs. cbn [map In] in Hs. destruct Hs as [<-|[<-|[<-|[]]]]; unfold nocellsF, O_stT1, O_stQ, O_stT2, carved, cA in Ha0; cbn [ob_base ob_lo ob_hi ob_dflt] in Ha0;
      rewrite obj_range_mk in Ha0 by lia; cbn [fst snd] in Ha0.
    + rewrite ET in Ha0. lia.
    + cbn [eval] in Ha0. rewrite add_val, u64_lit in Ha0 by lia. change (rw r 151%positive) with (eval r vT) in Ha0. rewrite ET in Ha0. rewrite Z.mod_small in Ha0 by lia. lia.
    + rewrite ET in Ha0. lia.
Qed.

Lemma RO_off : ltac2:(tb__ "0|1|
S19S0S3cS19R2S35A3S2S1bSeS0S0S48Vr;R3A2M0A3R2A2S1cR2S11S0S0G0A3A2A2S2S4S4cVA';Vi;Vch;R3A4A1S2S1bZ0R3A2S1cR3S1eZ2Z2fA2A2A2A2F_;F_;Fa;Fk;").
Proof.
  intros k a Hk Ha0. pose proof (geom_numsS _ HG2) as (_ & _ & _ & G4 & G5 & G6 & G7 & _). pose proof (topG_range G) as TG. fold T in G4, G5.
  destruct (ROSh_zone G r k a HG2 E151 E152 B12 Hk Ha0) as [[Z1 Z2]|[Z1|Z1]].
  - split; [exact (HZ_L a Z1 Z2) | unfold IMG_HI in Z1; lia].
  - split; [exact (HZ_T a Z1) | fold T in Z1; lia].
  - split; [exact (HZ_C a Z1) | lia].
Qed.
Lemma NKr : ltac2:(tb__ "0|4|
S19S3cS19R1S35A3S2S3cS21S1aR2A1VREST;A3S2S4bR2A1S2S4aR2A1S78Vr;S79S33S24Vr;A1A2S20SeS0S0S48Vr;R2A2A3S9S9S9S23S0A2M0S0A2M1SbS9S9S0SfA2S23A2A1M2A2M3S0Lk;R2G1G2G1S0Lp0;R2G0S0G0S0Lp1;R2S23S0R1Llo;Ls;X9x1Lz;Lp1;X9x1Ll;Lp0;X9x1A2G3G2Lk;R2G1G2G1G2Lp0;R2G0S0G0G2Lp1;R2S23S0R5Lz0;Ls;X9x1Lz;Lp1;X9x1Lcs;Lp0;X9x1A4A2A2A2F_;Fk;").
Proof.
  intros k Hk. split; [exact (RCIV' k Hk)|]. pose proof (proj1 (Forall_forall _ _) ROSh_small k Hk) as SM. split; [exact SM|].
  split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) ROSh_coverb k Hk)|].
  pose proof (LFRO r HEP k Hk) as LF. pose proof (RO_off k) as RO. destruct J2 as (_ & _ & _ & _ & _ & VK & _).
  destruct k as [[[b lo] hi] cs]. cbn [spec_range fst snd] in LF, RO |- *. destruct SM as (S1 & S2 & S3 & S4).
  unfold cells_in_view in LF |- *. apply Forall_forall. intros [[off kk] e] Hc j Hj.
  pose proof (proj1 (Forall_forall _ _) LF _ Hc j Hj) as X. cbn beta iota in X. rewrite <- X.
  pose proof (proj1 (Forall_forall _ _) S4 _ Hc) as CI. cbn beta iota in CI.
  set (z := bv_unsigned (eval r b) + lo - lo + off + Z.of_nat j).
  destruct (RO z Hk ltac:(unfold z; lia)) as [ND ZB].
  pose proof (VK z ND) as E. unfold vr in E. rewrite !view_in in E by lia. exact E.
Qed.
Lemma INRh : ltac2:(tb__ "0|4|
S30Q40M0A1S64Vr;VREST;R1A3S5S6S19S19S2S3cS19R1S35A3S2S1bSeS0S0S48Vr;R1A2M1A3S32G0R3A2M2A2S1cG2S11S0S0G1A3A2A2A2Lk;A2S2S1bS1dVT;Zad0A2S32G0R2A2M3A2S1cG3S1dVT;Zc60A2A2A2A2F_;Fa;").
Proof. intros a (o & Ho & Hr). exact (RCLS' o _ Ho Hr). Qed.
Lemma VO3 : ltac2:(tb__ "0|0|
S0S4S2S1bS1dVT;Zad0A2R1A2S1cR1S1dVT;Zc60A2A2A2A1S3S14S30Q8A1A1Vv3;R2A1Vvr;R2A1A3F_;Fz;").
Proof.
  intros z Hz. unfold v3, vr. destruct (Z_le_dec 0 z) as [L0|L0]; [destruct (Z_lt_dec z (2 ^ 64)) as [L1|L1]|].
  2,3: rewrite !view_out by lia; reflexivity.
  rewrite !view_in by lia.
  destruct (in_ranges_dec r REST (Z_to_bv 64 z)) as [Hin|Hout].
  - destruct (INRh _ Hin) as [(k & Hk & Hr)|Hc]; rewrite u64_lit in * by lia; [|exfalso; exact (Hz Hc)].
    unfold rho3. exact (absorb_specs_view r _ tr (vms md tpX ms) (vmd md) KEPT REST ROSh (rd_of segs (rm r)) Hsm1 OBJS NKr z k Hk Hr).
  - unfold rho3, rho_absorb, rd_of. cbn [rm]. destruct (in_ranges_dec r REST (Z_to_bv 64 z)) as [Hin'|]; [exfalso; exact (Hout Hin') | reflexivity].
Qed.
Lemma RMO3 : ltac2:(tb__ "0|0|
S30Q40A1S4S64Vr;VREST;R1A3A1S3S14S30Q8A1A1S24Vrho3;R2A2S24Vr;R2A2A3F_;Fa;").
Proof. intros a Hout. unfold rho3, rho_absorb. cbn [rm]. destruct (in_ranges_dec r REST a) as [Hin|]; [exfalso; exact (Hout Hin) | reflexivity]. Qed.
Lemma PRS3 : ltac2:(tb__ "0|3|
S0S4S3S14S30Q8A1M0A1M1Vvr;R1A1S16G0A1M2A3A1S4S3G1Vv3;R2A1G2A3A1F_;Fz;").
Proof.
  intros z Hd. unfold v3, vr in *. destruct (Z_le_dec 0 z) as [L0|L0]; [destruct (Z_lt_dec z (2 ^ 64)) as [L1|L1]|].
  2,3: rewrite view_out in Hd by lia; exfalso; apply Hd; reflexivity.
  destruct (in_ranges_dec r REST (Z_to_bv 64 z)) as [Hin|Hout].
  - destruct Hin as (o & Ho & Hr). rewrite u64_lit in Hr by lia.
    destruct (SpineMallocS9.absorb_obj r _ tr (vms md tpX ms) (vmd md) KEPT REST o Hsm1 OBJS Ho) as (_ & _ & X3 & _). cbn zeta in X3.
    unfold obj_range in Hr. cbn [fst snd] in Hr.
    destruct (X3 (or_introl (RUNK' o Ho)) (z - bv_unsigned (eval r (ob_base o))) ltac:(lia)) as [x Hx].
    unfold rho3. rewrite view_in by lia.
    replace (Z_to_bv 64 z) with (Z_to_bv 64 (bv_unsigned (eval r (ob_base o)) + (z - bv_unsigned (eval r (ob_base o))))) by (f_equal; lia).
    rewrite Hx. discriminate.
  - rewrite !view_in in * by lia. unfold rd_of in *. rewrite (RMO3 _ Hout). exact Hd.
Qed.

Lemma HA3 : ltac2:(tb__ "0|0|
S5aS33VA2;Vrho3;VtpX;Vmd;A5").
Proof.
  destruct J2 as (HA2 & HK & Htp & Htop & _ & _ & _).
  set (rK := rho_sets r [(156%positive, Z_to_bv 64 (ag_spacebeg G + kSpaceSize))]).
  assert (ERM : rm rK = rm r) by (unfold rK; apply rm_rho_sets).
  assert (OTH : forall v, v <> 156%positive -> rw rK v = rw r v) by (intros v Hv; unfold rK; rewrite rho_sets_other; [reflexivity | cbn; intros [E|[]]; congruence]).
  assert (HK0 : K0 Kc A2 rK tpX tr md).
  { split; [|split; [exact HK|split; [|split]]].
    - pose proof (AInvA_Q A2 r tpX md HA2) as HQ. unfold AInvQ in *. rewrite ERM. exact HQ.
    - unfold tp_ok in *. rewrite OTH by discriminate. exact Htp.
    - unfold top_high in *. unfold V_DEPTH in *. rewrite !OTH by discriminate. exact Htop.
    - unfold rigidQ. rewrite !OTH by discriminate. change (aa_geom A2) with G. split; [exact E151|]. split; [exact E152|]. split; [exact E155|].
      unfold rK. apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]. }
  set (rK3 := mkVal (rw rK) (rl rK) (rm rho3)).
  assert (HK3 : K0 Kc A2 rK3 tpX tr md).
  { apply (kq_view segsA (K0 Kc) (K0_laws Kc HKc) A2 rK rK3 tpX tr md); [intros; reflexivity | intros; reflexivity | | | exact HK0].
    - intros z NQ. cbn [rm rK3]. rewrite ERM. apply VO3. intros Hz. apply NQ. right. right. unfold qstat_zone. change (aa_geom A2) with G. fold T. exact Hz.
    - intros z _ Hp. cbn [rm rK3]. rewrite ERM in Hp. exact (PRS3 z Hp). }
  destruct (AInvB_Q kQuarantineCacheMax A2 r tpX md HA2) as (HQ2 & QM & QB1 & QB2).
  assert (R5 : q_pure A2) by (destruct HQ2 as (_ & _ & _ & HRest & _); destruct HRest as (_ & _ & _ & _ & (R5 & _) & _); exact R5).
  pose proof (geomTI A2 r tpX md HA2) as TI. change (aa_geom A2) with G in TI. fold T in TI.
  assert (QM3 : q_mem (view segsA (rm rK3)) A2).
  { cbn [rm rK3]. apply (q_mem_frame A2 vr v3 R5); [| | | exact QM].
    - intros z Hz. apply VO3. intros Hs. apply (qfoot_offT A2 r tpX md HA2 z Hz). change (aa_geom A2) with G. fold T. lia.
    - intros z Hz. apply VO3. change (aa_geom A2) with G in Hz. fold T in Hz. lia.
    - intros z Hz. apply VO3. unfold QG in Hz. lia. }
  destruct (K0_back Kc A2 rK3 tpX tr md HK3 QM3 QB1 QB2) as (HA3' & _). exact HA3'.
Qed.

Lemma CLA : ltac2:(tb__ "0|0|
S0S7S3fVCST;VA;R1A3S3fVCST;VA';R1A3A2Fa;").
Proof. intros a. destruct HDO as (EG & _ & _ & _ & _ & EL & _ & _ & _ & EFB & _). unfold client_addrA, client_mut_addrA, aa_frames. rewrite EG, EL, EFB. tauto. Qed.
Lemma CLS : ltac2:(tb__ "0|0|
S0S7S40VCST;VXGL;VA;R1A4S40VCST;VXGL;VA';R1A4A2Fa;").
Proof. intros a. unfold client_shadowA. split; (intros [(x & Hx & E)|R]; [left; exists x; split; [apply CLA; exact Hx | exact E] | right; exact R]). Qed.
Lemma CLA2 : ltac2:(tb__ "0|0|
S0S3fVCST;VA2;R1A3S3fVCST;VA';R2A3F_;Fa;").
Proof.
  intros a Hc. unfold client_addrA, client_mut_addrA, aa_frames in *. change (aa_geom A2) with (aa_geom A') in Hc. change (aa_fs_busy A2) with (aa_fs_busy A') in Hc.
  change (aa_live A2) with (l1 ++ l2) in Hc. destruct Hc as [[S|[L|[FR|C]]]|FL]; [left; left; exact S | left; right; left | left; right; right; left; exact FR | left; right; right; right; exact C | right; exact FL].
  destruct L as (b & m & Hbm & Hx). exists b, m. split; [|exact Hx]. rewrite HLV. apply in_app_or in Hbm as [X|X]; apply in_or_app; [left; exact X | right; right; exact X].
Qed.
Lemma CLS2 : ltac2:(tb__ "0|0|
S0S40VCST;VXGL;VA2;R1A4S40VCST;VXGL;VA';R2A4F_;Fa;").
Proof. intros a [(x & Hx & E)|R]; [left; exists x; split; [exact (CLA2 x Hx) | exact E] | right; exact R]. Qed.

Lemma A2parts : ltac2:(tb__ "0|0|
S2S5fS6dS5eVG;A1Vvr;A2VA2;A2S61VA2;A1A2").
Proof. destruct J2 as (HA2 & _). destruct HA2 as (_ & _ & HF & (Hsep & _) & _). exact (conj HF Hsep). Qed.

Lemma client_off_REST : ltac2:(tb__ "0|2|
S30Q40M0A1S5S3fVCST;VA2;S32G0R1A2M1A3S40VCST;VXGL;VA2;G1A4A2S4S64Vr;VREST;R2A3A1F_;Fa;").
Proof.
  intros a Hcl Hin. destruct A2parts as (HF & Hsep). pose proof HG2 as HG.
  pose proof (geom_bands _ HG) as (WF & TB' & CB & DB & _). fold T in TB'. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB', CB, DB.
  assert (ZON : (0 <= bv_unsigned a < IMG_HI) \/ (T <= bv_unsigned a < T + 0x1000) \/ (ag_ctx G <= bv_unsigned a < ag_ctx G + 0x1000)).
  { destruct (INRh a Hin) as [(k & Hk & Hr)|Hs]; [|right; left; lia].
    destruct (ROSh_zone G r k _ HG E151 E152 B12 Hk Hr) as [[Z1 _]|[Z1|Z1]]; [left; exact Z1 | right; left; exact Z1 | right; right; exact Z1]. }
  destruct Hcl as [Hc|Hs].
  -
    destruct ZON as [ZI|ZT].
    + destruct (client_addr_cases CST A2 _ _ HF Hc) as [S|[L|[FR|[C|FL]]]]; change (aa_geom A2) with G in *.
      * pose proof (topG_range G). unfold IMG_HI in ZI. lia.
      * destruct L as (b & m & Hbm & Hx). destruct (Hsep b m Hbm) as (S1 & S2 & _). unfold IMG_HI in *. lia.
      * destruct FR as (c & p0 & Hc0 & Hp & _ & Hx). pose proof (fs_geom_nums G c p0 HG Hc0 Hp) as M. cbn zeta in M.
        rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. pose proof (geom_numsS _ HG) as (_ & F1 & _). unfold IMG_HI in *. lia.
      * destruct (INRh a Hin) as [(k & Hk & Hr)|Hs]; [|pose proof (geom_numsS _ HG) as (_ & _ & _ & G4 & G5 & _); fold T in G4, G5;
            destruct (HCST _ C) as [X _]; pose proof (geomTI A2 r tpX md (proj1 J2)) as TI; change (aa_geom A2) with G in TI; fold T in TI; unfold IMG_LO, IMG_HI in *; lia].
        unfold ROSh in Hk. apply in_app_or in Hk as [Hk|Hk].
        -- pose proof (NRTX_zone G r k _ HG E151 E152 B12 Hk Hr) as [R|R]; [|exact (HCSTF _ C R)].
           exact (client_not_rt CST HCST A2 _ _ HG HF Hsep Hc R).
        -- apply (HNQ _ (CLA2 _ Hc)). apply in_app_or in Hk as [Hk|Hk].
           ++ unfold N_hb in Hk. cbn [firstn In] in Hk. right. unfold qrtc_zone, SEC_INST in *.
              destruct Hk as [<-|[<-|[<-|[]]]]; cbn [spec_range fst snd eval] in Hr; rewrite u64_lit in Hr by lia.
              ** left. lia.
              ** left. lia.
              ** exfalso. apply (HNQ _ (CLA2 _ Hc)). left. right. right. right. left. unfold SEC_INST. lia.
           ++ destruct Hk as [<-|[]]. left. left. right. left. unfold qhdr_zone. left.
              cbn [spec_range fst snd qsz_spec] in Hr. pose proof EvT as ET. unfold cQ in Hr. cbn [eval] in Hr. rewrite add_val, u64_lit in Hr by lia.
              change (rw r 151%positive) with (eval r vT) in Hr. rewrite ET in Hr. pose proof (geom_numsS _ HG) as (_ & _ & _ & G4 & G5 & _). pose proof (topG_range G). fold T in G4, G5.
              rewrite Z.mod_small in Hr by lia. change (aa_geom A') with G. fold T. lia.
      * destruct FL as (c & p0 & Hc0 & Hp & _ & E). pose proof (fs_geom_nums G c p0 HG Hc0 Hp) as M. cbn zeta in M.
        rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *. pose proof (geom_numsS _ HG) as (_ & F1 & _). unfold IMG_HI in *. lia.
    + apply (client_not_rt CST HCST A2 _ _ HG HF Hsep Hc). unfold rt_zone. change (aa_geom A2) with G. fold T. right. destruct ZT as [ZT|ZT]; [left; exact ZT | right; left; exact ZT].
  -
    pose proof (client_shadow_bounds CST XGL HCST HXGL A2 _ _ HG HF Hsep Hs) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
    unfold IMG_HI in ZON. fold T in TB'. lia.
Qed.

Lemma client_off_TZ : ltac2:(tb__ "0|0|
S0S5S3fVCST;VA2;R1A3S40VCST;VXGL;VA2;R1A4A2S4S36VA';Vch;R2A3A1F_;Fa;").
Proof.
  intros a Hcl HT. destruct A2parts as (HF & Hsep). pose proof HG2 as HG.
  destruct CHB as (C1 & C2 & C3 & C4 & C5 & C6). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in C6.
  assert (SHZ : forall z, chunk_sh_zone ch z -> 2147446784 <= z < 17594333495296).
  { intros z Hz. unfold chunk_sh_zone in Hz. fold h msz in Hz. unfold IMG_HI in C3.
    pose proof (Z.div_pos h 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (h + msz) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). unfold Sh, SHADOW_OFF in Hz. lia. }
  destruct Hcl as [Hc|Hs].
  - destruct HT as [HQ|[HC|HS]]; [exact (HNQ _ (CLA2 _ Hc) HQ) | exact (HNOC _ Hc HC)|].
    destruct (client_addr_bounds CST HCST A2 a _ HG HF Hsep Hc) as [_ B]. pose proof (SHZ a HS). lia.
  - destruct HT as [HQ|[HC|HS]]; [exact (HNQS _ (CLS2 _ Hs) HQ)| |].
    + pose proof (client_shadow_bounds CST XGL HCST HXGL A2 a _ HG HF Hsep Hs) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B. unfold chunk_zone in HC. fold h msz in HC. lia.
    +
      destruct (proj1 (Z.mod_divide h 8 ltac:(lia)) C1) as [u Hu]. destruct (proj1 (Z.mod_divide (h + msz) 8 ltac:(lia)) ltac:(rewrite Z.add_mod, C1, C2 by lia; reflexivity)) as [u2 Hu2].
      unfold chunk_sh_zone in HS. fold h msz in HS. unfold Sh in HS. rewrite Hu2 in HS. rewrite Hu in HS. rewrite !Z.div_mul in HS by lia.
      assert (INCH : forall y, a = Sh y -> chunk_zone ch y).
      { intros y ->. unfold Sh in HS. pose proof (Z.div_mod y 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as MB. unfold chunk_zone. fold h msz. lia. }
      destruct Hs as [(y & Cy & Ey)|(y & Gy & Ey)].
      * exact (HNOC y Cy (INCH y Ey)).
      * destruct (HXGL y Gy) as [Y1 Y2]. pose proof (INCH y Ey) as X. unfold chunk_zone in X. fold h msz in X. unfold IMG_HI in *. lia.
Qed.

Lemma HKEPT : ltac2:(tb__ "0|0|
S45VCST;VXGL;VA;VA2;S24Vrho;A1S24Vrho3;A1A6").
Proof.
  destruct J2 as (HA2 & _ & _ & _ & KEY & _ & PR). destruct A2parts as (HF & Hsep). pose proof HG2 as HG.
  destruct HLK as (_ & _ & Lm & Ld). assert (Erm1 : rm rho1 = rm rho) by (unfold rho1, rhoF_of; apply rm_rho_sets).
  split.
  - intros a Ha Hcl.
    assert (C2 : client_addrA CST A2 a \/ client_shadowA CST XGL A2 a) by (destruct Hcl as [(_ & X & _)|(_ & X & _)]; [left; exact X | right; exact X]).
    assert (C0 : client_addrA CST A a \/ client_shadowA CST XGL A a) by (destruct Hcl as [(X & _ & _)|(X & _ & _)]; [left; exact X | right; exact X]).
    rewrite RMO3 by (apply client_off_REST; rewrite u64_lit by lia; exact C2).
    rewrite KEY by (rewrite u64_lit by lia; exact (client_off_TZ a C2)).
    rewrite (Lm (Z_to_bv 64 a)) by (rewrite u64_lit by lia; exact (HKEEP a C0)). rewrite Erm1. reflexivity.
  - intros x j Hx Hj Hdef.
    assert (Bx : 0 <= x < 2 ^ 47).
    { destruct Hx as [[_ CX]|GX]; [exact (proj1 (client_addr_bounds CST HCST A2 x _ HG HF Hsep CX))|]. destruct (HXGL x GX) as [X1 X2]. unfold IMG_HI in X2. lia. }
    destruct (word_byte_range (Sh x) j ltac:(unfold Sh, SHADOW_OFF; lia) Hj) as (W1 & W2 & W3).
    assert (BAND : SHADOW_BAND_LO <= bv_unsigned (word_byte (Sh x) j) < SHADOW_BAND_HI).
    { rewrite W2. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *.
      pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
    set (a := word_byte (Sh x) j) in *.
    assert (D1 : rm rho1' a <> None) by (apply Ld; [exact BAND | rewrite Erm1; exact Hdef]).
    assert (NIR : ~ in_ranges r REST a).
    { intros Hin. pose proof (geom_bands _ HG) as (WF & TB' & CB & DB & _). fold T in TB'. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
      destruct (INRh a Hin) as [(k & Hk & Hr)|Hs]; [|lia].
      destruct (ROSh_zone G r k _ HG E151 E152 B12 Hk Hr) as [[Z1 _]|[Z1|Z1]]; unfold IMG_HI in *; try (fold T in Z1); lia. }
    rewrite (RMO3 a NIR).
    assert (Ua : 0 <= bv_unsigned a < 2 ^ 64) by (pose proof (bv_unsigned_in_range _ a) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X).
    assert (HI : IMG_HI <= bv_unsigned a) by (unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, IMG_HI in *; lia).
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.RebuildR.view_rm_off (rm rho1') _ Ua (or_intror HI)) as VR1. change InvLaws.segsA with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA in VR1. rewrite Z_to_bv_bv_unsigned in VR1.
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.RebuildR.view_rm_off (rm r) _ Ua (or_intror HI)) as VR2. change InvLaws.segsA with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA in VR2. rewrite Z_to_bv_bv_unsigned in VR2.
    assert (V1 : view segs (rm rho1') (bv_unsigned a) <> None) by (rewrite VR1; exact D1).
    assert (NCZ : ~ chunk_zone ch (bv_unsigned a)).
    { destruct CHB as (_ & _ & C3 & C4 & C5 & C6). unfold chunk_zone. fold h msz. lia. }
    pose proof (PR _ NCZ V1) as V2. unfold vr in V2. rewrite VR2 in V2. exact V2.
Qed.

Theorem hb_finish : ltac2:(tb__ "0|1|
S59S33S75Vrho;Vtp;SaS9S55S58A2M0ScS55S58S82S41A1S42S5aS33A1VCST;VXGL;VA;VKc;A5A4S10G0A1A3Vw;A6").
Proof.
  destruct J2 as (HA2 & HK & Htp & _). pose proof HG2 as HG.
  assert (Hc : SPA segs KJ XR rho3 tpX w).
  { unfold XR. rewrite <- (x_EQR nW XF XOK). eapply SPA_restate; [exact (x_WXR nW XF XOK) | exact (x_DXR nW XF XOK) | exact (x_NXR nW XF XOK) | | constructor | exact Hb].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. change (aa_geom A2) with G. destruct (geom_old _ HG) as (_ & _ & _ & G4 & _). rewrite G4. reflexivity. }
  pose proof (smatchA_entails segs _ _ _ rho3 tpX _ (x_ENT nW XF XOK) (proj1 Hc)) as Hsm4.
  set (rho4 := rho_sub rho3 sX) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw r k).
  { intros k Hk. unfold rho4, sX. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ (x_SID nW XF XOK) Hk). reflexivity. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 sX).
  destruct HR as [[AGw AGl] _ _ _ _ _ _ _ _ _]. destruct HLK as (Lw & Ll & _).
  exists (L_free_tol AE_A), (JL_free (AInvA segs) CST XGL A Kc), rho4, tpX.
  split; [left; reflexivity|]. split; [|split; [exact Hsm4|]].
  { split.
    - intros k Hk. rewrite (Hlow k Hk), (proj1 HEP k) by (unfold NF, GW in *; lia). rewrite Lw. exact (AGw k Hk).
    - intros l. unfold rho4, rho3. cbn [rl rho_sub rho_absorb]. rewrite (proj1 (proj2 HEP) l), Ll. exact (AGl l). }
  cbn [w_tr w_cfg cfg_model fst snd]. unfold JL_free. exists A2, l1, l2.
  destruct HDO as (EG & EC & ECI & ESEC & EPC & EL & EQT & EQG & EII & EFB & EFH & EV & EKM & EKF).
  split; [pose proof HA3 as X; unfold AInvA in *; rewrite Erm4; exact X|].
  split; [rewrite Hp12, Hn13, <- EL; exact HLV|].
  split; [reflexivity|]. split; [unfold aa_frames; change (aa_fs_busy A2) with (aa_fs_busy A'); rewrite EFB; reflexivity|].
  split; [exact EV|]. split; [exact EKM|]. split; [exact EKF|]. split; [exact EG|].
  split; [rewrite Erm4; exact HKEPT|]. split; [exact HK|].
  intros c Hc0 NE Hfr. unfold class_fresh in *. change (aa_cls A2) with (aa_cls A'). rewrite EC. exact Hfr.
Qed.
End FINH.

Theorem G_exit : ltac2:(tb__ "0|3|
S25SbS30Q40M0A1M1A1S83S3G1S22R3Pc3A2S31G0S1dS4fVG;A1S68A2A2A3S3G1S22R4Pc8A2S31G0S50VG;A1A2A3S54S33S4dVKc;VA';Vrho1';Vl1;Vl2;Vi;Vch;S36VA';Vch;A2A8VXF;R5R4R3A6S59S33S75Vrho;Vtp;SaS9S55S58A2M2ScS55S58S82S41A1S42S5aS33A1VCST;VXGL;VA;VKc;A5A4S10G2A1A3R4A6F_;F_;F_;Fw;FtpX;Fr;").
Proof.
  intros r tpX [tr [ms md]] E195 E200 H.
  assert (HEP : EXPIN r).
  { destruct H as [_ (_ & _ & _ & _ & RW & RL & _)]. split; [exact RW|]. split; [exact RL|]. split; [exact E195 | exact E200]. }
  exact (hb_finish r tpX tr ms md HEP H).
Qed.
End ExitH.
End F0T_hbN_exit.

(* [comment removed for export] *)
Module CallocHitTail1E.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLeOrPc"; "Wcan"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "SVar"; "SLit"; "SPUle"; "rw"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "pair"; "prod"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "prim_room"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "V_RZ"; "C9"; "C9p"; "E3p"; "C10a"; "C10b"; "C10pa"; "C10pb"; "C9ma"; "C9mb"; "C9mpa"; "C9mpb"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Logic"; "not"; "eq"; "or"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "JLc_ok"; "Lc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineCallocE9"; "es9c_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineCallocEiW1"; "ECert10a_0"; "ECert10b_0"; "ECert10pa_0"; "ECert10pb_0"; "ECert9a_0"; "ECert9b_0"; "ECert9pa_0"; "ECert9pb_0"; "NX10a_0"; "NX10b_0"; "NX10pa_0"; "NX10pb_0"; "NX9fa_0"; "NX9fb_0"; "NX9fpa_0"; "NX9fpb_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS9iW1"; "D9ma_0"; "D9mb_0"; "D9mpa_0"; "D9mpb_0"; "ENT10a_0"; "ENT10b_0"; "ENT10pa_0"; "ENT10pb_0"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"; "FBCma_0"; "FBCmb_0"; "FBCmpa_0"; "FBCmpb_0"; "FBTma_0"; "FBTmb_0"; "FBTmpa_0"; "FBTmpb_0"; "FH_a_0"; "FH_b_0"; "FH_pa_0"; "FH_pb_0"; "HCC9ma_0"; "HCC9mb_0"; "HCC9mpa_0"; "HCC9mpb_0"; "HTma_0"; "HTmb_0"; "HTmpa_0"; "HTmpb_0"; "Hchkma_0"; "Hchkmb_0"; "Hchkmpa_0"; "Hchkmpb_0"; "Hema_0"; "Hemb_0"; "Hempa_0"; "Hempb_0"; "NX9ma_0"; "NX9mb_0"; "NX9mpa_0"; "NX9mpb_0"; "NXCma_0"; "NXCmb_0"; "NXCmpa_0"; "NXCmpb_0"; "Rma_0"; "Rmb_0"; "Rmpa_0"; "Rmpb_0"; "SID10a_0"; "SID10b_0"; "SID10pa_0"; "SID10pb_0"; "T9a_0"; "T9b_0"; "T9pa_0"; "T9pb_0"; "W9ma_0"; "W9mb_0"; "W9mpa_0"; "W9mpb_0"; "hcells_a"; "hcells_b"; "hcells_pa";
"hcells_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "sdma_0"; "sdmb_0"; "sdmpa_0"; "sdmpb_0"; "sf_a"; "sf_b"; "sf_pa"; "sf_pb"; "sma_0"; "smb_0"; "smpa_0"; "smpb_0"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ks.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.SpineCallocS5iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.SpineCallocS6iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.SpineCallocS7iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS8iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS9iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ks.CallocHitTail1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.SpineCallocE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineCallocE9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineCallocEiW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.CDepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kt.CDepotCallHW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineCallocS5t OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
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
Let law_die : forall A rho tp md, AInvA segsA A rho tp md -> cell_ok (view segsA (rm rho)) (mkACell 0x17fbdc 4 0) := AInvA_die.
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
Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x17fbdc 4 0) := AInvA_die.
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
    apply (espine_s7 1%nat st0 3 OV7a_0 OV7b_0 TAB7a_0 TAB7b_0 W7a_0 W7b_0 D7a_0 D7b_0 NX7a_0 NX7b_0 G7a_0 G7b_0 F7a_0 F7b_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS8iW1.s8a_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS8iW1.s8b_0
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
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "list"; "bool"; "nil"; "prod"; "nat"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "eval"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "qbatch"; "budget_bound"; "class_fresh"; "@Corelib.Init.Logic"; "eq"; "True"; "not"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "QP"; "JRD"; "JRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "clsB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQCF_call"; "ENVC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "JOK"; "TRP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drainA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "JD"; "JLD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQ3D_qcs"; "QC_full_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.SegQCF_states"; "PostD"; "PreD"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require le.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.SegQCF_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.SegQCF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQCF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQF_ri OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQ3D_qcs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.SegQCF_exit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
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
  - apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv.QP_push; [exact (QP_drain A0 A I4 NFR) | lia | exact NFR].
  - intros z Hz. apply I6. exact (SF_push_batch (drainA A 24) (mkQB a [] s) (tmp' ++ rest) _ z I1 I5 Hz).
Qed.
End QCFTop.
End SegQCF_top.

(* [comment removed for export] *)
Module SegQIF_m1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.SegQIF_m1"; "N"; "D_fa"; "D_fb"; "D_ga"; "D_gb"; "C1_fa"; "C1_fb"; "C1_ga"; "C1_gb"; "D_of"; "L1_fa"; "L1_fb"; "L1_ga"; "L1_gb"; "Lx_fa"; "Lx_fb"; "Lx_ga"; "Lx_gb"; "RF_fa"; "RF_fb"; "RF_ga"; "RF_gb"; "S0_fa"; "S0_fb"; "S0_ga"; "S0_gb"; "T1f_fa"; "T1f_fb"; "T1f_ga"; "T1f_gb"; "XC_fa"; "XC_fb"; "XC_ga"; "XC_gb"; "XX_fa"; "XX_fb"; "XX_ga"; "XX_gb"; "sF_fa"; "sF_fb"; "sF_ga"; "sF_gb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs"; "mcert"; "mkMD"; "mdata"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQS_lib RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_env SegQIF_mdefs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ln.SegQIF_m2"; "N"; "D_fa"; "D_fb"; "D_ga"; "D_gb"; "C1_fa"; "C1_fb"; "C1_ga"; "C1_gb"; "D_of"; "L1_fa"; "L1_fb"; "L1_ga"; "L1_gb"; "Lx_fa"; "Lx_fb"; "Lx_ga"; "Lx_gb"; "RF_fa"; "RF_fb"; "RF_ga"; "RF_gb"; "S0_fa"; "S0_fb"; "S0_ga"; "S0_gb"; "T1f_fa"; "T1f_fb"; "T1f_ga"; "T1f_gb"; "XC_fa"; "XC_fb"; "XC_ga"; "XC_gb"; "XX_fa"; "XX_fb"; "XX_ga"; "XX_gb"; "sF_fa"; "sF_fb"; "sF_ga"; "sF_gb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs"; "mcert"; "mkMD"; "mdata"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQS_lib RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQIF_env SegQIF_mdefs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
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

