(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_047.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g7.

(* [comment removed for export] *)
Module DrvTLXi_f4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "Some"; "nil"; "option"; "list"; "false"; "nat"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "axst"; "ax_S"; "mkLeafA"; "ax_X"; "sym_runA"; "ax_base"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "ss_next"; "ss_facts"; "ss_lenient"; "ss_objs"; "sstate"; "SPUle"; "SVar"; "sobj"; "sprop"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX"; "bd_J"; "keptX"; "CP"; "backedge_okb"; "bd_L"; "edge_okb"; "ndJX"; "ndLX"; "bd_E"; "exit1_b"; "exitc_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "PreF"; "PostF"; "S_T"; "CUTS_X"; "FUEL_X"; "bd_T"; "tv_T"; "vB"; "vCap"; "vPlen"; "locate"; "nd_T"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states"; "R_fp_P10"; "R_fp_Pc3"; "T_fp_P10"; "T_fp_Pc3"; "J_E"; "LJa_P10"; "LJa_Pc3"; "LJb_P10"; "LJb_Pc3"; "LX_P10"; "LX_Pc3"; "L_E"; "L_E1"; "L_Ec"; "s_fp"; "vP"; "CUTS_T"; "E_mP1"; "E_mPc"; "FUEL_T0"; "S_T1"; "S_T2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TR_INIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "drv_xrb"; "robjs_checkD"; "sp0_factsb"; "xrs_checkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "KU"; "bd_below"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceS GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB DrvGlueC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT Lib_fuzz_iface2 DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvTLXi_h.

Lemma XP10_facts : ltac2:(tb__ "0|12|
S1S0S7S8S1eA1M0A1S5bS23S46A1M1S2eS4bG1A1M2A3S5G0S3dA2A3S1S0S3S5aG1S2eG2S3dS4SeS2fS6SeA1M3A3A5S2A3S1S0S3S60S2dG2A2S2A3S1S0S3S3bS2dS17SfS46A1M4A1M5A2S2A3S1S1S0S3S3aG5S28S25Z1M6A1M7A1A2S2A3S0S3S5dG5S21A2S2A3A2S1S1S0S15S53G2PcA2S1dS4cA1M8A3S0S15S53G2PdA2S37A3A2S1S0S3S5eS18SfG1A1M9A1MaS16Z0MbA1McS5cG7S21A5S2A3S1S0S3S58GaA1S2A3S1S0S3S57GaS22S5SaU0A2MdS3dA4S2A3S1S0S3S59GaS22GdS1aG9A1S56S11G1A1A6S2A3S1S0S3S61S1fS20S1cS16Z1000A1G8A2A1GaA3S2A3S1S0SeS5fS2eG1G2S3dS2fA5S3fA3S1S1S0S3S3bS2dS17SfS3fA1MeA1MfA2S2A3S1S0S3S19GeA1S9A3S0S3S3aGfS27S21A1A2S2A3A2A2S1S0S7S8SdA1M10A1S12S3cS32S31S3fS2A5S5G10S4SdS10S42S2cA2S4SdS10S44S2cA2S6SdA1A3A3A2A3S1S0S3S62SeS24S41S54GbG6A2GcA2S4ScS15S15A2M11SbS15S15S35S36A4S6G11A1A3S21A3S4SeS42S4SeS44G3A3A3A3S2A3S0S3S2aS18G4A1A1S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Lemma XPc3_facts : ltac2:(tb__ "0|11|
S1S0S7S8S1eA1M0A1S5bS23S47A1M1S2eS4bG1A1M2A3S5G0S3eA2A3S1S0S3S5aG1S2eG2S3eS4SeS2fS6SeA1M3A3A5S2A3S1S0S3S60S2dG2A2S2A3S1S0S3S3bS2dS17SfS47A1M4A1M5A2S2A3S1S1S0S3S3aG5S28S25Z4A1M6A1A2S2A3S0S3S5dG5S21A2S2A3A2S1S1S0S15S53G2PcA2S1dS4cA1M7A3S0S15S53G2PdA2S37A3A2S1S0S3S5eS18SfG1A1M8A1M9S16Z0A1MaS5cG6S21A5S2A3S1S0S3S58G9A1S2A3S1S0S3S57G9S22S5SaU0A2MbS3eA4S2A3S1S0S3S59G9S22GbS1aG8A1S56S11G1A1A6S2A3S1S0S3S61S1fS20S1cS16Z1000A1G7A2A1G9A3S2A3S1S0SeS5fS2eG1G2S3eS2fA5S40A3S1S1S0S3S3bS2dS17SfS40A1McA1MdA2S2A3S1S0S3S19GcA1S9A3S0S3S3aGdS27S21A1A2S2A3A2A2S1S0S7S8SdA1MeA1S12S3cS32S31S40S2A5S5GeS4SdS10S43S2cA2S4SdS10S45S2cA2S6SdA1A3A3A2A3S1S0S3S62SeS24S41S54Z3MfZ1A2GaA2S4ScS15S15A2M10SbS15S15S35S36A4S6G10A1A3S21A3S4SeS43S4SeS45G3A3A3A3S2A3S0S3S2bGfS18G4A1A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Lemma T0_facts : ltac2:(tb__ "0|9|
S1S0S7S1bA1S63SfS30A1U0S16Nd0A1A3S5S1bSfS51A1M0A2A3S1S1S0S3S65S3cG0S38S1aG0A1S16Z0M1A1S16S55A1A3M2S54S55Z4A2M3Z1M4G1A6S2A3S0S1bS64G0G2G3G4G1A5SfS52A1M5A3A2S1S1S0S3S3bS2dS17G5A1M6A2S2A3S1S0S3S19G5A1S9A3S0S3S3aG6S39A2S2A3A2A2S1S0S7S8SdA1M7A1S12S3cS50S4dS14G5S11S30A1S13S30A1A3S2A5S5G7S4SdS10S4eS2cA2S4SdS10S49S2cA2S4SdS10S4aS2cA2S4SdS10S4fS2cA2S6SdA1A3A3A3A3A2A3S1S0S3S26S48S9G1A2S34S33S29G1A1M8S49A5S2A3S0S3S26S48S2G1A2S34S33G8S4aA5S2A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.
End DrvTLXi_f4.

(* [comment removed for export] *)
Module DrvTLXi_f6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "ss_next"; "ss_facts"; "ss_lenient"; "ss_objs"; "@Corelib.Init.Datatypes"; "nil"; "prod"; "Some"; "bool"; "option"; "true"; "list"; "cons"; "None"; "false"; "nat"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "mkLeafA"; "ax_X"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX"; "bd_J"; "backedge_okb"; "bd_E"; "exitc_b"; "ndEX"; "ndJE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states"; "J_E"; "LX_Ec0"; "R_fn_Ec0"; "PreFN"; "T_fn_Ec0"; "LJEa_Ec0"; "LJEb_Ec0"; "PostFN"; "s_fn"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "ex_pipe"; "fb_pipe"; "drv_xrb"; "robjs_checkD"; "sp0_factsb"; "xrs_checkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_below"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ANone"; "NDA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g8.DrvTLXi_f6"; "Ex_J00"; "Ex_J02"; "Ex_J10"; "Ex_J20"; "Ex_J30"; "Ex_J40"; "Rx_J00"; "Rx_J02"; "Rx_J10"; "Rx_J20"; "Rx_J30"; "Rx_J40"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "CUTS_X"; "FUEL_X"; "vB"; "vCap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceS GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB DrvGlueC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT Lib_fuzz_iface2 DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvTLXi_h.

Lemma XEc0_facts : ltac2:(tb__ "0|10|
S1S0SdSfS4A1M0A1S4cS22S24S29S22A1M1A3SbG0S23A2A3S1S0ScS4bS22S24G1S23S10S15S28S9S15A1M2A3A5SeA3S1S0ScS4eS37G1A2SeA3S1S0ScS45S37S5S17S22A1M3A1M4A2SeA3S1S1S0ScS36G4S1fS1dZ1M5A1M6A1A2SeA3S0ScS32G4S1bA2SeA3A2S1S0ScS33S6G3A1M7S3Z0M8A1M9G8G6S1bA5SeA3S1S0ScS2fG7A1SeA3S1S0ScS2eG7S10SaS2S2A2MaS14S2S2S49S4aA4S9GaA1A3MbS11S13A1McS23A4SeA3S1S0ScS30G7GbGcS8G3A1S2dS19S22A1A6SeA3S1S0S15S4dS24S22G1S23S28A5S25A3S1S1S0ScS45S37S5S17S25A1MdA1MeA2SeA3S1S0ScS7GdA1S12A3S0ScS36GeS20S1bA1A2SeA3A2A2S1S0SdSfS16A1MfA1S1aS46S48S47S25SeA5SbGfS10S16S18S26S44A2S10S16S18S27S44A2S9S16A1A3A3A2A3S1S0ScS4fS15S1cS21S50G8G5A2G9A2GbS1bA3S10S15S26S10S15S27G2A3A3A3SeA3S0ScS1eG8G7A2SeA3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Definition Ex_J10 : axst := Eval vm_compute in optA (fb_pipe bd_J [] (J_E 1 (SLit 0))) S_T.
Definition Rx_J10 : list sobj := Eval vm_compute in match ex_pipe (NDA [] [] [] ANone) Ex_J10 1 0 with Some R => R | None => [] end.
Lemma J10_facts : ltac2:(tb__ "0|4|
S1S0SdS15A1S2cS1bS9S31A1M0S21Z1M1S3Z0M2A1A2A3SbS15S3aA2A3S0SdSfS4A1M3A1S2bS35S9SaS2S2A2A1S9SaSaS2S2aA2S2A2A1G0S34A4S3aG1G2A4SbG3S40A2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Ex_J20 : axst := Eval vm_compute in optA (fb_pipe bd_J [] (J_E 2 (SLit 0))) S_T.
Definition Rx_J20 : list sobj := Eval vm_compute in match ex_pipe (NDA [] [] [] ANone) Ex_J20 2 0 with Some R => R | None => [] end.
Lemma J20_facts : ltac2:(tb__ "0|4|
S1S0SdS15A1S2cS1bS9S31A1M0S21Z2M1S3Z0M2A1A2A3SbS15S3bA2A3S0SdSfS4A1M3A1S2bS35S9SaS2S2A2A1S9SaSaS2S2aA2S2A2A1G0S34A4S3bG1G2A4SbG3S41A2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Ex_J30 : axst := Eval vm_compute in optA (fb_pipe bd_J [] (J_E 3 (SLit 0))) S_T.
Definition Rx_J30 : list sobj := Eval vm_compute in match ex_pipe (NDA [] [] [] ANone) Ex_J30 3 0 with Some R => R | None => [] end.
Lemma J30_facts : ltac2:(tb__ "0|4|
S1S0SdS15A1S2cS1bS9S31A1M0S21Z3M1S3Z0M2A1A2A3SbS15S3cA2A3S0SdSfS4A1M3A1S2bS35S9SaS2S2A2A1S9SaSaS2S2aA2S2A2A1G0S34A4S3cG1G2A4SbG3S42A2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Ex_J40 : axst := Eval vm_compute in optA (fb_pipe bd_J [] (J_E 4 (SLit 0))) S_T.
Definition Rx_J40 : list sobj := Eval vm_compute in match ex_pipe (NDA [] [] [] ANone) Ex_J40 4 0 with Some R => R | None => [] end.
Lemma J40_facts : ltac2:(tb__ "0|4|
S1S0SdS15A1S2cS1bS9S31A1M0S21Z4M1S3Z0M2A1A2A3SbS15S3dA2A3S0SdSfS4A1M3A1S2bS35S9SaS2S2A2A1S9SaSaS2S2aA2S2A2A1G0S34A4S3dG1G2A4SbG3S43A2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Ex_J02 : axst := Eval vm_compute in optA (fb_pipe bd_J [] (J_E 0 (SLit 2))) S_T.
Definition Rx_J02 : list sobj := Eval vm_compute in match ex_pipe (NDA [] [] [] ANone) Ex_J02 0 2 with Some R => R | None => [] end.
Lemma J02_facts : ltac2:(tb__ "0|4|
S1S0SdS15A1S2cS1bS9S31A1M0S21Z0M1S3Z2M2A1A2A3SbS15S39A2A3S0SdSfS4A1M3A1S2bS35S9SaS2S2A2A1S9SaSaS2S2aA2S2A2A1G0S34A4S39G1G2A4SbG3S3fA2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Ex_J00 : axst := Eval vm_compute in optA (fb_pipe bd_J [] (J_E 0 (SLit 0))) S_T.
Definition Rx_J00 : list sobj := Eval vm_compute in match ex_pipe (NDA [] [] [] ANone) Ex_J00 0 0 with Some R => R | None => [] end.
Lemma J00_facts : ltac2:(tb__ "0|3|
S1S0SdS15A1S2cS1bS9S31A1M0S21Z0M1S3G1A1A2A3SbS15S38A2A3S0SdSfS4A1M2A1S2bS35S9SaS2S2A2A1S9SaSaS2S2aA2S2A2A1G0S34A4S38G1G1A4SbG2S3eA2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End DrvTLXi_f6.

(* [comment removed for export] *)
Module DrvTLXi_f1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "True"; "@Corelib.Init.Datatypes"; "true"; "bool"; "Some"; "nat"; "cons"; "app"; "nil"; "length"; "option"; "false"; "list"; "prod"; "orb"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "ss_next"; "sstate"; "ss_objs"; "ss_facts"; "SLit"; "sv"; "sprop"; "ss_lenient"; "sprop_below"; "DUnknown"; "mkObj"; "swf"; "cell"; "SVar"; "obj_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "mkLeafA"; "ax_base"; "sym_runA"; "mkAX"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "ANone"; "NDA"; "nd_tv"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "Pre_fz"; "bd_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "seq"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "sp0_factsb"; "drv_objb"; "drv_xrb"; "kept_nzb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX"; "N_pf"; "kept"; "keptE"; "bd_E"; "bd_L"; "ms16_shapeb"; "backedge_okb"; "Cfz"; "CfzE"; "Cpf"; "Cpf0"; "Cpf0E"; "CpfE"; "P1c"; "P1cE"; "ndE0"; "ndE1"; "ndL0"; "ndL1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states"; "CUTS_L"; "FUEL_L"; "O_WloT"; "O_WfzT"; "O_payE"; "PreP"; "WDP"; "pf_hints"; "pf_u1"; "s_fz"; "s_pf"; "L_E"; "L_P"; "E_pfE10"; "E_pfEc0"; "E_pfEc1"; "E_pfEc2"; "E_pfEc3"; "E_pfP10"; "E_pfPc0"; "E_pfPc1"; "E_pfPc2"; "E_pfPc3"; "X_payE"; "vP"; "R_fzE10"; "R_fzEc0"; "R_fzEc1"; "R_fzEc2"; "R_fzEc3"; "R_fzP10"; "R_fzPc0"; "R_fzPc1"; "R_fzPc2"; "R_fzPc3"; "TT_fzE10"; "TT_fzEc0"; "TT_fzEc1"; "TT_fzEc2"; "TT_fzEc3"; "TT_fzP10"; "TT_fzPc0"; "TT_fzPc1"; "TT_fzPc2"; "TT_fzPc3"; "T_pfE10"; "T_pfEc0"; "T_pfEc1"; "T_pfEc2"; "T_pfEc3"; "T_pfP10"; "T_pfPc0"; "T_pfPc1"; "T_pfPc2"; "T_pfPc3"; "E_fzE10"; "E_fzEc0"; "E_fzEc1"; "E_fzEc2"; "E_fzEc3"; "E_fzP10"; "E_fzPc0"; "E_fzPc1"; "E_fzPc2"; "E_fzPc3"; "R_pfE10"; "R_pfEc0"; "R_pfEc1"; "R_pfEc2"; "R_pfEc3"; "R_pfP10"; "R_pfPc0"; "R_pfPc1"; "R_pfPc2"; "R_pfPc3"; "T_fzE10"; "T_fzEc0"; "T_fzEc1"; "T_fzEc2"; "T_fzEc3"; "T_fzP10"; "T_fzPc0"; "T_fzPc1"; "T_fzPc2"; "T_fzPc3"; "U_pfE10"; "U_pfEc0"; "U_pfEc1"; "U_pfEc2"; "U_pfEc3"; "U_pfP10"; "U_pfPc0"; "U_pfPc1"; "U_pfPc2"; "U_pfPc3"; "LB_Ec0"; "LB_Ec1"; "LB_Ec2"; "LB_Pc0"; "LB_Pc1"; "LB_Pc2"; "LX_E10"; "LX_Ec0"; "LX_Ec1"; "LX_Ec2"; "LX_Ec3"; "LX_P10"; "LX_Pc0"; "LX_Pc1"; "LX_Pc2"; "LX_Pc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "add"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "KV_T"; "KP_T"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2"; "P_fz"; "PD_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "xr_tracked"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "sp0"; "dropX"; "vPlen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "carve_okb"; "lc_obj"; "lcarve"; "uncarve_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.PFAddr"; "PW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "P_pf"; "Posts_pf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.FZAddr"; "fz_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "robj_tracked"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_below"; "bd_subst"; "bitem"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pd_okA"; "pdescA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g8.DrvTLXi_f1"; "LE10_P1"; "LEc0_P1"; "LEc1_P1"; "LEc2_P1"; "LEc3_P1"; "LP10_P1"; "LPc0_P1"; "LPc1_P1"; "LPc2_P1"; "LPc3_P1"; "LE10_S3"; "LEc0_S3"; "LEc1_S3"; "LEc2_S3"; "LEc3_S3"; "LP10_S2"; "LPc0_S2"; "LPc1_S2"; "LPc2_S2"; "LPc3_S2"; "LE10_Q1"; "LE10_S1"; "LE10_S2"; "LE10_U1"; "LEc0_Q1"; "LEc0_S1"; "LEc0_S2"; "LEc0_U1"; "LEc1_Q1"; "LEc1_S1"; "LEc1_S2"; "LEc1_U1"; "LEc2_Q1"; "LEc2_S1"; "LEc2_S2"; "LEc2_U1"; "LEc3_Q1"; "LEc3_S1"; "LEc3_S2"; "LEc3_U1"; "LP10_Q1"; "LP10_S1"; "LP10_U1"; "LPc0_Q1"; "LPc0_S1"; "LPc0_U1"; "LPc1_Q1"; "LPc1_S1"; "LPc1_U1"; "LPc2_Q1"; "LPc2_S1"; "LPc2_U1"; "LPc3_Q1"; "LPc3_S1"; "LPc3_U1"; "LE10_Q2"; "LE10_U3"; "LE10_iw"; "LEc0_Q2"; "LEc0_U3"; "LEc0_iw"; "LEc1_Q2"; "LEc1_U3"; "LEc1_iw"; "LEc2_Q2"; "LEc2_U3"; "LEc2_iw"; "LEc3_Q2"; "LEc3_U3"; "LEc3_iw"; "LP10_Q2"; "LP10_iw"; "LPc0_Q2"; "LPc0_iw"; "LPc1_Q2"; "LPc1_iw"; "LPc2_Q2"; "LPc2_iw"; "LPc3_Q2"; "LPc3_iw"; "LE10_Q4"; "LE10_U4"; "LEc0_Q4"; "LEc0_U4"; "LEc1_Q4"; "LEc1_U4"; "LEc2_Q4"; "LEc2_U4"; "LEc3_Q4"; "LEc3_U4"; "LP10_Q4"; "LP10_U3"; "LPc0_Q4"; "LPc0_U3"; "LPc1_Q4"; "LPc1_U3"; "LPc2_Q4"; "LPc2_U3"; "LPc3_Q4"; "LPc3_U3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "EMPTY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "drop_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC"; "add_obj"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceS GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB DrvGlueC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT Lib_fuzz_iface2 DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvTLXi_h.

Definition LP10_iw : nat := Eval vm_compute in locate (ss_objs (ax_S E_fzP10)) spT (SLit (- (DEEP - 80))).
Definition LP10_S1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_fzP10) LP10_iw (SLit (- fz_frame))) (ax_S E_fzP10).
Definition LP10_S2 : sstate := Eval vm_compute in set_obj_at LP10_S1 LP10_iw O_WfzT.
Definition LP10_U1 : sstate := Eval vm_compute in set_obj_at (ax_S TT_fzP10) 1 O_WloT.
Definition LP10_U3 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LP10_U1 (select (ss_objs LP10_U1) ([1; 0] ++ seq 2 (length (ss_objs LP10_U1) - 2))%nat)) 0) LP10_U1.
Definition LP10_P1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_pfP10) 0 (SLit (- PW))) (ax_S E_pfP10).
Definition LP10_Q1 : sstate := Eval vm_compute in set_objs (ax_S T_pfP10) (select (ss_objs (ax_S T_pfP10)) (pf_u1 (length (ss_objs (ax_S T_pfP10))))).
Definition LP10_Q2 : sstate := Eval vm_compute in set_objs LP10_Q1 (firstn (length (ss_objs LP10_Q1) - 4) (ss_objs LP10_Q1)).
Definition LP10_Q4 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LP10_Q2 (select (ss_objs LP10_Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs LP10_Q2) - 9))%nat)) 0) LP10_Q2.
Lemma LP10_facts : ltac2:(tb__ "0|37|
S1S1S0S4S31S2aS12S21S5eScZ0M0A2M1A1M2A1M3A2S3A3S1S0S4S19G2A1ScA3S0S4S2bG3S50S43G0A1M4A1A2S3A3A2A2S1S0SbSdS23A1M5A1M6S27S3aS53S52G1S3A5S5G5S7S23S25S8eS35A2S9S23A1M7A3A2A3S1S0SbS13A1M8ScdS21S8eA1M9S133S16Sc3Se1A1A1A3S5S13S115A2A3S1S0SbS11A1MaS30S11S14S115A1S133A3S5S11S54A2A3S1S0S13Sd1S115S133S55A3SfbA3S1S0S4ScbS115SfbA2S3A3S1S0S4S3bS15G9A1MbA1S3A3S1S1S0Sc5S12SfbA1S12G9A1McA3S0SdS18A1S15SfbA1GbA3A2S1S0S4SeaS24S46S8eSfbA2MdA1MeGeA2S3A3S1S0SbSdS11A1MfA1M10SceGdS32S5bGdA1M11A3S5GfS70A2A3S1S0S4Sd0GdS32G11S70S7S22Sc9S9S22A1A3A5S3A3S1S0S4Sd3S2aG11A2S3A3S1S0S4Se2G11S2aA2S3A3S1S0S4S31S2aGcA2S3A3S1S1S0S4S2bGcS2dS8SeS17S17A2M12S40S9G12A1A3S9SeSeS17Sc6A2S17A2A1G4S2cA4A2S3A3S0S4Se4GcS43Z1A1M13A2S3A3A2S1S0S4Se7S15S21GdA1M14A1M15S16G0A1M16G0G4S8Se6Se5G11S33A2G13A3A5S3A3S1S0S4S2fSe9Se8S32S2aG11S12G14A1A4ScaA3S3A3S1S0S4S3bG15A1S3A3S1S0S4S3eG15S40A2S3A3S1S0S4S2fS11S11SfS3cG15R1A2Se3S40S10S6A1M17R1A3A2Lo;S70A3S3A3S1S0S4S2fG12G12SfS3dR1A1Sd4S40G17R1A3A2Lr;GeA3S3A3S1S1S0S17Sd5G11PcA2S1fS6aA1A3S0S17Sd5G11PdA2Sd8A3A2S1S0S22Sd2S32GdG11S70Sc9A5S7aA3S1S0GaS30S11S14S21S7aA1M18A1U1M19A3S5S11S1cSe0Sd6S16N250A1A2S16Sc3S58A1A1G16S9S1eA1S1bA5A2A3S1S0S13Sd1G18G19S54A3S116A3S1S0S4ScbG18S116A2S3A3S1S0S4S3bS15G18A1A1S3A3S1S0S4Sc2SaS11S14S116A1M1aA2M1bS8S6S7S6G19S7S6U0M1cS9S6A1A3M1dA3S37U2M1eS36G1bG1eA2A2A3M1fA2S3A3S1S0G8SccS34S116Sc1G1aG1fA2A2G1cA2S5S13S147A2A3S1S0S22S28S147S24S7aA1S26S7aA1A3Sa2A3S1S1S0S4S31S2aS12S21Sa2A1M20A1M21A2S3A3S1S0S4S19G20A1ScA3S0S4S2bG21S51G13A1M22A2S3A3A2A2S1S0G6S27S3aS53S52Sa2S3A5S5G5S7S23S25S64S35A2G7A3A2A3S1S0G8ScdS21S64A1M23G1cS16Sc3SddA1A1A3S5S13Sf1A2A3S1S0S4S1dS4cSf1A1M24A1S3A3S1S0S4Sd9S15Sf1A1S14Sf1A1S24S64A1Sc7Sc8S2eG22A1S3fA7S3A3S1S0Sc5S12Sf1A1S12G23A1A3S1S0S17S26S64A1S16SebA1A3S1S0S4S2fS18S1aS12G24A1A1S8S18S59S49S64Sf1A2G0A2M25S15G24A1A3A3S3A3S1S0S4S2fS18S44G25A3S3A3S1S0G10SceS48G0S64Sf1A3M26S57G0A1M27S5cG26G0A2M28A3S5GfS98A2A3S1S0S4ScfG26G27G28S98S38S23S22S29SdfG0A1A4A5S3A3S1S0S4S31S2aS12S21G26A1M29A1M2aA2S3A3S1S0S4S2bG2aG22A2S3A3S1S0S4S2fS18S1aG2aA1S15G29A1A3S3A3S1S0S22Sd2G27G26G28S98SdeG0A1A5S84A3S1S0S4Sc2SaS11S14S21S84A1M2bA1M2cA2M2dS5aG2dA1M2eA2S3A3S1S0GfSc1G2cG2eA2S14S114A1M2fA3S1S0S13S34G2bG2fA2S114A3S1S0GfG2fS8S11S39S11S36SaS11G2fA2U4A2G2fA3M30S38SdbS11SdaS3fA4A3A3S1S0S13S34S114G30A2S132A3S1S0S4SdcSc7S3fA2S3A3S1S0S4S2bS12S114A1G22A2S3A3S1S0S4Sc2SaS11S14S132A1M31A2M32S8S6S7S6U8G1dA3S8S6S37G19U7A2S37U9M33S36G32G33A2A2A3A3M34A2S3A3S1S0G8SccS34S132Sc1G31G34A2A2G1cA2S5S13S146A2A3S1S0S22S28S146S24S84A1S26S84A1A3SacA3S1S1S0S4S31S2aS12S21SacA1M35A1M36A2S3A3S1S0S4S19G35A1ScA3S0S4S2bG36G22A2S3A3A2A2S1S0G6S27S3aS53S52SacS3A5S5G5S7S23S25SbcS35A2G7A3A2A3S2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Definition LPc0_iw : nat := Eval vm_compute in locate (ss_objs (ax_S E_fzPc0)) spT (SLit (- (DEEP - 80))).
Definition LPc0_S1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_fzPc0) LPc0_iw (SLit (- fz_frame))) (ax_S E_fzPc0).
Definition LPc0_S2 : sstate := Eval vm_compute in set_obj_at LPc0_S1 LPc0_iw O_WfzT.
Definition LPc0_U1 : sstate := Eval vm_compute in set_obj_at (ax_S TT_fzPc0) 1 O_WloT.
Definition LPc0_U3 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LPc0_U1 (select (ss_objs LPc0_U1) ([1; 0] ++ seq 2 (length (ss_objs LPc0_U1) - 2))%nat)) 0) LPc0_U1.
Definition LPc0_P1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_pfPc0) 0 (SLit (- PW))) (ax_S E_pfPc0).
Definition LPc0_Q1 : sstate := Eval vm_compute in set_objs (ax_S T_pfPc0) (select (ss_objs (ax_S T_pfPc0)) (pf_u1 (length (ss_objs (ax_S T_pfPc0))))).
Definition LPc0_Q2 : sstate := Eval vm_compute in set_objs LPc0_Q1 (firstn (length (ss_objs LPc0_Q1) - 4) (ss_objs LPc0_Q1)).
Definition LPc0_Q4 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LPc0_Q2 (select (ss_objs LPc0_Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs LPc0_Q2) - 9))%nat)) 0) LPc0_Q2.
Lemma LPc0_facts : ltac2:(tb__ "0|38|
S1S1S0S4S31S2aS12S21S5eS3Z0M0A2M1A1M2A1M3A2S3A3S1S0S4S19G2A1ScA3S0S4S2bG3S50S43G0A1M4A1A2S3A3A2A2S1S0SbSdS23A1M5A1M6S27S3aS53S52G1S3A5S5G5S7S23S25S8fS35A2S9S23A1M7A3A2A3S1S0SbS13A1M8ScdS21S8fA1M9S135S16Sc3Se1A1A1A3S5S13S118A2A3S1S0SbS11A1MaS30S11S14S118A1S135A3S5S11S54A2A3S1S0S13Sd1S118S135S55A3SfcA3S1S0S4ScbS118SfcA2S3A3S1S0S4S3bS15G9A1MbA1S3A3S1S1S0Sc5S12SfcA1S12G9A1McA3S0SdS18A1S15SfcA1GbA3A2S1S0S4SeaS24S46S8fSfcA2MdA1MeGeA2S3A3S1S0SbSdS11A1MfA1M10SceGdS32S5bGdA1M11A3S5GfS71A2A3S1S0S4Sd0GdS32G11S71S7S22Sc9S9S22A1A3A5S3A3S1S0S4Sd3S2aG11A2S3A3S1S0S4Se2G11S2aA2S3A3S1S0S4S31S2aGcA2S3A3S1S1S0S4S2bGcS2dS8SeS17S17A2M12S40S9G12A1A3S9SeSeS17Sc6A2S17A2A1G4S2cA4A2S3A3S0S4Se4GcS43Z1M13A1M14A2S3A3A2S1S0S4Se7S15S21GdA1M15A1M16S16G0A1M17G0G4S8Se6Se5G11S33A2G14A3A5S3A3S1S0S4S2fSe9Se8S32S2aG11S12G15A1A4ScaA3S3A3S1S0S4S3bG16A1S3A3S1S0S4S3eG16S40A2S3A3S1S0S4S2fS11S11SfS3cG16R1A2Se3S40S10S6A1M18R1A3A2Lo;S71A3S3A3S1S0S4S2fG12G12SfS3dR1A1Sd4S40G18R1A3A2Lr;GeA3S3A3S1S1S0S17Sd5G11PcA2S1fS6aA1A3S0S17Sd5G11PdA2Sd8A3A2S1S0S22Sd2S32GdG11S71Sc9A5S7bA3S1S0GaS30S11S14S21S7bA1M19A1U1M1aA3S5S11S1cSe0Sd6S16N250A1A2S16Sc3S58A1A1G17S9S1eA1S1bA5A2A3S1S0S13Sd1G19G1aS54A3S119A3S1S0S4ScbG19S119A2S3A3S1S0S4S3bS15G19A1A1S3A3S1S0S4Sc2SaS11S14S119A1M1bA2M1cS8S6S7S6G1aS7S6U0M1dS9S6A1A3M1eA3S37U2M1fS36G1cG1fA2A2A3M20A2S3A3S1S0G8SccS34S119Sc1G1bG20A2A2G1dA2S5S13S149A2A3S1S0S22S28S149S24S7bA1S26S7bA1A3Sa3A3S1S1S0S4S31S2aS12S21Sa3A1M21A1M22A2S3A3S1S0S4S19G21A1ScA3S0S4S2bG22S51G14A1M23A2S3A3A2A2S1S0G6S27S3aS53S52Sa3S3A5S5G5S7S23S25S65S35A2G7A3A2A3S1S0G8ScdS21S65A1M24G1dS16Sc3SddA1A1A3S5S13Sf2A2A3S1S0S4S1dS4cSf2A1M25A1S3A3S1S0S4Sd9S15Sf2A1S14Sf2A1S24S65A1Sc7Sc8S2eG23A1S3fA7S3A3S1S0Sc5S12Sf2A1S12G24A1A3S1S0S17S26S65A1S16SebA1A3S1S0S4S2fS18S1aS12G25A1A1S8S18S59S49S65Sf2A2G0A2M26S15G25A1A3A3S3A3S1S0S4S2fS18S44G26A3S3A3S1S0G10SceS48G0S65Sf2A3M27S57G0A1M28S5cG27G0A2M29A3S5GfS99A2A3S1S0S4ScfG27G28G29S99S38S23S22S29SdfG0A1A4A5S3A3S1S0S4S31S2aS12S21G27A1M2aA1M2bA2S3A3S1S0S4S2bG2bG23A2S3A3S1S0S4S2fS18S1aG2bA1S15G2aA1A3S3A3S1S0S22Sd2G28G27G29S99SdeG0A1A5S85A3S1S0S4Sc2SaS11S14S21S85A1M2cA1M2dA2M2eS5aG2eA1M2fA2S3A3S1S0GfSc1G2dG2fA2S14S117A1M30A3S1S0S13S34G2cG30A2S117A3S1S0GfG30S8S11S39S11S36SaS11G30A2U4A2G30A3M31S38SdbS11SdaS3fA4A3A3S1S0S13S34S117G31A2S134A3S1S0S4SdcSc7S3fA2S3A3S1S0S4S2bS12S117A1G23A2S3A3S1S0S4Sc2SaS11S14S134A1M32A2M33S8S6S7S6U8G1eA3S8S6S37G1aU7A2S37U9M34S36G33G34A2A2A3A3M35A2S3A3S1S0G8SccS34S134Sc1G32G35A2A2G1dA2S5S13S148A2A3S1S0S22S28S148S24S85A1S26S85A1A3SadA3S1S1S0S4S31S2aS12S21SadA1M36A1M37A2S3A3S1S0S4S19G36A1ScA3S0S4S2bG37G23A2S3A3A2A2S1S0G6S27S3aS53S52SadS3A5S5G5S7S23S25Sb4S35A2S7S23S25SbdS35A2G7A3A3A2A3S0S4S45S5eS3Sc4G0G13A2A2S40G14Sb4A4S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Definition LPc1_iw : nat := Eval vm_compute in locate (ss_objs (ax_S E_fzPc1)) spT (SLit (- (DEEP - 80))).
Definition LPc1_S1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_fzPc1) LPc1_iw (SLit (- fz_frame))) (ax_S E_fzPc1).
Definition LPc1_S2 : sstate := Eval vm_compute in set_obj_at LPc1_S1 LPc1_iw O_WfzT.
Definition LPc1_U1 : sstate := Eval vm_compute in set_obj_at (ax_S TT_fzPc1) 1 O_WloT.
Definition LPc1_U3 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LPc1_U1 (select (ss_objs LPc1_U1) ([1; 0] ++ seq 2 (length (ss_objs LPc1_U1) - 2))%nat)) 0) LPc1_U1.
Definition LPc1_P1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_pfPc1) 0 (SLit (- PW))) (ax_S E_pfPc1).
Definition LPc1_Q1 : sstate := Eval vm_compute in set_objs (ax_S T_pfPc1) (select (ss_objs (ax_S T_pfPc1)) (pf_u1 (length (ss_objs (ax_S T_pfPc1))))).
Definition LPc1_Q2 : sstate := Eval vm_compute in set_objs LPc1_Q1 (firstn (length (ss_objs LPc1_Q1) - 4) (ss_objs LPc1_Q1)).
Definition LPc1_Q4 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LPc1_Q2 (select (ss_objs LPc1_Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs LPc1_Q2) - 9))%nat)) 0) LPc1_Q2.
Lemma LPc1_facts : ltac2:(tb__ "0|38|
S1S1S0S4S31S2aS12S21S5eS3Z1M0A2M1A1M2A1M3A2S3A3S1S0S4S19G2A1ScA3S0S4S2bG3S50S43G0A1M4A1A2S3A3A2A2S1S0SbSdS23A1M5A1M6S27S3aS53S52G1S3A5S5G5S7S23S25S90S35A2S9S23A1M7A3A2A3S1S0SbS13A1M8ScdS21S90A1M9S137S16Sc3Se1A1A1A3S5S13S11bA2A3S1S0SbS11A1MaS30S11S14S11bA1S137A3S5S11S54A2A3S1S0S13Sd1S11bS137S55A3SfdA3S1S0S4ScbS11bSfdA2S3A3S1S0S4S3bS15G9A1MbA1S3A3S1S1S0Sc5S12SfdA1S12G9A1McA3S0SdS18A1S15SfdA1GbA3A2S1S0S4SeaS24S46S90SfdA2MdA1MeGeA2S3A3S1S0SbSdS11A1MfA1M10SceGdS32S5bGdA1M11A3S5GfS72A2A3S1S0S4Sd0GdS32G11S72S7S22Sc9S9S22A1A3A5S3A3S1S0S4Sd3S2aG11A2S3A3S1S0S4Se2G11S2aA2S3A3S1S0S4S31S2aGcA2S3A3S1S1S0S4S2bGcS2dS8SeS17S17A2M12S40S9G12A1A3S9SeSeS17Sc6A2S17A2A1G4S2cA4A2S3A3S0S4Se4GcS43Z2A1M13A2S3A3A2S1S0S4Se7S15S21GdA1M14A1M15S16Z0M16A1M17G16G4S8Se6Se5G11S33A2G13A3A5S3A3S1S0S4S2fSe9Se8S32S2aG11S12G14A1A4ScaA3S3A3S1S0S4S3bG15A1S3A3S1S0S4S3eG15S40A2S3A3S1S0S4S2fS11S11SfS3cG15R1A2Se3S40S10S6A1M18R1A3A2Lo;S72A3S3A3S1S0S4S2fG12G12SfS3dR1A1Sd4S40G18R1A3A2Lr;GeA3S3A3S1S1S0S17Sd5G11PcA2S1fS6aA1A3S0S17Sd5G11PdA2Sd8A3A2S1S0S22Sd2S32GdG11S72Sc9A5S7cA3S1S0GaS30S11S14S21S7cA1M19A1U1M1aA3S5S11S1cSe0Sd6S16N250A1A2S16Sc3S58A1A1G17S9S1eA1S1bA5A2A3S1S0S13Sd1G19G1aS54A3S11cA3S1S0S4ScbG19S11cA2S3A3S1S0S4S3bS15G19A1A1S3A3S1S0S4Sc2SaS11S14S11cA1M1bA2M1cS8S6S7S6G1aS7S6U0M1dS9S6A1A3M1eA3S37U2M1fS36G1cG1fA2A2A3M20A2S3A3S1S0G8SccS34S11cSc1G1bG20A2A2G1dA2S5S13S14bA2A3S1S0S22S28S14bS24S7cA1S26S7cA1A3Sa4A3S1S1S0S4S31S2aS12S21Sa4A1M21A1M22A2S3A3S1S0S4S19G21A1ScA3S0S4S2bG22S51G13A1M23A2S3A3A2A2S1S0G6S27S3aS53S52Sa4S3A5S5G5S7S23S25S66S35A2G7A3A2A3S1S0G8ScdS21S66A1M24G1dS16Sc3SddA1A1A3S5S13Sf3A2A3S1S0S4S1dS4cSf3A1M25A1S3A3S1S0S4Sd9S15Sf3A1S14Sf3A1S24S66A1Sc7Sc8S2eG23A1S3fA7S3A3S1S0Sc5S12Sf3A1S12G24A1A3S1S0S17S26S66A1S16SebA1A3S1S0S4S2fS18S1aS12G25A1A1S8S18S59S49S66Sf3A2G0A2M26S15G25A1A3A3S3A3S1S0S4S2fS18S44G26A3S3A3S1S0G10SceS48G0S66Sf3A3M27S57G0A1M28S5cG27G0A2M29A3S5GfS9aA2A3S1S0S4ScfG27G28G29S9aS38S23S22S29SdfG0A1A4A5S3A3S1S0S4S31S2aS12S21G27A1M2aA1M2bA2S3A3S1S0S4S2bG2bG23A2S3A3S1S0S4S2fS18S1aG2bA1S15G2aA1A3S3A3S1S0S22Sd2G28G27G29S9aSdeG0A1A5S86A3S1S0S4Sc2SaS11S14S21S86A1M2cA1M2dA2M2eS5aG2eA1M2fA2S3A3S1S0GfSc1G2dG2fA2S14S11aA1M30A3S1S0S13S34G2cG30A2S11aA3S1S0GfG30S8S11S39S11S36SaS11G30A2U4A2G30A3M31S38SdbS11SdaS3fA4A3A3S1S0S13S34S11aG31A2S136A3S1S0S4SdcSc7S3fA2S3A3S1S0S4S2bS12S11aA1G23A2S3A3S1S0S4Sc2SaS11S14S136A1M32A2M33S8S6S7S6U8G1eA3S8S6S37G1aU7A2S37U9M34S36G33G34A2A2A3A3M35A2S3A3S1S0G8SccS34S136Sc1G32G35A2A2G1dA2S5S13S14aA2A3S1S0S22S28S14aS24S86A1S26S86A1A3SaeA3S1S1S0S4S31S2aS12S21SaeA1M36A1M37A2S3A3S1S0S4S19G36A1ScA3S0S4S2bG37G23A2S3A3A2A2S1S0G6S27S3aS53S52SaeS3A5S5G5S7S23S25Sb5S35A2S7S23S25SbeS35A2G7A3A3A2A3S0S4S45S5eS3Sc4G0G0A2A2S40G13Sb5A4S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Definition LPc2_iw : nat := Eval vm_compute in locate (ss_objs (ax_S E_fzPc2)) spT (SLit (- (DEEP - 80))).
Definition LPc2_S1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_fzPc2) LPc2_iw (SLit (- fz_frame))) (ax_S E_fzPc2).
Definition LPc2_S2 : sstate := Eval vm_compute in set_obj_at LPc2_S1 LPc2_iw O_WfzT.
Definition LPc2_U1 : sstate := Eval vm_compute in set_obj_at (ax_S TT_fzPc2) 1 O_WloT.
Definition LPc2_U3 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LPc2_U1 (select (ss_objs LPc2_U1) ([1; 0] ++ seq 2 (length (ss_objs LPc2_U1) - 2))%nat)) 0) LPc2_U1.
Definition LPc2_P1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_pfPc2) 0 (SLit (- PW))) (ax_S E_pfPc2).
Definition LPc2_Q1 : sstate := Eval vm_compute in set_objs (ax_S T_pfPc2) (select (ss_objs (ax_S T_pfPc2)) (pf_u1 (length (ss_objs (ax_S T_pfPc2))))).
Definition LPc2_Q2 : sstate := Eval vm_compute in set_objs LPc2_Q1 (firstn (length (ss_objs LPc2_Q1) - 4) (ss_objs LPc2_Q1)).
Definition LPc2_Q4 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LPc2_Q2 (select (ss_objs LPc2_Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs LPc2_Q2) - 9))%nat)) 0) LPc2_Q2.
Lemma LPc2_facts : ltac2:(tb__ "0|38|
S1S1S0S4S31S2aS12S21S5eS3Z2M0A2M1A1M2A1M3A2S3A3S1S0S4S19G2A1ScA3S0S4S2bG3S50S43G0A1M4A1A2S3A3A2A2S1S0SbSdS23A1M5A1M6S27S3aS53S52G1S3A5S5G5S7S23S25S91S35A2S9S23A1M7A3A2A3S1S0SbS13A1M8ScdS21S91A1M9S139S16Sc3Se1A1A1A3S5S13S11eA2A3S1S0SbS11A1MaS30S11S14S11eA1S139A3S5S11S54A2A3S1S0S13Sd1S11eS139S55A3SfeA3S1S0S4ScbS11eSfeA2S3A3S1S0S4S3bS15G9A1MbA1S3A3S1S1S0Sc5S12SfeA1S12G9A1McA3S0SdS18A1S15SfeA1GbA3A2S1S0S4SeaS24S46S91SfeA2MdA1MeGeA2S3A3S1S0SbSdS11A1MfA1M10SceGdS32S5bGdA1M11A3S5GfS73A2A3S1S0S4Sd0GdS32G11S73S7S22Sc9S9S22A1A3A5S3A3S1S0S4Sd3S2aG11A2S3A3S1S0S4Se2G11S2aA2S3A3S1S0S4S31S2aGcA2S3A3S1S1S0S4S2bGcS2dS8SeS17S17A2M12S40S9G12A1A3S9SeSeS17Sc6A2S17A2A1G4S2cA4A2S3A3S0S4Se4GcS43Z3A1M13A2S3A3A2S1S0S4Se7S15S21GdA1M14A1M15S16Z0M16A1M17G16G4S8Se6Se5G11S33A2G13A3A5S3A3S1S0S4S2fSe9Se8S32S2aG11S12G14A1A4ScaA3S3A3S1S0S4S3bG15A1S3A3S1S0S4S3eG15S40A2S3A3S1S0S4S2fS11S11SfS3cG15R1A2Se3S40S10S6A1M18R1A3A2Lo;S73A3S3A3S1S0S4S2fG12G12SfS3dR1A1Sd4S40G18R1A3A2Lr;GeA3S3A3S1S1S0S17Sd5G11PcA2S1fS6aA1A3S0S17Sd5G11PdA2Sd8A3A2S1S0S22Sd2S32GdG11S73Sc9A5S7dA3S1S0GaS30S11S14S21S7dA1M19A1U1M1aA3S5S11S1cSe0Sd6S16N250A1A2S16Sc3S58A1A1G17S9S1eA1S1bA5A2A3S1S0S13Sd1G19G1aS54A3S11fA3S1S0S4ScbG19S11fA2S3A3S1S0S4S3bS15G19A1A1S3A3S1S0S4Sc2SaS11S14S11fA1M1bA2M1cS8S6S7S6G1aS7S6U0M1dS9S6A1A3M1eA3S37U2M1fS36G1cG1fA2A2A3M20A2S3A3S1S0G8SccS34S11fSc1G1bG20A2A2G1dA2S5S13S14dA2A3S1S0S22S28S14dS24S7dA1S26S7dA1A3Sa5A3S1S1S0S4S31S2aS12S21Sa5A1M21A1M22A2S3A3S1S0S4S19G21A1ScA3S0S4S2bG22S51G13A1M23A2S3A3A2A2S1S0G6S27S3aS53S52Sa5S3A5S5G5S7S23S25S67S35A2G7A3A2A3S1S0G8ScdS21S67A1M24G1dS16Sc3SddA1A1A3S5S13Sf4A2A3S1S0S4S1dS4cSf4A1M25A1S3A3S1S0S4Sd9S15Sf4A1S14Sf4A1S24S67A1Sc7Sc8S2eG23A1S3fA7S3A3S1S0Sc5S12Sf4A1S12G24A1A3S1S0S17S26S67A1S16SebA1A3S1S0S4S2fS18S1aS12G25A1A1S8S18S59S49S67Sf4A2G0A2M26S15G25A1A3A3S3A3S1S0S4S2fS18S44G26A3S3A3S1S0G10SceS48G0S67Sf4A3M27S57G0A1M28S5cG27G0A2M29A3S5GfS9bA2A3S1S0S4ScfG27G28G29S9bS38S23S22S29SdfG0A1A4A5S3A3S1S0S4S31S2aS12S21G27A1M2aA1M2bA2S3A3S1S0S4S2bG2bG23A2S3A3S1S0S4S2fS18S1aG2bA1S15G2aA1A3S3A3S1S0S22Sd2G28G27G29S9bSdeG0A1A5S87A3S1S0S4Sc2SaS11S14S21S87A1M2cA1M2dA2M2eS5aG2eA1M2fA2S3A3S1S0GfSc1G2dG2fA2S14S11dA1M30A3S1S0S13S34G2cG30A2S11dA3S1S0GfG30S8S11S39S11S36SaS11G30A2U4A2G30A3M31S38SdbS11SdaS3fA4A3A3S1S0S13S34S11dG31A2S138A3S1S0S4SdcSc7S3fA2S3A3S1S0S4S2bS12S11dA1G23A2S3A3S1S0S4Sc2SaS11S14S138A1M32A2M33S8S6S7S6U8G1eA3S8S6S37G1aU7A2S37U9M34S36G33G34A2A2A3A3M35A2S3A3S1S0G8SccS34S138Sc1G32G35A2A2G1dA2S5S13S14cA2A3S1S0S22S28S14cS24S87A1S26S87A1A3SafA3S1S1S0S4S31S2aS12S21SafA1M36A1M37A2S3A3S1S0S4S19G36A1ScA3S0S4S2bG37G23A2S3A3A2A2S1S0G6S27S3aS53S52SafS3A5S5G5S7S23S25Sb6S35A2S7S23S25SbfS35A2G7A3A3A2A3S0S4S45S5eS3Sc4G0Z1A2A2S40G13Sb6A4S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Definition LPc3_iw : nat := Eval vm_compute in locate (ss_objs (ax_S E_fzPc3)) spT (SLit (- (DEEP - 80))).
Definition LPc3_S1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_fzPc3) LPc3_iw (SLit (- fz_frame))) (ax_S E_fzPc3).
Definition LPc3_S2 : sstate := Eval vm_compute in set_obj_at LPc3_S1 LPc3_iw O_WfzT.
Definition LPc3_U1 : sstate := Eval vm_compute in set_obj_at (ax_S TT_fzPc3) 1 O_WloT.
Definition LPc3_U3 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LPc3_U1 (select (ss_objs LPc3_U1) ([1; 0] ++ seq 2 (length (ss_objs LPc3_U1) - 2))%nat)) 0) LPc3_U1.
Definition LPc3_P1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_pfPc3) 0 (SLit (- PW))) (ax_S E_pfPc3).
Definition LPc3_Q1 : sstate := Eval vm_compute in set_objs (ax_S T_pfPc3) (select (ss_objs (ax_S T_pfPc3)) (pf_u1 (length (ss_objs (ax_S T_pfPc3))))).
Definition LPc3_Q2 : sstate := Eval vm_compute in set_objs LPc3_Q1 (firstn (length (ss_objs LPc3_Q1) - 4) (ss_objs LPc3_Q1)).
Definition LPc3_Q4 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LPc3_Q2 (select (ss_objs LPc3_Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs LPc3_Q2) - 9))%nat)) 0) LPc3_Q2.
Lemma LPc3_facts : ltac2:(tb__ "0|38|
S1S1S0S4S31S2aS12S21S5eS3Z3M0A2M1A1M2A1M3A2S3A3S1S0S4S19G2A1ScA3S0S4S2bG3S50S43G0A1M4A1A2S3A3A2A2S1S0SbSdS23A1M5A1M6S27S3aS53S52G1S3A5S5G5S7S23S25S92S35A2S9S23A1M7A3A2A3S1S0SbS13A1M8ScdS21S92A1M9S13bS16Sc3Se1A1A1A3S5S13S121A2A3S1S0SbS11A1MaS30S11S14S121A1S13bA3S5S11S54A2A3S1S0S13Sd1S121S13bS55A3SffA3S1S0S4ScbS121SffA2S3A3S1S0S4S3bS15G9A1MbA1S3A3S1S1S0Sc5S12SffA1S12G9A1McA3S0SdS18A1S15SffA1GbA3A2S1S0S4SeaS24S46S92SffA2MdA1MeGeA2S3A3S1S0SbSdS11A1MfA1M10SceGdS32S5bGdA1M11A3S5GfS74A2A3S1S0S4Sd0GdS32G11S74S7S22Sc9S9S22A1A3A5S3A3S1S0S4Sd3S2aG11A2S3A3S1S0S4Se2G11S2aA2S3A3S1S0S4S31S2aGcA2S3A3S1S1S0S4S2bGcS2dS8SeS17S17A2M12S40S9G12A1A3S9SeSeS17Sc6A2S17A2A1G4S2cA4A2S3A3S0S4Se4GcS43Z4A1M13A2S3A3A2S1S0S4Se7S15S21GdA1M14A1M15S16Z0M16A1M17G16G4S8Se6Se5G11S33A2G13A3A5S3A3S1S0S4S2fSe9Se8S32S2aG11S12G14A1A4ScaA3S3A3S1S0S4S3bG15A1S3A3S1S0S4S3eG15S40A2S3A3S1S0S4S2fS11S11SfS3cG15R1A2Se3S40S10S6A1M18R1A3A2Lo;S74A3S3A3S1S0S4S2fG12G12SfS3dR1A1Sd4S40G18R1A3A2Lr;GeA3S3A3S1S1S0S17Sd5G11PcA2S1fS6aA1A3S0S17Sd5G11PdA2Sd8A3A2S1S0S22Sd2S32GdG11S74Sc9A5S7eA3S1S0GaS30S11S14S21S7eA1M19A1U1M1aA3S5S11S1cSe0Sd6S16N250A1A2S16Sc3S58A1A1G17S9S1eA1S1bA5A2A3S1S0S13Sd1G19G1aS54A3S122A3S1S0S4ScbG19S122A2S3A3S1S0S4S3bS15G19A1A1S3A3S1S0S4Sc2SaS11S14S122A1M1bA2M1cS8S6S7S6G1aS7S6U0M1dS9S6A1A3M1eA3S37U2M1fS36G1cG1fA2A2A3M20A2S3A3S1S0G8SccS34S122Sc1G1bG20A2A2G1dA2S5S13S14fA2A3S1S0S22S28S14fS24S7eA1S26S7eA1A3Sa6A3S1S1S0S4S31S2aS12S21Sa6A1M21A1M22A2S3A3S1S0S4S19G21A1ScA3S0S4S2bG22S51G13A1M23A2S3A3A2A2S1S0G6S27S3aS53S52Sa6S3A5S5G5S7S23S25S68S35A2G7A3A2A3S1S0G8ScdS21S68A1M24G1dS16Sc3SddA1A1A3S5S13Sf5A2A3S1S0S4S1dS4cSf5A1M25A1S3A3S1S0S4Sd9S15Sf5A1S14Sf5A1S24S68A1Sc7Sc8S2eG23A1S3fA7S3A3S1S0Sc5S12Sf5A1S12G24A1A3S1S0S17S26S68A1S16SebA1A3S1S0S4S2fS18S1aS12G25A1A1S8S18S59S49S68Sf5A2G0A2M26S15G25A1A3A3S3A3S1S0S4S2fS18S44G26A3S3A3S1S0G10SceS48G0S68Sf5A3M27S57G0A1M28S5cG27G0A2M29A3S5GfS9cA2A3S1S0S4ScfG27G28G29S9cS38S23S22S29SdfG0A1A4A5S3A3S1S0S4S31S2aS12S21G27A1M2aA1M2bA2S3A3S1S0S4S2bG2bG23A2S3A3S1S0S4S2fS18S1aG2bA1S15G2aA1A3S3A3S1S0S22Sd2G28G27G29S9cSdeG0A1A5S88A3S1S0S4Sc2SaS11S14S21S88A1M2cA1M2dA2M2eS5aG2eA1M2fA2S3A3S1S0GfSc1G2dG2fA2S14S120A1M30A3S1S0S13S34G2cG30A2S120A3S1S0GfG30S8S11S39S11S36SaS11G30A2U4A2G30A3M31S38SdbS11SdaS3fA4A3A3S1S0S13S34S120G31A2S13aA3S1S0S4SdcSc7S3fA2S3A3S1S0S4S2bS12S120A1G23A2S3A3S1S0S4Sc2SaS11S14S13aA1M32A2M33S8S6S7S6U8G1eA3S8S6S37G1aU7A2S37U9M34S36G33G34A2A2A3A3M35A2S3A3S1S0G8SccS34S13aSc1G32G35A2A2G1dA2S5S13S14eA2A3S1S0S22S28S14eS24S88A1S26S88A1A3Sb0A3S1S1S0S4S31S2aS12S21Sb0A1M36A1M37A2S3A3S1S0S4S19G36A1ScA3S0S4S2bG37G23A2S3A3A2A2S1S0G6S27S3aS53S52Sb0S3A5S5G5S7S23S25Sc0S35A2G7A3A2A3S2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Definition LE10_iw : nat := Eval vm_compute in locate (ss_objs (ax_S E_fzE10)) spT (SLit (- (DEEP - 80))).
Definition LE10_S1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_fzE10) LE10_iw (SLit (- fz_frame))) (ax_S E_fzE10).
Definition LE10_S2 : sstate := Eval vm_compute in set_obj_at LE10_S1 LE10_iw O_WfzT.
Definition LE10_S3 : sstate := Eval vm_compute in add_obj LE10_S2 O_payE.
Definition LE10_U1 : sstate := Eval vm_compute in set_obj_at (ax_S TT_fzE10) 1 O_WloT.
Definition LE10_U3 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LE10_U1 (select (ss_objs LE10_U1) ([1; 0] ++ seq 2 (length (ss_objs LE10_U1) - 2))%nat)) 0) LE10_U1.
Definition LE10_U4 : sstate := Eval vm_compute in drop_obj_at LE10_U3 1.
Definition LE10_P1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_pfE10) 0 (SLit (- PW))) (ax_S E_pfE10).
Definition LE10_Q1 : sstate := Eval vm_compute in set_objs (ax_S T_pfE10) (select (ss_objs (ax_S T_pfE10)) (pf_u1 (length (ss_objs (ax_S T_pfE10))))).
Definition LE10_Q2 : sstate := Eval vm_compute in set_objs LE10_Q1 (firstn (length (ss_objs LE10_Q1) - 4) (ss_objs LE10_Q1)).
Definition LE10_Q4 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LE10_Q2 (select (ss_objs LE10_Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs LE10_Q2) - 9))%nat)) 0) LE10_Q2.
Lemma LE10_facts : ltac2:(tb__ "0|38|
S1S1S0S4S31S2aS12S21S5dScZ0M0A2M1A1M2A1M3A2S3A3S1S0S4S19G2A1ScA3S0S4S2bG3S4eS42G0A1M4A1A2S3A3A2A2S1S0SbSdS23A1M5A1M6S27S3aS53S52G1S3A5S5G5S7S23S25S89S35A2S9S23A1M7A3A2A3S1S0SbS13A1M8ScdS21S89A1M9S125S16Sc3Se1A1A1A3S5S13S101A2A3S1S0SbS11A1MaS30S11S14S101A1S125A3S5S11S54A2A3S1S0S13Sd1S101S125S55A3S102A3S1S0S4ScbS101S102A2S3A3S1S0S4S3bS15G9A1MbA1S3A3S1S0S13S152S102S56A2Sf6A3S1S0S4S1dSf6A1S3A3S1S0S4S20S12S102A1S56A2S3A3S1S1S0Sc5S12Sf6A1S12G9A1McA3S0SdS18A1S15Sf6A1GbA3A2S1S0S4SeaS24S47S89Sf6A2MdA1MeGeA2S3A3S1S0SbSdS11A1MfA1M10SceGdS32S5bGdA1M11A3S5GfS6bA2A3S1S0S4Sd0GdS32G11S6bS7S22Sc9S9S22A1A3A5S3A3S1S0S4Sd3S2aG11A2S3A3S1S0S4Se2G11S2aA2S3A3S1S0S4S31S2aGcA2S3A3S1S1S0S4S2bGcS2dS8SeS17S17A2M12S41S9G12A1A3S9SeSeS17Sc6A2S17A2A1G4S2cA4A2S3A3S0S4Se4GcS42Z1A1M13A2S3A3A2S1S0S4Se7S15S21GdA1M14A1M15S16G0A1M16G0G4S8Se6Se5G11S33A2G13A3A5S3A3S1S0S4S2fSe9Se8S32S2aG11S12G14A1A4ScaA3S3A3S1S0S4S3bG15A1S3A3S1S0S4S3eG15S41A2S3A3S1S0S4S2fS11S11SfS3cG15R1A2Se3S41S10S6A1M17R1A3A2Lo;S6bA3S3A3S1S0S4S2fG12G12SfS3dR1A1Sd4S41G17R1A3A2Lr;GeA3S3A3S1S0S17Sd5G11PdA2G16A3S1S0S22Sd2S32GdG11S6bSc9A5S75A3S1S0GaS30S11S14S21S75A1M18A1U1M19A3S5S11S1cSe0Sd6S16N250A1A2S16Sc3S58A1A1G16S9S1eA1M1aS1bA5A2A3S1S0S13Sd1G18G19S54A3S103A3S1S0S4ScbG18S103A2S3A3S1S0S4S3bS15G18A1A1S3A3S1S0S4Sc2SaS11S14S103A1M1bA2M1cS8S6S7S6G19S7S6U0M1dS9S6A1A3M1eA3S37U2M1fS36G1cG1fA2A2A3M20A2S3A3S1S0G8SccS34S103Sc1G1bG20A2A2G1dA2S5S13S124A2A3S1S0GaS30S11S14S124A1G19A3S5S11S1cS16S150A1G16G16G1aS1bA5A2A3S1S0S13S151S124G19A2S13dA3S1S0S22Sd7S69S28S13dS24S75A1S26S75A1A3A2S9dA3S1S1S0S4S31S2aS12S21S9dA1M21A1M22A2S3A3S1S0S4S19G21A1ScA3S0S4S2bG22S4fG13A1M23A2S3A3A2A2S1S0G6S27S3aS53S52S9dS3A5S5G5S7S23S25S5fS35A2G7A3A2A3S1S0G8ScdS21S5fA1M24G1dS16Sc3SddA1A1A3S5S13SecA2A3S1S0S4S1dS4dSecA1M25A1S3A3S1S0S4Sd9S15SecA1S14SecA1S24S5fA1Sc7Sc8S2eG23A1S3fA7S3A3S1S0Sc5S12SecA1S12G24A1A3S1S0S17S26S5fA1S16SebA1A3S1S0S4S2fS18S1aS12G25A1A1S8S18S59S4aS5fSecA2G0A2M26S15G25A1A3A3S3A3S1S0S4S2fS18S44G26A3S3A3S1S0G10SceS4bG0S5fSecA3M27S57G0A1M28S5cG27G0A2M29A3S5GfS93A2A3S1S0S4ScfG27G28G29S93S38S23S22S29SdfG0A1A4A5S3A3S1S0S4S31S2aS12S21G27A1M2aA1M2bA2S3A3S1S0S4S2bG2bG23A2S3A3S1S0S4S2fS18S1aG2bA1S15G2aA1A3S3A3S1S0S22Sd2G28G27G29S93SdeG0A1A5S7fA3S1S0S4Sc2SaS11S14S21S7fA1M2cA1M2dA2M2eS5aG2eA1M2fA2S3A3S1S0GfSc1G2dG2fA2S14S100A1M30A3S1S0S13S34G2cG30A2S100A3S1S0GfG30S8S11S39S11S36SaS11G30A2U4A2G30A3M31S38SdbS11SdaS3fA4A3A3S1S0S13S34S100G31A2S123A3S1S0S4SdcSc7S3fA2S3A3S1S0S4S2bS12S100A1G23A2S3A3S1S0S4Sc2SaS11S14S123A1M32A2M33S8S6S7S6U8G1eA3S8S6S37G19U7A2S37U9M34S36G33G34A2A2A3A3M35A2S3A3S1S0G8SccS34S123Sc1G32G35A2A2G1dA2S5S13S13cA2A3S1S0S22S28S13cS24S7fA1S26S7fA1A3Sa7A3S1S1S0S4S31S2aS12S21Sa7A1M36A1M37A2S3A3S1S0S4S19G36A1ScA3S0S4S2bG37G23A2S3A3A2A2S1S0G6S27S3aS53S52Sa7S3A5S5G5S7S23S25Sb7S35A2G7A3A2A3S2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Definition LEc0_iw : nat := Eval vm_compute in locate (ss_objs (ax_S E_fzEc0)) spT (SLit (- (DEEP - 80))).
Definition LEc0_S1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_fzEc0) LEc0_iw (SLit (- fz_frame))) (ax_S E_fzEc0).
Definition LEc0_S2 : sstate := Eval vm_compute in set_obj_at LEc0_S1 LEc0_iw O_WfzT.
Definition LEc0_S3 : sstate := Eval vm_compute in add_obj LEc0_S2 O_payE.
Definition LEc0_U1 : sstate := Eval vm_compute in set_obj_at (ax_S TT_fzEc0) 1 O_WloT.
Definition LEc0_U3 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LEc0_U1 (select (ss_objs LEc0_U1) ([1; 0] ++ seq 2 (length (ss_objs LEc0_U1) - 2))%nat)) 0) LEc0_U1.
Definition LEc0_U4 : sstate := Eval vm_compute in drop_obj_at LEc0_U3 1.
Definition LEc0_P1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_pfEc0) 0 (SLit (- PW))) (ax_S E_pfEc0).
Definition LEc0_Q1 : sstate := Eval vm_compute in set_objs (ax_S T_pfEc0) (select (ss_objs (ax_S T_pfEc0)) (pf_u1 (length (ss_objs (ax_S T_pfEc0))))).
Definition LEc0_Q2 : sstate := Eval vm_compute in set_objs LEc0_Q1 (firstn (length (ss_objs LEc0_Q1) - 4) (ss_objs LEc0_Q1)).
Definition LEc0_Q4 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LEc0_Q2 (select (ss_objs LEc0_Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs LEc0_Q2) - 9))%nat)) 0) LEc0_Q2.
Lemma LEc0_facts : ltac2:(tb__ "0|39|
S1S1S0S4S31S2aS12S21S5dS3Z0M0A2M1A1M2A1M3A2S3A3S1S0S4S19G2A1ScA3S0S4S2bG3S4eS42G0A1M4A1A2S3A3A2A2S1S0SbSdS23A1M5A1M6S27S3aS53S52G1S3A5S5G5S7S23S25S8aS35A2S9S23A1M7A3A2A3S1S0SbS13A1M8ScdS21S8aA1M9S128S16Sc3Se1A1A1A3S5S13S105A2A3S1S0SbS11A1MaS30S11S14S105A1S128A3S5S11S54A2A3S1S0S13Sd1S105S128S55A3S106A3S1S0S4ScbS105S106A2S3A3S1S0S4S3bS15G9A1MbA1S3A3S1S0S13S152S106S56A2Sf7A3S1S0S4S1dSf7A1S3A3S1S0S4S20S12S106A1S56A2S3A3S1S1S0Sc5S12Sf7A1S12G9A1McA3S0SdS18A1S15Sf7A1GbA3A2S1S0S4SeaS24S47S8aSf7A2MdA1MeGeA2S3A3S1S0SbSdS11A1MfA1M10SceGdS32S5bGdA1M11A3S5GfS6cA2A3S1S0S4Sd0GdS32G11S6cS7S22Sc9S9S22A1A3A5S3A3S1S0S4Sd3S2aG11A2S3A3S1S0S4Se2G11S2aA2S3A3S1S0S4S31S2aGcA2S3A3S1S1S0S4S2bGcS2dS8SeS17S17A2M12S41S9G12A1A3S9SeSeS17Sc6A2S17A2A1G4S2cA4A2S3A3S0S4Se4GcS42Z1M13A1M14A2S3A3A2S1S0S4Se7S15S21GdA1M15A1M16S16G0A1M17G0G4S8Se6Se5G11S33A2G14A3A5S3A3S1S0S4S2fSe9Se8S32S2aG11S12G15A1A4ScaA3S3A3S1S0S4S3bG16A1S3A3S1S0S4S3eG16S41A2S3A3S1S0S4S2fS11S11SfS3cG16R1A2Se3S41S10S6A1M18R1A3A2Lo;S6cA3S3A3S1S0S4S2fG12G12SfS3dR1A1Sd4S41G18R1A3A2Lr;GeA3S3A3S1S0S17Sd5G11PdA2G17A3S1S0S22Sd2S32GdG11S6cSc9A5S76A3S1S0GaS30S11S14S21S76A1M19A1U1M1aA3S5S11S1cSe0Sd6S16N250A1A2S16Sc3S58A1A1G17S9S1eA1M1bS1bA5A2A3S1S0S13Sd1G19G1aS54A3S107A3S1S0S4ScbG19S107A2S3A3S1S0S4S3bS15G19A1A1S3A3S1S0S4Sc2SaS11S14S107A1M1cA2M1dS8S6S7S6G1aS7S6U0M1eS9S6A1A3M1fA3S37U2M20S36G1dG20A2A2A3M21A2S3A3S1S0G8SccS34S107Sc1G1cG21A2A2G1eA2S5S13S127A2A3S1S0GaS30S11S14S127A1G1aA3S5S11S1cS16S150A1G17G17G1bS1bA5A2A3S1S0S13S151S127G1aA2S13fA3S1S0S22Sd7S69S28S13fS24S76A1S26S76A1A3A2S9eA3S1S1S0S4S31S2aS12S21S9eA1M22A1M23A2S3A3S1S0S4S19G22A1ScA3S0S4S2bG23S4fG14A1M24A2S3A3A2A2S1S0G6S27S3aS53S52S9eS3A5S5G5S7S23S25S60S35A2G7A3A2A3S1S0G8ScdS21S60A1M25G1eS16Sc3SddA1A1A3S5S13SedA2A3S1S0S4S1dS4dSedA1M26A1S3A3S1S0S4Sd9S15SedA1S14SedA1S24S60A1Sc7Sc8S2eG24A1S3fA7S3A3S1S0Sc5S12SedA1S12G25A1A3S1S0S17S26S60A1S16SebA1A3S1S0S4S2fS18S1aS12G26A1A1S8S18S59S4aS60SedA2G0A2M27S15G26A1A3A3S3A3S1S0S4S2fS18S44G27A3S3A3S1S0G10SceS4bG0S60SedA3M28S57G0A1M29S5cG28G0A2M2aA3S5GfS94A2A3S1S0S4ScfG28G29G2aS94S38S23S22S29SdfG0A1A4A5S3A3S1S0S4S31S2aS12S21G28A1M2bA1M2cA2S3A3S1S0S4S2bG2cG24A2S3A3S1S0S4S2fS18S1aG2cA1S15G2bA1A3S3A3S1S0S22Sd2G29G28G2aS94SdeG0A1A5S80A3S1S0S4Sc2SaS11S14S21S80A1M2dA1M2eA2M2fS5aG2fA1M30A2S3A3S1S0GfSc1G2eG30A2S14S104A1M31A3S1S0S13S34G2dG31A2S104A3S1S0GfG31S8S11S39S11S36SaS11G31A2U4A2G31A3M32S38SdbS11SdaS3fA4A3A3S1S0S13S34S104G32A2S126A3S1S0S4SdcSc7S3fA2S3A3S1S0S4S2bS12S104A1G24A2S3A3S1S0S4Sc2SaS11S14S126A1M33A2M34S8S6S7S6U8G1fA3S8S6S37G1aU7A2S37U9M35S36G34G35A2A2A3A3M36A2S3A3S1S0G8SccS34S126Sc1G33G36A2A2G1eA2S5S13S13eA2A3S1S0S22S28S13eS24S80A1S26S80A1A3Sa8A3S1S1S0S4S31S2aS12S21Sa8A1M37A1M38A2S3A3S1S0S4S19G37A1ScA3S0S4S2bG38G24A2S3A3A2A2S1S0G6S27S3aS53S52Sa8S3A5S5G5S7S23S25Sb1S35A2S7S23S25Sb8S35A2G7A3A3A2A3S0S4S45S5dS3Sc4G0G13A2A2S41G14Sb1A4S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Definition LEc1_iw : nat := Eval vm_compute in locate (ss_objs (ax_S E_fzEc1)) spT (SLit (- (DEEP - 80))).
Definition LEc1_S1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_fzEc1) LEc1_iw (SLit (- fz_frame))) (ax_S E_fzEc1).
Definition LEc1_S2 : sstate := Eval vm_compute in set_obj_at LEc1_S1 LEc1_iw O_WfzT.
Definition LEc1_S3 : sstate := Eval vm_compute in add_obj LEc1_S2 O_payE.
Definition LEc1_U1 : sstate := Eval vm_compute in set_obj_at (ax_S TT_fzEc1) 1 O_WloT.
Definition LEc1_U3 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LEc1_U1 (select (ss_objs LEc1_U1) ([1; 0] ++ seq 2 (length (ss_objs LEc1_U1) - 2))%nat)) 0) LEc1_U1.
Definition LEc1_U4 : sstate := Eval vm_compute in drop_obj_at LEc1_U3 1.
Definition LEc1_P1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_pfEc1) 0 (SLit (- PW))) (ax_S E_pfEc1).
Definition LEc1_Q1 : sstate := Eval vm_compute in set_objs (ax_S T_pfEc1) (select (ss_objs (ax_S T_pfEc1)) (pf_u1 (length (ss_objs (ax_S T_pfEc1))))).
Definition LEc1_Q2 : sstate := Eval vm_compute in set_objs LEc1_Q1 (firstn (length (ss_objs LEc1_Q1) - 4) (ss_objs LEc1_Q1)).
Definition LEc1_Q4 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LEc1_Q2 (select (ss_objs LEc1_Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs LEc1_Q2) - 9))%nat)) 0) LEc1_Q2.
Lemma LEc1_facts : ltac2:(tb__ "0|39|
S1S1S0S4S31S2aS12S21S5dS3Z1M0A2M1A1M2A1M3A2S3A3S1S0S4S19G2A1ScA3S0S4S2bG3S4eS42G0A1M4A1A2S3A3A2A2S1S0SbSdS23A1M5A1M6S27S3aS53S52G1S3A5S5G5S7S23S25S8bS35A2S9S23A1M7A3A2A3S1S0SbS13A1M8ScdS21S8bA1M9S12bS16Sc3Se1A1A1A3S5S13S109A2A3S1S0SbS11A1MaS30S11S14S109A1S12bA3S5S11S54A2A3S1S0S13Sd1S109S12bS55A3S10aA3S1S0S4ScbS109S10aA2S3A3S1S0S4S3bS15G9A1MbA1S3A3S1S0S13S152S10aS56A2Sf8A3S1S0S4S1dSf8A1S3A3S1S0S4S20S12S10aA1S56A2S3A3S1S1S0Sc5S12Sf8A1S12G9A1McA3S0SdS18A1S15Sf8A1GbA3A2S1S0S4SeaS24S47S8bSf8A2MdA1MeGeA2S3A3S1S0SbSdS11A1MfA1M10SceGdS32S5bGdA1M11A3S5GfS6dA2A3S1S0S4Sd0GdS32G11S6dS7S22Sc9S9S22A1A3A5S3A3S1S0S4Sd3S2aG11A2S3A3S1S0S4Se2G11S2aA2S3A3S1S0S4S31S2aGcA2S3A3S1S1S0S4S2bGcS2dS8SeS17S17A2M12S41S9G12A1A3S9SeSeS17Sc6A2S17A2A1G4S2cA4A2S3A3S0S4Se4GcS42Z2A1M13A2S3A3A2S1S0S4Se7S15S21GdA1M14A1M15S16Z0M16A1M17G16G4S8Se6Se5G11S33A2G13A3A5S3A3S1S0S4S2fSe9Se8S32S2aG11S12G14A1A4ScaA3S3A3S1S0S4S3bG15A1S3A3S1S0S4S3eG15S41A2S3A3S1S0S4S2fS11S11SfS3cG15R1A2Se3S41S10S6A1M18R1A3A2Lo;S6dA3S3A3S1S0S4S2fG12G12SfS3dR1A1Sd4S41G18R1A3A2Lr;GeA3S3A3S1S0S17Sd5G11PdA2G17A3S1S0S22Sd2S32GdG11S6dSc9A5S77A3S1S0GaS30S11S14S21S77A1M19A1U1M1aA3S5S11S1cSe0Sd6S16N250A1A2S16Sc3S58A1A1G17S9S1eA1M1bS1bA5A2A3S1S0S13Sd1G19G1aS54A3S10bA3S1S0S4ScbG19S10bA2S3A3S1S0S4S3bS15G19A1A1S3A3S1S0S4Sc2SaS11S14S10bA1M1cA2M1dS8S6S7S6G1aS7S6U0M1eS9S6A1A3M1fA3S37U2M20S36G1dG20A2A2A3M21A2S3A3S1S0G8SccS34S10bSc1G1cG21A2A2G1eA2S5S13S12aA2A3S1S0GaS30S11S14S12aA1G1aA3S5S11S1cS16S150A1G17G17G1bS1bA5A2A3S1S0S13S151S12aG1aA2S141A3S1S0S22Sd7S69S28S141S24S77A1S26S77A1A3A2S9fA3S1S1S0S4S31S2aS12S21S9fA1M22A1M23A2S3A3S1S0S4S19G22A1ScA3S0S4S2bG23S4fG13A1M24A2S3A3A2A2S1S0G6S27S3aS53S52S9fS3A5S5G5S7S23S25S61S35A2G7A3A2A3S1S0G8ScdS21S61A1M25G1eS16Sc3SddA1A1A3S5S13SeeA2A3S1S0S4S1dS4dSeeA1M26A1S3A3S1S0S4Sd9S15SeeA1S14SeeA1S24S61A1Sc7Sc8S2eG24A1S3fA7S3A3S1S0Sc5S12SeeA1S12G25A1A3S1S0S17S26S61A1S16SebA1A3S1S0S4S2fS18S1aS12G26A1A1S8S18S59S4aS61SeeA2G0A2M27S15G26A1A3A3S3A3S1S0S4S2fS18S44G27A3S3A3S1S0G10SceS4bG0S61SeeA3M28S57G0A1M29S5cG28G0A2M2aA3S5GfS95A2A3S1S0S4ScfG28G29G2aS95S38S23S22S29SdfG0A1A4A5S3A3S1S0S4S31S2aS12S21G28A1M2bA1M2cA2S3A3S1S0S4S2bG2cG24A2S3A3S1S0S4S2fS18S1aG2cA1S15G2bA1A3S3A3S1S0S22Sd2G29G28G2aS95SdeG0A1A5S81A3S1S0S4Sc2SaS11S14S21S81A1M2dA1M2eA2M2fS5aG2fA1M30A2S3A3S1S0GfSc1G2eG30A2S14S108A1M31A3S1S0S13S34G2dG31A2S108A3S1S0GfG31S8S11S39S11S36SaS11G31A2U4A2G31A3M32S38SdbS11SdaS3fA4A3A3S1S0S13S34S108G32A2S129A3S1S0S4SdcSc7S3fA2S3A3S1S0S4S2bS12S108A1G24A2S3A3S1S0S4Sc2SaS11S14S129A1M33A2M34S8S6S7S6U8G1fA3S8S6S37G1aU7A2S37U9M35S36G34G35A2A2A3A3M36A2S3A3S1S0G8SccS34S129Sc1G33G36A2A2G1eA2S5S13S140A2A3S1S0S22S28S140S24S81A1S26S81A1A3Sa9A3S1S1S0S4S31S2aS12S21Sa9A1M37A1M38A2S3A3S1S0S4S19G37A1ScA3S0S4S2bG38G24A2S3A3A2A2S1S0G6S27S3aS53S52Sa9S3A5S5G5S7S23S25Sb2S35A2S7S23S25Sb9S35A2G7A3A3A2A3S0S4S45S5dS3Sc4G0G0A2A2S41G13Sb2A4S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Definition LEc2_iw : nat := Eval vm_compute in locate (ss_objs (ax_S E_fzEc2)) spT (SLit (- (DEEP - 80))).
Definition LEc2_S1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_fzEc2) LEc2_iw (SLit (- fz_frame))) (ax_S E_fzEc2).
Definition LEc2_S2 : sstate := Eval vm_compute in set_obj_at LEc2_S1 LEc2_iw O_WfzT.
Definition LEc2_S3 : sstate := Eval vm_compute in add_obj LEc2_S2 O_payE.
Definition LEc2_U1 : sstate := Eval vm_compute in set_obj_at (ax_S TT_fzEc2) 1 O_WloT.
Definition LEc2_U3 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LEc2_U1 (select (ss_objs LEc2_U1) ([1; 0] ++ seq 2 (length (ss_objs LEc2_U1) - 2))%nat)) 0) LEc2_U1.
Definition LEc2_U4 : sstate := Eval vm_compute in drop_obj_at LEc2_U3 1.
Definition LEc2_P1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_pfEc2) 0 (SLit (- PW))) (ax_S E_pfEc2).
Definition LEc2_Q1 : sstate := Eval vm_compute in set_objs (ax_S T_pfEc2) (select (ss_objs (ax_S T_pfEc2)) (pf_u1 (length (ss_objs (ax_S T_pfEc2))))).
Definition LEc2_Q2 : sstate := Eval vm_compute in set_objs LEc2_Q1 (firstn (length (ss_objs LEc2_Q1) - 4) (ss_objs LEc2_Q1)).
Definition LEc2_Q4 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LEc2_Q2 (select (ss_objs LEc2_Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs LEc2_Q2) - 9))%nat)) 0) LEc2_Q2.
Lemma LEc2_facts : ltac2:(tb__ "0|39|
S1S1S0S4S31S2aS12S21S5dS3Z2M0A2M1A1M2A1M3A2S3A3S1S0S4S19G2A1ScA3S0S4S2bG3S4eS42G0A1M4A1A2S3A3A2A2S1S0SbSdS23A1M5A1M6S27S3aS53S52G1S3A5S5G5S7S23S25S8cS35A2S9S23A1M7A3A2A3S1S0SbS13A1M8ScdS21S8cA1M9S12eS16Sc3Se1A1A1A3S5S13S10dA2A3S1S0SbS11A1MaS30S11S14S10dA1S12eA3S5S11S54A2A3S1S0S13Sd1S10dS12eS55A3S10eA3S1S0S4ScbS10dS10eA2S3A3S1S0S4S3bS15G9A1MbA1S3A3S1S0S13S152S10eS56A2Sf9A3S1S0S4S1dSf9A1S3A3S1S0S4S20S12S10eA1S56A2S3A3S1S1S0Sc5S12Sf9A1S12G9A1McA3S0SdS18A1S15Sf9A1GbA3A2S1S0S4SeaS24S47S8cSf9A2MdA1MeGeA2S3A3S1S0SbSdS11A1MfA1M10SceGdS32S5bGdA1M11A3S5GfS6eA2A3S1S0S4Sd0GdS32G11S6eS7S22Sc9S9S22A1A3A5S3A3S1S0S4Sd3S2aG11A2S3A3S1S0S4Se2G11S2aA2S3A3S1S0S4S31S2aGcA2S3A3S1S1S0S4S2bGcS2dS8SeS17S17A2M12S41S9G12A1A3S9SeSeS17Sc6A2S17A2A1G4S2cA4A2S3A3S0S4Se4GcS42Z3A1M13A2S3A3A2S1S0S4Se7S15S21GdA1M14A1M15S16Z0M16A1M17G16G4S8Se6Se5G11S33A2G13A3A5S3A3S1S0S4S2fSe9Se8S32S2aG11S12G14A1A4ScaA3S3A3S1S0S4S3bG15A1S3A3S1S0S4S3eG15S41A2S3A3S1S0S4S2fS11S11SfS3cG15R1A2Se3S41S10S6A1M18R1A3A2Lo;S6eA3S3A3S1S0S4S2fG12G12SfS3dR1A1Sd4S41G18R1A3A2Lr;GeA3S3A3S1S0S17Sd5G11PdA2G17A3S1S0S22Sd2S32GdG11S6eSc9A5S78A3S1S0GaS30S11S14S21S78A1M19A1U1M1aA3S5S11S1cSe0Sd6S16N250A1A2S16Sc3S58A1A1G17S9S1eA1M1bS1bA5A2A3S1S0S13Sd1G19G1aS54A3S10fA3S1S0S4ScbG19S10fA2S3A3S1S0S4S3bS15G19A1A1S3A3S1S0S4Sc2SaS11S14S10fA1M1cA2M1dS8S6S7S6G1aS7S6U0M1eS9S6A1A3M1fA3S37U2M20S36G1dG20A2A2A3M21A2S3A3S1S0G8SccS34S10fSc1G1cG21A2A2G1eA2S5S13S12dA2A3S1S0GaS30S11S14S12dA1G1aA3S5S11S1cS16S150A1G17G17G1bS1bA5A2A3S1S0S13S151S12dG1aA2S143A3S1S0S22Sd7S69S28S143S24S78A1S26S78A1A3A2Sa0A3S1S1S0S4S31S2aS12S21Sa0A1M22A1M23A2S3A3S1S0S4S19G22A1ScA3S0S4S2bG23S4fG13A1M24A2S3A3A2A2S1S0G6S27S3aS53S52Sa0S3A5S5G5S7S23S25S62S35A2G7A3A2A3S1S0G8ScdS21S62A1M25G1eS16Sc3SddA1A1A3S5S13SefA2A3S1S0S4S1dS4dSefA1M26A1S3A3S1S0S4Sd9S15SefA1S14SefA1S24S62A1Sc7Sc8S2eG24A1S3fA7S3A3S1S0Sc5S12SefA1S12G25A1A3S1S0S17S26S62A1S16SebA1A3S1S0S4S2fS18S1aS12G26A1A1S8S18S59S4aS62SefA2G0A2M27S15G26A1A3A3S3A3S1S0S4S2fS18S44G27A3S3A3S1S0G10SceS4bG0S62SefA3M28S57G0A1M29S5cG28G0A2M2aA3S5GfS96A2A3S1S0S4ScfG28G29G2aS96S38S23S22S29SdfG0A1A4A5S3A3S1S0S4S31S2aS12S21G28A1M2bA1M2cA2S3A3S1S0S4S2bG2cG24A2S3A3S1S0S4S2fS18S1aG2cA1S15G2bA1A3S3A3S1S0S22Sd2G29G28G2aS96SdeG0A1A5S82A3S1S0S4Sc2SaS11S14S21S82A1M2dA1M2eA2M2fS5aG2fA1M30A2S3A3S1S0GfSc1G2eG30A2S14S10cA1M31A3S1S0S13S34G2dG31A2S10cA3S1S0GfG31S8S11S39S11S36SaS11G31A2U4A2G31A3M32S38SdbS11SdaS3fA4A3A3S1S0S13S34S10cG32A2S12cA3S1S0S4SdcSc7S3fA2S3A3S1S0S4S2bS12S10cA1G24A2S3A3S1S0S4Sc2SaS11S14S12cA1M33A2M34S8S6S7S6U8G1fA3S8S6S37G1aU7A2S37U9M35S36G34G35A2A2A3A3M36A2S3A3S1S0G8SccS34S12cSc1G33G36A2A2G1eA2S5S13S142A2A3S1S0S22S28S142S24S82A1S26S82A1A3SaaA3S1S1S0S4S31S2aS12S21SaaA1M37A1M38A2S3A3S1S0S4S19G37A1ScA3S0S4S2bG38G24A2S3A3A2A2S1S0G6S27S3aS53S52SaaS3A5S5G5S7S23S25Sb3S35A2S7S23S25SbaS35A2G7A3A3A2A3S0S4S45S5dS3Sc4G0Z1A2A2S41G13Sb3A4S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.

Definition LEc3_iw : nat := Eval vm_compute in locate (ss_objs (ax_S E_fzEc3)) spT (SLit (- (DEEP - 80))).
Definition LEc3_S1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_fzEc3) LEc3_iw (SLit (- fz_frame))) (ax_S E_fzEc3).
Definition LEc3_S2 : sstate := Eval vm_compute in set_obj_at LEc3_S1 LEc3_iw O_WfzT.
Definition LEc3_S3 : sstate := Eval vm_compute in add_obj LEc3_S2 O_payE.
Definition LEc3_U1 : sstate := Eval vm_compute in set_obj_at (ax_S TT_fzEc3) 1 O_WloT.
Definition LEc3_U3 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LEc3_U1 (select (ss_objs LEc3_U1) ([1; 0] ++ seq 2 (length (ss_objs LEc3_U1) - 2))%nat)) 0) LEc3_U1.
Definition LEc3_U4 : sstate := Eval vm_compute in drop_obj_at LEc3_U3 1.
Definition LEc3_P1 : sstate := Eval vm_compute in optS' (split_obj_at (ax_S E_pfEc3) 0 (SLit (- PW))) (ax_S E_pfEc3).
Definition LEc3_Q1 : sstate := Eval vm_compute in set_objs (ax_S T_pfEc3) (select (ss_objs (ax_S T_pfEc3)) (pf_u1 (length (ss_objs (ax_S T_pfEc3))))).
Definition LEc3_Q2 : sstate := Eval vm_compute in set_objs LEc3_Q1 (firstn (length (ss_objs LEc3_Q1) - 4) (ss_objs LEc3_Q1)).
Definition LEc3_Q4 : sstate := Eval vm_compute in optS' (merge_objs_at (set_objs LEc3_Q2 (select (ss_objs LEc3_Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs LEc3_Q2) - 9))%nat)) 0) LEc3_Q2.
Lemma LEc3_facts : ltac2:(tb__ "0|39|
S1S1S0S4S31S2aS12S21S5dS3Z3M0A2M1A1M2A1M3A2S3A3S1S0S4S19G2A1ScA3S0S4S2bG3S4eS42G0A1M4A1A2S3A3A2A2S1S0SbSdS23A1M5A1M6S27S3aS53S52G1S3A5S5G5S7S23S25S8dS35A2S9S23A1M7A3A2A3S1S0SbS13A1M8ScdS21S8dA1M9S131S16Sc3Se1A1A1A3S5S13S111A2A3S1S0SbS11A1MaS30S11S14S111A1S131A3S5S11S54A2A3S1S0S13Sd1S111S131S55A3S112A3S1S0S4ScbS111S112A2S3A3S1S0S4S3bS15G9A1MbA1S3A3S1S0S13S152S112S56A2SfaA3S1S0S4S1dSfaA1S3A3S1S0S4S20S12S112A1S56A2S3A3S1S1S0Sc5S12SfaA1S12G9A1McA3S0SdS18A1S15SfaA1GbA3A2S1S0S4SeaS24S47S8dSfaA2MdA1MeGeA2S3A3S1S0SbSdS11A1MfA1M10SceGdS32S5bGdA1M11A3S5GfS6fA2A3S1S0S4Sd0GdS32G11S6fS7S22Sc9S9S22A1A3A5S3A3S1S0S4Sd3S2aG11A2S3A3S1S0S4Se2G11S2aA2S3A3S1S0S4S31S2aGcA2S3A3S1S1S0S4S2bGcS2dS8SeS17S17A2M12S41S9G12A1A3S9SeSeS17Sc6A2S17A2A1G4S2cA4A2S3A3S0S4Se4GcS42Z4A1M13A2S3A3A2S1S0S4Se7S15S21GdA1M14A1M15S16Z0M16A1M17G16G4S8Se6Se5G11S33A2G13A3A5S3A3S1S0S4S2fSe9Se8S32S2aG11S12G14A1A4ScaA3S3A3S1S0S4S3bG15A1S3A3S1S0S4S3eG15S41A2S3A3S1S0S4S2fS11S11SfS3cG15R1A2Se3S41S10S6A1M18R1A3A2Lo;S6fA3S3A3S1S0S4S2fG12G12SfS3dR1A1Sd4S41G18R1A3A2Lr;GeA3S3A3S1S0S17Sd5G11PdA2G17A3S1S0S22Sd2S32GdG11S6fSc9A5S79A3S1S0GaS30S11S14S21S79A1M19A1U1M1aA3S5S11S1cSe0Sd6S16N250A1A2S16Sc3S58A1A1G17S9S1eA1M1bS1bA5A2A3S1S0S13Sd1G19G1aS54A3S113A3S1S0S4ScbG19S113A2S3A3S1S0S4S3bS15G19A1A1S3A3S1S0S4Sc2SaS11S14S113A1M1cA2M1dS8S6S7S6G1aS7S6U0M1eS9S6A1A3M1fA3S37U2M20S36G1dG20A2A2A3M21A2S3A3S1S0G8SccS34S113Sc1G1cG21A2A2G1eA2S5S13S130A2A3S1S0GaS30S11S14S130A1G1aA3S5S11S1cS16S150A1G17G17G1bS1bA5A2A3S1S0S13S151S130G1aA2S145A3S1S0S22Sd7S69S28S145S24S79A1S26S79A1A3A2Sa1A3S1S1S0S4S31S2aS12S21Sa1A1M22A1M23A2S3A3S1S0S4S19G22A1ScA3S0S4S2bG23S4fG13A1M24A2S3A3A2A2S1S0G6S27S3aS53S52Sa1S3A5S5G5S7S23S25S63S35A2G7A3A2A3S1S0G8ScdS21S63A1M25G1eS16Sc3SddA1A1A3S5S13Sf0A2A3S1S0S4S1dS4dSf0A1M26A1S3A3S1S0S4Sd9S15Sf0A1S14Sf0A1S24S63A1Sc7Sc8S2eG24A1S3fA7S3A3S1S0Sc5S12Sf0A1S12G25A1A3S1S0S17S26S63A1S16SebA1A3S1S0S4S2fS18S1aS12G26A1A1S8S18S59S4aS63Sf0A2G0A2M27S15G26A1A3A3S3A3S1S0S4S2fS18S44G27A3S3A3S1S0G10SceS4bG0S63Sf0A3M28S57G0A1M29S5cG28G0A2M2aA3S5GfS97A2A3S1S0S4ScfG28G29G2aS97S38S23S22S29SdfG0A1A4A5S3A3S1S0S4S31S2aS12S21G28A1M2bA1M2cA2S3A3S1S0S4S2bG2cG24A2S3A3S1S0S4S2fS18S1aG2cA1S15G2bA1A3S3A3S1S0S22Sd2G29G28G2aS97SdeG0A1A5S83A3S1S0S4Sc2SaS11S14S21S83A1M2dA1M2eA2M2fS5aG2fA1M30A2S3A3S1S0GfSc1G2eG30A2S14S110A1M31A3S1S0S13S34G2dG31A2S110A3S1S0GfG31S8S11S39S11S36SaS11G31A2U4A2G31A3M32S38SdbS11SdaS3fA4A3A3S1S0S13S34S110G32A2S12fA3S1S0S4SdcSc7S3fA2S3A3S1S0S4S2bS12S110A1G24A2S3A3S1S0S4Sc2SaS11S14S12fA1M33A2M34S8S6S7S6U8G1fA3S8S6S37G1aU7A2S37U9M35S36G34G35A2A2A3A3M36A2S3A3S1S0G8SccS34S12fSc1G33G36A2A2G1eA2S5S13S144A2A3S1S0S22S28S144S24S83A1S26S83A1A3SabA3S1S1S0S4S31S2aS12S21SabA1M37A1M38A2S3A3S1S0S4S19G37A1ScA3S0S4S2bG38G24A2S3A3A2A2S1S0G6S27S3aS53S52SabS3A5S5G5S7S23S25SbbS35A2G7A3A2A3S2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.conj_vmc. Qed.
End DrvTLXi_f1.

(* [comment removed for export] *)
Module DrvTLXi.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nat"; "app"; "Some"; "nil"; "cons"; "prod"; "option"; "length"; "false"; "pair"; "None"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "sym_runA"; "mkLeafA"; "la_state"; "ax_base"; "mkAX"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sstate"; "sobj"; "ss_next"; "ss_facts"; "SLit"; "ss_objs"; "sprop"; "ss_lenient"; "sprop_below"; "mkObj"; "swf"; "DUnknown"; "SVar"; "cell"; "SPUle"; "holds"; "sprop_eqb"; "obj_wf"; "odefault"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "tcons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "ExitEv"; "WriteEv"; "m_fs"; "FdEntry"; "FdChannel"; "VmState"; "fd_lookup"; "m_fds"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "ok_frameKA"; "ANone"; "NDA"; "PTrue"; "ndesc"; "nd_tv"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states"; "J_E"; "s_fz"; "L_P"; "L_E"; "CUTS_L"; "FUEL_L"; "PreP"; "s_m"; "s_pf"; "s_fp"; "O_WloT"; "PreM"; "pf_hints"; "pf_u1"; "s_fn"; "CUTS_T"; "PreFN"; "s_mc"; "vP"; "LX_E10"; "LX_Ec0"; "LX_Ec1"; "LX_Ec2"; "LX_Ec3"; "LX_P10"; "LX_Pc0"; "LX_Pc1"; "LX_Pc2"; "LX_Pc3"; "O_WfzT"; "O_payE"; "O_srcT"; "PostFN"; "T_mok1"; "T_mokc"; "WDP"; "E_mP1"; "E_mPc"; "FUEL_T0"; "FUEL_T1"; "FUEL_T2"; "O_cstkB"; "PostsM"; "X_payE"; "mc_hints"; "sel_buf"; "sel_rtc_last"; "sel_win"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "le"; "lt"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX"; "bd_L"; "bd_E"; "bd_J"; "ndM"; "Cfz"; "CfzE"; "ndE1"; "ndL1"; "CP"; "EVk"; "kept"; "ndE0"; "ndJE"; "ndJX"; "Cmc"; "ndEX"; "ndL0"; "ndLX"; "Cpf"; "CpfE"; "N_pf"; "keptE"; "bd_M"; "B3c"; "N_mc"; "Cpf0"; "Cpf0E"; "O_srcM"; "P1c"; "P1cE"; "keptX"; "mc_needb"; "ms16_shape"; "B3h"; "X_T0"; "X_freeE"; "X_freeP"; "X_join"; "X_loopE"; "X_loopP"; "X_mc"; "X_msite"; "edge_okb"; "plen_factsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "KcT"; "JT"; "KV_T"; "KP_T"; "P0T"; "CST_drv"; "@Corelib.Lists.ListDef"; "map"; "seq"; "firstn"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2"; "fuzz_one_sumT"; "P_fz"; "PD_fz"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "calls_of"; "vB"; "vCap"; "nd_T"; "S_T"; "vPlen"; "PreF"; "sp0"; "tv_T"; "CUTS_X"; "FUEL_X"; "PostF"; "bd_T"; "dropX"; "locate"; "vClen"; "vLen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit"; "ch1"; "supported";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "sp0_factsb"; "drv_xrb"; "kept_nzb"; "robjs_checkD"; "xrs_checkD"; "drv_objb"; "ex_pipe"; "fb_pipe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "PEND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "Pre_fz"; "bd_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "bd_below"; "bud_le"; "bud_pay"; "bsumV"; "KU"; "LARGE_MIN"; "SECCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "xr_tracked"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "robj_tracked"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "carve_okb"; "lc_obj"; "lcarve"; "uncarve_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "Pre_mc0"; "P_icpt"; "Posts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "L_malloc_ok"; "UStopLe"; "V_RES"; "alloc_contractsA"; "ulink"; "with_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TR_INIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.PFAddr"; "PW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "P_pf"; "Posts_pf"; "kok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.FZAddr"; "fz_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "wsub_dom_below"; "pos_add_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pd_okA"; "pdescA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "drop_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC"; "add_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS"; "malloc_contractA_strong"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceS GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB DrvGlueC.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT Lib_fuzz_iface2 DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g7.
Export OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvTLXi_h OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g8.DrvTLXi_f1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g7.DrvTLXi_f2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g7.DrvTLXi_f3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g8.DrvTLXi_f4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g7.DrvTLXi_f5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g8.DrvTLXi_f6.
Section TLXI.
Variable AInv : ltac2:(tb__ "0|0|
S125S1fS8S45Q40A1A1S3cOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S48S102VCST;R1A2S1S84Z0R2A2S85R2S10bA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S48S102VXGL;R1A2S1S84Z0R2A2S85R2S10bA2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S48S102Sb9R1A2S102VCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Variable ok : world -> Prop.
Variable Spec : list event -> Prop.
Hypothesis HOKJ : ltac2:(tb__ "0|0|
S39S1fS8S45Q40A1A1S8S3bA1S3cR5R4R3R2R1A4S37VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S3aS5Vok;R2A3F_;FJ;").
Hypothesis HOKP : ltac2:(tb__ "0|0|
S39S1fS8S45Q40A1A1S8S3bA1S3cR5R4R3R2R1A4S37VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S11fS5Vok;R2A3F_;FJ;").
Hypothesis Hokh : ok_halted ok Spec.
Hypothesis AC : ltac2:(tb__ "0|0|
S110S5S10cVAInv;VCST;VXGL;A5").
Hypothesis MS : ltac2:(tb__ "0|0|
S124S5S10cVAInv;VCST;VXGL;A5").
Variable rhoT : valuation.
Variable F : list byte.
Variable T0 : list event.
Variable MD : Model -> Prop.
Hypothesis HMDvm : ltac2:(tb__ "0|0|
S3cS42VMD;R2A1VMD;S112R2R3A2A1F_;Fv;Fmd;").
Hypothesis HMDfd1 : ltac2:(tb__ "0|0|
S3cVMD;R1A1S0SfS40A1S43S44R2A1Sd9A2SbS40S41Sd9A1A2A3F_;Fmd;").
Hypothesis Htc : ltac2:(tb__ "0|0|
S9S37VSpec;SaS3bVT0;S91R1A1A3A2Fk;").
Let JT' (k : nat) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
Sb5VAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;S4eVk;Vnd;Aa").
Let X_loopP' := X_loopP AInv CST XGL ALA HCST HXGL HLV HCSTok HCSTdrv HLPP ok Spec HOKJ HOKP rhoT F T0 MD HMDvm HMDfd1 Htc.
Let X_loopE' := X_loopE AInv CST XGL ALA HCST HXGL HLV HCSTok HCSTdrv HLPP ok Spec HOKJ HOKP rhoT F T0 MD HMDvm HMDfd1 Htc.
Let X_freeP' := X_freeP AInv CST XGL ALA HCST HXGL HCSTdrv ok Spec HOKJ HOKP AC rhoT F T0 MD HMDvm Htc.
Let X_freeE' := X_freeE AInv CST XGL ALA HCST HXGL HCSTdrv ok Spec HOKJ HOKP AC rhoT F T0 MD HMDvm Htc.
Let X_join' : ltac2:(tb__ "0|6|
S9S8Sf1A1M0G0S48S20S48S16S8S22A1M1S0SfS16A1Se2R7R6S52R5R4A2A3SbS16R2A2A3S0SfG1A1Se1S4dScSeS20S20A2M2A1M3ScSeSeS20S48A2S20A2A1M4R7S4cA4R3R6R4A4SbG1R2A2A3Sc6SeS48S48A2S12S48S48R7R5A4SdaA3S3cVMD;R1A1VSpec;SaS3bSaS3bVT0;S91RdA1A3SaS3bSbaS45Q8A1S3bS3eSd9A1SeaRaA1A4SdS3bS3dS46Q40M5R8A2S3fR2A1A2ScS3bA1A3A3A3A1F_;Fmd;S1fS8S45G5A1A1S35S5Vok;S38S5S9S4fSb5VAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;S4eR2R1AaLnd;Lk;ReS4dSdG2S12S20S20Sc9ScaA4G3A3G4RdS4cA4A2S52RbRaA2R2R1A5S36S2L_;A4Ftp;Frho;F_;F_;F_;F_;FR;FEx;Fc;Fst;Fn;FbdX;FbdJ;Fkx;") := ltac2:(tb__ "0|0|
SadVAInv;VCST;VXGL;VALA;VHCST;VHXGL;VHCSTdrv;VHLPP;Vok;VSpec;VHOKJ;VHOKP;VHokh;VAC;VrhoT;VF;VT0;VMD;VHMDvm;VHMDfd1;VHtc;A15").
Let X_mc' := X_mc AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP ok Spec HOKJ rhoT F T0 MD HMDvm Htc.
Let X_msite' : ltac2:(tb__ "0|a|
S16S8S22A1M0S16S0SfG0A1SedR3S5dS59R3A1A3SbG0R2A2A3S0S7SeeR4S5dS59R4A1R3S7cA5S6A3S0S7SfbS47S59R5A1A2S6A3S0S7S51S47S23S15R6A1A1A2S6A3S1S0S7S4aS23S15R7A1A1M1ScbA2S6A3S0S7Sf3G1S9eA2S6A3A2S0S20Se7S59R8A1PcA2ScdA3S0S7S34S23S15R9A1A1ScdA2S6A3S1S0S20Se7Sf0S59RaA1S5dS10dS10cScS111A1S10eA3M2RaA4S10fA2S2dS11bS23S15RaA1A1UaA2M3A1A3S0S49G3S64A3A2S0S7Sf5S24S15RbA1A1ScdSf7Sd4S9eA5S6A3S0S7SdbS24S15RcA1A1A1S6A3S0S7SdeS24S15RdA1A1Sd0S13S9A1M4RcA4S6A3S0S7SdfS24S15ReA1M5A1Sd0G4S26G5A1SdcS18ReA1A6S6A3S0S7Sb3S24S15RfA1A1A1S6A3S0S16SfaS5dR10S59R10A1RfG2A5ReA3S1fS8S45Q40A1A1M6S35S5Vok;S38S5S9S4fSb5VAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;S4eR2R1AaLnd;Lk;M7U0M8S8bS9eA1A2R11R2R1A5S36S2L_;M9A4Ftp;Frho;S1fG6S35S5Vok;S38S5G7G8ScbA2R14R2R1A5G9A4Ftp;Frho;FHMC;FMTk;FMsz;FMxr;FMro;FMspf;FMpay;FMres;FMsv;FMs12;FMnb;FMnx;FMcT;FMcc;FMfr;FTk;FR;FEm;") := ltac2:(tb__ "0|0|
Sb1VAInv;VCST;VXGL;VALA;VHCST;VHXGL;VHCSTdrv;Vok;VSpec;VHOKJ;VHOKP;VMS;VrhoT;VF;VT0;VMD;VHMDvm;VHtc;A12").
Let X_T0' := X_T0 AInv CST XGL ALA ok Spec HOKJ rhoT F T0 MD HMDvm Htc.

Lemma X_LP10 : ltac2:(tb__ "0|6|
S36OF_;S4bS5Sb4VT0;VMD;U0M0A3M1R1A3SbeVAInv;VCST;VXGL;G1R2A5F_;Fok';S1fS8S45Q40A1A1M2S35S5Vok;S38S5VJT';U1S8fS88Z1A1A1A2S6aR2R1A5S36S2L_;M3A4Ftp;Frho;M4G4S1fG2S35S5Vok;S38S5VJT';G0S98S88Z0M5A1A1A2S54S11G5A2R2R1A5G3A4Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LP10_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58).
  apply (X_loopP' 0 0%nat 1%nat (bd_L 0) (bd_L 1) (bd_L_cap 0) (L_P false 0) LX_P10 E_fzP10 LP10_S1 LP10_S2 R_fzP10 TT_fzP10 LP10_U1 LP10_U3 T_fzP10 E_pfP10 LP10_P1 R_pfP10 T_pfP10 LP10_Q1 LP10_Q2 LP10_Q4 U_pfP10 [mkLeafA LX_P10 RsCut] LP10_iw
           A1 A2 A3 A4 A5 A6 A7 A8 HFZ A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A39 q Hq)) A40 A41 A42 A43 A44 (or_introl (conj eq_refl (conj eq_refl eq_refl))) A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57).
  - intros Lf Hin. destruct Hin as [<-|[]]. right; exact HLX.
  - exact Hnext.
Qed.

Lemma X_LPc0 : ltac2:(tb__ "0|7|
S36OF_;S4bS5Sb4VT0;VMD;U0M0A3M1R1A3SbeVAInv;VCST;VXGL;G1R2A5F_;Fok';S1fS8S45Q40A1A1M2S35S5Vok;S38S5VJT';U1S8fS88Z1M3A1A1A2M4S6bR2R1A5S36S2L_;M5A4Ftp;Frho;S1fG2S35S5Vok;S38S5G4S54S6S82Z0M6G3A2A2R2R1A5G5A4Ftp;Frho;S1fG2S35S5Vok;S38S5VJT';G0S98S88G6A1A1A2S54S6G6A2R2R1A5G5A4Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LPc0_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58).
  apply (X_loopP' 0 0%nat 1%nat (bd_L 0) (bd_L 1) (bd_L_cap 0) (L_P true 0) (L_P true (0 + 1)) E_fzPc0 LPc0_S1 LPc0_S2 R_fzPc0 TT_fzPc0 LPc0_U1 LPc0_U3 T_fzPc0 E_pfPc0 LPc0_P1 R_pfPc0 T_pfPc0 LPc0_Q1 LPc0_Q2 LPc0_Q4 U_pfPc0 [mkLeafA LB_Pc0 RsCut; mkLeafA LX_Pc0 RsCut] LPc0_iw
           A1 A2 A3 A4 A5 A6 A7 A8 HFZ A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A39 q Hq)) A40 A41 A42 A43 A44 (or_introl (conj eq_refl (conj eq_refl eq_refl))) A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57).
  - intros Lf Hin. destruct Hin as [<-|[<-|[]]]; [left; apply backedge_okb_sound; exact A58 | right; exact HLX].
  - exact Hnext.
Qed.

Lemma X_LPc1 : ltac2:(tb__ "0|6|
S36OF_;S4bS5Sb4VT0;VMD;U1M0A3M1R1A3SbeVAInv;VCST;VXGL;G1R2A5F_;Fok';S1fS8S45Q40A1A1M2S35S5Vok;S38S5VJT';G0S8fS88Z2A1A1A2M3S6cR2R1A5S36S2L_;M4A4Ftp;Frho;S1fG2S35S5Vok;S38S5G3S54S6S82Z1M5G5A2A2R2R1A5G4A4Ftp;Frho;S1fG2S35S5Vok;S38S5VJT';G0S98S88G5A1A1A2S54S6G5A2R2R1A5G4A4Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LPc1_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58).
  apply (X_loopP' 1 1%nat 1%nat (bd_L 1) (bd_L 2) (bd_L_cap 1) (L_P true 1) (L_P true (1 + 1)) E_fzPc1 LPc1_S1 LPc1_S2 R_fzPc1 TT_fzPc1 LPc1_U1 LPc1_U3 T_fzPc1 E_pfPc1 LPc1_P1 R_pfPc1 T_pfPc1 LPc1_Q1 LPc1_Q2 LPc1_Q4 U_pfPc1 [mkLeafA LB_Pc1 RsCut; mkLeafA LX_Pc1 RsCut] LPc1_iw
           A1 A2 A3 A4 A5 A6 A7 A8 HFZ A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A39 q Hq)) A40 A41 A42 A43 A44 (or_intror (conj (or_introl eq_refl) (conj eq_refl eq_refl))) A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57).
  - intros Lf Hin. destruct Hin as [<-|[<-|[]]]; [left; apply backedge_okb_sound; exact A58 | right; exact HLX].
  - exact Hnext.
Qed.

Lemma X_LPc2 : ltac2:(tb__ "0|6|
S36OF_;S4bS5Sb4VT0;VMD;U1M0A3M1R1A3SbeVAInv;VCST;VXGL;G1R2A5F_;Fok';S1fS8S45Q40A1A1M2S35S5Vok;S38S5VJT';G0S8fS88Z3A1A1A2M3S6dR2R1A5S36S2L_;M4A4Ftp;Frho;S1fG2S35S5Vok;S38S5G3S54S6S82Z2M5Z1A2A2R2R1A5G4A4Ftp;Frho;S1fG2S35S5Vok;S38S5VJT';G0S98S88G5A1A1A2S54S6G5A2R2R1A5G4A4Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LPc2_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58).
  apply (X_loopP' 2 1%nat 1%nat (bd_L 2) (bd_L 3) (bd_L_cap 2) (L_P true 2) (L_P true (2 + 1)) E_fzPc2 LPc2_S1 LPc2_S2 R_fzPc2 TT_fzPc2 LPc2_U1 LPc2_U3 T_fzPc2 E_pfPc2 LPc2_P1 R_pfPc2 T_pfPc2 LPc2_Q1 LPc2_Q2 LPc2_Q4 U_pfPc2 [mkLeafA LB_Pc2 RsCut; mkLeafA LX_Pc2 RsCut] LPc2_iw
           A1 A2 A3 A4 A5 A6 A7 A8 HFZ A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A39 q Hq)) A40 A41 A42 A43 A44 (or_intror (conj (or_intror (or_introl eq_refl)) (conj eq_refl eq_refl))) A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57).
  - intros Lf Hin. destruct Hin as [<-|[<-|[]]]; [left; apply backedge_okb_sound; exact A58 | right; exact HLX].
  - exact Hnext.
Qed.

Lemma X_LPc3 : ltac2:(tb__ "0|6|
S36OF_;S4bS5Sb4VT0;VMD;U1M0A3M1R1A3SbeVAInv;VCST;VXGL;G1R2A5F_;Fok';S1fS8S45Q40A1A1M2S35S5Vok;S38S5VJT';G0S8fS88Z4A1A1A2S6eR2R1A5S36S2L_;M3A4Ftp;Frho;M4G4S1fG2S35S5Vok;S38S5VJT';G0S98S88Z3M5A1A1A2S54S6G5A2R2R1A5G3A4Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LPc3_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58).
  apply (X_loopP' 3 1%nat 1%nat (bd_L 3) (bd_L 4) (bd_L_cap 3) (L_P true 3) LX_Pc3 E_fzPc3 LPc3_S1 LPc3_S2 R_fzPc3 TT_fzPc3 LPc3_U1 LPc3_U3 T_fzPc3 E_pfPc3 LPc3_P1 R_pfPc3 T_pfPc3 LPc3_Q1 LPc3_Q2 LPc3_Q4 U_pfPc3 [mkLeafA LX_Pc3 RsCut] LPc3_iw
           A1 A2 A3 A4 A5 A6 A7 A8 HFZ A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A39 q Hq)) A40 A41 A42 A43 A44 (or_intror (conj (or_intror (or_intror eq_refl)) (conj eq_refl eq_refl))) A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57).
  - intros Lf Hin. destruct Hin as [<-|[]]. right; exact HLX.
  - exact Hnext.
Qed.

Lemma X_LE10 : ltac2:(tb__ "0|6|
S36OF_;S4bS5Sb4VT0;VMD;U0M0A3M1R1A3SbeVAInv;VCST;VXGL;G1R2A5F_;Fok';S1fS8S45Q40A1A1M2S35S5Vok;S38S5VJT';U1S8eS89Z1A1A1A2S65R2R1A5S36S2L_;M3A4Ftp;Frho;M4G4S1fG2S35S5Vok;S38S5VJT';G0S93S89Z0M5A1A1A2S55S11G5A2R2R1A5G3A4Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LE10_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58 & A59 & A60 & A61 & A62 & A63).
  apply (X_loopE' 0 0%nat 1%nat (bd_E 0) (bd_E 1) (bd_E_cap 0) (L_E false 0) LX_E10 E_fzE10 LE10_S1 LE10_S2 LE10_S3 R_fzE10 TT_fzE10 LE10_U1 LE10_U3 LE10_U4 T_fzE10 (SLit EMPTY) DUnknown E_pfE10 LE10_P1 R_pfE10 T_pfE10 LE10_Q1 LE10_Q2 LE10_Q4 U_pfE10 [mkLeafA LX_E10 RsCut] LE10_iw
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 HFZ A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A44 q Hq)) A45 A46 A47 A48 A49 (or_introl (conj eq_refl (conj eq_refl eq_refl))) A50 A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A61 A62).
  - intros Lf Hin. destruct Hin as [<-|[]]. right; exact HLX.
  - exact Hnext.
Qed.

Lemma X_LEc0 : ltac2:(tb__ "0|7|
S36OF_;S4bS5Sb4VT0;VMD;U0M0A3M1R1A3SbeVAInv;VCST;VXGL;G1R2A5F_;Fok';S1fS8S45Q40A1A1M2S35S5Vok;S38S5VJT';U1S8eS89Z1M3A1A1A2M4S66R2R1A5S36S2L_;M5A4Ftp;Frho;S1fG2S35S5Vok;S38S5G4S55S6S82Z0M6G3A2A2R2R1A5G5A4Ftp;Frho;S1fG2S35S5Vok;S38S5VJT';G0S93S89G6A1A1A2S55S6G6A2R2R1A5G5A4Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LEc0_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58 & A59 & A60 & A61 & A62 & A63).
  apply (X_loopE' 0 0%nat 1%nat (bd_E 0) (bd_E 1) (bd_E_cap 0) (L_E true 0) (L_E true (0 + 1)) E_fzEc0 LEc0_S1 LEc0_S2 LEc0_S3 R_fzEc0 TT_fzEc0 LEc0_U1 LEc0_U3 LEc0_U4 T_fzEc0 (SLit EMPTY) DUnknown E_pfEc0 LEc0_P1 R_pfEc0 T_pfEc0 LEc0_Q1 LEc0_Q2 LEc0_Q4 U_pfEc0 [mkLeafA LB_Ec0 RsCut; mkLeafA LX_Ec0 RsCut] LEc0_iw
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 HFZ A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A44 q Hq)) A45 A46 A47 A48 A49 (or_introl (conj eq_refl (conj eq_refl eq_refl))) A50 A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A61 A62).
  - intros Lf Hin. destruct Hin as [<-|[<-|[]]]; [left; apply backedge_okb_sound; exact A63 | right; exact HLX].
  - exact Hnext.
Qed.

Lemma X_LEc1 : ltac2:(tb__ "0|6|
S36OF_;S4bS5Sb4VT0;VMD;U1M0A3M1R1A3SbeVAInv;VCST;VXGL;G1R2A5F_;Fok';S1fS8S45Q40A1A1M2S35S5Vok;S38S5VJT';G0S8eS89Z2A1A1A2M3S67R2R1A5S36S2L_;M4A4Ftp;Frho;S1fG2S35S5Vok;S38S5G3S55S6S82Z1M5G5A2A2R2R1A5G4A4Ftp;Frho;S1fG2S35S5Vok;S38S5VJT';G0S93S89G5A1A1A2S55S6G5A2R2R1A5G4A4Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LEc1_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58 & A59 & A60 & A61 & A62 & A63).
  apply (X_loopE' 1 1%nat 1%nat (bd_E 1) (bd_E 2) (bd_E_cap 1) (L_E true 1) (L_E true (1 + 1)) E_fzEc1 LEc1_S1 LEc1_S2 LEc1_S3 R_fzEc1 TT_fzEc1 LEc1_U1 LEc1_U3 LEc1_U4 T_fzEc1 (SLit EMPTY) DUnknown E_pfEc1 LEc1_P1 R_pfEc1 T_pfEc1 LEc1_Q1 LEc1_Q2 LEc1_Q4 U_pfEc1 [mkLeafA LB_Ec1 RsCut; mkLeafA LX_Ec1 RsCut] LEc1_iw
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 HFZ A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A44 q Hq)) A45 A46 A47 A48 A49 (or_intror (conj (or_introl eq_refl) (conj eq_refl eq_refl))) A50 A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A61 A62).
  - intros Lf Hin. destruct Hin as [<-|[<-|[]]]; [left; apply backedge_okb_sound; exact A63 | right; exact HLX].
  - exact Hnext.
Qed.

Lemma X_LEc2 : ltac2:(tb__ "0|6|
S36OF_;S4bS5Sb4VT0;VMD;U1M0A3M1R1A3SbeVAInv;VCST;VXGL;G1R2A5F_;Fok';S1fS8S45Q40A1A1M2S35S5Vok;S38S5VJT';G0S8eS89Z3A1A1A2M3S68R2R1A5S36S2L_;M4A4Ftp;Frho;S1fG2S35S5Vok;S38S5G3S55S6S82Z2M5Z1A2A2R2R1A5G4A4Ftp;Frho;S1fG2S35S5Vok;S38S5VJT';G0S93S89G5A1A1A2S55S6G5A2R2R1A5G4A4Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LEc2_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58 & A59 & A60 & A61 & A62 & A63).
  apply (X_loopE' 2 1%nat 1%nat (bd_E 2) (bd_E 3) (bd_E_cap 2) (L_E true 2) (L_E true (2 + 1)) E_fzEc2 LEc2_S1 LEc2_S2 LEc2_S3 R_fzEc2 TT_fzEc2 LEc2_U1 LEc2_U3 LEc2_U4 T_fzEc2 (SLit EMPTY) DUnknown E_pfEc2 LEc2_P1 R_pfEc2 T_pfEc2 LEc2_Q1 LEc2_Q2 LEc2_Q4 U_pfEc2 [mkLeafA LB_Ec2 RsCut; mkLeafA LX_Ec2 RsCut] LEc2_iw
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 HFZ A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A44 q Hq)) A45 A46 A47 A48 A49 (or_intror (conj (or_intror (or_introl eq_refl)) (conj eq_refl eq_refl))) A50 A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A61 A62).
  - intros Lf Hin. destruct Hin as [<-|[<-|[]]]; [left; apply backedge_okb_sound; exact A63 | right; exact HLX].
  - exact Hnext.
Qed.

Lemma X_LEc3 : ltac2:(tb__ "0|6|
S36OF_;S4bS5Sb4VT0;VMD;U1M0A3M1R1A3SbeVAInv;VCST;VXGL;G1R2A5F_;Fok';S1fS8S45Q40A1A1M2S35S5Vok;S38S5VJT';G0S8eS89Z4A1A1A2S69R2R1A5S36S2L_;M3A4Ftp;Frho;M4G4S1fG2S35S5Vok;S38S5VJT';G0S93S89Z3M5A1A1A2S55S6G5A2R2R1A5G3A4Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LEc3_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58 & A59 & A60 & A61 & A62 & A63).
  apply (X_loopE' 3 1%nat 1%nat (bd_E 3) (bd_E 4) (bd_E_cap 3) (L_E true 3) LX_Ec3 E_fzEc3 LEc3_S1 LEc3_S2 LEc3_S3 R_fzEc3 TT_fzEc3 LEc3_U1 LEc3_U3 LEc3_U4 T_fzEc3 (SLit EMPTY) DUnknown E_pfEc3 LEc3_P1 R_pfEc3 T_pfEc3 LEc3_Q1 LEc3_Q2 LEc3_Q4 U_pfEc3 [mkLeafA LX_Ec3 RsCut] LEc3_iw
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 HFZ A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A44 q Hq)) A45 A46 A47 A48 A49 (or_intror (conj (or_intror (or_intror eq_refl)) (conj eq_refl eq_refl))) A50 A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A61 A62).
  - intros Lf Hin. destruct Hin as [<-|[]]. right; exact HLX.
  - exact Hnext.
Qed.

Lemma X_XP10 : ltac2:(tb__ "0|6|
S0S48Sc8VF;A1S82Z0M0Z1M1A2M2A3S1fS8S45Q40A1A1M3S35S5Vok;S38S5VJT';U1M4S95S8aA1A2S52G2S25G0A1A2R2R1A5S36S2L_;M5A4Ftp;Frho;F_;S1fG3S35S5Vok;S38S5VJT';G4S99S88G1A1A1A2S6aR2R1A5G5A4Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XP10_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  apply (X_freeP' 1%nat (0 + 1) (bd_L 1) bd_J LX_P10 R_fp_P10 T_fp_P10 [mkLeafA LJa_P10 RsCut; mkLeafA LJb_P10 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14
           (fun Lf Hin => backedge_okb_sound (J_E (0 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A15 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 0 + 1) (fun rho HF HP0 Hav => exit1_sound rhoT F rho _ HF A16 HP0 Hav) HJ).
Qed.

Lemma X_XPc0 : ltac2:(tb__ "0|6|
S0S48Sc8VF;A1S82Z0M0Z1M1A2M2A3S1fS8S45Q40A1A1M3S35S5Vok;S38S5VJT';U1M4S95S8aA1A2S52G2S25G0A1A2R2R1A5S36S2L_;M5A4Ftp;Frho;F_;S1fG3S35S5Vok;S38S5VJT';G4S99S88G1A1A1A2S6bR2R1A5G5A4Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XPc0_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  apply (X_freeP' 1%nat (0 + 1) (bd_L 1) bd_J LX_Pc0 R_fp_Pc0 T_fp_Pc0 [mkLeafA LJa_Pc0 RsCut; mkLeafA LJb_Pc0 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14
           (fun Lf Hin => backedge_okb_sound (J_E (0 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A15 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 0 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 0 rho _ ltac:(lia) HF A16 HP0 Hav) HJ).
Qed.

Lemma X_XPc1 : ltac2:(tb__ "0|5|
S0S48Sc8VF;A1S82Z1M0G0A2M1A3S1fS8S45Q40A1A1M2S35S5Vok;S38S5VJT';U1M3S95S8aA1A2S52G1S25Z0A1A2R2R1A5S36S2L_;M4A4Ftp;Frho;F_;S1fG2S35S5Vok;S38S5VJT';G3S99S88Z2A1A1A2S6cR2R1A5G4A4Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XPc1_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  apply (X_freeP' 1%nat (1 + 1) (bd_L 2) bd_J LX_Pc1 R_fp_Pc1 T_fp_Pc1 [mkLeafA LJa_Pc1 RsCut; mkLeafA LJb_Pc1 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14
           (fun Lf Hin => backedge_okb_sound (J_E (1 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A15 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 1 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 1 rho _ ltac:(lia) HF A16 HP0 Hav) HJ).
Qed.

Lemma X_XPc2 : ltac2:(tb__ "0|4|
S0S48Sc8VF;A1S82Z2Z1A2M0A3S1fS8S45Q40A1A1M1S35S5Vok;S38S5VJT';U1M2S95S8aA1A2S52G0S25Z0A1A2R2R1A5S36S2L_;M3A4Ftp;Frho;F_;S1fG1S35S5Vok;S38S5VJT';G2S99S88Z3A1A1A2S6dR2R1A5G3A4Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XPc2_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  apply (X_freeP' 1%nat (2 + 1) (bd_L 3) bd_J LX_Pc2 R_fp_Pc2 T_fp_Pc2 [mkLeafA LJa_Pc2 RsCut; mkLeafA LJb_Pc2 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14
           (fun Lf Hin => backedge_okb_sound (J_E (2 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A15 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 2 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 2 rho _ ltac:(lia) HF A16 HP0 Hav) HJ).
Qed.

Lemma X_XPc3 : ltac2:(tb__ "0|4|
S0S48Sc8VF;A1S82Z3Z1A2M0A3S1fS8S45Q40A1A1M1S35S5Vok;S38S5VJT';U1M2S95S8aA1A2S52G0S25Z0A1A2R2R1A5S36S2L_;M3A4Ftp;Frho;F_;S1fG1S35S5Vok;S38S5VJT';G2S99S88Z4A1A1A2S6eR2R1A5G3A4Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XPc3_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  apply (X_freeP' 1%nat (3 + 1) (bd_L 4) bd_J LX_Pc3 R_fp_Pc3 T_fp_Pc3 [mkLeafA LJa_Pc3 RsCut; mkLeafA LJb_Pc3 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14
           (fun Lf Hin => backedge_okb_sound (J_E (3 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A15 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 3 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 3 rho _ ltac:(lia) HF A16 HP0 Hav) HJ).
Qed.

Lemma X_XE10 : ltac2:(tb__ "0|6|
S0S48Sc8VF;A1S82Z0M0Z1M1A2M2A3S1fS8S45Q40A1A1M3S35S5Vok;S38S5VJT';U1M4S94S8aA1A2S52G2S25G0A1A2R2R1A5S36S2L_;M5A4Ftp;Frho;F_;S1fG3S35S5Vok;S38S5VJT';G4S97S89G1A1A1A2S65R2R1A5G5A4Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XE10_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  apply (X_freeE' 1%nat (0 + 1) (bd_E 1) bd_J LX_E10 R_fn_E10 T_fn_E10 [mkLeafA LJEa_E10 RsCut; mkLeafA LJEb_E10 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
           (fun Lf Hin => backedge_okb_sound (J_E (0 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A13 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 0 + 1) (fun rho HF HP0 Hav => exit1_sound rhoT F rho _ HF A14 HP0 Hav) HJ).
Qed.

Lemma X_XEc0 : ltac2:(tb__ "0|6|
S0S48Sc8VF;A1S82Z0M0Z1M1A2M2A3S1fS8S45Q40A1A1M3S35S5Vok;S38S5VJT';U1M4S94S8aA1A2S52G2S25G0A1A2R2R1A5S36S2L_;M5A4Ftp;Frho;F_;S1fG3S35S5Vok;S38S5VJT';G4S97S89G1A1A1A2S66R2R1A5G5A4Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XEc0_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  apply (X_freeE' 1%nat (0 + 1) (bd_E 1) bd_J LX_Ec0 R_fn_Ec0 T_fn_Ec0 [mkLeafA LJEa_Ec0 RsCut; mkLeafA LJEb_Ec0 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
           (fun Lf Hin => backedge_okb_sound (J_E (0 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A13 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 0 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 0 rho _ ltac:(lia) HF A14 HP0 Hav) HJ).
Qed.

Lemma X_XEc1 : ltac2:(tb__ "0|5|
S0S48Sc8VF;A1S82Z1M0G0A2M1A3S1fS8S45Q40A1A1M2S35S5Vok;S38S5VJT';U1M3S94S8aA1A2S52G1S25Z0A1A2R2R1A5S36S2L_;M4A4Ftp;Frho;F_;S1fG2S35S5Vok;S38S5VJT';G3S97S89Z2A1A1A2S67R2R1A5G4A4Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XEc1_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  apply (X_freeE' 1%nat (1 + 1) (bd_E 2) bd_J LX_Ec1 R_fn_Ec1 T_fn_Ec1 [mkLeafA LJEa_Ec1 RsCut; mkLeafA LJEb_Ec1 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
           (fun Lf Hin => backedge_okb_sound (J_E (1 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A13 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 1 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 1 rho _ ltac:(lia) HF A14 HP0 Hav) HJ).
Qed.

Lemma X_XEc2 : ltac2:(tb__ "0|4|
S0S48Sc8VF;A1S82Z2Z1A2M0A3S1fS8S45Q40A1A1M1S35S5Vok;S38S5VJT';U1M2S94S8aA1A2S52G0S25Z0A1A2R2R1A5S36S2L_;M3A4Ftp;Frho;F_;S1fG1S35S5Vok;S38S5VJT';G2S97S89Z3A1A1A2S68R2R1A5G3A4Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XEc2_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  apply (X_freeE' 1%nat (2 + 1) (bd_E 3) bd_J LX_Ec2 R_fn_Ec2 T_fn_Ec2 [mkLeafA LJEa_Ec2 RsCut; mkLeafA LJEb_Ec2 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
           (fun Lf Hin => backedge_okb_sound (J_E (2 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A13 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 2 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 2 rho _ ltac:(lia) HF A14 HP0 Hav) HJ).
Qed.

Lemma X_XEc3 : ltac2:(tb__ "0|4|
S0S48Sc8VF;A1S82Z3Z1A2M0A3S1fS8S45Q40A1A1M1S35S5Vok;S38S5VJT';U1M2S94S8aA1A2S52G0S25Z0A1A2R2R1A5S36S2L_;M3A4Ftp;Frho;F_;S1fG1S35S5Vok;S38S5VJT';G2S97S89Z4A1A1A2S69R2R1A5G3A4Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XEc3_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  apply (X_freeE' 1%nat (3 + 1) (bd_E 4) bd_J LX_Ec3 R_fn_Ec3 T_fn_Ec3 [mkLeafA LJEa_Ec3 RsCut; mkLeafA LJEb_Ec3 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
           (fun Lf Hin => backedge_okb_sound (J_E (3 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A13 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 3 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 3 rho _ ltac:(lia) HF A14 HP0 Hav) HJ).
Qed.

Lemma X_MC1 : ltac2:(tb__ "0|4|
S1fS8S45Q40A1A1M0S35S5Vok;S38S5VJT';U0S8bS88Z0M1A1A1A2M2S54S11G1A2R2R1A5S36S2L_;M3A4Ftp;Frho;S1fG0S35S5Vok;S38S5G2S73R2R1A5G3A4Ftp;Frho;F_;").
Proof.
  intros Hnext. pose proof MC1_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37).
  exact (X_mc' (bd_L 0) T_mok1 E_mc1 MC1_W1 MC1_W2 MC1_B1 MC1_B2 MC1_B3 MC1_RS MC1_i0 MC1_i1 MC1_i2 R_mc1 T_mc1
           MC1_V1 MC1_V2 MC1_V3 MC1_V4 MC1_V5 MC1_V6 MC1_V7 MC1_V8 MC1_V9 MC1_V10 MC1_V11 U_mc1 L_P1 MC1_s (L_P false 0)
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 Hnext).
Qed.

Lemma X_MCc : ltac2:(tb__ "0|4|
S1fS8S45Q40A1A1M0S35S5Vok;S38S5VJT';U0S8bS88Z0M1A1A1A2M2S54S6G1A2R2R1A5S36S2L_;M3A4Ftp;Frho;S1fG0S35S5Vok;S38S5G2S74R2R1A5G3A4Ftp;Frho;F_;").
Proof.
  intros Hnext. pose proof MCc_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37).
  exact (X_mc' (bd_L 0) T_mokc E_mcc MCc_W1 MCc_W2 MCc_B1 MCc_B2 MCc_B3 MCc_RS MCc_i0 MCc_i1 MCc_i2 R_mcc T_mcc
           MCc_V1 MCc_V2 MCc_V3 MCc_V4 MCc_V5 MCc_V6 MCc_V7 MCc_V8 MCc_V9 MCc_V10 MCc_V11 U_mcc L_Pc MCc_s (L_P true 0)
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 Hnext).
Qed.

Lemma X_J10 : ltac2:(tb__ "0|5|
S3cVMD;R1A1VSpec;SaS3bSaS3bVT0;S91U1M0A1A3SaS3bSbaS45Q8A1S3bS3eSd9A1SeaZ1M1A1A4SdS3bS3dS46Q40M2Z0M3A2S3fR2A1A2ScS3bA1A3A3A3A1F_;Fmd;S1fS8S45G2A1A1S35S5Vok;S38S5VJT';G0S4dSdSeS20S20A2M4S12S20S20Sc9ScaA4ScG4A1A3ScSeSeS20S48A2S20A2A1S8aS4cA4A2S52G1S25G3A1A2R2R1A5S36S2L_;A4Ftp;Frho;F_;").
Proof.
  intros HS. destruct J10_facts as [A1 A2].
  apply (X_join' 1%nat bd_J [] 1 (SLit 0) 0 Ex_J10 Rx_J10 A1 A2 ltac:(cbn; tauto) HS).
Qed.

Lemma X_J20 : ltac2:(tb__ "0|5|
S3cVMD;R1A1VSpec;SaS3bSaS3bVT0;S91U1M0A1A3SaS3bSbaS45Q8A1S3bS3eSd9A1SeaZ2M1A1A4SdS3bS3dS46Q40M2Z0M3A2S3fR2A1A2ScS3bA1A3A3A3A1F_;Fmd;S1fS8S45G2A1A1S35S5Vok;S38S5VJT';G0S4dSdSeS20S20A2M4S12S20S20Sc9ScaA4ScG4A1A3ScSeSeS20S48A2S20A2A1S8aS4cA4A2S52G1S25G3A1A2R2R1A5S36S2L_;A4Ftp;Frho;F_;").
Proof.
  intros HS. destruct J20_facts as [A1 A2].
  apply (X_join' 1%nat bd_J [] 2 (SLit 0) 0 Ex_J20 Rx_J20 A1 A2 ltac:(cbn; tauto) HS).
Qed.

Lemma X_J30 : ltac2:(tb__ "0|5|
S3cVMD;R1A1VSpec;SaS3bSaS3bVT0;S91U1M0A1A3SaS3bSbaS45Q8A1S3bS3eSd9A1SeaZ3M1A1A4SdS3bS3dS46Q40M2Z0M3A2S3fR2A1A2ScS3bA1A3A3A3A1F_;Fmd;S1fS8S45G2A1A1S35S5Vok;S38S5VJT';G0S4dSdSeS20S20A2M4S12S20S20Sc9ScaA4ScG4A1A3ScSeSeS20S48A2S20A2A1S8aS4cA4A2S52G1S25G3A1A2R2R1A5S36S2L_;A4Ftp;Frho;F_;").
Proof.
  intros HS. destruct J30_facts as [A1 A2].
  apply (X_join' 1%nat bd_J [] 3 (SLit 0) 0 Ex_J30 Rx_J30 A1 A2 ltac:(cbn; tauto) HS).
Qed.

Lemma X_J40 : ltac2:(tb__ "0|5|
S3cVMD;R1A1VSpec;SaS3bSaS3bVT0;S91U1M0A1A3SaS3bSbaS45Q8A1S3bS3eSd9A1SeaZ4M1A1A4SdS3bS3dS46Q40M2Z0M3A2S3fR2A1A2ScS3bA1A3A3A3A1F_;Fmd;S1fS8S45G2A1A1S35S5Vok;S38S5VJT';G0S4dSdSeS20S20A2M4S12S20S20Sc9ScaA4ScG4A1A3ScSeSeS20S48A2S20A2A1S8aS4cA4A2S52G1S25G3A1A2R2R1A5S36S2L_;A4Ftp;Frho;F_;").
Proof.
  intros HS. destruct J40_facts as [A1 A2].
  apply (X_join' 1%nat bd_J [] 4 (SLit 0) 0 Ex_J40 Rx_J40 A1 A2 ltac:(cbn; tauto) HS).
Qed.

Lemma X_J02 : ltac2:(tb__ "0|5|
S3cVMD;R1A1VSpec;SaS3bSaS3bVT0;S91U0M0A1A3SaS3bSbaS45Q8A1S3bS3eSd9A1SeaZ0M1A1A4SdS3bS3dS46Q40M2Z2M3A2S3fR2A1A2ScS3bA1A3A3A3A1F_;Fmd;S1fS8S45G2A1A1S35S5Vok;S38S5VJT';G0S4dSdSeS20S20A2M4S12S20S20Sc9ScaA4ScG4A1A3ScSeSeS20S48A2S20A2A1S8aS4cA4A2S52G1S25G3A1A2R2R1A5S36S2L_;A4Ftp;Frho;F_;").
Proof.
  intros HS. destruct J02_facts as [A1 A2].
  apply (X_join' 0%nat bd_J [] 0 (SLit 2) 2 Ex_J02 Rx_J02 A1 A2 ltac:(cbn; tauto) HS).
Qed.

Lemma X_J00 : ltac2:(tb__ "0|4|
S3cVMD;R1A1VSpec;SaS3bSaS3bVT0;S91U0M0A1A3SaS3bSbaS45Q8A1S3bS3eSd9A1SeaZ0M1A1A4SdS3bS3dS46Q40M2G1A2S3fR2A1A2ScS3bA1A3A3A3A1F_;Fmd;S1fS8S45G2A1A1S35S5Vok;S38S5VJT';G0S4dSdSeS20S20A2M3S12S20S20Sc9ScaA4ScG3A1A3ScSeSeS20S48A2S20A2A1S8aS4cA4A2S52G1S25G1A1A2R2R1A5S36S2L_;A4Ftp;Frho;F_;").
Proof.
  intros HS. destruct J00_facts as [A1 A2].
  apply (X_join' 0%nat bd_J [] 0 (SLit 0) 0 Ex_J00 Rx_J00 A1 A2 ltac:(cbn; tauto) HS).
Qed.

Lemma X_MS1 : ltac2:(tb__ "0|3|
S1fS8S45Q40A1A1M0S35S5Vok;S38S5VJT';U0M1S8bS9eA1A2S73R2R1A5S36S2L_;M2A4Ftp;Frho;S1fG0S35S5Vok;S38S5VJT';G1ScbA2S76R2R1A5G2A4Ftp;Frho;F_;").
Proof.
  intros HMC. pose proof MS1_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  exact (X_msite' E_mP1 R_mP1 T_mok1 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A15 HMC).
Qed.

Lemma X_MSc : ltac2:(tb__ "0|3|
S1fS8S45Q40A1A1M0S35S5Vok;S38S5VJT';U0M1S8bS9eA1A2S74R2R1A5S36S2L_;M2A4Ftp;Frho;S1fG0S35S5Vok;S38S5VJT';G1ScbA2S77R2R1A5G2A4Ftp;Frho;F_;").
Proof.
  intros HMC. pose proof MSc_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  exact (X_msite' E_mPc R_mPc T_mokc A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A15 HMC).
Qed.

Theorem tlx_safe : ltac2:(tb__ "0|6|
S36OF_;M0S4bS5Sb4VT0;VMD;U0M1A3M2R1A3SbeVAInv;VCST;VXGL;G2R2A5F_;Fok';G0S4bS5Sb4VT0;VMD;U1M3A3M4R1A3SbeVAInv;VCST;VXGL;G4R2A5F_;Fok';S3cVMD;R1A1VSpec;SaS3bSaS3bVT0;S91G3A1A3SaS3bSbaS45Q8A1S3bS3eSd9A1SeaSc8VF;A1A1A4SdS3bS3dS46Q40M5Z0A2S3fR2A1A2ScS3bA1A3A3A3A1F_;Fmd;S1fS8S45G5A1A1S35S5Vok;S38S5VJT';G1ScbA2SccR2R1A5S36S2L_;A4Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ0 HFZ1 HSok.
  destruct T0_facts as (A1 & A1' & A2 & A3 & A4 & A5).

  assert (XJ : forall n, calls_of F = n ->
     (n = 1 \/ n = 2 \/ n = 3 \/ n = 4) ->
     forall rho tp, triple segs ok (SPA segs (JT' 1%nat (NDA [(vB, vCap)] [] bd_J ANone)) (J_E n (SLit 0)) rho tp) (fun _ => False)).
  { intros n Hn Hc. rewrite Hn in HSok.
    destruct Hc as [->|[->|[->| ->]]]; [apply (X_J10 HSok) | apply (X_J20 HSok) | apply (X_J30 HSok) | apply (X_J40 HSok)]. }
  assert (J1 : calls_of F = 0 + 1 -> forall rho tp, triple segs ok (SPA segs (JT' 1%nat (ndJX bd_J)) (J_E (0 + 1) (SLit 0)) rho tp) (fun _ => False))
    by (intros Hn; apply (XJ 1 Hn); tauto).
  assert (J2 : calls_of F = 1 + 1 -> forall rho tp, triple segs ok (SPA segs (JT' 1%nat (ndJX bd_J)) (J_E (1 + 1) (SLit 0)) rho tp) (fun _ => False))
    by (intros Hn; apply (XJ 2 Hn); tauto).
  assert (J3 : calls_of F = 2 + 1 -> forall rho tp, triple segs ok (SPA segs (JT' 1%nat (ndJX bd_J)) (J_E (2 + 1) (SLit 0)) rho tp) (fun _ => False))
    by (intros Hn; apply (XJ 3 Hn); tauto).
  assert (J4 : calls_of F = 3 + 1 -> forall rho tp, triple segs ok (SPA segs (JT' 1%nat (ndJX bd_J)) (J_E (3 + 1) (SLit 0)) rho tp) (fun _ => False))
    by (intros Hn; apply (XJ 4 Hn); tauto).

  pose proof (X_LPc3 HFZ1 (X_XPc3 J4) (X_XPc3 J4)) as LPc3.
  pose proof (X_LPc2 HFZ1 (X_XPc2 J3) LPc3) as LPc2.
  pose proof (X_LPc1 HFZ1 (X_XPc1 J2) LPc2) as LPc1.
  pose proof (X_LPc0 HFZ0 (X_XPc0 J1) LPc1) as LPc0.
  pose proof (X_LP10 HFZ0 (X_XP10 J1) (X_XP10 J1)) as LP10.

  pose proof (X_LEc3 HFZ1 (X_XEc3 J4) (X_XEc3 J4)) as LEc3.
  pose proof (X_LEc2 HFZ1 (X_XEc2 J3) LEc3) as LEc2.
  pose proof (X_LEc1 HFZ1 (X_XEc1 J2) LEc2) as LEc1.
  pose proof (X_LEc0 HFZ0 (X_XEc0 J1) LEc1) as LEc0.
  pose proof (X_LE10 HFZ0 (X_XE10 J1) (X_XE10 J1)) as LE10.

  pose proof (X_MS1 (X_MC1 LP10)) as MS1.
  pose proof (X_MSc (X_MCc LPc0)) as MSc.
  exact (X_T0' (ax_S S_T1) (ax_S S_T2) E_mP1 L_E1 L_Ec E_mPc A1 A1' A2 A3 MS1 MSc (L_E false 0) (L_E true 0) A4 A5 LE10 LEc0).
Qed.

End TLXI.
End DrvTLXi.

