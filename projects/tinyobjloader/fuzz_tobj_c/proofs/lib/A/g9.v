(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g8.

(* [comment removed for export] *)
Module DrvTLXe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "False"; "True"; "not"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "nil"; "nat"; "prod"; "option"; "Some"; "cons"; "app"; "length"; "pair"; "false"; "None"; "orb"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_next"; "ss_facts"; "sstate"; "valuation"; "ss_objs"; "SLit"; "sprop"; "ss_lenient"; "SVar"; "sprop_below"; "holds"; "cell"; "mkObj"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "DUnknown"; "SPUle"; "sprop_eqb"; "agree_below"; "rm"; "obj_wf"; "rw"; "sv_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "ax_X"; "ax_base"; "la_state"; "sym_runA"; "mkAX"; "mkLeafA"; "entailsA"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "smatchA"; "stableA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "ExitEv"; "FdEntry"; "WriteEv"; "m_fs"; "FdChannel"; "fd_lookup"; "m_fds"; "VmState"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "ndesc"; "ANone"; "NDA"; "PTrue"; "nd_tv"; "nd_am"; "JAi"; "nd_bd"; "nd_fr"; "tvinA"; "JA"; "am_eqb"; "am_subst"; "amode"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "w_tr"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g9.DrvTLXe.TLXE.LoopE"; "CfzE"; "CpfE"; "keptE"; "ndE1"; "Cpf0E"; "P1cE"; "ndE0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g9.DrvTLXe.TLXE.LoopP"; "Cfz"; "Cpf"; "kept"; "ndL1"; "Cpf0"; "P1c"; "ndL0"; "@Corelib.Lists.ListDef"; "map"; "seq"; "Forall"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states"; "s_fz"; "vP"; "CUTS_L"; "FUEL_L"; "J_E"; "PreP"; "pf_hints"; "s_m"; "s_pf"; "s_fp"; "O_WloT"; "PreM"; "pf_u1"; "s_fn"; "CUTS_T"; "PreFN"; "s_mc"; "O_WfzT"; "O_payE"; "O_srcT"; "PostFN"; "WDP"; "X_payE"; "FUEL_T0"; "FUEL_T1"; "FUEL_T2"; "O_cstkB"; "mc_hints"; "sel_buf"; "sel_rtc_last"; "sel_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g9.DrvTLXe.TLXE.ExitFreeP"; "CP"; "keptX"; "ndJX"; "ndLX"; "@Stdlib.Lists.List"; "forallb"; "In"; "nth_error"; "existsb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "vB"; "vCap"; "vPlen"; "nd_T"; "S_T"; "tv_T"; "PreF"; "bd_T"; "sp0"; "CUTS_X"; "FUEL_X"; "PostF"; "dropX"; "clen_of"; "facts_T"; "locate"; "vClen"; "vLen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "sp0_factsb"; "drv_xrb"; "kept_nzb"; "robjs_checkD"; "xrs_checkD"; "drv_objb"; "ex_pipe"; "fb_pipe"; "site_ok_drv"; "xrs_okF_drv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "KV_T"; "BX0"; "KP_T"; "HKVrng_T"; "JT"; "P0T"; "CST_drv"; "HCSTKV_T"; "HKP_T"; "HKV_T"; "JT_tv_band_free"; "JTi"; "SH0";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "lcarve"; "lc_obj"; "JAK"; "carve_okb"; "uncarve_okb"; "JA_carve"; "JA_uncarve"; "pure_callJ_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g9.DrvTLXe.TLXE.SegMC"; "B3h"; "Cmc"; "ndM"; "B3c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_get"; "wsub_id_below"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_postA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX"; "N_pf"; "EVk"; "N_mc"; "bd_E"; "bd_M"; "edge_okb"; "O_srcM"; "mc_needb"; "ms16_shape"; "plen_factsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "Pre_fz"; "bd_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_subst"; "bud_le"; "bd_below"; "bud_pay"; "bitem"; "bsumV"; "KU"; "LARGE_MIN"; "SECCAP"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "xr_tracked"; "site_okA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "opp"; "add"; "sub"; "of_nat"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit"; "ch1"; "supported"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "AE_A"; "L_malloc_ok"; "UStopLe"; "ulink"; "Kc_ok"; "V_RES"; "alloc_contractsA_ex"; "band_free"; "with_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "robj_tracked"; "tnz"; "tvz"; "T0"; "tvd"; "tvv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "acell"; "cells_ok"; "mkACell"; "view"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "PEND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g9.DrvTLXe.TLXE"; "kept"; "ndE0"; "ndM"; "plen0_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2"; "P_fz"; "PD_fz"; "fuzz_one_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "wsub_dom_below"; "pos_add_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g9.DrvTLXe.TLXE.ExitFreeE"; "ndJE"; "ndEX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "Pre_mc0"; "P_icpt"; "Posts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TR_INIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.PFAddr"; "PW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "P_pf"; "Posts_pf"; "kok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.FZAddr";
"fz_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pd_okA"; "pdescA"; "xrs_inclb"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC"; "add_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS"; "malloc_contractA_strong_ex"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceS GlueM IfaceEx.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvSiteEx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvBox.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Section TLXE.
Variable AInv : ltac2:(tb__ "0|0|
S11bS1dS9S45Q40A1A1S4eOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S42S123VCST;R1A2S1S105Z0R2A2S106R2S136A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S42S123VXGL;R1A2S1S105Z0R2A2S106R2S136A2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S42S123ScaR1A2S123VCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Hypothesis ACX : ltac2:(tb__ "0|0|
S118S41S112VAInv;VCST;VXGL;A5").
Hypothesis MSX : ltac2:(tb__ "0|0|
S14dS41S112VAInv;VCST;VXGL;A5").

Variable Q : world -> Prop.

Variable rhoT : valuation.
Variable F : list byte.
Variable T0 : list event.
Variable MD : Model -> Prop.
Hypothesis HMDvm : ltac2:(tb__ "0|0|
S4eS56VMD;R2A1VMD;S11aR2R3A2A1F_;Fv;Fmd;").
Hypothesis HMDfd1 : ltac2:(tb__ "0|0|
S4eVMD;R1A1S0SdS50A1S54S55R2A1S10dA2SeS50S53S10dA1A2A3F_;Fmd;").

Let KcT := KcT T0 MD.
Let P0T := P0T F.
Let JT (k : nat) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
Sc8VAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;S5bVk;Vnd;Aa").
Let JTi (k : nat) (nd : ndesc) (Ai : AA) (kc : Z) : jpredA := ltac2:(tb__ "0|0|
ScfVAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;S5bVk;Vnd;VAi;Vkc;Ac").

Let HKV : ltac2:(tb__ "0|1|
S111S58S11bS42S1dS9S45Q40A1A1S9S4dA1S4eS5eVAInv;VCST;VXGL;S44R8VrhoT;Sc9VF;A1SaScS42S42A2M0A1SaScG0S42A2A1Sc5S5bR7R6R5R4R3R2R1A12S125S127S41S31R5A1A2Sc4A2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc;") := ltac2:(tb__ "0|0|
ScdVAInv;VCST;VXGL;VALA;VHCSTdrv;VHLPP;VrhoT;VF;S5bA9").
Let HKP := HKP_T AInv CST XGL HCSTdrv rhoT F PTrue.
Let HCK := HCSTKV_T AInv CST HCSTok HLPP.
Let carveT : ltac2:(tb__ "0|3|
S111S58S38S1dS9S45Q40A1A1S68S9Sd1A1S43S48S41Sd3VAInv;VCST;VXGL;S44VrhoT;VP0T;SaScS42S42A2M0A1M1SaScG0S42A2A1M2Sc5S5bR8R7AcR6R5R4R3A6S36R7A1S1cS27S2aR1A1S2bR1A1S29R1A1S28R1A1S2cR1A1S10S19S1eR1A1S7aSd1S19Sd2R4A4A3S1bR1A1R3S21R1A1A9S1cS0S7S35R1A1S8A3S0S7S6aS1aR3A1R5A2S8A3S0S18S3aRbA1S1fS135A1A3S0S7Sd4S1bR5A1S1eR5A1S39RcA1Sc4Sc6S5cRdA1R8A7S8A3S48S41Sd3VAInv;VCST;VXGL;S44VrhoT;VP0T;G1G2Sc5S5bRfReAcS40RdR5A2RcRbRaA6F_;F_;F_;F_;TS';TS;F_;Fnx;FN;Fw;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
Sd6VAInv;VCST;VXGL;VALA;S44VrhoT;VP0T;SaScS42S42A2M0A1SaScG0S42A2A1Sc5S5bSc4VHKV;Sc7Sc6VHKP;A10").
Let uncarveT : ltac2:(tb__ "0|5|
S111S58S38S1dS9S45Q40A1A1S9S4dA1M0S128S4eS9S19A1M1S9Sd1A1S116RaA1S0G1S1eS36R9A1A1S10S19R3S7aSd1S19Sd2R2A4A3A3S0S7Sd5Sc4R3A2S8A3S0S65S5dRcA1S59A3S0S7S57S1aS36RcA1A1RdA2S8A3S48S41Sd3VAInv;VCST;VXGL;S44VrhoT;VP0T;SaScS42S42A2M2A1M3SaScG2S42A2A1M4Sc5S5bRfReAcRdRcRbS12G0S137RaS138R9R8A2A4A6S48S41Sd3VAInv;VCST;VXGL;S44VrhoT;VP0T;G3G4Sc5S5bR10RfAcS40ReSa6S36ReA1R8A2A2Se0RdS7aSd1S19Sd2R7A4S145R9RcRaA3A3RcS12G0S137RbS138RaR9A2A4A6F_;F_;F_;F_;F_;F_;FN;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
Sd7VAInv;VCST;VXGL;VALA;VHLV;S44VrhoT;VP0T;SaScS42S42A2M0A1SaScG0S42A2A1Sc5S5bSc4VHKV;Sc7VHCK;A10").
Let pcallT := pure_callJ_ex AInv CST XGL ALA NF rhoT P0T [] [] BX0 PTrue.

Let site_ok_drv := site_ok_drv AInv CST XGL ALA HCSTdrv rhoT P0T.
Let robjs_okF_drv := robjs_okF_drv CST HCSTdrv rhoT.
Let xrs_okF_drv := xrs_okF_drv CST XGL HCSTdrv rhoT.
Let kept_in_FBx := kept_in_FBx CST.
Let JT_tv_band_free : ltac2:(tb__ "0|1|
S11bOF_;SbS58S1dS9S45Q40A1A1S9S4dA1S4eScS18S18A2M0Sc8VAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;R8R7R6R5R4R3R2AeSa2G0R2S5cR7A1A3S11eR7R3A2S119S100R8S16S18S18R4A3A2S100R8S17S18S18R4A3A2A2F_;F_;F_;Ft;Fmd;Ftr;Ftp;Frho;Fnd;Fk;FPA;") := ltac2:(tb__ "0|0|
SceVAInv;VCST;VXGL;VALA;VrhoT;VF;VT0;VMD;A8").

Lemma JT_Kc : ltac2:(tb__ "0|1|
SbS58S1dS9S45Q40A1A1S9S4dA1M0S4eVJT;R6R5R4R3R2R1A6S1VMD;R2A1S0G0R3S10S4dVT0;SecR7A1A3A3A2F_;Fmd;Ftr;Ftp;Frho;Fnd;Fk;").
Proof. intros k nd rho tp tr md (Ai & kc & _ & [H1 H2] & _). split; [exact H1 | exact H2]. Qed.

Lemma JT_stable : ltac2:(tb__ "0|0|
SbS58S43S6bS44R1A2S0S7S57R2R3A2S8A3S4cS41R3VJT;R5R4A2A3F_;F_;Fn;Fnd;Fk;").
Proof. intros k nd n Hn Hb. apply (stableA_JA segs AInv CST XGL NF _ rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm k) ALA n nd Hn Hb). Qed.

Lemma JT_erun : ltac2:(tb__ "0|1|
SbS58SbS9S42A1S38S9S37A1M0S1dS9S45Q40A1A1S68OF_;S0SdG0A1S3cS41R7R6R5S8A5SeG0R4A2A3S0S7S21S36R6A1A1S13A3S0S7S6aS44S1aS36R7A1A1A2S8A3S0S7S57S1aS36R8A1A1RbA2S8A3S37S1dSa2S37R2RaA3S30S1aS36RcA1A1RaR2A3S67S41S48S41VJT;R11R10A2S3bR4A1R3RaA5R9A3F_;F_;Frho';FL;S67S41S48S41VJT;ReRdA2RaR8R7A5R6A3F_;F_;F_;F_;F_;FQ';Ftp;Frho;Fleaves;FA;Fcuts;Ffuel;Fnd;Fk;").
Proof.
  intros k nd fuel cuts A leaves rho tp Q' Hrun Hlen Hnf Hnb H. apply Pos.leb_le in Hnf.
  exact (erunA_tr segs fuel cuts A leaves (JT k nd) rho tp Q' Hrun Hlen (JT_stable k nd _ Hnf Hnb) H).
Qed.

Lemma JT_entails : ltac2:(tb__ "0|0|
SbS38S38SddS58S58S1dS9S45Q40A1A1S68S0S7S3fR8R7R6A3S8A3S0S7SdfR7S44A2S8A3S0S7S6aS44S1aS36RaA1A1A2S8A3S0S7S57S1aS36RbA1A1R8A2S8A3S0S7S11cRaS5cR9A1S5cR8A1A3S8A3S0S7S66RbS60RaA1S60R9A1A3S8A3S0S7Sf8S1bS36ReA1A1Sf7RcS5fRaA1A2S5fRbA1A3S8A3S0S7S63S64RdS5dRbA1A2S5dRcA1A2S8A3S48S41VJT;R11RdA2R10RbRaR9A6S48S41VJT;R12RdA2R10Se1RcRfA2RbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fndj;Fndi;Fs;FT;FL;Fk;").
Proof.
  intros k L T s ndi ndj rho tp w. apply (SPA_entails_JA segs AInv CST XGL ALA NF (KcT k) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm k)).
Qed.

Lemma JT_factsT : ltac2:(tb__ "0|0|
SbS58S1dS9S45Q40A1A1S9S4dA1S4eVJT;R6R5R4R3R2R1A6S7cS20S24R5A1Sb6A3S5F_;F_;Fmd;Ftr;Ftp;Frho;Fnd;Fk;").
Proof. intros; exact I. Qed.

Lemma etriple_JT_pre : ltac2:(tb__ "0|0|
SbS58S38S1dS9S45Q40A1A1S68OF_;VP0T;VrhoT;A1S132S44VrhoT;R4A3S67S41S48S41VJT;R8R7A2R6R5R4A5R3A3F_;F_;S67S41S48S41VJT;R7R6A2R5R4R3A5R2A3F_;FQ';Ftp;Frho;FA;Fnd;Fk;").
Proof.
  intros k nd A rho tp Q' H w [Hsm HJ]. pose proof HJ as (Ai & kc & Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _).
  exact (H HP0 Hav w (conj Hsm HJ)).
Qed.

Definition plen0_b (facts : list sprop) : bool := ltac2:(tb__ "0|0|
Sa4S20S2fS2eSaaS1fZ0A1A2A1Vfacts;A3").
Lemma X_dead_plen0_ex : ltac2:(tb__ "0|0|
SbS58S38S0S7S12dS1bS36R1A1A1A1S8A3S106Z0S109S109S10aS11S45Q8A1VF;A2A1Z6A2Sb5VF;A1A2A2S1dS9S45Q40A1A1S67S41S48S41VJT;R7R6A2R5R2R1A5VQ;A3Ftp;Frho;F_;F_;FA;Fnd;Fk;").
Proof.
  intros k nd A Hb Hpl rho tp. apply etriple_factsA. intros HF. apply etriple_JT_pre. intros HP0 Hav.
  pose proof (holds_mem _ _ _ HF Hb) as X. cbn [holds] in X. unfold vPlen in X. cbn [eval] in X. rewrite lit_unsigned in X.
  change (0 mod 2 ^ 64) with 0 in X.
  destruct HP0 as [(_ & _ & _ & H34 & _) _]. rewrite <- (proj1 Hav 44%positive ltac:(unfold NF; lia)) in X. rewrite H34 in X.
  intros w _. exfalso. lia.
Qed.

Lemma P0T_SH : ltac2:(tb__ "0|0|
S1dVP0T;R1A1Sd0R2A1F_;Fr;").
Proof. intros r [_ H]. exact H. Qed.
Lemma HKfd1_T : ltac2:(tb__ "0|0|
SbS9S4dA1S4eVKcT;R3R2R1A3S0SdS50A1S54S55R2A1S10dA2SeS50S53S10dA1A2A3F_;Fmd;Ftr;Fk;").
Proof. intros k tr md [H _]. apply HMDfd1. exact H. Qed.
Lemma HQ_T : ltac2:(tb__ "0|6|
SbS42S42S68S4eVMD;R1A1S0S9S4dA1M0S69R3A1S10S4dS10S4dVT0;SecR6A1A3S10S4dS7aS45Q8A1M1S4dS51S10dA1M2S129R5A1A4SfS4dS4fS46Q40M3R4A2S52R2A1M4A2SaS4dA1M5A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;S68G0S4eVKcT;R7R2R1A3S0G0S69R4A1S10S4dR3S10S4dS7aG1S4dG2S129R7A1A4SfS4dS4fS46G3R6A2G4A2G5A3A3A3A3VQ;R5A1F_;F_;Fmd;Ftr;Fw;F_;Fc;Fn;Fk;").
Proof. intros k n c H w tr md [Hmd ->] Hw. exact (H w md Hmd Hw). Qed.

Lemma X_exit_pipe_ex : ltac2:(tb__ "0|2|
SbS58S42S42S38S9S19A1M0S0SdG0A1Sc0R5R2R4R3A4SeG0R1A2A3Sa2ScS42S42A2S12S42S42R5R4A4S10eA3S68S4eVMD;R1A1S0S9S4dA1S69R3A1S10S4dS10S4dVT0;SecRbA1A3S10S4dS7aS45Q8A1S4dS51S10dA1S129R9A1A4SfS4dS4fS46Q40M1R8A2S52R2A1A2SaS4dA1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;S1dS9S45G1A1A1S67S41S48S41VJT;RbRaA2R7R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;FR;FE;Fc;Fn;FndX;Fkx;").
Proof.
  intros kx ndX n c E R Hp Hs HQ.
  exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvSiteEx.X_exit_pipe_ex AInv CST XGL ALA HCSTdrv HLPP (KcT kx) (Kc_okT T0 MD HMDvm kx) rhoT P0T P0T_SH PTrue
           ndX n c E R Q Hp Hs (HKfd1_T kx) (HQ_T kx n c HQ)).
Qed.

Lemma X_join_ex : ltac2:(tb__ "0|6|
SbS9SfbA1M0G0S42S18S42S38S9S19A1M1S0SdS38A1Sc1R7R6S82R5R4A2A3SeS38R2A2A3S0SdG1A1Sc0S5aSaScS18S18A2M2A1M3SaScScS18S42A2S18A2A1M4R7S59A4R3R6R4A4SeG1R2A2A3Sa2ScS42S42A2S12S42S42R7R5A4S10eA3S68S4eVMD;R1A1S0S9S4dA1S69R3A1S10S4dS10S4dVT0;SecReA1A3S10S4dS7aS45Q8A1S4dS51S10dA1S129RbA1A4SfS4dS4fS46Q40M5R9A2S52R2A1A2SaS4dA1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;S1dS9S45G5A1A1S67S41S48S41VJT;ReS5aSfG2S12S18S18Sa8Sa9A4G3A3G4RdS59A4A2S82RbRaA2R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;F_;FR;FEx;Fc;Fst;Fn;FbdX;FbdJ;Fkx;").
Proof.
  intros kx bdJ bdX n st c Ex R Hfb Hex Hs HQ.
  exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvSiteEx.X_join_ex AInv CST XGL ALA HCST HXGL HCSTdrv HLPP ACX (KcT kx) (Kc_okT T0 MD HMDvm kx) rhoT P0T P0T_SH PTrue (fun _ _ _ _ => I)
           bdJ bdX (J_E n st) n c Ex R Q Hfb Hex Hs (HKfd1_T kx) (HQ_T kx n c HQ)).
Qed.

Section LoopP.
Variable k : Z.
Variables kx kx' : nat.
Variables bd0 bd1 : list bitem.
Hypothesis Hcapbd : ltac2:(tb__ "0|0|
S1dS105S108S10bSfeZ2A2S109SfcVbd0;R1A2SfcVbd1;R1A2A2A2SffA2Frho;").
Definition kept : list (sv * sv) := ltac2:(tb__ "0|1|
SfScS18S18A2M0S12S18S18S22S7fA1SaaA4SfG0S12S18S18Sa8Sa9A4SaG0A1A3A3").
Definition ndL0 : ndesc := ltac2:(tb__ "0|0|
S5aS75SaScScS18S42A2S18A2A1Vbd0;S59A4").
Definition ndL1 : ndesc := ltac2:(tb__ "0|0|
S5aS75SaScScS18S42A2S18A2A1Vbd1;S59A4").
Variable L : axst.
Variable Lnext : axst.
Variables (Efz : axst) (S1 S2 : sstate) (Rfz : list sobj) (TT : axst) (U1 U3 : sstate) (Tfz : axst).
Variables (Epf : axst) (P1 : sstate) (Rpf : list sobj) (TP : axst) (Q1 Q2 Q4 : sstate) (Upf : axst).
Variable leaves : list leafA.
Variable iw : nat.

Hypothesis HLwf : ltac2:(tb__ "0|2|
S1S0S7S6aS44S1aS36VL;A1M0A1M1A2S8A3S1S0S7S21G0A1S13A3S0S7S57G1S79A2S8A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S0SdS9S37A1M0A1S3cS41S81S80VL;S8A5SeG0SfS37S3eVEfz;Sa7A2SaS37A1A3A2A3").

Hypothesis F1 : ltac2:(tb__ "0|0|
S0SdS1cA1Se2S36VEfz;A1Viw;S1fS107S144A1A1A3SeS1cVS1;A2A3").
Hypothesis F2n : ltac2:(tb__ "0|0|
S0SdS19A1Sa3S19S1eVS1;A1Viw;A3SeS19S88A2A3").
Hypothesis F2e : ltac2:(tb__ "0|0|
S0S1cS110VS1;Viw;S8fA3VS2;A3").
Hypothesis F2s : ltac2:(tb__ "0|0|
S0S7S10fVS1;VS2;A2S8A3").
Hypothesis HspfE : ltac2:(tb__ "0|0|
S0S7SbaS1bS36VEfz;A1A1A1S8A3").
Definition Cfz : axst := ltac2:(tb__ "0|0|
S3dVS2;S39VEfz;A1S3aVEfz;A1A3").
Hypothesis F3n : ltac2:(tb__ "0|1|
S1S0S43S1aVS2;A1S1aS36VEfz;A1M0A1A3S0S9S20A1S1bVS2;A1S1bG0A1A3A2").

Hypothesis HFZ : ltac2:(tb__ "0|0|
S131VAInv;VCST;VXGL;VKcT;Vkx;A1A4").
Hypothesis Fxk : ltac2:(tb__ "0|1|
S0S7S148S39S73A1M0G0A2S8A3").
Hypothesis Ffr : ltac2:(tb__ "0|1|
S0SdS9S19A1M0A1Se5S73Sf5S7eS73A1A3SeG0VRfz;A2A3").
Hypothesis Fcc : ltac2:(tb__ "0|0|
S0S7Se6S73Sf5S7eS73A1VRfz;SfS38S12fSaS38A1A3A5S8A3").
Hypothesis Ftp : ltac2:(tb__ "0|0|
S0S7S102S44S7eS73A1A2S8A3").
Hypothesis Fdom : ltac2:(tb__ "0|0|
S0S7S133S7eS73A1S44A2S8A3").
Hypothesis Fnx : ltac2:(tb__ "0|0|
S0S7S6aS44S1aS36VEfz;A1A1A2S8A3").
Hypothesis Fnb : ltac2:(tb__ "0|2|
S1S0S7S57S1aS36VEfz;A1A1M0S5aS10ScS18S18A2M1S75SaG1A1A3SaScScS18S42A2S18A2A1Vbd0;S59A4A2S8A3S0S7Sf9G0Vbd1;A2S8A3A2").
Hypothesis Fpay : ltac2:(tb__ "0|1|
S0S7SfaS1bS36S73A1A1S1fZ0M0A1G0Vbd0;S10SfbSf7S7eS73A1Sf6A2Vbd1;A3A5S8A3").
Hypothesis Fpd : ltac2:(tb__ "0|0|
S0S7Sa1S147S146Sf5S44S7eS73A1S1aS36S73A1A1A4S130A3S8A3").
Hypothesis FspfC : ltac2:(tb__ "0|0|
S0S7SbaS1bS36S73A1A1A1S8A3").
Hypothesis Fknz : ltac2:(tb__ "0|0|
S0S7SbcS1bS36S73A1A1S75A2S8A3").
Hypothesis Fro : ltac2:(tb__ "0|0|
S0S7Sa1S19S19S15SbfS1bS36S73A1A1R1A2S11dS75S14SbA1R1A3A2Lo;VRfz;A3S8A3").
Hypothesis Fxr : ltac2:(tb__ "0|1|
S0S7Sa1ScS18S18A2M0G0S15SbbR1A1S103S75S14SbA1R1A3A2Lr;S39S73A1A3S8A3").
Hypothesis Fa0 : ltac2:(tb__ "0|1|
S1S0S18SdeS7eS73A1M0PcA2S22S7fA1A3S0S18SdeG0PdA2SaaA3A2").
Hypothesis FTT : ltac2:(tb__ "0|0|
S0S38S101Sf5S73S7eS73A1VRfz;S12fA5VTT;A3").

Hypothesis U1n : ltac2:(tb__ "0|0|
S0SdS19A1Sa3S19S1eS36VTT;A1A1U1A3SeS19S26S12eSb0S1fN250A1A2S1fS107S93A1A1S1fZ0A1SaS25A1S2dA5A2A3").
Hypothesis U1e : ltac2:(tb__ "0|0|
S0S1cS110S36VTT;A1U1S88A3VU1;A3").
Hypothesis U1s : ltac2:(tb__ "0|0|
S0S7S10fS36VTT;A1VU1;A2S8A3").
Hypothesis U1f : ltac2:(tb__ "0|0|
S0S7SbaS1bS36VTT;A1A1A1S8A3").
Hypothesis U2 : ltac2:(tb__ "0|2|
S0S7SeaS11S19S1eVU1;A1A2M0S10SbSfSbU1SfSbU0SaSbA1A3A3S7bU2M1Sa5G0G1A2A2A3A2S8A3").
Hypothesis U3e : ltac2:(tb__ "0|3|
S0SdS1cA1Se3Sa6VU1;Se4S1eVU1;A1M0S10SbSfSbU1SfSbU0M1SaSbA1A3A3S7bU2M2Sa5S11S19G0A2G2A2A2A3A2A2G1A2SeS1cVU3;A2A3").
Hypothesis UT : ltac2:(tb__ "0|0|
S0S38S3dVU3;S39VTT;A1S3aVTT;A1A3VTfz;A3").

Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S6aS44S1aS36VTfz;A1M0A1M1A2S8A3S1S0S7S21G0A1S13A3S0S7S57G1S76A2S8A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S0SdS9S37A1M0A1S3cS41S81S80VTfz;S8A5SeG0SfS37S3eVEpf;Sa7A2SaS37A1A3A2A3").

Hypothesis P1e : ltac2:(tb__ "0|0|
S0SdS1cA1Se2S36VEpf;A1U0S1fS107S140A1A1A3SeS1cVP1;A2A3").
Definition P1c : sstate := ltac2:(tb__ "0|0|
S27S2aVP1;A1S2bVP1;A1S29VP1;A1S28VP1;A1S2cVP1;A1S10S19S1eVP1;A1S7aSd1S19Sd2SebA4A3S1bVP1;A1S1aVP1;A1S21VP1;A1A9").
Hypothesis P2w : swf P1c = true.
Hypothesis P2c : ltac2:(tb__ "0|0|
S0S7Sd4S1bVP1;A1S1eVP1;A1S39VEpf;A1Sc4Sc6S5cS76A1SebA7S8A3").
Hypothesis P2n : ltac2:(tb__ "0|0|
S0S43S1aVP1;A1S1aS36VEpf;A1A1A3").
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S18S3aVEpf;A1S1fS135A1A3").
Definition Cpf0 : axst := ltac2:(tb__ "0|0|
S3dS78S39VEpf;A1S3aVEpf;A1A3").
Definition Cpf : axst := ltac2:(tb__ "0|0|
S13eS84S77Vk;A2S77A2").
Hypothesis P3b : ltac2:(tb__ "0|0|
S0S7Sa1S20S23S1aS78A1A1S10S20S84S77Vk;A2S1bS78A1A3A3S8A3").
Hypothesis P3h : ltac2:(tb__ "0|0|
S20Sa2S20R1S84S77Vk;A2A3S2S18S18S0S20R3Sf3R1A1A3Lx;A2F_;Fq;").

Hypothesis Pfr : ltac2:(tb__ "0|1|
S0SdS9S19A1M0A1Se5S74S83Vk;A1S86S74Vk;A2A3SeG0VRpf;A2A3").
Hypothesis Pcc : ltac2:(tb__ "0|0|
S0S7Se7S74S83Vk;A1S86S74Vk;A2VRpf;S7aS37S38S3bS142Vk;A1A4A5S8A3").
Hypothesis Pnx : ltac2:(tb__ "0|0|
S0S7S6aS44S1aS36S74A1A1A2S8A3").
Hypothesis Pnb : ltac2:(tb__ "0|0|
S0S7S57S1aS36S74A1A1S76A2S8A3").
Hypothesis Pfb : ltac2:(tb__ "0|1|
S0S7Sa1S20S23S1aS36S74A1M0A1A1S1bG0A1A3S8A3").
Hypothesis Pk : ltac2:(tb__ "0|2|
S3S1S0S42Vk;Z0A3S1S0SbVkx;U0A3S0SbVkx';U1M0A3M1A2A2S1S143Vk;A1S1S0SbVkx;G0A3G1A2A2A2").
Hypothesis PTP : ltac2:(tb__ "0|0|
S0S38S101S83Vk;A1S74S86S74Vk;A2VRpf;S141Vk;A1A5VTP;A3").

Hypothesis Q1e : ltac2:(tb__ "0|1|
S0S7SeaS11S19S1eS36VTP;A1A1A2M0S8aG0A1A2S8A3").
Hypothesis Q1o : ltac2:(tb__ "0|1|
S0S9S19A1Se4S1eS36VTP;A1A1M0S8aS11S19G0A2A1A2S1eVQ1;A1A3").
Hypothesis Q1d : ltac2:(tb__ "0|0|
S0S1cSa6S36VTP;A1S1eVQ1;A1A2VQ1;A3").
Hypothesis Q1s : ltac2:(tb__ "0|1|
S0S9S19A1S1eVQ1;A1M0S10S19S7dS19Sa5S11S19G0A2U4A2G0A3S7aSd1S19Sd2SebA4A3A3").
Hypothesis Q2e : ltac2:(tb__ "0|1|
S0S1cSa6VQ1;S7dS19Sa5S11S19S1eVQ1;A1M0A2U4A2G0A3A2VQ2;A3").
Hypothesis Q2u : ltac2:(tb__ "0|0|
S0S7Sd5Sc4SebA2S8A3").
Hypothesis Q2n : ltac2:(tb__ "0|0|
S0S7S57S1aVQ1;A1S76A2S8A3").
Hypothesis Q3e : ltac2:(tb__ "0|2|
S0S7SeaS11S19S1eVQ2;A1A2M0S10SbSfSbU8SfSbU0SaSbA1A3A3S10SbS7bU1U7A2S7bU9M1Sa5G0G1A2A2A3A3A2S8A3").
Hypothesis Q4e : ltac2:(tb__ "0|3|
S0SdS1cA1Se3Sa6VQ2;Se4S1eVQ2;A1M0S10SbSfSbU8SfSbU0M1SaSbA1A3A3S10SbS7bU1U7A2S7bU9M2Sa5S11S19G0A2G2A2A2A3A3A2A2G1A2SeS1cVQ4;A2A3").
Hypothesis QU : ltac2:(tb__ "0|0|
S0S38S3dVQ4;S39VTP;A1S3aVTP;A1A3VUpf;A3").

Hypothesis HUwf : ltac2:(tb__ "0|2|
S1S0S7S6aS44S1aS36VUpf;A1M0A1M1A2S8A3S1S0S7S21G0A1S13A3S0S7S57G1S76A2S8A3A2A2").
Hypothesis Hrun3 : ltac2:(tb__ "0|1|
S0SdS9S37A1M0A1S3cS41S81S80VUpf;S8A5SeG0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|3|
S37Sa2S37R1Vleaves;A3S3S2SddSddS1S0S7S3fS3bR3A1M0VLnext;R1A3S8A3S1S0S7SdfR1S44A2S8A3S1S0S7S6aS44S1aS36G0A1M1A1M2A2S8A3S1S0S7S57G2S76A2S8A3S1S0S7S11cR1S75S75A3S8A3S0S7Sf8S1bG1A1Sf7R1Vbd1;A2Vbd1;A3S8A3A2A2A2A2A2Ls;A2S1dS9S45Q40A1A1S67S41S48S41VJT;Vkx';S76A2S3bR4A1R2R1A5VQ;A3Ftp;Frho;A2F_;FLf;").
Hypothesis Hnext : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;Vkx';S76A2VLnext;R2R1A5VQ;A3Ftp;Frho;").

Lemma X_loopP_ex : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;Vkx;S79A2VL;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. destruct HLwf as (W1 & W2 & W3). destruct Fnb as [Fnb1 Fnb2]. destruct Fa0 as [Fa12 Fa13]. destruct F3n as [F3nx F3f].
  destruct HTwf as (V1 & V2 & V3). destruct HUwf as (Y1 & Y2 & Y3).

  eapply JT_erun; [exact Hrun1 | exact W2 | exact W1 | exact W3 |].
  intros Lf rho1 [<-|[]] Hag1. cbn [la_state].
  apply etriple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho1 sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF | exact HspfE]. }

  eapply (etriple_conseq (P := SPA segs (JT kx ndL0) Cfz rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof (SPA_split segs (JT kx ndL0) rho1 Efz iw (SLit (- fz_frame)) S1 tp w F1 HS) as HS1.
    unfold Cfz. rewrite <- F2e. change (mkAX (set_obj_at S1 iw O_WfzT) (ax_X Efz) (ax_base Efz)) with (ax_setS (mkAX S1 (ax_X Efz) (ax_base Efz)) (set_obj_at S1 iw O_WfzT)).
    apply (SPA_reslice segs (JT kx ndL0) rho1 (mkAX S1 (ax_X Efz) (ax_base Efz)) iw O_WloT O_WfzT tp w F2n); try reflexivity.
    - cbn [ax_S]. rewrite F2e. exact F2s.
    - unfold O_WloT, O_WfzT, spT. rewrite !obj_range_lits by (unfold WDP, DEEP, fz_frame; lia).
      rewrite !U_add_lit by (unfold fz_frame; try lia; rewrite U_add_lit by lia; lia). unfold WDP, DEEP, fz_frame. f_equal; lia.
    - unfold O_WfzT, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold WDP, DEEP, fz_frame; lia). unfold WDP, DEEP, fz_frame; lia.
    - exact HS1. }

  assert (HnxC : ss_next (ax_S Cfz) = ss_next (ax_S Efz)) by (unfold Cfz; cbn [ax_S]; exact F3nx).
  unfold ndL0, kept.

  assert (Fnbc : bd_below (ss_next (ax_S Efz)) (bd_subst (s_fz Cfz) bd_fz) = true).
  { pose proof (proj1 (Pos.leb_le _ _) Fnx) as Hnf. unfold NF in Hnf. unfold bd_fz, bd_subst, bi_subst, lf_subst, bd_below, vLEN. cbn [map forallb bi_f fst snd atom_subst asv sv_subst].
    rewrite Fa13. unfold vPlen. cbn [sv_below]. try (assert (E : (44 <? ss_next (ax_S Efz))%positive = true) by (apply Pos.ltb_lt; lia); rewrite E). reflexivity. }
  apply (box_open_Te segs AInv CST XGL ALA NF (KcT kx) rhoT P0T [] [] PTrue BX0 [(SVar vP, vPlen); (vB, vCap)] [] bd0 (bd_subst (s_fz Cfz) bd_fz) bd1 Cfz rho1 tp _ (BXnn_mk00 0) Fpay).
  { intros _. pose proof (Hcapbd rho1) as HC. assert (LMP : 0 <= LARGE_MIN) by (unfold LARGE_MIN; lia). cbn [length]. lia. }
  intros BXc HBXc Hback.
  rewrite <- (app_nil_r [(SVar vP, vPlen); (vB, vCap)]).
  apply (client_callA_ex segs AInv CST XGL ALA HCST HXGL NF (KcT kx) rhoT P0T [] [] BXc PTrue (Kc_okT T0 MD HMDvm kx) HBXc
           (P0_fz CST) PTrue (fun _ H => H) (fun _ _ _ H => H) Pre_fz nd_fz0 PD_fz NF eq_refl eq_refl eq_refl
           (fun FBc FFc BXc rho2 tp2 HB => HFZ FBc FFc BXc rho2 tp2 HB) eq_refl
           Cfz (s_fz Cfz) Rfz (ax_X Cfz) rho1 tp [(SVar vP, vPlen); (vB, vCap)] [] [] (bd_subst (s_fz Cfz) bd_fz) [] ANone Q
           Fxk Ffr Fcc Ftp Fdom).
  - rewrite HnxC. exact Fnx.
  - rewrite HnxC. pose proof (nd_below_split _ _ Fnb1) as (N1 & N2 & _ & N4). pose proof (nd_below_len _ _ Fnb1) as N5. cbn [nd_tv nd_fr nd_bd nd_am] in N1, N2, N4, N5. apply nd_below_intro; cbn [nd_tv nd_fr nd_bd nd_am]; [exact N1 | exact N2 | exact Fnbc | exact N4 | exact N5].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply payA_self. reflexivity.
  - rewrite HnxC. unfold Cfz in Fpd. cbn [ax_S] in Fpd. rewrite F3nx in Fpd. exact Fpd.
  -
    intros Ai ms HF' HP0 Hav HB HFF HN HD HZ HFR HM HTPA HTok. rewrite app_nil_r in HN, HD, HZ.
    split; [eapply robjs_okF_drv; [exact HF' | exact FspfC | exact (T0_of_site _ _ _ HTPA HTok) | exact Fknz | exact Fro]|].
    split; [eapply xrs_okF_drv; [exact HF' | exact FspfC | exact (T0_of_site _ _ _ HTPA HTok) | exact Fknz | exact Fxr]|].
    unfold P0_fz. split; [|intros c; reflexivity].
    intros a Ha. unfold uval, vDAT, vLEN in Ha. cbn [eval] in Ha. rewrite !rw_call' in Ha. rewrite Fa12, Fa13 in Ha.
    eapply (kept_in_FBx _ rho1 (ss_facts (ax_S Cfz)) [(SVar vP, vPlen); (vB, vCap)] (SVar vP, vPlen) a HF' Fknz); [left; reflexivity|].
    unfold tvv. cbn [fst snd]. exact Ha.
  -
    intros d rho' tp' [<-|[]] Hag'. cbn [fst snd nd_tv nd_bd nd_am nd_fz1 import_tv bd_subst am_subst map app].
    unfold T_afterA3. rewrite import_postA3_full. fold (T_afterA Pre_fz Cfz (s_fz Cfz) Rfz P_fz). rewrite FTT.
    fold kept. fold ndL1.

    eapply (etriple_conseq (P := SPA segs (JT kx ndL1) TT rho' tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { exact (box_close segs AInv CST XGL NF (KcT kx) rhoT P0T [] [] PTrue BX0 BXc bd1 kept [] [] ANone (ss_next (ax_S Cfz)) TT rho1 rho' tp' w (BXnn_mk00 0) Hback Hag' ltac:(rewrite HnxC; exact Fnb2) HS). }

    apply etriple_factsA. intros HF2.
    assert (Hsp' : 0x7fff80000000 <= bv_unsigned (eval rho' sp0) <= 2 ^ 47 - 224).
    { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF2 | exact U1f]. }
    eapply (etriple_conseq (P := SPA segs (JT kx ndL1) Tfz rho' tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { assert (HS1 : SPA segs (JT kx ndL1) (ax_setS TT U1) rho' tp' w).
      { rewrite <- U1e. apply (SPA_reslice segs (JT kx ndL1) rho' TT 1 _ O_WloT tp' w U1n); try reflexivity.
        - rewrite U1e. exact U1s.
        - unfold O_WloT, spT. rewrite !obj_range_lits by (unfold WDP, DEEP, fz_frame; lia).
          rewrite !U_add_lit by (unfold fz_frame; try lia; rewrite U_add_lit by lia; lia). unfold WDP, DEEP, fz_frame. f_equal; lia.
        - unfold O_WloT, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP, fz_frame; lia). unfold DEEP, fz_frame; lia.
        - exact HS. }
      pose proof (AxXform.SPA_select segs (JT kx ndL1) rho' (mkAX U1 (ax_X TT) (ax_base TT)) _ tp' w U2 HS1) as HS2.
      pose proof (SPA_merge segs (JT kx ndL1) rho' (mkAX (set_objs U1 (select (ss_objs U1) ([1; 0] ++ seq 2 (length (ss_objs U1) - 2))%nat)) (ax_X TT) (ax_base TT)) 0 U3 tp' w U3e HS2) as HS3.
      rewrite <- UT. exact HS3. }

    eapply JT_erun; [exact Hrun2 | exact V2 | exact V1 | exact V3 |].
    intros Lf rho2 [<-|[]] Hag2. cbn [la_state].
    apply etriple_factsA. intros HF3.

    eapply (etriple_conseq (P := SPA segs (JT kx ndL1) Cpf rho2 tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { pose proof (SPA_split segs (JT kx ndL1) rho2 Epf 0 (SLit (- PW)) P1 tp' w P1e HS) as HS1.
      assert (HS2 : SPA segs (JT kx ndL1) Cpf0 rho2 tp' w).
      { pose proof (carveT (KcT kx) ndL1 (mkAX P1 (ax_X Epf) (ax_base Epf)) rho2 tp' w N_pf (ss_next P1) HS1) as X.
        cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X; [exact P2w | apply Pos.leb_refl | exact HbE | exact P2c]. }
      unfold Cpf, ax_add_facts.
      change (ax_setS Cpf0 (add_facts (pf_hints Cpf0 k) (ax_S Cpf0))) with (ax_with_facts Cpf0 (pf_hints Cpf0 k ++ ss_facts (ax_S Cpf0))).
      apply (SPA_refacts_JA segs); [exact HS2 | exact P3b |].
      intros tr md HJ HFc. apply Forall_app. split; [|exact HFc]. apply Forall_forall. intros q Hq.
      destruct (P3h q Hq) as [x ->]. apply ms16_holds. }

    assert (HnxP : ss_next (ax_S Cpf) = ss_next (ax_S Epf)).
    { unfold Cpf, Cpf0, ax_add_facts. cbn [ax_S ss_next add_facts P1c]. exact P2n. }
    set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JT kx ndL1 rho2 t tr md).
    assert (JpK : forall r t tr md, Jp r t tr md -> MD md /\ tr = T0 ++ EVk kx) by (intros r t tr md HJ; exact (JT_Kc _ _ _ _ _ _ HJ)).
    assert (HstJp : stableA segs NF Jp).
    { intros r r' t tr md md' Hag Hme HJ. unfold Jp in HJ |- *. destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF (KcT kx) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm kx) ALA (ss_next (ax_S Cpf)) ndL1 Ai kc rho2 rho2 t tr md md');
        [apply Pos.leb_le; exact Pnx | exact Pnb | apply agree_below_refl | exact Hme | exact HJi]. }
    assert (CONT : forall Lf rho3, In Lf (Posts_pf k) -> agree_below (ss_next (ax_S Cpf)) rho2 rho3 ->
              etriple segs (SPA segs (JT kx' ndL1) (ax_add_facts (ss_facts (ax_S Cpf)) (import_postA (s_pf Cpf k) (PreP k) (la_state Lf) Cpf Rpf)) rho3 tp') Q).
    { intros Lf rho3 HinL Hag3. unfold Posts_pf in HinL. destruct HinL as [<-|[]]. cbn [la_state].
      fold (T_afterA (PreP k) Cpf (s_pf Cpf k) Rpf (P_pf k)). rewrite PTP.

      eapply (etriple_conseq (P := fun w => exists rho4, SPA segs (JT kx' ndL1) Upf rho4 tp' w)); [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct w as [tr [ms md]].
        pose proof (AxXform.SPA_select segs (JT kx' ndL1) rho3 TP _ tp' _ Q1e HS) as HS1. rewrite Q1o, Q1d in HS1.
        pose proof (uncarveT (KcT kx') ndL1 (mkAX Q1 (ax_X TP) (ax_base TP)) rho3 tp' tr ms md _ N_pf (Kc_okT T0 MD HMDvm kx') Q1s Q2u eq_refl Q2n HS1) as HS2.
        cbn [ax_S ax_setS ax_X ax_base] in HS2. rewrite Q2e in HS2.
        set (rho4 := rho_absorb rho3 (map lc_obj N_pf) (vms md tp' ms)) in HS2. exists rho4.
        pose proof (AxXform.SPA_select segs (JT kx' ndL1) rho4 (mkAX Q2 (ax_X TP) (ax_base TP)) _ tp' _ Q3e HS2) as HS3.
        pose proof (SPA_merge segs (JT kx' ndL1) rho4 (mkAX (set_objs Q2 (select (ss_objs Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs Q2) - 9))%nat)) (ax_X TP) (ax_base TP)) 0 Q4 tp' _ Q4e HS3) as HS4.
        rewrite <- QU. exact HS4. }
      apply etriple_ex. intros rho4.

      eapply JT_erun; [exact Hrun3 | exact Y2 | exact Y1 | exact Y3 |].
      intros Lf rho5 HinLf Hag5.
      destruct (Hleaves Lf HinLf) as [(s5 & E1 & E2 & E3 & E4 & E5 & E6)|HX]; [|apply HX].
      eapply (etriple_conseq (P := SPA segs (JT kx' ndL1) Lnext (rho_sub rho5 s5) tp')); [intros w HS | intros w' Hw'; exact Hw' | apply Hnext].
      apply (JT_entails kx' (la_state Lf) Lnext s5 ndL1 ndL1 rho5 tp' w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS). }
    destruct Pk as [(Ek & Ekx & Ekx')|(Hkok & Ekx & Ekx')].
    +
      subst kx kx'. unfold PreP in *. rewrite Ek in *. cbn [Z.eqb] in *.
      apply (pcallT (KcT 0) (KcT 1) Cpf Pre_pf0 (s_pf Cpf 0) Rpf (Posts_pf 0) rho2 tp' ndL1 Jp (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.Kw Jp 2) Q (Kc_okT T0 MD HMDvm 1)).
      * intros rho6 tp6. apply (printf0_sum_ex Jp HstJp). intros r t tr md HJ. apply HMDfd1. exact (proj1 (JpK _ _ _ _ HJ)).
      * exact Pfr.
      * exact Pcc.
      * exact Pnx.
      * exact Pnb.
      * exact Pfb.
      * intros tr ms md Hsm HJ. exact HJ.
      * intros rhoL tr' md' (tr0 & HJ & ->). unfold Jp in HJ. destruct HJ as (Ai & kc & Hav & [Hmd Htr] & REST).
        exists Ai, kc. split; [exact Hav|]. split; [|exact REST]. split; [exact Hmd|]. rewrite Htr. cbn [EVk]. rewrite app_nil_r. reflexivity.
      * exact CONT.
    +
      subst kx kx'.
      assert (EP : PreP k = Pre_pf k).
      { unfold PreP. destruct Hkok as [->|[->| ->]]; reflexivity. }
      rewrite EP in *.
      apply (pcallT (KcT 1) (KcT 1) Cpf (Pre_pf k) (s_pf Cpf k) Rpf (Posts_pf k) rho2 tp' ndL1 Jp Jp Q (Kc_okT T0 MD HMDvm 1)).
      * intros rho6 tp6. apply (printf_sum_ex Jp HstJp k rho6 tp6 Hkok).
      * exact Pfr.
      * exact Pcc.
      * exact Pnx.
      * exact Pnb.
      * exact Pfb.
      * intros tr ms md Hsm HJ. exact HJ.
      * intros rhoL tr' md' HJ. exact HJ.
      * exact CONT.
Qed.
End LoopP.

Section LoopE.
Variable k : Z.
Variables kx kx' : nat.
Variables bd0 bd1 : list bitem.
Hypothesis Hcapbd : ltac2:(tb__ "0|0|
S1dS105S108S10bSfeZ2A2S109SfcVbd0;R1A2SfcVbd1;R1A2A2A2SffA2Frho;").
Definition keptE : list (sv * sv) := ltac2:(tb__ "0|1|
SfScS18S18A2M0S12S18S18Sa8Sa9A4SaG0A1A3").
Definition ndE0 : ndesc := ltac2:(tb__ "0|0|
S5aS6eSaScScS18S42A2S18A2A1Vbd0;S59A4").
Definition ndE1 : ndesc := ltac2:(tb__ "0|0|
S5aS6eSaScScS18S42A2S18A2A1Vbd1;S59A4").
Variable L : axst.
Variable Lnext : axst.
Variables (Efz : axst) (S1 S2 S3 : sstate) (Rfz : list sobj) (TT : axst) (U1 U3 U4 : sstate) (Tfz : axst).
Variables (bE : sv) (dE : odefault).
Variables (Epf : axst) (P1 : sstate) (Rpf : list sobj) (TP : axst) (Q1 Q2 Q4 : sstate) (Upf : axst).
Variable leaves : list leafA.
Variable iw : nat.

Hypothesis HLwf : ltac2:(tb__ "0|2|
S1S0S7S6aS44S1aS36VL;A1M0A1M1A2S8A3S1S0S7S21G0A1S13A3S0S7S57G1S72A2S8A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S0SdS9S37A1M0A1S3cS41S81S80VL;S8A5SeG0SfS37S3eVEfz;Sa7A2SaS37A1A3A2A3").

Hypothesis F1 : ltac2:(tb__ "0|0|
S0SdS1cA1Se2S36VEfz;A1Viw;S1fS107S144A1A1A3SeS1cVS1;A2A3").
Hypothesis F2n : ltac2:(tb__ "0|0|
S0SdS19A1Sa3S19S1eVS1;A1Viw;A3SeS19S88A2A3").
Hypothesis F2e : ltac2:(tb__ "0|0|
S0S1cS110VS1;Viw;S8fA3VS2;A3").
Hypothesis F2s : ltac2:(tb__ "0|0|
S0S7S10fVS1;VS2;A2S8A3").
Hypothesis HspfE : ltac2:(tb__ "0|0|
S0S7SbaS1bS36VEfz;A1A1A1S8A3").

Hypothesis F2a : ltac2:(tb__ "0|0|
S0S1cS14cVS2;S90A2VS3;A3").
Hypothesis F2w : swf S3 = true.
Hypothesis F2o : ltac2:(tb__ "0|0|
S0S7S32S1aVS2;A1S90A2S8A3").
Definition CfzE : axst := ltac2:(tb__ "0|1|
S3dVS3;S10ScS18S18A2M0S39VEfz;A1SfG0S94SaG0A1A3A3S3aVEfz;A1A3").
Hypothesis F3n : ltac2:(tb__ "0|1|
S1S0S43S1aVS3;A1S1aS36VEfz;A1M0A1A3S0S9S20A1S1bVS3;A1S1bG0A1A3A2").

Hypothesis HFZ : ltac2:(tb__ "0|0|
S131VAInv;VCST;VXGL;VKcT;Vkx;A1A4").
Hypothesis Fxk : ltac2:(tb__ "0|1|
S0S7S148S39S6cA1M0G0A2S8A3").
Hypothesis Ffr : ltac2:(tb__ "0|1|
S0SdS9S19A1M0A1Se5S6cSf5S7eS6cA1A3SeG0VRfz;A2A3").
Hypothesis Fcc : ltac2:(tb__ "0|0|
S0S7Se6S6cSf5S7eS6cA1VRfz;SfS38S12fSaS38A1A3A5S8A3").
Hypothesis Ftp : ltac2:(tb__ "0|0|
S0S7S102S44S7eS6cA1A2S8A3").
Hypothesis Fdom : ltac2:(tb__ "0|0|
S0S7S133S7eS6cA1S44A2S8A3").
Hypothesis Fnx : ltac2:(tb__ "0|0|
S0S7S6aS44S1aS36VEfz;A1A1A2S8A3").
Hypothesis Fnb : ltac2:(tb__ "0|2|
S1S0S7S57S1aS36VEfz;A1A1M0S5aS10ScS18S18A2M1S6eSaG1A1A3SaScScS18S42A2S18A2A1Vbd0;S59A4A2S8A3S0S7Sf9G0Vbd1;A2S8A3A2").
Hypothesis Fpay : ltac2:(tb__ "0|1|
S0S7SfaS1bS36S6cA1A1S1fZ0M0A1G0Vbd0;S10SfbSf7S7eS6cA1Sf6A2Vbd1;A3A5S8A3").
Hypothesis Fpd : ltac2:(tb__ "0|0|
S0S7Sa1S147S146Sf5S44S7eS6cA1S1aS36S6cA1A1A4S130A3S8A3").
Hypothesis FspfC : ltac2:(tb__ "0|0|
S0S7SbaS1bS36S6cA1A1A1S8A3").
Hypothesis Fknz : ltac2:(tb__ "0|0|
S0S7SbcS1bS36S6cA1A1S6eA2S8A3").
Hypothesis Fro : ltac2:(tb__ "0|0|
S0S7Sa1S19S19S15SbfS1bS36S6cA1A1R1A2S11dS6eS14SbA1R1A3A2Lo;VRfz;A3S8A3").
Hypothesis Fxr : ltac2:(tb__ "0|1|
S0S7Sa1ScS18S18A2M0G0S15SbbR1A1S103S6eS14SbA1R1A3A2Lr;S39S6cA1A3S8A3").
Hypothesis Fa0 : ltac2:(tb__ "0|0|
S0S18SdeS7eS6cA1PdA2S1fZ0A1A3").
Hypothesis FTT : ltac2:(tb__ "0|0|
S0S38S101Sf5S6cS7eS6cA1VRfz;S12fA5VTT;A3").

Hypothesis U1n : ltac2:(tb__ "0|0|
S0SdS19A1Sa3S19S1eS36VTT;A1A1U1A3SeS19S26S12eSb0S1fN250A1A2S1fS107S93A1A1S1fZ0A1SaS25A1S2dA5A2A3").
Hypothesis U1e : ltac2:(tb__ "0|0|
S0S1cS110S36VTT;A1U1S88A3VU1;A3").
Hypothesis U1s : ltac2:(tb__ "0|0|
S0S7S10fS36VTT;A1VU1;A2S8A3").
Hypothesis U1f : ltac2:(tb__ "0|0|
S0S7SbaS1bS36VTT;A1A1A1S8A3").
Hypothesis U2 : ltac2:(tb__ "0|2|
S0S7SeaS11S19S1eVU1;A1A2M0S10SbSfSbU1SfSbU0SaSbA1A3A3S7bU2M1Sa5G0G1A2A2A3A2S8A3").
Hypothesis U3e : ltac2:(tb__ "0|3|
S0SdS1cA1Se3Sa6VU1;Se4S1eVU1;A1M0S10SbSfSbU1SfSbU0M1SaSbA1A3A3S7bU2M2Sa5S11S19G0A2G2A2A2A3A2A2G1A2SeS1cVU3;A2A3").

Hypothesis U4n : ltac2:(tb__ "0|1|
S0SdS19A1Sa3S19S1eVU3;A1U1A3SeS19S26VbE;S1fZ0A1M0G0SaS25A1VdE;A5A2A3").
Hypothesis U4e : drop_obj_at U3 1 = U4.
Hypothesis UT : ltac2:(tb__ "0|0|
S0S38Sb4S94S3dVU4;S39VTT;A1S3aVTT;A1A3A2VTfz;A3").

Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S6aS44S1aS36VTfz;A1M0A1M1A2S8A3S1S0S7S21G0A1S13A3S0S7S57G1S6fA2S8A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S0SdS9S37A1M0A1S3cS41S81S80VTfz;S8A5SeG0SfS37S3eVEpf;Sa7A2SaS37A1A3A2A3").

Hypothesis P1e : ltac2:(tb__ "0|0|
S0SdS1cA1Se2S36VEpf;A1U0S1fS107S140A1A1A3SeS1cVP1;A2A3").
Definition P1cE : sstate := ltac2:(tb__ "0|0|
S27S2aVP1;A1S2bVP1;A1S29VP1;A1S28VP1;A1S2cVP1;A1S10S19S1eVP1;A1S7aSd1S19Sd2SebA4A3S1bVP1;A1S1aVP1;A1S21VP1;A1A9").
Hypothesis P2w : swf P1cE = true.
Hypothesis P2c : ltac2:(tb__ "0|0|
S0S7Sd4S1bVP1;A1S1eVP1;A1S39VEpf;A1Sc4Sc6S5cS6fA1SebA7S8A3").
Hypothesis P2n : ltac2:(tb__ "0|0|
S0S43S1aVP1;A1S1aS36VEpf;A1A1A3").
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S18S3aVEpf;A1S1fS135A1A3").
Definition Cpf0E : axst := ltac2:(tb__ "0|0|
S3dS71S39VEpf;A1S3aVEpf;A1A3").
Definition CpfE : axst := ltac2:(tb__ "0|0|
S13eS84S70Vk;A2S70A2").
Hypothesis P3b : ltac2:(tb__ "0|0|
S0S7Sa1S20S23S1aS71A1A1S10S20S84S70Vk;A2S1bS71A1A3A3S8A3").
Hypothesis P3h : ltac2:(tb__ "0|0|
S20Sa2S20R1S84S70Vk;A2A3S2S18S18S0S20R3Sf3R1A1A3Lx;A2F_;Fq;").

Hypothesis Pfr : ltac2:(tb__ "0|1|
S0SdS9S19A1M0A1Se5S6dS83Vk;A1S86S6dVk;A2A3SeG0VRpf;A2A3").
Hypothesis Pcc : ltac2:(tb__ "0|0|
S0S7Se7S6dS83Vk;A1S86S6dVk;A2VRpf;S7aS37S38S3bS142Vk;A1A4A5S8A3").
Hypothesis Pnx : ltac2:(tb__ "0|0|
S0S7S6aS44S1aS36S6dA1A1A2S8A3").
Hypothesis Pnb : ltac2:(tb__ "0|0|
S0S7S57S1aS36S6dA1A1S6fA2S8A3").
Hypothesis Pfb : ltac2:(tb__ "0|1|
S0S7Sa1S20S23S1aS36S6dA1M0A1A1S1bG0A1A3S8A3").
Hypothesis Pk : ltac2:(tb__ "0|2|
S3S1S0S42Vk;Z0A3S1S0SbVkx;U0A3S0SbVkx';U1M0A3M1A2A2S1S143Vk;A1S1S0SbVkx;G0A3G1A2A2A2").
Hypothesis PTP : ltac2:(tb__ "0|0|
S0S38S101S83Vk;A1S6dS86S6dVk;A2VRpf;S141Vk;A1A5VTP;A3").

Hypothesis Q1e : ltac2:(tb__ "0|1|
S0S7SeaS11S19S1eS36VTP;A1A1A2M0S8aG0A1A2S8A3").
Hypothesis Q1o : ltac2:(tb__ "0|1|
S0S9S19A1Se4S1eS36VTP;A1A1M0S8aS11S19G0A2A1A2S1eVQ1;A1A3").
Hypothesis Q1d : ltac2:(tb__ "0|0|
S0S1cSa6S36VTP;A1S1eVQ1;A1A2VQ1;A3").
Hypothesis Q1s : ltac2:(tb__ "0|1|
S0S9S19A1S1eVQ1;A1M0S10S19S7dS19Sa5S11S19G0A2U4A2G0A3S7aSd1S19Sd2SebA4A3A3").
Hypothesis Q2e : ltac2:(tb__ "0|1|
S0S1cSa6VQ1;S7dS19Sa5S11S19S1eVQ1;A1M0A2U4A2G0A3A2VQ2;A3").
Hypothesis Q2u : ltac2:(tb__ "0|0|
S0S7Sd5Sc4SebA2S8A3").
Hypothesis Q2n : ltac2:(tb__ "0|0|
S0S7S57S1aVQ1;A1S6fA2S8A3").
Hypothesis Q3e : ltac2:(tb__ "0|2|
S0S7SeaS11S19S1eVQ2;A1A2M0S10SbSfSbU8SfSbU0SaSbA1A3A3S10SbS7bU1U7A2S7bU9M1Sa5G0G1A2A2A3A3A2S8A3").
Hypothesis Q4e : ltac2:(tb__ "0|3|
S0SdS1cA1Se3Sa6VQ2;Se4S1eVQ2;A1M0S10SbSfSbU8SfSbU0M1SaSbA1A3A3S10SbS7bU1U7A2S7bU9M2Sa5S11S19G0A2G2A2A2A3A3A2A2G1A2SeS1cVQ4;A2A3").
Hypothesis QU : ltac2:(tb__ "0|0|
S0S38S3dVQ4;S39VTP;A1S3aVTP;A1A3VUpf;A3").

Hypothesis HUwf : ltac2:(tb__ "0|2|
S1S0S7S6aS44S1aS36VUpf;A1M0A1M1A2S8A3S1S0S7S21G0A1S13A3S0S7S57G1S6fA2S8A3A2A2").
Hypothesis Hrun3 : ltac2:(tb__ "0|1|
S0SdS9S37A1M0A1S3cS41S81S80VUpf;S8A5SeG0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|3|
S37Sa2S37R1Vleaves;A3S3S2SddSddS1S0S7S3fS3bR3A1M0VLnext;R1A3S8A3S1S0S7SdfR1S44A2S8A3S1S0S7S6aS44S1aS36G0A1M1A1M2A2S8A3S1S0S7S57G2S6fA2S8A3S1S0S7S11cR1S6eS6eA3S8A3S0S7Sf8S1bG1A1Sf7R1Vbd1;A2Vbd1;A3S8A3A2A2A2A2A2Ls;A2S1dS9S45Q40A1A1S67S41S48S41VJT;Vkx';S6fA2S3bR4A1R2R1A5VQ;A3Ftp;Frho;A2F_;FLf;").
Hypothesis Hnext : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;Vkx';S6fA2VLnext;R2R1A5VQ;A3Ftp;Frho;").

Lemma X_loopE_ex : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;Vkx;S72A2VL;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. destruct HLwf as (W1 & W2 & W3). destruct Fnb as [Fnb1 Fnb2]. pose proof Fa0 as Fa13. destruct F3n as [F3nx F3f].
  destruct HTwf as (V1 & V2 & V3). destruct HUwf as (Y1 & Y2 & Y3).

  eapply JT_erun; [exact Hrun1 | exact W2 | exact W1 | exact W3 |].
  intros Lf rho1 [<-|[]] Hag1. cbn [la_state].
  apply etriple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho1 sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF | exact HspfE]. }

  eapply (etriple_conseq (P := SPA segs (JT kx ndE0) CfzE rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof (SPA_split segs (JT kx ndE0) rho1 Efz iw (SLit (- fz_frame)) S1 tp w F1 HS) as HS1.
    assert (HS2 : SPA segs (JT kx ndE0) (mkAX S2 (ax_X Efz) (ax_base Efz)) rho1 tp w).
    { rewrite <- F2e. change (mkAX (set_obj_at S1 iw O_WfzT) (ax_X Efz) (ax_base Efz)) with (ax_setS (mkAX S1 (ax_X Efz) (ax_base Efz)) (set_obj_at S1 iw O_WfzT)).
      apply (SPA_reslice segs (JT kx ndE0) rho1 (mkAX S1 (ax_X Efz) (ax_base Efz)) iw O_WloT O_WfzT tp w F2n); try reflexivity.
      - cbn [ax_S]. rewrite F2e. exact F2s.
      - unfold O_WloT, O_WfzT, spT. rewrite !obj_range_lits by (unfold WDP, DEEP, fz_frame; lia).
        rewrite !U_add_lit by (unfold fz_frame; try lia; rewrite U_add_lit by lia; lia). unfold WDP, DEEP, fz_frame. f_equal; lia.
      - unfold O_WfzT, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold WDP, DEEP, fz_frame; lia). unfold WDP, DEEP, fz_frame; lia.
      - exact HS1. }
    assert (HS3 : SPA segs (JT kx ndE0) (mkAX S3 (ax_X Efz) (ax_base Efz)) rho1 tp w).
    { rewrite <- F2a. change (mkAX (add_obj S2 O_payE) (ax_X Efz) (ax_base Efz)) with (ax_setS (mkAX S2 (ax_X Efz) (ax_base Efz)) (add_obj (ax_S (mkAX S2 (ax_X Efz) (ax_base Efz))) O_payE)).
      apply (SPA_add_empty segs (JT kx ndE0) rho1 (mkAX S2 (ax_X Efz) (ax_base Efz)) O_payE tp w); [cbn [ax_S]; rewrite F2a; exact F2w | reflexivity | reflexivity | cbn [ax_S]; exact F2o | | exact HS2].
      intros _. unfold O_payE, obj_hi_of, obj_lo_of. cbn [ob_hi ob_lo ob_base eval]. rewrite !soff_lit_small by lia. rewrite lit_unsigned. unfold EMPTY. cbn. lia. }
    pose proof (SPA_x_publish_empty segs (JT kx ndE0) rho1 (mkAX S3 (ax_X Efz) (ax_base Efz)) EMPTY tp w ltac:(unfold EMPTY; lia) eq_refl HS3) as HS4.
    unfold CfzE. change (mkAX S3 (ax_X Efz ++ [X_payE]) (ax_base Efz)) with (ax_setX (ax_setX (mkAX S3 (ax_X Efz) (ax_base Efz)) ((SLit EMPTY, SLit 0) :: ax_X (mkAX S3 (ax_X Efz) (ax_base Efz)))) (ax_X Efz ++ [X_payE])).
    apply SPA_x_sub; [| exact HS4]. cbn [ax_X ax_setX]. intros r Hr. apply in_app_or in Hr as [Hr|[<-|[]]]; [right; exact Hr | left; reflexivity]. }

  assert (HnxC : ss_next (ax_S CfzE) = ss_next (ax_S Efz)) by (unfold CfzE; cbn [ax_S]; exact F3nx).
  unfold ndE0, keptE.

  assert (Fnbc : bd_below (ss_next (ax_S Efz)) (bd_subst (s_fz CfzE) bd_fz) = true).
  { pose proof (proj1 (Pos.leb_le _ _) Fnx) as Hnf. unfold NF in Hnf. unfold bd_fz, bd_subst, bi_subst, lf_subst, bd_below, vLEN. cbn [map forallb bi_f fst snd atom_subst asv sv_subst].
    rewrite Fa13. unfold vPlen. cbn [sv_below]. try (assert (E : (44 <? ss_next (ax_S Efz))%positive = true) by (apply Pos.ltb_lt; lia); rewrite E). reflexivity. }
  apply (box_open_Te segs AInv CST XGL ALA NF (KcT kx) rhoT P0T [] [] PTrue BX0 [(vB, vCap)] [] bd0 (bd_subst (s_fz CfzE) bd_fz) bd1 CfzE rho1 tp _ (BXnn_mk00 0) Fpay).
  { intros _. pose proof (Hcapbd rho1) as HC. assert (LMP : 0 <= LARGE_MIN) by (unfold LARGE_MIN; lia). cbn [length]. lia. }
  intros BXc HBXc Hback.
  rewrite <- (app_nil_r [(vB, vCap)]).
  apply (client_callA_ex segs AInv CST XGL ALA HCST HXGL NF (KcT kx) rhoT P0T [] [] BXc PTrue (Kc_okT T0 MD HMDvm kx) HBXc
           (P0_fz CST) PTrue (fun _ H => H) (fun _ _ _ H => H) Pre_fz nd_fz0 PD_fz NF eq_refl eq_refl eq_refl
           (fun FBc FFc BXc rho2 tp2 HB => HFZ FBc FFc BXc rho2 tp2 HB) eq_refl
           CfzE (s_fz CfzE) Rfz (ax_X CfzE) rho1 tp [(vB, vCap)] [] [] (bd_subst (s_fz CfzE) bd_fz) [] ANone Q
           Fxk Ffr Fcc Ftp Fdom).
  - rewrite HnxC. exact Fnx.
  - rewrite HnxC. pose proof (nd_below_split _ _ Fnb1) as (N1 & N2 & _ & N4). pose proof (nd_below_len _ _ Fnb1) as N5. cbn [nd_tv nd_fr nd_bd nd_am] in N1, N2, N4, N5. apply nd_below_intro; cbn [nd_tv nd_fr nd_bd nd_am]; [exact N1 | exact N2 | exact Fnbc | exact N4 | exact N5].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply payA_self. reflexivity.
  - rewrite HnxC. unfold CfzE in Fpd. cbn [ax_S] in Fpd. rewrite F3nx in Fpd. exact Fpd.
  -
    intros Ai ms HF' HP0 Hav HB HFF HN HD HZ HFR HM HTPA HTok. rewrite app_nil_r in HN, HD, HZ.
    split; [eapply robjs_okF_drv; [exact HF' | exact FspfC | exact (T0_of_site _ _ _ HTPA HTok) | exact Fknz | exact Fro]|].
    split; [eapply xrs_okF_drv; [exact HF' | exact FspfC | exact (T0_of_site _ _ _ HTPA HTok) | exact Fknz | exact Fxr]|].
    unfold P0_fz. split; [|intros c; reflexivity].
    intros a Ha. exfalso. unfold uval, vDAT, vLEN in Ha. cbn [eval] in Ha. rewrite !rw_call' in Ha. rewrite Fa13 in Ha.
    cbn [eval] in Ha. rewrite lit_unsigned in Ha. change (0 mod 2 ^ 64) with 0 in Ha. lia.
  -
    intros d rho' tp' [<-|[]] Hag'. cbn [fst snd nd_tv nd_bd nd_am nd_fz1 import_tv bd_subst am_subst map app].
    unfold T_afterA3. rewrite import_postA3_full. fold (T_afterA Pre_fz CfzE (s_fz CfzE) Rfz P_fz). rewrite FTT.
    fold keptE. fold ndE1.

    eapply (etriple_conseq (P := SPA segs (JT kx ndE1) TT rho' tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { exact (box_close segs AInv CST XGL NF (KcT kx) rhoT P0T [] [] PTrue BX0 BXc bd1 keptE [] [] ANone (ss_next (ax_S CfzE)) TT rho1 rho' tp' w (BXnn_mk00 0) Hback Hag' ltac:(rewrite HnxC; exact Fnb2) HS). }

    apply etriple_factsA. intros HF2.
    assert (Hsp' : 0x7fff80000000 <= bv_unsigned (eval rho' sp0) <= 2 ^ 47 - 224).
    { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF2 | exact U1f]. }
    eapply (etriple_conseq (P := SPA segs (JT kx ndE1) Tfz rho' tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { assert (HS1 : SPA segs (JT kx ndE1) (ax_setS TT U1) rho' tp' w).
      { rewrite <- U1e. apply (SPA_reslice segs (JT kx ndE1) rho' TT 1 _ O_WloT tp' w U1n); try reflexivity.
        - rewrite U1e. exact U1s.
        - unfold O_WloT, spT. rewrite !obj_range_lits by (unfold WDP, DEEP, fz_frame; lia).
          rewrite !U_add_lit by (unfold fz_frame; try lia; rewrite U_add_lit by lia; lia). unfold WDP, DEEP, fz_frame. f_equal; lia.
        - unfold O_WloT, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP, fz_frame; lia). unfold DEEP, fz_frame; lia.
        - exact HS. }
      pose proof (AxXform.SPA_select segs (JT kx ndE1) rho' (mkAX U1 (ax_X TT) (ax_base TT)) _ tp' w U2 HS1) as HS2.
      pose proof (SPA_merge segs (JT kx ndE1) rho' (mkAX (set_objs U1 (select (ss_objs U1) ([1; 0] ++ seq 2 (length (ss_objs U1) - 2))%nat)) (ax_X TT) (ax_base TT)) 0 U3 tp' w U3e HS2) as HS3.
      pose proof (SPA_drop_empty segs (JT kx ndE1) rho' (mkAX U3 (ax_X TT) (ax_base TT)) 1 _ tp' w U4n
                    ltac:(intros _; unfold obj_hi_of, obj_lo_of; cbn [ob_hi ob_lo]; apply Z.le_refl) HS3) as HS4.
      cbn [ax_S ax_setS ax_X ax_base] in HS4. rewrite U4e in HS4.
      rewrite <- UT. unfold dropX. apply SPA_x_sub; [cbn [ax_X]; apply In_dropX | exact HS4]. }

    eapply JT_erun; [exact Hrun2 | exact V2 | exact V1 | exact V3 |].
    intros Lf rho2 [<-|[]] Hag2. cbn [la_state].
    apply etriple_factsA. intros HF3.

    eapply (etriple_conseq (P := SPA segs (JT kx ndE1) CpfE rho2 tp')); [intros w HS | intros w' Hw'; exact Hw' |].
    { pose proof (SPA_split segs (JT kx ndE1) rho2 Epf 0 (SLit (- PW)) P1 tp' w P1e HS) as HS1.
      assert (HS2 : SPA segs (JT kx ndE1) Cpf0E rho2 tp' w).
      { pose proof (carveT (KcT kx) ndE1 (mkAX P1 (ax_X Epf) (ax_base Epf)) rho2 tp' w N_pf (ss_next P1) HS1) as X.
        cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X; [exact P2w | apply Pos.leb_refl | exact HbE | exact P2c]. }
      unfold CpfE, ax_add_facts.
      change (ax_setS Cpf0E (add_facts (pf_hints Cpf0E k) (ax_S Cpf0E))) with (ax_with_facts Cpf0E (pf_hints Cpf0E k ++ ss_facts (ax_S Cpf0E))).
      apply (SPA_refacts_JA segs); [exact HS2 | exact P3b |].
      intros tr md HJ HFc. apply Forall_app. split; [|exact HFc]. apply Forall_forall. intros q Hq.
      destruct (P3h q Hq) as [x ->]. apply ms16_holds. }

    assert (HnxP : ss_next (ax_S CpfE) = ss_next (ax_S Epf)).
    { unfold CpfE, Cpf0E, ax_add_facts. cbn [ax_S ss_next add_facts P1cE]. exact P2n. }
    set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JT kx ndE1 rho2 t tr md).
    assert (JpK : forall r t tr md, Jp r t tr md -> MD md /\ tr = T0 ++ EVk kx) by (intros r t tr md HJ; exact (JT_Kc _ _ _ _ _ _ HJ)).
    assert (HstJp : stableA segs NF Jp).
    { intros r r' t tr md md' Hag Hme HJ. unfold Jp in HJ |- *. destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF (KcT kx) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm kx) ALA (ss_next (ax_S CpfE)) ndE1 Ai kc rho2 rho2 t tr md md');
        [apply Pos.leb_le; exact Pnx | exact Pnb | apply agree_below_refl | exact Hme | exact HJi]. }
    assert (CONT : forall Lf rho3, In Lf (Posts_pf k) -> agree_below (ss_next (ax_S CpfE)) rho2 rho3 ->
              etriple segs (SPA segs (JT kx' ndE1) (ax_add_facts (ss_facts (ax_S CpfE)) (import_postA (s_pf CpfE k) (PreP k) (la_state Lf) CpfE Rpf)) rho3 tp') Q).
    { intros Lf rho3 HinL Hag3. unfold Posts_pf in HinL. destruct HinL as [<-|[]]. cbn [la_state].
      fold (T_afterA (PreP k) CpfE (s_pf CpfE k) Rpf (P_pf k)). rewrite PTP.

      eapply (etriple_conseq (P := fun w => exists rho4, SPA segs (JT kx' ndE1) Upf rho4 tp' w)); [intros w HS | intros w' Hw'; exact Hw' |].
      { destruct w as [tr [ms md]].
        pose proof (AxXform.SPA_select segs (JT kx' ndE1) rho3 TP _ tp' _ Q1e HS) as HS1. rewrite Q1o, Q1d in HS1.
        pose proof (uncarveT (KcT kx') ndE1 (mkAX Q1 (ax_X TP) (ax_base TP)) rho3 tp' tr ms md _ N_pf (Kc_okT T0 MD HMDvm kx') Q1s Q2u eq_refl Q2n HS1) as HS2.
        cbn [ax_S ax_setS ax_X ax_base] in HS2. rewrite Q2e in HS2.
        set (rho4 := rho_absorb rho3 (map lc_obj N_pf) (vms md tp' ms)) in HS2. exists rho4.
        pose proof (AxXform.SPA_select segs (JT kx' ndE1) rho4 (mkAX Q2 (ax_X TP) (ax_base TP)) _ tp' _ Q3e HS2) as HS3.
        pose proof (SPA_merge segs (JT kx' ndE1) rho4 (mkAX (set_objs Q2 (select (ss_objs Q2) ([8; 0] ++ seq 1 7 ++ seq 9 (length (ss_objs Q2) - 9))%nat)) (ax_X TP) (ax_base TP)) 0 Q4 tp' _ Q4e HS3) as HS4.
        rewrite <- QU. exact HS4. }
      apply etriple_ex. intros rho4.

      eapply JT_erun; [exact Hrun3 | exact Y2 | exact Y1 | exact Y3 |].
      intros Lf rho5 HinLf Hag5.
      destruct (Hleaves Lf HinLf) as [(s5 & E1 & E2 & E3 & E4 & E5 & E6)|HX]; [|apply HX].
      eapply (etriple_conseq (P := SPA segs (JT kx' ndE1) Lnext (rho_sub rho5 s5) tp')); [intros w HS | intros w' Hw'; exact Hw' | apply Hnext].
      apply (JT_entails kx' (la_state Lf) Lnext s5 ndE1 ndE1 rho5 tp' w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS). }
    destruct Pk as [(Ek & Ekx & Ekx')|(Hkok & Ekx & Ekx')].
    +
      subst kx kx'. unfold PreP in *. rewrite Ek in *. cbn [Z.eqb] in *.
      apply (pcallT (KcT 0) (KcT 1) CpfE Pre_pf0 (s_pf CpfE 0) Rpf (Posts_pf 0) rho2 tp' ndE1 Jp (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.Kw Jp 2) Q (Kc_okT T0 MD HMDvm 1)).
      * intros rho6 tp6. apply (printf0_sum_ex Jp HstJp). intros r t tr md HJ. apply HMDfd1. exact (proj1 (JpK _ _ _ _ HJ)).
      * exact Pfr.
      * exact Pcc.
      * exact Pnx.
      * exact Pnb.
      * exact Pfb.
      * intros tr ms md Hsm HJ. exact HJ.
      * intros rhoL tr' md' (tr0 & HJ & ->). unfold Jp in HJ. destruct HJ as (Ai & kc & Hav & [Hmd Htr] & REST).
        exists Ai, kc. split; [exact Hav|]. split; [|exact REST]. split; [exact Hmd|]. rewrite Htr. cbn [EVk]. rewrite app_nil_r. reflexivity.
      * exact CONT.
    +
      subst kx kx'.
      assert (EP : PreP k = Pre_pf k).
      { unfold PreP. destruct Hkok as [->|[->| ->]]; reflexivity. }
      rewrite EP in *.
      apply (pcallT (KcT 1) (KcT 1) CpfE (Pre_pf k) (s_pf CpfE k) Rpf (Posts_pf k) rho2 tp' ndE1 Jp Jp Q (Kc_okT T0 MD HMDvm 1)).
      * intros rho6 tp6. apply (printf_sum_ex Jp HstJp k rho6 tp6 Hkok).
      * exact Pfr.
      * exact Pcc.
      * exact Pnx.
      * exact Pnb.
      * exact Pfb.
      * intros tr ms md Hsm HJ. exact HJ.
      * intros rhoL tr' md' HJ. exact HJ.
      * exact CONT.
Qed.
End LoopE.

Section ExitFreeP.
Variable kx : nat.
Variable n : Z.
Variables bd1 bdJ : list bitem.
Definition keptX : list (sv * sv) := ltac2:(tb__ "0|1|
SfScS18S18A2M0S12S18S18S22S7fA1SaaA4SfG0S12S18S18Sa8Sa9A4SaG0A1A3A3").
Definition ndLX : ndesc := ltac2:(tb__ "0|0|
S5aS9eSaScScS18S42A2S18A2A1Vbd1;S59A4").
Definition ndJX : ndesc := ltac2:(tb__ "0|1|
S5aSfScS18S18A2M0S12S18S18Sa8Sa9A4SaG0A1A3SaScScS18S42A2S18A2A1VbdJ;S59A4").
Variables (LX : axst) (R : list sobj) (T : axst) (leaves : list leafA).
Definition CP : axst := ltac2:(tb__ "0|0|
Sb4S12S18S18S22S7fA1SaaA4VLX;A2").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0SdS9S19A1M0A1Se5S9dSaeS87S9dA1A3SeG0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S0S7Se6S9dSaeS87S9dA1VR;SfS38Sb3SaS38A1A3A5S8A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S0S7S102S44S87S9dA1A2S8A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S7S6aS44S1aS36VLX;A1A1A2S8A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S1S0S7S57S1aS36VLX;A1A1M0Sa0A2S8A3S0S7Sf9G0VbdJ;A2S8A3A2").
Hypothesis Hs12 : ltac2:(tb__ "0|1|
S1S0S18SdeS87S9dA1M0PcA2S22S7fA1A3S0S18SdeG0PdA2SaaA3A2").
Hypothesis Hpay : ltac2:(tb__ "0|0|
S0S7SfaS1bS36S9dA1A1S1fZ0A1SfdVbd1;VbdJ;A5S8A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S0S7SbaS1bS36S9dA1A1A1S8A3").
Hypothesis Hro : ltac2:(tb__ "0|0|
S0S7SbdS1bS36S9dA1A1S9eSeSbU0A2VR;A4S8A3").
Hypothesis Hxr : ltac2:(tb__ "0|1|
S0S7SbeS1bS36S9dA1M0A1S9eSeSbU0A2S1eG0A1SbbS39S9dA1A6S8A3").
Hypothesis HvP : ltac2:(tb__ "0|0|
S0S7Sa4S20S2fS2eS1fZ1000A1S22S7fA1A2A1S1bS36S9dA1A1A3S8A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S38S101SaeS9dS87S9dA1VR;Sb3A5VT;A3").
Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S6aS44S1aS36VT;A1M0A1M1A2S8A3S1S0S7S21G0A1S13A3S0S7S57G1S9fA2S8A3A2A2").
Hypothesis Hrun : ltac2:(tb__ "0|1|
S0SdS9S37A1M0A1S3cS41Sb2Sb1VT;S8A5SeG0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|5|
S37Sa2S37R1Vleaves;A3S2SddSddS1S0S7S3fS3bR3A1M0S82Vn;S1fZ0A1A2R1A3S8A3S1S0S7SdfR1S44A2S8A3S1S0S7S6aS44S1aS36G0A1M1A1M2A2S8A3S1S0S7S57G2S9fA2S8A3S1S0S7S11cR1SfScS18S18A2M3S12S18S18Sa8Sa9A4SaG3A1A3M4G4A3S8A3S0S7Sf8S1bG1A1Sf7R1VbdJ;A2VbdJ;A3S8A3A2A2A2A2A2Ls;A2F_;FLf;").

Variable CondJ : Prop.
Hypothesis Hcond : ltac2:(tb__ "0|0|
S1dS7cS20S24R1A1S1bS36VLX;A1A1A3VP0T;VrhoT;A1S132S44VrhoT;R3A3VCondJ;F_;F_;F_;Frho;").
Hypothesis HJ : ltac2:(tb__ "0|0|
VCondJ;S1dS9S45Q40A1A1S67S41S48S41VJT;Vkx;S9fA2S82Vn;S1fZ0A1A2R2R1A5VQ;A3Ftp;Frho;F_;").

Lemma X_freeP_ex : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;Vkx;Sa0A2VLX;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. destruct Hnb as [Hnb1 Hnb2]. destruct Hs12 as [Hs12a Hs13]. destruct HTwf as (V1 & V2 & V3).
  apply etriple_factsA. intros HF. apply etriple_JT_pre. intros HP0' Hav'. pose proof (Hcond rho HF HP0' Hav') as HC.
  eapply (etriple_conseq (P := SPA segs (JT kx ndLX) CP rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { unfold CP, dropX. apply SPA_x_sub; [|exact HS]. apply In_dropX. }
  assert (HnxC : ss_next (ax_S CP) = ss_next (ax_S LX)) by reflexivity.
  unfold ndLX, keptX.
  apply (free_callA_ex segs AE_A AInv CST XGL ALA HCST HXGL NF (KcT kx) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm kx) [] UStopLe CP (s_fp CP) R rho tp
           (NDA [(SVar vP, vPlen); (vB, vCap)] [] bd1 ANone) 0%nat (SVar vP, vPlen) bdJ Q free_shape_nil ACX Hfr Hcc HcT).
  - rewrite HnxC. exact Hnx.
  - rewrite HnxC. exact Hnb1.
  - rewrite HnxC. exact Hnb2.
  - reflexivity.
  - apply payA_of_bud_pay. exact Hpay.
  - intros A A' _ _. exact I.
  - apply (site_ok_drv (NDA [(SVar vP, vPlen); (vB, vCap)] [] bd1 ANone) CP (s_fp CP) R rho (Some 0%nat) (Some (uval rho (wsub_get (s_fp CP) 12%positive)))); try assumption.
    + intros Ai HF' HN HZ. exists (SVar vP, vPlen). split; [reflexivity|]. rewrite Hs12a.
      assert (Hnz : tnz rho (SVar vP, vPlen)).
      { unfold tnz. cbn [fst]. pose proof (holds_mem _ _ _ HF' HvP) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X.
        rewrite Z.mod_small in X by lia. unfold uval in *. lia. }
      split; [exact Hnz | reflexivity].
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. split; [|split; [| exact I]].
      * unfold tnz. cbn [fst]. pose proof (holds_mem _ _ _ HF' HvP) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X.
        rewrite Z.mod_small in X by lia. lia.
      * rewrite Hs12a, Hs13. reflexivity.
  - intros rho' tp'. unfold PreF, PostF in HT. rewrite HT. cbn [nd_tv nd_fr nd_am remove_nth]. fold ndJX.
    eapply JT_erun; [exact Hrun | exact V2 | exact V1 | exact V3 |].
    intros Lf rho2 HinLf Hag2. destruct (Hleaves Lf HinLf) as (s5 & E1 & E2 & E3 & E4 & E5 & E6).
    eapply (etriple_conseq (P := SPA segs (JT kx ndJX) (J_E n (SLit 0)) (rho_sub rho2 s5) tp')); [intros w HS | intros w' Hw'; exact Hw' | apply (HJ HC)].
    apply (JT_entails kx (la_state Lf) (J_E n (SLit 0)) s5 ndJX ndJX rho2 tp' w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS).
Qed.
End ExitFreeP.

Section ExitFreeE.
Variable kx : nat.
Variable n : Z.
Variables bd1 bdJ : list bitem.
Definition ndEX : ndesc := ltac2:(tb__ "0|1|
S5aSfScS18S18A2M0S12S18S18Sa8Sa9A4SaG0A1A3SaScScS18S42A2S18A2A1Vbd1;S59A4").
Definition ndJE : ndesc := ltac2:(tb__ "0|1|
S5aSfScS18S18A2M0S12S18S18Sa8Sa9A4SaG0A1A3SaScScS18S42A2S18A2A1VbdJ;S59A4").
Variables (LX : axst) (R : list sobj) (T : axst) (leaves : list leafA).
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0SdS9S19A1M0A1Se5VLX;S8dS8bVLX;A1A3SeG0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S0S7Se6VLX;S8dS8bVLX;A1VR;SfS38S92SaS38A1A3A5S8A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S0S7S102S44S8bVLX;A1A2S8A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S7S6aS44S1aS36VLX;A1A1A2S8A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S1S0S7S57S1aS36VLX;A1A1M0S13aA2S8A3S0S7Sf9G0VbdJ;A2S8A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|1|
S0S7SfaS1bS36VLX;A1A1S1fZ0M0A1G0Vbd1;VbdJ;A5S8A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S0S7SbaS1bS36VLX;A1A1A1S8A3").
Hypothesis Hro : ltac2:(tb__ "0|1|
S0S7SbdS1bS36VLX;A1A1SfScS18S18A2M0S12S18S18Sa8Sa9A4SaG0A1A3S14SbA1VR;A4S8A3").
Hypothesis Hxr : ltac2:(tb__ "0|2|
S0S7SbeS1bS36VLX;A1M0A1SfScS18S18A2M1S12S18S18Sa8Sa9A4SaG1A1A3S14SbA1S1eG0A1SbbS39VLX;A1A6S8A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S38S101S8dVLX;S8bVLX;A1VR;S92A5VT;A3").
Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S6aS44S1aS36VT;A1M0A1M1A2S8A3S1S0S7S21G0A1S13A3S0S7S57G1S139A2S8A3A2A2").
Hypothesis Hrun : ltac2:(tb__ "0|1|
S0SdS9S37A1M0A1S3cS41Sb2Sb1VT;S8A5SeG0Vleaves;A2A3").
Hypothesis Hleaves : ltac2:(tb__ "0|5|
S37Sa2S37R1Vleaves;A3S2SddSddS1S0S7S3fS3bR3A1M0S82Vn;S1fZ0A1A2R1A3S8A3S1S0S7SdfR1S44A2S8A3S1S0S7S6aS44S1aS36G0A1M1A1M2A2S8A3S1S0S7S57G2S139A2S8A3S1S0S7S11cR1SfScS18S18A2M3S12S18S18Sa8Sa9A4SaG3A1A3M4G4A3S8A3S0S7Sf8S1bG1A1Sf7R1VbdJ;A2VbdJ;A3S8A3A2A2A2A2A2Ls;A2F_;FLf;").
Variable CondJ : Prop.
Hypothesis Hcond : ltac2:(tb__ "0|0|
S1dS7cS20S24R1A1S1bS36VLX;A1A1A3VP0T;VrhoT;A1S132S44VrhoT;R3A3VCondJ;F_;F_;F_;Frho;").
Hypothesis HJ : ltac2:(tb__ "0|0|
VCondJ;S1dS9S45Q40A1A1S67S41S48S41VJT;Vkx;S139A2S82Vn;S1fZ0A1A2R2R1A5VQ;A3Ftp;Frho;F_;").

Lemma X_freeE_ex : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;Vkx;S13aA2VLX;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. destruct Hnb as [Hnb1 Hnb2]. destruct HTwf as (V1 & V2 & V3).
  apply etriple_factsA. intros HF. apply etriple_JT_pre. intros HP0' Hav'. pose proof (Hcond rho HF HP0' Hav') as HC.
  unfold ndEX.
  apply (free_null_callA_ex segs AE_A AInv CST XGL ALA HCST HXGL NF (KcT kx) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm kx) [] UStopLe LX (s_fn LX) R rho tp
           (NDA [(vB, vCap)] [] bd1 ANone) bdJ Q eq_refl ACX Hfr Hcc HcT Hnx Hnb1 Hnb2).
  - apply payA_of_bud_pay. exact Hpay.
  - intros A A' _. exact I.
  - apply (site_ok_drv (NDA [(vB, vCap)] [] bd1 ANone) LX (s_fn LX) R rho None None); try assumption.
    + intros Ai HF' HN HZ. exact I.
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. exact I.
  - intros rho' tp'. unfold PreFN, PostFN in HT. rewrite HT. cbn [nd_tv nd_fr nd_am]. fold ndJE.
    eapply JT_erun; [exact Hrun | exact V2 | exact V1 | exact V3 |].
    intros Lf rho2 HinLf Hag2. destruct (Hleaves Lf HinLf) as (s5 & E1 & E2 & E3 & E4 & E5 & E6).
    eapply (etriple_conseq (P := SPA segs (JT kx ndJE) (J_E n (SLit 0)) (rho_sub rho2 s5) tp')); [intros w HS | intros w' Hw'; exact Hw' | apply (HJ HC)].
    apply (JT_entails kx (la_state Lf) (J_E n (SLit 0)) s5 ndJE ndJE rho2 tp' w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS).
Qed.
End ExitFreeE.

Section SegMC.
Variable bd0 : list bitem.
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S5aS12aSaScScS18S42A2S18A2A1Vbd0;S59A4").
Variables (TM Emc : axst) (W1 W2 B1 B2 B3 RS : sstate) (i0 i1 i2 : nat) (Rmc : list sobj) (TMC : axst).
Variables (V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 : sstate) (Umc Lp : axst) (sLP : wsub) (LP0 : axst)  .

Hypothesis HTwf : ltac2:(tb__ "0|2|
S1S0S7S6aS44S1aS36VTM;A1M0A1M1A2S8A3S1S0S7S21G0A1S13A3S0S7S57G1SdbA2S8A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S0SdS9S37A1M0A1S3cS41S96S8cVTM;S8A5SeG0SfS37S3eVEmc;Sa7A2SaS37A1A3A2A3").

Hypothesis M1 : ltac2:(tb__ "0|0|
S0SdS1cA1Se2S36VEmc;A1U0S1fN870A1A3SeS1cVW1;A2A3").
Hypothesis M2 : ltac2:(tb__ "0|0|
S0SdS1cA1Se2VW1;U0S1fN8c0A1A3SeS1cVW2;A2A3").
Hypothesis M3 : ltac2:(tb__ "0|0|
S0SdS1cA1Se2VW2;Vi0;S1fZ6A1A3SeS1cVB1;A2A3").
Hypothesis M4 : ltac2:(tb__ "0|0|
S0SdS1cA1Se2VB1;Vi1;S12eSb8S1fZ6A1A2A3SeS1cVB2;A2A3").
Hypothesis M5 : ltac2:(tb__ "0|0|
S0SdS1cA1Se2VB2;Vi2;Sb9A3SeS1cVB3;A2A3").

Hypothesis M6b : ltac2:(tb__ "0|0|
S0S7Sa1S20S23S1aVB3;A1A1S10S20S99S1bVB3;A1A3A3S8A3").
Hypothesis M6z : ltac2:(tb__ "0|0|
S0S7SbcS1bVB3;A1S12aA2S8A3").
Definition B3h : sstate := add_facts mc_hints B3.
Definition B3c : sstate := ltac2:(tb__ "0|0|
S27S2aSd9A1S2bSd9A1S29Sd9A1S28Sd9A1S2cSd9A1S10S19S1eSd9A1S7aSd1S19Sd2SedA4A3S1bSd9A1S1aSd9A1S21Sd9A1A9").
Hypothesis M6w : swf B3c = true.
Hypothesis M6c : ltac2:(tb__ "0|0|
S0S7Sd4S1bSd9A1S1eSd9A1S39VEmc;A1Sc4Sc6S5cSdbA1SedA7S8A3").
Hypothesis M6x : ltac2:(tb__ "0|1|
S1S0S43S1aVB3;A1S1aS36VEmc;A1M0A1A3S0S9S20A1S1bVB3;A1S1bG0A1A3A2").
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S18S3aVEmc;A1S1fS135A1A3").
Hypothesis M7n : ltac2:(tb__ "0|0|
S0SdS19A1Sa3S19S1eSdcA1Vi2;A3SeS19Sf1A2A3").
Hypothesis M7e : ltac2:(tb__ "0|0|
S0S1cS110SdcVi2;S91A3VRS;A3").
Hypothesis M7s : ltac2:(tb__ "0|0|
S0S7S10fSdcVRS;A2S8A3").
Hypothesis M7f : ltac2:(tb__ "0|1|
S1S0S7Sf2S1bS36VEmc;A1M0A1A1S8A3S0S43S1aVRS;A1S1aG0A1A3A2").
Definition Cmc : axst := ltac2:(tb__ "0|0|
S3dVRS;S39VEmc;A1S3aVEmc;A1A3").

Hypothesis Cfr : ltac2:(tb__ "0|1|
S0SdS9S19A1M0A1Se5SdaS13bS8eSdaA1A3SeG0VRmc;A2A3").
Hypothesis Ccc : ltac2:(tb__ "0|0|
S0S7Se7SdaS13bS8eSdaA1VRmc;S7aS37S38S3bS13dA4A5S8A3").
Hypothesis Cnx : ltac2:(tb__ "0|0|
S0S7S6aS44S1aS36SdaA1A1A2S8A3").
Hypothesis Cnb : ltac2:(tb__ "0|0|
S0S7S57S1aS36SdaA1A1SdbA2S8A3").
Hypothesis Cfb : ltac2:(tb__ "0|1|
S0S7Sa1S20S23S1aS36SdaA1M0A1A1S1bG0A1A3S8A3").
Hypothesis ChB : ltac2:(tb__ "0|0|
S0S7Sa4S20S2fS2eS1fZ1000A1Sa8A2A1S1bS36SdaA1A1A3S8A3").
Hypothesis CT : ltac2:(tb__ "0|0|
S0S38S101S13bSdaS8eSdaA1VRmc;S13cA5VTMC;A3").

Hypothesis V1e : ltac2:(tb__ "0|4|
S1S0S7SeaS11S19S1eS36VTMC;A1M0A1M1A2M2S9bG2A1M3A2S8A3S0S1cSa6G0Se4G1G3A2A2VV1;A3A2").
Hypothesis V2e : ltac2:(tb__ "0|2|
S1S0S9S19A1S1eVV1;A1M0S10S19S7dS19Sa5S11S19G0A2U3A2G0A3M1S7aSd1S19Sd2SedA4A3A3S1S0S1cSa6VV1;G1A2VV2;A3S1S0S7Sd5Sc4SedA2S8A3S0S7S57S1aVV1;A1SdbA2S8A3A2A2A2").
Hypothesis V3e : ltac2:(tb__ "0|1|
S1S0SdS19A1Sa3S19S1eVV2;A1U3M0A3SeS19S91A2A3S1S0S1cS110VV2;G0Sf1A3VV3;A3S1S0S7S10fVV2;VV3;A2S8A3S0S7Sf2S1bVV2;A1A1S8A3A2A2A2").
Hypothesis V4e : ltac2:(tb__ "0|1|
S1S0SdS19A1Sa3S19S1eVV3;A1U1M0A3SeS19S26S12eSb0S1fN940A1A2S1fN50A1S1fZ0A1SaS25A1S2dA5A2A3S1S0S1cS110VV3;G0S98A3VV4;A3S1S0S7S10fVV3;VV4;A2S8A3S0S7SbaS1bVV3;A1A1S8A3A2A2A2").
Hypothesis V5e : ltac2:(tb__ "0|3|
S1S0S7SeaS11S19S1eVV4;A1M0A2M1S9cG1A1M2A2S8A3S0S1cSa6VV4;Se4G0G2A2A2VV5;A3A2").
Hypothesis V6e : ltac2:(tb__ "0|0|
S0SdS1cA1Se3VV5;U0A2SeS1cVV6;A2A3").
Hypothesis V7e : ltac2:(tb__ "0|0|
S0SdS1cA1Se3VV6;U0A2SeS1cVV7;A2A3").
Hypothesis V8e : ltac2:(tb__ "0|2|
S1S0S7SeaS11S19S1eVV7;A1M0A2S9aG0A1M1A2S8A3S0S1cSa6VV7;Se4G0G1A2A2VV8;A3A2").
Hypothesis V9e : ltac2:(tb__ "0|2|
S1S0SdS1cA1M0Se3VV8;U0M1A2SeS1cVV9;A2A3S1S0G0Se3VV9;G1A2SeS1cVV10;A2A3S0G0Se3VV10;G1A2SeS1cVV11;A2A3A2A2").
Hypothesis VU : ltac2:(tb__ "0|0|
S0S38S3dVV11;S39VTMC;A1S3aVTMC;A1A3VUmc;A3").

Hypothesis HUwf : ltac2:(tb__ "0|2|
S1S0S7S6aS44S1aS36VUmc;A1M0A1M1A2S8A3S1S0S7S21G0A1S13A3S0S7S57G1SdbA2S8A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S0SdS9S37A1M0A1S3cS41S97S8cVUmc;S8A5SeG0SfS37S3eVLp;Sa7A2SaS37A1A3A2A3").
Hypothesis HLp : ltac2:(tb__ "0|2|
S1S0S7S3fVLp;VLP0;VsLP;A3S8A3S1S0S7SdfVsLP;S44A2S8A3S1S0S7S6aS44S1aS36VLp;A1M0A1M1A2S8A3S1S0S7S57G1SdbA2S8A3S1S0S7S11cVsLP;S12aS12aA3S8A3S0S7Sf8S1bG0A1Sf7VsLP;Vbd0;A2Vbd0;A3S8A3A2A2A2A2A2").
Hypothesis Hnext : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;U0SdbA2VLP0;R2R1A5VQ;A3Ftp;Frho;").

Lemma X_mc_ex : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;U0SdbA2VTM;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. destruct HTwf as (W1' & W2' & W3'). destruct M6x as [M6nx M6fx]. destruct M7f as [M6f1 M7nx]. destruct HUwf as (Y1 & Y2 & Y3).
  destruct V1e as [V1a V1b]. destruct V2e as (V2a & V2b & V2c & V2d). destruct V3e as (V3a & V3b & V3c & V3d). destruct V4e as (V4a & V4b & V4c & V4d).
  destruct V5e as [V5a V5b]. destruct V8e as [V8a V8b]. destruct V9e as (V9a & V9b & V9c). destruct HLp as (E1 & E2 & E3 & E4 & E5 & E6).

  eapply JT_erun; [exact Hrun1 | exact W2' | exact W1' | exact W3' |].
  intros Lf rho1 [<-|[]] Hag1. cbn [la_state].
  apply etriple_factsA. intros HF.
  destruct (mc_src_range rho1 _ HF M6f1) as (RG & (L1 & L2) & L3 & L4 & L5).

  eapply (etriple_conseq (P := SPA segs (JT 0 ndM) Cmc rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof (SPA_split segs (JT 0 ndM) rho1 Emc 0 (SLit (-2160)) W1 tp w M1 HS) as HS1.
    pose proof (SPA_split segs (JT 0 ndM) rho1 (mkAX W1 (ax_X Emc) (ax_base Emc)) 0 (SLit (-2240)) W2 tp w M2 HS1) as HS2.
    pose proof (SPA_split segs (JT 0 ndM) rho1 (mkAX W2 (ax_X Emc) (ax_base Emc)) i0 (SLit 6) B1 tp w M3 HS2) as HS3.
    pose proof (SPA_split segs (JT 0 ndM) rho1 (mkAX B1 (ax_X Emc) (ax_base Emc)) i1 (add vClen (SLit 6)) B2 tp w M4 HS3) as HS4.
    pose proof (SPA_split segs (JT 0 ndM) rho1 (mkAX B2 (ax_X Emc) (ax_base Emc)) i2 vLen B3 tp w M5 HS4) as HS5.
    assert (HS5h : SPA segs (JT 0 ndM) (mkAX B3h (ax_X Emc) (ax_base Emc)) rho1 tp w).
    { unfold B3h. change (mkAX (add_facts mc_hints B3) (ax_X Emc) (ax_base Emc)) with (ax_with_facts (mkAX B3 (ax_X Emc) (ax_base Emc)) (mc_hints ++ ss_facts B3)).
    apply (SPA_refacts_JA segs); [exact HS5 | exact M6b |].
    intros tr md HJ HFc. apply Forall_app. split; [|exact HFc].

    assert (Hnz : tnz rho1 (SVar vP, vPlen)).
    { unfold tnz. cbn [fst]. unfold kept_nzb in M6z. cbn [forallb fst] in M6z. apply andb_prop in M6z as [Z1 _].
      pose proof (holds_mem _ _ _ HFc Z1) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X. rewrite Z.mod_small in X by lia.
      unfold uval, vP in *. cbn [fst eval] in X |- *. lia. }
    pose proof (JA_tv_facts segs AInv CST XGL NF (KcT 0) rhoT P0T [] [] BX0 PTrue ALA ndM rho1 tp tr md (SVar vP, vPlen) eq_refl HJ ltac:(left; reflexivity) Hnz) as TF.
    unfold tv_factsA in TF. cbn [fst snd] in TF.
    inversion TF as [| ? ? T1 TF2]; subst. inversion TF2 as [| ? ? _ TF3]; subst. inversion TF3 as [| ? ? T3 TF4]; subst.
    inversion TF4 as [| ? ? _ TF5]; subst. inversion TF5 as [| ? ? _ TF6]; subst. inversion TF6 as [| ? ? T6 TF7]; subst.
    inversion TF7 as [| ? ? T7 TF8]; subst. inversion TF8 as [| ? ? T8 _]; subst.
    unfold mc_hints. constructor; [exact T1 | constructor; [exact T3 | constructor; [exact T6 | constructor; [exact T8 | constructor; [exact T7 | constructor]]]]]. }
    assert (HS6 : SPA segs (JT 0 ndM) (mkAX B3c (ax_X Emc) (ax_base Emc)) rho1 tp w).
    { pose proof (carveT (KcT 0) ndM (mkAX B3h (ax_X Emc) (ax_base Emc)) rho1 tp w N_mc (ss_next B3h) HS5h) as X.
      cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X; [exact M6w | apply Pos.leb_refl | exact HbE | exact M6c]. }
    unfold Cmc. rewrite <- M7e. change (mkAX (set_obj_at B3c i2 O_srcT) (ax_X Emc) (ax_base Emc)) with (ax_setS (mkAX B3c (ax_X Emc) (ax_base Emc)) (set_obj_at B3c i2 O_srcT)).
    apply (SPA_reslice segs (JT 0 ndM) rho1 (mkAX B3c (ax_X Emc) (ax_base Emc)) i2 O_srcM O_srcT tp w M7n); try reflexivity.
    - cbn [ax_S]. rewrite M7e. exact M7s.
    - exact RG.
    - exact L2.
    - exact L3.
    - exact HS6. }

  assert (HnxC : ss_next (ax_S Cmc) = ss_next (ax_S Emc)) by exact M7nx.
  apply etriple_factsA. intros HFC.
  set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JT 0 ndM rho1 t tr md /\ clsZ r 15 16 /\ clsZ r 19 52).
  assert (JpK : forall r t tr md, Jp r t tr md -> MD md /\ tr = T0 ++ EVk 0) by (intros r t tr md (HJ & _); exact (JT_Kc _ _ _ _ _ _ HJ)).
  assert (HstJp : stableA segs NF Jp).
  { intros r r' t tr md md' Hag Hme (HJ & C1 & C2). unfold Jp. split; [|split].
    - destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF (KcT 0) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm 0) ALA (ss_next (ax_S Cmc)) ndM Ai kc rho1 rho1 t tr md md');
        [apply Pos.leb_le; exact Cnx | exact Cnb | apply agree_below_refl | exact Hme | exact HJi].
    - unfold clsZ in C1 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact C1.
    - unfold clsZ in C2 |- *. rewrite <- !(proj1 Hag) by (unfold NF; lia). exact C2. }
  apply (pcallT (KcT 0) (KcT 0) Cmc Pre_mc0 (s_mc Cmc) Rmc Posts_mc rho1 tp ndM Jp Jp Q (Kc_okT T0 MD HMDvm 0)).
  - intros rho6 tp6. apply (memcpy_icpt_sum_ex Jp rho6 tp6 HstJp).
    + intros r t tr md (_ & C1 & _). exact C1.
    + intros r t tr md (_ & _ & C2). exact C2.
  - exact Cfr.
  - exact Ccc.
  - exact Cnx.
  - exact Cnb.
  - exact Cfb.
  -
    intros tr ms md Hsm HJ. unfold Jp. split; [exact HJ|].
    assert (Hnz : tnz rho1 (SVar vP, vPlen)).
    { unfold tnz. cbn [fst]. unfold kept_nzb in M6z. cbn [forallb fst] in M6z. apply andb_prop in M6z as [Z1 _]. rewrite M6fx in Z1.
      pose proof (holds_mem _ _ _ HF Z1) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X. rewrite Z.mod_small in X by lia.
      unfold uval, vP in X |- *. cbn [fst eval] in X |- *. lia. }
    assert (HnzB : tnz rho1 (vB, vCap)).
    { unfold tnz, vB. cbn [fst eval]. pose proof (holds_mem _ _ _ HFC ChB) as X. unfold vB in X. cbn [holds eval] in X.
      rewrite lit_unsigned, Z.mod_small in X by lia. lia. }
    split; apply band_free_clsZ; rewrite !rw_call'.
    + change (wsub_get (s_mc Cmc) 15%positive) with (SVar vP). change (wsub_get (s_mc Cmc) 16%positive) with vPlen.
      exact (JT_tv_band_free _ 0 ndM rho1 tp tr md (SVar vP, vPlen) HJ ltac:(left; reflexivity) Hnz).
    + change (wsub_get (s_mc Cmc) 19%positive) with vB. change (wsub_get (s_mc Cmc) 52%positive) with vCap.
      exact (JT_tv_band_free _ 0 ndM rho1 tp tr md (vB, vCap) HJ ltac:(right; left; reflexivity) HnzB).
  - intros rhoL tr' md' (HJ & _). exact HJ.
  -
    intros Lf rho3 HinL Hag3. unfold Posts_mc in HinL. destruct HinL as [<-|[]]. cbn [la_state].
    fold (T_afterA Pre_mc0 Cmc (s_mc Cmc) Rmc P_icpt). rewrite CT.
    eapply (etriple_conseq (P := fun w => exists rho4, SPA segs (JT 0 ndM) Umc rho4 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
    { destruct w as [tr [ms md]].
      pose proof (AxXform.SPA_select segs (JT 0 ndM) rho3 TMC _ tp _ V1a HS) as HS1. rewrite V1b in HS1.
      pose proof (uncarveT (KcT 0) ndM (mkAX V1 (ax_X TMC) (ax_base TMC)) rho3 tp tr ms md _ N_mc (Kc_okT T0 MD HMDvm 0) V2a V2c eq_refl V2d HS1) as HS2.
      cbn [ax_S ax_setS ax_X ax_base] in HS2. rewrite V2b in HS2.
      set (rho4 := rho_absorb rho3 (map lc_obj N_mc) (vms md tp ms)) in HS2. exists rho4.
      destruct HS2 as [HS2a HS2b]. pose proof (conj HS2a HS2b : SPA segs (JT 0 ndM) (mkAX V2 (ax_X TMC) (ax_base TMC)) rho4 tp (tr, mkCfg ms md)) as HS2. clear HS2a HS2b.
      assert (HF4 : Forall (holds rho4) (ss_facts V2)) by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (proj1 HS2))))))))))))).
      destruct (mc_src_range rho4 _ HF4 V3d) as (RG' & _ & _ & L4' & L5').
      assert (HS3 : SPA segs (JT 0 ndM) (mkAX V3 (ax_X TMC) (ax_base TMC)) rho4 tp (tr, mkCfg ms md)).
      { rewrite <- V3b. change (mkAX (set_obj_at V2 3 O_srcM) (ax_X TMC) (ax_base TMC)) with (ax_setS (mkAX V2 (ax_X TMC) (ax_base TMC)) (set_obj_at V2 3 O_srcM)).
        apply (SPA_reslice segs (JT 0 ndM) rho4 (mkAX V2 (ax_X TMC) (ax_base TMC)) 3 O_srcT O_srcM tp _ V3a); try reflexivity.
        - cbn [ax_S]. rewrite V3b. exact V3c.
        - symmetry. exact RG'.
        - exact L4'.
        - exact L5'.
        - exact HS2. }
      assert (HF5 : Forall (holds rho4) (ss_facts V3)) by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (proj1 HS3))))))))))))).
      assert (Hsp4 : 0x7fff80000000 <= bv_unsigned (eval rho4 sp0) <= 2 ^ 47 - 224).
      { unfold sp0. cbn [eval]. eapply (fun r f HF0 Hb => proj1 (sp0_facts_sound r f HF0 Hb)); [exact HF5 | exact V4d]. }
      assert (HS4 : SPA segs (JT 0 ndM) (mkAX V4 (ax_X TMC) (ax_base TMC)) rho4 tp (tr, mkCfg ms md)).
      { rewrite <- V4b. change (mkAX (set_obj_at V3 1 O_cstkB) (ax_X TMC) (ax_base TMC)) with (ax_setS (mkAX V3 (ax_X TMC) (ax_base TMC)) (set_obj_at V3 1 O_cstkB)).
        apply (SPA_reslice segs (JT 0 ndM) rho4 (mkAX V3 (ax_X TMC) (ax_base TMC)) 1 _ O_cstkB tp _ V4a); try reflexivity.
        - cbn [ax_S]. rewrite V4b. exact V4c.
        - unfold O_cstkB, spT. rewrite !obj_range_lits by lia. rewrite !U_add_lit by (try lia; rewrite U_add_lit by lia; lia). f_equal; lia.
        - unfold O_cstkB, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by lia. lia.
        - exact HS3. }
      pose proof (AxXform.SPA_select segs (JT 0 ndM) rho4 (mkAX V4 (ax_X TMC) (ax_base TMC)) _ tp _ V5a HS4) as HS5. cbn [ax_S ax_X ax_base] in HS5. rewrite V5b in HS5.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V5 (ax_X TMC) (ax_base TMC)) 0 V6 tp _ V6e HS5) as HS6.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V6 (ax_X TMC) (ax_base TMC)) 0 V7 tp _ V7e HS6) as HS7.
      pose proof (AxXform.SPA_select segs (JT 0 ndM) rho4 (mkAX V7 (ax_X TMC) (ax_base TMC)) _ tp _ V8a HS7) as HS8. cbn [ax_S ax_X ax_base] in HS8. rewrite V8b in HS8.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V8 (ax_X TMC) (ax_base TMC)) 0 V9 tp _ V9a HS8) as HS9.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V9 (ax_X TMC) (ax_base TMC)) 0 V10 tp _ V9b HS9) as HS10.
      pose proof (SPA_merge segs (JT 0 ndM) rho4 (mkAX V10 (ax_X TMC) (ax_base TMC)) 0 V11 tp _ V9c HS10) as HS11.
      rewrite <- VU. exact HS11. }
    apply etriple_ex. intros rho4.

    eapply JT_erun; [exact Hrun2 | exact Y2 | exact Y1 | exact Y3 |].
    intros Lf rho5 [<-|[]] Hag5. cbn [la_state].
    eapply (etriple_conseq (P := SPA segs (JT 0 ndM) LP0 (rho_sub rho5 sLP) tp)); [intros w HS | intros w' Hw'; exact Hw' | apply Hnext].
    apply (JT_entails 0%nat Lp LP0 sLP ndM ndM rho5 tp w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS).
Qed.
End SegMC.

Lemma JT_edge_ex : ltac2:(tb__ "0|3|
SbS38S9ScS18S18A2A1S9SfbA1M0G0S38S1dS9S45Q40A1A1M1S0S7Sf0R7R6R5R4R3A5S8A3S1dG1S67S41S48S41VJT;RbS5aR9SaScScS18S42A2S18A2A1M2R7S59A4A2RaR2R1A5VQ;A3Ftp';Frho';S67S41S48S41VJT;RaS5aR8G2R7S59A4A2R5R4R3A5VQ;A3F_;F_;Ftp;Frho;FLf;Fbdj;Fbdi;Ftv;FLnext;Fk;").
Proof.
  intros k Lnext tv bdi bdj Lf rho tp H Hn. destruct (edge_okb_sound _ _ _ _ _ H) as (s5 & E1 & E2 & E3 & E4 & E5 & E6).
  eapply (etriple_conseq (P := SPA segs (JT k (NDA tv [] bdj ANone)) Lnext (rho_sub rho s5) tp)); [intros w HS | intros w' Hw'; exact Hw' | apply Hn].
  apply (JT_entails k Lf Lnext s5 (NDA tv [] bdi ANone) (NDA tv [] bdj ANone) rho tp w E1 E2 E3 E4 E5 eq_refl E6 eq_refl HS).
Qed.

Section MallocSiteEx.

Variables (Em : axst) (R : list sobj) (Tk : axst).
Hypothesis Mfr : ltac2:(tb__ "0|1|
S0SdS9S19A1M0A1Se5VEm;S89S85VEm;A1A3SeG0VR;A2A3").
Hypothesis McO : ltac2:(tb__ "0|0|
S0S7Se6VEm;S89S85VEm;A1VR;SfS38S113S112SaS115A1S114A3SaS38A1A3A5S8A3").
Hypothesis McT : ltac2:(tb__ "0|0|
S0S7S102S44S85VEm;A1A2S8A3").
Hypothesis Mnx : ltac2:(tb__ "0|0|
S0S7S6aS44S1aS36VEm;A1A1A2S8A3").
Hypothesis Mnb : ltac2:(tb__ "0|1|
S1S0S7S57S1aS36VEm;A1A1M0SabA2S8A3S0S7Sf9G0SefA2S8A3A2").
Hypothesis Ms12 : ltac2:(tb__ "0|0|
S0S18SdeS85VEm;A1PcA2SaaA3").
Hypothesis Msv : ltac2:(tb__ "0|0|
S0S7S34S1aS36VEm;A1A1SaaA2S8A3").
Hypothesis Mres : ltac2:(tb__ "0|1|
S1S0S18SdeSe9S85VEm;A1S89S113S112SaS115A1S114A3VEm;A4S117A2S22S134S1aS36VEm;A1A1UaA2M0A1A3S0S43G0S7fA3A2").
Hypothesis Mpay : ltac2:(tb__ "0|0|
S0S7SfaS1bS36VEm;A1A1SaaSfdSafSefA5S8A3").
Hypothesis Mspf : ltac2:(tb__ "0|0|
S0S7SbaS1bS36VEm;A1A1A1S8A3").
Hypothesis Mro : ltac2:(tb__ "0|0|
S0S7SbdS1bS36VEm;A1A1SadS14SbA1VR;A4S8A3").
Hypothesis Mxr : ltac2:(tb__ "0|1|
S0S7SbeS1bS36VEm;A1M0A1SadS14SbA1S1eG0A1SbbS39VEm;A1A6S8A3").
Hypothesis Msz : ltac2:(tb__ "0|0|
S0S7Sf4S1bS36VEm;A1A1A1S8A3").
Hypothesis MTk : ltac2:(tb__ "0|0|
S0S38S101S89VEm;S85VEm;A1VR;S113S112SaS115A1S114A3A5VTk;A3").
Hypothesis HMC : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;U0S12cSefA1A2VTk;R2R1A5VQ;A3Ftp;Frho;").

Lemma X_msite_ex_ok : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;U0SabA2VEm;R2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. destruct Mnb as [Mnb1 Mnb2]. destruct Mres as [Mres1 Mres2].
  apply etriple_factsA. intros HF.
  pose proof (plen_facts_sound rho _ HF Msz) as HSZ. pose proof (plen_facts_sound26 rho _ HF Msz) as HSZ26.
  unfold nd_T.
  apply (malloc_callA_ex_S segs AE_A AInv CST XGL ALA HCST HXGL NF (KcT 0) rhoT P0T [] [] BX0 PTrue (Kc_okT T0 MD HMDvm 0) PTrue [] UStopLe Em (s_m Em) R rho tp
           (NDA tv_T [] bd_T ANone) bd_M Q malloc_shape_nil MSX Mfr McO McT Mnx Mnb1 Mnb2).
  - rewrite Ms12. exact Msv.
  - exact Mres1.
  - rewrite Ms12. apply payA_of_bud_pay. exact Mpay.
  - intros A A' _ _. exact I.
  - intros A kc _ _ HB. rewrite Ms12. cbn [nd_bd nd_am] in HB. exact (room_T A kc rho _ HSZ26 HB).
  - reflexivity.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - apply (site_ok_drv (NDA tv_T [] bd_T ANone) Em (s_m Em) R rho None None); try assumption.
    + intros Ai HF' HN HZ. exact I.
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. rewrite Ms12. split; [exact HSZ | exact I].
  - intros rho' tp'. unfold PreM in MTk. rewrite MTk, Mres2, Ms12. cbn [nd_tv nd_fr nd_am]. fold kept. fold (ndM bd_M). apply HMC.
Qed.
End MallocSiteEx.

Section SegT0.
Variables (S1 S2 : sstate) (EmA LeA LeB EmB : axst).
Hypothesis T1 : ltac2:(tb__ "0|0|
S0SdS1cA1Se2S36SacA1U0S1fNd0A1A3SeS1cVS1;A2A3").

Hypothesis T2 : ltac2:(tb__ "0|4|
S1S0S7S14bS41VS1;Sb7S1eVS1;A1S1fZ0M0A1S1fS13fA1A3M1S108S13fZ4A2M2Z1M3G0A6S8A3S0S1cS14aVS1;G1G2G3G0A5VS2;A3A2").
Hypothesis T1w : ltac2:(tb__ "0|1|
S1S0S7S6aS44S1aVS2;A1M0A2S8A3S1S0S7S21VS2;A1S13A3S0S7S57G0SabA2S8A3A2A2").
Hypothesis Trun : ltac2:(tb__ "0|1|
S0SdS9S37A1M0A1S3cS41S95S8cS3dVS2;S39SacA1S3aSacA1A3S8A5SeG0SfS37S3eVEmA;Sa7A2SfS37S3eVLeA;Sa7A2SfS37S3eVLeB;Sa7A2SfS37S3eVEmB;Sa7A2SaS37A1A3A3A3A3A2A3").
Hypothesis HmA : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;U0SabA2VEmA;R2R1A5VQ;A3Ftp;Frho;").
Hypothesis HmB : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;U0SabA2VEmB;R2R1A5VQ;A3Ftp;Frho;").
Variables LEA LEB : axst.
Hypothesis HeA : ltac2:(tb__ "0|0|
S0S7Sf0VLEA;SadSafSeeZ0A1VLeA;A5S8A3").
Hypothesis HeB : ltac2:(tb__ "0|0|
S0S7Sf0VLEB;SadSafSeeZ0A1VLeB;A5S8A3").
Hypothesis HLEA : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;U0S12bSeeZ0A1A1A2VLEA;R2R1A5VQ;A3Ftp;Frho;").
Hypothesis HLEB : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;U0S12bSeeZ0A1A1A2VLEB;R2R1A5VQ;A3Ftp;Frho;").

Lemma X_T0_ex : ltac2:(tb__ "0|0|
S1dS9S45Q40A1A1S67S41S48S41VJT;U0SabA2SacR2R1A5VQ;A3Ftp;Frho;").
Proof.
  intros rho tp. destruct T1w as (W1' & W2' & W3').
  eapply (etriple_conseq (P := SPA segs (JT 0 nd_T) (mkAX S1 (ax_X S_T) (ax_base S_T)) rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { exact (SPA_split segs (JT 0 nd_T) rho S_T 0 (SLit (-208)) S1 tp w T1 HS). }
  eapply (etriple_conseq (P := SPA segs (JT 0 nd_T) (mkAX S2 (ax_X S_T) (ax_base S_T)) rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { destruct T2 as [T2a T2b]. rewrite <- T2b. exact (SPA_img_cell segs (JT 0 nd_T) rho (mkAX S1 (ax_X S_T) (ax_base S_T)) _ _ 1 0 tp w T2a HS). }
  eapply JT_erun; [exact Trun | exact W2' | exact W1' | exact W3' |].
  intros Lf rho1 Hin Hag1. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [la_state].
  - apply HmA.
  - unfold nd_T. exact (JT_edge_ex 0%nat LEA tv_T bd_T (bd_E 0) LeA rho1 tp HeA HLEA).
  - unfold nd_T. exact (JT_edge_ex 0%nat LEB tv_T bd_T (bd_E 0) LeB rho1 tp HeB HLEB).
  - apply HmB.
Qed.
End SegT0.

End TLXE.
End DrvTLXe.

(* [comment removed for export] *)
Module DrvTLXie.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nat"; "nil"; "app"; "Some"; "cons"; "prod"; "option"; "length"; "false"; "pair"; "None"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "sym_runA"; "mkLeafA"; "la_state"; "ax_base"; "mkAX"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sstate"; "sobj"; "ss_next"; "ss_facts"; "SLit"; "ss_objs"; "sprop"; "ss_lenient"; "sprop_below"; "mkObj"; "swf"; "DUnknown"; "SVar"; "cell"; "SPUle"; "holds"; "sprop_eqb"; "obj_wf"; "odefault"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "w_tr"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "ExitEv"; "WriteEv"; "m_fs"; "FdEntry"; "FdChannel"; "VmState"; "fd_lookup"; "m_fds"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "ANone"; "NDA"; "PTrue"; "ndesc"; "nd_tv"; "JA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states"; "J_E"; "s_fz"; "L_P"; "L_E"; "s_m"; "CUTS_L"; "FUEL_L"; "PreM"; "PreP"; "s_pf"; "s_fp"; "O_WloT"; "pf_hints"; "pf_u1"; "s_fn"; "CUTS_T"; "E_mP1"; "E_mPc"; "PreFN"; "s_mc"; "vP"; "LX_E10"; "LX_Ec0"; "LX_Ec1"; "LX_Ec2"; "LX_Ec3"; "LX_P10"; "LX_Pc0"; "LX_Pc1"; "LX_Pc2"; "LX_Pc3"; "O_WfzT"; "O_payE"; "O_srcT"; "PostFN"; "T_mok1"; "T_mokc"; "WDP"; "FUEL_T0"; "FUEL_T1"; "FUEL_T2"; "O_cstkB"; "R_mP1"; "R_mPc"; "X_payE"; "mc_hints"; "sel_buf"; "sel_rtc_last"; "sel_win"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "le"; "lt"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX"; "bd_L"; "bd_E"; "bd_J"; "EVk"; "N_pf"; "bd_M"; "N_mc"; "O_srcM"; "mc_needb"; "ms16_shape"; "edge_okb"; "plen_factsb"; "@Corelib.Lists.ListDef"; "map"; "seq"; "firstn"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "KcT"; "JT"; "KV_T"; "KP_T"; "P0T"; "BX0"; "CST_drv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2"; "fuzz_one_sumE"; "P_fz"; "PD_fz"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g9.DrvTLXe"; "ndM"; "Cfz"; "CfzE"; "ndE1"; "ndL1"; "CP"; "kept"; "ndE0"; "ndJE"; "ndJX"; "Cmc"; "ndEX"; "ndL0"; "ndLX"; "Cpf"; "CpfE"; "keptE"; "B3c"; "Cpf0"; "Cpf0E"; "P1c"; "P1cE"; "keptX"; "B3h"; "X_T0_ex"; "X_freeE_ex"; "X_freeP_ex"; "X_join_ex"; "X_loopE_ex"; "X_loopP_ex"; "X_mc_ex"; "X_msite_ex_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "In"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "calls_of"; "vB"; "vCap"; "nd_T"; "S_T"; "vPlen"; "PreF"; "sp0"; "tv_T"; "CUTS_X"; "FUEL_X"; "PostF"; "bd_T"; "dropX"; "locate"; "vClen"; "vLen";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit"; "ch1"; "supported"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "sp0_factsb"; "drv_xrb"; "kept_nzb"; "robjs_checkD"; "xrs_checkD"; "drv_objb"; "ex_pipe"; "fb_pipe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "PEND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "Pre_fz"; "bd_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "call_checkA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "bd_below"; "bud_le"; "bud_pay"; "bsumV"; "KU"; "LARGE_MIN"; "SECCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "xr_tracked"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "robj_tracked"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "L_malloc_ok"; "UStopLe"; "ulink"; "V_RES"; "alloc_contractsA_ex"; "with_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "carve_okb"; "lc_obj"; "lcarve"; "uncarve_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "Pre_mc0"; "P_icpt"; "Posts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TR_INIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.PFAddr"; "PW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "P_pf"; "Posts_pf"; "kok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.FZAddr"; "fz_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "wsub_dom_below"; "pos_add_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pd_okA"; "pdescA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "drop_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueC"; "add_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS"; "malloc_contractA_strong_ex"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceS IfaceEx GlueM.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvSiteEx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvTLX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g9.DrvTLXe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g8.DrvTLXi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Section TLXIE.
Variable AInv : ltac2:(tb__ "0|0|
S11eS1eS6S42Q40A1A1S39OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S45S108VCST;R1A2S1S82Z0R2A2S83R2S111A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S45S108VXGL;R1A2S1S82Z0R2A2S83R2S111A2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S45S108S9cR1A2S108VCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Hypothesis ACX : ltac2:(tb__ "0|0|
S105S13S100VAInv;VCST;VXGL;A5").
Hypothesis MSX : ltac2:(tb__ "0|0|
S123S13S100VAInv;VCST;VXGL;A5").
Variable Q : world -> Prop.
Variable rhoT : valuation.
Variable F : list byte.
Variable T0 : list event.
Variable MD : Model -> Prop.
Hypothesis HMDvm : ltac2:(tb__ "0|0|
S39S3fVMD;R2A1VMD;S106R2R3A2A1F_;Fv;Fmd;").
Hypothesis HMDfd1 : ltac2:(tb__ "0|0|
S39VMD;R1A1S0SdS3dA1S40S41R2A1Sd8A2SaS3dS3eSd8A1A2A3F_;Fmd;").
Let JT' (k : nat) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S97VAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;S4aVk;Vnd;Aa").
Let X_loopP' := X_loopP_ex AInv CST XGL ALA HCST HXGL HLV HCSTok HCSTdrv HLPP Q rhoT F T0 MD HMDvm HMDfd1.
Let X_loopE' := X_loopE_ex AInv CST XGL ALA HCST HXGL HLV HCSTok HCSTdrv HLPP Q rhoT F T0 MD HMDvm HMDfd1.
Let X_freeP' := X_freeP_ex AInv CST XGL ALA HCST HXGL HCSTdrv ACX Q rhoT F T0 MD HMDvm.
Let X_freeE' := X_freeE_ex AInv CST XGL ALA HCST HXGL HCSTdrv ACX Q rhoT F T0 MD HMDvm.
Let X_join' : ltac2:(tb__ "0|6|
S7S6Sf0A1M0G0S45S1fS45S15S6S21A1M1S0SdS15A1Se1R7R6S4fR5R4A2A3SaS15R2A2A3S0SdG1A1Se0S49S8ScS1fS1fA2M2A1M3S8ScScS1fS45A2S1fA2A1M4R7S48A4R3R6R4A4SaG1R2A2A3Sc5ScS45S45A2S10S45S45R7R5A4Sd9A3S36S39VMD;R1A1S0S6S38A1S35R3A1S9S38S9S38VT0;S89ReA1A3S9S38S92S42Q8A1S38S3bSd8A1Se9RbA1A4SbS38S3aS43Q40M5R9A2S3cR2A1A2S8S38A1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;S1eS6S42G5A1A1S34S13S37S13S7S4bS97VAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;S4aR2R1AaLnd;Lk;ReS49SbG2S10S1fS1fSc8Sc9A4G3A3G4RdS48A4A2S4fRbRaA2R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;F_;FR;FEx;Fc;Fst;Fn;FbdX;FbdJ;Fkx;") := ltac2:(tb__ "0|0|
SbcVAInv;VCST;VXGL;VALA;VHCST;VHXGL;VHCSTdrv;VHLPP;VACX;VQ;VrhoT;VF;VT0;VMD;VHMDvm;VHMDfd1;A10").
Let X_mc' := X_mc_ex AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP Q rhoT F T0 MD HMDvm.
Let X_msite' : ltac2:(tb__ "0|9|
S15S6S21A1M0S15S0SdG0A1SecR3S56S53R3A1A3SaG0R2A2A3S0S5SedR4S56S53R4A1R3SbS15S101S100S8S103A1S102A3M1S8S15A1A3A5S4A3S0S5SfaS44S53R5A1A2S4A3S0S5S4eS44S22S14R6A1A1A2S4A3S1S0S5S47S22S14R7A1A1M2ScaA2S4A3S0S5Sf2G2S8bA2S4A3A2S0S1fSe6S53R8A1PcA2SccA3S0S5S33S22S14R9A1A1SccA2S4A3S1S0S1fSe6SefS53RaA1S56G1RaA4S104A2S2cS11aS22S14RaA1A1UaA2M3A1A3S0S46G3S63A3A2S0S5Sf4S23S14RbA1A1SccSf6Sd3S8bA5S4A3S0S5SdaS23S14RcA1A1A1S4A3S0S5SddS23S14RdA1A1ScfS11S7A1M4RcA4S4A3S0S5SdeS23S14ReA1M5A1ScfG4S25G5A1SdbS17ReA1A6S4A3S0S5S91S23S14RfA1A1A1S4A3S0S15Sf9S56R10S53R10A1RfG1A5ReA3S1eS6S42Q40A1A1M6S34S13S37S13S7S4bS97VAInv;VCST;VXGL;VrhoT;VF;VT0;VMD;S4aR2R1AaLnd;Lk;M7U0M8Sa1S8bA1A2R11R2R1A5VQ;A3Ftp;Frho;S1eG6S34S13S37S13G7G8ScaA2R14R2R1A5VQ;A3Ftp;Frho;FHMC;FMTk;FMsz;FMxr;FMro;FMspf;FMpay;FMres;FMsv;FMs12;FMnb;FMnx;FMcT;FMcO;FMfr;FTk;FR;FEm;") := ltac2:(tb__ "0|0|
Sc0VAInv;VCST;VXGL;VALA;VHCST;VHXGL;VHCSTdrv;VMSX;VQ;VrhoT;VF;VT0;VMD;VHMDvm;Ae").
Let X_T0' := X_T0_ex AInv CST XGL ALA Q rhoT F T0 MD HMDvm.

Lemma X_LP10_ex : ltac2:(tb__ "0|4|
S9dVAInv;VCST;VXGL;S96VT0;VMD;U0M0A3A4S1eS6S42Q40A1A1M1S34S13S37S13VJT';U1Sa5S86Z1A1A1A2S69R2R1A5VQ;A3Ftp;Frho;M2G2S1eG1S34S13S37S13VJT';G0SadS86Z0M3A1A1A2S51SfG3A2R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LP10_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58).
  apply (X_loopP' 0 0%nat 1%nat (bd_L 0) (bd_L 1) (bd_L_cap 0) (L_P false 0) LX_P10 E_fzP10 LP10_S1 LP10_S2 R_fzP10 TT_fzP10 LP10_U1 LP10_U3 T_fzP10 E_pfP10 LP10_P1 R_pfP10 T_pfP10 LP10_Q1 LP10_Q2 LP10_Q4 U_pfP10 [mkLeafA LX_P10 RsCut] LP10_iw
           A1 A2 A3 A4 A5 A6 A7 A8 HFZ A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A39 q Hq)) A40 A41 A42 A43 A44 (or_introl (conj eq_refl (conj eq_refl eq_refl))) A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57).
  - intros Lf Hin. destruct Hin as [<-|[]]. right; exact HLX.
  - exact Hnext.
Qed.

Lemma X_LPc0_ex : ltac2:(tb__ "0|5|
S9dVAInv;VCST;VXGL;S96VT0;VMD;U0M0A3A4S1eS6S42Q40A1A1M1S34S13S37S13VJT';U1Sa5S86Z1M2A1A1A2M3S6aR2R1A5VQ;A3Ftp;Frho;S1eG1S34S13S37S13G3S51S4S80Z0M4G2A2A2R2R1A5VQ;A3Ftp;Frho;S1eG1S34S13S37S13VJT';G0SadS86G4A1A1A2S51S4G4A2R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LPc0_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58).
  apply (X_loopP' 0 0%nat 1%nat (bd_L 0) (bd_L 1) (bd_L_cap 0) (L_P true 0) (L_P true (0 + 1)) E_fzPc0 LPc0_S1 LPc0_S2 R_fzPc0 TT_fzPc0 LPc0_U1 LPc0_U3 T_fzPc0 E_pfPc0 LPc0_P1 R_pfPc0 T_pfPc0 LPc0_Q1 LPc0_Q2 LPc0_Q4 U_pfPc0 [mkLeafA LB_Pc0 RsCut; mkLeafA LX_Pc0 RsCut] LPc0_iw
           A1 A2 A3 A4 A5 A6 A7 A8 HFZ A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A39 q Hq)) A40 A41 A42 A43 A44 (or_introl (conj eq_refl (conj eq_refl eq_refl))) A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57).
  - intros Lf Hin. destruct Hin as [<-|[<-|[]]]; [left; apply backedge_okb_sound; exact A58 | right; exact HLX].
  - exact Hnext.
Qed.

Lemma X_LPc1_ex : ltac2:(tb__ "0|4|
S9dVAInv;VCST;VXGL;S96VT0;VMD;U1M0A3A4S1eS6S42Q40A1A1M1S34S13S37S13VJT';G0Sa5S86Z2A1A1A2M2S6bR2R1A5VQ;A3Ftp;Frho;S1eG1S34S13S37S13G2S51S4S80Z1M3G3A2A2R2R1A5VQ;A3Ftp;Frho;S1eG1S34S13S37S13VJT';G0SadS86G3A1A1A2S51S4G3A2R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LPc1_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58).
  apply (X_loopP' 1 1%nat 1%nat (bd_L 1) (bd_L 2) (bd_L_cap 1) (L_P true 1) (L_P true (1 + 1)) E_fzPc1 LPc1_S1 LPc1_S2 R_fzPc1 TT_fzPc1 LPc1_U1 LPc1_U3 T_fzPc1 E_pfPc1 LPc1_P1 R_pfPc1 T_pfPc1 LPc1_Q1 LPc1_Q2 LPc1_Q4 U_pfPc1 [mkLeafA LB_Pc1 RsCut; mkLeafA LX_Pc1 RsCut] LPc1_iw
           A1 A2 A3 A4 A5 A6 A7 A8 HFZ A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A39 q Hq)) A40 A41 A42 A43 A44 (or_intror (conj (or_introl eq_refl) (conj eq_refl eq_refl))) A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57).
  - intros Lf Hin. destruct Hin as [<-|[<-|[]]]; [left; apply backedge_okb_sound; exact A58 | right; exact HLX].
  - exact Hnext.
Qed.

Lemma X_LPc2_ex : ltac2:(tb__ "0|4|
S9dVAInv;VCST;VXGL;S96VT0;VMD;U1M0A3A4S1eS6S42Q40A1A1M1S34S13S37S13VJT';G0Sa5S86Z3A1A1A2M2S6cR2R1A5VQ;A3Ftp;Frho;S1eG1S34S13S37S13G2S51S4S80Z2M3Z1A2A2R2R1A5VQ;A3Ftp;Frho;S1eG1S34S13S37S13VJT';G0SadS86G3A1A1A2S51S4G3A2R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LPc2_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58).
  apply (X_loopP' 2 1%nat 1%nat (bd_L 2) (bd_L 3) (bd_L_cap 2) (L_P true 2) (L_P true (2 + 1)) E_fzPc2 LPc2_S1 LPc2_S2 R_fzPc2 TT_fzPc2 LPc2_U1 LPc2_U3 T_fzPc2 E_pfPc2 LPc2_P1 R_pfPc2 T_pfPc2 LPc2_Q1 LPc2_Q2 LPc2_Q4 U_pfPc2 [mkLeafA LB_Pc2 RsCut; mkLeafA LX_Pc2 RsCut] LPc2_iw
           A1 A2 A3 A4 A5 A6 A7 A8 HFZ A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A39 q Hq)) A40 A41 A42 A43 A44 (or_intror (conj (or_intror (or_introl eq_refl)) (conj eq_refl eq_refl))) A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57).
  - intros Lf Hin. destruct Hin as [<-|[<-|[]]]; [left; apply backedge_okb_sound; exact A58 | right; exact HLX].
  - exact Hnext.
Qed.

Lemma X_LPc3_ex : ltac2:(tb__ "0|4|
S9dVAInv;VCST;VXGL;S96VT0;VMD;U1M0A3A4S1eS6S42Q40A1A1M1S34S13S37S13VJT';G0Sa5S86Z4A1A1A2S6dR2R1A5VQ;A3Ftp;Frho;M2G2S1eG1S34S13S37S13VJT';G0SadS86Z3M3A1A1A2S51S4G3A2R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LPc3_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58).
  apply (X_loopP' 3 1%nat 1%nat (bd_L 3) (bd_L 4) (bd_L_cap 3) (L_P true 3) LX_Pc3 E_fzPc3 LPc3_S1 LPc3_S2 R_fzPc3 TT_fzPc3 LPc3_U1 LPc3_U3 T_fzPc3 E_pfPc3 LPc3_P1 R_pfPc3 T_pfPc3 LPc3_Q1 LPc3_Q2 LPc3_Q4 U_pfPc3 [mkLeafA LX_Pc3 RsCut] LPc3_iw
           A1 A2 A3 A4 A5 A6 A7 A8 HFZ A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A39 q Hq)) A40 A41 A42 A43 A44 (or_intror (conj (or_intror (or_intror eq_refl)) (conj eq_refl eq_refl))) A45 A46 A47 A48 A49 A50 A51 A52 A53 A54 A55 A56 A57).
  - intros Lf Hin. destruct Hin as [<-|[]]. right; exact HLX.
  - exact Hnext.
Qed.

Lemma X_LE10_ex : ltac2:(tb__ "0|4|
S9dVAInv;VCST;VXGL;S96VT0;VMD;U0M0A3A4S1eS6S42Q40A1A1M1S34S13S37S13VJT';U1Sa4S87Z1A1A1A2S64R2R1A5VQ;A3Ftp;Frho;M2G2S1eG1S34S13S37S13VJT';G0Sa8S87Z0M3A1A1A2S52SfG3A2R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LE10_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58 & A59 & A60 & A61 & A62 & A63).
  apply (X_loopE' 0 0%nat 1%nat (bd_E 0) (bd_E 1) (bd_E_cap 0) (L_E false 0) LX_E10 E_fzE10 LE10_S1 LE10_S2 LE10_S3 R_fzE10 TT_fzE10 LE10_U1 LE10_U3 LE10_U4 T_fzE10 (SLit EMPTY) DUnknown E_pfE10 LE10_P1 R_pfE10 T_pfE10 LE10_Q1 LE10_Q2 LE10_Q4 U_pfE10 [mkLeafA LX_E10 RsCut] LE10_iw
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 HFZ A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A44 q Hq)) A45 A46 A47 A48 A49 (or_introl (conj eq_refl (conj eq_refl eq_refl))) A50 A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A61 A62).
  - intros Lf Hin. destruct Hin as [<-|[]]. right; exact HLX.
  - exact Hnext.
Qed.

Lemma X_LEc0_ex : ltac2:(tb__ "0|5|
S9dVAInv;VCST;VXGL;S96VT0;VMD;U0M0A3A4S1eS6S42Q40A1A1M1S34S13S37S13VJT';U1Sa4S87Z1M2A1A1A2M3S65R2R1A5VQ;A3Ftp;Frho;S1eG1S34S13S37S13G3S52S4S80Z0M4G2A2A2R2R1A5VQ;A3Ftp;Frho;S1eG1S34S13S37S13VJT';G0Sa8S87G4A1A1A2S52S4G4A2R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LEc0_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58 & A59 & A60 & A61 & A62 & A63).
  apply (X_loopE' 0 0%nat 1%nat (bd_E 0) (bd_E 1) (bd_E_cap 0) (L_E true 0) (L_E true (0 + 1)) E_fzEc0 LEc0_S1 LEc0_S2 LEc0_S3 R_fzEc0 TT_fzEc0 LEc0_U1 LEc0_U3 LEc0_U4 T_fzEc0 (SLit EMPTY) DUnknown E_pfEc0 LEc0_P1 R_pfEc0 T_pfEc0 LEc0_Q1 LEc0_Q2 LEc0_Q4 U_pfEc0 [mkLeafA LB_Ec0 RsCut; mkLeafA LX_Ec0 RsCut] LEc0_iw
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 HFZ A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A44 q Hq)) A45 A46 A47 A48 A49 (or_introl (conj eq_refl (conj eq_refl eq_refl))) A50 A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A61 A62).
  - intros Lf Hin. destruct Hin as [<-|[<-|[]]]; [left; apply backedge_okb_sound; exact A63 | right; exact HLX].
  - exact Hnext.
Qed.

Lemma X_LEc1_ex : ltac2:(tb__ "0|4|
S9dVAInv;VCST;VXGL;S96VT0;VMD;U1M0A3A4S1eS6S42Q40A1A1M1S34S13S37S13VJT';G0Sa4S87Z2A1A1A2M2S66R2R1A5VQ;A3Ftp;Frho;S1eG1S34S13S37S13G2S52S4S80Z1M3G3A2A2R2R1A5VQ;A3Ftp;Frho;S1eG1S34S13S37S13VJT';G0Sa8S87G3A1A1A2S52S4G3A2R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LEc1_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58 & A59 & A60 & A61 & A62 & A63).
  apply (X_loopE' 1 1%nat 1%nat (bd_E 1) (bd_E 2) (bd_E_cap 1) (L_E true 1) (L_E true (1 + 1)) E_fzEc1 LEc1_S1 LEc1_S2 LEc1_S3 R_fzEc1 TT_fzEc1 LEc1_U1 LEc1_U3 LEc1_U4 T_fzEc1 (SLit EMPTY) DUnknown E_pfEc1 LEc1_P1 R_pfEc1 T_pfEc1 LEc1_Q1 LEc1_Q2 LEc1_Q4 U_pfEc1 [mkLeafA LB_Ec1 RsCut; mkLeafA LX_Ec1 RsCut] LEc1_iw
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 HFZ A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A44 q Hq)) A45 A46 A47 A48 A49 (or_intror (conj (or_introl eq_refl) (conj eq_refl eq_refl))) A50 A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A61 A62).
  - intros Lf Hin. destruct Hin as [<-|[<-|[]]]; [left; apply backedge_okb_sound; exact A63 | right; exact HLX].
  - exact Hnext.
Qed.

Lemma X_LEc2_ex : ltac2:(tb__ "0|4|
S9dVAInv;VCST;VXGL;S96VT0;VMD;U1M0A3A4S1eS6S42Q40A1A1M1S34S13S37S13VJT';G0Sa4S87Z3A1A1A2M2S67R2R1A5VQ;A3Ftp;Frho;S1eG1S34S13S37S13G2S52S4S80Z2M3Z1A2A2R2R1A5VQ;A3Ftp;Frho;S1eG1S34S13S37S13VJT';G0Sa8S87G3A1A1A2S52S4G3A2R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LEc2_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58 & A59 & A60 & A61 & A62 & A63).
  apply (X_loopE' 2 1%nat 1%nat (bd_E 2) (bd_E 3) (bd_E_cap 2) (L_E true 2) (L_E true (2 + 1)) E_fzEc2 LEc2_S1 LEc2_S2 LEc2_S3 R_fzEc2 TT_fzEc2 LEc2_U1 LEc2_U3 LEc2_U4 T_fzEc2 (SLit EMPTY) DUnknown E_pfEc2 LEc2_P1 R_pfEc2 T_pfEc2 LEc2_Q1 LEc2_Q2 LEc2_Q4 U_pfEc2 [mkLeafA LB_Ec2 RsCut; mkLeafA LX_Ec2 RsCut] LEc2_iw
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 HFZ A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A44 q Hq)) A45 A46 A47 A48 A49 (or_intror (conj (or_intror (or_introl eq_refl)) (conj eq_refl eq_refl))) A50 A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A61 A62).
  - intros Lf Hin. destruct Hin as [<-|[<-|[]]]; [left; apply backedge_okb_sound; exact A63 | right; exact HLX].
  - exact Hnext.
Qed.

Lemma X_LEc3_ex : ltac2:(tb__ "0|4|
S9dVAInv;VCST;VXGL;S96VT0;VMD;U1M0A3A4S1eS6S42Q40A1A1M1S34S13S37S13VJT';G0Sa4S87Z4A1A1A2S68R2R1A5VQ;A3Ftp;Frho;M2G2S1eG1S34S13S37S13VJT';G0Sa8S87Z3M3A1A1A2S52S4G3A2R2R1A5VQ;A3Ftp;Frho;F_;F_;F_;").
Proof.
  intros HFZ HLX Hnext.
  pose proof LEc3_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37 & A38 & A39 & A40 & A41 & A42 & A43 & A44 & A45 & A46 & A47 & A48 & A49 & A50 & A51 & A52 & A53 & A54 & A55 & A56 & A57 & A58 & A59 & A60 & A61 & A62 & A63).
  apply (X_loopE' 3 1%nat 1%nat (bd_E 3) (bd_E 4) (bd_E_cap 3) (L_E true 3) LX_Ec3 E_fzEc3 LEc3_S1 LEc3_S2 LEc3_S3 R_fzEc3 TT_fzEc3 LEc3_U1 LEc3_U3 LEc3_U4 T_fzEc3 (SLit EMPTY) DUnknown E_pfEc3 LEc3_P1 R_pfEc3 T_pfEc3 LEc3_Q1 LEc3_Q2 LEc3_Q4 U_pfEc3 [mkLeafA LX_Ec3 RsCut] LEc3_iw
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 HFZ A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 (fun q Hq => ms16_shapeb_sound q (proj1 (forallb_forall _ _) A44 q Hq)) A45 A46 A47 A48 A49 (or_intror (conj (or_intror (or_intror eq_refl)) (conj eq_refl eq_refl))) A50 A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A61 A62).
  - intros Lf Hin. destruct Hin as [<-|[]]. right; exact HLX.
  - exact Hnext.
Qed.

Lemma X_XP10_ex : ltac2:(tb__ "0|5|
S0S45Sc7VF;A1S80Z0M0Z1M1A2M2A3S1eS6S42Q40A1A1M3S34S13S37S13VJT';U1M4SaaS88A1A2S4fG2S24G0A1A2R2R1A5VQ;A3Ftp;Frho;F_;S1eG3S34S13S37S13VJT';G4SaeS86G1A1A1A2S69R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XP10_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  apply (X_freeP' 1%nat (0 + 1) (bd_L 1) bd_J LX_P10 R_fp_P10 T_fp_P10 [mkLeafA LJa_P10 RsCut; mkLeafA LJb_P10 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14
           (fun Lf Hin => backedge_okb_sound (J_E (0 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A15 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 0 + 1) (fun rho HF HP0 Hav => exit1_sound rhoT F rho _ HF A16 HP0 Hav) HJ).
Qed.

Lemma X_XPc0_ex : ltac2:(tb__ "0|5|
S0S45Sc7VF;A1S80Z0M0Z1M1A2M2A3S1eS6S42Q40A1A1M3S34S13S37S13VJT';U1M4SaaS88A1A2S4fG2S24G0A1A2R2R1A5VQ;A3Ftp;Frho;F_;S1eG3S34S13S37S13VJT';G4SaeS86G1A1A1A2S6aR2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XPc0_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  apply (X_freeP' 1%nat (0 + 1) (bd_L 1) bd_J LX_Pc0 R_fp_Pc0 T_fp_Pc0 [mkLeafA LJa_Pc0 RsCut; mkLeafA LJb_Pc0 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14
           (fun Lf Hin => backedge_okb_sound (J_E (0 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A15 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 0 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 0 rho _ ltac:(lia) HF A16 HP0 Hav) HJ).
Qed.

Lemma X_XPc1_ex : ltac2:(tb__ "0|4|
S0S45Sc7VF;A1S80Z1M0G0A2M1A3S1eS6S42Q40A1A1M2S34S13S37S13VJT';U1M3SaaS88A1A2S4fG1S24Z0A1A2R2R1A5VQ;A3Ftp;Frho;F_;S1eG2S34S13S37S13VJT';G3SaeS86Z2A1A1A2S6bR2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XPc1_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  apply (X_freeP' 1%nat (1 + 1) (bd_L 2) bd_J LX_Pc1 R_fp_Pc1 T_fp_Pc1 [mkLeafA LJa_Pc1 RsCut; mkLeafA LJb_Pc1 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14
           (fun Lf Hin => backedge_okb_sound (J_E (1 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A15 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 1 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 1 rho _ ltac:(lia) HF A16 HP0 Hav) HJ).
Qed.

Lemma X_XPc2_ex : ltac2:(tb__ "0|3|
S0S45Sc7VF;A1S80Z2Z1A2M0A3S1eS6S42Q40A1A1M1S34S13S37S13VJT';U1M2SaaS88A1A2S4fG0S24Z0A1A2R2R1A5VQ;A3Ftp;Frho;F_;S1eG1S34S13S37S13VJT';G2SaeS86Z3A1A1A2S6cR2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XPc2_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  apply (X_freeP' 1%nat (2 + 1) (bd_L 3) bd_J LX_Pc2 R_fp_Pc2 T_fp_Pc2 [mkLeafA LJa_Pc2 RsCut; mkLeafA LJb_Pc2 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14
           (fun Lf Hin => backedge_okb_sound (J_E (2 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A15 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 2 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 2 rho _ ltac:(lia) HF A16 HP0 Hav) HJ).
Qed.

Lemma X_XPc3_ex : ltac2:(tb__ "0|3|
S0S45Sc7VF;A1S80Z3Z1A2M0A3S1eS6S42Q40A1A1M1S34S13S37S13VJT';U1M2SaaS88A1A2S4fG0S24Z0A1A2R2R1A5VQ;A3Ftp;Frho;F_;S1eG1S34S13S37S13VJT';G2SaeS86Z4A1A1A2S6dR2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XPc3_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  apply (X_freeP' 1%nat (3 + 1) (bd_L 4) bd_J LX_Pc3 R_fp_Pc3 T_fp_Pc3 [mkLeafA LJa_Pc3 RsCut; mkLeafA LJb_Pc3 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14
           (fun Lf Hin => backedge_okb_sound (J_E (3 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A15 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 3 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 3 rho _ ltac:(lia) HF A16 HP0 Hav) HJ).
Qed.

Lemma X_XE10_ex : ltac2:(tb__ "0|5|
S0S45Sc7VF;A1S80Z0M0Z1M1A2M2A3S1eS6S42Q40A1A1M3S34S13S37S13VJT';U1M4Sa9S88A1A2S4fG2S24G0A1A2R2R1A5VQ;A3Ftp;Frho;F_;S1eG3S34S13S37S13VJT';G4SacS87G1A1A1A2S64R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XE10_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  apply (X_freeE' 1%nat (0 + 1) (bd_E 1) bd_J LX_E10 R_fn_E10 T_fn_E10 [mkLeafA LJEa_E10 RsCut; mkLeafA LJEb_E10 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
           (fun Lf Hin => backedge_okb_sound (J_E (0 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A13 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 0 + 1) (fun rho HF HP0 Hav => exit1_sound rhoT F rho _ HF A14 HP0 Hav) HJ).
Qed.

Lemma X_XEc0_ex : ltac2:(tb__ "0|5|
S0S45Sc7VF;A1S80Z0M0Z1M1A2M2A3S1eS6S42Q40A1A1M3S34S13S37S13VJT';U1M4Sa9S88A1A2S4fG2S24G0A1A2R2R1A5VQ;A3Ftp;Frho;F_;S1eG3S34S13S37S13VJT';G4SacS87G1A1A1A2S65R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XEc0_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  apply (X_freeE' 1%nat (0 + 1) (bd_E 1) bd_J LX_Ec0 R_fn_Ec0 T_fn_Ec0 [mkLeafA LJEa_Ec0 RsCut; mkLeafA LJEb_Ec0 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
           (fun Lf Hin => backedge_okb_sound (J_E (0 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A13 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 0 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 0 rho _ ltac:(lia) HF A14 HP0 Hav) HJ).
Qed.

Lemma X_XEc1_ex : ltac2:(tb__ "0|4|
S0S45Sc7VF;A1S80Z1M0G0A2M1A3S1eS6S42Q40A1A1M2S34S13S37S13VJT';U1M3Sa9S88A1A2S4fG1S24Z0A1A2R2R1A5VQ;A3Ftp;Frho;F_;S1eG2S34S13S37S13VJT';G3SacS87Z2A1A1A2S66R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XEc1_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  apply (X_freeE' 1%nat (1 + 1) (bd_E 2) bd_J LX_Ec1 R_fn_Ec1 T_fn_Ec1 [mkLeafA LJEa_Ec1 RsCut; mkLeafA LJEb_Ec1 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
           (fun Lf Hin => backedge_okb_sound (J_E (1 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A13 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 1 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 1 rho _ ltac:(lia) HF A14 HP0 Hav) HJ).
Qed.

Lemma X_XEc2_ex : ltac2:(tb__ "0|3|
S0S45Sc7VF;A1S80Z2Z1A2M0A3S1eS6S42Q40A1A1M1S34S13S37S13VJT';U1M2Sa9S88A1A2S4fG0S24Z0A1A2R2R1A5VQ;A3Ftp;Frho;F_;S1eG1S34S13S37S13VJT';G2SacS87Z3A1A1A2S67R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XEc2_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  apply (X_freeE' 1%nat (2 + 1) (bd_E 3) bd_J LX_Ec2 R_fn_Ec2 T_fn_Ec2 [mkLeafA LJEa_Ec2 RsCut; mkLeafA LJEb_Ec2 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
           (fun Lf Hin => backedge_okb_sound (J_E (2 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A13 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 2 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 2 rho _ ltac:(lia) HF A14 HP0 Hav) HJ).
Qed.

Lemma X_XEc3_ex : ltac2:(tb__ "0|3|
S0S45Sc7VF;A1S80Z3Z1A2M0A3S1eS6S42Q40A1A1M1S34S13S37S13VJT';U1M2Sa9S88A1A2S4fG0S24Z0A1A2R2R1A5VQ;A3Ftp;Frho;F_;S1eG1S34S13S37S13VJT';G2SacS87Z4A1A1A2S68R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HJ. pose proof XEc3_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  apply (X_freeE' 1%nat (3 + 1) (bd_E 4) bd_J LX_Ec3 R_fn_Ec3 T_fn_Ec3 [mkLeafA LJEa_Ec3 RsCut; mkLeafA LJEb_Ec3 RsCut] A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
           (fun Lf Hin => backedge_okb_sound (J_E (3 + 1) (SLit 0)) [(vB, vCap)] bd_J (la_state Lf)
                            (proj1 (forallb_forall _ _) A13 (la_state Lf) ltac:(destruct Hin as [<-|[<-|[]]]; cbn; tauto)))
           (calls_of F = 3 + 1) (fun rho HF HP0 Hav => exitc_sound rhoT F 3 rho _ ltac:(lia) HF A14 HP0 Hav) HJ).
Qed.

Lemma X_MC1_ex : ltac2:(tb__ "0|3|
S1eS6S42Q40A1A1M0S34S13S37S13VJT';U0Sa1S86Z0M1A1A1A2M2S51SfG1A2R2R1A5VQ;A3Ftp;Frho;S1eG0S34S13S37S13G2S72R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros Hnext. pose proof MC1_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37).
  exact (X_mc' (bd_L 0) T_mok1 E_mc1 MC1_W1 MC1_W2 MC1_B1 MC1_B2 MC1_B3 MC1_RS MC1_i0 MC1_i1 MC1_i2 R_mc1 T_mc1
           MC1_V1 MC1_V2 MC1_V3 MC1_V4 MC1_V5 MC1_V6 MC1_V7 MC1_V8 MC1_V9 MC1_V10 MC1_V11 U_mc1 L_P1 MC1_s (L_P false 0)
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 Hnext).
Qed.

Lemma X_MCc_ex : ltac2:(tb__ "0|3|
S1eS6S42Q40A1A1M0S34S13S37S13VJT';U0Sa1S86Z0M1A1A1A2M2S51S4G1A2R2R1A5VQ;A3Ftp;Frho;S1eG0S34S13S37S13G2S73R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros Hnext. pose proof MCc_facts as FACTS. destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30 & A31 & A32 & A33 & A34 & A35 & A36 & A37).
  exact (X_mc' (bd_L 0) T_mokc E_mcc MCc_W1 MCc_W2 MCc_B1 MCc_B2 MCc_B3 MCc_RS MCc_i0 MCc_i1 MCc_i2 R_mcc T_mcc
           MCc_V1 MCc_V2 MCc_V3 MCc_V4 MCc_V5 MCc_V6 MCc_V7 MCc_V8 MCc_V9 MCc_V10 MCc_V11 U_mcc L_Pc MCc_s (L_P true 0)
           A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 Hnext).
Qed.

Lemma X_J10_ex : ltac2:(tb__ "0|5|
S36S39VMD;R1A1S0S6S38A1S35R3A1S9S38S9S38VT0;S89U1M0A1A3S9S38S92S42Q8A1S38S3bSd8A1Se9Z1M1A1A4SbS38S3aS43Q40M2Z0M3A2S3cR2A1A2S8S38A1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;S1eS6S42G2A1A1S34S13S37S13VJT';G0S49SbScS1fS1fA2M4S10S1fS1fSc8Sc9A4S8G4A1A3S8ScScS1fS45A2S1fA2A1S88S48A4A2S4fG1S24G3A1A2R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HQ. destruct J10_facts as [A1 A2].
  apply (X_join' 1%nat bd_J [] 1 (SLit 0) 0 Ex_J10 Rx_J10 A1 A2 ltac:(cbn; tauto) HQ).
Qed.

Lemma X_J20_ex : ltac2:(tb__ "0|5|
S36S39VMD;R1A1S0S6S38A1S35R3A1S9S38S9S38VT0;S89U1M0A1A3S9S38S92S42Q8A1S38S3bSd8A1Se9Z2M1A1A4SbS38S3aS43Q40M2Z0M3A2S3cR2A1A2S8S38A1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;S1eS6S42G2A1A1S34S13S37S13VJT';G0S49SbScS1fS1fA2M4S10S1fS1fSc8Sc9A4S8G4A1A3S8ScScS1fS45A2S1fA2A1S88S48A4A2S4fG1S24G3A1A2R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HQ. destruct J20_facts as [A1 A2].
  apply (X_join' 1%nat bd_J [] 2 (SLit 0) 0 Ex_J20 Rx_J20 A1 A2 ltac:(cbn; tauto) HQ).
Qed.

Lemma X_J30_ex : ltac2:(tb__ "0|5|
S36S39VMD;R1A1S0S6S38A1S35R3A1S9S38S9S38VT0;S89U1M0A1A3S9S38S92S42Q8A1S38S3bSd8A1Se9Z3M1A1A4SbS38S3aS43Q40M2Z0M3A2S3cR2A1A2S8S38A1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;S1eS6S42G2A1A1S34S13S37S13VJT';G0S49SbScS1fS1fA2M4S10S1fS1fSc8Sc9A4S8G4A1A3S8ScScS1fS45A2S1fA2A1S88S48A4A2S4fG1S24G3A1A2R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HQ. destruct J30_facts as [A1 A2].
  apply (X_join' 1%nat bd_J [] 3 (SLit 0) 0 Ex_J30 Rx_J30 A1 A2 ltac:(cbn; tauto) HQ).
Qed.

Lemma X_J40_ex : ltac2:(tb__ "0|5|
S36S39VMD;R1A1S0S6S38A1S35R3A1S9S38S9S38VT0;S89U1M0A1A3S9S38S92S42Q8A1S38S3bSd8A1Se9Z4M1A1A4SbS38S3aS43Q40M2Z0M3A2S3cR2A1A2S8S38A1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;S1eS6S42G2A1A1S34S13S37S13VJT';G0S49SbScS1fS1fA2M4S10S1fS1fSc8Sc9A4S8G4A1A3S8ScScS1fS45A2S1fA2A1S88S48A4A2S4fG1S24G3A1A2R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HQ. destruct J40_facts as [A1 A2].
  apply (X_join' 1%nat bd_J [] 4 (SLit 0) 0 Ex_J40 Rx_J40 A1 A2 ltac:(cbn; tauto) HQ).
Qed.

Lemma X_J02_ex : ltac2:(tb__ "0|5|
S36S39VMD;R1A1S0S6S38A1S35R3A1S9S38S9S38VT0;S89U0M0A1A3S9S38S92S42Q8A1S38S3bSd8A1Se9Z0M1A1A4SbS38S3aS43Q40M2Z2M3A2S3cR2A1A2S8S38A1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;S1eS6S42G2A1A1S34S13S37S13VJT';G0S49SbScS1fS1fA2M4S10S1fS1fSc8Sc9A4S8G4A1A3S8ScScS1fS45A2S1fA2A1S88S48A4A2S4fG1S24G3A1A2R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HQ. destruct J02_facts as [A1 A2].
  apply (X_join' 0%nat bd_J [] 0 (SLit 2) 2 Ex_J02 Rx_J02 A1 A2 ltac:(cbn; tauto) HQ).
Qed.

Lemma X_J00_ex : ltac2:(tb__ "0|4|
S36S39VMD;R1A1S0S6S38A1S35R3A1S9S38S9S38VT0;S89U0M0A1A3S9S38S92S42Q8A1S38S3bSd8A1Se9Z0M1A1A4SbS38S3aS43Q40M2G1A2S3cR2A1A2S8S38A1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;S1eS6S42G2A1A1S34S13S37S13VJT';G0S49SbScS1fS1fA2M3S10S1fS1fSc8Sc9A4S8G3A1A3S8ScScS1fS45A2S1fA2A1S88S48A4A2S4fG1S24G1A1A2R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HQ. destruct J00_facts as [A1 A2].
  apply (X_join' 0%nat bd_J [] 0 (SLit 0) 0 Ex_J00 Rx_J00 A1 A2 ltac:(cbn; tauto) HQ).
Qed.

Lemma MS1_factsO : ltac2:(tb__ "0|0|
S0S5SedS5fS56S53S5fA1S79SbS15S101S100S8S103A1S102A3S8S15A1A3A5S4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_MS1_ex_ok : ltac2:(tb__ "0|2|
S1eS6S42Q40A1A1M0S34S13S37S13VJT';U0M1Sa1S8bA1A2S72R2R1A5VQ;A3Ftp;Frho;S1eG0S34S13S37S13VJT';G1ScaA2S5fR2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HMC. pose proof MS1_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  exact (X_msite' E_mP1 R_mP1 T_mok1 A1 MS1_factsO A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A15 HMC).
Qed.

Lemma MSc_factsO : ltac2:(tb__ "0|0|
S0S5SedS60S56S53S60A1S7aSbS15S101S100S8S103A1S102A3S8S15A1A3A5S4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_MSc_ex_ok : ltac2:(tb__ "0|2|
S1eS6S42Q40A1A1M0S34S13S37S13VJT';U0M1Sa1S8bA1A2S73R2R1A5VQ;A3Ftp;Frho;S1eG0S34S13S37S13VJT';G1ScaA2S60R2R1A5VQ;A3Ftp;Frho;F_;").
Proof.
  intros HMC. pose proof MSc_facts as FACTS.
  destruct FACTS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  exact (X_msite' E_mPc R_mPc T_mokc A1 MSc_factsO A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A15 HMC).
Qed.

Theorem tlx_ex_ok : ltac2:(tb__ "0|4|
S11eOF_;S9dVAInv;VCST;VXGL;S96VT0;VMD;U0A3M0A4S9dVAInv;VCST;VXGL;S96VT0;VMD;U1M1A3A4S36S39VMD;R1A1S0S6S38A1S35R3A1S9S38S9S38VT0;S89G1A1A3S9S38S92S42Q8A1S38S3bSd8A1Se9Sc7VF;A1A1A4SbS38S3aS43Q40M2Z0A2S3cR2A1A2S8S38A1A3A3A3A3VQ;R4A1F_;F_;Fmd;Fw;S1eS6S42G2A1A1S34S13S37S13S4dVAInv;VCST;VXGL;S44G0VrhoT;S9aVF;A1S8ScS45S45A2M3A1S8ScG3S45A2A1S9bR6ScaAcScbR2R1A5VQ;A3Ftp;Frho;F_;F_;F_;FPA0;").
Proof.
  intros PA0 HFZ0 HFZ1 HQ rho tp.
  destruct T0_facts as (A1 & A1' & A2 & A3 & A4 & A5).
  eapply (etriple_conseq (P := SPA segs (JT' 0%nat nd_T) S_T rho tp)); [intros w HS; exact (SPA_JA_PA_weaken segs AInv CST XGL NF (KcT T0 MD 0%nat) rhoT (P0T F) [] [] BX0 PA0 PTrue nd_T S_T rho tp w (fun _ _ => I) HS) | intros w' Hw'; exact Hw' |].
  assert (XJ : forall n, calls_of F = n -> (n = 1 \/ n = 2 \/ n = 3 \/ n = 4) ->
     forall rho tp, etriple segs (SPA segs (JT' 1%nat (NDA [(vB, vCap)] [] bd_J ANone)) (J_E n (SLit 0)) rho tp) Q).
  { intros n Hn Hc. rewrite Hn in HQ.
    destruct Hc as [->|[->|[->| ->]]]; [apply (X_J10_ex HQ) | apply (X_J20_ex HQ) | apply (X_J30_ex HQ) | apply (X_J40_ex HQ)]. }
  assert (J1 : calls_of F = 0 + 1 -> forall rho tp, etriple segs (SPA segs (JT' 1%nat (ndJX bd_J)) (J_E (0 + 1) (SLit 0)) rho tp) Q)
    by (intros Hn; apply (XJ 1 Hn); tauto).
  assert (J2 : calls_of F = 1 + 1 -> forall rho tp, etriple segs (SPA segs (JT' 1%nat (ndJX bd_J)) (J_E (1 + 1) (SLit 0)) rho tp) Q)
    by (intros Hn; apply (XJ 2 Hn); tauto).
  assert (J3 : calls_of F = 2 + 1 -> forall rho tp, etriple segs (SPA segs (JT' 1%nat (ndJX bd_J)) (J_E (2 + 1) (SLit 0)) rho tp) Q)
    by (intros Hn; apply (XJ 3 Hn); tauto).
  assert (J4 : calls_of F = 3 + 1 -> forall rho tp, etriple segs (SPA segs (JT' 1%nat (ndJX bd_J)) (J_E (3 + 1) (SLit 0)) rho tp) Q)
    by (intros Hn; apply (XJ 4 Hn); tauto).
  pose proof (X_LPc3_ex HFZ1 (X_XPc3_ex J4) (X_XPc3_ex J4)) as LPc3.
  pose proof (X_LPc2_ex HFZ1 (X_XPc2_ex J3) LPc3) as LPc2.
  pose proof (X_LPc1_ex HFZ1 (X_XPc1_ex J2) LPc2) as LPc1.
  pose proof (X_LPc0_ex HFZ0 (X_XPc0_ex J1) LPc1) as LPc0.
  pose proof (X_LP10_ex HFZ0 (X_XP10_ex J1) (X_XP10_ex J1)) as LP10.
  pose proof (X_LEc3_ex HFZ1 (X_XEc3_ex J4) (X_XEc3_ex J4)) as LEc3.
  pose proof (X_LEc2_ex HFZ1 (X_XEc2_ex J3) LEc3) as LEc2.
  pose proof (X_LEc1_ex HFZ1 (X_XEc1_ex J2) LEc2) as LEc1.
  pose proof (X_LEc0_ex HFZ0 (X_XEc0_ex J1) LEc1) as LEc0.
  pose proof (X_LE10_ex HFZ0 (X_XE10_ex J1) (X_XE10_ex J1)) as LE10.
  pose proof (X_MS1_ex_ok (X_MC1_ex LP10)) as MS1.
  pose proof (X_MSc_ex_ok (X_MCc_ex LPc0)) as MSc.
  exact (X_T0' (ax_S S_T1) (ax_S S_T2) E_mP1 L_E1 L_Ec E_mPc A1 A1' A2 A3 MS1 MSc (L_E false 0) (L_E true 0) A4 A5 LE10 LEc0 rho tp).
Qed.

End TLXIE.
End DrvTLXie.

