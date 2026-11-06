(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "nat"; "cons"; "nil"; "bool"; "true"; "Some"; "fst"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_facts"; "sobj"; "holds"; "sprop"; "ss_next"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "JA"; "TPA"; "fbinA"; "ffinA"; "frinA"; "ok_frameKA"; "tvinA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "phiK"; "efnode"; "fnode"; "JAF"; "efdrop"; "enodeIAF"; "nodeIAF"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD_eqs"; "PhisD"; "nd_d2"; "nd_d0"; "tvA"; "nd_z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "z0"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_pure"; "J_pure_pre"; "JL_stack_free"; "J_stack_free_pre"; "V_FL"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vF"; "vFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2"; "L_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "ldef"; "extraLO"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS5"; "Es_s80"; "Es_sf"; "Es_sf0"; "P_okL"; "Ts_s82"; "nd_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "K_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD3"; "L_sf"; "Pre_sf"; "P_errL"; "X_sx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS5.IF"; "P_err"; "P_ok"; "nd_lo_err"; "nd_lo_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS5_chk"; "cutsS5"; "exitsS5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "L_f8"; "L_mc48"; "Pre_f8"; "Pre_mc48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface"; "al48_cells";
"memcpy48_contractA"; "memcpy48_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvpk"; "extraXlo"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "remove_nth"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "robjs_okL"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_hvkit Lib_load_obj_hvpk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiD3 Lib_load_obj_epiD_eqs Lib_load_obj_epiD_chk Lib_load_obj_epiS5 Lib_load_obj_epiS5_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_load_obj_epiD_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DP. Include Lib_load_obj_epiD_pf. End DP.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S3fS11S3S18Q40A1A1S49OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S54S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S10S7bVCST;R1A2S33S45Z0R2A2S46R2S84A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S10S7bVXGL;R1A2S33S45Z0R2A2S46R2S84A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S10S87R1A1S7bVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S2S2S10S10A2S10A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S11OFr;") := ltac2:(tb__ "0|0|
S88VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1bVAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBX;S1aVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S2eVAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBX;S1aVPhi;Vnd;Ad").

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S10S3S18Q40A1A1S3dF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S23SdS11S3S18Q40A1A1S3dS5dS16S15R3A1S13SeR4A1A1A3VTR;S22S0R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S3dS3dS3dS3eR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S23S23SdSdS67S3S14A1M0S3S2SdS25A2M1A1S3S2S12S12A2M2A1S3dS11S3S18Q40A1A1M3G2S42G2R1R5A3S42G2R2SfRbA1A3F_;Fr;S32SbG0A1S29RaR9R8A3S9G0R7A2A3S32S7S28RbRaR9R8S5cG1SdSaSdS25A2R7A4A5S8A3S11G3VTR;S22S0RfRdR2R1A5S26S0S17SeRdA1A1R2R1RaA5A2Ftp1;Frho1;S3S4aA1M4S69S49S24S0R9R8R10S1G4S6aR3S6bR2R1A2A4A5R13RaR9R4R2A4R13S65S64RbRfS4bR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SdS25G4S69S49S11G3G4S69S49S42G1S1SdS25RaR9A4R14A3S24S0R12R11R19S1G4S6aR9S6bR8R7A2A4A5R1cR13R12RaR8A4S81S17SeR1aA1A1S65S64R14R18S4bR9R13RaA3A3R19A2R8A3S24S0R9R8ReS1G4S6aR7S6bR6R5A2A4A5ReS65S64R16R1aS4bRbR15RcA3A3R1bA2R15RaR9R8R6A6S33S91R17S4bRcR16RdA3R1bR1cR1dR10R1eR19RbA9S11S82R18S4bRdR17ReA3R1cR1dSeR1eA1SeR1fA1SeR11A1R1RcA9VTR;S22S0S27R11S65S64R19R1dS4bReR18RfA3A3R1eA2R18RdRcA5S92R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S22S0R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S11OF_;S19SdS11S3S18Q40A1A1S3dR6R3A1VTR;S22S0VJAv;R6A1R5R4R3A5R2A2F_;VTR;S22S0VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").

Hypothesis CMC48 : ltac2:(tb__ "0|1|
S3fS11S3S18Q40A1A1VTR;S22S0S4eVAInv;R3VKc;A3S7aR2R1A5S26S0S43R2R1S5S2SdS25A2M0S1SdS25S78S4dVAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CF8 : ltac2:(tb__ "0|1|
S3fS11S3S18Q40A1A1VTR;S22S0S4eVAInv;R3VKc;A3S79R2R1A5S26S0S43R2R1S5S2SdS25A2M0S1SdS25S77S4dVAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CSF : ltac2:(tb__ "0|2|
S3fS11S3S18Q40A1A1VTR;S22S0S50VAInv;Z5M0R3VKc;A4S6eR2R1A5S26S0S43R2R1S5S2SdS25A2M1S1SdS25S6dS4fVAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CUT5 : ltac2:(tb__ "0|5|
SdS19S4S2S10S12A2M0S11S3S18Q40A1A1M1S10G1S42S2S2S2SdS19A2M2S4A2M3G0A2S1G3G0S1G2S4S1SdS19R8R7A4R6A4R5A4S75A3S2bS36R7R5A3S33S45Z0S2aS1G3G0S1G2S4S1SdS19RaR9A4R8A4R7A4R6A2M4A2S46G4R4A2A2VTR;S22S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Hypothesis XPK : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAv;S74A1S72R3R2A5VFAM;S47Z158S48Z2Z40A2A2R1A2A2Ftp0;Ftp;Frho;").
Hypothesis XPE : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAv;S73A1S71R3R2A5VFAM;S47Zd1S48Z2Z40A2A2R1A2A2Ftp0;Ftp;Frho;").

Lemma CXR_s8aS : ltac2:(tb__ "0|0|
S32S7S80VXGL;S13SeS5eA1A1S39Z38ZdbS70S5eA1A6S8A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_s8rS : ltac2:(tb__ "0|0|
S32S7S80VXGL;S13SeS62A1A1S39Z14Z34SfS62A1A6S8A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXL_sfS : ltac2:(tb__ "0|0|
S32S7S83VXGL;S13SeS5fA1A1S39S59S9S4U0A2S6S14A1S7fSfS5fA1A8S8A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma c5_ok : 0 <= 5 <= 6. Proof using . lia. Qed.
Lemma k68 : 0 <= 56. Proof using . lia. Qed.
Lemma k32 : 0 <= 20. Proof using . lia. Qed.
Lemma k68_231 : 56 <= 219 <= fs_frame_size 5 / 8. Proof using . change (fs_frame_size 5) with 2048. lia. Qed.
Lemma k32_64 : 20 <= 52 <= fs_frame_size 5 / 8. Proof using . change (fs_frame_size 5) with 2048. lia. Qed.
Ltac meas_z0 := rewrite !DP.efmeas_z0; vm_compute; split; [discriminate | reflexivity].

Lemma X_L_ok : ltac2:(tb__ "0|2|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAv;S37A1S58R3R2A5VFAM;S2aS1S2S2SdS19A2M1S4A2S2S10S12A2S1G1S4S1SdS19S58S37A4U1A4S1S10S12Z167S44A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  pose proof epiS5_checks_mc as (Cx1 & Cx2 & Cx3 & Cent & Cchk & Cta & CT0 & CxB & Ctidy & Cwf & _).
  pose proof epiS5_chk_mc as (Cnp & Cnb & Cbb & Cwp & Cshape & Cnf & Cbp & CR & CX).
  apply (TR_pre (SPA segs (JAv nd_d2) Es_mc rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv nd_d2) _ rho Es_mc2 Es_mc tp w Cx3). apply (SPA_axforms segs (JAv nd_d2) _ rho Es_mc1 Es_mc2 tp w Cx2).
    exact (SPA_axforms segs (JAv nd_d2) _ rho L_ok Es_mc1 tp w Cx1 Hw). }
  apply (purec_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre_mc48 [L_mc48] Es_mc s_mcS Rs_mc rho tp nd_d2 KU1 (FAM (efmeasA (L_ok, nd_d2, 1%nat, (359, z0)) rho) tp0)).
  - intros Ai rho2 tp2. cbn [map]. apply CMC48.
  - exact Cnf.
  - exact Cbp.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cbb.
  - apply DP.payA_same. exact Cwp.
  - exact Cshape.
  - exact (DP.site_rt_lo0 AInv CST XGL ALA HCST HXlits FB FF rho0 Es_mc s_mcS Rs_mc rho tvA KU1 (AHead pH false) CR CX).
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_am nd_d2 ndEp]. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_d2) Ts_mc rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_d2) (xfb_mcS Ts_mc0) rho' Ts_mc0 Bs_mc tp' w CxB Hw). }
    apply (CUT5 Ts_mc nd_d2 1%nat (355, z0) rho' tp'); [left; reflexivity | exact I | meas_z0].
Qed.

Lemma X_Es_s80 : ltac2:(tb__ "0|3|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAFv;S2bS36U1M1A2S37A2S5eR3R2A5VFAM;S2aS1S2S2SdS19A2M2S4A2S2S10S12A2S1G2S4S1SdS19S5eS37A4G1A4S1S10S12Z162S44A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiS5_checks_s8 as (CwfA & CeqA & Cxf & Cent & Cchk & CT0 & Cxb & Cobjs & Ceq82 & Cwf82 & CeqR & CwfR & Ctidy & CwfT & _).
  pose proof epiS5_chk_s8 as (Cbase0 & Chf0 & CR0 & Cta & Cnp & Cnb & Cshape & CR & CX & Cbase1 & Chf1 & Cnb1 & CR1 & Cbase2 & Chf2 & CR2 & Cbb).
  pose proof epiS5_chk_sx as (XeqA & XwfA & Xeq82 & XeqR & XwfR & _).
  apply (TR_pre (SPA segs (JAv nd_d2) Es_s8 rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv nd_d2) (xf_shcall Es_s8a 56) rho Es_s8a Es_s8 tp w Cxf). rewrite <- XeqA.
    apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             tvA frL KU1 (AHead pH false) 0%nat 110%positive 5 120%positive g5 56 219 Es_s80 (X_sx Es_s80) rho tp w eq_refl c5_ok Cbase0 k68
             k68_231 Chf0 (DP.X_sx_incl Es_s80) XwfA); [|exact Hw].
    intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    - exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai rho _ tvA _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR0).
    - exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ tvA (X_sx Es_s80) rho3 tp3 md3 56 219 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR_s8aS). }
  apply (purec_callT segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre_f8 [L_f8] Es_s8 (s_s8 Es_s8) Rs_s8 rho tp nd_d2 KU1 (FAM (efmeasA (Es_s80, nd_d2, 1%nat, (354, z0)) rho) tp0)).
  - intros Ai rho2 tp2. cbn [map]. apply CF8.
  - reflexivity.
  - reflexivity.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cbb.
  - apply DP.payA_same. reflexivity.
  - exact Cshape.
  - exact (DP.site_rt_lo0 AInv CST XGL ALA HCST HXlits FB FF rho0 Es_s8 (s_s8 Es_s8) Rs_s8 rho tvA KU1 (AHead pH false) CR CX).
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_am nd_d2 ndEp]. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_d2) Ts_s81 rho' tp')).
    { intros w Hw. exact (SPA_axforms segs (JAv nd_d2) (xf_shback Ts_s80) rho' Ts_s80 Ts_s81 tp' w Cxb Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv nd_d2) Ts_s8 rho2 tp' w)).
    { intros [tr [ms md]] Hw. exists (rho_absorb rho' [shobj g5 56 219 [] DUnknown] (vms md tp' ms)).
      rewrite <- Ctidy. apply SPA_tidy. rewrite <- XeqR.
      apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tvA frL KU1 (AHead pH false) 0%nat 110%positive 5 120%positive g5 20 52 Ts_s82 (ax_X Ts_s82) _ tp' (tr, mkCfg ms md) eq_refl c5_ok Cbase2 k32
               k32_64 Chf2 (fun r H => H) XwfR).
      - intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
        + exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai _ _ tvA _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR2).
        + exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai _ _ tvA (ax_X Ts_s82) rho3 tp3 md3 20 52 HM HF HP0 Hav HT HTK HN HD HZ HFR CXR_s8rS).
      - rewrite <- Xeq82.
        apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
                 tvA frL KU1 (AHead pH false) 0%nat 110%positive 5 120%positive g5 56 219 [] DUnknown Ts_s81 (objs_butlast Ts_s81) [] rho' tp' tr ms md
                 eq_refl c5_ok Cbase1 Cobjs k68 k68_231 eq_refl Chf1 eq_refl Cnb1); [|exact Hw].
        intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
        exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai rho' _ tvA _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CR1). }
    apply TR_exw. intros rho2.
    apply (CUT5 Ts_s8 nd_d2 1%nat (350, z0) rho2 tp'); [right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma site_sfT : ltac2:(tb__ "0|7|
S3S2S12S12A2A1SdS67S3S14A1S11S32S7S95S13SeR4A1A1R5S59S9S4U0M0A2M1S5bR2A6S8A3S32S7S83VXGL;S13SeR5A1A1R6S59G1S6S14A1S7fSfR5A1A8S8A3S32S12S66R5PcM2A2S56A3S32S12S66R6S51A2S57A3S3fS5dS16S15R6A1S13SeR9A1A1A3VP0;Vrho0;A1S81S55Vrho0;R8A3S1dVFB;R4A2S1eVFF;R5A2S21VFB;R6RbRfA4S8dRcR10A2S8eRdR11A2S1fVFF;R9ReS59A4S34S11S11S34S3S18Q40A1A1M3G3S34S49S49VAInv;RdR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S1cVrho0;RbA2S8bR11S41S40RcA1A1A2S33S93VCST;Vrho0;VFB;VFF;R12R16S8cS2S2S12S10A2M4S12A2G0S59A3M5R13A8S33S94VCST;VXGL;Vrho0;VFB;VFF;R12R16G5SfR15A1A9S33S32S10S68R12S66R14G2A2A2S68R12SaS12S10SaG4S12S1G4S12S1S12S10S56Z5A4S57A4M6A3A3A2A3S32S10S68R12S66R14S51A2A2S68R12ScG4S12G6A3A2A3A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;F_;F_;F_;F_;Frho;FR;Fs;FE;Ftv;").
Proof using ALA HXlits.
  intros tv E s R rho HR HX Hs12 Hs16 Ai HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  pose proof (T_ok_T0 rho0 rho Ai HT HTK) as HT0.
  split; [|split; [|rewrite Hs12, Hs16; cbn [fst snd]; split; reflexivity]].
  - intros o a Ho Hr.
    apply (TobjJAT.robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ tv frL (Some 0%nat) extraLO R rho1 tp1 md1 HM HF HT0 HN HD HZ HFR HR) with (o := o); [| exact Ho | exact Hr].
    intros o' a' _ HE Hr'. exact (extraLO_pclMA CST rho0 FB FF rho tv _ o' a' Hav HP0 HE Hr').
  - apply (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho _ tv frL (Some 0%nat) [] extraXlo (ax_X E) rho1 tp1 md1 HM HF HT0 HN HD HZ HFR HX).
    intros r' a' _ HE Ha. unfold extraXlo in HE. apply lazy_orb_prop in HE as [HE|HE].
    + left. exact (xextraLO_pclMA CST rho0 FB FF rho tv _ r' a' Hav HP0 HE Ha).
    + right. apply HXlits. exact (xr_inlits_sound r' rho a' HE Ha).
Qed.

Lemma X_Es_sf0 : ltac2:(tb__ "0|3|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAFv;S2bS36U1M1A2S37A2S60R3R2A5VFAM;S2aS1S2S2SdS19A2M2S4A2S2S10S12A2S1G2S4S1SdS19S60S37A4G1A4S1S10S12Z15dS44A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiS5_checks_sf as (CxfA & CwfB & CxfC & CxfD & CwfE & Cent & Cchk & CwfT & _).
  pose proof epiS5_chk_sf as (CbaseA & CobjsA & Cdw & ChfA & CnbA & CRA & CeqB & CbaseD & CeqF & CswfF & CRD & CXD & Cta & Cnp & Cnb & C12 & C16 & CRsf & CT0 & Ctidy).
  pose proof epiS5_chk_sx as (_ & _ & _ & _ & _ & XeqB & XwfF).
  apply (TR_pre (fun w => exists rho1, SPA segs (JAv nd_d2) Es_sf rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj g5 20 52 (ob_cells shs) (ob_dflt shs)] (vms md tp ms)).
    rewrite <- CeqF.
    apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
             tvA frL KU1 (AHead pH false) 0%nat 110%positive 5 120%positive Es_sfD _ tp (tr, mkCfg ms md) eq_refl c5_ok CbaseD XwfF).
    - intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
      + intros o a Ho Hr. destruct (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai _ _ tvA _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CRD o a Ho Hr) as [X|X]; [left; exact X | right; left; exact X].
      + exact (xrs47_chk_sound segs AInv CST ALA HCST FB Ai _ _ tvA _ rho3 tp3 md3 HM HF HN HZ CXD).
    - apply (SPA_axforms segs (JAv nd_d2) (xf_merge Es_sfC) _ Es_sfC Es_sfD tp _ CxfD).
      apply (SPA_axforms segs (JAv nd_d2) (xf_rebase Es_sfB) _ Es_sfB Es_sfC tp _ CxfC).
      rewrite <- XeqB.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tvA frL KU1 (AHead pH false) 0%nat 110%positive 5 120%positive g5 20 52 (ob_cells shs) (ob_dflt shs) Es_sfA (objs_butlast Es_sfA) [] rho tp tr ms md
               eq_refl c5_ok CbaseA CobjsA k32 k32_64 Cdw ChfA eq_refl CnbA).
      + intros Ai rho3 tp3 md3 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
        exact (DP.lo_robjsR0 AInv CST ALA HCST FB FF rho0 Ai rho _ tvA _ rho3 tp3 md3 HM HF HP0 Hav HT HTK HN HD HZ HFR CRA).
      + exact (SPA_axforms segs (JAv nd_d2) (xf_sh Es_sf0) rho Es_sf0 Es_sfA tp _ CxfA Hw). }
  apply TR_exw. intros rho1.
  unfold Pre_sf, L_sf in Cent, Cchk.
  apply (sfree_callT segs AE_A AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           5 Es_sf (s_sf Es_sf) Rs_sf (ax_X Es_sf) rho1 tp nd_d2 0%nat (vF, 5, vFL) (FAM (efmeasA (Es_sf0, nd_d2, 1%nat, (349, z0)) rho) tp0) CSF c5_ok).
  - intros r H. exact H.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros A A' _. exact I.
  - exact (site_sfT tvA Es_sf (s_sf Es_sf) Rs_sf rho1 CRsf CXL_sfS C12 C16).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_bd nd_am nd_d2 ndEp remove_nth frL]. unfold Pre_sf, L_sf in CT0. rewrite CT0.
    apply (TR_pre (SPA segs (JAv nd_okL) Ts_sf rho' tp')).
    { intros w Hw. rewrite <- Ctidy. apply SPA_tidy. exact Hw. }
    apply (CUT5 Ts_sf nd_okL 1%nat (345, z0) rho' tp'); [right; right; left; reflexivity | exact I | meas_z0].
Qed.

Lemma X_P_okL : ltac2:(tb__ "0|3|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAFv;S2bS36U1M1A2S63A2S61R3R2A5VFAM;S2aS1S2S2SdS19A2M2S4A2S2S10S12A2S1G2S4S1SdS19S61S63A4G1A4S1S10S12Z158S44A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros _.
  pose proof epiS5_checks_post as (CxR & CxM & _ & Cent & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam & _).
  pose proof epiS5_chk_post as (Cfb & Cwf & C4096 & _).
  rewrite DP.efmeas_z0.
  apply (TR_pre (SPA segs (JAv IF.nd_lo_ok) IF.P_ok (rho_sub rho s_pok) tp)); [|apply XPK].
  intros w Hw.
  apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc P_okF IF.P_ok s_pok nd_okL IF.nd_lo_ok rho tp w Cent Cid Cnp Cnb Ctv Cfr Cbd Cam).
  rewrite <- Cwf. apply (SPA_refacts_JA segs); [| exact Cfb |].
  - apply (SPA_axforms segs (JAv nd_okL) (xf_mergeR P_okR) rho P_okR P_okM tp w CxM). exact (SPA_axforms segs (JAv nd_okL) (xf_rebaseR P_okL) rho P_okL P_okR tp w CxR Hw).
  - intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    apply (JA_tv_facts segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue ALA _ _ _ _ _ (vARn, SLit 64) eq_refl HJ); [left; reflexivity|].
    exact (DP.tnz_of_ule4096 rho _ (vARn, SLit 64) HF C4096).
Qed.
Lemma X_P_errL : ltac2:(tb__ "0|2|
S11S3S18Q40A1A1M0G0VTR;S22S0VJAv;S3aA1S6fR3R2A5VFAM;S2aS1S2S2SdS19A2M1S4A2S2S10S12A2S1G1S4S1SdS19S6fS3aA4U1A4S1S10S12Zd1S44A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  pose proof epiS5_checks_post as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CxR & CxM & Cent & Cid & Cnp).
  pose proof epiS5_chk_post as (_ & _ & _ & Cnb & Ctv & Cfr & Cbd & Cam).
  rewrite DP.efmeas_z0.
  apply (TR_pre (SPA segs (JAv IF.nd_lo_err) IF.P_err (rho_sub rho s_perr) tp)); [|apply XPE].
  intros w Hw.
  apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc P_errM IF.P_err s_perr nd_z IF.nd_lo_err rho tp w Cent Cid Cnp Cnb Ctv Cfr Cbd Cam).
  apply (SPA_axforms segs (JAv nd_z) (xf_mergeR P_errR) rho P_errR P_errM tp w CxM). exact (SPA_axforms segs (JAv nd_z) (xf_rebaseR P_errL) rho P_errL P_errR tp w CxR Hw).
Qed.

Lemma exitsS5_ok : ltac2:(tb__ "0|4|
SdS19S4S2S10S12A2M0S11S3S18Q40A1A1M1G1S42S2S2S2SdS19A2M2S4A2M3G0A2S1G3G0S1G2S4S1SdS19R7R6A4R5A4R4A4S76A3VTR;S22S0VJAFv;S2bS36R6A2R7A2R8R4R3A5VFAM;S2aS1G3G0S1G2S4S1SdS19R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FX;").
Proof.
  intros X nd k rv rho tp tp0 Hin. cbn [exitsS5 In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <- <- <-.
  - apply X_Es_s80.
  - apply X_Es_sf0.
  - apply X_P_okL.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S20S0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S52S0S4cVAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S10S42S10R1S5S10Z0S5S10Zf5S5S10Zf8S6S10A1A3A3A3A3S85S0S4cVAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48 : ltac2:(tb__ "0|0|
S7dS0S4cVAInv;VCST;VXGL;S7cA6").
Variable FAMQ : list word -> assn.
Hypothesis XPK_T : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0S3cS0Vok;S22S0VJAv;S74A1S72R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XPE_T : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0S3cS0Vok;S22S0VJAv;S73A1S71R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CMC48_T : ltac2:(tb__ "0|1|
S3fS11S3S18Q40A1A1S3cS0Vok;S22S0S4eVAInv;R3VKc;A3S7aR2R1A5S26S0S43R2R1S5S2SdS25A2M0S1SdS25S78S4dVAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply MC48; [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.
Lemma CF8_T : ltac2:(tb__ "0|1|
S3fS11S3S18Q40A1A1S3cS0Vok;S22S0S4eVAInv;R3VKc;A3S79R2R1A5S26S0S43R2R1S5S2SdS25A2M0S1SdS25S77S4dVAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (SSC 248 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.
Lemma CSF_T : ltac2:(tb__ "0|2|
S3fS11S3S18Q40A1A1S3cS0Vok;S22S0S50VAInv;Z5M0R3VKc;A4S6eR2R1A5S26S0S43R2R1S5S2SdS25A2M1S1SdS25S6dS4fVAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A4Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (aca_stack_free _ _ _ _ _ AC 5 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. Qed.

Let famS (cuts : list efnode) (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S10S3S18Q40A1A1S3eS35S90S0S5cS2dS8aS31VAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBX;S1aS36AcS5cS2cS2dS2fVcuts;A4A4R1A3VFAMQ;Vtp0;R1A2A2Lw;L_;L_;").
Lemma reenterS : ltac2:(tb__ "0|6|
S3S2S2S2SdS19A2M0S4A2M1S2S10S12A2M2A2M3A1S3S18Q40A1A1M4SdS19S4G2S11G4S10G4S42G3S1G1G2S1G0S4S1SdS19R8R7A4R6A4R5A4RaA3S2bS36R7R5A3S33S45Z0S2aS1G1G2S1G0S4S1SdS19RaR9A4R8A4R7A4R6A2M5A2S46G5R4A2A2S3cS0Vok;S22S0VJAv;RaA1RbR7R6A5VfamS;RdRcR5R4A4A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;Fcuts;").
Proof.
  intros cuts tp0 T nd k rv rho tp b tp0' Hin Hphi _.
  apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisD ok (map efdrop cuts) T nd k (FAMQ tp0) rho tp); [|exact Hphi].
  apply in_map_iff. exists (T, nd, k, rv). split; [reflexivity | exact Hin].
Qed.
Lemma rightS : ltac2:(tb__ "0|1|
S3S2cA1S3S18Q40A1A1M0S3dS10G0S3cS0Vok;R3VFAMQ;R4A1A4S3cS0Vok;R4VfamS;R6R5R3R2A4A4F_;Ftp0';Fb;FP;Ftp0;Fcuts;").
Proof. intros cuts tp0 P b tp0' H. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact H]. Qed.

Lemma S5_T : ltac2:(tb__ "0|4|
SdS19S4S2S10S12A2M0S11S3S18Q40A1A1M1G1S42S2S2S2SdS19A2M2S4A2M3G0A2S1G3G0S1G2S4S1SdS19R7R6A4R5A4R4A4S75A3S2bS36R6R4A3S3cS0Vok;S22S0VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads 300%nat cps_ad NP (map efdrop cutsS5) (map efdrop exitsS5) ok (FAMQ tp0) Hok
           (ejcertAF_jcertAF segs NP PhisD _ _ _ _ _ ecertS5_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  exact (exitsS5_ok (triple segs ok) (famS cutsS5 tp0) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           CF8_T CSF_T (reenterS cutsS5 tp0)
           (fun rho tp tp0' => rightS cutsS5 tp0 _ _ tp0' (XPK_T rho tp tp0)) X' nd' k' rv' rho1 tp1 tp0 HinX).
Qed.

Theorem epiK_T : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0S3cS0Vok;S22S0VJAv;S37A1S58R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (X_L_ok (triple segs ok) (fun _ tp0' => FAMQ tp0') (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok) CMC48_T
           (fun T nd k rv rho tp b tp0' Hi Hp _ => S5_T T nd k rv rho tp tp0' Hi Hp) rho tp tp0).
Qed.

Theorem epiDK_T : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0S5aR3A1S3cS0Vok;S22S0VJAv;S38A1S6cR4R3A5VFAMQ;R2A1A4F_;Ftp0;Ftp;Frho;").
Proof.
  exact (DP.epiD_T AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC FAMQ epiK_T
           (fun rho tp tp0 => X_P_errL (triple segs ok) (fun _ tp0' => FAMQ tp0') (TRs_pre segs ok) (fun rho tp tp0' => XPE_T rho tp tp0') rho tp tp0)).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S53S0S4cVAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S10S42S10R1S5S10Z0S5S10Zf5S5S10Zf8S6S10A1A3A3A3A3S86S0S4cVAInv;VCST;VXGL;R2A6F_;Fxx;").
Hypothesis MC48X : ltac2:(tb__ "0|0|
S7eS0S4cVAInv;VCST;VXGL;S7cA6").
Variable FAM : ltac2:(tb__ "0|0|
S10S3S18Q40A1A1S3dF_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S10S10S3S18Q40A1A1S3eS45R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XPK_E : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0S3bS0S22S0VJAv;S74A1S72R3R2A5VFAM;S47Z158S48Z2Z40A2A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XPE_E : ltac2:(tb__ "0|1|
S11S3S18Q40A1A1M0G0S3bS0S22S0VJAv;S73A1S71R3R2A5VFAM;S47Zd1S48Z2Z40A2A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CMC48_E : ltac2:(tb__ "0|1|
S3fS11S3S18Q40A1A1S3bS0S22S0S4eVAInv;R3VKc;A3S7aR2R1A5S26S0S43R2R1S5S2SdS25A2M0S1SdS25S78S4dVAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply MC48X. exact HKc. Qed.
Lemma CF8_E : ltac2:(tb__ "0|1|
S3fS11S3S18Q40A1A1S3bS0S22S0S4eVAInv;R3VKc;A3S79R2R1A5S26S0S43R2R1S5S2SdS25A2M0S1SdS25S77S4dVAInv;VCST;VXGL;R3VKc;A5A4S6G0A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (SSCX 248 ltac:(cbn; tauto)). exact HKc. Qed.
Lemma CSF_E : ltac2:(tb__ "0|2|
S3fS11S3S18Q40A1A1S3bS0S22S0S50VAInv;Z5M0R3VKc;A4S6eR2R1A5S26S0S43R2R1S5S2SdS25A2M1S1SdS25S6dS4fVAInv;VCST;VXGL;G0R3VKc;A6A4S6G1A1A3A5A3Ftp1;Frho1;FAi;").
Proof. intros Ai rho1 tp1. apply (acx_stack_free _ _ _ _ _ ACX 5 ltac:(cbn; tauto)). exact HKc. Qed.

Let famE (cuts : list efnode) (tp0 : list word) : Z -> list word -> assn := ltac2:(tb__ "0|0|
S10S3S18Q40A1A1S3eS35S8fS0S5cS2cS89S30VAInv;VCST;VXGL;S55VKc;Vrho0;VP0;VFB;VFF;VBX;S1aS36AcVcuts;A4R3R1A4VFAM;R3Vtp0;R1A3A2Lw;L_;Lb;").
Lemma reenterE : ltac2:(tb__ "0|6|
S3S2S2S2SdS19A2M0S4A2M1S2S10S12A2M2A2M3A1S3S18Q40A1A1M4SdS19S4G2S11G4S10G4S42G3S1G1G2S1G0S4S1SdS19R8R7A4R6A4R5A4RaA3S2bS36R7R5A3S33S45Z0S2aS1G1G2S1G0S4S1SdS19RaR9A4R8A4R7A4R6A2M5A2S46G5R4A2A2S3bS0S22S0VJAv;RaA1RbR7R6A5VfamE;RdRcR5R4A4A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;Ftp0;Fcuts;").
Proof.
  intros cuts tp0 T nd k rv rho tp b tp0' Hin Hphi Hm.
  exact (ereenter_cutJAF_b segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisD cuts T nd k rv (FAM b tp0) b rho tp Hin Hphi Hm).
Qed.
Lemma rightE : ltac2:(tb__ "0|1|
S3S2cA1S3S18Q40A1A1M0S3dS10S10G0S45R3R2A2S3bS0R5VFAM;R4R6A2A3S3bS0R6VfamE;R8R7R4R3A4A3F_;F_;Ftp0';Fb;Fm;FP;Ftp0;Fcuts;").
Proof. intros cuts tp0 P m b tp0' Hm H. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact (FAM_mono m b tp0 w Hm Hw) | exact H]. Qed.

Lemma S5_E : ltac2:(tb__ "0|4|
SdS19S4S2S10S12A2M0S11S3S18Q40A1A1M1G1S42S2S2S2SdS19A2M2S4A2M3G0A2S1G3G0S1G2S4S1SdS19R7R6A4R5A4R4A4S75A3S2bS36R6R4A3S3bS0S22S0VJAv;R8A1R9R5R4A5VFAM;S2aS1G3G0S1G2S4S1SdS19R9R8A4R7A4R6A4R5A2R3A2A3F_;F_;Ftp0;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp tp0 Hin Hphi.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisD k) nd T rho tp _ Hphi).
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisD PhisD_reads 300%nat cps_ad NP cutsS5 exitsS5 (fun b w => FAM b tp0 w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0 w Hb Hw) ecertS5_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  exact (exitsS5_ok (etriple segs) (famE cutsS5 tp0) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           CF8_E CSF_E (reenterE cutsS5 tp0)
           (fun rho tp tp0' => rightE cutsS5 tp0 _ _ _ tp0' (Z.le_refl _) (XPK_E rho tp tp0)) X ndX kX rvX rho1 tp1 tp0 HinX).
Qed.

Theorem epiK_E : ltac2:(tb__ "0|2|
S11S3S18Q40A1A1M0G0S3bS0S22S0VJAv;S37A1S58R3R2A5VFAM;S2aS1S2S2SdS19A2M1S4A2S2S10S12A2S1G1S4S1SdS19S58S37A4U1A4S1S10S12Z167S44A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply (X_L_ok (etriple segs) FAM (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs) CMC48_E).
  intros T nd k rv rho1 tp1 b tp0' Hi Hp Hm.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w (Z.lt_le_incl _ _ (proj2 Hm)) Hw) | exact (S5_E T nd k rv rho1 tp1 tp0' Hi Hp)].
Qed.

Theorem epiDK_E : ltac2:(tb__ "0|2|
S11S3S18Q40A1A1M0G0S5aR3A1S3bS0S22S0VJAv;S38A1S6cR4R3A5VFAM;S2aS1S2S2SdS19A2M1S4A2S2S10S12A2S1G1S4S1SdS19S6cS38A4U0A4S1S10S12Z186S44A4A4R4A2R2A2A3F_;Ftp0;Ftp;Frho;").
Proof.
  exact (DP.epiD_E AInv CST XGL ALA HCST HXGL HXlits LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX FAM FAM_mono epiK_E
           (fun rho tp tp0 => X_P_errL (etriple segs) FAM (TRe_pre segs) XPE_E rho tp tp0)).
Qed.
End Existence.
End Sum.
