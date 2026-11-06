(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "prod"; "bool"; "list"; "pair"; "true"; "nat"; "app"; "false"; "None"; "fst"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "cell"; "sobj"; "SLit"; "valuation"; "sprop"; "DUnknown"; "FcsrFrm0"; "SExt"; "SVar"; "mkSS"; "swf"; "DZero"; "SPAlign"; "SPBranch"; "SPNot"; "mkObj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "A_globals"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "Kc_ok"; "alloc_lawsA"; "alloc_contractsA"; "alloc_contractsA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "KU"; "batom"; "BI"; "BXok_d"; "bxt"; "ASv"; "BIc"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "O_Dlo"; "O_Flo"; "O_cfg"; "O_lnk"; "O_out"; "O_txtL"; "Pre_lo"; "X_lo"; "lo_facts"; "vCFGp"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_iface"; "P0_los"; "qAR"; "NPOST_LO"; "P_err"; "P_ok"; "nd_lo0"; "Posts_loJ"; "al_cells_at"; "nd_lo_ok"; "post_fregs_lo"; "qHD"; "qRC"; "NZ32"; "O_arsP"; "PD_lo"; "bd_lo0"; "fcallee_saved"; "lo_classes"; "nd_lo_err"; "out_ok_cells"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "div"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "NDA"; "PTrue"; "ndesc"; "ANone"; "JA_pre"; "nd_below"; "AHead"; "ok_frameKA"; "tv_factsA"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface"; "al48_cells"; "memcpy48_contractA"; "memcpy48_contractA_ex"; "thunk_alloc48"; "thunk_calloc48"; "thunk_free48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface"; "white_hv"; "memcpyR_contractA"; "memcpyR_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs.LOAddr"; "lo_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "post_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "law_flag_stmt"; "law_fshadow_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA";
"infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "PostsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "ccount"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "CK0"; "CK_DIV"; "CV"; "CV0"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_p0.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import LOAddr.

Definition qRC : sv := SVar 180.
Definition qAR : sv := SVar 181.
Definition qHD : sv := SVar 182.
Definition NPOST_LO : positive := 200%positive.
Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition post_fregs_lo : list sv := ltac2:(tb__ "0|0|
S67S7SdS7S3SdL_;S4fR1A1S16S7dS66U3cR1A2A1A1S16S7dS66U8cR1A2A1A1X3x2Lr;S68U0U20A2A4").

Definition al_cells_at (o : Z) : list cell := ltac2:(tb__ "0|1|
S0SeS21Vo;S10S6dA1A2S0SeS21S54Vo;Z8A2S10S6eA1A2S0SeS21S54Vo;Z10A2S10Z0A1M0A2S0SeS21S54Vo;Z18A2S10S6fA1A2S0SeS21S54Vo;Z20A2G0A2S0SeS21S54Vo;Z28A2G0A2S1SeA1A3A3A3A3A3A3").
Definition out_ok_cells : list cell := ltac2:(tb__ "0|0|
S8SeS46Z90A1S0SeS21Zc0S40A2S0SeS21Zc8S10Z0A1A2S1SeA1A3A3A3").
Definition O_arsP : sobj := ltac2:(tb__ "0|1|
S1dS40S10Z0M0A1S10Z40A1S8SeS46G0A1S0SeS21Z30S49A2S0SeS21Z38S10Z10000A1A2S1SeA1A3A3A3S13A5").
Definition NZ32 (e : sv) : sprop := ltac2:(tb__ "0|0|
S1cS1bS7fS15S6Q20Ve;A3S10Z0A1A3A1").

Definition P_err : axst := ltac2:(tb__ "0|2|
S20S17S74S78S77S33A1S0S2S7SdA2M0S5S7SdUaS15S6Q20S4aA3A4S1G0A1A3A2S48S14SaSdA1S8SfS0SfS35S1SeA1M1A1S0SfS34S0SfS38G1S19A2S0SfS39S0SfS36S0SfS37S1SfA1A3A3A3A3A3A3S1fA3S0S12S4bS4aA1S3cA3S41S9A9S3bA2").
Definition P_ok : axst := ltac2:(tb__ "0|3|
S20S17S74S78S77S33A1S0S2S7SdA2M0S5S7SdUaS10Z0A1A4S1G0A1A3A2S48S14SaSdA1S8SfS0SfS35S1SeA1A1S0SfS34S0SfS38S52S13A2S0SfS39S0SfS36S0SfS37S0SfS4cS1SfA1A3A3A3A3A3A3A3S1fA3S8S12S65S5SdSdS40S10Z40A1A4M1A1S0S12S1aPb5Z4A2S3cA3A3S41S9A9S8S2SdSdA2M2S3bS0G2G1S1G2A1A3A3A2").
Definition nd_lo_err : ndesc := ltac2:(tb__ "0|0|
S5dS1S2SdSdA2A1S1S2S2SdScA2SdA2A1S1S2aA1S60A4").
Definition nd_lo_ok : ndesc := ltac2:(tb__ "0|1|
S5dS0S2SdSdA2M0S5SdSdS40S10Z40A1A4S1G0A1A3S1S2S2SdScA2SdA2A1S0S2aS31Z0S2bZ1A3S1S2aA1A3S63S49S9A2A4").
Definition PD_lo : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S2S5aS5fA2M0S5S5aS5fS42S51A4S0G0S5S5aS5fS43S47A4S1G0A1A3A3").

Definition bd_lo0 : list bitem := ltac2:(tb__ "0|5|
S0S2aS2dZ1M0Z0M1S0S2ScS2cA2M2S5ScS2cS8bS30S3eA1M3A4S1G2A1M4A3S8cA4S0S2aS2dG1G0S0G2S5ScS2cS57S2bS8aA2G3A4G4A3S58S2bS89A2A4S1S2aA1A3A3").
Definition nd_lo0 : ndesc := ltac2:(tb__ "0|0|
S5dS1S2SdSdA2A1S1S2S2SdScA2SdA2A1S4eS60A4").

Definition lo_classes : list Z := ltac2:(tb__ "0|0|
S0ScZ0S0ScZ1S0ScZ3S0ScZ5S0ScZ6S1ScA1A3A3A3A3A3").
Definition P0_los (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S22S82VCST;VFB;VFF;Vr;A4S22S86VFF;S32Vr;S3dA2Z90A3ScS53ScR1S50A3S23S7S88R2S67S2S2ScScA2M0ScA2G0SbG0ScA2VFF;A4A2U0A3F_;Fc;A2A2").
Lemma P0_los_mono : ltac2:(tb__ "0|2|
S4S2ScScA2M0A1M1G1G1S4S2G0ScA2A1S11G0S53G0R1R5A3S53G0R2R5A3F_;Fbn;S3fR6R5R3R2A4S3fR7R5R4R3A4F_;F_;Fr;FFFc;FF';FF;FCST;").
Proof.
  intros CST F F' FFc r Hsub ((H1 & H2 & H3) & Hc & Hn). split; [|split; [exact Hc | exact Hn]].
  split; [|split]; intros a Ha; (eapply pclMA_mono; [exact Hsub | intros x Hx; exact Hx |]); [exact (H1 a Ha) | exact (H2 a Ha) | exact (H3 a Ha)].
Qed.

Lemma posts_swf : ltac2:(tb__ "0|0|
S22S23S3S18S5bS42A1A1S6A3S22S23S3S18S5bS43A1A1S6A3S22S23S3S5cS42A1S6A3S22S23S3S5cS43A1S6A3S22S23S3S62S41S47A2S6A3S23S3S62S33S44A2S6A3A2A2A2A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Posts_loJ AInv CST XGL Kc FB FF BX : list (axst * jpostA) := ltac2:(tb__ "0|0|
S87VAInv;VCST;VXGL;VKc;S3fVCST;A1S5eS4dVFB;VFF;VBX;Aa").

Definition load_obj_stmt : Prop := ltac2:(tb__ "0|5|
S7cS11S4S7eQ40A1A1M0S69OF_;F_;F_;F_;S4S2ScScA2M1A1M2G2S27S1eR3R2A3ScS59R4R1A2S22S55Z0M3R2A2S56R2S7bA2A2F_;Fa;M4G4ScS73R1A1S59R6R2A2F_;Fa;S79R7A1S7aR8A1S25S26R1A1G2S4S2G1ScA2A1S2fS2eZ7R1A2S11S85OF_;S64S1eR8R1A3S28S1eS24R12R11R10A5ScS53ScR1S0ScG3S0ScZf5S0ScZf8S1ScA1A3A3A3A3S80S1eS24R15R14R13R2A6F_;Fxx;S6bS1eS24R14R13R12S6aA6S71S1eS24R15R14R13S70ZcA7G0S84S1eR7S75S1eS61R17R16R15ReS3fR16RcRbA3RcRbRaS5eS44AaS3aR8R1A5S76S1eS33R8R1S45R17R16R15ReRcRbRaA7A5A4Ftp0;FMCROM;FMC48;FSSC;FAC;FHok;Fok;Frho0;FHBX;FBX;FFF;FFB;FHKc;FKc;FLFSH;FLFLAG;FHXlits;FHXGL;FHCST;FALA;FXGL;FCST;FAInv;").
Definition load_obj_stmt_ex : Prop := ltac2:(tb__ "0|5|
S7cS11S4S7eQ40A1A1M0S69OF_;F_;F_;F_;S4S2ScScA2M1A1M2G2S27S1eR3R2A3ScS59R4R1A2S22S55Z0M3R2A2S56R2S7bA2A2F_;Fa;M4G4ScS73R1A1S59R6R2A2F_;Fa;S79R7A1S7aR8A1S25S26R1A1G2S4S2G1ScA2A1S2fS2eZ7R1A2S11S29S1eS24R10RfReA5ScS53ScR1S0ScG3S0ScZf5S0ScZf8S1ScA1A3A3A3A3S81S1eS24R13R12R11R2A6F_;Fxx;S6cS1eS24R12R11R10S6aA6S72S1eS24R13R12R11S70ZcA7G0S83S1eS75S1eS61R15R14R13RcS3fR14RaR9A3RaR9R8S5eS44AaS3aR6R1A5S76S1eS33R6R1S45R15R14R13RcRaR9R8A7A5A3Ftp0;FMCROMX;FMC48X;FSSCX;FACX;Frho0;FHBX;FBX;FFF;FFB;FHKc;FKc;FLFSH;FLFLAG;FHXlits;FHXGL;FHCST;FALA;FXGL;FCST;FAInv;").
