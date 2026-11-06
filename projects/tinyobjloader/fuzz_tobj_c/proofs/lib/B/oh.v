(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes Lib_handle_f_s8w.

(* [comment removed for export] *)
Module Lib_handle_f_gdefs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "andb"; "app"; "nat"; "prod"; "None"; "cons"; "orb"; "S"; "nil"; "fst"; "list"; "pair"; "Some"; "bool"; "false"; "snd"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "SPUle"; "SLit"; "sv"; "SPBranch"; "SAlu"; "sv_eqb"; "ss_facts"; "ss_next"; "SPUlt"; "ss_objs"; "sobj"; "sprop_below"; "SPEq"; "SPNot"; "SVar"; "dflt_writable"; "swf"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pA"; "fr_hf"; "am2"; "pQ"; "pT0"; "PD_vn"; "co_n"; "pKco"; "room_r"; "pDco"; "xbo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "B32"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_base"; "ax_X"; "entailsA"; "g8"; "has_facts"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "pow"; "ltb"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "tE"; "tL"; "kb"; "tI"; "hG"; "hF"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "BC_EQ"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "ANone"; "NDA"; "ndesc"; "fr_sub_eqb"; "nd_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "extraOH"; "extraXH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "bF"; "feF"; "roomF"; "triAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7"; "pNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "sv_subst"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_wpos"; "bd_below"; "bd_subst"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xrs_checkL"; "robjs_checkF"; "local_ok"; "shadow_reopen_stateA"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "skipn"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "nd0"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8"; "pL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "call_checkA"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xrs_inclb"; "pd_okA"; "pdescA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vAL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "arity_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5"; "needA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "wsub_dom_below"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

Definition bF (F : list sprop) : bool := baseF DW F.
Definition fF (F : list sprop) : bool := frameF hG 160 512 F.
Definition feF (F : list sprop) : bool := ltac2:(tb__ "0|0|
S39S5S11S1fS38S43A1S44A2S5S11S13S21S43A1S14S3dS3bZ2Z3dA2Z1A2A1A2S8S11A1A3A3VF;A2").

Definition vr_chk (XGL : list (Z * Z)) (E : axst) (kept : list (sv * sv)) (d k : sv) (e off : Z) (bd brest : list bitem) (s : wsub) (R : list sobj) (Xk : list (sv * sv)) : bool := ltac2:(tb__ "0|8|
S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S70VXk;S36VE;A1A2S6bVE;S67Vs;VR;S64S3S34S4cA2S34S9S34S4cA2S2bA4A5A2S75S3eVs;A2A2S7dVs;S6eA2A2S5dS3eS1aS33VE;A1M0A1M1A2A2S49G1S4bS1S3S15S15A2M2Vkept;S5G2SbS15S15Vd;S41Ve;Vk;A2A4S8G2A1A3M3A3S27S1S59S5cVs;S4eS68A1A2Vbrest;A3M4S4aA4A2A2S5bG1Vbrest;A2A2S6fVs;G3S69A3A2S73Vbd;G4A2A2S5aG4A1A2S25S72S71S67S6eVs;G1A4S2bA3A2S51S19G0A1M5A1A2S76G5Vkept;S27S4S2A1M6S4fVR;A6A2S5fVXGL;G5Vkept;S27G6S1cG0A1S50VXk;A8A2S3cZ0M7Ve;A2A2S3aVe;ZcA2A2S24S11S12S13Vk;S14S31A1A2A1G5A3A2S18S56Vs;P11A2Vk;A2A2S18S56Vs;PfA2Vd;A2A2S18S56Vs;PeA2S78A2A2S18S56Vs;PcA2S30Voff;A1A2A2S3aG7Voff;A2A2S3aVoff;Z4f8A2A2").

Definition land_chk (L C : axst) (s : wsub) (tv1 tv2 : list (sv * sv)) (bd1 bd2 : list bitem) (tvC : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S0S0S0S0S0S0S0S74Vtv1;Vtv2;A2S73Vbd1;Vbd2;A2A2S37VL;VC;Vs;A3A2S58Vs;S3eA2A2S5dS3eS1aS33VL;A1A1M0A2A2S49G0S4bVtv2;S27Vbd2;S4aA4A2A2S6fVs;Vtv2;VtvC;A3A2S4dVs;S27S27A3A2").

Definition reopen_chk (XGL : list (Z * Z)) (A : axst) (X' : list (sv * sv)) (tv : list (sv * sv)) (k1 k2 : Z) : bool := ltac2:(tb__ "0|3|
S0S0S0S0S0S0S0S0S0S18S35VA;A1S14S77A1A2S3aZ0Vk1;A2A2S3aVk1;Vk2;A2A2S3aVk2;Z40A2A2S52S19S33VA;A1M0A1M1A1A2S70VX';S36VA;A1A2A2S23S33S62VA;VX';S43Vk1;Vk2;A5A1A1A2S51G1A1A2S60G1Vtv;S27S4S2A1S4fS1cG0A1M2A6A2S5fVXGL;G1Vtv;S27ScS2U0A2G2S50VX';A8A2").

Definition release_chk (A : axst) (objs : list sobj) (k1 k2 : Z) (cells : list cell) (d : odefault) (L : list (Z * Z)) (tv : list (sv * sv)) (bd : list bitem) : bool := ltac2:(tb__ "0|2|
S0S0S0S0S0S0S0S0S0S18S35VA;A1S14S77A1A2S3aZ0Vk1;A2A2S3aVk1;Vk2;A2A2S3aVk2;Z40A2A2S22Vd;A1A2S52S19S33VA;A1M0A1M1A1A2S25S3S66S66A2S61Vcells;Vd;Vk1;Vk2;A4VL;A3A2S49S1aG0A1S4bVtv;S27Vbd;S4aA4A2A2S51G1A1A2S60G1Vtv;S27S4S2A1S4fVobjs;A6A2").

Definition xff_chk (T1 : axst) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S25S11S1eS1aS33VT1;A1M0A1A1S1S11VF;S19G0A1A3A3").

Definition purec_chk (XGL : list (Z * Z)) (Pre : axst) (Ls : list axst) (E : axst) (tv : list (sv * sv)) (bd : list bitem) (s : wsub) (R : list sobj) : bool := ltac2:(tb__ "0|5|
S0S0S0S0S0S0S0S0S6bVE;VPre;Vs;VR;VLs;A5S75S3eVs;A2A2S5dS3eS1aS33VE;A1M0A1M1A2A2S49G1S4bVtv;S27Vbd;S4aA4A2A2S5aVbd;A1A2S25S34S34S0S0SaS1dA1M2SdLx;S7cS33VPre;A1S33R1A1A2S10S1dG2SeLl;Ls0;Xax2S6dVPre;R1A2A2S18S35R1A1S35VPre;A1A2A2LL;VLs;A3A2S51S19G0A1M3A1A2S76G3Vtv;S27S4S2A1M4S4fVR;A6A2S5fVXGL;G3Vtv;S27G4S1cG0A1S50S36VE;A1A8A2").

Definition pure_chk (Pre P E : axst) (nd : ndesc) (s : wsub) (R : list sobj) : bool := ltac2:(tb__ "0|2|
S0S0S0S6cVE;VPre;Vs;VR;S5S34VP;S8S34A1A3A5S5dS3eS1aS33VE;A1M0A1M1A2A2S49G1Vnd;A2A2S25S11S1eG1A1S19G0A1A3A2").

Definition coF (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S0S0S0S0S24S11S12S2eZcM0Z1G0S2cS42A5A1VF;A3S24S11S12S13S2cS14S31A1A2A1VF;A3A2S24S11S12S13S42S2aA2A1VF;A3A2S6S24S11S12S13S2aS29A2A1VF;A3S24S11S12S1bS2aS29A2A1VF;A3A2A2S24S11S12S13S29S3fA2A1VF;A3A2S24S11S12S13S3fS40A2A1VF;A3A2S24S11S12S13S40S14S5eA1A2A1VF;A3A2").

Definition vrF (q : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S0S0S6S24S11S12S13Vq;S3fA2A1VF;A3S24S11S12S1bVq;S3fA2A1VF;A3A2S24S11S12S13S3fS40A2A1VF;A3A2S24S11S12S13S40S14S5eA1A2A1VF;A3A2").
Definition vlF (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S0S24S11S12S1bS6aS55A2A1VF;A3S24S11S12S13S55S28A2A1VF;A3A2S24S11S12S16S46S14Z2M0A1S26A3A1VF;A3A2S24S11S12S13S26S14S3bG0Z14A2A1A2A1VF;A3A2").

Definition slotF (c k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S24S11S12S13S17S45S41ZcM0Vc;A2S14G0A1A3S41G0Vk;A2A2A1VF;A3S24S11S12S13Vc;Vk;A2A1VF;A3A2S24S11S12S13Vk;S14S31A1A2A1VF;A3A2").

Definition rsF (d cm : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S0S24S11S12S13Vd;S14Z800000000000A1A2A1VF;A3S24S11S12S13Vcm;S14S31A1A2A1VF;A3A2").
Definition rsFk (d c k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S0S0S24S11S12S13Vd;S14Z800000000000A1A2A1VF;A3S24S11S12S13Vc;Vk;A2A1VF;A3A2S24S11S12S13Vk;S14S31A1A2A1VF;A3A2").

Definition gF (F : list sprop) : bool := ltac2:(tb__ "0|3|
S0S0S0S0S24S11S12S13S2fS14S32A1A2A1VF;A3S24S11S12S13S41ZcM0S2dA2M1S14S31A1M2A2A1VF;A3A2S24S11S12S13S2dG2A2A1VF;A3A2S24S11S12S13S41G0S26A2G1A2A1VF;A3A2S24S11S12S13S26S14S3bZ2Z14A2A1A2A1VF;A3A2").

Definition roomF (e r sl : Z) (c n : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S0S0S0S0S0S0S24S11S12S13Vc;Vn;A2A1VF;A3S24S11S12S13Vn;S14S31A1A2A1VF;A3A2S24S11S12S2eVe;Vr;Vsl;Vn;S42A5A1VF;A3A2S24S11S12S79S26A1A1VF;A3A2S24S11S12S13S42S3fA2A1VF;A3A2S24S11S12S13S3fS40A2A1VF;A3A2S24S11S12S13S40S14S5eA1A2A1VF;A3A2").
Definition vr3F (e r sl : Z) (c n : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S0S53Ve;Vr;Vsl;Vc;Vn;VF;A6S24S11S12S16S47S26S14Z3A1A3A1VF;A3A2").
Definition vrLF (e r sl : Z) (c n : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S0S0S53Ve;Vr;Vsl;Vc;Vn;VF;A6S24S11S12S1bS6aS55A2A1VF;A3A2S24S11S12S13S55S28A2A1VF;A3A2S24S11S12S16S46S14Z2M0A1S26A3A1VF;A3A2S24S11S12S13S26S14S3bG0Z14A2A1A2A1VF;A3A2").

Definition triAF (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S24S11S12S20S16S47S26S14Z3A1A3A1A1VF;A3S24S11S12S16S46S14Z2M0A1S26A3A1VF;A3A2S24S11S12S13S26S14S3bG0Z14A2A1A2A1VF;A3A2").

Definition live3F (a k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S0S0S24S11S12S16S47Va;S14Z3A1A3A1VF;A3S24S11S12S13Va;Vk;A2A1VF;A3A2S24S11S12S13Vk;S14S31A1A2A1VF;A3A2").
Definition liveTri (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S0S24S11S12S13S17S45S17S48S28S14Z1A1A3S28A3Vk;A2A1VF;A3S24S11S12S16S46S14Z2M0A1S26A3A1VF;A3A2S24S11S12S13S26S14S3bG0Z14A2A1A2A1VF;A3A2S24S11S12S13Vk;S14S31A1A2A1VF;A3A2").
Definition liveRp (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S0S24S11S12S13S17S45S17S48S26S14Z1A1A3S26A3Vk;A2A1VF;A3S24S11S12S16S46S14Z2M0A1S26A3A1VF;A3A2S24S11S12S13S26S14S3bG0Z14A2A1A2A1VF;A3A2S24S11S12S13Vk;S14S31A1A2A1VF;A3A2").
Definition liveTs (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S0S0S24S11S12S13S7aVk;A2A1VF;A3S54VF;A1A2S24S11S12S13Vk;S14S31A1A2A1VF;A3A2").

Definition liveFa (x a : sv) (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S0S24S11S12S13S17S45Vx;Va;A3Vk;A2A1VF;A3S24S11S12S16S47Va;S14Z3A1A3A1VF;A3A2S24S11S12S13Vk;S14S31A1M0A2A1VF;A3A2S6S24S11S12S13Vx;G0A2A1VF;A3S24S11S12S13Vx;Vk;A2A1VF;A3A2A2").
Definition liveF (x : sv) (c : Z) (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S24S11S12S13S17S45Vx;S14Vc;A1A3Vk;A2A1VF;A3S24S11S12S13Vk;S14S31A1M0A2A1VF;A3A2S6S24S11S12S13Vx;G0A2A1VF;A3S24S11S12S13Vx;Vk;A2A1VF;A3A2A2").

Definition tv_rm (i : nat) (tv : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|1|
S1S3S15S15A2M0S63G0Vi;Vtv;A3S65G0S7Vi;A1Vtv;A3A3").
Definition bd_rm2 (j : nat) (bd : list bitem) : list bitem := ltac2:(tb__ "0|0|
S1S59S63S59Vj;Vbd;A3S65S59S7S7Vj;A1A1Vbd;A3A3").
Definition tv_sb (s : wsub) (tv : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|1|
S64S3S15S15A2M0G0G0SbS15S15S57Vs;S9S15S15R1A3A2S57Vs;SfS15S15R1A3A2A4Lt;Vtv;A4").
Definition land_sub (L C : axst) : wsub := ltac2:(tb__ "0|0|
S7bS3eS33VL;A1S33VC;A1A3").

Definition cells_pro : list cell := Eval vm_compute in ob_cells sh_pro.

Definition E_co1 : axst := Eval vm_compute in optAp (apply_axforms E_co0 (xf_vr 19 720)).
Definition kept_co : list (sv * sv) := Eval vm_compute in tv_rm 5 (tv_body pDco pKco).
Definition brest_co : list bitem := Eval vm_compute in bd_rm2 2 (bd_loop pQ pKco).
Definition tvG_co : list (sv * sv) := Eval vm_compute in import_tv (import_subA s_co VN.Pre_vr VN.P_grown E_co) VN.tvP.
Definition bdK_co : list bitem := Eval vm_compute in bd_subst (import_subA s_co VN.Pre_vr VN.P_keep E_co) (nd_bd VN.nd0).
Definition bdG_co : list bitem := Eval vm_compute in bd_subst (import_subA s_co VN.Pre_vr VN.P_grown E_co) (VN.bdP VN.vN VN.vKn).

Definition s_cok : wsub := Eval vm_compute in land_sub T_coks JR_co.
Definition s_cog : wsub := Eval vm_compute in land_sub T_cog JR_co.
Definition s_cof : wsub := Eval vm_compute in land_sub T_cof JF_co.
Definition tv2_cok : list (sv * sv) := Eval vm_compute in tv_sb s_cok (tv_body pD2 pK2).
Definition tv2_cog : list (sv * sv) := Eval vm_compute in tv_sb s_cog (tv_body pD2 pK2).
Definition tv2_cof : list (sv * sv) := Eval vm_compute in tv_sb s_cof (tv_body pD2 pK2).
Definition bd2_cok : list bitem := Eval vm_compute in bd_subst s_cok (bd_loop pQ pK2).
Definition bd2_cog : list bitem := Eval vm_compute in bd_subst s_cog (bd_loop pQ pK2).
Definition bd2_cof : list bitem := Eval vm_compute in bd_subst s_cof [PROG cVF pQ].

Definition E_pc2 : axst := Eval vm_compute in reshapeA E_pc1 34 (slot_obj pD2 pA).
Definition T_pc2 : axst := Eval vm_compute in optAp (apply_axforms T_pc1 [AXSelect sel_pc; AXMerge 0; AXMerge 32; AXMerge 32]).
Definition T_da2 : axst := Eval vm_compute in optAp (apply_axforms T_da0 [AXSelect sel_da; AXMerge 0]).
Definition T_dg2 : axst := Eval vm_compute in optAp (apply_axforms T_dg0 [AXSelect sel_da; AXMerge 0]).

Definition E_mi1x : axst := Eval vm_compute in optAp (apply_axforms E_mi0 (xf_vr 15 496)).
Definition kept_mi : list (sv * sv) := Eval vm_compute in tv_rm 1 (nd_tv ndXA).
Definition brest_mi : list bitem := Eval vm_compute in bd_rm2 3 (nd_bd ndXA).
Definition bdK_mi : list bitem := Eval vm_compute in bd_subst (import_subA s_mi VN.Pre_vr VN.P_keep E_mi) (nd_bd VN.nd0).
Definition bdG_mi : list bitem := Eval vm_compute in bd_subst (import_subA s_mi VN.Pre_vr VN.P_grown E_mi) (VN.bdP VN.vN VN.vKn).
Definition s_mik : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA T_miks (ax_X T_miks) hG 4 5) JR_mi.
Definition tv2_mik : list (sv * sv) := Eval vm_compute in tv_sb s_mik (nd_tv ndMI).
Definition bd2_mik : list bitem := Eval vm_compute in bd_subst s_mik (nd_bd ndMI).
Definition s_mif : wsub := Eval vm_compute in land_sub T_mifs JF_mi.
Definition tv2_mif : list (sv * sv) := Eval vm_compute in tv_sb s_mif (nd_tv ndMIf).
Definition s_mig : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA T_migs (ax_X T_migs) hG 4 5) JR_mi.
Definition tv2_mig : list (sv * sv) := Eval vm_compute in tv_sb s_mig (nd_tv ndMI).
Definition bd2_mig : list bitem := Eval vm_compute in bd_subst s_mig (nd_bd ndMI).

Definition cells_fv : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S E_fv0)) O_Wf).
Definition E_fv1x : axst := Eval vm_compute in optAp (apply_axforms E_fv1 (xf_vr 16 528)).
Definition kept_fv : list (sv * sv) := Eval vm_compute in tv_rm 2 (nd_tv ndMI).
Definition brest_fv : list bitem := Eval vm_compute in bd_rm2 5 (nd_bd ndMI).
Definition bdK_fv : list bitem := Eval vm_compute in bd_subst (import_subA s_fv VN.Pre_vr VN.P_keep E_fv) (nd_bd VN.nd0).
Definition bdG_fv : list bitem := Eval vm_compute in bd_subst (import_subA s_fv VN.Pre_vr VN.P_grown E_fv) (VN.bdP VN.vN VN.vKn).
Definition s_fvk : wsub := Eval vm_compute in land_sub T_fvks JR_fv.
Definition tv2_fvk : list (sv * sv) := Eval vm_compute in tv_sb s_fvk (nd_tv ndFV).
Definition bd2_fvk : list bitem := Eval vm_compute in bd_subst s_fvk (nd_bd ndFV).
Definition s_fvf : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA T_fvf (X_face pDmi fv_d mm_d sg_d pDco rp_d tr_d ts_d pKmi fv_k mm_k sg_k pKco rp_k tr_k ts_k) hG 4 5) JF_fv.
Definition tv2_fvf : list (sv * sv) := Eval vm_compute in tv_sb s_fvf (nd_tv ndFVf).
Definition s_fvg : wsub := Eval vm_compute in land_sub T_fvg JR_fv.
Definition tv2_fvg : list (sv * sv) := Eval vm_compute in tv_sb s_fvg (nd_tv ndFV).
Definition bd2_fvg : list bitem := Eval vm_compute in bd_subst s_fvg (nd_bd ndFV).

Definition E_mm1x : axst := Eval vm_compute in optAp (apply_axforms E_mm0 (xf_vr 17 560)).
Definition kept_mm : list (sv * sv) := Eval vm_compute in tv_rm 3 (nd_tv ndFV).
Definition brest_mm : list bitem := Eval vm_compute in bd_rm2 7 (nd_bd ndFV).
Definition bdK_mm : list bitem := Eval vm_compute in bd_subst (import_subA s_mm VN.Pre_vr VN.P_keep E_mm) (nd_bd VN.nd0).
Definition bdG_mm : list bitem := Eval vm_compute in bd_subst (import_subA s_mm VN.Pre_vr VN.P_grown E_mm) (VN.bdP VN.vN VN.vKn).
Definition s_mmk : wsub := Eval vm_compute in land_sub T_mmks JR_mm.
Definition tv2_mmk : list (sv * sv) := Eval vm_compute in tv_sb s_mmk (nd_tv ndMM).
Definition bd2_mmk : list bitem := Eval vm_compute in bd_subst s_mmk (nd_bd ndMM).
Definition s_mmf : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA T_mmf (XMM mm_d mm_k) hG 4 5) JF_mm.
Definition tv2_mmf : list (sv * sv) := Eval vm_compute in tv_sb s_mmf (nd_tv ndMMf).
Definition s_mmg : wsub := Eval vm_compute in land_sub T_mmg JR_mm.
Definition tv2_mmg : list (sv * sv) := Eval vm_compute in tv_sb s_mmg (nd_tv ndMM).
Definition bd2_mmg : list bitem := Eval vm_compute in bd_subst s_mmg (nd_bd ndMM).

Definition E_sg1x : axst := Eval vm_compute in optAp (apply_axforms E_sg0 (xf_vr 18 592)).
Definition kept_sg : list (sv * sv) := Eval vm_compute in tv_rm 4 (nd_tv ndMM).
Definition brest_sg : list bitem := Eval vm_compute in bd_rm2 9 (nd_bd ndMM).
Definition bdK_sg : list bitem := Eval vm_compute in bd_subst (import_subA s_sg VN.Pre_vr VN.P_keep E_sg) (nd_bd VN.nd0).
Definition bdG_sg : list bitem := Eval vm_compute in bd_subst (import_subA s_sg VN.Pre_vr VN.P_grown E_sg) (VN.bdP VN.vN VN.vKn).
Definition s_sgk : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA T_sgks (XnoL T_sgks) hG 4 5) JR_sg.
Definition tv2_sgk : list (sv * sv) := Eval vm_compute in tv_sb s_sgk (nd_tv ndSG).
Definition bd2_sgk : list bitem := Eval vm_compute in bd_subst s_sgk (nd_bd ndSG).
Definition s_sgf : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA T_sgf (XnoL T_sgf) hG 4 5) JF_sg.
Definition tv2_sgf : list (sv * sv) := Eval vm_compute in tv_sb s_sgf (nd_tv ndSGf).
Definition s_sgg : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA T_sgg (XnoL T_sgg) hG 4 5) JR_sg.
Definition tv2_sgg : list (sv * sv) := Eval vm_compute in tv_sb s_sgg (nd_tv ndSG).
Definition bd2_sgg : list bitem := Eval vm_compute in bd_subst s_sgg (nd_bd ndSG).

Definition E_trg1x : axst := Eval vm_compute in optAp (apply_axforms E_trg0 (xf_vr 21 784)).
Definition kept_trg : list (sv * sv) := Eval vm_compute in tv_rm 7 (nd_tv ndXA).
Definition brest_trg : list bitem := Eval vm_compute in bd_rm2 13 (nd_bd ndXA).
Definition bdK_trg : list bitem := Eval vm_compute in bd_subst (import_subA s_trg VN.Pre_vr VN.P_keep E_trg) (nd_bd VN.nd0).
Definition bdG_trg : list bitem := Eval vm_compute in bd_subst (import_subA s_trg VN.Pre_vr VN.P_grown E_trg) (VN.bdP VN.vN VN.vKn).
Definition T_trgk0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_trg s_trg R_trg VN.P_keep (XkeepF tr_d (X_body pDco pKco)).
Definition T_trgf0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_trg s_trg R_trg VN.P_fail (XkeepF tr_d (X_body pDco pKco)).
Definition T_trgg0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_trg s_trg R_trg VN.P_grown (XkeepF tr_d (X_body pDco pKco)).
Definition T_trgk1 : axst := Eval vm_compute in optAp (apply_axforms T_trgk0 (xf_backV 20 34 784)).
Definition s_trgk : wsub := Eval vm_compute in land_sub T_trgk JR_trg.
Definition tv2_trgk : list (sv * sv) := Eval vm_compute in tv_sb s_trgk (nd_tv ndTR).
Definition bd2_trgk : list bitem := Eval vm_compute in bd_subst s_trgk (nd_bd ndTR).
Definition s_trgf : wsub := Eval vm_compute in land_sub T_trgf JF_trg.
Definition tv2_trgf : list (sv * sv) := Eval vm_compute in tv_sb s_trgf (nd_tv ndTRf).
Definition s_trgg : wsub := Eval vm_compute in land_sub T_trgg JR_trg.
Definition tv2_trgg : list (sv * sv) := Eval vm_compute in tv_sb s_trgg (nd_tv ndTR).
Definition bd2_trgg : list bitem := Eval vm_compute in bd_subst s_trgg (nd_bd ndTR).

Definition E_trb1x : axst := Eval vm_compute in optAp (apply_axforms E_trb0 (xf_vr 21 784)).
Definition kept_trb : list (sv * sv) := Eval vm_compute in tv_rm 7 (nd_tv ndXA).
Definition brest_trb : list bitem := Eval vm_compute in bd_rm2 13 (nd_bd ndXA).
Definition bdK_trb : list bitem := Eval vm_compute in bd_subst (import_subA s_trb VN.Pre_vr VN.P_keep E_trb) (nd_bd VN.nd0).
Definition bdG_trb : list bitem := Eval vm_compute in bd_subst (import_subA s_trb VN.Pre_vr VN.P_grown E_trb) (VN.bdP VN.vN VN.vKn).
Definition T_trbk0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_trb s_trb R_trb VN.P_keep (XkeepF tr_d (X_body pDco pKco)).
Definition T_trbf0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_trb s_trb R_trb VN.P_fail (XkeepF tr_d (X_body pDco pKco)).
Definition T_trbg0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_trb s_trb R_trb VN.P_grown (XkeepF tr_d (X_body pDco pKco)).
Definition T_trbk1 : axst := Eval vm_compute in optAp (apply_axforms T_trbk0 (xf_backV 20 34 784)).
Definition s_trbk : wsub := Eval vm_compute in land_sub T_trbk JR_trb.
Definition tv2_trbk : list (sv * sv) := Eval vm_compute in tv_sb s_trbk (nd_tv ndTR).
Definition bd2_trbk : list bitem := Eval vm_compute in bd_subst s_trbk (nd_bd ndTR).
Definition s_trbf : wsub := Eval vm_compute in land_sub T_trbf JF_trb.
Definition tv2_trbf : list (sv * sv) := Eval vm_compute in tv_sb s_trbf (nd_tv ndTRf).
Definition s_trbg : wsub := Eval vm_compute in land_sub T_trbg JR_trb.
Definition tv2_trbg : list (sv * sv) := Eval vm_compute in tv_sb s_trbg (nd_tv ndTR).
Definition bd2_trbg : list bitem := Eval vm_compute in bd_subst s_trbg (nd_bd ndTR).

Definition E_rp1x : axst := Eval vm_compute in optAp (apply_axforms E_rp0 (xf_vr 20 752)).
Definition kept_rp : list (sv * sv) := Eval vm_compute in tv_rm 6 (nd_tv ndTR).
Definition brest_rp : list bitem := Eval vm_compute in bd_rm2 11 (nd_bd ndTR).
Definition bdK_rp : list bitem := Eval vm_compute in bd_subst (import_subA s_rp VN.Pre_vr VN.P_keep E_rp) (nd_bd VN.nd0).
Definition bdG_rp : list bitem := Eval vm_compute in bd_subst (import_subA s_rp VN.Pre_vr VN.P_grown E_rp) (VN.bdP VN.vN VN.vKn).
Definition T_rpk0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_rp s_rp R_rp VN.P_keep (XkeepF rp_d (XTR pDtr pKtr)).
Definition T_rpf0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_rp s_rp R_rp VN.P_fail (XkeepF rp_d (XTR pDtr pKtr)).
Definition T_rpg0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_rp s_rp R_rp VN.P_grown (XkeepF rp_d (XTR pDtr pKtr)).
Definition T_rpk1 : axst := Eval vm_compute in optAp (apply_axforms T_rpk0 (xf_backV 19 33 752)).
Definition s_rpk : wsub := Eval vm_compute in land_sub T_rpk JR_rp.
Definition tv2_rpk : list (sv * sv) := Eval vm_compute in tv_sb s_rpk (nd_tv ndRP).
Definition bd2_rpk : list bitem := Eval vm_compute in bd_subst s_rpk (nd_bd ndRP).
Definition s_rpf : wsub := Eval vm_compute in land_sub T_rpf JF_rp.
Definition tv2_rpf : list (sv * sv) := Eval vm_compute in tv_sb s_rpf (nd_tv ndRPf).
Definition s_rpg : wsub := Eval vm_compute in land_sub T_rpg JR_rp.
Definition tv2_rpg : list (sv * sv) := Eval vm_compute in tv_sb s_rpg (nd_tv ndRP).
Definition bd2_rpg : list bitem := Eval vm_compute in bd_subst s_rpg (nd_bd ndRP).

Definition E_ts1x : axst := Eval vm_compute in optAp (apply_axforms E_ts0 (xf_vr 22 816)).
Definition kept_ts : list (sv * sv) := Eval vm_compute in tv_rm 8 (nd_tv ndRP).
Definition brest_ts : list bitem := Eval vm_compute in bd_rm2 15 (nd_bd ndRP).
Definition bdK_ts : list bitem := Eval vm_compute in bd_subst (import_subA s_ts VN.Pre_vr VN.P_keep E_ts) (nd_bd VN.nd0).
Definition bdG_ts : list bitem := Eval vm_compute in bd_subst (import_subA s_ts VN.Pre_vr VN.P_grown E_ts) (VN.bdP VN.vN VN.vKn).
Definition T_tsk0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_ts s_ts R_ts VN.P_keep (XkeepF ts_d (XRT pDrp pKrp ts_d ts_k)).
Definition T_tsf0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_ts s_ts R_ts VN.P_fail (XkeepF ts_d (XRT pDrp pKrp ts_d ts_k)).
Definition T_tsg0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_ts s_ts R_ts VN.P_grown (XkeepF ts_d (XRT pDrp pKrp ts_d ts_k)).
Definition T_tsk1 : axst := Eval vm_compute in optAp (apply_axforms T_tsk0 (xf_backV 21 35 816)).
Definition s_tsk : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA T_tsk (ax_X T_tsk) hG 6 23) JR_ts.
Definition tv2_tsk : list (sv * sv) := Eval vm_compute in tv_sb s_tsk (nd_tv ndTS).
Definition bd2_tsk : list bitem := Eval vm_compute in bd_subst s_tsk (nd_bd ndTS).
Definition s_tsf : wsub := Eval vm_compute in land_sub T_tsf JF_ts.
Definition tv2_tsf : list (sv * sv) := Eval vm_compute in tv_sb s_tsf (nd_tv ndTSf).
Definition s_tsg : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA T_tsg (ax_X T_tsg) hG 6 23) JR_ts.
Definition tv2_tsg : list (sv * sv) := Eval vm_compute in tv_sb s_tsg (nd_tv ndTS).
Definition bd2_tsg : list bitem := Eval vm_compute in bd_subst s_tsg (nd_bd ndTS).

Definition cells_mi4 : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S E_mi4_0)) O_Wf).
Definition E_mi41x : axst := Eval vm_compute in optAp (apply_axforms E_mi4_1 (xf_vr 15 496)).
Definition kept_mi4 : list (sv * sv) := Eval vm_compute in tv_rm 1 (nd_tv ndLL).
Definition brest_mi4 : list bitem := Eval vm_compute in bd_rm2 3 (nd_bd ndLL).
Definition bdK_mi4 : list bitem := Eval vm_compute in bd_subst (import_subA s_mi4 VN.Pre_vr VN.P_keep E_mi4) (nd_bd VN.nd0).
Definition bdG_mi4 : list bitem := Eval vm_compute in bd_subst (import_subA s_mi4 VN.Pre_vr VN.P_grown E_mi4) (VN.bdP VN.vN VN.vKn).
Definition T_mi4k0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mi4 s_mi4 R_mi4 VN.P_keep (XkeepF lDmi (ax_X E_mi4_1)).
Definition T_mi4f0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mi4 s_mi4 R_mi4 VN.P_fail (XkeepF lDmi (ax_X E_mi4_1)).
Definition T_mi4g0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mi4 s_mi4 R_mi4 VN.P_grown (XkeepF lDmi (ax_X E_mi4_1)).
Definition T_mi4k1 : axst := Eval vm_compute in optAp (apply_axforms T_mi4k0 (xf_backV 14 28 496)).
Definition s_mi4k : wsub := Eval vm_compute in land_sub T_mi4k JR_mi4.
Definition tv2_mi4k : list (sv * sv) := Eval vm_compute in tv_sb s_mi4k (nd_tv ndL4a).
Definition bd2_mi4k : list bitem := Eval vm_compute in bd_subst s_mi4k (nd_bd ndL4a).
Definition s_mi4f : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA (shadow_reopen_stateA T_mi4f (XnoLoc T_mi4f) hG 38 39) (XnoLoc T_mi4f) hG 28 33) JF_mi4.
Definition tv2_mi4f : list (sv * sv) := Eval vm_compute in tv_sb s_mi4f (nd_tv ndL4af).
Definition s_mi4g : wsub := Eval vm_compute in land_sub T_mi4g JR_mi4.
Definition tv2_mi4g : list (sv * sv) := Eval vm_compute in tv_sb s_mi4g (nd_tv ndL4a).
Definition bd2_mi4g : list bitem := Eval vm_compute in bd_subst s_mi4g (nd_bd ndL4a).

Definition E_fv41x : axst := Eval vm_compute in optAp (apply_axforms E_fv4_0 (xf_vr 16 528)).
Definition kept_fv4 : list (sv * sv) := Eval vm_compute in tv_rm 2 (nd_tv ndL4a).
Definition brest_fv4 : list bitem := Eval vm_compute in bd_rm2 5 (nd_bd ndL4a).
Definition bdK_fv4 : list bitem := Eval vm_compute in bd_subst (import_subA s_fv4 VN.Pre_vr VN.P_keep E_fv4) (nd_bd VN.nd0).
Definition bdG_fv4 : list bitem := Eval vm_compute in bd_subst (import_subA s_fv4 VN.Pre_vr VN.P_grown E_fv4) (VN.bdP VN.vN VN.vKn).
Definition T_fv4k0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_fv4 s_fv4 R_fv4 VN.P_keep (XkeepF lDfv (ax_X E_fv4_0)).
Definition T_fv4f0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_fv4 s_fv4 R_fv4 VN.P_fail (XkeepF lDfv (ax_X E_fv4_0)).
Definition T_fv4g0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_fv4 s_fv4 R_fv4 VN.P_grown (XkeepF lDfv (ax_X E_fv4_0)).
Definition T_fv4k1 : axst := Eval vm_compute in optAp (apply_axforms T_fv4k0 (xf_backV 15 29 528)).
Definition s_fv4k : wsub := Eval vm_compute in land_sub T_fv4k JR_fv4.
Definition tv2_fv4k : list (sv * sv) := Eval vm_compute in tv_sb s_fv4k (nd_tv ndL4b).
Definition bd2_fv4k : list bitem := Eval vm_compute in bd_subst s_fv4k (nd_bd ndL4b).
Definition s_fv4f : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA (shadow_reopen_stateA T_fv4f (XnoLoc T_fv4f) hG 38 39) (XnoLoc T_fv4f) hG 28 33) JF_fv4.
Definition tv2_fv4f : list (sv * sv) := Eval vm_compute in tv_sb s_fv4f (nd_tv ndL4bf).
Definition s_fv4g : wsub := Eval vm_compute in land_sub T_fv4g JR_fv4.
Definition tv2_fv4g : list (sv * sv) := Eval vm_compute in tv_sb s_fv4g (nd_tv ndL4b).
Definition bd2_fv4g : list bitem := Eval vm_compute in bd_subst s_fv4g (nd_bd ndL4b).

Definition E_mm41x : axst := Eval vm_compute in optAp (apply_axforms E_mm4_0 (xf_vr 17 560)).
Definition kept_mm4 : list (sv * sv) := Eval vm_compute in tv_rm 3 (nd_tv ndL4b).
Definition brest_mm4 : list bitem := Eval vm_compute in bd_rm2 7 (nd_bd ndL4b).
Definition bdK_mm4 : list bitem := Eval vm_compute in bd_subst (import_subA s_mm4 VN.Pre_vr VN.P_keep E_mm4) (nd_bd VN.nd0).
Definition bdG_mm4 : list bitem := Eval vm_compute in bd_subst (import_subA s_mm4 VN.Pre_vr VN.P_grown E_mm4) (VN.bdP VN.vN VN.vKn).
Definition T_mm4k0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mm4 s_mm4 R_mm4 VN.P_keep (XkeepF lDmm (ax_X E_mm4_0)).
Definition T_mm4f0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mm4 s_mm4 R_mm4 VN.P_fail (XkeepF lDmm (ax_X E_mm4_0)).
Definition T_mm4g0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_mm4 s_mm4 R_mm4 VN.P_grown (XkeepF lDmm (ax_X E_mm4_0)).
Definition T_mm4k1 : axst := Eval vm_compute in optAp (apply_axforms T_mm4k0 (xf_backV 16 30 560)).
Definition s_mm4k : wsub := Eval vm_compute in land_sub T_mm4k JR_mm4.
Definition tv2_mm4k : list (sv * sv) := Eval vm_compute in tv_sb s_mm4k (nd_tv ndL4c).
Definition bd2_mm4k : list bitem := Eval vm_compute in bd_subst s_mm4k (nd_bd ndL4c).
Definition s_mm4f : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA (shadow_reopen_stateA T_mm4f (XnoLoc T_mm4f) hG 28 33) (XnoLoc T_mm4f) hG 38 39) JF_mm4.
Definition tv2_mm4f : list (sv * sv) := Eval vm_compute in tv_sb s_mm4f (nd_tv ndL4cf).
Definition s_mm4g : wsub := Eval vm_compute in land_sub T_mm4g JR_mm4.
Definition tv2_mm4g : list (sv * sv) := Eval vm_compute in tv_sb s_mm4g (nd_tv ndL4c).
Definition bd2_mm4g : list bitem := Eval vm_compute in bd_subst s_mm4g (nd_bd ndL4c).

Definition E_sg41x : axst := Eval vm_compute in optAp (apply_axforms E_sg4_0 (xf_vr 18 592)).
Definition kept_sg4 : list (sv * sv) := Eval vm_compute in tv_rm 4 (nd_tv ndL4c).
Definition brest_sg4 : list bitem := Eval vm_compute in bd_rm2 9 (nd_bd ndL4c).
Definition bdK_sg4 : list bitem := Eval vm_compute in bd_subst (import_subA s_sg4 VN.Pre_vr VN.P_keep E_sg4) (nd_bd VN.nd0).
Definition bdG_sg4 : list bitem := Eval vm_compute in bd_subst (import_subA s_sg4 VN.Pre_vr VN.P_grown E_sg4) (VN.bdP VN.vN VN.vKn).
Definition T_sg4k0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_sg4 s_sg4 R_sg4 VN.P_keep (XkeepF lDsg (ax_X E_sg4_0)).
Definition T_sg4f0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_sg4 s_sg4 R_sg4 VN.P_fail (XkeepF lDsg (ax_X E_sg4_0)).
Definition T_sg4g0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_sg4 s_sg4 R_sg4 VN.P_grown (XkeepF lDsg (ax_X E_sg4_0)).
Definition T_sg4k1 : axst := Eval vm_compute in optAp (apply_axforms T_sg4k0 (xf_backV 17 31 592)).
Definition s_sg4k : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA (shadow_reopen_stateA T_sg4k (XnoLoc T_sg4k) hG 28 33) (XnoLoc T_sg4k) hG 38 39) JR_sg4.
Definition tv2_sg4k : list (sv * sv) := Eval vm_compute in tv_sb s_sg4k (nd_tv ndL4d).
Definition bd2_sg4k : list bitem := Eval vm_compute in bd_subst s_sg4k (nd_bd ndL4d).
Definition s_sg4f : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA (shadow_reopen_stateA T_sg4f (XnoLoc T_sg4f) hG 28 33) (XnoLoc T_sg4f) hG 38 39) JF_sg4.
Definition tv2_sg4f : list (sv * sv) := Eval vm_compute in tv_sb s_sg4f (nd_tv ndL4df).
Definition s_sg4g : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA (shadow_reopen_stateA T_sg4g (XnoLoc T_sg4g) hG 28 33) (XnoLoc T_sg4g) hG 38 39) JR_sg4.
Definition tv2_sg4g : list (sv * sv) := Eval vm_compute in tv_sb s_sg4g (nd_tv ndL4d).
Definition bd2_sg4g : list bitem := Eval vm_compute in bd_subst s_sg4g (nd_bd ndL4d).
End Lib_handle_f_gdefs.

(* [comment removed for export] *)
Module Lib_handle_f_nodes2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SAlu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "z0"; "VL"; "VR"; "ndLL"; "ndRP"; "ndTS"; "ndTR"; "ndL4a"; "ndMI"; "VK3"; "ndFV"; "ndL4b"; "ndP"; "ndH"; "ndJN"; "ndL4c"; "ndMM"; "ndT"; "ndTRf"; "ndEf'"; "ndEo'"; "ndFVf"; "ndJ"; "ndL4af"; "ndL4bf"; "ndL4cf"; "ndL4d"; "ndL4df"; "ndMIf"; "ndMMf"; "ndRPf"; "ndSG"; "ndSGf"; "ndTSf"; "vC36"; "vT36"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "ndXA"; "ndEf"; "ndEo"; "C36"; "E_dg0"; "E_fv0"; "E_mi0"; "E_mm0"; "JF_fv"; "JF_mi"; "JR_fv"; "JR_mi"; "RJ"; "RW"; "T_dg"; "T_mcq"; "XA"; "X_conull"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pQ"; "ndR"; "nd0"; "C_pre"; "C_pro"; "E_co0"; "E_sm0"; "H"; "JF_co"; "JR_co"; "K"; "L1"; "L2"; "Pre_hf"; "X_pro"; "am1"; "am2"; "ndFc"; "pP"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi"; "C_Ef2"; "C_Eo2"; "C_rlf"; "C_rlo"; "E_f5f0"; "E_f5o0"; "P_fail"; "P_ok"; "T_f5f"; "T_f5o"; "XEf42"; "XEo42"; "X_rlf"; "X_rlo"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2"; "cutsF2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1"; "E_da0"; "E_pc0"; "T_da"; "T_ms"; "T_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10"; "XEf6a"; "XEf6b"; "XEo6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3"; "E_sg0"; "JF_mm"; "JF_sg"; "JR_mm"; "JR_sg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "E_tdg0"; "E_trb0"; "E_trg0"; "JF_trb"; "JF_trg"; "JR_trb"; "JR_trg"; "K1"; "K1Xb"; "K1Xg"; "K2"; "T_tdg"; "pI"; "pT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5"; "E_rp0"; "E_ts0"; "JF_rp"; "JF_ts"; "JR_rp"; "JR_ts"; "K3"; "K3m"; "K3x"; "TS"; "X_avnull"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6"; "E_pg0"; "T_md"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7"; "E_wdg0"; "J"; "T_pgiR"; "T_pgoR"; "T_wdg"; "XJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8"; "E_g1_0"; "E_g2_0"; "E_g3_0"; "L14"; "T_g1"; "T_g2"; "XLJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w"; "E_mi4_0_0"; "E_mi4_0_4"; "T_g3_0"; "T_g3_4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9"; "C_T36"; "E_fv4_0"; "JF_fv4"; "JF_mi4"; "JR_fv4"; "JR_mi4"; "T_c4"; "T_m4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b"; "E_mm4_0"; "E_sg4_0"; "JF_mm4"; "JF_sg4"; "JR_mm4"; "JR_sg4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA"; "ejcert_hdr"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes Lib_handle_f_s8w.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition cutsF2 : list edescA := ltac2:(tb__ "0|1b|
S1S2S2S6S7A2M0S2S8S9A2M1A2M2S0G0G1S0S6S7S4eS43A4S0S8S9Z64SbA4A4S1G2S0G0G1S0S6S7S45S17A4S0S8S9Z60SbA4A4S1G2S0G0G1S0S6S7S44S17A4S0S8S9Z5cSbA4A4S1G2S0G0G1S0S6S7S48S18A4S0S8S9Z50M3SdS53Z2M4A2A4A4S1G2S0G0G1S0S6S7S4cS18A4S0S8S9G3SdS41Z1M5A2A4A4S1G2S0G0G1S0S6S7S4dS1cA4S0S8S9G3SdS41Z0M6A2A4A4S1G2S0G0G1S0S6S7S4bS1cA4S0S8S9G3SdS41Z3cM7A2A4A4S1G2S0G0G1S0S6S7S4aS42A4S0S8S9G3SdS41Z3aM8A2A4A4S1G2S0G0G1S0S6S7S49S52A4S0S8S9Z1eSbA4A4S1G2S0G0G1S0S6S7S6bS42A4S0S8S9G3SdS41Z38M9A2A4A4S1G2S0G0G1S0S6S7S6cS42A4S0S8S9G3SdS41Z36MaA2A4A4S1G2S0G0G1S0S6S7S6aS42A4S0S8S9G3SdS41Z34MbA2A4A4S1G2S0G0G1S0S6S7S3fS2fA4S0S8S9Z46SbA4A4S1G2S0G0G1S0S6S7S3dS2fA4S0S8S9Z44SbA4A4S1G2S0G0G1S0S6S7S3cS2fA4S0S8S9Z42McSbA4A4S1G2S0G0G1S0S6S7S3aS13A4S0S8S9Z40SbA4MdA4S1G2S0G0G1S0S6S7S38S27A4S0S8S9Z14SbA4MeA4S1G2S0G0G1S0S6S7S32S13A4S0S8S9Z3eMfS2dA4A4S1G2S0G0G1S0S6S7S3bS13A4S0S8S9G7SbA4M10A4S1G2S0G0G1S0S6S7S39S15A4S0S8S9G8SbA4A4S1G2S0G0G1S0S6S7S37S20A4GeA4S1G2S0G0G1S0S6S7S3eS15A4S0S8S9G9SbA4M11A4S1G2S0G0G1S0S6S7S73S1bA4S0S8S9GaSbA4M12A4S1G2S0G0G1S0S6S7S71S28A4GeA4S1G2S0G0G1S0S6S7S74S2aA4S0S8S9GbSbA4M13A4S1G2S0G0G1S0S6S7S72S2bA4GeA4S1G2S0G0G1S0S6S7S7cS2fA4S0S8S9GcSaS54S50S81A3A4A4S1G2S0G0G1S0S6S7S7eS2fA4GdA4S1G2S0G0G1S0S6S7S7dS2fA4GdA4S1G2S0G0G1S0S6S7S7bS11A4S0S8S9GfSbA4M14A4S1G2S0G0G1S0S6S7S79S1dA4GeA4S1G2S0G0G1S0S6S7S7aS11A4G14A4S1G2S0G0G1S0S6S7S78S1dA4GeA4S1G2S0G0G1S0S6S7S80S11A4G10A4S1G2S0G0G1S0S6S7S7fS11A4S0S8S9G8SaS54S51S82A3A4A4S1G2S0G0G1S0S6S7S87SfA4G10A4S1G2S0G0G1S0S6S7S85S29A4GeA4S1G2S0G0G1S0S6S7S89SfA4S0S8S9G8S14G4A1A4A4S1G2S0G0G1S0S6S7S8aSfA4S0S8S9G8S14G5A1A4A4S1G2S0G0G1S0S6S7S8bSfA4S0S8S9G8S14G6A1A4A4S1G2S0G0G1S0S6S7S8cSfA4G11A4S1G2S0G0G1S0S6S7S88S10A4G12A4S1G2S0G0G1S0S6S7S86S2cA4GeA4S1G2S0G0G1S0S6S7S8fS10A4G13A4S1G2S0G0G1S0S6S7S93S10A4S0S8S9Z32SbA4M15A4S1G2S0G0G1S0S6S7S92S10A4G15A4S1G2S0G0G1S0S6S7S94S10A4S0S8S9Z30SbA4A4S1G2S0G0G1S0S6S7S91S19A4S0S8S9Z2eSbA4A4S1G2S0G0G1S0S6S7S99SeA4S0S8S9Z28M16ScG7A1A4A4S1G2S0G0G1S0S6S7S9aSeA4S0S8S9G16ScG8A1A4A4S1G2S0G0G1S0S6S7S9bSeA4S0S8S9G16ScG9A1A4A4S1G2S0G0G1S0S6S7Sa0SeA4S0S8S9G16ScGaA1A4M17A4S1G2S0G0G1S0S6S7Sa6S12A4S0S8S9G16ScGbA1A4A4S1G2S0G0G1S0S6S7Sa4S22A4GeA4S1G2S0G0G1S0S6S7Sa7S12A4S0S8S9G16ScZfA1A4A4S1G2S0G0G1S0S6S7Sa5S16A4S0S8S9G16ScZdA1A4A4S1G2S0G0G1S0S6S7Sa3S23A4GeA4S1G2S0G0G1S0S6S7Sa8S16A4S0S8S9G16ScZbA1A4A4S1G2S0G0G1S0S6S7SadS1aA4S0S8S9G16ScZ9A1A4A4S1G2S0G0G1S0S6S7SabS24A4GeA4S1G2S0G0G1S0S6S7SaeS25A4S0S8S9G16ScZ7A1A4A4S1G2S0G0G1S0S6S7SacS26A4GeA4S1G2S0G0G1S0S6S7S57S30A4S0S8S9ZeSbA4M18A4S1G2S0G0G1S0S6S7S58S31A4G18A4S1G2S0G0G1S0S6S7S5fS30A4S0S8S9ZcSbA4M19A4S1G2S0G0G1S0S6S7S60S31A4G19A4S1G2S0G0G1S0S6S7S59S1eA4S0S8S9ZaSbA4M1aA4S1G2S0G0G1S0S6S7S5aS1fA4G1aA4S1G2S0G0G1S0S6S7S9fSeA4G17A4S1G2S0G0G1S0S6S7Sa1S12A4S0S8S9G16S2eA4A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition exitsF2 : list edescA := ltac2:(tb__ "0|12|
S1S2S2S6S7A2M0S2S8S9A2M1A2M2S0G0G1S0S6S7S47S43A4S0S8S9Z62SbA4A4S1G2S0G0G1S0S6S7S4fS17A4S0S8S9Z5eSbA4A4S1G2S0G0G1S0S6S7S46S21A4S0S8S9Z50M3SdS41Z3bM4A2A4A4S1G2S0G0G1S0S6S7S69S42A4S0S8S9G3SdS41Z37M5A2A4A4S1G2S0G0G1S0S6S7S68S42A4S0S8S9G3SdS41Z35M6A2A4A4S1G2S0G0G1S0S6S7S33S2fA4S0S8S9Z45SbA4M7A4S1G2S0G0G1S0S6S7S35S2fA4S0S8S9Z41SbA4A4S1G2S0G0G1S0S6S7S34S13A4S0S8S9G4SbA4M8A4S1G2S0G0G1S0S6S7S36S15A4S0S8S9G5SbA4M9A4S1G2S0G0G1S0S6S7S70S1bA4S0S8S9G6SbA4A4S1G2S0G0G1S0S6S7S61S30A4S0S8S9Z10SbA4MaA4S1G2S0G0G1S0S6S7S62S31A4GaA4S1G2S0G0G1S0S6S7S77S2fA4S0S8S9Z3fSbA4MbA4S1G2S0G0G1S0S6S7S76S2fA4GbA4S1G2S0G0G1S0S6S7S75S11A4S0S8S9Z3dSbA4McA4S1G2S0G0G1S0S6S7S83S11A4GcA4S1G2S0G0G1S0S6S7S84SfA4G9A4S1G2S0G0G1S0S6S7S8eS10A4S0S8S9Z33SbA4A4S1G2S0G0G1S0S6S7S90S10A4S0S8S9Z31SbA4A4S1G2S0G0G1S0S6S7S95S19A4S0S8S9Z2fSbA4A4S1G2S0G0G1S0S6S7S9cSeA4S0S8S9Z2dSbA4A4S1G2S0G0G1S0S6S7S96SeA4S0S8S9Z28MdScG4A1A4A4S1G2S0G0G1S0S6S7S97SeA4S0S8S9GdScZ39A1A4A4S1G2S0G0G1S0S6S7S98SeA4S0S8S9GdScG5A1A4A4S1G2S0G0G1S0S6S7S9eSeA4S0S8S9GdScG6A1A4MeA4S1G2S0G0G1S0S6S7Sa2S12A4S0S8S9GdScZeA1A4A4S1G2S0G0G1S0S6S7Sa9S16A4S0S8S9GdScZaA1A4A4S1G2S0G0G1S0S6S7SaaS1aA4S0S8S9GdScZ8A1A4A4S1G2S0G0G1S0S6S7S6dS30A4GaA4S1G2S0G0G1S0S6S7S6eS30A4GaA4S1G2S0G0G1S0S6S7S6fS31A4GaA4S1G2S0G0G1S0S6S7S5bS30A4S0S8S9ZdSbA4MfA4S1G2S0G0G1S0S6S7S5cS31A4GfA4S1G2S0G0G1S0S6S7S63S30A4S0S8S9ZbSbA4M10A4S1G2S0G0G1S0S6S7S64S31A4G10A4S1G2S0G0G1S0S6S7S5dS65A4S0S8S9Z0SbA4M11A4S1G2S0G0G1S0S6S7S5eS66A4G11A4S1G2S0G0G1S0S6S7S9dSeA4GeA4S1G2S0G0G1S0S6S7S40S2fA4G7A4S1G2S0G0G1S0S6S7S8dSfA4G8A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Goal (length cutsF2 = 70%nat) /\ (length exitsF2 = 40%nat). Proof. split; reflexivity. Qed.
Lemma hdr_ok2 : ltac2:(tb__ "0|0|
S55S4SafS56S67A2S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_handle_f_nodes2.

