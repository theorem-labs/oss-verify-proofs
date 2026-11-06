(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_036.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes f9 fa.

(* [comment removed for export] *)
Module Lib_handle_f_gdefs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "andb"; "app"; "nat"; "prod"; "None"; "cons"; "S"; "nil"; "orb"; "fst"; "list"; "pair"; "Some"; "bool"; "false"; "snd"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "SPUle"; "SLit"; "sv"; "SPBranch"; "sv_eqb"; "SAlu"; "ss_facts"; "ss_next"; "SPUlt"; "ss_objs"; "sobj"; "sprop_below"; "SPEq"; "SPNot"; "SVar"; "dflt_writable"; "swf"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pA"; "fr_hf"; "am2"; "pQ"; "pT0"; "PD_vn"; "co_n"; "pKco"; "room_r"; "pDco"; "xbo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "B32"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_base"; "ax_X"; "entailsA"; "g8"; "has_facts"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "pow"; "ltb"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "tE"; "tL"; "kb"; "tI"; "hG"; "hF"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "ALU_ADD"; "BC_EQ"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "ANone"; "NDA"; "ndesc"; "fr_sub_eqb"; "nd_bd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "extraOH"; "extraXH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "bF"; "feF"; "roomF"; "triAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7"; "pNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "sv_subst"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_wpos"; "bd_below"; "bd_subst"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xrs_checkL"; "robjs_checkF"; "local_ok"; "shadow_reopen_stateA"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "skipn"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "Pre_vr"; "nd0"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8"; "pL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "call_checkA"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "pd_okA"; "pdescA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vAL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "arity_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "needA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "wsub_dom_below"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.

Definition bF (F : list sprop) : bool := baseF DW F.
Definition fF (F : list sprop) : bool := frameF hG 160 512 F.
Definition feF (F : list sprop) : bool := ltac2:(tb__ "0|0|
S39S5S11S1fS38S43A1S44A2S5S11S13S21S43A1S14S3dS3bZ2Z3dA2Z1A2A1A2S7S11A1A3A3VF;A2").

Definition vr_chk (XGL : list (Z * Z)) (E : axst) (kept : list (sv * sv)) (d k : sv) (e off : Z) (bd brest : list bitem) (s : wsub) (R : list sobj) (Xk : list (sv * sv)) : bool := ltac2:(tb__ "0|8|
S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S70VXk;S36VE;A1A2S6bVE;S67Vs;VR;S64S3S34S4cA2S34S9S34S4cA2S2bA4A5A2S75S3eVs;A2A2S7dVs;S6eA2A2S5dS3eS1aS33VE;A1M0A1M1A2A2S49G1S4bS1S3S15S15A2M2Vkept;S5G2SbS15S15Vd;S41Ve;Vk;A2A4S7G2A1A3M3A3S27S1S59S5cVs;S4eS68A1A2Vbrest;A3M4S4aA4A2A2S5bG1Vbrest;A2A2S6fVs;G3S69A3A2S73Vbd;G4A2A2S5aG4A1A2S25S72S71S67S6eVs;G1A4S2bA3A2S51S19G0A1M5A1A2S76G5Vkept;S27S4S2A1M6S4fVR;A6A2S5fVXGL;G5Vkept;S27G6S1cG0A1S50VXk;A8A2S3cZ0M7Ve;A2A2S3aVe;ZcA2A2S24S11S12S13Vk;S14S31A1A2A1G5A3A2S17S56Vs;P11A2Vk;A2A2S17S56Vs;PfA2Vd;A2A2S17S56Vs;PeA2S78A2A2S17S56Vs;PcA2S30Voff;A1A2A2S3aG7Voff;A2A2S3aVoff;Z4f8A2A2").

Definition land_chk (L C : axst) (s : wsub) (tv1 tv2 : list (sv * sv)) (bd1 bd2 : list bitem) (tvC : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S0S0S0S0S0S0S0S74Vtv1;Vtv2;A2S73Vbd1;Vbd2;A2A2S37VL;VC;Vs;A3A2S58Vs;S3eA2A2S5dS3eS1aS33VL;A1A1M0A2A2S49G0S4bVtv2;S27Vbd2;S4aA4A2A2S6fVs;Vtv2;VtvC;A3A2S4dVs;S27S27A3A2").

Definition reopen_chk (XGL : list (Z * Z)) (A : axst) (X' : list (sv * sv)) (tv : list (sv * sv)) (k1 k2 : Z) : bool := ltac2:(tb__ "0|3|
S0S0S0S0S0S0S0S0S0S17S35VA;A1S14S77A1A2S3aZ0Vk1;A2A2S3aVk1;Vk2;A2A2S3aVk2;Z40A2A2S52S19S33VA;A1M0A1M1A1A2S70VX';S36VA;A1A2A2S23S33S62VA;VX';S43Vk1;Vk2;A5A1A1A2S51G1A1A2S60G1Vtv;S27S4S2A1S4fS1cG0A1M2A6A2S5fVXGL;G1Vtv;S27ScS2U0A2G2S50VX';A8A2").

Definition release_chk (A : axst) (objs : list sobj) (k1 k2 : Z) (cells : list cell) (d : odefault) (L : list (Z * Z)) (tv : list (sv * sv)) (bd : list bitem) : bool := ltac2:(tb__ "0|2|
S0S0S0S0S0S0S0S0S0S17S35VA;A1S14S77A1A2S3aZ0Vk1;A2A2S3aVk1;Vk2;A2A2S3aVk2;Z40A2A2S22Vd;A1A2S52S19S33VA;A1M0A1M1A1A2S25S3S66S66A2S61Vcells;Vd;Vk1;Vk2;A4VL;A3A2S49S1aG0A1S4bVtv;S27Vbd;S4aA4A2A2S51G1A1A2S60G1Vtv;S27S4S2A1S4fVobjs;A6A2").

Definition xff_chk (T1 : axst) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S25S11S1eS1aS33VT1;A1M0A1A1S1S11VF;S19G0A1A3A3").

Definition purec_chk (XGL : list (Z * Z)) (Pre : axst) (Ls : list axst) (E : axst) (tv : list (sv * sv)) (bd : list bitem) (s : wsub) (R : list sobj) : bool := ltac2:(tb__ "0|5|
S0S0S0S0S0S0S0S0S6bVE;VPre;Vs;VR;VLs;A5S75S3eVs;A2A2S5dS3eS1aS33VE;A1M0A1M1A2A2S49G1S4bVtv;S27Vbd;S4aA4A2A2S5aVbd;A1A2S25S34S34S0S0SaS1dA1M2SdLx;S7cS33VPre;A1S33R1A1A2S10S1dG2SeLl;Ls0;Xax2S6dVPre;R1A2A2S17S35R1A1S35VPre;A1A2A2LL;VLs;A3A2S51S19G0A1M3A1A2S76G3Vtv;S27S4S2A1M4S4fVR;A6A2S5fVXGL;G3Vtv;S27G4S1cG0A1S50S36VE;A1A8A2").

Definition pure_chk (Pre P E : axst) (nd : ndesc) (s : wsub) (R : list sobj) : bool := ltac2:(tb__ "0|2|
S0S0S0S6cVE;VPre;Vs;VR;S5S34VP;S7S34A1A3A5S5dS3eS1aS33VE;A1M0A1M1A2A2S49G1Vnd;A2A2S25S11S1eG1A1S19G0A1A3A2").

Definition coF (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S0S0S0S0S24S11S12S2eZcM0Z1G0S2cS42A5A1VF;A3S24S11S12S13S2cS14S31A1A2A1VF;A3A2S24S11S12S13S42S2aA2A1VF;A3A2S8S24S11S12S13S2aS29A2A1VF;A3S24S11S12S1bS2aS29A2A1VF;A3A2A2S24S11S12S13S29S3fA2A1VF;A3A2S24S11S12S13S3fS40A2A1VF;A3A2S24S11S12S13S40S14S5eA1A2A1VF;A3A2").

Definition vrF (q : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S0S0S8S24S11S12S13Vq;S3fA2A1VF;A3S24S11S12S1bVq;S3fA2A1VF;A3A2S24S11S12S13S3fS40A2A1VF;A3A2S24S11S12S13S40S14S5eA1A2A1VF;A3A2").
Definition vlF (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S0S24S11S12S1bS6aS55A2A1VF;A3S24S11S12S13S55S28A2A1VF;A3A2S24S11S12S16S45S14Z2M0A1S26A3A1VF;A3A2S24S11S12S13S26S14S3bG0Z14A2A1A2A1VF;A3A2").

Definition slotF (c k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S24S11S12S13S18S46S41ZcM0Vc;A2S14G0A1A3S41G0Vk;A2A2A1VF;A3S24S11S12S13Vc;Vk;A2A1VF;A3A2S24S11S12S13Vk;S14S31A1A2A1VF;A3A2").

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
S0S0S0S0S53Ve;Vr;Vsl;Vc;Vn;VF;A6S24S11S12S1bS6aS55A2A1VF;A3A2S24S11S12S13S55S28A2A1VF;A3A2S24S11S12S16S45S14Z2M0A1S26A3A1VF;A3A2S24S11S12S13S26S14S3bG0Z14A2A1A2A1VF;A3A2").

Definition triAF (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S24S11S12S20S16S47S26S14Z3A1A3A1A1VF;A3S24S11S12S16S45S14Z2M0A1S26A3A1VF;A3A2S24S11S12S13S26S14S3bG0Z14A2A1A2A1VF;A3A2").

Definition live3F (a k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S0S0S24S11S12S16S47Va;S14Z3A1A3A1VF;A3S24S11S12S13Va;Vk;A2A1VF;A3A2S24S11S12S13Vk;S14S31A1A2A1VF;A3A2").
Definition liveTri (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S0S24S11S12S13S18S46S18S48S28S14Z1A1A3S28A3Vk;A2A1VF;A3S24S11S12S16S45S14Z2M0A1S26A3A1VF;A3A2S24S11S12S13S26S14S3bG0Z14A2A1A2A1VF;A3A2S24S11S12S13Vk;S14S31A1A2A1VF;A3A2").
Definition liveRp (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S0S24S11S12S13S18S46S18S48S26S14Z1A1A3S26A3Vk;A2A1VF;A3S24S11S12S16S45S14Z2M0A1S26A3A1VF;A3A2S24S11S12S13S26S14S3bG0Z14A2A1A2A1VF;A3A2S24S11S12S13Vk;S14S31A1A2A1VF;A3A2").
Definition liveTs (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S0S0S24S11S12S13S7aVk;A2A1VF;A3S54VF;A1A2S24S11S12S13Vk;S14S31A1A2A1VF;A3A2").

Definition liveF (x : sv) (c : Z) (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S0S0S24S11S12S13S18S46Vx;S14Vc;A1A3Vk;A2A1VF;A3S24S11S12S13Vk;S14S31A1M0A2A1VF;A3A2S8S24S11S12S13Vx;G0A2A1VF;A3S24S11S12S13Vx;Vk;A2A1VF;A3A2A2").

Definition tv_rm (i : nat) (tv : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|1|
S1S3S15S15A2M0S63G0Vi;Vtv;A3S65G0S6Vi;A1Vtv;A3A3").
Definition bd_rm2 (j : nat) (bd : list bitem) : list bitem := ltac2:(tb__ "0|0|
S1S59S63S59Vj;Vbd;A3S65S59S6S6Vj;A1A1Vbd;A3A3").
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
Definition s_tsk : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA T_tsk (ax_X T_tsk) hG 6 15) JR_ts.
Definition tv2_tsk : list (sv * sv) := Eval vm_compute in tv_sb s_tsk (nd_tv ndTS).
Definition bd2_tsk : list bitem := Eval vm_compute in bd_subst s_tsk (nd_bd ndTS).
Definition s_tsf : wsub := Eval vm_compute in land_sub T_tsf JF_ts.
Definition tv2_tsf : list (sv * sv) := Eval vm_compute in tv_sb s_tsf (nd_tv ndTSf).
Definition s_tsg : wsub := Eval vm_compute in land_sub (shadow_reopen_stateA T_tsg (ax_X T_tsg) hG 6 15) JR_ts.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SAlu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "z0"; "VL"; "VR"; "ndLL"; "ndTS"; "ndRP"; "ndTR"; "ndFV"; "ndL4a"; "ndL4b"; "ndMI"; "VK3"; "ndP"; "ndH"; "ndJN"; "ndL4c"; "ndMM"; "ndT"; "ndTRf"; "ndEf'"; "ndEo'"; "ndFVf"; "ndJ"; "ndL4af"; "ndL4bf"; "ndL4cf"; "ndL4d"; "ndL4df"; "ndMIf"; "ndMMf"; "ndRPf"; "ndSG"; "ndSGf"; "ndTSf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pQ"; "ndR"; "nd0"; "C_pre"; "C_pro"; "E_co0"; "E_ms0"; "E_sm0"; "H"; "JF_co"; "JR_co"; "K"; "L1"; "L2"; "Pre_hf"; "X_pro"; "am1"; "am2"; "ndFc"; "pP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "ndXA"; "ndEf"; "ndEo"; "C36"; "E_dg0"; "E_fv0"; "E_mc0"; "E_mi0"; "E_mm0"; "JF_fv"; "JF_mi"; "JR_fv"; "JR_mi"; "RJ"; "RW"; "T_dg"; "T_mcq"; "XA"; "pR"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi"; "C_Ef2"; "C_Eo2"; "C_rlf"; "C_rlo"; "E_f5f0"; "E_f5o0"; "P_fail"; "P_ok"; "T_f5f"; "T_f5o"; "XEf42"; "XEo42"; "X_rlf"; "X_rlo"; "nd_fail"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_nodes2"; "cutsF2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1"; "E_da0"; "E_pc0"; "T_da"; "T_ms"; "T_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10"; "XEf6a"; "XEf6b"; "XEo6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3"; "E_sg0"; "JF_mm"; "JF_sg"; "JR_mm"; "JR_sg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "E_tdg0"; "E_trb0"; "E_trg0"; "JF_trb"; "JF_trg"; "JR_trb"; "JR_trg"; "K1"; "K1Xb"; "K1Xg"; "K2"; "T_tdg"; "pI"; "pT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "E_rp0"; "E_ts0"; "JF_rp"; "JF_ts"; "JR_rp"; "JR_ts"; "K3"; "K3m"; "K3x"; "TS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6"; "E_md0"; "E_pg0"; "T_md"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7"; "E_wdg0"; "J"; "T_pgiR"; "T_pgoR"; "T_wdg"; "XJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8"; "E_g1_0"; "E_g2_0"; "E_g3_0"; "L14"; "T_g1"; "T_g2"; "XLJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w"; "E_mi4_0_0"; "E_mi4_0_4"; "T_g3_0"; "T_g3_4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9"; "E_c4_0"; "E_fv4_0"; "E_m4_0"; "JF_fv4"; "JF_mi4"; "JR_fv4"; "JR_mi4"; "T_c4"; "T_m4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b"; "E_mm4_0"; "E_sg4_0"; "JF_mm4"; "JF_sg4"; "JR_mm4"; "JR_sg4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA"; "ejcert_hdr"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition cutsF2 : list edescA := ltac2:(tb__ "0|1e|
S1S2S2S6S7A2M0S2S8S9A2M1A2M2S0G0G1S0S6S7S3bS2fA4S0S8S9Z64SbA4A4S1G2S0G0G1S0S6S7S31S17A4S0S8S9Z60SbA4A4S1G2S0G0G1S0S6S7S30S17A4S0S8S9Z5cSbA4A4S1G2S0G0G1S0S6S7S35S18A4S0S8S9Z50M3SdS40Z2M4A2A4A4S1G2S0G0G1S0S6S7S39S18A4S0S8S9G3SdS2dZ1M5A2A4A4S1G2S0G0G1S0S6S7S3aS1cA4S0S8S9G3SdS2dZ0M6A2A4A4S1G2S0G0G1S0S6S7S38S1cA4S0S8S9G3SdS2dZ3cM7A2A4A4S1G2S0G0G1S0S6S7S37S2eA4S0S8S9G3SdS2dZ3aM8A2A4A4S1G2S0G0G1S0S6S7S36S3fA4S0S8S9Z1eSbA4A4S1G2S0G0G1S0S6S7S6bS2eA4S0S8S9G3SdS2dZ38M9A2A4A4S1G2S0G0G1S0S6S7S6cS2eA4S0S8S9G3SdS2dZ36MaA2A4A4S1G2S0G0G1S0S6S7S6aS2eA4S0S8S9G3SdS2dZ34MbA2A4A4S1G2S0G0G1S0S6S7S52S41A4S0S8S9Z46SbA4A4S1G2S0G0G1S0S6S7S50S41A4S0S8S9Z44SbA4A4S1G2S0G0G1S0S6S7S4fS41A4S0S8S9Z42McSbA4A4S1G2S0G0G1S0S6S7S4dS15A4S0S8S9Z40SbA4MdA4S1G2S0G0G1S0S6S7S4bS27A4S0S8S9Z14SbA4MeA4S1G2S0G0G1S0S6S7S44S15A4S0S8S9Z3eMfS53A4A4S1G2S0G0G1S0S6S7S4eS15A4S0S8S9G7SbA4M10A4S1G2S0G0G1S0S6S7S4cS12A4S0S8S9G8SbA4A4S1G2S0G0G1S0S6S7S4aS20A4GeA4S1G2S0G0G1S0S6S7S51S12A4S0S8S9G9SbA4M11A4S1G2S0G0G1S0S6S7S73S1bA4S0S8S9GaSbA4M12A4S1G2S0G0G1S0S6S7S71S28A4GeA4S1G2S0G0G1S0S6S7S74S2aA4S0S8S9GbSbA4M13A4S1G2S0G0G1S0S6S7S72S2bA4GeA4S1G2S0G0G1S0S6S7S7cS41A4S0S8S9GcSaS54S3dS81A3A4A4S1G2S0G0G1S0S6S7S7eS41A4GdA4S1G2S0G0G1S0S6S7S7dS41A4GdA4S1G2S0G0G1S0S6S7S7bS11A4S0S8S9GfSbA4M14A4S1G2S0G0G1S0S6S7S79S1dA4GeA4S1G2S0G0G1S0S6S7S7aS11A4G14A4S1G2S0G0G1S0S6S7S78S1dA4GeA4S1G2S0G0G1S0S6S7S80S11A4G10A4S1G2S0G0G1S0S6S7S7fS11A4S0S8S9G8SaS54S3eS82A3A4A4S1G2S0G0G1S0S6S7S87S10A4G10A4S1G2S0G0G1S0S6S7S85S29A4GeA4S1G2S0G0G1S0S6S7S89S10A4S0S8S9G8S16G4A1A4A4S1G2S0G0G1S0S6S7S8aS10A4S0S8S9G8S16G5A1A4A4S1G2S0G0G1S0S6S7S8bS10A4S0S8S9G8S16G6A1A4A4S1G2S0G0G1S0S6S7S8cS10A4G11A4S1G2S0G0G1S0S6S7S88SfA4G12A4S1G2S0G0G1S0S6S7S86S2cA4GeA4S1G2S0G0G1S0S6S7S8fSfA4G13A4S1G2S0G0G1S0S6S7S93SfA4S0S8S9Z32M15SbA4M16A4S1G2S0G0G1S0S6S7S92SfA4G16A4S1G2S0G0G1S0S6S7S94SfA4S0S8S9Z30M17SbA4A4S1G2S0G0G1S0S6S7S91S19A4S0S8S9Z2eM18SbA4A4S1G2S0G0G1S0S6S7S99SeA4S0S8S9Z28M19ScG7A1A4A4S1G2S0G0G1S0S6S7S9aSeA4S0S8S9G19ScG8A1A4A4S1G2S0G0G1S0S6S7S9bSeA4S0S8S9G19ScG9A1A4A4S1G2S0G0G1S0S6S7Sa0SeA4S0S8S9G19ScGaA1A4M1aA4S1G2S0G0G1S0S6S7Sa7S13A4S0S8S9G19ScGbA1A4A4S1G2S0G0G1S0S6S7Sa5S22A4GeA4S1G2S0G0G1S0S6S7Sa8S13A4S0S8S9G19ScG15A1A4A4S1G2S0G0G1S0S6S7Sa6S14A4S0S8S9G19ScG17A1A4A4S1G2S0G0G1S0S6S7Sa4S23A4GeA4S1G2S0G0G1S0S6S7Sa9S14A4S0S8S9G19ScG18A1A4A4S1G2S0G0G1S0S6S7SaeS1aA4S0S8S9G19ScZ2cA1A4A4S1G2S0G0G1S0S6S7SacS24A4GeA4S1G2S0G0G1S0S6S7SafS25A4S0S8S9G19ScZ2aA1A4A4S1G2S0G0G1S0S6S7SadS26A4GeA4S1G2S0G0G1S0S6S7S57S42A4S0S8S9ZeSbA4M1bA4S1G2S0G0G1S0S6S7S58S43A4G1bA4S1G2S0G0G1S0S6S7S5fS42A4S0S8S9ZcSbA4M1cA4S1G2S0G0G1S0S6S7S60S43A4G1cA4S1G2S0G0G1S0S6S7S59S1eA4S0S8S9ZaSbA4M1dA4S1G2S0G0G1S0S6S7S5aS1fA4G1dA4S1G2S0G0G1S0S6S7S9fSeA4G1aA4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition exitsF2 : list edescA := ltac2:(tb__ "0|16|
S1S2S2S6S7A2M0S2S8S9A2M1A2M2S0G0G1S0S6S7S34S2fA4S0S8S9Z62SbA4A4S1G2S0G0G1S0S6S7S3cS17A4S0S8S9Z5eSbA4A4S1G2S0G0G1S0S6S7S32S21A4S0S8S9Z50M3SdS2dZ3bM4A2A4A4S1G2S0G0G1S0S6S7S33S2eA4S0S8S9G3SdS2dZ39M5A2A4A4S1G2S0G0G1S0S6S7S69S2eA4S0S8S9G3SdS2dZ37M6A2A4A4S1G2S0G0G1S0S6S7S68S2eA4S0S8S9G3SdS2dZ35M7A2A4A4S1G2S0G0G1S0S6S7S45S41A4S0S8S9Z45SbA4A4S1G2S0G0G1S0S6S7S48S41A4S0S8S9Z41SbA4A4S1G2S0G0G1S0S6S7S46S15A4S0S8S9G4SbA4A4S1G2S0G0G1S0S6S7S47S12A4S0S8S9G5SbA4A4S1G2S0G0G1S0S6S7S49S12A4S0S8S9G6SbA4M8A4S1G2S0G0G1S0S6S7S70S1bA4S0S8S9G7SbA4M9A4S1G2S0G0G1S0S6S7S61S42A4S0S8S9Z10SbA4MaA4S1G2S0G0G1S0S6S7S62S43A4GaA4S1G2S0G0G1S0S6S7S77S41A4S0S8S9Z3fSbA4MbA4S1G2S0G0G1S0S6S7S76S41A4GbA4S1G2S0G0G1S0S6S7S75S11A4S0S8S9Z3dSbA4McA4S1G2S0G0G1S0S6S7S83S11A4GcA4S1G2S0G0G1S0S6S7S84S10A4G8A4S1G2S0G0G1S0S6S7S8dSfA4G9A4S1G2S0G0G1S0S6S7S8eSfA4S0S8S9Z33MdSbA4A4S1G2S0G0G1S0S6S7S90SfA4S0S8S9Z31MeSbA4A4S1G2S0G0G1S0S6S7S95S19A4S0S8S9Z2fMfSbA4A4S1G2S0G0G1S0S6S7S9cSeA4S0S8S9Z2dM10SbA4A4S1G2S0G0G1S0S6S7S96SeA4S0S8S9Z28M11ScG4A1A4A4S1G2S0G0G1S0S6S7S97SeA4S0S8S9G11ScG5A1A4A4S1G2S0G0G1S0S6S7S98SeA4S0S8S9G11ScG6A1A4A4S1G2S0G0G1S0S6S7S9eSeA4S0S8S9G11ScG7A1A4M12A4S1G2S0G0G1S0S6S7Sa1S13A4S0S8S9G11ScGdA1A4A4S1G2S0G0G1S0S6S7Sa2S13A4S0S8S9G11ScGeA1A4A4S1G2S0G0G1S0S6S7Sa3S14A4S0S8S9G11ScGfA1A4A4S1G2S0G0G1S0S6S7SaaS14A4S0S8S9G11ScG10A1A4A4S1G2S0G0G1S0S6S7SabS1aA4S0S8S9G11ScZ2bA1A4A4S1G2S0G0G1S0S6S7S6dS42A4GaA4S1G2S0G0G1S0S6S7S6eS42A4GaA4S1G2S0G0G1S0S6S7S6fS43A4GaA4S1G2S0G0G1S0S6S7S5bS42A4S0S8S9ZdSbA4M13A4S1G2S0G0G1S0S6S7S5cS43A4G13A4S1G2S0G0G1S0S6S7S63S42A4S0S8S9ZbSbA4M14A4S1G2S0G0G1S0S6S7S64S43A4G14A4S1G2S0G0G1S0S6S7S5dS65A4S0S8S9Z0SbA4M15A4S1G2S0G0G1S0S6S7S5eS66A4G15A4S1G2S0G0G1S0S6S7S9dSeA4G12A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Goal (length cutsF2 = 69%nat) /\ (length exitsF2 = 43%nat). Proof. split; reflexivity. Qed.
Lemma hdr_ok2 : ltac2:(tb__ "0|0|
S55S4Sb0S56S67A2S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_handle_f_nodes2.

(* [comment removed for export] *)
Module Lib_load_obj_epiS5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "swf"; "ss_objs"; "ss_pc"; "ob_base"; "ob_lo"; "ss_next"; "DUnknown"; "cell"; "ss_facts"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "false"; "true"; "nat"; "Some"; "nil"; "pair"; "option"; "list"; "prod"; "app"; "negb"; "orb"; "None"; "length"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "axwf"; "la_reason"; "la_state"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXMerge"; "AXRebase"; "AXSelect"; "AXSplit"; "AXUnbase"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vOUT"; "idxB"; "Pre_f8"; "L_f8"; "g5"; "objs_butlast"; "vDp"; "xf_shback"; "xf_shcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiS5"; "s_pok"; "Es_mc"; "Es_s8"; "nd_okL"; "Es_s8a"; "Es_sf"; "P_errM"; "P_okF"; "Ts_s81"; "s_mcS"; "Es_mc1"; "Es_mc2"; "Es_sfB"; "Es_sfC"; "P_errR"; "P_okR"; "Rs_mc"; "Rs_s8"; "Ts_mc"; "Ts_mc0"; "Ts_s8"; "Ts_s80"; "Ts_s82"; "Ts_s8r"; "Bs_mc"; "Es_sf0"; "P_okL"; "P_okM"; "Rs_sf"; "Ts_sf"; "s_perr"; "xf_mergeR"; "xf_rebaseR"; "Es_s80"; "Es_sfA"; "Es_sfD"; "fr_offR"; "frame_idxR"; "needs_rebaseR"; "xfb_mcS"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "repeat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2"; "nobj"; "cps_ad"; "L_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiS5.IF"; "nd_lo_ok"; "P_err"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "Pre_mc48"; "L_mc48"; "ax_tidy"; "vARn"; "vALo"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@Stdlib.Lists.List"; "filter"; "existsb"; "fold_right"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3"; "P_errL"; "Pre_sf"; "dflt_obj"; "L_sf"; "insert_by"; "s_s8"; "s_sf"; "sx_T82"; "sx_T8r"; "sx_s8a"; "xf_merge"; "xf_rebase"; "xf_sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "BIc"; "KU"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "AHead"; "NDA"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "nd_below"; "tv_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs.LOAddr"; "lo_ret"; "sf5_pc"; "ssf8_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_iface.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3.
Module IF. Include Lib_load_obj_iface. End IF.

Definition Es_mc1 : axst := Eval vm_compute in optL (apply_axforms L_ok [AXSplit (idxB L_ok vOUT 0) (SLit 144)]).
Definition Es_mc2 : axst := Eval vm_compute in optL (apply_axforms Es_mc1 [AXSplit (idxB Es_mc1 vOUT 144) (SLit 192)]).
Definition Es_mc : axst := Eval vm_compute in optL (apply_axforms Es_mc2 [AXUnbase (idxB Es_mc2 vOUT 144) 144]).
Definition s_mcS : wsub := ltac2:(tb__ "0|1|
S12S1bS0S5A2M0S18S0S5P35S35A4S12G0S18S0S5P36S7Zd0A1A4S12G0S18S0S5P37S74A4S12G0S18S0S5P38S7Z30A1A4S12G0S18S0S5Sa6S3bA4S77PaS23S3fA1S23S70A1A3A3A3A3A3A3").
Definition Rs_mc : list sobj := Eval vm_compute in optR (entails_frA Es_mc Pre_mc48 s_mcS).
Definition Ts_mc0 : axst := Eval vm_compute in T_afterA Pre_mc48 Es_mc s_mcS Rs_mc L_mc48.

Definition xfb_mcS (T : axst) : list axform := ltac2:(tb__ "0|3|
S36VT;S35Z0A3S15S36VT;S35Zc0A3S15S12S2aS2cU1M0A1S12S2aS2dS12S15R2S12S15G0S12S15R1S7aS15S15S1dS1eS1eS75R1R3A2S75R1G0A2A2S75R1R2A2A2A1Li;S67U0M1S6aVT;A1A2A3A3A3A3A1S12S2aS2bG1A1M2S12S2aG2S17S2aA1A3A3A3A3TiB;TiA;").
Definition Bs_mc : axst := Eval vm_compute in optL (apply_axforms Ts_mc0 (xfb_mcS Ts_mc0)).
Definition Ts_mc : axst := Eval vm_compute in ax_tidy Bs_mc.

Definition Es_s80 : axst := Eval vm_compute in leafL (runL 300 cps_ad Ts_mc) ssf8_pc 0.
Definition Es_s8a : axst := Eval vm_compute in sx_s8a Es_s80.
Definition Es_s8 : axst := Eval vm_compute in sx_s8 Es_s80.
Definition Rs_s8 : list sobj := Eval vm_compute in optR (entails_frA Es_s8 Pre_f8 (s_s8 Es_s8)).
Definition Ts_s80 : axst := Eval vm_compute in sx_T80 Es_s8.
Definition Ts_s81 : axst := Eval vm_compute in sx_T81 Ts_s80.
Definition Ts_s82 : axst := Eval vm_compute in sx_T82 Ts_s81.
Definition Ts_s8r : axst := Eval vm_compute in sx_T8r Ts_s82.
Definition Ts_s8 : axst := Eval vm_compute in ax_tidy Ts_s8r.
Definition Es_sf0 : axst := Eval vm_compute in leafL (runL 300 cps_ad Ts_s8) sf5_pc 0.
Definition Es_sfA : axst := Eval vm_compute in sx_sfA Es_sf0.
Definition Es_sfB : axst := Eval vm_compute in sx_sfB Es_sfA.
Definition Es_sfC : axst := Eval vm_compute in sx_sfC Es_sfB.
Definition Es_sfD : axst := Eval vm_compute in sx_sfD Es_sfC.
Definition Es_sf : axst := Eval vm_compute in sx_sf Es_sfD.
Definition Rs_sf : list sobj := Eval vm_compute in optR (entails_frA Es_sf Pre_sf (s_sf Es_sf)).
Definition Ts_sf : axst := Eval vm_compute in sx_Tsf Es_sf.
Definition P_okL : axst := Eval vm_compute in leafL (runL 300 cps_ad Ts_sf) lo_ret 0.

Definition fr_offR (o : sobj) : option Z := ltac2:(tb__ "0|19|
S5S19S1A1M0Lx;M1SbVo;A1S1S1fS1A1M2Lz;M3S0S0G0Li;M4R1S0G2Lp;M5S0S0G0Lp;M6R1S0S0G0Lp0;M7R1S0G2Lp1;M8S0S0G0Lp1;M9R1S0G2Lp2;MaGaG1ScVo;A1MbS1S16S1R1A2Llo;S0G2Li0;McS30S5S5G2Lb;La;MdLop;MeGeS31GdLop;MfGfS11S2S5G2La;Lw;Lsgn;M10S0S5S1G2Lk;M11Li0;Ll;M12X5x8X0x3Lp1;G2X0x3Lp0;S0G2Lp0;M13G2X0x3Lp;G2X0x3Li;S30S5S5S30G0Lop;R3S5G0La;R2G3S0G4R1G5S0G6R1S0G7R1G8S0G9R1GaGaS5G0Lb;R5S1G1GbS1S16S1Sa7R2R1A2A2Llo;GcS30S5S5G2Lb0;La0;M14Lop0;M15G15S31G14Lop0;M16G16S11S2S5G2La0;Lw;Lsgn;M17G12X5x8Lc;GcG15G15G16G16G17G12X5x8X0x3Lp1;G2X0x3Lp0;G13G2X0x3Lp;G2X0x3Li;G15G15G16G16G17S0S5G11Li;Ll;M18X5x8G2G2G2G2G2G2G2G2G2X30xaLb;La;Lop;GeGfGfG10G18X5x8").

Definition needs_rebaseR (o : sobj) : bool := ltac2:(tb__ "0|d|
S5S11Lx;M0SbVo;A1S1S13Lz;M1S0S13Li;S30S5S5S30S11Lop;R3S5S11La;R2G1S0S0S11Li;R1S0S13Lp;S0S0S11Lp;R1S0S0S11Lp0;R1S0S13Lp1;S0S0S11Lp1;R1S0S13Lp2;M2G2S5S11Lb;R5S1G0ScVo;A1S1S14Lz0;S0S13Li0;M3S30S5S5S13Lb0;La0;M4Lop0;M5G5S31G4Lop0;M6G6S11S2S5S13La0;Lw;Lsgn;M7S0S5S1S13Lk;M8Li0;Ll;M9X5x8Lz;G3G5G5G6G6G7G9X5x8X0x3Lp1;S13X0x3Lp0;S0S13Lp0;S13X0x3Lp;S13X0x3Li;G5G5G6G6G7S0S5G8Li;Ll;MaX5x8S13S13S13S13S13S13S13S13S13X30xaLb;La;Lop;S30S5S5S13Lb;La;MbLop;S31GbLop;McGcS11S2S5S13La;Lw;Lsgn;GaX5x8").
Definition xf_rebaseR (A : axst) : list axform := ltac2:(tb__ "0|0|
S66S15S2aS15S2cR1A1Li;S7aS15S15S64S68S6R1S9S23VA;A1A1S7fA4A1Li;S67U0S6aVA;A1A2A3A4").
Definition frame_idxR (A : axst) : list nat := ltac2:(tb__ "0|2|
S66S1bS1S15A2M0S15S21S1S15A2S7cS1aG0A1M1S15S15G1S19S1A1G1Lx;S62S68S6R2S9S23VA;A1A1S7fA4A1S1S81R1R3R2A3Lk;R1X19x2Lacc;Li;S17G0A1S67U0S6aVA;A1A2A5A4").
Definition xf_mergeR (A : axst) : list axform := ltac2:(tb__ "0|1|
S63VA;A1S1aS15A1S12S2aS2dS1cS15R1S7aS15S15S1dS7bS15S75R1A1R2A3A1Li;S67U0M0S6aVA;A1A2A3A3A1S69S2aS2bG0A1S9dS20S15R1A2U1A2A3A3Tfi;").
Definition P_okR : axst := Eval vm_compute in optL (apply_axforms P_okL (xf_rebaseR P_okL)).
Definition P_okM : axst := Eval vm_compute in optL (apply_axforms P_okR (xf_mergeR P_okR)).
Definition P_okF : axst := Eval vm_compute in ax_add_facts (tv_factsA (vARn, SLit 64)) P_okM.
Definition s_pok : wsub := ltac2:(tb__ "0|0|
S77S34S23S45A1S23S6fA1A3").
Definition P_errR : axst := Eval vm_compute in optL (apply_axforms P_errL (xf_rebaseR P_errL)).
Definition P_errM : axst := Eval vm_compute in optL (apply_axforms P_errR (xf_mergeR P_errR)).
Definition s_perr : wsub := ltac2:(tb__ "0|0|
S77S34S23S44A1S23S6eA1A3").

Definition nd_okL : ndesc := ltac2:(tb__ "0|1|
S94S12S1bS5S5A2M0S18S5S5S73S7Z40A1A4S17G0A1A3S17S1bS1bS5S1A2S5A2A1S12S8bS8cZ0S8dZ1A3S17S8bA1A3S93Sa1S13A2A4").

Lemma epiS5_checks_mc : ltac2:(tb__ "0|5|
S4S3S19S22A1M0S29S6cS12S2aS2eS36S6cS35Z0A3S7Z90M1A1A2S17S2aA1M2A3A2S16S22S48A2A3S4S3G0S29S48S12S2aS2eS36S48S35G1A3S7Zc0A1A2G2A3A2S16S22S49A2A3S4S3G0S29S49S12S2aS2fS36S49S35G1A3G1A2G2A3A2S16S22S3fA2A3S4S3S19S1aS6A1M3A1S79S3fS70S47A3S16G3S4eA2A3S4S3S11S78S3fS70S47S4eS12S22S71S17S22A1A3A5S14A3S4S3S11S9bS34S47A2S14A3S4S3S22S9aS70S3fS47S4eS71A5S51A3S4S3G0S29S51S65S51A1A2S16S22S56A2A3S4S3S22S72S56A1S50A3S4S3S11S25S50A1S14A3S3S1aS1bS1S32A2M4A1S66S24G4S24S18S1S32SaS23S27R1A1A1A1S26R1A1A4LL;S76U12cS6bS50A3A4S12G4S18S1S32Sa0S33A4S17G4A1A3A3A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS5_checks_s8 : ltac2:(tb__ "0|5|
S4S3S11S8S23S42A1A1S14A3S4S3S22S86S5fA1S42A3S4S3S19S22A1M0S29S42S3dS42Z44M1A2A2S16S22S40A2A3S4S3S19S1aS6A1M2A1S79S40S37S82S40A1M3A3S16G2S4fA2A3S4S3S11S78S40S37G3S4fS12S22S38S17S22A1A3A5S14A3S4S3S22S9aS37S40G3S4fS38A5S53A3S4S3G0S29S53S3cS53A1A2S16S22S46A2A3S4S3G2S9S23S46A1A1S1cS6S3aS46A1S12S6Sa5S39G1Ze7S17SfA1SeA5S17S6A1A3A3A3S4S3S22S84S46A1S54A3S4S3S11S8S23S54A1A1S14A3S4S3S22S85S54A1S55A3S4S3S11S8S23S55A1A1S14A3S4S3S22S72S55A1S52A3S4S3S11S25S52A1S14A3S3S1aS1bS1S32A2M4A1S66S24G4S24S18S1S32SaS23S27R1A1A1A1S26R1A1A4LL;S76U12cS6bS52A3A4S12G4S18S1S32S9fS33A4S17G4A1A3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS5_checks_sf : ltac2:(tb__ "0|4|
S4S3S19S22A1M0S29S57S89S57A1A2S16S22S60A2A3S4S3S11S8S23S4aA1A1S14A3S4S3G0S29S4aS88S4aA1A2S16S22S4bA2A3S4S3G0S29S4bS87S4bA1A2S16S22S61A2A3S4S3S11S25S43A1S14A3S4S3S19S1aS6A1M1A1S79S43S7eS83S43A1M2A3S16G1S5aA2A3S4S3S11S78S43S7eG2S5aS12S22S80S17S22A1A3A5S14A3S4S3S11S25S5bA1S14A3S3S1aS1bS1S32A2M3A1S66S24G3S24S18S1S32SaS23S27R1A1A1A1S26R1A1A4LL;S76U12cS6bS5bA3A4S12G3S18S1S32S9eS33A4S17G3A1A3A3A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiS5_checks_post : ltac2:(tb__ "0|3|
S4S3S19S22A1M0S29S58S5eS58A1A2S16S22S4dA2A3S4S3G0S29S4dS5dS4dA1A2S16S22S59A2A3S4S3S22Sa2S99S18S5S5S73S7Z40A1A4A1S59A2S45A3S4S3S11S28S45S6fS3eA3S14A3S4S3S11S8aS3eS34A2S14A3S4S3S11S9cS34SdS23S45A1M1A1M2A2S14A3S4S3S11S98G2S41A2S14A3S4S3S11Sa3S3eS92S41A1S92S6dA1A3S14A3S4S3S11S97S3eS91S41A1S91S6dA1A3S14A3S4S3S11Sa4S10G1A1S8eS3eS90S6dA1A2S90S41A1A3S14A3S4S3S11S95S96S3eS8fS6dA1A2S8fS41A1A2S14A3S4S3G0S29S7dS5eS7dA1A2S16S22S4cA2A3S4S3G0S29S4cS5dS4cA1A2S16S22S44A2A3S4S3S11S28S44S6eS5cA3S14A3S4S3S11S8aS5cS34A2S14A3S3S11S9cS34SdS23S44A1A1A2S14A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiS5.

(* [comment removed for export] *)
Module Lib_load_obj_epiD_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "nil"; "app"; "bool"; "true"; "list"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "sprop"; "SLit"; "SPUle"; "valuation"; "SAlu"; "SPEq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "NDA"; "ANone"; "AHeadN"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efnode"; "ejcertAF"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2"; "vG"; "nB"; "vNx"; "cps_ad"; "C_L"; "E_fa0"; "E_fd0"; "E_ms0"; "E_s80"; "K_fa"; "L_L1"; "L_L3"; "L_ok"; "T_fa"; "T_fd"; "T_ms"; "X_A"; "X_A2"; "X_B"; "X_B2"; "X_fa0"; "X_fa1"; "vCap"; "vNd"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "gp"; "nd_d2"; "nd_e"; "PhisD"; "nd_d1"; "KU1"; "ndN"; "tvA"; "cutsD1"; "cutsD2"; "cutsD3"; "exitsD1"; "exitsD2"; "exitsD3"; "ndT"; "nd_A2"; "nd_B2"; "nd_CL"; "nd_d0"; "nd_fa"; "nd_z"; "H_ecertD1_ok"; "H_ecertD2_ok"; "H_ecertD3_ok"; "V_ld"; "keep_ecertD1_ok"; "keep_ecertD2_ok"; "keep_ecertD3_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "ldef"; "tblL"; "@Stdlib.PArith.BinPos.Pos"; "add"; "@Corelib.Init.Logic"; "eq"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideN"; "hide_set"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "E_bd0"; "K_disp"; "K_j1"; "L_fl0"; "L_fl1"; "L_j1s"; "Lb_j1"; "T_bd"; "T_fl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3"; "Ee_sf0"; "P_errL"; "Te_s8"; "Te_sf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "vARn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "e32"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builder_dispose.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3.

Definition V_ld : list positive := [466; 468]%positive.
Definition PhisD : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|4|
S1S3S8S19A1M0S10OFrho;M1A2S0G0G1S51S59A4S1S3G0S10OF_;M2A2M3S0G0G2S4S19A1S10S5dL_;A4S4G3A1A3A3").

Definition tvA : list (sv * sv) := ltac2:(tb__ "0|1|
S1S3SbSbA2M0S0SbSbS71SeZ40A1A4S4G0A1A3").
Definition KU1 : list bitem := [BIc 0 KU 1].
Definition nd_d0 : ndesc := ndEp tvL bd_disp.
Definition nd_d1 : ndesc := ndEp kept_bd brest_bd.
Definition nd_d2 : ndesc := ndEp tvA KU1.
Definition ndN (nd cap nx g : sv) : ndesc := ltac2:(tb__ "0|0|
S15S1S3SbSbA2S0SbSbVnd;S72Vcap;A1A4S40A3S58S5S55S3eS1S55S56Z0Z1S57A3S4S55A1A3A3S17Vnx;Vg;A2A4").
Definition ndT (nx g : sv) : ndesc := ltac2:(tb__ "0|0|
S15S40S58S3eS17Vnx;Vg;A2A4").
Definition nd_A2 : ndesc := ltac2:(tb__ "0|0|
S3fS70ScP2aaA1ScP2a9A1ScP2acA1A4").
Definition nd_CL : ndesc := ltac2:(tb__ "0|0|
S3fS35S34S20S1eA4").
Definition nd_B2 : ndesc := ltac2:(tb__ "0|0|
S3fS20ScS5bS1fP1A2A1ScS1fA1ScS5bS1fP3A2A1A4").
Definition nd_fa : ndesc := ltac2:(tb__ "0|0|
S15S40S58S3eS16A4").
Definition nd_e : ndesc := ltac2:(tb__ "0|0|
S15S4S3SbSbA2A1S58S4S55A1S16A4").
Definition nd_z : ndesc := ltac2:(tb__ "0|0|
S15S4S3SbSbA2A1S4S3S3SbS18A2SbA2A1S4S55A1S16A4").
Definition gp (g : sv) (k : Z) : sv := ltac2:(tb__ "0|0|
S11S62Vg;SeVk;A1A3").

Definition cutsD1 : list efnode := ltac2:(tb__ "0|5|
S1S3S3S3S13S14A2M0S2A2M1S3S18SbA2M2A2M3S0G1G2S0G0S2S0S13S14S64S4bA4U0M4A4S0S18SbZ186S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S6aS3dA4G4A4S0S18SbZ17cS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S6bS3aA4U1A4S0S18SbZ172S1aA4A4S4G3A1A3A3A3").
Definition exitsD1 : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S13S14A2M0S2A2M1S3S18SbA2M2A2M3S0G1G2S0G0S2S0S13S14S63S4bA4U0M4A4S0S18SbZ185S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S68S3dA4G4A4S0S18SbZ17bS1aA4M5A4S1G3S0G1G2S0G0S2S0S13S14S66S3dA4G4A4G5A4S1G3S0G1G2S0G0S2S0S13S14S67S3dA4G4A4G5A4S1G3S0G1G2S0G0S2S0S13S14S69S3aA4U1A4S0S18SbZ171S1aA4A4S4G3A1A3A3A3A3A3").
Definition cutsD2 : list efnode := ltac2:(tb__ "0|6|
S1S3S3S3S13S14A2M0S2A2M1S3S18SbA2M2A2M3S0G1G2S0G0S2S0S13S14S65S3aA4U1M4A4S0S18SbZ168S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S2fS48A4G4A4S0S18SbZ15eS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S22S4aA4G4A4S0S18SbZ12cM5S39S1eZ8A2A4A4S1G3S0G1G2S0G0S2S0S13S14S2cS47S20S1eA2A4G4A4S0S18SbG5S39S1eZ6A2A4A4S1G3S0G1G2S0G0S2S0S13S14S31S49A4G4A4S0S18SbG5S39ScS5bS1fP3A2A1ZcA2A4A4S4G3A1A3A3A3A3A3").
Definition exitsD2 : list efnode := ltac2:(tb__ "0|8|
S1S3S3S3S13S14A2M0S2A2M1S3S18SbA2M2A2M3S0G1G2S0G0S2S0S13S14S2aS3aA4U1M4A4S0S18SbZ167S1aA4M5A4S1G3S0G1G2S0G0S2S0S13S14S32S3aA4G4A4G5A4S1G3S0G1G2S0G0S2S0S13S14S2eS3aA4G4A4G5A4S1G3S0G1G2S0G0S2S0S13S14S28S48A4G4A4S0S18SbZ15dS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S24S4aA4G4A4S0S18SbZ12cM6S39S1eZ7A2A4A4S1G3S0G1G2S0G0S2S0S13S14S33S47S20S1eA2M7A4G4A4S0S18SbZ12bS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S30G7A4G4A4S0S18SbG6S39S1eZ5A2A4A4S1G3S0G1G2S0G0S2S0S13S14S29S49A4G4A4S0S18SbG6S39ScS5bS1fP3A2A1ZbA2A4A4S4G3A1A3A3A3A3A3A3A3A3").
Definition cutsD3 : list efnode := ltac2:(tb__ "0|5|
S1S3S3S3S13S14A2M0S2A2M1S3S18SbA2M2A2M3S0G1G2S0G0S2S0S13S14S27S4cA4U1M4A4S0S18SbZfaS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S2bS3bA4G4A4S0S18SbZf0S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S2dS3bA4G4A4S0S18SbZe6S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S6eS3bA4G4A4S0S18SbZdcS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S6fS4dA4G4A4S0S18SbZd2S1aA4A4S4G3A1A3A3A3A3A3").
Definition exitsD3 : list efnode := ltac2:(tb__ "0|5|
S1S3S3S3S13S14A2M0S2A2M1S3S18SbA2M2A2M3S0G1G2S0G0S2S0S13S14S23S4cA4U1M4A4S0S18SbZf9S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S25S3bA4G4A4S0S18SbZefS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S26S3bA4G4A4S0S18SbZe5S1aA4A4S1G3S0G1G2S0G0S2S0S13S14S6cS3bA4G4A4S0S18SbZdbS1aA4A4S1G3S0G1G2S0G0S2S0S13S14S6dS4dA4G4A4S0S18SbZd1S1aA4A4S4G3A1A3A3A3A3A3").

Definition keep_ecertD1_ok : list sprop := ltac2:(tb__ "0|0|
S1SdSfScP1d4A1SeZffffffffA1A2S4SdA1A3").
Definition H_ecertD1_ok : list sprop := ltac2:(tb__ "0|0|
S60S52S5S1bS41S44A3A2").
Lemma ecertD1_ok : ltac2:(tb__ "0|1|
S5cS6S1cS5eS38S3cU12cS21S38S36S1bS1bS5fS4eA1M0S41A4S36S1bS1bG0S44A4A8S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition keep_ecertD2_ok : list sprop := ltac2:(tb__ "0|3|
S1SdSfScP110A1M0SeZ800000000000A1A2S1SdSfScP1d1A1ScP1eA1M1A2S1SdS12S11S61ScP156A1M2SeZ3A1A3G0A2S1SdSfG2SeZ1fffffffffffffffA1A2S1SdSfG1SeZ7fffff800000A1A2S4SdA1A3A3A3A3A3").
Definition H_ecertD2_ok : list sprop := ltac2:(tb__ "0|0|
S60S53S5S1bS42S45A3A2").
Lemma ecertD2_ok : ltac2:(tb__ "0|1|
S5cS6S1cS5eS38S3cU12cS21S38S36S1bS1bS5fS4fA1M0S42A4S36S1bS1bG0S45A4A8S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition keep_ecertD3_ok : list sprop := ltac2:(tb__ "0|3|
S1SdSfScP110A1M0SeZ800000000000A1A2S1SdSfScP156A1M1SeZ1fffffffffffffffA1A2S1SdSfS11S61G1SeZ3A1A3M2G0A2S1SdSfG0G2A2S4SdA1A3A3A3A3").
Definition H_ecertD3_ok : list sprop := ltac2:(tb__ "0|0|
S60S54S5S1bS43S46A3A2").
Lemma ecertD3_ok : ltac2:(tb__ "0|1|
S5cS6S1cS5eS38S3cU12cS21S38S36S1bS1bS5fS50A1M0S43A4S36S1bS1bG0S46A4A8S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ldef_reads : phi_reads V_ld ldef.
Proof.
  intros rho rho' HV _ HM HD z Hz. rewrite <- HM. apply HD.
  rewrite <- (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), <- (uval_rw rho rho' 468 xLK eq_refl ltac:(apply HV; cbn; tauto)). exact Hz.
Qed.
Lemma PhisD_reads : ltac2:(tb__ "0|3|
S37S3S8S19A1M0S10OF_;M1A2M2G2S1dS9G0G1R1A3SaG0G1R1A3A2Lp;S3cA3").
Proof. constructor; [exact ldef_reads | constructor; [intros rho rho' _ _ _ _; exact I | constructor]]. Qed.

Lemma tblL_ldef : ltac2:(tb__ "0|0|
S10S5aR1A1S59R2A1F_;Frho;").
Proof. intros rho [_ H]. exact H. Qed.
End Lib_load_obj_epiD_eqs.

(* [comment removed for export] *)
Module Lib_load_obj_hv3f.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "nat"; "app"; "list"; "Some"; "length"; "option"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sobj"; "SVar"; "SPUle"; "sprop_eqb"; "sv"; "ss_facts"; "ss_next"; "ss_objs"; "DUnknown"; "SPEq"; "SPUlt"; "ob_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "V_B"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_base"; "entailsA"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "g5"; "vLEN"; "vF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "oidx"; "extra_hv"; "robjs_chkR"; "sel_front"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "@Stdlib.Lists.List"; "existsb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLC"; "pH"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "AHead"; "NDA"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "LAX"; "LAXK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "optL'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3"; "brest_vr"; "objs_nl"; "sh_of"; "tv_fail"; "tv_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv3e"; "X_rlF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_hv3f"; "X_rlFb"; "X_rlFr"; "lx_chk"; "s_rlF"; "xf_tail"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "spm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "V_below"; "bud_le2"; "wsub_id_on"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv3e OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition xf_tail (T : axst) : list axform := ltac2:(tb__ "0|2|
S4S1bS1eS2cS50Z90A1SdZ0A1VT;A3A1S5S1bA1M0A3S8S1bA1S43S1cVT;R1A2A1S23S7S1bR2S4S1bS2fS4S6S2cS10PaA1M1SdN90A1R1A3S4S6S2cG1SdN88A1R1A3S5S6A1A3A3SaSfS16S22R1A1A1A2A2S4S1bS1dU0A1G0A3A3A3TT1;Tpre;").

Definition lx_chk (tv : list (sv * sv)) (bd : list bitem) (tvj : list (sv * sv)) (bdj : list bitem) (X L Lr Lb : axst) (s : wsub) : Prop := ltac2:(tb__ "0|a|
S1S0S8SfA1S16S22VL;A1M0A1S7SfS45VL;A1M1S4SfS58S29Z4Z1eS1aS46VL;A1A1S17A5S5SfA1A3A3A3S1S0S13S24VL;A1SdS59A1A3S1S0S3S27S4SeS18S26S29A1S2bA2S4SeS11S10S29A1SdS5cS5bZ2Z3dA2Z1A2A1A2S5SeA1A3A3S14G0A1M2A2S2A3S1S0S3S3aS15G0A1M3S3cVtv;S1fVbd;S3bS35S2A2M4A4M5A2S2A3S1S0S3S2eG2Vtv;S1fS2dG1A5S2A3S1S0S3S40G2A1S2A3S1S0S23S57VL;G1P6eS5ScS33S33A2A1A4VLr;A3S1S0SbS23A1S1cVLr;S4eVLr;A1A2S9S23VLb;A2A3S1S0S38S51S28S22VLb;A1M6S22VX;A1A3Vs;A3S1S0S3S25VLb;VX;Vs;A3S2A3S1S0S3S39Vs;S28A2S2A3S1S0S3S5aS28S15G6A1M7A2S2A3S1S0S3S3aG7G5A2S2A3S1S0S3S52Vs;Vtv;Vtvj;A3S2A3S1S0S3S3fVs;S1fS1fA3S2A3S1S0S3S54S14G6A1S31Vs;Vbdj;A2Vbd;A3S2A3S1S0S3S3dS3eVs;G4A2G4A2S2A3S1S0S3S55S20Vs;A2S2A3S1S0S13S37Vs;P1ccM8A2S10G8A1A3S1S0S13S37Vs;P1d3M9A2S10G9A1A3S1S0S3S56Vtvj;S21A2S2A3S1S0S3S53G3S20A2S2A3S1S0S3S32SeS12S19S36S34A2A1G2A3S2A3S1S0S3S32SeS12S11S34S2aA2A1G2A3S2A3S0S3S32SeS12S11S2aSdZ4000000A1A2A1G2A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").

Definition X_rlFr : axst := Eval vm_compute in shadow_release_stateA X_rlF (objs_nl X_rlF) 110 [].
Definition X_rlFb : axst := Eval vm_compute in optL' (apply_axforms X_rlFr (xf_tail X_rlFr)).
Definition s_rlF : wsub := Eval vm_compute in infer_sub NP (ax_S X_rlFb) (ax_S X_latchE2).
Lemma hv3_checks_rlF : ltac2:(tb__ "0|1|
S4cS47S44S48S4S30S41Z0M0A1S4S30S42G0A1S5S30A1A3A3S4fS49S4bS4aS4dA9").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_load_obj_hv3f.

