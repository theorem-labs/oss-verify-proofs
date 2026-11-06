(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartArgBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartReshape StartHandoffLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceM.

(* [comment removed for export] *)
Module Lib_handle_f_s8.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "app"; "pair"; "prod"; "None"; "bool"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "cell"; "sobj"; "sprop"; "SLit"; "SAlu"; "DUnknown"; "mkObj"; "SPUle"; "FcsrFrm0"; "SPBranch"; "SPNot"; "SPUlt"; "SVar"; "mkSS"; "ss_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "spm"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "xbo"; "pDco"; "shB"; "pKco"; "reshapeA"; "xfo"; "optAp"; "vec_facts0"; "O_F"; "O_Wf"; "O_flag"; "O_frame"; "V496"; "V528"; "V560"; "V592"; "V752e"; "V784"; "V816"; "am2"; "builderF"; "hdr3"; "mi_c"; "pA"; "pHP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "AXMerge"; "apply_axforms"; "AXSelect"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "O_data"; "kb"; "hG"; "vec_facts"; "HNEXT"; "O_cE"; "O_cP"; "av_d"; "av_k"; "hF"; "h_fregs"; "h_xregs"; "tB"; "tL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "pDtr"; "pKtr"; "O_dataD"; "hint12"; "ncoB"; "trK"; "tr_facts"; "triF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7"; "pNT"; "qDrp'"; "qDts'"; "qKrp'"; "qKts'"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "ALU_XOR"; "BC_EQ"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8"; "lDfv"; "lDmi"; "lDmm"; "lDsg"; "lKfv"; "lKmi"; "lKmm"; "lKsg"; "pL"; "src_of"; "LC"; "XL0"; "cFV"; "cMI"; "cMM"; "cSG"; "off_of"; "FCUT3"; "F_L14"; "F_Lold"; "L_facts"; "XL"; "datasL"; "g_need"; "objs_face3"; "regsLs"; "sel_g"; "shL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.HFAddr"; "hf_L14"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_reopen_stateA"; "shobj"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@Corelib.Lists.ListDef"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "mkA"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "O_al"; "vERR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "Pre_mc"; "X_face"; "coP"; "co_live"; "pX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition pL : sv := SVar 357.
Definition lDmi : sv := SVar 360. Definition lKmi : sv := SVar 361. Definition lDfv : sv := SVar 362. Definition lKfv : sv := SVar 363.
Definition lDmm : sv := SVar 364. Definition lKmm : sv := SVar 365. Definition lDsg : sv := SVar 366. Definition lKsg : sv := SVar 367.
Definition cMI (t : sv) : sv := ltac2:(tb__ "0|0|
SeS58S32S3eZ3Vt;A2A3").
Definition cFV (t : sv) : sv := SAlu ALU_ADD fv_c t.
Definition cMM (t : sv) : sv := SAlu ALU_ADD mm_c t.
Definition cSG (t : sv) : sv := SAlu ALU_ADD sg_c t.

Definition F_Lold : list cell := Eval vm_compute in
  List.filter (fun c => negb (existsb (fun o => sv_eqb (c_off c) (SLit o)) [-352; -328; -320; -344; -336; -280; -224; -264; -200; -208; -232; -192; -256; -184; -248; -216; -240; -176; -136; -144])) F_cells.
Definition F_L14 : list cell := ltac2:(tb__ "0|0|
S3SaS70S0SaS19N160S1eZ45A1A2S0SaS19N148S1eZ3eA1A2S0SaS19N140S1eZ41A1A2S0SaS19N158S1eZ42A1A2S0SaS19N150S1cZ228A1A2S0SaS19N118SdZ5555555555555555A1A2S0SaS19Ne0S1cZ1f0A1A2S0SaS19N108S1cZ208A1A2S0SaS19N170S1cZ268A1A2S0SaS19Nc8S1cZ258A1A2S0SaS19Nd0S1cZ250A1A2S0SaS19N168S1cZ248A1A2S0SaS19Ne8S1cZ238A1A2S0SaS19Nc0S1cZ230A1A2S0SaS19N100S21Zf8A1A2S0SaS19Nb8SeS5aS4bSdZffffffffffffffffA1A3A2S0SaS19Nf8S21ZecA1A2S0SaS19Nd8S1cZ1f8A1A2S0SaS19Nf0S53A2S0SaS19Nb0S1eZ3fA1A2S0SaS19N88S1dA2S0SaS19N98S1cZ210A1A2S0SaS19Na8S1cZ218A1A2S0SaS19N90S1eZ0A1A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition objs_face3 (cur hp : sv) (co rp tr mi fv mm sg ts : sobj) (Fc fcells txt : list cell) (datas : list sobj) (tail : list sobj) : list sobj := ltac2:(tb__ "0|1|
S3SbS0SbS25S0SbS27S3SaS31Vfcells;A3A1S0SbS26S2SbA1M0A3A3A3S3SbS83S3SbS0SbS24VFc;A1G0A3S3SbS30S87Vhp;Vco;Vrp;Vtr;Vmi;Vfv;Vmm;Vsg;Vts;AaS3SbS0SbS86S0SbS43Vcur;A1S0SbS42S0SbS10S49SdZ0A1S4aVtxt;SfA5G0A3A3A3A3S3SbVdatas;Vtail;A3A3A3A3A3A3").
Definition FCUT3 (pc : Z) (regs : list (nat * sv)) (cur : sv) (co rp tr mi fv mm sg ts : sobj) (Fc fcells : list cell) (datas tail : list sobj)
                (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S84S17Vpc;S48Vregs;A1S47S12S6S9A1S75Vcur;S34Vco;Vrp;Vtr;Vmi;Vfv;Vmm;Vsg;Vts;VFc;Vfcells;S2SaA1Vdatas;Vtail;AfVfacts;S41S8A9VX;A2").
Definition datasL (dmi kmi dfv kfv dmm kmm dsg ksg : sv) (trd : odefault) : list sobj := ltac2:(tb__ "0|2|
S0SbS3dS44Z4M0S45A3S0SbS3dVdmi;ZcM1Vkmi;A3S0SbS3dVdfv;G0Vkfv;A3S0SbS3dVdmm;G0Vkmm;A3S0SbS3dVdsg;G0Vksg;A3S0SbS3dS1dG1S1fA3S0SbS3dS54G0S56A3S0SbS4dS4bG0S4cVtrd;A4S0SbS3dS55Z1S57A3S2SbA1A3A3A3A3A3A3A3A3A3").
Definition XL (dmi dfv dmm dsg kmi kfv kmm ksg : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S89Vdmi;Vdfv;Vdmm;Vdsg;S1dS54S4bS55Vkmi;Vkfv;Vkmm;Vksg;S1fS56S4cS57A10").
Definition regsLs : list (nat * sv) := ltac2:(tb__ "0|5|
S0S5S1S9A2M0S4S1S9U2S1aS7dA1M1A4S0G0S4S1S9U8S16PaA1A4S0G0S4S1S9U9G1A4S0G0S4S1S9U5S1dA4S0G0S4S1S9U12S85A4S0G0S4S1S9U13S1cZ4ecA1M2A4S0G0S4S1S9U14S1eZ43A1A4S0G0S4S1S9U15S4fA4S0G0S4S1S9U16SeS5aG2SdZffffffffffffffffA1M3A3A4S0G0S4S1S9U18SeS5aS1cZ4e8A1M4G3A3A4S0G0S4S1S9U19S4bA4S0G0S4S1S9U1bG4A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition L_facts (t dmi kmi dfv kfv dmm kmm dsg ksg : sv) : list sprop := ltac2:(tb__ "0|2|
S3ScS0ScS15Vt;S53A2S0ScS11S53S2fA2S0ScS14S13S5bS53SdZ0A1A3A1S0ScS4eVt;A1S0ScS11S3eZcM0S53A2S3eZ4M1S4cA2A2S0ScS11S3eG0S33A2S3eG0S1fA2A2S2ScA1A3A3A3A3A3A3S3ScS40Vdmi;S6aVt;A1Vkmi;G0P168A5S3ScS40Vdfv;S69Vt;A1Vkfv;G1P16aA5S3ScS40Vdmm;S6bVt;A1Vkmm;G1P16cA5S3ScS40Vdsg;S6cVt;A1Vksg;G1P16eA5S3ScS51S4bS4cP157A3S3ScS23S54S56G1P160A4S3ScS23S55S57Z1P162A4S52A3A3A3A3A3A3A3A3").
Definition shL : list sobj := ltac2:(tb__ "0|1|
S0SbS7fS3fZ1cZ21S2SaA1M0SfA5S0SbS7fS3fZ26Z27G0SfA5S2SbA1A3A3").
Definition LC (pc : Z) (regs : list (nat * sv)) (t : sv) (fcells : list cell) (tail : list sobj) (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S6eVpc;S3S5S1S9A2S76Vregs;A3S8cS8aS2cS54S56A2S2dS4bSdZ0A1S4cA3S28S5eS6aVt;A1S62A3S29S5dS69Vt;A1S61A3S2aS5fS6bVt;A1S63A3S2bS60S6cVt;A1S64A3S2eS55S57A2S6fVfcells;S73S5eS62S5dS61S5fS63S60S64S50S53A1A9Vtail;S3ScVfacts;S71Vt;S5eS62S5dS61S5fS63S60S64A9A3VX;A11").
Definition XL0 : list (sv * sv) := ltac2:(tb__ "0|0|
S72S5eS5dS5fS60S62S61S63S64A8").

Definition L14 : axst := ltac2:(tb__ "0|1|
S67S7cS0S5S1S9A2M0S4S1S9U17S65A4S2G0A1A3S65S2SaA1S78S0ScS8bS2ScA1A3S68A7").

Definition XLJ : axst := ltac2:(tb__ "0|1|
S67S7cS0S5S1S9A2M0S4S1S9U17S65A4S2G0A1A3S65S2SaA1S2SbA1S2ScA1S68A7").
Definition reopenL (A : axst) : axst := ltac2:(tb__ "0|1|
S7eS7eVA;S7bVA;A1M0S3fZ1cZ21A5G0S3fZ26Z27A5").
Goal leaf_matches1A NPH (leaf_at J hf_L14 0) XLJ = true /\ leaf_matches1A NPH (reopenL (ax_add_facts [co_live] XLJ)) L14 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition lvsL14 := Eval vm_compute in lvs L14.
Goal lvsL14 = [(memcpy_pc, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_g1_0 : axst := Eval vm_compute in leaf_at L14 memcpy_pc 0.

Goal local_ok (ob_cells (nth 36 (ss_objs (ax_S E_g1_0)) O_dummy)) DUnknown 28 33 (224, 36) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_g1_1 : axst := Eval vm_compute in optAp (apply_axforms E_g1_0 [AXSelect (sel_last E_g1_0 36)]).
Definition E_g1_2 : axst := Eval vm_compute in shadow_release_stateA E_g1_1 (objs_butlast E_g1_1) 160 [(224, 36)].

Definition E_g1_3 : axst := Eval vm_compute in shadow_release_stateA E_g1_2 (objs_butlast E_g1_2) 160 [].

Definition src_of (E : axst) : sv := ltac2:(tb__ "0|0|
S81S9UbS18S79VE;A1A1SdZ0A1A4").
Definition off_of (E : axst) : sv := ltac2:(tb__ "0|3|
S9S9Lx;S66VE;A1S3bSdZ0A1M0Lz;S3aG0Li;S59S9S9S59S9Lop;R3R1G0G0G0G0G0G0G0G0G0X59xaLo;La;Lop;S59S9S9G0Lb;La;M1Lop;S5cG1Lop;M2G2S7S3cS9G0La;Lw;Lsgn;S3aS9S3bG0Lk;Li;Ll;X9x8").

Definition g_need (E : axst) : list sprop := ltac2:(tb__ "0|1|
S0ScS11SeS58S66VE;A1SdZcM0A1A3SeS58S1dS3eG0S1fA2A3A2S2ScA1A3").
Definition g_site (E : axst) (dj : Z) : axst := ltac2:(tb__ "0|6|
S6dVE;A1S9S22S38VE;S0S35S36U1SdVdj;A1A2S0S35S36U2M0SdS80Vdj;ZcM1A2A1A2S0S35S36U22R1A2S0S35S36U23M2SeS58R1SdG1A1M3A3A2S2S35A1A3A3A3A3A2A1S7aS8eS74VE;A1S20S20R1G0S10S21Vdj;A1SdZ0A1M4G3S2SaA1M5SfA5A3G2S10S66VE;A1G4G3G5SfA5A3A2TE1;Toff;").
Definition s_g (E : axst) : wsub := ltac2:(tb__ "0|1|
S0S5S3aS9A2M0S4S3aS9P35S21Ze0A1A4S0G0S4S3aS9P36SdZ24A1A4S0G0S4S3aS9P37S1dA4S0G0S4S3aS9P38S3eZcS1fA2A4S0G0S4S3aS9S8fS1bA4S8dPaS79VE;A1S79S88A1A3A3A3A3A3A3").

Definition sel_g : list nat := ltac2:(tb__ "0|1|
S3S1S0S1U0S0S1U5S0S1U1S0S1U6S0S1U7S0S1U3S0S1U4S0S1U8S2S1A1M0A3A3A3A3A3A3A3A3S3S1S82U9U15A2S0S1U1eS0S1U1fS0S1U20S0S1U21S0S1U22S0S1U23S0S1U2S0S1U24S0S1U25S0S1U26S0S1U27G0A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition g_back (T : axst) (E : axst) (dj : Z) : axst := ltac2:(tb__ "0|5|
S6dVE;A1S9S20S20VT;U1M0S10S46SdVdj;A1SdS80Vdj;ZcM1A2A1S2SaA1M2SfA5A3U2S10S1dR1SeS58R1SdG1A1A3G2SfA5A3S7aS22S38R1S0S35S39S77A1S0S35S37G0A1M3S0S35G3S0S35S37U20A1M4S0S35G4S2S35A1A3A3A3A3A3A2A1TT1;Toff;").

Definition E_g1 : axst := Eval vm_compute in g_site E_g1_3 224.
Definition R_g1 : list sobj := Eval vm_compute in optR (entails_frA E_g1 Pre_mc (s_g E_g1)).
Goal entails_frA E_g1 Pre_mc (s_g E_g1) = Some R_g1 /\ call_checkPA E_g1 Pre_mc (s_g E_g1) R_g1 [L_mc1; L_mc1] = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_g1 : axst := Eval vm_compute in g_back (T_afterA Pre_mc E_g1 (s_g E_g1) R_g1 L_mc1) E_g1_3 224.
Goal shape T_g1 = shape E_g1_3 /\ lvs T_g1 = [(memcpy_pc, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_g2_0 : axst := Eval vm_compute in leaf_at T_g1 memcpy_pc 0.
Definition E_g2 : axst := Eval vm_compute in g_site E_g2_0 236.
Definition R_g2 : list sobj := Eval vm_compute in optR (entails_frA E_g2 Pre_mc (s_g E_g2)).
Goal entails_frA E_g2 Pre_mc (s_g E_g2) = Some R_g2 /\ call_checkPA E_g2 Pre_mc (s_g E_g2) R_g2 [L_mc1; L_mc1] = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_g2 : axst := Eval vm_compute in g_back (T_afterA Pre_mc E_g2 (s_g E_g2) R_g2 L_mc1) E_g2_0 236.
Goal shape T_g2 = shape E_g1_3 /\ lvs T_g2 = [(memcpy_pc, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_g3_0 : axst := Eval vm_compute in leaf_at T_g2 memcpy_pc 0.
Definition E_g3 : axst := Eval vm_compute in g_site E_g3_0 248.
Definition R_g3 : list sobj := Eval vm_compute in optR (entails_frA E_g3 Pre_mc (s_g E_g3)).
Goal entails_frA E_g3 Pre_mc (s_g E_g3) = Some R_g3 /\ call_checkPA E_g3 Pre_mc (s_g E_g3) R_g3 [L_mc1; L_mc1] = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_g3 : axst := Eval vm_compute in reopenX 38 39 (g_back (T_afterA Pre_mc E_g3 (s_g E_g3) R_g3 L_mc1) E_g3_0 248).

Goal lvs T_g3 = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_handle_f_s8.

(* [comment removed for export] *)
Module StartHandoffPres.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "sub"; "of_nat"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "SLit"; "SAlu"; "SVar"; "rm"; "ss_objs"; "valuation"; "sobj"; "smatch"; "sv"; "sv_eqb"; "soff"; "eval"; "image_byte"; "ob_base"; "ob_hi"; "ob_lo"; "sstate"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "option"; "None"; "pair"; "andb"; "@Corelib.Numbers.BinNums"; "Z"; "N"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffPres"; "has_obj"; "o_aux_b"; "o_env_b"; "o_env_hi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8"; "MAIN_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "page_round_up_Z"; "Model"; "event"; "in_argv"; "in_envp"; "ProcInput"; "stack_max_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "mkEntry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS"; "ARGF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF"; "arg_layout"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "img_len"; "valid_entry48"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "PhdrInfo"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.StackLayout"; "EntryDraw"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init"; "imgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartArgBytes"; "RNDo"; "ms0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "ms0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAP"; "STKP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "PRES"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymSoundM SymFrame SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartArgBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require os.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartArgBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation U := bv_unsigned.

Lemma ms0_stack_present : ltac2:(tb__ "0|3|
S22S44A1S28S43S1Q40M0A1S45S37S27S7S8S0G0R4A2ScS41S35R2A1S36R2A1A2A1A2S9Z2Z2fA2A2S4S7SbS0G0R5A2M1S38A2R2A2SaR2S32S8G1ScS41S35R3A1S36R3A1A2A1A2A1A2A2S7Z0R3A2S5S3S23S1Q8A1M2A1S3aS4aRaR9R8R7R6R5A6S2G0R4A2A2S24G2A1A3A1F_;F_;F_;Fz;Finp;Fdraw;Fsp;Fph;Fpc0;Fsegs;").
Proof.
  intros segs pc0 ph sp draw inp z Hfit Hz Hz0. rewrite ms0_mem_def. unfold stack_to_mem.
  pose proof (entry_stack_image_top ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw) as ET.
  unfold entry_page_top, entry_block_top in ET. pose proof (InitState.length_BSB ph sp draw inp) as LB. unfold bsb in LB. rewrite LB in ET.
  assert (PT : page_round_up_Z (U sp + Z.of_nat (img_len (in_argv inp) (in_envp inp))) <= 2 ^ 47).
  { unfold page_round_up_Z, page_size. set (q := U sp + Z.of_nat (img_len (in_argv inp) (in_envp inp))) in *.
    assert (Q : (q + 4096 - 1) / 4096 <= (2 ^ 47 + 4096 - 1) / 4096) by (apply Z.div_le_mono; lia).
    change ((2 ^ 47 + 4096 - 1) / 4096) with (2 ^ 35) in Q. change (2 ^ 47) with (2 ^ 35 * 4096). nia. }
  assert (EZ : U (Z_to_bv 64 z) = z) by (apply Z_to_bv_small; change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite EZ. destruct (Z.leb (U sp) z) eqn:E1.
  - apply Z.leb_le in E1. replace (z - U sp <? Z.of_nat (length (entry_stack_image ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw))) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (nth_error _ (Z.to_nat (z - U sp))) as [b|] eqn:E2; [discriminate|]. apply nth_error_None in E2. lia.
  - apply Z.leb_gt in E1. replace (U sp - stack_max_size <=? z) with true by (symmetry; apply Z.leb_le; lia).
    replace (z <? U sp) with true by (symmetry; apply Z.ltb_lt; lia). discriminate.
Qed.

Definition has_obj (b lo hi : sv) (objs : list sobj) : bool := ltac2:(tb__ "0|0|
S4dS15S15S26S26S18S1cR1A1Vb;A2S18S1eR1A1Vlo;A2A2S18S1dR1A1Vhi;A2A2Lo;Vobjs;A3").
Lemma has_obj_sound : ltac2:(tb__ "0|3|
S17S17S17S22S15A1S14S1Q40M0A1S3S20S2bR6R5R4R3A4S21A3S4S7S8S0G0S1aR3R7A2A2M1S19R3R6A2A2S0G0R2A2M2A2SaG2S8G1S19R3R5A2A2A2A2S31R4R5R3A3F_;F_;Fa;Frho;Fobjs;Fhi;Flo;Fb;").
Proof.
  intros b lo hi objs rho a H Hr. apply existsb_exists in H as (o & Ho & E). apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
  exists o. split; [exact Ho|]. unfold obj_range, obj_lo_of, obj_hi_of. cbn [fst snd]. rewrite E1, E2, E3. exact Hr.
Qed.

Definition o_env_b : sv := ltac2:(tb__ "0|0|
S10S29S10S29S11P1A1S10S2aS11P2A1SfZ3A1A3A3SfZ10A1A3").
Definition o_env_hi : sv := ltac2:(tb__ "0|0|
S10S29S10S2aS11P3A1SfZ3A1A3SfZ8A1A3").
Definition o_aux_b : sv := ltac2:(tb__ "0|1|
S10S29S10S29S10S29S11P1A1S10S2aS11P2A1SfZ3A1M0A3A3S10S2aS11P3A1G0A3A3SfZ18A1A3").

Lemma main_stack_objs : ltac2:(tb__ "0|4|
S20S13S30S2fR1A1A1A1S22S15A1S4S3S20S2bS11P1A1M0SfN100000A1SfN11c0A1R1A4S21A3S4S3S20S2bS10S29G0SfN70A1M1A3SfN1150A1SfZ0A1M2R1A4S21A3S4S3S20S2bG0G1G2R1A4S21A3S4S3S20S2bG0G2SfZ10A1M3R1A4S21A3S4S3S20S2bS2dG2S2eR1A4S21A3S4S3S20S2bS2cG2SfZa0A1R1A4S21A3S4S3S20S2bS11P4A1G2S10S29S11P5A1SfZ1A1A3R1A4S21A3S3S20S2bS11P6A1G2G3R1A4S21A3A2A2A2A2A2A2A2TL;Fv;").
Proof. intros [|]; vm_cast_no_check (conj (@eq_refl bool true) (conj (@eq_refl bool true) (conj (@eq_refl bool true) (conj (@eq_refl bool true) (conj (@eq_refl bool true) (conj (@eq_refl bool true) (conj (@eq_refl bool true) (@eq_refl bool true)))))))). Qed.

Lemma U_add_neg : ltac2:(tb__ "0|2|
S1Q40M0A1S27S4S7SdS9Z2M1Z28A2A1R1A2S7R1Z0A2A2S7S9G1Z29A2S0G0R3A2A2S3S27S0G0S46S29R4S2G0R3A2A3A2S8S0G0R4A2R3A2A3F_;F_;Fc;Fx;").
Proof.
  intros x c Hc Hx. pose proof (urange x) as Ux. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

Section Cover.
Variable rho : valuation.
Hypothesis HX1 : ltac2:(tb__ "0|1|
S4S7Z7fff80000000S0Q40SeVrho;P1A2A2M0A2S7G0S9Z2Z2fA2A2A2").
Hypothesis HAL : arg_layout rho.
Hypothesis H6 : ltac2:(tb__ "0|2|
S4S7S8S8S0Q40M0SeVrho;P4A2A2S0G0SeVrho;P5A2A2A2Z1A2S0G0SeVrho;P6A2A2M1A2S7S8G1Z10A2S9Z2Z2fA2A2A2").

Lemma main_cover : ltac2:(tb__ "0|2|
S20S1Q40M0A1S4S7SbS0G0SeVrho;P1A2A2Z100000A2S0G0R1A2M1A2SaG1S32S8S0G0SeVrho;P6A2A2Z10A2A1A2A2S6S31Vrho;S13S30S2fR3A1A1A1R2A3S3fVrho;R2A2A2F_;Fa;Fv;").
Proof.
  intros v a Ha. pose proof HAL as (A1 & A2 & A3 & A5 & A4). destruct H6 as [H6a H6b].
  pose proof (main_stack_objs v) as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8). cbv zeta in O1, O2, O3, O4, O5, O6, O7, O8.
  pose proof (urange (rw rho 1%positive)) as U1. pose proof (urange (rw rho 2%positive)) as U2. pose proof (urange (rw rho 3%positive)) as U3.
  pose proof (urange (rw rho 4%positive)) as U4. pose proof (urange (rw rho 5%positive)) as U5. pose proof (urange (rw rho 6%positive)) as U6.
  assert (S2 : U (alu64 ALU_SLL (rw rho 2%positive) (Z_to_bv 64 3)) = 8 * U (rw rho 2%positive)) by (apply U_sll3; lia).
  assert (S3 : U (alu64 ALU_SLL (rw rho 3%positive) (Z_to_bv 64 3)) = 8 * U (rw rho 3%positive)) by (apply U_sll3; lia).
  assert (E1 : U (alu64 ALU_ADD (rw rho 1%positive) (alu64 ALU_SLL (rw rho 2%positive) (Z_to_bv 64 3))) = U (rw rho 1%positive) + 8 * U (rw rho 2%positive)).
  { rewrite U_add_words by (rewrite S2; lia). rewrite S2. reflexivity. }
  assert (E2 : U (alu64 ALU_ADD (alu64 ALU_ADD (rw rho 1%positive) (alu64 ALU_SLL (rw rho 2%positive) (Z_to_bv 64 3))) (alu64 ALU_SLL (rw rho 3%positive) (Z_to_bv 64 3)))
               = U (rw rho 1%positive) + 8 * U (rw rho 2%positive) + 8 * U (rw rho 3%positive)).
  { rewrite U_add_words by (rewrite E1, S3; lia). rewrite E1, S3. reflexivity. }

  destruct (Z_lt_le_dec (U a) (U (rw rho 1%positive) - 4544)) as [C1|C1].
  { left. apply (has_obj_sound _ _ _ _ rho a O1). cbn [eval]. rewrite !soff_lit_small by lia. lia. }
  destruct (Z_lt_le_dec (U a) (U (rw rho 1%positive) - 112)) as [C2|C2].
  { left. apply (has_obj_sound _ _ _ _ rho a O2). cbn [eval]. rewrite !soff_lit_small by lia. rewrite U_add_neg by lia. lia. }
  destruct (Z_lt_le_dec (U a) (U (rw rho 1%positive))) as [C3|C3].
  { left. apply (has_obj_sound _ _ _ _ rho a O3). cbn [eval]. rewrite !soff_lit_small by lia. lia. }
  destruct (Z_lt_le_dec (U a) (U (rw rho 1%positive) + 16)) as [C4|C4].
  { left. apply (has_obj_sound _ _ _ _ rho a O4). cbn [eval]. rewrite !soff_lit_small by lia. lia. }

  destruct (Z_lt_le_dec (U a) (U (rw rho 1%positive) + 16 + 8 * U (rw rho 2%positive))) as [C5|C5].
  { right. split; [exact C4 | left; exact C5]. }

  destruct (Z_lt_le_dec (U a) (U (rw rho 1%positive) + 16 + 8 * U (rw rho 2%positive) + 8 * U (rw rho 3%positive) + 8)) as [C6|C6].
  { left. apply (has_obj_sound _ _ _ _ rho a O5). unfold o_env_b, o_env_hi. cbn [eval].
    rewrite (U_add_small _ 16) by (rewrite ?E1; lia). rewrite E1.
    rewrite soff_lit_small by lia. unfold soff. cbn [eval].
    rewrite signed_small by (rewrite U_add_small; rewrite ?S3; lia). rewrite U_add_small by (rewrite ?S3; lia). rewrite S3. lia. }

  destruct (Z_lt_le_dec (U a) (U (rw rho 4%positive))) as [C7|C7].
  { left. apply (has_obj_sound _ _ _ _ rho a O6). unfold o_aux_b. cbn [eval]. rewrite !soff_lit_small by lia.
    rewrite U_add_small by (rewrite ?E2; lia). rewrite E2. lia. }

  destruct (Z_lt_le_dec (U a) (U (rw rho 4%positive) + U (rw rho 5%positive) + 1)) as [C8|C8].
  { left. apply (has_obj_sound _ _ _ _ rho a O7). cbn [eval]. rewrite soff_lit_small by lia. unfold soff. cbn [eval].
    rewrite signed_small by (rewrite U_add_small; lia). rewrite U_add_small by lia. lia. }

  destruct (Z_lt_le_dec (U a) (U (rw rho 6%positive))) as [C9|C9].
  { right. split; [exact C4 | right; split; [exact C8 | left; exact C9]]. }

  destruct (Z_lt_le_dec (U a) (U (rw rho 6%positive) + 16)) as [C10|C10].
  { left. apply (has_obj_sound _ _ _ _ rho a O8). cbn [eval]. rewrite !soff_lit_small by lia. lia. }

  right. split; [exact C4 | right; split; [exact C8 | right; lia]].
Qed.
End Cover.

Lemma smatch_inranges_presentS : ltac2:(tb__ "0|4|
S14S1fS22S34A1M0S3bS33S1Q40A1S16S39R6R5S25G0S3cR4S3dR3R2A2A4A4S31R7S13R6A1R2A3S3S23S1Q8A1M1A1M2S1bS39R3A2S24G1A1M3A3S5S3G2S3aR6R4A2G3A3A1F_;F_;F_;Fa;Fmd;Fms;Ftr;FS;Frho;").
Proof.
  intros rho S tr ms md a Hsm Hin Himg.
  pose proof Hsm as (WF & _ & _ & _ & ROM & _). cbn [snd cfg_ms cfg_model] in ROM.
  pose proof (proj1 (smatch_mm segsA _ _ _ _ _ Hsm)) as HOL.
  destruct Hin as (o & Ho & Hr). unfold obj_range in Hr. cbn [fst snd] in Hr.
  pose proof (proj1 (Forall_forall _ _) HOL o Ho) as OH.
  unfold swf in WF. apply andb_true_iff in WF as [WF _]. apply andb_true_iff in WF as [_ WFO].
  rewrite forallb_forall in WFO. specialize (WFO o Ho).
  destruct (obj_byte_readable segsA rho ms o (U a - U (eval rho (ob_base o))) (ss_next S) ROM WFO OH ltac:(lia)) as [b Hb].
  replace (U (eval rho (ob_base o)) + (U a - U (eval rho (ob_base o)))) with (U a) in Hb by lia.
  rewrite Z_to_bv_bv_unsigned in Hb. unfold rd, ms_read_byte in Hb. intros X. rewrite X, ROM, Himg in Hb. discriminate.
Qed.

Theorem main_zone_present : ltac2:(tb__ "0|e|
S20S14S14S22S34A1M0S3bS33S1Q40M1A1M2S23S1Q8A1M3A1M4F_;S16S39R6S30S2fR7A1A1S25G0S3cR4S3dR3R2A2A4A4S4S7Z7fff80000000S0G1SeR7P1M5A2A2M6A2S7G6S9Z2Z2fA2M7A2A2S40R8A1S4S7S8S8S0G1SeR9P4A2A2S0G1SeR9P5A2A2A2Z1A2S0G1SeR9P6M8A2A2M9A2S7S8G9Z10MaA2G7A2A2G2S5S31RbS13S30S2fRcA1A1A1R1A3A1S3G4S12RbR2A2S12RcR2A2MbA3F_;Fa;G2S31RcS13S30S2fRdA1A1A1R1A3S3G4GbS3aRaR2A2A3F_;Fa;G2S3fRdR1A2S3G4S12ReR2A2R9R2A1A3F_;Fa;S27S4S7S0G1SeReG5A2A2R1A2SaR1S32S8S0G1SeReG8A2A2GaA2A1A2A2S5S3G4RaS2G1R2A2McA1S24G3A1MdA3A1F_;Fz;S27S4S7SbS0G1SeRfG5A2A2Z100000A2R1A2SaR1S32S8S0G1SeRfG8A2A2GaA2A1A2A2S5S3G4S12RfGcA2GdA3A1F_;Fz;F_;F_;F_;F_;F_;F_;F_;F_;Fm0;Fmd;Fms;Ftr;FrhoM;Frho1;Fv;").
Proof.
  intros v rho1 rhoM tr ms md m0 Hsm HX1 HAL H6 RMo RMi HRM HM0 z Hz.
  assert (PT : page_round_up_Z (U (rw rho1 6%positive) + 16) <= 2 ^ 47).
  { unfold page_round_up_Z, page_size. set (q := U (rw rho1 6%positive) + 16) in *.
    assert (Q : (q + 4096 - 1) / 4096 <= (2 ^ 47 + 4096 - 1) / 4096) by (apply Z.div_le_mono; lia).
    change ((2 ^ 47 + 4096 - 1) / 4096) with (2 ^ 35) in Q. change (2 ^ 47) with (2 ^ 35 * 4096). nia. }
  assert (EZ : U (Z_to_bv 64 z) = z) by (apply Z_to_bv_small; change (bv_modulus 64) with (2 ^ 64); lia).
  destruct (in_ranges_dec rho1 (ss_objs (ax_S (MAIN_of v))) (Z_to_bv 64 z)) as [Hin|Hout].
  - rewrite (RMi _ Hin). apply (smatch_inranges_presentS rho1 _ tr ms md _ Hsm Hin). apply image_byte_none_A. rewrite EZ. lia.
  - destruct (main_cover rho1 HX1 HAL H6 v (Z_to_bv 64 z) ltac:(rewrite EZ; exact Hz)) as [Hin|Harg]; [exfalso; exact (Hout Hin)|].
    rewrite (RMo _ Hout), (HRM _ Harg). apply HM0. destruct Harg as [Hlo _]. rewrite EZ in Hlo. lia.
Qed.

Lemma pageup_mono : ltac2:(tb__ "0|0|
S27S27S7R2R1A2S7S32R3A1S32R2A1A2F_;Fy;Fx;").
Proof. intros x y H. unfold page_round_up_Z, page_size. assert (Q : (x + 4096 - 1) / 4096 <= (y + 4096 - 1) / 4096) by (apply Z.div_le_mono; lia). nia. Qed.
Lemma PRES_of_present : ltac2:(tb__ "0|3|
S1Q40M0A1S23S1Q8A1M1A1M2F_;S27S27S27S4S7R3R1A2SaR1R2A2A2S5S3G2R5S2G0R2A2A1S24G1A1A3A1F_;Fz;S4cS39R4R3R2A4F_;Fhi;Flo;Fm;").
Proof.
  intros m lo hi H z Hz. specialize (H z Hz). unfold wok_of, rd_of. destruct (m (Z_to_bv 64 z)) as [b|]; [|congruence]. split; [reflexivity | exists b; reflexivity].
Qed.

Section AtMain.
Variables (sp brk mb : word) (draw : EntryDraw) (inp : ProcInput).
Hypothesis Hent : ltac2:(tb__ "0|0|
S42S47S3eVsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.

Theorem main_STKP : ltac2:(tb__ "0|8|
S20S14S14S22S34A1M0S3bS33S16S39R5S30S2fR6A1A1S25G0S3cR3S3dR2R1A2A4A4S3S1Q40M1A1M2SeR6P1A2Vsp;A3S3G2SeR7P6M3A2S2G1S8S0G1Vsp;A2M4S48Vinp;A1A2A2A3S40R8A1S4S7S8S8S0G1SeR9P4A2A2S0G1SeR9P5A2A2A2Z1A2S0G1SeR9G3A2A2M5A2S7S8G5Z10A2S9Z2Z2fA2A2A2G2S5S31RbS13S30S2fRcA1A1A1R1A3A1S3S23S1Q8A1A1M6S12RbR2A2S12RcR2A2M7A3F_;Fa;G2S31RcS13S30S2fRdA1A1A1R1A3S3G6G7S3aRaR2A2A3F_;Fa;G2S3fRdR1A2S3G6S12ReR2A2S3aS49Vsp;Vdraw;Vinp;A3R2A2A3F_;Fa;S3S27S0G1SeRcP1eA2A2SbG4Z800000A2A3S4bS39RdA2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;FrhoM;Frho1;Fv;").
Proof.
  intros v rho1 rhoM tr ms md Hsm E1 E6 HAL H6 RMo RMi HRM V30.
  pose proof (StartArgBytes.arg_nums sp brk mb draw inp Hent Hinp) as (Nsp & Nfit & N16 & Nargc & Nstr & Nstr8 & NA1 & NA1b & Nrnd & Npad & Nrnd8 & Nlen & Nlenb & _).
  pose proof (Zle_0_nat (tab (in_argv inp))) as T0. pose proof (Zle_0_nat (tab (in_envp inp))) as T1. pose proof (Zle_0_nat (pad_len (in_argv inp) (in_envp inp))) as T2.
  pose proof (Zle_0_nat (length (in_envp inp))) as T3.
  assert (U6 : U (rw rho1 6%positive) = U sp + StartArgBytes.RNDo inp) by (rewrite E6; apply Z_to_bv_small; change (bv_modulus 64) with (2 ^ 64); lia).
  assert (U1 : U (rw rho1 1%positive) = U sp) by (rewrite E1; reflexivity).
  assert (ELEN : U (rw rho1 6%positive) + 16 = U sp + Z.of_nat (img_len (in_argv inp) (in_envp inp))) by (rewrite U6; unfold StartArgBytes.LEN in Nlen; lia).
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAP.STKP, HB. change (U (rw rhoM V_TOP)) with (U (rw rhoM 30%positive)). rewrite V30. split; [lia|].
  apply PRES_of_present. intros z Hz. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAP.STK_LO in Hz.
  apply (main_zone_present v rho1 rhoM tr ms md (ms_mem (StartArgBytes.ms0A sp draw inp)) Hsm ltac:(rewrite U1; lia) HAL H6 RMo RMi HRM).
  - intros z' Hz'. unfold StartArgBytes.ms0A. rewrite ELEN, U1 in Hz'. apply ms0_stack_present; [unfold StartArgBytes.LEN in Nfit; exact Nfit | rewrite stack_max_size_val; lia | lia].
  - rewrite U1. split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 Hz)|]. unfold HBz, STK_SPAN. apply pageup_mono. rewrite U6. lia.
Qed.
End AtMain.
End StartHandoffPres.

(* [comment removed for export] *)
Module StartHandoffLits.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "leb"; "div"; "le"; "eqb"; "lt"; "ltb"; "pow"; "sub"; "modulo"; "mul"; "to_nat"; "@Corelib.Init.Datatypes"; "andb"; "bool"; "true"; "false"; "Some"; "list"; "negb"; "option"; "orb"; "pair"; "prod"; "@Corelib.Init.Logic"; "eq"; "and"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "outside_all"; "rm"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape"; "binfo"; "byte_info"; "BLit"; "zseq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffLits"; "lits_ok"; "PGLIT"; "lit_byte_ok"; "lit_entry_ok"; "lit_hi"; "lit_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "xr_ok"; "ax_S"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "X_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8"; "MAIN_of"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymFrame SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartReshape.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require os.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition lit_lo (off B : Z) : Z := ltac2:(tb__ "0|1|
SbS3S1Voff;S3VB;Z8M0A2A2G0A2G0A2").
Definition lit_hi (off B L : Z) : Z := ltac2:(tb__ "0|1|
S1SbS3S1Voff;S3S9S1VB;VL;A2Z1A2Z8M0A2A2G0A2G0A2G0A2").

Definition lit_byte_ok (off B L z b : Z) : bool := ltac2:(tb__ "0|7|
SdSdS2Z0M0Vb;A2S7Vb;Z100A2A2SeSeL_;M1SdS2S1Voff;S3VB;Z8M2A2A2Vz;A2S7Vz;S1Voff;S3S1VB;VL;A2M3G2A2A2M4A2A2S5Vb;G0A2M5G1SdS5Vz;G4A2S13S5SaG3G2A2M6G0A2A1A2S15G5S5Vb;G6A2A2SfXex2Xex2A2").

Definition lit_entry_ok (objs : list sobj) (pg off B L : Z) : bool := ltac2:(tb__ "0|1|
S2bVoff;VB;A2S0S2aVoff;VB;VL;A3S0SdSdSdSdSdSdSdS5SaVB;Z8A2Z0M0A2S7G0VL;A2A2S2G0VB;A2A2S2S1VB;VL;A2S8Z2Z28A2A2A2S2Vpg;R2A2A2S2R2R1A2A2S2R1S1Vpg;Z1000A2A2A2S32S0S0S22SeLx;S23Vobjs;S1dVpg;A1S9R1Vpg;A2A3S10S10S0S28Voff;VB;VL;R2R1A5Lb;S10X22x4Lz;S25R2ScS9R1R2A2A1A2A3A2Thi;Tlo;").

Fixpoint lits_ok (objs : list sobj) (pg off : Z) (X : list (sv * sv)) : bool :=
  match X with
  | [] => true
  | (SLit B, SLit L) :: r => lit_entry_ok objs pg off B L && lits_ok objs pg off r
  | _ :: _ => false
  end.

Lemma u64_of_lit : ltac2:(tb__ "0|1|
S0S19S4Z0R1A2S6R1S8Z2Z40A2A2A2S18S0S1bQ40M0S1aG0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.
Lemma u8_of_lit : ltac2:(tb__ "0|1|
S0S19S4Z0R1A2S6R1Z100A2A2S18S0S1bQ8M0S1aG0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

Section Sound.
Variable rho : valuation.
Variable objsS : list sobj.
Variable objsM : list sobj.
Variables pg off : Z.
Hypothesis Hpg : ltac2:(tb__ "0|0|
S19S4Z0Vpg;A2S4S1Vpg;Z1000A2S8Z2Z3eA2A2A2").
Hypothesis Hoff : 0 <= off.
Hypothesis Hmem : ltac2:(tb__ "0|2|
S0S0S19S4Z0R2A2S6R2Z1000A2A2S18S22S23VobjsS;S1dVpg;A1R3A3S24R2A1A3S18S14S1cQ8M0A1M1A1S20Vrho;S1aQ40S1Vpg;R4A2A2A2S11G1S1aG0R3A2A2A3F_;F_;Fb;Foffp;").
Hypothesis Hout : ltac2:(tb__ "0|0|
S0S19S4Vpg;R1A2S6R1S1Vpg;Z1000A2A2A2S1fVrho;VobjsM;S1aQ40R2A2A3F_;Fz;").

Lemma lit_entry_sound : ltac2:(tb__ "0|0|
S0S0S18SeS29VobjsS;Vpg;Voff;R2R1A5SfA3S2cVrho;VobjsM;Voff;S16S1eS1eS1dR3A1S1dR2A1A4A4F_;FL;FB;").
Proof.
  intros B L Hok. unfold lit_entry_ok in Hok. cbv zeta in Hok.
  apply andb_prop in Hok as [Hok Hall]. apply andb_prop in Hok as [Hok H6]. apply andb_prop in Hok as [Hok H5]. apply andb_prop in Hok as [Hok H4].
  apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [Hok H2]. apply andb_prop in Hok as [H0 H1].
  apply Z.eqb_eq in H0. apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5. apply Z.leb_le in H6.
  set (lo := lit_lo off B) in *. set (hi := lit_hi off B L) in *.

  assert (BY : forall z, lo <= z < hi -> exists b, rm rho (Z_to_bv 64 z) = Some (Z_to_bv 8 b) /\ lit_byte_ok off B L z b = true).
  { intros z Hz. pose proof (proj1 (forallb_forall _ _) Hall z ltac:(apply In_zseq; rewrite Z2Nat.id by lia; lia)) as X. cbn beta in X.
    destruct (byte_info objsS (SLit pg) (z - pg)) as [| |b|] eqn:E; try discriminate.
    exists b. split; [|exact X]. replace z with (pg + (z - pg)) at 1 by lia. apply (Hmem (z - pg) b); [lia | exact E]. }

  assert (LOHI : forall a, B <= a < B + L -> lo <= off + a / 8 < hi /\ (forall j, 0 <= j < 8 -> lo <= (off + a / 8) / 8 * 8 + j < hi)).
  { intros a Ha. subst lo hi. unfold lit_lo, lit_hi.
    assert (M1 : B / 8 <= a / 8) by (apply Z.div_le_mono; lia). assert (M2 : a / 8 <= (B + L - 1) / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_mod (off + B / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (off + B / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (off + (B + L - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (off + (B + L - 1) / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (off + a / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (off + a / 8) 8 ltac:(lia)).
    assert (D1 : (off + B / 8) / 8 <= (off + a / 8) / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : (off + a / 8) / 8 <= (off + (B + L - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
    split; [lia|]. intros j Hj. lia. }
  unfold xr_ok. cbn [fst snd eval]. rewrite !u64_of_lit by lia.
  split; [exact H0|]. split; [lia|].
  intros a Ha. destruct (LOHI a Ha) as [Z1 Z2].
  split; [lia|]. split; [unfold shadow_addr; apply Hout; lia|]. split.
  - unfold word_ok. intros j Hj. unfold word_byte. split; [apply Hout; pose proof (Z2 j Hj); lia|].
    destruct (BY ((off + a / 8) / 8 * 8 + j) (Z2 j Hj)) as (b & Hb & _). rewrite Hb. discriminate.
  - destruct (BY (off + a / 8) Z1) as (b & Hb & Hk). unfold shadow_addr. exists (Z_to_bv 8 b). split; [exact Hb|].
    unfold lit_byte_ok in Hk. apply andb_prop in Hk as [Hk Hc]. apply andb_prop in Hk as [Hb0 Hb1]. apply Z.leb_le in Hb0. apply Z.ltb_lt in Hb1.
    rewrite u8_of_lit by lia.
    assert (AB : a / 8 <= (B + L) / 8) by (apply Z.div_le_mono; lia).
    destruct ((off + B / 8 <=? off + a / 8) && (off + a / 8 <? off + (B + L) / 8)) eqn:E1.
    + apply Z.eqb_eq in Hc. left. exact Hc.
    + apply andb_false_iff in E1. assert (EQ : a / 8 = (B + L) / 8).
      { destruct E1 as [E1|E1]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E1]; [|lia].
        exfalso. assert (B / 8 <= a / 8) by (apply Z.div_le_mono; lia). lia. }
      assert (NZ : (B + L) mod 8 <> 0).
      { intros Hz0. pose proof (Z.div_mod (B + L) 8 ltac:(lia)) as D. rewrite Hz0, Z.add_0_r in D.
        assert (a / 8 <= (B + L) / 8 - 1); [|lia].
        replace ((B + L) / 8 - 1) with ((B + L - 8) / 8).
        2:{ replace (B + L - 8) with ((B + L) / 8 * 8 + (-1) * 8) by lia. rewrite Z.div_add by lia. lia. }
        apply Z.div_le_mono; lia. }
      replace ((off + a / 8 =? off + (B + L) / 8) && negb ((B + L) mod 8 =? 0)) with true in Hc.
      2:{ symmetry. apply andb_true_intro. split; [apply Z.eqb_eq; lia | apply Bool.negb_true_iff; apply Z.eqb_neq; exact NZ]. }
      apply Bool.orb_prop in Hc as [Hc|Hc]; apply Z.eqb_eq in Hc; [left; exact Hc | right; split; [exact Hc | exact EQ]].
Qed.

Lemma lits_sound : ltac2:(tb__ "0|1|
S12S17S1eS1eA2M0A1S18SeS26VobjsS;Vpg;Voff;R1A4SfA3S2eG0S2cVrho;VobjsM;Voff;A3R2A3F_;FX;").
Proof.
  induction X as [|[e1 e2] r IH]; intros Hok; [constructor|]. cbn [lits_ok] in Hok.
  destruct e1 as [B| | | | | | |]; try discriminate. destruct e2 as [L| | | | | | |]; try discriminate.
  apply andb_prop in Hok as [H1 H2]. constructor; [exact (lit_entry_sound B L H1) | exact (IH H2)].
Qed.
End Sound.

Definition PGLIT : Z := 0x7fffc000.
Lemma lits_ok_main : ltac2:(tb__ "0|0|
SeS18SeS26S21S2dS31R1A1A1A1S27S2fS30A4SfA3Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End StartHandoffLits.

(* [comment removed for export] *)
Module StartHandoffApart.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "SVar"; "SAlu"; "sv"; "cell"; "mkObj"; "obj_range"; "rw"; "valuation"; "DUnknown"; "eval"; "ranges_disjoint"; "ss_objs"; "DList"; "ob_base"; "ob_hi"; "ob_lo"; "odefault"; "sv_eqb"; "holds"; "sprop"; "ss_facts"; "sstate"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "leb"; "pow"; "opp"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "iff"; "or"; "@Corelib.Init.Datatypes"; "nat"; "option"; "list"; "cons"; "pair"; "Some"; "andb"; "bool"; "fst"; "prod"; "snd"; "true"; "false"; "nil"; "orb"; "app"; "length"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@Stdlib.Lists.List"; "nth_error"; "In"; "forallb"; "combine"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "subst_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffApart"; "GMe"; "ZLOW"; "lit_low_b"; "obj_low_b"; "objs_far_except_b"; "obj_far_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS"; "ARGF"; "@Corelib.Lists.ListDef"; "Forall"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape"; "lit_of"; "lit_small"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF"; "ARG_LIM"; "arg_layout"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7"; "kHighMemBeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8"; "G24"; "MAIN_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "eblk_clear_b"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffApart.MainApart"; "skipA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib"; "img_clear_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundV SymSoundL SymSoundM SymFrame SymEntail SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require os.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartReshape StartHandoffLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition lit_low_b (o : sobj) : bool := ltac2:(tb__ "0|3|
S2aS0A1S30Lx;M0S4cS11Vo;A1A1S0G0S4cS13Vo;A1A1S0G0S4cS12Vo;A1A1S0S2fS2fS2fS2fS2fS1dZ0M1R3A2S1dG1R2A2A2S1dR2R1A2A2S1dS1cR3R1A2S4eA2A2S1dR3S1eZ2Z3eA2M2A2A2S1dR1G2A2A2Lhi;S35X2ax2Llo;S35X2ax2Lb;S35X2ax2").

Lemma lit_low_sound : ltac2:(tb__ "0|1|
SbS2S0S24S30S45R2A1S34A3S1aS4eR2A2S25S23S1aS31S0S0S9R5R4A2M0A3R3A2S1bR3S33S0S0G0A3A2A2A1F_;F_;Fa;Fo;Frho;").
Proof.
  intros rho o a Hb Ha. unfold lit_low_b in Hb.
  destruct (lit_of (ob_base o)) as [b|] eqn:Eb; [|discriminate].
  destruct (lit_of (ob_lo o)) as [lo|] eqn:Elo; [|discriminate].
  destruct (lit_of (ob_hi o)) as [hi|] eqn:Ehi; [|discriminate].
  apply lit_of_sound in Eb. apply lit_of_sound in Elo. apply lit_of_sound in Ehi.
  apply andb_prop in Hb as [Hb H5]. apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5.
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, Elo, Ehi. cbn [eval fst snd]. unfold ARG_LIM in *.
  rewrite !soff_lit_small by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Definition obj_far_b (Ge : list (sv * Z)) (o : sobj) : bool := ltac2:(tb__ "0|0|
S37S37S56Vo;A1S45Vo;A1A2S53VGe;Vo;A2A2").

Definition objs_far_except_b (Ge : list (sv * Z)) (skip : list nat) (objs : list sobj) : bool := ltac2:(tb__ "0|1|
S3eS32S29S2A2M0G0S37S40S29S58S31S29S2R1A3A1Vskip;A3S48VGe;S33S29S2R1A3A2A2Lio;S3fS29S2S4bU0S39S2Vobjs;A2A2Vobjs;A4A3").

Lemma disjoint_point : ltac2:(tb__ "0|4|
SbS2S21Q40M0A1SeS9R3R2A2S2dS0S0S20G0R1A2M1S1cG1Z1A2A4A2S25S23S1aS31S0S0S9R4R3A2M2A3S20G0R2A2M3A2S1bG3S33S0S0G2A3A2A2A1F_;Fa;Fo;Frho;").
Proof. intros rho o a HD Hr. unfold ranges_disjoint in HD. cbn [fst snd] in HD. lia. Qed.

Lemma objs_far_except_sound : ltac2:(tb__ "0|6|
SbS2bS32S6S0A2M0A1S2bS29A1S2bS2A1S21Q40M1A1S24S30S47R4R3R2A3S34A3S1aS4eS20G1R2A2A2S6S0S3dG0S2dS6S0R2R1A4R8A3S25S23S1aS20G1SdRaR3A2A2M2S20G1R6A2M3A2S1bG3S1cG2R2A2A2A2A1F_;Fsz;Fe;S29S2S3dS29R2R8A3S24S2aS2A1S3cS2R8R3A3S2eS2R2A2A3S25S23S1aS31S0S0S9RcR3A2M4A3S20G1R8A2M5A2S1bG5S33S0S0G4A3A2A2A1F_;F_;Fo;Fi;S25S41R9R6R5A3A1F_;F_;F_;F_;Fa;Fobjs;Fskip;FGe;Frho;").
Proof.
  intros rho Ge skip objs a Hb Ha HG Hskip (o & Ho & Hr).
  destruct (combine_seq_In objs 0 o Ho) as [i Hi].
  pose proof (proj1 (forallb_forall _ _) Hb _ Hi) as X. cbn [fst snd] in X.
  apply Bool.orb_prop in X as [X|X].
  - apply existsb_exists in X as (j & Hj & Hij). apply Nat.eqb_eq in Hij. subst j.
    destruct (combine_seq_nth objs 0 i o Hi) as [Hn _]. rewrite Nat.sub_0_r in Hn. exact (Hskip i o Hj Hn Hr).
  - unfold obj_far_b in X. apply Bool.orb_prop in X as [X|X]; [apply Bool.orb_prop in X as [X|X]|].
    + apply (disjoint_point rho o a); [|exact Hr]. apply (img_clear_sound rho a 1); [|exact X]. intros x Hx. unfold ARG_LIM in Ha. lia.
    + exact (lit_low_sound rho o (bv_unsigned a) X Ha Hr).
    + apply (disjoint_point rho o a); [|exact Hr]. apply (eblk_clear_sound rho Ge a 1 o); [|exact X].
      intros e sz Hin x Hx. replace x with (bv_unsigned a) by lia. exact (HG e sz Hin).
Qed.

Definition obj_low_b (K : Z) (o : sobj) : bool := ltac2:(tb__ "0|3|
S2aS0A1S30Lx;M0S4dS13Vo;A1A1S0G0S4dS12Vo;A1A1S0S2fS1dR2R1A2S37S2fS15S11Vo;A1M1S4P1A1A2S1dR1VK;A2A2S2fS2fS15G1S3Z0M2A1A2S1dG2R2A2A2S1dR1Z643000A2A2A2A2Lh;S35X2ax2Ll;S35X2ax2").

Lemma obj_low_sound : ltac2:(tb__ "0|0|
SbS0S2S0S0S24S30S46R4R3A2S34A3S1aS1cS20Q40SaR6P1A2A2R5A2R3A2S1aZ643000R4A2SeS9R8R6A2S2dS0S0R5R4A4A2F_;F_;F_;Fhi;Flo;Fo;FK;Frho;").
Proof.
  intros rho K o lo hi Hb HK Himg. unfold obj_low_b in Hb.
  destruct (lit_small (ob_lo o)) as [l|] eqn:El; [|discriminate]. destruct (lit_small (ob_hi o)) as [h|] eqn:Eh; [|discriminate].
  apply andb_prop in Hb as [Hlh Hb]. apply Z.leb_le in Hlh.
  unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [fst snd]. rewrite (soff_small rho _ _ El), (soff_small rho _ _ Eh).
  apply Bool.orb_prop in Hb as [Hb|Hb].
  - apply andb_prop in Hb as [E Hh]. apply sv_eqb_sound in E. apply Z.leb_le in Hh. rewrite E. cbn [eval]. lia.
  - apply andb_prop in Hb as [Hb Hh]. apply andb_prop in Hb as [E Hl]. apply sv_eqb_sound in E. apply Z.leb_le in Hh. apply Z.leb_le in Hl.
    rewrite E. cbn [eval]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. lia.
Qed.

Lemma objs_low_sound : ltac2:(tb__ "0|0|
SbS0S2bS2A1S0S0S24S30S3eS2S46R4A1R3A3S34A3S1aS1cS20Q40SaR6P1A2A2R5A2R3A2S1aZ643000R4A2S4aS2S2SeS9R9R1A2S2dS0S0R6R5A4A2Lo;R6A3F_;F_;F_;Fhi;Flo;Fobjs;FK;Frho;").
Proof.
  intros rho K objs lo hi Hb HK Himg. apply Forall_forall. intros o Hin.
  exact (obj_low_sound rho K o lo hi (proj1 (forallb_forall _ _) Hb o Hin) HK Himg).
Qed.

Lemma in_ranges_subst_const : ltac2:(tb__ "0|4|
SbS1S0S2bS2A1M0S21Q40M1A1M2S1S19S24G2SaR7R6A2S22G1R5A2A3S24G0SfR2A1R5A3S27S41R9SfS42S2cS32S1S6A2M3S2dS1S6R8S3R7A1A4S36G3A1A3R3R4A3A1R5A3S41R9R6R5A3A2F_;F_;FS;Fnx;Fa;FL;Fz;Fi;Frho;").
Proof.
  intros rho i z L a nx S Hi HL. unfold subst_state. cbn [ss_objs]. rewrite HL.
  assert (E : forall o, obj_range rho (obj_subst [(i, SLit z)] o) = obj_range rho o).
  { intros o. rewrite obj_range_subst. unfold obj_range, obj_lo_of, obj_hi_of, soff.
    assert (EV : forall e, eval (rho_sub rho [(i, SLit z)]) e = eval rho e).
    { intros e. apply (eval_agree_vars (fun _ => true)); [| intros l; reflexivity | apply sv_vars_all_true].
      intros v _. unfold rho_sub. cbn [rw wsub_get]. destruct (Pos.eqb v i) eqn:Ev; [|reflexivity]. apply Pos.eqb_eq in Ev. subst v. cbn [eval]. symmetry. exact Hi. }
    rewrite !EV. reflexivity. }
  unfold in_ranges. split; intros (o & Hin & Hr).
  - apply in_map_iff in Hin as (o0 & <- & Hin0). exists o0. split; [exact Hin0|]. rewrite <- (E o0). exact Hr.
  - exists (obj_subst [(i, SLit z)] o). split; [apply in_map; exact Hin|]. rewrite (E o). exact Hr.
Qed.

Lemma rng_aux : ltac2:(tb__ "0|4|
SbS2bS7A1S21Q40M0A1S4fR3A1S49R4R2A2S8S5S3aS5S3aS5S3aS4P1A1S5S3bS4P2A1S3Z3A1M1A3A3S5S3bS4P3A1G1A3A3S3Z18A1A3S3Z0A1S3Za0A1R4ScA5S2S25S23S1aS31S0S0S9R6R1A2M2A3S20G0R4A2M3A2S1bG3S33S0S0G2A3A2A2A1To;F_;F_;Fa;Fcs;Frho;").
Proof.
  intros rho cs a HAL Ha. pose proof HAL as (A1 & A2 & A3 & A5 & A4). pose proof Ha as [HaLo HaHi]. cbv zeta.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd eval]. rewrite !soff_lit_small by lia.
  pose proof (urange (rw rho 1%positive)) as U1. pose proof (urange (rw rho 2%positive)) as U2. pose proof (urange (rw rho 3%positive)) as U3. pose proof (urange (rw rho 5%positive)) as U5.
  assert (S2 : bv_unsigned (alu64 ALU_SLL (rw rho 2%positive) (Z_to_bv 64 3)) = 8 * bv_unsigned (rw rho 2%positive)) by (apply U_sll3; lia).
  assert (S3 : bv_unsigned (alu64 ALU_SLL (rw rho 3%positive) (Z_to_bv 64 3)) = 8 * bv_unsigned (rw rho 3%positive)) by (apply U_sll3; lia).
  assert (E1 : bv_unsigned (alu64 ALU_ADD (rw rho 1%positive) (alu64 ALU_SLL (rw rho 2%positive) (Z_to_bv 64 3))) = bv_unsigned (rw rho 1%positive) + 8 * bv_unsigned (rw rho 2%positive)).
  { rewrite U_add_words by (rewrite S2; lia). rewrite S2. reflexivity. }
  assert (E2 : bv_unsigned (alu64 ALU_ADD (alu64 ALU_ADD (rw rho 1%positive) (alu64 ALU_SLL (rw rho 2%positive) (Z_to_bv 64 3))) (alu64 ALU_SLL (rw rho 3%positive) (Z_to_bv 64 3)))
               = bv_unsigned (rw rho 1%positive) + 8 * bv_unsigned (rw rho 2%positive) + 8 * bv_unsigned (rw rho 3%positive)).
  { rewrite U_add_words by (rewrite E1, S3; lia). rewrite E1, S3. reflexivity. }
  rewrite U_add_small by (rewrite ?E2; lia). rewrite E2. clear S2 S3 E1 E2. intros [X Y]. destruct HaHi as [H|H]; lia.
Qed.

Lemma rng_stack : ltac2:(tb__ "0|6|
SbS0S0S0S2bS7A1S14S21Q40M0A1S1aZ7fff80000000S20G0SaR7P1M1A2A2A2S23S1aS1fS1eZ2Z28A2M2A1R7A2M3S1aR7Z0A2A2S23G3S1aR7R6A2A2S1aR7G2A2S1aS1cRaR8A2Z10A2S49RcR6A2S8S5S3aS4G1A1S3RcA1A3S3RbA1S3RaA1R9R8A5S2S25S23S1aS31S0S0S9ReR1A2M4A3S20G0R8A2M5A2S1bG5S33S0S0G4A3A2A2A1To;F_;F_;F_;F_;F_;F_;Fa;Fd;Fcs;Fhi;Flo;Fc;Frho;").
Proof.
  intros rho c lo hi cs d a H1 Hc Hlh Hhi Hsum [Ha _]. cbv zeta.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd eval]. rewrite !soff_lit_small by lia.
  pose proof (urange (rw rho 1%positive)) as U1.
  assert (E : bv_unsigned (alu64 ALU_ADD (rw rho 1%positive) (Z_to_bv 64 c)) = bv_unsigned (rw rho 1%positive) + c).
  { unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
  rewrite E. lia.
Qed.
Lemma rng_stack1 : ltac2:(tb__ "0|3|
SbS0S0S2bS7A1S14S21Q40M0A1S23S1aS1fS1eZ2Z28A2A1R5A2S1aR5R4A2A2S1aR5Z10A2S49R8R3A2S8S4P1A1S3R8A1S3R7A1R6R5A5S2S25S23S1aS31S0S0S9RaR1A2M1A3S20G0R5A2M2A2S1bG2S33S0S0G1A3A2A2A1To;F_;F_;F_;Fa;Fd;Fcs;Fhi;Flo;Frho;").
Proof.
  intros rho lo hi cs d a Hlh Hhi [Ha _]. cbv zeta.
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd eval]. rewrite !soff_lit_small by lia. lia.
Qed.

Definition GMe : list (sv * Z) := ltac2:(tb__ "0|2|
S38S32S6S0A2M0S51S2cG0S2dS6S0S3Z7fffc000A1Z1000M1A4S2cG0S2dS6S0S3Z80015000A1G1A4S36G0A1A3A3A3").

Definition ZLOW (y : Z) : Prop := ltac2:(tb__ "0|0|
S28S23S1aZ7fffa000Vy;A2S1bVy;Z7fffc000A2A2S23S1aZ800ba000Vy;A2S1bVy;Z800bc000A2A2A2").

Section MainApart.
Variable v : bool.
Let S := ax_S (MAIN_of v).
Let L : ltac2:(tb__ "0|0|
S2bS2A1") := ltac2:(tb__ "0|0|
SfS57S52Vv;A1A1A1").
Variable rho : valuation.
Hypothesis HF : ltac2:(tb__ "0|0|
S4aS17S16Vrho;A1S18VS;A1A3").

Hypothesis H1 : ltac2:(tb__ "0|1|
S23S1aZ7fff80000000S20Q40SaVrho;P1A2A2M0A2S1aG0S1eZ2Z2fA2A2A2").
Hypothesis HAL : arg_layout rho.
Hypothesis H6 : ltac2:(tb__ "0|2|
S23S1aS1cS1cS20Q40M0SaVrho;P4A2A2S20G0SaVrho;P5A2A2A2Z1A2S20G0SaVrho;P6A2A2M1A2S1aS1cG1Z10A2S1eZ2Z2fA2A2A2").

Variable qlo : Z.
Hypothesis Hqlo : 0x800bd000 <= qlo <= kHighMemBeg.
Hypothesis HGlow : ltac2:(tb__ "0|1|
S6S0S3dS32S6S0A2S2dS6S0R2R1A4S43A3S0S44R1A1S25S23S1aS20Q40SdVrho;R5A2A2M0R2A2S1bR2S1cG0R4A2A2A2A1F_;Fy;F_;Fsz;Fe;").
Hypothesis HGhigh : ltac2:(tb__ "0|1|
S6S0S3dS32S6S0A2S2dS6S0R2R1A4S43A3S0S23S1aVqlo;R1A2S1bR1S50A2A2S25S23S1aS20Q40SdVrho;R5A2A2M0R2A2S1bR2S1cG0R4A2A2A2A1F_;Fy;F_;Fsz;Fe;").
Hypothesis HGargf : ltac2:(tb__ "0|2|
S6S0S3dS32S6S0A2S2dS6S0R2R1A4S43A3S0S23S1aS20Q40M0SaVrho;P1A2A2R1A2S1bR1S1eZ2Z2fA2A2A2S25S23S1aS20G0SdVrho;R5A2A2M1R2A2S1bR2S1cG1R4A2A2A2A1F_;Fy;F_;Fsz;Fe;").

Lemma clearM : ltac2:(tb__ "0|0|
S24S30S54S43VS;A2S34A3").
Proof. clear. subst S. destruct v; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma main_disjoint_low : ltac2:(tb__ "0|3|
S21Q40M0A1S0S1aZ0R1A2S0S23S1aS20G0R4A2M1R1A2S1bR1S1cG1R3A2A2A2S44R2A1F_;Fy;S4aS2S2SeS9Vrho;R1A2S2dS0S0S20G0R5A2M2S1cG2R4A2A4A2Lo;VL;A3F_;F_;Fn;Fa;").
Proof.
  intros a n Hn HZ. apply Forall_forall. intros o Hin.
  destruct (Z.eq_dec n 0) as [->|NZ]. { unfold ranges_disjoint. cbn [fst snd]. lia. }
  apply (objs_clear_e_sound rho GMe S a n HF clearM Hn); [| | | exact Hin].
  - left. pose proof (HZ (bv_unsigned a + n - 1) ltac:(lia)) as Y. unfold ZLOW in Y. lia.
  - intros x Hx. pose proof (HZ x Hx) as X. unfold ZLOW in X. lia.
  - intros e sz He x Hx. exact (HGlow e sz He x (HZ x Hx)).
Qed.

Lemma main_apart_low : ltac2:(tb__ "0|1|
S21Q40M0A1S44S20G0R1A2A1S25S41Vrho;VL;R2A3A1F_;Fa;").
Proof.
  intros a Ha (o & Hin & Hr). apply (disjoint_point rho o a); [|exact Hr].
  apply (proj1 (Forall_forall _ _) (main_disjoint_low a 1 ltac:(lia) ltac:(intros y Hy; replace y with (bv_unsigned a) by lia; exact Ha)) o Hin).
Qed.

Lemma main_apart_band : ltac2:(tb__ "0|2|
S21Q40M0A1S23S1aVqlo;S20G0R1A2M1A2S1bG1S50A2A2S25S41Vrho;VL;R2A3A1F_;Fa;").
Proof.
  intros a Ha (o & Hin & Hr). apply (disjoint_point rho o a); [|exact Hr].
  apply (objs_clear_e_sound rho GMe S a 1 HF clearM ltac:(lia)); [| | | exact Hin].
  - left. unfold kHighMemBeg in Ha. lia.
  - intros x Hx. lia.
  - intros e sz He x Hx. replace x with (bv_unsigned a) by lia. exact (HGhigh e sz He _ Ha).
Qed.

Definition skipA : list nat := ltac2:(tb__ "0|0|
S2cS29U0S2cS29U10S2cS29U11S2cS29U12S2cS29U13S2cS29U14S2cS29U3aS2cS29U3bS36S29A1A3A3A3A3A3A3A3A3").
Lemma apart_argf_b : ltac2:(tb__ "0|0|
S24S30S47S43S55VL;A3S34A3").
Proof. clear. subst L. destruct v; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma nth0 : ltac2:(tb__ "0|1|
S26S2bS7A1M0G0S24S2aS2A1S3cS2VL;U0A3S2eS2S8S5S3aS4P1A1S3N70A1A3S3N1150A1S3Z0A1R1ScA5A2A3Lcs;A2").
Proof. clear. subst L. destruct v; vm_compute; eexists; reflexivity. Qed.
Lemma nth16 : ltac2:(tb__ "0|1|
S26S2bS7A1M0G0S24S2aS2A1S3cS2VL;U10A3S2eS2S8S4P1A1S3Z0A1S3Z10A1R1ScA5A2A3Lcs;A2").
Proof. clear. subst L. destruct v; vm_compute; eexists; reflexivity. Qed.
Lemma nth17 : ltac2:(tb__ "0|2|
S24S2aS2A1S3cS2VL;U11A3S2eS2S8S5S3aS5S3aS4P1M0A1S5S3bS4P2A1S3Z3A1M1A3A3S3Z10A1A3S3Z0A1S5S3aS5S3bS4P3A1G1A3S3Z8A1A3S36S7A1S10G0A1A5A2A3").
Proof. clear. subst L. destruct v; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth18 : ltac2:(tb__ "0|2|
S26S2bS7A1M0G0S24S2aS2A1S3cS2VL;U12A3S2eS2S8S5S3aS5S3aS5S3aS4P1A1S5S3bS4P2A1S3Z3A1M1A3A3S5S3bS4P3A1G1A3A3S3Z18A1A3S3Z0A1S3Za0A1R1ScA5A2A3Lcs;A2").
Proof. clear. subst L. destruct v; vm_compute; eexists; reflexivity. Qed.
Lemma nth19 : ltac2:(tb__ "0|0|
S24S2aS2A1S3cS2VL;U13A3S2eS2S8S4P4A1S3Z0A1S5S3aS4P5A1S3Z1A1A3S36S7A1S10P2A1A5A2A3").
Proof. clear. subst L. destruct v; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth20 : ltac2:(tb__ "0|1|
S26S2bS7A1M0G0S24S2aS2A1S3cS2VL;U14A3S2eS2S8S4P6A1S3Z0A1S3Z10A1R1ScA5A2A3Lcs;A2").
Proof. clear. subst L. destruct v; vm_compute; eexists; reflexivity. Qed.
Lemma nth58 : ltac2:(tb__ "0|1|
S26S2bS7A1M0G0S24S2aS2A1S3cS2VL;U3aA3S2eS2S8S4P1A1S3S1fS1eZ2Z14A2A1A1S3N11c0A1R1ScA5A2A3Lcs;A2").
Proof. clear. subst L. destruct v; vm_compute; eexists; reflexivity. Qed.
Lemma nth59 : ltac2:(tb__ "0|1|
S26S2bS7A1M0G0S24S2aS2A1S3cS2VL;U3bA3S2eS2S8S4P1A1S3N70A1S3Z0A1R1ScA5A2A3Lcs;A2").
Proof. clear. subst L. destruct v; vm_compute; eexists; reflexivity. Qed.

Lemma main_apart_argf : ltac2:(tb__ "0|0|
S21Q40A1S49Vrho;R1A2S25S41Vrho;VL;R2A3A1F_;Fa;").
Proof.
  intros a Ha. pose proof HAL as (A1 & A2 & A3 & A5 & A4). pose proof Ha as [HaLo HaHi]. pose proof (urange a) as Ua.
  assert (HX1 : ARG_LIM <= bv_unsigned a) by (unfold ARG_LIM; lia).
  apply (objs_far_except_sound rho GMe skipA L a apart_argf_b HX1).
  { intros e sz He. apply (HGargf e sz He). pose proof (urange (rw rho 2%positive)). pose proof (urange (rw rho 3%positive)). pose proof (urange (rw rho 5%positive)). destruct H6 as [H6a H6b]. pose proof (pageup_le_47 _ H6b) as HPT. destruct HaHi; lia. }
  intros i o Hi Hn. unfold skipA in Hi. destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  - destruct nth0 as [cs E]. rewrite E in Hn. injection Hn as <-. apply (rng_stack rho (-112) (-4432) 0 cs DUnknown a); try lia. exact Ha.
  - destruct nth16 as [cs E]. rewrite E in Hn. injection Hn as <-. apply (rng_stack1 rho 0 16 cs DUnknown a); try lia. exact Ha.
  - rewrite nth17 in Hn. injection Hn as <-. exact (argf_not_env rho _ _ a HAL Ha).
  - destruct nth18 as [cs E]. rewrite E in Hn. injection Hn as <-. exact (rng_aux rho cs a HAL Ha).
  - rewrite nth19 in Hn. injection Hn as <-. exact (argf_not_str0 rho _ _ a HAL Ha).
  - destruct nth20 as [cs E]. rewrite E in Hn. injection Hn as <-. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd eval]. rewrite !soff_lit_small by lia.
    pose proof (urange (rw rho 3%positive)). pose proof (urange (rw rho 5%positive)). destruct H6 as [H6a H6b]. lia.
  - destruct nth58 as [cs E]. rewrite E in Hn. injection Hn as <-. apply (rng_stack1 rho (- 2 ^ 20) (-4544) cs DUnknown a); try lia. exact Ha.
  - destruct nth59 as [cs E]. rewrite E in Hn. injection Hn as <-. apply (rng_stack1 rho (-112) 0 cs DUnknown a); try lia. exact Ha.
Qed.
End MainApart.
End StartHandoffApart.

(* [comment removed for export] *)
Module StartHandoffStates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "bool"; "true"; "app"; "option"; "prod"; "None"; "negb"; "Some"; "false"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "SVar"; "SAlu"; "sstate"; "cell"; "mkObj"; "DUnknown"; "swf"; "mkSS"; "sprop"; "ss_objs"; "DList"; "FcsrFrm0"; "mkCell"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Init.Logic"; "eq"; "and"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHandoffLib"; "state_vl_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8"; "MAIN_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffStates"; "sM"; "vA1L"; "KN"; "LM2"; "LM3"; "LU2"; "LU3"; "T0a"; "T0b"; "T0c"; "TM"; "TU"; "add_objs"; "s2"; "sJ"; "vALL"; "vL2L"; "vL3L"; "LM1"; "LM2_raw"; "LM2o"; "LU1"; "LU2_raw"; "LU2o"; "O_a1pL"; "O_arg0L"; "O_arg1L"; "S_M0"; "S_U0"; "sFM"; "sFU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape"; "reshape_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceM"; "objs_M"; "objs_U"; "O_hdrU"; "regs_M"; "regs_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "O_stage2"; "fregs_T"; "O_hdr2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "main_entry"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "obj_subst"; "subst_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymFrame SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ne.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ob.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require os.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceM DrvIfaceT DrvIfaceR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartReshape StartHandoffLib.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import TAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition s2 : wsub := ltac2:(tb__ "0|1|
S0S7ScSdA2M0S1ScSdP2SeZ2A1A4S2G0A1A3").

Definition vA1L : sv := ltac2:(tb__ "0|0|
S11S26S11S26S10P4A1S10P5A1A3SeZ1A1A3").
Definition vENDL : sv := SAlu ALU_ADD (SVar 6) (SLit 16).
Definition vL3L : sv := SAlu ALU_SUB vENDL vA1L.
Definition vL2L : sv := SAlu ALU_SUB vENDL (SVar 4).
Definition vALL : sv := SAlu ALU_SUB vENDL (SVar 1).

Definition KN : positive := 193%positive.
Definition sM : wsub := ltac2:(tb__ "0|3|
S0S7ScSdA2M0S1ScSdP10S10P18M1A1A4S0G0S1ScSdPfS11S27S10P9A1SeZffffffffffff00ffA1A3A4S0G0S1ScSdG1SeS57A1A4S0G0S1ScSdP1eS11S26S10P1A1SeN800000A1A3A4S0G0S1ScSdP2fS11S26S10P1bA1M2SeZ53b0A1A3A4S0G0S1ScSdP30S11S26G2SeZ4dc0A1A3A4S2G0A1A3A3A3A3A3A3").
Definition sJ : wsub := ltac2:(tb__ "0|5|
S0S7ScSdA2M0S1ScSdP91M1SeZ4000000000000000A1A4S0G0S1ScSdP92M2SeZ0A1M3A4S0G0S1ScSdP93M4SeZ1000000000000000A1A4S0G0S1ScSdP99SeZ6000000000000000A1A4S0G0S1ScSdP9aSeZafffff00000fffffA1A4S0G0S1ScSdP9bSeZefffffffffffffffA1A4S0G0S1ScSdP9cSeZfffff0000000000A1A4S0G0S1ScSdP9dSeZffffff0000000000A1A4S0G0S1ScSdPa8G3A4S0G0S1ScSdPa9S10G1A1A4S0G0S1ScSdPaaS10G2A1A4S0G0S1ScSdPabS10G4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition sFM : wsub := ltac2:(tb__ "0|1|
S5S7ScSdA2M0S2aS5G0S0G0S1ScSdP8S2bA4S0G0S1ScSdP9S10S2cA1A4S0G0S1ScSdPaS3bA4S0G0S1ScSdPbS39A4S0G0S1ScSdP98S11S26S10P1A1SeZ20A1A3A4S2G0A1A3A3A3A3A3S38A3A3").
Definition sFU : wsub := ltac2:(tb__ "0|1|
S5S7ScSdA2M0S2aS5G0S0G0S1ScSdPcS3aA4S0G0S1ScSdPbS39A4S2G0A1A3A3S38A3A3").

Definition T0a : sobj := ltac2:(tb__ "0|0|
S14S10P1A1SeN10000A1SeN11c0A1S2S13A1S15A5").
Definition T0b : sobj := ltac2:(tb__ "0|0|
S14S11S26S10P1A1SeN70A1A3SeN1150A1SeZ0A1S2S13A1S15A5").
Definition T0c : sobj := ltac2:(tb__ "0|0|
S14S10P1A1SeN70A1SeN30A1S2S13A1S15A5").
Definition TM : list sobj := ltac2:(tb__ "0|0|
S5SfS0SfS31S0SfS32S0SfS33S2SfA1A3A3A3S4bSfSfS5aS2aA1S0SfS53S0SfS55S4cSfU5S4eA3A3A3A4A3").
Definition TU : list sobj := ltac2:(tb__ "0|0|
S5SfS0SfS31S0SfS32S0SfS33S2SfA1A3A3A3S4bSfSfS5aS2aA1S0SfS53S0SfS50S4cSfU4S4fA3A3A3A4A3").

Definition O_a1pL : sobj := ltac2:(tb__ "0|1|
S14S10P1A1SeZ10A1M0SeZ18A1S0S13S1cG0Z8S2bA3S2S13A1A3S15A5").
Definition O_arg1L : sobj := ltac2:(tb__ "0|0|
S14S2bSeZ0A1S3bS2S13A1S1aP3A1A5").
Definition O_arg0L : sobj := ltac2:(tb__ "0|0|
S14S10P4A1SeZ0A1S3aS2S13A1S1aP2A1A5").

Definition S_M0 : sstate := ltac2:(tb__ "0|0|
S17S56S51S54S1bS8SdA1S4eS2S18A1PbeSbA9").
Definition S_U0 : sstate := ltac2:(tb__ "0|0|
S17S56S52S54S1bS8SdA1S4fS2S18A1PbeSbA9").

Definition shape_deep (S : sstate) : option sstate := ltac2:(tb__ "0|4|
S6S12A1M0G0Lx;M1S5eVS;U1A2S12G1S5dR1U0A2M2S12G2LS2;S8S12A1M3X6x2LS1;G3X6x2").
Definition add_objs (S : sstate) (os : list sobj) : sstate := ltac2:(tb__ "0|0|
S17S21VS;A1S22VS;A1S1eVS;A1S1dVS;A1S23VS;A1S5SfS19VS;A1Vos;A3S2S18A1S20VS;A1S1fVS;A1A9").

Definition LM1 (v : bool) : sstate := ltac2:(tb__ "0|0|
S5cS5bS37S49S29Vv;A1A1Pc2A3S34A2").
Definition LU1 (v : bool) : sstate := ltac2:(tb__ "0|0|
S5cS49S29Vv;A1A1S35A2").
Definition LM2o (v : bool) : option sstate := shape_deep (LM1 v).
Definition LU2o (v : bool) : option sstate := shape_deep (LU1 v).
Definition LM2A_raw : sstate := Eval vm_compute in (match LM2o true with Some Sx => Sx | None => S_M0 end).
Definition LM2B_raw : sstate := Eval vm_compute in (match LM2o false with Some Sx => Sx | None => S_M0 end).
Definition LU2A_raw : sstate := Eval vm_compute in (match LU2o true with Some Sx => Sx | None => S_M0 end).
Definition LU2B_raw : sstate := Eval vm_compute in (match LU2o false with Some Sx => Sx | None => S_M0 end).
Definition LM2_raw (v : bool) : sstate := if v then LM2A_raw else LM2B_raw.
Definition LU2_raw (v : bool) : sstate := if v then LU2A_raw else LU2B_raw.
Definition LM2 (v : bool) : sstate := no_facts (LM2_raw v).
Definition LU2 (v : bool) : sstate := no_facts (LU2_raw v).
Definition LM3 (v : bool) : sstate := ltac2:(tb__ "0|0|
S36S2dVv;A1S0SfS42S0SfS44S2SfA1A3A3A2").
Definition LU3 (v : bool) : sstate := ltac2:(tb__ "0|0|
S36S2fVv;A1S0SfS43S2SfA1A3A2").

Lemma reshape_M : ltac2:(tb__ "0|0|
S3S25S24S3S4dS58S19S5bS37S49S29R1A1A1Pc2A3A1S34A3S4A3S25S24S3S16S3cR1A1A1S4A3S24S6S12A1S3eR1A1SaS12S3dR1A1A2A3A2A2Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma reshape_U : ltac2:(tb__ "0|0|
S3S25S24S3S4dS58S19S49S29R1A1A1A1S35A3S4A3S25S24S3S16S3fR1A1A1S4A3S24S6S12A1S41R1A1SaS12S40R1A1A2A3A2A2Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma entails_M : ltac2:(tb__ "0|1|
S3S25S24S3S16S2eR1A1M0A1S4A3S25S24S3S59G0S45S47A3S4A3S24S3S28ScS4L_;ScS9S4aR1P3A2A1Ll';S2dR1A1A3S4A3A2A2Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma entails_U : ltac2:(tb__ "0|1|
S3S25S24S3S16S30R1A1M0A1S4A3S25S24S3S59G0S46S48A3S4A3S24S3S28ScS4L_;ScS9S4aR1P2A2A1Ll';S2fR1A1A3S4A3A2A2Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma LM3_noKN : ltac2:(tb__ "0|2|
S3S25S24S3S28ScS9S4aR1S2cA2A1Li;M0ScS4L_;M1S2eR1A1A3S4A3S24S3S28G0G1S30R1A1A3S4A3A2Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End StartHandoffStates.

