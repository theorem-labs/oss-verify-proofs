(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "app"; "nil"; "pair"; "nat"; "prod"; "list"; "negb"; "option"; "bool"; "fst"; "orb"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SLit"; "SPUle"; "sobj"; "SAlu"; "cell"; "DUnknown"; "SPBranch"; "SPNot"; "SPUlt"; "mkCell"; "ss_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8"; "pL"; "lDmm"; "lDsg"; "lKmm"; "lKsg"; "cFV"; "lDfv"; "cMI"; "cMM"; "cSG"; "lKfv"; "XL"; "FCUT3"; "F_L14"; "datasL"; "lDmi"; "regsLs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9"; "pKm4"; "pDm4"; "pKf4"; "pDf4"; "XnoLoc"; "E_fv4"; "E_mi4"; "F1"; "F2"; "JFV4"; "JMI4"; "LB"; "LFX"; "XL1"; "XL2"; "cMI3"; "cutpcs_hf9"; "fv2c"; "mi4F"; "regsL4"; "sh28o"; "sh38o"; "ubL"; "E_fv4_0"; "E_mi4_1"; "R_fv4"; "R_mi4"; "a0_of"; "fv4F"; "hf_T36"; "reopen28n"; "s_fv4"; "s_mi4"; "vr_ret_fv4"; "vr_ret_mi4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "hG"; "vec_facts"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "BC_EQ"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xlocal"; "shadow_reopen_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7"; "pNT"; "qDrp'"; "qDts'"; "qKrp'"; "qKts'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "leafA"; "axst"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "apply_axforms"; "AXMerge"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pA"; "vec_facts0"; "FUEL_hf"; "V496"; "V528"; "V560"; "V592"; "optAp"; "BAD"; "V752e"; "V784"; "V816"; "am2"; "fv_c"; "mi_c"; "mm_c"; "pKco"; "sg_c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "pKtr"; "pDtr"; "hint12"; "trK"; "tr_facts"; "triF"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "XkeepF"; "xf_backV"; "NFV"; "NMI"; "coP"; "co_live"; "pX"; "sel_backV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.VRAddr"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "vDp"; "B32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "xr_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Stdlib.Lists.List"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "SHB"; "leavesA_at"; "segs"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6"; "cutpcs_hf6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "pow"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition pDm4 : sv := SVar 370. Definition pKm4 : sv := SVar 371. Definition pDf4 : sv := SVar 372. Definition pKf4 : sv := SVar 373.
Definition pDn4 : sv := SVar 374. Definition pKn4 : sv := SVar 375. Definition pDs4 : sv := SVar 376. Definition pKs4 : sv := SVar 377.

Definition LFX (t dmi cmi kmi : sv) (ami : positive) (dfv cfv kfv : sv) (afv : positive) (dmm cmm kmm : sv) (amm : positive) (dsg csg ksg : sv) (asg : positive) : list sprop := ltac2:(tb__ "0|2|
S1SdS0SdS17Vt;S5bA2S0SdS10S5bS77A2S0SdS16S15S56S5bSfZ0A1A3A1S0SdS7fVt;A1S0SdS10S51ZcM0S5bA2S51Z4M1S7dA2A2S0SdS10S51G0S6bA2S51G0S7bA2A2S0SdS8aS2SdA1A3A3A3A3A3A3A3S1SdS53Vdmi;Vcmi;Vkmi;G0Vami;A5S1SdS53Vdfv;Vcfv;Vkfv;G1Vafv;A5S1SdS53Vdmm;Vcmm;Vkmm;G1Vamm;A5S1SdS53Vdsg;Vcsg;Vksg;G1Vasg;A5S1SdS81S7eS7dP157A3S1SdS6cS5cS5eG1P160A4S1SdS6cS5dS5fZ1P162A4S82A3A3A3A3A3A3A3A3").

Definition regsL4 (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S1S5S4SeA2M0S94G0G0S7S9bSaS4SeR1A3U5A2A1Lp;S2aA3S0G0S3S4SeU1Vra;A4S0G0S3S4SeUaVa0;A4S0G0S3S4SeU17S1aA4S2G0A1A3A3A3A3").
Definition sh38c : sobj := ltac2:(tb__ "0|1|
S5aS52Z26M0Z27S0S13S18SfS9cS95G0A2A1Z1SfZ4A1A3S2S13A1A3S14A5").
Definition sh28o : sobj := shobj hG 28 33 [] DUnknown.
Definition sh38o : sobj := shobj hG 38 39 [] DUnknown.
Definition fv2c : list cell := [c4 304 (SLit 3)].

Definition LB (pc : Z) (regs : list (nat * sv)) (mi fv mm sg : sobj) (dmi kmi dfv kfv dmm kmm dsg ksg : sv) (fcells : list cell) (tail : list sobj)
              (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S26Vpc;Vregs;S8bS89S74S5cS5eA2S75S7eSfZ0A1S7dA3Vmi;Vfv;Vmm;Vsg;S76S5dS5fA2S27Vfcells;S28Vdmi;Vkmi;Vdfv;Vkfv;Vdmm;Vkmm;Vdsg;Vksg;S80S5bA1A9Vtail;Vfacts;VX;A11").
Definition a0_of (E : axst) : sv := ltac2:(tb__ "0|0|
S83SeUaS19S60VE;A1A1SfZ0A1A4").
Definition offd_of (E : axst) : sv := ltac2:(tb__ "0|3|
SeSeLx;S49VE;A1S2bSfZ0A1M0Lz;S2cG0Li;S55SeSeS55SeLop;R3R1G0G0G0G0G0G0G0G0G0X55xaLo;La;Lop;S55SeSeG0Lb;La;M1Lop;S57G1Lop;M2G2S9S2dSeG0La;Lw;Lsgn;S2cSeS2bG0Lk;Li;Ll;Xex8").

Definition xf_backL (vi di : nat) (off : Z) : list axform := ltac2:(tb__ "0|0|
S0S65S66U1Z40A2S0S65S69S1S4S8cVvi;Vdi;A2S0S4U25S2S4A1A3A3A1S0S65S68U0A1S0S65S66Vvi;S9dVoff;A1A2S2S65A1A3A3A3A3").

Definition E_mi4_0 : axst := Eval vm_compute in leaf_at T_g3 vr_entry 0.

Goal local_ok (ob_cells (sh_last E_mi4_0)) DUnknown 38 39 (304, 4) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_mi4_1 : axst := Eval vm_compute in shadow_release_stateA E_mi4_0 (objs_butlast E_mi4_0) 160 [(304, 4)].
Definition E_mi4 : axst := Eval vm_compute in ax_add_facts (vr_need 12 (SAlu ALU_ADD (cMI pL) (SLit 3)) (NMI pA)) (optAp (apply_axforms E_mi4_1 (xf_vr 15 496))).
Definition s_mi4 : wsub := ltac2:(tb__ "0|1|
S0S5S2cSeA2M0S3S2cSeP3bS88S6bA1A4S0G0S3S2cSeP13S12S54S8eSfZ40A1A3A4S90PaS60S34A1S60S6aA1A3A3A3").
Definition R_mi4 : list sobj := Eval vm_compute in optR (entails_frA E_mi4 VN.Pre_vr s_mi4).
Goal entails_frA E_mi4 VN.Pre_vr s_mi4 = Some R_mi4 /\ call_checkPA E_mi4 VN.Pre_vr s_mi4 R_mi4 (map fst PD_vn) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition vr_ret_mi4 : Z := 0x9de1c.
Definition XL1 : list (sv * sv) := ltac2:(tb__ "0|0|
S25S2fS20S1bS1cS2eS24S1dS1eA8").
Definition F1 : list sprop := ltac2:(tb__ "0|0|
S3aS1aS2fS21S1aA1S2eP172S20S1fS1aA1S24P16aS1bS22S1aA1S1dP16cS1cS23S1aA1S1eP16eA11").
Definition mi4F : list sprop := ltac2:(tb__ "0|2|
S0SdS10S12S54S21S1aA1M0SfZ3A1A3S2eA2S0SdS10SfS93A1S2fA2S0SdS10S12S54S51ZcM1G0A2SfZ24A1A3S51G1S2eA2A2S2SdA1A3A3A3").
Definition JMI4 (a0 : sv) (tail : list sobj) (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S39S8dS41SfS50A1Va0;A2S6eS2fS21S1aA1S2eA3S6fS20S1fS1aA1S24A3S70S1bS22S1aA1S1dA3S71S1cS23S1aA1S1eA3S2fS2eS20S24S1bS1dS1cS1eS3fVtail;Vfacts;VX;A12").
Definition ubL : list sprop := ltac2:(tb__ "0|1|
S0SdS10S79SfS8fA1M0A2S0SdS10S78G0A2S0SdS10S7aG0A2S0SdS10S7cG0A2S0SdS10S1aSfS9eZ2Z14A2A1A2S2SdA1A3A3A3A3A3").
Definition JR_mi4 : axst := ltac2:(tb__ "0|2|
S38SfZ1A1S2S11A1S1SdS40S1SdS35S44A3A3S0S5SeSeA2M0S58Pa0M1S3S2bS2bZ130Z4A4A2S0G0S58G1S3S2bS2bZe0Z24A4A2S3bA3A3A4").

Definition JF_mi4 : axst := ltac2:(tb__ "0|0|
S38SfZ0A1S0S11S43S0S11S42S2S11A1A3A3S35S3bA4").
Definition contMI4 (P : axst) : axst := ltac2:(tb__ "0|0|
S72S67S91S6aS34S4eS48VP;S85S29S61S46A1A2A6S86UeU1cZ1f0A3A2A1").
Definition T_mi4k : axst := Eval vm_compute in ax_add_facts [SPUle (SLit IMG_HI) lDmi] (contMI4 VN.P_keep).
Definition T_mi4f : axst := Eval vm_compute in contMI4 VN.P_fail.
Definition T_mi4g : axst := Eval vm_compute in contMI4 VN.P_grown.

Definition XnoLoc (A : axst) : list (sv * sv) := ltac2:(tb__ "0|2|
S94S5SeSeA2M0G0S7SbS92R1S58Pa0M1S3S2bS2bZe0Z24A4A2A2S92R1S58G1S3S2bS2bZ130Z4A4A2A2A2A1Lr;S61VA;A1A3").
Definition reopen28n (A : axst) : axst := ltac2:(tb__ "0|0|
S59VA;S32VA;A1S52Z1cZ21A5").
Definition reopen2n (A : axst) : axst := ltac2:(tb__ "0|0|
S59S4cVA;A1S32VA;A1S52Z26Z27A5").

Definition reopen2f (A : axst) : axst := ltac2:(tb__ "0|1|
S59S59VA;S32VA;A1M0S52Z26Z27A5G0S52Z1cZ21A5").
Goal map (fun L => leaf_matches1A NPH L JR_mi4) [T_mi4k; T_mi4g] = [true; true] /\ leaf_matches1A NPH (reopen2f T_mi4f) JF_mi4 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition hf_T36 : Z := 0x9dea0.
Definition cutpcs_hf9 : list Z := ltac2:(tb__ "0|0|
S1S2bS99S0S2bS4bS2S2bA1A3A3").
Definition lvs9 (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S8S6S62A1M0A1S6S5S2bS9aA2M1A1Lx;S64S97S6dS3eVS;ScA5G0S84S62G1S98R1A4Ll;S2G1A1X8x2").
Definition leaf_at9 (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S83S63Vk;S96S6dS3eVS;Vpc;A4S73A4").
Goal lvs9 JR_mi4 = [(hf_T36, RsCut)] /\ lvs JF_mi4 = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition L_T36 : axst := Eval vm_compute in leaf_at9 JR_mi4 hf_T36 0.
Definition C_T36 : axst := Eval vm_compute in bl_cut L_T36 13 (SLit 36) [10; 11; 16]%nat [].
Goal leaf_matches1A NPH L_T36 C_T36 = true /\ lvs9 C_T36 = [(hf_T36, RsCut); (hf_T36X, RsCut); (hf_T36, RsCut); (hf_T36X, RsCut)]
  /\ map (fun L => leaf_matches1A NPH L C_T36) (leavesA_at FUEL_hf cutpcs_hf9 C_T36 hf_T36) = [true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_c4 : axst := Eval vm_compute in bl_forget (bl_prune HNEXT (bl_junk (leaf_at9 C_T36 hf_T36X 0) [10; 11; 13; 16]%nat)) [1%nat; 28%nat].
Goal map (fun L => leaf_matches1A NPH L T_c4) (leavesA_at FUEL_hf cutpcs_hf9 C_T36 hf_T36X) = [true; true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Goal shape T_c4 = shape JR_mi4 /\ lvs T_c4 = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_fv4_0 : axst := Eval vm_compute in leaf_at T_c4 vr_entry 0.
Definition E_fv4 : axst := Eval vm_compute in ax_add_facts (vr_need 4 (SAlu ALU_ADD (cFV pL) (SLit 1)) (NFV pA)) (optAp (apply_axforms E_fv4_0 (xf_vr 16 528))).
Definition s_fv4 : wsub := ltac2:(tb__ "0|1|
S0S5S2cSeA2M0S3S2cSeP3bS87S6bA1A4S0G0S3S2cSeP13S12S54S8eSfZ40A1A3A4S90PaS60S33A1S60S6aA1A3A3A3").
Definition R_fv4 : list sobj := Eval vm_compute in optR (entails_frA E_fv4 VN.Pre_vr s_fv4).
Goal entails_frA E_fv4 VN.Pre_vr s_fv4 = Some R_fv4 /\ call_checkPA E_fv4 VN.Pre_vr s_fv4 R_fv4 (map fst PD_vn) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition vr_ret_fv4 : Z := 0x9df48.
Definition cMI3 : sv := ltac2:(tb__ "0|0|
S12S54S21S1aA1SfZ3A1A3").
Definition XL2 : list (sv * sv) := ltac2:(tb__ "0|0|
S25S2fS31S1bS1cS2eS30S1dS1eA8").
Definition F2 : list sprop := ltac2:(tb__ "0|1|
S1SdS40S1SdS6cS2fS2eZcP172M0A4S3aS1aS2fS3dS2eG0S31S1fS1aA1S30P174S1bS22S1aA1S1dP16cS1cS23S1aA1S1eP16eA11A3A3").
Definition fv4F : list sprop := ltac2:(tb__ "0|2|
S0SdS10S12S54S1fS1aA1M0SfZ1A1A3S30A2S0SdS10SfS93A1S31A2S0SdS10S12S54S51Z4M1G0A2SfG1A1A3S51G1S30A2A2S2SdA1A3A3A3").
Definition JFV4 (a0 : sv) (tail : list sobj) (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S39S8dS41SfS4fA1Va0;A2S6eS2fS3dS2eA3S6fS31S1fS1aA1S30A3S70S1bS22S1aA1S1dA3S71S1cS23S1aA1S1eA3S2fS2eS31S30S1bS1dS1cS1eS3fVtail;Vfacts;VX;A12").
Definition JR_fv4 : axst := ltac2:(tb__ "0|2|
S37SfZ1A1S2S11A1S1SdS4aS1SdS36S44A3A3S0S5SeSeA2M0S58Pa0M1S3S2bS2bZ130Z4A4A2S0G0S58G1S3S2bS2bZe0Z24A4A2S3cA3A3A4").
Definition JF_fv4 : axst := ltac2:(tb__ "0|0|
S37SfZ0A1S0S11S43S0S11S42S2S11A1A3A3S36S3cA4").
Definition contFV4 (P : axst) : axst := ltac2:(tb__ "0|0|
S72S67S91S6aS33S4dS47VP;S85S20S61S45A1A2A6S86UfU1dZ210A3A2A1").
Definition T_fv4k : axst := Eval vm_compute in ax_add_facts [SPUle (SLit IMG_HI) lDfv] (contFV4 VN.P_keep).
Definition T_fv4f : axst := Eval vm_compute in contFV4 VN.P_fail.
Definition T_fv4g : axst := Eval vm_compute in contFV4 VN.P_grown.
Goal map (fun L => leaf_matches1A NPH L JR_fv4) [T_fv4k; T_fv4g] = [true; true] /\ leaf_matches1A NPH (reopen2f T_fv4f) JF_fv4 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_fv4 = [(hf_TFX, RsCut)] /\ lvs JF_fv4 = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_m4 : axst := Eval vm_compute in bl_forget (bl_prune HNEXT (leaf_at JR_fv4 hf_TFX 0)) [29%nat].
Goal length (ss_objs (ax_S T_m4)) = 36%nat /\ lvs T_m4 = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

