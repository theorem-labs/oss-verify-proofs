(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "app"; "prod"; "true"; "bool"; "None"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "cell"; "DUnknown"; "SAlu"; "tfact"; "SPBranch"; "SVar"; "SPUle"; "TFle"; "SPNot"; "DArr"; "mkObj"; "FcsrFrm0"; "SMd"; "SPEq"; "SPUlt"; "mkSS"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pA"; "pDco"; "am2"; "pKco"; "shB"; "xbo"; "X_body"; "cA"; "tr_d"; "vec_facts0"; "V784"; "am1"; "fv_d"; "fv_k"; "mi_d"; "mi_k"; "mm_d"; "mm_k"; "rp_d"; "rp_k"; "sg_d"; "sg_k"; "tr_k"; "ts_d"; "ts_k"; "O_F"; "O_Wf"; "O_flag"; "O_frame"; "builderF"; "hdr3"; "optAp"; "pHP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "pDtr"; "pKtr"; "pT"; "pI"; "JTR"; "coK"; "datasD"; "triF"; "flagB"; "pBAD"; "tr_facts"; "FCUT2"; "K1X"; "O_dataD"; "XTR"; "cT"; "flagG"; "hint12"; "ntri3"; "regsT"; "E_tdg"; "E_trb"; "E_trg"; "F_main2"; "flds3"; "objs_face2"; "regsK2"; "regsT2"; "trK"; "vr_ret_tr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "O_data"; "hF"; "kb"; "av_nv"; "HNEXT"; "O_cE"; "O_cP"; "av_d"; "av_k"; "h_fregs"; "h_xregs"; "tB"; "tL"; "tp"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "ALU_SUB"; "BC_EQ"; "BC_LTU"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "pX"; "coP"; "fvP"; "miP"; "mmP"; "rpP"; "sgP"; "tsP"; "FCUT"; "NTR"; "trP"; "X_face"; "XkeepF"; "face_facts"; "lregsF"; "xf_backV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vb"; "O_al"; "vERR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "spm"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.HFAddr"; "FR"; "hf_K1"; "hf_K1X"; "hf_K2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "mkA"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.VRAddr"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition triF : list sprop := ltac2:(tb__ "0|0|
S4SdS0SdS17S13S72S22SeZ3A1A3A1S0SdS13S73SeZ2A1S22A3S3SdA1A3A3S82S75A1A3").

Definition coK (k : sv) : odefault := ltac2:(tb__ "0|1|
S18ZcVk;S0S5S1fS1fA2M0S1S1fS1fZ0Z4A4S3G0A1A3S0S12S16S6U0S9S5S7S21A2S1S7S21S6Q20A4A2S64A4S3S12A1A3A4").
Definition flds3 : list (Z * Z) := ltac2:(tb__ "0|2|
S0S5S1fS1fA2M0S1S1fS1fZ0Z4M1A4S0G0S1S1fS1fG1G1A4S0G0S1S1fS1fZ8G1A4S3G0A1A3A3A3").
Definition trK (k : sv) : odefault := ltac2:(tb__ "0|1|
S18ZcVk;S5bS0S12S16S6U0S8S5S7S21A2A1M0S22A4S0S12S16S6U1G0S22A4S0S12S16S6U2G0S22A4S3S12A1A3A3A3A4").
Definition O_dataD (d : sv) (e : Z) (k : sv) (df : odefault) : sobj := ltac2:(tb__ "0|0|
S19Vd;SeZ0A1S63Ve;Vk;A2S3SfA1Vdf;A5").
Definition datasD (cod : odefault) (dtr ktr : sv) (trd : odefault) : list sobj := ltac2:(tb__ "0|2|
S0ScS61S68Z4M0S69A3S0ScS61S30ZcM1S31A3S0ScS61S2eG0S2fA3S0ScS61S32G0S33A3S0ScS61S36G0S37A3S0ScS50S23G1S25Vcod;A4S0ScS61S34G0S35A3S0ScS50Vdtr;G0Vktr;Vtrd;A4S0ScS61S39Z1S3aA3S3ScA1A3A3A3A3A3A3A3A3A3").
Definition hint12 (k : sv) : sprop := ltac2:(tb__ "0|1|
S1cS1bS74SeZcA1Vk;A3M0G0A2").

Definition pI : sv := SVar 309.
Definition regsT : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S2SbA2M0S83S0G0S1S2SbU10S24A4S0G0S1S2SbU12S22A4S0G0S1S2SbU14S14P1a4A1A4S0G0S1S2SbU15S6eS75A1A4S0G0S1S2SbU16S23A4S0G0S1S2SbU17S62A4S0G0S1S2SbU18S62A4S0G0S1S2SbU19S27Z218A1A4S0G0S1S2SbU1aS26Z43A1A4S0G0S1S2SbU1bS27Z508A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3").
Definition K1 : axst := ltac2:(tb__ "0|3|
S7dS8fS4S5S2SbA2M0S56S0G0S1S2SbUaS11S6fS23S63ZcS46A2A3M1A4S0G0S1S2SbUbS64A4S0G0S1S2SbUcG1A4S0G0S1S2SbU11S11S71S2dS46A3A4S3G0A1A3A3A3A3A3S75S76S7aS7fS78S77S79S7bS7cS4SfS29S0SfS89N88S86A2S3SfA1M2A3A3G2S49S48S46A1S2aS38S10A4S3ScA1S4SdS0SdS15S46S2dA2S0SdS54S46A1S3SdA1A3A3S4aA3S28S23S25A2A11").
Goal leaf_matches1A NPH (leaf_at XA hf_K1 0) K1 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs K1 = [(hf_K1X, RsCut); (hf_K1, RsCut); (hf_K1X, RsCut)] /\ map (fun L => leaf_matches1A NPH L K1) (leavesA_at FUEL_hf cutpcs_hf K1 hf_K1) = [true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition K1X (flag : sprop) (cod : odefault) : axst := ltac2:(tb__ "0|2|
S7dS90S4S5S2SbA2M0S56S0G0S1S2SbUbS64A4S3G0A1A3A3S75S76S7aS7fS78S77S79S7bS7cS4SfS29S0SfS89N88S86A2S3SfA1M1A3A3G1S49Vcod;S2aS38S10A4S3ScA1S0SdVflag;S4aA3S28S23S25A2A11").
Definition K1Xg : axst := ltac2:(tb__ "0|0|
S4fS17S13S70S14P1a4A1SeZ0A1A3A1S48S22A1A2").
Definition K1Xb : axst := ltac2:(tb__ "0|0|
S4fS13S70S14P1a4A1SeZ0A1A3S10A2").
Goal map (fun L => (leaf_matches1A NPH L K1Xg, leaf_matches1A NPH L K1Xb)) (leavesA_at FUEL_hf cutpcs_hf K1 hf_K1X) = [(false, true); (true, false)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs K1Xg = [(vr_entry, RsCut)] /\ lvs K1Xb = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition F_main2 : list cell := Eval vm_compute in List.filter (fun c => negb (sv_eqb (c_off c) (SLit (-144)))) F_main.
Definition objs_face2 (cur hp : sv) (co rp tr mi fv mm sg ts : sobj) (ofcells fcells txt : list cell) (datas : list sobj) (tail : list sobj) : list sobj := ltac2:(tb__ "0|1|
S4ScS0ScS3cS0ScS3eS4SfS40Vfcells;A3A1S0ScS3dS3ScA1M0A3A3A3S4ScS92S4ScS0ScS3bS4SfS5aVofcells;A3A1G0A3S4ScS3fS88Vhp;Vco;Vrp;Vtr;Vmi;Vfv;Vmm;Vsg;Vts;AaS4ScS0ScS87S0ScS67Vcur;A1S0ScS66S0ScS19S6cSeZ0A1S6dVtxt;S10A5G0A3A3A3A3S4ScVdatas;Vtail;A3A3A3A3A3A3").
Definition FCUT2 (pc : Z) (regs : list (nat * sv)) (cur : sv) (co rp tr mi fv mm sg ts : sobj) (ofcells fcells : list cell) (datas tail : list sobj)
                (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S93S1eVpc;S6bVregs;A1S6aS1aS8SbA1S5cVcur;S42Vco;Vrp;Vtr;Vmi;Vfv;Vmm;Vsg;Vts;Vofcells;Vfcells;S3SfA1Vdatas;Vtail;AfVfacts;S65SaA9VX;A2").

Definition E_trg0 : axst := Eval vm_compute in leaf_at K1Xg vr_entry 0.
Definition E_trb0 : axst := Eval vm_compute in leaf_at K1Xb vr_entry 0.
Definition E_trg : axst := Eval vm_compute in optAp (apply_axforms E_trg0 (xf_vr 21 784)).
Definition E_trb : axst := Eval vm_compute in optAp (apply_axforms E_trb0 (xf_vr 21 784)).
Definition s_trg : wsub := ltac2:(tb__ "0|1|
S0S5S20SbA2M0S1S20SbP3bS7eS22A1A4S0G0S1S20SbP13S11S6fS8bSeZ40A1A3A4S8dPaS85S59A1S85S8cA1A3A3A3").
Definition s_trb : wsub := ltac2:(tb__ "0|1|
S0S5S20SbA2M0S1S20SbP3bS7eS22A1A4S0G0S1S20SbP13S11S6fS8bSeZ40A1A3A4S8dPaS85S58A1S85S8cA1A3A3A3").
Definition R_trg : list sobj := Eval vm_compute in optR (entails_frA E_trg VN.Pre_vr s_trg).
Definition R_trb : list sobj := Eval vm_compute in optR (entails_frA E_trb VN.Pre_vr s_trb).
Goal entails_frA E_trg VN.Pre_vr s_trg = Some R_trg /\ call_checkPA E_trg VN.Pre_vr s_trg R_trg (map fst PD_vn) = true
  /\ entails_frA E_trb VN.Pre_vr s_trb = Some R_trb /\ call_checkPA E_trb VN.Pre_vr s_trb R_trb (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pDtr : sv := SVar 343. Definition pKtr : sv := SVar 344. Definition pBAD : sv := SVar 420.
Definition vr_ret_tr : Z := 0x9f32c.
Definition regsT2 (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S2SbA2M0S1S2SbU2S8aS8eA1M1A4S0G0S1S2SbU8S14PaA1A4S0G0S1S2SbU9G1A4S0G0S1S2SbU1Vra;A4S0G0S1S2SbUaVa0;A4S0G0S1S2SbU12S27Z310A1A4S0G0S1S2SbU13S26Z0A1A4S0G0S1S2SbU14S4cA4S0G0S1S2SbU15S86A4S0G0S1S2SbU16S23A4S0G0S1S2SbU17S62A4S0G0S1S2SbU18S62A4S0G0S1S2SbU19S24A4S0G0S1S2SbU1aS26Z43A1A4S0G0S1S2SbU1bS24A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition cT : list cell := ltac2:(tb__ "0|0|
S4SfS29S0SfS89N88S86A2S0SfS89N90S27Z218A1A2S3SfA1A3A3A3").
Definition ntri3 : sv := kb 3 am2.
Definition XTR (dtr ktr : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S80S30S2eS32S36S23S34Vdtr;S39S31S2fS33S37S25S35Vktr;S3aA10").
Definition tr_facts (dtr ktr : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S4SdS0SdS15S55Vktr;A2S0SdS15SeS99A1Vdtr;A2S0SdS15S63Z4M0S55A2S63G0Vktr;A2A2S3SdA1A3A3A3S2bVdtr;Vktr;G0Vdv;A4A3").
Definition flagG : sprop := ltac2:(tb__ "0|0|
S17S13S70S4cSeZ0A1A3A1"). Definition flagB : sprop := SPBranch BC_NE pBAD (SLit 0).
Definition JTR (a0 : sv) (flag : sprop) (cod : odefault) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S4eS96S5eSeS60A1Va0;A2S75S76S7aS2cS43SeZ0A1S44A3S78S77S79S7bS7cS52S3SfA1S49Vcod;S43S44S10A4S3ScA1S0SdVflag;S4SdVfacts;S4aA3A3S51S43S44A2A11").
Definition JR_trg : axst := ltac2:(tb__ "0|0|
S47SeZ1A1S53S48S22A1S4dS43S44P157A3A4").
Definition JF_trg : axst := ltac2:(tb__ "0|0|
S47SeZ0A1S53S48S22A1S2bS43S44Z4P157A4A4").
Definition JR_trb : axst := ltac2:(tb__ "0|0|
S47SeZ1A1S4bS10S4dS43S44P157A3A4").
Definition JF_trb : axst := ltac2:(tb__ "0|0|
S47SeZ0A1S4bS10S2bS43S44Z4P157A4A4").
Definition contTR (E : axst) (s : wsub) (R : list sobj) (P : axst) : axst := ltac2:(tb__ "0|0|
S41S97S98S8cVE;Vs;VR;VP;S81S2aS28S23S25A2A2A6S84U14U22Z310A3A2A1").
Definition T_trgk : axst := Eval vm_compute in ax_add_facts [SPUle (SLit IMG_HI) tr_d] (contTR E_trg s_trg R_trg VN.P_keep).
Definition T_trgf : axst := Eval vm_compute in contTR E_trg s_trg R_trg VN.P_fail.
Definition T_trgg : axst := Eval vm_compute in contTR E_trg s_trg R_trg VN.P_grown.
Definition T_trbk : axst := Eval vm_compute in ax_add_facts [SPUle (SLit IMG_HI) tr_d] (contTR E_trb s_trb R_trb VN.P_keep).
Definition T_trbf : axst := Eval vm_compute in contTR E_trb s_trb R_trb VN.P_fail.
Definition T_trbg : axst := Eval vm_compute in contTR E_trb s_trb R_trb VN.P_grown.
Goal map (fun L => leaf_matches1A NPH L JR_trg) [T_trgk; T_trgg] = [true; true] /\ leaf_matches1A NPH T_trgf JF_trg = true
  /\ map (fun L => leaf_matches1A NPH L JR_trb) [T_trbk; T_trbg] = [true; true] /\ leaf_matches1A NPH T_trbf JF_trb = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_trg = [(vr_entry, RsCut)] /\ lvs JR_trb = [(da_entry, RsCut)] /\ lvs JF_trg = [(hf_EPI, RsCut); (hf_EPI, RsCut)] /\ lvs JF_trb = [(hf_EPI, RsCut); (hf_EPI, RsCut)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_tdg0 : axst := Eval vm_compute in leaf_at JR_trb da_entry 0.
Definition E_tdg : axst := Eval vm_compute in optAp (apply_axforms E_tdg0 [AXSplit 0 (SLit (-96))]).
Definition s_tdg : wsub := ltac2:(tb__ "0|0|
S8dPaS85S57A1S85S95A1A3").
Definition R_tdg : list sobj := Eval vm_compute in optR (entails_frA E_tdg Pre_da s_tdg).
Goal entails_frA E_tdg Pre_da s_tdg = Some R_tdg /\ call_checkA E_tdg Pre_da s_tdg R_tdg (map la_state Posts_da) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_tdg0 : axst := Eval vm_compute in T_pure Pre_da E_tdg s_tdg R_tdg P_da.
Definition T_tdg : axst := Eval vm_compute in ax_setX (optAp (apply_axforms T_tdg0 [AXSelect sel_da; AXMerge 0])) (XTR pDtr pKtr).
Goal shape T_tdg = shape JR_trb /\ lvs T_tdg = [(hf_K2, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pT : sv := SVar 345.
Definition regsK2 : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S2SbA2M0S1S2SbU2S8aS8eA1M1A4S0G0S1S2SbU8S14PaA1A4S0G0S1S2SbU9G1A4S0G0S1S2SbUbS11S6fSeZ1A1S45A3A4S0G0S1S2SbUcS11S6fS11S71SeN2A1S45A3S22A3A4S0G0S1S2SbUdS11S6fSeZ2A1S63Z3S45A2A3A4S0G0S1S2SbU12S27Z310A1A4S0G0S1S2SbU13S26Z0A1A4S0G0S1S2SbU14S4cA4S0G0S1S2SbU15S86A4S0G0S1S2SbU16S23A4S0G0S1S2SbU17S62A4S0G0S1S2SbU18S43A4S0G0S1S2SbU19S24A4S0G0S1S2SbU1aS26Z43A1A4S0G0S1S2SbU1bS94A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition K2 : axst := ltac2:(tb__ "0|0|
S4eS91S5dS75S76S7aS2cS43SeZ0A1S44A3S78S77S79S7bS7cS52S3SfA1S49S10S43S44S5fS45A1A4S3ScA1S4SdS0SdS4bS0SdS1dS45S24A2S0SdS54S45A1S3SdA1A3A3A3S4SdS4dS43S44P157A3S4aA3A3S51S43S44A2A11").
Goal leaf_matches1A NPH (leaf_at T_tdg hf_K2 0) K2 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

