(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "app"; "prod"; "true"; "bool"; "None"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "cell"; "sprop"; "DUnknown"; "SAlu"; "SVar"; "tfact"; "SPBranch"; "SPUle"; "TFle"; "SPNot"; "DArr"; "mkObj"; "FcsrFrm0"; "SMd"; "SPEq"; "SPUlt"; "mkSS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pA"; "xbo"; "pDco"; "am2"; "pKco"; "shB"; "X_body"; "cA"; "tr_d"; "vec_facts0"; "V784"; "am1"; "fv_d"; "fv_k"; "mi_d"; "mi_k"; "mm_d"; "mm_k"; "rp_d"; "rp_k"; "sg_d"; "sg_k"; "tr_k"; "ts_d"; "ts_k"; "O_F"; "O_Wf"; "O_flag"; "O_frame"; "builderF"; "hdr3"; "optAp"; "pHP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "pDtr"; "pKtr"; "pT"; "pI"; "JTR"; "coK"; "datasD"; "triF"; "flagB"; "ncoB"; "pBAD"; "tr_facts"; "FCUT2"; "K1X"; "O_dataD"; "XTR"; "cT"; "flagG"; "hint12"; "ntri3"; "regsT"; "E_tdg"; "E_trb"; "E_trg"; "F_main2"; "flds3"; "objs_face2"; "regsK2"; "regsT2"; "trK"; "vr_ret_tr"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "spm"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "O_data"; "kb"; "av_nv"; "hF"; "HNEXT"; "O_cE"; "O_cP"; "av_d"; "av_k"; "h_fregs"; "h_xregs"; "tB"; "tL"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "ALU_SUB"; "ALU_XOR"; "BC_EQ"; "BC_LTU"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "pX"; "coP"; "fvP"; "miP"; "mmP"; "rpP"; "sgP"; "tsP"; "FCUT"; "NTR"; "trP"; "X_face"; "XkeepF"; "face_facts"; "xf_backV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "shb"; "A_globals"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.HFAddr"; "FR"; "hf_K1"; "hf_K1X"; "hf_K2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "O_al"; "vERR"; "vb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.VRAddr"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition triF : list sprop := ltac2:(tb__ "0|0|
S4SfS0SfS17S14S76S1fSdZ3A1A3A1S0SfS14S77SdZ2A1S1fA3S3SfA1A3A3S87S7aA1A3").

Definition coK (k : sv) : odefault := ltac2:(tb__ "0|1|
S18ZcVk;S0S5S5fS5fA2M0S1S5fS5fZ0Z4A4S3G0A1A3S0S13S16S6U0S9S5S7S61A2S1S7S61S6Q20A4A2S67A4S3S13A1A3A4").
Definition flds3 : list (Z * Z) := ltac2:(tb__ "0|2|
S0S5S5fS5fA2M0S1S5fS5fZ0Z4M1A4S0G0S1S5fS5fG1G1A4S0G0S1S5fS5fZ8G1A4S3G0A1A3A3A3").
Definition trK (k : sv) : odefault := ltac2:(tb__ "0|1|
S18ZcVk;S59S0S13S16S6U0S8S5S7S61A2A1M0S1fA4S0S13S16S6U1G0S1fA4S0S13S16S6U2G0S1fA4S3S13A1A3A3A3A4").
Definition O_dataD (d : sv) (e : Z) (k : sv) (df : odefault) : sobj := ltac2:(tb__ "0|0|
S19Vd;SdZ0A1S66Ve;Vk;A2S3SeA1Vdf;A5").
Definition datasD (cod : odefault) (dtr ktr : sv) (trd : odefault) : list sobj := ltac2:(tb__ "0|2|
S0ScS65S6cZ4M0S6dA3S0ScS65S2dZcM1S2eA3S0ScS65S2bG0S2cA3S0ScS65S2fG0S30A3S0ScS65S33G0S34A3S0ScS4eS21G1S23Vcod;A4S0ScS65S31G0S32A3S0ScS4eVdtr;G0Vktr;Vtrd;A4S0ScS65S36Z1S37A3S3ScA1A3A3A3A3A3A3A3A3A3").
Definition hint12 (k : sv) : sprop := ltac2:(tb__ "0|1|
S1cS1bS78SdZcA1Vk;A3M0G0A2").

Definition pI : sv := SVar 309.
Definition ncoB : sv := SAlu ALU_XOR pDco (SLit 18446744073709551615).
Definition regsT : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S2SbA2M0S1S2SbU2S63S8cA1M1A4S0G0S1S2SbU8S12PaA1A4S0G0S1S2SbU9G1A4S0G0S1S2SbU12S89A4S0G0S1S2SbU13S1fA4S0G0S1S2SbU14S24Z43A1A4S0G0S1S2SbU15S49A4S0G0S1S2SbU17S12P1a7A1A4S0G0S1S2SbU18S68A4S0G0S1S2SbU19S20Z218A1A4S0G0S1S2SbU1aS20Z210A1A4S0G0S1S2SbU1bS22A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition K1 : axst := ltac2:(tb__ "0|4|
S82S8dS4S5S2SbA2M0S54S0G0S1S2SbU10S43A4S0G0S1S2SbUaS11S72S66ZcM1S43A2S21A3M2A4S0G0S1S2SbUbS67A4S0G0S1S2SbUcS2aA4S0G0S1S2SbUdSdG1A1A4S0G0S1S2SbUeG2A4S3G0A1A3A3A3A3A3A3A3S7aS7bS7fS84S7dS7cS7eS80S81S4SeS26S0SeS62N88S21A2S0SeS62N98S20Z210A1A2S0SeS62Na8S20Z218A1A2S3SeA1M3A3A3A3A3G3S46S45S43A1S27S35S10A4S3ScA1S4SfS0SfS15S43S2aA2S0SfS52S43A1S3SfA1A3A3S47A3S25S21S23A2A11").
Goal leaf_matches1A NPH (leaf_at XA hf_K1 0) K1 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs K1 = [(hf_K1X, RsCut); (hf_K1, RsCut); (hf_K1X, RsCut)] /\ map (fun L => leaf_matches1A NPH L K1) (leavesA_at FUEL_hf cutpcs_hf K1 hf_K1) = [true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition K1X (flag : sprop) (cod : odefault) : axst := ltac2:(tb__ "0|2|
S82S8eS4S5S2SbA2M0S54S0G0S1S2SbUbS67A4S3G0A1A3A3S7aS7bS7fS84S7dS7cS7eS80S81S4SeS26S0SeS62N88S21A2S0SeS62N98S20Z210A1A2S0SeS62Na8S20Z218A1A2S3SeA1M1A3A3A3A3G1S46Vcod;S27S35S10A4S3ScA1S0SfVflag;S47A3S25S21S23A2A11").
Definition K1Xg : axst := ltac2:(tb__ "0|0|
S4dS17S14S73S12P1a7A1SdZ0A1A3A1S45S1fA1A2").
Definition K1Xb : axst := ltac2:(tb__ "0|0|
S4dS14S73S12P1a7A1SdZ0A1A3S10A2").
Goal map (fun L => (leaf_matches1A NPH L K1Xg, leaf_matches1A NPH L K1Xb)) (leavesA_at FUEL_hf cutpcs_hf K1 hf_K1X) = [(false, true); (true, false)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs K1Xg = [(vr_entry, RsCut)] /\ lvs K1Xb = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition F_main2 : list cell := Eval vm_compute in List.filter (fun c => negb (sv_eqb (c_off c) (SLit (-144)) || sv_eqb (c_off c) (SLit (-176)))) F_main.
Definition objs_face2 (cur hp : sv) (co rp tr mi fv mm sg ts : sobj) (ofcells fcells txt : list cell) (datas : list sobj) (tail : list sobj) : list sobj := ltac2:(tb__ "0|1|
S4ScS0ScS39S0ScS3bS4SeS3dVfcells;A3A1S0ScS3aS3ScA1M0A3A3A3S4ScS8aS4ScS0ScS38S4SeS58Vofcells;A3A1G0A3S4ScS3cS93Vhp;Vco;Vrp;Vtr;Vmi;Vfv;Vmm;Vsg;Vts;AaS4ScS0ScS92S0ScS6bVcur;A1S0ScS6aS0ScS19S70SdZ0A1S71Vtxt;S10A5G0A3A3A3A3S4ScVdatas;Vtail;A3A3A3A3A3A3").
Definition FCUT2 (pc : Z) (regs : list (nat * sv)) (cur : sv) (co rp tr mi fv mm sg ts : sobj) (ofcells fcells : list cell) (datas tail : list sobj)
                (facts : list sprop) (X : list (sv * sv)) : axst := ltac2:(tb__ "0|0|
S8bS1eVpc;S6fVregs;A1S6eS1aS8SbA1S5aVcur;S3fVco;Vrp;Vtr;Vmi;Vfv;Vmm;Vsg;Vts;Vofcells;Vfcells;S3SeA1Vdatas;Vtail;AfVfacts;S69SaA9VX;A2").

Definition E_trg0 : axst := Eval vm_compute in leaf_at K1Xg vr_entry 0.
Definition E_trb0 : axst := Eval vm_compute in leaf_at K1Xb vr_entry 0.
Definition E_trg : axst := Eval vm_compute in optAp (apply_axforms E_trg0 (xf_vr 21 784)).
Definition E_trb : axst := Eval vm_compute in optAp (apply_axforms E_trb0 (xf_vr 21 784)).
Definition s_trg : wsub := ltac2:(tb__ "0|1|
S0S5S60SbA2M0S1S60SbP3bS83S1fA1A4S0G0S1S60SbP13S11S72S64SdZ40A1A3A4S91PaS79S57A1S79S90A1A3A3A3").
Definition s_trb : wsub := ltac2:(tb__ "0|1|
S0S5S60SbA2M0S1S60SbP3bS83S1fA1A4S0G0S1S60SbP13S11S72S64SdZ40A1A3A4S91PaS79S56A1S79S90A1A3A3A3").
Definition R_trg : list sobj := Eval vm_compute in optR (entails_frA E_trg VN.Pre_vr s_trg).
Definition R_trb : list sobj := Eval vm_compute in optR (entails_frA E_trb VN.Pre_vr s_trb).
Goal entails_frA E_trg VN.Pre_vr s_trg = Some R_trg /\ call_checkPA E_trg VN.Pre_vr s_trg R_trg (map fst PD_vn) = true
  /\ entails_frA E_trb VN.Pre_vr s_trb = Some R_trb /\ call_checkPA E_trb VN.Pre_vr s_trb R_trb (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pDtr : sv := SVar 343. Definition pKtr : sv := SVar 344. Definition pBAD : sv := SVar 423.
Definition vr_ret_tr : Z := 0x9d56c.
Definition regsT2 (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S2SbA2M0S1S2SbU2S63S8cA1M1A4S0G0S1S2SbU8S12PaA1A4S0G0S1S2SbU9G1A4S0G0S1S2SbU1Vra;A4S0G0S1S2SbUaVa0;A4S0G0S1S2SbU12S89A4S0G0S1S2SbU13S20Z310A1A4S0G0S1S2SbU14S24Z43A1A4S0G0S1S2SbU15S49A4S0G0S1S2SbU16S22A4S0G0S1S2SbU17S4aA4S0G0S1S2SbU18S68A4S0G0S1S2SbU19S94A4S0G0S1S2SbU1aS20Z210A1A4S0G0S1S2SbU1bS22A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition cT : list cell := ltac2:(tb__ "0|0|
S4SeS26S0SeS62N88S21A2S0SeS62N98S20Z210A1A2S0SeS62Na8S20Z218A1A2S0SeS62N90S24Z0A1A2S0SeS62Nb0S1fA2S3SeA1A3A3A3A3A3A3").
Definition ntri3 : sv := kb 3 am2.
Definition XTR (dtr ktr : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S85S2dS2bS2fS33S21S31Vdtr;S36S2eS2cS30S34S23S32Vktr;S37A10").
Definition tr_facts (dtr ktr : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S4SfS0SfS15S53Vktr;A2S0SfS15SdS99A1Vdtr;A2S0SfS15S66Z4M0S53A2S66G0Vktr;A2A2S3SfA1A3A3A3S28Vdtr;Vktr;G0Vdv;A4A3").
Definition flagG : sprop := ltac2:(tb__ "0|0|
S17S14S73S4aSdZ0A1A3A1"). Definition flagB : sprop := SPBranch BC_NE pBAD (SLit 0).
Definition JTR (a0 : sv) (flag : sprop) (cod : odefault) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S4cS96S5cSdS5eA1Va0;A2S7aS7bS7fS29S40SdZ0A1S41A3S7dS7cS7eS80S81S50S3SeA1S46Vcod;S40S41S10A4S3ScA1S0SfVflag;S4SfVfacts;S47A3A3S4fS40S41A2A11").
Definition JR_trg : axst := ltac2:(tb__ "0|0|
S44SdZ1A1S51S45S1fA1S4bS40S41P157A3A4").
Definition JF_trg : axst := ltac2:(tb__ "0|0|
S44SdZ0A1S51S45S1fA1S28S40S41Z4P157A4A4").
Definition JR_trb : axst := ltac2:(tb__ "0|0|
S44SdZ1A1S48S10S4bS40S41P157A3A4").
Definition JF_trb : axst := ltac2:(tb__ "0|0|
S44SdZ0A1S48S10S28S40S41Z4P157A4A4").
Definition contTR (E : axst) (s : wsub) (R : list sobj) (P : axst) : axst := ltac2:(tb__ "0|0|
S3eS97S98S90VE;Vs;VR;VP;S86S27S25S21S23A2A2A6S88U14U22Z310A3A2A1").
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
S91PaS79S55A1S79S95A1A3").
Definition R_tdg : list sobj := Eval vm_compute in optR (entails_frA E_tdg Pre_da s_tdg).
Goal entails_frA E_tdg Pre_da s_tdg = Some R_tdg /\ call_checkA E_tdg Pre_da s_tdg R_tdg (map la_state Posts_da) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_tdg0 : axst := Eval vm_compute in T_pure Pre_da E_tdg s_tdg R_tdg P_da.
Definition T_tdg : axst := Eval vm_compute in ax_setX (optAp (apply_axforms T_tdg0 [AXSelect sel_da; AXMerge 0])) (XTR pDtr pKtr).
Goal shape T_tdg = shape JR_trb /\ lvs T_tdg = [(hf_K2, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pT : sv := SVar 345.
Definition regsK2 : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S2SbA2M0S1S2SbU2S63S8cA1M1A4S0G0S1S2SbU8S12PaA1A4S0G0S1S2SbU9G1A4S0G0S1S2SbU5S21A4S0G0S1S2SbUbS11S75S40SdZffffffffffffffffA1A3A4S0G0S1S2SbUcS11S72SdZ1A1S42A3A4S0G0S1S2SbUdS11S72S11S74SdN2A1S42A3S1fA3A4S0G0S1S2SbUeS11S72SdZ2A1S66Z3S42A2A3A4S0G0S1S2SbU12S89A4S0G0S1S2SbU13S20Z310A1A4S0G0S1S2SbU14S24Z43A1A4S0G0S1S2SbU15S49A4S0G0S1S2SbU16S22A4S0G0S1S2SbU17S4aA4S0G0S1S2SbU18S68A4S0G0S1S2SbU19S40A4S0G0S1S2SbU1aS20Z210A1A4S0G0S1S2SbU1bS22A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition K2 : axst := ltac2:(tb__ "0|0|
S4cS8fS5bS7aS7bS7fS29S40SdZ0A1S41A3S7dS7cS7eS80S81S50S3SeA1S46S10S40S41S5dS42A1A4S3ScA1S4SfS0SfS48S0SfS1dS42S22A2S0SfS52S42A1S3SfA1A3A3A3S4SfS4bS40S41P157A3S47A3A3S4fS40S41A2A11").
Goal leaf_matches1A NPH (leaf_at T_tdg hf_K2 0) K2 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

