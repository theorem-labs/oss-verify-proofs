(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "app"; "prod"; "list"; "option"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "sobj"; "SAlu"; "SPUle"; "DUnknown"; "cell"; "SVar"; "SPUlt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5"; "pDrp"; "pKrp"; "XRT"; "datasR"; "pDts"; "pKts"; "needA"; "pV"; "rp_facts"; "triG"; "K3facts"; "av_room"; "pG"; "E_rp"; "E_ts"; "JRP"; "JTS"; "a3x"; "cutpcs_hf5"; "g12"; "hf_K3x"; "need_facts"; "regsK3"; "regsK3s"; "M16"; "M32"; "R_rp"; "R_ts"; "av_slot"; "navB"; "nrpB"; "regsK3m"; "regsK3x"; "regsT3"; "regsT4"; "rpG"; "rp_slot"; "s_rp"; "s_ts"; "ts_factsJ"; "vr_ret_rp"; "vr_ret_ts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "pDtr"; "pKtr"; "FCUT2"; "cT"; "coK"; "ncoB"; "O_dataD"; "XTR"; "flagG"; "hint12"; "tr_facts"; "triF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pA"; "ts_d"; "ts_k"; "V752"; "V784"; "am2"; "xbo"; "vec_facts0"; "pDco"; "shB"; "FUEL_hf"; "fv_d"; "fv_k"; "mi_d"; "mi_k"; "mm_d"; "mm_k"; "optAp"; "pKco"; "sg_d"; "sg_k"; "BAD"; "V816"; "cutpcs_hf"; "rp_d"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "O_data"; "av_d"; "av_k"; "av_nv"; "hG"; "hF"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "coP"; "fvP"; "miP"; "mmP"; "pX"; "sgP"; "tsP"; "XkeepF"; "xf_backV"; "NRP"; "NTS"; "X_face"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "ax_X"; "axst"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "shb"; "leavesA_at"; "segs"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.HFAddr"; "FR"; "hf_K3"; "hf_K3m"; "hf_TS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "spm"; "vDp"; "two40"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.VRAddr"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_reopen_stateA"; "shobj"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Goal lvs K2 = [(hf_K2, RsCut); (hf_J, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal map (fun L => leaf_matches1A NPH L K2) (leavesA_at FUEL_hf cutpcs_hf K2 hf_K2) = [true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition datasR (cod : odefault) (drp krp dtr ktr : sv) (trd : odefault) (dts kts : sv) : list sobj := ltac2:(tb__ "0|2|
S0ScS67S68Z4M0S69A3S0ScS67S56ZcM1S57A3S0ScS67S54G0S55A3S0ScS67S58G0S59A3S0ScS67S5cG0S5dA3S0ScS43S51G1S5bVcod;A4S0ScS67Vdrp;G0Vkrp;A3S0ScS43Vdtr;G0Vktr;Vtrd;A4S0ScS67Vdts;Z1Vkts;A3S3ScA1A3A3A3A3A3A3A3A3A3").
Definition XRT (drp krp dts kts : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S7aS56S54S58S5cS51Vdrp;S3dVdts;S57S55S59S5dS5bVkrp;S3eVkts;A10").

Definition E_rp0 : axst := Eval vm_compute in leaf_at JR_trg vr_entry 0.
Definition E_rp : axst := Eval vm_compute in optAp (apply_axforms E_rp0 (xf_vr 20 752)).
Definition s_rp : wsub := ltac2:(tb__ "0|1|
S0S5S6dS9A2M0S2S6dS9P3bS78S49A1A4S0G0S2S6dS9P13SdS62S8bSbZ40A1A3A4S8ePaS7cS20A1S7cS7bA1A3A3A3").
Definition R_rp : list sobj := Eval vm_compute in optR (entails_frA E_rp VN.Pre_vr s_rp).
Goal entails_frA E_rp VN.Pre_vr s_rp = Some R_rp /\ call_checkPA E_rp VN.Pre_vr s_rp R_rp (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pDrp : sv := SVar 346. Definition pKrp : sv := SVar 347.
Definition vr_ret_rp : Z := 0x9d77c.
Definition regsT3 (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1S9A2M0S2S1S9U2S8aS86A1M1A4S0G0S2S1S9U8S11PaA1A4S0G0S2S1S9U9G1A4S0G0S2S1S9U1Vra;A4S0G0S2S1S9UaVa0;A4S0G0S2S1S9U12S81A4S0G0S2S1S9U13S4fZ2f0A1A4S0G0S2S1S9U14S52Z43A1A4S0G0S2S1S9U15S42A4S0G0S2S1S9U16S4eA4S0G0S2S1S9U17S85A4S0G0S2S1S9U18S6cA4S0G0S2S1S9U19S3dA4S0G0S2S1S9U1aS4fZ210A1A4S0G0S2S1S9U1bS4eA4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition a3x : sv := kb 3 pA.
Definition rp_facts (drp krp : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|2|
S4SaS0SaSeS24Vkrp;A2S0SaSeSbS91A1Vdrp;A2S0SaSeS66Z4M0S24A2S66G0Vkrp;A2M1A2S0SaSeS66ZcS49A2G1A2S3SaA1A3A3A3A3S50Vdrp;Vkrp;G0Vdv;A4A3").
Definition triG : list sprop := ltac2:(tb__ "0|0|
S0SaS45S4SaS47S3dS3eP157A3S48A3A3").
Definition JRP (a0 : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S3fS8dS34SbS3bA1Va0;A2S73S6fS4cS13SbZ0A1M0S14A3S4dS3dG0S3eA3S71S70S72S74S75S40S3S10A1S16S41S49A1S13S14S3dS3eSfS4aS4bA8S3ScA1S4SaVfacts;S1cA3S15S13S14S4aS4bA4A11").
Definition JR_rp : axst := ltac2:(tb__ "0|0|
S22SbZ1A1S1bS13S14P15aA3A2").
Definition JF_rp : axst := ltac2:(tb__ "0|0|
S22SbZ0A1S50S13S14Z4P15aA4A2").
Definition contRP (P : axst) : axst := ltac2:(tb__ "0|0|
S5aS8fS90S7bS20S38S2dVP;S76S61S44S3dS3eA2A2A6S77U13U21Z2f0A3A2A1").
Definition T_rpk : axst := Eval vm_compute in ax_add_facts [SPUle (SLit IMG_HI) rp_d] (contRP VN.P_keep).
Definition T_rpf : axst := Eval vm_compute in contRP VN.P_fail.
Definition T_rpg : axst := Eval vm_compute in contRP VN.P_grown.
Goal map (fun L => leaf_matches1A NPH L JR_rp) [T_rpk; T_rpg] = [true; true] /\ leaf_matches1A NPH T_rpf JF_rp = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition hf_trap2 : Z := 0x9e9a8.
Definition X_avnull : axst := Eval vm_compute in leaf_at JR_rp hf_trap2 0.
Goal lvs JR_rp = [(hf_K3, RsCut); (hf_trap2, RsUnsupported)] /\ lvs JF_rp = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pG : sv := SVar 348.
Definition g12 : sv := kb 12 pG.
Definition navB : sv := SAlu ALU_XOR av_d (SLit 18446744073709551615).
Definition nrpB : sv := SAlu ALU_XOR pDrp (SLit 18446744073709551615).
Definition regsK3s : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1S9A2M0S2S1S9U2S8aS86A1M1A4S0G0S2S1S9U8S11PaA1A4S0G0S2S1S9U9G1A4S0G0S2S1S9U1fS49A4S0G0S2S1S9U12S81A4S0G0S2S1S9U13S4fZ2f0A1A4S0G0S2S1S9U14S52Z43A1A4S0G0S2S1S9U15S42A4S0G0S2S1S9U16S4eA4S0G0S2S1S9U17S85A4S0G0S2S1S9U18S13A4S0G0S2S1S9U19S3dA4S0G0S2S1S9U1aS4fZ210A1A4S0G0S2S1S9U1bS4eA4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition regsK3 : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1S9A2M0S2aS0G0S2S1S9UfS1fA4S0G0S2S1S9U5SdS62S26SbZ8A1A3A4S0G0S2S1S9U1eS51A4S0G0S2S1S9UeS68A4S0G0S2S1S9UdS30A4S0G0S2S1S9U11S31A4S0G0S2S1S9U6SbZ1A1A4S0G0S2S1S9U10SbZaaaaaaaaaaaaaa9A1A4S3G0A1A3A3A3A3A3A3A3A3A3").
Definition av_room : sprop := ltac2:(tb__ "0|0|
SeS66ZcS6aA2S66Z4S69A2A2").

Definition rp_slot : sprop := ltac2:(tb__ "0|0|
SeSdS62S26SbZcA1A3S66Z4S14A2A2").
Definition K3facts : list sprop := ltac2:(tb__ "0|0|
S4SaS0SaS12S1fS49A2S0SaS37S0SaS46S1fA1S0SaS1eS3SaA1A3A3A3A3S4SaS1bS13S14P15aA3S1cA3A3").
Definition K3 : axst := ltac2:(tb__ "0|1|
S3fS87S29S73S6fS4cS13SbZ0A1M0S14A3S4dS3dG0S3eA3S71S70S72S74S75S40S3S10A1S16S41S49A1S13S14S3dS3eSfS4aS4bA8S3ScA1S1dS15S13S14S4aS4bA4A11").
Goal leaf_matches1A NPH (leaf_at JR_rp hf_K3 0) K3 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition pV : sv := SVar 358.
Definition av_slot : sprop := ltac2:(tb__ "0|1|
SeSdS62S66ZcM0S1aA2SbG0A1A3S66Z4S69A2A2").
Definition regsK3m : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1S9A2M0S29S0G0S2S1S9UcSdS62S68S66ZcS1aA2A3A4S0G0S2S1S9U7S66Z3S1aA2A4S3G0A1A3A3A3").
Definition K3m : axst := ltac2:(tb__ "0|1|
S3fS88S32S73S6fS4cS13SbZ0A1M0S14A3S4dS3dG0S3eA3S71S70S72S74S75S40S3S10A1S16S41S49A1S13S14S3dS3eSfS4aS4bA8S3ScA1S0SaS12S1aS6aA2S0SaS2fS1dA3A3S15S13S14S4aS4bA4A11").
Goal lvs K3 = [(hf_K3m, RsCut)] /\ leaf_matches1A NPH (leaf_at K3 hf_K3m 0) K3m = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition hf_K3x : Z := 0x9d930.
Definition cutpcs_hf5 : list Z := ltac2:(tb__ "0|0|
S4S6eS60S0S6eS27S3S6eA1A3A3").
Definition leaf_at5 (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S93S7fVk;S82S53S25VS;Vpc;A4S5eA4").
Definition lvs5 (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S7S6S7dA1M0A1S6S5S6eS94A2M1A1Lx;S80S83S53S25VS;S8A5G0S92S7dG1S84R1A4Ll;S3G1A1X7x2").
Definition regsK3x : list (nat * sv) := regsK3.
Definition K3x : axst := ltac2:(tb__ "0|1|
S3fS27S33S73S6fS4cS13SbZ0A1M0S14A3S4dS3dG0S3eA3S71S70S72S74S75S40S3S10A1S16S41S49A1S13S14S3dS3eSfS4aS4bA8S3ScA1S1dS15S13S14S4aS4bA4A11").

Goal lvs5 K3m = [(hf_K3x, RsCut); (hf_K3x, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal map (fun L => leaf_matches1A NPH L K3x) (leavesA_at FUEL_hf cutpcs_hf5 K3m hf_K3x) = [true; true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs5 K3x = [(hf_K3, RsCut); (hf_TS, RsCut)] /\ map (fun L => leaf_matches1A NPH L K3) (leavesA_at FUEL_hf cutpcs_hf5 K3x hf_K3) = [true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition TS : axst := ltac2:(tb__ "0|1|
S3fS89S2aS73S6fS4cS13SbZ0A1M0S14A3S4dS3dG0S3eA3S71S70S72S74S75S40S3S10A1S16S41S49A1S13S14S3dS3eSfS4aS4bA8S3ScA1S4SaS0SaS1eS3SaA1A3S4SaS1bS13S14P15aA3S1cA3A3S15S13S14S4aS4bA4A11").
Goal map (fun L => leaf_matches1A NPH L TS) (leavesA_at FUEL_hf cutpcs_hf5 K3x hf_TS) = [true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs TS = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition M16 : sv := SLit 18446744073709551600. Definition M32 : sv := SLit 18446744073709551584.
Definition needA : sv := ltac2:(tb__ "0|1|
SdS62SdS62SdS63SdS62SdS64S49SbZ3A1M0A3SbZ1eA1A3S2cA3SdS64S49SbZ4A1A3A3SdS63SdS62SdS65SdS62S49SbZ7A1A3G0A3SbZfA1A3S2bA3A3").
Definition need_facts : list sprop := ltac2:(tb__ "0|0|
S0SaSeS19S66Z25S49A2A2S0SaSeS19SbS8cA1A2S3SaA1A3A3").
Definition E_ts0 : axst := Eval vm_compute in leaf_at TS vr_entry 0.
Definition a1_ts : sv := Eval vm_compute in nth 11 (ss_regs (ax_S E_ts0)) (SLit 0).
Goal sv_eqb a1_ts needA = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_ts : axst := Eval vm_compute in ax_add_facts need_facts (optAp (apply_axforms E_ts0 (xf_vr 22 816))).
Definition s_ts : wsub := ltac2:(tb__ "0|1|
S0S5S6dS9A2M0S2S6dS9P3bS79S49A1A4S0G0S2S6dS9P13SdS62S8bSbZ40A1A3A4S8ePaS7cS21A1S7cS7bA1A3A3A3").
Definition R_ts : list sobj := Eval vm_compute in optR (entails_frA E_ts VN.Pre_vr s_ts).
Goal entails_frA E_ts VN.Pre_vr s_ts = Some R_ts /\ call_checkPA E_ts VN.Pre_vr s_ts R_ts (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pDts : sv := SVar 350. Definition pKts : sv := SVar 351.
Definition vr_ret_ts : Z := 0x9da2c.
Definition regsT4 (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1S9A2M0S2S1S9U2S8aS86A1M1A4S0G0S2S1S9U8S11PaA1A4S0G0S2S1S9U9G1A4S0G0S2S1S9U1Vra;A4S0G0S2S1S9UaVa0;A4S0G0S2S1S9U12S81A4S0G0S2S1S9U13S4fZ330A1A4S0G0S2S1S9U14S52Z43A1A4S0G0S2S1S9U15S42A4S0G0S2S1S9U16S4eA4S0G0S2S1S9U17S19A4S0G0S2S1S9U18S13A4S0G0S2S1S9U19S3dA4S0G0S2S1S9U1aS85A4S0G0S2S1S9U1bS4eA4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition ts_factsJ (dts kts : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|0|
S4SaS0SaSeS19Vkts;A2S0SaSeSbS91A1Vdts;A2S3SaA1A3A3S4SaS28S50Vdts;Vkts;Z1Vdv;A4A3A3").
Definition rpG : list sprop := ltac2:(tb__ "0|0|
S4SaS0SaS1eS3SaA1A3S4SaS1bS13S14P15aA3S1cA3A3").

Definition JTS (a0 : sv) (facts : list sprop) (tail : list sobj) : axst := ltac2:(tb__ "0|1|
S3fS8dS35SbS3cA1Va0;A2S73S6fS4cS13SbZ0A1M0S14A3S4dS3dG0S3eA3S71S70S72S74S5fS17S18A2S40S3S10A1S16S41S49A1S13S14S3dS3eSfS17S18A8Vtail;S4SaVfacts;S36A3S15S13S14S17S18A4A11").
Definition JR_ts : axst := ltac2:(tb__ "0|0|
S23SbZ1A1S3aS17S18P15eA3S0ScS96S6bZ6Z17S3S10A1SfA5S3ScA1A3A3").
Definition JF_ts : axst := ltac2:(tb__ "0|0|
S23SbZ0A1S4SaS28S50S17S18Z1P15eA4A3S3ScA1A3").
Definition reopenX (k1 k2 : Z) (A : axst) : axst := ltac2:(tb__ "0|0|
S95VA;S7eVA;A1S6bVk1;Vk2;A5").
Definition contTS (P : axst) : axst := ltac2:(tb__ "0|0|
S5aS8fS90S7bS21S39S2eVP;S76S4aS15S13S14S4aS4bA4A2A6S77U15U23Z330A3A2A1").
Definition T_tsk : axst := Eval vm_compute in ax_add_facts [SPUle (SLit IMG_HI) ts_d] (contTS VN.P_keep).
Definition T_tsf : axst := Eval vm_compute in contTS VN.P_fail.
Definition T_tsg : axst := Eval vm_compute in contTS VN.P_grown.
Goal map (fun L => leaf_matches1A NPH L JR_ts) [reopenX 6 23 T_tsk; reopenX 6 23 T_tsg] = [true; true] /\ leaf_matches1A NPH T_tsf JF_ts = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_ts = [(pg_pc, RsCut)] /\ lvs JF_ts = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
