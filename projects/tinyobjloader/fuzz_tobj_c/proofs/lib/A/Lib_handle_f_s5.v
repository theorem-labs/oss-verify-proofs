(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "app"; "prod"; "list"; "option"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SAlu"; "sobj"; "SPUle"; "DUnknown"; "cell"; "SVar"; "SPUlt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "pDrp"; "pKrp"; "XRT"; "datasR"; "g12"; "pDts"; "pKts"; "needA"; "rp_facts"; "triG"; "K3facts"; "av_room"; "pG"; "pV"; "regsK3"; "E_rp"; "E_ts"; "JRP"; "JTS"; "a3x"; "cutpcs_hf5"; "hf_K3x"; "need_facts"; "regsK3s"; "M16"; "M32"; "R_rp"; "R_ts"; "av_slot"; "regsK3m"; "regsK3x"; "regsT3"; "regsT4"; "rpG"; "rp_slot"; "s_rp"; "s_ts"; "ts_factsJ"; "vr_ret_rp"; "vr_ret_ts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "pDtr"; "pKtr"; "FCUT2"; "cT"; "coK"; "O_dataD"; "XTR"; "flagG"; "hint12"; "tr_facts"; "triF"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SRL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pA"; "ts_d"; "ts_k"; "V752"; "V784"; "pDco"; "shB"; "am2"; "vec_facts0"; "xbo"; "FUEL_hf"; "fv_d"; "fv_k"; "mi_d"; "mi_k"; "mm_d"; "mm_k"; "optAp"; "pKco"; "sg_d"; "sg_k"; "BAD"; "V816"; "cutpcs_hf"; "rp_d"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "O_data"; "av_d"; "av_k"; "hF"; "av_nv"; "hG"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "coP"; "fvP"; "miP"; "mmP"; "pX"; "sgP"; "tsP"; "XkeepF"; "xf_backV"; "NRP"; "NTS"; "X_face"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "ax_X"; "axst"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.HFAddr"; "FR"; "hf_K3"; "hf_K3m"; "hf_TS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "spm"; "vDp"; "two40"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.VRAddr"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "leavesA_at"; "segs"; "shb"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_reopen_stateA"; "shobj"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Goal lvs K2 = [(hf_K2, RsCut); (hf_J, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal map (fun L => leaf_matches1A NPH L K2) (leavesA_at FUEL_hf cutpcs_hf K2 hf_K2) = [true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition datasR (cod : odefault) (drp krp dtr ktr : sv) (trd : odefault) (dts kts : sv) : list sobj := ltac2:(tb__ "0|2|
S0SdS65S66Z4M0S67A3S0SdS65S58ZcM1S59A3S0SdS65S56G0S57A3S0SdS65S5aG0S5bA3S0SdS65S5eG0S5fA3S0SdS40S50G1S5dVcod;A4S0SdS65Vdrp;G0Vkrp;A3S0SdS40Vdtr;G0Vktr;Vtrd;A4S0SdS65Vdts;Z1Vkts;A3S3SdA1A3A3A3A3A3A3A3A3A3").
Definition XRT (drp krp dts kts : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S78S58S56S5aS5eS50Vdrp;S3bVdts;S59S57S5bS5fS5dVkrp;S3cVkts;A10").

Definition E_rp0 : axst := Eval vm_compute in leaf_at JR_trg vr_entry 0.
Definition E_rp : axst := Eval vm_compute in optAp (apply_axforms E_rp0 (xf_vr 20 752)).
Definition s_rp : wsub := ltac2:(tb__ "0|1|
S0S5S6bS9A2M0S2S6bS9P3bS76S4bA1A4S0G0S2S6bS9P13ScS46S85SbZ40A1A3A4S88PaS7bS22A1S7bS7aA1A3A3A3").
Definition R_rp : list sobj := Eval vm_compute in optR (entails_frA E_rp VN.Pre_vr s_rp).
Goal entails_frA E_rp VN.Pre_vr s_rp = Some R_rp /\ call_checkPA E_rp VN.Pre_vr s_rp R_rp (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pDrp : sv := SVar 346. Definition pKrp : sv := SVar 347.
Definition vr_ret_rp : Z := 0x9f58c.
Definition regsT3 (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1S9A2M0S2S1S9U2S84S80A1M1A4S0G0S2S1S9U8S11PaA1A4S0G0S2S1S9U9G1A4S0G0S2S1S9U1Vra;A4S0G0S2S1S9UaVa0;A4S0G0S2S1S9U12S54Z2f0A1A4S0G0S2S1S9U13S51Z0A1A4S0G0S2S1S9U14S79A4S0G0S2S1S9U15S79A4S0G0S2S1S9U16S50A4S0G0S2S1S9U17S68A4S0G0S2S1S9U18S3bA4S0G0S2S1S9U19S52A4S0G0S2S1S9U1aS51Z43A1A4S0G0S2S1S9U1bS52A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition a3x : sv := kb 3 pA.
Definition rp_facts (drp krp : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|2|
S4SaS0SaSeS26Vkrp;A2S0SaSeSbS8bA1Vdrp;A2S0SaSeS64Z4M0S26A2S64G0Vkrp;A2M1A2S0SaSeS64ZcS4bA2G1A2S3SaA1A3A3A3A3S53Vdrp;Vkrp;G0Vdv;A4A3").
Definition triG : list sprop := ltac2:(tb__ "0|0|
S0SaS42S4SaS44S3bS3cP157A3S45A3A3").
Definition JRP (a0 : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S3dS87S32SbS39A1Va0;A2S71S6dS4eS13SbZ0A1M0S14A3S4fS3bG0S3cA3S6fS6eS70S72S73S3eS3S10A1S16S3fS4bA1S13S14S3bS3cSfS4cS4dA8S3SdA1S4SaVfacts;S1cA3S15S13S14S4cS4dA4A11").
Definition JR_rp : axst := ltac2:(tb__ "0|0|
S24SbZ1A1S1bS13S14P15aA3A2").
Definition JF_rp : axst := ltac2:(tb__ "0|0|
S24SbZ0A1S53S13S14Z4P15aA4A2").
Definition contRP (P : axst) : axst := ltac2:(tb__ "0|0|
S5cS89S8aS7aS22S36S2dVP;S74S63S41S3bS3cA2A2A6S75U13U21Z2f0A3A2A1").
Definition T_rpk : axst := Eval vm_compute in ax_add_facts [SPUle (SLit IMG_HI) rp_d] (contRP VN.P_keep).
Definition T_rpf : axst := Eval vm_compute in contRP VN.P_fail.
Definition T_rpg : axst := Eval vm_compute in contRP VN.P_grown.
Goal map (fun L => leaf_matches1A NPH L JR_rp) [T_rpk; T_rpg] = [true; true] /\ leaf_matches1A NPH T_rpf JF_rp = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_rp = [(hf_K3, RsCut)] /\ lvs JF_rp = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pG : sv := SVar 348.
Definition g12 : sv := kb 12 pG.
Definition regsK3s : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1S9A2M0S2S1S9U2S84S80A1M1A4S0G0S2S1S9U8S11PaA1A4S0G0S2S1S9U9G1A4S0G0S2S1S9U7S4bA4S0G0S2S1S9U1cS90A4S0G0S2S1S9UfS66A4S0G0S2S1S9U12S54Z2f0A1A4S0G0S2S1S9U13S51Z0A1A4S0G0S2S1S9U14S79A4S0G0S2S1S9U15S79A4S0G0S2S1S9U16S50A4S0G0S2S1S9U17S68A4S0G0S2S1S9U18S3bA4S0G0S2S1S9U19S52A4S0G0S2S1S9U1aS51Z43A1A4S0G0S2S1S9U1bS13A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition regsK3 : list (nat * sv) := ltac2:(tb__ "0|2|
S4S5S1S9A2M0S2aS0G0S2S1S9U5ScS4aS4bScS46S1fSbZ0A1A3A3A4S0G0S2S1S9UaScS46S50S17A3M1A4S0G0S2S1S9UbScS46S13S17A3A4S0G0S2S1S9U10ScS46ScS46S13SbZ8A1A3S17A3A4S0G0S2S1S9U11G1A4S3G0A1A3A3A3A3A3A3").
Definition av_room : sprop := ltac2:(tb__ "0|0|
SeS64ZcS69A2S64Z4S67A2A2").

Definition rp_slot : sprop := ltac2:(tb__ "0|0|
SeScS46S17SbZcA1A3S64Z4S14A2A2").
Definition K3facts : list sprop := ltac2:(tb__ "0|0|
S4SaS0SaS12S1fS4bA2S0SaS35S0SaS43S1fA1S0SaS1eS3SaA1A3A3A3A3S4SaS1bS13S14P15aA3S1cA3A3").
Definition K3 : axst := ltac2:(tb__ "0|1|
S3dS81S21S71S6dS4eS13SbZ0A1M0S14A3S4fS3bG0S3cA3S6fS6eS70S72S73S3eS3S10A1S16S3fS4bA1S13S14S3bS3cSfS4cS4dA8S3SdA1S1dS15S13S14S4cS4dA4A11").
Goal leaf_matches1A NPH (leaf_at JR_rp hf_K3 0) K3 = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition pV : sv := SVar 358.
Definition av_slot : sprop := ltac2:(tb__ "0|1|
SeScS46S64ZcM0S20A2SbG0A1A3S64Z4S67A2A2").
Definition regsK3m : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1S9A2M0S21S0G0S2S1S9UcScS46S66S64ZcS20A2A3A4S3G0A1A3A3").
Definition K3m : axst := ltac2:(tb__ "0|1|
S3dS82S30S71S6dS4eS13SbZ0A1M0S14A3S4fS3bG0S3cA3S6fS6eS70S72S73S3eS3S10A1S16S3fS4bA1S13S14S3bS3cSfS4cS4dA8S3SdA1S0SaS12S20S69A2S0SaS2fS1dA3A3S15S13S14S4cS4dA4A11").
Goal lvs K3 = [(hf_K3m, RsCut)] /\ leaf_matches1A NPH (leaf_at K3 hf_K3m 0) K3m = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition hf_K3x : Z := 0x9f690.
Definition cutpcs_hf5 : list Z := ltac2:(tb__ "0|0|
S4S6cS62S0S6cS28S3S6cA1A3A3").
Definition leaf_at5 (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S8dS7eVk;S8eS55S27VS;Vpc;A4S60A4").
Definition lvs5 (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S7S6S7cA1M0A1S6S5S6cS92A2M1A1Lx;S7fS8fS55S27VS;S8A5G0S8cS7cG1S91R1A4Ll;S3G1A1X7x2").
Definition regsK3x : list (nat * sv) := ltac2:(tb__ "0|1|
S4S5S1S9A2M0S21S0G0S2S1S9UdScS46ScS46S13S17A3SbZ8A1A3A4S3G0A1A3A3").
Definition K3x : axst := ltac2:(tb__ "0|1|
S3dS28S31S71S6dS4eS13SbZ0A1M0S14A3S4fS3bG0S3cA3S6fS6eS70S72S73S3eS3S10A1S16S3fS4bA1S13S14S3bS3cSfS4cS4dA8S3SdA1S1dS15S13S14S4cS4dA4A11").

Goal lvs5 K3m = [(hf_K3x, RsCut); (hf_K3x, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal map (fun L => leaf_matches1A NPH L K3x) (leavesA_at FUEL_hf cutpcs_hf5 K3m hf_K3x) = [true; true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs5 K3x = [(hf_K3, RsCut); (hf_TS, RsCut)] /\ map (fun L => leaf_matches1A NPH L K3) (leavesA_at FUEL_hf cutpcs_hf5 K3x hf_K3) = [true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition TS : axst := ltac2:(tb__ "0|1|
S3dS83S2aS71S6dS4eS13SbZ0A1M0S14A3S4fS3bG0S3cA3S6fS6eS70S72S73S3eS3S10A1S16S3fS4bA1S13S14S3bS3cSfS4cS4dA8S3SdA1S4SaS0SaS1eS3SaA1A3S4SaS1bS13S14P15aA3S1cA3A3S15S13S14S4cS4dA4A11").
Goal map (fun L => leaf_matches1A NPH L TS) (leavesA_at FUEL_hf cutpcs_hf5 K3x hf_TS) = [true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs TS = [(vr_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition M16 : sv := SLit 18446744073709551600. Definition M32 : sv := SLit 18446744073709551584.
Definition needA : sv := ltac2:(tb__ "0|1|
ScS46ScS46ScS47ScS46ScS48S4bSbZ3A1M0A3SbZ1eA1A3S2cA3ScS48S4bSbZ4A1A3A3ScS47ScS46ScS49ScS46S4bSbZ7A1A3G0A3SbZfA1A3S2bA3A3").
Definition need_facts : list sprop := ltac2:(tb__ "0|0|
S0SaSeS1aS64Z25S4bA2A2S0SaSeS1aSbS86A1A2S3SaA1A3A3").
Definition E_ts0 : axst := Eval vm_compute in leaf_at TS vr_entry 0.
Definition a1_ts : sv := Eval vm_compute in nth 11 (ss_regs (ax_S E_ts0)) (SLit 0).
Goal sv_eqb a1_ts needA = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_ts : axst := Eval vm_compute in ax_add_facts need_facts (optAp (apply_axforms E_ts0 (xf_vr 22 816))).
Definition s_ts : wsub := ltac2:(tb__ "0|1|
S0S5S6bS9A2M0S2S6bS9P3bS77S4bA1A4S0G0S2S6bS9P13ScS46S85SbZ40A1A3A4S88PaS7bS23A1S7bS7aA1A3A3A3").
Definition R_ts : list sobj := Eval vm_compute in optR (entails_frA E_ts VN.Pre_vr s_ts).
Goal entails_frA E_ts VN.Pre_vr s_ts = Some R_ts /\ call_checkPA E_ts VN.Pre_vr s_ts R_ts (map fst PD_vn) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition pDts : sv := SVar 350. Definition pKts : sv := SVar 351.
Definition vr_ret_ts : Z := 0x9f78c.
Definition regsT4 (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S1S9A2M0S2S1S9U2S84S80A1M1A4S0G0S2S1S9U8S11PaA1A4S0G0S2S1S9U9G1A4S0G0S2S1S9U1Vra;A4S0G0S2S1S9UaVa0;A4S0G0S2S1S9U12S1aA4S0G0S2S1S9U13S51Z0A1A4S0G0S2S1S9U14S79A4S0G0S2S1S9U15S54Z330A1A4S0G0S2S1S9U16S50A4S0G0S2S1S9U17S68A4S0G0S2S1S9U18S3bA4S0G0S2S1S9U19S52A4S0G0S2S1S9U1aS51Z43A1A4S0G0S2S1S9U1bS13A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition ts_factsJ (dts kts : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|0|
S4SaS0SaSeS1aVkts;A2S0SaSeSbS8bA1Vdts;A2S3SaA1A3A3S4SaS29S53Vdts;Vkts;Z1Vdv;A4A3A3").
Definition rpG : list sprop := ltac2:(tb__ "0|0|
S4SaS0SaS1eS3SaA1A3S4SaS1bS13S14P15aA3S1cA3A3").

Definition JTS (a0 : sv) (facts : list sprop) (tail : list sobj) : axst := ltac2:(tb__ "0|1|
S3dS87S33SbS3aA1Va0;A2S71S6dS4eS13SbZ0A1M0S14A3S4fS3bG0S3cA3S6fS6eS70S72S61S18S19A2S3eS3S10A1S16S3fS4bA1S13S14S3bS3cSfS18S19A8Vtail;S4SaVfacts;S34A3S15S13S14S18S19A4A11").
Definition JR_ts : axst := ltac2:(tb__ "0|0|
S25SbZ1A1S38S18S19P15eA3S0SdS94S6aZ6ZfS3S10A1SfA5S3SdA1A3A3").
Definition JF_ts : axst := ltac2:(tb__ "0|0|
S25SbZ0A1S4SaS29S53S18S19Z1P15eA4A3S3SdA1A3").
Definition reopenX (k1 k2 : Z) (A : axst) : axst := ltac2:(tb__ "0|0|
S93VA;S7dVA;A1S6aVk1;Vk2;A5").
Definition contTS (P : axst) : axst := ltac2:(tb__ "0|0|
S5cS89S8aS7aS23S37S2eVP;S74S4cS15S13S14S4cS4dA4A2A6S75U15U23Z330A3A2A1").
Definition T_tsk : axst := Eval vm_compute in ax_add_facts [SPUle (SLit IMG_HI) ts_d] (contTS VN.P_keep).
Definition T_tsf : axst := Eval vm_compute in contTS VN.P_fail.
Definition T_tsg : axst := Eval vm_compute in contTS VN.P_grown.
Goal map (fun L => leaf_matches1A NPH L JR_ts) [reopenX 6 15 T_tsk; reopenX 6 15 T_tsg] = [true; true] /\ leaf_matches1A NPH T_tsf JF_ts = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_ts = [(memset_pc, RsCut)] /\ lvs JF_ts = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
