(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "app"; "prod"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SLit"; "SPUle"; "cell"; "SAlu"; "sobj"; "DUnknown"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3"; "pKmm"; "pDmm"; "pKsg"; "pDsg"; "fvP1"; "rawF2"; "XMM"; "XSG"; "datasMM"; "datasSG"; "mmP1"; "rawF3"; "regsF3"; "regsF4"; "vr_ret_mm"; "vr_ret_sg"; "E_sg"; "T_sgk"; "XnoL"; "mm_facts"; "sg_facts"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "mm_c"; "pDco"; "xbo"; "sg_c"; "shB"; "vec_facts0"; "cA"; "pKco"; "rp_d"; "rp_k"; "tr_d"; "tr_k"; "ts_d"; "ts_k"; "V560"; "sg_d"; "V592"; "datasF"; "fv_c"; "sg_k"; "V528"; "mm_d"; "pA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "pDfv"; "pKfv"; "FCUT"; "coP"; "miP3"; "pDmi"; "pKmi"; "pX"; "rpP"; "trP"; "tsP"; "X_face"; "sgP"; "NSG"; "T_mmk"; "rawF"; "reopen45X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "hG"; "av_d"; "av_k"; "hF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.VRAddr"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "B32"; "spm"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shobj"; "xlocal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.HFAddr"; "FR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xr_eqb"; "@Stdlib.Lists.List"; "filter"].
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

Definition pDmm : sv := SVar 316. Definition pKmm : sv := SVar 317.
Definition vr_ret_mm : Z := 0x9e5e8.
Definition regsF3 (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S2S8A2M0S1S2S8U2S59S5eA1M1A4S0G0S1S2S8U8SfPaA1A4S0G0S1S2S8U9G1A4S0G0S1S2S8U1Vra;A4S0G0S1S2S8UaVa0;A4S0G0S1S2S8U12S5dA4S0G0S1S2S8U13S28Z230A1A4S0G0S1S2S8U14S28Z238A1A4S0G0S1S2S8U15S2aZ47A1A4S0G0S1S2S8U16S2aZ0A1A4S0G0S1S2S8U17S2aZ3fA1A4S0G0S1S2S8U18S55A4S0G0S1S2S8U19S28Z218A1A4S0G0S1S2S8U1aS28Z210A1A4S0G0S1S2S8U1bS9Z3A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition fvP1 : sobj := ltac2:(tb__ "0|0|
S3aS3dScS25S38S9Z1A1A3S3eA3").
Definition datasMM (dmm kmm : sv) : list sobj := ltac2:(tb__ "0|0|
S37S53S54S42S43S3dS3eVdmm;Vkmm;S35S39S27S2dS2eS2fS30S31S32S33A12").
Definition XMM (dmm kmm : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S48S42S3dVdmm;S35S27S2eS30S32S43S3eVkmm;S39S2dS2fS31S33A10").
Definition mm_facts (dmm kmm : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S4S7S0S7SaScS25S26S9Z1A1A3Vkmm;A2S0S7SaS9S4eA1Vdmm;A2S0S7SaScS25S51Z4M0S26A2S9G0A1A3S51G0Vkmm;A2A2S3S7A1A3A3A3S2bVdmm;Vkmm;G0Vdv;A4A3").

Definition rawF2 : list sprop := ltac2:(tb__ "0|0|
S4S7S0S7SaScS25S38S9Z1A1A3S3eA2S0S7SaS9S4eA1S3dA2S3S7A1A3A3S4S7S2bS3dS3eZ4P13aA4S4cA3A3").
Definition JR_mm : axst := ltac2:(tb__ "0|1|
S3fS56S1cS9S1eA1S9Z1A1A2S44S40S45S46S41S14S34S11S26S10A3S49S47S4SbS2cS0SbS57N88S27A2S3SbA1M0A3A3G0S18S11S10A2S3SdA1S4S7S23S11S10P13cA3S4S7S15S0S7SaS26S9S58A1A2S3S7A1A3A3A3S0S5S8S8A2S5cPa0S1S4fS4fZ20Z4A4A2S16S11S10A2A3A11").
Definition JF_mm : axst := ltac2:(tb__ "0|2|
S3fS56S1cS9S1eA1S9Z0A1A2S44S40S45S46S41S14S34S11S26S10A3S49S47S4SbS2cS0SbS57N88S27A2S3SbA1M0A3A3G0S18S11S10A2S0SdS5bS52Z4M1Z5G0SeA5S3SdA1A3S4S7S0S7SaS26S10A2S3S7A1A3S4S7S2bS11S10G1P13cA4S15A3A3S16S11S10A2A11").
Definition T_mmks : axst := ltac2:(tb__ "0|0|
S5fS0S7SaS9S4eA1S3bA2S3S7A1A3S4bA2").
Goal map (fun L => leaf_matches1A NPH L JR_mm) [T_mmks; T_mmg] = [true; true]
  /\ leaf_matches1A NPH (reopen45X T_mmf (XMM mm_d mm_k)) JF_mm = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_mm = [(vr_entry, RsCut)] /\ lvs JF_mm = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_sg0 : axst := Eval vm_compute in leaf_at JR_mm vr_entry 0.

Definition E_sg : axst := Eval vm_compute in ax_add_facts (vr_need 4 (SAlu ALU_ADD sg_c (SLit 1)) (NSG pA)) (optAp (apply_axforms E_sg0 (xf_vr 18 592))).
Definition s_sg : wsub := ltac2:(tb__ "0|1|
S0S5S50S8A2M0S1S50S8P3bS4aS3cA1A4S0G0S1S50S8P13ScS25S5aS9Z40A1A3A4S63PaS60S20A1S60S62A1A3A3A3").
Definition R_sg : list sobj := Eval vm_compute in optR (entails_frA E_sg VN.Pre_vr s_sg).
Goal entails_frA E_sg VN.Pre_vr s_sg = Some R_sg /\ call_checkPA E_sg VN.Pre_vr s_sg R_sg (map fst PD_vn) = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_sgk0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_sg s_sg R_sg VN.P_keep (XkeepF sg_d (XMM pDmm pKmm)).
Definition T_sgf0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_sg s_sg R_sg VN.P_fail (XkeepF sg_d (XMM pDmm pKmm)).
Definition T_sgg0 : axst := Eval vm_compute in T_afterA3 VN.Pre_vr E_sg s_sg R_sg VN.P_grown (XkeepF sg_d (XMM pDmm pKmm)).
Definition T_sgk : axst := Eval vm_compute in optAp (apply_axforms T_sgk0 (xf_backV 17 31 592)).
Definition T_sgf : axst := Eval vm_compute in optAp (apply_axforms T_sgf0 (xf_backV 17 31 592)).
Definition T_sgg : axst := Eval vm_compute in optAp (apply_axforms T_sgg0 (xf_backV 17 31 592)).

Definition pDsg : sv := SVar 318. Definition pKsg : sv := SVar 319.
Definition vr_ret_sg : Z := 0x9e718.
Definition regsF4 (ra a0 : sv) : list (nat * sv) := ltac2:(tb__ "0|2|
S0S5S2S8A2M0S1S2S8U2S59S5eA1M1A4S0G0S1S2S8U8SfPaA1A4S0G0S1S2S8U9G1A4S0G0S1S2S8U1Vra;A4S0G0S1S2S8UaVa0;A4S0G0S1S2S8U12S5dA4S0G0S1S2S8U13S28Z250A1A4S0G0S1S2S8U14S28Z258A1A4S0G0S1S2S8U15S2aZ4bA1A4S0G0S1S2S8U16S2aZ0A1A4S0G0S1S2S8U17S2aZ3fA1A4S0G0S1S2S8U18S55A4S0G0S1S2S8U19S28Z218A1A4S0G0S1S2S8U1aS28Z210A1A4S0G0S1S2S8U1bS9Z3A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition mmP1 : sobj := ltac2:(tb__ "0|0|
S34S11ScS25S26S9Z1A1A3S10A3").
Definition datasSG (dsg ksg : sv) : list sobj := ltac2:(tb__ "0|0|
S37S53S54S42S43S3dS3eS11S10Vdsg;Vksg;S27S2dS2eS2fS30S31S32S33A12").
Definition XSG (dsg ksg : sv) : list (sv * sv) := ltac2:(tb__ "0|0|
S48S42S3dS11Vdsg;S27S2eS30S32S43S3eS10Vksg;S2dS2fS31S33A10").
Definition sg_facts (dsg ksg : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|1|
S4S7S0S7SaScS25S29S9Z1A1A3Vksg;A2S0S7SaS9S4eA1Vdsg;A2S0S7SaScS25S51Z4M0S29A2S9G0A1A3S51G0Vksg;A2A2S3S7A1A3A3A3S2bVdsg;Vksg;G0Vdv;A4A3").
Definition rawF3 : list sprop := ltac2:(tb__ "0|0|
S4S7S0S7SaScS25S26S9Z1A1A3S10A2S0S7SaS9S4eA1S11A2S3S7A1A3A3S4S7S2bS11S10Z4P13cA4S15A3A3").
Definition JR_sg : axst := ltac2:(tb__ "0|1|
S3fS56S1dS9S1fA1S9Z1A1A2S44S40S45S46S41S14S1aS36S13S29S12A3S47S4SbS2cS0SbS57N88S27A2S3SbA1M0A3A3G0S19S13S12A2S0SdS5bS52Z4Z5G0SeA5S3SdA1A3S4S7S24S13S12P13eA3S4S7S1bS0S7SaS29S9S58A1A2S3S7A1A3A3A3S17S13S12A2A11").
Definition JF_sg : axst := ltac2:(tb__ "0|2|
S3fS56S1dS9S1fA1S9Z0A1A2S44S40S45S46S41S14S1aS36S13S29S12A3S47S4SbS2cS0SbS57N88S27A2S3SbA1M0A3A3G0S19S13S12A2S0SdS5bS52Z4M1Z5G0SeA5S3SdA1A3S4S7S0S7SaS29S12A2S3S7A1A3S4S7S2bS13S12G1P13eA4S1bA3A3S17S13S12A2A11").
Definition T_sgks : axst := ltac2:(tb__ "0|0|
S5fS0S7SaS9S4eA1S35A2S3S7A1A3S21A2").

Definition XnoL (A : axst) : list (sv * sv) := ltac2:(tb__ "0|1|
S65S5S8S8A2M0G0S6S64R1S5cPa0S1S4fS4fZ20Z4A4A2A2A1Lr;S61VA;A1A3").
Definition reopen45n (A : axst) : axst := ltac2:(tb__ "0|0|
S4dVA;S22VA;A1A2").
Goal map (fun L => leaf_matches1A NPH L JR_sg) [reopen45n T_sgks; reopen45n T_sgg] = [true; true] /\ leaf_matches1A NPH (reopen45n T_sgf) JF_sg = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal lvs JR_sg = [(hf_EPI, RsCut)] /\ lvs JF_sg = [(hf_EPI, RsCut); (hf_EPI, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Goal map (fun L => leaf_matches1A NPH L XEo4) (leaves_at2 [JR_sg] hf_EPI) = [true]
  /\ map (fun L => leaf_matches1A NPH L XEf4) (leaves_at2 [JF_mm; JF_sg] hf_EPI) = [true; true; true; true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
