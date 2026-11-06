(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_007.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s3 ns ob.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start7 Start8M StartStates Start3 Start4Fail.

(* [comment removed for export] *)
Module Lib_handle_f_epi.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "app"; "nil"; "nat"; "prod"; "pair"; "None"; "false"; "fst"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "SPUle"; "cell"; "DUnknown"; "FcsrFrm0"; "mkSS"; "ss_objs"; "SLit"; "SVar"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "AXRebase"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "qCUR"; "qERR"; "q_vfacts"; "qKco"; "qKfv"; "qKmi"; "qKmm"; "qKrp"; "qKsg"; "qKtr"; "qKts"; "q_base"; "NZ32"; "qA"; "qDco"; "qDfv"; "qDmi"; "qDmm"; "qDrp"; "qDsg"; "qDtr"; "qDts"; "q_acct"; "datasQ"; "qCfv"; "qCmi"; "qCmm"; "qCsg"; "tvQ"; "XQ"; "bd_face"; "regsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi"; "EC2"; "PC"; "Pre_f5"; "q_baseR"; "E_f5f"; "E_f5o"; "F_mainE"; "NREL"; "P_fail"; "P_ok"; "XQR"; "XR"; "hf_retA"; "ilast"; "nd_fail"; "nd_ok"; "objs_rel"; "regsE2"; "sel_rel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "hG"; "HNEXT"; "O_cE"; "O_cP"; "O_text"; "h_fregs"; "PROG"; "av_d"; "av_k"; "hF"; "h_xregs"; "tE"; "tI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vERR"; "O_al"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pHP"; "O_F"; "O_Wf"; "V496"; "V528"; "V560"; "V592"; "V720"; "V752e"; "V784e"; "V816"; "builderF"; "optAp"; "O_flag"; "O_frame"; "X_hf"; "cVF"; "hdr3"; "hf_facts"; "sel_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "mkA"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shobj"; "shadow_reopen_stateA"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.HFAddr"; "hf_EPI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "post_regs"; "@Stdlib.Lists.List"; "filter"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition hf_retA : Z := 0x9d2f4.

Definition F_mainE : list cell := Eval vm_compute in
  List.filter (fun c => negb (existsb (fun o => sv_eqb (c_off c) (SLit o)) [-136; -144; -176; -240; -216; -248; -184; -256; -192; -232; -208; -200; -264; -224; -280; -336; -344; -320; -328; -352])) F_cells.
Definition regsE2 : list (nat * sv) := ltac2:(tb__ "0|1|
S1S4S3SdA2M0S3bS0G0S5S3SdU12S15P164A1A4S2G0A1A3A3").
Definition EC2 (err : sv) (facts : list sprop) (sh : list sobj) : axst := ltac2:(tb__ "0|1|
S7bS12S85S5fS53A1S5aS11S6SdA1S1SbS0SbS66S0SbS72S75A1S0SbS71S2SbA1M0A3A3A3S1SbS7aS1SbS0SbS65S48A1G0A3S1SbS6fVerr;S64S6bS2aS29S1fA3S6cS2eS23A2S6dS30S25A2S67S2cS35S21A3S68S2bS34S20A3S69S2dS36S22A3S6aS2fS37S24A3S6eS31S26A2AaS1SbS0SbS63S0SbS58S1cA1S0SbS57S0SbS59G0A3A3A3A3S1SbS33Vsh;A3A3A3A3A3A3Vfacts;S56S7A9S39A2").
Definition C_Eo2 : axst := ltac2:(tb__ "0|0|
S42S62S1ScS32S1ScS1eS27A3A3S2SbA1A3").
Definition C_Ef2 : axst := ltac2:(tb__ "0|0|
S42S1dS1ScS0ScS28S1dA1S2ScA1A3S1ScS1eS27A3A3S2SbA1A3").

Definition XEo42 : axst := ltac2:(tb__ "0|0|
S42S62S1ScS32S1ScS1eS27A3A3S0SbS80S55Z4Z5S2SfA1S10A5S2SbA1A3A3").
Definition XEf42 : axst := ltac2:(tb__ "0|0|
S42S1dS1ScS0ScS28S1dA1S2ScA1A3S1ScS1eS27A3A3S0SbS80S55Z4Z5S2SfA1S10A5S2SbA1A3A3").

Goal map (fun L => leaf_matches1A NPH L C_Eo2) (leaves_at2 [T_dg] hf_EPI) = [true]
  /\ map (fun L => leaf_matches1A NPH L C_Ef2) (leaves_at2 [JF_co; K; JF_mi] hf_EPI) = [true; true; true; true; true; true]
  /\ map (fun L => leaf_matches1A NPH L XEf42) (leaves_at2 [JF_fv; JF_mm; JF_sg] hf_EPI) = [true; true; true; true; true; true]
  /\ map (fun L => leaf_matches1A NPH L XEo42) (leaves_at2 [JR_sg] hf_EPI) = [true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Goal lvs C_Eo2 = [(f5_pc, RsCut)] /\ lvs C_Ef2 = [(f5_pc, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E_f5o0 : axst := Eval vm_compute in leaf_at C_Eo2 f5_pc 0.
Definition E_f5f0 : axst := Eval vm_compute in leaf_at C_Ef2 f5_pc 0.
Definition Pre_f5 : axst := Pre_set_shadow AE_A 245.
Definition L_f5 : axst := L_set_shadow 245.

Definition XR (A : axst) : list (sv * sv) := ltac2:(tb__ "0|1|
S88S4SdSdA2M0G0SaS16S8SdSdR1A3S5eA2A1Lr;S3eVA;A1A3").
Definition ilast (A : axst) : nat := ltac2:(tb__ "0|0|
S82S9SbS13S3cVA;A1A1A2U1A2").
Definition f5_site (E0 : axst) : axst := ltac2:(tb__ "0|0|
S81VE0;S4dVE0;A1S55Z0Z40A5S3dS70S19R1S0S17S1bS4fR1A1S7cA2S2S17A1A3A2A1TE1;").
Definition E_f5o : axst := Eval vm_compute in f5_site E_f5o0.
Definition E_f5f : axst := Eval vm_compute in f5_site E_f5f0.
Definition s_f5o : wsub := ltac2:(tb__ "0|0|
S0S4S40SdA2S5S40SdPfS7dA4S7ePaS3cS47A1S3cS44A1A3A3").
Definition s_f5f : wsub := ltac2:(tb__ "0|0|
S0S4S40SdA2S5S40SdPfS7dA4S7ePaS3cS46A1S3cS44A1A3A3").
Definition R_f5o : list sobj := Eval vm_compute in optR (entails_frA E_f5o Pre_f5 s_f5o).
Definition R_f5f : list sobj := Eval vm_compute in optR (entails_frA E_f5f Pre_f5 s_f5f).
Goal entails_frA E_f5o Pre_f5 s_f5o = Some R_f5o /\ call_checkPA E_f5o Pre_f5 s_f5o R_f5o [L_f5] = true
  /\ entails_frA E_f5f Pre_f5 s_f5f = Some R_f5f /\ call_checkPA E_f5f Pre_f5 s_f5f R_f5f [L_f5] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition xf_shback (A : axst) : list axform := ltac2:(tb__ "0|1|
S0S17S1aU1M0A1S0S17S18S77VA;G0A2A1S2S17A1A3A3").
Definition T_f5o0 : axst := Eval vm_compute in T_afterA Pre_f5 E_f5o s_f5o R_f5o L_f5.
Definition T_f5f0 : axst := Eval vm_compute in T_afterA Pre_f5 E_f5f s_f5f R_f5f L_f5.
Definition T_f5o : axst := Eval vm_compute in flag_carve_stateA (optAp (apply_axforms T_f5o0 (xf_shback T_f5o0))) 170.
Definition T_f5f : axst := Eval vm_compute in flag_carve_stateA (optAp (apply_axforms T_f5f0 (xf_shback T_f5f0))) 170.
Goal lvs T_f5o = [(hf_REL, RsCut)] /\ lvs T_f5f = [(hf_REL, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_rlo : axst := Eval vm_compute in leaf_at T_f5o hf_REL 0.
Definition X_rlf : axst := Eval vm_compute in leaf_at T_f5f hf_REL 0.
Definition sel_rel : list nat := ltac2:(tb__ "0|1|
S1S3S0S3U0S0S3U1S0S3U2S2S3A1M0A3A3A3S1S3S84U5U1fA2S0S3U3S0S3U4S0S3U24S0S3U25G0A3A3A3A3A3A3").
Definition NREL : nat := 34%nat.
Definition rel_state (X : axst) : axst := ltac2:(tb__ "0|1|
S70S19VX;S0S17S18S54A1S2S17A1A3A2A1S3dS3fR1S86S3cR1A1M0S83SbS49S13G0A1A3A2A2TX1;").
Definition C_rlo : axst := Eval vm_compute in rel_state X_rlo.
Definition C_rlf : axst := Eval vm_compute in rel_state X_rlf.
Goal map (fun X => release_objs_ok 160 170 hG 3 (skipn NREL (ss_objs (ax_S (optAp (apply_axforms X [AXSelect sel_rel])))))) [X_rlo; X_rlf] = [true; true]
  /\ map (fun A => length (ss_objs (ax_S A))) [C_rlo; C_rlf] = [NREL; NREL]
  /\ lvs C_rlo = [(hf_retA, RsSymJump)] /\ lvs C_rlf = [(hf_retA, RsSymJump)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition X_reto : axst := Eval vm_compute in leaf_at C_rlo hf_retA 0.
Definition X_retf : axst := Eval vm_compute in leaf_at C_rlf hf_retA 0.

Definition XQR : list (sv * sv) := ltac2:(tb__ "0|0|
S73S5cS2cS2bS2dS2fS2aS2eS30S31S5dS21S20S22S24S1fS23S25S26A12").
Definition objs_rel (err : sv) : list sobj := ltac2:(tb__ "0|1|
S1SbS0SbS66S2SbA1M0A3S1SbS7aS1SbS0SbS65S2SfA1A1G0A3S1SbS6fVerr;S64S6bS2aS29S1fA3S6cS2eS23A2S6dS30S25A2S67S2cS35S21A3S68S2bS34S20A3S69S2dS36S22A3S6aS2fS37S24A3S6eS31S26A2AaS1SbS0SbS63S0SbS58S1cA1S0SbS57S0SbS59G0A3A3A3A3S33A3A3A3A3A3").
Definition q_baseR : list sprop := ltac2:(tb__ "0|0|
S1ScS0ScSeS64S14Z1A1A2S0ScSeS61S1cA2S0ScSeS1cS60A2S2ScA1A3A3A3S76A3").
Definition PC (err : sv) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S7bS12S4eS87P190A1S5aS11S6SdA1S52Verr;A1Vfacts;S56S7A9S4cA2").
Definition P_ok : axst := ltac2:(tb__ "0|0|
S43S62S1ScS32S1ScS1eS45A3A3A2").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S43S1dS1ScS0ScS28S1dA1S2ScA1A3S1ScS1eS45A3A3A2").
Definition nd_ok : ndesc := ltac2:(tb__ "0|0|
S79S38S2S4S4SdS41A2SdA2A1S3aS1cS29S21S20S22S24S1fS23S25S26AaA3").
Definition nd_fail : ndesc := ltac2:(tb__ "0|0|
S79S38S2S4S4SdS41A2SdA2A1S0S7fS5bS74S1cA2S2S7fA1A3A3").
Definition Posts_hf : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S4S3dS78A2M0S5S3dS78S4aS50A4S0G0S5S3dS78S4bS51A4S2G0A1A3A3").
Goal leaf_matches1A NPH X_reto P_ok = true /\ leaf_matches1A NPH X_retf P_fail = true /\ leaf_matches1A NPH X_reto P_fail = false.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_handle_f_epi.

(* [comment removed for export] *)
Module Lib_build_line_index_rom.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "prod"; "app"; "None"; "false"; "list"; "option"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "cell"; "SVar"; "SAlu"; "sobj"; "SPBranch"; "DUnknown"; "mkObj"; "FcsrFrm0"; "SPAlign"; "mkSS"; "SMd"; "SPNot"; "valuation"; "SPEq"; "reg_sv"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom"; "c8"; "vDp"; "spm"; "vC"; "vK"; "vDt"; "KLG"; "PHI"; "two47"; "B32"; "Pre_vr"; "tv0"; "vUD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_build_line_index_rom"; "pD"; "pK"; "vLEN"; "pC"; "pJ"; "vOUT"; "X_bli"; "pI"; "vALC"; "vBUF"; "kb16"; "nd_pre"; "pG"; "VL"; "XL0n"; "bli_facts"; "canon"; "ndB"; "vecL_facts"; "tvB"; "z0"; "LS"; "PROGL"; "P_ret_S"; "Pre_blr"; "ra_vr"; "shOf"; "C_LI"; "FEo"; "FUEL_blr"; "F_cells"; "HNEXT"; "K_ok_S0"; "P_retL_S"; "bdL"; "cutpcs_blr"; "loop_regs"; "ndPE"; "ndPL"; "ok_facts"; "pNX"; "slot_facts"; "C_LI_S"; "C_z"; "E_vr"; "E_vr_S"; "E_vrx"; "K_ok"; "K_ok_S"; "K_st"; "K_st_S"; "O_D"; "O_F"; "O_al"; "O_txt"; "O_vec16"; "P_retL0"; "P_retL1"; "Pre_blr_S"; "T_fail"; "T_grown"; "T_keep"; "VZ"; "Vs"; "XL0"; "XR0a"; "XR0b"; "X_st"; "bdS"; "g8"; "hx"; "loop_facts"; "ndF"; "ndS"; "rvR"; "slot_obj"; "st_facts"; "vIz"; "vKg"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_LTU"; "BC_EQ"; "BC_GE"; "M_MUL"; "ALU_XOR"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "ASv"; "BI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "SHB"; "A_globals"; "leavesA_at"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_build_line_index_rom.BLRAddr"; "FR"; "bli_LI"; "bli_ST"; "bli_ret"; "bli_entry"; "memset_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "NF"; "setregs"; "post_regs"; "pre_regs"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom.VRRAddr"; "vr_entry"; "vr_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Corelib.Init.Logic"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom.RR.RRAddr"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase CellTile ArrMat.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM TobjJAR TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ns.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Module RV. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_vec_reserve_rom. End RV.
Module RVP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Lib_vec_reserve_rom_pf. End RVP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRRAddr RR.RRAddr.

Module BLRAddr.
  Definition bli_entry : Z := 0x8ffe0.
  Definition bli_LI : Z := 0x90124.
  Definition bli_rr : Z := 0x90180.
  Definition bli_z : Z := 0x901dc.
  Definition bli_ST : Z := 0x90278.
  Definition bli_ret : Z := 0x90320.
  Definition memset_pc : Z := 0x901dc.
  Definition FR : Z := 128.
End BLRAddr.
Import BLRAddr.

Definition FUEL_blr : nat := 500%nat.
Definition vBUF : sv := SVar 12. Definition vLEN : sv := SVar 13. Definition vOUT : sv := SVar 14. Definition vALC : sv := SVar 33.

Definition kb16 (k : sv) : sv := SMd M_MUL (SLit 16) k.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S11PaA1SeS9fSa1A1A1SeZ0A1Vcells;S15A5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S16S25Sa1A1S24SeZ0A1S3S10A1S15A5").
Definition O_vec16 (d c k : sv) : sobj := ltac2:(tb__ "0|2|
S16S3aSeZ0M0A1SeZ20A1S0S10S23G0Vd;A2S0S10S23Z8Vc;A2S0S10S23Z10M1Vk;A2S0S10S23Z18SeG1A1A2S3S10A1A3A3A3A3S15A5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S16S3dSeZ0M0A1M1SeZ30A1S0S10S23G0SeSb5A1A2S0S10S23Z8SeSb6A1A2S0S10S23Z10G1A2S0S10S23Z18SeSb7A1A2S0S10S23Z20G1A2S0S10S23Z28S2fA2S3S10A1A3A3A3A3A3A3S15A5").
Definition O_txt : sobj := ltac2:(tb__ "0|0|
S16S3eSeZ0A1S37S3S10A1S15A5").

Definition vecL_facts (d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|3|
S0SdS18Vdv;Z4A2S0SdSfVd;S11P1eA1M0A2S0SdSfS12S84Vd;S3fVk;A1M1A3G0A2S0SdSfVd;SeS2bA1A2S0SdSfVc;Vk;A2S0SdSfVk;SeS2cA1M2A2S0SdSfG1G2A2S3SdA1A3A3A3A3A3A3A3").
Definition bli_facts : list sprop := ltac2:(tb__ "0|b|
S0SdS18PaM0Z4M1A2S0SdSfS11G0A1M2SeS2bA1M3A2S0SdSfS11P1eA1M4S12S84S25Sa1A1M5S24A3A2S0SdSfG4S25S9eS9eSa1Z40A2Z1060A2A1A2S0SdSfG4G5A2S0SdSfG4G2A2S0SdS14S88SeN10a0A1S24A3S0SdS14S88S24SeS9fS9dZ2M6Z26A2A1A1A3S0SdS18PeZ3M7A2S0SdSfG2S3aA2S0SdSfS12S84S3aSeZ20A1A3G3A2S0SdSfS3aG3A2S0SdS18P21G7A2S0SdSfSeZ1000A1M8S3dA2S0SdSfS12S84S3dSeZ30A1A3G4A2S0SdSfS3dG3A2S0SdS18PcG1A2S0SdSfG8S3eA2S0SdSfS12S84S3eS37A3SeZ7fffff800000A1M9A2S0SdSfS3eG9A2S0SdSfS37SeS9dG6Z1aA2A1A2S0SdSfSeZ7fff7f800000A1MaG4A2S0SdSfG4G9A2S0SdSfGaG2A2S3SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X_bli (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4ScScA2M0S1ScScS3aSeZ20A1A4S0G0S1ScScS3dSeZ30A1A4S0G0S1ScScS3eS37A4S0G0S1ScScVd;S3fVk;A1A4S3G0A1A3A3A3A3").

Definition canon (fcells : list cell) (d c k : sv) : list sobj := ltac2:(tb__ "0|0|
S5S13S0S13S69Vfcells;A1S0S13S68S0S13S6cVd;Vc;Vk;A3S0S13S6aS0S13S6bS3S13A1A3A3A3A3A3S95A3").
Definition Pre_blr_S : sstate := ltac2:(tb__ "0|0|
S19Sa5SabSa7S17S6ScA1S45S3S10A1S28S26S27A4S5SdS0SdSfS26SeZ0A1A2S3SdA1A3S5SdS47S28S26S27PfA4S44A3A3Sa8S7A9").
Definition Pre_blr : axst := ltac2:(tb__ "0|0|
S93S6fS3bS28S27A2A2").

Definition cutpcs_blr : list Z := ltac2:(tb__ "0|0|
S0S20Sa2S0S20Sb0S0S20Sa6S0S20Sa3S3S20A1A3A3A3A3").
Definition optAb (x : option axst) : axst := match x with Some s => s | None => Pre_blr end.
Definition optSb (x : option sstate) : sstate := match x with Some s => s | None => Pre_blr_S end.
Definition leavesB (S : axst) : list axst := ltac2:(tb__ "0|1|
S9S8S32A1M0A1S8S30A1Lx;S34S97S52S58VS;SbA5G0SacS32S30S33R1A4Lls;S3S30A1X9x2").
Definition leafB_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
SadS30Vk;S96S52S58VS;Vpc;A4S4dA4").

Definition hx (r : nat) : sv := SVar (Pos.of_nat (200 + r)).
Definition pD : sv := SVar 280. Definition pC : sv := SVar 281. Definition pK : sv := SVar 282.
Definition pI : sv := SVar 283. Definition pJ : sv := SVar 284. Definition pG : sv := SVar 288. Definition pNX : sv := SVar 290.
Definition HNEXT : positive := 300.
Definition g8 (g : sv) : sv := SAlu ALU_SLL g (SLit 3).
Definition FEo (g : sv) : list sprop := ltac2:(tb__ "0|1|
S0SdS1dS7aVg;A1M0S3aA2S0SdSfVg;SeSa0S9dZ2Z3dA2Z1A2A1A2S0SdSfG0S3aA2S0SdSfS3aG0A2S3SdA1A3A3A3A3").
Definition shOf (g : sv) (k : Z) : sv := ltac2:(tb__ "0|0|
S12S84Vg;SeS9eS94Vk;A2A1A3").
Definition F_cells (g : sv) : list cell := ltac2:(tb__ "0|0|
S0S10S23N80S4fVg;Z3A2A2S0S10S23N78S4fVg;Z0A2A2S0S10S23N70S3dA2S0S10S23N68S11P2fA1A2S0S10S23N60S11P2eA1A2S0S10S23N58S11P2dA1A2S0S10S23N50S11P2cA1A2S0S10S23N48S11P2bA1A2S0S10S23N40S11P2aA1A2S0S10S23N38S11P29A1A2S0S10S23N30S11P28A1A2S0S10S23N28S11P27A1A2S0S10S23N20S11P26A1A2S0S10S23N18S11P1dA1A2S0S10S23N10S11P1cA1A2S0S10S23N8S11PbA1A2S3S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition loop_regs (g i j : sv) (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|2|
Sa9SacS2ScS7bSaeU0M0U20A2A4S5S4S2ScA2M1S0G1S1S2ScG0SeZ0A1A4S0G1S1S2ScU2S25Sa1A1A4S0G1S1S2ScU3S11P17A1A4S0G1S1S2ScU4S11P18A1A4S0G1S1S2ScU8S37A4S0G1S1S2ScU9S3eA4S0G1S1S2ScU12S3aA4S0G1S1S2ScU13Vi;A4S0G1S1S2ScU14S4fVg;Z1A2A4S0G1S1S2ScU15S12S84S3aSeZ8A1A3A4S0G1S1S2ScU16S12S84S3aSeZ18A1A3A4S0G1S1S2ScU17SeS94A1A4S0G1S1S2ScU18S12S8aS3eSeZffffffffffffffffA1A3A4S0G1S1S2ScU19Vj;A4S0G1S1S2ScU1aSeZaA1A4S0G1S1S2ScU1bSeZdA1A4S3G1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").

Definition PROGL (p : sv) : bitem := ltac2:(tb__ "0|2|
S92Z60Z0M0S0S4S20S90A2M1S1S20S90Z1S91S37A1A4S0G1S1S20S90N1S91Vp;A1A4S3G1A1A3A3G0A4").
Definition bdL (i c k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S8fS2aS12S84Vc;SeZ1A1A3Vk;A2S0S8fS29Vk;A1S0S8fS4bVi;A1S3S8fA1A3A3A3").
Definition loop_facts (i j c : sv) : list sprop := ltac2:(tb__ "0|0|
S0SdSfS5dVi;A2S0SdSfVi;Vj;A2S0SdSfVc;Vi;A2S0SdS14S86Vi;S37A3S0SdSfVj;SeS9dZ2Z1aA2A1A2S3SdA1A3A3A3A3A3").
Definition LS (pc : Z) (g i j : sv) (regs : list (nat * sv)) (d c k : sv) (dv : positive) (facts : list sprop) : sstate := ltac2:(tb__ "0|0|
S19Vpc;S59Vg;Vi;Vj;Vregs;A4Sa7S17S6ScA1S45S53Vg;A1Vd;Vc;Vk;A4S5SdVfacts;S5SdS7cVi;Vj;Vc;A3S5SdS51Vg;A1S5SdS47Vd;Vc;Vk;Vdv;A4S44A3A3A3A3S54S7A9").
Definition C_LI_S : sstate := ltac2:(tb__ "0|0|
S4aSa2S41S3cS39S3S4S2ScA2A1S35S38S36P118S0SdS14S86S39S37A3S3SdA1A3Aa").
Definition C_LI : axst := ltac2:(tb__ "0|0|
S93S5fS3bS35S36A2A2").

Definition XL0 : list axst := Eval vm_compute in leavesA_at FUEL_blr cutpcs_blr Pre_blr bli_LI.
Definition XR0 : list axst := Eval vm_compute in leavesA_at FUEL_blr cutpcs_blr Pre_blr bli_ret.

Definition s_L0 (X : axst) : wsub := ltac2:(tb__ "0|0|
S0S4S21ScA2S1S21ScP122SeZ0A1A4SafSa8S31VX;A1S31S50A1A3A3").

Definition ra_vr : Z := 0x90180.
Definition E_vr_S : sstate := ltac2:(tb__ "0|1|
S4aSb0S41S3cS39S0S4S2ScA2M0S1S2ScU1SeS4eA1A4S0G0S1S2ScUaS3aA4S0G0S1S2ScUbS12S84S38SeZ1A1A3A4S0G0S1S2ScUcS3dA4S3G0A1A3A3A3A3S35S38S36P118S0SdSfS39S37A2S3SdA1A3Aa").
Definition E_vr : axst := ltac2:(tb__ "0|0|
S93S62S3bS35S36A2A2").

Definition xf_vcall : list axform := ltac2:(tb__ "0|2|
S0S98S9cU1M0SeN40M1A1A2S0S98S99G0G1A2S3S98A1A3A3").
Definition E_vrx : axst := Eval vm_compute in optAb (apply_axforms E_vr xf_vcall).
Definition s_v : wsub := ltac2:(tb__ "0|0|
S0S4S21ScA2S1S21ScP13S12S84S24SeZ40A1A3A4SafPaS31S63A1S31S2dA1A3A3").
Definition R_v : list sobj := Eval vm_compute in optR (entails_frA E_vrx Pre_vr s_v).
Definition PD_vrr : list pdescK := RVP.PDk_vrr.
Definition Xk_v : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4ScScA2M0S1ScScS3aSeZ20A1A4S0G0S1ScScS3dSeZ30A1A4S0G0S1ScScS3eS37A4S3G0A1A3A3A3").
Definition T_keep0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrx s_v R_v P_keep Xk_v.
Definition T_fail0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrx s_v R_v P_fail Xk_v.
Definition T_grown0 : axst := Eval vm_compute in T_afterA3 Pre_vr E_vrx s_v R_v P_grown Xk_v.

Definition xf_vback : list axform := ltac2:(tb__ "0|1|
S0S98S99U1M0Z40A2S0S98S9bS0S2U6S0S2G0S0S2U0S0S2U2S0S2U3S0S2U7S0S2U4S0S2U5S3S2A1A3A3A3A3A3A3A3A3A1S0S98S9aG0A1S3S98A1A3A3A3").
Definition T_keep : axst := Eval vm_compute in optAb (apply_axforms T_keep0 xf_vback).
Definition T_fail : axst := Eval vm_compute in optAb (apply_axforms T_fail0 xf_vback).
Definition T_grown : axst := Eval vm_compute in optAb (apply_axforms T_grown0 xf_vback).

Definition slot_obj (d c : sv) : sobj := ltac2:(tb__ "0|0|
S16S12S84Vd;S3fVc;A1A3SeZ0A1SeZ10A1S3S10A1S15A5").
Definition slot_facts (c k : sv) : list sprop := ltac2:(tb__ "0|2|
S0SdSfS12S84S3fVc;A1M0SeZ10A1A3S3fVk;A1M1A2S0SdSfG0G1A2S3SdA1A3A3").
Definition ok_facts (d c k : sv) : list sprop := ltac2:(tb__ "0|0|
S5SdS0SdSfS12S84Vc;SeZ1A1A3Vk;A2S0SdSfSeSb3A1Vd;A2S0SdS1bS14S87Vd;SeZ0A1A3A1S3SdA1A3A3A3S5eVc;Vk;A2A3").
Definition K_ok_S0 : sstate := ltac2:(tb__ "0|1|
S4aSb1S41S3cS39S0S4S2ScA2M0S1S2ScU1SeS4eA1A4S0G0S1S2ScUaSeZ1A1A4S3G0A1A3A3S35S38S36P118S5SdS5cS35S38S36A3S0SdSfS39S37A2S3SdA1A3A3Aa").
Definition K_ok_S : sstate := ltac2:(tb__ "0|0|
Sb8S55S5S13S1fS55A1S0S13S80S35S38A2S3S13A1A3A3A2").
Definition K_ok : axst := ltac2:(tb__ "0|0|
S93S65S3bS35S36A2A2").
Definition T_keepF : axst := ltac2:(tb__ "0|0|
Sb2S5cS35S38S36A3S72A2").
Definition vDg : sv := SVar 340. Definition vKg : sv := SVar 341.
Definition T_grownF : axst := ltac2:(tb__ "0|0|
Sb2S5eS38S83A2S71A2").
Definition T_keepC : axst := Eval vm_compute in carve_stateA T_keepF (SAlu ALU_ADD pD (kb16 pC)) (SLit 16).
Definition T_grownC : axst := Eval vm_compute in carve_stateA T_grownF (SAlu ALU_ADD vDg (kb16 pC)) (SLit 16).
Definition s_keep : wsub := Eval vm_compute in infer_sub NF (ax_S T_keepC) (ax_S K_ok).
Definition s_grown : wsub := Eval vm_compute in infer_sub NF (ax_S T_grownC) (ax_S K_ok).

Definition E_ms0 : axst := Eval vm_compute in leafB_at K_ok memset_pc 0.

Definition C_z : axst := Eval vm_compute in bl_cut E_ms0 13 (SLit 16) [11; 15; 16]%nat [].
Definition vIz : sv := Eval vm_compute in reg_sv (ax_S C_z) 13.
Definition X_st : axst := Eval vm_compute in leafB_at C_z bli_ST 0.
Definition sel_st : list nat := ltac2:(tb__ "0|0|
S0S2U0S0S2U1S0S2U2S0S2U3S0S2U4S0S2U5S0S2U6S0S2U7S3S2A1A3A3A3A3A3A3A3A3").
Definition X_stS : axst := Eval vm_compute in optAb (apply_axforms X_st [AXSelect sel_st]).
Definition X_stA : axst := Eval vm_compute in drop_lastA X_stS (removelast (ss_objs (ax_S X_stS))).
Definition st_facts : list sprop := ltac2:(tb__ "0|1|
S0SdSfS5dS12S84S39SeZ1A1A3M0A2S0SdSfS38G0A2S0SdSfS38S37A2S0SdSfS3cS39A2S0SdSfS3cS37A2S0SdS14S86S3cS37A3S0SdSfS39S37A2S0SdSfS39SeS9dZ2Z1aA2A1A2S0SdSfSeSb3A1S35A2S0SdS1bS14S87S35SeZ0A1A3A1S3SdA1A3A3A3A3A3A3A3A3A3A3").
Definition K_st_S : sstate := ltac2:(tb__ "0|1|
S19Sa3S59S41S3cS39S0S4S2ScA2M0S1S2ScU1SeS4eA1A4S3G0A1A3A4Sa7S17S6ScA1S45S53S41A1S35S38S36A4S5SdS81S5SdS51S41A1S5SdS47S35S38S36P118A4S44A3A3A3S54S7A9").
Definition K_st : axst := ltac2:(tb__ "0|0|
S93S67S3bS35S36A2A2").
Definition s_st : wsub := Eval vm_compute in (281%positive, SAlu ALU_ADD pC (SLit 1)) :: (290%positive, SAlu ALU_ADD pJ (SLit 1)) :: infer_sub NF (ax_S X_stA) (ax_S K_st).

Definition bdS (i c k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S8fS2aVc;Vk;A2S0S8fS29Vk;A1S0S8fS4bVi;A1S3S8fA1A3A3A3").

Definition P_ret_S (rv : Z) : sstate := ltac2:(tb__ "0|5|
S19Sa4Sa9SaaSa8A1S0S4S2ScA2M0S1S2ScUaSeVrv;A1A4S3G0A1A3A2Sa7S17S6ScA1S45S3S10A1S11P8cM1A1M2S11P8dA1M3S11P8eA1M4A4S5SdS0SdSfG3S37A2S3SdA1A3S5SdS47G2G3G4G1A4S44A3A3P90S7A9").
Definition P_ret1 : axst := ltac2:(tb__ "0|0|
S93S4cZ1A1S3bS11P8cA1S11P8eA1A2A2").
Definition P_ret0 : axst := ltac2:(tb__ "0|0|
S93S4cZ0A1S3bS11P8cA1S11P8eA1A2A2").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4ScScA2M0S1ScScS11P8cA1S3fS11P8eA1A1A4S3G0A1A3").
Definition tvB (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4ScScA2M0S1ScScVd;S3fVk;A1A4S3G0A1A3").

Definition P_retL_S (rv : Z) : sstate := ltac2:(tb__ "0|1|
S19Sa4Sa9SaaP190A1S0S4S2ScA2M0S1S2ScUaSeVrv;A1A4S3G0A1A3A2Sa7S17S6ScA1S45S3S10A1S35S38S36A4S5SdS0SdSfS38S37A2S3SdA1A3S5SdS47S35S38S36P118A4S44A3A3P1b0S7A9").
Definition P_retL1 : axst := ltac2:(tb__ "0|0|
S93S56Z1A1S3bS35S36A2A2").
Definition P_retL0 : axst := ltac2:(tb__ "0|0|
S93S56Z0A1S3bS35S36A2A2").
Definition s_retL (rv : Z) : wsub := Eval vm_compute in infer_sub NF (ax_S (mkA (P_retL_S rv) (X_bli pD pK))) (ax_S (mkA (P_ret_S rv) (X_bli (SVar 140) (SVar 142)))).
Definition XR0a : axst := Eval vm_compute in nth 0 XR0 Pre_blr.
Definition XR0b : axst := Eval vm_compute in nth 1 XR0 Pre_blr.
Definition rvR (X : axst) : Z := ltac2:(tb__ "0|4|
ScS20Lx;S1eS31VX;A1ZaA2S20R1Lz;S21Z1M0Li;S8bScScG0Lb;La;M1Lop;M2G2S8cG1Lop;M3G3SaS22ScG0La;Lw;Lsgn;S21ScS20G0Lk;Li;Ll;Xcx8").
Definition s_retE (X : axst) : wsub := ltac2:(tb__ "0|0|
SafSa8S31VX;A1S31S93S4cS7fVX;A1A1S3bS11P8cA1S11P8eA1A2A2A1A3").

Definition nd_pre : ndesc := ltac2:(tb__ "0|0|
S8eS2eS3S4S4ScS20A2ScA2A1S57SeZ0A1S26S27A3A3").
Definition ndB : ndesc := ltac2:(tb__ "0|0|
S8eS48S35S36A2S3S4S4ScS20A2ScA2A1S57S3cS38S36A3A3").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S8eS48S35S36A2S3S4S4ScS20A2ScA2A1S79S3cS38S36A3A3").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S8eS48S35S36A2S3S4S4ScS20A2ScA2A1S0S8fS4bS3cA1S3S8fA1A3A3").
Definition ndP : ndesc := ND tvP [] [].
Definition ndPL : ndesc := ltac2:(tb__ "0|0|
S8eS48S35S36A2S3S4S4ScS20A2ScA2A1S3S8fA1A3").
Definition ndPE : ndesc := ND tv0 [] [].
Definition z0 : sv := SLit 0.

Definition VL (j : sv) (ph : Z) : sv := ltac2:(tb__ "0|0|
S12S84S1aS89SeZ40A1S12S85S12S84SeS9eS9dZ2Z1aA2Z10A2A1S37A3Vj;A3A3SeVph;A1A3").

Definition VZ (j i : sv) : sv := ltac2:(tb__ "0|1|
S12S84S1aS89SeZ40A1S12S85S12S84SeS9eS9dZ2Z1aM0A2Z10A2A1S37A3Vj;A3A3S12S85SeG0A1Vi;A3A3").

Definition Vs : list (list positive) := ltac2:(tb__ "0|2|
S0S8S21A1M0S3S21A1M1S0G0S0S21P119S0S21P118S0S21P122S0S21P11aG1A3A3A3A3S3G0A1A3A3").
Definition PhisV : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|2|
SacS8S21A1M0S4G0S1cOF_;M1A2G0S1G0G1R1S1cSb4L_;A4LV;S74A4").
Definition XL0n (k : nat) : axst := ltac2:(tb__ "0|0|
SadS30Vk;S75S4dA4").
Definition cutsE : list efnode := ltac2:(tb__ "0|6|
S0S4S4S4S30S8dA2M0S2A2M1S4S20ScA2M2A2M3S1G1G2S1G0S2S1S30S8dS4dS40A4U0A4S1S20ScZ64S49A4A4S0G3S1G1G2S1G0S2S1S30S8dS50S46A4U1M4A4S1S20ScZ32M5S42S39Z3cA2A4A4S0G3S1G1G2S1G0S2S1S30S8dS64S46A4G4A4S1S20ScG5S42S39Z28A2A4A4S0G3S1G1G2S1G0S2S1S30S8dS70S7dA4G4A4S1S20ScZ2dS49A4A4S0G3S1G1G2S1G0S2S1S30S8dS60S46A4G4A4S1S20ScG5S73S39S82A2A4A4S0G3S1G1G2S1G0S2S1S30S8dS66S7eA4G4A4S1S20ScG5S42S39Z0A2A4A4S3G3A1A3A3A3A3A3A3").
Definition exitsE : list efnode := ltac2:(tb__ "0|9|
S0S4S4S4S30S8dA2M0S2A2M1S4S20ScA2M2A2M3S1G1G2S1G0S2S1S30S8dS43U0M4A1S40A4G4A4S1S20ScZ5aS49A4M5A4S0G3S1G1G2S1G0S2S1S30S8dS43U1M6A1S40A4G4A4G5A4S0G3S1G1G2S1G0S2S1S30S8dS43U2A1S40A4G4A4G5A4S0G3S1G1G2S1G0S2S1S30S8dS43U3A1S40A4G4A4G5A4S0G3S1G1G2S1G0S2S1S30S8dS43U4A1S40A4G4A4G5A4S0G3S1G1G2S1G0S2S1S30S8dS76S5aA4G4A4S1S20ScZ0S49A4M7A4S0G3S1G1G2S1G0S2S1S30S8dS77S5aA4G4A4G7A4S0G3S1G1G2S1G0S2S1S30S8dS61S46A4G6A4S1S20ScZ32M8S42S39G8A2A4A4S0G3S1G1G2S1G0S2S1S30S8dS78S46A4G6A4S1S20ScG8S42S39Z5A2A4A4S0G3S1G1G2S1G0S2S1S30S8dS6eS5bA4G6A4G7A4S0G3S1G1G2S1G0S2S1S30S8dS6dS5bA4G6A4G7A4S3G3A1A3A3A3A3A3A3A3A3A3A3A3").

Goal entails_frA E_vrx Pre_vr s_v = Some R_v /\ call_checkPA E_vrx Pre_vr s_v R_v (map (fun d => fst (fst d)) PD_vrr) = true
     /\ entailsA T_keepC K_ok s_keep = true /\ entailsA T_grownC K_ok s_grown = true
     /\ entailsA X_stA K_st s_st = true
     /\ entailsA P_retL1 P_ret1 (s_retL 1) = true /\ entailsA P_retL0 P_ret0 (s_retL 0) = true
     /\ entailsA XR0a (mkA (P_ret_S (rvR XR0a)) (X_bli (SVar 140) (SVar 142))) (s_retE XR0a) = true
     /\ entailsA XR0b (mkA (P_ret_S (rvR XR0b)) (X_bli (SVar 140) (SVar 142))) (s_retE XR0b) = true
     /\ length XL0 = 5%nat /\ length XR0 = 2%nat.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_build_line_index_rom.

(* [comment removed for export] *)
Module Start8CallDefs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "cell"; "DZero"; "SVar"; "c_off"; "c_val"; "enc_bytes"; "mkObj"; "ob_cells"; "sobj"; "ss_fregs"; "ss_objs"; "ss_regs"; "sv_eqb"; "@Corelib.Init.Datatypes"; "nat"; "pair"; "cons"; "app"; "nil"; "option"; "prod"; "Some"; "list"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Lists.ListDef"; "nth"; "map"; "seq"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Nat"; "add"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs"; "cellv22"; "AFL1V"; "AFL2V"; "odummy22"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueD"; "subcell_val"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "image_bytes"; "@Stdlib.Lists.List"; "find"; "@Stdlib.ZArith.BinInt.Z"; "mul"; "of_nat"; "sub"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CompleteA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ne.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ns.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ob.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Start8RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition splits22 : list (nat * sv) := ltac2:(tb__ "0|3|
S11S15SfS0A2M0S10SfS0U2aS1N11c0A1A4S11G0S10SfS0U2bS1N70A1A4S11G0S10SfS0UfM1S1Z170308A1A4S11G0S10SfS0U10M2S1Z170318A1A4S11G0S10SfS0UbS1Ze67c0A1A4S11G0S10SfS0UcS1Ze67c8A1A4S11G0S10SfS0UdS1Ze91f0A1A4S11G0S10SfS0UeS1Zea9f0A1A4S11G0S10SfS0G1S1Zeb8b8A1A4S11G0S10SfS0G2S1Zeb8e4A1A4S11G0S10SfS0U11S1Zeb8f0A1A4S11G0S10SfS0U12S1Zeb930A1A4S11G0S10SfS0U13S1Zeb980A1A4S11G0S10SfS0U14S1Zed91cA1A4S11G0S10SfS0U15S1Zed91dA1A4S13G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition odummy22 : sobj := ltac2:(tb__ "0|1|
S8S1Z0A1M0G0G0S13S2A1S3A5").
Definition ob22 (St : sstate) (i : nat) : sobj := ltac2:(tb__ "0|0|
S1aSaVi;ScVSt;A1S24A4").
Definition cellv22 (o : sobj) (off : Z) : sv := ltac2:(tb__ "0|0|
S14S2A1S0Lx;S28S2S2SeS5R1A1S1Voff;A1A2Lc;S9Vo;A1A3S2S6R1A1Lc;S1Z0A1X14x2").

Definition mk_s22 (St : sstate) (win : sobj) : wsub := ltac2:(tb__ "0|5|
S12S15S18S0A2M0S11G0S10S18S0P1S4P1bA1A4S11G0S10S18S0P2S1aS0U8SdVSt;A1M1S1Z0A1M2A4A4S11G0S10S18S0P3S21Vwin;N78A2A4S13G0A1A3A3A3S12G0S1bSfG0SfS10S18S0S20S1fU4R1A2A1S21Vwin;S2bN80S29Z8S2aR1A1A2A2A2A4Lk;S1cU0M3UcA2A4S12G0S1bSfG0SfS10S18S0S20S1fU14R1A2A1S1aS0R1SbVSt;A1G2A4A4Lr;S1cG3U20A2M4A4S1bSfG0SfS10S18S0S20S1fU3cR1A2A1S1aS0R1G1G2A4A4Lr;G4A4A3A3A3").
Definition AFL1V : Z := 72340168526266369.
Definition AFL2V : Z := 72340172838010881.
Lemma subcell_vals22 : ltac2:(tb__ "0|1|
S1eS1dS19S25S22Z0Z4A3Z1M0A3S1dS19S25S23Z5G0A3G0A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma gl_img22 : ltac2:(tb__ "0|2|
S1dS14S17S2dQ8A1A1M0A1S27S26Zeb938U8M1A3S16G0S7G1S2cQ40Z0A2A2A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition PGA : word := Z_to_bv 64 0x7fffc000.
Definition PGB : word := Z_to_bv 64 0x80015000.
Definition MAINPC : Z := 0x8c524.
End Start8CallDefs.

(* [comment removed for export] *)
Module Start8Out.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "m_vm_lazy"; "vm_limit"; "vm_init_sp"; "vm_maps"; "VmMaps"; "vm_noaccess"; "vm_brk"; "event"; "maps_subtract"; "vm_reserved"; "Model"; "alloc_top"; "lazy_interior"; "vm_start_brk"; "mkVmMapsFull"; "vm_mmap_base"; "page_in_ranges"; "region_free"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "True"; "ex"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "list"; "nil"; "app"; "bool"; "true"; "false"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "divide"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7"; "mE"; "Q18"; "out18"; "TOPz"; "out18_ok"; "out18_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes"; "n8w"; "pgw"; "brk0w"; "brk0"; "n2w"; "mg"; "mf_exp"; "mf_res"; "mg_dead"; "mg_ok"; "a4"; "mgrant"; "n3w"; "reqw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.Seg8M"; "LmE"; "X1_18"; "L18"; "X18"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "mmap_n"; "mmap_none_vm"; "mmap_fixed_dead_vm"; "mmap_fixed_ok_vm"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.MuslMalloc40Post"; "out1"; "out1_ok"; "out0"; "O1_dead"; "O1_ok"; "out1_model"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M"; "minv8"; "ranges_apart"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_LO"; "SHADOW_BAND_HI"; "SHADOW_RW_LO_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4"; "n7"; "n9"; "m8"; "RI"; "m10"; "m11"; "m9"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5"; "m13"; "m12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6"; "n17"; "m16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA
  MmapA MmapFixedA MmapFixedA2 MmapBrkA MmapNodesA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Init Code StartLib KxA Placement PlacementA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start7 Start8M.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Start5bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o2.Start6Aux OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.MuslMalloc40States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.MuslMalloc40Post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.MuslMalloc40 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma filter_all_true : forall {T} (f : T -> bool) (l : list T), (forall e, In e l -> f e = true) -> List.filter f l = l.
Proof.
  intros T f l H. induction l as [|e l IH]; [reflexivity|]. cbn [List.filter]. rewrite (H e (or_introl eq_refl)). rewrite IH; [reflexivity|].
  intros e' He'. apply H. right. exact He'.
Qed.

Section Seg8M.

Variables (m : Model) (a1 a2 : word) (B : Z).
Hypothesis Hres : ltac2:(tb__ "0|1|
S16S1eS1dS1Q40A1M0G0A2A1SdS3Vm;A1A1S5bS53A1A3").
Hypothesis Hmaps : ltac2:(tb__ "0|3|
S16S1eS1dS1Q40M0A1M1G1A2M2A1S7S3Vm;A1A1S1cG2S1bG1G1Va2;S0G0Z38e000A2A4S1cG2S1bG1G1Va1;S0G0Z10000A2A4S1cG2S1bG1G1S0G0Z2008fff7000A2S0G0Zdfff0001000A2A4S1cG2S1bG1G1S0G0Z8fff7000A2S0G0Z20000000000A2A4S1cG2S1bG1G1S0G0Z7fff7000A2S0G0Z10000000A2A4S1fG2A1A3A3A3A3A3A3").
Hypothesis Hna : ltac2:(tb__ "0|3|
S16S1eS1dS1Q40M0A1M1G1A2M2A1S9S3Vm;A1A1S1cG2S1bG1G1S0G0Z8fff7000A2S0G0Z20000000000A2A4S1fG2A1A3A3").
Hypothesis Hlz : ltac2:(tb__ "0|3|
S16S1eS1dS1Q40M0A1M1G1A2M2A1S4Vm;A1S20G2S10S0G0Z2008fff7000A2S0G0Zdfff0001000A2A2S20G2S10S0G0Z8fff7000A2S0G0Z20000000000A2A2S10S0G0Z7fff7000A2S0G0Z10000000A2A2A3A3A3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Ha1 : ltac2:(tb__ "0|2|
S17S24Z643000S2Q40Va1;A2M0A2S17S18S24S25G0Z10000A2M1S50A2S24S51G0A2A2S24G1SfS3Vm;A1A1A2A2A2").
Hypothesis Ha2 : ltac2:(tb__ "0|2|
S17S24Z643000S2Q40Va2;A2M0A2S17S18S24S25G0Z38e000A2M1S50A2S24S51G0A2A2S24G1SfS3Vm;A1A1A2A2A2").
Hypothesis HBlim : ltac2:(tb__ "0|0|
S24S25VB;Z1000000A2S5S3Vm;A1A1A2").
Hypothesis Hsb : ltac2:(tb__ "0|1|
S16S1Q40A1S11S3Vm;A1M0A1SaG0A1A3").
Hypothesis Hbrk : ltac2:(tb__ "0|1|
S17S24Z643000S2Q40SaS3Vm;A1A1A2M0A2S24G0Z80643000A2A2").
Hypothesis Hbal : ltac2:(tb__ "0|0|
S27Z1000S2Q40SaS3Vm;A1A1A2A2").
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S64S61S1eS1Q40A1A1S1eSbA1M0SeR5R4R3R2R1A4S16G0R3S1fSbA1A3F_;Fmd;Ftr;Ftp;Frho;S65S53Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S64S61S1eS1Q40A1A1S1eSbA1M0SeR5R4R3R2R1A4S16G0R3S1fSbA1A3F_;Fmd;Ftr;Ftp;Frho;S66S53Vok;R2A3F_;FJ;").
Variables (P b4 b5 b6 : word).
Hypothesis HPL : ltac2:(tb__ "0|0|
S41S0Q40Z0A2Vm;S54VP;A4").
Hypothesis HPL4 : ltac2:(tb__ "0|0|
S41S0Q40Z0A2S56Vm;VP;A2S55Vb4;A4").
Hypothesis HPL5 : ltac2:(tb__ "0|1|
S41S0Q40M0Z0A2S5aVm;VP;Vb4;A3S0G0Z1000A2Vb5;A4").
Hypothesis HPL6 : ltac2:(tb__ "0|1|
S41S0Q40M0Z0A2S58Vm;VP;Vb4;Vb5;A4S0G0Z10000A2Vb6;A4").
Variables (b7 b8 b9 : word).
Hypothesis HPL7 : ltac2:(tb__ "0|1|
S41S0Q40M0Z0A2S59Vm;VP;Vb4;Vb5;Vb6;A5S0G0Z1000A2Vb7;A4").
Hypothesis HPL8 : ltac2:(tb__ "0|1|
S41S0Q40M0Z0A2S5eVm;VP;Vb4;Vb5;Vb6;Vb7;A6S0G0Z1000A2Vb8;A4").
Hypothesis HPL9 : ltac2:(tb__ "0|1|
S41S0Q40M0Z0A2S5dVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;A7S0G0Z1000A2Vb9;A4").
Variables (x : Z) (b10 : word).
Hypothesis Hx : 0x7fff80000000 <= x <= 2 ^ 47.
Hypothesis H16 : x mod 16 = 0.
Hypothesis Hxtop : ltac2:(tb__ "0|0|
S16S4dSfS3Vm;A1A1S28Vx;Z800000A2A3").
Hypothesis HPL10 : ltac2:(tb__ "0|1|
S41S0Q40M0Z0A2S60Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;A9S0G0S5fA2Vb10;A4").

Hypothesis Hapart0 : ltac2:(tb__ "0|2|
S4fS20S1dS1Q40A1M0G0A2SdS3Vm;A1M1A1S7G1A1A3A1").

Local Notation mE := (Start7.mE m P b4 b5 b6 b7 b8 b9 x b10).
Local Notation TOPz := (Start7.TOPz x).
Local Notation Q18 := (Start7.Q18 x).
Local Notation out18_ok := (Start7.out18_ok m P b4 b5 b6 b7 b8 b9 x b10).
Local Notation out18_model := (Start7.out18_model m P b4 b5 b6 b7 b8 b9 x b10).
Local Notation P_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.P_facts m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation RI_range := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.RI_range m a1 a2 Hres Hmaps Htop P HPL) (only parsing).
Local Notation b4_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b4_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4) (only parsing).
Local Notation b5_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b5_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5) (only parsing).
Local Notation b6_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b6_facts m a1 a2 Hres Hmaps Htop P HPL b4 HPL4 b5 HPL5 b6 HPL6) (only parsing).
Local Notation b7_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.b7_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7) (only parsing).
Local Notation b8_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.b8_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8) (only parsing).
Local Notation b9_facts := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.b9_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8 b9 HPL9) (only parsing).
Local Notation mF_vmmaps := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.mF_vmmaps m P b4 b5 b6 b7 b8 b9) (only parsing).
Local Notation m16_fields := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.m16_fields m P b4 b5 b6 b7 b8 b9) (only parsing).
Local Notation W9 := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.W9 m a1 a2 Hres Hmaps Hna Htop P b4 HPL HPL4) (only parsing).
Local Notation low_shadow_lazy_mF := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.low_shadow_lazy_mF m a1 a2 Hres Hmaps Hlz Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation low_shadow_acc_mF := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.low_shadow_acc_mF m a1 a2 Hres Hmaps Hna Hlz Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9) (only parsing).
Local Notation mE_fields := (Start7.mE_fields m P b4 b5 b6 b7 b8 b9 x b10) (only parsing).
Local Notation top_mE := (Start7.top_mE m P b4 b5 b6 b7 b8 b9 x b10 Hxtop) (only parsing).
Local Notation init_sp_ok_mE := (Start7.init_sp_ok_mE m Htop P b4 b5 b6 b7 b8 b9 x b10) (only parsing).
Local Notation b10_facts := (Start7.b10_facts m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxtop HPL10) (only parsing).
Local Notation band_mE := (Start7.band_mE m a1 a2 Hres Hmaps Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10) (only parsing).
Local Notation CAx := (Start7.CAx x Hx H16) (only parsing).
Local Notation lazy_mE_facts := (Start7.lazy_mE_facts m a1 a2 Hres Hmaps Hlz Htop P b4 b5 b6 HPL HPL4 b7 b8 b9 x b10 Hx H16) (only parsing).
Local Notation high_shadow_lazy_mE := (Start7.high_shadow_lazy_mE m a1 a2 Hres Hmaps Hlz Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx H16) (only parsing).
Local Notation noacc_mF_wf := (Start7.noacc_mF_wf m a1 a2 Hres Hmaps Hna Htop P b4 b5 b6 HPL HPL4 b7 b8 b9) (only parsing).
Local Notation high_shadow_acc_mE := (Start7.high_shadow_acc_mE m a1 a2 Hres Hmaps Hna Hlz Htop P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx H16) (only parsing).
Local Notation brk0_mE := (Start7.brk0_mE m Hbrk P b4 b5 b6 b7 b8 b9 x b10 Hx H16 Hxtop) (only parsing).
Local Notation out18_Wok := (Start7.out18_Wok m a1 a2 Hres Hmaps Htop Hbrk P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx H16 Hxtop HPL10) (only parsing).

Ltac klia := unfold kHighMemBeg in *; repeat match goal with H : context [Z.modulo _ _] |- _ => clear H end; lia.

Definition LmE : list (word * word) := ltac2:(tb__ "0|4|
S20S1dS1Q40M0A1M1G1A2M2S1cG2S1bG1G1Vb10;S0G0S5fA2A4S1cG2S1bG1G1Vb8;S0G0Z1000A2M3A4S1cG2S1bG1G1Vb7;G3A4S1cG2S1bG1G1Vb6;S0G0Z10000A2A4S1cG2S1bG1G1Vb5;G3A4S1cG2S1bG1G1Vb4;S55A4S1cG2S1bG1G1VP;S54A4S1fG2A1A3A3A3A3A3A3A3S7S3Vm;A1A1A3").

Lemma maps_m13 : ltac2:(tb__ "0|4|
S16S1eS1dS1Q40M0A1M1G1A2M2A1S7S3S5dVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;A7A1A1S20G2S1cG2S1bG1G1Vb8;S0G0Z1000A2M3A4S1cG2S1bG1G1Vb7;G3A4S1cG2S1bG1G1Vb6;S0G0Z10000A2A4S1cG2S1bG1G1Vb5;G3A4S1cG2S1bG1G1Vb4;S55A4S1cG2S1bG1G1VP;S54A4S1fG2A1A3A3A3A3A3A3S7S3Vm;A1A1A3A3").
Proof.
  clear. pose proof (m13_ledger m P b4 b5 b6 b7 b8) as (_ & L2 & _). pose proof (m12_ledger m P b4 b5 b6 b7) as (_ & O2 & _). pose proof (mE_ledger m P b4 b5 b6) as (_ & Q2 & _).
  rewrite L2, O2, Q2. reflexivity.
Qed.

Lemma maps_mE_eq : ltac2:(tb__ "0|1|
S16S1eS1dS1Q40A1M0G0A2A1S7S3S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaA1A1S3dA3").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop.
  clear Hna Hlz Ha1 Ha2 HBlim Hsb Hbrk Hbal OKF OKP Hx H16 Hxtop HPL10 Hapart0.
  pose proof mE_fields as (_ & MM & _). rewrite MM. pose proof (m16_fields x) as (_ & M6 & _). rewrite M6. unfold LmE. cbn [List.app]. f_equal.
  pose proof (m13_ledger m P b4 b5 b6 b7 b8) as (R13 & _).
  pose proof b9_facts as (_ & _ & _ & _ & _ & K4). rewrite R13, maps_m13 in K4.
  unfold map_remove. cbn [List.filter fst]. rewrite (proj2 (bv_eqb_eq b9 b9) eq_refl). cbn [negb]. rewrite maps_m13.
  apply filter_all_true. intros [e s] Hin. cbn [fst].
  assert (Hs : 0 < bv_unsigned s).
  { rewrite Hmaps in Hin. cbn [List.app In] in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]; injection E as <- <-; unfold n9, n7; rewrite ?u64_of_lit by lia; lia. }
  rewrite (region_free_In_neq _ b9 (Z_to_bv 64 4096) e s (region_free_app_r _ _ _ _ K4) Hin Hs ltac:(rewrite u64_of_lit by lia; lia)). reflexivity.
Qed.

Lemma LmE_pos : ltac2:(tb__ "0|2|
S1Q40M0A1M1G1S5cS1dG1G1A2S1bG1G1R2R1A4S3dA3S26Z0S2G0R2A2A2F_;Fs;Fb;").
Proof using Hmaps.
  clear - Hmaps. intros b s Hin. unfold LmE in Hin. rewrite Hmaps in Hin. cbn [List.app In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <-; unfold n17, n9, n7; rewrite ?u64_of_lit by lia; lia.
Qed.

Lemma LmE_wf : ivs_wf LmE.
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hmaps Hres Htop Hxtop Hx.
  clear Hna Hlz HBlim Hsb Hbrk Hbal OKF OKP Hapart0.
  intros [b s] Hin. pose proof (alloc_top_lt (m_vmmaps m)) as TL. unfold two_pow_64 in TL.
  pose proof P_facts as (_ & Pceil & _). pose proof b4_facts as (_ & _ & C4 & _). pose proof b5_facts as (_ & _ & _ & C5 & _).
  pose proof b6_facts as (_ & _ & C6 & _). pose proof b7_facts as (_ & _ & C7 & _). pose proof b8_facts as (_ & _ & C8 & _).
  pose proof b10_facts as (_ & _ & C10 & _). unfold Start7.TOPz in C10.
  unfold iv_wf, ivB, ivS. cbn [fst snd]. unfold LmE in Hin. rewrite Hmaps in Hin. cbn [List.app In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <-; unfold n17, n9, n7 in *; rewrite ?u64_of_lit by lia; lia.
Qed.

Lemma apart_mE : ltac2:(tb__ "0|1|
S4fS20S1dS1Q40A1M0G0A2S5bS53A1S3dA3A1").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hmaps Hres Htop Hxtop Hapart0.
  clear Hna Hlz Ha1 Ha2 HBlim Hsb Hbrk Hbal OKF OKP.
  pose proof P_facts as (_ & _ & F7 & _). pose proof b4_facts as (_ & _ & _ & _ & F4). pose proof b5_facts as (_ & _ & _ & _ & _ & F5).
  pose proof b6_facts as (_ & _ & _ & _ & F6). pose proof b7_facts as (_ & _ & _ & _ & F7b). pose proof b8_facts as (_ & _ & _ & _ & F8).
  pose proof b10_facts as (_ & _ & _ & _ & F10).
  pose proof (m8_ledger m P) as (R8 & M8 & _). pose proof (m9_ledger m P b4) as (R9 & M9 & _). pose proof (m10_ledger m P b4 b5) as (R10 & M10 & _).
  pose proof (mE_ledger m P b4 b5 b6) as (R11 & M11 & _). pose proof (m12_ledger m P b4 b5 b6 b7) as (R12 & M12 & _).
  pose proof (m16_fields x) as (R16 & M16 & _). pose proof mE_fields as (_ & MM & _).
  rewrite R8, M8, Hres in F4. rewrite R9, M9, Hres in F5. rewrite R10, M10, Hres in F6. rewrite R11, M11, Hres in F7b. rewrite R12, M12, M11, Hres in F8.
  rewrite Hres in F7. rewrite Hres in Hapart0.

  assert (M16' : vm_maps (m_vmmaps (m16 m P b4 b5 b6 b7 b8 b9 x)) = [(b8, Z_to_bv 64 4096); (b7, Z_to_bv 64 4096); (b6, Z_to_bv 64 65536); (b5, Z_to_bv 64 4096); (b4, n9); (P, n7)] ++ vm_maps (m_vmmaps m)).
  { pose proof maps_mE_eq as E. rewrite MM in E. unfold LmE in E. cbn [List.app] in E. injection E as E'. exact E'. }
  rewrite R16, M16', Hres in F10.
  unfold LmE. cbn [List.app].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F10 He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F8 He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F7b He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F6 He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F5 He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F4 He)].
  apply ranges_apart_insert; [|intros e He; exact (apart_of_region_free _ _ _ e F7 He)].
  exact Hapart0.
Qed.

Lemma low_lazy_mE : ltac2:(tb__ "0|1|
S1Q40M0A1S24S50S2G0R1A2A2S24S25S2G0R2A2Z1000A2S52A2S16S21S14R3S4S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaA1A2S22A3F_;F_;Fp;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hlz Hmaps Hres Htop Hx H16.
  clear Hna Ha1 Ha2 HBlim Hsb Hbrk Hbal OKF OKP Hxtop HPL10 Hapart0.
  intros p Hlo Hhi. pose proof mE_fields as (_ & _ & _ & _ & LZ & _). rewrite LZ.
  pose proof (m16_fields x) as (_ & _ & _ & _ & LZ6 & _). rewrite LZ6.
  apply low_shadow_lazy_mF; assumption.
Qed.

Lemma low_acc_mE : ltac2:(tb__ "0|0|
S4dS17S24S50R1A2S26R1S52A2A2S16S21S62S9S3S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaA1A1R2A2S23A3F_;Fz;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hlz Hna Hmaps Hres Htop Hx H16.
  clear Ha1 Ha2 HBlim Hsb Hbrk Hbal OKF OKP Hxtop HPL10 Hapart0.
  intros z Hz. pose proof mE_fields as (_ & _ & _ & _ & _ & NA & _). rewrite NA.
  pose proof (m16_fields x) as (_ & _ & _ & _ & _ & NA6). rewrite NA6.
  exact (low_shadow_acc_mF z Hz).
Qed.

Lemma noacc_wf8 : ltac2:(tb__ "0|5|
S17S16S1eS1dS1Q40M0A1M1G1A2M2A1S9S3S56Vm;VP;A2A1A1ScS1cG2S1bG1G1VP;S54A4S1cG2S1bG1G1S0G0Z8fff7000A2S0G0Z20000000000A2A4S1fG2A1A3A3M3S2G0S57VP;A1A2M4S25G4Z1000A2A3A3S63G3A1A2").
Proof using HPL Hna Hmaps Hres Htop.
  clear - HPL Hna Hmaps Hres Htop.
  pose proof P_facts as (Pal & Pceil & _). pose proof (alloc_top_lt (m_vmmaps m)) as TL. unfold two_pow_64 in TL.
  split.
  - rewrite (m8_vmmaps m P). unfold h8, mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite (mP_vmmaps m P). cbn [vm_noaccess]. rewrite Hna.
    replace (bv_unsigned pg) with 4096 by (symmetry; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). reflexivity.
  - apply ivs_wf_cons; [|apply ivs_wf_cons; [|apply ivs_wf_nil]]; unfold iv_wf, ivB, ivS; cbn [fst snd]; [unfold n7|]; rewrite ?u64_of_lit by lia; lia.
Qed.

Lemma namaps_mE : ltac2:(tb__ "0|3|
S4dS16S21S62S9S3S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaA1A1R1A2S22A3S1aS1Q40M0A1M1G1S1aG1G1S17S5cS1dG1G1A2S1bG1G1R2R1A4S3dA3S17S24S2G0R2A2M2R4A2S26R4S25G2S2G0R1A2A2A2A2A2Ls;A2Lb;A2F_;Fz;").
Proof using HPL HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hlz Hna Hmaps Hres Htop Hx H16.
  clear Ha1 Ha2 HBlim Hsb Hbrk Hbal OKF OKP Hxtop HPL10 Hapart0.
  intros z Hz. pose proof noacc_mF_wf as WF. pose proof mE_fields as (_ & _ & _ & _ & _ & NA & _). rewrite NA in Hz.
  pose proof (m16_fields x) as (_ & _ & _ & _ & _ & NA6). rewrite NA6 in Hz. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.mF in NA6, Hz, WF.
  pose proof mF_vmmaps as (_ & _ & NAF & _). unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.mF in NAF. rewrite NAF in Hz. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.b9lo in Hz.
  destruct (maps_subtract_sem _ (bv_unsigned b9) (bv_unsigned b9 + 4096) W9 ltac:(lia)) as (_ & _ & Cv9). rewrite Cv9 in Hz. apply andb_prop in Hz as [Hz _].
  apply covered_cons_iff8 in Hz as [Hz|Hz].
  - unfold ivB, ivS in Hz. cbn [fst snd] in Hz. exists b4, n9. split; [unfold LmE; cbn [List.app In]; tauto | lia].
  - pose proof noacc_wf8 as [E8 W7]. rewrite E8 in Hz. pose proof P_facts as (Pal & Pceil & _).
    destruct (maps_subtract_sem _ (bv_unsigned (RI P)) (bv_unsigned (RI P) + 4096) W7 ltac:(lia)) as (_ & _ & Cv7). rewrite Cv7 in Hz. apply andb_prop in Hz as [Hz _].
    apply covered_cons_iff8 in Hz as [Hz|Hz]; [|apply covered_cons_iff8 in Hz as [Hz|Hz]; [|discriminate]]; unfold ivB, ivS in Hz; cbn [fst snd] in Hz.
    + exists P, n7. split; [unfold LmE; cbn [List.app In]; tauto | lia].
    + exists (Z_to_bv 64 0x8fff7000), (Z_to_bv 64 0x20000000000). split; [unfold LmE; rewrite Hmaps; cbn [List.app In]; tauto | lia].
Qed.

Theorem minv8_mE : ltac2:(tb__ "0|1|
S4eS3dS5S3Vm;A1M0A1S6G0A1S2aVx;A1S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaA5").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbrk Hbal OKF OKP.
  pose proof mE_fields as (MR & MM & ML & MB & LZ & NA & K1 & K2). pose proof lazy_mE_facts as [WL _].
  constructor.
  - rewrite MR. exact Hres.
  - exact maps_mE_eq.
  - exact ML.
  - exact MB.
  - exact init_sp_ok_mE.
  - rewrite <- Hres, <- MR, <- maps_mE_eq. exact band_mE.
  - exact apart_mE.
  - exact LmE_pos.
  - exact LmE_wf.
  - exact low_lazy_mE.
  - exact low_acc_mE.
  - intros p H1 H2. apply high_shadow_lazy_mE; [exact H1 | unfold SHADOW_BAND_HI in H2; unfold kHighMemBeg; exact H2].
  - intros z Hz. apply high_shadow_acc_mE. unfold SHADOW_RW_HI_BEG, SHADOW_BAND_HI in Hz. unfold kHighMemBeg. exact Hz.
  - intros z Hz. exact (namaps_mE z Hz).
  - rewrite NA. pose proof (m16_fields x) as (_ & _ & _ & _ & _ & NA6). rewrite NA6. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.mF. exact noacc_mF_wf.
  - exact WL.
  -
    rewrite NA. pose proof (m16_fields x) as (_ & _ & _ & _ & _ & NA6). rewrite NA6. pose proof mF_vmmaps as (_ & _ & NAF & _). rewrite NAF.
    assert (N9 : bv_unsigned n9 = 0x800000) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    apply ivs_pos_subtract. apply ivs_pos_cons; [rewrite N9; lia|]. pose proof noacc_wf8 as [E8 _]. rewrite E8. apply ivs_pos_subtract.
    apply ivs_pos_cons; [unfold n7; rewrite u64_of_lit by lia; lia|]. apply ivs_pos_cons; [rewrite u64_of_lit by lia; lia | apply ivs_pos_nil].
Qed.

Definition X1_18 (o : out1) : list (word * word) := ltac2:(tb__ "0|7|
S47S1eS1dS1Q40M0A1M1G1A2M2A1Lo;Vo;S1cG2S1bG1G1S31S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM3A1S33A4S1fG2A1M4A3M5G5S1cG2S1bG1G1S0G0S25S32G3A1Z1000M6A2A2S0G0G6A2A4G4A3G1S1cG2S1bG1G1R1S2fA4G4A3La;X47x4").
Definition X18 (o : out18) : list (word * word) := ltac2:(tb__ "0|4|
S2bS1eS1dS1Q40A1M0G0A2M1A1M2Lo;Vo;S49S49G2Lo0;R1S1fG1A1M3G0S1cG1S1bG0G0R1S2fA4G3A3La;X49x2Lo0;S47S3eR1A1Lo1;S47G0S1cG1S1bG0G0R1S30A4S3eR2A1A3Lg;Lo1;X2bx3").
Definition L18 (o : out18) : list (word * word) := X18 o ++ LmE.

Lemma pgw_n : ltac2:(tb__ "0|4|
S17S16S1Q40M0A1M1S42S30A1S30A3S17S16S4dS2G0S30A2Z1000M2A3S17S16G1S42S2fA1S2fA3S17S16S4dS2G0S2fA2Z2000M3A3S17S16S4dS2G0S33A2G3A3S17S16G1S2fS0G0G3A2A3S16G1S30S0G0G2A2A3A2A2A2A2A2A2").
Proof. clear. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma brk_mE : ltac2:(tb__ "0|4|
S17S24Z643000S32S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0A1M1A2S17S24G1Z80643000A2S17S16S4dS2Q40M2S31G0A1M3A2G1A3S16S1G2A1G3SaS3Vm;A1A1A3A2A2A2").
Proof using Hbrk Hx H16 Hxtop.
  clear - Hbrk Hx H16 Hxtop. pose proof brk0_mE as (B1 & B2 & B3). repeat split; try assumption; try reflexivity.
Qed.

Lemma mg_shape : ltac2:(tb__ "0|5|
S17S16S8S3S34S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0A1M1A1S12SdS3G0A1M2A1S1cS1dS1Q40A1M3G3A2M4S1bG3G3S31G0A1S33A4S7G2A1A3S9G2A1S11G2A1S3cG0A1S5G2A1S13G2A1S6G2A1A8A3S16S1eG4A1S4G1A1S4G0A1A3A2").
Proof using Hbrk Hx H16 Hxtop. clear - Hbrk Hx H16 Hxtop. pose proof brk_mE as (H1 & H2 & _). split; [exact (mg_vmmaps mE H1 H2) | unfold mg; apply m_vm_lazy_with_vmmaps]. Qed.

Lemma mg_ok_shape : ltac2:(tb__ "0|4|
S17S16S8S3S38S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0A1M1A1S45S3S34G0A1A1S31G0A1S30A3A3S16S1eS1dS1Q40A1M2G2A2A1S4G1A1ScS4G0A1S32G0A1M3S25G3Z1000A2A3A3A2").
Proof using Hbrk Hx H16 Hxtop.
  clear - Hbrk Hx H16 Hxtop. unfold mg_ok. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps, m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps.
  split; [reflexivity|]. rewrite (proj2 mg_shape). reflexivity.
Qed.
Lemma mg_dead_shape : ltac2:(tb__ "0|4|
S17S16S8S3S37S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0A1M1A1S44S3S34G0A1A1S31G0A1S30A3A3S16S1eS1dS1Q40A1M2G2A2A1S4G1A1ScS4G0A1S32G0A1M3S25G3Z1000A2A3A3A2").
Proof using Hbrk Hx H16 Hxtop.
  clear - Hbrk Hx H16 Hxtop. unfold mg_dead. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps, m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps.
  split; [reflexivity|]. rewrite (proj2 mg_shape). reflexivity.
Qed.
Lemma mf_res_shape : ltac2:(tb__ "0|3|
S1Q40A1M0S17S16S8S3S36S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM1R1A2M2A1S43S3G1A1S2fR1A3A3S16S1eS1dG0G0A2A1S4G2A1S4G1A1A3A2Fa;").
Proof. clear. intros a. split; [apply mf_res_vmmaps | unfold mf_res; apply m_vm_lazy_with_vmmaps]. Qed.
Lemma mf_exp_shape : ltac2:(tb__ "0|5|
S1Q40M0A1M1S43S3S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM2A1S2fR1A3S8S17S16S8S3S35G2R2A2M3A1S12SdR1A1S7R1A1ScS9R1A1S2G0S39R2A1A2M4S25G4S2G0S30A2A2A3S11R1A1SaR1A1S5R1A1S13R1A1S6R1A1A8A3S16S1eS1dG1G1A2A1S4G3A1S4G2A1A3A2Th;Fa;").
Proof.
  clear. intros a h. unfold mf_exp, mprotect_model_next. rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps, mf_res_vmmaps. subst h.
  split; [reflexivity | unfold mf_res; apply m_vm_lazy_with_vmmaps].
Qed.
Lemma mgrant_shape : ltac2:(tb__ "0|2|
SeS1Q40A1M0S17S16S8S3S3aR2R1A2M1A1S46S3R2A1S30R1A3A3S16S1eS1dG0G0A2A1S4G1A1S4R2A1A3A2Fg;Fmx;").
Proof. clear. intros. unfold mgrant. rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps. split; reflexivity. Qed.

Lemma grow_facts : ltac2:(tb__ "0|4|
S47S48S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0R1A2S47OLo1;R2S17S16S21S15S20S1dS1Q40A1M1G1A2S5bS53A1S3dA3S31G0A1S3bA3S22A3S17S24S25S32G0A1Z2000A2M2S50A2S24G2S2cVx;A1A2A2A2M3G3G3G1S19La;X47x4F_;Fo1;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Hbrk Hmaps Hres Htop Hx H16 Hxtop.
  clear Hna Hlz Ha1 Ha2 HBlim Hsb Hbal OKF OKP Hapart0.
  intros o1 Ho. pose proof mE_fields as (MR & _). pose proof brk_mE as (B1 & B2 & B3 & _).
  assert (GEN : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0 mE + 8192 <= alloc_top (m_vmmaps mE) /\ State.region_free (vm_reserved (m_vmmaps mE) ++ vm_maps (m_vmmaps mE)) (brk0w mE) n3w = true ->
                State.region_free (segments_reserved segsA ++ LmE) (brk0w mE) n3w = true
                /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0 mE + 8192 <= SHADOW_BAND_LO /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0 mE + 8192 <= TOPz).
  { intros [A1 A2]. rewrite top_mE in A1.
    pose proof (grant_avoids_band _ SHADOW_BAND_LO SHADOW_BAND_HI (brk0w mE) n3w band_mE ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) A2 ltac:(rewrite n3w_val; lia)) as A4.
    rewrite n3w_val, B3 in A4. rewrite MR, Hres, maps_mE_eq in A2. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *.
    split; [exact A2|]. split; lia. }
  destruct o1; cbn [out1_ok] in Ho; [apply GEN; exact Ho | apply GEN; exact Ho | apply GEN; exact Ho | exact I].
Qed.

Lemma place8k : ltac2:(tb__ "0|3|
S1Q40M0A1S41S0G0Z0A2M1S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM2S2fR1A4S41G1G2S0G0Z2000A2R2A4F_;Fa;").
Proof. clear. intros a H. pose proof pgw_n as (_ & _ & _ & _ & _ & E & _). rewrite E in H. exact H. Qed.

Local Notation limv := (vm_limit (m_vmmaps m)).
Local Notation ispv := (vm_init_sp (m_vmmaps m)).

Lemma minv8_mg : ltac2:(tb__ "0|4|
S47S48S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0R1A2S47OLo1;R2S4eS1cS1dS1Q40A1M1G1A2S1bG1G1S31G0A1S33A4S3dA3S5S3Vm;A1M2A1S6G2A1S2aVx;A1S34G0A1A5M3G3G3G1S19La;X47x4F_;Fo1;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hbrk Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbal OKF OKP.
  intros o1 Ho. pose proof (grow_facts o1 Ho) as GF. pose proof mg_shape as [SH LZ]. pose proof pgw_n as (_ & _ & _ & _ & N2 & _). pose proof brk_mE as (B1 & B2 & B3 & _).
  assert (GEN : State.region_free (segments_reserved segsA ++ LmE) (brk0w mE) n3w = true /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0 mE + 8192 <= SHADOW_BAND_LO /\ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0 mE + 8192 <= TOPz ->
                minv8 ((brk0w mE, n2w) :: LmE) limv ispv Q18 (mg mE)).
  { intros (G1 & G2 & G3).
    apply (minv8_cons_low LmE limv ispv Q18 mE (mg mE) (brk0w mE) n2w n3w minv8_mE G1).
    all: rewrite ?SH, ?LZ; try reflexivity; rewrite ?N2, ?n3w_val, ?B3; try lia. }
  destruct o1; cbv beta iota; cbv beta iota in GF; [apply GEN; exact GF | apply GEN; exact GF | apply GEN; exact GF | exact I].
Qed.

Lemma minv8_mg_ok : ltac2:(tb__ "0|3|
S48S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0S4bA2S4eS1cS1dS1Q40A1M1G1A2S1bG1G1S31G0A1S33A4S3dA3S5S3Vm;A1M2A1S6G2A1S2aVx;A1S38G0A1A5F_;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hbrk Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbal OKF OKP.
  intros Ho. pose proof (grow_facts O1_ok Ho) as GF. cbv beta iota in GF. destruct GF as (G1 & G2 & G3).
  pose proof (minv8_mg O1_ok Ho) as MI. cbv beta iota in MI.
  pose proof mg_ok_shape as [SH LZ]. pose proof mg_shape as [SHg LZg]. pose proof pgw_n as (_ & PG & _ & _ & N2 & _). pose proof brk_mE as (B1 & B2 & B3 & _).
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & _).
  apply (minv8_guard _ limv ispv Q18 (mg mE) (mg_ok mE) (brk0w mE) pgw (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0 mE) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0 mE + 4096) MI).
  all: rewrite ?SH, ?LZ, ?LZg; unfold mmap_fixed_ok_vm; cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_init_sp]; rewrite ?PG, ?N2;
       unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0, Start7.Q18 in *; unfold SHADOW_BAND_LO in *; try reflexivity; try lia.
  exists (brk0w mE), n2w. split; [left; reflexivity | rewrite ?PG, ?N2; lia].
Qed.

Lemma minv8_mg_dead : ltac2:(tb__ "0|5|
S48S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0S4aA2S4eS1cS1dS1Q40M1A1M2G2A2S1bG2G2S0G1S25S32G0A1Z1000M3A2A2S0G1G3A2A4S3dA3S5S3Vm;A1M4A1S6G4A1S2aVx;A1S37G0A1A5F_;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hbrk Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbal OKF OKP.
  intros Ho. pose proof (grow_facts O1_dead Ho) as GF. cbv beta iota in GF. destruct GF as (G1 & G2 & G3).
  pose proof (minv8_mg O1_dead Ho) as MI. cbv beta iota in MI.
  pose proof mg_dead_shape as [SH LZ]. pose proof mg_shape as [SHg LZg]. pose proof pgw_n as (_ & PG & _ & _ & N2 & _). pose proof brk_mE as (B1 & B2 & B3 & _).
  pose proof CAx as CA. cbv zeta in CA. destruct CA as (Ct & CHPlo & CPEhi & CPEHP & _).
  assert (E4096 : Z_to_bv 64 4096 = Z_to_bv 64 (bv_unsigned (brk0w mE) + bv_unsigned n2w - (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0 mE + 4096)))
    by (f_equal; rewrite N2; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0; lia).
  rewrite E4096 at 1.
  apply (minv8_dead LmE limv ispv Q18 (mg mE) (mg_dead mE) (brk0w mE) n2w (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0 mE + 4096) MI).
  all: rewrite ?SH, ?LZ, ?LZg; unfold mmap_fixed_dead_vm; cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_init_sp]; rewrite ?PG, ?N2;
       unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0, Start7.Q18 in *; unfold SHADOW_BAND_LO in *; try reflexivity; try lia.
Qed.

Lemma minv8_mf_res : ltac2:(tb__ "0|4|
S1Q40M0A1M1S41S0G0Z0A2S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM2S2fR1A4S4eS1cS1dG1G1A2S1bG1G1R2S2fA4S3dA3S5S3Vm;A1M3A1S6G3A1S2aVx;A1S36G2R2A2A5F_;Fa;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbrk Hbal OKF OKP.
  intros a Hpl. pose proof (mf_res_shape a) as [SH LZ]. pose proof pgw_n as (_ & _ & N8 & _).
  apply (minv8_reserve LmE limv ispv Q18 mE (mf_res mE a) 8192 a minv8_mE).
  all: rewrite ?SH, ?LZ; unfold mmap_none_vm; cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_init_sp]; rewrite ?N8; try reflexivity; try lia.
  exact (place8k a Hpl).
Qed.

Lemma minv8_mf_exp : ltac2:(tb__ "0|4|
S1Q40M0A1M1S41S0G0Z0A2S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM2S2fR1A4S4eS1cS1dG1G1A2S1bG1G1R2S2fA4S3dA3S5S3Vm;A1M3A1S6G3A1S2aVx;A1S35G2R2A2A5F_;Fa;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbrk Hbal OKF OKP.
  intros a Hpl. pose proof (mf_exp_shape a) as [SH LZ]. cbv zeta in SH. pose proof (mf_res_shape a) as [SHr LZr].
  apply (minv8_expose _ limv ispv Q18 (mf_res mE a) (mf_exp mE a) (bv_unsigned (a4 a)) (bv_unsigned (a4 a) + bv_unsigned pgw) (minv8_mf_res a Hpl)).
  all: rewrite ?SH, ?SHr, ?LZ, ?LZr; cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_init_sp]; try reflexivity.
  pose proof (urange pgw). lia.
Qed.

Lemma minv8_out1 : ltac2:(tb__ "0|3|
S47S48S29Vm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;AaM0R1A2S4eS20S1dS1Q40A1M1G1A2S3eR2A1S3dA3S5S3Vm;A1M2A1S6G2A1S2aVx;A1S4cG0R2A2A5F_;Fo1;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hbrk Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbal OKF OKP.
  intros o1 Ho. destruct o1 as [| | |a]; cbn [out1_model X1_18 List.app].
  - pose proof (minv8_mg O1_kept Ho) as MI. exact MI.
  - exact (minv8_mg_ok Ho).
  - exact (minv8_mg_dead Ho).
  - exact (minv8_mf_exp a Ho).
Qed.

Theorem minv8_out18 : ltac2:(tb__ "0|1|
S2bS2dVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;R1AbS4eS3fR2A1S5S3Vm;A1M0A1S6G0A1S2aVx;A1S2eVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;R2AbA5F_;Fo;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hbrk Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbal OKF OKP.
  intros o Ho. unfold L18. destruct o as [[|a]|o1|o1 g]; cbn [Start7.out18_model Start7.out18_ok out0_model X18 List.app] in Ho |- *.
  - exact minv8_mE.
  - exact (minv8_mf_res a Ho).
  - exact (minv8_out1 o1 Ho).
  - destruct Ho as [Ho Hg]. pose proof (minv8_out1 o1 Ho) as MI.
    pose proof (mgrant_shape (out1_model mE o1) g) as [SH LZ]. pose proof pgw_n as (PG & _ & _ & _ & _ & _ & E4).
    rewrite E4 in Hg |- *.
    apply (minv8_cong _ _ _ _ (eager_model 4096 (out1_model mE o1) g)).
    + rewrite SH. unfold eager_model. rewrite m_vmmaps_with_vmmaps. unfold mmap_rw_vm, eager_h. rewrite <- E4, PG. reflexivity.
    + rewrite LZ. unfold eager_model. rewrite m_vm_lazy_with_vmmaps. reflexivity.
    + apply minv8_eager; [exact MI | lia | reflexivity | lia | exact Hg].
Qed.

Lemma X18_facts : ltac2:(tb__ "0|6|
S2bS1Q40M0A1M1G1S2dVm;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;R3AbS5cS1dG1G1A2S1bG1G1R3R2A4S40R4A1A3S17S18S16S4dS2G0R3A2M2Z2000A3S16S4dG2Z1000M3A3A2S17S24G3S2G0R4A2M4A2S17S24S25G4G2A2M5S2cVx;A1A2S17S18S24G5Z10000A2S24Z643000G4A2A2S18S24G5S50A2S24S51G4A2A2A2A2A2A2F_;F_;Fs;Fb;Fo;").
Proof using HPL HPL10 HPL4 HPL5 HPL6 HPL7 HPL8 HPL9 Ha1 Ha2 Hbrk Hlz Hna Hmaps Hres Htop Hx H16 Hxtop Hapart0.
  clear HBlim Hsb Hbal OKF OKP.
  intros o b s Ho Hin. pose proof (out18_Wok o Ho) as W. pose proof pgw_n as (_ & PG & _ & N8 & N2 & _). pose proof brk_mE as (B1 & B2 & B3 & _).
  assert (W1 : forall o1, out1_ok mE o1 -> In (b, s) (X1_18 o1) ->
            (bv_unsigned s = 8192 \/ bv_unsigned s = 4096) /\ 0x1000 <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= TOPz
            /\ (bv_unsigned b + bv_unsigned s <= 0x10000 \/ 0x643000 <= bv_unsigned b) /\ (bv_unsigned b + bv_unsigned s <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= bv_unsigned b)).
  { intros o1 Ho1 Hin1. pose proof (out18_Wok (O18b o1) Ho1) as Wb. cbn [Start7.out18_W out1_W fst snd] in Wb.
    destruct o1 as [| | |a]; cbn [X1_18 In out1_base] in Hin1, Wb.
    - destruct Hin1 as [[= <- <-]|[]]. rewrite N2. unfold Start7.Wok in Wb. rewrite B3 in *. destruct Wb as [Wb|Wb]; [lia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia.
    - destruct Hin1 as [[= <- <-]|[]]. rewrite N2. unfold Start7.Wok in Wb. rewrite B3 in *. destruct Wb as [Wb|Wb]; [lia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia.
    - destruct Hin1 as [[= <- <-]|[]]. rewrite !u64_of_lit by lia. unfold Start7.Wok in Wb. rewrite B3 in *. destruct Wb as [Wb|Wb]; [lia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia.
    - destruct Hin1 as [[= <- <-]|[]]. rewrite N8. unfold Start7.Wok in Wb. destruct Wb as [Wb|Wb]; [lia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia. }
  destruct o as [[|a]|o1|o1 g]; cbn [X18 Start7.out18_ok out0_ok] in Hin, Ho.
  - destruct Hin.
  - destruct Hin as [[= <- <-]|[]]. rewrite N8. cbn [Start7.out18_W out0_W fst snd] in W. unfold Start7.Wok in W. destruct W as [W|W]; [lia|]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia.
  - exact (W1 o1 Ho Hin).
  - destruct Ho as [Ho Hg]. destruct Hin as [[= <- <-]|Hin]; [|exact (W1 o1 Ho Hin)].
    pose proof pgw_n as (_ & _ & _ & _ & _ & _ & E4). rewrite E4 in Hg. rewrite PG.
    pose proof (minv8_place _ _ _ _ _ 4096 g (minv8_out1 o1 Ho) ltac:(lia) eq_refl ltac:(lia) Hg) as (P1 & P2 & P3 & P4 & _).
    change (LB_of 4096) with 0x1000 in P1.
    assert (UI : bv_unsigned ispv = x) by (unfold alloc_top in Hxtop; rewrite stack_max_size_val in Hxtop; lia).
    unfold Start7.TOPz. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. lia.
Qed.

End Seg8M.
End Start8Out.

(* [comment removed for export] *)
Module StartBD.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "pow"; "mul"; "max"; "of_nat"; "div"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_LO"; "SHADOW_BAND_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6"; "q12x"; "x1"; "TP17"; "LIMz"; "RM6"; "enspage"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4"; "priZ"; "TP11"; "ZD11"; "pRI"; "sbZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7"; "r6of"; "kHighMemBeg"; "TP18"; "Q18"; "Wz"; "grp_out"; "ZX18"; "band"; "lowb"; "out18"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.StartBD"; "BDT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States"; "LOWPG"; "@Corelib.Init.Datatypes"; "option"; "list"; "None"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5"; "TP12"; "e12"; "n12"; "q12"; "shZ"; "stackshadow_zero"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "pageZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "agree_vars"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA
  MmapA MmapFixedA MmapFixedA2 MmapBrkA MmapNodesA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Init Code StartLib KxA Placement PlacementA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartNodes3E.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ne.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start4Fail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start3States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start4FailStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4FailCut OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start4Fail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Start5bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o2.Start6Aux OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.MuslMalloc40States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.MuslMalloc40Post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.MuslMalloc40 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac mlia := repeat match goal with H : context [Z.modulo _ _] |- _ => clear H end; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, kHighMemBeg in *; lia.

Definition BDT (T : list (bv 64)) (pri : Z) (rho : valuation) : Prop :=
  forall p a, In p T -> bv_unsigned p <= a < bv_unsigned p + 4096 -> a < 2 ^ 64 ->
    ~ (pri <= a < pri + 512) -> ~ (LOWPG <= a < LOWPG + 0x4600) -> rm rho (Z_to_bv 64 a) <> None.

Lemma In_enspage_inv : ltac2:(tb__ "0|1|
S11Q40A1M0G0S2fG0A1S14G0R3S1cR2R1A2A3SeScG0R4R3A3S14G0R4R2A3A2F_;Ftp;Fp;Fq;").
Proof.
  intros q p tp H. unfold enspage in H. destruct (page_mem p tp); [right; exact H|].
  destruct H as [H|H]; [left; symmetry; exact H | right; exact H].
Qed.

Lemma pagedown_unique : ltac2:(tb__ "0|1|
SaSaScSaS3R2Z1000M0A2Z0A3SbS0R3R2A2S2R2S1R3G0A2A2A2ScSaS5S8R3G0A2G0A2R4A3F_;F_;Fa;Fq;").
Proof.
  intros q a Hal Hqa. pose proof (Z.div_mod q 4096 ltac:(lia)) as Dq. rewrite Hal, Z.add_0_r in Dq.
  set (m := q / 4096) in *.
  assert (E : a / 4096 = m) by (symmetry; apply (Z.div_unique a 4096 m (a - 4096 * m)); lia). rewrite E. lia.
Qed.

Lemma pagedown_aligned : ltac2:(tb__ "0|1|
SaScSaS3S9R1S3R1Z1000M0A2A2G0A2Z0A3Fs;").
Proof.
  intros s. pose proof (Z.div_mod s 4096 ltac:(lia)) as D. replace (s - s mod 4096) with ((s / 4096) * 4096) by lia. apply Z_mod_mult.
Qed.

Lemma pageZ_val : ltac2:(tb__ "0|1|
SaS31S0Z0R2A2S2S1R3S5Z1000M0S7R2A1A2A2S4Z2Z40A2A2ScSaS12Q40S38R4R3A2A2S1R4S5G0S7R3A1A2A2A3F_;F_;Fk;Fq;").
Proof. intros q k H0 H64. unfold pageZ. apply u64_of_lit. lia. Qed.

Lemma stack12_arith : ltac2:(tb__ "0|4|
SfSbScSaS3S35R1A1M0Z1000M1A2Z0A3SbS0Z7ffd8000G0A2SbS0G0S33R1A1M2A2SbS0S1G2Z9A2S36R1A1M3A2SbS0G3S1S4Z2Z3dA2Z7fff8000A2A2ScSaS1G0S5G1S7S34R1A1A1A2A2S1G2G1A2A3A2A2A2A2A2Frho;").
Proof.
  intros rho. pose proof (urange (rw rho 1%positive)) as U1.
  assert (D8 : 0 <= bv_unsigned (rw rho 1%positive) / 8 < 2 ^ 61).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; change (8 * 2 ^ 61) with (2 ^ 64); lia]. }
  assert (Hsh : 0x7fff8000 <= shZ rho <= 2 ^ 61 + 0x7fff8000) by (unfold shZ; lia).
  pose proof (Z.div_mod (shZ rho - 131072) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (shZ rho - 131072) 4096 ltac:(lia)) as M1.
  pose proof (Z.div_mod (shZ rho - 9) 4096 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (shZ rho - 9) 4096 ltac:(lia)) as M2.
  assert (Hle : (shZ rho - 131072) / 4096 <= (shZ rho - 9) / 4096) by (apply Z.div_le_mono; lia).
  assert (Hq : q12 rho = 4096 * ((shZ rho - 131072) / 4096)) by (unfold q12; lia).
  assert (He : e12 rho = 4096 * ((shZ rho - 9) / 4096)) by (unfold e12; lia).
  set (tq := (shZ rho - 131072) / 4096) in *. set (te := (shZ rho - 9) / 4096) in *.
  assert (Hn : Z.of_nat (n12 rho) = te - tq + 1).
  { unfold n12. rewrite Hq, He. replace (4096 * te - 4096 * tq) with ((te - tq) * 4096) by lia. rewrite Z_div_mult by lia. rewrite Z2Nat.id; lia. }
  split; [rewrite Hq; replace (4096 * tq) with (tq * 4096) by lia; apply Z_mod_mult|].
  rewrite Hn. lia.
Qed.

Lemma BD12 : ltac2:(tb__ "0|0|
SfS1fR1A1S37R2A1S2cS32R3A1S1dR3A1R3A3F_;F_;Frho;").
Proof.
  intros rho HD HZ p a Hp Ha H64 N1 N2. unfold TP12 in Hp. apply in_app_iff in Hp as [Hp|Hp].
  -
    pose proof (stack12_arith rho) as (QAL & QLO & QE & ESH & SHI & QN).
    apply In_pages_rev in Hp as (k & Hk & ->).
    apply Nat2Z.inj_lt in Hk.
    rewrite (pageZ_val (q12 rho) k) in Ha by lia.
    rewrite (HZ a) by lia. discriminate.
  -
    exact (HD a p Hp Ha H64 N1).
Qed.

Lemma BD17 : ltac2:(tb__ "0|5|
SaSfSfScSaR3S18R2A1A3SbS0Z7fff80000000R4A2S0R4S4Z2Z2fA2A2A2ScSaS3R5Z10A2Z0M0A3S11Q40M1A1M2S14G2R1S1eR6A1A3SbScSaS3S12G1R2A2M3Z1000M4A2G0A3SbS0S15G3A2S0S1G3G4A2S17R8A1A2A2A2F_;Fp;S2cS32R6A1S1dR6A1R6A3S1bR7R6A2S2cS19R8A1S1dR8A1R7A3F_;F_;F_;F_;F_;F_;Frho';Frho;Fx;").
Proof.
  intros x rho rho' Ex Hx H16 HT11 BD HRM p a Hp Ha H64 N1 N2.
  pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CHPal & CPEal & _ & _ & _ & CPEHP & CHPlo & CPEhi & CPEe & CHPq & Ce12al & _ & _).
  destruct (n16_val x Hx H16) as [N16 N16b]. destruct (site_arith x Hx H16) as (SQal & SQlo & _ & _ & SQPE & SEND & _).
  unfold RM6, RM16 in HRM. cbv zeta in HRM. rewrite <- Ex in HRM. destruct HRM as (R1 & R2 & R3 & R4 & R5).
  pose proof (stack12_arith rho) as (QAL & QLO & QE & ESH & SHI & QN).
  assert (Eq12 : q12 rho = q12x x) by (rewrite Ex; reflexivity).
  assert (Ee12 : e12 rho = e12x x) by (rewrite Ex; reflexivity).
  pose proof (urange p) as Up.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply u64_of_lit; lia).
  assert (UHP : bv_unsigned (Z_to_bv 64 (HPz x)) = HPz x) by (apply u64_of_lit; lia).
  set (t := tcls x) in *.

  destruct (Z_le_dec (HPz x + 512 * t) a) as [C1|C1]; [destruct (Z_lt_dec a (PEz x + 512 * t)) as [C2|C2]|].
  { rewrite (R2 a ltac:(lia)). discriminate. }
  -
    assert (H12 : In p (TP12 rho)).
    { apply In_TP17 in Hp as [(k & Hk & _ & Uk)|Hp]; [exfalso; rewrite Uk in Ha; unfold LOWPG in Ha; lia|].
      unfold TP16 in Hp. cbv zeta in Hp. rewrite <- Ex in Hp. apply in_app_iff in Hp as [Hp|Hp].
      - exfalso. apply In_pages_rev in Hp as (k & Hk & ->). apply Nat2Z.inj_lt in Hk. rewrite (pageZ_val (HPz x + 4096) k) in Ha by lia. lia.
      - apply In_enspage_inv in Hp as [->|Hp]; [exfalso; rewrite UHP in Ha; lia | exact Hp]. }
    rewrite (R1 (Z_to_bv 64 a)) by (rewrite Ua; unfold LOWPG; lia). exact (BD p a H12 Ha H64 N1 N2).
  -
    destruct (Z_le_dec (HPz x) a) as [C3|C3].
    +
      destruct (R3 a ltac:(lia)) as [E1 E2].
      destruct (page_mem (Z_to_bv 64 (HPz x)) (TP12 rho)) eqn:PMH; [apply page_mem_In in PMH; rename PMH into Hin | apply page_mem_false in PMH; rename PMH into Hnin].
      * rewrite (E1 Hin). apply (BD (Z_to_bv 64 (HPz x)) a Hin); [rewrite UHP; lia | exact H64 | exact N1 | exact N2].
      * rewrite (E2 Hnin). discriminate.
    +
      assert (HPQ : (exists k, (k < 5)%nat /\ p = Z_to_bv 64 (LOWPG + 4096 * Z.of_nat k) /\ bv_unsigned p = LOWPG + 4096 * Z.of_nat k) \/ In p (TP12 rho)).
      { apply In_TP17 in Hp as [HL|Hp]; [left; exact HL|]. right.
        unfold TP16 in Hp. cbv zeta in Hp. rewrite <- Ex in Hp. apply in_app_iff in Hp as [Hp|Hp].
        - exfalso. apply In_pages_rev in Hp as (k & Hk & ->). apply Nat2Z.inj_lt in Hk. rewrite (pageZ_val (HPz x + 4096) k) in Ha by lia. lia.
        - apply In_enspage_inv in Hp as [->|Hp]; [exfalso; rewrite UHP in Ha; lia | exact Hp]. }
      destruct (Z_le_dec LOWPG a) as [L1|L1]; [destruct (Z_lt_dec a (LOWPG + 0x5000)) as [L2|L2]|].
      *
        set (kz := (a - LOWPG) / 4096).
        assert (Kb : 0 <= kz < 5) by (unfold kz; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; unfold LOWPG in *; lia).
        assert (Kr : LOWPG + 4096 * kz <= a < LOWPG + 4096 * kz + 4096).
        { unfold kz. pose proof (Z.div_mod (a - LOWPG) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (a - LOWPG) 4096 ltac:(lia)). lia. }
        assert (Ek : Z.of_nat (Z.to_nat kz) = kz) by (apply Z2Nat.id; lia).
        set (q := Z_to_bv 64 (LOWPG + 4096 * Z.of_nat (Z.to_nat kz))).
        assert (Uq : bv_unsigned q = LOWPG + 4096 * kz) by (unfold q; rewrite Ek; apply u64_of_lit; unfold LOWPG; lia).
        destruct (page_mem q (TP16 rho)) eqn:PM.
        -- apply page_mem_In in PM. rewrite (R5 (Z.to_nat kz) ltac:(lia) PM (Z_to_bv 64 a)) by (rewrite Ua, Ek; lia).
           assert (In12 : In q (TP12 rho)).
           { unfold TP16 in PM. cbv zeta in PM. rewrite <- Ex in PM. apply in_app_iff in PM as [PM|PM].
             - exfalso. apply In_pages_rev in PM as (k & Hk & Ek'). apply (f_equal bv_unsigned) in Ek'. apply Nat2Z.inj_lt in Hk.
               rewrite Uq, (pageZ_val (HPz x + 4096) k) in Ek' by lia. unfold LOWPG in Ek'. lia.
             - apply In_enspage_inv in PM as [E|PM]; [exfalso; apply (f_equal bv_unsigned) in E; rewrite Uq, UHP in E; unfold LOWPG in E; lia | exact PM]. }
           apply (BD q a In12); [rewrite Uq; lia | exact H64 | exact N1 | exact N2].
        -- apply page_mem_false in PM. rewrite (R4 (Z.to_nat kz) ltac:(lia) PM a ltac:(rewrite Ek; lia)). discriminate.
      * rewrite (R1 (Z_to_bv 64 a)) by (rewrite Ua; lia).
        destruct HPQ as [(k & Hk & _ & Uk)|H12]; [exfalso; rewrite Uk in Ha; lia | exact (BD p a H12 Ha H64 N1 N2)].
      * rewrite (R1 (Z_to_bv 64 a)) by (rewrite Ua; lia).
        destruct HPQ as [(k & Hk & _ & Uk)|H12]; [exfalso; rewrite Uk in Ha; lia | exact (BD p a H12 Ha H64 N1 N2)].
Qed.

Lemma TP17_pages : ltac2:(tb__ "0|7|
SaSfScSaR2S18R1A1A3SbS0Z7fff80000000R3A2S0R3S4Z2Z2fA2A2A2ScSaS3R4Z10A2Z0M0A3S11Q40M1A1M2S14G2R1S1eR5A1A3SbScSaS3S12G1R2A2M3Z1000M4A2G0A3SbS0S15G3A2M5S0S1G3G4A2M6S17R7A1A2A2A2F_;Fp;G2S14G2R1S19R6A1A3SbG5S0G6S23A2A2F_;Fp;F_;F_;F_;F_;Frho;Fx;").
Proof.
  intros x rho Ex Hx H16 HT11 p Hp.
  pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & C79al & C80x8 & C80al & C80nn & C79lo & C79hi & Ctop1 & Ctop2 & Ctopal & Ctoplo & Cand & CHPal & CPEal & CPBal & CPB & CLEN & CPEHP & CHPlo & CPEhi & CPEe & CHPq & Ce12al & CLIM & CLIM0).
  clear C79al C80x8 C80al C80nn C79lo C79hi Ctop1 Ctop2 Ctopal Ctoplo Cand CLIM CLIM0 CPB CLEN CPBal.
  pose proof (stack12_arith rho) as (QAL & QLO & QE & ESH & SHI & QN).
  assert (Eq12 : q12 rho = q12x x) by (rewrite Ex; reflexivity).
  assert (Ee12 : e12 rho = e12x x) by (rewrite Ex; reflexivity).
  assert (Esh : shZ rho = shx x) by (rewrite Ex; reflexivity).
  pose proof (q12x_hi x Hx) as QHI.

  assert (EHI : e12x x + 4096 <= kHighMemBeg).
  { assert (Hsx : shx x <= kHighMemBeg) by (unfold shx, kHighMemBeg, SHADOW_BAND_HI; pose proof (Z.div_le_mono x (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D; change (2 ^ 47 / 8) with 17592186044416 in D; lia).
    apply Z.mod_divide in Ce12al as [ke Hke]; [|lia]. unfold kHighMemBeg, SHADOW_BAND_HI in *. rewrite <- Ee12, Hke in *. rewrite <- Esh in Hsx.
    assert (ke < 4295491704) by lia. lia. }
  apply In_TP17 in Hp as [(k & Hk & _ & Uk)|Hp].
  { rewrite Uk. unfold LOWPG. mlia. }
  unfold TP16 in Hp. cbv zeta in Hp. rewrite <- Ex in Hp.
  assert (S12 : In p (TP12 rho) -> SHADOW_BAND_LO <= bv_unsigned p /\ bv_unsigned p + 4096 <= kHighMemBeg).
  { intros Hq. unfold TP12 in Hq. apply in_app_iff in Hq as [Hq|Hq].
    - apply In_pages_rev in Hq as (k & Hk & ->). apply Nat2Z.inj_lt in Hk. rewrite (pageZ_val (q12 rho) k) by lia. mlia.
    - pose proof (HT11 p Hq) as (_ & L1 & L2). mlia. }
  destruct (n16_val x Hx H16) as [N16 N16b]. destruct (site_arith x Hx H16) as (_ & SQlo & _ & _ & SQPE & _).
  apply in_app_iff in Hp as [Hp|Hp].
  - apply In_pages_rev in Hp as (k & Hk & ->). apply Nat2Z.inj_lt in Hk. rewrite (pageZ_val (HPz x + 4096) k) by lia. mlia.
  - apply In_enspage_inv in Hp as [->|Hp]; [rewrite u64_of_lit by lia; mlia | exact (S12 Hp)].
Qed.

Lemma TP18_pages : ltac2:(tb__ "0|9|
SaSfScSaR2S18R1A1A3SbS0Z7fff80000000R3A2S0R3S4Z2Z2fA2M0A2A2ScSaS3R4Z10M1A2Z0M2A3S0S1R5Z50A2S22R4A1A2S0S1S22R5A1G1A2G0A2S0S1S22R6A1G1A2S1R7Z2228cfA2A2S11Q40M3A1M4S14G4R1S1eR8A1A3SbScSaS3S12G3R2A2M5Z1000M6A2G2A3SbS0S15G5A2M7S0S1G5G6A2M8S17RaA1A2A2A2F_;Fp;G4S14G4R1S24RaR9A2A3SbG7S0G8S23A2A2F_;Fp;F_;F_;F_;F_;F_;F_;F_;Frho;Fx;").
Proof.
  intros x rho Ex Hx H16 R1 R2 R3 HT11 p Hp.
  pose proof (arith18 x Hx H16 (r6of rho) R1 R2 R3) as AR.
  destruct AR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WK & _ & _ & QLO & QK & Q12Q & _ & _ & NE0 & NE1 & Q12LO).
  unfold TP18 in Hp. cbv zeta in Hp. destruct (Nat.eqb_spec (nE x (r6of rho)) 0) as [E0|E0]; [exact (TP17_pages x rho Ex Hx H16 HT11 p Hp)|].
  pose proof (NE1 E0) as HW.
  apply in_app_iff in Hp as [Hp|Hp].
  - apply In_pages_rev in Hp as (k & Hk & ->). apply Nat2Z.inj_lt in Hk. rewrite Nat2Z.inj_sub in Hk by lia. cbn [Z.of_nat Pos.to_nat] in Hk.
    rewrite (pageZ_val (Q18 x + 4096) k) by mlia. mlia.
  - apply In_enspage_inv in Hp as [->|Hp]; [|exact (TP17_pages x rho Ex Hx H16 HT11 p Hp)].
    rewrite u64_of_lit by mlia. mlia.
Qed.

Lemma BD18 : forall x rho rhoA rhoB pri, x = x1 rho -> 140735340871680 <= x <= 2 ^ 47 -> x mod 16 = 0 ->
  x + 80 <= r6of rho -> r6of rho + 16 <= 2 ^ 47 -> r6of rho + 16 <= x + 2238671 ->
  (forall p, In p (TP11 rho) -> bv_unsigned p mod 4096 = 0 /\ SHADOW_BAND_LO <= bv_unsigned p /\ bv_unsigned p + 4096 <= q12x x) ->
  BDT (TP17 rho) pri rhoA ->
  (forall a, SHADOW_BAND_LO <= a < q12x x -> ~ (pri <= a < pri + 512) -> ~ (LOWPG <= a < LOWPG + 0x4600) ->
     rm rhoB (Z_to_bv 64 a) = rm rhoA (Z_to_bv 64 a)) ->
  (forall a, q12x x <= a < kHighMemBeg -> Z.max (Q18 x) (Wz (r6of rho)) <= a -> rm rhoB (Z_to_bv 64 a) = rm rhoA (Z_to_bv 64 a)) ->
  ZX18 x (r6of rho) rhoB -> BDT (TP18 x rho) pri rhoB.
Proof.
  intros x rho rhoA rhoB pri Ex Hx H16 R1 R2 R3 HT11 BD HL HH HZ p a Hp Ha H64 N1 N2.
  pose proof (arith18 x Hx H16 (r6of rho) R1 R2 R3) as AR.
  destruct AR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WK & _ & _ & QLO & QK & Q12Q & _ & _ & NE0 & NE1 & Q12LO).

  assert (HP2 : In p (TP17 rho) \/ (Q18 x <= bv_unsigned p /\ bv_unsigned p + 4096 <= Wz (r6of rho))).
  { unfold TP18 in Hp. cbv zeta in Hp. destruct (Nat.eqb_spec (nE x (r6of rho)) 0) as [E0|E0]; [left; exact Hp|].
    pose proof (NE1 E0) as HW. apply in_app_iff in Hp as [Hp|Hp].
    - apply In_pages_rev in Hp as (k & Hk & ->). right. apply Nat2Z.inj_lt in Hk. rewrite Nat2Z.inj_sub in Hk by lia. cbn [Z.of_nat Pos.to_nat] in Hk.
      rewrite (pageZ_val (Q18 x + 4096) k) by mlia. mlia.
    - apply In_enspage_inv in Hp as [->|Hp]; [|left; exact Hp]. right. rewrite u64_of_lit by mlia. mlia. }
  destruct HP2 as [Hp17|[Qlo Qhi]].
  - pose proof (TP17_pages x rho Ex Hx H16 HT11 p Hp17) as [PLO PHI].
    destruct (Z.lt_ge_cases a (q12x x)) as [C1|C1].
    + rewrite (HL a ltac:(lia) N1 N2). exact (BD p a Hp17 Ha H64 N1 N2).
    + destruct (Z.lt_ge_cases a (Z.max (Q18 x) (Wz (r6of rho)))) as [C2|C2].
      * rewrite (HZ a ltac:(lia)). discriminate.
      * rewrite (HH a ltac:(mlia) C2). exact (BD p a Hp17 Ha H64 N1 N2).
  - rewrite (HZ a ltac:(lia)). discriminate.
Qed.

Lemma BD_frame : ltac2:(tb__ "0|4|
S2fS11Q40M0A1M1A1SaSfSfSaSaG1S14G1R1R7A3SbS0S15S12G0R2A2M2A2S0S1G2Z1000A2S23A2A2F_;Fp;SeS0R2S15A2S0S16R3A2A2G1SdSbS0R5S12G0R1A2M3A2S2G3R4A2A2A1ScS2eS11Q8A1A1S10R7R2A2S10R8R2A2A3F_;Fa;S2cR9R8R7A3S2cRaR9R7A3F_;F_;F_;F_;Fhi;Flo;FrhoB;FrhoA;Fpri;FT;").
Proof.
  intros T pri rhoA rhoB lo hi HT Hwin HF BD p a Hp Ha H64 N1 N2. pose proof (HT p Hp) as [PLO PHI].
  rewrite (HF (Z_to_bv 64 a)) by (rewrite u64_of_lit by mlia; mlia). exact (BD p a Hp Ha H64 N1 N2).
Qed.

Lemma TP11_pages : ltac2:(tb__ "0|5|
SaSfScSaR2S18R1A1A3SbS0Z7fff80000000R3A2S0R3S4Z2Z2fA2A2A2ScSaS3R4Z10A2Z0M0A3ScSaS12Q40M1S20R4A1A2S1dR4A1A3S0S1S1dR5A1Z200A2S1aR6A1A2ScSaS3S1dR6A1Z1000M2A2G0A3S0Z2008fff7000S1dR7A1A2S0S1S21R8A1Z2000A2S1aR9A1A2S11G1A1M3S14G3R1S1eRaA1A3SbScSaS3S12G1R2A2M4G2A2G0A3SbS0S15G4A2S0S1G4G2A2S17RcA1A2A2A2F_;Fp;F_;F_;F_;F_;F_;F_;F_;F_;Frho;Fx;").
Proof.
  intros x rho Ex Hx H16 UP PR1 PR2 PR3 SB1 p Hp.
  pose proof (class_arith x Hx H16) as CA. cbv zeta in CA.
  destruct CA as (Ct & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CHPal & _ & _ & _ & _ & CPEHP & CHPlo & CPEhi & _ & CHPq & _ & CLIM & _).
  assert (SB0 : 0x7fff8000 <= sbZ rho) by (unfold sbZ; pose proof (urange (rw rho 35%positive)); lia).
  pose proof (Z.mod_pos_bound (sbZ rho) 4096 ltac:(lia)) as MQ.
  assert (QB : q1Z rho <= sbZ rho < q1Z rho + 4096) by (unfold q1Z; lia).
  pose proof (pagedown_aligned (sbZ rho)) as QAL. change (sbZ rho - sbZ rho mod 4096) with (q1Z rho) in QAL. clear MQ.
  apply Z.mod_divide in PR2 as [kp Hkp]; [|lia]. apply Z.mod_divide in CHPal as [kh Hkh]; [|lia]. apply Z.mod_divide in QAL as [kq Hkq]; [|lia].
  assert (KP : kp <= kh) by lia.
  assert (KQ : kq + 2 <= kh) by lia.
  unfold TP11 in Hp. destruct (Z.eqb_spec (q1Z rho) (priZ rho)) as [EQ|NE].
  - assert (KPQ : kp = kq) by lia.
    destruct Hp as [<-|[<-|[<-|[]]]].
    + rewrite u64_of_lit by mlia. split; [rewrite Hkp; replace (kp * 4096 + 8192) with ((kp + 2) * 4096) by lia; apply Z_mod_mult | mlia].
    + rewrite u64_of_lit by mlia. split; [rewrite Hkp; replace (kp * 4096 + 4096) with ((kp + 1) * 4096) by lia; apply Z_mod_mult | mlia].
    + rewrite UP. split; [rewrite Hkp; apply Z_mod_mult | mlia].
  - destruct Hp as [<-|[<-|[<-|[<-|[]]]]].
    + rewrite u64_of_lit by mlia. split; [rewrite Hkq; replace (kq * 4096 + 8192) with ((kq + 2) * 4096) by lia; apply Z_mod_mult | mlia].
    + rewrite u64_of_lit by mlia. split; [rewrite Hkq; replace (kq * 4096 + 4096) with ((kq + 1) * 4096) by lia; apply Z_mod_mult | mlia].
    + rewrite u64_of_lit by mlia. split; [rewrite Hkq; apply Z_mod_mult | mlia].
    + rewrite UP. split; [rewrite Hkp; apply Z_mod_mult | mlia].
Qed.

Lemma lowb_adapter : forall x rhoL rhoA rhoB (o : out18) pri, 140735340871680 <= x <= 2 ^ 47 -> priZ rhoL = pri ->
  (forall a, SHADOW_BAND_LO <= a < kHighMemBeg -> grp_out o a) ->
  (forall a : bv 64, lowb x rhoL (bv_unsigned a) -> grp_out o (bv_unsigned a) -> rm rhoB a = rm rhoA a) ->
  forall a, SHADOW_BAND_LO <= a < q12x x -> ~ (pri <= a < pri + 512) -> ~ (LOWPG <= a < LOWPG + 0x4600) ->
    rm rhoB (Z_to_bv 64 a) = rm rhoA (Z_to_bv 64 a).
Proof.
  intros x rhoL rhoA rhoB o pri Hx Epri HG HL a Ha N1 N2. pose proof (q12x_hi x Hx) as QH.
  apply HL; rewrite u64_of_lit by mlia; [|apply HG; mlia]. unfold lowb. rewrite Epri. split; [exact Ha | split; [exact N1 | exact N2]].
Qed.

Lemma band_adapter : ltac2:(tb__ "0|3|
SaSaSfSfSbS0Z7fff80000000R4A2S0R4S4Z2Z2fA2A2A2S11Q40M0A1S29R6S12G0R1A2A2S0S6S25R7A1S26R6A1A2S12G0R2A2A2ScS2eS11Q8A1A1M1S10R5R3A2S10R6R3A2A3F_;F_;Fa;SaSbS0S17R7A1R1A2S2R1S23A2A2S0S6S25R8A1S26R7A1A2R2A2ScG1S10R6S13G0R3A2M2A2S10R7G2A2A3F_;F_;Fa;F_;F_;FrhoB;FrhoA;Fr6;Fx;").
Proof.
  intros x r6 rhoA rhoB Hx HH a Ha Hm.
  assert (Q0 : 0 <= q12x x).
  { unfold q12x, shx. pose proof (Z.mod_pos_bound (x / 8 + 2147450880 - 131072) 4096 ltac:(lia)). pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia. }
  apply HH; rewrite u64_of_lit by mlia; [unfold band; exact Ha | exact Hm].
Qed.

Lemma TP18_ext36 : ltac2:(tb__ "0|0|
SaSfSfS39P24R2R1A3ScS2fS11Q40A1A1S24R4R2A2S24R4R3A2A3F_;Frho';Frho;Fx;").
Proof.
  intros x rho rho' AG. pose proof AG as [AV AL]. unfold TP18, r6of. rewrite (AV 6%positive) by lia. unfold TP17. rewrite (TP16_ext rho rho' AG). reflexivity.
Qed.
End StartBD.

(* [comment removed for export] *)
Module Start8StatesA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "list"; "option"; "Some"; "app"; "prod"; "bool"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "mkLeafA"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "axst"; "@Corelib.Init.Decimal"; "D0"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "sobj"; "ss_objs"; "SVar"; "ss_next"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8StatesA"; "E23A"; "E24A"; "EGA"; "GPC"; "S23okA"; "S22okA"; "S24okA"; "SPIN22A"; "SPIN23A"; "SPIN24A"; "S23ok0A"; "E23A_R"; "E24A_R"; "EGA_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "fail_state"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0"; "E22A"; "F22"; "F23"; "F24"; "o13p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "axA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "mmap_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ob.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition S22okA : axst := ltac2:(tb__ "0|2|
S40S41S3bS42S12S3aA1M0S20P9fM1A1SaS1eS1fG0A1S4S1eS43G1Z100000A2S5S1eA1A3A3Pa0A4A2A1").
Lemma S22okA_eq : eager_ok E22A 0x100000 160%positive = S22okA.
Proof. reflexivity. Qed.
Definition E23A_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z706a0S4S0Z6bf18S5S0A1A3A3S2eS6A5").
Local Strategy expand [E23A_run__R].
Definition E23A_R : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) E23A_run__R).
Lemma E23A_run : ltac2:(tb__ "0|0|
S2S8S7SfA1A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z706a0S4S0Z6bf18S5S0A1A3A3S2eS6A5S34A3").
Proof. exact (@eq_refl (option (list leafA)) E23A_run__R <: E23A_run__R = E23A_R). Qed.
Definition E23A : axst := Eval vm_compute in (match E23A_R with Some (l :: _) => la_state l | _ => S22okA end).
Lemma run23A : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z706a0S4S0Z6bf18S5S0A1A3A3S2eS6A5S9G0S4SfS11S29S26A2S5SfA1A3A2A3").
Proof. rewrite E23A_run. reflexivity. Qed.
Definition run22A_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23U12cS4S0Z6bf18S5S0A1A3S37S3aA1S6A5").
Local Strategy expand [run22A_fail__R].
Definition SPIN22A : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => (leaf1 (fail_state E22A) (ro2__))) run22A_fail__R).
Lemma run22A_fail : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U12cS4S0Z6bf18S5S0A1A3S37S3aA1S6A5S9G0S4SfS11S30S26A2S5SfA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run22A_fail__R <: run22A_fail__R = Some [mkLeafA SPIN22A RsCut]). Qed.
Lemma spin22A : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U2S4S0Z6bf18S5S0A1A3S30S6A5S9G0S4SfS11S30S26A2S5SfA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E23A_at : ltac2:(tb__ "0|4|
S3S2S0S22S12S29A1M0A1M1Z706a0A3S3S2S1S21G0A1Pa0A3S3S2S8S38A1S27S23G1A2S9S38S39A2A3S3S2S7SbS1bS1bA2M2A1S13S29A1S5G2A1A3S3S2S1bS14S29A1S1cS3fA1A3S3S2S1bS1dG0Z11A2S1cZdeA1A3S3S2S1bS1dG0ZaA2S1cZ0A1M3A3S3S2S1bS1dG0ZbA2S1cZ800000A1A3S3S2S1bS1dG0ZcA2S1cZ3A1A3S3S2S1bS1dG0ZdA2S1cZ4022A1A3S3S2S1bS1dG0ZeA2S1cZffffffffffffffffA1A3S2S1bS1dG0ZfA2G3A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition S23ok0A : axst := ltac2:(tb__ "0|1|
S40S41S3cS42S12S29A1M0S20Pa0A1S1fG0A1Pa1A4A2A1").
Lemma S23ok0A_eq : null_rw_ok E23A 0x800000 161%positive = S23ok0A.
Proof. reflexivity. Qed.
Definition S23okA : axst := Eval vm_compute in set_objs' S23ok0A (ss_objs (ax_S S23ok0A) ++ [o13p]).
Lemma S23okA_eq : ltac2:(tb__ "0|2|
S3S2S16S15S33S28S12S33A1M0SaS1eS1fG0A1S4S1eS3eS5S1eA1A3A3A2M1A2S2dA3S2ScS44G0G1A2S6A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition E24A_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z706a0S4S0Z6bf18S5S0A1A3A3S2dS6A5").
Local Strategy expand [E24A_run__R].
Definition E24A_R : option (list leafA) := Eval vm_compute in ((fun ro3__ : option (list leafA) => ro3__) E24A_run__R).
Lemma E24A_run : ltac2:(tb__ "0|0|
S2S8S7SfA1A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z706a0S4S0Z6bf18S5S0A1A3A3S2dS6A5S35A3").
Proof. exact (@eq_refl (option (list leafA)) E24A_run__R <: E24A_run__R = E24A_R). Qed.
Definition E24A : axst := Eval vm_compute in (match E24A_R with Some (l :: _) => la_state l | _ => S23okA end).
Lemma run24A : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0Z706a0S4S0Z6bf18S5S0A1A3A3S2dS6A5S9G0S4SfS11S2aS26A2S5SfA1A3A2A3").
Proof. rewrite E24A_run. reflexivity. Qed.
Definition run23A_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23U12cS4S0Z6bf18S5S0A1A3S37S29A1S6A5").
Local Strategy expand [run23A_fail__R].
Definition SPIN23A : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => (leaf1 (fail_state E23A) (ro4__))) run23A_fail__R).
Lemma run23A_fail : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U12cS4S0Z6bf18S5S0A1A3S37S29A1S6A5S9G0S4SfS11S31S26A2S5SfA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run23A_fail__R <: run23A_fail__R = Some [mkLeafA SPIN23A RsCut]). Qed.
Lemma spin23A : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U2S4S0Z6bf18S5S0A1A3S31S6A5S9G0S4SfS11S31S26A2S5SfA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E24A_at : ltac2:(tb__ "0|4|
S3S2S0S22S12S2aA1M0A1M1Z706a0A3S3S2S1S21G0A1Pa1A3S3S2S8S38A1S27S23G1A2S9S38S39A2A3S3S2S7SbS1bS1bA2M2A1S13S2aA1S5G2A1A3S3S2S1bS14S2aA1S1cS3fA1A3S3S2S1bS1dG0Z11A2S1cZdeA1A3S3S2S1bS1dG0ZaA2S1cZ0A1M3A3S3S2S1bS1dG0ZbA2S1cZ1000A1A3S3S2S1bS1dG0ZcA2S1cZ3A1A3S3S2S1bS1dG0ZdA2S1cZ22A1A3S3S2S1bS1dG0ZeA2S1cZffffffffffffffffA1A3S2S1bS1dG0ZfA2G3A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition S24okA : axst := ltac2:(tb__ "0|2|
S40S41S3dS42S12S2aA1M0S20Pa1M1A1SaS1eS1fG0A1S4S1eS43G1Z1000A2S5S1eA1A3A3Pa2A4A2A1").
Lemma S24okA_eq : eager_ok E24A 4096 162%positive = S24okA.
Proof. reflexivity. Qed.
Definition GPC : Z := 0x4a180.
Definition EGA_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0S2cS4S0Z706a0S4S0Z6bf18S5S0A1A3A3A3S2fS6A5").
Local Strategy expand [EGA_run__R].
Definition EGA_R : option (list leafA) := Eval vm_compute in ((fun ro5__ : option (list leafA) => ro5__) EGA_run__R).
Lemma EGA_run : ltac2:(tb__ "0|0|
S2S8S7SfA1A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0S2cS4S0Z706a0S4S0Z6bf18S5S0A1A3A3A3S2fS6A5S36A3").
Proof. exact (@eq_refl (option (list leafA)) EGA_run__R <: EGA_run__R = EGA_R). Qed.
Definition EGA : axst := Eval vm_compute in (match EGA_R with Some (l :: _) => la_state l | _ => S24okA end).
Lemma runGA : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23S24S25S18S19S17S17S17S1aA1A1A1A1A1A1A1S4S0S2cS4S0Z706a0S4S0Z6bf18S5S0A1A3A3A3S2fS6A5S9G0S4SfS11S2bS26A2S5SfA1A3A2A3").
Proof. rewrite EGA_run. reflexivity. Qed.
Definition run24A_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S10S23U12cS4S0Z6bf18S5S0A1A3S37S2aA1S6A5").
Local Strategy expand [run24A_fail__R].
Definition SPIN24A : axst := Eval vm_compute in ((fun ro6__ : option (list leafA) => (leaf1 (fail_state E24A) (ro6__))) run24A_fail__R).
Lemma run24A_fail : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U12cS4S0Z6bf18S5S0A1A3S37S2aA1S6A5S9G0S4SfS11S32S26A2S5SfA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run24A_fail__R <: run24A_fail__R = Some [mkLeafA SPIN24A RsCut]). Qed.
Lemma spin24A : ltac2:(tb__ "0|1|
S2S8S7SfA1M0A1S10S23U2S4S0Z6bf18S5S0A1A3S32S6A5S9G0S4SfS11S32S26A2S5SfA1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma EGA_at : ltac2:(tb__ "0|2|
S3S2S0S22S12S2bA1M0A1S2cA3S3S2S1S21G0A1Pa2A3S3S2S7SbS1bS1bA2M1A1S13S2bA1S5G1A1A3S3S2S1bS14S2bA1S1cS3fA1A3S2SeSdS1eS1fG0A1A2U31A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start8StatesA.

