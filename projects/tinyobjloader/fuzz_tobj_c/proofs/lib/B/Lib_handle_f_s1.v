(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "app"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "sv"; "SLit"; "sprop"; "SPUle"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@Corelib.Lists.ListDef"; "seq"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "tL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pA"; "pD2"; "slot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1"; "E_da"; "E_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2"; "Pre_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Lib_byteloops.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition T_ms : axst := Eval vm_compute in bl_forget (bl_prune HNEXT (leaf_at JR_co hf_ZX 0)) [32%nat].
Goal shape T_ms = shape JR_co. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs T_ms = [(pc_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition xslot (d c : sv) : sv * sv := ltac2:(tb__ "0|0|
S4S7S7Vd;S6S10S6SfS19Vd;Vc;A2S8ZcA1A3Vd;A3A4").
Definition xf_pc : list axform := ltac2:(tb__ "0|2|
S0SdSeU0S8N70A1A2S0SdSeU21S14ZcM0S17A2M1A2S0SdSeU22S6SfG1S8G0A1A3A2S2SdA1A3A3A3").
Definition E_pc0 : axst := Eval vm_compute in leaf_at T_ms pc_entry 0.
Definition E_pc1 : axst := Eval vm_compute in optAp (apply_axforms E_pc0 xf_pc).

Definition pc_need (t q : sv) : list sprop := ltac2:(tb__ "0|0|
S0S9SaS6SfVt;S6S10Vq;Vt;A3A3S15A2S2S9A1A3").
Definition E_pc : axst := Eval vm_compute in ax_add_facts (pc_need pT0 pQ) (ax_setX (reshapeA E_pc1 34 (slot_obj pD2 pA)) (xslot pD2 pA :: ax_X E_pc1)).
Definition s_pc : wsub := ltac2:(tb__ "0|0|
S0S5S12S7A2S4S12S7P38S18A4S13PaScS1bA1ScS1cA1A3A3").
Definition R_pc : list sobj := Eval vm_compute in optR (entails_frA E_pc Pre_pc s_pc).
Goal entails_frA E_pc Pre_pc s_pc = Some R_pc /\ call_checkA E_pc Pre_pc s_pc R_pc (map la_state Posts_pc) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_pure (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S1dSbScVCl;A1A1S1eVs;VPre;VL;VCl;VR;A5A2").
Definition T_pc0 : axst := Eval vm_compute in T_pure Pre_pc E_pc s_pc R_pc P_ret.
Goal lvs T_pc0 = [(hf_H, RsCut); (hf_H, RsCut); (da_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition sel_pc : list nat := ltac2:(tb__ "0|1|
S3S1S0S1U5S0S1U0S0S1U6S0S1U7S0S1U3S0S1U4S0S1U8S2S1A1M0A3A3A3A3A3A3A3S3S1S11U9U11A2S0S1U1aS0S1U1bS0S1U1cS0S1U1S0S1U1dS0S1U1eS0S1U1fS0S1U20S0S1U21S0S1U22S0S1U2S0S1U23S0S1U24S0S1U25S0S1U26G0A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition T_pc1 : axst := Eval vm_compute in reshapeA T_pc0 2 (mid_slot pD2 pA DUnknown).
Definition T_pc : axst := Eval vm_compute in ax_setX (optAp (apply_axforms T_pc1 [AXSelect sel_pc; AXMerge 0; AXMerge 32; AXMerge 32])) (X_body pD2 pK2).
Goal shape T_pc = shape JR_co. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs T_pc = [(hf_H, RsCut); (hf_H, RsCut); (da_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal map (fun L => leaf_matches1A NPH L H) (leavesA_at FUEL_hf cutpcs_hf T_pc hf_H) = [true; true]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_da0 : axst := Eval vm_compute in leaf_at T_pc da_entry 0.
Definition E_da : axst := Eval vm_compute in optAp (apply_axforms E_da0 [AXSplit 0 (SLit (-96))]).
Definition s_da : wsub := ltac2:(tb__ "0|0|
S13PaScS1aA1ScS16A1A3").
Definition R_da : list sobj := Eval vm_compute in optR (entails_frA E_da Pre_da s_da).
Goal entails_frA E_da Pre_da s_da = Some R_da /\ call_checkA E_da Pre_da s_da R_da (map la_state Posts_da) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_da0 : axst := Eval vm_compute in T_pure Pre_da E_da s_da R_da P_da.

Definition sel_da : list nat := ltac2:(tb__ "0|0|
S3S1S0S1U3S0S1U0S0S1U4S0S1U5S0S1U1S0S1U2S2S1A1A3A3A3A3A3A3S11U6U1fA2A3").
Definition T_da : axst := Eval vm_compute in ax_setX (optAp (apply_axforms T_da0 [AXSelect sel_da; AXMerge 0])) (X_body pD2 pK2).
Goal shape T_da = shape JR_co. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Goal lvs T_da = [(hf_H, RsCut)] /\ map (fun L => leaf_matches1A NPH L H) (leavesA_at FUEL_hf cutpcs_hf T_da hf_H) = [true].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
