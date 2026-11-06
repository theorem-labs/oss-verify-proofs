(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ef Lib_vec_finalize e7 Lib_builderH_defs eh.

(* [comment removed for export] *)
Module Lib_intern_rest_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "ss_objs"; "sprop"; "ss_facts"; "SLit"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "app"; "nil"; "list"; "Some"; "length"; "nat"; "option"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXSplit"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_intern_rest"; "X_sretc2"; "X_sretn2"; "vN"; "X_fitc"; "X_fitn"; "X_ret2"; "X_sretc1"; "X_sretn1"; "E_m"; "Pre_m"; "R_m"; "X_nofit1"; "X_ret"; "fit_facts"; "new_facts"; "p_fit"; "p_new"; "s_m"; "C_open"; "FUEL_ir"; "T_mnull"; "T_mok0"; "X_fitc3"; "X_fitn3"; "X_nofit2"; "X_open"; "X_ret3"; "X_sretc"; "X_sretc3"; "X_sretn"; "X_sretn3"; "cutpcs_ir"; "cutsI"; "exitsI"; "nofit_fact"; "vHDi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_intern_rest_eqs"; "objsR"; "objsNc"; "objsNn"; "ohNc"; "ohNn"; "ohR"; "sel_c"; "sel_n"; "ohFc"; "ohFn"; "osR"; "otNc"; "otNn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "carve_stateA"; "drop_lastA"; "open_stateA"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "ulink"; "L_malloc_null"; "L_malloc_ok"; "@Stdlib.Lists.List"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ejcertA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_intern_rest.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Module AAP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_alloc_pf. End AAP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import IRAddr RA.ReallocAddr.
Local Open Scope lazy_bool_scope.

Definition ohFc : sobj := Eval vm_compute in last (ss_objs (ax_S X_fitc)) O_Wi.
Definition ohFn : sobj := Eval vm_compute in last (ss_objs (ax_S X_fitn)) O_Wi.

Definition iNc : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) (SVar pN)) (ss_objs (ax_S X_sretc)) 0%nat.
Definition sel_c : list nat := Eval vm_compute in (List.filter (fun j => negb (Nat.eqb j iNc)) (seq 0 (length (ss_objs (ax_S X_sretc))))) ++ [iNc].
Definition iNn : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) (SVar pN)) (ss_objs (ax_S X_sretn)) 0%nat.
Definition sel_n : list nat := Eval vm_compute in (List.filter (fun j => negb (Nat.eqb j iNn)) (seq 0 (length (ss_objs (ax_S X_sretn))))) ++ [iNn].
Definition objsNc : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sretc1))).
Definition ohNc : sobj := Eval vm_compute in nth (length objsNc) (ss_objs (ax_S X_sretc1)) O_Wi.
Definition otNc : sobj := Eval vm_compute in nth (S (length objsNc)) (ss_objs (ax_S X_sretc1)) O_Wi.
Definition objsNn : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sretn1))).
Definition ohNn : sobj := Eval vm_compute in nth (length objsNn) (ss_objs (ax_S X_sretn1)) O_Wi.
Definition otNn : sobj := Eval vm_compute in nth (S (length objsNn)) (ss_objs (ax_S X_sretn1)) O_Wi.

Definition objsR : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_ret))).
Definition ohR : sobj := Eval vm_compute in nth (length objsR) (ss_objs (ax_S X_ret)) O_Wi.
Definition osR : sobj := Eval vm_compute in nth (S (length objsR)) (ss_objs (ax_S X_ret)) O_Wi.

Lemma C_open_eq : ltac2:(tb__ "0|0|
S5S10S4aS30S3aA2S29A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S5S10S4cS20S1fS28S21S50S4dS8S4fA1S4eA3A5S2bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S5S10S4cS20S1fS28S21S51S4dS8S4fA1S4eA3A5S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_nofit2_eq : ltac2:(tb__ "0|0|
S5S10S16S22S6S2S39S3S11S22A1A1A3A2S2fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsFc_eq : ltac2:(tb__ "0|1|
S5S9S0A1S1S11S1aA1A1M0S7S0S52S0G0A2S6S0S43S8S0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsFn_eq : ltac2:(tb__ "0|1|
S5S9S0A1S1S11S1bA1A1M0S7S0S52S0G0A2S6S0S44S8S0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_fitc3_eq : ltac2:(tb__ "0|0|
S5S10S16S48S1aS26S19A3S7S2S24S3S11S1aA1A1A3A2S2dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_fitn3_eq : ltac2:(tb__ "0|0|
S5S10S16S48S1bS26S19A3S7S2S24S3S11S1bA1A1A3A2S2eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sretc1_eq : ltac2:(tb__ "0|0|
S5SdS10A1S15S32S6S12S13S41A1S6S12S14S4bSbScS41A2U1A2S4Z18A1A2S8S12A1A3A3A2SaS10S1dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sretn1_eq : ltac2:(tb__ "0|0|
S5SdS10A1S15S34S6S12S13S42A1S6S12S14S4bSbScS42A2U1A2S4Z18A1A2S8S12A1A3A3A2SaS10S1eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsNc_eq : ltac2:(tb__ "0|1|
S5S9S0A1S1S11S1dA1A1S7S0S7S0S3cS6S0S3eS8S0A1M0A3A3S6S0S46G0A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsNn_eq : ltac2:(tb__ "0|1|
S5S9S0A1S1S11S1eA1A1S7S0S7S0S3dS6S0S3fS8S0A1M0A3A3S6S0S47G0A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sretc2_eq : ltac2:(tb__ "0|0|
S5S10S49S1dS7S0S3cS6S0S3eS8S0A1A3A3A2S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sretn2_eq : ltac2:(tb__ "0|0|
S5S10S49S1eS7S0S3dS6S0S3fS8S0A1A3A3A2S18A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsNc2_eq : ltac2:(tb__ "0|0|
S5S9S0A1S1S11S17A1A1S7S0S3cS6S0S3eS8S0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsNn2_eq : ltac2:(tb__ "0|0|
S5S9S0A1S1S11S18A1A1S7S0S3dS6S0S3fS8S0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sretc3_eq : ltac2:(tb__ "0|0|
S5S10S16S48S17S27S19A3S7S2S25S3S11S17A1A1A3A2S33A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sretn3_eq : ltac2:(tb__ "0|0|
S5S10S16S48S18S27S19A3S7S2S25S3S11S18A1A1A3A2S35A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsR_eq : ltac2:(tb__ "0|1|
S5S9S0A1S1S11S23A1A1S7S0S7S0S3bS6S0S40S8S0A1M0A3A3S6S0S45G0A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_ret2_eq : ltac2:(tb__ "0|0|
S5S10S49S23S7S0S3bS6S0S40S8S0A1A3A3A2S1cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsR2_eq : ltac2:(tb__ "0|0|
S5S9S0A1S1S11S1cA1A1S7S0S3bS6S0S40S8S0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_ret3_eq : ltac2:(tb__ "0|0|
S5S10S49S1cS3bA2S31A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ejcertI_ok : ltac2:(tb__ "0|0|
S5SeS55S53S54S2aS36P64S37S38A7SfA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_intern_rest_eqs.

(* [comment removed for export] *)
Module Lib_intern_rest_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "list"; "prod"; "pair"; "nil"; "app"; "false"; "fst"; "Some"; "nat"; "option"; "snd"; "None"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "valuation"; "SLit"; "SPUle"; "ss_facts"; "sobj"; "SAlu"; "ss_next"; "sprop_eqb"; "SVar"; "sv_eqb"; "holds"; "SPBranch"; "ob_base"; "ob_hi"; "ob_lo"; "ss_objs"; "sv_below"; "cell"; "ob_dflt"; "obj_range"; "sprop_below"; "swf"; "DUnknown"; "SPNot"; "dflt_writable"; "odefault"; "rw"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "mul"; "lt"; "sub"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "entailsA"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "BI"; "batom"; "ASv"; "KU"; "bd_subst"; "bud_le"; "bd_wpos"; "bsumK"; "bsumV"; "bd_nn"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "O_got"; "O_rtc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_intern_rest"; "vN"; "vHDi"; "vCAP"; "tv_ir"; "vBld"; "vK"; "p_fit"; "vU"; "p_new"; "bd_slow"; "nd0"; "ndO"; "vARi"; "P_fail"; "P_ok"; "X_ir"; "am_np"; "bd_m2"; "cutsI"; "ndF"; "ndK"; "ndL"; "ndMok"; "ndS"; "s_m"; "vC1"; "vC2"; "vDp"; "vUg"; "E_m"; "P_b8"; "Pre_ir"; "R_m"; "am_loop"; "bd_loop"; "bd_open"; "fit_facts"; "ndKc"; "new_facts"; "spm"; "two40"; "vLEN"; "CHi"; "CHn"; "C_K"; "O_Wi"; "X_K1"; "X_K2"; "X_fitc"; "X_fitn"; "X_nofit"; "X_nohead"; "X_open"; "X_ret"; "X_sretc"; "X_sretn"; "bd_K"; "bd_m"; "exitsI"; "pN"; "vNX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "potK"; "potV"; "NDA"; "am_eqb"; "am_subst"; "nd_below"; "AOpen"; "JA_pre"; "emeasA"; "JA"; "JLA"; "nodeIA"; "ok_frameKA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "BC_EQ"; "BC_GEU"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_intern_rest_pf"; "P0_ir"; "baseFI"; "ccF"; "basezI"; "objclass"; "openF"; "base_factsI"; "cc_facts"; "open_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "vB"; "vL"; "vE"; "vI"; "O_txt"; "two26"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "carve_stateA"; "e32"; "POT"; "xrs_ok47"; "drop_lastA"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pclMA"; "xr_eqb"; "FFx";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_intern_rest_pf.Sum"; "Posts_ir"; "JL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "ulink"; "J_alloc_pre"; "Posts_malloc"; "Pre_malloc"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "uleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "FBx"; "T0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXSplit"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "payA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "hdr_shape"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_intern_rest OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_intern_rest_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import IRAddr ScanDoubleAddr RA.ReallocAddr.
Local Open Scope lazy_bool_scope.

Definition P0_ir (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S1S3S1S31S3dVr;Sb0A2M0R1A2S35R1S32G0S3dVr;Sb1A2A2A2A2SceVCST;Vr;VFB;VFF;R2A5F_;Fa;SebVFF;S3dVr;S51A2Z518A3A2").

Definition is_xo (o : sobj) : bool := ltac2:(tb__ "0|4|
S4S4L_;M0G0S1fS22Vo;A1M1S51A2G0S1fS24Vo;A1M2S17Z8A1A2S1fS23Vo;A1M3S17Z10A1A2ScX4x2ScX4x2S5G0S1fG1Sb0A2G0S1fG2S17Z0A1A2S1fG3Sb1A2ScX4x2ScX4x2X4x2").
Definition is_xX (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S4S4L_;ScfVr;S9S15S15S51S17Z518A1A4A2S5ScfVr;S9S15S15Sb0Sb1A4A2X4x2").

Definition base_factsI : list sprop := ltac2:(tb__ "0|5|
S6S14S18S1ePaA1M0S17Sb6A1M1A2S6S14S18S1eP1eA1M2S1bS9fS74Z50A1M3S68A3A2S6S14S18G2G3A2S6S14S18G2G0A2S6S14S21Sa0S17N1000A1S68A3S6S14S21Sa0S68S17S37S75A1A1A3S6S14S18S17SeeA1S51A2S6S14S18S1bS9fS51S17Z518A1A3G2A2S6S14S18S17Z1000A1S59A2S6S14S18S1bS9fS59S17Z40A1A3G2A2S6S14S18Sb3Sb2A2S6S14S18Sb2Sb1A2S6S14S18Sb1S17Sb5A1A2S6S14S18S17Z1A1Sb0A2S6S14S18S1bS9fSb0Sb1A3S17Z7fffff800000A1M4A2S6S14S18S51G1A2S6S14S18S59G1A2S6S14S18Sb0G1A2S6S14S18S17Z7fff7f800000A1G2A2S6S14S18G2G4A2SaS14A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition baseFI (F : list sprop) : bool := ltac2:(tb__ "0|0|
Sa5S14S14Sa3S14S1dR1A1VF;A3Lp;SadA3").
Record basezI (rho : valuation) : Prop := BZI {
  bz_sp : aceil + 80 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_win : forall a, fst (obj_range rho O_Wi) <= a < snd (obj_range rho O_Wi) -> bv_unsigned (rw rho V_TOP) <= a < uval rho (SVar 10) - 80;
  bz_b : IMG_HI <= uval rho vBld /\ uval rho vBld + 1304 <= bv_unsigned (rw rho V_TOP);
  bz_ar : 4096 <= uval rho vARi /\ uval rho vARi + 64 <= bv_unsigned (rw rho V_TOP);
  bz_txt : uval rho vI <= uval rho vE /\ uval rho vE <= uval rho vL /\ uval rho vL <= 2 ^ 26;
  bz_B : 1 <= uval rho vB /\ uval rho vB + uval rho vL <= 140737479966720;

  bz_top : bv_unsigned (rw rho V_TOP) + 80 <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm80 : ltac2:(tb__ "0|2|
S16S31Z50M0S3dR1S1ePaA1M1A2A2S0S3S3dR2S74G0A1A2S36S3dR2G1A2G0A2A3F_;Frho;").
Proof.
  intros rho Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - 80) with (x - 80) by lia. apply Z.mod_small. lia.
Qed.
Lemma basezI_of : ltac2:(tb__ "0|0|
S16S7S14A1SbcS14S20R2A1R1A3S0S4Sa8R2A1S5A3SaaR4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold baseFI in HB.
  assert (G : forall p, In p base_factsI -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [base_factsI] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  pose proof (G _ ltac:(do 6 right; left; reflexivity)) as F7. pose proof (G _ ltac:(do 7 right; left; reflexivity)) as F8.
  pose proof (G _ ltac:(do 8 right; left; reflexivity)) as F9. pose proof (G _ ltac:(do 9 right; left; reflexivity)) as F10.
  pose proof (G _ ltac:(do 10 right; left; reflexivity)) as F11. pose proof (G _ ltac:(do 11 right; left; reflexivity)) as F12.
  pose proof (G _ ltac:(do 12 right; left; reflexivity)) as F13. pose proof (G _ ltac:(do 13 right; left; reflexivity)) as F14.
  pose proof (G _ ltac:(do 14 right; left; reflexivity)) as F15. pose proof (G _ ltac:(do 15 right; left; reflexivity)) as F16.
  pose proof (G _ ltac:(do 16 right; left; reflexivity)) as F17. pose proof (G _ ltac:(do 17 right; left; reflexivity)) as F18.
  pose proof (G _ ltac:(do 18 right; left; reflexivity)) as F19. pose proof (G _ ltac:(do 19 right; left; reflexivity)) as F20.
  rewrite h_ule in F1, F2, F3, F4, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20.
  apply (proj1 (holds_bge _ _ _)) in F5. apply (proj1 (holds_bge _ _ _)) in F6.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *.
  unfold two47, two26, two40, RA.two40 in *. unfold IMG_HI in *.
  rewrite !uval_lit in F1, F7, F9, F13, F14, F16, F17, F18, F19, F20 by lia. rewrite uval_lit in F15 by lia.
  change (uval rho (SLit (-4096))) with (bv_unsigned (eval rho (SLit (-4096)))) in F5. rewrite U_lit in F5. change ((-4096) mod M64v) with 18446744073709547520 in F5.
  change (uval rho (SLit (- 2 ^ 40))) with (bv_unsigned (eval rho (SLit (- 2 ^ 40)))) in F6. rewrite U_lit in F6.
  change ((- 2 ^ 40) mod M64v) with 18446742974197923840 in F6.
  pose proof (uval_range rho vBld) as Rb. pose proof (uval_range rho vARi) as Rar. pose proof (uval_range rho vB) as RB. pose proof (uval_range rho vL) as RL.
  rewrite uval_add_small in F8 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F8 by lia.
  rewrite uval_add_small in F10 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F10 by lia.
  rewrite uval_add_small in F15 by lia.
  rewrite uval_spm80 in F3 by lia.
  pose proof (uval_range rho vDp) as RD.
  destruct (Zsigned_spec (uval rho vDp)) as [[L1 E1]|[L1 E1]]; rewrite E1 in F5, F6;
    [destruct (Zsigned_spec 18446744073709547520) as [[? E2]|[? E2]]; rewrite E2 in F5; lia|].
  destruct (Zsigned_spec 18446744073709547520) as [[? E2]|[? E2]]; rewrite E2 in F5; [lia|].
  destruct (Zsigned_spec 18446742974197923840) as [[? E3]|[? E3]]; rewrite E3 in F6; [lia|].
  assert (EA : uval rho (SAlu ALU_ADD (spm 80) vDp) = uval rho (SVar 10) - 80 + (uval rho vDp - 2 ^ 64)).
  { unfold uval at 1. rewrite U_add. change (bv_unsigned (eval rho (spm 80))) with (uval rho (spm 80)). change (bv_unsigned (eval rho vDp)) with (uval rho vDp).
    rewrite uval_spm80 by lia. unfold M64v.
    replace (uval rho (SVar 10) - 80 + uval rho vDp) with ((uval rho (SVar 10) - 80 + (uval rho vDp - 2 ^ 64)) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite EA in F2.
  constructor; unfold aceil, IMG_HI; try lia.
  intros a Hr. unfold obj_range, obj_lo_of, obj_hi_of, O_Wi in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. change (bv_unsigned (eval rho (spm 80))) with (uval rho (spm 80)) in Hr. rewrite uval_spm80 in Hr by lia.
  unfold soff in Hr. rewrite bv_signed_U in Hr. change (bv_unsigned (eval rho vDp)) with (uval rho vDp) in Hr. rewrite E1 in Hr. lia.
Qed.
Ltac basez_tac HF := exact (basezI_of _ _ HF ltac:(vm_compute; reflexivity)).

Lemma P0_now : ltac2:(tb__ "0|3|
S7S8S3S3A2M0A1M1G1S7S8G0S3A2A1S16S16Sa7R5R4R3R2A4Sf2S8fR3R2A3S1S3S1S31S3dR4Sb0A2M2R1A2S35R1S32G2S3dR4Sb1A2A2A2A2SceR9R6R8R7R2A5F_;Fa;SebR5S3dR3S51A2Z518A3A2F_;F_;Frho;Frho0;FFF;FFB;FCST;").
Proof.
  intros CST FB FF rho0 rho [HT Hb] [Hav _]. unfold uval in *. cbn [eval vB vL vBld] in *.
  rewrite <- (Hav 15%positive) by reflexivity. rewrite <- (Hav 18%positive) by reflexivity. rewrite <- (Hav 12%positive) by reflexivity.
  split; [exact HT | exact Hb].
Qed.
Lemma pclMA_x : ltac2:(tb__ "0|2|
S7S8S3S3A2M0A1M1S16G1S7S8G0S3A2A1S16S7S8S15S15A2A1S7S8S8S15S3A2S15A2A1S3SceR8R7R6R5R1A5SceR9R8Se5R7R5R4A3Sd0R6R5R3A3R2A5F_;Fa;Ffr;Ftv;Frho;FFF;FFB;Frho0;FCST;").
Proof.
  intros CST rho0 FB FF rho tv fr a [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. split; [apply In_FBx; left; exact Hin | exact Hr].
  - right; right; right. exists f, s, fl. split; [apply In_FFx; left; exact Hin | exact Hr].
Qed.
Lemma txt_range : ltac2:(tb__ "0|2|
S16S3SaaR2A1S1S31SdS3S3S29R3Sb4SaS27A1A1A2M0A3R2A2S35R2S11S3S3G0A3A2A2S1S31S3dR4Sb0A2M1R3A2S35R3S32G1S3dR4Sb1A2A2A2A2F_;F_;Fa;Frho;").
Proof.
  intros rho a BZ Hr. destruct BZ as [_ _ _ _ T1 T2 TT]. unfold obj_range, obj_lo_of, obj_hi_of, O_txt in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite (soff_smallu rho vL) in Hr by lia. unfold uval in *. lia.
Qed.
Lemma b8_range : ltac2:(tb__ "0|2|
S16S3SaaR2A1S1S31SdS3S3S29R3S6bA2M0A3R2A2S35R2S11S3S3G0A3A2A2S1S31S3dR4S51A2M1R3A2S35R3S32G1Z518A2A2A2F_;F_;Fa;Frho;").
Proof. intros rho a BZ Hr. unfold P_b8 in Hr. apply range_lit' in Hr; lia. Qed.

Definition objclass (o : sobj) : Prop := ltac2:(tb__ "0|5|
S2S1S0S15S22Vo;A1M0S1ePaA1A3S1S0S15S24Vo;A1M1S17N50A1A3S1S0S15S23Vo;A1M2S17Z0A1M3A3S0S2fS28Vo;A1S2cA3M4A2A2A2S2S0S1aVo;S7aA3S2S0S1aVo;S6bA3S2S1S0S15G0S59A3S1S0S15G1G3A3S1S0S15G2S17Z40A1A3G4A2A2A2S2S2S0S1aVo;S4bA3S0S1aVo;S4cA3A2S0S1aVo;Sb4SaS27A1A1A3A2A2A2A2A2").
Lemma objs_ok_ir : ltac2:(tb__ "0|3|
S7S8S3S3A2M0A1M1S16G1S7S8G0S3A2A1S16S7S1aA1SaaR2A1S3S1S31S3dR4Sb0A2M2R1A2S35R1S32G2S3dR4Sb1A2A2A2A2SceR9R8R7R6R2A5F_;Fa;SebR5S3dR4S51A2Z518A3S1aSa4S1aR1R5A3SabR2A1F_;Fo;S0S3Se6R9A1S8eQ40S30R6SdcA2A2A3Sc8RbRaR9R8R7S50SaS8S8S15S3A2S15A2A1R6A8F_;F_;F_;F_;F_;Fobjs;Frho;FFF;FFB;Frho0;FCST;").
Proof.
  intros CST rho0 FB FF rho objs BZ HT Hb Hcls ET o a Ho Hr. pose proof BZ as [Bsp Bwin Bb Bar Btxt BB Btop].
  destruct (Hcls o Ho) as [(H1 & H2 & H3 & H4)|[->|[->|[(H1 & H2 & H3 & H4)|[[->| ->]| ->]]]]].
  - left. left. destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi ob_dflt] in H1, H2, H3, H4. subst.
    apply range_lit' in Hr; [|lia|lia]. lia.
  - left. left. pose proof (Bwin a Hr). lia.
  - left. apply pclMA_x. eapply (infrFF_pclMA CST rho0 FF FB rho) in Hb; [| exact (b8_range rho a BZ Hr)].
    unfold FFx in Hb. cbn [map] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - left. right; right; left. exists (uval rho vARi), 64. split.
    + apply In_FBx. right. exists (vARi, SLit 64). split; [left; reflexivity|]. split; [unfold tnz; cbn [fst]; unfold uval in Bar; lia|].
      unfold tvv. cbn [fst snd]. unfold uval. rewrite U_lit. reflexivity.
    + destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi ob_dflt] in H1, H2, H3, H4. subst. apply range_lit' in Hr; [|lia|lia]. lia.
  - right. unfold obj_range, obj_lo_of, obj_hi_of, O_got in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr. unfold GOT_LO, GOT_HI in Hr.
    rewrite lit_unsigned, !soff_lit_small in Hr by lia. unfold IMG_HI. change (0 mod 2 ^ 64) with 0 in Hr. lia.
  - right. unfold obj_range, obj_lo_of, obj_hi_of, O_rtc in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr. unfold RTC_LO, RTC_HI in Hr.
    rewrite lit_unsigned, !soff_lit_small in Hr by lia. unfold IMG_HI. change (0 mod 2 ^ 64) with 0 in Hr. lia.
  - left. apply pclMA_x. apply HT. exact (txt_range rho a BZ Hr).
Qed.

Definition cc_facts : list sprop := ltac2:(tb__ "0|0|
S6S14S18Sb3S66A2S6S14S18S66S67A2S6S14S18S67Sb2A2SaS14A1A3A3A3").
Definition ccF (F : list sprop) : bool := ltac2:(tb__ "0|0|
Sa5S14S14Sa3S14S1dR1A1VF;A3Lp;SaeA3").
Lemma nval : ltac2:(tb__ "0|8|
S16S7S14A1SbcS14S20R2A1R1A3S0S4Sa8R2A1S5A3S0S4Sa9R3A1S5A3S1S31S3dR5Sb3A2M0S3dR5S66A2M1A2S1S31G1S3dR5S67A2M2A2S1S31G2S3dR5Sb2A2M3A2S1S0S3S3dR5S76A2S36G2G1A2M4A3S1S0S3S3dR5S4dA2M5S32G4Z1M6A2A3S1S1S31G6G5A2S31G5S32S36G3G0A2G6A2A2A2S1S31G5S33Z2M7Z1bA2A2S31G3S33G7Z1aA2A2A2A2A2A2A2A2A2F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB HC. pose proof (uval_range rho vI). pose proof (basezI_of rho F HF HB) as [_ _ _ _ [T1 [T2 T3]] _ _].
  unfold ccF in HC.
  assert (G : forall p, In p cc_facts -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HC p Hp). }
  cbn [cc_facts] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3.
  rewrite h_ule in F1, F2, F3.
  pose proof (uval_range rho vC1) as R1. pose proof (uval_range rho vC2) as R2.
  assert (EL : uval rho vLEN = uval rho vC2 - uval rho vC1).
  { unfold vLEN, uval. rewrite U_sub. change (bv_unsigned (eval rho vC2)) with (uval rho vC2). change (bv_unsigned (eval rho vC1)) with (uval rho vC1).
    unfold M64v. apply Z.mod_small. lia. }
  assert (EN : uval rho vN = uval rho vC2 - uval rho vC1 + 1).
  { unfold vN. fold vLEN. rewrite uval_add_small by (rewrite EL, uval_lit by lia; lia). rewrite EL, uval_lit by lia. lia. }
  repeat split; lia.
Qed.

Lemma xrs47_ir : ltac2:(tb__ "0|0|
S16SaaR1A1Sc6R2S5cA2F_;Frho;").
Proof.
  intros rho [_ _ [B1 B2] [A1 A2] _ [T1 T2] [BT1 BT2]] r a Hr Ha. unfold IMG_HI in *.
  assert (HX : In r [(vBld, SLit 1304); (vARi, SLit 64); (vB, vL)]) by exact Hr. clear Hr.
  destruct HX as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha; rewrite ?uval_lit in Ha by lia; lia.
Qed.
Lemma xrs47_cons : ltac2:(tb__ "0|1|
S16S15S15S7S8S15S15A2M0A1S31S32S3dR4R3A2S32S3dR4R2A2Z20A2A2Z7fffff800000A2Sc6R5R2A2Sc6R6S6G0S9S15S15R5Sc4R4A1A4R3A3A2F_;F_;FX;Fc;Fh;Frho;").
Proof.
  intros rho h c X Hh HX r a [<-|Hr] Ha; [|exact (HX r a Hr Ha)]. cbn [fst snd] in Ha.
  pose proof (uval_range rho c). pose proof (uval_range rho h). unfold e32 in Ha.
  rewrite uval_add_small in Ha by (rewrite uval_lit by lia; lia). rewrite uval_lit in Ha by lia. lia.
Qed.

Definition open_facts : list sprop := ltac2:(tb__ "0|1|
S6S14S18S4eS1eP1eA1M0A2S6S14S18S54S4fA2S6S14S18S4fS17S36S33Z2Z28A2Z21A2A1A2S6S14S18S17Z10000A1S4fA2S6S14S18S1bS9fS4eSc4S4fA1A3G0A2S6S14S18S17Z1000A1S4eA2S6S14S18G0S17Z7fffff800000A1A2SaS14A1A3A3A3A3A3A3A3").
Definition openF (F : list sprop) : bool := ltac2:(tb__ "0|0|
Sa5S14S14Sa3S14S1dR1A1VF;A3Lp;SafA3").
Lemma openz : ltac2:(tb__ "0|7|
S16S7S14A1SbcS14S20R2A1R1A3S0S4SacR2A1S5A3S1S31S3dR4S4eA2M0Z7fffff800000M1A2S1S31S3dR4S54A2S3dR4S4fA2M2A2S1S31G2S36S33Z2Z28A2Z21A2A2S1S31Z10000G2A2S1S31S32G0S32G2Z20A2M3A2M4S3dR4S1eP1eA1A2M5A2S1S1S31Z1000G0A2S31G5G1A2A2S1S0S3S3dR4Sc4S4fA1M6A2G3A3S0S3S3dR4S1bS9fS4eG6A3A2G4A3A2A2A2A2A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold openF in HB.
  assert (G : forall p, In p open_facts -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [open_facts] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  pose proof (G _ ltac:(do 6 right; left; reflexivity)) as F7.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7. rewrite !uval_lit in F3, F4, F6, F7 by lia.
  pose proof (uval_range rho vHDi) as R1. pose proof (uval_range rho vCAP) as R3.
  assert (EK : uval rho (e32 vCAP) = uval rho vCAP + 32) by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  assert (EH : uval rho (SAlu ALU_ADD vHDi (e32 vCAP)) = uval rho vHDi + (uval rho vCAP + 32)) by (rewrite uval_add_small by (rewrite EK; lia); rewrite EK; lia).
  rewrite EH in F5. repeat split; lia.
Qed.
Ltac openz_tac HF := exact (openz _ _ HF ltac:(vm_compute; reflexivity)).

Lemma fit_arith : ltac2:(tb__ "0|7|
S16S31S3dR1S4eA2Z7fffff800000A2S31S3dR2S54A2S3dR2S4fA2A2S31S3dR3S4fA2S36S33Z2M0Z28A2Z21A2A2S1S31Z1S3dR4S4dA2M1A2S31G1S33G0Z1bA2A2A2S1S0S3S3dR5S53A2M2S32S32S3dR5S4eA2M3S3dR5S54A2M4A2Z20M5A2A3S1S0S3S3dR5S1bS9fS53S4dA3A2S32G2S3dR5S4dA2M6A2A3S1S0S3S3dR5S1bS9fS54S4dA3A2S32G4G6A2A3S0S3S3dR5S1bS9fS4eS17G5A1A3A2S32G3G5A2A3A2A2A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho Hh Hu Hc Hn.
  pose proof (uval_range rho vHDi) as R1. pose proof (uval_range rho vU) as R2. pose proof (uval_range rho vCAP) as R3. pose proof (uval_range rho vN) as R4.
  assert (EP : uval rho p_fit = uval rho vHDi + uval rho vU + 32).
  { unfold p_fit. rewrite uval_add_small by (rewrite uval_add_small by lia; rewrite uval_lit by lia; lia).
    rewrite uval_add_small by lia. rewrite uval_lit by lia. lia. }
  split; [exact EP|]. split; [rewrite uval_add_small by lia; lia|]. split; [rewrite uval_add_small by lia; lia|].
  rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma sums_slow : ltac2:(tb__ "0|2|
S16S1S0S3S47S56R1A2S32S93S3dR1S69A2M0A1S32S34Z2S3dR1S4dA2M1A2Z60A2A2A3S0S3S46S56R1A2S32S92G0A1S32S34Z4G1A2Z40A2A2A3A2Fr;").
Proof.
  intros r. unfold bd_slow. rewrite bsumV_app, bsumK_app. destruct (POT_vals r vUg) as (-> & -> & _).
  unfold CHn. cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. lia.
Qed.
Lemma sums_K : ltac2:(tb__ "0|7|
S16S15S1S0S3S47SbS3eS6S3eS3fZ1M0Z0M1S6S8S3S40A2M2S9S3S40G0S41R1A1A4SaG2A1M3A3G1A4S6S3eS3fG1G0G3S34Z2S42A2M4A4SaS3eA1A3A3Sc5S4dA1A3M5R2A2S32S3dR2R1A2S93S3dR2S4dA2M6A1A2A3S1S0S3S46G5R2A2S32G4S92G6A1A2A3S1S48G5R2A2S0S4S45G5A1S5A3A2A2A2Fk;Fr;").
Proof.
  intros r k. rewrite bsumV_app, bsumK_app. destruct (POT_vals r vN) as (-> & -> & NN & WP).
  cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. pose proof (uval_range r k). unfold KU.
  split; [lia|]. split; [lia|]. split; [|reflexivity].
  apply bd_nn_app. split; [|exact NN]. repeat constructor; unfold bival; cbn [lfval aval bi_f bi_c]; lia.
Qed.
Lemma pay_K_arith : ltac2:(tb__ "0|4|
S3S3S3S31Z0R3A2S1S31Z1M0R3A2S31R3S33Z2M1Z1bA2A2A2S31Z10001S32R5R4A2A2S2S1S0S3R4Z10000M2A3S35S32R5G0A2M3G2A2A2S1S0S3R4G3A3S31G2G3A2A2A2S1S31S32S32R5Z20A2S93R6A1A2S32S93R7A1S32S34G1R6A2Z60A2A2A2S31S32S34G1S42A2S92R6A1A2S32S92R7A1S32S34Z4R6A2Z40A2A2A2A2F_;F_;F_;F_;Fk;Fn;Fug;").
Proof. intros ug n k Hu Hn Hs Hk. unfold potV, potK, AV0, AK0, KU. destruct Hk as [[-> Hc]|[-> Hc]]; split; lia. Qed.

Lemma len2_val : ltac2:(tb__ "0|0|
S16S7S14A1SbcS14S20R2A1R1A3S0S4Sa8R2A1S5A3S0S4Sa9R3A1S5A3S0S3S3dR5S1bS9fS76S17Z2A1A3A2S32S3dR5S4dA2Z1A2A3F_;F_;F_;FF;Fr;").
Proof.
  intros r F HF HB HC. pose proof (nval r _ HF HB HC) as (N1 & N2 & N3 & EL & EN & N4 & N4b & N5).
  pose proof (uval_range r vC1). pose proof (uval_range r vI).
  rewrite uval_add_small by (rewrite EL, uval_lit by lia; lia). rewrite EL, uval_lit by lia. lia.
Qed.

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Variable AInv : ltac2:(tb__ "0|0|
Sf0S16S7S8dQ40A1A1Sd2OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
SdfS4aVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S3Sf5VCST;R1A2S1S31Z0R2A2S35R2SeeA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S3Sf5VXGL;R1A2S1S31Z0R2A2S35R2SeeA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S7S8S8S3S3A2S3A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S9cVAInv;VCST;VXGL;VKc;Sa7VCST;VFB;VFF;A3VFB;VFF;VBX;S91Vnd;Aa").
Definition Posts_ir : list (axst * jpostA) := ltac2:(tb__ "0|1|
S6S8S39Sb7A2M0S9S39Sb7S5aSd5S60A1A4S6G0S9S39Sb7S5bSd5S61A1A4SaG0A1A3A3").

Definition PD_ir : list (axst * ndesc) := ltac2:(tb__ "0|1|
S6S8S39S90A2M0S9S39S90S5aS60A4S6G0S9S39S90S5bS61A4SaG0A1A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S9bVAInv;VCST;VXGL;S8fVKc;Vrho0;Sa7VCST;VFB;VFF;A3VFB;VFF;VBX;S91Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S8S39S90A2Sf7Fn;") := ltac2:(tb__ "0|0|
S9dVAInv;VCST;VXGL;S8fVKc;Vrho0;Sa7VCST;VFB;VFF;A3VFB;VFF;VBX;S91Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sb8S4aS8fVrho0;Vtp0;Sd4A5").

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S3S7S8dQ40A1A1SbeF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S8bS39S16S7S8dQ40A1A1SbeSbcS14S20R3A1S19S38R4A1A1A3VTR;S8aS4aR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
SbeSbeSbeSc1R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S8bS8bS39S39ScbS7S1aA1M0S7S8S39Sb7A2M1A1S7S8S15S15A2M2A1SbeS16S7S8dQ40A1A1M3G2Sa4G2R1R5A3Sa4G2R2S3aRbA1A3F_;Fr;S0S10G0A1SbbRaR9R8A3SeG0R7A2A3S0S4SbaRbRaR9R8SbdG1S39SdS39Sb7A2R7A4A5S5A3S16G3VTR;S8aS4aRfRdR2R1A5Sb8S4aS1cS38RdA1A1R2R1RaA5A2Ftp1;Frho1;S7Sd3A1M4Sd1Sd2S8cS4aR9R8R10S9G4Se1R3Se2R2R1A2A4A5R13RaR9R4R2A4R13ScaSc9RbRfSc2R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S39Sb7G4Sd1Sd2S16G3G4Sd1Sd2Sa4G1S9S39Sb7RaR9A4R14A3S8cS4aR12R11R19S9G4Se1R9Se2R8R7A2A4A5R1cR13R12RaR8A4Sf2S1cS38R1aA1A1ScaSc9R14R18Sc2R9R13RaA3A3R19A2R8A3S8cS4aR9R8ReS9G4Se1R7Se2R6R5A2A4A5ReScaSc9R16R1aSc2RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sf9R17Sc2RcR16RdA3R1bR1cR1dR10R1eR19RbA9S16Sf3R18Sc2RdR17ReA3R1cR1dS38R1eA1S38R1fA1S38R11A1R1RcA9VTR;S8aS4aSb9R11ScaSc9R19R1dSc2ReR18RfA3A3R1eA2R18RdRcA5SfaR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S8aS4aR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
Sf0S16S7S8dQ40A1A1VTR;S8aS4aSd9VAInv;SaSd8A1M0Sd7R3VKc;S1ePcA1A6SdbSd6G0Sd7A3R2R1A5Sb8S4aS8fR2R1SdaSd6VAInv;VCST;VXGL;G0Sd7R3VKc;A8A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S39S90S8S3S15A2M0S16S7S8dQ40A1A1M1S3G1Sa4S8S8S39S90A2M2G0A2S9G2G0S9S39S90R7R6A4R5A4S5fA3S1S31Z0S9aS9G2G0S9S39S90R8R7A4R6A4R5A2M3A2S35G3R3A2A2VTR;S8aS4aVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S39S90S16S7S8dQ40A1A1M0S3G0Sa4S8S39Sb7A2S9S39Sb7R6Sd5R5A1A4Sd4A3VTR;S8aS4aVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd];
  match goal with |- context [bv_unsigned (eval ?r ?e)] => pose proof (U_range (eval r e)) end; unfold M64v in *; lia.
Tactic Notation "innth" integer(k) := do k right; left; reflexivity.

Lemma pay_CHn : ltac2:(tb__ "0|1|
S39S7S3eA1S0S4Sa8S19S38R2A1A1A1S5A3S0S4Sa9S19S38R3A1A1A1S5A3S0S4S45R3A1S5A3SecS8fVrho0;Sa7VCST;VFB;VFF;A3S19S38R5A1A1S17Z0M0A1G0SbS3eS77R4A3SbS3eS78R4A3A8F_;F_;F_;Frest;FX;").
Proof.
  intros X rest HB HC HW. split; [unfold bd_wpos in *; rewrite forallb_app, HW; reflexivity|]. split; [lia|]. intros r HF _ _ HNN. unfold pay_sem.
  destruct (nval r _ HF HB HC) as (N1 & N2 & N3 & EL & EN & N4 & N4b & N5).
  rewrite uval_lit by lia. rewrite !bsumV_app, !bsumK_app.
  unfold CHi, CHn. cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. rewrite EN.
  split; [lia|]. split; [lia|].
  apply bd_nn_app. split.
  - repeat constructor; unfold bival; cbn [lfval aval bi_f bi_c]; rewrite ?EN; lia.
  - unfold bd_nn in HNN |- *. apply Forall_app in HNN as [_ HNN]. exact HNN.
Qed.

Lemma X_P_fail : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0VTR;S8aS4aVJAv;S60A1S5aR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. left. reflexivity. Qed.
Lemma X_P_ok : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0VTR;S8aS4aVJAv;S61A1S5bR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. right. left. reflexivity. Qed.

Lemma X_X_open : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0S31S34Z5bS33Z2Z40A2A2R2A2VTR;S8aS4aVJAv;S57A1S81R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndO) C_open rho' tp w)).
  { intros w Hw0.
    pose proof (JA_repay segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue tv_ir [] (CHi ++ []) (CHn ++ []) am_ir X_open rho tp w
                  (pay_CHn X_open [] ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) eq_refl) Hw0) as Hw.
    rewrite app_nil_r in Hw.
    destruct (JA_open segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc HBX HNP tv_ir [] CHn vHDi true X_open rho tp w) as (rho' & _ & Hw');
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Hw |].
    - intros Ai rho1 tp1 md1 HF HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. destruct (P0_now CST FB FF rho0 rho HP0 Hav) as [HT Hbb]. split.
      + apply (objs_ok_ir CST rho0 FB FF); [basez_tac HF | exact HT | exact Hbb | | exact ET].
        intros o Ho. cbn in Ho. unfold objclass. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; auto 10.
      + apply xrs47_ir. basez_tac HF.
    - exists rho'. rewrite <- C_open_eq. exact Hw'. }
  apply TR_exw. intros rho'. apply (REENTER C_open ndO (90, z0)); [innth 5 | meas].
Qed.

Lemma X_X_nohead : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0S31S34Z51S33Z2Z40A2A2R2A2VTR;S8aS4aVJAv;S57A1S80R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_slow ndS (80, z0) (rho_sub rho s_nohead)); [innth 6 | meas]].
  intros w Hw0.
  pose proof (JA_repay segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue tv_ir [] (CHi ++ []) (CHn ++ []) am_ir X_nohead rho tp w
                (pay_CHn X_nohead [] ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) eq_refl) Hw0) as Hw.
  rewrite app_nil_r in Hw.
  apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc X_nohead C_slow s_nohead (NDA tv_ir [] (CHn ++ [BIc 1 0 AV0; BIc 0 1 AK0]) (AHead vHDi false)) ndS);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  apply (JA_pot_out0 segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HBX); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Hw].
Qed.

Lemma X_X_nofit : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0S31S34Z51S33Z2Z40A2A2R2A2VTR;S8aS4aVJAv;S58A1S7fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  assert (BZ : basezI rho) by basez_tac HF.
  pose proof (nval rho _ HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (N1 & N2 & N3 & EL & EN & N4 & N4b & N5).
  assert (OZ : uval rho vHDi <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHDi + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ (4096 <= uval rho vHDi /\ uval rho (SVar 30) <= 140737479966720)
               /\ uval rho (e32 vCAP) = uval rho vCAP + 32 /\ uval rho (SAlu ALU_ADD vHDi (e32 vCAP)) = uval rho vHDi + (uval rho vCAP + 32)) by openz_tac HF.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & EK & EH).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(lia)) as (EP & EPN & EUN & EH32).
  factz HF (SPNot (SPBranch BC_GEU vCAP (SAlu ALU_ADD vU vN))) H0. rewrite EUN in H0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndS) C_slow rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (JA_close_np segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc HBX HNP tv_ir [] bd_open vHDi vNX vCAP vU X_nofit
                  (removelast (ss_objs (ax_S X_nofit))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.O_hdr vHDi vNX vCAP vU) rho tp tr ms md) as CL.
    specialize (CL ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(vm_compute; left; reflexivity) eq_refl Hw).
    set (rho1 := rho_absorb rho [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.O_hdr vHDi vNX vCAP vU] (vms md tp ms)) in CL.
    assert (CL2 : SPA segs (JAv (NDA tv_ir [] bd_open am_np)) X_nofit2 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_nofit2_eq. change (drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit)))) with X_nofit1 in CL.
      apply (SPA_refacts_JA segs _ rho1 X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1))); [exact CL | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
      intros tr' md' _ HF1. constructor; [|exact HF1].
      apply (proj2 (holds_ule _ _ _)). rewrite U_lit. change (65537 mod M64v) with 65537.
      assert (EU : forall e, eval rho1 e = eval rho e) by (intros e; unfold rho1; apply eval_absorb).
      rewrite EU. change (bv_unsigned (eval rho (SAlu ALU_ADD vU vN))) with (uval rho (SAlu ALU_ADD vU vN)). rewrite EUN. lia. }
    exists (rho_sub rho1 s_nofit).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc X_nofit2 C_slow s_nofit (NDA tv_ir [] bd_open am_np) ndS);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact CL2]. }
  apply TR_exw. intros rho'. apply (REENTER C_slow ndS (80, z0)); [innth 6 | meas].
Qed.

Lemma X_X_fitG : ltac2:(tb__ "0|7|
S39S39S39S1aScbS3S15S16S7S8dQ40A1A1M0S3G0S0S7S1aA1S25S38RbA1A1M1SbS1aSa6S1aG1A2S6S1aR8SaS1aA1A3A3A3S1S0S15S22R9A1S4eA3S1S0S15S24R9A1S17Z0M2A1A3S0S15S23R9A1S17Z18A1A3A2A2S1aSa4S1aR1Sa6S1aS25S38ReA1A1A2A3SabR2A1F_;Fo;S0S7S8S15S15A2M3A1S3aReA1S6G3S9S15S15S4eSc4S4fA1A4S5cA3A3S0S4Sa8S19S38RfA1A1A1S5A3S0S4Sa9S19S38R10A1A1A1S5A3S0S4SacS19S38R11A1A1A1S5A3S0S4Sa3S14S1dS21Sa2S4fS1bS9fS54S4dA3A3A1S19S38R12A1A1A3S5A3S0S4S2bS38Sc3R13S53S4dA3A1A1S5A3S0S15S3cR14A1S17SefA1A3S0S4S26S1cS38R15A1A1S53A2S5A3S0S4S26S1cS38R16A1A1S4dA2S5A3S0S39Sf4Sc3R17S53S4dA3SbS14S71S19S38R17A1A1A3A2R16A3S0S4Sa5S14S2aS1cS38Sc3R18S53S4dA3A1A1A1SbS14S71S19S38R18A1A1A3A3S5A3Sa4S8S8S39S90A2M4S8S3S15A2M5A2S9G4G5S9S39S90R17S62A4S9S3S15R14R13A4A4S5fA3S1S31G2R15A2S31R15Z32A2A2S0S4S3bR1aR19R17A3S5A3S0S4SccR18S8fA2S5A3S0S4Sf1S8fS1cS38R1cA1A1A2S5A3S0S4S97S1cS38R1dA1A1S94S50SaS8S8S15S3A2S15A2A1S70S98S4eS89S4fS6G3S9S15S15S53S4dA4SaG3A1A3A4M6A4A2S5A3S0S4Se4R1bS50S50A3S5A3S0S4S44S19S38R1fA1A1S43R1cS6fA2S70A3S5A3S0S4S95S96R1dS6eA2G6A2S5A3S31S34Z33S33Z2Z40A2A2R19A2VTR;S8aS4aVJAv;S58A1R23R1cR1bA5VFAM;R1aR19A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frvar;Frk;Fs;Foh;FT;FXf3;FXf;").
Proof.
  intros Xf Xf3 T oh s rk rvar rho tp b tp0 Hobjs (Ohb & Ohl & Ohh) Hcls HX HB HC HO Hge Hwf Hbase Hb1 Hb2 HX3 Hfb HinT Hrk He Hid Hnf Hnb Htv Hle Ham Hb.
  apply TR_facts. intros HF.
  assert (BZ : basezI rho) by exact (basezI_of _ _ HF HB).
  pose proof (nval rho _ HF HB HC) as (N1 & N2 & N3 & EL & EN & N4 & N4b & N5).
  destruct (openz rho _ HF HO) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & EK & EH).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(lia)) as (EP & EPN & EUN & EH32).
  pose proof (holds_mem _ _ _ HF Hge) as H0. zf H0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in H0. rewrite EUN in H0.
  eapply TR_pre; [|apply (REENTER T ndL (rk, rvar) (rho_sub rho s)); [exact HinT | unfold emeasA; cbn [eda_rank eda_var fst snd]; pose proof (U_range (eval (rho_sub rho s) rvar)); unfold M64v in *; nia]].
  intros w Hw.
  apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc Xf3 T s (NDA tv_ir [] bd_open (AOpen vHDi vNX vCAP [(p_fit, vN)])) ndL);
    [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | exact Ham |].
  rewrite <- HX3. apply (SPA_refacts_JA segs _ rho (carve_stateA Xf p_fit vN) (fit_facts ++ ss_facts (ax_S Xf))); [| exact Hfb |].
  - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HNP tv_ir [] bd_open vHDi vNX vCAP p_fit vN Xf rho tp w);
      [exact Hwf | exact Hbase | exact Hb1 | exact Hb2 | | | exact Hw].
    + intros r HFr.
      pose proof (nval r _ HFr HB HC) as (_ & _ & _ & _ & _ & M4 & M4b & M5).
      destruct (openz r _ HFr HO) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & _).
      destruct (fit_arith r Y1 Y2 Y3 ltac:(lia)) as (EP' & _ & EUN' & _).
      pose proof (holds_mem _ _ _ HFr Hge) as H1. zf H1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H1. rewrite EUN' in H1.
      pose proof (uval_range r vU). lia.
    + intros Ai rho1 tp1 md1 HF' HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. destruct (P0_now CST FB FF rho0 rho HP0 Hav) as [HT Hbb]. split.
      * intros o a Ho Hr. rewrite Hobjs in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
        -- destruct (objs_ok_ir CST rho0 FB FF rho (removelast (ss_objs (ax_S Xf))) BZ HT Hbb Hcls ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
        -- right; right. unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Ohb, Ohl, Ohh in Hr. cbn [fst snd] in Hr.
           rewrite !soff_lit_small in Hr by lia. unfold uval. lia.
      * rewrite HX. apply xrs47_cons; [lia | apply xrs47_ir; exact BZ].
  - intros tr md _ HF2. apply Forall_app. split; [|exact HF2].
    unfold fit_facts. pose proof (uval_range rho vU).
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
      rewrite ?EPN, ?EH, ?EH32, ?EP; rewrite ?uval_lit by lia; lia.
Qed.
Lemma X_X_fitc : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0S31S34Z33S33Z2Z40A2A2R2A2VTR;S8aS4aVJAv;S58A1S7dR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_X_fitG X_fitc X_fitc3 C_loop ohFc s_fitc 50 vR rho tp b tp0 objsFc_eq);
    [cbn; repeat split; reflexivity | | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact X_fitc3_eq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | innth 10 | lia | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Hb].
  intros o Ho. cbn in Ho. unfold objclass. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; auto 10.
Qed.
Lemma X_X_fitn : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0S31S34Z33S33Z2Z40A2A2R2A2VTR;S8aS4aVJAv;S58A1S7eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_X_fitG X_fitn X_fitn3 C_nul ohFn s_fitn 45 z0 rho tp b tp0 objsFn_eq);
    [cbn; repeat split; reflexivity | | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact X_fitn3_eq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | innth 11 | lia | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Hb].
  intros o Ho. cbn in Ho. unfold objclass. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; auto 10.
Qed.

Lemma pay_K : ltac2:(tb__ "0|9|
S39S15S0S4Sa8S19S38R2A1A1A1S5A3S0S4Sa9S19S38R3A1A1A1S5A3S0S4Sa3S14S1dS18S17Z10001A1S1bS9fS69S4dA3A2A1S19S38R4A1A1A3S5A3S0S4Sa3S14S1dS18S69S17S75A1A2A1S19S38R5A1A1A3S5A3S16SbcS14S20R1A1S19S38R7A1A1M0A3S2S1S0S3S3dR2R7A2M1Z10020A3S35S32S3dR2S4dA2M2Z1M3A2M4Z10000M5A2A2S1S0S3G1S32G2Z21A2A3S31G5G4A2A2A2F_;Fr;SecS8fVrho0;Sa7VCST;VFB;VFF;A3G0S17Z0M6A1G6S56SbS3eS6S3eS3fG3G6S6S8S3S40A2M7S9S3S40G3S41R6A1A4SaG7A1M8A3G6A4S6S3eS3fG6G3G8S34Z2S42A2A4SaS3eA1A3A3Sc5S4dA1A3A8F_;F_;F_;F_;F_;Fk;FX;").
Proof.
  intros X k HB HC Hug1 Hug2 HK. destruct (sums_K rho0 k) as (_ & _ & _ & WP). split; [exact WP|]. split; [lia|]. intros r HF _ _ _. unfold pay_sem.
  pose proof (nval r _ HF HB HC) as (N1 & N2 & N3 & EL & EN & N4 & N4b & N5).
  destruct (sums_K r k) as (-> & -> & NN & _). destruct (sums_slow r) as [-> ->]. rewrite uval_lit by lia.
  pose proof (holds_mem _ _ _ HF Hug1) as H1. pose proof (holds_mem _ _ _ HF Hug2) as H2. zf H1. zf H2.
  repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H2.
  unfold two40, RA.two40 in H2. rewrite !uval_lit in H1, H2 by lia. pose proof (uval_range r vUg).
  rewrite uval_add_small in H1 by lia.
  pose proof (HK r HF) as HKr.
  destruct (pay_K_arith (uval r vUg) (uval r vN) (uval r k - 32) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [A B].
  split; [lia|]. split; [lia | exact NN].
Qed.

Lemma X_X_K : ltac2:(tb__ "0|8|
S39ScbS15S16S7S8dQ40A1A1M0S3G0SecS8fVrho0;Sa7VCST;VFB;VFF;A3S19S38R7A1A1S17Z0M1A1G1S56SbS3eS6S3eS3fZ1M2G1S6S8S3S40A2M3S9S3S40G2S41R5A1A4SaG3A1M4A3G1A4S6S3eS3fG1G2G4S34Z2M5S42A2A4SaS3eA1A3M6A3Sc5S4dA1M7A3A8S0S4S3bR8S79R7A3S5A3S0S4SccR8S8fA2S5A3S0S4Sf1S8fS1cS38RaA1A1A2S5A3S0S4S97S1cS38RbA1A1S94S50SaS8S8S15S3A2S15A2A1SbS3eS6S3eS3fG2G1S6G3S9S3S40G2S41R9A1A4G4A3G1A4G6A3G7A3S5dA4A2S5A3S0S4S44S19S38RcA1A1S43RbS85A2SbS3eS6S3eS3fG2G1S6G3S9S3S40G2S41RaA1A4G4A3G1A4G6A3G7A3A3S5A3S0S4S95S96RcS5dA2S5dA2S5A3S0S4Se4RdS50S50A3S5A3S31S34Z4cS33G5Z40A2A2RaA2VTR;S8aS4aVJAv;S64A1R10RdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fk;Fs;FX;").
Proof.
  intros X s k rho tp b tp0 HPAY He Hid Hnf Hnb Hle Ham Htv Hb.
  eapply TR_pre; [|apply (REENTER C_K ndKc (75, z0) (rho_sub rho s)); [innth 7 | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc X C_K s (NDA tv_ir [] ([BI 1 0 [(1, ASv k)] 0; BI 0 1 [] (2 * KU)] ++ POT vN) am_np) ndKc);
    [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | exact Ham |].
  apply (JA_repay segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue tv_ir [] bd_slow _ am_np X rho tp w HPAY Hw).
Qed.
Lemma X_X_K1 : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0S31S34Z4cS33Z2Z40A2A2R2A2VTR;S8aS4aVJAv;S64A1S7bR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K1 s_K1 (SLit 65568));
    [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Hb].
  apply pay_K; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros r HF. left. factz HF (SPBranch BC_LTU (SAlu ALU_ADD vLEN (SLit 2)) (SLit 65536)) H1.
  rewrite (len2_val r _ HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) in H1.
  rewrite !uval_lit in * by lia. lia.
Qed.
Lemma X_X_K2 : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0S31S34Z4cS33Z2Z40A2A2R2A2VTR;S8aS4aVJAv;S64A1S7cR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K2 s_K2 (SAlu ALU_ADD vN (SLit 33)));
    [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Hb].
  apply pay_K; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros r HF. right. factz HF (SPNot (SPBranch BC_LTU (SAlu ALU_ADD vLEN (SLit 2)) (SLit 65536))) H1.
  rewrite (len2_val r _ HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) in H1.
  pose proof (nval r _ HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (_ & _ & _ & _ & _ & N4 & N4b & N5).
  rewrite !uval_lit in * by lia. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma site_m : ltac2:(tb__ "0|1|
S16SedVAInv;VCST;VXGL;S8fVrho0;Sa7VCST;VFB;VFF;A3VFB;VFF;S6aS65S6dR1S72S12S3A1Sf0Sd1S1S1S31Z1S3dR3ScdS65PcA2A2M0A2S35G0S33Z2Z27A2A2A2Se0SaSd8A1Sd7ScaSc9R3S6dR1A3S65A2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HTP HTK. cbn [nd_tv nd_fr nd_bd ndKc] in HN, HD, HZ, HFR.
  assert (BZ : basezI rho) by basez_tac HF. destruct (P0_now CST FB FF rho0 rho HP0 Hav) as [HT Hbb].
  assert (XO : forall o a, is_xo o = true -> fst (obj_range rho o) <= a < snd (obj_range rho o) -> cmaddrA CST Ai None a).
  { intros o a Hx Hr. unfold is_xo in Hx. apply lazy_orb_prop in Hx as [Hx|Hx];
      apply lazy_andb_prop in Hx as [H1 Hx]; apply lazy_andb_prop in Hx as [H2 H3];
      apply sv_eqb_sound in H1; apply sv_eqb_sound in H2; apply sv_eqb_sound in H3;
      destruct o as [ob olo ohi oc od]; cbn [ob_base ob_lo ob_hi] in H1, H2, H3; subst.
    - apply (infrFF_cmaddrA CST FF Ai (uval rho vBld) 1304 None a HFF Hbb).
      unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr. rewrite !soff_lit_small in Hr by lia. unfold uval. lia.
    - apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HTP). apply HT.
      destruct BZ as [_ _ _ _ [T1 [T2 T3]] _].
      unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr. rewrite soff_lit_small in Hr by lia.
      rewrite (soff_smallu rho vL) in Hr by lia. unfold uval in *. lia. }
  assert (XX : forall r a, is_xX r = true -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) -> cmaddrA CST Ai None a).
  { intros r a Hx Ha. unfold is_xX in Hx. apply lazy_orb_prop in Hx as [Hx|Hx]; apply xr_eqb_sound in Hx; subst r; cbn [fst snd] in Ha.
    - apply (infrFF_cmaddrA CST FF Ai (uval rho vBld) 1304 None a HFF Hbb). rewrite uval_lit in Ha by lia. exact Ha.
    - apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HTP). apply HT. exact Ha. }
  split; [|split; [|split; [|exact I]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_m)) tv_ir None is_xo R_m None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros o a Ho Hb Hr. exact (XO o a Hb Hr).
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv_ir None (ss_objs (ax_S E_m)) is_xX (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros r a Hr Hb Ha. left. exact (XX r a Hb Ha).
    + exact I.
  - change (wsub_get s_m 12) with (e32 vK). factz HF (SPUle (SLit 65536) vK) H1. factz HF (SPUle vK (SLit (2 ^ 27))) H2.
    rewrite !uval_lit in H1, H2 by lia. unfold e32. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma X_E_m : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0S31S34Z42S33Z2Z40A2A2R2A2VTR;S8aS4aVJAv;S72A1S6aR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (malloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_m R_m rho tp ndKc bd_m (FAM b tp0) CMALLOC).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mnull_eq. apply (REENTER T_mnull ndM (65, z0)); [innth 8 | meas].
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok ndMok (65, z0)); [innth 9 | meas]].
    intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. apply (holds_mem _ _ _ HF). OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma X_X_sretG : ltac2:(tb__ "0|11|
S39S39S39S39S39S7SfA1S7S1aA1M0S1aS1aScbS3S15S16S7S8dQ40A1A1M1S3G1S0S10S39A1SeaR10S6Se7Se8RbA1S6Se7Se9Sf6S13SfRbA2U1A2S17Z18A1M2A2SaSe7A1A3A3A2SeS39RfA2A3S0G0S25S38R10A1A1SbS1aSbS1aRbS6S1aRaSaS1aA1M3A3A3S6S1aR9G3A3A3A3S0S4Sf8RbS1eS88A1M4S4eS52S4dA5S5A3S0S4S4S4L_;M5S1fS22RbA1G4A2G5S1fS24RbA1G2A2G5S1fS23RbA1Sc4S52A1M6A2S2eS28RbA1A1ScX4x2ScX4x2ScX4x2S5A3S0S4Se3S19S38R13A1A1G6Z0M7G6A4S5A3S0S4Se3S19S38R14A1A1S17Z10000A1M8G7S52A4S5A3S0S4Se3S19S38R15A1A1S52G7S17S36S33Z2M9Z28A2Z21A2A1A4S5A3S0S4Sa3S14S1dS2dS21Sa1G4S17G7A1MaA3A1A1S19S38R16A1A1A3S5A3S0S4S49S19S38R17A1A1GaS42S86S5eA5S5A3S0S39Sc7R18SbS1aR13S6S1aR12G3A3A3A2R17A3S0G0S25S38R18A1A1SbS1aR14S6S1aR13G3A3A3A3S1aSa4S1aR1R16A3SabR2A1F_;Fo;S0S7S8S15S15A2MbA1S3aR1aA1SbGbS5cS6GbS9S15S15G4G6A4SaGbA1McA3A3A3S0S4Sa8S19S38R1bA1A1A1S5A3S0S4Sa9S19S38R1cA1A1A1S5A3S0S4Sa3S14S1dS18S1bS9fG4G6A3S1eP1eA1MdA2A1S19S38R1dA1A1A3S5A3S0S4Sa3S14S1dS18G4GdA2A1S19S38R1eA1A1A3S5A3S0S4Sa3S14S1dS18G8S52A2A1S19S38R1fA1A1A3S5A3S0S4Sa3S14S1dS18S52S17S33G9Z1bA2A1A2A1S19S38R20A1A1A3S5A3S0S4Sa3S14S1dS18S1bS9fS4dS17Z1A1A3S52A2A1S19S38R21A1A1A3S5A3S0S4S2bS38Sc3R22S55S4dA3A1A1S5A3S0S15S3cR23A1S17SefA1A3S0S4S26S1cS38R24A1A1S55A2S5A3S0S4S26S1cS38R25A1A1S4dA2S5A3S0S39Sf4Sc3R26S55S4dA3SbS14S73S19S38R26A1A1A3A2R25A3S0S4Sa5S14S2aS1cS38Sc3R27S55S4dA3A1A1A1SbS14S73S19S38R27A1A1A3A3S5A3Sa4S8S8S39S90A2MeS8S3S15A2MfA2S9GeGfS9S39S90R26S62A4S9S3S15R20R1fA4A4S5fA3S1S31G7R21A2S31R21Z32A2A2S0S4S3bR29R28R23A3S5A3S0S4SccR24S8fA2S5A3S0S4Sf1S8fS1cS38R2bA1A1A2S5A3S0S4S97S1cS38R2cA1A1S94S50SaS8S8S15S3A2S15A2A1S5eS98G4S4eS52S6GbS9S15S15S55S4dA4GcA3A4M10A4A2S5A3S0S4Se4R27S50S50A3S5A3S0S4S44S19S38R2eA1A1S43R28S6fA2S5eA3S5A3S0S4S95S96R29S6eA2G10A2S5A3S31S34Z33S33G9Z40A2A2R25A2VTR;S8aS4aVJAv;S63A1R34R28R27A5VFAM;R26R25A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frvar;Frk;Fs;FotN;FohN;FobjsN;Fsel;FT;FXs3;FXs2;FXs1;FXs;").
Proof.
  intros Xs Xs1 Xs2 Xs3 T sel objsN ohN otN s rk rvar rho tp b tp0 Hax Hobjs1 Hsh Hot Hu1 Hu2 Hu3 Hnz Hpay HX2 Hobjs2 Hcls HX HB HC He1 He2 Hk1 Hk2 Hk3
         Hwf Hbase Hb1 Hb2 HX3 Hfb HinT Hrk He Hid Hnf Hnb Htv Hle Ham Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndL) T rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho Xs Xs1 tp _ Hax Hw) as H1.
    pose proof (JA_push_open segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc HBX HNP tv_m [] bd_m bd_m2 0 blkN vHDi vK vN
                  Xs1 objsN ohN otN rho tp tr ms md Hobjs1 eq_refl Hsh Hot Hu1 Hu1 Hu2 Hu3 Hnz Hpay H1) as H2.
    rewrite HX2 in H2. cbn [remove_nth fst blkN tv_m] in H2.
    set (rho1 := rho_absorb rho [otN] (vms md tp ms)) in H2.
    assert (HF1 : Forall (holds rho1) (ss_facts (ax_S Xs2))) by exact (smatchA_facts segs _ _ _ _ (proj1 H2)).
    assert (BZ1 : basezI rho1) by exact (basezI_of _ _ HF1 HB).
    pose proof (nval rho1 _ HF1 HB HC) as (N1 & N2 & N3 & EL & EN & N4 & N4b & N5).
    pose proof (holds_mem _ _ _ HF1 He1) as HE1. pose proof (holds_mem _ _ _ HF1 He2) as HE2.
    pose proof (holds_mem _ _ _ HF1 Hk1) as HK1. pose proof (holds_mem _ _ _ HF1 Hk2) as HK2. pose proof (holds_mem _ _ _ HF1 Hk3) as HK3.
    rewrite h_ule in HE1, HE2, HK1, HK2, HK3.
    change (uval rho1 (SVar 30)) with (bv_unsigned (rw rho1 V_TOP)) in HE1, HE2. pose proof BZ1 as [_ _ _ _ _ _ [BT0 [BT1 BT2]]].
    rewrite !uval_lit in HK1, HK2 by lia.
    pose proof (uval_range rho1 (SVar pN)) as RP. pose proof (uval_range rho1 vK) as RK.
    assert (EK : uval rho1 (e32 vK) = uval rho1 vK + 32) by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small in HE1 by (rewrite EK; lia). rewrite EK in HE1.
    rewrite uval_add_small in HK3 by (rewrite uval_lit by lia; lia). rewrite uval_lit in HK3 by lia.
    assert (EPn : uval rho1 p_new = uval rho1 (SVar pN) + 32) by (unfold p_new; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    assert (H3 : SPA segs (JAv (NDA tv_ir [] bd_m2 (AOpen (SVar pN) vHDi vK [(p_new, vN)]))) Xs3 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- HX3.
      apply (SPA_refacts_JA segs _ rho1 (carve_stateA Xs2 p_new vN) (new_facts ++ ss_facts (ax_S Xs2))); [| exact Hfb |].
      - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HNP tv_ir [] bd_m2 (SVar pN) vHDi vK p_new vN Xs2 rho1 tp _);
          [exact Hwf | exact Hbase | exact Hb1 | exact Hb2 | | | exact H2].
        + intros r HFr.
          pose proof (nval r _ HFr HB HC) as (_ & _ & _ & _ & _ & M4 & M4b & M5).
          pose proof (holds_mem _ _ _ HFr Hk3) as HK3'. pose proof (holds_mem _ _ _ HFr Hk2) as HK2'. pose proof (holds_mem _ _ _ HFr He2) as HE2'.
          rewrite h_ule in HK3', HK2', HE2'. rewrite uval_lit in HK2' by lia. change (uval r (SVar 30)) with (bv_unsigned (rw r V_TOP)) in HE2'.
          pose proof (basezI_of _ _ HFr HB) as [_ _ _ _ _ _ [_ [_ BT2']]].
          rewrite uval_add_small in HK3' by (rewrite uval_lit by lia; lia). rewrite uval_lit in HK3' by lia.
          pose proof (uval_range r (SVar pN)). unfold p_new.
          rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
        + intros Ai rho2 tp2 md2 HF' HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho1 Hav eq_refl) as ET. destruct (P0_now CST FB FF rho0 rho1 HP0 Hav) as [HT Hbb]. split.
          * intros o a Ho Hr. rewrite Hobjs2 in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
            -- destruct (objs_ok_ir CST rho0 FB FF rho1 objsN BZ1 HT Hbb Hcls ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
            -- right; right. unfold TobjJVA.hdr_shape in Hsh.
               apply lazy_andb_prop in Hsh as [Q1 Hsh']. apply lazy_andb_prop in Hsh' as [Q2 Hsh'']. apply lazy_andb_prop in Hsh'' as [Q3 _].
               apply sv_eqb_sound in Q1. apply sv_eqb_sound in Q2. apply sv_eqb_sound in Q3.
               unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Q1, Q2, Q3 in Hr. cbn [fst snd] in Hr.
               rewrite !soff_lit_small in Hr by lia. unfold uval. lia.
          * rewrite HX. intros r a Hr Ha. apply in_app_or in Hr. destruct Hr as [Hr|[<-|[]]]; [exact (xrs47_ir rho1 BZ1 r a Hr Ha)|].
            cbn [fst snd] in Ha. rewrite EK in Ha. lia.
      - intros tr' md' _ HF2. apply Forall_app. split; [|exact HF2].
        unfold new_facts. change (bv_unsigned (rw rho1 V_TOP)) with (uval rho1 (SVar 30)) in *.
        assert (EPS : uval rho1 (SAlu ALU_ADD p_new vN) = uval rho1 p_new + uval rho1 vN) by (rewrite uval_add_small by lia; lia).
        assert (EHC : uval rho1 (SAlu ALU_ADD (SVar pN) (e32 vK)) = uval rho1 (SVar pN) + (uval rho1 vK + 32)) by (rewrite uval_add_small by (rewrite EK; lia); rewrite EK; lia).
        repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
          rewrite ?EPS, ?EHC, ?EPn; rewrite ?uval_lit by lia; lia. }
    exists (rho_sub rho1 s).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc Xs3 T s (NDA tv_ir [] bd_m2 (AOpen (SVar pN) vHDi vK [(p_new, vN)])) ndL);
      [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | exact Ham | exact H3]. }
  apply TR_exw. intros rho'. apply (REENTER T ndL (rk, rvar)); [exact HinT | unfold emeasA; cbn [eda_rank eda_var fst snd]; pose proof (U_range (eval rho' rvar)); unfold M64v in *; nia].
Qed.
Lemma X_X_sretc : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0S31S34Z33S33Z2Z40A2A2R2A2VTR;S8aS4aVJAv;S63A1S83R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_X_sretG X_sretc X_sretc1 X_sretc2 X_sretc3 C_loop sel_c objsNc ohNc otNc s_sretc 50 vR rho tp b tp0 X_sretc1_eq objsNc_eq);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact X_sretc2_eq | exact objsNc2_eq | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | exact X_sretc3_eq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 10 | lia | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Hb].
  intros o Ho. cbn in Ho. unfold objclass. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; auto 10.
Qed.
Lemma X_X_sretn : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0S31S34Z33S33Z2Z40A2A2R2A2VTR;S8aS4aVJAv;S63A1S84R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_X_sretG X_sretn X_sretn1 X_sretn2 X_sretn3 C_nul sel_n objsNn ohNn otNn s_sretn 45 z0 rho tp b tp0 X_sretn1_eq objsNn_eq);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact X_sretn2_eq | exact objsNn2_eq | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | exact X_sretn3_eq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 11 | lia | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Hb].
  intros o Ho. cbn in Ho. unfold objclass. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn; auto 10.
Qed.

Lemma X_X_ret : ltac2:(tb__ "0|1|
S16S7S8dQ40A1A1M0S3G0VTR;S8aS4aVJAv;S62A1S82R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndK) P_ok rho' tp w)).
  { intros [tr [ms md]] H1.
    pose proof (JA_unslot segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc HNP tv_ir [] bd_loop vH vNXl vCAPl vP vNn
                  X_ret (objsR ++ [ohR]) osR rho tp tr ms md objsR_eq ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) H1) as H2.
    rewrite X_ret2_eq in H2. set (rho1 := rho_absorb rho [osR] (vms md tp ms)) in H2.
    pose proof (JA_close segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc HBX HNP tv_ir [] bd_loop [] vH vNXl vCAPl vUc
                  X_ret2 objsR ohR rho1 tp tr ms md objsR2_eq ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)
                  ltac:(vm_compute; left; reflexivity) eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) H2) as H3.
    rewrite X_ret3_eq in H3. set (rho2 := rho_absorb rho1 [ohR] (vms md tp ms)) in H3.
    exists (rho_sub rho2 s_ret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc X_ret3 P_ok s_ret (NDA tv_ir [] [] (AHead vH true)) ndK);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact H3]. }
  apply TR_exw. intros rho'. apply X_P_ok.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S39S90S8S3S15A2M0S16S7S8dQ40A1A1M1G1Sa4S8S8S39S90A2M2G0A2S9G2G0S9S39S90R6R5A4R4A4S87A3VTR;S8aS4aVJAv;R6A1R7R4R3A5VFAM;S9aS9G2G0S9S39S90R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsI] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X_open. meas.
  - apply X_X_nohead. meas.
  - apply X_X_fitc. meas.
  - apply X_X_fitn. meas.
  - apply X_X_nofit. meas.
  - apply X_X_K1. meas.
  - apply X_X_K2. meas.
  - apply X_E_m. meas.
  - apply X_X_sretc. meas.
  - apply X_X_sretn. meas.
  - apply X_X_ret.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S9eS4aVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
SddS4aSd6VAInv;VCST;VXGL;A5").

Theorem intern_rest_sum : ltac2:(tb__ "0|0|
S7S8dQ40A1A1Sc0S4aVok;S8aS4aS99VAInv;VCST;VXGL;VKc;Sa7VCST;VFB;VFF;A3VFB;VFF;VBX;S91S57AaS6cVrho0;R1A5Sb8S4aS8fVrho0;R1Sd4A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc ALA FUEL_ir cutpcs_ir 100
                (map edropA cutsI) (map edropA exitsI) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertI_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0' & Hin). cbn in E0'. injection E0' as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsI)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok))
         with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue ok (map edropA cutsI) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_ir CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_ir P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
SdeS4aSd6VAInv;VCST;VXGL;A5").

Theorem intern_rest_sum_ex : ltac2:(tb__ "0|0|
S7S8dQ40A1A1SbfS4aS8aS4aS99VAInv;VCST;VXGL;VKc;Sa7VCST;VFB;VFF;A3VFB;VFF;VBX;S91S57AaS6cVrho0;R1A5Sb8S4aS8fVrho0;R1Sd4A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc ALA FUEL_ir cutpcs_ir 100 cutsI exitsI (Q tp0) ejcertI_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue) cutsI) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue cutsI T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_ir CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_ir P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_intern_rest_pf.

(* [comment removed for export] *)
Module Lib_vec_finalize_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "cons"; "bool"; "nil"; "false"; "true"; "Some"; "app"; "fst"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "holds"; "ss_facts"; "SLit"; "sv_eqb"; "ss_next"; "ob_base"; "ob_hi"; "ob_lo"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "AHead"; "am_subst"; "amode"; "emeasA"; "JA"; "JLA"; "ejcertA"; "nodeIA"; "ok_frameKA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "import_subA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "BXok_d"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_finalize"; "E_call"; "s_call"; "nd0"; "R_call"; "X_go"; "vL"; "vV"; "P_fail"; "P_ok"; "Xk_call"; "vD"; "P_zero"; "Pre_vf"; "cutsV"; "exitsV"; "go_facts"; "nd_fail"; "nd_ok"; "nd_zero"; "tv_vf"; "C_go"; "FUEL_vf"; "cutpcs_vf"; "vHDn"; "vHDv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup"; "Pre_ad"; "P_fail"; "P_ok"; "tv0"; "am_np"; "am_ok"; "nd0"; "ndF"; "ndK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_vec_finalize_pf"; "P0_vf"; "PD_adv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_vec_finalize_pf.Sum"; "JL"; "Posts_vf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pclMA"; "FFx"; "T_afterA3"; "PostsC"; "robjs_okF"; "xr_eqb"; "xrs_okF"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ef.Lib_arena_dup_pf"; "P0_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ef.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_finalize.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ef.Lib_arena_dup_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import VFAddr ADAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma C_go_eq : ltac2:(tb__ "0|0|
S12S1S89S45SdS17S50S19S2S45A1A1A3A2S55A3"). Proof. reflexivity. Qed.
Lemma P_fail_eq : ltac2:(tb__ "0|0|
S12S1S76S5aS41S42S44S5bS4aA6S48A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma P_ok_eq : ltac2:(tb__ "0|0|
S12S1S76S5aS41S42S44S5cS4aA6S49A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition PD_adv : list (axst * ndesc) := ltac2:(tb__ "0|1|
S7S4S1S21A2M0S5S1S21S5bS61A4S7G0S5S1S21S5cS62A4S9G0A1A3A3").
Lemma imp_fail_tv : ltac2:(tb__ "0|0|
S12S6S4S15S15A2A1S81S38S42S5aS5bS41A4S5dA2S54A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ok_tv : ltac2:(tb__ "0|0|
S12S6S4S15S15A2A1S81S38S42S5aS5cS41A4S5dA2S54A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail_am : ltac2:(tb__ "0|0|
S12S26S25S38S42S5aS5bS41A4S5eA2S24S59SaA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ok_am : ltac2:(tb__ "0|0|
S12S26S25S38S42S5aS5cS41A4S5fA2S24S58SbA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition P0_vf (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|5|
S11S0S11S2dS3eVr;S47A2M0R1A2S2fR1S2eG0Z20A2A2A2S74VCST;Vr;VFB;VFF;R2A5F_;Fa;S14S12S0S3eVr;S46A2M1Z0A3S14S13S0S0S13S0S0S11S3cS4S0S0A2M2S5S0S0R2R1A4VFB;A3S11S2dR2S3eVr;S4bA2M3A2S2dS2eG3G1A2M4S2eR2R1A2A2A2A2Ln;A2Lb;A2S13S0S0S13S0S0S13S0S0S11S3cS4G2S0A2S5G2S0S5S0S0R3R2A4R1A4VFF;A3S11S2dR3G3A2S2dG4S2eR3R2A2A2A2A2Lfl;A2Ls;A2Lf;A2A2A2A2").
Definition is_vec (o : sobj) : bool := ltac2:(tb__ "0|1|
S8S8L_;M0S1bS1dVo;A1S47A2G0S1bS1fVo;A1S1aZ0A1A2S1bS1eVo;A1S1aZ20A1A2SaX8x2SaX8x2").
Definition is_vecX (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S79Vr;S5S15S15S47S1aZ20A1A4A2").

Lemma pclMA_monox : ltac2:(tb__ "0|2|
S6S4S0S0A2M0A1M1S16G1S6S4G0S0A2A1S16S6S4S15S15A2A1S6S4S4S15S0A2S15A2A1S0S74R8R7R6R5R1A5S74R9R8S80R7R5R4A3S75R6R5R3A3R2A5F_;Fa;Ffrs;Fkept;Frho;FFF;FFB;Frho0;FCST;").
Proof.
  intros CST rho0 FB FF rho kept frs a [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. split; [apply In_FBx; left; exact Hin | exact Hr].
  - right; right; right. exists f, s, fl. split; [apply In_FFx; left; exact Hin | exact Hr].
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S8cS16S6S32Q40A1A1S6aOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S86S10VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S87VCST;R1A2S11S2dZ0R2A2S2fR2S82A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S87VXGL;R1A2S11S2dZ0R2A2S2fR2S82A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S6S4S4S0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 4 BX.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S29VAInv;VCST;VXGL;VKc;S63VCST;VFB;VFF;A3VFB;VFF;VBX;S22Vnd;Aa").
Definition Posts_vf : list (axst * jpostA) := ltac2:(tb__ "0|1|
S7S4S1S36A2M0S5S1S36S4cS72S53A1A4S7G0S5S1S36S48S72S51A1A4S7G0S5S1S36S49S72S52A1A4S9G0A1A3A3A3").

Definition PD_vf : list (axst * ndesc) := ltac2:(tb__ "0|1|
S7S4S1S21A2M0S5S1S21S4cS53A4S7G0S5S1S21S48S51A4S7G0S5S1S21S49S52A4S9G0A1A3A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S28VAInv;VCST;VXGL;S3dVKc;Vrho0;S63VCST;VFB;VFF;A3VFB;VFF;VBX;S22Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S4S1S21A2S88Fn;") := ltac2:(tb__ "0|0|
S2bVAInv;VCST;VXGL;S3dVKc;Vrho0;S63VCST;VFB;VFF;A3VFB;VFF;VBX;S22Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S37S10S3dVrho0;Vtp0;S73A5").

Lemma P0_now : ltac2:(tb__ "0|4|
S16S7eS3dVrho0;R1A3S63VCST;VFB;VFF;Vrho0;A4S11S0S11S2dS3eR4S47A2M0R1A2S2fR1S2eG0Z20A2A2A2S74VCST;Vrho0;VFB;VFF;R2A5F_;Fa;S14S12S0S3eR3S46A2Z0A3S14S13S0S0S13S0S0S11S3cS4S0S0A2M1S5S0S0R2R1A4VFB;A3S11S2dR2S3eR5S4bA2M2A2S2dS2eG2S3eR5S46A2A2S2eR2R1A2A2A2A2Ln;A2Lb;A2S13S0S0S13S0S0S13S0S0S11S3cS4G1S0A2S5G1S0S5S0S0R3R2A4R1A4VFF;A3S11S2dR3S3eR6S4bA2M3A2S2dS2eG3S3eR6S46A2A2S2eR3R2A2A2A2A2Lfl;A2Ls;A2Lf;A2A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav H. unfold P0_vf, uval, vV, vL, vD in *. cbn [eval] in *.
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 17%positive eq_refl). exact H.
Qed.

Lemma go_holds : ltac2:(tb__ "0|0|
S16S6S32Q40A1A1S6S6bA1S6aVJAv;S43R4R3R2R1A5S6fS17S18R5A1S19S2S45A1A1A3S6fS17S18R6A1S50A3F_;F_;Fmd;Ftr;Ftp;Frho;").
Proof.
  intros rho tp tr md (Ai & kc & HJ) HF.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & _ & _ & _ & HP0 & _).
  fact HF (SPBranch BC_EQ (SMd M_MULHU vC vE) (SLit 0)) F1. fact HF (SPNot (SPBranch BC_EQ vC (SLit 0))) F2.
  fact HF (SPUle (SLit 1) vE) F3. fact HF (SPUle eC vL) F4.
  apply (proj1 (holds_beq _ _ _)) in F1. apply (proj1 (holds_nbeq _ _ _)) in F2. rewrite h_ule in F3, F4.
  rewrite U_mulhu in F1. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)) in F1, F2.
  change (bv_unsigned (eval rho vC)) with (uval rho vC) in F1, F2. change (bv_unsigned (eval rho vE)) with (uval rho vE) in F1.
  rewrite uval_lit in F1 by lia. rewrite uval_lit in F2 by lia. rewrite uval_lit in F3 by lia.
  pose proof (uval_range rho vC) as RC. pose proof (uval_range rho vE) as RE. pose proof (uval_range rho vL) as RL. pose proof (uval_range rho vD) as RD.
  rewrite Z.shiftr_div_pow2 in F1 by lia. unfold M64v in F1.
  assert (HP : uval rho vC * uval rho vE < 2 ^ 64).
  { destruct (Z_lt_dec (uval rho vC * uval rho vE) (2 ^ 64)) as [L|L]; [exact L|]. exfalso.
    assert (1 <= uval rho vC * uval rho vE / 2 ^ 64) by (apply Z.div_le_lower_bound; lia).
    assert (uval rho vC * uval rho vE / 2 ^ 64 < 2 ^ 64) by (apply Z.div_lt_upper_bound; [lia|]; nia).
    rewrite Z.mod_small in F1 by lia. lia. }
  assert (EC : uval rho eC = uval rho vE * uval rho vC).
  { unfold eC, uval. rewrite U_mul. unfold M64v. change (bv_unsigned (eval rho vE)) with (uval rho vE). change (bv_unsigned (eval rho vC)) with (uval rho vC).
    rewrite Z.mod_small by nia. reflexivity. }
  assert (G1 : 1 <= uval rho eC) by (rewrite EC; nia).
  unfold go_facts. constructor; [|constructor; [|constructor]]; rewrite h_ule; rewrite uval_lit by lia; [|exact G1].

  destruct (P0_now rho Hav HP0) as [_ [HL|[(b & n & Hin & H1 & H2)|(f & s & fl & Hin & H1 & H2)]]]; [exfalso; lia| |].
  - destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & HBl & _). destruct (HBl b n (HB _ Hin)) as (_ & _ & B3 & _). lia.
  - destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & _ & HFr). destruct (HFr f s (proj1 (HFF _ _ _ Hin))) as (_ & _ & _ & F4' & _).
    unfold IMG_HI in F4'. lia.
Qed.

Lemma HIN_call : ltac2:(tb__ "0|2|
S16S71S6fS17S18R2A1S19S2S41A1A1A3S63VCST;VFB;VFF;Vrho0;A4S7eS3dVrho0;R4A3S11S78VCST;Vrho0;VFB;VFF;R5S9S4S15S15A2A1M0S9S4S4S15S0A2S15A2A1M1S44A8S11S7aVCST;VXGL;Vrho0;VFB;VFF;R5G0G1S4aA9S7dVCST;S80VFB;R5G0A3S75VFF;R5G1A3S6dS6cR5S44R4A3S42A2A4A2A2F_;F_;F_;Fms;Frho;").
Proof.
  intros rho ms HF HP0 Hav. destruct (P0_now rho Hav HP0) as [HV HD].
  split; [|split].
  - intros o a Ho Hr. cbn in Ho. destruct Ho as [<-|[]]. apply pclMA_monox. apply HV.
    unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi O_vec] in Hr. rewrite !soff_lit_small in Hr by lia. cbn [fst snd] in Hr. unfold uval, vV in *. lia.
  - intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha. rewrite uval_lit in Ha by lia. left. apply pclMA_monox. apply HV. unfold uval, vV in *. lia.
  - unfold P0_ad. intros a Ha. unfold uval, vSRC, vLS in Ha. cbn [eval] in Ha. rewrite !rw_call' in Ha.
    change (wsub_get s_call 13) with vD in Ha. change (wsub_get s_call 16) with vL in Ha.
    change (bv_unsigned (eval rho vD)) with (uval rho vD) in Ha. change (bv_unsigned (eval rho vL)) with (uval rho vL) in Ha.
    destruct HD as [HL|[(b & n & Hin & H1 & H2)|(f & s & fl & Hin & H1 & H2)]]; [exfalso; lia| |].
    + right; right; left. exists b, n. split; [apply In_FBx; left; exact Hin | lia].
    + right; right; right. exists f, s, fl. split; [apply In_FFx; left; exact Hin | lia].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S0S6S32Q40A1A1S65F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S34S1S16S6S32Q40A1A1S65S6fS17S18R3A1S19S2R4A1A1A3VTR;S33S10R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S65S65S65S68R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S34S34S1S1S6eS6S20A1M0S6S4S1S36A2M1A1S6S4S15S15A2M2A1S65S16S6S32Q40A1A1M3G2S3cG2R1R5A3S3cG2R2S3RbA1A3F_;Fr;S12SfG0A1S3bRaR9R8A3ScG0R7A2A3S12S8S3aRbRaR9R8S70G1S1SeS1S36A2R7A4A5SbA3S16G3VTR;S33S10RfRdR2R1A5S37S10S1cS2RdA1A1R2R1RaA5A2Ftp1;Frho1;S6S6bA1M4S71S6aS35S10R9R8R10S5G4S7bR3S7cR2R1A2A4A5R13RaR9R4R2A4R13S6dS6cRbRfS69R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S1S36G4S71S6aS16G3G4S71S6aS3cG1S5S1S36RaR9A4R14A3S35S10R12R11R19S5G4S7bR9S7cR8R7A2A4A5R1cR13R12RaR8A4S7eS1cS2R1aA1A1S6dS6cR14R18S69R9R13RaA3A3R19A2R8A3S35S10R9R8ReS5G4S7bR7S7cR6R5A2A4A5ReS6dS6cR16R1aS69RbR15RcA3A3R1bA2R15RaR9R8R6A6S11S8aR17S69RcR16RdA3R1bR1cR1dR10R1eR19RbA9S16S7fR18S69RdR17ReA3R1cR1dS2R1eA1S2R1fA1S2R11A1R1RcA9VTR;S33S10S39R11S6dS6cR19R1dS69ReR18RfA3A3R1eA2R18RdRcA5S8bR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S33S10R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CAD : ltac2:(tb__ "0|1|
S6S4S0S0A2M0A1S6S4G0S0A2A1S40S16S6S32Q40A1A1S3fZ3R3A2VTR;S33S10S23VAInv;VCST;VXGL;VKc;S7dVCST;R6R5A3R6R5R4S22S60AaS5aR3R2A5S37S10S3dR3R2S77VAInv;VCST;VXGL;VKc;S7dVCST;A1S22S64R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S1S21S4S0S15A2M0S16S6S32Q40A1A1M1S0G1S3cS4S4S1S21A2M2G0A2S5G2G0S5S1S21R7R6A4R5A4S4eA3S11S2dZ0S27S5G2G0S5S1S21R8R7A4R6A4R5A2M3A2S2fG3R3A2A2VTR;S33S10VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S1S21S16S6S32Q40A1A1M0S0G0S3cS4S1S36A2S5S1S36R6S72R5A1A4S73A3VTR;S33S10VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.
Ltac vmr := vm_compute; reflexivity.
Tactic Notation "innth" integer(n) := cbn [In cutsV exitsV Posts_vf PD_vf PD_adv]; do n right; left; reflexivity.

Lemma X_X_go : ltac2:(tb__ "0|1|
S16S6S32Q40A1A1M0S0G0S2dS30Z5aS31Z2Z40A2A2R2A2VTR;S33S10VJAv;S43A1S45R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_go nd0 (80, z0)); [innth 1 | meas]].
  intros w Hw. rewrite <- C_go_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
  intros tr md HJ HF. apply Forall_app. split; [exact (go_holds rho tp tr md HJ HF) | exact HF].
Qed.

Lemma X_E_call : ltac2:(tb__ "0|1|
S16S6S32Q40A1A1M0S0G0S2dS30Z46S31Z2Z40A2A2R2A2VTR;S33S10VJAv;S43A1S41R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF. unfold nd0. change tv_vf with ([] ++ tv_vf).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue HKc HBX (P0_ad CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_ad OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.nd0 PD_adv NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CAD eq_refl
           E_call s_call R_call Xk_call rho tp [] tv_vf [] CHv [] am_vf (FAM b tp0)).
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - apply payA_of_bud_pay. vmr.
  - vmr.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK. exact (HIN_call rho ms HF' HP0 Hav).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_adv In] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am ndF ndK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.nd0 ND am_subst app].
    + rewrite P_fail_eq, imp_fail_tv, imp_fail_am. change (bd_subst _ []) with (@nil bitem). cbn [app]. apply POST. innth 1.
    + rewrite P_ok_eq, imp_ok_tv, imp_ok_am. change (bd_subst _ []) with (@nil bitem). cbn [app]. apply POST. innth 2.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S1S21S4S0S15A2M0S16S6S32Q40A1A1M1G1S3cS4S4S1S21A2M2G0A2S5G2G0S5S1S21R6R5A4R4A4S4fA3VTR;S33S10VJAv;R6A1R7R4R3A5VFAM;S27S5G2G0S5S1S21R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsV] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <- <-.
  - apply X_X_go. meas.
  - apply X_E_call. meas.
  - apply POST. innth 0.
  - apply POST. innth 1.
  - apply POST. innth 2.
Qed.
End X.

Lemma ejcertV_ok : ltac2:(tb__ "0|0|
S12S8S2aS10S3dS56S57P64S4eS4fA7SbA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S2cS10VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S84S10S83VAInv;VCST;VXGL;A5").

Theorem vec_finalize_sum : ltac2:(tb__ "0|0|
S6S32Q40A1A1S67S10Vok;S33S10S23VAInv;VCST;VXGL;VKc;S63VCST;VFB;VFF;A3VFB;VFF;VBX;S22S43AaS4dVrho0;R1A5S37S10S3dVrho0;R1S73A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue HKc ALA FUEL_vf cutpcs_vf 100
                (map edropA cutsV) (map edropA exitsV) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertV_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsV)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (arena_dup_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue ok (map edropA cutsV) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_vf CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_vf P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S85S10S83VAInv;VCST;VXGL;A5").

Theorem vec_finalize_sum_ex : ltac2:(tb__ "0|0|
S6S32Q40A1A1S66S10S33S10S23VAInv;VCST;VXGL;VKc;S63VCST;VFB;VFF;A3VFB;VFF;VBX;S22S43AaS4dVrho0;R1A5S37S10S3dVrho0;R1S73A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue HKc ALA FUEL_vf cutpcs_vf 100 cutsV exitsV (Q tp0) ejcertV_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue) cutsV) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (arena_dup_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue cutsV T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_vf CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_vf P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_vec_finalize_pf.

(* [comment removed for export] *)
Module Lib_handle_mtllib.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "app"; "list"; "option"; "None"; "Some"; "false"; "true"; "S"; "bool"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "cell"; "sprop"; "ss_objs"; "FcsrFrm0"; "mkCell"; "mkSS"; "SPUle"; "mkObj"; "DUnknown"; "DZero"; "SVar"; "ss_facts"; "SAlu"; "SExt"; "SPAlign"; "SPBranch"; "ob_base"; "ob_hi"; "ob_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "leafA"; "ax_setS"; "sym_runA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ANone"; "NDA"; "ejcertA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_handle_mtllib"; "z0"; "nd0"; "ndP"; "E_da"; "T_sm1"; "X_ml"; "C_pro0"; "E_sm0"; "FUEL_ml"; "X_pro"; "cutpcs_ml"; "ml_facts"; "C_epi"; "C_pre"; "C_pro"; "E_da0"; "O_F"; "O_Wm"; "O_cfg"; "P_fail"; "P_ok"; "T_da0"; "T_sm"; "X_rl"; "Y_da"; "objs_post"; "objs_pro"; "objs_sm1"; "optAp"; "qERR"; "sel_rel"; "BAD"; "C_rl"; "NZ32"; "Pre_ml"; "Pre_sm"; "R_da"; "R_sm"; "cells_pro"; "cfg_facts"; "cutsM"; "epi_state"; "exitsM"; "fr_ml"; "objs_ml"; "s_da"; "s_sm"; "sel_sm"; "xf_tda"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "xCFG"; "NPH"; "hF"; "HNEXT"; "O_cE"; "O_cP"; "O_text"; "P_hdr"; "hFL"; "hG"; "h_fregs"; "tI"; "handle_facts"; "tB"; "tL"; "@Corelib.Lists.ListDef"; "seq"; "map"; "firstn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "segs"; "leavesA_at"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_handle_mtllib.HMLAddr"; "DW"; "FR"; "ml_ret"; "ml_PRO"; "ml_REL"; "ml_entry"; "sm1_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "O_al"; "P_alloc"; "P_st"; "vERR"; "vAL"; "vb"; "vc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "P_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "spm"; "vDp"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "post_regs"; "pre_fregs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "fs_frame_size"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "L_stack_malloc"; "Pre_stack_malloc"; "V_DEPTH"; "flagbyte_obj"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.DiagAppendAddr"; "da_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS";
"flag_carve_stateA"; "frame_open_stateA"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr DiagAppendAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module HMLAddr.
  Definition ml_entry : Z := 0xa1a3c.
  Definition sm1_pc : Z := 0x47a7c.
  Definition ml_PRO : Z := 0xa1b58.
  Definition ml_EPI : Z := 0xa2114.
  Definition ml_REL : Z := 0xa21c0.
  Definition ml_ret : Z := 0xa21fc.
  Definition ml_ra_da : Z := 0xa20fc.
  Definition DW : Z := 4608.
  Definition FR : Z := 256.
End HMLAddr.
Import HMLAddr.

Definition FUEL_ml : nat := 300%nat.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S1cPaA1S11SaeS81A1A1S11Z0A1Vcells;S1aA5").
Definition O_Wm : sobj := ltac2:(tb__ "0|0|
S19S90S81A1S91S11Z0A1S2S12A1S1aA5").

Definition O_cfg : sobj := ltac2:(tb__ "0|1|
S19S68S11Z0A1S11Z90A1S0S12S16S11Z30A1Z2S11Z101A1A3S0S12S16S11Z32A1Z1M0S11G0A1A3S0S12S16S11Z38A1Z4S11ZffffffffA1A3S2S12A1A3A3A3S1bA5").
Definition cfg_facts : list sprop := ltac2:(tb__ "0|0|
S0S13S20P6dZ3A2S0S13S18S11S9aA1S68A2S0S13S18S1eSa1S68S11Z90A1A3S1cP1eA1A2S0S13S18S68S11S92A1A2S2S13A1A3A3A3A3").
Definition ml_facts : list sprop := ltac2:(tb__ "0|0|
S5S13S74S81S80A2S5eA3").
Definition X_ml : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3SfSfA2M0S1SfSfS8cS11Z518A1A4S0G0S1SfSfS8dS11Z10A1A4S0G0S1SfSfS8bS11Z30A1A4S0G0S1SfSfS75S76A4S0G0S1SfSfS68S11Z90A1A4S0G0S1SfSfS90S80A1S11S80A1A4S2G0A1A3A3A3A3A3A3").
Definition objs_ml (err : sv) (fcells : list cell) : list sobj := ltac2:(tb__ "0|0|
S5S10S0S10S47Vfcells;A1S0S10S48S0S10S88S0S10S6fS0S10S89Verr;A1S0S10S87S0S10S6dS73A1S0S10S6cS0S10S6eS0S10S49S2S10A1A3A3A3A3A3A3A3A3A3A3S7cA3").
Definition Pre_ml_S : sstate := ltac2:(tb__ "0|0|
S17S85S98S97S15S8SfA1S63S8aS2S12A1A2S42S69SaA9").
Definition Pre_ml : axst := mkA Pre_ml_S X_ml.
Definition nd0 : ndesc := ND [] [] [].

Definition cutpcs_ml : list Z := ltac2:(tb__ "0|0|
S0S2bS86S0S2bS83S0S2bSa3S0S2bS84S2S2bA1A3A3A3A3").
Definition BAD : axst := ltac2:(tb__ "0|1|
S7bS17Z0S2SfA1M0G0S15S8SfA1S2S10A1S2S13A1P1SaA9S2S3SfSfA2A1A2").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leaf_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S7aS25Vk;S7eS3fS41VS;Vpc;A4S56A4").
Definition lvs (S : axst) : list (Z * stop_reason) := ltac2:(tb__ "0|2|
S7S6S28A1M0A1S6S3S2bSa5A2M1A1Lx;S2aS7dS3fS41VS;SbA5G0S78S28G1S7fR1A4Ll;S2G1A1X7x2").
Definition shape (A : axst) : ltac2:(tb__ "0|0|
S6S3S3SfSfA2SfA2A1") := ltac2:(tb__ "0|1|
S78S10S3S3SfSfA2M0SfA2S10S1G0SfS1SfSfS22R1A1S24R1A1A4S23R1A1A4Lo;S14S26VA;A1A1A4").

Definition E_sm0 : axst := Eval vm_compute in leaf_at Pre_ml sm1_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 1.
Definition L_sm : axst := L_stack_malloc AE_A 1.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S3S2cSfA2S1S2cSfS9eS91A4S93PaS26S3eA1S26S5aA1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Goal lvs Pre_ml = [(sm1_pc, RsCut)] /\ entails_frA E_sm0 Pre_sm s_sm = Some R_sm /\ call_checkPA E_sm0 Pre_sm s_sm R_sm [L_sm] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.
Definition fr_ml : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S3S3SfS2bA2M0SfA2M1S1G0SfS1SfS2bS6aZ1A4S70A4S2G1A1A3").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S5S4S77U0Vi;A2S5S4S77ScVi;A1M0Sa0SeS10S14S26VA;A1A1A2G0A2A2S0S4Vi;S2S4A1A3A3A3").
Definition T_sm1 : axst := Eval vm_compute in optAp (apply_axforms T_sm [AXSelect (sel_last T_sm 3)]).
Definition objs_sm1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_sm1)).
Goal ss_objs (ax_S T_sm1) = objs_sm1 ++ [flagbyte_obj hFL [mkCell (SLit 0) 1 (SLit 1)]] /\ ax_X T_sm1 = X_ml ++ (hF, SLit 128) :: [] /\ ss_next (ax_S T_sm1) = hG.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 objs_sm1 X_ml 160 128.
Definition C_pro : axst := Eval vm_compute in ax_setX C_pro0 ((hF, SLit 0) :: ax_X C_pro0).

Definition X_pro : axst := Eval vm_compute in leaf_at C_pro ml_PRO 0.
Definition sh_pro : sobj := Eval vm_compute in last (ss_objs (ax_S X_pro)) O_Wm.
Definition objs_pro : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_pro)).
Goal lvs C_pro = [(ml_PRO, RsCut)] /\ sh_pro = shobj hG 0 16 (ob_cells sh_pro) DZero.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition C_pre : axst := Eval vm_compute in shadow_release_stateA X_pro objs_pro 160 [].
Definition E_da0 : axst := Eval vm_compute in leaf_at C_pre da_entry 0.
Goal lvs C_pre = [(da_entry, RsCut)]. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_da : axst := Eval vm_compute in optAp (apply_axforms E_da0 [AXSplit 0 (SLit (-96))]).
Definition s_da : wsub := ltac2:(tb__ "0|0|
S93PaS26S3aA1S26S8eA1A3").
Definition R_da : list sobj := Eval vm_compute in optR (entails_frA E_da Pre_da s_da).
Goal entails_frA E_da Pre_da s_da = Some R_da /\ call_checkA E_da Pre_da s_da R_da (map la_state Posts_da) = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T_pure (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S94S1dS26VCl;A1A1S95Vs;VPre;VL;VCl;VR;A5A2").
Definition T_da0 : axst := Eval vm_compute in T_pure Pre_da E_da s_da R_da P_da.

Definition xf_tda : list axform := ltac2:(tb__ "0|1|
S0S32S34S5S4S0S4U3S0S4U0M0S0S4U4S0S4U5S0S4U1S0S4U2S2S4A1A3A3A3A3A3A3S77U6U9A2A3A1S0S32S35G0A1S2S32A1A3A3").
Definition Y_da : axst := Eval vm_compute in optAp (apply_axforms T_da0 xf_tda).
Definition epi_state (Y : axst) : axst := ltac2:(tb__ "0|0|
Sa9SacVY;S27VY;A1S71Z0Z10A5PaaA2").
Definition C_epi : axst := Eval vm_compute in epi_state Y_da.

Definition X_rl : axst := Eval vm_compute in leaf_at C_epi ml_REL 0.
Definition sel_rel : list nat := ltac2:(tb__ "0|1|
S5S4S0S4U0S2S4A1M0A3S5S4S77U3UbA2S0S4U1S0S4U2S0S4UeS0S4UfG0A3A3A3A3A3A3").
Definition rel_state (X : axst) : axst := ltac2:(tb__ "0|1|
S53S33VX;S0S32S34S55A1S2S32A1A3A2A1S25S29R1Sa4S26R1A1M0S79S10UcS14G0A1A3A2A2TX1;").
Definition C_rl : axst := Eval vm_compute in rel_state X_rl.
Definition X_ret : axst := Eval vm_compute in leaf_at C_rl ml_ret 0.
Goal shape Y_da = shape E_da0 /\ lvs C_epi = [(ml_REL, RsCut)]
  /\ release_objs_ok 160 170 hG 1 (skipn 12 (ss_objs (ax_S (optAp (apply_axforms X_rl [AXSelect sel_rel]))))) = true
  /\ length (ss_objs (ax_S C_rl)) = 12%nat /\ lvs C_rl = [(ml_ret, RsSymJump)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition qERR : sv := SVar 315.
Definition objs_post (err : sv) : list sobj := ltac2:(tb__ "0|1|
S5S10S0S10S48S2S10A1M0A3S5S10S7cS0S10S47S2S12A1A1S0S10S88S0S10S6fS0S10S89Verr;A1S0S10S87S0S10S6dS73A1S0S10S6cS0S10S6eS0S10S49G0A3A3A3A3A3A3A3A3A3A3A3").
Definition NZ32 (e : sv) : sprop := ltac2:(tb__ "0|0|
S21Sa2S1fSbQ20Ve;A3S11Z0A1A3").
Definition P_ok : axst := ltac2:(tb__ "0|0|
S7bS17S82S96P190A1S72S15S8SfA1S50S8aA1S42S6bSaA9S3cA2").
Definition P_fail : axst := ltac2:(tb__ "0|0|
S7bS17S82S96P190A1S72S15S8SfA1S50S54A1S0S13S58S54A1S42A3S6bSaA9S3cA2").
Definition Posts_ml : list (axst * ndesc) := ltac2:(tb__ "0|1|
S0S3S25S2dA2M0S1S25S2dS4aS38A4S0G0S1S25S2dS4bS38A4S2G0A1A3A3").
Goal leaf_matches1A NPH X_ret P_ok = true /\ leaf_matches1A NPH X_ret P_fail = false. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ndP : ndesc := ltac2:(tb__ "0|0|
S2fS2S3SfSfA2A1S62S2Sa7A1S2eA4").
Definition z0 : sv := SLit 0.
Definition cutsM : list edescA := ltac2:(tb__ "0|3|
S0S3S3S25S2dA2M0S3S2bSfA2M1A2M2S1G0G1S1S25S2dS59S38A4S1S2bSfZ64S37A4A4S0G2S1G0G1S1S25S2dS45S39A4S1S2bSfZ60S37A4A4S0G2S1G0G1S1S25S2dS44S39A4S1S2bSfZ5cS37A4A4S0G2S1G0G1S1S25S2dS43S39A4S1S2bSfZ32S37A4A4S0G2S1G0G1S1S25S2dS57S38A4S1S2bSfZ14S37A4A4S2G2A1A3A3A3A3A3").
Definition exitsM : list edescA := ltac2:(tb__ "0|4|
S0S3S3S25S2dA2M0S3S2bSfA2M1A2M2S1G0G1S1S25S2dS3eS38A4S1S2bSfZ62S37A4A4S0G2S1G0G1S1S25S2dS40S39A4S1S2bSfZ5eS37A4A4S0G2S1G0G1S1S25S2dS46S39A4S1S2bSfZ5aS37A4A4S0G2S1G0G1S1S25S2dS4eS39A4S1S2bSfZ1eS37A4A4S0G2S1G0G1S1S25S2dS4aS38A4S1S2bSfZ0S37A4M3A4S0G2S1G0G1S1S25S2dS4bS38A4G3A4S2G2A1A3A3A3A3A3A3").
Lemma ejcertM_ok : ltac2:(tb__ "0|0|
S31SdS30S7dS69S3fS41S69S5fS61A7SbA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma T_sm_eq : ltac2:(tb__ "0|1|
S31S25Sa8S9dS9bZ1M0A2S3eS65S5cS9cS9bG0A2A5S4dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sel_sm : list nat := Eval vm_compute in sel_last T_sm 3.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S31S7S25A1S33S4dS0S32S34S66A1S2S32A1A3A2S9S25S3bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_objs : ltac2:(tb__ "0|1|
S31S6S10A1S14S26S3bA1A1S5S10S52S0S10S9fS70S0S12S16S11Z0A1Z1M0S11G0A1A3S2S12A1A3A2S2S10A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_X : ltac2:(tb__ "0|1|
S31S6S3SfSfA2M0A1S27S3bA1S5G0S3cS0G0S1SfSfS6aS11S99Z1A1A1A4S2G0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|0|
S31S25SaaS3bS52S3cPa0S99Z1A1A5S3dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro_eq : ltac2:(tb__ "0|0|
S31S25Sa6S3dS0S3SfSfA2S1SfSfS6aS11Z0A1A4S27S3dA1A3A2S45A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition cells_pro : list cell := Eval vm_compute in ob_cells sh_pro.
Lemma X_pro_objs : ltac2:(tb__ "0|0|
S31S6S10A1S14S26S40A1A1S5S10S51S0S10SadS71Z0Z10S5dS1bA5S2S10A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pre_eq : ltac2:(tb__ "0|0|
S31S25SabS40S51Pa0S2S3S2bS2bA2A1A4S44A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_da_eq : ltac2:(tb__ "0|0|
S31S7S25A1S33S46S0S32S36U0S11N60A1A2S2S32A1A3A2S9S25S3aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_da0_eq : ltac2:(tb__ "0|0|
S31S25S94S1dS26S3aA1A1S95S64S8eS8fS3aS5bA5A2S4cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_da_eq : ltac2:(tb__ "0|0|
S31S7S25A1S33S4cS67A2S9S25S4fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_epi_eq : ltac2:(tb__ "0|0|
S31S25S60S4fA1S43A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rl_eq : ltac2:(tb__ "0|1|
S31S7S25A1S33S4eS0S32S34S55A1S2S32A1A3A2M0S9S25S53G0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_handle_mtllib.

(* [comment removed for export] *)
Module Lib_builderH_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sv_eqb"; "SLit"; "sobj"; "sprop"; "holds"; "ob_base"; "ob_hi"; "ob_lo"; "obj_range"; "ss_facts"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "false"; "list"; "bool"; "prod"; "true"; "andb"; "None"; "nat"; "orb"; "fst"; "snd"; "option"; "pair"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "True"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "leb"; "add"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "extraOH"; "extraXH"; "in_callersH"; "litb"; "alb"; "bvecb"; "pieceb"; "textb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vb"; "vAL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf"; "baseF"; "basez"; "P0_builder"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "tB"; "tL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "tvd"; "tvz"; "FBx"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "TPA"; "frinA"; "tvinA"; "fbinA"; "ffinA"; "ANone"; "NDA"; "PTrue"; "frozen"; "nd_below"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pclMA"; "FFx"; "xr_eqb"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "robjs_checkF"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "is_shadowZ"; "payA"; "robjs_okA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "robjs_okF"; "xrs_ok47"; "@Stdlib.Lists.List"; "In"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition litb (e : sv) (lo hi : Z) : bool := ltac2:(tb__ "0|3|
S0S12Le;Ve;SdS15S24Vlo;R1A2S24R1Vhi;A2A2Lz;SeS10Li;S26S0S0S10Lb;La;M0Lop;M1G1S27G0Lop;M2G2S12SfS0S10La;Lw;Lsgn;SeS0SdS10Lk;Li;Ll;X0x8").
Lemma litb_sound : ltac2:(tb__ "0|0|
S0SdSdS1dS12S2fR3R2R1A3S14A3S21SdSdS1eS1dS0R5S3R1A1A3S1eS22R4R1A2S22R1R3A2A2A2Lz;A2F_;Fhi;Flo;Fe;").
Proof. intros [z| | | | | | |] lo hi H; cbn in H; try discriminate. apply andb_prop in H as [A B]. exists z. apply Z.leb_le in A. apply Z.leb_le in B. auto. Qed.

Definition pieceb (o : sobj) : bool := ltac2:(tb__ "0|2|
S15S15S2S7Vo;A1S34A2S2fS9Vo;A1Z0M0Z518M1A3A2S2fS8Vo;A1G0G1A3A2").

Definition bvecb (o : sobj) : bool := ltac2:(tb__ "0|9|
S0S12Lx;S7Vo;A1SdS10Lz;SeS10Li;M0S26S0S0S26S12Lop;R3S0S12Lb0;R1SdS15S15S15S15S2R3S34A2S24Z0M1R1A2A2S24R1Z4f8A2A2S2S9Vo;A1S3G1A1A2A2S2S8Vo;A1S3Z20A1A2A2Lk;G0S26S0S0S10Lb1;La;M2Lop0;M3G3S27G2Lop0;M4G4S12SfS0S10La;Lw;Lsgn;M5SeS0SdS10Lk;Li;Ll;M6X0x8S10S10S10S10S10S10S10S10S10X26xaLb0;Lb;Lop;S26S0S0S10Lb;La;M7Lop;S27G7Lop;M8G8G5G6X0x8").
Definition alb (o : sobj) : bool := ltac2:(tb__ "0|0|
S15S15S2S7Vo;A1S35A2S2S9Vo;A1S3Z0A1A2A2S2S8Vo;A1S3Z30A1A2A2").
Definition textb (o : sobj) : bool := ltac2:(tb__ "0|0|
S15S15S2S7Vo;A1S3fA2S2S9Vo;A1S3Z0A1A2A2S2S8Vo;A1S40A2A2").
Definition extraOH (o : sobj) : bool := ltac2:(tb__ "0|0|
S18S18S18S32Vo;A1S31Vo;A1A2S30Vo;A1A2S33Vo;A1A2").

Definition extraXH (r : sv * sv) : bool := ltac2:(tb__ "0|a|
S18S18S18S53Vr;S1cS0S0S34S3Z518M0A1A4A2S53Vr;S1cS0S0S35S3Z30A1A4A2A2S53Vr;S1cS0S0S3fS40A4A2A2S13S0S0A2S12Lr;Vr;S0S0S0S12Ls;R2SdS10Lz;SeS10Li;M1S26S0S0S26S12Lop;R3S0S12Lb0;R1SdS0S12Ls0;R5SdS15S15S15S2R4S34A2S24Z0M2R2A2A2S24G2R1A2A2S24S25R2R1A2G0A2A2Ln;G1S26S0S0S10Lb1;La;M3Lop0;M4G4S27G3Lop0;M5G5S12SfS0S10La;Lw;Lsgn;M6SeS0SdS10Lk0;Li;Ll;X0x8Lk;G1G4G4G5G5G6SeS0SdS10Lk;Li;Ll;M7X0x8S10S10S10S10S10S10S10S10S10X26xaLb0;Lb;Lop;S26S0S0S10Lb;La;M8Lop;S27G8Lop;M9G9G6G7X0x8Ls0;Ls;X13x1A2").
Definition in_callersH (rho : valuation) (a : Z) : Prop := ltac2:(tb__ "0|3|
S1fS1eS22S28Vrho;S34A2M0Va;A2S23Va;S25G0Z518A2A2A2S1fS1eS22S28Vrho;S35A2M1Va;A2S23Va;S25G1Z30A2A2A2S1eS22S28Vrho;S3fA2M2Va;A2S23Va;S25G2S28Vrho;S40A2A2A2A2A2A2").

Lemma sv_eqb_eq : ltac2:(tb__ "0|0|
S0S0S1dS12S2R2R1A2S14A3S1dS0R3R2A3F_;Fb;Fa;").
Proof. intros a b H. apply sv_eqb_sound in H. exact H. Qed.

Lemma extraOH_sound : ltac2:(tb__ "0|1|
SdS1S4SdS3bR4R3A2S1dS12S2cR3A1S14A3S1eS22S19SdSdSaR5R4A2M0A3R3A2S23R3S1aSdSdG0A3A2A2S2eR6R4A2F_;F_;F_;Fa;Fo;Frho;FDW;").
Proof.
  intros DW rho o a [Bsp Bb Bal BL BB Btop] HE Hr. rewrite aceil_val in *. unfold IMG_HI in *.
  unfold extraOH in HE. unfold in_callersH.
  apply orb_prop in HE as [HE|HE]; [apply orb_prop in HE as [HE|HE]; [apply orb_prop in HE as [HE|HE]|]|].
  -   unfold pieceb in HE. apply andb_prop in HE as [HE Hh]. apply andb_prop in HE as [Hb Hl]. apply sv_eqb_eq in Hb.
    destruct (litb_sound _ _ _ Hl) as (lo & El & Rl). destruct (litb_sound _ _ _ Hh) as (hi & Eh & Rh).
    eapply obj_rangeZ in Hr; [| rewrite El; apply soff_lit_small; lia | rewrite Eh; apply soff_lit_small; lia]. rewrite Hb in Hr. left. lia.
  -   unfold bvecb in HE. destruct (ob_base o) as [|v|op b e| | | | |] eqn:EB; try discriminate.
    destruct op; try discriminate. destruct e as [k| | | | | | |]; try discriminate.
    apply andb_prop in HE as [HE Hh]. apply andb_prop in HE as [HE Hl]. apply andb_prop in HE as [HE Hk2]. apply andb_prop in HE as [Hb Hk1].
    apply sv_eqb_eq in Hb. apply sv_eqb_eq in Hl. apply sv_eqb_eq in Hh. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. subst b.
    eapply obj_rangeZ in Hr; [| rewrite Hl; apply soff_lit_small; lia | rewrite Hh; apply soff_lit_small; lia]. rewrite EB in Hr.
    pose proof (uval_range rho vb). rewrite (uval_add_litZ rho vb k) in Hr by lia. left. lia.
  -   unfold alb in HE. apply andb_prop in HE as [HE Hh]. apply andb_prop in HE as [Hb Hl]. apply sv_eqb_eq in Hb. apply sv_eqb_eq in Hl. apply sv_eqb_eq in Hh.
    eapply obj_rangeZ in Hr; [| rewrite Hl; apply soff_lit_small; lia | rewrite Hh; apply soff_lit_small; lia]. rewrite Hb in Hr. right; left. lia.
  -   unfold textb in HE. apply andb_prop in HE as [HE Hh]. apply andb_prop in HE as [Hb Hl]. apply sv_eqb_eq in Hb. apply sv_eqb_eq in Hl. apply sv_eqb_eq in Hh.
    eapply obj_rangeZ in Hr; [| rewrite Hl; apply soff_lit_small; lia | rewrite Hh; apply soff_smallu; change tL with vL; lia]. rewrite Hb in Hr. right; right. lia.
Qed.

Lemma extraXH_sound : ltac2:(tb__ "0|1|
SdS1S13S0S0A2SdS3bR4R3A2S1dS12S2dR3A1S14A3S1eS22S28R5S19S0S0R4A3A2M0R3A2S23R3S25G0S28R5S1aS0S0R4A3A2A2A2A2S2eR6R4A2F_;F_;F_;Fa;Fr;Frho;FDW;").
Proof.
  intros DW rho r a [Bsp Bb Bal BL BB Btop] HE Hr. rewrite aceil_val in *. unfold IMG_HI in *.
  unfold extraXH in HE. unfold in_callersH.
  apply orb_prop in HE as [HE|HE]; [apply orb_prop in HE as [HE|HE]; [apply orb_prop in HE as [HE|HE]|]|].
  - apply xr_eqb_sound in HE. subst r. cbn [fst snd] in Hr. rewrite uval_lit in Hr by lia. left. lia.
  - apply xr_eqb_sound in HE. subst r. cbn [fst snd] in Hr. rewrite uval_lit in Hr by lia. right; left. lia.
  - apply xr_eqb_sound in HE. subst r. cbn [fst snd] in Hr. right; right. exact Hr.
  - destruct r as [e n]. destruct e as [|v|op b e'| | | | |]; try discriminate. destruct op; try discriminate.
    destruct e' as [k| | | | | | |]; try discriminate. destruct n as [n| | | | | | |]; try discriminate.
    apply andb_prop in HE as [HE H3]. apply andb_prop in HE as [HE H2]. apply andb_prop in HE as [Hb H1].
    apply sv_eqb_eq in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. subst b. cbn [fst snd] in Hr.
    pose proof (uval_range rho vb). rewrite (uval_add_litZ rho vb k) in Hr by lia. rewrite uval_lit in Hr by lia. left. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S36S1S11S3dQ40A1A1S39OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
SdS5dVCST;R1A2S1eS22Z0R2A2S23R2S58A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SdS5dVXGL;R1A2S1eS22Z0R2A2S23R2S58A2A2F_;Fa;").

Variable NPc : positive.
Hypothesis HNPc : (NF <= NPc)%positive.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S11S13S13SdSdA2SdA2A1").
Variable BX : bxt.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Hypothesis HP0b : ltac2:(tb__ "0|0|
S1VP0f;R1A1S3cVCST;VFB;VFF;R2A4F_;Fr;").
Variable DW : Z.
Hypothesis HDW : 0 <= DW < 2 ^ 40.

Lemma agree_NF : ltac2:(tb__ "0|0|
S1S2bVNPc;Vrho0;R1A3S2bS62Vrho0;R2A3F_;Frho;").
Proof.
  intros rho [H1 H2]. split; [|exact H2]. intros v Hv. apply H1. pose proof HNPc. lia.
Qed.

Lemma P0b_nowH : ltac2:(tb__ "0|1|
S1S2bVNPc;Vrho0;R1A3VP0f;Vrho0;A1S1eSdS1eS22S28R4S3fA2M0R1A2S23R1S25G0S28R4S40A2A2A2A2S51VCST;Vrho0;VFB;VFF;R2A5F_;Fa;S1eS59VFF;S28R3S34A2Z518A3S59VFF;S28R3S35A2Z30A3A2A2F_;F_;Frho;").
Proof. intros rho Hav HP. unfold tL, tB. fold vL vB. exact (P0b_now CST FB FF rho0 P0f HP0b rho (agree_NF rho Hav) HP). Qed.

Lemma in_callersH_ok : ltac2:(tb__ "0|0|
S1SdS11S13S0S0A2A1S11S13S13S0SdA2S0A2A1S2bVNPc;Vrho0;R4A3VP0f;Vrho0;A1S2eR6R5A2S51VCST;Vrho0;S44VFB;R7R5A3S52VFF;R7R4A3R6A5F_;F_;F_;Ffrs;Fkept;Fa;Frho;").
Proof.
  intros rho a kept frs Hav HP0 H. destruct (P0b_nowH rho Hav HP0) as (HT & Hb & Hal).
  destruct H as [H|[H|H]].
  - destruct Hb as (f & sz & fl & Hin & H1 & H2). right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - destruct Hal as (f & sz & fl & Hin & H1 & H2). right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - apply pclMA_mono. apply HT. exact H.
Qed.
Lemma extraOH_client : ltac2:(tb__ "0|1|
S1S4SdS11S13S0S0A2A1S11S13S13S0SdA2S0A2A1S3bVDW;R5A2S2bVNPc;Vrho0;R6A3VP0f;Vrho0;A1S1dS12S2cR7A1S14A3S1eS22S19SdSdSaR9R8A2M0A3R7A2S23R7S1aSdSdG0A3A2A2S51VCST;Vrho0;S44VFB;RaR7A3S52VFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;").
Proof.
  intros rho o a kept frs BZ Hav HP0 HE Hr. apply (in_callersH_ok rho a kept frs Hav HP0). exact (extraOH_sound DW rho o a BZ HE Hr).
Qed.

Lemma sitePH : ltac2:(tb__ "0|0|
S36S1S11S5A1S11S13S0S0A2A1S11S13S13S0SdA2S0A2A1S1bS17A1S11S4A1S1S11S3dQ40A1A1S39VAInv;RaR3R2R1A4S3eS5S6RaA1R9A3S1dS12S3aVDW;RaA2S14A3S2bVNPc;Vrho0;RcA3VP0f;Vrho0;A1S46Vrho0;RfA2S41RfS38S37R10A1A1A2S49VFB;R11A2S4aVFF;R12A2S48VFB;R13R12R10A4S42R13R11A2S43R14R12A2S47VFF;R16R15R12A4S1dS12S5cR15R14R13R12S2cR11A6S14A3S65VCST;R18S16SdA1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  eapply (robjsP_okA segs AInv CST ALA rho0 FB FF Ai rho facts tv fr skip extraOH R rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraOH_client rho o a _ _ (basez_of DW rho facts HDW HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteFH : ltac2:(tb__ "0|0|
S36S1S11S5A1S11S13S0S0A2A1S11S13S13S0SdA2S0A2A1S11S4A1S1S11S3dQ40A1A1S39VAInv;R9R3R2R1A4S3eS5S6R9A1R8A3S1dS12S3aVDW;R9A2S14A3S2bVNPc;Vrho0;RbA3VP0f;Vrho0;A1S46Vrho0;ReA2S41ReS38S37RfA1A1A2S48VFB;R10RfRdA4S42R10ReA2S43R11RfA2S47VFF;R13R12RfA4S1dS12S5aR12R11R10S16S17A1S2cRfA6S14A3S68VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_okF segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraOH R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraOH_client rho o a _ _ (basez_of DW rho facts HDW HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteHH : ltac2:(tb__ "0|1|
S36S1S11S5A1S11S13S0S0A2A1S11S13S13S0SdA2S0A2A1S11S4A1S1S11S3dQ40A1A1S39VAInv;R9R3R2R1A4S3eS5S6R9A1R8A3S1dS12S3aVDW;R9A2S14A3S2bVNPc;Vrho0;RbA3VP0f;Vrho0;A1S46Vrho0;ReA2S41ReS38S37RfA1A1A2S48VFB;R10RfRdA4S42R10ReA2S43R11RfA2S47VFF;R13R12RfA4S1dS12S5aR12R11R10S16S17A1S2cRfA6S14A3S4SdS6aS4R2R12A3S1eS22S19SdSdSaR17R3A2M0A3R2A2S23R2S1aSdSdG0A3A2A2S1fS51VCST;Vrho0;S44VFB;R18R16A3S52VFF;R18R15A3R3A5S1fS1eS22Z0R3A2S23R3S58A2A2S63R3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_hse segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraOH R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraOH_client rho o a _ _ (basez_of DW rho facts HDW HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteXH : ltac2:(tb__ "0|4|
S36S1S11S5A1S11S13S0S0A2A1M0S11S13S13S0SdA2S0A2M1A1M2S1bS17A1M3S11S4A1G0S1S11S3dQ40A1A1S39VAInv;RbR3R2R1A4S3eS5S6RbA1RaA3S1dS12S3aVDW;RbA2S14A3S2bVNPc;Vrho0;RdA3VP0f;Vrho0;A1S46Vrho0;R10A2S41R10S38S37R11A1A1A2S49VFB;R12A2S4aVFF;R13A2S48VFB;R14R13R11A4S42R14R12A2S43R15R13A2S47VFF;R17R16R13A4S1dS12S5bVXGL;R16R15R14R13R12S2dR11A8S14A3S1eS54VCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S17S45G1R1R16A3Li;R15X1bx2R12A9S1eS67VCST;VXGL;R19S16SdA1R18R12A6S69R18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip objs X rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  assert (HEX : forall r a, In r X -> extraXH r = true -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) ->
            pclMA CST rho0 (FBx FB rho tv) (FFx FF rho (match skip with Some i => remove_nth i fr | None => fr end)) a \/ RtCells.in_rangesZ XGL a).
  { intros r a Hr HE Ha. left. apply (in_callersH_ok rho a _ _ Hav HP0). exact (extraXH_sound DW rho r a (basez_of DW rho facts HDW HF HB) HE Ha). }
  split; [exact (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extraXH X rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hchk HEX)|].
  exact (xrs_checkL_okA segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho facts tv fr skip objs extraXH X rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk HEX).
Qed.
Lemma site_pureH : ltac2:(tb__ "0|2|
S57S60S11S4A1S1S11S13S0S0A2A1S11S13S13S0SdA2S0A2A1S11S29A1S1dS12S3aVDW;SbS55R7A1A1A2S14A3S1dS12S5cSbS55R8A1A1R4R3S16S17A1M0S2cR6A6S14A3S1dS12S5bVXGL;SbS55R9A1M1A1R5R4G0ScG1A1S2dS56R9A1A8S14A3S66VAInv;VCST;VXGL;VNPc;Vrho0;VP0f;VFB;VFF;RaR9R8R7S4cR6R5R4S4bA4S16SdA1S36S5eS20L_;L_;AfF_;F_;F_;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;").
Proof.
  intros E s R rho tv fr bd HB HR HX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  split; [exact (sitePH Ai rho _ tv fr None R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HR)|].
  split; [exact (proj1 (proj2 (siteXH Ai rho _ tv fr None _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HX))) | exact I].
Qed.

Lemma frozen_stableH : ltac2:(tb__ "0|0|
SeSeS50S1S6bVNPc;R3A2S1dS12S4fR4R3A2S14A3S61S5fR6S4eVAInv;VCST;VXGL;VNPc;VKc;Vrho0;VP0f;VFB;VFF;VBX;S4dR4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;").
Proof.
  intros n m nd rho Hm Hb r r' tp tr md md' _ Hme (Ai & kc & HJ). exists Ai, kc.
  eapply (JAi_stable segs AInv CST XGL NPc Kc rho0 P0f FB FF BX PTrue HKc ALA m nd Ai kc rho rho tp tr md md'); [exact Hm | exact Hb | apply agree_below_refl | exact Hme | exact HJ].
Qed.
Lemma payA_sameH : ltac2:(tb__ "0|1|
S11S5A1S11S29A1S1dS12S2aR1A1S14A3S64VNPc;Vrho0;VP0f;R3S3Z0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof.
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.
End Sum.
End Lib_builderH_pf.

(* [comment removed for export] *)
Module Lib_tess_polygon_chk3.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_tess_scale2d.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_polygon_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_tess_polygon_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessPolygonAddr.
Lemma cc_11 : CC 11 Kext = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_12 : CC 12 Ke1 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_13 : CC 13 Ke2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_14 : CC 14 Ke3 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_15 : CC 15 Kproj = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_16 : CC 16 Kbbp = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_17 : CC 17 K708 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_18 : CC 18 K830 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_tess_polygon_chk3.

