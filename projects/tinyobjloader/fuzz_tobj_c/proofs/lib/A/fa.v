(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_032.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_int es Lib_finalize_shape_pf f7.

(* [comment removed for export] *)
Module Lib_load_obj_as.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "true"; "bool"; "nil"; "prod"; "Some"; "app"; "option"; "length"; "list"; "andb"; "negb"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSplit"; "AXMerge"; "AXRebase"; "AXUnbase"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sv"; "SPUle"; "sobj"; "SAlu"; "SVar"; "sprop_eqb"; "ss_facts"; "ss_objs"; "cell"; "sprop_below"; "ss_next"; "mkCell"; "sv_eqb"; "swf"; "DUnknown"; "SPEq"; "SPUlt"; "mkObj"; "mkSS"; "ob_base"; "ob_lo"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "la_state"; "leafA"; "ax_X"; "ax_base"; "axwf"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_as"; "oidx"; "pST"; "T_s1f"; "pSL"; "spA"; "E_s1"; "E_s2"; "E_si"; "s1A"; "K_s"; "R_s1"; "R_s2"; "s_s1"; "s_s2"; "T_s1f0"; "T_s1n0"; "T_s2n0"; "T_s2y0"; "pSI"; "sel_front"; "vSL"; "B_s1f"; "B_s1n"; "B_s2n"; "B_s2y"; "K_sB"; "T_s1n"; "T_s2n"; "T_s2y"; "cutsS"; "exitsS"; "pEr"; "sB_facts"; "xf_si0"; "xfb_s1"; "xfb_s2"; "H_ecertS_ok"; "O_midS"; "keep_ecertS_ok"; "ra_si"; "xf_s1"; "xf_si"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "ndX0"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vLEN"; "NP"; "optL"; "vBUF"; "vDp"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "combine"; "filter"; "find"; "tl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_as.NT"; "Pre_nt"; "P_found"; "P_nf"; "Posts_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_as.SI"; "Pre_si"; "P_none"; "P_num"; "Posts_si"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "spm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efnode"; "V_below"; "ejcertAF"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA"; "pinA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "V_B"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "txt"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop.LOLAddr"; "c_si"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideN"; "hide_set"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_int.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_aus.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Module NT. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_next_token. End NT.
Module SI. Include Lib_scan_int. End SI.
Import NT.NextTokenAddr SI.ScanIntAddr.

Definition oidx (b lo : sv) (T : axst) : nat := ltac2:(tb__ "0|3|
S9S6S1S1cA2M0A1S1Lx;S7aG0G0ScS26S2dSeS1S1cR1A3M1A1Vb;A2S26S2eG1A1Vlo;A2A2Lp;S78S1S1cS8aU0SaS1cS21S36VT;A1A1M2A2A2G2A4A3G0G0S1Lp;R1S1S1cR2Ls;Li;X6x1Lp;U3e7X9x2").
Definition spA : sv := SVar 10.
Definition s1A : sv := SAlu ALU_ADD spA (SLit (-512)).

Definition sel_front (sel : list nat) (n : nat) : axform := ltac2:(tb__ "0|0|
S17S8S1Vsel;S79S1S1SdS76S1S9fR1A1Vsel;A3A1Li;S8aU0Vn;A2A3A3A1").

Definition xf_s1 : list axform := ltac2:(tb__ "0|3|
S0S11S14U3M0A1S0S11S13U6S18N10A1A2S0S11S13U4M1S18N88A1A2S0S11S16G1N90A2S0S11S13U2S18Na8M2A1A2S0S11S16G0G2A2S5S11A1A3A3A3A3A3A3").
Definition E_s1 : axst := Eval vm_compute in optL (apply_axforms E_nt xf_s1).
Definition s_s1 : wsub := ltac2:(tb__ "0|0|
S93PaS36S42A1S36S7cA1A3").
Definition R_s1 : list sobj := Eval vm_compute in optR (entails_frA E_s1 NT.Pre_nt s_s1).
Definition T_s1n0 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_s1)) (import_postA s_s1 NT.Pre_nt NT.P_nf E_s1 R_s1).
Definition T_s1f0 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_s1)) (import_postA s_s1 NT.Pre_nt NT.P_found E_s1 R_s1).

Definition xfb_s1 (T : axst) : list axform := ltac2:(tb__ "0|2|
S0S11S15U3A1S0S11S15U4A1S0S11S13U1M0S18Z8A1A2S5S11A1M1A3A3A3SbS11A1S73S12VT;R1A2A1S35SaS1cS21S36R1A1A1A2S1S8S11R3S0S11S50S0S1S3dS41S18Nb8A1R2A3S0S1S3dS41S18Na8A1R2A3S0S1S3dS41S18N90A1R2A3S0S1S3dS41S18N88A1R2A3S0S1S3dS45S75R2A3S0S1S3dS45S18N10A1R2A3S5S1A1A3A3A3A3A3A3R1A2S0S11S14U0A1S0S11S14G0A1S0S11S14U2A1G1A3A3A3A3A3Tn;TT1;Tpre;").
Definition B_s1n : axst := Eval vm_compute in optL (apply_axforms T_s1n0 (xfb_s1 T_s1n0)).
Definition B_s1f : axst := Eval vm_compute in optL (apply_axforms T_s1f0 (xfb_s1 T_s1f0)).
Definition T_s1n : axst := Eval vm_compute in ax_tidy B_s1n.
Definition T_s1f : axst := Eval vm_compute in ax_tidy B_s1f.
Definition pST : sv := SVar 641. Definition pSL : sv := SVar 642. Definition pSI : sv := SVar 643. Definition vSL : positive := 642%positive.

Lemma as_checks1 : ltac2:(tb__ "0|5|
S10SfS9S35A1M0S12S99S65A2S7S35S42A2A3S10SfS9SbS1cA1M1A1S8eS42S7cS49A3S7G1S47A2A3S10SfS4S8dS42S7cS49S47S89S38S35S37S7fA4A5S3A3S10SfS4S95S72S24S36S42A1M2A1M3A2S3A3S10SfS4S6aG3S6bA2S3A3S10SfS4S77S19S23G3A1S20G2A1M4A3S3A3S10SfS35S85G4S8cS49S7cS7eS42S47A5A2S4cA3S10SfS35S85G4S8cS49S7cS7dS42S47A5A2S4bA3S10SfG0S12S4cS5fS4cA1A2S7S35S53A2A3S10SfS35S8bS53A1S57A3S10SfG0S12S4bS5fS4bA1A2S7S35S52A2A3S10SfS35S8bS52A1S3fA3SfS4S87G3S90A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition K_s (t : Z) : axst := ltac2:(tb__ "0|1|
S85S0S19S1bS1dS70S3eS18Vt;A1M0A3S71A2S5S19A1A3S8fS3fS51G0A3A2").

Definition pEr : sv := SAlu ALU_ADD pLNL pPOS.
Definition sB_facts : list sprop := ltac2:(tb__ "0|2|
S0S19S1bS18Z4A1M0S40A2S0S19S1bS1dS70S3eG0A3M1S5cA2S0S19S1bG1S71A2S0S19S1bS1dS70S3eS40A3S71A2S5S19A1A3A3A3A3").
Definition K_sB : axst := ax_add_facts sB_facts T_s1f.

Lemma as_checks_split : ltac2:(tb__ "0|7|
S10SfS4S9bS68S3L_;S36S3fA1M0A2S3A3S10SfS4S77S67S67S27S36S8fS3fS51S18R1A1M1A3A1M2A1Lt;S0S67Z1M3S0S67Z2S0S67Z3S5S67A1A3A3A3M4A3S3A3S10SfS4S77S19S23S24G0A1A1S5dA3S3A3S10SfS4S77S67S67S77S19S23S24G2A1A1S0S19S1bS1dS70S3eG1A3S71A2S5S19A1A3A3Lt;G4A3S3A3S10SfS4S76S19S1fS1bS18G3A1S40A2A1S20G0A1M5A3S3A3S10SfS4S76S19S1fS29S1dS70S3eS40A3S4fA2A1G5A3S3A3S10SfS4S76S19S1fS1bS4fS5cA2A1G5A3S3A3S10SfS4S76S19S1fS1bS4fS71A2A1G5A3S3A3S10SfS4S76S19S1fS1bS3eS18Z10000000000A1M6A2A1G5A3S3A3SfS4S76S19S1fS1bS40G6A2A1G5A3S3A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma K_s_eq : ltac2:(tb__ "0|2|
S67SfS35S46R1A1S94S8fS3fS51S18R1A1M0A3M1S8S19S0S19S1bS1dS70S3eG0A3S71A2S5S19A1A3S20S36G1A1A1A3A2A3Ft;").
Proof. intros t. reflexivity. Qed.
Lemma K_sB_eq : ltac2:(tb__ "0|0|
SfS35S56S94S3fS8S19S5dS20S36S3fA1A1A3A2A3").
Proof. reflexivity. Qed.

Definition ra_si : Z := 0x8e230.
Definition O_midS : sobj := ltac2:(tb__ "0|1|
S2bS41S18Nb8A1S18Na0A1S0S22S25S18Nb4A1Z4S18Z0A1A3S0S22S25S18Nb0A1Z8M0S91S3eA1A3S0S22S25S18Na8A1G0S40A3S5S22A1A3A3A3S28A5").
Definition E_si : axst := ltac2:(tb__ "0|1|
S36S3fA1S34S3cS2cS9aS9cS32R1A1S0S6S1S1aA2M0S2S1S1aU1S18S64A1A4S0G0S2S1S1aUaS84Zb0A1A4S0G0S2S1S1aUbS1dS70S91S3eA1S40A3A4S0G0S2S1S1aUcS84Zb4A1A4S0G0S2S1S1aUdS1eP284A1A4S0G0S2S1S1aUeS1eP285A1A4S5G0A1A3A3A3A3A3A3A2S30R1A1S2fR1A1S33R1A1S0S1cS62S7bS1cS21R1A1A2A3S0S19S1bS1dS70S3eS40A3S71A2S20R1A1A3P286S31R1A1A9S39S3fA1S3aS3fA1A3TS;").

Definition xf_si0 : list axform := ltac2:(tb__ "0|4|
S0S11S13U2M0S18N10A1A2S0S11S13U0M1S18Na8A1A2S0S11S13G1S18Nb0M2A1A2S0S11S13G1S18Nb4M3A1A2S0S11S16U1G3A2S0S11S16G0G2A2S5S11A1A3A3A3A3A3A3").
Definition xf_si (E : axst) : list axform := ltac2:(tb__ "0|1|
S73S12VE;S5eA2A1S35S8S11S5eS0S11S50S0S1S3dS45S18N10A1R1A3S0S1S3dS84Zb0A1S18Z0A1M0R1A3S0S1S3dS74G0R1A3S0S1S3dS84Zb4A1G0R1A3S5S1A1A3A3A3A3SaS1cS21S36R1A1A1A2A2S5S11A1A3A3TT1;").
Definition E_s2 : axst := Eval vm_compute in optL (apply_axforms E_si (xf_si E_si)).

Definition s_s2 : wsub := ltac2:(tb__ "0|1|
S0S6S68S1aA2M0S2S68S1aPfS74A4S0G0S2S68S1aP10S3eA4S0G0S2S68S1aP11S1dS70S3eS40A3A4S0G0S2S68S1aP13S84Zb8A1A4S93PaS36S43A1S36S80A1A3A3A3A3A3").
Definition R_s2 : list sobj := Eval vm_compute in optR (entails_frA E_s2 SI.Pre_si s_s2).
Definition T_s2n0 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_s2)) (import_postA s_s2 SI.Pre_si SI.P_none E_s2 R_s2).
Definition T_s2y0 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_s2)) (import_postA s_s2 SI.Pre_si SI.P_num E_s2 R_s2).

Definition xfb_s2 (T : axst) : list axform := ltac2:(tb__ "0|3|
S0S11S15U1M0A1S0S11S15U3A1S5S11A1M1A3A3SbS11A1S73S12VT;R1A2A1S35SaS1cS21S36R1A1A1A2S1S8S11R3S0S11S50S0S1S3dS41S18Nb8A1R2A3S0S1S3dS41S18Nb4A1R2A3S0S1S3dS41S18Nb0A1R2A3S0S1S3dS41S18Na8A1R2A3S0S1S3dS45S75R2A3S0S1S3dS45S18N10A1R2A3S5S1A1A3A3A3A3A3A3R1A2S0S11S14U0A1M2S0S11G2S0S11G2S0S11S14G0A1G1A3A3A3A3A3A3Tn;TT1;Tpre;").
Definition B_s2n : axst := Eval vm_compute in optL (apply_axforms T_s2n0 (xfb_s2 T_s2n0)).
Definition B_s2y : axst := Eval vm_compute in optL (apply_axforms T_s2y0 (xfb_s2 T_s2y0)).
Definition T_s2n : axst := Eval vm_compute in ax_tidy B_s2n.
Definition T_s2y : axst := Eval vm_compute in ax_tidy B_s2y.

Lemma as_checks2 : ltac2:(tb__ "0|5|
S10SfS4S27S36S44A1A1S3A3S10SfS4S3bS44A1S3A3S10SfS9S35A1M0S12S44S66S44A1A2S7S35S43A2A3S10SfS9SbS1cA1M1A1S8eS43S80S4aA3S7G1S48A2A3S10SfS4S8dS43S80S4aS48S89S38S35S37S83A4A5S3A3S10SfS4S95S72S24S36S43A1M2A1M3A2S3A3S10SfS4S6aG3S6bA2S3A3S10SfS4S77S19S23G3A1S20G2A1M4A3S3A3S10SfS35S85G4S8cS4aS80S81S43S48A5A2S4dA3S10SfS35S85G4S8cS4aS80S82S43S48A5A2S4eA3S10SfG0S12S4dS60S4dA1A2S7S35S54A2A3S10SfS35S8bS54A1S58A3S10SfG0S12S4eS60S4eA1A2S7S35S55A2A3S10SfS35S8bS55A1S59A3SfS4S87G3S90A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsS : list efnode := ltac2:(tb__ "0|7|
S0S6S6S6S35S69A2M0S1A2M1S6S67S1aA2M2A2M3S2G1G2S2G0S1S2S35S69S57S6bA4U1M4A4S2S67S1aS6cS6dZaS6eA2A4M5A4S0G3S2G1G2S2G0S1S2S35S69S46Z1A1S6bA4G4A4G5A4S0G3S2G1G2S2G0S1S2S35S69S46Z2A1S6bA4G4A4G5A4S0G3S2G1G2S2G0S1S2S35S69S46Z3A1S6bA4G4A4G5A4S0G3S2G1G2S2G0S1S2S35S69S56S6bA4G4A4G5A4S0G3S2G1G2S2G0S1S2S35S69S58S6bA4G4A4S2S67S1aS6cS6dZ5S6eA2A4M6A4S0G3S2G1G2S2G0S1S2S35S69S59S6bA4G4A4G6A4S5G3A1A3A3A3A3A3A3A3").
Definition exitsS : list efnode := ltac2:(tb__ "0|5|
S0S6S6S6S35S69A2M0S1A2M1S6S67S1aA2M2A2M3S2G1G2S2G0S1S2S35S69S44S6bA4U1M4A4S2S67S1aS6cS6dZ7S6eA2A4A4S0G3S2G1G2S2G0S1S2S35S69S92S6fA4G4A4S2S67S1aS6cS6dZ1S6eA2A4A4S5G3A1A3A3").

Definition keep_ecertS_ok : list sprop := ltac2:(tb__ "0|2|
S0S19S2aS1eP1ccA1S1eP1d3A1M0A2S0S19S1bS1eP1eaA1S1eP1e0A1A2S0S19S1bG0S1ePeA1M1A2S0S19S1bG1S18Z4000000A1A2S0S19S1bS1ePdA1S18Z800000000000A1A2S5S19A1A3A3A3A3A3").
Definition H_ecertS_ok : list sprop := ltac2:(tb__ "0|0|
S9eS63S8S86S5aS5bA3A2").
Lemma ecertS_ok : ltac2:(tb__ "0|1|
SfS4S88S96S72S97Uc8S98S72S89S86S86S9dS61A1M0S5aA4S89S86S86G0S5bA4A8S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_as.

(* [comment removed for export] *)
Module Lib_load_obj_as_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "nat"; "list"; "cons"; "bool"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA"; "frozen"; "nd_below"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "holds"; "sprop"; "ss_facts"; "agree_below"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aus_pf"; "pure_ruleL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "ndX0"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp"; "E_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tblB"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "@Corelib.Lists.ListDef"; "Forall"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_as"; "cutsS"; "T_s1f"; "E_s2"; "E_si"; "K_s"; "K_sB"; "T_s2n"; "T_s2y"; "pEr"; "pSI"; "pSL"; "pST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn"; "PhisV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_next_token"; "Posts_nt"; "Pre_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_int"; "Posts_si"; "Pre_si"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "frozen_stableH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_int.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_aus OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_aus_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_as.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S52S13S3S1dQ40A1A1S4fOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S51S8VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S9S4eVCST;R1A2S1eS22Z0R2A2S23R2S4dA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S9S4eVXGL;R1A2S1eS22Z0R2A2S23R2S4dA2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S1S1S9S9A2S9A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let P0 : ltac2:(tb__ "0|0|
S13OFr;") := ltac2:(tb__ "0|0|
S37VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
SdVAInv;VCST;VXGL;S33VKc;Vrho0;VP0;VFB;VFF;VBX;ScVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S32VAInv;VCST;VXGL;S33VKc;Vrho0;VP0;VFB;VFF;VBX;ScVPhi;Vnd;Ad").
Let frozen_stable : ltac2:(tb__ "0|0|
SaSaSbS13S53S33R3A2S1fS5SfR4R3A2S7A3S1cS8R6SeVAInv;VCST;VXGL;S33VKc;Vrho0;VP0;VFB;VFF;VBX;ScR4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
S50VAInv;VCST;VXGL;VALA;S33VKc;VHKc;VFB;VFF;VBX;Vrho0;VP0;Ac").

Lemma s1f_facts : ltac2:(tb__ "0|4|
S13S39S16S15R1A1S17S12S3cA1A1A3S1eS22Z1S38R2S45A2M0A2S1eS1fS9S24S38R2S46A2M1G0A2S38R2S44A2M2A3S1eS22G2S38R2S43A2A2S1eS22G2S38R2S34A2A2S1eS22G1S25Z2Z28A2M3A2S22G0G3A2A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF.
  factz HF (SPUle (SLit 1) pSL) H1. rewrite uval_lit in H1 by lia.
  fact HF (SPEq (SAlu ALU_ADD pST pSL) pSI) H2. cbn [holds] in H2.
  factz HF (SPUle pSI pEr) H3. factz HF (SPUle pSI vLEN) H4.
  factz HF (SPUle pST (SLit 1099511627776)) H5. factz HF (SPUle pSL (SLit 1099511627776)) H6. rewrite uval_lit in H5, H6 by lia.
  assert (E2 : uval r (SAlu ALU_ADD pST pSL) = uval r pSI) by (unfold uval; rewrite H2; reflexivity).
  rewrite uval_add_small in E2 by lia. repeat split; lia.
Qed.

Lemma s_split : ltac2:(tb__ "0|0|
SbS13S3S1dQ40A1A1S29S1aS8VJAv;R4A1S3cR3R2R1A6S21S20S9S9S1eS3aS9R1S4S9Z1S4S9Z2S4S9Z3S6S9A1A3A3A3A3S1aS8VJAv;R6A1S3fR1A1R5R4R3A6A2Lt;A2S1aS8VJAv;R5A1S40R4R3R2A6A2F_;Fw;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp w HS. pose proof (smatchA_facts segs _ _ _ _ (proj1 HS)) as HF.
  destruct (s1f_facts rho HF) as (H1 & H2 & H3 & H4 & H5 & H6). pose proof as_checks_split as (Cva & Cwf & CfB & Cft & _).
  pose proof (uval_range rho pEr) as RE. pose proof (uval_range rho vLEN) as RL'.
  destruct (Z_le_dec (uval rho pSL) 3) as [LE|GT].
  - left. set (t := uval rho pSL).
    assert (Ht : In t [1; 2; 3]) by (cbn; lia).
    exists t. split; [exact Ht|]. rewrite K_s_eq.
    assert (Hpin : SPA segs (JAv nd) (pinA T_s1f vSL (SLit t)) rho tp w).
    { apply (SPA_pin segs _ rho tp T_s1f vSL _ w); [| exact Cva | | exact HS].
      - exact (proj1 (forallb_forall _ _) Cwf t Ht).
      - apply bv_eq. change (uval rho pSL = uval rho (SLit t)). rewrite uval_lit by lia. reflexivity. }
    apply (SPA_refacts_JA segs _ rho _ _ tp w Hpin).
    + rewrite forallb_app, (proj1 (forallb_forall _ _) Cft t Ht). exact (swf_facts _ (proj1 (forallb_forall _ _) Cwf t Ht)).
    + intros tr md _ HFp. apply Forall_app. split; [|exact HFp]. constructor; [|constructor]. apply (proj2 (h_ule _ _ _)).
      rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
  - right. rewrite K_sB_eq. apply (SPA_refacts_JA segs _ rho _ (sB_facts ++ ss_facts (ax_S T_s1f)) tp w HS).
    + rewrite forallb_app, CfB. cbn [andb]. pose proof as_checks1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT & _). rewrite <- CT at 1.
      OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros tr md _ HFp. apply Forall_app. split; [|exact HFp]. unfold sB_facts.
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; apply (proj2 (h_ule _ _ _)).
      * rewrite uval_lit by lia. lia.
      * rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
      * rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
      * rewrite uval_add_small by lia. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S9S3S1dQ40A1A1S26F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S1bS11S13S3S1dQ40A1A1S26S39S16S15R3A1S17S12R4A1A1A3VTR;S1aS8R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S26S26S26S29R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_JAF : ltac2:(tb__ "0|0|
S13OF_;SbS11S13S3S1dQ40A1A1S26R6R3A1VTR;S1aS8VJAv;R6A1R5R4R3A5R2A2F_;VTR;S1aS8VJAFv;R7R6A2R5R4R3A5R2A2F_;FQ;Ftp;Frho;FA;Fnd;FPhi;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S26OS26S29R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis PURE_nt : ltac2:(tb__ "0|0|
S2aVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;VTR;S4aS49Ab").
Hypothesis PURE_si : ltac2:(tb__ "0|0|
S2aVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;VTR;S4cS4bAb").
Hypothesis CUTV : ltac2:(tb__ "0|5|
S11SbS2S1S9S14A2M0S13S3S1dQ40A1A1M1S9G1S3aS1S1S1S11SbA2M2S2A2M3G0A2S0G3G0S0G2S2S0S11SbR8R7A4R6A4R5A4S3bA3S31S47R7R5A3S1eS22Z0S30S0G3G0S0G2S2S0S11SbRaR9A4R8A4R7A4R6A2M4A2S23G4R4A2A2VTR;S1aS8VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").

Lemma site_si : ltac2:(tb__ "0|4|
S13S3S1dQ40A1A1S26S13S39S16S15R4A1S17S12S3dA1M0A1M1A3S18S19G0A1M2R5R2A3VTR;S1aS8VJAv;S2bA1M3S41R3R5A5R4A2F_;F_;Frho';S13S39S16S15R5A1G1A3S18G2R6R2A3VTR;S1aS8G3S42R3R6A5R5A2F_;F_;Frho';VTR;S1aS8G3S3eR5R4A5R3A2F_;F_;FQ;Ftp;Frho;").
Proof.
  intros rho tp Q HKn HKy. pose proof as_checks2 as (_ & _ & Cxf & Cent & Cchk & Cnp & Cnb & Cfb & CTn0 & CTy0 & CBn & CTn & CBy & CTy & _).
  apply (TR_pre (SPA segs (JAv ndA1) E_s2 rho tp)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) (xf_si E_si) rho E_si E_s2 tp w Cxf Hw). }
  apply TR_facts. intros HF.
  apply (PURE_si E_s2 s_s2 R_s2 rho tp ndA1 _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag. cbn [In Lib_scan_int.Posts_si] in HL. destruct HL as [<-|[<-|[]]]; cbn [la_state].
  - rewrite CTn0. apply (TR_pre (SPA segs (JAv ndA1) T_s2n rho' tp)).
    { intros w Hw. rewrite <- CTn. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_s2 T_s2n0) rho' T_s2n0 B_s2n tp w CBn Hw). }
    exact (HKn rho' HF Hag).
  - rewrite CTy0. apply (TR_pre (SPA segs (JAv ndA1) T_s2y rho' tp)).
    { intros w Hw. rewrite <- CTy. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_s2 T_s2y0) rho' T_s2y0 B_s2y tp w CBy Hw). }
    exact (HKy rho' HF Hag).
Qed.

Theorem arm_s : ltac2:(tb__ "0|2|
S13S3S1dQ40A1A1M0G0VTR;S1aS8VJAFv;S36S2bA2S35R3R2A5VFAM;S30S0S1S1S11SbA2M1S2A2S1S9S14A2S0G1S2S0S11SbS35S2bA4U1A4S0S9S14S2cS2dZ11S2fA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_JAF. intros HPHI.
  pose proof as_checks1 as (Cxf & Cent & Cchk & Cnp & Cnb & Cfb & CTn0 & CTf0 & CBn & CTn & CBf & CTf & CVB).
  apply (TR_pre (SPA segs (JAv ndA1) E_s1 rho tp)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) xf_s1 rho E_nt E_s1 tp w Cxf Hw). }
  apply TR_facts. intros HF.
  fact HF (SPUlt pI xLC) HiC. rewrite h_ult in HiC. fact HF (SPUle xLC vLEN) HcL. rewrite h_ule in HcL.
  fact HF (SPUle vLEN (SLit 67108864)) HL26. rewrite h_ule, uval_lit in HL26 by lia.
  apply (PURE_nt E_s1 s_s1 R_s1 rho tp ndA1 _ Cent Cchk Cnp Cnb Cfb).
  intros L rho' HL Hag.
  assert (HPHI' : tblB rho') by exact (phi_agree V_B tblB tblB_reads _ rho rho' CVB Hag HPHI).
  assert (HM : forall T' nd' k', 0 <= efmeasA (T', nd', k', (RL, VLA 10 z0)) rho' < efmeasA (E_nt, ndA1, 1%nat, (RL, VLA 17 z0)) rho).
  { intros T' nd' k'. apply (VLA_lt rho rho' 17 10 z0 E_nt T' ndA1 nd' 1%nat k');
      [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia]. }
  cbn [In OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_next_token.Posts_nt] in HL. destruct HL as [<-|[<-|[]]]; cbn [la_state].
  -
    rewrite CTn0. apply (TR_pre (SPA segs (JAv ndA1) T_s1n rho' tp)).
    { intros w Hw. rewrite <- CTn. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_s1 T_s1n0) rho' T_s1n0 B_s1n tp w CBn Hw). }
    apply (CUTV T_s1n ndA1 1%nat (RL, VLA 10 z0) rho' tp); [left; reflexivity | exact HPHI' | exact (HM T_s1n ndA1 1%nat)].
  -
    rewrite CTf0. apply (TR_pre (SPA segs (JAv ndA1) T_s1f rho' tp)).
    { intros w Hw. rewrite <- CTf. apply SPA_tidy. exact (SPA_axforms segs (JAv ndA1) (xfb_s1 T_s1f0) rho' T_s1f0 B_s1f tp w CBf Hw). }
    apply (TR_pre (fun w => exists c : option Z,
              (fun c w => match c with Some t => In t [1; 2; 3] /\ SPA segs (JAv ndA1) (K_s t) rho' tp w | None => SPA segs (JAv ndA1) K_sB rho' tp w end) c w)).
    { intros w Hw. destruct (s_split ndA1 rho' tp w Hw) as [(t & Ht & Hw')|Hw']; [exists (Some t); split; [exact Ht | exact Hw'] | exists None; exact Hw']. }
    apply TR_exw. intros [t|]; lazy beta iota.
    + apply (TR_pureP _ (In t [1; 2; 3])); [intros w [Ht _]; exact Ht|]. intros Ht.
      apply (TR_pre (SPA segs (JAv ndA1) (K_s t) rho' tp)); [intros w [_ Hw]; exact Hw|].
      apply (CUTV (K_s t) ndA1 1%nat (RL, VLA 10 z0) rho' tp); [| exact HPHI' | exact (HM (K_s t) ndA1 1%nat)].
      cbn [In] in Ht. destruct Ht as [<-|[<-|[<-|[]]]]; [right; left; reflexivity | do 2 right; left; reflexivity | do 3 right; left; reflexivity].
    + apply (CUTV K_sB ndA1 1%nat (RL, VLA 10 z0) rho' tp); [do 4 right; left; reflexivity | exact HPHI' | exact (HM K_sB ndA1 1%nat)].
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S10S8VKc;Vok;A3").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
S13S3S1dQ40A1A1M0G0S28S8Vok;S1aS8VJAFv;S36S2eA2S48R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma PURE_nt_T : ltac2:(tb__ "0|0|
S2aVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S28S8Vok;A2S4aS49Ab").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_next_token.Pre_nt s R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_next_token.Posts_nt rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_next_token.next_token_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.
Lemma PURE_si_T : ltac2:(tb__ "0|0|
S2aVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S28S8Vok;A2S4cS4bAb").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl Lib_scan_int.Pre_si s R Lib_scan_int.Posts_si rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply Lib_scan_int.scan_int_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.

Lemma CUTV_T : ltac2:(tb__ "0|5|
S11SbS2S1S9S14A2M0S13S3S1dQ40A1A1M1S9G1S3aS1S1S1S11SbA2M2S2A2M3G0A2S0G3G0S0G2S2S0S11SbR8R7A4R6A4R5A4S3bA3S31S47R7R5A3S1eS22Z0S30S0G3G0S0G2S2S0S11SbRaR9A4R8A4R7A4R6A2M4A2S23G4R4A2A2S28S8Vok;S1aS8VJAv;RaA1RbR7R6A5VFAMQ;R4A1A4F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi _.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads H_ecertS_ok 200%nat cps_arm NP cutsS exitsS ok (FAMQ tp0') Hok
           ecertS_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsS In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    pose proof as_checks2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CVB).
    apply (site_si (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) PURE_si_T rho1 tp1); intros rho' HF Hag.
    + apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV ok (map efdrop cutsS) T_s2n ndA1 1%nat (FAMQ tp0') rho' tp1); [do 5 right; left; reflexivity |].
      exact (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1).
    + apply (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV ok (map efdrop cutsS) T_s2y ndA1 1%nat (FAMQ tp0') rho' tp1); [do 6 right; left; reflexivity |].
      exact (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1).
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
Qed.

Theorem arm_s_T : ltac2:(tb__ "0|1|
S13S3S1dQ40A1A1M0G0S28S8Vok;S1aS8VJAFv;S36S2bA2S35R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_s (triple segs ok) (fun _ tp0 => FAMQ tp0) (TRs_facts segs ok) (TRs_pre segs ok)
           (fun Phi nd A rho tp Q H => triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi ok nd A rho tp Q H)
           (@triple_ex segs ok) (TRs_pureP segs ok) PURE_nt_T CUTV_T rho tp tp0).
Qed.
End Safety.

Section Existence.
Variable FAM : ltac2:(tb__ "0|0|
S9S3S1dQ40A1A1S26F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S9S9S3S1dQ40A1A1S29S22R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
S13S3S1dQ40A1A1M0G0S27S8S1aS8VJAFv;S36S2eA2S48R3R2A5VFAM;S30S0S1S1S11SbA2M1S2A2S1S9S14A2S0G1S2S0S11SbS48S2eA4U1A4S0S9S14S2cS2dZ1S2fA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma PURE_nt_E : ltac2:(tb__ "0|0|
S2aVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S27S8A1S4aS49Ab").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_next_token.Pre_nt s R OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_next_token.Posts_nt rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_next_token.next_token_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.
Lemma PURE_si_E : ltac2:(tb__ "0|0|
S2aVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S27S8A1S4cS4bAb").
Proof.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl Lib_scan_int.Pre_si s R Lib_scan_int.Posts_si rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply Lib_scan_int.scan_int_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.

Lemma CUTV_E : ltac2:(tb__ "0|5|
S11SbS2S1S9S14A2M0S13S3S1dQ40A1A1M1S9G1S3aS1S1S1S11SbA2M2S2A2M3G0A2S0G3G0S0G2S2S0S11SbR8R7A4R6A4R5A4S3bA3S31S47R7R5A3S1eS22Z0S30S0G3G0S0G2S2S0S11SbRaR9A4R8A4R7A4R6A2M4A2S23G4R4A2A2S27S8S1aS8VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisV PhisV_reads H_ecertS_ok 200%nat cps_arm NP cutsS exitsS (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertS_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX. cbn [exitsS In] in HinX. destruct HinX as [E|[E|[]]]; injection E as <- <- <- <-.
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisV 1)). intros HP1.
    pose proof as_checks2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CVB).
    apply (site_si (etriple segs) (TRe_facts segs) (TRe_pre segs) PURE_si_E rho1 tp1); intros rho' HF Hag;
      (fact HF (SPUlt pI xLC) HiC; rewrite h_ult in HiC; fact HF (SPUle xLC vLEN) HcL; rewrite h_ule in HcL;
       fact HF (SPUle vLEN (SLit 67108864)) HL26; rewrite h_ule, uval_lit in HL26 by lia).
    + eapply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV cutsS T_s2n ndA1 1%nat (RL, VLA 5 z0));
        [do 5 right; left; reflexivity | exact (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1) |].
      apply (VLA_lt rho1 rho' 7 5 z0 E_si T_s2n ndA1 ndA1 1%nat 1%nat);
        [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
    + eapply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisV cutsS T_s2y ndA1 1%nat (RL, VLA 5 z0));
        [do 6 right; left; reflexivity | exact (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1) |].
      apply (VLA_lt rho1 rho' 7 5 z0 E_si T_s2y ndA1 ndA1 1%nat 1%nat);
        [symmetry; apply (proj1 Hag); reflexivity | symmetry; apply (proj1 Hag); reflexivity | exact HiC | lia | unfold z0; rewrite uval_lit by lia; lia | lia | lia].
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH rho1 tp1 tp0')].
Qed.

Theorem arm_s_E : ltac2:(tb__ "0|2|
S13S3S1dQ40A1A1M0G0S27S8S1aS8VJAFv;S36S2bA2S35R3R2A5VFAM;S30S0S1S1S11SbA2M1S2A2S1S9S14A2S0G1S2S0S11SbS35S2bA4U1A4S0S9S14S2cS2dZ11S2fA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  exact (arm_s (etriple segs) FAM (TRe_facts segs) (TRe_pre segs)
           (fun Phi nd A rho tp Q H => etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue Phi nd A rho tp Q H)
           (@etriple_ex segs) (TRe_pureP segs) PURE_nt_E CUTV_E rho tp tp0).
Qed.
End Existence.
End Sum.

End Lib_load_obj_as_pf.

(* [comment removed for export] *)
Module Lib_load_obj_epiS1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "app"; "nil"; "prod"; "pair"; "Some"; "fst"; "list"; "option"; "nat"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "bd_below"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "axwf"; "entailsA"; "la_reason"; "la_state"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1"; "s_fs2"; "E_fs2"; "R_fs2"; "EK"; "EV"; "K_succ"; "Xk_fs2"; "brest_fs2"; "cE"; "kE"; "s_kn"; "s_nn"; "bdrest_fs2"; "E_fs21"; "L_sk"; "L_sn"; "T_fz2"; "T_fz20"; "T_nop2"; "T_nop20"; "T_ok2"; "T_ok20"; "bd_s0"; "bd_succ"; "cps_s"; "kept_fs2"; "tv_fs2"; "xfb_fs2"; "B_fz2"; "B_nop2"; "B_ok2"; "PDk_fs2"; "T_f20"; "bd_nop2"; "bd_ok2"; "hand_fs2"; "payX_fs2"; "payY_fs2"; "qHk2"; "qHn2"; "tvL_k"; "tv_nop2"; "tv_ok2"; "Es_fs0"; "FINi2"; "VPsh2"; "bd_fz2"; "f_absurd"; "nd_fz2"; "nd_nop2"; "nd_ok2"; "nnPhi"; "passed_fs2"; "pc_succ"; "qHz2"; "tv_fz2"; "xf_fs2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1.FS"; "Pre_fs"; "nd_fail_f"; "nd_nop"; "nd_ok"; "NP"; "P_failz"; "P_nop"; "P_ok"; "nd0"; "P_fail"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "AHead"; "NDA"; "am_subst"; "ndesc"; "nd_am"; "nd_tv"; "am_eqb"; "nd_bd"; "nd_below"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "ss_facts"; "sv"; "SAlu"; "SMd"; "ss_next"; "ss_pc"; "valuation"; "SPBranch"; "SPNot"; "SPUle"; "sobj"; "sprop_below"; "sprop_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vDp"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "t_c"; "t_k"; "v_sh"; "vsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "tv_permb"; "bd_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "bd_rest"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_le2"; "bud_pay2"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@Corelib.Init.Nat"; "sub";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "cps_epi"; "pc_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_epiS1.FS.FSAddr"; "fs_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits"; "K_after0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_finalize_shape Lib_finalize_shape_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
Module FS. Include Lib_finalize_shape. End FS.  Module FSP. Include Lib_finalize_shape_pf. End FSP.

Definition EV (c : Z) : bitem := BIc 1 0 c.
Definition EK (k : Z) : bitem := BIc 0 1 k.
Definition cE : Z := 600000.
Definition kE : Z := 64 * KU.
Definition bd_s0 : list bitem := ltac2:(tb__ "0|0|
S4SfS1fS23A1S4SfS1eS24A1S9eA3A3").
Definition nd_s0 : ndesc := ltac2:(tb__ "0|0|
S61S5fS5eS31S60S88S2A2A4").
Definition pc_succ : Z := 0x8e98c.
Definition cps_s : list Z := pc_succ :: cps_epi.

Definition Es_fs0 : axst := Eval vm_compute in leafL (runL 300 cps_epi K_after0) FS.FSAddr.fs_entry 0.
Definition xf_fs2 : list axform := ltac2:(tb__ "0|2|
S4S7dS82U7M0S6cNd0M1A1A2S4S7dS7fG0G1A2S6S7dA1A3A3").
Definition E_fs21 : axst := Eval vm_compute in optL (apply_axforms Es_fs0 xf_fs2).
Definition nnPhi : sprop := ltac2:(tb__ "0|2|
S77S71S9bS6cZ4A1S9dZ80M0S8aS8bS8cA1M1A1A2A3S70S9aS71S9bS6cZ6A1S9dG0S89G1A1A2A3S6cZ1000A1A3A2").
Definition E_fs2 : axst := Eval vm_compute in ax_add_facts [nnPhi] E_fs21.
Definition s_fs2 : wsub := ltac2:(tb__ "0|0|
S4S7S6bS6fA2S8S6bS6fP13S70S9aS84S6cZd0A1A3A4S94PaS14S1cA1S14S54A1A3A3").
Definition R_fs2 : list sobj := Eval vm_compute in optR (entails_frA E_fs2 FS.Pre_fs s_fs2).
Definition PDk_fs2 : list pdescK := liftPD FSP.PD_fs.
Definition passed_fs2 : list (sv * sv) := Eval vm_compute in import_tv s_fs2 (nd_tv FS.nd0).
Definition kept_fs2 : list (sv * sv) := Eval vm_compute in List.filter (fun t => negb (existsb (fun p => sv_eqb (fst p) (fst t)) passed_fs2)) tvL.
Definition tv_fs2 : list (sv * sv) := kept_fs2 ++ passed_fs2.
Definition hand_fs2 : list bitem := Eval vm_compute in bd_subst s_fs2 (nd_bd FS.nd0).
Definition VPsh2 : list bitem := Eval vm_compute in firstn 2 (skipn 12 bd_rest).
Definition FINi2 : list bitem := Eval vm_compute in firstn 2 (skipn 36 bd_rest).
Definition bdrest_fs2 : list bitem := Eval vm_compute in (firstn 12 bd_rest ++ firstn 22 (skipn 14 bd_rest) ++ skipn 38 bd_rest).
Definition brest_fs2 : list bitem := ltac2:(tb__ "0|0|
S4SfS1fS69S23Z362A2A1S4SfS1eS69S24Z44A2A1S27A3A3").
Definition payX_fs2 : list bitem := ltac2:(tb__ "0|0|
S5SfS47S5SfS48S4SfS1fS23A1S4SfS1eS24A1S6SfA1A3A3A3A3").
Definition payY_fs2 : list bitem := ltac2:(tb__ "0|0|
S5SfS3eS4SfS1fS69S23Z362A2A1S4SfS1eS69S24Z44A2A1S6SfA1A3A3A3").
Definition Xk_fs2 : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (existsb (fun t => sv_eqb (fst r) (fst t)) passed_fs2)) (ax_X E_fs2).

Lemma epiS1_checks_fs : ltac2:(tb__ "0|c|
S1S0SbS7S6aS7bA2M0A1S85S15G0S15S8S6aS7bS73S14S19R1A1A1A1S18R1A1A4LL;S87U12cSa5Sa9A3A4S4G0S8S6aS7bSa8S7cA4S6G0A1A3A3S1S0ScS13A1S7eS46S53A2S9S13S28A2A3S1S0S13SabS28S5S6dS4S6dS4eS6S6dA1A3S6eS14S28A1M1A1A3M2A2S1cA3S1S0S3Sa2S6dS79S72G1A1A1G2A3S2A3S1S0ScSbS78A1M3A1S97S1cS54S1bA3S9G3S1dA2A3S1S0S3S96S1cS54S1bS1dS85S7S7S13S63A2M4S74S74OF_;F_;M5A2M6S13G6SaS13S63SaG4G5R1A3A3Ld;S3aA4A5S2A3S1S0S3SacS83S1bA2S2A3S1S0S3SaaS1bS58A2S2A3S1S0S3S99S1bS4fS65S5cA1A3S2A3S1S0S3S66S62S1bS64S5cA1A2S60S88S2A2M7A2S2A3S1S0S3Sa2S7S8eG5A2M8G8S8fS54S58S1bS72S14S1cA1M9A1MaSaS8eG5R1A3A5Ld;S3aA3S2A3S1S0S3S91S5fS35A2S2A3S1S0S3S91S35S5fA2S2A3S1S0S3S90S21S1aS1cA1A2S2A3S1S0S3S92S31S5SfS27S3fA3A2S2A3S1S0S3S92S5SfS27S40A3S5SfS3eS22A3A2S2A3S1S0S3S12S27A1S2A3S1S0S3Sa1S6eG9A1S6cZ0MbA1GbS3fS40A5S2A3S1S0S3S68GaS61S35S5eS31G7A4A2S2A3S1S0S3S11GaS22A2S2A3S0S3SadS83GaA2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition xfb_fs2 (T : axst) : list axform := ltac2:(tb__ "0|3|
S4S7dS7fU1M0Zd0A2S4S7dS81S4SdG0S4SdU0M1S86U2M2Sa4Sa7VT;A1G2A2A2A3A3A1S4S7dS80G1A1S6S7dA1A3A3A3").
Definition T_nop20 : axst := Eval vm_compute in T_afterA3 FS.Pre_fs E_fs2 s_fs2 R_fs2 FS.P_nop Xk_fs2.
Definition T_ok20 : axst := Eval vm_compute in T_afterA3 FS.Pre_fs E_fs2 s_fs2 R_fs2 FS.P_ok Xk_fs2.
Definition T_f20 : axst := Eval vm_compute in T_afterA3 FS.Pre_fs E_fs2 s_fs2 R_fs2 FS.P_fail Xk_fs2.
Definition T_fz20 : axst := Eval vm_compute in T_afterA3 FS.Pre_fs E_fs2 s_fs2 R_fs2 FS.P_failz Xk_fs2.
Definition B_nop2 : axst := Eval vm_compute in optL (apply_axforms T_nop20 (xfb_fs2 T_nop20)).
Definition B_ok2 : axst := Eval vm_compute in optL (apply_axforms T_ok20 (xfb_fs2 T_ok20)).
Definition B_fz2 : axst := Eval vm_compute in optL (apply_axforms T_fz20 (xfb_fs2 T_fz20)).
Definition T_nop2 : axst := Eval vm_compute in ax_tidy B_nop2.
Definition T_ok2 : axst := Eval vm_compute in ax_tidy B_ok2.
Definition T_fz2 : axst := Eval vm_compute in ax_tidy B_fz2.
Definition isub_nop2 : wsub := Eval vm_compute in import_subA s_fs2 FS.Pre_fs FS.P_nop E_fs2.
Definition isub_ok2 : wsub := Eval vm_compute in import_subA s_fs2 FS.Pre_fs FS.P_ok E_fs2.
Definition isub_fz2 : wsub := Eval vm_compute in import_subA s_fs2 FS.Pre_fs FS.P_failz E_fs2.
Definition qHn2 : sv := Eval vm_compute in sv_subst isub_nop2 FS.vHD.
Definition qHk2 : sv := Eval vm_compute in sv_subst isub_ok2 FS.qHD.
Definition qHz2 : sv := Eval vm_compute in sv_subst isub_fz2 FS.qHD.
Definition tv_nop2 : list (sv * sv) := Eval vm_compute in (kept_fs2 ++ import_tv isub_nop2 (nd_tv FS.nd_nop)).
Definition bd_nop2 : list bitem := Eval vm_compute in (bd_subst isub_nop2 (nd_bd FS.nd_nop) ++ brest_fs2).
Definition tv_ok2 : list (sv * sv) := Eval vm_compute in (kept_fs2 ++ import_tv isub_ok2 (nd_tv FS.nd_ok)).
Definition bd_ok2 : list bitem := Eval vm_compute in (bd_subst isub_ok2 (nd_bd FS.nd_ok) ++ brest_fs2).
Definition tv_fz2 : list (sv * sv) := Eval vm_compute in (kept_fs2 ++ import_tv isub_fz2 (nd_tv FS.nd_fail_f)).
Definition bd_fz2 : list bitem := Eval vm_compute in (bd_subst isub_fz2 (nd_bd FS.nd_fail_f) ++ brest_fs2).
Definition nd_nop2 : ndesc := ltac2:(tb__ "0|0|
S61S44S5eS3cS60S42S2A2A4").
Definition nd_ok2 : ndesc := ltac2:(tb__ "0|0|
S61S45S5eS3dS60S41S2A2A4").
Definition nd_fz2 : ndesc := ltac2:(tb__ "0|0|
S61S52S5eS49S60S51SeA2A4").
Definition f_absurd : sprop := ltac2:(tb__ "0|1|
S76S75S9cS6cZ0A1M0G0A3A1").

Lemma epiS1_checks_nd : ltac2:(tb__ "0|5|
S1S0S63S61S5S7S6fS6fA2M0S34S98S95S1bS54S5aS1cA4M1S65S56A1A2A3S5eS5SfS10G1S67S56A1A2S22A3S62G1S64S56A1A2A4S4cA3S1S0S63S61S5G0S34S98S95S1bS54S5bS1cA4M2S65S57A1A2A3S5eS5SfS10G2S67S57A1A2S22A3S62G2S64S57A1A2A4S4dA3S1S0S63S61S5G0S34S98S95S1bS54S59S1cA4M3S65S55A1A2A3S5eS5SfS10G3S67S55A1A2S22A3S62G3S64S55A1A2A4S4bA3S1S0S13S8dS54S1cS1bS1dS5aS21A6S2eA3S1S0S13S8dS54S1cS1bS1dS5bS21A6S30A3S1S0S13S8dS54S1cS1bS1dS5dS21A6S3bA3S1S0S13S8dS54S1cS1bS1dS59S21A6S2cA3S1S0ScS13A1M4S7eS2eS36S2eA1A2S9S13S38A2A3S1S0G4S7eS30S36S30A1A2S9S13S39A2A3S1S0G4S7eS2cS36S2cA1A2S9S13S37A2A3S1S0S13S93S38A1S2dA3S1S0S13S93S39A1S2fA3S1S0S13S93S37A1S2bA3S1S0S3S16S2dA1S2A3S1S0S3S16S2fA1S2A3S1S0S3S16S2bA1S2A3S0S3Sa3S6dS7aS4aA1S6eS14S3bA1A1A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition L_sn : axst := Eval vm_compute in leafL (runL 300 cps_s T_nop2) pc_succ 0.
Definition L_sk : axst := Eval vm_compute in leafL (runL 300 cps_s T_ok2) pc_succ 0.
Definition L_dz : axst := Eval vm_compute in leafL (runL 300 cps_s T_fz2) pc_disp 0.
Definition K_succ : axst := Eval vm_compute in ax_with_facts L_sn (List.filter (fun f => negb (sprop_eqb f nnPhi)) (ss_facts (ax_S L_sn))).
Definition s_kn : wsub := ltac2:(tb__ "0|0|
S94S83S14S29A1S14S20A1A3").
Definition s_nn : wsub := ltac2:(tb__ "0|0|
S94S83S14S2aA1S14S20A1A3").
Definition bd_succ : list bitem := ltac2:(tb__ "0|0|
S4SfS1fS69S69S23Z362A2Z100A2A1S4SfS1eS69S69S24Z44A2Z200A2A1S9eA3A3").
Definition nd_succ : ndesc := ltac2:(tb__ "0|0|
S61S5fS5eS32S60S88S2A2A4").
Definition tvL_k : list (sv * sv) := Eval vm_compute in map (fun t => (sv_subst s_kn (fst t), sv_subst s_kn (snd t))) tvL.

Lemma epiS1_checks_succ : ltac2:(tb__ "0|7|
S1S0SbS7S6aS7bA2M0A1M1S85S15G0S15S8S6aS7bS73S14S19R1A1A1A1S18R1A1A4LL;M2S87U12cM3S33S2dA3A4S4G0S8S6aS7bS50S7cA4S6G0A1M4A3M5A3S1S0G1S85S15G0G2S87G3S33S2fA3A4G5A3S1S0G1S85S15G0G2S87G3S33S2bA3A4S4G0S8S6aS7bSa6S7cA4G4A3A3S1S0S3S16S20A1S2A3S1S0S3S17S2aS20S26A3S2A3S1S0S3S9fS26S83A2S2A3S1S0S3S17S29S20S25A3S2A3S1S0S3S9fS25S83A2S2A3S1S0S3S91S44S5fA2S2A3S1S0S3S91S45S43A2S2A3S1S0S3S99S25S43S5fA3S2A3S1S0S3S99S26S5fS5fA3S2A3S1S0S3Sa0S6eS14S2aA1A1S10S26S32A2S3cA3S2A3S1S0S3Sa0S6eS14S29A1A1S10S25S32A2S3dA3S2A3S1S0S3S66S62S25S60S88S2A2M6A2S60S41S2A2A2S2A3S0S3S66S62S26G6A2S60S42S2A2A2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiS1.

(* [comment removed for export] *)
Module Lib_load_obj_hv_pf3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "valuation"; "ss_facts"; "SPUle"; "SLit"; "sprop_eqb"; "holds"; "rw"; "sobj"; "SAlu"; "SVar"; "ss_next"; "DUnknown"; "SPEq"; "eval"; "ob_base"; "obj_hi_of"; "obj_lo_of"; "soff"; "ss_objs"; "ob_cells"; "swf"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "prod"; "pair"; "cons"; "andb"; "nil"; "Some"; "app"; "option"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "g8"; "has_facts"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tblB"; "V_B"; "P0_lo"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv_pf3"; "mc_src"; "slot_src"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "BXok_d"; "bxt"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "g5"; "NP"; "vF"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3"; "cb_av"; "kept_vr"; "d_av"; "cnt_av"; "k_av"; "E_vr1"; "R_vr"; "tv_fail"; "vDg"; "E_vr"; "PD_vr"; "PDk_vr"; "T_fail"; "T_failr"; "T_grown"; "T_grownS"; "T_keep"; "T_keepS"; "Xk_vr"; "c_av"; "h0"; "nd_fail"; "nd_grown"; "nd_keep"; "objs_nl"; "passed_vr"; "room_av"; "s_vr"; "sh_of"; "slot_facts"; "tv_keep"; "tv_vr"; "vKg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLD"; "xLK"; "pH"; "pNX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "NDA"; "PTrue"; "AHead"; "ndesc"; "ANone"; "JA"; "JA_pre"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "nd_below"; "tvinA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m"; "L_mc1"; "Pre_mc"; "E_mg1"; "E_mk1"; "R_mc"; "T_mg0"; "T_mk0"; "dst_obj"; "mc_chk"; "mc_ok"; "mid_dst"; "s_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom";
"topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "extra_hv"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "X_hv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3.VR"; "B32"; "Pre_vr"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv_pf3.Sum.X"; "rel_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv_pf3.Sum"; "reo_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj"; "K_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "robjs_okF"; "xrs_inclb"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "local_ok"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "JL_pure"; "J_memcpy_pre"; "alloc_lawsA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Lib_scan_double_ex OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_build_line_index_rom_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_hv_pf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ScanDoubleAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Lemma h0_ltNF : (h0 < NF)%positive. Proof. reflexivity. Qed.
Lemma HamC_vr : nd_am VR.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_vr : ltac2:(tb__ "0|1|
S3eS1cS26S87A2M0G0S0S8cS90S25S26S87R1A3A1S88A3Ld;S5bA3"). Proof. repeat constructor. Qed.
Lemma P0_vr_mono : ltac2:(tb__ "0|2|
S1bS1cS2cS2cA2M0A1M1G1S1bS1cG0S2cA2A1S4G0S32G0R1R5A3S32G0R2R5A3F_;Fbn;S7aR5R3R2A3S7aR5R4R3A3F_;F_;Fr;FFFc;FF';FF;").
Proof. intros F F' FFc r _ H. exact H. Qed.
Lemma lines_in_kept_vr : ltac2:(tb__ "0|0|
S32S1cS2S2A2S1dS2S2S80S40Z10S81A2A4S52A3").
Proof. cbn. do 17 right. left. reflexivity. Qed.
Lemma av_in_tv_keep : ltac2:(tb__ "0|0|
S32S1cS2S2A2S1dS2S2S53S40Z4S55A2A4S6fA3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
Lemma lines_in_tv_fail : ltac2:(tb__ "0|0|
S32S1cS2S2A2S1dS2S2S80S40Z10S81A2A4S58A3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
Lemma av_in_tv_vr : ltac2:(tb__ "0|0|
S32S1cS2S2A2S1dS2S2S53S40Z4S55A2A4S70A3").
Proof. unfold tv_vr. apply in_or_app. right. left. reflexivity. Qed.

Lemma hv3_facts_room : ltac2:(tb__ "0|1|
S1S0S1aS33S3S8S6S64S83A2A1S5S27S56A1A1M0A3S19A3S1S0S1aS33S3S8S6S83ScS7fS50S7Z1A1A3A2A1G0A3S19A3S0S1aS33S3S8S6S50S7Z4000000A1A2A1G0A3S19A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma room_av_holds : ltac2:(tb__ "0|0|
S4S3eS3S9R1A1S5S27S56A1A1A3S9R2S6bA2F_;Frho;").
Proof.
  intros rho HF. pose proof hv3_facts_room as (CC & CN & CL).
  pose proof (holds_mem _ _ _ HF CL) as FL. pose proof (holds_mem _ _ _ HF CC) as FC. pose proof (holds_mem _ _ _ HF CN) as FN.
  rewrite h_ule in FL, FC, FN. rewrite uval_lit in FL by lia.
  pose proof (uval_range rho pNX) as RN. pose proof (uval_range rho c_av) as RC.
  rewrite uval_add_small in FN by (rewrite uval_lit by lia; lia). rewrite uval_lit in FN by lia.
  assert (E0 : uval rho cnt_av = 3 * uval rho c_av) by (unfold cnt_av; rewrite uval_mul_comm; apply uval_mul_lit; lia).
  assert (E1 : uval rho (SAlu ALU_ADD cnt_av (SLit 3)) = 3 * uval rho c_av + 3) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  assert (E2 : uval rho (SMd M_MUL (SLit 4) (SAlu ALU_ADD cnt_av (SLit 3))) = 4 * (3 * uval rho c_av + 3)) by (rewrite uval_mul_lit by (rewrite ?E1; lia); rewrite E1; reflexivity).
  unfold room_av. rewrite h_ule, E2. rewrite uval_lit by (unfold VR.B_EW; lia).
  apply (room4_arith (3 * uval rho c_av) (uval rho pNX) (uval rho vLEN) 3); lia.
Qed.

Definition slot_src (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S1fS1fS1fS33S3S8S6ScS7fS54S7Z3A1A3Vk;A2A1VF;A3S33S3S8S6S54Vk;A2A1VF;A3A2S33S3S8S6Vk;S7ZffffffffA1M0A2A1VF;A3A2S33S3S8S6S40Z4Vk;A2G0A2A1VF;A3A2").
Lemma hv3_facts_slot : ltac2:(tb__ "0|0|
S1S0S1aS42S55S5S27S61A1A1A2S19A3S0S1aS42S71S5S27S5fA1A1A2S19A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma slot_vals : ltac2:(tb__ "0|4|
S4S1bS3A1S2S3eS3S9R3A1R2A3S0S1aS42R2R3A2S19A3S1S48S47S43R5S54A2M0Z3A2S43R5R3A2M1A2S1S48S4aZ4M2G1A2M3ZffffffffA2S1S0S2cS43R5S40G2R3A2A2G3A3S0S2cS43R5S51A2S4aG2G0A2A3A2A2A2F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H. unfold slot_src in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H4) as F4.
  rewrite h_ule in F1, F2, F3, F4. rewrite uval_lit in F3, F4 by lia.
  pose proof (uval_range rho cnt_av) as RC. pose proof (uval_range rho k) as RK.
  rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
  assert (E4k : uval rho (kb 4 k) = 4 * uval rho k) by (unfold kb; apply uval_mul_lit; lia).
  assert (E4c : uval rho cb_av = 4 * uval rho cnt_av) by (unfold cb_av; rewrite uval_mul_comm; apply uval_mul_lit; lia).
  rewrite E4k in F4. repeat split; lia.
Qed.
Lemma slot_holds : ltac2:(tb__ "0|0|
S4S1bS3A1S2S3eS3S9R3A1R2A3S0S1aS42R2R3A2S19A3S3eS3S9R5A1S6eR3A1A3F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H. destruct (slot_vals rho F k HF H) as (V1 & V2 & V3 & V4).
  pose proof (uval_range rho cnt_av) as RC.
  unfold slot_facts. constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
  - lia.
  - unfold VR.B32. rewrite uval_lit by lia. lia.
Qed.

Definition mc_src (d : sv) (F : list sprop) : bool := ltac2:(tb__ "0|1|
S1fS1fS33S3S8S6Vd;SdP1eA1M0A2A1VF;A3S33S3S8S6S51S7Sb1A1A2A1VF;A3A2S33S3S8S6G0S7Z7fffff800000A1A2A1VF;A3A2").
Lemma hv3_facts_mc : ltac2:(tb__ "0|0|
S1S0S1aS41S53S5S27S99A1A1A2S19A3S1S0S1aS41S53S5S27S9cA1A1A2S19A3S1S0S1aS41S59S5S27S98A1A1A2S19A3S0S1aS41S59S5S27S9bA1A1A2S19A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma mc_rng : ltac2:(tb__ "0|2|
S4S1bS3A1S2S3eS3S9R3A1R2A3S0S1aS41R2R3A2S19A3S1S0S2cS43R5ScS7fR3S51A3A2S47S43R5R3A2S43R5S51A2M0A2A3S1S0S2cS15R5S51A2G0A3S0S2cS15R5ScS7fS51S7ZcM1A1A3A2S47G0G1A2A3A2A2F_;F_;Fd;FF;Fr;").
Proof.
  intros r F d HF H. unfold mc_src in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  rewrite h_ule in F1, F2, F3. unfold VR.B32, Lib_vec_reserve.B32 in F2. rewrite uval_lit in F2, F3 by lia.
  pose proof (uval_range r cb_av) as Rc. pose proof (uval_range r d) as Rd.
  assert (A12 : uval r (SAlu ALU_ADD cb_av (SLit 12)) = uval r cb_av + 12) by (apply uval_add_litZ; lia).
  split; [apply uval_add_small; lia|]. split; [apply soff_smallu; lia|]. rewrite <- A12. apply soff_smallu. rewrite A12. lia.
Qed.
Lemma mc_rng_fwd : ltac2:(tb__ "0|5|
S4S1bS3A1S2S3eS3S9R3A1R2A3S0S1aS41R2R3A2S19A3S1S0S2cS47S3dQ40M0S11R5S12S9dR3A1M1A1A2A2M2S14R5G1A2A2S47S3dG0S11R5S12Sa0R3A1M3A1A2A2M4S14R5G3A2A2A3S0S2cS47G2S13R5G1A2A2S47G4S13R5G3A2A2A3A2F_;F_;Fd;FF;Fr;").
Proof.
  intros r F d HF H. destruct (mc_rng r F d HF H) as (A1 & A2 & A3).
  unfold dst_obj, mid_dst, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
  change (bv_unsigned (eval r (SAlu ALU_ADD d cb_av))) with (uval r (SAlu ALU_ADD d cb_av)). rewrite A1. unfold uval. lia.
Qed.
Lemma mc_ok_ent : ltac2:(tb__ "0|3|
S26S2S2S0S1aS9fR3R2R1A3S19A3S1S0S23S1bSbA1M0A1S75R4S97Sa1R4R3R2A3M1A3S21G0S9aR4R3R2A3M2A2A3S0S1aS74R4S97G1G2S1eS26S96S1eS26S96S20S26A1A3A3A5S19A3A2F_;Fk;Fd;FE;").
Proof. intros E d k H. unfold mc_ok, R_mc in *. destruct (entails_frA E Pre_mc (s_mc E d k)) as [R|]; [split; [reflexivity | exact H] | discriminate]. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sa3S4S1bS3cQ40A1A1S78OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sc9S2eVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S2cSa6VCST;R1A2S1S48Z0R2A2S49R2SadA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2cSa6VXGL;R1A2S1S48Z0R2A2S49R2SadA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S2cSafR1A1Sa6VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1bS1cS1cS2cS2cA2S2cA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S4OFr;") := ltac2:(tb__ "0|0|
S38VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S89VAInv;VCST;VXGL;S4eVKc;Vrho0;VP0;VFB;VFF;VBX;S85Vnd;Ac").

Lemma HIN_vr : ltac2:(tb__ "0|1|
S4S7eSa3S4S1bS3cQ40A1A1S78S3eS3S9R6A1S5S27S5aA1A1A3VP0;Vrho0;A1SaaS4eVrho0;R8A3VAInv;R7R6R5R4A4S8bVrho0;R8A2Sb8RbSa5Sa4R9A1A1A2S8dVFB;RaA2S8eVFF;RbA2S92VFB;RcReS22S1cS2S2A2S52S6aA3M0A4Sb9RfG0A2SbaR10G0A2S8fVFF;RfR11S35A4S1SbeVCST;Vrho0;VFB;VFF;R12S52S35S57A8S1Sc0VCST;VXGL;Vrho0;VFB;VFF;R12S52S35S63A9S7aSb7VFB;R12S52A3SbdVFF;R12S35A3S7cS7bR12S57R11A3S6cA2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof using ALA HCST HXlits.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof hv3_checks_vr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & CX & CLN & _).
  assert (HNk : tvinA FB Ai rho kept_vr) by (apply (tvinA_sublist FB Ai rho (kept_vr ++ passed_vr)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_vr) by (exact (tvd_app_l rho kept_vr passed_vr HD)).
  assert (HZk : tvz rho kept_vr) by (apply (tvz_sublist rho (kept_vr ++ passed_vr)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (lo_robjsF AInv CST ALA HCST FB FF rho0 Ai rho _ kept_vr R_vr rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CLN lines_in_kept_vr CR).
  - exact (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ kept_vr Xk_vr rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold P0_vr. rewrite !rw_call'.
    change (wsub_get s_vr 17) with k_av. change (wsub_get s_vr 15) with d_av. change (wsub_get s_vr 12) with (SAlu ALU_ADD vF (SLit 664)). change (wsub_get s_vr 14) with alA.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (E664 : uval rho (SAlu ALU_ADD vF (SLit 664)) = uval rho vF + 664) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
    assert (EalA : uval rho alA = uval rho vF + 464) by (unfold alA; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    split; [|split].
    + fact HF (SPUle k_av (SLit 4294967295)) HkB. rewrite h_ule, uval_lit in HkB by lia.
      intros Hk. apply (tvz_in_kd rho (kept_vr ++ passed_vr) d_av 4 k_av HZ); [apply in_or_app; right; left; reflexivity | lia | unfold B32, Lib_vec_reserve.B32; lia | exact Hk].
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite E664. lia.
    + exists (uval rho vF), 2048, (uval rho vFL). split; [exact HinF|]. rewrite EalA. lia.
Qed.

Definition reo_chk (tv : list (sv * sv)) (X : list (sv * sv)) (Tb T : axst) : Prop := ltac2:(tb__ "0|2|
S1S0S2S29VTb;A1S7SaeA1A3S1S0S1aS2bS1eS3S10S2aS4dA1S4fA2S1eS3S6SdS4dA1S7S4cS4bZ2Z3dA2Z1A2A1A2S20S3A1A3A3S5S27VTb;A1M0A1M1A2S19A3S1S0S1aSbfVX;S28VTb;A1A2S19A3S1S0S26Sc5VTb;VX;S4dZ4Z1eA5VT;A3S1S0S1aS18S27VT;A1A1S19A3S1S0S1aSa9G1Vtv;S35Sa8S16G0A1A5S19A3S0S1aSa7G1A1S19A3A2A2A2A2A2A2").
Lemma SPA_reopen_lo : ltac2:(tb__ "0|3|
S1bS1cS2S2A2M0A1M1S1bS44A1G1S26S26S4S1bS3cQ40A1A1S3bSb5R8R6R5R4A4S32G0S1dS2S2S80S40Z10S81A2A4R9A3S0S1aSa2VXGL;S5S27R7A1A1RaZ4Z1eR8A6S19A3S2fS2eVJAv;S84RbS35RaS86S82S19A2M2A4A1R8R6R5R4A6S2fS2eVJAv;S84RcS35RbG2A4A1R8R7R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;FT;FTb;FX;Fbd;Ftv;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX.
  intros tv bd X Tb T rho tp w (C1 & C2 & C3 & C4 & C5 & C6 & C7) Hlin CXR Hw. rewrite <- C4.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
           tv frL bd (AHead pH true) 0%nat 110%positive 5 120%positive g5 4 30 Tb X rho tp w frL_0 ltac:(lia) C1 ltac:(lia)
           ltac:(change (fs_frame_size 5) with 2048; lia) C2 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC.xrs_inclb_sound _ _ C3) ltac:(rewrite C4; exact C5)); [|exact Hw].
  intros Ai rho3 tp3 md3 HF3 HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (lo_robjsR AInv CST ALA HCST FB FF rho0 Ai rho _ tv _ rho3 tp3 md3 HM HF3 HP0 Hav HT HTK HN HD HZ HFR C7 Hlin C6).
  - exact (lo_xrsRo AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ tv X rho3 tp3 md3 4 30 HM HF3 HP0 Hav HT HTK HN HD HZ HFR CXR).
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S30S26S4S1bS3cQ40A1A1S3aS3eS3S9R3A1S5S27R4A1A1A3VTR;S2fS2eR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S3aS3aS3aS3bR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S3aOS3aS3bR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S30S30S26S26S7dS1bSbA1M0S1bS1cS26S72A2M1A1S1bS1cS2S2A2M2A1S3aS4S1bS3cQ40A1A1M3G2S32G2R1R5A3S32G2R2S28RbA1A3F_;Fr;S0S23G0A1S75RaR9R8A3S21G0R7A2A3S0S1aS74RbRaR9R8S3fG1S26S24S26S72A2R7A4A5S19A3S4G3VTR;S2fS2eRfRdR2R1A5S73S2eSeS27RdA1A1R2R1RaA5A2Ftp1;Frho1;S1bS79A1M4S7eS78S31S2eR9R8R10S1dG4S93R3S94R2R1A2A4A5R13RaR9R4R2A4R13S7cS7bRbRfS77R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S26S72G4S7eS78S4G3G4S7eS78S32G1S1dS26S72RaR9A4R14A3S31S2eR12R11R19S1dG4S93R9S94R8R7A2A4A5R1cR13R12RaR8A4SaaSeS27R1aA1A1S7cS7bR14R18S77R9R13RaA3A3R19A2R8A3S31S2eR9R8ReS1dG4S93R7S94R6R5A2A4A5ReS7cS7bR16R1aS77RbR15RcA3A3R1bA2R15RaR9R8R6A6S1SbbR17S77RcR16RdA3R1bR1cR1dR10R1eR19RbA9S4SabR18S77RdR17ReA3R1cR1dS27R1eA1S27R1fA1S27R11A1R1RcA9VTR;S2fS2eS76R11S7cS7bR19R1dS77ReR18RfA3A3R1eA2R18RdRcA5SbcR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S2fS2eR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CHVR : ltac2:(tb__ "0|1|
S1bS1cS2cS2cA2M0A1S1bS1cG0S2cA2A1S46S4S1bS3cQ40A1A1S45Z3R3A2VTR;S2fS2eS8aVAInv;VCST;VXGL;VKc;S7aR6R5A2R6R5R4S85Sc1S65S19Sb3A3AaSb2R3R2A5S73S2eSacR3R2Sc2VAInv;VCST;VXGL;VKc;S7aS85S5cR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CMEMCPY : ltac2:(tb__ "0|2|
Sa3S4S1bS3cQ40A1A1VTR;S2fS2eSc8VAInv;R3VKc;A3S97R2R1A5S73S2eSacR2R1S1eS1cS26S72A2M0S1dS26S72S96Sc7VAInv;VCST;VXGL;R3VKc;A5A4M1S1eG0G1S20G0A1A3A3A5A2Ftp1;Frho1;FAi;").

Definition rel_chk (L : list (Z * Z)) (E0 Er : axst) : Prop := ltac2:(tb__ "0|6|
S1S0S1bSbA1S16S27VE0;A1M0A1S22SbS69VE0;A1M1S1eSbSc6S4dZ4M2Z1eM3S17S6dVE0;A1A1M4SfA5S20SbA1A3A3A3S1S0S2S29VE0;A1S7SaeA1A3S1S0S1aS2bS1eS3S10S2aS4dA1S4fA2S1eS3S6SdS4dA1S7S4cS4bZ2Z3dA2Z1A2A1A2S20S3A1A3A3S5G0A1M5A2S19A3S1S0S1aS34S1cS2cS2cA2Sc3G4SfG2G3A4VL;A3S19A3S1S0S1aS91SeG0A1S95A2S19A3S1S0S1aSa9G5S39S35Sa8G1A5S19A3S1S0S1aSa7G5A1S19A3S0S26Sc4VE0;G1P6eVL;A4VEr;A3A2A2A2A2A2A2A2").
Lemma site_rel : ltac2:(tb__ "0|2|
S1bS1cS2cS2cA2A1S26S26S4S1bS3cQ40A1M0A1S3aSb4R6R5R4A3S36R4A1S4S36R1A1S2dS32S2dR1S37A3S0G0SaR4R2A2SaR9R2A2A3F_;Fv;VTR;S2fS2eVJAv;S95A1M1R9R3R7A5R6A2F_;F_;Frho1;VTR;S2fS2eG1R8R6R5A5R4A2F_;F_;F_;FQ;Ftp;Frho;FEr;FE0;FL;").
Proof using ALA HCST HXGL LFSH HKc HBX TR_facts TR_pre TR_exw TR_pureP.
  intros L E0 Er rho tp Q (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8) HPHI HK.
  apply TR_facts. intros HF0.
  apply (TR_pre (fun w => exists rho1, (tblB rho1 /\ forall v, In v V_B -> rw rho1 v = rw rho v) /\ SPA segs (JAv ndA1) Er rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj g5 4 30 (ob_cells (sh_of E0)) DUnknown] (vms md tp ms)). split.
    - split; [|intros v _; reflexivity].
      destruct Hw as [Hsm (Ai & kc & HJ)]. pose proof HJ as (Hav & _ & HM & HT & _ & _ & (_ & _ & HZ) & _).
      pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
      destruct (lines_blk rho _ (topG (aa_geom Ai)) HF0 R7 HTK) as (_ & HiC & HcK & _ & _ & Htop).
      pose proof (lines_nz rho _ (topG (aa_geom Ai)) tvL HF0 R7 HTK HZ lines_in_tvL) as Hnz.
      pose proof (has_facts_sound rho _ _ HF0 R3) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
      pose proof (topG_range (aa_geom Ai)) as TG.
      apply (tblB_absorb_sh AInv CST XGL ALA HCST Kc FB FF BX rho0 ndA1 Ai kc rho tp tr md 0%nat 110%positive 5 120%positive g5 4 30 _ DUnknown _ HJ frL_0);
        [lia | lia | change (fs_frame_size 5) with 2048; lia | exact HG1 | exact HG2 | exact lines_in_tvL | exact Hnz | lia | exact HiC | exact HcK | exact HPHI].
    - rewrite <- R8.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tvL frL (bdA A1) (AHead pH true) 0%nat 110%positive 5 120%positive g5 4 30 (ob_cells (sh_of E0)) DUnknown E0 (objs_nl E0) L rho tp tr ms md
               frL_0 ltac:(lia) R2 R1 ltac:(lia) ltac:(change (fs_frame_size 5) with 2048; lia) eq_refl R3 R4 R5); [|exact Hw].
      intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
      exact (lo_robjsR AInv CST ALA HCST FB FF rho0 Ai rho _ tvL (objs_nl E0) rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR R7 lines_in_tvL R6). }
  apply TR_exw. intros rho1.
  apply (TR_pureP _ (tblB rho1 /\ forall v, In v V_B -> rw rho1 v = rw rho v)); [intros w [H _]; exact H|]. intros [HPHI1 HV1].
  apply (TR_pre (SPA segs (JAv ndA1) Er rho1 tp)); [intros w [_ Hw]; exact Hw|]. exact (HK rho1 HPHI1 HV1).
Qed.

Lemma site_vr : ltac2:(tb__ "0|5|
S4S1bS3cQ40A1M0A1M1S3aS0S1aSa2VXGL;S5S27S5eA1A1S58Z4Z1eSb0A6S19A3S36R4A1S4G1S36R2A1M2S2dS32S2dR1S37A3M3S0G0SaR5R2A2M4SaRaR2A2A3F_;Fv;VTR;S2fS2eVJAv;S68A1S62R4R3A5R7A2F_;F_;Ftp';Frho';S4G1G2S2dG3S0G0G4SaRbR2A2A3F_;Fv;VTR;S2fS2eVJAv;S67A1S60R4R3A5R8A2F_;F_;Ftp';Frho';S4G1G2S2dG3S0G0G4SaRcR2A2A3F_;Fv;VTR;S2fS2eVJAv;S66A1S5dR4R3A5R9A2F_;F_;Ftp';Frho';VTR;S2fS2eVJAv;S95A1Sb6R8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_facts TR_ex TR_pre TR_exw TR_pureP TR_callP CHVR.
  intros rho tp Q CXR HPHI Kk Kg Kf.
  pose proof hv3_checks_vr as (Cxf & CEvr & Cfb & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cpbd & Cxk & Chand & Cpay & Cnb & Cbr & Cnp & _ & _ & CLN & CVB).

  assert (CREL : rel_chk [(128, 12)] K_vr K_vrr).
  { pose proof hv3_checks_rel as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _). exact (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 R8))))))). }
  apply (site_rel [(128, 12)] K_vr K_vrr rho tp Q CREL HPHI). intros rho1 HPHI1 HV1.

  set (ndv := NDA tv_vr frL bd_vr (AHead pH true)).
  apply (TR_pre (SPA segs (JAv ndv) E_vr rho1 tp)).
  { intros w Hw. rewrite <- CEvr. apply (SPA_refacts_JA segs); [| exact Cfb |].
    - apply (SPA_axforms segs (JAv ndv) (xf_vr K_vrr) rho1 K_vrr E_vr1 tp w Cxf).
      unfold ndv, tv_vr. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL (bdA A1) bd_vr _ K_vrr rho1 tp w Cpbd).
      apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvL _ frL (bdA A1) _ K_vrr rho1 tp w Cptv). exact Hw.
    - intros tr md _ HF1. apply Forall_app. split; [|exact HF1]. constructor; [exact (room_av_holds rho1 HF1) | constructor]. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho1 xLD <> 0 /\ uval rho1 pI < uval rho1 xLC /\ uval rho1 xLC <= uval rho1 xLK /\ 16 * uval rho1 xLK <= 4294967295
                     /\ uval rho1 xLD + 16 * uval rho1 xLK <= 2 ^ 47)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho1 Ai Hav ltac:(reflexivity) HT) as HTK. pose proof (topG_range (aa_geom Ai)) as TG.
    destruct (lines_blk rho1 _ (topG (aa_geom Ai)) HF CLN HTK) as (_ & HiC & HcK & Hk32 & _ & HdT).
    split; [|repeat split; lia].
    apply (lines_nz rho1 _ (topG (aa_geom Ai)) tv_vr HF CLN HTK HZ). unfold tv_vr. apply in_or_app. left. exact lines_in_kept_vr. }
  intros (Hdnz & HiC & HcK & Hk32 & HdT).
  unfold ndv, tv_vr.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           VR.Pre_vr (ndh h0 true VR.nd0) PDk_vr NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHVR eq_refl
           E_vr s_vr R_vr Xk_vr rho1 tp kept_vr passed_vr frL bd_vr brest_vr (AHead pH true) Q
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. apply (payA_of_bud_pay2 NP rho0 P0). exact Cpay.
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho2 & tp2 & md2 & HM) HT HTK.
    exact (HIN_vr rho1 ms Ai rho2 tp2 md2 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.
    assert (HV' : forall v, In v V_B -> rw rho' v = rw rho v).
    { intros v Hv. rewrite (V_B_agree_n _ rho1 rho' CVB Hag v Hv). exact (HV1 v Hv). }
    assert (HPHI' : tblB rho').
    { apply (tblB_kept rho1 rho' (V_B_agree_n _ rho1 rho' CVB Hag)); [| exact HiC | exact HcK | exact HPHI1].
      apply (keptK_lines CST FB FF rho0 rho1 kept_vr frL rho' HK lines_in_kept_vr Hdnz); [exact HdT | unfold B32, Lib_vec_reserve.B32; lia]. }
    pose proof hv3_checks_vr_nd as (Nk & Ng & Nf & Tk0 & Tg0 & Tf0 & Bk & Bg & Bf & Tik & Tig & Tif & Reo & RBase & RHf & RXi & RSwf & RRo & RLn & Sk & Sg & Fbk & Fbg & _).
    pose proof hv3_facts_slot as [Ssk Ssg].
    cbn [PDk_vr liftPD PDh PD_vr map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite Tk0, Nk.
      apply (TR_pre (SPA segs (JAv nd_keep) T_keepS rho' tp')); [|exact (Kk rho' tp' HPHI' HV')].
      intros w Hw. rewrite <- Sk. apply (SPA_refacts_JA segs); [| exact Fbk |].
      * rewrite <- Tik. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_keep) (xfb_vr T_keep0) rho' T_keep0 B_keep tp' w Bk Hw).
      * intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. unfold inj_keep. apply Forall_app. split; [exact (slot_holds rho' _ k_av HF2 Ssk)|].
        constructor; [|constructor].
        destruct (slot_vals rho' _ k_av HF2 Ssk) as (V1 & V2 & _ & _). pose proof (uval_range rho' cnt_av) as RC.
        assert (TNZ : tnz rho' (d_av, kb 4 k_av)).
        { unfold tnz. cbn [fst]. pose proof HJ as (Ai & kc & _ & _ & _ & _ & _ & _ & (_ & _ & HZ') & _). cbn [nd_tv nd_keep] in HZ'.
          apply (tvz_in_kd rho' tv_keep d_av 4 k_av HZ'); [exact av_in_tv_keep | lia | unfold B32, Lib_vec_reserve.B32; lia | lia]. }
        pose proof (JA_tv_facts segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue ALA nd_keep rho' tp' tr md (d_av, kb 4 k_av) eq_refl HJ
                      av_in_tv_keep TNZ) as TF.
        apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity.
    +
      rewrite Tf0, Nf.
      apply (TR_pre (SPA segs (JAv nd_fail) T_fail rho' tp')); [|exact (Kf rho' tp' HPHI' HV')].
      intros w Hw.
      apply (SPA_reopen_lo tv_fail brest_vr X_hv T_failr T_fail rho' tp' w (conj RBase (conj RHf (conj RXi (conj Reo (conj RSwf (conj RRo RLn)))))) lines_in_tv_fail CXR).
      rewrite <- Tif. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_fail) (xfb_vr T_fail0) rho' T_fail0 B_fail tp' w Bf Hw).
    +
      rewrite Tg0, Ng.
      apply (TR_pre (SPA segs (JAv nd_grown) T_grownS rho' tp')); [|exact (Kg rho' tp' HPHI' HV')].
      intros w Hw. rewrite <- Sg. apply (SPA_refacts_JA segs); [| exact Fbg |].
      * rewrite <- Tig. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_grown) (xfb_vr T_grown0) rho' T_grown0 B_grown tp' w Bg Hw).
      * intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. exact (slot_holds rho' _ vKg HF2 Ssg).
Qed.

Lemma site_mc : ltac2:(tb__ "0|6|
S2S2S1bS1cS2S2A2M0A1M1S1bS44A1G1S26S26S26S26S26S26S26S4S1bS3cQ40A1M2A1M3S3aS9eRfReRdRcRbRaR9R8R7R6R5R4AcS0S1aS41R10S5S27RaA1A1A2S19A3S0S1aS41R11S5S27R9A1A1M4A2S19A3S32G0S1dS2S2S80S40Z10S81A2A4R10A3S0S1aSa2VXGL;G4R11Z4Z1eRfA6S19A3S36R8A1S4G3S36R2A1S2dS32S2dR1S37A3S0G2SaR5R2A2SaReR2A2A3F_;Fv;VTR;S2fS2eVJAv;S84R17S35R16S86S82S19A2M5A4A1ReR4R3A5RbA2F_;F_;Ftp';Frho';VTR;S2fS2eVJAv;S84R14S35R13G5A4A1R11RaR9A5R8A2F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FT;FTb;FTr;FT0;FE;FE1;FE0;FX;Fbd;Ftv;Fk;Fd;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_facts TR_ex TR_pre TR_exw TR_pureP TR_callP CMEMCPY.
  intros d k tv bd X E0 E1 E T0 Tr Tb T rho tp Q
    (Cxf & Cnth & Cwf & CE & Cok & Cta & Cnp & Cnb & Cbb & Cwp & Cpp & CR & CX & CLN & CVE & CT0 & Cnth1 & Cwf1 & CTr & CTb & RBase & RHf & RXi & Reo & RSwf & RRo & RLn & _)
    CS1 CS0 Hlin CXR HPHI HK.
  destruct (mc_ok_ent E d k Cok) as [Cent Cchk].
  set (nd := NDA tv frL bd (AHead pH true)).

  apply (TR_pre (SPA segs (JAv nd) E rho tp)).
  { intros w Hw. pose proof (SPA_axforms segs (JAv nd) (xf_mc d E0) rho E0 E1 tp w Cxf Hw) as Hw1. rewrite <- CE. unfold E_mc.
    apply (SPA_reshape segs (JAv nd) rho E1 (i_dst d E1) (mid_dst d) (dst_obj d) tp w Cnth eq_refl eq_refl eq_refl Cwf); [|exact Hw1].
    intros HF. exact (mc_rng_fwd rho _ d HF CS1). }

  apply TR_facts. intros HF1.
  apply (TR_pureP _ (uval rho xLD <> 0 /\ uval rho pI < uval rho xLC /\ uval rho xLC <= uval rho xLK /\ uval rho (kb 16 xLK) = 16 * uval rho xLK)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv nd] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
    destruct (lines_blk rho _ (topG (aa_geom Ai)) HF1 CLN HTK) as (_ & HiC & HcK & _ & EK & _).
    split; [exact (lines_nz rho _ (topG (aa_geom Ai)) tv HF1 CLN HTK HZ Hlin) | split; [exact HiC | split; [exact HcK | exact EK]]]. }
  intros (Hdnz & HiC & HcK & EK).
  apply (purec_callT_k_xp segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memcpy Pre_mc [L_mc1; L_mc1] E (s_mc E d k) (R_mc E d k) rho tp nd bd Q).
  - intros Ai rho2 tp2. cbn [map]. exact (CMEMCPY Ai rho2 tp2).
  - reflexivity.
  - reflexivity.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cbb.
  - cbn [nd_bd nd]. apply payA_same. exact Cwp.
  - exact Cpp.
  - exact (site_rt_lo AInv CST XGL ALA HCST HXlits FB FF rho0 E (s_mc E d k) (R_mc E d k) rho tv bd (AHead pH true) CR CX CLN Hlin).
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E memcpy_pc (s_mc E d k) (R_mc E d k) rho tp tr ms md Hsm HM HX' Cent).
  -
    intros L rho2 tp2 HL Hag HKR. assert (HL' : L = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L. cbn [nd_tv nd_fr nd_am nd].
    change (T_afterA Pre_mc E (s_mc E d k) (R_mc E d k) L_mc1) with (T_mc0 E d k). rewrite CT0.
    assert (HV2 : forall v, In v V_B -> rw rho2 v = rw rho v) by (exact (V_B_agree_n _ rho rho2 CVE Hag)).
    apply (TR_pre (SPA segs (JAv nd) T rho2 tp2)).
    { intros w Hw.
      assert (Hw1 : SPA segs (JAv nd) Tr rho2 tp2 w).
      { rewrite <- CTr. unfold T_mcr.
        apply (SPA_reshape segs (JAv nd) rho2 T0 1 (dst_obj d) (mid_dst d) tp2 w Cnth1 eq_refl eq_refl eq_refl Cwf1); [|exact Hw].
        intros HF. destruct (mc_rng_fwd rho2 _ d HF CS0) as [G1 G2]. split; symmetry; assumption. }
      pose proof (SPA_axforms segs (JAv nd) (xfb_mc d Tr) rho2 Tr Tb tp2 w CTb Hw1) as Hw2.
      exact (SPA_reopen_lo tv bd X Tb T rho2 tp2 w (conj RBase (conj RHf (conj RXi (conj Reo (conj RSwf (conj RRo RLn)))))) Hlin CXR Hw2). }
    apply (HK rho2 tp2); [|exact HV2].
    apply (tblB_kept rho rho2 (V_B_agree_n _ rho rho2 CVE Hag)); [| exact HiC | exact HcK | exact HPHI].
    intros z Hz. apply (HKR (xLD, kb 16 xLK) z Hlin); [unfold tnz; cbn [fst]; exact Hdnz|].
    unfold tvv. cbn [fst snd]. change (bv_unsigned (eval rho xLD)) with (uval rho xLD). change (bv_unsigned (eval rho (kb 16 xLK))) with (uval rho (kb 16 xLK)).
    rewrite EK. exact Hz.
Qed.
End X.
End Sum.
End Lib_load_obj_hv_pf3.

(* [comment removed for export] *)
Module Lib_load_obj_hv3e.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "nat"; "prod"; "cons"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3"; "nd_keep"; "nd_fail"; "T_fail"; "T_grownS"; "T_keepS"; "nd_grown"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "mH"; "PhisH"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "RL"; "VLA"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "cps_v"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv3e"; "X_rlF"; "cutsH3"; "exitsH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m"; "E_mk0"; "E_o1"; "T_mck"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "ejcertAF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition X_rlF : axst := Eval vm_compute in leafL (runL 600 cps_v T_fail) pc_latch 0.
Definition cutsH3 : list efnode := ltac2:(tb__ "0|7|
S3S2S2S2S7S8A2M0S1A2M1S2S11S12A2M2A2M3S0G1G2S0G0S1S0S7S8SdS9A4U1M4A4SfZfM5Z5aA2M6A4S3G3S0G1G2S0G0S1S0S7S8ScSeA4G4A4G6A4S3G3S0G1G2S0G0S1S0S7S8SbSaA4G4A4G6A4S3G3S0G1G2S0G0S1S0S7S8S1fS9A4G4A4SfG5Z46A2A4S4G3A1A3A3A3A3").
Definition exitsH3 : list efnode := ltac2:(tb__ "0|6|
S3S2S2S2S7S8A2M0S1A2M1S2S11S12A2M2A2M3S0G1G2S0G0S1S0S7S8S1dS9A4U1M4A4SfZfM5Z50A2A4S3G3S0G1G2S0G0S1S0S7S8S1eS9A4G4A4SfG5Z3cA2A4S3G3S0G1G2S0G0S1S0S7S8S1aSaA4G4A4S0S11S12S16S17Z1S18A2A4A4S4G3A1A3A3A3").
Lemma ecertH3_ok : ltac2:(tb__ "0|0|
S14S5S20S15S13S10U258S19S13S1bS1cA8S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_load_obj_hv3e.

