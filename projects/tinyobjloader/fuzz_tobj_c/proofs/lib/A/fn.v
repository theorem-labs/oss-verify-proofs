(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFpIface.

(* [comment removed for export] *)
Module Start5CallStates.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "ss_objs"; "sstate"; "ss_facts"; "ss_pc"; "ss_next"; "SVar"; "sprop"; "DUnknown"; "SAlu"; "cell"; "mkObj"; "mkSS"; "sprop_below"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "@Corelib.Init.Datatypes"; "nat"; "cons"; "nil"; "pair"; "true"; "Some"; "option"; "app"; "bool"; "list"; "prod"; "length"; "negb"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Start5CallStates"; "T13c"; "E_s13"; "T13b"; "IP12"; "T13a"; "myregs12"; "IP12f"; "R12"; "T13e"; "s12"; "T13d"; "T13f"; "T13g"; "E_s13g"; "mstk13"; "myfregs12"; "ostk13"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "sym_runA"; "ax_X"; "la_state"; "mkAX"; "mkLeafA"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@Corelib.Lists.ListDef"; "nth"; "map"; "seq"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start5States"; "C12"; "C12e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@Corelib.Init.Nat"; "add"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "RsCut"; "set_objs"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition myregs12 : list sv := ss_regs C12e.
Definition myfregs12 : list sv := ss_fregs C12e.
Definition s12 : wsub := ltac2:(tb__ "0|8|
S1eS21S24S2A2M0S18G0S1aS24S2PaS42S2U2M1S2bS4Z0A1M2A4A4S18G0S1aS24S2PbS42S2U1M3S2bG2A4A4S18G0S1aS24S2PeS42S2UcM4S2bG2A4A4S18G0S1aS24S2PfSdS47SaP1A1S4N100000A1A3A4S18G0S1aS24S2P10S4S56Z100000M5Z40A2A1A4S18G0S1aS24S2P11S4S56G5Z320A2A1A4S18G0S1aS24S2P12S4Z130A1A4S19G0A1A3A3A3A3A3A3A3S1eG0S43S17G0S17S1aS24S2S55S4eU14R1A2A1S42S2R1S2bG2A4A4Lr;S64S17S20S17A1S66S17A1S17S61S23S62S17S60R1A1S18S17G3S18S17G1S18S17UaS18S17UbS18S17G4S19S17A1A3A3A3A3A3A3A1M6A1Lr;S17S65G6A1Lx;S44U0U20A2M7A6A4S43S17G0S17S1aS24S2S55S4eU3cR1A2A1S42S2R1S35G2A4A4Lr;G7A4A3A3").

Definition R12 : list sobj := Eval vm_compute in (match entails_frA C12 Pre_rip s12 with Some R => R | None => [] end).
Lemma entails12 : ltac2:(tb__ "0|1|
S0S1dS20S3A1M0A1S5eS4bS4aS2fA3S1cG0S2dA2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma callcheck12 : ltac2:(tb__ "0|0|
S0S1fS5dS4bS4aS2fS2dS43S38S39S3cS58A4A5S1bA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IP12 : axst := Eval vm_compute in (import_postA s12 Pre_rip P_ret C12 R12).
Lemma IP12_eq : ltac2:(tb__ "0|0|
S0S39S5fS2fS4aS57S4bS2dA5S29A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IP12_at : ltac2:(tb__ "0|0|
S1S0S25S8S37S29A1A1Z600e4A3S0S24S9S4cA1P25A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition IP12f : axst := Eval vm_compute in (ax_with_facts (ax_setX IP12 []) (ss_facts (ax_S IP12) ++ ss_facts C12e)).
Lemma IP12f_eq : ltac2:(tb__ "0|0|
S0S39S5cS5bS29S19S21S2S2A2A1A2S1eSbS7S37S29A1A1S7S4cA1A3A2S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C12e_facts_below : ltac2:(tb__ "0|0|
S0S1fS63SbS11P25A1S7S4cA1A3S1bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run12c__R : option (list leafA) := ltac2:(tb__ "0|0|
S3aS48S4fS50S40S3fS3fS3fS41A1A1A1A1A1A1S18S25S49S19S25A1A3S2cS1bA5").
Local Strategy expand [run12c__R].
Definition E_s13 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 IP12f (ro1__)))) run12c__R).
Lemma run12c : ltac2:(tb__ "0|1|
S0S1dS20S38A1M0A1S3aS48S4fS50S40S3fS3fS3fS41A1A1A1A1A1A1S18S25S49S19S25A1A3S2cS1bA5S1cG0S18S38S3eS27S53A2S19S38A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run12c__R <: run12c__R = Some [mkLeafA E_s13 RsCut]). Qed.
Lemma E_s13_at : ltac2:(tb__ "0|1|
S1S0S25S8S37S27A1A1M0S49A3S0S1dS45A1S52S48G0A2S1cS45S46A2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T13a : sstate := Eval vm_compute in (move_obj_last (ax_S E_s13) 0).
Lemma T13a_eq : ltac2:(tb__ "0|0|
S0S6S5aS37S27A1U0A2S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_T13a : ltac2:(tb__ "0|0|
S0S1fS4dS37S27A1S2aA2S1bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition ostk13 : sobj := Eval vm_compute in (last (ss_objs T13a) (mmap_obj 1%positive 0)).
Definition T13b : sstate := Eval vm_compute in (set_objs T13a (removelast (ss_objs T13a))).
Lemma T13a_split : ltac2:(tb__ "0|0|
S0S20S3A1S5S2aA1S1eS3S5S28A1S18S3S36S19S3A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T13b_eq : ltac2:(tb__ "0|0|
S0S6S54S2aS5S28A1A2S28A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T13c : sstate := Eval vm_compute in (move_obj_last T13b 3).
Lemma T13c_eq : move_obj_last T13b 3 = T13c. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_T13c : ltac2:(tb__ "0|0|
S0S1fS4dS28S26A2S1bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition mstk13 : sobj := ltac2:(tb__ "0|0|
SfSaP1A1S4Nc20A1S4Nbd0A1S19SeA1ScA5").
Definition T13d : sstate := Eval vm_compute in
  (mkSS (ss_pc T13c) (ss_regs T13c) (ss_fregs T13c) (ss_fcsr T13c) (ss_resv T13c) (ss_objs T13c ++ [mstk13]) (ss_facts T13c) (ss_next T13c) (ss_lenient T13c)).
Lemma T13d_eq : ltac2:(tb__ "0|0|
S0S6S10S8S26A1S15S26A1S13S26A1S12S26A1S16S26A1S1eS3S5S26A1S18S3S34S19S3A1A3A3S7S26A1S9S26A1S14S26A1A9S30A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T13d_swf : swf T13d = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T13e : sstate := Eval vm_compute in (match merge_objs_at T13d 23 with Some St => St | None => T13d end).
Lemma T13e_eq : ltac2:(tb__ "0|0|
S0S1dS6A1S51S30U17A2S1cS6S2eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T13f : sstate := Eval vm_compute in (move_obj_last T13e 3).
Lemma T13f_eq : move_obj_last T13e 3 = T13f. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_T13f : ltac2:(tb__ "0|0|
S0S1fS4dS2eS31A2S1bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T13g : sstate := Eval vm_compute in (match merge_objs_at T13f 22 with Some St => St | None => T13f end).
Lemma T13g_eq : ltac2:(tb__ "0|0|
S0S1dS6A1S51S31U16A2S1cS6S32A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_s13g : axst := ltac2:(tb__ "0|0|
S3dS32S19S21S2S2A2A1S4S59A1A3").
Lemma E_s13g_at : ltac2:(tb__ "0|4|
S1S0S25S8S37S33A1M0A1M1S49A3S1S0S24S9G0A1P4dA3S1S0S1dS45A1S52S48G1A2S1cS45S46A2A3S1S0S17S22S3S5S28A1A2U18M2A3S1S0S17S22S3S5S37S27A1A1A2U19A3S1S0S17S22S3S5S2eA1A2G2A3S0S20S21S2S2A2M3A1S3bS27A1S19G3A1A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start5CallStates.

(* [comment removed for export] *)
Module Icpt_read.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "bool"; "true"; "prod"; "app"; "None"; "false"; "list"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "sprop"; "cell"; "mkCell"; "SPUle"; "sobj"; "mkObj"; "DUnknown"; "SAlu"; "sprop_below"; "FcsrFrm0"; "mkSS"; "DImage"; "SPAlign"; "SPBranch"; "SPNot"; "ss_next"; "SPEq"; "SPUlt"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "entailsA"; "leafA"; "ax_S"; "la_state"; "mkLeafA"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "ax_add_facts"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read"; "hc"; "vC"; "E_reg"; "buf"; "vLb"; "FUELR"; "Fpos"; "vBb"; "E_L_bk"; "E_L_in"; "E_ecall"; "E_pos"; "R_reg_h"; "R_reg_k"; "X_rd"; "objs_rd"; "s_reg_h"; "s_reg_k"; "CL_0"; "FR"; "base_rd"; "cutpcs_rd"; "CL"; "P_rd"; "P_rd_d"; "T_pos"; "Tr1"; "vOb"; "F_L"; "Pre_rd"; "T_pos_0"; "T_rd_d"; "T_rd_h"; "T_rd_k"; "cur"; "frame_cells_rd"; "s_L_bk"; "s_L_in"; "spm"; "vcuts_rd"; "O_buf"; "O_cstk"; "O_errno"; "O_frame"; "O_realrd"; "O_rtc3"; "cstk_cells1"; "cuts_h"; "cuts_k"; "exits_h"; "exits_k"; "gs"; "regs_ecall"; "vcuts_h"; "vcuts_k"; "vexits_h"; "vexits_k"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.Seg3"; "tv"; "res"; "cur"; "gl"; "mid_state"; "Fpos"; "F8of"; "FR"; "gs"; "l_regs"; "lastb"; "s4v"; "E_reg"; "F_L"; "P_rd"; "mid_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "add"; "shp"; "P_ret"; "g8"; "O_rtc2"; "shpk"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "add"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "BC_GEU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "mkA"; "ACEIL"; "A_globals"; "SHB"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "post_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.Icpt_read.RDAddr"; "rl_head"; "ra_icpt"; "rd_ecall"; "rd_pos"; "rd_ret"; "musl_read"; "ra_musl"; "ra_reg"; "rd_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "call_checkA"; "entails_frA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA"; "A_after_fresh"; "A_after_hdr"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA SysStepA SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import RegionAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module RDAddr.
  Definition rd_entry : Z := 0x4ee40.
  Definition rd_ecall : Z := 0xdeb5c.
  Definition rd_ret : Z := 0x4ef10.
  Definition rd_pos : Z := 0x4ee98.
  Definition rl_head : Z := 0x4f054.
  Definition ra_reg : Z := 0x4ef9c.
  Definition ra_musl : Z := 0xe36a0.
  Definition ra_icpt : Z := 0x4ee90.
  Definition musl_read : Z := 0xe3678.
End RDAddr.
Import RDAddr.

Definition vBb := SVar 15. Definition vLb := SVar 16. Definition vOb := SVar 17. Definition vC := SVar 19.
Definition buf : sv := add vBb vOb.
Definition X_rd : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6SdSdA2M0S1SdSdS38S35A4S3G0A1A3").

Definition O_rtc3 : sobj := ltac2:(tb__ "0|3|
S15SfZ0A1SfZf20d8A1M0SfZf20daA1S0S11S12G0Z1M1SfG1A1M2A3S0S11S12SfZf20d9A1G1G2A3S3S11A1A3A3S16A5").
Definition O_realrd : sobj := ltac2:(tb__ "0|1|
S15SfZ0A1SfZe99b8A1M0SfZe99c0A1S0S11S12G0Z8SfS98A1A3S3S11A1A3S1bA5").
Definition frame_cells_rd : list cell := ltac2:(tb__ "0|1|
S0S11S12SfN30A1Z8M0SeP28A1A3S0S11S12SfN28A1G0SeP27A1A3S0S11S12SfN20A1G0SeP26A1A3S0S11S12SfN18A1G0SeP1dA1A3S0S11S12SfN10A1G0SeP1cA1A3S0S11S12SfN8A1G0SePbA1A3S3S11A1A3A3A3A3A3A3").
Definition O_frame (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S15SePaA1SfN850A1SfZ0A1Vcs;S16A5").
Definition spm : sv := add (SVar 10) (SLit (-2128)).
Definition O_cstk (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S15S57SfN50A1SfZ0A1Vcs;S16A5").
Definition O_buf (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S15S34SfZ0A1S32Vcs;S16A5").

Definition O_errno (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S15SeP18A1SfNa4A1SfNa0A1Vcs;S16A5").
Definition objs_rd (fr cs bc ec : list cell) : list sobj := ltac2:(tb__ "0|0|
S7S14S0S14S5cVfr;A1S0S14S5aVcs;A1S0S14S59Vbc;A1S0S14S5bVec;A1S0S14S5eS0S14S7eS0S14S5dS3S14A1A3A3A3A3A3A3A3S8aA3").

Definition base_rd : list sprop := ltac2:(tb__ "0|c|
S0S10S13S7aS4cS32A2S35A2S0S10S13S4cS35A2S0S10S13S32S35A2S0S10S13S35SfS80Z2M0Z28A2A1A2S0S10S13S7aS38S35A2M1SfS81S8bZ8M2A2A1A2S0S10S13SfZ1000M3A1M4S38A2S0S10S13G1SfS81S80G0Z2fA2M5G2A2A1M6A2S0S10S13S38G6A2S0S10S1cPfZ3M7A2S0S10S13SfZ1A1S32A2S0S10S13S32SfZ10000A1A2S0S10S1cPaM8Z4A2S0S10S13SfS82S89G3A2A1SeG8A1M9A2S0S10S13G9SfS80G0Z3fA2A1A2S0S10S13G4SeP18MaA1MbA2S0S10S13GbSfG5A1A2S0S10S1cGaG7A2S3S10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition Pre_rd : axst := ltac2:(tb__ "0|2|
S88S1aS9bS90S91S0S6S2SdA2M0S1S2SdUaSfZ3A1A4S0G0S1S2SdUbS34A4S0G0S1S2SdUcS32A4S3G0A1A3A3A3A2S8fS19S8SdA1S40S3S11A1M1G1G1G1A4S45S8eS9A9S3fA2").

Definition cstk_cells1 : list cell := ltac2:(tb__ "0|1|
S0S11S12SfN8A1Z8M0SfS94A1A3S0S11S12SfN10A1G0SePaA1A3S3S11A1A3A3").
Definition regs_ecall : list sv := ltac2:(tb__ "0|4|
S90S91S0S6S2SdA2M0S1S2SdU1SfS99A1A4S0G0S1S2SdU2S7aSePaA1M1SfN860A1A2A4S0G0S1S2SdU8G1A4S0G0S1S2SdU9S34A4S0G0S1S2SdUaSfZ3A1M2A4S0G0S1S2SdUbS34A4S0G0S1S2SdUcS32A4S0G0S1S2SdUdSfZ0A1M3A4S0G0S1S2SdUeG3A4S0G0S1S2SdUfG3A4S0G0S1S2SdU10G3A4S0G0S1S2SdU11SfZ3fA1A4S0G0S1S2SdU12S32A4S0G0S1S2SdU13G2A4S0G0S1S2SdU14SfZ1A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").
Definition E_ecall : axst := ltac2:(tb__ "0|1|
S88S1aS95S65S8fS19S8SdA1S40S54S5fS3S11A1M0G0A4S45S8eS9A9S3fA2").

Definition FUELR : nat := 600%nat.
Lemma echeck_rd1 : ltac2:(tb__ "0|3|
S2aS4S30S87S36S0S23S95S3S23A1A3S8eS0S2cS2dS4eZ1SfZ0M0A1M1A3S3S2cA1M2A3S0S2cS2dS3bG0G1A3G2A3A6S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check_rd1 : ltac2:(tb__ "0|1|
S2aS4S2eS87S36S0S23S95S3S23A1A3S8eS0S24S4eS3S24A1M0A3S0S24S3bG0A3A6S5A3").
Proof. exact (check_cfgA_of_ecfgA segs FUELR [rd_ecall] NF _ _ _ _ eq_refl eq_refl echeck_rd1). Qed.

Section Seg3.

Variables (bc : list cell) (lv : positive).
Definition res : sv := SVar lv.
Definition lastb : sv := ltac2:(tb__ "0|0|
S7aS7aS34S6bA2SfN1A1A2").
Definition FR : list sprop := ltac2:(tb__ "0|0|
S7S10S0S10S13S6bS32A2S3S10A1A3S45A3").
Definition Fpos : list sprop := ltac2:(tb__ "0|0|
S0S10S13SfZ1A1S6bA2S0S10S13S7aS4cS6bA2S35A2S0S10S13S6bS35A2S3S10A1A3A3A3").

Definition tv (k : nat) : sv := SVar (Pos.of_nat (150 + k)).
Definition mid_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|12|
S90S91S7S6S2SdA2M0S0G0S1S2SdU1M1S6aG1A1A4S0G0S1S2SdU2S57A4S0G0S1S2SdU5M2S6aG2A1A4S0G0S1S2SdU6M3S6aG3A1A4S0G0S1S2SdU7M4S6aG4A1A4S0G0S1S2SdU8SePaA1A4S0G0S1S2SdU9S34A4S0G0S1S2SdUaM5S6aG5A1A4S0G0S1S2SdUbM6S6aG6A1A4S0G0S1S2SdUcM7S6aG7A1A4S0G0S1S2SdUdM8S6aG8A1A4S0G0S1S2SdUeM9S6aG9A1A4S0G0S1S2SdUfMaS6aGaA1A4S0G0S1S2SdU10MbS6aGbA1A4S0G0S1S2SdU11McS6aGcA1A4S0G0S1S2SdU12MdS6aGdA1A4S0G0S1S2SdU13SfZ3A1A4S0G0S1S2SdU14SfZ1A1A4S0G0S1S2SdU1cMeS6aGeA1A4S0G0S1S2SdU1dMfS6aGfA1A4S0G0S1S2SdU1eM10S6aG10A1A4S0G0S1S2SdU1fM11S6aG11A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition mid_state (pc : Z) (l : list (nat * sv)) (facts : list sprop) : axst := ltac2:(tb__ "0|1|
S88S1aVpc;S79Vl;A1S8fS19S8SdA1S40S54S3S11A1M0Vbc;G0A4S7S10Vfacts;S71A3PbeS9A9S3fA2").

Definition E_pos : axst := ltac2:(tb__ "0|1|
S6eS96S0S6S2SdA2M0S1S2SdU1SfS94A1A4S0G0S1S2SdUaS6bA4S0G0S1S2SdUcS32A4S0G0S1S2SdU12S32A4S3G0A1A3A3A3A3S0S10S1eS1dS84SfZ0A1S6bA3A1S3S10A1A3A3").
Definition T_pos_0 : axst := ltac2:(tb__ "0|1|
S6eS96S0S6S2SdA2M0S1S2SdU1SfS94A1A4S0G0S1S2SdUaS6bA4S0G0S1S2SdUcS32A4S0G0S1S2SdU12S32A4S3G0A1A3A3A3A3S3S10A1A3").
Definition T_pos : axst := ax_add_facts Fpos T_pos_0.

Definition s4v : sv := add (SVar 10) (SLit (-2120)).
Definition E_reg : axst := ltac2:(tb__ "0|1|
S6eSa0S0S6S2SdA2M0S1S2SdU1SfS9aA1A4S0G0S1S2SdUaS34A4S0G0S1S2SdUbS6bA4S0G0S1S2SdU12S6bA4S0G0S1S2SdU14S75A4S3G0A1A3A3A3A3A3S6fA3").

Definition cur : sv := SVar 140. Definition gl : sv := SVar 141. Definition gs : sv := SVar 142.
Definition F8of (g : sv) (gi : positive) (e : sv) : list sprop := ltac2:(tb__ "0|1|
S0S10S13S7dVg;A1M0Ve;A2S0S10S13Ve;S7aG0SfZ7A1A2A2S0S10S13Vg;SfS81S80Z2Z3dA2Z1A2A1A2S3S10A1A3A3A3").
Definition F_L : list sprop := ltac2:(tb__ "0|1|
S7S10S0S10S13S38S7dS6cA1M0A2S0S10S13S7aG0SfZ8A1A2S7aS38S35A2A2S0S10S20G0G0A2S0S10S13S6cSfS81S80Z2Z3dA2Z1A2A1A2S0S10S21S6cS6dA2S3S10A1A3A3A3A3A3S70S6dP8dS74A3A3").
Definition l_regs (a1 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S2SdA2M0S1S2SdUaS6bA4S0G0S1S2SdUbVa1;A4S0G0S1S2SdUcS7bS6dA1A4S0G0S1S2SdU12S32A4S0G0S1S2SdU14S75A4S3G0A1A3A3A3A3A3").
Definition CL_0 : axst := ltac2:(tb__ "0|0|
S6eS93S73S7bS6cA1A1S6fA3").
Definition CL : axst := ax_add_facts F_L CL_0.
Definition E_L_in : axst := ltac2:(tb__ "0|1|
S6eS93S73S7bS72A1M0A1S7S10S70S72P8eS34A3S7S10S70S6dP8dS74A3S7S10S0S10S1eS1dS85G0S7bS6dA1A3A1S3S10A1A3S6fA3A3A3A3").
Definition E_L_bk : axst := ltac2:(tb__ "0|1|
S6eS93S73S7fS6cZ1A2M0A1S7S10S77S7S10S0S10S1dS86G0S7bS6dA1A3S3S10A1A3S6fA3A3A3").

Definition P_rd : axst := ltac2:(tb__ "0|2|
S88S1aS97S90S92P96A1S0S6S2SdA2M0S1S2SdUaS6bA4S3G0A1A3A2S8fS19S8SdA1S40S3S11A1M1G1Vbc;G1A4S71PbeS9A9S3fA2").
Definition Posts_rd : list leafA := ltac2:(tb__ "0|0|
S0S26S29S78Sa2A2S3S26A1A3").

Definition Tr1 (s : wsub) (R : list sobj) : axst := ltac2:(tb__ "0|0|
S2fS7S10S6fS71A3S9cVs;S8dS7cS76VR;A5A2").

Definition s_pos : wsub := [].
Definition s_L_in : wsub := ltac2:(tb__ "0|1|
S0S6S22SdA2M0S1S22SdP8cS72A4S3G0A1A3").
Definition s_L_bk : wsub := ltac2:(tb__ "0|1|
S0S6S22SdA2M0S1S22SdP8cS7aS6cSfZ1A1A2A4S3G0A1A3").
End Seg3.

Definition cutpcs_rd : list Z := ltac2:(tb__ "0|0|
S0S23S96S0S23Sa0S0S23S93S3S23A1A3A3A3").

Definition s_reg_k : wsub := ltac:(let x := eval vm_compute in ((16%positive, vLb) :: infer_sub 1 (ax_S (E_reg [] 100)) (ax_S Pre_rip_lo)) in exact x).
Definition R_reg_k : list sobj := ltac:(let x := eval vm_compute in (match entails_frA (E_reg [] 100) Pre_rip_lo s_reg_k with Some R => R | None => [] end) in exact x).
Definition T_rd_k : axst := ltac2:(tb__ "0|0|
S2fS0S10S13SeP64A1S32A2S3S10A1A3Sa5S3bA1A2").
Definition cuts_k : list axst := ltac2:(tb__ "0|2|
S0S24S52S0S24S4aS3S11A1M0P64M1A2S0S24S4bG0G1S42S3eA4S0S24S47G0G1A2S3S24A1A3A3A3A3").
Definition exits_k : list axst := ltac2:(tb__ "0|2|
S0S24S48S3S11A1M0P64M1A2S0S24S3cG0G1A2S0S24S33G0G1A2S0S24S3aG0G1A2S0S24S39G0G1A2S3S24A1A3A3A3A3A3").

Definition hc : list cell := ltac2:(tb__ "0|0|
S0S11S12SfZ0A1Z4SeP64A1A3S3S11A1A3").
Definition s_reg_h : wsub := ltac:(let x := eval vm_compute in ((16%positive, vLb) :: infer_sub 1 (ax_S (E_reg hc 101)) (ax_S Pre_rip_lo)) in exact x).
Definition R_reg_h : list sobj := ltac:(let x := eval vm_compute in (match entails_frA (E_reg hc 101) Pre_rip_lo s_reg_h with Some R => R | None => [] end) in exact x).
Definition T_rd_h : axst := ltac2:(tb__ "0|0|
S2fS0S10S13SeP65A1S32A2S3S10A1A3Sa6S3bU2S34SfZ0A1S32A5A2").
Definition cuts_h : list axst := ltac2:(tb__ "0|1|
S0S24S51S0S24S4aS31P65M0A2S0S24S4bS31G0S41S3dA4S0S24S47S31G0A2S3S24A1A3A3A3A3").
Definition exits_h : list axst := ltac2:(tb__ "0|1|
S0S24S48S31P65M0A2S0S24S3cS31G0A2S0S24S33S31G0A2S0S24S3aS31G0A2S0S24S39S31G0A2S3S24A1A3A3A3A3A3").

Definition T_rd_d : axst := ltac2:(tb__ "0|0|
Sa4S3bSfS81S80Z2Z40A2Z15A2A1A2").
Definition P_rd_d : axst := ltac2:(tb__ "0|2|
S88S1aS97S90S92P96A1S0S6S2SdA2M0S1S2SdUaSfS81S80Z2Z40A2Z1A2A1A4S3G0A1A3A2S8fS19S8SdA1S40S3S11A1M1G1G1S0S11S12SfNa4A1Z4SfZ15A1A3G1A3A4S45PbeS9A9S3fA2").
Definition Posts_rd_d : list leafA := ltac2:(tb__ "0|0|
S0S26S29S49Sa2A2S3S26A1A3").

Lemma fr_reg_k : ltac2:(tb__ "0|1|
S2aScSaS14A1M0A1S9eS33S3S11A1P64A2S8dS42A3SbG0S3eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_reg_k : ltac2:(tb__ "0|0|
S2aS4S9dS33S3S11A1P64A2S8dS42S3eS9fS26S24S28Sa1A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_reg_h : ltac2:(tb__ "0|1|
S2aScSaS14A1M0A1S9eS33S31P65A2S8dS41A3SbG0S3dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_reg_h : ltac2:(tb__ "0|0|
S2aS4S9dS33S31P65A2S8dS41S3dS9fS26S24S28Sa1A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition vcuts_rd (bc : list cell) (lv : positive) (T0 : axst) (s : wsub) (R : list sobj) : list vnodeA := ltac2:(tb__ "0|1|
S0S2cS2dVT0;Zc8SfZ0A1M0A3S0S2cS2dS4aVbc;Vlv;A2Z95G0A3S0S2cS2dS4bVbc;Vlv;Vs;VR;A4Z4fSfS80Z2Z3dA2A1A3S0S2cS2dS47Vbc;Vlv;A2Z64S53A3S3S2cA1A3A3A3A3").
Definition vexits_rd (bc : list cell) (lv : positive) : list vnodeA := ltac2:(tb__ "0|4|
S0S2cS2dS48Vbc;Vlv;A2Z0M0SfS81S80Z2M1Z40A2Z1M2A2A1A3S0S2cS2dS3cVbc;Vlv;A2Z96SfG0A1A3S0S2cS2dS33Vbc;Vlv;A2Z50SfS80G1Z3dA2A1A3S0S2cS2dS3aVbc;Vlv;A2Z65M3S64A3S0S2cS2dS39Vbc;Vlv;A2G3S7aS53SfG2A1A2A3S3S2cA1A3A3A3A3A3").
Definition vcuts_k : ltac2:(tb__ "0|0|
SaS2cA1") := ltac2:(tb__ "0|0|
S58S3S11A1P64S52S42S3eA5").
Definition vexits_k := vexits_rd [] 100.
Definition vcuts_h : ltac2:(tb__ "0|0|
SaS2cA1") := ltac2:(tb__ "0|0|
S58S31P65S51S41S3dA5").
Definition vexits_h := vexits_rd hc 101.
Lemma echeck_k : ltac2:(tb__ "0|0|
S2aS4Sa3S87S36S46P65S67S69A6S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma echeck_h : ltac2:(tb__ "0|0|
S2aS4Sa3S87S36S46P66S66S68A6S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma echeck_d : ltac2:(tb__ "0|3|
S2aS4S30S87S36S3S23A1S8eS0S2cS2dS50Z1SfZ0M0A1M1A3S3S2cA1M2A3S0S2cS2dS49G0G1A3G2A3A6S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma check_k : ltac2:(tb__ "0|0|
S2aS4S2eS87S36S46P65S61S63A6S5A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELR cutpcs_rd 101 vcuts_k vexits_k cuts_k exits_k eq_refl eq_refl echeck_k). Qed.
Lemma check_h : ltac2:(tb__ "0|0|
S2aS4S2eS87S36S46P66S60S62A6S5A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELR cutpcs_rd 102 vcuts_h vexits_h cuts_h exits_h eq_refl eq_refl echeck_h). Qed.
Lemma check_d : ltac2:(tb__ "0|1|
S2aS4S2eS87S36S3S23A1S8eS0S24S50S3S24A1M0A3S0S24S49G0A3A6S5A3").
Proof. exact (check_cfgA_of_ecfgA segs FUELR [] NF [mkVNA T_rd_d 1 (SLit 0)] [mkVNA P_rd_d 0 (SLit 0)] _ _ eq_refl eq_refl echeck_d). Qed.

Lemma ent_pos_k : ltac2:(tb__ "0|2|
S2aS4S25S3cS3S11A1M0P64M1A2S4fG0G1A2S3S6S22SdA2A1A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_L_in_k : ltac2:(tb__ "0|2|
S2aS4S25S3aS3S11A1M0P64M1A2S43G0G1A2S56A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_L_bk_k : ltac2:(tb__ "0|2|
S2aS4S25S39S3S11A1M0P64M1A2S43G0G1A2S55A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_pos_h : ltac2:(tb__ "0|1|
S2aS4S25S3cS31P65M0A2S4fS31G0A2S3S6S22SdA2A1A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_L_in_h : ltac2:(tb__ "0|1|
S2aS4S25S3aS31P65M0A2S43S31G0A2S56A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_L_bk_h : ltac2:(tb__ "0|1|
S2aS4S25S39S31P65M0A2S43S31G0A2S55A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_rd : wsub_id_below ([] : wsub) 102 = true /\ wsub_id_below s_L_in 102 = true /\ wsub_id_below s_L_bk 102 = true
               /\ wsub_id_below ([] : wsub) 101 = true /\ wsub_id_below s_L_in 101 = true /\ wsub_id_below s_L_bk 101 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma Fpos_below : ltac2:(tb__ "0|1|
S2bS2aS4S8cS10S18PbeA1M0S37P64A1A3S5A3S2aS4S8cS10G0S37P65A1A3S5A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma FL_below : ltac2:(tb__ "0|1|
S2bS2aS4S8cS10S18PbeA1M0S4dP64A1A3S5A3S2aS4S8cS10G0S4dP65A1A3S5A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma FT_below_rd : ltac2:(tb__ "0|2|
S2bS2aS4S8cS10S18P65M0A1S7S10S37P64M1A1S44G1A1A3A3S5A3S2aS4S8cS10S18P66A1S7S10S37G0A1S44G0A1A3A3S5A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma FT_below_Tr : ltac2:(tb__ "0|2|
S2bS2aS4S8cS10S18S1fS27S9cS42S8dS7cS33S3S11A1P64M0A2S3eA5A1A1A1S7S10S37G0A1S44G0A1A3A3S5A3S2aS4S8cS10S18S1fS27S9cS41S8dS7cS33S31P65M1A2S3dA5A1A1A1S7S10S37G1A1S44G1A1A3A3S5A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Icpt_read.

(* [comment removed for export] *)
Module DrvFpStates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "option"; "true"; "bool"; "Some"; "list"; "pair"; "app"; "false"; "prod"; "S"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "SLit"; "sobj"; "sv"; "ss_next"; "ss_objs"; "cell"; "mkObj"; "SAlu"; "SVar"; "ob_hi"; "ob_lo"; "sprop"; "ss_pc"; "DList"; "DRom"; "DUnknown"; "dflt_writable"; "is_arr"; "ob_base"; "ob_cells"; "ob_dflt"; "ss_facts"; "ss_lenient"; "ss_regs"; "swf"; "valuation"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "XMerge"; "XRebase"; "XSelect"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fn.DrvFpStates"; "S6_r"; "O8_r"; "W_r"; "s_r"; "CUTS_FP"; "FUEL_FP"; "F_r"; "G3_r"; "Tf_r"; "C_r"; "G1_r"; "R_r"; "T_r"; "BL_r"; "Cs_r"; "G2u_r"; "sp_r"; "EX_r"; "G2_r"; "O_b2e"; "XP1"; "XP2"; "splits_fp"; "unk_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "sym_runA"; "ax_base"; "mkLeafA"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates"; "obindW"; "axc"; "junk_fw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "nth"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err.WLerrS"; "Pre_wl2"; "D"; "@Stdlib.Lists.List"; "nth_error"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface"; "Pre_ref"; "facts_fp"; "fp_ret"; "MSG_REF"; "P_ref"; "X_ref"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "FERR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "beval"; "cells_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "state_nolist"; "@Stdlib.ZArith.BinInt.Z"; "add"; "sub"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "state_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListObj"; "obj_to_list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.PArith.BinPos.Pos"; "add"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFpIface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition CUTS_FP : list Z := ltac2:(tb__ "0|0|
S0S2bZd9ad4S0S2bS61S2S2bA1A3A3").
Definition FUEL_FP : nat := 4000%nat.

Definition O_b2e : sobj := ltac2:(tb__ "0|1|
S16S10Z0A1M0G0G0S2S15A1S1eP6A1A5").

Definition splits_fp (S : sstate) : option sstate := ltac2:(tb__ "0|0|
S52SfSfS49VS;U0S10N248A1A3SfS52SfSfS49R1U1S10N228A1A3SfS52SfSfS49R1U2S10N1d0A1A3SfS52SfSfS49R1U3S10N1aaA1A3SfS52SfSfS49R1U5S10S6eS65Z78A2A1A3SfS49R1U6S10S6eS65Z7cA2A1A3LS5;A4LS4;A4LS3;A4LS2;A4LS1;A4").
Definition finish_fp (S6 : sstate) : sstate := app_obj (obj_to_list S6 3 5) O_b2e.
Definition wl2_sub_head : wsub := ltac2:(tb__ "0|2|
S0SbS2aS12A2M0S8S2aS12PcS17S5dS18PaA1S10N1d0A1A3A4S0G0S8S2aS12PdS10Z26A1A4S0G0S8S2aS12PeS10Z0A1M1A4S0G0S8S2aS12PfG1A4S2G0A1A3A3A3A3").

Definition XP1 : list xform := ltac2:(tb__ "0|0|
S0S2cS2fS0S1U0S0S1U1S0S1U3S0S1U4S0S1U5S0S1U6S0S1U7S0S1U8S0S1U9S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS0S1UfS0S1U2S2S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S2S2cA1A3").
Definition drop1 (S : sstate) : sstate := ltac2:(tb__ "0|0|
S6cVS;S56S11UfS14VS;A1A3A2").

Definition unk_obj (o : sobj) : sobj := ltac2:(tb__ "0|0|
S16S22Vo;A1S1aVo;A1S19Vo;A1S2S15A1S1fA5").
Definition unlist_at (S : sstate) (i : nat) : sstate := ltac2:(tb__ "0|1|
S3S11A1SfLx;S5cS11S14VS;A1M0Vi;A3S11S6cVS;S9S11S56S11Vi;G0A3S0S11S48R1A1S59S11ScVi;A1G0A3A3A3A2Lo;VS;X3x2").
Definition XP2 : list xform := ltac2:(tb__ "0|4|
S0S2cS2eU0M0A1S0S2cS2eU1M1A1S0S2cS2fS0S1U3S0S1G0S0S1U4S0S1G1S0S1U5S0S1U6S0S1U2S0S1U7S0S1U8S0S1U9S0S1UaS0S1UbS0S1UcS0S1UdS0S1UeS2S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S2cS2dG0A1M2S0S2cG2S0S2cG2S0S2cG2S0S2cS2dG1A1M3S0S2cG3S2S2cA1A3A3A3A3A3A3A3A3A3").
Definition post_sub_fp (S : sstate) : wsub := ltac2:(tb__ "0|0|
S57S1SbS2aS12A2S1S8S2aS12S78P64S79R1A1A2S58S12R1S27VS;A1S10Z0A1A4A4Lr;S54A4").

Definition runW_r__R : option (list leafA) := ltac2:(tb__ "0|0|
S4dS55S36S35S5fS4A5").
Local Strategy expand [runW_r__R].
Definition W_r : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1W Pre_ref (ro1__)))) runW_r__R).
Lemma runW_r : ltac2:(tb__ "0|1|
SdS3S7S4bA1M0A1S4dS55S36S35S5fS4A5S6G0S0S4bS4fS33S6bA2S2S4bA1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) runW_r__R <: runW_r__R = Some [mkLeafA W_r RsCut]). Qed.
Definition S6_r : sstate := Eval vm_compute in (match splits_fp (ax_S W_r) with Some s => s | None => ax_S W_r end).
Lemma splits_r : ltac2:(tb__ "0|0|
SdS3SfA1S47S4aS33A1A1S6SfS31A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Cs_r : sstate := Eval vm_compute in (finish_fp S6_r).
Lemma finish_r : finish_fp S6_r = Cs_r. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_r : axst := ax_setS W_r Cs_r.
Definition s_r : wsub := Eval vm_compute in (wl2_sub_head ++ infer_sub 10 Cs_r (ax_S WLerrS.Pre_wl2)).
Definition R_r : list sobj := Eval vm_compute in (match entails_frA C_r WLerrS.Pre_wl2 s_r with Some R => R | None => [] end).
Lemma efr_r : ltac2:(tb__ "0|1|
SdS3S7S11A1M0A1S74S3aS5aS34A3S6G0S3cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_r : ltac2:(tb__ "0|0|
SdS5S73S3aS5aS34S3cS0S4cS5bS2S4cA1A3A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_r : axst := Eval vm_compute in (import_postA s_r WLerrS.Pre_wl2 WLerrS.D C_r R_r).
Lemma T_r_eq : ltac2:(tb__ "0|0|
SdS4cS75S34S5aS5bS3aS3cA5S3dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Tf_r : axst := Eval vm_compute in (ax_add_facts facts_fp T_r).
Lemma Tf_r_eq : ltac2:(tb__ "0|0|
SdS4cS72S60S3dA2S39A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition runF_r__R : option (list leafA) := ltac2:(tb__ "0|0|
S4dS55S36S35S39S4A5").
Local Strategy expand [runF_r__R].
Definition F_r : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1W Tf_r (ro2__)))) runF_r__R).
Lemma runF_r : ltac2:(tb__ "0|1|
SdS3S7S4bA1M0A1S4dS55S36S35S39S4A5S6G0S0S4bS4fS37S6bA2S2S4bA1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) runF_r__R <: runF_r__R = Some [mkLeafA F_r RsCut]). Qed.
Definition G1_r : sstate := Eval vm_compute in (match apply_xforms (ax_S F_r) XP1 with Some s => s | None => ax_S F_r end).
Lemma xp1_r : ltac2:(tb__ "0|0|
SdS3SfA1S30S4aS37A1S45A2S6SfS3bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition G2_r : sstate := Eval vm_compute in (drop1 G1_r).
Lemma drop1_r : drop1 G1_r = G2_r. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition G2u_r : sstate := Eval vm_compute in (unlist_at G2_r 1).
Lemma unlist_r : unlist_at G2_r 1 = G2u_r. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition G3_r : sstate := Eval vm_compute in (match apply_xforms G2u_r XP2 with Some s => s | None => G2u_r end).
Lemma xp2_r : ltac2:(tb__ "0|0|
SdS3SfA1S30S40S46A2S6SfS38A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sp_r : wsub := Eval vm_compute in (post_sub_fp G3_r).
Lemma ent_r : ltac2:(tb__ "0|0|
SdS5S51S53S38A1S63S41A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition EX_r : list sprop := Eval vm_compute in (firstn (length (ss_facts (ax_S W_r)) - 4)%nat (ss_facts (ax_S W_r))).
Lemma shapeW_r : ltac2:(tb__ "0|1|
SeSdS2aS13S4aS33A1M0A1P74A3SeSdS7SbS12S12A2A1S50S33A1S64A3SeSdS12S4eS33A1S10S5eA1A3SeSdS7S1bA1S25G0A1S9S1bS42S60A3A3SdS2bS1cG0A1Zd9ad4A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition O8_r : sobj := Eval vm_compute in (nth 3 (ss_objs S6_r) O_b2e).
Definition BL_r : list bexp := Eval vm_compute in (match cells_bytes (ob_cells O8_r) (SLit (-464)) 0 38 with Some bl => bl | None => [] end).
Lemma shapeC_r : ltac2:(tb__ "0|8|
SeSdS5S6dS31A1S4A3SeSdS5S71P5M0S31A2SaA3SeSdS3S11A1S5cS11S14S31A1U3M1A3S6S11S32A2A3SeSdS12S1aS32A1S10N1d0M2A1M3A3SeSdS12S19S32A1S10N1aaM4A1A3SeSdS5S20S24S32A1M5A1S4A3SeSdS5S21G5A1SaA3SeSdS3S7S66A1M6A1S68S23S32A1G3Z0S70S6fG4G2A2A1A4S6G6S3eA2A3SeSdS5S28S3fA1S4A3SeSdS2aS13S3fA1P74M7A3SeSdS2aS13S31A1G7A3SdS2aS13S76S31G1G0A3A1G7A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma BL_r_val : ltac2:(tb__ "0|1|
S29SdS7S7aQ8A1M0A1S57S66G0S67R1A1S3eA4S62A3Fr;").
Proof. intros r. reflexivity. Qed.
Lemma shapeS_r : ltac2:(tb__ "0|0|
SeSdS12S69S34PdA2S10Z26A1A3SdS12S69S34PfA2S10Z0A1A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeT_r : ltac2:(tb__ "0|2|
SeSdS2aS13S4aS3dA1A1P8dM0A3SeSdS5S26S4aS39A1M1A1SaA3SdS2aS13G1A1G0A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeF_r : ltac2:(tb__ "0|3|
SeSdS2bS1cS4aS37A1M0A1S61A3SeSdS2aS13G0A1P8dM1A3SeSdS12S4eS37A1S10S5eA1A3SeSdS7S11A1S14S3bA1M2S9S11S56S11UfG2A3S0S11S44S2S11A1A3A3A3SeSdS2aS13S3bA1G1A3SeSdS2aS13S40A1G1A3SeSdS2aS13S38A1G1A3SeSdS5S6dS38A1S4A3SeSdS5S6aS41S77A2S4A3SdS3S11A1S5cS11S14S43A1U1A3S6S11S16S17S5dS18PaA1S10N1d0A1A3S10Z0A1S10Z26A1S2S15A1S1dP5A1A5A2A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End DrvFpStates.

