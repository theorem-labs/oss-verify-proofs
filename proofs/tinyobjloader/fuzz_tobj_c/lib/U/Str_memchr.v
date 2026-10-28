(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "prod"; "bool"; "true"; "list"; "false"; "None"; "app"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "holds"; "SLit"; "valuation"; "SVar"; "sstate"; "SAlu"; "ss_facts"; "rl"; "rw"; "SPUle"; "SPBranch"; "eval"; "SPNot"; "sobj"; "SPEq"; "FcsrFrm0"; "agree_below"; "mkSS"; "sprop_below"; "ss_next"; "DList"; "cell"; "mkObj"; "ss_lenient"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr"; "v120"; "mc_state"; "v122"; "tf"; "inv"; "curs"; "r1"; "BNZ_eq"; "NOZ"; "s_f2"; "s_f3"; "BNZ_ne"; "BYTE"; "C3_0"; "FirstNul"; "HI"; "P_ret_0"; "Pre_memchr0"; "T_1j"; "T_23"; "T_23w"; "T_b1"; "T_b2"; "T_b3"; "T_f2"; "T_f3"; "base_facts"; "c1"; "inc1"; "svals"; "BZ_eq"; "BZ_ne"; "C1M"; "C1_0"; "O_str"; "X_2"; "X_3e"; "X_3n"; "X_j"; "r8"; "s_1j"; "s_23"; "s_23w"; "s_b1"; "s_b2"; "s_b3"; "C1"; "C2"; "C2_0"; "C3"; "C84"; "C84_0"; "C84b"; "FUELM"; "Posts_memchr0"; "c8"; "cutpcs_mc"; "cuts_mc"; "inc8"; "C84b_0"; "HZT"; "P_ret"; "WRD"; "exits_mc"; "step1_vals"; "step8_vals"; "vcuts_mc"; "vexits_mc"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "iff"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "mkVN"; "add_facts"; "check_cfg"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "modulo"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "two62"; "setregs"; "cut_regs"; "post_regs"; "pre_regs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_get"; "wsub_id_below"; "wsub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes"; "nthb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_EQ"; "ALU_SLTU"; "ALU_AND"; "ALU_OR"; "ALU_SUB"; "BC_LTU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.StrAddr"; "memchr_ret"; "memchr_L3"; "memchr_J84"; "memchr_L1"; "memchr_L2"; "memchr_entry"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "list_set"; "mkLeaf"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue"; "check_ecfgI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memchr.ZFacts"; "invZ"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymBytes.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv HasZero StrBytes CfgGlue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Code.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import StrAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition FUELM : nat := 400%nat.

Definition O_str : sobj := ltac2:(tb__ "0|0|
S23S10PcA1SeZ0A1S10P11A1S3S22A1S21P3A1A5").
Definition base_facts : list sprop := ltac2:(tb__ "0|6|
S0ScS17S91S10P10A1M0S10PeA1M1A3S0ScS16S12S8aG0SeZ8A1M2A3S10P11A1M3A2S0ScS16G2G3A2S0ScS16G3SeS80A1M4A2S0ScS16G1G4A2S0ScS16SeZ1A1S10PcA1M5A2S0ScS16G5G4A2S3ScA1A3A3A3A3A3A3A3").
Definition Pre_memchr0 : sstate := ltac2:(tb__ "0|1|
S1eS99S81S84S0S4S1SbA2M0S2S1SbUbSeZ0A1A4S3G0A1A3A2S7fS1cS9SbA1S0S1aS47S3S1aA1A3S3fS7eS8A9").

Definition C1M : Z := 72340172838076672.
Definition HI : Z := 9259542123273814144.

Definition v120 : sv := SVar 120.
Definition v122 : sv := SVar 122.
Definition curs (e : sv) : sv := SAlu ALU_ADD (SVar 12) e.
Definition inv (c r : sv) : list sprop := ltac2:(tb__ "0|3|
S0ScS16Vc;S10P10A1A2S0ScS16S12S8aVc;SeZ8A1A3S10P11A1A2S0ScS16Vc;SeS80A1M0A2S0ScS16S10PeA1M1S12S8aVc;Vr;A3M2A2S0ScS16G2G1A2S0ScS16Vr;G0A2S3ScA1A3A3A3A3A3A3").

Definition mc_state (pc : Z) (regs : list (nat * sv)) (facts : list sprop) (nx : positive) : sstate := ltac2:(tb__ "0|1|
S1eVpc;S81S82S7eA1SaS4S1SbA2M0S0G0S2S1SbUbSeZ0A1A4S3G0A1A3Vregs;A3A2S7fS1cS9SbA1S0S1aS47S3S1aA1A3SaScVfacts;S3fA3Vnx;S8A9").

Definition C1_0 : sstate := ltac2:(tb__ "0|2|
S26S97S0S4S1SbA2M0S2S1SbUaS2aS25A1A4S0G0S2S1SbUcS27A4S0G0S2S1SbUfS2aS12S8aS25SeZ1A1M1A3A1A4S0G0S2S1SbU10G1A4S3G0A1A3A3A3A3S3ScA1P87A4").
Definition C84_0 : sstate := ltac2:(tb__ "0|1|
S26S96S0S4S1SbA2M0S2S1SbUaS2aS25A1A4S0G0S2S1SbUcS27A4S0G0S2S1SbUeS12S8dSeZ0A1S27A3A4S3G0A1A3A3A3S3ScA1P87A4").
Definition C2_0 : sstate := ltac2:(tb__ "0|1|
S26S98S0S4S1SbA2M0S2S1SbUaS2aS25A1A4S0G0S2S1SbUcS27A4S0G0S2S1SbUdSeS45A1A4S0G0S2S1SbUeSeS34A1A4S0G0S2S1SbUfSeZ0A1A4S0G0S2S1SbU10SeZ7A1A4S3G0A1A3A3A3A3A3A3S3ScA1P87A4").
Definition C3_0 : sstate := ltac2:(tb__ "0|1|
S26S95S0S4S1SbA2M0S2S1SbUaS2aS25A1A4S0G0S2S1SbUdS27A4S3G0A1A3A3S3ScA1P87A4").

Definition C84b_0 : sstate := ltac2:(tb__ "0|1|
S26S96S0S4S1SbA2M0S2S1SbUaS2aS25A1A4S0G0S2S1SbUcS27A4S0G0S2S1SbUeSeZ1A1A4S3G0A1A3A3A3S3ScA1P87A4").
Definition C1 : sstate := ltac2:(tb__ "0|0|
S74S29S25S27A2S46A2").
Definition C84 : sstate := ltac2:(tb__ "0|0|
S74S29S25S27A2S58A2").
Definition C84b : sstate := ltac2:(tb__ "0|0|
S74S29S25S27A2S60A2").
Definition C2 : sstate := ltac2:(tb__ "0|0|
S74S29S25S27A2S55A2").
Definition C3 : sstate := ltac2:(tb__ "0|0|
S74S29S25S27A2S32A2").

Definition BYTE (e : sv) : sv := SExt false 8 (SLBytes 3 e 1).
Definition WRD (e : sv) : sv := SLBytes 3 e 8.
Definition BZ_eq (e : sv) : sprop := ltac2:(tb__ "0|0|
S17S8cS31Ve;A1SeZ0A1A3").
Definition BNZ_eq (e : sv) : sprop := ltac2:(tb__ "0|0|
S19S17S8cS31Ve;A1SeZ0A1A3A1").
Definition BNZ_ne (e : sv) : sprop := ltac2:(tb__ "0|0|
S17S8bS31Ve;A1SeZ0A1A3").
Definition BZ_ne (e : sv) : sprop := ltac2:(tb__ "0|0|
S19S17S8bS31Ve;A1SeZ0A1A3A1").
Definition HZT (e : sv) : sv := ltac2:(tb__ "0|1|
S12S8eS12S8fS12S90SeS45A1S63Ve;A1M0A3G0A3SeS34A1A3").
Definition NOZ (e : sv) : sprop := ltac2:(tb__ "0|0|
S19S17S8bS61Ve;A1SeS34A1A3A1").

Definition c1 : sv := ltac2:(tb__ "0|0|
S12S8aS2aS25A1SeZ1A1A3").
Definition r1 : sv := SAlu ALU_ADD v122 (SLit (-1)).
Definition c8 : sv := ltac2:(tb__ "0|0|
S12S8aS2aS25A1SeZ8A1A3").
Definition r8 : sv := SAlu ALU_ADD v122 (SLit (-8)).
Definition tf (f : sprop) : list sprop := ltac2:(tb__ "0|0|
S0ScVf;S29S25S27A2A3").

Definition T_b1 : sstate := ltac2:(tb__ "0|2|
S26S97S0S4S1SbA2M0S2S1SbUaS40A4S0G0S2S1SbUcS2bA4S0G0S2S1SbUfS12S8aS2aS12S8aS25SeZ1A1M1A3A1G1A3A4S0G0S2S1SbU10G1A4S3G0A1A3A3A3A3S28S2cS25A1A1P87A4").
Definition T_1j : sstate := ltac2:(tb__ "0|1|
S26S96S0S4S1SbA2M0S2S1SbUaS40A4S0G0S2S1SbUcS2bA4S0G0S2S1SbUeS12S8dSeZ0A1S2bA3A4S3G0A1A3A3A3S28S2cS25A1A1P87A4").

Definition T_b2 : sstate := ltac2:(tb__ "0|1|
S26S98S0S4S1SbA2M0S2S1SbUaS5cA4S0G0S2S1SbUcS4cA4S0G0S2S1SbUdSeS45A1A4S0G0S2S1SbUeSeS34A1A4S0G0S2S1SbUfSeZ0A1A4S0G0S2S1SbU10SeZ7A1A4S3G0A1A3A3A3A3A3A3S28S2dS25A1A1P87A4").
Definition T_23 : sstate := ltac2:(tb__ "0|1|
S26S95S0S4S1SbA2M0S2S1SbUaS40A4S0G0S2S1SbUdS2bA4S3G0A1A3A3S28S30S25A1A1P87A4").
Definition T_23w : sstate := ltac2:(tb__ "0|1|
S26S95S0S4S1SbA2M0S2S1SbUaS5cA4S0G0S2S1SbUdS4cA4S3G0A1A3A3S28S2dS25A1A1P87A4").

Definition T_b3 : sstate := ltac2:(tb__ "0|1|
S26S95S0S4S1SbA2M0S2S1SbUaS40A4S0G0S2S1SbUdS2bA4S3G0A1A3A3S28S2cS25A1A1P87A4").

Definition T_f2 : sstate := ltac2:(tb__ "0|1|
S26S94S0S4S1SbA2M0S2S1SbUaS2aS25A1A4S3G0A1A3S28S44S25A1A1P87A4").
Definition T_f3 : sstate := ltac2:(tb__ "0|1|
S26S94S0S4S1SbA2M0S2S1SbUaS2aS25A1A4S3G0A1A3S28S43S25A1A1P87A4").

Definition X_j : sstate := ltac2:(tb__ "0|2|
S26S94S0S4S1SbA2M0S2S1SbUaSeZ0A1M1A4S3G0A1A3S28S17S8cS12S8dG1S27A3G1A3A1P87A4").
Definition X_2 : sstate := ltac2:(tb__ "0|2|
S26S94S0S4S1SbA2M0S2S1SbUaSeZ0A1M1A4S3G0A1A3S0ScS17S8cS4cG1A3S28S2dS25A1A1A3P87A4").
Definition X_3e : sstate := ltac2:(tb__ "0|2|
S26S94S0S4S1SbA2M0S2S1SbUaSeZ0A1M1A4S3G0A1A3S0ScS19S17S8bS2bG1A3A1S28S2cS25A1A1A3P87A4").
Definition X_3n : sstate := ltac2:(tb__ "0|2|
S26S94S0S4S1SbA2M0S2S1SbUaSeZ0A1M1A4S3G0A1A3S0ScS19S17S8bS2bG1A3A1S28S30S25A1A1A3P87A4").

Definition P_ret_0 : sstate := ltac2:(tb__ "0|0|
S1eS94Sa1SbS83S7eA1UaS2aS10P8cA1A1A4S7fS1cS9SbA1S0S1aS47S3S1aA1A3S3fP8dS8A9").
Definition P_ret : sstate := ltac2:(tb__ "0|0|
S74S0ScS1bS10P8cA1S10P10A1A2S3ScA1A3S35A2").
Definition Posts_memchr0 : list leaf := ltac2:(tb__ "0|0|
S0S9fSa2S62Sa0A2S3S9fA1A3").

Definition cuts_mc : list sstate := ltac2:(tb__ "0|0|
S0S11S36S0S11S53S0S11S57S0S11S54S0S11S56S0S11S59S3S11A1A3A3A3A3A3A3").
Definition exits_mc : list sstate := ltac2:(tb__ "0|0|
S0S11S3aS0S11S37S0S11S3bS0S11S38S0S11S39S0S11S3cS0S11S3dS0S11S3eS0S11S4bS0S11S48S0S11S49S0S11S4aS3S11A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition cutpcs_mc : list Z := ltac2:(tb__ "0|0|
S0S70S97S0S70S96S0S70S98S0S70S95S3S70A1A3A3A3A3").

Lemma check_mc : ltac2:(tb__ "0|0|
S69S5S75S92S5aS5dS7eS5eS64A6S6A3").
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cuts_mc_strict : ltac2:(tb__ "0|0|
S69S5Sa4S11S24S5eA3S8A3").
Proof. vm_compute. reflexivity. Qed.

Definition s_b1 : wsub := infer_sub NF T_b1 C1_0.
Definition s_1j : wsub := infer_sub NF T_1j C84_0.
Definition s_b2 : wsub := infer_sub NF T_b2 C2_0.
Definition s_23 : wsub := infer_sub NF T_23 C3_0.
Definition s_23w : wsub := infer_sub NF T_23w C3_0.
Definition s_b3 : wsub := infer_sub NF T_b3 C3_0.
Definition s_f2 : wsub := infer_sub NF T_f2 P_ret_0.
Definition s_f3 : wsub := infer_sub NF T_f3 P_ret_0.

Lemma ent_b1 : ltac2:(tb__ "0|0|
S69S5S93S3aS46S50A3S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma ent_1j : ltac2:(tb__ "0|0|
S69S5S93S37S58S4dA3S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma ent_b2 : ltac2:(tb__ "0|0|
S69S5S93S3bS55S51A3S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma ent_23 : ltac2:(tb__ "0|0|
S69S5S93S38S32S4eA3S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma ent_23w : ltac2:(tb__ "0|0|
S69S5S93S39S32S4fA3S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma ent_b3 : ltac2:(tb__ "0|0|
S69S5S93S3cS32S52A3S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma ent_f2 : ltac2:(tb__ "0|0|
S69S5S93S3dS35S2eA3S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma ent_f3 : ltac2:(tb__ "0|0|
S69S5S93S3eS35S2fA3S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma id_b1 : ltac2:(tb__ "0|0|
S69S5S87S50S7eA2S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma id_1j : ltac2:(tb__ "0|0|
S69S5S87S4dS7eA2S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma id_b2 : ltac2:(tb__ "0|0|
S69S5S87S51S7eA2S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma id_23 : ltac2:(tb__ "0|0|
S69S5S87S4eS7eA2S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma id_23w : ltac2:(tb__ "0|0|
S69S5S87S4fS7eA2S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma id_b3 : ltac2:(tb__ "0|0|
S69S5S87S52S7eA2S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma id_f2 : ltac2:(tb__ "0|0|
S69S5S87S2eS7eA2S6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma id_f3 : ltac2:(tb__ "0|0|
S69S5S87S2fS7eA2S6A3"). Proof. vm_compute. reflexivity. Qed.

Definition svals (s : wsub) : list sv := ltac2:(tb__ "0|0|
S6fS71SbS86Vs;A1S0S71P78S0S71P7aS0S71P10S0S71P11S0S71PeS3S71A1A3A3A3A3A3A4").
Definition step1_vals : list sv := ltac2:(tb__ "0|0|
S0SbS12S8aS10P78A1SeZ1A1A3S0SbS12S8aS10P7aA1SeN1A1A3S0SbS10P10A1S0SbS10P11A1S0SbS10PeA1S3SbA1A3A3A3A3A3").
Definition step8_vals : list sv := ltac2:(tb__ "0|0|
S0SbS12S8aS10P78A1SeZ8A1A3S0SbS12S8aS10P7aA1SeN8A1A3S0SbS10P10A1S0SbS10P11A1S0SbS10PeA1S3SbA1A3A3A3A3A3").
Lemma vals_b1 : svals s_b1 = step1_vals. Proof. vm_compute. reflexivity. Qed.
Lemma vals_1j : svals s_1j = step1_vals. Proof. vm_compute. reflexivity. Qed.
Lemma vals_23 : svals s_23 = step1_vals. Proof. vm_compute. reflexivity. Qed.
Lemma vals_b3 : svals s_b3 = step1_vals. Proof. vm_compute. reflexivity. Qed.
Lemma vals_b2 : svals s_b2 = step8_vals. Proof. vm_compute. reflexivity. Qed.
Lemma vals_23w : svals s_23w = step8_vals. Proof. vm_compute. reflexivity. Qed.
Lemma vals_f2 : ltac2:(tb__ "0|1|
S69S4SbSbA2S2SbSbS86S2eP8cA2S86S2eP10M0A2A4S2SbSbS10P78A1S10G0A1A4A3"). Proof. vm_compute. reflexivity. Qed.
Lemma vals_f3 : ltac2:(tb__ "0|1|
S69S4SbSbA2S2SbSbS86S2fP8cA2S86S2fP10M0A2A4S2SbSbS10P78A1S10G0A1A4A3"). Proof. vm_compute. reflexivity. Qed.

Definition FirstNul (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S6aS69S70S89S14Vrho;P3A2M0S76Q40S15Vrho;P10A2A2M1A2Z0M2A3S70S6aS78G2R1A2S7bR1G1A2A2S6bS69S70S89G0R2A2G2A3A1F_;Fi;A2").

Lemma FirstNul_agree : ltac2:(tb__ "0|1|
S71SfSfSabP10R3A2S1dR4R3R2A3S33R4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof.
  intros n rho rho' Hn (A & B & C) [H1 H2]. unfold FirstNul.
  rewrite <- (A 16%positive Hn), <- B. split; assumption.
Qed.

Lemma two62_mod : ltac2:(tb__ "0|1|
S69S70S7cS80S7aZ2M0Z40A2A2S7aG0Z3eA2A3"). Proof. reflexivity. Qed.
Ltac zholds H := cbn [holds eval branch_taken v120 v122 curs c1 r1 c8 r8] in H; unfold bv_ltu, bv_eqb in H;
  rewrite ?add_lit_val, ?add_val, ?lit_unsigned, ?two62_mod in H; cbn [snorm Z.leb Z.ltb Z.sub Z.add Z.opp] in H;
  repeat match type of H with
    | negb _ = true => apply Bool.negb_true_iff in H
    | ~ negb _ = true => apply Bool.not_true_iff_false in H; apply Bool.negb_false_iff in H
    | Z.ltb _ _ = true => apply Z.ltb_lt in H
    | Z.ltb _ _ = false => apply Z.ltb_ge in H
    | Z.leb _ _ = true => apply Z.leb_le in H
    | Z.eqb _ _ = true => apply Z.eqb_eq in H
    | Z.eqb _ _ = false => apply Z.eqb_neq in H
    end.

Section ZFacts.
Variable rho : valuation.
Let c : Z := bv_unsigned (rw rho 120).
Let r : Z := bv_unsigned (rw rho 122).
Let z : Z := bv_unsigned (rw rho 16).
Let A : Z := bv_unsigned (rw rho 17).
Let n : Z := bv_unsigned (rw rho 14).

Definition invZ : Prop := ltac2:(tb__ "0|3|
S6aS78Vc;Vz;A2S6aS78S79Vc;Z8M0A2VA;A2S6aS78Vc;S7aZ2Z3eA2M1A2S6aS78Vn;S79Vc;Vr;A2M2A2S6aS78G2Vn;A2S6aS78Vr;G1A2S6aS7bVz;Vn;A2S6aS78S79Vz;G0A2VA;A2S6aS78VA;G1A2S78Vn;G1A2A2A2A2A2A2A2A2A2A2").

Lemma tf_facts : ltac2:(tb__ "0|0|
ScS6eScSdVrho;A1SaScS28R1A1S3fA3A3S6aSdVrho;R2A2SaaA2F_;Ff;").
Proof using .
  intros f HF. unfold tf, inv, base_facts in HF. cbn [app] in HF.
  repeat match type of HF with Forall _ (_ :: _) => apply Forall_cons_iff in HF as [? HF] end.
  split; [assumption|].
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (urange (rw rho 16)) as R6. pose proof (urange (rw rho 17)) as R7. pose proof (urange (rw rho 14)) as R4.
  unfold invZ. subst c r z A n.
  repeat match goal with H : holds rho _ |- _ => zholds H end.
  change (snorm 8) with 8 in *.
  change (8 mod 2 ^ 64) with 8 in *.
  rewrite Z.mod_small in H1 by lia. rewrite Z.mod_small in H3 by lia. rewrite Z.mod_small in H4 by lia.
  rewrite Z.mod_small in H7 by lia.
  repeat split; lia.
Qed.
End ZFacts.

Lemma inv_intro : ltac2:(tb__ "0|2|
SfS76Q40M0S15R1P78A2A2S70S76G0S15R2P7aA2A2S70S76G0S15R3P10A2A2S70S76G0S15R4P11A2A2S70S76G0S15R5PeA2A2S70S78R5R3A2S78S79R6Z8A2R3A2S78R7S7aZ2Z3eA2M1A2S78R4S79R8R7A2A2S78S79R9R8A2R5A2S78R9G1A2S78R8G1A2S6eScSdRdA1S29S25S27A2A3F_;F_;F_;F_;F_;F_;F_;Tn;TA;Tz;Tr;Tc;Frho';").
Proof.
  intros rho' c r z A n H1 H2 H3 H4 H5 H6 H7. subst c r z A n.
  pose proof (urange (rw rho' 120)) as R0. pose proof (urange (rw rho' 122)) as R2.
  pose proof (urange (rw rho' 17)) as R7. pose proof (urange (rw rho' 14)) as R4.
  unfold inv. repeat constructor; cbn [holds eval v120 v122]; rewrite ?add_lit_val, ?add_val, ?lit_unsigned, ?two62_mod;
    change (snorm 8) with 8; rewrite ?Z.mod_small by lia; lia.
Qed.

Lemma rw_sub : ltac2:(tb__ "0|0|
SfS88S71S69S77Q40A1S15S85R3R2A2R1A2S18R3S86R2R1A2A2A3Fi;Fs;Frho;").
Proof. reflexivity. Qed.
Lemma rl_sub : ltac2:(tb__ "0|0|
SfS88S69S71S7S77Q8A1A1F_;S14S85R2R1A2A1S14R2A1A3Fs;Frho;").
Proof. reflexivity. Qed.

Lemma svals_eq : ltac2:(tb__ "0|0|
S88SbSbSbSbSbS69S7SbA1S42R6A1S0SbR5S0SbR4S0SbR3S0SbR2S0SbR1S3SbA1A3A3A3A3A3A3S6aS69SbS86R7P78A2R6A3S6aS69SbS86R7P7aA2R5A3S6aS69SbS86R7P10A2R4A3S6aS69SbS86R7P11A2R3A3S69SbS86R7PeA2R2A3A2A2A2A2F_;Fe;Fd;Fc;Fb;Fa;Fs;").
Proof. intros s a b c d e H. unfold svals in H. cbn [map] in H. injection H as -> -> -> -> ->. repeat split; reflexivity. Qed.

Lemma holds_BNZ_eq : ltac2:(tb__ "0|0|
SfSbS6dSdR2S2cR1A1A2S6bS69S70S89S14R2P3A2S76Q40S18R2R1A2A2A2Z0A3A1A2Fe;Frho;").
Proof. intros. unfold BNZ_eq, BYTE. apply holds_BNZ'. Qed.
Lemma holds_BZ_eq : ltac2:(tb__ "0|0|
SfSbS6dSdR2S43R1A1A2S69S70S89S14R2P3A2S76Q40S18R2R1A2A2A2Z0A3A2Fe;Frho;").
Proof. intros. unfold BZ_eq, BYTE. apply holds_BZ'. Qed.
Lemma holds_BNZ_ne : ltac2:(tb__ "0|0|
SfSbS6dSdR2S30R1A1A2S6bS69S70S89S14R2P3A2S76Q40S18R2R1A2A2A2Z0A3A1A2Fe;Frho;").
Proof. intros. unfold BNZ_ne, BYTE. apply holds_BNZ. Qed.
Lemma holds_BZ_ne : ltac2:(tb__ "0|0|
SfSbS6dSdR2S44R1A1A2S69S70S89S14R2P3A2S76Q40S18R2R1A2A2A2Z0A3A2Fe;Frho;").
Proof. intros. unfold BZ_ne, BYTE. apply holds_BZ. Qed.
Lemma holds_NOZ_mc : ltac2:(tb__ "0|0|
SfSbSdR2S2dR1A1A2S1Sa5R1U8A2S6bS69S70S89S14R5P3A2S79S76Q40S18R5R4A2A2S7dR2A1A2A2Z0A3A1F_;Fk;F_;Fe;Frho;").
Proof.
  intros rho e H. apply StrBytes.holds_NOZ. unfold NOZ, HZT in H. unfold StrBytes.NOZ.
  change (StrBytes.WRD e) with (WRD e). fold C1M HI.
  cbn [holds branch_taken] in H |- *. destruct (bv_eqb _ _); [reflexivity|]. exfalso. apply H. reflexivity.
Qed.

Section WithFirstNul.
Variable rho0 : valuation.
Hypothesis FN : FirstNul rho0.
Let G : valuation -> Prop := ltac2:(tb__ "0|0|
SfS1dS7eVrho0;R1A3Lrho;").

Lemma G_FN : ltac2:(tb__ "0|0|
SfVG;R1A1S33R2A1F_;Frho;").
Proof using FN. intros rho Hg. eapply FirstNul_agree; [| exact Hg | exact FN]. reflexivity. Qed.
Lemma G_trans : ltac2:(tb__ "0|0|
SfSfVG;R2A1S1dS7eR3R2A3VG;R3A1F_;F_;Fr2;Fr1;").
Proof using rho0. intros r1 r2 H1 H2. eapply agree_below_trans; eauto. Qed.

Lemma glue_step1 : ltac2:(tb__ "0|1|
S88ScSfS69S7SbA1S42R3A1S65A3SfSdR1R4A2S6bS69S70S89S14R2P3A2S76Q40S15R2P78A2A2A2Z0M0A3A1F_;Frho;VG;R3A1S6eScSdR4A1S13S26G0S3S4S1SbA2A1S28R5A1P87A4A1A3S6eScSdS85R5R7A2A1S29S25S27A2A3F_;F_;F_;F_;Frho;Ff;Fs;").
Proof using FN.
  intros s f rho Hs Hf Hg HF. cbn [ss_facts mc_state] in HF.
  destruct (tf_facts rho f HF) as [Hff Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1]. pose proof (Hf rho Hff) as NZ.
  destruct (svals_eq s _ _ _ _ _ Hs) as (E120 & E122 & E16 & E17 & E14).
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (fn_step (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) ltac:(lia) NZ) as ST.
  apply inv_intro; rewrite !rw_sub, ?E120, ?E122, ?E16, ?E17, ?E14; cbn [eval];
    rewrite ?add_lit_val; cbn [snorm Z.leb]; change (snorm 1) with 1; change (snorm (-1)) with (-1);
    rewrite ?Z.mod_small by lia; lia.
Qed.

Lemma glue_step8 : ltac2:(tb__ "0|0|
S88SfS69S7SbA1S42R2A1S66A3VG;R2A1S6eScSdR3A1S13S26Z0S3S4S1SbA2A1S28S2dS25A1A1P87A4A1A3S6eScSdS85R4R5A2A1S29S25S27A2A3F_;F_;F_;Frho;Fs;").
Proof using FN.
  intros s rho Hs Hg HF. cbn [ss_facts mc_state] in HF.
  destruct (tf_facts rho _ HF) as [Hff Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1].
  pose proof (holds_NOZ_mc rho v120 Hff) as NZ. cbn [eval v120] in NZ.
  destruct (svals_eq s _ _ _ _ _ Hs) as (E120 & E122 & E16 & E17 & E14).
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (fn_word (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) ltac:(lia) NZ) as ST.
  apply inv_intro; rewrite !rw_sub, ?E120, ?E122, ?E16, ?E17, ?E14; cbn [eval];
    rewrite ?add_lit_val; change (snorm 8) with 8; change (snorm (-8)) with (-8);
    rewrite ?Z.mod_small by lia; lia.
Qed.

Lemma mc_facts : ltac2:(tb__ "0|2|
S70S7S4S1SbA2M0A1S7ScA1M1S71S69G1S13S26R4R3R2R1A4A1S13S26Z0S3G0A1R2P87A4A1A3Fnx;FF;Fregs;Fpc;").
Proof using . reflexivity. Qed.

Lemma BNZ_eq_120 : ltac2:(tb__ "0|0|
SfSdR1S2cS25A1A2S6bS69S70S89S14R2P3A2S76Q40S15R2P78A2A2A2Z0A3A1F_;Frho;").
Proof using . intros rho H. apply holds_BNZ_eq in H. exact H. Qed.
Lemma BNZ_ne_120 : ltac2:(tb__ "0|0|
SfSdR1S30S25A1A2S6bS69S70S89S14R2P3A2S76Q40S15R2P78A2A2A2Z0A3A1F_;Frho;").
Proof using . intros rho H. apply holds_BNZ_ne in H. exact H. Qed.

Lemma glue_b1 : ltac2:(tb__ "0|0|
SfVG;R1A1S6eScSdR2A1S13S3aA1A3S6eScSdS85R3S50A2A1S29S25S27A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_b1. rewrite mc_facts. apply glue_step1; [exact vals_b1 | exact BNZ_eq_120]. Qed.
Lemma glue_1j : ltac2:(tb__ "0|0|
SfVG;R1A1S6eScSdR2A1S13S37A1A3S6eScSdS85R3S4dA2A1S29S25S27A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_1j. rewrite mc_facts. apply glue_step1; [exact vals_1j | exact BNZ_eq_120]. Qed.
Lemma glue_23 : ltac2:(tb__ "0|0|
SfVG;R1A1S6eScSdR2A1S13S38A1A3S6eScSdS85R3S4eA2A1S29S25S27A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_23. rewrite mc_facts. apply glue_step1; [exact vals_23 | exact BNZ_ne_120]. Qed.
Lemma glue_b3 : ltac2:(tb__ "0|0|
SfVG;R1A1S6eScSdR2A1S13S3cA1A3S6eScSdS85R3S52A2A1S29S25S27A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_b3. rewrite mc_facts. apply glue_step1; [exact vals_b3 | exact BNZ_eq_120]. Qed.
Lemma glue_b2 : ltac2:(tb__ "0|0|
SfVG;R1A1S6eScSdR2A1S13S3bA1A3S6eScSdS85R3S51A2A1S29S25S27A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_b2. rewrite mc_facts. apply glue_step8. exact vals_b2. Qed.
Lemma glue_23w : ltac2:(tb__ "0|0|
SfVG;R1A1S6eScSdR2A1S13S39A1A3S6eScSdS85R3S4fA2A1S29S25S27A2A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_23w. rewrite mc_facts. apply glue_step8. exact vals_23w. Qed.

Lemma glue_found : ltac2:(tb__ "0|5|
S88ScSfS69S4SbSbA2S2SbSbS86R3P8cM0A2S86R3P10M1A2A4S2SbSbS10P78M2A1S10G1A1M3A4A3SfSdR1R4A2S69S70S89S14R2P3A2S76Q40S15R2G2A2A2A2Z0M4A3F_;Frho;VG;R3A1S6eScSdR4A1S13S26G4S3S4S1SbA2A1S28R5A1P87A4A1A3S6eScSdS85R5R7A2A1S0ScS1bS10G0A1G3A2S3ScA1A3A3F_;F_;F_;F_;Frho;Ff;Fs;").
Proof using FN.
  intros s f rho Hs Hf Hg HF. cbn [ss_facts mc_state] in HF.
  destruct (tf_facts rho f HF) as [Hff Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1]. pose proof (Hf rho Hff) as ZB.
  injection Hs as E140 E16.
  pose proof (fn_found (rl rho 3) (bv_unsigned (rw rho 16)) FN1 (bv_unsigned (rw rho 120)) ltac:(pose proof (urange (rw rho 120)); lia) ltac:(lia) ZB) as EQ.
  constructor; [|constructor]. cbn [holds eval]. rewrite !rw_sub, E140, E16. cbn [eval].
  apply bv_eq. exact EQ.
Qed.
Lemma BZ_ne_120 : ltac2:(tb__ "0|0|
SfSdR1S44S25A1A2S69S70S89S14R2P3A2S76Q40S15R2P78A2A2A2Z0A3F_;Frho;").
Proof using . intros rho H. apply holds_BZ_ne in H. exact H. Qed.
Lemma BZ_eq_120 : ltac2:(tb__ "0|0|
SfSdR1S43S25A1A2S69S70S89S14R2P3A2S76Q40S15R2P78A2A2A2Z0A3F_;Frho;").
Proof using . intros rho H. apply holds_BZ_eq in H. exact H. Qed.
Lemma glue_f2 : ltac2:(tb__ "0|0|
SfVG;R1A1S6eScSdR2A1S13S3dA1A3S6eScSdS85R3S2eA2A1S0ScS1bS10P8cA1S10P10A1A2S3ScA1A3A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_f2. rewrite mc_facts. apply glue_found; [exact vals_f2 | exact BZ_ne_120]. Qed.
Lemma glue_f3 : ltac2:(tb__ "0|0|
SfVG;R1A1S6eScSdR2A1S13S3eA1A3S6eScSdS85R3S2fA2A1S0ScS1bS10P8cA1S10P10A1A2S3ScA1A3A3F_;F_;Frho;").
Proof using FN. intros rho. unfold T_f3. rewrite mc_facts. apply glue_found; [exact vals_f3 | exact BZ_eq_120]. Qed.

Lemma contra_j : ltac2:(tb__ "0|0|
SfVG;R1A1S6eScSdR2A1S13S4bA1A3S6cF_;F_;Frho;").
Proof using rho0.
  intros rho Hg HF. unfold X_j in HF. rewrite mc_facts in HF. cbn [ss_facts mc_state] in HF.
  destruct (tf_facts rho _ HF) as [H Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  cbn [holds eval branch_taken v122] in H.
  destruct (sltu0_cases (rw rho 122)) as [[EE BB]|[EE BB]]; rewrite EE in H.
  - vm_compute in H. discriminate.
  - lia.
Qed.
Lemma contra_2 : ltac2:(tb__ "0|0|
SfVG;R1A1S6eScSdR2A1S13S48A1A3S6cF_;F_;Frho;").
Proof using FN.
  intros rho Hg HF. unfold X_2 in HF. rewrite mc_facts in HF. cbn [ss_facts mc_state] in HF.
  apply Forall_cons_iff in HF as [H8 HF].
  destruct (tf_facts rho _ HF) as [Hn Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1].
  pose proof (holds_NOZ_mc rho v120 Hn) as NZ. cbn [eval v120] in NZ.
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (fn_word (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) ltac:(lia) NZ) as ST.
  zholds H8. change (snorm (-8)) with (-8) in H8. change (0 mod 2 ^ 64) with 0 in H8.
  assert (bv_unsigned (rw rho 122) >= 9) by lia.
  rewrite Z.mod_small in H8 by lia. lia.
Qed.
Lemma contra_3 : ltac2:(tb__ "0|1|
ScSfSfSdR1R3A2S6bS69S70S89S14R2P3A2S76Q40S15R2P78A2A2A2Z0M0A3A1F_;Frho;VG;R2A1S6eScSdR3A1S0ScS19S17S8bS2bSeG0A1A3A1S13S26G0S3S4S1SbA2A1S28R4A1P87A4A1A3A3S6cF_;F_;F_;Frho;Ff;").
Proof using FN.
  intros f rho Hf Hg HF. cbn [ss_facts mc_state] in HF.
  apply Forall_cons_iff in HF as [H1 HF].
  destruct (tf_facts rho _ HF) as [Hn Z]. unfold invZ in Z. destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10).
  destruct (G_FN rho Hg) as [FN0 FN1]. pose proof (Hf rho Hn) as NZ.
  pose proof (urange (rw rho 120)) as R0. pose proof (urange (rw rho 122)) as R2.
  pose proof (fn_step (rl rho 3) (bv_unsigned (rw rho 16)) FN0 (bv_unsigned (rw rho 120)) ltac:(lia) ltac:(lia) NZ) as ST.
  zholds H1. change (snorm (-1)) with (-1) in H1. change (0 mod 2 ^ 64) with 0 in H1.
  assert (bv_unsigned (rw rho 122) >= 2) by lia.
  rewrite Z.mod_small in H1 by lia. lia.
Qed.
Lemma contra_3e : ltac2:(tb__ "0|0|
SfVG;R1A1S6eScSdR2A1S13S49A1A3S6cF_;F_;Frho;").
Proof using FN. intros rho. unfold X_3e. rewrite mc_facts. apply contra_3. exact BNZ_eq_120. Qed.
Lemma contra_3n : ltac2:(tb__ "0|0|
SfVG;R1A1S6eScSdR2A1S13S4aA1A3S6cF_;F_;Frho;").
Proof using FN. intros rho. unfold X_3n. rewrite mc_facts. apply contra_3. exact BNZ_ne_120. Qed.

End WithFirstNul.

Lemma inv_below : ltac2:(tb__ "0|0|
S69S5Sa3ScS1fS20S46A1A1S29S25S27A2A3S6A3").
Proof. vm_compute. reflexivity. Qed.
Lemma post_below : ltac2:(tb__ "0|0|
S69S5Sa3ScS1fS20S35A1A1S0ScS1bS10P8cA1S10P10A1A2S3ScA1A3A3S6A3").
Proof. vm_compute. reflexivity. Qed.

Theorem memchr0_sum : ltac2:(tb__ "0|0|
Sa8OF_;S7S9bA1S9aOF_;F_;SfS9eS92R3R2A3S33R2A1Sa7S92R5S9dS92R4S36R3A4S9cS92R4S7eR3S5bA5A4F_;F_;Frho;FK;Fok;").
Proof.
  intros ok K rho Hok HFN.
  apply (cfg_sound segs FUELM cutpcs_mc NF cuts_mc exits_mc
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho Posts_memchr0) Hok).
  - rewrite cuts_mc_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_mc.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]].
    + revert HagE. apply (exit_reenter_G segs ok K _ NF cuts_mc _ T_b1 C1_0 (inv v120 v122) s_b1);
        [right; left; reflexivity | exact ent_b1 | exact id_b1 | intros; eapply agree_below_trans; eauto | exact inv_below | exact (glue_b1 rho HFN)].
    + revert HagE. apply (exit_reenter_G segs ok K _ NF cuts_mc _ T_1j C84_0 (inv v120 v122) s_1j);
        [right; right; left; reflexivity | exact ent_1j | exact id_1j | intros; eapply agree_below_trans; eauto | exact inv_below | exact (glue_1j rho HFN)].
    + revert HagE. apply (exit_reenter_G segs ok K _ NF cuts_mc _ T_b2 C2_0 (inv v120 v122) s_b2);
        [right; right; right; left; reflexivity | exact ent_b2 | exact id_b2 | intros; eapply agree_below_trans; eauto | exact inv_below | exact (glue_b2 rho HFN)].
    + revert HagE. apply (exit_reenter_G segs ok K _ NF cuts_mc _ T_23 C3_0 (inv v120 v122) s_23);
        [right; right; right; right; left; reflexivity | exact ent_23 | exact id_23 | intros; eapply agree_below_trans; eauto | exact inv_below | exact (glue_23 rho HFN)].
    + revert HagE. apply (exit_reenter_G segs ok K _ NF cuts_mc _ T_23w C3_0 (inv v120 v122) s_23w);
        [right; right; right; right; left; reflexivity | exact ent_23w | exact id_23w | intros; eapply agree_below_trans; eauto | exact inv_below | exact (glue_23w rho HFN)].
    + revert HagE. apply (exit_reenter_G segs ok K _ NF cuts_mc _ T_b3 C3_0 (inv v120 v122) s_b3);
        [right; right; right; right; left; reflexivity | exact ent_b3 | exact id_b3 | intros; eapply agree_below_trans; eauto | exact inv_below | exact (glue_b3 rho HFN)].
    + revert HagE. apply (exit_post_G segs ok K NF rho cuts_mc Posts_memchr0 T_f2 P_ret_0 [SPEq (SVar 140) (SVar 16)] s_f2);
        [left; reflexivity | exact ent_f2 | exact id_f2 | exact post_below | exact (glue_f2 rho HFN)].
    + revert HagE. apply (exit_post_G segs ok K NF rho cuts_mc Posts_memchr0 T_f3 P_ret_0 [SPEq (SVar 140) (SVar 16)] s_f3);
        [left; reflexivity | exact ent_f3 | exact id_f3 | exact post_below | exact (glue_f3 rho HFN)].
    + revert HagE. apply (exit_contra segs ok K _ X_j). exact (contra_j rho).
    + revert HagE. apply (exit_contra segs ok K _ X_2). exact (contra_2 rho HFN).
    + revert HagE. apply (exit_contra segs ok K _ X_3e). exact (contra_3e rho HFN).
    + revert HagE. apply (exit_contra segs ok K _ X_3n). exact (contra_3n rho HFN).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition inc1 : sv := SAlu ALU_ADD v120 (SLit 1).
Definition inc8 : sv := SAlu ALU_ADD v120 (SLit 8).
Definition vcuts_mc : list vnode := ltac2:(tb__ "0|1|
S0S72S73S36Z14SeZ0A1A3S0S72S73S53ZaS25A3S0S72S73S57Z8M0S25A3S0S72S73S54Z6S25A3S0S72S73S56Z4S25A3S0S72S73S59G0S25A3S3S72A1A3A3A3A3A3A3").
Definition vexits_mc : list vnode := ltac2:(tb__ "0|3|
S0S72S73S3aZcM0S41A3S0S72S73S37G0S41A3S0S72S73S3bG0S5fA3S0S72S73S38G0S41A3S0S72S73S39G0S5fA3S0S72S73S3cG0S41A3S0S72S73S3dZ1M1S25A3S0S72S73S3eG1S25A3S0S72S73S4bZ0M2S25A3S0S72S73S48G2S25A3S0S72S73S49G2S25A3S0S72S73S4aG2S25A3S3S72A1A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma echeck_mc : ltac2:(tb__ "0|0|
S69S5Sa9S92S5aS5dS7eS67S68A6S6A3").
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma meas_reenter : ltac2:(tb__ "0|2|
SfS88SbS7SbA1M0S69G0S42R3A1S0SbR2R1A3A3S78S76Q40M1S18R5R3A2A2S76G1S18S85R5R4A2S25A2A2A2F_;Frest;Fv;Fs;Frho;").
Proof.
  intros rho s v rest H. unfold svals in H. cbn [map] in H. injection H as H _.
  cbn [eval v120]. rewrite rw_sub, H. lia.
Qed.

Theorem memchr0_sum_ex : ltac2:(tb__ "0|0|
S7S9bA1S9aOF_;F_;SfS33R1A1Sa6S92S9dS92R3S36R2A4S9cS92R3S7eR2S5bA5A3F_;Frho;FK;").
Proof.
  intros K rho HFN.
  change Pre_memchr0 with (vn_state (mkVN Pre_memchr0 20 (SLit 0))).
  apply (cfg_complete_autoI segs FUELM cutpcs_mc NF vcuts_mc vexits_mc
           (fun rho' => agree_below NF rho rho') K (LQ segs K NF rho Posts_memchr0)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_mc.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]].
    + revert HgE. apply (eexit_reenter_I segs K _ NF vcuts_mc _ (mkVN T_b1 12 inc1) (mkVN C1 10 v120) (inv v120 v122) C1_0 s_b1);
        [right; left; reflexivity | reflexivity | exact ent_b1 | exact id_b1 | intros; eapply agree_below_trans; eauto | exact inv_below
        | intros r Hg HF; split; [exact (glue_b1 rho HFN r Hg HF) | exact (meas_reenter r s_b1 _ _ vals_b1)] | cbn; lia | cbn; lia].
    + revert HgE. apply (eexit_reenter_I segs K _ NF vcuts_mc _ (mkVN T_1j 12 inc1) (mkVN C84 8 v120) (inv v120 v122) C84_0 s_1j);
        [right; right; left; reflexivity | reflexivity | exact ent_1j | exact id_1j | intros; eapply agree_below_trans; eauto | exact inv_below
        | intros r Hg HF; split; [exact (glue_1j rho HFN r Hg HF) | exact (meas_reenter r s_1j _ _ vals_1j)] | cbn; lia | cbn; lia].
    + revert HgE. apply (eexit_reenter_I segs K _ NF vcuts_mc _ (mkVN T_b2 12 inc8) (mkVN C2 6 v120) (inv v120 v122) C2_0 s_b2);
        [right; right; right; left; reflexivity | reflexivity | exact ent_b2 | exact id_b2 | intros; eapply agree_below_trans; eauto | exact inv_below
        | intros r Hg HF; split; [exact (glue_b2 rho HFN r Hg HF) | exact (meas_reenter r s_b2 _ _ vals_b2)] | cbn; lia | cbn; lia].
    + revert HgE. apply (eexit_reenter_I segs K _ NF vcuts_mc _ (mkVN T_23 12 inc1) (mkVN C3 4 v120) (inv v120 v122) C3_0 s_23);
        [right; right; right; right; left; reflexivity | reflexivity | exact ent_23 | exact id_23 | intros; eapply agree_below_trans; eauto | exact inv_below
        | intros r Hg HF; split; [exact (glue_23 rho HFN r Hg HF) | exact (meas_reenter r s_23 _ _ vals_23)] | cbn; lia | cbn; lia].
    + revert HgE. apply (eexit_reenter_I segs K _ NF vcuts_mc _ (mkVN T_23w 12 inc8) (mkVN C3 4 v120) (inv v120 v122) C3_0 s_23w);
        [right; right; right; right; left; reflexivity | reflexivity | exact ent_23w | exact id_23w | intros; eapply agree_below_trans; eauto | exact inv_below
        | intros r Hg HF; split; [exact (glue_23w rho HFN r Hg HF) | exact (meas_reenter r s_23w _ _ vals_23w)] | cbn; lia | cbn; lia].
    + revert HgE. apply (eexit_reenter_I segs K _ NF vcuts_mc _ (mkVN T_b3 12 inc1) (mkVN C3 4 v120) (inv v120 v122) C3_0 s_b3);
        [right; right; right; right; left; reflexivity | reflexivity | exact ent_b3 | exact id_b3 | intros; eapply agree_below_trans; eauto | exact inv_below
        | intros r Hg HF; split; [exact (glue_b3 rho HFN r Hg HF) | exact (meas_reenter r s_b3 _ _ vals_b3)] | cbn; lia | cbn; lia].
    + revert HgE. apply (eexit_post_I segs K NF rho vcuts_mc Posts_memchr0 (mkVN T_f2 1 v120) P_ret_0 [SPEq (SVar 140) (SVar 16)] s_f2);
        [left; reflexivity | exact ent_f2 | exact id_f2 | exact post_below | exact (glue_f2 rho HFN)].
    + revert HgE. apply (eexit_post_I segs K NF rho vcuts_mc Posts_memchr0 (mkVN T_f3 1 v120) P_ret_0 [SPEq (SVar 140) (SVar 16)] s_f3);
        [left; reflexivity | exact ent_f3 | exact id_f3 | exact post_below | exact (glue_f3 rho HFN)].
    + revert HgE. apply (eexit_contra segs K _ X_j). exact (contra_j rho).
    + revert HgE. apply (eexit_contra segs K _ X_2). exact (contra_2 rho HFN).
    + revert HgE. apply (eexit_contra segs K _ X_3e). exact (contra_3e rho HFN).
    + revert HgE. apply (eexit_contra segs K _ X_3n). exact (contra_3n rho HFN).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
