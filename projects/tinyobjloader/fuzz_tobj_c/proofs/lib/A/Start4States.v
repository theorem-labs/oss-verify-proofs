(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "option"; "Some"; "list"; "bool"; "length"; "nat"; "app"; "pair"; "prod"; "orb"; "false"; "fst"; "negb"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "mkLeafA"; "axst"; "ax_setS"; "entailsA"; "la_state"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "sprop"; "ss_objs"; "SVar"; "SPUle"; "ss_next"; "ss_pc"; "SAlu"; "SPAlign"; "cell"; "ss_regs"; "mkObj"; "sv_eqb"; "DZero"; "sstate"; "mkSS"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_resv"; "SPUlt"; "c_off"; "c_val"; "c_width"; "mkCell"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sprop_eqb"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "ECALL_MMAP"; "fail_state"; "SPIN_MMAPORDIE"; "SPIN_RAR"; "restate_sv"; "E_k10"; "E_k11"; "E_k9"; "MEMSET"; "E_k12c"; "L11m"; "ri30"; "E_k12d"; "E_k8"; "E_k8x"; "SPIN10"; "SPIN11"; "SPIN7"; "SPIN9"; "T1_11"; "E_k12"; "L11mx"; "L8m"; "M11"; "M8"; "S_k10ok"; "S_k7ok"; "S_k8ok"; "S_k9ok"; "T2_11"; "e_ri"; "e_rid"; "e_sb"; "objShB6"; "CLS11"; "F10"; "F11"; "F11m"; "F7"; "F8m"; "F8x"; "F9"; "L8mx"; "S_k11c"; "S_k11ok"; "leaf1"; "objRI"; "objShRI"; "ps8"; "restate_S"; "restate_cell"; "restate_obj"; "set_objs'"; "shB6_base"; "shRI_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "ALU_ADD"; "ALU_AND"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "axA"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "infer_sub"; "@Corelib.Lists.ListDef"; "nth"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "mmap_obj"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start3States"; "E_k7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "withX0"; "move_obj_last"; "noX"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@Stdlib.Lists.List"; "existsb"; "filter"; "find"; "last"; "removelast"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e0.Start3States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ECALL_MMAP : Z := 0x7050c.
Definition SPIN_RAR : Z := 0x7a41c.
Definition SPIN_MMAPORDIE : Z := 0x6bd84.
Definition MEMSET : Z := 0xde378.

Definition leaf1 (A : axst) (o : option (list leafA)) : axst := ltac2:(tb__ "0|1|
S3S5S15A1M0A1S19Lo;Vo;G0G0S19Ll0;R1VA;S15G0G0S19Ll1;R1S1cR2A1S15G0VA;Ll3;Ll2;X5x2Ll1;Ll;X5x2Ll0;VA;X3x2").
Definition run_to (fuel : nat) (cuts : list Z) (A : axst) : axst := ltac2:(tb__ "0|0|
S6fVA;S17S41Vfuel;Vcuts;VA;S2A5A2").

Definition fail_state (E : axst) : axst := ltac2:(tb__ "0|0|
S81S95S16VE;A1S96A2A1").

Definition restate_sv (ps : list (sv * sv)) (e : sv) : sv := ltac2:(tb__ "0|1|
S3SbS1eS1eA2M0A1S1eLx;S9aG0G0S2cSeS1eS1eR1A3Ve;A2Lp;Vps;A3G0S10S1eS1eR1A3Lp;Ve;X3x2").
Definition restate_cell (ps : list (sv * sv)) (c : cell) : cell := ltac2:(tb__ "0|0|
S39S46Vps;S36Vc;A1A2S38Vc;A1S46Vps;S37Vc;A1A2A3").
Definition restate_obj (ps : list (sv * sv)) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S2bS46Vps;S3aVo;A1A2S46Vps;S3eVo;A1A2S46Vps;S3dVo;A1A2S86S29S29S74Vps;A1S3bVo;A1A4S3cVo;A1A5").
Definition restate_S (ps : list (sv * sv)) (S : sstate) : sstate := ltac2:(tb__ "0|0|
S2fS26VS;A1S86S1eS1eS46Vps;A1S2aVS;A1A4S32VS;A1S31VS;A1S34VS;A1S86S1fS1fS75Vps;A1S22VS;A1A4S30VS;A1S25VS;A1S33VS;A1A9").

Definition set_objs' (A : axst) (objs : list sobj) : axst := ltac2:(tb__ "0|0|
S1dS7bS16VA;A1Vobjs;A2S1SbS1eS1eA2A1S20S82A1A3").
Definition drop_last_obj (A : axst) : axst := ltac2:(tb__ "0|0|
S76VA;S9cS1fS22S16VA;A1A1A2A2").

Definition F7 : list sprop := ltac2:(tb__ "0|2|
S0S21S28P1dM0ZcA2S0S21S24S20Z10007fff8000A1S23G0A1M1A2S0S21S24G1S20S8aZ7fffff800000Z2000011000A2A1A2S1S21A1A3A3A3").
Definition S_k7ok : axst := ltac2:(tb__ "0|1|
S81S83S68S88S16S8eA1M0S23P1dA1S22G0A1P1fA4A2A1").
Definition run7_ok__R : option (list leafA) := ltac2:(tb__ "0|0|
S17S41Ubb8S0S13S42S1S13A1A3S5cS2A5").
Local Strategy expand [run7_ok__R].
Definition E_k8 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 S_k7ok (ro1__)))) run7_ok__R).
Definition run7_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S17S41Uc8S0S13S45S1S13A1A3S43S8eA1S2A5").
Local Strategy expand [run7_fail__R].
Definition SPIN7 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 (fail_state E_k7) (ro2__)))) run7_fail__R).
Lemma run7_ok : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41Ubb8S0S13S42S1S13A1A3S5cS2A5S4G0S0S15S18S4fS79A2S1S15A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run7_ok__R <: run7_ok__R = Some [mkLeafA E_k8 RsCut]). Qed.
Lemma run7_fail : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41Uc8S0S13S45S1S13A1A3S43S8eA1S2A5S4G0S0S15S18S53S79A2S1S15A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run7_fail__R <: run7_fail__R = Some [mkLeafA SPIN7 RsCut]). Qed.
Lemma spin7 : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41U2S0S13S45S1S13A1A3S53S2A5S4G0S0S15S18S53S79A2S1S15A1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_k8_at : ltac2:(tb__ "0|2|
S12S11S13S26S16S4fA1M0A1M1S42A3S12S11S14S25G0A1P1fA3S12S11S3S7cA1S7aS41G1A2S4S7cS7dA2A3S11S8S7S1fS22G0A1A2UcA3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition e_sb : sv := ltac2:(tb__ "0|1|
S27S80S27S7eS23P1dA1M0S20Z10000A1A3S27S7fG0S20ZffffA1A3A3").
Definition e_ri : sv := SAlu ALU_ADD e_sb (SLit 137438953472).
Definition e_rid : sv := SAlu ALU_AND e_ri (SLit 18446744073709547520).
Definition ri30 : sv := SAlu ALU_ADD (SVar 30%positive) (SLit 137438953472).
Definition ps8 : list (sv * sv) := ltac2:(tb__ "0|1|
S0SbS1eS1eA2M0SaS1eS1eS61S4dA4S0G0SaS1eS1eS60S4dA4S0G0SaS1eS1eS62S23P1eA1A4S1G0A1A3A3A3").
Definition F8x : list sprop := ltac2:(tb__ "0|3|
S0S21S28P1eM0Z10A2S0S21S35S23P1dA1M1S23G0A1M2A2S0S21S24G2S27S7eG1S20Z10000A1A3A2S1S21A1A3A3A3").
Definition E_k8x : axst := Eval vm_compute in (axA (add_facts F8x (restate_S ps8 (ax_S E_k8)))).
Lemma E_k8x_eq : ltac2:(tb__ "0|0|
S11S19S50S81S83S6aS73S72S16S4fA1A2A2A1A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_k8x_no29expr : ltac2:(tb__ "0|0|
S11S6S98S1eS1eScScS2cR1S61A2S2cR1S60A2A2S2cR1S62A2A2Lr;S2aS16S50A1A1A3SdA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition objRI : sobj := ltac2:(tb__ "0|0|
S2bS4dS20Z0A1S20Z1000A1S1S29A1S2dA5").
Definition S_k8ok : axst := ltac2:(tb__ "0|1|
S81S88S16S50A1M0S4dS9S1fS22G0A1S0S1fS70S1S1fA1A3A3P1fA4A1").

Definition run8a__R : option (list leafA) := ltac2:(tb__ "0|0|
S17S41Ubb8S0S13S4aS0S13S42S1S13A1A3A3S8fS5dA1S2A5").
Local Strategy expand [run8a__R].
Definition L8mx : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => ((leaf1 (withX0 S_k8ok) (ro3__)))) run8a__R).
Lemma run8a : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41Ubb8S0S13S4aS0S13S42S1S13A1A3A3S8fS5dA1S2A5S4G0S0S15S18S6cS79A2S1S15A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run8a__R <: run8a__R = Some [mkLeafA L8mx RsCut]). Qed.
Definition L8m : axst := Eval vm_compute in (noX L8mx).
Lemma L8m_eq : noX L8mx = L8m. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L8m_at : ltac2:(tb__ "0|3|
S12S11S13S26S16S58A1M0A1S4aA3S12S11S14S25G0A1P20A3S12S11S1eS85S1eUaS2aG0A1M1S20Z0A1M2A4S27S7eS23P1fA1S20Z47fff8000A1A3A3S12S11S1eS85S1eUbG1G2A4S20ZfaA1A3S11S1eS85S1eUcG1G2A4S20Z200A1A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition shRI_base : sv := SAlu ALU_ADD (SVar 31%positive) (SLit 0x47fff8000).
Definition objShRI : sobj := ltac2:(tb__ "0|0|
S2bS78S20Z0A1S20Z1000A1S1S29A1S2dA5").
Definition F8m : list sprop := [SPAlign 31%positive 13].
Definition M8 : axst := ltac2:(tb__ "0|1|
S81S83S69S7bS16S58A1M0S9S1fS22G0A1S0S1fS71S1S1fA1A3A3A2A2A1").
Definition run8b__R : option (list leafA) := ltac2:(tb__ "0|0|
S17S41Ubb8S0S13S42S1S13A1A3S5aS2A5").
Local Strategy expand [run8b__R].
Definition E_k9 : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => ((leaf1 M8 (ro4__)))) run8b__R).
Lemma run8b : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41Ubb8S0S13S42S1S13A1A3S5aS2A5S4G0S0S15S18S49S79A2S1S15A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run8b__R <: run8b__R = Some [mkLeafA E_k9 RsCut]). Qed.
Lemma E_k9_at : ltac2:(tb__ "0|2|
S12S11S13S26S16S49A1M0A1M1S42A3S12S11S14S25G0A1P20A3S12S11S3S7cA1S7aS41G1A2S4S7cS7dA2A3S11S8S7S1fS22G0A1A2UeA3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition F9 : list sprop := ltac2:(tb__ "0|2|
S0S21S28P20M0ZcA2S0S21S24S20Z646000A1S23G0A1M1A2S0S21S24G1S20S8aZ7fffff800000Z800000A2A1A2S1S21A1A3A3A3").
Definition S_k9ok : axst := ltac2:(tb__ "0|1|
S81S83S6bS88S16S49A1M0S23P20A1S22G0A1P21A4A2A1").
Definition run9_ok__R : option (list leafA) := ltac2:(tb__ "0|0|
S17S41Ubb8S0S13S42S1S13A1A3S5eS2A5").
Local Strategy expand [run9_ok__R].
Definition E_k10 : axst := Eval vm_compute in ((fun ro5__ : option (list leafA) => ((leaf1 S_k9ok (ro5__)))) run9_ok__R).
Definition run9_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S17S41Uc8S0S13S45S1S13A1A3S43S49A1S2A5").
Local Strategy expand [run9_fail__R].
Definition SPIN9 : axst := Eval vm_compute in ((fun ro6__ : option (list leafA) => ((leaf1 (fail_state E_k9) (ro6__)))) run9_fail__R).
Lemma run9_ok : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41Ubb8S0S13S42S1S13A1A3S5eS2A5S4G0S0S15S18S47S79A2S1S15A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run9_ok__R <: run9_ok__R = Some [mkLeafA E_k10 RsCut]). Qed.
Lemma run9_fail : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41Uc8S0S13S45S1S13A1A3S43S49A1S2A5S4G0S0S15S18S54S79A2S1S15A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run9_fail__R <: run9_fail__R = Some [mkLeafA SPIN9 RsCut]). Qed.
Lemma spin9 : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41U2S0S13S45S1S13A1A3S54S2A5S4G0S0S15S18S54S79A2S1S15A1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_k10_at : ltac2:(tb__ "0|2|
S12S11S13S26S16S47A1M0A1M1S42A3S12S11S14S25G0A1P21A3S12S11S3S7cA1S7aS41G1A2S4S7cS7dA2A3S11S8S7S1fS22G0A1A2UeA3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition F10 : list sprop := ltac2:(tb__ "0|3|
S0S21S28P21M0ZcA2S0S21S24S20Z1000M1A1S23G0A1M2A2S0S21S24G2S20S8aZ7fffff800000G1A2A1A2S1S21A1A3A3A3").
Definition S_k10ok : axst := ltac2:(tb__ "0|2|
S81S83S65S88S16S47A1M0S23P21M1A1S9S1fS22G0A1S0S1fS89G1Z1000A2S1S1fA1A3A3P22A4A2A1").
Definition run10_ok__R : option (list leafA) := ltac2:(tb__ "0|0|
S17S41Ubb8S0S13S42S1S13A1A3S5bS2A5").
Local Strategy expand [run10_ok__R].
Definition E_k11 : axst := Eval vm_compute in ((fun ro7__ : option (list leafA) => ((leaf1 S_k10ok (ro7__)))) run10_ok__R).
Definition run10_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S17S41Uc8S0S13S44S1S13A1A3S43S47A1S2A5").
Local Strategy expand [run10_fail__R].
Definition SPIN10 : axst := Eval vm_compute in ((fun ro8__ : option (list leafA) => ((leaf1 (fail_state E_k10) (ro8__)))) run10_fail__R).
Lemma run10_ok : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41Ubb8S0S13S42S1S13A1A3S5bS2A5S4G0S0S15S18S48S79A2S1S15A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run10_ok__R <: run10_ok__R = Some [mkLeafA E_k11 RsCut]). Qed.
Lemma run10_fail : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41Uc8S0S13S44S1S13A1A3S43S47A1S2A5S4G0S0S15S18S51S79A2S1S15A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run10_fail__R <: run10_fail__R = Some [mkLeafA SPIN10 RsCut]). Qed.
Lemma spin10 : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41U2S0S13S44S1S13A1A3S51S2A5S4G0S0S15S18S51S79A2S1S15A1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_k11_at : ltac2:(tb__ "0|2|
S12S11S13S26S16S48A1M0A1M1S42A3S12S11S14S25G0A1P22A3S12S11S3S7cA1S7aS41G1A2S4S7cS7dA2A3S11S8S7S1fS22G0A1A2UfA3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition F11 : list sprop := ltac2:(tb__ "0|2|
S0S21S28P22M0ZcA2S0S21S24S20Z646000A1S23G0A1M1A2S0S21S24G1S20S8aZ7fffff800000Z10000A2A1A2S1S21A1A3A3A3").
Definition CLS11 (hi : bool) : sprop := ltac2:(tb__ "0|1|
S6S21Lhi;Vhi;S24S20Z10007fff8000A1S23P22A1M0A2S24G0S20S8aZ7fff7000Z10000A2A1A2X6x2").
Definition S_k11ok : axst := ltac2:(tb__ "0|2|
S81S83S66S88S16S48A1M0S23P22M1A1S9S1fS22G0A1S0S1fS89G1Z10000A2S1S1fA1A3A3P23A4A2A1").
Definition S_k11c (hi : bool) : axst := ltac2:(tb__ "0|0|
S81S83S0S21S64Vhi;A1S1S21A1A3S16S6eA1A2A1").
Definition run11_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S17S41Uc8S0S13S44S1S13A1A3S43S48A1S2A5").
Local Strategy expand [run11_fail__R].
Definition SPIN11 : axst := Eval vm_compute in ((fun ro9__ : option (list leafA) => ((leaf1 (fail_state E_k11) (ro9__)))) run11_fail__R).
Lemma run11_fail : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41Uc8S0S13S44S1S13A1A3S43S48A1S2A5S4G0S0S15S18S52S79A2S1S15A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run11_fail__R <: run11_fail__R = Some [mkLeafA SPIN11 RsCut]). Qed.
Lemma spin11 : ltac2:(tb__ "0|1|
S11S3S5S15A1M0A1S17S41U2S0S13S44S1S13A1A3S52S2A5S4G0S0S15S18S52S79A2S1S15A1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition L11mx_lo : axst := Eval vm_compute in (run_to 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k11c false))).
Definition L11mx_hi : axst := Eval vm_compute in (run_to 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k11c true))).
Definition L11mx (hi : bool) : axst := if hi then L11mx_hi else L11mx_lo.
Lemma run11a : ltac2:(tb__ "0|1|
S6S11S3S5S15A1M0A1S17S41Ubb8S0S13S4aS0S13S42S1S13A1A3A3S8fS6dR1A1A1S2A5S4G0S0S15S18S57R1A1S79A2S1S15A1A3A2A3Fhi;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition L11m_lo : axst := Eval vm_compute in (noX L11mx_lo).
Definition L11m_hi : axst := Eval vm_compute in (noX L11mx_hi).
Definition L11m (hi : bool) : axst := if hi then L11m_hi else L11m_lo.
Lemma L11m_eq : ltac2:(tb__ "0|0|
S6S11S19S91S57R1A1A1S4cR1A1A3Fhi;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L11m_at : ltac2:(tb__ "0|3|
S6S12S11S13S26S16S4cR1A1A1M0A1S4aA3S12S11S14S25G0A1P24A3S12S11S1eS85S1eUaS2aG0A1M1S20Z0A1M2A4S27S7eS23P23A1S20Z7fff8000A1A3A3S12S11S1eS85S1eUbG1G2A4S20ZfeA1A3S12S11S1eS85S1eUcG1G2A4S20Z2000A1A3S11S8S7S1fS22G0A1A2U10A3A2A2A2A2A2Fhi;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition shB6_base : sv := SAlu ALU_ADD (SVar 35%positive) (SLit 0x7fff8000).
Definition objShB6 : sobj := ltac2:(tb__ "0|0|
S2bS77S20Z0A1S20Z2000A1S1S29A1S2dA5").
Definition F11m : list sprop := [SPAlign 35%positive 9].

Definition T1_11_lo : sstate := Eval vm_compute in (move_obj_last (ax_S L11m_lo) 13).
Definition T1_11_hi : sstate := Eval vm_compute in (move_obj_last (ax_S L11m_hi) 13).
Definition T1_11 (hi : bool) : sstate := if hi then T1_11_hi else T1_11_lo.
Lemma T1_11_eq : ltac2:(tb__ "0|0|
S6S11S2eS90S16S4cR1A1A1UdA2S55R1A1A3Fhi;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_T1_11 : ltac2:(tb__ "0|0|
S6S11S6S94S16S4cR1A1A1S55R1A1A2S2A3Fhi;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T2_11_lo : sstate := Eval vm_compute in (match split_obj_at T1_11_lo 15 (SLit 512) with Some S' => S' | None => T1_11_lo end).
Definition T2_11_hi : sstate := Eval vm_compute in (match split_obj_at T1_11_hi 15 (SLit 512) with Some S' => S' | None => T1_11_hi end).
Definition T2_11 (hi : bool) : sstate := if hi then T2_11_hi else T2_11_lo.
Lemma split_T2_11 : ltac2:(tb__ "0|0|
S6S11S3S2eA1S97S55R1A1UfS20Z200A1A3S4S2eS5fR1A1A2A3Fhi;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition M11 (hi : bool) : axst := ltac2:(tb__ "0|1|
S81S83S67S7bS5fVhi;A1M0S9S1fS87S1fU10S22G0A1A3S0S1fS63S1S1fA1A3A3A2A2A1").
Lemma M11_swf : ltac2:(tb__ "0|0|
S6S11S6S40S16S59R1A1A1A1S2A3Fhi;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_k12c_lo : axst := Eval vm_compute in (run_to 6000%nat [ECALL_MMAP] (M11 false)).
Definition E_k12c_hi : axst := Eval vm_compute in (run_to 6000%nat [ECALL_MMAP] (M11 true)).
Definition E_k12c (hi : bool) : axst := if hi then E_k12c_hi else E_k12c_lo.
Lemma run11b : ltac2:(tb__ "0|1|
S6S11S3S5S15A1M0A1S17S41S92S93S8cS8bS8bS8bS8dA1A1A1A1A1A1S0S13S42S1S13A1A3S59R1A1S2A5S4G0S0S15S18S4bR1A1S79A2S1S15A1A3A2A3Fhi;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_k12c_at : ltac2:(tb__ "0|2|
S6S12S11S13S26S16S4bR1A1A1M0A1M1S42A3S12S11S14S25G0A1P24A3S12S11S3S7cA1S7aS41G1A2S4S7cS7dA2A3S11S8S7S1fS22G0A1A2U11A3A2A2A2Fhi;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition E_k12 : axst := Eval vm_compute in (drop_last_obj E_k12c_hi).
Lemma E_k12_split : ltac2:(tb__ "0|1|
S6S11S5S1fA1S22S16S4bR1A1A1A1M0S9S1fS22S16S56A1A1S0S1fS9bS1fG0S63A3S1S1fA1A3A3A3Fhi;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition drop_fact (f : sprop) (S : sstate) : sstate := ltac2:(tb__ "0|0|
S2fS26VS;A1S2aVS;A1S32VS;A1S31VS;A1S34VS;A1S22VS;A1S99S21S21SfS3fR1Vf;A2A1Lg;S30VS;A1A3S25VS;A1S33VS;A1A9").
Definition E_k12d : axst := Eval vm_compute in (axA (drop_fact (CLS11 true) (ax_S E_k12))).
Lemma E_k12d_at : ltac2:(tb__ "0|2|
S12S11S13S26S16S4eA1M0A1M1S42A3S12S11S14S25G0A1P24A3S12S11S3S7cA1S7aS41G1A2S4S7cS7dA2A3S11S8S7S1fS22G0A1A2U10A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma merge12_ok : ltac2:(tb__ "0|2|
S6S11S6S1bS1aS4bR1A1M0S7bS16G0A1S22S16S56A1A1A2M1A2S4eS84P24G1S16S4eA1A3A3S2A3Fhi;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
