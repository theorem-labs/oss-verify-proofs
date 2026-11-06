(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_026.   (* [comment removed for export] *)
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "option"; "true"; "Some"; "prod"; "bool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sprop"; "reg_sv"; "SPUle"; "SVar"; "SPAlign"; "ss_next"; "DZero"; "cell"; "mkObj"; "ss_pc"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Decimal"; "D0"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8States0"; "K18x"; "E22A"; "E22B"; "E22_of"; "R22"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "ax_S"; "ax_X"; "ax_base"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States"; "K18S"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start7States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition pick {T} (v : bool) (a b : T) : T := if v then a else b.

Definition K18x : axst := ax_setX K18 [].
Lemma K18x_at : ltac2:(tb__ "0|2|
S1S0S18S11S24S1dA1M0A1P9fA3S1S0S4S8SbSbA2M1A1S25S1dA1S3G1A1A3S1S0SbS26S1dA1SaS2eA1A3S0S16G0S31A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition R22_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S28S29S2aS1aS1bS19S19S19S1cA1A1A1A1A1A1A1S2S17Z7050cS2S17Z6bd84S3S17A1A3A3S1dS6A5").
Local Strategy expand [R22_run__R].
Definition R22 : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) R22_run__R).
Lemma R22_run : ltac2:(tb__ "0|0|
S0S5S4S22A1A1S23S28S29S2aS1aS1bS19S19S19S1cA1A1A1A1A1A1A1S2S17Z7050cS2S17Z6bd84S3S17A1A3A3S1dS6A5S21A3").
Proof. exact (@eq_refl (option (list leafA)) R22_run__R <: R22_run__R = R22). Qed.
Definition E22A : axst := Eval vm_compute in (match R22 with Some (l :: _) => la_state l | _ => K18x end).
Definition E22B : axst := Eval vm_compute in (match R22 with Some (_ :: l :: _) => la_state l | _ => K18x end).
Lemma run22 : ltac2:(tb__ "0|1|
S0S5S4S22A1M0A1S23S28S29S2aS1aS1bS19S19S19S1cA1A1A1A1A1A1A1S2S17Z7050cS2S17Z6bd84S3S17A1A3A3S1dS6A5S7G0S2S22S27S1eS2fA2S2S22S27S1fS2fA2S3S22A1A3A3A2A3").
Proof. rewrite R22_run. reflexivity. Qed.
Definition E22_of (v : bool) : axst := pick v E22A E22B.
Lemma E22_at : ltac2:(tb__ "0|5|
S9S1S0S17S15S24S20R1A1M0A1M1A1M2Z7050cA3S1S0S18S11G1A1P9fA3S1S0S5S2cA1S30S28G2A2S7S2cS2dA2A3S1S0S4S8SbSbA2M3A1S25G0A1S3G3A1A3S1S0SbS26G0A1SaS2eA1A3S1S0SbSdG1Z11A2SaZdeA1A3S1S0SbSdG1ZaA2SaZ0A1M4A3S1S0SbSdG1ZbA2SaZ100000A1A3S1S0SbSdG1ZcA2SaZ3A1A3S1S0SbSdG1ZdA2SaZ22A1A3S1S0SbSdG1ZeA2SaZffffffffffffffffA1A3S0SbSdG1ZfA2G4A3A2A2A2A2A2A2A2A2A2A2A2Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition F22 : list sprop := ltac2:(tb__ "0|2|
S2ScS10P9fM0ZcA2S2ScSeSaZ646000A1SfG0A1M1A2S2ScSeG1SaS2bZ7fffff800000Z100000A2A1A2S3ScA1A3A3A3").
Definition F23 : list sprop := ltac2:(tb__ "0|2|
S2ScS10Pa0M0ZcA2S2ScSeSaZ646000A1SfG0A1M1A2S2ScSeG1SaS2bZ7fffff800000Z800000A2A1A2S3ScA1A3A3A3").
Definition o13p : sobj := ltac2:(tb__ "0|0|
S14SfPa0A1SaZ0A1SaZ1000A1S3S13A1S12A5").
Definition F24 : list sprop := ltac2:(tb__ "0|3|
S2ScS10Pa1M0ZcA2S2ScSeSaZ1000M1A1SfG0A1M2A2S2ScSeG2SaS2bZ7fffff800000G1A2A1A2S3ScA1A3A3A3").
