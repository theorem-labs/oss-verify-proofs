(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_009.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9 oe.

(* [comment removed for export] *)
Module Start8States.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "sym_runA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "list"; "Some"; "option"; "true"; "prod"; "app"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "sobj"; "ss_next"; "ss_pc"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Decimal"; "D0"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8States"; "E23_of"; "E24_of"; "EG_of"; "S22ok_of"; "S23ok0_of"; "S23ok_of"; "S24ok_of"; "SPIN22_of"; "SPIN23_of"; "SPIN24_of"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "fail_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0"; "E22_of"; "o13p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oe.Start8StatesB"; "GPC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes"; "eager_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3"; "null_rw_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oe.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8StatesA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oe.Start8StatesB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition S22ok_of (v : bool) : axst := pick v S22okA S22okB.
Lemma S22ok_eq : ltac2:(tb__ "0|0|
SeS0S6S39S36R1A1Z100000Pa0A3S2bR1A1A3Fv;").
Proof. intros [|]; reflexivity. Qed.
Definition E23_of (v : bool) : axst := pick v E23A E23B.
Lemma run23 : ltac2:(tb__ "0|1|
SeS0S11SfS2A1M0A1S4S1eS32S33S20S21S1fS1fS1fS22A1A1A1A1A1A1A1ScSaZ706a0ScSaZ6bf18SdSaA1A3A3S2bR1A1S12A5S10G0ScS2S3S28R1A1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact run23A | exact run23B]. Qed.
Definition SPIN22_of (v : bool) : axst := pick v SPIN22A SPIN22B.
Lemma run22_fail : ltac2:(tb__ "0|1|
SeS0S11SfS2A1M0A1S4S1eU12cScSaZ6bf18SdSaA1A3S34S36R1A1A1S12A5S10G0ScS2S3S2fR1A1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact run22A_fail | exact run22B_fail]. Qed.
Lemma spin22 : ltac2:(tb__ "0|2|
SeS0S11SfS2A1M0A1S4S1eU2ScSaZ6bf18SdSaA1A3S2fR1A1M1S12A5S10G0ScS2S3G1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact spin22A | exact spin22B]. Qed.
Lemma E23_at : ltac2:(tb__ "0|5|
SeS1S0SaS1cS5S28R1A1M0A1M1A1M2Z706a0A3S1S0SbS1bG1A1Pa0A3S1S0S11S26A1S24S1eG2A2S10S26S27A2A3S1S0SfS13S17S17A2M3A1S7G0A1SdG3A1A3S1S0S17S8G0A1S18S35A1A3S1S0S17S19G1Z11A2S18ZdeA1A3S1S0S17S19G1ZaA2S18Z0A1M4A3S1S0S17S19G1ZbA2S18Z800000A1A3S1S0S17S19G1ZcA2S18Z3A1A3S1S0S17S19G1ZdA2S18Z4022A1A3S1S0S17S19G1ZeA2S18ZffffffffffffffffA1A3S0S17S19G1ZfA2G4A3A2A2A2A2A2A2A2A2A2A2A2Fv;").
Proof. intros [|]; [exact E23A_at | exact E23B_at]. Qed.
Definition S23ok0_of (v : bool) : axst := pick v S23ok0A S23ok0B.
Lemma S23ok0_eq : ltac2:(tb__ "0|0|
SeS0S6S3aS28R1A1Z800000Pa1A3S2cR1A1A3Fv;").
Proof. intros [|]; reflexivity. Qed.
Definition S23ok_of (v : bool) : axst := pick v S23okA S23okB.
Lemma S23ok_eq : ltac2:(tb__ "0|3|
SeS1S0S6S9S2cR1A1M0S25S5G0A1M1S14S1aS1dG1A1ScS1aS37SdS1aA1A3A3A2M2A2S2dR1A1A3S0SeS3bG1G2A2S12A3A2Fv;").
Proof. intros [|]; [exact S23okA_eq | exact S23okB_eq]. Qed.
Definition E24_of (v : bool) : axst := pick v E24A E24B.
Lemma run24 : ltac2:(tb__ "0|1|
SeS0S11SfS2A1M0A1S4S1eS32S33S20S21S1fS1fS1fS22A1A1A1A1A1A1A1ScSaZ706a0ScSaZ6bf18SdSaA1A3A3S2dR1A1S12A5S10G0ScS2S3S29R1A1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact run24A | exact run24B]. Qed.
Definition SPIN23_of (v : bool) : axst := pick v SPIN23A SPIN23B.
Lemma run23_fail : ltac2:(tb__ "0|1|
SeS0S11SfS2A1M0A1S4S1eU12cScSaZ6bf18SdSaA1A3S34S28R1A1A1S12A5S10G0ScS2S3S30R1A1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact run23A_fail | exact run23B_fail]. Qed.
Lemma spin23 : ltac2:(tb__ "0|2|
SeS0S11SfS2A1M0A1S4S1eU2ScSaZ6bf18SdSaA1A3S30R1A1M1S12A5S10G0ScS2S3G1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact spin23A | exact spin23B]. Qed.
Lemma E24_at : ltac2:(tb__ "0|5|
SeS1S0SaS1cS5S29R1A1M0A1M1A1M2Z706a0A3S1S0SbS1bG1A1Pa1A3S1S0S11S26A1S24S1eG2A2S10S26S27A2A3S1S0SfS13S17S17A2M3A1S7G0A1SdG3A1A3S1S0S17S8G0A1S18S35A1A3S1S0S17S19G1Z11A2S18ZdeA1A3S1S0S17S19G1ZaA2S18Z0A1M4A3S1S0S17S19G1ZbA2S18Z1000A1A3S1S0S17S19G1ZcA2S18Z3A1A3S1S0S17S19G1ZdA2S18Z22A1A3S1S0S17S19G1ZeA2S18ZffffffffffffffffA1A3S0S17S19G1ZfA2G4A3A2A2A2A2A2A2A2A2A2A2A2Fv;").
Proof. intros [|]; [exact E24A_at | exact E24B_at]. Qed.
Definition S24ok_of (v : bool) : axst := pick v S24okA S24okB.
Lemma S24ok_eq : ltac2:(tb__ "0|0|
SeS0S6S39S29R1A1Z1000Pa2A3S2eR1A1A3Fv;").
Proof. intros [|]; reflexivity. Qed.
Definition EG_of (v : bool) : axst := pick v EGA EGB.
Lemma runG : ltac2:(tb__ "0|1|
SeS0S11SfS2A1M0A1S4S1eS32S33S20S21S1fS1fS1fS22A1A1A1A1A1A1A1ScSaS38ScSaZ706a0ScSaZ6bf18SdSaA1A3A3A3S2eR1A1S12A5S10G0ScS2S3S2aR1A1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact runGA | exact runGB]. Qed.
Definition SPIN24_of (v : bool) : axst := pick v SPIN24A SPIN24B.
Lemma run24_fail : ltac2:(tb__ "0|1|
SeS0S11SfS2A1M0A1S4S1eU12cScSaZ6bf18SdSaA1A3S34S29R1A1A1S12A5S10G0ScS2S3S31R1A1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact run24A_fail | exact run24B_fail]. Qed.
Lemma spin24 : ltac2:(tb__ "0|2|
SeS0S11SfS2A1M0A1S4S1eU2ScSaZ6bf18SdSaA1A3S31R1A1M1S12A5S10G0ScS2S3G1S23A2SdS2A1A3A2A3Fv;").
Proof. intros [|]; [exact spin24A | exact spin24B]. Qed.
Lemma EG_at : ltac2:(tb__ "0|3|
SeS1S0SaS1cS5S2aR1A1M0A1M1A1S38A3S1S0SbS1bG1A1Pa2A3S1S0SfS13S17S17A2M2A1S7G0A1SdG2A1A3S1S0S17S8G0A1S18S35A1A3S0S16S15S1aS1dG1A1A2U31A3A2A2A2A2Fv;").
Proof. intros [|]; [exact EGA_at | exact EGB_at]. Qed.
End Start8States.

(* [comment removed for export] *)
Module Start8CallA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "list"; "bool"; "option"; "prod"; "Some"; "app"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallA"; "C22Ag"; "C22Aa"; "IGA"; "C22Ae"; "IGAf"; "MAINA"; "C22A"; "R22A"; "s22A"; "RMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_facts"; "ss_objs"; "sstate"; "sprop"; "ss_pc"; "SLit"; "ss_regs"; "sprop_below"; "ss_next"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "sym_runA"; "ax_X"; "ax_base"; "la_state"; "mkAX"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs"; "MAINPC"; "PGA"; "PGB"; "splits22"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Start8RegGlob"; "Pre_G2"; "P_G2"; "Posts_G2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8StatesA"; "EGA"; "GPC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "zero_page_obj"; "ax_setX"; "ax_with_facts"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "split_chain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface"; "regglob_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Start8RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8StatesA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition C22Aa : sstate := Eval vm_compute in (match split_chain (ax_S EGA) splits22 with Some St => St | None => ax_S EGA end).
Lemma split22A_ok : ltac2:(tb__ "0|0|
S0S9S1dA1S40S25S36A1S31A2SbS1dS10A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition C22Ae : sstate := Eval vm_compute in set_objs C22Aa (ss_objs C22Aa ++ [zero_page_obj PGA]).
Definition C22Ag : sstate := Eval vm_compute in set_objs C22Ae (ss_objs C22Ae ++ [zero_page_obj PGB]).
Lemma C22Ae_facts : ltac2:(tb__ "0|3|
S1S0S1dS3aS10ScS1aS1cS10A1S4S1aS3cS2fA1S5S1aA1M0A3A3A2M1S12A3S1S0S8S39S10G1A2S6A3S1S0S1dS3aS12ScS1aS1cS12A1S4S1aS3cS30A1G0A3A3A2M2SfA3S0S8S39S12G2A2S6A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C22A : axst := ltac2:(tb__ "0|0|
S2cSfS5SaS19S19A2A1S20S38A1A3").
Lemma C22A_at : ltac2:(tb__ "0|1|
S1S0S2S1fSfA1S37A3S1S0S3S23SfA1Pa2A3S1S0SeSdS1aS1cSfA1A2U42A3S1S0S8S24SfA1S6A3S1S0S7S1eA1S1bSfA1S1bS25S36A1M0A1A3S1S0S7S19A1S21SfA1S21G0A1A3S0SeSdS1aS1cS10A1A2U40A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C22A_facts_below : ltac2:(tb__ "0|0|
S0S8S45S1eS22Pa2A1S1bSfA1A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition owinA : sobj := Eval vm_compute in ob22 C22Ag 56.
Definition s22A : wsub := Eval vm_compute in mk_s22 C22Ag owinA.
Definition R22A : list sobj := Eval vm_compute in (match entails_frA C22A Pre_G2 s22A with Some R => R | None => [] end).
Lemma ent22A : ltac2:(tb__ "0|1|
S0S9S7S1aA1M0A1S43S15S33S17A3SbG0S16A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk22A : ltac2:(tb__ "0|0|
S0S8S42S15S33S17S16S3fS26S27S2bS35A4A5S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R22A_len : length R22A = 51%nat. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IGA : axst := Eval vm_compute in (import_postA s22A Pre_G2 P_G2 C22A R22A).
Lemma IGA_eq : ltac2:(tb__ "0|0|
S0S27S44S17S33S34S15S16A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IGAf : axst := Eval vm_compute in (ax_with_facts (ax_setX IGA []) (ss_facts (ax_S IGA) ++ ss_facts C22Ag)).
Lemma IGAf_eq : ltac2:(tb__ "0|0|
S0S27S3eS3dS11S5SaS19S19A2A1A2ScS1eS1bS25S11A1A1S1bSfA1A3A2S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IGA_at : ltac2:(tb__ "0|1|
S1S0S2S1fS25S11A1A1S41A3S0S7SaS19S19A2M0A1S29S11A1S5G0A1A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition RMA_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S28S32Ubb8S4S2S2eS4S2Z706a0S4S2Z6bf18S5S2A1A3A3A3S13S6A5").
Local Strategy expand [RMA_run__R].
Definition RMA : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) RMA_run__R).
Lemma RMA_run : ltac2:(tb__ "0|0|
S0S9S7S26A1A1S28S32Ubb8S4S2S2eS4S2Z706a0S4S2Z6bf18S5S2A1A3A3A3S13S6A5S18A3").
Proof. exact (@eq_refl (option (list leafA)) RMA_run__R <: RMA_run__R = RMA). Qed.
Definition MAINA : axst := Eval vm_compute in (match RMA with Some (l :: _) => la_state l | _ => IGAf end).
Lemma runMA : ltac2:(tb__ "0|1|
S0S9S7S26A1M0A1S28S32Ubb8S4S2S2eS4S2Z706a0S4S2Z6bf18S5S2A1A3A3A3S13S6A5SbG0S4S26S2dS14S3bA2S5S26A1A3A2A3").
Proof. rewrite RMA_run. reflexivity. Qed.
Lemma MAINA_at : ltac2:(tb__ "0|1|
S1S0S2S1fS25S14A1A1S2eA3S1S0S7SaS19S19A2M0A1S29S14A1S5G0A1A3S0S19S2aS14A1S20S38A1A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start8CallA.

(* [comment removed for export] *)
Module Start8CallB.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "list"; "bool"; "option"; "prod"; "Some"; "app"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallB"; "C22Bg"; "C22Ba"; "IGB"; "C22Be"; "IGBf"; "MAINB"; "C22B"; "R22B"; "s22B"; "RMB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_facts"; "ss_objs"; "sstate"; "sprop"; "ss_pc"; "SLit"; "ss_regs"; "sprop_below"; "ss_next"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "sym_runA"; "ax_X"; "ax_base"; "la_state"; "mkAX"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs"; "MAINPC"; "PGA"; "PGB"; "splits22"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Start8RegGlob"; "Pre_G2"; "P_G2"; "Posts_G2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oe.Start8StatesB"; "EGB"; "GPC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "zero_page_obj"; "ax_setX"; "ax_with_facts"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "split_chain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface"; "regglob_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.StartGlueC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ns.Start8RegGlob OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oe.Start8StatesB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition C22Ba : sstate := Eval vm_compute in (match split_chain (ax_S EGB) splits22 with Some St => St | None => ax_S EGB end).
Lemma split22B_ok : ltac2:(tb__ "0|0|
S0S9S1dA1S40S25S36A1S31A2SbS1dS10A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition C22Be : sstate := Eval vm_compute in set_objs C22Ba (ss_objs C22Ba ++ [zero_page_obj PGA]).
Definition C22Bg : sstate := Eval vm_compute in set_objs C22Be (ss_objs C22Be ++ [zero_page_obj PGB]).
Lemma C22Be_facts : ltac2:(tb__ "0|3|
S1S0S1dS3aS10ScS1aS1cS10A1S4S1aS3cS2fA1S5S1aA1M0A3A3A2M1S12A3S1S0S8S39S10G1A2S6A3S1S0S1dS3aS12ScS1aS1cS12A1S4S1aS3cS30A1G0A3A3A2M2SfA3S0S8S39S12G2A2S6A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition C22B : axst := ltac2:(tb__ "0|0|
S2cSfS5SaS19S19A2A1S20S38A1A3").
Lemma C22B_at : ltac2:(tb__ "0|1|
S1S0S2S1fSfA1S37A3S1S0S3S23SfA1Pa2A3S1S0SeSdS1aS1cSfA1A2U42A3S1S0S8S24SfA1S6A3S1S0S7S1eA1S1bSfA1S1bS25S36A1M0A1A3S1S0S7S19A1S21SfA1S21G0A1A3S0SeSdS1aS1cS10A1A2U40A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C22B_facts_below : ltac2:(tb__ "0|0|
S0S8S45S1eS22Pa2A1S1bSfA1A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition owinB : sobj := Eval vm_compute in ob22 C22Bg 56.
Definition s22B : wsub := Eval vm_compute in mk_s22 C22Bg owinB.
Definition R22B : list sobj := Eval vm_compute in (match entails_frA C22B Pre_G2 s22B with Some R => R | None => [] end).
Lemma ent22B : ltac2:(tb__ "0|1|
S0S9S7S1aA1M0A1S43S15S33S17A3SbG0S16A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk22B : ltac2:(tb__ "0|0|
S0S8S42S15S33S17S16S3fS26S27S2bS35A4A5S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R22B_len : length R22B = 51%nat. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IGB : axst := Eval vm_compute in (import_postA s22B Pre_G2 P_G2 C22B R22B).
Lemma IGB_eq : ltac2:(tb__ "0|0|
S0S27S44S17S33S34S15S16A5S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IGBf : axst := Eval vm_compute in (ax_with_facts (ax_setX IGB []) (ss_facts (ax_S IGB) ++ ss_facts C22Bg)).
Lemma IGBf_eq : ltac2:(tb__ "0|0|
S0S27S3eS3dS11S5SaS19S19A2A1A2ScS1eS1bS25S11A1A1S1bSfA1A3A2S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IGB_at : ltac2:(tb__ "0|1|
S1S0S2S1fS25S11A1A1S41A3S0S7SaS19S19A2M0A1S29S11A1S5G0A1A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition RMB_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S28S32Ubb8S4S2S2eS4S2Z706a0S4S2Z6bf18S5S2A1A3A3A3S13S6A5").
Local Strategy expand [RMB_run__R].
Definition RMB : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) RMB_run__R).
Lemma RMB_run : ltac2:(tb__ "0|0|
S0S9S7S26A1A1S28S32Ubb8S4S2S2eS4S2Z706a0S4S2Z6bf18S5S2A1A3A3A3S13S6A5S18A3").
Proof. exact (@eq_refl (option (list leafA)) RMB_run__R <: RMB_run__R = RMB). Qed.
Definition MAINB : axst := Eval vm_compute in (match RMB with Some (l :: _) => la_state l | _ => IGBf end).
Lemma runMB : ltac2:(tb__ "0|1|
S0S9S7S26A1M0A1S28S32Ubb8S4S2S2eS4S2Z706a0S4S2Z6bf18S5S2A1A3A3A3S13S6A5SbG0S4S26S2dS14S3bA2S5S26A1A3A2A3").
Proof. rewrite RMB_run. reflexivity. Qed.
Lemma MAINB_at : ltac2:(tb__ "0|1|
S1S0S2S1fS25S14A1A1S2eA3S1S0S7SaS19S19A2M0A1S29S14A1S5G0A1A3S0S19S2aS14A1S20S38A1A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start8CallB.

