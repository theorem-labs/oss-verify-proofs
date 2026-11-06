(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3 Start4States.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require MuslMemset.

(* [comment removed for export] *)
Module RegGlob.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "nat"; "cons"; "list"; "true"; "bool"; "nil"; "option"; "None"; "Some"; "false"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "ss_regs"; "ss_next"; "valuation"; "DUnknown"; "FcsrFrm0"; "SVar"; "cell"; "mkObj"; "mkSS"; "sobj"; "sprop"; "ss_facts"; "ss_objs"; "ss_pc"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "sym_runA"; "mkLeafA"; "ax_setS"; "axwf"; "entailsA"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.RegGlob"; "E_G"; "P_G"; "CUTS_G"; "FUEL_G"; "NPG"; "NPOST_G"; "Posts_G"; "junk_regs"; "sub_G"; "O_gstk'"; "leaf1G"; "post_regs_G"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface"; "Pre_G"; "facts_G"; "regglob_ret"; "vS0"; "D_G"; "fregs_G"; "vRA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@Stdlib.PArith.BinPos.Pos"; "add"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Lists.List"; "existsb"; "@Stdlib.ZArith.BinInt.Z"; "opp"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CompleteA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition leaf1G (A : axst) (o : option (list leafA)) : axst := ltac2:(tb__ "0|1|
S6S2S20A1M0A1S22Lo;Vo;G0G0S22Ll0;R1VA;S20G0G0S22Ll1;R1S28R2A1S20G0VA;Ll3;Ll2;X2x2Ll1;Ll;X2x2Ll0;VA;X6x2").
Definition run_toG (fuel : nat) (cuts : list Z) (A : axst) : axst := ltac2:(tb__ "0|0|
S33VA;S23ScVfuel;Vcuts;VA;S3A5A2").

Definition CUTS_G : list Z := [regglob_ret].
Definition FUEL_G : nat := 13500%nat.

Definition run_G__R : option (list leafA) := ltac2:(tb__ "0|0|
S23ScS2cS2bS3aS3A5").
Local Strategy expand [run_G__R].
Definition E_G : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1G Pre_G (ro1__)))) run_G__R).
Lemma run_G : ltac2:(tb__ "0|1|
SdS6S2S20A1M0A1S23ScS2cS2bS3aS3A5S8G0S1S20S24S29S41A2S5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_G__R <: run_G__R = Some [mkLeafA E_G RsCut]). Qed.

Lemma E_G_at : ltac2:(tb__ "0|3|
SeSdS39S1eS21S29A1M0A1S3cA3SeSdS38S12G0A1S35A3SeSdS2S1bA1S1cG0A1S3bA3SeSdSfS36SfU1S11G0A1M1S10Z0A1M2A4S40A3SdSfS36SfU2G1G2A4S3dA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition junk_regs : list nat := ltac2:(tb__ "0|0|
S1S0U5S1S0U6S1S0U7S1S0UaS1S0UbS1S0UcS1S0UdS1S0UeS1S0UfS1S0U10S1S0U11S5S0A1A3A3A3A3A3A3A3A3A3A3A3").
Definition NPG : positive := 100.
Definition NPOST_G : positive := 132.
Definition post_reg_G (r : nat) : sv := ltac2:(tb__ "0|0|
S4SfL_;S50S0S4fVr;A1S30A3S16S48S2dS49Vr;A1A2A1S36SfVr;S11S21S29A1A1S10Z0A1A4X4x2").
Definition post_regs_G : list sv := map post_reg_G (seq 0 32).

Definition O_gstk' : sobj := ltac2:(tb__ "0|0|
S18S3dS10S51S3eA1A1S10Z0A1S5S17A1S14A5").
Definition P_G0 : axst := ltac2:(tb__ "0|0|
S25S29S19S3cS34S3fS15S7SfA1S42S1aS1dS21S29A1A1U0S32A4S3bS2eS9A9A2").
Definition P_G : axst := Eval vm_compute in P_G0.
Definition Posts_G : list leafA := ltac2:(tb__ "0|0|
S1S20S24S2aS41A2S5S20A1A3").

Definition sub_G : wsub := ltac2:(tb__ "0|0|
S37S0SbS38SfA2S0SaS38SfS48S2dS49R1A1A2S36SfR1S11S21S29A1A1S10Z0A1A4A4Lr;S30A4").
Lemma ent_G : ltac2:(tb__ "0|0|
SdS4S27S29S2aS31A3S3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma wid_G : ltac2:(tb__ "0|0|
SdS4S4eS31S35A2S3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma P_G_wf : ltac2:(tb__ "0|1|
SeSdS4S26S2aA1S3A3SeSdS4S1fS21S2aA1M0A1S3A3SdS38S12G0A1S2eA3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Theorem regglob_sum : ltac2:(tb__ "0|0|
S4dOF_;S45S13S2S4aQ40A1A1S47ScR4R3A3S46ScS35R4A3S4cScR6S44ScR5S3aR4R3A5S43ScR5S35R4R3S2fA6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_seq.
  { apply triple1_triple. eapply sym_run_soundA; [exact run_G | exact Hok | reflexivity | exact Hst]. }
  apply triple_LQA_of_leaves. intros L rho1 [<-|[]] Hag. cbn [la_state].
  eapply (triple_entailsA segsA ok J NF E_G P_G sub_G rho1 tp); [exact ent_G | exact wid_G | exact Hst |].
  eapply triple_conseq; [ | intros w Hw; exact Hw | apply triple_refl ].
  intros w Hw. eapply (LQA_intro segsA J NF rho tp (mkLeafA P_G RsCut)); [left; reflexivity | | exact Hw].
  eapply agree_below_trans; [exact Hag | apply rho_sub_agree; exact wid_G].
Qed.

Theorem regglob_sum_ex : ltac2:(tb__ "0|0|
S45S13S2S4aQ40A1A1S46ScS35R3A3S4bScS44ScR4S3aR3R2A5S43ScR4S35R3R2S2fA6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_seq.
  { eapply sym_run_etripleA; [reflexivity | exact Hst | exact run_G]. }
  apply etriple_LQA_of_leaves. intros L rho1 [<-|[]] Hag. cbn [la_state].
  eapply (etriple_entailsA segsA J NF E_G P_G sub_G rho1 tp); [exact ent_G | exact wid_G | exact Hst |].
  eapply etriple_conseq; [ | intros w Hw; exact Hw | apply etriple_refl ].
  intros w Hw. eapply (LQA_intro segsA J NF rho tp (mkLeafA P_G RsCut)); [left; reflexivity | | exact Hw].
  eapply agree_below_trans; [exact Hag | apply rho_sub_agree; exact wid_G].
Qed.
End RegGlob.

(* [comment removed for export] *)
Module Start4FailStates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start4FailStates"; "F0"; "RUN1"; "FUEL1"; "PC_OUT"; "PC_SPIN"; "@Corelib.Init.Datatypes"; "list"; "option"; "cons"; "nil"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "axst"; "la_state"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Corelib.Init.Logic"; "eq"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition F0 : axst := fail_state E_k8x.
Definition PC_OUT : Z := 0x7360c.
Definition PC_SPIN : Z := 0x6bd84.
Definition FUEL1 : nat := 2500%nat.
Definition RUN1_eq__R : option (list leafA) := ltac2:(tb__ "0|0|
SeSfS2S7SaS3S7SaS4S8SaA1A3A3S0S9A5").
Local Strategy expand [RUN1_eq__R].
Definition RUN1 : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) RUN1_eq__R).
Lemma RUN1_eq : ltac2:(tb__ "0|0|
S10S6S5SbA1A1SeSfS2S7SaS3S7SaS4S8SaA1A3A3S0S9A5S1A3").
Proof. exact (@eq_refl (option (list leafA)) RUN1_eq__R <: RUN1_eq__R = RUN1). Qed.
Definition L1a : axst := ltac2:(tb__ "0|1|
S6S5SbA1M0A1ScLx;S1G0G0ScLl0;R1S0SbG0SdR2A1Ll1;Ll;X5x2Ll0;S0X6x2").
Definition L1b : axst := ltac2:(tb__ "0|1|
S6S5SbA1M0A1ScLx;S1G0G0ScLl0;R1S0SbG0G0ScLl2;R1S0SbG0SdR2A1Ll3;Ll;X5x2Ll2;Ll1;X5x2Ll0;S0X6x2").
End Start4FailStates.

(* [comment removed for export] *)
Module Start5States.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "bool"; "nat"; "pair"; "Some"; "option"; "list"; "prod"; "app"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sobj"; "sprop"; "SVar"; "SPUle"; "sprop_eqb"; "sstate"; "ss_objs"; "SAlu"; "SPAlign"; "mkCell"; "ob_cells"; "ss_facts"; "SPEq"; "enc_bytes"; "ss_next"; "ss_pc"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "mkLeafA"; "mkAX"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start5States"; "L12r"; "C12c"; "C12d"; "o12rtc2a"; "RIP_ENTRY"; "SPIN12"; "o12rtc2"; "C12e"; "L12x"; "S_s12ok"; "o12rtc2b"; "rX12"; "F12"; "splits12"; "@Stdlib.Lists.List"; "existsb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "replace_obj_at"; "add_cell_front"; "cells_clear_lit"; "unknown_obj_at"; "split_chain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "E_k12d"; "SPIN_MMAPORDIE"; "ECALL_MMAP"; "fail_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "image_bytes"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "axA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "mmap_obj"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA Start4States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition RIP_ENTRY : Z := 0x5ff44.

Definition F12 : list sprop := ltac2:(tb__ "0|3|
S0S10S17P24M0ZcA2S0S10S12SdZ1000M1A1S11G0A1M2A2S0S10S12G2SdS44Z7fffff800000G1A2A1A2S2S10A1A3A3A3").
Definition S_s12ok : axst := ltac2:(tb__ "0|2|
S47S4aS34S4bS22S3dA1M0S11P24M1A1SaSfS15G0A1S0SfS4cG1Z1000A2S2SfA1A3A3P25A4A2A1").

Definition run12a__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S27Ufa0S0S1fS2cS0S1fS3fS2S1fA1A3A3S31S1A5").
Local Strategy expand [run12a__R].
Definition L12r : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 S_s12ok (ro1__)))) run12a__R).
Definition run12_fail__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S27Uc8S0S1fS3eS2S1fA1A3S40S3dA1S1A5").
Local Strategy expand [run12_fail__R].
Definition SPIN12 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 (fail_state E_k12d) (ro2__)))) run12_fail__R).
Lemma run12a : ltac2:(tb__ "0|1|
SbS7S8S21A1M0A1S23S27Ufa0S0S1fS2cS0S1fS3fS2S1fA1A3A3S31S1A5S6G0S0S21S24S28S42A2S2S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run12a__R <: run12a__R = Some [mkLeafA L12r RsCut]). Qed.
Lemma run12_fail : ltac2:(tb__ "0|1|
SbS7S8S21A1M0A1S23S27Uc8S0S1fS3eS2S1fA1A3S40S3dA1S1A5S6G0S0S21S24S2dS42A2S2S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run12_fail__R <: run12_fail__R = Some [mkLeafA SPIN12 RsCut]). Qed.
Lemma spin12 : ltac2:(tb__ "0|1|
SbS7S8S21A1M0A1S23S27U2S0S1fS3eS2S1fA1A3S2dS1A5S6G0S0S21S24S2dS42A2S2S21A1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L12r_at : ltac2:(tb__ "0|1|
ScSbS1fS1eS22S28A1M0A1S2cA3SbS20S1dG0A1P25A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition rX12 : sv * sv := ltac2:(tb__ "0|0|
S5SeSeS16S48S11P1A1SdN100000A1A3SdS44Z100000Z40A2A1A4").
Definition L12x : axst := Eval vm_compute in (mkAX (unknown_obj_at (ax_S L12r) 0) [rX12] (SLit SHB)).
Lemma L12x_eq : ltac2:(tb__ "0|1|
SbS26S25S3bS22S28A1U0A2S0S9SeSeA2M0S33S2G0A1A3SdS46A1A3S30A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_L12u : ltac2:(tb__ "0|1|
SbS3S41S22S28A1M0S3bG0U0A2A2S1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma L12r_facts35 : ltac2:(tb__ "0|2|
ScSbS3S36S10S13S1bS16S49S11P23A1M0SdZ3A1A3S11P22A1A2A1S1aS22S28A1A1M1A3S1A3SbS3S36S10S13S12G0SdS44S45Z2Z3dA2Z1A2A1A2A1G1A3S1A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma L12r_facts1 : ltac2:(tb__ "0|3|
ScSbS3S36S10S13S17P1M0Z4A2A1S1aS22S28A1A1M1A3S1A3ScSbS3S36S10S13S12SdZ7fff80000000A1S11G0A1M2A2A1G1A3S1A3SbS3S36S10S13S12G2SdZ7fffffffff20A1A2A1G1A3S1A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition splits12 : list (nat * sv) := ltac2:(tb__ "0|1|
S0S9S4SeA2M0S5S4SeU0SdNc20A1A4S0G0S5S4SeU1SdNbd0A1A4S0G0S5S4SeU8SdZe7bd8A1A4S0G0S5S4SeU9SdZe8978A1A4S0G0S5S4SeUaSdZf13f8A1A4S0G0S5S4SeUbSdZf1404A1A4S0G0S5S4SeUcSdZf20e0A1A4S0G0S5S4SeUdSdZf20f8A1A4S2G0A1A3A3A3A3A3A3A3A3").
Definition C12c : sstate := Eval vm_compute in (match split_chain (ax_S L12x) splits12 with Some St => St | None => ax_S L12x end).
Lemma split12_ok : ltac2:(tb__ "0|0|
SbS7S14A1S3cS22S30A1S35A2S6S14S29A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition o12rtc2 : sobj := Eval vm_compute in (nth 13 (ss_objs C12c) (mkObj (SLit 0) (SLit 0) (SLit 0) [] DZero)).
Lemma o12rtc2_nth : ltac2:(tb__ "0|0|
SbS7SfA1S37SfS15S29A1UdA3S6SfS2eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition o12rtc2a : sobj := ltac2:(tb__ "0|0|
S39S2eS18SdZf20f0A1Z8SdZ0A1A3A2").
Definition C12d : sstate := Eval vm_compute in (replace_obj_at C12c 13 o12rtc2a).
Lemma C12d_eq : ltac2:(tb__ "0|0|
SbS14S38S29UdS2bA3S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_C12d : ltac2:(tb__ "0|0|
SbS3S41S29S38S29UdS2bA3A2S1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma o12rtc2a_nth : ltac2:(tb__ "0|0|
SbS7SfA1S37SfS15S2aA1UdA3S6SfS2bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition o12rtc2b : sobj := ltac2:(tb__ "0|0|
S39S2bS18SdZf20e8A1Z8SdZ0A1A3A2").
Definition C12e : sstate := Eval vm_compute in (replace_obj_at C12d 13 o12rtc2b).
Lemma C12e_eq : ltac2:(tb__ "0|0|
SbS14S38S2aUdS32A3S2fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma same_C12e : ltac2:(tb__ "0|0|
SbS3S41S2aS38S2aUdS32A3A2S1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma rtc2_clear : ltac2:(tb__ "0|1|
ScSbS3S3aS19S2eA1Zf20f0Z8M0A3S1A3SbS3S3aS19S2bA1Zf20e8G0A3S1A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma rtc2_img : ltac2:(tb__ "0|4|
ScSbS7S8S4eQ8A1A1M0A1M1S43S27Zf20f0U8M2A3S6G0S1cG2S4dQ40Z0A2A2A2M3A3SbG1S43S27Zf20e8G2A3G3A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition C12 : axst := ltac2:(tb__ "0|1|
S25S2fS0S9SeSeA2M0S33S2G0A1A3SdS46A1A3").
End Start5States.

(* [comment removed for export] *)
Module Str_memcpyAH.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "None"; "false"; "list"; "prod"; "true"; "app"; "bool"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sprop"; "SLit"; "sv"; "sobj"; "sstate"; "SPBranch"; "FcsrFrm0"; "SAlu"; "cell"; "mkSS"; "SPUle"; "holds"; "valuation"; "DUnknown"; "SPAlign"; "mkObj"; "mkCell"; "SExt"; "SPNot"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "NPOST"; "post_regs"; "pre_regs"; "cut_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "mkVN"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "ALU_ADD"; "ALU_AND"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memcpyAH.States"; "F_ah"; "N14a"; "O_srcH"; "O_dst0"; "P_ah1"; "P_ah2"; "C0_ah"; "C1_ah"; "HV"; "O_dstH"; "Pre_ah"; "Z_ah1"; "Z_ah2"; "B120a"; "B121a"; "F_c1a"; "F_z"; "Fge16"; "J120a"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "memcpy_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memcpyAH"; "FUELAH"; "cutpcs_ah"; "Posts_ahA"; "Pre_ahA"; "cuts_ahA"; "Z_ah"; "exits_ahA"; "vcuts_ahA"; "vexits_ahA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "@Corelib.Init.Logic"; "False"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section States.
Variable base : Z.

Definition HV : positive := 16%positive.
Definition N14a : sprop := SPUle (SVar 14) (SLit two62).

Definition F_ah : list sprop := ltac2:(tb__ "0|1|
S0SdS1bPcZ2M0A2S0SdS1bPdG0A2S0SdS17SeZ4A1ScPeA1A2S1SdA1A3A3A3").
Definition O_dst0 : sobj := ltac2:(tb__ "0|0|
S1cScPcA1SeZ0A1ScPeA1S1S15A1S1aA5").
Definition O_dstH : sobj := ltac2:(tb__ "0|1|
S1cScPcA1SeZ0A1M0ScPeA1S0S15S1dG0Z4S1eS8Q20ScS37A1A3A3S1S15A1A3S1aA5").
Definition O_srcH : sobj := ltac2:(tb__ "0|1|
S1cScPdA1SeZ0A1M0ScPeA1S0S15S1dG0Z4ScS37A1A3S1S15A1A3S1aA5").

Definition Pre_ah : sstate := ltac2:(tb__ "0|0|
S16Vbase;S27S23S13S4SfA1S0S10S32S0S10S31S1S10A1A3A3S0SdS30S2fA3S22S5A9").

Definition Fge16 : sprop := ltac2:(tb__ "0|0|
S1fS12S2bScPeA1SeZ10A1A3A1").
Definition C0_ah : sstate := ltac2:(tb__ "0|1|
S16S42Vbase;Z12cA2S24S27S0S7S2SfA2M0S3S2SfUdScPcA1A4S0G0S3S2SfUeSeZfA1A4S0G0S3S2SfUfSeZ0A1A4S1G0A1A3A3A3A2S23S13S4SfA1S0S10S32S0S10S31S1S10A1A3A3S0SdS40S0SdS30S2fA3A3S22S5A9").

Definition J120a : sprop := ltac2:(tb__ "0|0|
S17S14S2cScP78A1ScP79A1A3ScPeA1A2").
Definition B120a : sprop := SPUle (SVar 120) (SLit two62).
Definition B121a : sprop := SPUle (SVar 121) (SLit two62).
Definition F_c1a : list sprop := ltac2:(tb__ "0|1|
S0SdS12S2bSeZfA1ScP79A1A3S0SdS1bP78M0Z4A2S0SdS17SeZ10A1ScG0A1A2S0SdS41S0SdS3cS0SdS3dS1SdA1A3A3A3A3A3A3").
Definition C1_ah : sstate := ltac2:(tb__ "0|3|
S16S42Vbase;Z12cA2S24S28S22A1S0S7S2SfA2M0S3S2SfUaScPcA1M1A4S0G0S3S2SfUbS14S2cScPdA1ScP78A1M2A3A4S0G0S3S2SfUcScP79A1A4S0G0S3S2SfUdS14S2cG1G2A3A4S0G0S3S2SfUeSeZfA1A4S1G0A1A3A3A3A3A3A2S23S13S4SfA1S0S10S38S0S10S31S1S10A1A3A3S9SdS3eS0SdS30S2fA3A3P87S5A9").

Definition P_ah (off : Z) : sstate := ltac2:(tb__ "0|1|
S16S42Vbase;Voff;A2S24S26S22A1S0S7S2SfA2M0S3S2SfUaScPcA1A4S1G0A1A3A2S23S13S4SfA1S0S10S38S0S10S31S1S10A1A3A3S0SdS30S2fA3S25S5A9").
Definition P_ah1 : sstate := P_ah 0x3d0.
Definition P_ah2 : sstate := P_ah 0x400.
Definition Posts_ah : list leaf := ltac2:(tb__ "0|0|
S0S4dS4fS33S4eA2S0S4dS4fS34S4eA2S1S4dA1A3A3").

Definition F_z : list sprop := ltac2:(tb__ "0|1|
S0SdS12S2bScPeA1M0SeZ10A1A3S0SdS12S2bG0SeZ8A1A3S0SdS12S2eS14S2dG0SeZ4A1A3SeZ0A1A3S1SdA1A3A3A3").
Definition Z_ah (off : Z) : sstate := ltac2:(tb__ "0|1|
S16S42Vbase;Voff;A2S24S26S22A1S0S7S2SfA2M0S3S2SfUaScPcA1A4S1G0A1A3A2S23S13S4SfA1S0S10S32S0S10S31S1S10A1A3A3S9SdS3fS0SdS30S2fA3A3S25S5A9").
Definition Z_ah1 : sstate := Z_ah 0x3d0.
Definition Z_ah2 : sstate := Z_ah 0x400.

Definition cuts_ah : list sstate := ltac2:(tb__ "0|0|
S0S11S39S0S11S35S0S11S36S1S11A1A3A3A3").
Definition exits_ah : list sstate := ltac2:(tb__ "0|0|
S0S11S33S0S11S34S0S11S3aS0S11S3bS1S11A1A3A3A3A3").
Definition cutpcs_ah : list Z := [base + 0x12c].

Definition vcuts_ah : list vnode := ltac2:(tb__ "0|1|
S0S29S2aS39ZaSeZ0A1M0A3S0S29S2aS35Z9G0A3S0S29S2aS36Z7ScP79A1A3S1S29A1A3A3A3").
Definition vexits_ah : list vnode := ltac2:(tb__ "0|2|
S0S29S2aS33Z0M0SeG0A1M1A3S0S29S2aS34G0G1A3S0S29S2aS3aG0G1A3S0S29S2aS3bG0G1A3S1S29A1A3A3A3A3").
End States.

Definition FUELAH : nat := 400%nat.

Lemma ah_junk_absurd : ltac2:(tb__ "0|2|
S19S18R1S17SeZ4A1M0ScPeA1M1A2A2S18R2S12S2bG1SeZ8A1A3A2S18R3S12S2eS14S2dG1G0A3SeZ0A1A3A2S50F_;F_;F_;Frho;").
Proof.
  intros rho H1 H2 H3. cbn [holds eval branch_taken] in H1, H2, H3.
  rewrite lit_unsigned in H1. change (4 mod 2 ^ 64) with 4 in H1.
  unfold bv_ltu in H2. rewrite lit_unsigned in H2. change (8 mod 2 ^ 64) with 8 in H2. apply Z.ltb_lt in H2.
  apply (proj1 (Fs.bv_eqb_eq _ _)) in H3. apply (f_equal bv_unsigned) in H3.
  unfold alu64, alu in H3. rewrite bv_and_unsigned, !lit_unsigned in H3.
  change (4 mod 2 ^ 64) with 4 in H3. change (0 mod 2 ^ 64) with 0 in H3.
  set (n := bv_unsigned (rw rho 14)) in *.
  assert (E : n = 4 \/ n = 5 \/ n = 6 \/ n = 7) by lia.
  destruct E as [E|[E|[E|E]]]; rewrite E in H3; cbv in H3; discriminate.
Qed.

Lemma Z_ah_facts : ltac2:(tb__ "0|0|
S52S52S19S59SdS18R1A1S20S49R3R2A2A1A3S50F_;Frho;Foff;Fbase;").
Proof.
  intros base off rho HF. cbn [Z_ah ss_facts F_z N14a F_ah app] in HF.
  pose proof (Forall_inv (Forall_inv_tail HF)) as H2.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF))) as H3.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF))))))) as H1.
  exact (ah_junk_absurd rho H1 H2 H3).
Qed.

Definition Pre_ahA : axst := liftA (Pre_ah memcpy_entryA).
Definition Posts_ahA : list leafA := map liftLA (Posts_ah memcpy_entryA).
Definition cuts_ahA : list axst := map liftA (cuts_ah memcpy_entryA).
Definition exits_ahA : list axst := map liftA (exits_ah memcpy_entryA).
Definition vcuts_ahA : list vnodeA := map liftVA (vcuts_ah memcpy_entryA).
Definition vexits_ahA : list vnodeA := map liftVA (vexits_ah memcpy_entryA).

Definition check_ahA__runs : ltac2:(tb__ "0|0|
S6SbS6S60A1A1A1") := ltac2:(tb__ "0|0|
S5fS21S44S45S43A1S48A4").
Lemma check_ahA : ltac2:(tb__ "0|0|
S51SaS5dS21S44S45S43A1S22S48S4aA6S8A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUELAH (cutpcs_ah memcpy_entryA) NF cuts_ahA exits_ahA check_ahA__runs); [unfold check_ahA__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Lemma echeck_ahA : ltac2:(tb__ "0|0|
S51SaS5eS21S44S45S43A1S22S4bS4cA6S8A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUELAH (cutpcs_ah memcpy_entryA) NF vcuts_ahA vexits_ahA check_ahA__runs); [unfold check_ahA__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem memcpy_ah_sumA : ltac2:(tb__ "0|0|
S5cOF_;S55S19S6S58Q40A1A1S57S21R4R3A3S56S21S22R4A3S5bS21R6S54S21R5S47R4R3A5S53S21R5S22R4R3S46A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_ahA rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELAH (cutpcs_ah memcpy_entryA) NF cuts_ahA exits_ahA (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_ahA) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_ahA.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
    + apply exit_postA. in_nth 0.
    + apply exit_postA. in_nth 1.
    + apply triple_factsA. intros HF. exfalso. exact (Z_ah_facts _ _ _ HF).
    + apply triple_factsA. intros HF. exfalso. exact (Z_ah_facts _ _ _ HF).
  - left; reflexivity.
Qed.

Theorem memcpy_ah_sumA_ex : ltac2:(tb__ "0|0|
S55S19S6S58Q40A1A1S56S21S22R3A3S5aS21S54S21R4S47R3R2A5S53S21R4S22R3R2S46A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_ahA rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_ahA with (vna_state (liftVA (mkVN (Pre_ah memcpy_entryA) 10 (SLit 0)))).
  apply (cfg_complete_autoA segs FUELAH (cutpcs_ah memcpy_entryA) NF vcuts_ahA vexits_ahA (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_ahA) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. unfold vcuts_ahA, vcuts_ah in Hin. cbn [map] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbv; congruence|]). destruct Hin.
  - exact echeck_ahA.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
    + apply (eexit_postA segs J NF rho vcuts_ahA Posts_ahA (liftVA (mkVN (P_ah1 memcpy_entryA) 0 (SLit 0)))). in_nth 0.
    + apply (eexit_postA segs J NF rho vcuts_ahA Posts_ahA (liftVA (mkVN (P_ah2 memcpy_entryA) 0 (SLit 0)))). in_nth 1.
    + cbn [vna_state liftVA vn_state]. apply etriple_factsA. intros HF. exfalso. exact (Z_ah_facts _ _ _ HF).
    + cbn [vna_state liftVA vn_state]. apply etriple_factsA. intros HF. exfalso. exact (Z_ah_facts _ _ _ HF).
  - left; reflexivity.
Qed.
End Str_memcpyAH.

(* [comment removed for export] *)
Module Str_memset.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "memset_entryA"; "Posts_memsetA"; "Pre_memsetA"; "cuts_memsetA"; "exits_memsetA"; "vcuts_memsetA"; "vexits_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "option"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "FUEL_MS"; "cutpcs_memset"; "C_164_0"; "C_loop_0"; "E_164"; "E_in"; "s164"; "s_in"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "entailsA"; "axst"; "leafA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition memset_entryA : Z := 0xde378.

Definition Pre_memsetA : axst := liftA (Pre_memset memset_entryA).
Definition Posts_memsetA : list leafA := map liftLA (Posts_memset memset_entryA).
Definition cuts_memsetA : list axst := map liftA (cuts_memset memset_entryA).
Definition exits_memsetA : list axst := map liftA (exits_memset memset_entryA).
Definition vcuts_memsetA : list vnodeA := map liftVA (vcuts_memset memset_entryA).
Definition vexits_memsetA : list vnodeA := map liftVA (vexits_memset memset_entryA).

Definition check_memsetA__runs : ltac2:(tb__ "0|0|
SaSdSaS21A1A1A1") := ltac2:(tb__ "0|0|
S2aS0SfS10S1A1S4A4").
Lemma check_memsetA : ltac2:(tb__ "0|0|
SeSbS28S0SfS10S1A1S9S4S5A6ScA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUEL_MS (cutpcs_memset memset_entryA) NF cuts_memsetA exits_memsetA check_memsetA__runs); [unfold check_memsetA__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Lemma echeck_memsetA : ltac2:(tb__ "0|0|
SeSbS29S0SfS10S1A1S9S6S7A6ScA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUEL_MS (cutpcs_memset memset_entryA) NF vcuts_memsetA vexits_memsetA check_memsetA__runs); [unfold check_memsetA__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Lemma ent_164A : ltac2:(tb__ "0|0|
SeSbS1fS8S13S1A1A1S8S11S1A1A1S15S1A1A3ScA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_inA : ltac2:(tb__ "0|0|
SeSbS1fS8S14S1A1A1S8S12S1A1A1S16S1A1A3ScA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma liftA_add_facts : ltac2:(tb__ "0|0|
SaS18A1S19SeS20S8S26R2R1A2A1S27R2S8R1A1A2A3FS;FF;").
Proof. intros F S. reflexivity. Qed.

Theorem memset_sumA : ltac2:(tb__ "0|0|
S25OF_;S1cS17SaS22Q40A1A1S1eS0R4R3A3S1dS0S9R4A3S24S0R6S1bS0R5S3R4R3A5S1aS0R5S9R4R3S2A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_memsetA rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_MS (cutpcs_memset memset_entryA) NF cuts_memsetA exits_memsetA (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_memsetA) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - exact HstG.
  - exact check_memsetA.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[]]]].
    + apply exit_postA. in_nth 0.
    +
      unfold liftA at 1. change (mkA (E_164 memset_entryA) []) with (liftA (E_164 memset_entryA)).
      apply (exit_reenterA segs ok _ NF cuts_memsetA _ (liftA (E_164 memset_entryA)) (liftA (C_164_0 memset_entryA)) F164_sem (s164 memset_entryA) tp).
      * rewrite <- liftA_add_facts. in_nth 1.
      * exact ent_164A.
      * apply s164_id.
      * exact HstG.
      * apply F164_below.
      * intros r tp' tr md _ HF. exact (glue_164 memset_entryA r HF).
    +
      unfold liftA at 1. change (mkA (E_in memset_entryA) []) with (liftA (E_in memset_entryA)).
      apply (exit_reenterA segs ok _ NF cuts_memsetA _ (liftA (E_in memset_entryA)) (liftA (C_loop_0 memset_entryA)) Floop_sem (s_in memset_entryA) tp).
      * rewrite <- liftA_add_facts. in_nth 2.
      * exact ent_inA.
      * apply s_in_id.
      * exact HstG.
      * apply Floop_below.
      * intros r tp' tr md _ HF. exact (glue_in memset_entryA r HF).
  - left; reflexivity.
Qed.

Theorem memset_sumA_ex : ltac2:(tb__ "0|0|
S1cS17SaS22Q40A1A1S1dS0S9R3A3S23S0S1bS0R4S3R3R2A5S1aS0R4S9R3R2S2A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_memsetA rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_memsetA with (vna_state (liftVA (mkVN (Pre_memset memset_entryA) 6 (SLit 0)))).
  apply (cfg_complete_autoA segs FUEL_MS (cutpcs_memset memset_entryA) NF vcuts_memsetA vexits_memsetA (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_memsetA) tp).
  - exact HstG.
  - intros n Hin. unfold vcuts_memsetA, vcuts_memset in Hin. cbn [map] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbv; congruence|]). destruct Hin.
  - exact echeck_memsetA.
  - intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[]]]].
    + apply (eexit_postA segs J NF rho vcuts_memsetA Posts_memsetA (liftVA (mkVN (P_ret_memset memset_entryA) 0 (SLit 0)))). in_nth 0.
    + apply (eexit_reenterA segs _ NF vcuts_memsetA _ (liftVA (mkVN (E_164 memset_entryA) 5 (SLit 0))) (liftVA (mkVN (C_164 memset_entryA) 4 (SLit 0)))
               F164_sem (liftA (C_164_0 memset_entryA)) (s164 memset_entryA) tp);
        [in_nth 1 | reflexivity | exact ent_164A | apply s164_id | exact HstG | apply F164_below
        | intros r tp' tr md _ HF; exact (glue_164 memset_entryA r HF) | cbn; lia | cbn; lia].
    + apply (eexit_reenterA segs _ NF vcuts_memsetA _ (liftVA (mkVN (E_in memset_entryA) 3 (SLit 0))) (liftVA (mkVN (C_loop memset_entryA) 2 (SVar 121)))
               Floop_sem (liftA (C_loop_0 memset_entryA)) (s_in memset_entryA) tp);
        [in_nth 2 | reflexivity | exact ent_inA | apply s_in_id | exact HstG | apply Floop_below
        | intros r tp' tr md _ HF; exact (glue_in memset_entryA r HF) | cbn; lia | cbn; lia].
  - left; reflexivity.
Qed.
End Str_memset.

