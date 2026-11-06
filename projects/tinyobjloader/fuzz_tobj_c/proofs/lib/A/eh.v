(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxArrA TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fk.

(* [comment removed for export] *)
Module Lib_finalize_unknowns.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "pair"; "prod"; "None"; "bool"; "false"; "nat"; "true"; "app"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "cell"; "sprop"; "sobj"; "SPUle"; "FcsrFrm0"; "mkSS"; "valuation"; "DUnknown"; "SAlu"; "SPAlign"; "SVar"; "mkObj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "mkA"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vb"; "piece"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_finalize_unknowns"; "FUEL_fu"; "Pre_fu"; "cutpcs_fu"; "P_fu"; "Posts_fu"; "cuts_fu"; "fu_facts"; "fu_objs"; "NXP_fu"; "O_fstk"; "Vd"; "exits_fu"; "vcuts_fu"; "vexits_fu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_finalize_unknowns.FinUnkAddr"; "fu_entry"; "fu_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module FinUnkAddr.
  Definition fu_entry : Z := 0x90850.
  Definition fu_ret : Z := 0x90dd8.
End FinUnkAddr.
Import FinUnkAddr.

Definition FUEL_fu : nat := 100%nat.
Definition NXP_fu : positive := 140%positive.

Definition O_fstk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S18PaA1ScNa0A1ScZ0A1Vcells;S15A5").

Definition Vd (o e : Z) : sobj := ltac2:(tb__ "0|1|
S23Vo;S2aVo;Z20A2S0SeS24Vo;ScZ0A1M0A2S0SeS24S2aVo;Z8A2G0A2S0SeS24S2aVo;Z10A2G0A2S0SeS24S2aVo;Z18A2ScVe;A1A2S1SeA1A3A3A3A3A3").
Definition fu_facts : list sprop := ltac2:(tb__ "0|0|
S0SfS17PcZ4A2S0SfS11ScS4aA1S22A2S0SfS11S16S42S22ScZ518A1A3ScZ7fffff800000A1A2S0SfS11S22ScS25A1A2S1SfA1A3A3A3A3").
Definition fu_objs : list sobj := ltac2:(tb__ "0|0|
SaS10S0S10S34S1SeA1A1S0S10S35Z1a0Z18A2S1S10A1A3A3S1cA3").

Definition Pre_fu : axst := ltac2:(tb__ "0|1|
S1bS13S43S20S1eS12S5SdA1S32S31S1dS7A9S0S4SdSdA2M0S3SdSdS22ScZ518A1A4S1G0A1A3A2").
Definition P_fu : axst := ltac2:(tb__ "0|2|
S1bS13S44S21S1fS1dA1S0S4S8SdA2M0S3S8SdUaScZ0A1A4S1G0A1A3A2S1eS12S5SdA1S32S31S33S7A9S0S4SdSdA2M1S3SdSdS22ScZ518A1A4S1G1A1A3A2").
Definition Posts_fu : list leafA := ltac2:(tb__ "0|0|
S0S39S3aS2eS48A2S1S39A1A3").

Definition cuts_fu : list axst := [Pre_fu].
Definition exits_fu : list axst := [P_fu].
Definition cutpcs_fu : list Z := [].

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Definition check_fu__runs : ltac2:(tb__ "0|0|
S2SbS2S39A1A1A1") := ltac2:(tb__ "0|0|
S49S1aS2bS2dS30A4").
Lemma check_fu : ltac2:(tb__ "0|0|
S3bS6S28S1aS2bS2dS1dS30S36A6S9A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUEL_fu cutpcs_fu NF cuts_fu exits_fu check_fu__runs); [unfold check_fu__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem finalize_unknowns_sum : ltac2:(tb__ "0|0|
S47OF_;S3eS14S2S41Q40A1A1S40S1aR4R3A3S3fS1aS1dR4A3S46S1aR6S3dS1aR5S2cR4R3A5S3cS1aR5S1dR4R3S2fA6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_fu rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_fu cutpcs_fu NF cuts_fu exits_fu (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_fu) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_fu.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply exit_postA. in_nth 0.
  - left; reflexivity.
Qed.

Definition vcuts_fu : list vnodeA := ltac2:(tb__ "0|0|
S0S26S27S2cZ1eScZ0A1A3S1S26A1A3").
Definition vexits_fu : list vnodeA := ltac2:(tb__ "0|0|
S0S26S27S2eZ1ScZ0A1A3S1S26A1A3").

Lemma echeck_fu : ltac2:(tb__ "0|0|
S3bS6S29S1aS2bS2dS1dS37S38A6S9A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUEL_fu cutpcs_fu NF vcuts_fu vexits_fu check_fu__runs); [unfold check_fu__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem finalize_unknowns_sum_ex : ltac2:(tb__ "0|0|
S3eS14S2S41Q40A1A1S3fS1aS1dR3A3S45S1aS3dS1aR4S2cR3R2A5S3cS1aR4S1dR3R2S2fA6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_fu rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_fu with (vna_state (mkVNA Pre_fu 30 (SLit 0))).
  apply (cfg_complete_autoA segs FUEL_fu cutpcs_fu NF vcuts_fu vexits_fu (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_fu) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. destruct Hin as [<-|[]]; cbv; congruence.
  - exact echeck_fu.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply (eexit_postA segs J NF rho vcuts_fu Posts_fu (mkVNA P_fu 1 (SLit 0))). in_nth 0.
  - left; reflexivity.
Qed.
End Lib_finalize_unknowns.

(* [comment removed for export] *)
Module Lib_mat_find.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "pair"; "prod"; "None"; "bool"; "false"; "nat"; "true"; "app"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "cell"; "sobj"; "sprop"; "SPUle"; "FcsrFrm0"; "mkSS"; "valuation"; "DUnknown"; "SAlu"; "SPAlign"; "SVar"; "mkObj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "mkA"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vb"; "piece"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_mat_find"; "FUEL_mf"; "Pre_mf"; "cutpcs_mf"; "P_mf"; "Posts_mf"; "Vd"; "cuts_mf"; "mf_facts"; "mf_objs"; "NXP_mf"; "O_mstk"; "exits_mf"; "vcuts_mf"; "vexits_mf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_mat_find.MatFindAddr"; "mf_entry"; "mf_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module MatFindAddr.
  Definition mf_entry : Z := 0x9d3bc.
  Definition mf_ret : Z := 0x9d594.
End MatFindAddr.
Import MatFindAddr.

Definition FUEL_mf : nat := 100%nat.
Definition NXP_mf : positive := 140%positive.

Definition O_mstk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S18PaA1ScN20A1ScZ0A1Vcells;S15A5").

Definition Vd (o e : Z) : sobj := ltac2:(tb__ "0|1|
S23Vo;S2aVo;Z20A2S0SeS24Vo;ScZ0A1M0A2S0SeS24S2aVo;Z8A2G0A2S0SeS24S2aVo;Z10A2G0A2S0SeS24S2aVo;Z18A2ScVe;A1A2S1SeA1A3A3A3A3A3").
Definition mf_facts : list sprop := ltac2:(tb__ "0|0|
S0S10S17PcZ4A2S0S10S11ScS4cA1S22A2S0S10S11S16S44S22ScZ518A1A3ScZ7fffff800000A1A2S0S10S11S22ScS25A1A2S1S10A1A3A3A3A3").
Definition mf_objs : list sobj := ltac2:(tb__ "0|0|
SaSfS0SfS37S1SeA1A1S0SfS32Z160Z8A2S0SfS32Z180Z4A2S1SfA1A3A3A3S1cA3").

Definition Pre_mf : axst := ltac2:(tb__ "0|1|
S1bS13S45S20S1eS12S5SdA1S35S34S1dS7A9S0S4SdSdA2M0S3SdSdS22ScZ518A1A4S1G0A1A3A2").
Definition P_mf : axst := ltac2:(tb__ "0|2|
S1bS13S46S21S1fS1dA1S0S4S8SdA2M0S3S8SdUaScS2cS2bZ2Z40A2Z1A2A1A4S1G0A1A3A2S1eS12S5SdA1S35S34S36S7A9S0S4SdSdA2M1S3SdSdS22ScZ518A1A4S1G1A1A3A2").
Definition Posts_mf : list leafA := ltac2:(tb__ "0|0|
S0S3bS3cS30S4aA2S1S3bA1A3").

Definition cuts_mf : list axst := [Pre_mf].
Definition exits_mf : list axst := [P_mf].
Definition cutpcs_mf : list Z := [].

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Definition check_mf__runs : ltac2:(tb__ "0|0|
S2SbS2S3bA1A1A1") := ltac2:(tb__ "0|0|
S4bS1aS2dS2fS33A4").
Lemma check_mf : ltac2:(tb__ "0|0|
S3dS6S28S1aS2dS2fS1dS33S38A6S9A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segs FUEL_mf cutpcs_mf NF cuts_mf exits_mf check_mf__runs); [unfold check_mf__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem mat_find_sum : ltac2:(tb__ "0|0|
S49OF_;S40S14S2S43Q40A1A1S42S1aR4R3A3S41S1aS1dR4A3S48S1aR6S3fS1aR5S2eR4R3A5S3eS1aR5S1dR4R3S31A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mf rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_mf cutpcs_mf NF cuts_mf exits_mf (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_mf) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_mf.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply exit_postA. in_nth 0.
  - left; reflexivity.
Qed.

Definition vcuts_mf : list vnodeA := ltac2:(tb__ "0|0|
S0S26S27S2eZ1eScZ0A1A3S1S26A1A3").
Definition vexits_mf : list vnodeA := ltac2:(tb__ "0|0|
S0S26S27S30Z1ScZ0A1A3S1S26A1A3").

Lemma echeck_mf : ltac2:(tb__ "0|0|
S3dS6S29S1aS2dS2fS1dS39S3aA6S9A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segs FUEL_mf cutpcs_mf NF vcuts_mf vexits_mf check_mf__runs); [unfold check_mf__runs; reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Theorem mat_find_sum_ex : ltac2:(tb__ "0|0|
S40S14S2S43Q40A1A1S41S1aS1dR3A3S47S1aS3fS1aR4S2eR3R2A5S3eS1aR4S1dR3R2S31A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mf rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mf with (vna_state (mkVNA Pre_mf 30 (SLit 0))).
  apply (cfg_complete_autoA segs FUEL_mf cutpcs_mf NF vcuts_mf vexits_mf (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_mf) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. destruct Hin as [<-|[]]; cbv; congruence.
  - exact echeck_mf.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply (eexit_postA segs J NF rho vcuts_mf Posts_mf (mkVNA P_mf 1 (SLit 0))). in_nth 0.
  - left; reflexivity.
Qed.
End Lib_mat_find.

(* [comment removed for export] *)
Module Lib_builder_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "valuation"; "SPUle"; "sobj"; "holds"; "SAlu"; "SVar"; "obj_range"; "rw"; "ss_facts"; "sv_eqb"; "ob_base"; "ob_hi"; "ob_lo"; "soff"; "sprop_eqb"; "DUnknown"; "SPEq"; "cell"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "prod"; "cons"; "bool"; "true"; "pair"; "fst"; "snd"; "None"; "nat"; "nil"; "option"; "andb"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "True"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "div"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vb"; "vAL"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pclMA"; "FFx"; "xrs_okL"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf"; "baseF"; "extraO"; "basez"; "extraX"; "frameF"; "in_callers"; "vb184"; "P0_builder"; "base_facts"; "extra_tab"; "frame_facts"; "framez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "vB"; "vL"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "TPA"; "frinA"; "tvinA"; "fbinA"; "ffinA"; "ANone"; "NDA"; "PTrue"; "frozen"; "nd_below"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "g8"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "is_shadowZ"; "payA"; "robjs_okA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "robjs_checkF"; "xrs_checkL"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "robjs_okF"; "xrs_ok47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Lib_scan_double_ex.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma uval_add_litZ : ltac2:(tb__ "0|0|
S3S0S16S29Z0R1A2S2aS2bS2fR4R3A2R2A2S2cZ2Z40A2A2S26S16S2fR5S7S3aR4S2R3A1A3A2S2bS2fR5R4A2R3A2A3F_;F_;Fk;Fa;Frho;").
Proof. intros rho a k Hk H. pose proof (uval_range rho a). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. Qed.

Lemma obj_rangeZ : ltac2:(tb__ "0|2|
S3S5S16S16S16S25S29S1eS16S16S9R5R4A2M0A3R3A2S2aR3S1fS16S16G0A3A2A2S26S16S10R6SfR5A1A2R3A3S26S16S10R7SeR6A1A2R3A3S25S29S2bS2fR8SdR7A1A2M1R5A2R6A2S2aR6S2bG1R4A2A2A2F_;F_;F_;Fhi;Flo;Fa;Fo;Frho;").
Proof. intros rho o a lo hi Hr <- <-. unfold obj_range, obj_lo_of, obj_hi_of in Hr. unfold uval. exact Hr. Qed.

Definition P0_builder (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S25S16S25S29S51Q40M0SaVr;PfA2A2M1R1A2S2aR1S2bG1S51G0SaVr;P12A2A2A2A2A2S37VCST;Vr;VFB;VFF;R2A5F_;Fa;S25S57VFF;S51G0SaVr;PcA2A2Z518A3S57VFF;S51G0SaVr;P3aA2A2Z30A3A2A2").

Lemma pclMA_mono : ltac2:(tb__ "0|2|
S18S19S16S16A2M0A1M1S3G1S18S19G0S16A2A1S3S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S16S37R8R7R6R5R1A5S37R9R8S52R7R5R4A3S38R6R5R3A3R2A5F_;Fa;Ffrs;Fkept;Frho;FFF;FFB;Frho0;FCST;").
Proof.
  intros CST rho0 FB FF rho kept frs a [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. split; [apply In_FBx; left; exact Hin | exact Hr].
  - right; right; right. exists f, s, fl. split; [apply In_FFx; left; exact Hin | exact Hr].
Qed.

Definition base_facts (DW : Z) : list sprop := ltac2:(tb__ "0|4|
S1aS1S4S8PaA1M0S2S76A1M1A2S1aS1S4S7S3aS8P1eA1M2S2VDW;A1A3G0A2S1aS1S4S2S4fA1M3S33A2S1aS1S4S7S3aS33S2Z518A1A3G2A2S1aS1S4S33G1A2S1aS1S4G3S34A2S1aS1S4S7S3aS34S2Z30A1A3G2A2S1aS1S4S34G1A2S1aS1S4S4dS2S4eA1A2S1aS1S4S4cG1A2S1aS1S4S2Z7fff7f800000A1G2A2S1aS1S4G2S2Z7fffff800000A1A2S22S1A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition baseF (DW : Z) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S69S1S1S68S1S11R1A1VF;A3Lp;S43VDW;A1A3").
Record basez (DW : Z) (rho : valuation) : Prop := BZ {
  bz_sp : aceil + DW <= uval rho (SVar 10) <= 2 ^ 47;
  bz_b : IMG_HI <= uval rho vb /\ uval rho vb + 1304 <= bv_unsigned (rw rho V_TOP);
  bz_al : IMG_HI <= uval rho vAL /\ uval rho vAL + 48 <= bv_unsigned (rw rho V_TOP);
  bz_L : uval rho vL <= 2 ^ 26;
  bz_B : uval rho vB <= 2 ^ 47;
  bz_top : bv_unsigned (rw rho V_TOP) + DW <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma basez_of : ltac2:(tb__ "0|0|
S16S3S18S1A1S25S29Z0R3A2S2aR3S2cZ2Z28A2A2A2S35S1S6R3A1R2A3S26S1bS3bR5R3A2S1cA3S3dR6R5A2F_;F_;F_;FF;Frho;FDW;").
Proof.
  intros DW rho F HDW HF HB. unfold baseF in HB.
  assert (G : forall p, In p (base_facts DW) -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [base_facts] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  pose proof (G _ ltac:(do 6 right; left; reflexivity)) as F7. pose proof (G _ ltac:(do 7 right; left; reflexivity)) as F8.
  pose proof (G _ ltac:(do 8 right; left; reflexivity)) as F9. pose proof (G _ ltac:(do 9 right; left; reflexivity)) as F10.
  pose proof (G _ ltac:(do 10 right; left; reflexivity)) as F11. pose proof (G _ ltac:(do 11 right; left; reflexivity)) as F12.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12.
  unfold two47, two26, RA.two47 in *. unfold IMG_HI in *.
  rewrite !uval_lit in * by lia. pose proof (uval_range rho (SVar 30)) as R30. rewrite uval_add_litZ in F2 by lia.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *.
  pose proof (uval_range rho vb) as Rb. pose proof (uval_range rho vAL) as Ral.
  rewrite uval_add_litZ in F4 by lia. rewrite uval_add_litZ in F7 by lia.
  constructor; rewrite ?aceil_val; unfold IMG_HI in *; lia.
Qed.

Definition frame_facts (g pR : positive) (sz : Z) : list sprop := ltac2:(tb__ "0|3|
S1aS1S13S67Vg;A1S8VpR;A1M0A2S1aS1S4S8Vg;A1S2S2eS2cZ2M1Z3dA2Z1A2A1A2S1aS1S4S2S4fA1G0A2S1aS1S4S7S3aG0S2Vsz;A1A3S8P1eA1M2A2S1aS1S4G0S2S2cG1Z2fA2A1A2S1aS1S4G2S2Z7fffff800000A1A2S22S1A1A3A3A3A3A3A3").
Definition frameF (g pR : positive) (sz : Z) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S69S1S1S68S1S11R1A1VF;A3Lp;S45Vg;VpR;Vsz;A3A3").
Record framez (g pR : positive) (sz : Z) (rho : valuation) : Prop := FZ {
  fz_g : uval rho (SVar g) = uval rho (SVar pR) / 8;
  fz_g8 : uval rho (SVar pR) mod 8 = 0;
  fz_f : IMG_HI <= uval rho (SVar pR) /\ uval rho (SVar pR) + sz <= bv_unsigned (rw rho V_TOP) /\ bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma framez_of : ltac2:(tb__ "0|0|
S17S17S16S3S18S1A1S25S29Z0R3A2S2aR3S2cZ2Z28A2A2A2S35S1S6R3A1R2A3S26S1bS3fR7R6R5R3A4S1cA3S46R8R7R6R5A4F_;F_;F_;FF;Frho;Fsz;FpR;Fg;").
Proof.
  intros g pR sz rho F Hsz HF HB. unfold frameF in HB.
  assert (G : forall p, In p (frame_facts g pR sz) -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [frame_facts] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  rewrite h_ule in F2, F3, F4, F5, F6. cbn [holds] in F1. change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *. unfold IMG_HI in *.
  rewrite !uval_lit in * by lia. pose proof (uval_range rho (SVar pR)) as Rf. pose proof (uval_range rho (SVar g)) as Rg.
  rewrite uval_add_litZ in F4 by lia.
  assert (E8 : uval rho (g8 g) = (uval rho (SVar g) * 8) mod 2 ^ 64).
  { unfold uval, g8. rewrite U_sll_lit. change (2 ^ (3 mod 64)) with 8. reflexivity. }
  apply (f_equal bv_unsigned) in F1. change (uval rho (g8 g) = uval rho (SVar pR)) in F1. rewrite E8 in F1.
  rewrite Z.mod_small in F1 by lia.
  constructor; [rewrite <- F1; rewrite Z.div_mul by lia; reflexivity | rewrite <- F1; apply Z_mod_mult | unfold IMG_HI; lia].
Qed.

Lemma shobj_range_hse : ltac2:(tb__ "0|2|
S17S17S16S16S16S3S18S1A1S16S25S29Z0R6A2M0S2aR6S2cZ2Z28A2A2A2G0S25S29R7R6A2S29R6S2dR8Z8A2A2A2S35S1S6R6A1R5A3S26S1bS3fRcRbRaR6A4S1cA3S25S29S1eS16S16S9R8S73RdRaR9S22S14A1S12A5A2M1A3R6A2S2aR6S1fS16S16G1A3A2A2S6cR7A1F_;F_;F_;F_;F_;F_;Fa;FF;Frho;Fk2;Fk1;Fsz;FpR;Fg;").
Proof.
  intros g pR sz k1 k2 rho F a Hsz Hk1 Hk2 HF HFR Hr. pose proof (framez_of g pR sz rho F Hsz HF HFR) as [G1 G2 G3]. unfold is_shadowZ, IMG_HI in *.
  unfold shobj, obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  pose proof (Z.div_le_mono sz (2 ^ 40) 8 ltac:(lia) ltac:(lia)) as D8. change (2 ^ 40 / 8) with 137438953472 in D8.
  unfold SHADOW_OFF, HIGH_SHADOW_END in *. rewrite !soff_lit_small in Hr by lia.
  change (bv_unsigned (eval rho (SVar g))) with (uval rho (SVar g)) in Hr. rewrite G1 in Hr.
  pose proof (uval_range rho (SVar pR)). lia.
Qed.

Lemma frame_off_rng : ltac2:(tb__ "0|2|
S17S17S16S16S3S18S1A1S25S29Z0R4A2M0S2aR4S2cZ2Z28A2A2A2S25G0S29R4R5A2A2S35S1S6R4A1R3A3S26S1bS3fR9R8R7R4A4S1cA3S26S16S2fR6S7S3aS8R9A1M1S2R7A1A3A2S2bS2fR6G1A2R7A2A3F_;F_;F_;F_;FF;Frho;Foff;Fsz;FpR;Fg;").
Proof.
  intros g pR sz off rho F Hsz Hoff HF HFR. pose proof (framez_of g pR sz rho F Hsz HF HFR) as [_ _ G3]. unfold IMG_HI in G3.
  pose proof (uval_range rho (SVar pR)). apply uval_add_litZ; lia.
Qed.

Definition vb184 : sv := SAlu ALU_ADD vb (SLit 184).
Definition extra_tab : list (sv * sv * sv) := ltac2:(tb__ "0|3|
S1aS19S19S0S0A2M0S0A2M1S1dG0S0S1dS0S0S33S2Z0A1M2A4S2Z8A1A4S1aG1S1dG0S0S1dS0S0S33S2Z60A1A4S2Z78A1A4S1aG1S1dG0S0S1dS0S0S33S2Zb8A1A4S2Zd8A1A4S1aG1S1dG0S0S1dS0S0S41G2A4S2Z20A1A4S1aG1S1dG0S0S1dS0S0S34G2A4S2Z30A1A4S1aG1S1dG0S0S1dS0S0S4cG2A4S4dA4S22G1A1A3A3A3A3A3A3").
Definition extraO (o : sobj) : bool := ltac2:(tb__ "0|3|
S68S19S19S0S0A2M0S0A2M1G1S24S24ScSdVo;A1S1eS0S0S1eG0S0R1A3M2A3A2ScSfVo;A1S1fS0S0G2A3A2A2ScSeVo;A1S1fG0S0R1A3A2A2Lt;S44A3").
Definition extraX_tab : list (sv * sv) := ltac2:(tb__ "0|1|
S1aS19S0S0A2M0S1dS0S0S33S2Z518A1A4S1aG0S1dS0S0S34S2Z30A1A4S1aG0S1dS0S0S4cS4dA4S1aG0S1dS0S0S41S2Z20A1A4S1aG0S1dS0S0S2S4bA1S2Zb8A1A4S22G0A1A3A3A3A3A3").
Definition extraX (r : sv * sv) : bool := existsb (xr_eqb r) extraX_tab.
Definition in_callers (rho : valuation) (a : Z) : Prop := ltac2:(tb__ "0|3|
S27S25S29S2fVrho;S33A2M0Va;A2S2aVa;S2bG0Z518A2A2A2S27S25S29S2fVrho;S34A2M1Va;A2S2aVa;S2bG1Z30A2A2A2S27S25S29S2fVrho;S4cA2M2Va;A2S2aVa;S2bG2S2fVrho;S4dA2A2A2A2S25S29S4bVa;A2S2aVa;S2bS4bZb8A2A2A2A2A2A2").

Lemma extraO_sound : ltac2:(tb__ "0|1|
S16S3S5S16S3dR4R3A2S26S1bS3cR3A1S1cA3S25S29S1eS16S16S9R5R4A2M0A3R3A2S2aR3S1fS16S16G0A3A2A2S40R6R4A2F_;F_;F_;Fa;Fo;Frho;FDW;").
Proof.
  intros DW rho o a [Bsp Bb Bal BL BB Btop] HE Hr. rewrite aceil_val in *. unfold IMG_HI in *.
  assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; lia).
  unfold extraO in HE. apply existsb_exists in HE as (t & Hin & Heq).
  apply andb_prop in Heq as [Heq Hh]. apply andb_prop in Heq as [Hb Hl]. apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  unfold in_callers. cbn [extra_tab In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hb, Hl, Hh;
    (eapply obj_rangeZ in Hr; [| rewrite Hl; first [apply soff_lit_small; lia | apply soff_smallu; lia] | rewrite Hh; first [apply soff_lit_small; lia | apply soff_smallu; lia]]);
    rewrite Hb in Hr; rewrite ?E184 in Hr; lia.
Qed.

Lemma extraX_sound : ltac2:(tb__ "0|1|
S16S3S19S0S0A2S16S3dR4R3A2S26S1bS3eR3A1S1cA3S25S29S2fR5S1eS0S0R4A3A2M0R3A2S2aR3S2bG0S2fR5S1fS0S0R4A3A2A2A2A2S40R6R4A2F_;F_;F_;Fa;Fr;Frho;FDW;").
Proof.
  intros DW rho r a [Bsp Bb Bal BL BB Btop] HE Hr. rewrite aceil_val in *. unfold IMG_HI in *.
  assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; lia).
  unfold extraX in HE. apply existsb_exists in HE as (t & Hin & Heq). apply xr_eqb_sound in Heq. subst t.
  unfold in_callers. cbn [extraX_tab In] in Hin. unfold pow10_tab in *.
  destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; destruct r as [b l]; injection E as <- <-; cbn [fst snd] in Hr;
    rewrite ?uval_lit in Hr by lia; rewrite ?E184 in Hr; lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S47S3S18S50Q40A1A1S4aOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S7bS6bVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S16S63VCST;R1A2S25S29Z0R2A2S2aR2S4fA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S16S63VXGL;R1A2S25S29Z0R2A2S2aR2S4fA2A2F_;Fa;").

Hypothesis HXpow : ltac2:(tb__ "0|0|
S16S25S29S4bR1A2S2aR1S2bS4bZb8A2A2A2S63VXGL;R2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S18S19S19S16S16A2S16A2A1").
Variable BX : bxt.
Variable rho0 : valuation.

Variable P0f : valuation -> Prop.
Hypothesis HP0b : ltac2:(tb__ "0|0|
S3VP0f;R1A1S42VCST;VFB;VFF;R2A4F_;Fr;").
Variable DW : Z.
Hypothesis HDW : 0 <= DW < 2 ^ 40.

Lemma P0b_now : ltac2:(tb__ "0|1|
S3S36S32Vrho0;R1A3VP0f;Vrho0;A1S25S16S25S29S2fR4S4cA2M0R1A2S2aR1S2bG0S2fR4S4dA2A2A2A2S37VCST;Vrho0;VFB;VFF;R2A5F_;Fa;S25S57VFF;S2fR3S33A2Z518A3S57VFF;S2fR3S34A2Z30A3A2A2F_;F_;Frho;").
Proof.
  intros rho Hav HP. destruct (HP0b _ HP) as (A & B & C). unfold uval, vL, vB, vb, vAL. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 18%positive eq_refl), <- (proj1 Hav 58%positive eq_refl).
  repeat (split; [assumption|]). assumption.
Qed.

Lemma in_callers_ok : ltac2:(tb__ "0|0|
S3S16S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S36S32Vrho0;R4A3VP0f;Vrho0;A1S40R6R5A2S27S37VCST;Vrho0;S52VFB;R7R5A3S38VFF;R7R4A3R6A5S63VXGL;R6A2A2F_;F_;F_;Ffrs;Fkept;Fa;Frho;").
Proof.
  intros rho a kept frs Hav HP0 H. destruct (P0b_now rho Hav HP0) as (HT & Hb & Hal).
  destruct H as [H|[H|[H|H]]].
  - destruct Hb as (f & sz & fl & Hin & H1 & H2). left. right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - destruct Hal as (f & sz & fl & Hin & H1 & H2). left. right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - left. apply pclMA_mono. apply HT. exact H.
  - right. exact (HXpow a H).
Qed.
Lemma extraO_client : ltac2:(tb__ "0|1|
S3S5S16S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S3dVDW;R5A2S36S32Vrho0;R6A3VP0f;Vrho0;A1S26S1bS3cR7A1S1cA3S25S29S1eS16S16S9R9R8A2M0A3R7A2S2aR7S1fS16S16G0A3A2A2S37VCST;Vrho0;S52VFB;RaR7A3S38VFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;").
Proof.
  intros rho o a kept frs BZ Hav HP0 HE Hr. destruct (P0b_now rho Hav HP0) as (HT & Hb & Hal).
  pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *. unfold IMG_HI in *.
  assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; lia).
  unfold extraO in HE. apply existsb_exists in HE as (t & Hin & Heq).
  apply andb_prop in Heq as [Heq Hh]. apply andb_prop in Heq as [Hb0 Hl]. apply sv_eqb_sound in Hb0. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  cbn [extra_tab In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hb0, Hl, Hh;
    (eapply obj_rangeZ in Hr; [| rewrite Hl; first [apply soff_lit_small; lia | apply soff_smallu; lia] | rewrite Hh; first [apply soff_lit_small; lia | apply soff_smallu; lia]]);
    rewrite Hb0 in Hr; rewrite ?E184 in Hr.
  1-4: destruct Hb as (f & sz & fl & Hin & H1 & H2); right; right; right; exists f, sz, fl; split; [apply In_FFx; left; exact Hin | lia].
  - destruct Hal as (f & sz & fl & Hin & H1 & H2). right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - apply pclMA_mono. apply HT. lia.
Qed.

Lemma siteP : ltac2:(tb__ "0|0|
S47S3S18S1A1S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S23S21A1S18S5A1S3S18S50Q40A1A1S4aVAInv;RaR3R2R1A4S35S1S6RaA1R9A3S26S1bS3bVDW;RaA2S1cA3S36S32Vrho0;RcA3VP0f;Vrho0;A1S58Vrho0;RfA2S53RfS49S48R10A1A1A2S5bVFB;R11A2S5cVFF;R12A2S5aVFB;R13R12R10A4S54R13R11A2S55R14R12A2S59VFF;R16R15R12A4S26S1bS74R15R14R13R12S3cR11A6S1cA3S6eVCST;R18S20S16A1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  eapply (robjsP_okA segs AInv CST ALA rho0 FB FF Ai rho facts tv fr skip extraO R rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraO_client rho o a _ _ (basez_of DW rho facts HDW HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteF : ltac2:(tb__ "0|0|
S47S3S18S1A1S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S18S5A1S3S18S50Q40A1A1S4aVAInv;R9R3R2R1A4S35S1S6R9A1R8A3S26S1bS3bVDW;R9A2S1cA3S36S32Vrho0;RbA3VP0f;Vrho0;A1S58Vrho0;ReA2S53ReS49S48RfA1A1A2S5aVFB;R10RfRdA4S54R10ReA2S55R11RfA2S59VFF;R13R12RfA4S26S1bS71R12R11R10S20S21A1S3cRfA6S1cA3S79VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_okF segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraO R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraO_client rho o a _ _ (basez_of DW rho facts HDW HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteH : ltac2:(tb__ "0|1|
S47S3S18S1A1S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S18S5A1S3S18S50Q40A1A1S4aVAInv;R9R3R2R1A4S35S1S6R9A1R8A3S26S1bS3bVDW;R9A2S1cA3S36S32Vrho0;RbA3VP0f;Vrho0;A1S58Vrho0;ReA2S53ReS49S48RfA1A1A2S5aVFB;R10RfRdA4S54R10ReA2S55R11RfA2S59VFF;R13R12RfA4S26S1bS71R12R11R10S20S21A1S3cRfA6S1cA3S5S16S6aS5R2R12A3S25S29S1eS16S16S9R17R3A2M0A3R2A2S2aR2S1fS16S16G0A3A2A2S27S37VCST;Vrho0;S52VFB;R18R16A3S38VFF;R18R15A3R3A5S27S25S29Z0R3A2S2aR3S4fA2A2S6cR3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_hse segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraO R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraO_client rho o a _ _ (basez_of DW rho facts HDW HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteX : ltac2:(tb__ "0|4|
S47S3S18S1A1S18S19S0S0A2A1M0S18S19S19S0S16A2S0A2M1A1M2S23S21A1M3S18S5A1G0S3S18S50Q40A1A1S4aVAInv;RbR3R2R1A4S35S1S6RbA1RaA3S26S1bS3bVDW;RbA2S1cA3S36S32Vrho0;RdA3VP0f;Vrho0;A1S58Vrho0;R10A2S53R10S49S48R11A1A1A2S5bVFB;R12A2S5cVFF;R13A2S5aVFB;R14R13R11A4S54R14R12A2S55R15R13A2S59VFF;R17R16R13A4S26S1bS72VXGL;R16R15R14R13R12S3eR11A8S1cA3S25S39VCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S21S56G1R1R16A3Li;R15X23x2R12A9S25S70VCST;VXGL;R19S20S16A1R18R12A6S7aR18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip objs X rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  assert (HEX : forall r a, In r X -> extraX r = true -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) ->
            pclMA CST rho0 (FBx FB rho tv) (FFx FF rho (match skip with Some i => remove_nth i fr | None => fr end)) a \/ RtCells.in_rangesZ XGL a).
  { intros r a Hr HE Ha. apply (in_callers_ok rho a _ _ Hav HP0). exact (extraX_sound DW rho r a (basez_of DW rho facts HDW HF HB) HE Ha). }
  split; [exact (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extraX X rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hchk HEX)|].
  exact (xrs_checkL_okA segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho facts tv fr skip objs extraX X rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk HEX).
Qed.

Lemma site_pure : ltac2:(tb__ "0|2|
S66S77S18S5A1S3S18S19S0S0A2A1S18S19S19S0S16A2S0A2A1S18S30A1S26S1bS3bVDW;SbS64R7A1A1A2S1cA3S26S1bS74SbS64R8A1A1R4R3S20S21A1M0S3cR6A6S1cA3S26S1bS72VXGL;SbS64R9A1M1A1R5R4G0S15G1A1S3eS65R9A1A8S1cA3S6fVAInv;VCST;VXGL;S32Vrho0;VP0f;VFB;VFF;RaR9R8R7S5eR6R5R4S5dA4S20S16A1S47S75S28L_;L_;AfF_;F_;F_;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;").
Proof.
  intros E s R rho tv fr bd HB HR HX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  split; [exact (siteP Ai rho _ tv fr None R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HR)|].
  split; [exact (proj1 (proj2 (siteX Ai rho _ tv fr None _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HX))) | exact I].
Qed.

Lemma frozen_stableA' : ltac2:(tb__ "0|0|
S17S17S62S3S7cS32R3A2S26S1bS61R4R3A2S1cA3S78S6bR6S60VAInv;VCST;VXGL;S32VKc;Vrho0;VP0f;VFB;VFF;VBX;S5fR4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;").
Proof.
  intros n m nd rho Hm Hb r r' tp tr md md' _ Hme (Ai & kc & HJ). exists Ai, kc.
  eapply (JAi_stable segs AInv CST XGL NF Kc rho0 P0f FB FF BX PTrue HKc ALA m nd Ai kc rho rho tp tr md md'); [exact Hm | exact Hb | apply agree_below_refl | exact Hme | exact HJ].
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
S18S1A1S18S30A1S26S1bS31R1A1S1cA3S6dS32Vrho0;VP0f;R3S2Z0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof.
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.
End Sum.
End Lib_builder_pf.

(* [comment removed for export] *)
Module Lib_tess_polygon_chk0.

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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_polygon_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessPolygonAddr.

Abbreviation TG := (etargets cutsE exitsE).
Abbreviation PE := (eecheckJA NF (cutsE ++ exitsE)).
Abbreviation CC i T := (cut_okE segs FUEL_pg cutpcs_pg 100 PE i T TG).
End Lib_tess_polygon_chk0.

(* [comment removed for export] *)
Module Lib_realloc_rom.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "list"; "prod"; "app"; "None"; "false"; "bool"; "fst"; "option"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "SPUle"; "SVar"; "SAlu"; "cell"; "SPBranch"; "FcsrFrm0"; "mkSS"; "DUnknown"; "SPAlign"; "mkObj"; "ss_regs"; "valuation"; "ss_next"; "SMd"; "SPNot"; "rm"; "rw"; "ss_facts"; "ss_fregs"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_realloc_rom"; "kb16"; "vK"; "VQ"; "vKn"; "vP"; "ndR"; "vQ"; "pN"; "vA"; "z0"; "c8"; "vD"; "X_cp0"; "O_D"; "O_F"; "O_al"; "q1"; "ra_facts"; "tv0"; "vPn"; "B32"; "bd1"; "fs_facts"; "pls"; "two47"; "E_m"; "FUEL_rr"; "Pre_rr"; "X_step"; "bd0"; "cutpcs_rr"; "eoff"; "ok_facts"; "spm"; "tv1"; "tv2"; "C_0"; "D_1"; "D_10"; "D_11"; "D_12"; "D_13"; "D_14"; "D_15"; "D_2"; "D_3"; "D_4"; "D_5"; "D_6"; "D_7"; "D_8"; "D_9"; "E_free"; "E_freeT"; "O_fs"; "P0_ra"; "P_fail"; "P_okX"; "P_ok_S"; "PhisV"; "Pre_f"; "Pre_m"; "T_free"; "T_mnull"; "T_mok"; "Vs"; "X_a2"; "X_cp0f"; "cp_regs"; "cutsE"; "exitsE"; "pre_regs_ra"; "q_facts"; "two40"; "vF0"; "vF1"; "vUD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "tv_factsA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_LTU"; "BC_GE"; "BC_EQ"; "M_MUL"; "aluop"; "mulop"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "uval"; "BIc"; "BIs"; "KU"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "True"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "leavesA_at"; "mkA"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "opp"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_realloc_rom.RRAddr"; "ra_ret"; "ra_L"; "free_pc"; "malloc_pc"; "ra_entry"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "ejcertAF"; "efnode"; "ent_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "NPOSTM"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV CellTile ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import BudA CfgGenTA SummaryA3 TobjJA TobjJAM AxXform AxArrA TobjJAR TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module RRAddr. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.Lib_realloc.ReallocAddr. End RRAddr.
Import RRAddr.

Definition FUEL_rr : nat := 400%nat.
Definition two40 : Z := 2 ^ 40.
Definition two47 : Z := 2 ^ 47.
Definition B32 : Z := 4294967295.

Definition vA : sv := SVar 12. Definition vP : sv := SVar 13. Definition vK : sv := SVar 14. Definition vKn : sv := SVar 33.
Definition vD : sv := SVar 19. Definition vUD : sv := SVar 52.
Definition spm (k : Z) : sv := ltac2:(tb__ "0|0|
S13S7aS12PaA1S10S9aVk;A1A1A3").
Definition kb16 (k : sv) : sv := SMd M_MUL (SLit 16) k.

Definition c8 (o : Z) (v : sv) : cell := mkCell (SLit o) 8 v.
Definition O_F (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1aS12PaA1S10N60A1S10Z0A1Vcells;S18A5").
Definition O_D : sobj := ltac2:(tb__ "0|0|
S1aS49Z60A1S33S10Z0A1S3S14A1S18A5").
Definition O_al : sobj := ltac2:(tb__ "0|2|
S1aS30S10Z0M0A1M1S10Z30A1S0S14S32G0S10Sa1A1A2S0S14S32Z8S10Sa2A1A2S0S14S32Z10G1A2S0S14S32Z18S10Sa3A1A2S0S14S32Z20G1A2S0S14S32Z28S74A2S3S14A1A3A3A3A3A3A3S18A5").

Definition O_fs (d c k : sv) : sobj := ltac2:(tb__ "0|0|
S1aS13S7aVd;S28Vc;A1A3S10Z0A1S28S13S7bVk;Vc;A3A1S3S14A1S18A5").

Definition ra_facts : list sprop := ltac2:(tb__ "0|9|
S0SeS19PaM0Z4M1A2S0SeS11S12G0A1M2S10S40A1M3A2S0SeS11S12P1eA1M4S13S7aS49Z60A1M5S33A3A2S0SeS11G4G5A2S0SeS11G4G2A2S0SeS15S7dS10N1000A1S33A3S0SeS15S7dS33S10S9aS71A1A1A3S0SeS19PcZ3A2S0SeS11S10Z1000A1M6S30A2S0SeS11S13S7aS30S10Z30A1A3G4A2S0SeS11S30G3A2S0SeS19PdG1A2S0SeS11G6S2cA2S0SeS11S13S7aS2cS28S29A1A3G4A2S0SeS11S2cG3A2S0SeS11S10Z1A1S29A2S0SeS15S7cS29S2bA3S0SeS11S28S2bA1S10S3cA1M7A2S0SeS11S2bG7A2S0SeS11S10Z7fff7f800000A1M8G4A2S0SeS11G4S10Z7fffff800000A1A2S0SeS11G8G2A2S3SeA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition pre_regs_ra : list sv := ltac2:(tb__ "0|1|
S94S96S0S5S2SdA2M0S1S2SdUcS28S29A1A4S0G0S1S2SdUdS28S2bA1A4S0G0S1S2SdUeS10Z10A1A4S3G0A1A3A3A3A2").
Definition X_ra : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS30S10Z30A1A4S0G0S1SdSdS2cS28S29A1A4S3G0A1A3A3").
Definition Pre_rr_S : sstate := ltac2:(tb__ "0|0|
S17Sa0S6fS93S16S7SdA1S6SfS0SfS36S3S14A1A1S0SfS35S0SfS37S3SfA1A3A3A3S8eA3S39S92S8A9").
Definition Pre_rr : axst := mkA Pre_rr_S X_ra.

Definition cutpcs_rr : list Z := ltac2:(tb__ "0|0|
S0S25S9dS0S25S9fS0S25S9eS3S25A1A3A3A3").
Definition optA (x : option axst) : axst := match x with Some s => s | None => Pre_rr end.
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_rr_S end.
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S82S75Vk;S8fS42S46VS;Vpc;A4S43A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition E_m : axst := Eval vm_compute in leafA_at Pre_rr malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S5S26SdA2S1S26SdPfS33A4Sa7PaS76S41A1S76S65A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := pos_add_nat (ss_next (ax_S E_m)) 10.
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := ltac2:(tb__ "0|0|
S79S1SdSdS12S2fA1S28S2bA1A4A1").
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition X_cp0 : axst := Eval vm_compute in leafA_at T_mok ra_L 0.

Definition vQ : sv := SVar 172.  Definition vF0 : sv := SVar 173.  Definition vF1 : sv := SVar 174.
Definition eoff (j : Z) : sv := ltac2:(tb__ "0|0|
S13S7aS28S2eA1S10Vj;A1A3").
Definition pls (b : sv) (o : sv) : sv := SAlu ALU_ADD b o.
Definition q1 : sv := SAlu ALU_ADD vQ (SLit 1).
Definition cp_regs : list sv := ltac2:(tb__ "0|15|
S4SdA1M0G0Lx;S1bS76S34A1A1S3SdA1M1SdG0G0G0Ll;R1S0SdR2G1A3M2SdG0G0G0Ll0;R1S0SdR4G2A3M3SdG0G0G0Ll1;R1S0SdR6G3A3M4SdG0G0G0Ll2;R1S0SdR8G4A3M5SdG0G0G0Ll3;R1S0SdRaG5A3M6SdG0G0G0Ll4;R1S0SdRcG6A3M7SdG0G0G0Ll5;R1S0SdReG7A3M8SdG0G0G0Ll6;R1S0SdR10G8A3M9SdG0G0G0Ll7;R1S0SdR12G9A3MaSdG0G0G0Ll8;R1S0SdR14GaA3MbSdG0G0G0Ll9;R1S0SdR16GbA3McSdG0G0G0Ll10;R1S0SdR18GcA3MdSdG0G0G0Ll11;R1S0SdR1aGdA3MeSdG0G0G0Ll12;R1S0SdR1cGeA3MfSdG0G0G0Ll13;R1S0SdR1eGfA3M10SdG0G0G0Ll14;R1S0SdR20G10A3M11SdG0G0G0Ll15;R1S0SdR22G11A3SdG0S0SdR24S0SdR22S0SdR20S0SdR1eS0SdR1cS0SdS3fS12S2fA1S28S2eA1M12A2M13S0SdS12PafA1S0SdS12Pb0A1S0SdR14S0SdR12S0SdR10S0SdReS0SdRcS0SdRaS0SdS3fS2cG12A2M14S0SdG13S0SdS13S7bS28S29A1G12A3S0SdG14R1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Lrest;Lr17;X4x2Ll15;Lr16;X4x2Ll14;Lr15;X4x2Ll13;Lr14;X4x2Ll12;Lr13;X4x2Ll11;Lr12;X4x2Ll10;Lr11;X4x2Ll9;Lr10;X4x2Ll8;Lr9;X4x2Ll7;Lr8;X4x2Ll6;Lr7;X4x2Ll5;Lr6;X4x2Ll4;Lr5;X4x2Ll3;Lr4;X4x2Ll2;Lr3;X4x2Ll1;Lr2;X4x2Ll0;Lr1;X4x2Ll;Lr0;X4x2").

Definition fs_facts (q : sv) : list sprop := ltac2:(tb__ "0|1|
S0SeS11S10Z10A1S28S13S7bS2bVq;A3A1M0A2S0SeS11G0S10S3cA1A2S3SeA1A3A3").
Definition q_facts : list sprop := ltac2:(tb__ "0|1|
S6SeS0SeS15S7cS2eS29A3S0SeS11S47Z10A1M0S28S29A1A2S0SeS11G0S28S2bA1A2S0SeS11S2eS10S3cA1A2S3SeA1A3A3A3A3S3eS2eA1A3").
Definition C_0c : axst := ltac2:(tb__ "0|7|
S77S34S17S9dS6cS23S76S34A1M0A1S16S7SdA1S4SfA1M1G1Lx;S24G0A1S3SfA1M2SfG1G1G1Ll;R1S0SfR2G2A3M3SfG1G1G1Ll0;R1S0SfR4G3A3M4SfG1G1G1Ll1;R1S0SfR6G4A3M5SfG1G1G1Ll2;R1S0SfR8G5A3M6SfG1G1G1Ll3;R1S0SfRaG6A3SfG1G1G1Ll4;R1S0SfRcS0SfS5eS12S2fA1S2eS2bA3S0SfR8S0SfR6S0SfR4S0SfR2S0SfSa6S3fS2cS28S2eA1A2PadA2G2A3A3A3A3A3A3A3SfG1S0SfReS0SfRcS0SfRaS0SfR8S0SfR6S0SfR4S0SfR2R1A3A3A3A3A3A3A3Ll5;Ls;X4x2Ll4;Lo5;X4x2Ll3;Lo4;X4x2Ll2;Lo3;X4x2Ll1;Lo2;X4x2Ll0;Lo1;X4x2Ll;Lo0;X4x2S6SeS70S22G0A1A3Pb1S8A9A2").
Definition C_0 : axst := Eval vm_compute in C_0c.

Definition stepD (S : axst) : axst := leafA_at S ra_L 0.
Definition D_1 : axst := Eval vm_compute in stepD C_0.
Definition D_2 : axst := Eval vm_compute in stepD D_1.
Definition D_3 : axst := Eval vm_compute in stepD D_2.
Definition D_4 : axst := Eval vm_compute in stepD D_3.
Definition D_5 : axst := Eval vm_compute in stepD D_4.
Definition D_6 : axst := Eval vm_compute in stepD D_5.
Definition D_7 : axst := Eval vm_compute in stepD D_6.
Definition D_8 : axst := Eval vm_compute in stepD D_7.
Definition D_9 : axst := Eval vm_compute in stepD D_8.
Definition D_10 : axst := Eval vm_compute in stepD D_9.
Definition D_11 : axst := Eval vm_compute in stepD D_10.
Definition D_12 : axst := Eval vm_compute in stepD D_11.
Definition D_13 : axst := Eval vm_compute in stepD D_12.
Definition D_14 : axst := Eval vm_compute in stepD D_13.
Definition D_15 : axst := Eval vm_compute in stepD D_14.

Definition X_step : axst := Eval vm_compute in stepD D_15.
Definition E_free : axst := Eval vm_compute in leafA_at D_15 free_pc 0.

Definition tiles2 : list (nat * sv * Z * sv) := ltac2:(tb__ "0|5|
S0S5S5S5S2SdA2M0S25A2M1SdA2M2S1G1SdS1G0S25S1S2SdU1M3S10Z0A1A4Z8M4A4S72A4S0G2S1G1SdS1G0S25S1S2SdG3S10G4A1A4G4A4S73A4S3G2A1A3A3").

Definition sel8 : list nat := ltac2:(tb__ "0|0|
S0S2U0S0S2U2S0S2U3S0S2U4S0S2U5S0S2U6S0S2U7S0S2U1S3S2A1A3A3A3A3A3A3A3A3").

Definition step_facts : list sprop := ltac2:(tb__ "0|1|
S6SeS0SeS15S7cS38S29A3S0SeS11S47Z20A1M0S28S29A1A2S0SeS11G0S28S2bA1A2S3SeA1A3A3A3S3eS38A1A3").
Definition X_t : axst := Eval vm_compute in ax_setS X_step (optS (tiles_at (ax_S X_step) tiles2)).
Definition X_f : axst := ax_add_facts step_facts X_t.
Definition X_s : axst := Eval vm_compute in optA (apply_axforms X_f [AXSplit 1 (SLit 16)]).
Definition X_r : axst := Eval vm_compute in ax_setS X_s (reshape_obj_at (ax_S X_s) 2 (O_fs (SVar pN) q1 vKn)).
Definition X_p : axst := Eval vm_compute in optA (apply_axforms X_r [AXSelect sel8]).

Definition X_a1 : axst := Eval vm_compute in drop_lastA X_p (removelast (ss_objs (ax_S X_p))).
Definition X_a2 : axst := Eval vm_compute in drop_lastA X_a1 (removelast (ss_objs (ax_S X_a1))).
Definition X_c : axst := Eval vm_compute in carve_ent_stateA X_a2 (pls vP (kb16 q1)).
Definition s_step : wsub := ltac2:(tb__ "0|4|
S0S5S26SdA2M0S1S26SdPacS38A4S0G0S1S26SdPadS12S1dS76S6aA1A1M1A1A4S0G0S1S26SdPaeS12Sa8G1A1A1A4S0G0S1S26SdPafS82SdU6S1bS76S44A1A1M2S10Z0A1M3A4A4S0G0S1S26SdPb0S82SdU7G2G3A4A4S3G0A1A3A3A3A3A3").

Definition cp0_facts : list sprop := ltac2:(tb__ "0|2|
S6SeS0SeS15S7cS10Z0A1M0S29A3S0SeS11S10Z10A1M1S28S29A1A2S0SeS11G1S28S2bA1A2S3SeA1A3A3A3S3eG0A1A3").
Definition X_cp0f : axst := ax_add_facts cp0_facts X_cp0.
Definition X_cp0c : axst := Eval vm_compute in carve_ent_stateA X_cp0f (pls vP (kb16 (SLit 0))).
Definition s_cp0 : wsub := ltac2:(tb__ "0|4|
S0S5S26SdA2M0S1S26SdPacS10Z0A1M1A4S0G0S1S26SdPadS12S1dS76S6bA1A1M2A1A4S0G0S1S26SdPaeS12Sa8G2A1A1A4S0G0S1S26SdPafS82SdU6S1bS76S34A1A1M3G1A4A4S0G0S1S26SdPb0S82SdU7G3G1A4A4S3G0A1A3A3A3A3A3").

Definition free_facts : list sprop := ltac2:(tb__ "0|0|
S0SeS11S29S38A2S3SeA1A3").
Definition sel7 : list nat := ltac2:(tb__ "0|0|
S0S2U0S0S2U2S0S2U3S0S2U4S0S2U5S0S2U6S0S2U1S3S2A1A3A3A3A3A3A3A3").
Definition E_ft : axst := Eval vm_compute in ax_setS E_free (optS (tiles_at (ax_S E_free) tiles2)).
Definition E_ff : axst := ax_add_facts free_facts E_ft.
Definition E_fp : axst := Eval vm_compute in optA (apply_axforms E_ff [AXSelect sel7]).
Definition E_fa1 : axst := Eval vm_compute in drop_lastA E_fp (removelast (ss_objs (ax_S E_fp))).
Definition E_fa2 : axst := Eval vm_compute in drop_lastA E_fa1 (removelast (ss_objs (ax_S E_fa1))).
Definition E_fc : axst := Eval vm_compute in carve_stateA E_fa2 vP (kb16 vK).
Definition X_rrT : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS30S10Z30A1A4S0G0S1SdSdS12S2fA1S28S2bA1A4S3G0A1A3A3").
Definition E_freeT : axst := Eval vm_compute in mkAX (ax_S E_fc) X_rrT shb.

Definition Pre_f : axst := Pre_free AE_A [] UStopLe.
Definition s_f : wsub := ltac2:(tb__ "0|1|
S0S5S26SdA2M0S1S26SdPfS33A4S0G0S1S26SdPdS28S29A1A4Sa7PaS76S5dA1S76S64A1A3A3A3").
Definition R_f : list sobj := Eval vm_compute in optR (entails_frA E_freeT Pre_f s_f).
Definition T_free : axst := Eval vm_compute in T_afterA Pre_f E_freeT s_f R_f (L_free AE_A [] UStopLe).

Definition vPn : sv := SVar 140.
Definition P_fail_S : sstate := ltac2:(tb__ "0|1|
S17S9cS94S95S92A1S0S5S2SdA2M0S1S2SdUaS10Z0A1A4S3G0A1A3A2S93S16S7SdA1S6SfS0SfS36S3S14A1A1S0SfS35S0SfS37S3SfA1A3A3A3S8eA3S39SabS8A9").
Definition P_fail : axst := mkA P_fail_S X_ra.
Definition ok_facts (p : sv) : list sprop := ltac2:(tb__ "0|4|
S0SeS19SdS26Lp;Vp;S25P8cM0Lz;S26R1Lv;S80SdSdG0Lb;La;M1Lop;M2G2S81G1Lop;M3G3S9S27SdG0La;Lw;Lsgn;S26SdS25G0Lk;Li;Ll;Xdx8Z4A2S0SeS1fS15S7eVp;S10Z0A1A3A1S0SeS11S10Z1000A1Vp;A2S0SeS11S13S7aVp;S28S2bA1A3S12P1eA1A2S0SeS11Vp;S10S40A1A2S0SeS11S10SaaA1Vp;A2S3SeA1A3A3A3A3A3A3").
Definition P_ok_S : sstate := ltac2:(tb__ "0|1|
S17S9cS94S95S92A1S0S5S2SdA2M0S1S2SdUaS3bA4S3G0A1A3A2S93S16S7SdA1S6SfS0SfS36S3S14A1A1S0SfS35S0SfS37S3SfA1A3A3A3S8eA3S6SeS48S3bA1S39A3P8dS8A9").
Definition P_ok : axst := ltac2:(tb__ "0|1|
S90S62S0S5SdSdA2M0S1SdSdS30S10Z30A1A4S0G0S1SdSdS3bS28S2bA1A4S3G0A1A3A3A2").

Definition P_okX_S : sstate := ltac2:(tb__ "0|2|
S17S9cS94S95Pc8A1S0S5S2SdA2M0S1S2SdUaS12S2fA1M1A4S3G0A1A3A2S93S16S7SdA1S6SfS0SfS36S3S14A1A1S0SfS35S0SfS37S3SfA1A3A3A3S8eA3S6SeS48G1A1S39A3Pe8S8A9").
Definition P_okX : axst := mkA P_okX_S X_rrT.
Definition s_post : wsub := Eval vm_compute in infer_sub NF (ax_S P_okX) (ax_S P_ok).

Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS2cS28S29A1A4S3G0A1A3").
Definition tv1 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS12S2fA1S28S2bA1A4S0G0S1SdSdS2cS28S29A1A4S3G0A1A3A3").
Definition tv2 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS12S2fA1S28S2bA1A4S3G0A1A3").
Definition tvP : list (sv * sv) := ltac2:(tb__ "0|1|
S0S5SdSdA2M0S1SdSdS3bS28S2bA1A4S3G0A1A3").
Definition bd0 : list bitem := ltac2:(tb__ "0|2|
S0S84S87Z1M0Z0M1S28S2bA1A3S0S84S86G1S99Z2S88A2G0A3S3S84A1A3A3").
Definition bd1 : list bitem := [BIc 0 KU 1].
Definition ndR (tv : list (sv * sv)) (bd : list bitem) : ndesc := ND tv [] bd.

Definition z0 : sv := SLit 0.

Definition VQ (c : Z) : sv := ltac2:(tb__ "0|0|
S13S7bS1eS7fS10Z20A1S13S7bS13S7aS10S97S40Z1A2A1S29A3S2eA3A3S10Vc;A1A3").

Definition Vs : list (list positive) := ltac2:(tb__ "0|3|
S0S4S26A1M0S3S26A1M1S0G0S0S26P6fM2S0S26PacS0S26PadS0S26PaeG1A3A3A3A3S0G0S0S26G2G1A3S3G0A1A3A3A3").
Definition cutsE : list efnode := ltac2:(tb__ "0|9|
S0S5S5S5S75S78A2M0S2A2M1S5S25SdA2M2A2M3S1G1G2S1G0S2S1S75S78S43S2dS3aS45A2A4U0M4A4S1S25SdZ64S31A4A4S0G3S1G1G2S1G0S2S1S75S78S67S2dS3aS3dA2A4G4A4S1S25SdZ50S31A4M5A4S0G3S1G1G2S1G0S2S1S75S78S68S2dS4aS3dA2M6A4G4A4G5A4S0G3S1G1G2S1G0S2S1S75S78S4cG6A4U1M7A4S1S25SdZ46M8S2aZ0A1A4A4S0G3S1G1G2S1G0S2S1S75S78S4dG6A4G7A4S1S25SdG8S2aZ1A1A4A4S0G3S1G1G2S1G0S2S1S75S78S54G6A4G7A4S1S25SdG8S2aZ3A1A4A4S0G3S1G1G2S1G0S2S1S75S78S55G6A4G7A4S1S25SdG8S2aZ5A1A4A4S0G3S1G1G2S1G0S2S1S75S78S56G6A4G7A4S1S25SdG8S2aZ7A1A4A4S0G3S1G1G2S1G0S2S1S75S78S57G6A4G7A4S1S25SdG8S2aZ9A1A4A4S0G3S1G1G2S1G0S2S1S75S78S58G6A4G7A4S1S25SdG8S2aZbA1A4A4S0G3S1G1G2S1G0S2S1S75S78S59G6A4G7A4S1S25SdG8S2aZdA1A4A4S0G3S1G1G2S1G0S2S1S75S78S5aG6A4G7A4S1S25SdG8S2aZfA1A4A4S0G3S1G1G2S1G0S2S1S75S78S5bG6A4G7A4S1S25SdG8S2aZ11A1A4A4S0G3S1G1G2S1G0S2S1S75S78S4eG6A4G7A4S1S25SdG8S2aZ13A1A4A4S0G3S1G1G2S1G0S2S1S75S78S4fG6A4G7A4S1S25SdG8S2aZ15A1A4A4S0G3S1G1G2S1G0S2S1S75S78S50G6A4G7A4S1S25SdG8S2aZ17A1A4A4S0G3S1G1G2S1G0S2S1S75S78S51G6A4G7A4S1S25SdG8S2aZ19A1A4A4S0G3S1G1G2S1G0S2S1S75S78S52G6A4G7A4S1S25SdG8S2aZ1bA1A4A4S0G3S1G1G2S1G0S2S1S75S78S53G6A4G7A4S1S25SdG8S2aZ1dA1A4A4S0G3S1G1G2S1G0S2S1S75S78S66S2dS4bS3S84A1A2A4U2A4S1S25SdZ3cS31A4A4S3G3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list efnode := ltac2:(tb__ "0|9|
S0S5S5S5S75S78A2M0S2A2M1S5S25SdA2M2A2M3S1G1G2S1G0S2S1S75S78S41S2dS3aS45A2A4U0M4A4S1S25SdZ5aS31A4A4S0G3S1G1G2S1G0S2S1S75S78S34S2dS4aS3dA2M5A4G4A4S1S25SdZ4bS31A4A4S0G3S1G1G2S1G0S2S1S75S78S44G5A4U1M6A4S1S25SdZ46S2aZ1fA1A4A4S0G3S1G1G2S1G0S2S1S75S78S5cG5A4G6A4S1S25SdZ41S31A4A4S0G3S1G1G2S1G0S2S1S75S78S60S2dS3aS3S84A1M7A2A4G4A4S1S25SdZ0S31A4M8A4S0G3S1G1G2S1G0S2S1S75S78S61S2dS4bG7A2A4U2A4G8A4S3G3A1A3A3A3A3A3A3").

Definition PhisV : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|2|
S83S4S26A1M0S5G0S1cOF_;M1A2G0S1G0G1R1S1cS8cL_;A4LV;S69A4").

Definition P0_ra (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S8bS25S25S8bS25S25S8bS25S25S89SacS5S5S25S25A2M0S25A2S1G0S25S1S25S25R3R2A4R1A4VFF;A3S89S98R3SafQ40S21Vr;PcA2A2M1A2S98S97G1Z30A2S97R3R2A2A2A2A2Lfl;A2Ls;A2Lf;A2").
Definition P0_rr (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S89S5fVFB;VFF;Vr;A3S25S89S98S85Vr;S2cA2M0R1A2S9bR1S97G0S99Z10S85Vr;S29A2A2A2A2A2S8dS8aSbSaeQ8A1M1A1S20Vr;SadQ40R2A2A2S7G1A1A3A1F_;Fz;A2").

Goal entailsA X_c C_0 s_step = true /\ entailsA X_cp0c C_0 s_cp0 = true /\ entailsA E_fc E_freeT [] = true
     /\ entailsA P_okX P_ok s_post = true
     /\ call_checkPA E_freeT Pre_f s_f R_f [L_free AE_A [] UStopLe] = true /\ length R_f = 2%nat
     /\ call_checkPA E_m Pre_m s_m R_m [L_malloc_null AE_A [] UStopLe; L_malloc_ok AE_A [] UStopLe] = true /\ length R_m = 2%nat.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma ejcertAF_ok0 : ltac2:(tb__ "0|0|
S8aS9Sa4S91S92S63S42S46P64S6dS6eA8ScA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ejcertAF_V : ltac2:(tb__ "0|6|
S4Sa9A1S26S4S5S4S26A1M0S1cOF_;M1A2M2A1M3G3S2S4S25A1S26S4Sa5A1M4G4S8aS4G0A1S83G2G0SaG0G1A2M5R7A4S83G2G0G5R6A4A3S8aS9Sa4RaR9R8R6R5R4R3R2A8Sa4RaR9R7R6R5R4R3R2A8A3F_;Fexits;Fcuts;Fg;Fcps;Ffuel;FPhis';FPhis;Fnp;Fsg;").
Proof.
  intros sg np Phis Phis' fuel cps g cuts exits H. unfold ejcertAF, eecheckJAF_pf, echeckJAF_pf, VK. rewrite H. reflexivity.
Qed.
End Lib_realloc_rom.

(* [comment removed for export] *)
Module Icpt_strnlen_st.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "true"; "bool"; "nil"; "Some"; "option"; "list"; "false"; "pair"; "app"; "prod"; "None"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "sym_runA"; "mkLeafA"; "axwf"; "entailsA"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sv"; "ss_next"; "sprop"; "sobj"; "SLit"; "ss_lenient"; "sstate"; "SPEq"; "sprop_below"; "FcsrFrm0"; "SAlu"; "mkSS"; "swf"; "DUnknown"; "SPBranch"; "SPUle"; "cell"; "mkObj"; "sprop_eqb"; "ss_facts"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXRebase"; "AXMerge"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "mkA"; "ACEIL"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Icpt_strnlen_st"; "CUTS_SI"; "FUEL_SI"; "facts_si"; "E_callS"; "E_ripS"; "P_si"; "Pre_si"; "s_call"; "D_SI"; "E_call"; "E_rip"; "G_B"; "G_S"; "R_B"; "R_S"; "R_call"; "R_rip"; "T_B"; "T_S"; "T_rip"; "T_ripF"; "s_rip"; "F_SI"; "T_imp"; "X_si"; "objs_si"; "si_ret"; "sp_B"; "sp_S"; "O_winI"; "XB4"; "XS4"; "si_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "RsSymJump"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Str_strnlenA_st"; "Pre_sn"; "P_sn"; "Posts_sn"; "sn_entry"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "O_cfsl"; "O_realmc"; "O_realsn"; "O_strS"; "factsB"; "factsS"; "facts_mci"; "sX"; "vXB"; "vXL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "O_rtc2"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Str_strnlenA_st.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import MCHAddr. Import RegionAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition si_entry : Z := 0x4d440.
Definition si_ret : Z := 0x4d52c.
Definition F_SI : Z := 2144.
Definition D_SI : Z := D_SN + F_SI.
Definition O_winI : sobj := ltac2:(tb__ "0|0|
S29S17PaA1S1cS68S3fA1A1S1cZ0A1S4S28A1S25A5").
Definition facts_si : list sprop := ltac2:(tb__ "0|0|
SaS1aS0S1aS27S1cS67S67S67S35Z1000A2Z20A2S4dA2A1S17PaA1A2S0S1aS26S6bS22S6aS17P10A1S1cZ1A1A3S17PeA1A3S4S1aA1A3A3S78A3").
Definition X_si : list (sv * sv) := ltac2:(tb__ "0|1|
S0SbS18S18A2M0S9S18S18S7aS7bA4S0G0S9S18S18S22S6aS17PaA1S1cS68S3fA1A1A3S1cS3fA1A4S4G0A1A3A3").
Definition objs_si : list sobj := ltac2:(tb__ "0|0|
SaS1bS0S1bS54S0S1bS75S0S1bS7cS0S1bS7dS0S1bS73S0S1bS74S0S1bS72S4S1bA1A3A3A3A3A3A3A3S36A3").

Definition Pre_si : axst := ltac2:(tb__ "0|1|
S34S23S57S5aS5cS0SbS1S18A2M0S9S1S18UaS79A4S0G0S9S1S18UbS17PeA1A4S0G0S9S1S18UcS17PdA1A4S4G0A1A3A3A3A2S59S21ScS18A1S50S39S58S8A9S4fA2").
Definition CUTS_SI : ltac2:(tb__ "0|0|
S7S2dA1") := ltac2:(tb__ "0|0|
S0S2dS65S0S2dS7fS0S2dS51S4S2dA1A3A3A3").
Definition FUEL_SI : nat := 300%nat.

Definition si_run_call__R : option (list leafA) := ltac2:(tb__ "0|0|
S12S33S38S37S3dS2A5").
Local Strategy expand [si_run_call__R].
Definition E_call : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => lf0 Pre_si (ro1__) 0) si_run_call__R).
Definition E_callS : axst := Eval vm_compute in match split_obj_at (ax_S E_call) 0 (SLit (- F_SI)) with Some S' => ax_setS E_call S' | None => E_call end.
Definition s_call : wsub := Eval vm_compute in infer_sub 10 (ax_S E_callS) (ax_S Pre_sn).
Definition R_call : list sobj := Eval vm_compute in match entails_frA E_callS Pre_sn s_call with Some R => R | None => [] end.
Definition T_imp : axst := Eval vm_compute in import_postA s_call Pre_sn P_sn E_callS R_call.
Definition T_impF : axst := ax_add_facts facts_si T_imp.

Definition T_S : axst := ax_add_facts factsS T_impF.
Definition T_B : axst := ax_add_facts factsB T_impF.

Definition si_run_S__R : option (list leafA) := ltac2:(tb__ "0|0|
S12S33S38S37S49S2A5").
Local Strategy expand [si_run_S__R].
Definition R_S : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => lf0 T_S (ro2__) 0) si_run_S__R).

Definition si_run_B__R : option (list leafA) := ltac2:(tb__ "0|0|
S12S33S38S37S48S2A5").
Local Strategy expand [si_run_B__R].
Definition E_rip : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => lf0 T_B (ro3__) 0) si_run_B__R).
Definition E_ripS : axst := Eval vm_compute in match split_obj_at (ax_S E_rip) 0 (SLit (-80)) with Some S' => ax_setS E_rip S' | None => E_rip end.
Definition s_rip : wsub := Eval vm_compute in ((16%positive, vXL8) :: infer_sub 10 (ax_S E_ripS) (ax_S Pre_rip)).
Definition R_rip : list sobj := Eval vm_compute in match entails_frA E_ripS Pre_rip s_rip with Some R => R | None => [] end.
Definition T_rip : axst := Eval vm_compute in import_postA s_rip Pre_rip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.P_ret E_ripS R_rip.
Definition T_ripF : axst := ltac2:(tb__ "0|0|
S81S0S1aS1fS17P8cA1S17P10A1A2S39A3S4aA2").
Definition si_run_B2__R : option (list leafA) := ltac2:(tb__ "0|0|
S12S33S38S37S4bS2A5").
Local Strategy expand [si_run_B2__R].
Definition R_B : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => lf0 T_ripF (ro4__) 0) si_run_B2__R).

Definition XS4 : list axform := ltac2:(tb__ "0|1|
S0S2eS2fU0M0A1S0S2eS31S0S1G0S0S1U7S0S1U1S0S1U2S0S1U3S0S1U4S0S1U8S0S1U9S0S1U5S0S1U6S4S1A1A3A3A3A3A3A3A3A3A3A3A1S0S2eS30G0A1S4S2eA1A3A3A3").
Definition XB4 : list axform := ltac2:(tb__ "0|3|
S0S2eS2fU0M0A1S0S2eS2fU4M1A1S0S2eS31S0S1G1S0S1G0S0S1U8S0S1U5S0S1U6S0S1U1S0S1U7S0S1U9S0S1UaS0S1U2S0S1U3S4S1A1A3A3A3A3A3A3A3A3A3A3A3A1S0S2eS30G0A1M2S0S2eG2S4S2eA1A3A3A3A3A3").
Definition G_S : axst := Eval vm_compute in match apply_axforms R_S XS4 with Some A => A | None => R_S end.
Definition G_B : axst := Eval vm_compute in match apply_axforms R_B XB4 with Some A => A | None => R_B end.
Definition P_si0 : axst := ltac2:(tb__ "0|1|
S34S23S51S5aS5bS58A1S0SbS1S18A2M0S9S1S18UaS17P8cA1A4S4G0A1A3A2S59S21ScS18A1S50S39P8dS8A9S4fA2").
Definition P_si : axst := ax_add_facts F_post P_si0.
Definition Posts_si : list leafA := ltac2:(tb__ "0|0|
S0S10S13S3cS5eA2S4S10A1A3").
Definition sp_S : wsub := Eval vm_compute in infer_sub NF (ax_S G_S) (ax_S P_si0).
Definition sp_B : wsub := Eval vm_compute in infer_sub NF (ax_S G_B) (ax_S P_si0).

Lemma si_wf : ltac2:(tb__ "0|0|
SeSdS3S14S3dA1S2A3SeSdS3S24SfS3dA1A1S2A3SeSdS3S14S3cA1S2A3SdS3S24SfS3cA1A1S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma si_run_call : ltac2:(tb__ "0|1|
SdS6S7S10A1M0A1S12S33S38S37S3dS2A5S5G0S0S10S13S40S5dA2S4S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) si_run_call__R <: si_run_call__R = Some [mkLeafA E_call RsCut]). Qed.
Lemma si_split_call : ltac2:(tb__ "0|0|
SdS6S1eA1S6eSfS40A1U0S1cS68S4dA1A1A3S5S1eSfS3aA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_efr_call : ltac2:(tb__ "0|1|
SdS6S7S1bA1M0A1S70S3aS62S3eA3S5G0S46A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_chk_call : ltac2:(tb__ "0|0|
SdS3S6fS3aS62S3eS46S69S10S11S16S64A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_imp_call : ltac2:(tb__ "0|0|
SdS11S71S3eS62S63S3aS46A5S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_run_S : ltac2:(tb__ "0|1|
SdS6S7S10A1M0A1S12S33S38S37S49S2A5S5G0S0S10S13S45S5dA2S4S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) si_run_S__R <: si_run_S__R = Some [mkLeafA R_S RsCut]). Qed.
Lemma si_run_B : ltac2:(tb__ "0|1|
SdS6S7S10A1M0A1S12S33S38S37S48S2A5S5G0S0S10S13S41S5dA2S4S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) si_run_B__R <: si_run_B__R = Some [mkLeafA E_rip RsCut]). Qed.
Lemma si_split_rip : ltac2:(tb__ "0|0|
SdS6S1eA1S6eSfS41A1U0S1cN50A1A3S5S1eSfS3bA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_efr_rip : ltac2:(tb__ "0|1|
SdS6S7S1bA1M0A1S70S3bS61S4cA3S5G0S47A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_chk_rip : ltac2:(tb__ "0|0|
SdS3S6fS3bS61S4cS47S69S10S11S16S80A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_imp_rip : ltac2:(tb__ "0|0|
SdS11S71S4cS61S7eS3bS47A5S4aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_run_B2 : ltac2:(tb__ "0|1|
SdS6S7S10A1M0A1S12S33S38S37S4bS2A5S5G0S0S10S13S44S5dA2S4S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) si_run_B2__R <: si_run_B2__R = Some [mkLeafA R_B RsCut]). Qed.
Lemma si_xf_S : ltac2:(tb__ "0|0|
SdS6S11A1S32S45S56A2S5S11S43A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_xf_B : ltac2:(tb__ "0|0|
SdS6S11A1S32S44S55A2S5S11S42A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_ent_S : ltac2:(tb__ "0|0|
SdS3S15S43S3cS53A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_ent_B : ltac2:(tb__ "0|0|
SdS3S15S42S3cS52A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma si_ids : ltac2:(tb__ "0|0|
SeSdS3S6cS53S58A2S2A3SdS3S6cS52S58A2S2A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma si_shape_call : ltac2:(tb__ "0|2|
SeSdS3S1dSfS3dA1M0A1S8A3SeSdS2cS19G0A1S58A3SeSdS2cS19SfS40A1A1S58A3SeSdS2cS19SfS3aA1A1S58A3SeSdS18S6dS3eP10M1A2S17G1A1A3SdS3S5fS1aS20S58A1S39A3S2A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma si_shape_imp : ltac2:(tb__ "0|5|
SeSdS2cS19SfS4eA1M0A1P8dM1A3SeSdS3S1dSfS49A1M2A1S8A3SeSdS2cS19G2A1G1A3SeSdS3S1dSfS48A1M3A1S8A3SeSdS2cS19G3A1G1A3SeSdS3S60S1aS2aS1fS17P8cA1S17P10A1A2A1S2bG0A1A3S2A3SeSdS3S5fS1aS20G1A1M4SaS1aS77S39A3A3S2A3SdS3S5fS1aG4SaS1aS76S39A3A3S2A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma si_shape_rip : ltac2:(tb__ "0|3|
SeSdS2cS19SfS3bA1A1S19SfS41A1A1M0A3SeSdS2cS19SfS4aA1A1Pb5M1A3SeSdS3S1dSfS4bA1M2A1S8A3SeSdS2cS19G2A1G1A3SeSdS3S66P8dG0A2S2A3SdS3S5fS1aS20G1A1S0S1aS1fS17P8cA1S17P10A1A2S39A3A3S2A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma si_shape_ret : ltac2:(tb__ "0|2|
SeSdS2cS19SfS45A1A1M0S19SfS43A1A1A3SeSdS2cS19SfS44A1A1M1S19SfS42A1A1A3SeSdS3S66P8dG0A2S2A3SdS3S66Pb5G1A2S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Icpt_strnlen_st.

