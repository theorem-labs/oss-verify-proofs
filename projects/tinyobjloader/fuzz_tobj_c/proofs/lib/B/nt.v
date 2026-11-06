(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_003.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.

(* [comment removed for export] *)
Module Lib_mat_find.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "pair"; "prod"; "None"; "bool"; "false"; "nat"; "true"; "app"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "cell"; "sobj"; "sprop"; "SPUle"; "FcsrFrm0"; "mkSS"; "valuation"; "DUnknown"; "SAlu"; "SPAlign"; "SVar"; "mkObj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vb"; "piece"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Lib_mat_find"; "FUEL_mf"; "Pre_mf"; "cutpcs_mf"; "P_mf"; "Posts_mf"; "Vd"; "cuts_mf"; "mf_facts"; "mf_objs"; "NXP_mf"; "O_mstk"; "exits_mf"; "vcuts_mf"; "vexits_mf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Lib_mat_find.MatFindAddr"; "mf_entry"; "mf_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module MatFindAddr.
  Definition mf_entry : Z := 0x9b4e0.
  Definition mf_ret : Z := 0x9b66c.
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
Module Lib_tess_polygon_chk0.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_tess_scale2d.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates.
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
Module Start6Run0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run0"; "M16_0"; "R16_0"; "IPm_0"; "F17_0"; "IPr_0"; "IP16_0"; "s16_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run16_0__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ0A1A1SfA5").
Local Strategy expand [run16_0__R].
Definition M16_0 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 0)) (ro1__)))) run16_0__R).
Lemma run16_0 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ0A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_0__R <: run16_0__R = Some [mkLeafA M16_0 RsCut]). Qed.
Lemma M16_0_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S37A3S1S0S4S26S1aA1S6S3eA1A3S1S0S4S7G0Z1A2S6S3cA1A3S1S0S4S7G0ZaA2S3dZ0M1A1A3S1S0S4S7G0ZbA2S6G1A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s16_0 : wsub := Eval vm_compute in infer_sub 1 (ax_S M16_0) (ax_S Pre_mszA).
Definition R16_0 : list sobj := Eval vm_compute in (match entails_frA M16_0 Pre_mszA s16_0 with Some R => R | None => [] end).
Lemma fr16_0 : ltac2:(tb__ "0|1|
S0S17S12S5A1M0A1S48S1aS30S20A3S13G0S1bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_0 : ltac2:(tb__ "0|0|
S0S14S47S1aS30S20S1bS43S21S24S29S32A4A5SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IP16_0 : axst := Eval vm_compute in import_postA s16_0 Pre_mszA (liftA P_msz) M16_0 R16_0.
Lemma IP16_0_eq : ltac2:(tb__ "0|0|
S0S24S49S20S30S44S31A1S1aS1bA5S1fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IPm_0 : sstate := Eval vm_compute in move_obj_last (ax_S IP16_0) 0.
Definition IPr_0 : axst := Eval vm_compute in ax_with_facts (ax_setS IP16_0 (set_objs IPm_0 R16_0)) (ss_facts (ax_S M16_0)).
Lemma IPr_0_facts : ltac2:(tb__ "0|3|
S1S0SeS39S22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S3bZ0A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_0__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_0__R].
Definition F17_0 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_0 (ro2__)))) run17x_0__R).
Lemma run17x_0 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_0__R <: run17x_0__R = Some [mkLeafA F17_0 RsCut]). Qed.
Lemma F17_0_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S37A3S1S0S4S26S1dA1S6S3eA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run0.

(* [comment removed for export] *)
Module Start6Run1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run1"; "M16_1"; "R16_1"; "IPm_1"; "F17_1"; "IPr_1"; "IP16_1"; "s16_1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run16_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ1A1A1SfA5").
Local Strategy expand [run16_1__R].
Definition M16_1 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 1)) (ro1__)))) run16_1__R).
Lemma run16_1 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ1A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_1__R <: run16_1__R = Some [mkLeafA M16_1 RsCut]). Qed.
Lemma M16_1_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S37A3S1S0S4S26S1aA1S6S3eA1A3S1S0S4S7G0Z1M1A2S6S3cA1A3S1S0S4S7G0ZaA2S3dG1A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s16_1 : wsub := Eval vm_compute in infer_sub 1 (ax_S M16_1) (ax_S Pre_mszA).
Definition R16_1 : list sobj := Eval vm_compute in (match entails_frA M16_1 Pre_mszA s16_1 with Some R => R | None => [] end).
Lemma fr16_1 : ltac2:(tb__ "0|1|
S0S17S12S5A1M0A1S48S1aS30S20A3S13G0S1bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_1 : ltac2:(tb__ "0|0|
S0S14S47S1aS30S20S1bS43S21S24S29S32A4A5SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IP16_1 : axst := Eval vm_compute in import_postA s16_1 Pre_mszA (liftA P_msz) M16_1 R16_1.
Lemma IP16_1_eq : ltac2:(tb__ "0|0|
S0S24S49S20S30S44S31A1S1aS1bA5S1fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IPm_1 : sstate := Eval vm_compute in move_obj_last (ax_S IP16_1) 0.
Definition IPr_1 : axst := Eval vm_compute in ax_with_facts (ax_setS IP16_1 (set_objs IPm_1 R16_1)) (ss_facts (ax_S M16_1)).
Lemma IPr_1_facts : ltac2:(tb__ "0|3|
S1S0SeS39S22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S3bZ1A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_1__R].
Definition F17_1 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_1 (ro2__)))) run17x_1__R).
Lemma run17x_1 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_1__R <: run17x_1__R = Some [mkLeafA F17_1 RsCut]). Qed.
Lemma F17_1_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S37A3S1S0S4S26S1dA1S6S3eA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run1.

(* [comment removed for export] *)
Module Start6Run2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run2"; "M16_2"; "R16_2"; "IPm_2"; "F17_2"; "IPr_2"; "IP16_2"; "s16_2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run16_2__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ2A1A1SfA5").
Local Strategy expand [run16_2__R].
Definition M16_2 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 2)) (ro1__)))) run16_2__R).
Lemma run16_2 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ2A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_2__R <: run16_2__R = Some [mkLeafA M16_2 RsCut]). Qed.
Lemma M16_2_at : ltac2:(tb__ "0|1|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S37A3S1S0S4S26S1aA1S6S3eA1A3S1S0S4S7G0Z1A2S6S3cA1A3S1S0S4S7G0ZaA2S3dZ2A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s16_2 : wsub := Eval vm_compute in infer_sub 1 (ax_S M16_2) (ax_S Pre_mszA).
Definition R16_2 : list sobj := Eval vm_compute in (match entails_frA M16_2 Pre_mszA s16_2 with Some R => R | None => [] end).
Lemma fr16_2 : ltac2:(tb__ "0|1|
S0S17S12S5A1M0A1S48S1aS30S20A3S13G0S1bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_2 : ltac2:(tb__ "0|0|
S0S14S47S1aS30S20S1bS43S21S24S29S32A4A5SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IP16_2 : axst := Eval vm_compute in import_postA s16_2 Pre_mszA (liftA P_msz) M16_2 R16_2.
Lemma IP16_2_eq : ltac2:(tb__ "0|0|
S0S24S49S20S30S44S31A1S1aS1bA5S1fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IPm_2 : sstate := Eval vm_compute in move_obj_last (ax_S IP16_2) 0.
Definition IPr_2 : axst := Eval vm_compute in ax_with_facts (ax_setS IP16_2 (set_objs IPm_2 R16_2)) (ss_facts (ax_S M16_2)).
Lemma IPr_2_facts : ltac2:(tb__ "0|3|
S1S0SeS39S22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S3bZ2A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_2__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_2__R].
Definition F17_2 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_2 (ro2__)))) run17x_2__R).
Lemma run17x_2 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_2__R <: run17x_2__R = Some [mkLeafA F17_2 RsCut]). Qed.
Lemma F17_2_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S37A3S1S0S4S26S1dA1S6S3eA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run2.

(* [comment removed for export] *)
Module Start6Run3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "reg_sv"; "ss_objs"; "ss_pc"; "sprop"; "sprop_below"; "ss_next"; "ss_facts"; "sstate"; "@Corelib.Init.Datatypes"; "true"; "cons"; "nil"; "list"; "Some"; "bool"; "length"; "nat"; "option"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run3"; "M16_3"; "R16_3"; "IPm_3"; "F17_3"; "IPr_3"; "IP16_3"; "s16_3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "sym_runA"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "mkLeafA"; "la_state"; "@Corelib.Init.Decimal"; "D0"; "D6"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "MEMSET"; "ECALL_MMAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "X0"; "withX0"; "move_obj_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States"; "R16c"; "O_ss"; "RA16"; "SSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run16_3__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ3A1A1SfA5").
Local Strategy expand [run16_3__R].
Definition M16_3 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1 (withX0 (R16c 3)) (ro1__)))) run16_3__R).
Lemma run16_3 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dS33S34S2bS2aS2aS2aS2cA1A1A1A1A1A1S10S2S2eS11S2A1A3S38S3aZ3A1A1SfA5S13G0S10S21S28S1aS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run16_3__R <: run16_3__R = Some [mkLeafA M16_3 RsCut]). Qed.
Lemma M16_3_at : ltac2:(tb__ "0|1|
S1S0S2S9S22S1aA1M0A1S2eA3S1S0S3ScG0A1P51A3S1S0S12S18S4S4A2A1S25S1aA1S37A3S1S0S4S26S1aA1S6S3eA1A3S1S0S4S7G0Z1A2S6S3cA1A3S1S0S4S7G0ZaA2S3dZ3A1A3S1S0S4S7G0ZbA2S6Z0A1A3S1S0S4S7G0ZcA2S6Z100000A1A3S0S16S15S5S8G0A1A2U1aA3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s16_3 : wsub := Eval vm_compute in infer_sub 1 (ax_S M16_3) (ax_S Pre_mszA).
Definition R16_3 : list sobj := Eval vm_compute in (match entails_frA M16_3 Pre_mszA s16_3 with Some R => R | None => [] end).
Lemma fr16_3 : ltac2:(tb__ "0|1|
S0S17S12S5A1M0A1S48S1aS30S20A3S13G0S1bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc16_3 : ltac2:(tb__ "0|0|
S0S14S47S1aS30S20S1bS43S21S24S29S32A4A5SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition IP16_3 : axst := Eval vm_compute in import_postA s16_3 Pre_mszA (liftA P_msz) M16_3 R16_3.
Lemma IP16_3_eq : ltac2:(tb__ "0|0|
S0S24S49S20S30S44S31A1S1aS1bA5S1fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition IPm_3 : sstate := Eval vm_compute in move_obj_last (ax_S IP16_3) 0.
Definition IPr_3 : axst := Eval vm_compute in ax_with_facts (ax_setS IP16_3 (set_objs IPm_3 R16_3)) (ss_facts (ax_S M16_3)).
Lemma IPr_3_facts : ltac2:(tb__ "0|3|
S1S0SeS39S22S1fA1M0U0A2S1cA3S1S0S14S45G0S1cA2SfA3S1S0S12S5A1S8S1cA1S19S5S1bS10S5S3bZ3A1S11S5A1A3A3A3S1S0S16S15S5S8G0A1A2U1aA3S1S0S24S46S27S27S1fS1cA2S41S1cS1bA2A2SdS22S1aA1A1M1A2S1eA3S1S0S14S42SaSbScG0A1M2A1G1A3SfA3S1S0S14S42SaSbP51A1G1A3SfA3S1S0S3G2P79A3S1S0S2S9S22S1eA1A1S4aS2eZf4A2A3S0S16S15S5S1bA2U19A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition run17x_3__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5").
Local Strategy expand [run17x_3__R].
Definition F17_3 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1 IPr_3 (ro2__)))) run17x_3__R).
Lemma run17x_3 : ltac2:(tb__ "0|1|
S0S17S12S21A1M0A1S23S2dUfa0S10S2S2fS11S2A1A3S1eSfA5S13G0S10S21S28S1dS3fA2S11S21A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run17x_3__R <: run17x_3__R = Some [mkLeafA F17_3 RsCut]). Qed.
Lemma F17_3_at : ltac2:(tb__ "0|2|
S1S0S2S9S22S1dA1M0A1M1S2fA3S1S0S17S35A1S40S2dG1A2S13S35S36A2A3S1S0S12S18S4S4A2A1S25S1dA1S37A3S1S0S4S26S1dA1S6S3eA1A3S1S0S4S7G0Z11A2S6ZdeA1A3S0S16S15S5S8G0A1A2U19A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6Run3.

