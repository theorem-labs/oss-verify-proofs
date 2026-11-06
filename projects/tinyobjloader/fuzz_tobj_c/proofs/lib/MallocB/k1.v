(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_lib F0A_blind j7 j8 ji k3.

(* [comment removed for export] *)
Module SpineCallocSec3IL.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IL.INST"; "nx0"; "CO1c"; "CO2c"; "CT1c"; "CT2c"; "T0c"; "ET1c"; "ET2c"; "D1c"; "E0c"; "R1c"; "R2c"; "T1c"; "T2c"; "s1c"; "s2c"; "D2c"; "run1"; "run2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sprop_below"; "valuation"; "swf"; "ss_objs"; "DUnknown"; "SLit"; "cell"; "mkObj"; "holds"; "rw"; "@Corelib.Init.Datatypes"; "nil"; "bool"; "cons"; "list"; "true"; "prod"; "app"; "option"; "pair"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "GS"; "SKEL0"; "JGs"; "JGsC"; "clsP"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "KcA"; "Kc_ok"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "ES1g"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "B2"; "F_map"; "L1"; "L2"; "Pret_ms"; "carveS"; "B1"; "O_1"; "a0e2"; "a2e1"; "a2e2"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Definition nx0 : positive := 220%positive.

Lemma Hnx_0 : ltac2:(tb__ "0|0|
S0S36S5cVW;Vst;Vtmax;A3S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXG_0 : ltac2:(tb__ "0|0|
S0S29S4aS34S6A2S2cA3").
Proof. reflexivity. Qed.

Definition E0c : axst := Eval vm_compute in (ES1g W st tmax).
Lemma HE0_0 : ltac2:(tb__ "0|0|
S0S2S5bVW;Vst;Vtmax;A3SfA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T0c : axst := Eval vm_compute in (ax_add_facts (F_map nx0 false) E0c).
Lemma SKT_0 : ltac2:(tb__ "0|1|
S0S2bS2dS2dS19S19A2S19A2M0A1S37S1aG0S3bS21S1SbA1A1A4S37S1aG0S3bS40U0S6A2A4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FCT_0 : ltac2:(tb__ "0|0|
S3dS1bS2eS1bS47VW;Vst;A2S46S45A1A3S1dS1SbA1A1A3").
Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBM_0 : ltac2:(tb__ "0|0|
S0S29S3cS1bS1eS1cS1SfA1A1A1S5eS6S32A2A3S2cA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma AF0_0 : ltac2:(tb__ "0|0|
S1fS2bS4cQ40A1A1S2dS2bS6dA1S6cA2S55S33R3R2SfR1A5S38S1bS26R4A1S5eS6S32A2A3S55S33R5R4SbR3A5F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hsm HF. replace T0c with (ax_add_facts (F_map nx0 false) E0c) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  apply smatchA_add_facts; [exact Hsm | exact HF | exact FBM_0].
Qed.

Definition run1 : option (list leafA) := Eval vm_compute in (runT0 T0c).
Lemma run1__runeq : ltac2:(tb__ "0|1|
S0S2bS2fS2bS3A1A1M0A1S52S33Ufa0S2aS35S3eS28S35A1A3S2aS2SbS28S2A1A3A4S2aG0S17S28G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run1]). Qed.
Definition ET1c : axst := Eval vm_compute in (leafS 0 run1).
Lemma Cert1_0 : ltac2:(tb__ "0|1|
S0S29S51S33Ufa0S2aS35S3eS28S35A1A3S3fS6A1S2aS2SbS28S2A1M0A3S2aS2ScG0A3A6S2cA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [T0c] [ET1c] [run1]); [exact run1__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT1c : axst := Eval vm_compute in (CT1 ET1c).
Definition CO1c : axst := Eval vm_compute in (CO1 W st tmax ET1c).
Lemma WC1_0 : ltac2:(tb__ "0|0|
S0S29S20S1S9A1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF1_0 : ltac2:(tb__ "0|4|
S0S2fS2dS2bS2dS19S19A2M0A1M1S2bS1bA1M2A2M3A1S50S1ScA1S1S9A1A2S31G3S30G1G2S2aG0S30S19S19S66S6A1S5fA4S28G0A1A3S28S1bA1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1_0 : ltac2:(tb__ "0|0|
S0S36S1cS1S9A1A1S1cS1ScA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC1_0 : ltac2:(tb__ "0|0|
S0S2S4ScS1S9A1A2S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK1_0 : ltac2:(tb__ "0|2|
S0S2bS2dS2dS19S19A2S19A2M0A1S37S1aG0S3bS21S1S9A1A1A4S37S1aG0S3bS2eS1aS28S1aA1M1S2eS1aS40U0S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC1_0 : ltac2:(tb__ "0|0|
S3dS1bS2eS1bS47VW;Vst;A2S46S45A1A3S1dS1S9A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC1_0 : ax_X CT1c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO1_0 : ltac2:(tb__ "0|0|
S0S2S62S9S25S63S6A1S23Z0A1S5fS28S24A1S22A5A2S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO1_0 : ltac2:(tb__ "0|0|
S0S29S20S1S7A1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s1c : wsub := Eval vm_compute in (callsub CO1c Pre_memsetA).
Definition R1c : list sobj := Eval vm_compute in (callR CO1c Pre_memsetA s1c).
Definition T1c : axst := Eval vm_compute in (callT CO1c Pre_memsetA Pret_ms s1c R1c).
Lemma He1_0 : ltac2:(tb__ "0|1|
S0S2fS2bS1aA1M0A1S59S7S39S14A3S31G0S10A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk1_0 : ltac2:(tb__ "0|0|
S0S29S58S7S39S14S10S37S3S2S5S3aA4A5S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT1_0 : ltac2:(tb__ "0|0|
S0S2S5aS14S39S61S7S10A5S12A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC1_0 : ltac2:(tb__ "0|1|
S0S29S3cS1bS1eS1cS1S7A1M0A1A1S1dG0A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT1_0 : ltac2:(tb__ "0|0|
S0S29S3cS1bS1eS1cS1S12A1A1A1S1dS1S7A1A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1_0 : ltac2:(tb__ "0|0|
S0S29S4aS3fS6A1S1cS1S7A1A1A2S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D1c : axst := Eval vm_compute in (ax_with_facts T1c (ss_facts (ax_S CO1c))).
Lemma HD1_0 : ltac2:(tb__ "0|0|
S0S2S53S12S1dS1S7A1A1A2SeA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run2 : option (list leafA) := Eval vm_compute in (runT0 D1c).
Lemma run2__runeq : ltac2:(tb__ "0|1|
S0S2bS2fS2bS3A1A1M0A1S52S33Ufa0S2aS35S3eS28S35A1A3S2aS2SeS28S2A1A3A4S2aG0S18S28G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run2]). Qed.
Definition ET2c : axst := Eval vm_compute in (leafS 0 run2).
Lemma Cert2_0 : ltac2:(tb__ "0|1|
S0S29S51S33Ufa0S2aS35S3eS28S35A1A3S3fS6A1S2aS2SeS28S2A1M0A3S2aS2SdG0A3A6S2cA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [D1c] [ET2c] [run2]); [exact run2__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT2c : axst := Eval vm_compute in (CT2 W st tmax ET2c).
Definition CO2c : axst := Eval vm_compute in (CO2 W st tmax ET2c).
Lemma WC2_0 : ltac2:(tb__ "0|0|
S0S29S20S1SaA1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF2_0 : ltac2:(tb__ "0|4|
S0S2fS2dS2bS2dS19S19A2M0A1M1S2bS1bA1M2A2M3A1S50S1SdA1S1SaA1A2S31G3S30G1G2S2aG0S30S19S19S65S6A1S5dS6A1A4S2aG0S30S19S19S67S6A1S60A4S28G0A1A3A3S68A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX2_0 : ltac2:(tb__ "0|0|
S0S36S1cS1SaA1A1S1cS1SdA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC2_0 : ltac2:(tb__ "0|0|
S0S2S4SdS1SaA1A2SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK2_0 : ltac2:(tb__ "0|2|
S0S2bS2dS2dS19S19A2S19A2M0A1S37S1aG0S3bS21S1SaA1A1A4S37S1aG0S3bS2eS1aS2aS1aS64S6A1S28S1aA1M1A3S2eS1aS40U0S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC2_0 : ltac2:(tb__ "0|0|
S3dS1bS2eS1bS47VW;Vst;A2S46S45A1A3S1dS1SaA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC2_0 : ax_X CT2c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO2_0 : ltac2:(tb__ "0|0|
S0S2S62SaS25S5dS6A1S23Z0A1S60S28S24A1S22A5A2S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO2_0 : ltac2:(tb__ "0|0|
S0S29S20S1S8A1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s2c : wsub := Eval vm_compute in (callsub CO2c Pre_memsetA).
Definition R2c : list sobj := Eval vm_compute in (callR CO2c Pre_memsetA s2c).
Definition T2c : axst := Eval vm_compute in (callT CO2c Pre_memsetA Pret_ms s2c R2c).
Lemma He2_0 : ltac2:(tb__ "0|1|
S0S2fS2bS1aA1M0A1S59S8S39S15A3S31G0S11A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk2_0 : ltac2:(tb__ "0|0|
S0S29S58S8S39S15S11S37S3S2S5S3aA4A5S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT2_0 : ltac2:(tb__ "0|0|
S0S2S5aS15S39S61S8S11A5S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC2_0 : ltac2:(tb__ "0|1|
S0S29S3cS1bS1eS1cS1S8A1M0A1A1S1dG0A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT2_0 : ltac2:(tb__ "0|0|
S0S29S3cS1bS1eS1cS1S13A1A1A1S1dS1S8A1A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC2_0 : ltac2:(tb__ "0|0|
S0S29S4aS3fS6A1S1cS1S8A1A1A2S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D2c : axst := Eval vm_compute in (ax_with_facts T2c (ss_facts (ax_S CO2c))).
Lemma HD2_0 : ltac2:(tb__ "0|0|
S0S2S53S13S1dS1S8A1A1A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Theorem sec_g12_0l : ltac2:(tb__ "0|5|
S4fOF_;S69S48S1fS4cQ40M0A1M1S2bG1A1M2S4eS6bVW;Vst;A2S49R6A1S57S33R9S56R7A1A3S4bG0S27R7PcA2A2S35S43S32S4bG0R7A2S6aR1A1A3S1fS1fG2S44S4bG0RbA2S6aR5A1RcR3A4S4dS33R10S54S33S41U0M3Vst;S6S69R1LX;M4RfReR4RcA8S16R3R2A5RaA4F_;FtpY;FrhoY;Frho';S1fS4dS33ReS54S33S42G3Vst;S6G4RdRcRbRaA8S5bVW;Vst;Vtmax;A3R1R9A5R8A4FrhoX;F_;F_;Tnv;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp Q HUS HKc Hokl nv HC HCONT rhoX. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  exact (sec_g12 0%nat st tmax false nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) E0c T0c SKT_0 FCT_0 AF0_0
           ET1c CT1c CO1c T1c ET2c CT2c CO2c T2c s1c s2c R1c R2c
           Cert1_0 ltac:(rewrite HD1_0; exact Cert2_0)
           WC1_0 DF1_0 NX1_0 HC1_0 SK1_0 FC1_0 XC1_0 HCO1_0 WCO1_0 He1_0 Hchk1_0 HT1_0 FBC1_0 FBT1_0 NXC1_0
           WC2_0 DF2_0 NX2_0 HC2_0 SK2_0 FC2_0 XC2_0 HCO2_0 WCO2_0 He2_0 Hchk2_0 HT2_0 FBC2_0 FBT2_0 NXC2_0
           ok A Kc rho a tp Q ltac:(hw_discharge) HUS HKc Hokl HC HCONT rhoX).
Qed.
End INST.
End SpineCallocSec3IL.

(* [comment removed for export] *)
Module SpineCallocSecE1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "sprop"; "ss_next"; "ss_facts"; "eval"; "SLit"; "sprop_below"; "rw"; "swf"; "ss_objs"; "DUnknown"; "cell"; "mkObj"; "obj_range"; "ranges_disjoint"; "holds"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "prod"; "nil"; "cons"; "app"; "pair"; "Some"; "option"; "nat"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "vna_state"; "SPfamEA"; "enodeA"; "to_enodeA"; "vmeasA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "smatchA"; "LQA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "budget_bound"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "Kc_ok"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@Stdlib.Lists.List"; "forallb"; "incl"; "In"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "SKEL0"; "slink"; "JGs"; "JGsC"; "clsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "B2"; "L1"; "L2"; "carveS"; "B1"; "O_1"; "Pret_ms"; "F_map"; "a0e2"; "a2e1"; "a2e2"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSecE1.SEC3E.G12E"; "HBLty"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SEC3E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z. Variable hi : bool.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S39S70VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S1cS45S71Vnx;A2S1dA3").
Variable AX : AA -> AA.
Hypothesis AXg : ltac2:(tb__ "0|0|
S3cS0S3fS3dVAX;R1A1A1S3dR1A1A3FX;").
Hypothesis AXb : ltac2:(tb__ "0|0|
S3cS0S38S3eVAX;R1A1A1S3eR1A1A3FX;").
Let GS : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.GS nx.
Let JGs : ltac2:(tb__ "0|0|
S3cS40SbS29Q40A1S33Fa;Frho;FKc;FA;") := ltac2:(tb__ "0|0|
S54VnW;Vst;Vnx;VAX;A4").
Let JGsC : ltac2:(tb__ "0|0|
S3cS40SbS29Q40A1S33Fa;Frho;FKc;FA;") := ltac2:(tb__ "0|0|
S55VnW;Vst;Vnx;VAX;A4").

Lemma ecfg_cutG : ltac2:(tb__ "0|1|
S25S1bS38A1S39S1bS2aA1M0G0S33S3bOF_;S1bS29Q40A1A1S4SbS34Vsegs;R8R5A3S2aS4bS2aR1R9A3S46RbSdS3S2dR2A1A1A1A2F_;Fn;S0S1cS2cVsegs;RcRbRaR9R8A6S1dA3S2aSbS4bS2aR2RbA3S3aVsegs;S32Vsegs;RbS2dR3A1R2R9A5S3bS2S2eVsegs;S26S2aS2fS30RcA1ReA4RaS31R4R3A2R1A5RbR1A1A2Lw;A3F_;Frho';FE;S4bS2aS2bR6Z1S10Z0A1A3RbA3S3aVsegs;S32Vsegs;RaR7R6R8A5R9A3F_;F_;F_;F_;F_;Frho;FC;Ftp;FQ;FJx;Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof. intros fuel cutpcs g cuts exits Jx Q tp C rho HS HN HC HE HI. exact (cfg_complete_autoA segs fuel cutpcs g cuts exits Jx Q tp HS HN HC HE (mkVNA C 1 (SLit 0)) rho HI). Qed.

Lemma etc_pre : ltac2:(tb__ "0|1|
S3bOF_;M0G0G0S3bR3R1A1R5R2A1F_;Fw;S3aVsegs;R4R2A3S3aVsegs;R4R3A3F_;F_;FQ;FP';FP;").
Proof. intros P P' Q HP H. exact (etriple_conseq P' Q HP (fun w Hw => Hw) H). Qed.

Lemma ecfg_1 : ltac2:(tb__ "0|3|
S1bS38A1S4S4S33S3bOF_;S1bS29Q40A1A1SbS34Vsegs;VGS;R4A3S0S1cS45VGS;SdS3R7A1A1A2S1dA3S0S1cS2cS68Ufa0R9VGS;S20S2aS2bR8Z1S10Z0M0A1M1A3S1fS2aA1M2A3S20S2aS2bR7G0G1A3G2A3A6S1dA3SbS3aVsegs;S32Vsegs;R8R9R1R6A5R7A3Frho';S3aVsegs;S32Vsegs;R8RaR5R6A5R7A3F_;F_;F_;F_;Frho;Ftp;FQ;FJx;FE;FC;Fcutpcs;").
Proof.
  intros cutpcs C E Jx Q tp rho HST NXC HC HE.
  apply (ecfg_cutG 4000%nat cutpcs GS [mkVNA C 1 (SLit 0)] [mkVNA E 0 (SLit 0)] Jx Q tp C rho HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. apply Pos.leb_le. exact NXC.
  - exact HC.
  - intros E' rho' HinE. destruct HinE as [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HE rho')].
  - left. reflexivity.
Qed.

Section MSE.
Variables (E C CO T : axst) (B L : sv) (P0 P : list sobj).
Variables (Pre Pret : axst) (Posts : list leafA) (s : wsub) (R : list sobj).
Hypothesis HPosts : ltac2:(tb__ "0|0|
S0S1bS5A1VPosts;S20S5S8VPret;S6fA2S1fS5A1A3A3").
Hypothesis Hsum : ltac2:(tb__ "0|0|
S33SbS1bS29Q40A1A1S34Vsegs;S57R3A3S3aVsegs;S32Vsegs;R4VPre;R3R2A5S36Vsegs;R4S57R3R2VPosts;A6A3F_;Ftp;Frho;FJx;").
Hypothesis NPre : ltac2:(tb__ "0|0|
S0S39SdS3VPre;A1A1S57A3").
Hypothesis RS : ltac2:(tb__ "0|1|
S3cS40SbS29Q40A1M0SbS1bG0A1S3bS51VW;Vst;A2S32Vsegs;VJGs;R8R7R6R5A4VE;R4R3R2A6S32Vsegs;VJGs;R9R8R7R6A4VC;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Hypothesis HBL : ltac2:(tb__ "0|a|
S3cS40SbS29Q40M0A1M1SbS1bG1A1S3bS32Vsegs;VJGs;R7R6R5R4A4VC;R3R2R1A6S1S4dS6bS28G0R5A2A1M2S28G0SfR4VB;A2A2M3A2S1S4dS4cG3S28G0SfR4VL;A2A2A2S4cG2S4eS4fS28G0S12R6PcA2A2A1Z8A2A2A2S1S1bS9A1M4S0S1bS1eS1eSaSaA2SaA2M5A1M6S26S9G5S37R1A4M7S26S9G5S37VP0;A4A3S27S9S9S19S18R7R1A2S22S38S38S28G0SfR7VB;A2A2M8S4cG8S28G0SfR7VL;A2A2A2A4A2Lo;R2A3M9F_;Fl;G4S0G6G7S26S9G5S37VP;A4A3G9F_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Hypothesis SKC : ltac2:(tb__ "0|1|
S0S1bS1eS1eSaSaA2SaA2M0A1S26S9G0S37S14S3VC;A1A1A4S26S9G0S37S21S9VP0;S21S9S52VnW;Vnx;A2VP;A3A3A4A3").
Hypothesis FCC : ltac2:(tb__ "0|0|
S4aScS21ScS43VW;Vst;A2S42S41A1A3SeS3VC;A1A1A3").
Hypothesis XC : ax_X C = [].
Hypothesis HCO : ltac2:(tb__ "0|0|
S0S4S5fVC;S17VB;S10Z0A1VL;S1fS16A1S15A5A2VCO;A3").
Hypothesis WCO : ltac2:(tb__ "0|0|
S0S1cS13S3VCO;A1A1S1dA3").
Hypothesis He : ltac2:(tb__ "0|1|
S0S24S1bS9A1M0A1S5aVCO;VPre;Vs;A3S23G0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S1cS59VCO;VPre;Vs;VR;S26S5S4S6VPosts;A4A5S1dA3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S4S5bVs;VPre;VPret;VCO;VR;A5VT;A3").
Hypothesis FBC : ltac2:(tb__ "0|1|
S0S1cS49ScS11SdS3VCO;A1M0A1A1SeG0A1A3S1dA3").
Hypothesis FBT : ltac2:(tb__ "0|0|
S0S1cS49ScS11SdS3VT;A1A1A1SeS3VCO;A1A1A3S1dA3").
Hypothesis NXC : ltac2:(tb__ "0|0|
S0S1cS45VGS;SdS3VCO;A1A1A2S1dA3").

Lemma ems_step : ltac2:(tb__ "0|4|
S3cS40SbSbS29Q40M0A1M1S1bG1A1M2S3bOF_;S51VW;Vst;A2S50VW;Vst;A2S44R8A1S53S28G0R6A2S4fS28G0S12R7PcA2A2A1R8R7A4SbG2S3aVsegs;S32Vsegs;VJGs;RdRcRaR9A4M3S58VT;SeS3VCO;A1A1A2R2R1A5R7A3FtpY;FrhoY;SbS3aVsegs;S32Vsegs;G3VE;R1R8A5R7A3FrhoX;F_;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp Q HW HUS HKc SL HD rhoX.
  pose proof (JGs_stable nW st tmax nx Hnx NXG AX A Kc rho a HUS HKc) as HST.

  apply (etc_pre (SPA segs (JGs A Kc rho a) CO rhoX tp)); [intros w Hw |].
  { pose proof (RS A Kc rho a rhoX tp w HW Hw) as HC.
    destruct (HBL A Kc rho a rhoX tp w HC) as (HB1 & HB2 & HDP0 & HDP).
    rewrite <- HCO. apply (carve_piece nW st tmax nx Hnx AX C B L A Kc rho0 rho a rhoX tp w SL HC); [rewrite HCO; exact WCO | exact XC | exact HB1 | exact HB2 |].
    destruct w as [trw [msw mdw]]. pose proof (proj2 HC) as HJc. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJc.
    destruct HJc as (_ & _ & _ & HPc & _ & _ & _ & HNc & _). pose proof HPc as (_ & _ & HLc & DIc & _). destruct DIc as (D0c & _ & DTc & _).
    pose proof (topG_range (aa_geom A)) as TG. pose proof (urange a) as Ra.
    pose proof (Sh_in_band (bv_unsigned a) ltac:(clear -Ra DTc TG HLc; lia)) as SB.
    apply (pieces_disjoint nW st tmax nx Hnx AX AXg C P0 P A Kc rho a rhoX tp _ _ _ HW HC SKC FCC); [| |exact HDP0|exact HDP].
    - clear -SB HB1. lia.
    - eapply Z.le_trans; [exact HB2|]. clear -DTc TG Ra HLc. unfold Sh, SHADOW_OFF, SHADOW_BAND_HI, HIGH_SHADOW_END in *.
      pose proof (Z.div_le_mono (bv_unsigned a + secmapsize (bv_unsigned (rw rho 12%positive))) 140737479966720 8 ltac:(lia) ltac:(lia)).
      assert (DS : bv_unsigned a / 8 + secmapsize (bv_unsigned (rw rho 12%positive)) / 8 <= (bv_unsigned a + secmapsize (bv_unsigned (rw rho 12%positive))) / 8).
      { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (bv_unsigned a) 8). pose proof (Z.mul_div_le (secmapsize (bv_unsigned (rw rho 12%positive))) 8). lia. }
      lia. }

  set (Jf := (fun (_ : valuation) t tr md => JGs A Kc rho a rhoX t tr md) : jpredA).
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (etriple_pre_pure segs _ _ (Forall (holds rhoX) (ss_facts (ax_S CO)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoX CO tp w Hw). }
  intros HFC.
  apply (call_completeA segs (JGs A Kc rho a) Jf Jf (JGs A Kc rho a) CO Pre s R Posts Q rhoX tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum Jf rho1 tp1 Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros Lf rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [apply Pos.leb_le; exact NXC | exact (proj1 HLK)].
  - intros Lf rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply etriple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD rho' tpL)].
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoX rho' _ Hag FBC HFC).
Qed.
End MSE.

Ltac byhyp L := intros; eapply L; eassumption.

Section G12E.
Variables E0 T0 : axst.
Hypothesis SKT : ltac2:(tb__ "0|1|
S0S1bS1eS1eSaSaA2SaA2M0A1S26S9G0S37S14S3VT0;A1A1A4S26S9G0S37S52VnW;Vnx;A2A4A3").
Hypothesis FCT : ltac2:(tb__ "0|0|
S4aScS21ScS43VW;Vst;A2S42S41A1A3SeS3VT0;A1A1A3").
Hypothesis AF0 : ltac2:(tb__ "0|0|
SbS1bS29Q40A1A1S1eS1bS6eA1S6dA2S35Vsegs;R3R2VE0;R1A5S27ScS1aR4A1S63Vnx;Vhi;A2A3S35Vsegs;R5R4VT0;R3A5F_;F_;Fw;Ftp;Frho;").
Variables (ET1 CT1 CO1 T1 ET2 CT2 CO2 T2 : axst) (s1 s2 : wsub) (R1 R2 : list sobj).
Let D1 : axst := ltac2:(tb__ "0|0|
S58VT1;SeS3VCO1;A1A1A2").
Let D2 : axst := ltac2:(tb__ "0|0|
S58VT2;SeS3VCO2;A1A1A2").

Hypothesis NXT0 : ltac2:(tb__ "0|0|
S0S1cS45VGS;SdS3VT0;A1A1A2S1dA3").
Hypothesis NXD1 : ltac2:(tb__ "0|0|
S0S1cS45VGS;SdS3VD1;A1A1A2S1dA3").
Hypothesis ECert1 : ltac2:(tb__ "0|3|
S0S1cS2cS68Ufa0S20S38S6aS1fS38A1A3VGS;S20S2aS2bVT0;Z1S10Z0M0A1M1A3S1fS2aA1M2A3S20S2aS2bVET1;G0G1A3G2A3A6S1dA3").
Hypothesis ECert2 : ltac2:(tb__ "0|3|
S0S1cS2cS68Ufa0S20S38S6aS1fS38A1A3VGS;S20S2aS2bVD1;Z1S10Z0M0A1M1A3S1fS2aA1M2A3S20S2aS2bVET2;G0G1A3G2A3A6S1dA3").

Hypothesis WC1 : ltac2:(tb__ "0|0|
S0S1cS13S3VCT1;A1A1S1dA3").
Hypothesis DF1 : ltac2:(tb__ "0|4|
S0S24S1eS1bS1eSaSaA2M0A1M1S1bScA1M2A2M3A1S69S3VET1;A1S3VCT1;A1A2S23G3S22G1G2S20G0S22SaSaS65Vnx;A1S5dA4S1fG0A1A3S1fScA1A4A2A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S39SdS3VCT1;A1A1SdS3VET1;A1A1A3").
Hypothesis HC1 : ltac2:(tb__ "0|0|
S0S4S7VET1;S3VCT1;A1A2VCT1;A3").
Hypothesis SK1 : ltac2:(tb__ "0|2|
S0S1bS1eS1eSaSaA2SaA2M0A1S26S9G0S37S14S3VCT1;A1A1A4S26S9G0S37S21S9S1fS9A1M1S21S9S52VnW;Vnx;A2G1A3A3A4A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S4aScS21ScS43VW;Vst;A2S42S41A1A3SeS3VCT1;A1A1A3").
Hypothesis XC1 : ax_X CT1 = [].
Hypothesis HCO1 : ltac2:(tb__ "0|0|
S0S4S5fVCT1;S17S60Vnx;A1S10Z0A1S5dS1fS16A1S15A5A2VCO1;A3").
Hypothesis WCO1 : ltac2:(tb__ "0|0|
S0S1cS13S3VCO1;A1A1S1dA3").
Hypothesis He1 : ltac2:(tb__ "0|1|
S0S24S1bS9A1M0A1S5aVCO1;S47Vs1;A3S23G0VR1;A2A3").
Hypothesis Hchk1 : ltac2:(tb__ "0|0|
S0S1cS59VCO1;S47Vs1;VR1;S26S5S4S6S48A4A5S1dA3").
Hypothesis HT1 : ltac2:(tb__ "0|0|
S0S4S5bVs1;S47S62VCO1;VR1;A5VT1;A3").
Hypothesis FBC1 : ltac2:(tb__ "0|1|
S0S1cS49ScS11SdS3VCO1;A1M0A1A1SeG0A1A3S1dA3").
Hypothesis FBT1 : ltac2:(tb__ "0|0|
S0S1cS49ScS11SdS3VT1;A1A1A1SeS3VCO1;A1A1A3S1dA3").
Hypothesis NXC1 : ltac2:(tb__ "0|0|
S0S1cS45VGS;SdS3VCO1;A1A1A2S1dA3").

Hypothesis WC2 : ltac2:(tb__ "0|0|
S0S1cS13S3VCT2;A1A1S1dA3").
Hypothesis DF2 : ltac2:(tb__ "0|4|
S0S24S1eS1bS1eSaSaA2M0A1M1S1bScA1M2A2M3A1S69S3VET2;A1S3VCT2;A1A2S23G3S22G1G2S20G0S22SaSaS64Vnx;A1S5cVnx;A1A4S20G0S22SaSaS66Vnx;A1S5eA4S1fG0A1A3A3S67A4A2A3").
Hypothesis NX2 : ltac2:(tb__ "0|0|
S0S39SdS3VCT2;A1A1SdS3VET2;A1A1A3").
Hypothesis HC2 : ltac2:(tb__ "0|0|
S0S4S7VET2;S3VCT2;A1A2VCT2;A3").
Hypothesis SK2 : ltac2:(tb__ "0|2|
S0S1bS1eS1eSaSaA2SaA2M0A1S26S9G0S37S14S3VCT2;A1A1A4S26S9G0S37S21S9S20S9S61Vnx;A1S1fS9A1M1A3S21S9S52VnW;Vnx;A2G1A3A3A4A3").
Hypothesis FC2 : ltac2:(tb__ "0|0|
S4aScS21ScS43VW;Vst;A2S42S41A1A3SeS3VCT2;A1A1A3").
Hypothesis XC2 : ax_X CT2 = [].
Hypothesis HCO2 : ltac2:(tb__ "0|0|
S0S4S5fVCT2;S17S5cVnx;A1S10Z0A1S5eS1fS16A1S15A5A2VCO2;A3").
Hypothesis WCO2 : ltac2:(tb__ "0|0|
S0S1cS13S3VCO2;A1A1S1dA3").
Hypothesis He2 : ltac2:(tb__ "0|1|
S0S24S1bS9A1M0A1S5aVCO2;S47Vs2;A3S23G0VR2;A2A3").
Hypothesis Hchk2 : ltac2:(tb__ "0|0|
S0S1cS59VCO2;S47Vs2;VR2;S26S5S4S6S48A4A5S1dA3").
Hypothesis HT2 : ltac2:(tb__ "0|0|
S0S4S5bVs2;S47S62VCO2;VR2;A5VT2;A3").
Hypothesis FBC2 : ltac2:(tb__ "0|1|
S0S1cS49ScS11SdS3VCO2;A1M0A1A1SeG0A1A3S1dA3").
Hypothesis FBT2 : ltac2:(tb__ "0|0|
S0S1cS49ScS11SdS3VT2;A1A1A1SeS3VCO2;A1A1A3S1dA3").
Hypothesis NXC2 : ltac2:(tb__ "0|0|
S0S1cS45VGS;SdS3VCO2;A1A1A2S1dA3").

Definition HBLty (C : axst) (B L : sv) (P0 P : list sobj) : Prop := ltac2:(tb__ "0|a|
S3cS40SbS29Q40M0A1M1SbS1bG1A1S3bS32Vsegs;VJGs;R7R6R5R4A4VC;R3R2R1A6S1S4dS6bS28G0R5A2A1M2S28G0SfR4VB;A2A2M3A2S1S4dS4cG3S28G0SfR4VL;A2A2A2S4cG2S4eS4fS28G0S12R6PcA2A2A1Z8A2A2A2S1S1bS9A1M4S0S1bS1eS1eSaSaA2SaA2M5A1M6S26S9G5S37R1A4M7S26S9G5S37VP0;A4A3S27S9S9S19S18R7R1A2S22S38S38S28G0SfR7VB;A2A2M8S4cG8S28G0SfR7VL;A2A2A2A4A2Lo;R2A3M9F_;Fl;G4S0G6G7S26S9G5S37VP;A4A3G9F_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Definition RSty (E C : axst) : Prop := ltac2:(tb__ "0|1|
S3cS40SbS29Q40A1M0SbS1bG0A1S3bS51VW;Vst;A2S32Vsegs;VJGs;R8R7R6R5A4VE;R4R3R2A6S32Vsegs;VJGs;R9R8R7R6A4VC;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Lemma RS1' : RSty ET1 CT1. Proof. unfold RSty. intros. eapply RS1; eassumption. Qed.
Lemma HBL1' : ltac2:(tb__ "0|1|
S6cVCT1;S60Vnx;A1S5dS1fS9A1M0G0A5"). Proof. unfold HBLty. intros. eapply (HBL1 nW st tmax nx Hnx AX ET1 CT1 ET2 CT2); eassumption. Qed.
Lemma RS2' : RSty ET2 CT2. Proof. unfold RSty. intros. eapply (RS2 nW st tmax nx Hnx AX ET1 CT1 ET2 CT2); eassumption. Qed.
Lemma HBL2' : ltac2:(tb__ "0|1|
S6cVCT2;S5cVnx;A1S5eS20S9S61Vnx;A1S1fS9A1M0A3G0A5"). Proof. unfold HBLty. intros. eapply (HBL2 nW st tmax nx Hnx AX ET1 CT1 ET2 CT2); eassumption. Qed.

Theorem esec_g12 : ltac2:(tb__ "0|4|
S3cS40SbS29Q40M0A1M1S1bG1A1M2S3bOF_;S51VW;Vst;A2S50VW;Vst;A2S44R7A1S56Vhi;S28G0R6A2S4fS28G0S12R7PcM3A2A2A1A3SbSbG2S53S28G0RaA2S4fS28G0S12RbG3A2A2A1RbR3A4S3aVsegs;S32Vsegs;VJGs;ReRdR4RbA4VD2;R3R2A5R9A3F_;FtpY;FrhoY;Frho';SbS3aVsegs;S32Vsegs;VJGsC;RcRbRaR9A4VE0;R1R8A5R7A3FrhoX;F_;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Proof.
  assert (USED := (SKT, FCT, AF0, NXT0, NXD1, ECert1, ECert2, WC1, DF1, NX1, HC1, SK1, FC1, XC1, HCO1, WCO1, He1, Hchk1, HT1, FBC1, FBT1, NXC1, WC2, DF2, NX2, HC2, SK2, FC2, XC2, HCO2, WCO2, He2, Hchk2, HT2, FBC2, FBT2, NXC2)); clear USED.
  intros A Kc rho a tp Q HW HUS HKc HC HCONT rhoX.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  apply (etc_pre (fun w => exists tp1 rhoX' rho', slink (bv_unsigned a) (secmapsize nv) rho rho' /\ SPA segs (JGs A Kc rho' a) T0 rhoX' (tp1 ++ tp) w)); [intros w Hw |].
  { destruct w as [tr [ms md]].
    destruct (sec_reveal nW st tmax hi nx Hnx AX AXg AXb E0 T0 SKT FCT AF0 A Kc rho a rhoX tp tr ms md HW HUS HKc HC Hw) as (tp1 & rhoX' & rho' & SL & _ & _ & Hsp).
    exists tp1, rhoX', rho'. exact (conj SL Hsp). }
  apply etriple_ex; intros tp1. apply etriple_ex; intros rhoX'. apply etriple_ex; intros rho'.
  apply (etriple_pre_pure segs _ _ (slink (bv_unsigned a) (secmapsize nv) rho rho')); [intros w [SL _]; exact SL|]. intros SL.
  apply (etc_pre (SPA segs (JGs A Kc rho' a) T0 rhoX' (tp1 ++ tp))); [intros w [_ Hw]; exact Hw|].
  assert (E12' : rw rho' 12%positive = rw rho 12%positive) by (destruct SL as (SW & _); apply SW).
  assert (HST : stableA segs GS (JGs A Kc rho' a)) by (apply (JGs_stable nW st tmax nx Hnx NXG AX); assumption).
  apply (ecfg_1 [MSENT] T0 ET1 (JGs A Kc rho' a) Q (tp1 ++ tp) rhoX' HST NXT0 ECert1). intros rhoE.
  apply (ems_step ET1 CT1 CO1 T1 (B1 nx) L1 [] [] Pre_memsetA Pret_ms Posts_memsetA s1 R1 eq_refl
           (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) eq_refl
           RS1' HBL1' SK1 FC1 XC1 HCO1 WCO1 He1 Hchk1 HT1 FBC1 FBT1 NXC1
           A Kc rho rho' a (tp1 ++ tp) Q HW HUS HKc); [unfold nv in SL; rewrite E12'; exact SL|].
  intros rhoY tpY. fold D1.
  apply (ecfg_1 [MSENT] D1 ET2 (JGs A Kc rho' a) Q tpY rhoY HST NXD1 ECert2). intros rhoE'.
  apply (ems_step ET2 CT2 CO2 T2 (B2 nx) L2 [O_1 nx] [] Pre_memsetA Pret_ms Posts_memsetA s2 R2 eq_refl
           (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs) eq_refl
           RS2' HBL2' SK2 FC2 XC2 HCO2 WCO2 He2 Hchk2 HT2 FBC2 FBT2 NXC2
           A Kc rho rho' a tpY Q HW HUS HKc); [unfold nv in SL; rewrite E12'; exact SL|].
  intros rhoZ tpZ. fold D2. apply HCONT. exact SL.
Qed.
End G12E.
End SEC3E.
End SpineCallocSecE1.

(* [comment removed for export] *)
Module SpineCallocSec3ILW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3ILW1.INST"; "nx0"; "CO1c"; "CO2c"; "CT1c"; "CT2c"; "T0c"; "ET1c"; "ET2c"; "D1c"; "E0c"; "R1c"; "R2c"; "T1c"; "T2c"; "s1c"; "s2c"; "D2c"; "run1"; "run2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sprop_below"; "valuation"; "swf"; "ss_objs"; "DUnknown"; "SLit"; "cell"; "mkObj"; "holds"; "rw"; "@Corelib.Init.Datatypes"; "nil"; "bool"; "cons"; "list"; "true"; "prod"; "app"; "option"; "pair"; "Some"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "GS"; "SKEL0"; "JGs"; "JGsC"; "clsP"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "KcA"; "Kc_ok"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "ES1g"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "B2"; "F_map"; "L1"; "L2"; "Pret_ms"; "carveS"; "B1"; "O_1"; "a0e2"; "a2e1"; "a2e2"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Definition nx0 : positive := 220%positive.

Lemma Hnx_0 : ltac2:(tb__ "0|0|
S0S36S5cVW;Vst;Vtmax;A3S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXG_0 : ltac2:(tb__ "0|0|
S0S29S4aS34S6A2S2cA3").
Proof. reflexivity. Qed.

Definition E0c : axst := Eval vm_compute in (ES1g W st tmax).
Lemma HE0_0 : ltac2:(tb__ "0|0|
S0S2S5bVW;Vst;Vtmax;A3SfA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T0c : axst := Eval vm_compute in (ax_add_facts (F_map nx0 false) E0c).
Lemma SKT_0 : ltac2:(tb__ "0|1|
S0S2bS2dS2dS19S19A2S19A2M0A1S37S1aG0S3bS21S1SbA1A1A4S37S1aG0S3bS40U1S6A2A4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FCT_0 : ltac2:(tb__ "0|0|
S3dS1bS2eS1bS47VW;Vst;A2S46S45A1A3S1dS1SbA1A1A3").
Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBM_0 : ltac2:(tb__ "0|0|
S0S29S3cS1bS1eS1cS1SfA1A1A1S5eS6S32A2A3S2cA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma AF0_0 : ltac2:(tb__ "0|0|
S1fS2bS4cQ40A1A1S2dS2bS6dA1S6cA2S55S33R3R2SfR1A5S38S1bS26R4A1S5eS6S32A2A3S55S33R5R4SbR3A5F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hsm HF. replace T0c with (ax_add_facts (F_map nx0 false) E0c) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  apply smatchA_add_facts; [exact Hsm | exact HF | exact FBM_0].
Qed.

Definition run1 : option (list leafA) := Eval vm_compute in (runT0 T0c).
Lemma run1__runeq : ltac2:(tb__ "0|1|
S0S2bS2fS2bS3A1A1M0A1S52S33Ufa0S2aS35S3eS28S35A1A3S2aS2SbS28S2A1A3A4S2aG0S17S28G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run1]). Qed.
Definition ET1c : axst := Eval vm_compute in (leafS 0 run1).
Lemma Cert1_0 : ltac2:(tb__ "0|1|
S0S29S51S33Ufa0S2aS35S3eS28S35A1A3S3fS6A1S2aS2SbS28S2A1M0A3S2aS2ScG0A3A6S2cA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [T0c] [ET1c] [run1]); [exact run1__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT1c : axst := Eval vm_compute in (CT1 ET1c).
Definition CO1c : axst := Eval vm_compute in (CO1 W st tmax ET1c).
Lemma WC1_0 : ltac2:(tb__ "0|0|
S0S29S20S1S9A1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF1_0 : ltac2:(tb__ "0|4|
S0S2fS2dS2bS2dS19S19A2M0A1M1S2bS1bA1M2A2M3A1S50S1ScA1S1S9A1A2S31G3S30G1G2S2aG0S30S19S19S66S6A1S5fA4S28G0A1A3S28S1bA1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1_0 : ltac2:(tb__ "0|0|
S0S36S1cS1S9A1A1S1cS1ScA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC1_0 : ltac2:(tb__ "0|0|
S0S2S4ScS1S9A1A2S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK1_0 : ltac2:(tb__ "0|2|
S0S2bS2dS2dS19S19A2S19A2M0A1S37S1aG0S3bS21S1S9A1A1A4S37S1aG0S3bS2eS1aS28S1aA1M1S2eS1aS40U1S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC1_0 : ltac2:(tb__ "0|0|
S3dS1bS2eS1bS47VW;Vst;A2S46S45A1A3S1dS1S9A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC1_0 : ax_X CT1c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO1_0 : ltac2:(tb__ "0|0|
S0S2S62S9S25S63S6A1S23Z0A1S5fS28S24A1S22A5A2S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO1_0 : ltac2:(tb__ "0|0|
S0S29S20S1S7A1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s1c : wsub := Eval vm_compute in (callsub CO1c Pre_memsetA).
Definition R1c : list sobj := Eval vm_compute in (callR CO1c Pre_memsetA s1c).
Definition T1c : axst := Eval vm_compute in (callT CO1c Pre_memsetA Pret_ms s1c R1c).
Lemma He1_0 : ltac2:(tb__ "0|1|
S0S2fS2bS1aA1M0A1S59S7S39S14A3S31G0S10A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk1_0 : ltac2:(tb__ "0|0|
S0S29S58S7S39S14S10S37S3S2S5S3aA4A5S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT1_0 : ltac2:(tb__ "0|0|
S0S2S5aS14S39S61S7S10A5S12A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC1_0 : ltac2:(tb__ "0|1|
S0S29S3cS1bS1eS1cS1S7A1M0A1A1S1dG0A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT1_0 : ltac2:(tb__ "0|0|
S0S29S3cS1bS1eS1cS1S12A1A1A1S1dS1S7A1A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1_0 : ltac2:(tb__ "0|0|
S0S29S4aS3fS6A1S1cS1S7A1A1A2S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D1c : axst := Eval vm_compute in (ax_with_facts T1c (ss_facts (ax_S CO1c))).
Lemma HD1_0 : ltac2:(tb__ "0|0|
S0S2S53S12S1dS1S7A1A1A2SeA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run2 : option (list leafA) := Eval vm_compute in (runT0 D1c).
Lemma run2__runeq : ltac2:(tb__ "0|1|
S0S2bS2fS2bS3A1A1M0A1S52S33Ufa0S2aS35S3eS28S35A1A3S2aS2SeS28S2A1A3A4S2aG0S18S28G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run2]). Qed.
Definition ET2c : axst := Eval vm_compute in (leafS 0 run2).
Lemma Cert2_0 : ltac2:(tb__ "0|1|
S0S29S51S33Ufa0S2aS35S3eS28S35A1A3S3fS6A1S2aS2SeS28S2A1M0A3S2aS2SdG0A3A6S2cA3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [D1c] [ET2c] [run2]); [exact run2__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT2c : axst := Eval vm_compute in (CT2 W st tmax ET2c).
Definition CO2c : axst := Eval vm_compute in (CO2 W st tmax ET2c).
Lemma WC2_0 : ltac2:(tb__ "0|0|
S0S29S20S1SaA1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF2_0 : ltac2:(tb__ "0|4|
S0S2fS2dS2bS2dS19S19A2M0A1M1S2bS1bA1M2A2M3A1S50S1SdA1S1SaA1A2S31G3S30G1G2S2aG0S30S19S19S65S6A1S5dS6A1A4S2aG0S30S19S19S67S6A1S60A4S28G0A1A3A3S68A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX2_0 : ltac2:(tb__ "0|0|
S0S36S1cS1SaA1A1S1cS1SdA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC2_0 : ltac2:(tb__ "0|0|
S0S2S4SdS1SaA1A2SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK2_0 : ltac2:(tb__ "0|2|
S0S2bS2dS2dS19S19A2S19A2M0A1S37S1aG0S3bS21S1SaA1A1A4S37S1aG0S3bS2eS1aS2aS1aS64S6A1S28S1aA1M1A3S2eS1aS40U1S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC2_0 : ltac2:(tb__ "0|0|
S3dS1bS2eS1bS47VW;Vst;A2S46S45A1A3S1dS1SaA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC2_0 : ax_X CT2c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO2_0 : ltac2:(tb__ "0|0|
S0S2S62SaS25S5dS6A1S23Z0A1S60S28S24A1S22A5A2S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO2_0 : ltac2:(tb__ "0|0|
S0S29S20S1S8A1A1S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s2c : wsub := Eval vm_compute in (callsub CO2c Pre_memsetA).
Definition R2c : list sobj := Eval vm_compute in (callR CO2c Pre_memsetA s2c).
Definition T2c : axst := Eval vm_compute in (callT CO2c Pre_memsetA Pret_ms s2c R2c).
Lemma He2_0 : ltac2:(tb__ "0|1|
S0S2fS2bS1aA1M0A1S59S8S39S15A3S31G0S11A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk2_0 : ltac2:(tb__ "0|0|
S0S29S58S8S39S15S11S37S3S2S5S3aA4A5S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT2_0 : ltac2:(tb__ "0|0|
S0S2S5aS15S39S61S8S11A5S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC2_0 : ltac2:(tb__ "0|1|
S0S29S3cS1bS1eS1cS1S8A1M0A1A1S1dG0A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT2_0 : ltac2:(tb__ "0|0|
S0S29S3cS1bS1eS1cS1S13A1A1A1S1dS1S8A1A1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC2_0 : ltac2:(tb__ "0|0|
S0S29S4aS3fS6A1S1cS1S8A1A1A2S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D2c : axst := Eval vm_compute in (ax_with_facts T2c (ss_facts (ax_S CO2c))).
Lemma HD2_0 : ltac2:(tb__ "0|0|
S0S2S53S13S1dS1S8A1A1A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Theorem sec_g12_1l : ltac2:(tb__ "0|5|
S4fOF_;S69S48S1fS4cQ40M0A1M1S2bG1A1M2S4eS6bVW;Vst;A2S49R6A1S57S33R9S56R7A1A3S4bG0S27R7PcA2A2S35S43S32S4bG0R7A2S6aR1A1A3S1fS1fG2S44S4bG0RbA2S6aR5A1RcR3A4S4dS33R10S54S33S41U1M3Vst;S6S69R1LX;M4RfReR4RcA8S16R3R2A5RaA4F_;FtpY;FrhoY;Frho';S1fS4dS33ReS54S33S42G3Vst;S6G4RdRcRbRaA8S5bVW;Vst;Vtmax;A3R1R9A5R8A4FrhoX;F_;F_;Tnv;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp Q HUS HKc Hokl nv HC HCONT rhoX. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  exact (sec_g12 1%nat st tmax false nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) E0c T0c SKT_0 FCT_0 AF0_0
           ET1c CT1c CO1c T1c ET2c CT2c CO2c T2c s1c s2c R1c R2c
           Cert1_0 ltac:(rewrite HD1_0; exact Cert2_0)
           WC1_0 DF1_0 NX1_0 HC1_0 SK1_0 FC1_0 XC1_0 HCO1_0 WCO1_0 He1_0 Hchk1_0 HT1_0 FBC1_0 FBT1_0 NXC1_0
           WC2_0 DF2_0 NX2_0 HC2_0 SK2_0 FC2_0 XC2_0 HCO2_0 WCO2_0 He2_0 Hchk2_0 HT2_0 FBC2_0 FBT2_0 NXC2_0
           ok A Kc rho a tp Q ltac:(hw_discharge) HUS HKc Hokl HC HCONT rhoX).
Qed.
End INST.
End SpineCallocSec3ILW1.

(* [comment removed for export] *)
Module SpineCallocSec3IW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.SpineCallocSec3IW1.INST"; "nx0"; "CO1c"; "CO2c"; "CT1c"; "CT2c"; "T0c"; "ET1c"; "ET2c"; "D1c"; "E0c"; "R1c"; "R2c"; "T1c"; "T2c"; "s1c"; "s2c"; "D2c"; "run1"; "run2"; "@Corelib.Init.Datatypes"; "true"; "nil"; "bool"; "cons"; "list"; "prod"; "app"; "option"; "pair"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sprop_below"; "valuation"; "swf"; "ss_objs"; "DUnknown"; "SLit"; "cell"; "mkObj"; "holds"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "GS"; "SKEL0"; "JGs"; "JGsC"; "clsP"; "slink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "KcA"; "Kc_ok"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS"; "ES1g"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST"; "B2"; "F_map"; "L1"; "L2"; "Pret_ms"; "carveS"; "B1"; "O_1"; "a0e2"; "a2e1"; "a2e2"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Definition nx0 : positive := 220%positive.

Lemma Hnx_0 : ltac2:(tb__ "0|0|
S0S35S5bVW;Vst;Vtmax;A3S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXG_0 : ltac2:(tb__ "0|0|
S0S1bS49S33S6A2S19A3").
Proof. reflexivity. Qed.

Definition E0c : axst := Eval vm_compute in (ES1g W st tmax).
Lemma HE0_0 : ltac2:(tb__ "0|0|
S0S2S5aVW;Vst;Vtmax;A3SfA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T0c : axst := Eval vm_compute in (ax_add_facts (F_map nx0 true) E0c).
Lemma SKT_0 : ltac2:(tb__ "0|1|
S0S1dS1eS1eS23S23A2S23A2M0A1S36S24G0S3aS2bS1SbA1A1A4S36S24G0S3aS3fU1S6A2A4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FCT_0 : ltac2:(tb__ "0|0|
S3cS25S1fS25S46VW;Vst;A2S45S44A1A3S27S1SbA1A1A3").
Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBM_0 : ltac2:(tb__ "0|0|
S0S1bS3bS25S28S26S1SfA1A1A1S5dS6S19A2A3S19A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma AF0_0 : ltac2:(tb__ "0|0|
S29S1dS4bQ40A1A1S1eS1dS6cA1S6bA2S54S32R3R2SfR1A5S37S25S30R4A1S5dS6S19A2A3S54S32R5R4SbR3A5F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hsm HF. replace T0c with (ax_add_facts (F_map nx0 true) E0c) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  apply smatchA_add_facts; [exact Hsm | exact HF | exact FBM_0].
Qed.

Definition run1 : option (list leafA) := Eval vm_compute in (runT0 T0c).
Lemma run1__runeq : ltac2:(tb__ "0|1|
S0S1dS20S1dS3A1A1M0A1S51S32Ufa0S1cS34S3dS1aS34A1A3S1cS2SbS1aS2A1A3A4S1cG0S17S1aG0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run1]). Qed.
Definition ET1c : axst := Eval vm_compute in (leafS 0 run1).
Lemma Cert1_0 : ltac2:(tb__ "0|1|
S0S1bS50S32Ufa0S1cS34S3dS1aS34A1A3S3eS6A1S1cS2SbS1aS2A1M0A3S1cS2ScG0A3A6S19A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [T0c] [ET1c] [run1]); [exact run1__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT1c : axst := Eval vm_compute in (CT1 ET1c).
Definition CO1c : axst := Eval vm_compute in (CO1 W st tmax ET1c).
Lemma WC1_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1S9A1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF1_0 : ltac2:(tb__ "0|4|
S0S20S1eS1dS1eS23S23A2M0A1M1S1dS25A1M2A2M3A1S4fS1ScA1S1S9A1A2S22G3S21G1G2S1cG0S21S23S23S65S6A1S5eA4S1aG0A1A3S1aS25A1A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1_0 : ltac2:(tb__ "0|0|
S0S35S26S1S9A1A1S26S1ScA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC1_0 : ltac2:(tb__ "0|0|
S0S2S4ScS1S9A1A2S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK1_0 : ltac2:(tb__ "0|2|
S0S1dS1eS1eS23S23A2S23A2M0A1S36S24G0S3aS2bS1S9A1A1A4S36S24G0S3aS1fS24S1aS24A1M1S1fS24S3fU1S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC1_0 : ltac2:(tb__ "0|0|
S3cS25S1fS25S46VW;Vst;A2S45S44A1A3S27S1S9A1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC1_0 : ax_X CT1c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO1_0 : ltac2:(tb__ "0|0|
S0S2S61S9S2fS62S6A1S2dZ0A1S5eS1aS2eA1S2cA5A2S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO1_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1S7A1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s1c : wsub := Eval vm_compute in (callsub CO1c Pre_memsetA).
Definition R1c : list sobj := Eval vm_compute in (callR CO1c Pre_memsetA s1c).
Definition T1c : axst := Eval vm_compute in (callT CO1c Pre_memsetA Pret_ms s1c R1c).
Lemma He1_0 : ltac2:(tb__ "0|1|
S0S20S1dS24A1M0A1S58S7S38S14A3S22G0S10A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk1_0 : ltac2:(tb__ "0|0|
S0S1bS57S7S38S14S10S36S3S2S5S39A4A5S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT1_0 : ltac2:(tb__ "0|0|
S0S2S59S14S38S60S7S10A5S12A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC1_0 : ltac2:(tb__ "0|1|
S0S1bS3bS25S28S26S1S7A1M0A1A1S27G0A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT1_0 : ltac2:(tb__ "0|0|
S0S1bS3bS25S28S26S1S12A1A1A1S27S1S7A1A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1_0 : ltac2:(tb__ "0|0|
S0S1bS49S3eS6A1S26S1S7A1A1A2S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D1c : axst := Eval vm_compute in (ax_with_facts T1c (ss_facts (ax_S CO1c))).
Lemma HD1_0 : ltac2:(tb__ "0|0|
S0S2S52S12S27S1S7A1A1A2SeA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run2 : option (list leafA) := Eval vm_compute in (runT0 D1c).
Lemma run2__runeq : ltac2:(tb__ "0|1|
S0S1dS20S1dS3A1A1M0A1S51S32Ufa0S1cS34S3dS1aS34A1A3S1cS2SeS1aS2A1A3A4S1cG0S18S1aG0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run2]). Qed.
Definition ET2c : axst := Eval vm_compute in (leafS 0 run2).
Lemma Cert2_0 : ltac2:(tb__ "0|1|
S0S1bS50S32Ufa0S1cS34S3dS1aS34A1A3S3eS6A1S1cS2SeS1aS2A1M0A3S1cS2SdG0A3A6S19A3").
Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] (GS nx0) [D1c] [ET2c] [run2]); [exact run2__runeq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Definition CT2c : axst := Eval vm_compute in (CT2 W st tmax ET2c).
Definition CO2c : axst := Eval vm_compute in (CO2 W st tmax ET2c).
Lemma WC2_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1SaA1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DF2_0 : ltac2:(tb__ "0|4|
S0S20S1eS1dS1eS23S23A2M0A1M1S1dS25A1M2A2M3A1S4fS1SdA1S1SaA1A2S22G3S21G1G2S1cG0S21S23S23S64S6A1S5cS6A1A4S1cG0S21S23S23S66S6A1S5fA4S1aG0A1A3A3S67A4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX2_0 : ltac2:(tb__ "0|0|
S0S35S26S1SaA1A1S26S1SdA1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HC2_0 : ltac2:(tb__ "0|0|
S0S2S4SdS1SaA1A2SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK2_0 : ltac2:(tb__ "0|2|
S0S1dS1eS1eS23S23A2S23A2M0A1S36S24G0S3aS2bS1SaA1A1A4S36S24G0S3aS1fS24S1cS24S63S6A1S1aS24A1M1A3S1fS24S3fU1S6A2G1A3A3A4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC2_0 : ltac2:(tb__ "0|0|
S3cS25S1fS25S46VW;Vst;A2S45S44A1A3S27S1SaA1A1A3"). Proof. apply inclb_incl. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC2_0 : ax_X CT2c = []. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HCO2_0 : ltac2:(tb__ "0|0|
S0S2S61SaS2fS5cS6A1S2dZ0A1S5fS1aS2eA1S2cA5A2S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WCO2_0 : ltac2:(tb__ "0|0|
S0S1bS2aS1S8A1A1S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s2c : wsub := Eval vm_compute in (callsub CO2c Pre_memsetA).
Definition R2c : list sobj := Eval vm_compute in (callR CO2c Pre_memsetA s2c).
Definition T2c : axst := Eval vm_compute in (callT CO2c Pre_memsetA Pret_ms s2c R2c).
Lemma He2_0 : ltac2:(tb__ "0|1|
S0S20S1dS24A1M0A1S58S8S38S15A3S22G0S11A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk2_0 : ltac2:(tb__ "0|0|
S0S1bS57S8S38S15S11S36S3S2S5S39A4A5S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT2_0 : ltac2:(tb__ "0|0|
S0S2S59S15S38S60S8S11A5S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBC2_0 : ltac2:(tb__ "0|1|
S0S1bS3bS25S28S26S1S8A1M0A1A1S27G0A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT2_0 : ltac2:(tb__ "0|0|
S0S1bS3bS25S28S26S1S13A1A1A1S27S1S8A1A1A3S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC2_0 : ltac2:(tb__ "0|0|
S0S1bS49S3eS6A1S26S1S8A1A1A2S19A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition D2c : axst := Eval vm_compute in (ax_with_facts T2c (ss_facts (ax_S CO2c))).
Lemma HD2_0 : ltac2:(tb__ "0|0|
S0S2S52S13S27S1S8A1A1A2S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Theorem sec_g12_1h : ltac2:(tb__ "0|5|
S4eOF_;S68S47S29S4bQ40M0A1M1S1dG1A1M2S4dS6aVW;Vst;A2S48R6A1S56S32R9S55R7A1A3S4aG0S31R7PcA2A2S34S42S19S4aG0R7A2S69R1A1A3S29S29G2S43S4aG0RbA2S69R5A1RcR3A4S4cS32R10S53S32S40U1M3Vst;S6S68R1LX;M4RfReR4RcA8S16R3R2A5RaA4F_;FtpY;FrhoY;Frho';S29S4cS32ReS53S32S41G3Vst;S6G4RdRcRbRaA8S5aVW;Vst;Vtmax;A3R1R9A5R8A4FrhoX;F_;F_;Tnv;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp Q HUS HKc Hokl nv HC HCONT rhoX. rewrite HE0_0. rewrite <- HD2_0 in HCONT.
  exact (sec_g12 1%nat st tmax true nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) E0c T0c SKT_0 FCT_0 AF0_0
           ET1c CT1c CO1c T1c ET2c CT2c CO2c T2c s1c s2c R1c R2c
           Cert1_0 ltac:(rewrite HD1_0; exact Cert2_0)
           WC1_0 DF1_0 NX1_0 HC1_0 SK1_0 FC1_0 XC1_0 HCO1_0 WCO1_0 He1_0 Hchk1_0 HT1_0 FBC1_0 FBT1_0 NXC1_0
           WC2_0 DF2_0 NX2_0 HC2_0 SK2_0 FC2_0 XC2_0 HCO2_0 WCO2_0 He2_0 Hchk2_0 HT2_0 FBC2_0 FBT2_0 NXC2_0
           ok A Kc rho a tp Q ltac:(hw_discharge) HUS HKc Hokl HC HCONT rhoX).
Qed.
End INST.
End SpineCallocSec3IW1.

(* [comment removed for export] *)
Module F0A_hbN_step.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "rm"; "rw"; "rl"; "ss_objs"; "eval"; "holds"; "odefault"; "sprop"; "DUnknown"; "DZero"; "agree_below"; "ob_dflt"; "ss_facts"; "@Corelib.Init.Datatypes"; "list"; "prod"; "nat"; "pair"; "app"; "length"; "bool"; "option"; "true"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "opp"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue"; "dspec"; "dobj"; "keepN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "bview"; "cell_ok"; "mkACell"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.Lists.List"; "In"; "Forall2"; "combine"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.F0A_hbN_step.StepW"; "ro_condW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib"; "s_C"; "s_bs"; "s_Cd"; "s_F"; "s_M"; "s_N"; "s_T"; "s_ZDn"; "s_ZDo"; "s_k"; "s_ok"; "strans"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_inside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_hbN_zones"; "in_zoneW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "carve_okq"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SegQS_lib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_hbN_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section StepW.
Variables (Zn TZ : Z -> Prop).
Variable J : jpredA.
Hypothesis HST : ltac2:(tb__ "0|0|
S36S5S49VJ;A3").
Let JWn : jpredA := ltac2:(tb__ "0|0|
S47S5VZn;VTZ;VJ;A4").

Definition ro_condW (rho : valuation) (d : dspec) : Prop := ltac2:(tb__ "0|d|
S19S19S19S19S9S6A2M0S6A2M1S18S19S19S6S1aA2M2S9A2M3A1M4A2M5S6A2OLd;Vd;G5S6G5OLp;R2G1G4G1OLp0;R2G0S6G0OLp1;R2S9S6S0S1S2eQ40M6A1M7SfVrho;R2A2M8S2fG6R7A2A3S0S0S22Z0M9R7A2S23R7S26Z2Z3eA2MaA2A2S0S22S25GaA1R1A2S0S22R1R3A2S0S22R3GaA2S0S22G9S21R7R1A2A2S0S56R1R3R5A3S0S6S0S22S21R8R2A2R1A2S23R1S21R8R4A2A2A2MbS2S6S6S2S1aS1aS2S9S9S2S6S6S0S40G3S1bG2S9S1bS6S1aR4R3A4R2A4RbA3S0S0S22S21RdR4A2McR6A2S23R6S21GcS24R3A1A2A2A2S0S1G7G8S2fG6R1A2A3S2cS2aS5SbVrho;A1A2S2dGcR3R1A3A2A2A2A2Lval;A2Le;A2Lk;A2Loff;A2F_;Fz;S6GbVTZ;R2A1F_;Fz;A2A2A2A2A2A2A2A2Llo;Lb;X19x1Lhi;Lp1;X19x1Lcs;Lp0;X19x1La;Lp;X19x1").

Lemma ro_dissolveW : ltac2:(tb__ "0|3|
S39S18S8A1M0S18S27A1SaS18S2eQ40A1M1A1S18S3cA1M2S3aS3bS1G0SeS37R8A1A1S1cS8R7S32S27S8S28R6A4A3A3S35S5VJWn;R9R6R5S1bG2S33R4S34R3R2A2A4A6S31S27S48R7A1R8A3S3dR8S32S27S8S28R9A4S3fR4R7R5A3A3SaS0S35S5VJWn;S38RcS43S37RcA1RbA2A2R1R8S1bG2S33R7S34R6R5A2A4A6S0S7S1G1ScR2R1A2ScRaR1A2A3Fi;S0S7S1S18S2eQ8A1A1SdR2R1A2SdRaR1A2A3Fl;S1S2bS2aS5SbR1A1A2S2aS5SbR9A1A2A3A2A2A2Trho3;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fds;FBASE;FC;").
Proof.
  intros C BASE ds rho tp tr ms md HOBJ HS HD rho3.
  pose proof (proj1 (proj1 HS)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)).
  assert (INZ : forall z, dzone ds z -> v3 z = v z).
  { intros z Hz. apply List.Exists_exists in Hz as (d & Hd & Hz). pose proof (proj1 (Forall_forall _ _) HD d Hd) as X. destruct d as [[[[b lo] hi] cs] a].
    destruct X as (Eb & A1' & L1 & L2 & L3 & L4 & CI & HC & _).
    destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) BASE (map dobj ds) b lo hi cs Hsm HOBJ (in_map dobj ds _ Hd) ltac:(lia) ltac:(lia) ltac:(lia) CI
                ltac:(rewrite Eb, u64_lit by lia; lia) ltac:(rewrite Eb, u64_lit by lia; lia)) as [AVc PRc].
    fold rho3 in AVc, PRc. rewrite Eb, u64_lit in AVc, PRc by lia.
    destruct (HC z Hz) as (off & k & e & val & Hin & Hzc & Ee & Cv).
    pose proof (av_cell (view segsA (rm rho3)) a off k e val rho (fun j Hj => AVc off k e j Hin Hj) Ee) as C3.
    exact (cell_ok_same v v3 _ Cv C3 z ltac:(cbn [c_addr c_w]; lia)). }
  assert (INRG : forall x, in_ranges rho (map dobj ds) x -> dzone ds (bv_unsigned x)).
  { intros x (o & Ho & Hz). apply in_map_iff in Ho as (d & <- & Hd). pose proof (proj1 (Forall_forall _ _) HD d Hd) as X. apply List.Exists_exists. exists d. split; [exact Hd|].
    destruct d as [[[[b lo] hi] cs] a]. destruct X as (Eb & A1' & L1 & L2 & L3 & _). rewrite (dobj_range rho b lo hi cs a Eb A1' L1 L2 L3) in Hz. cbn [fst snd] in Hz. exact Hz. }
  destruct (absorb_out rho (map dobj ds) (vms md tp ms) (dzone ds) INRG) as [FR FRrm]. fold rho3 in FR, FRrm.
  assert (EV : v3 = v).
  { apply functional_extensionality. intros z. destruct (dzone_dec ds z) as [Hz|Nz]; [exact (INZ z Hz) | exact (FR z Nz)]. }
  pose proof (SPA_unobj segsA JWn rho C BASE (map dobj ds) tp tr ms md HOBJ HS) as HU. cbn zeta in HU. fold rho3 in HU.
  split; [|split; [intros i; reflexivity | split; [intros l; reflexivity | exact EV]]].
  apply HU. intros HJ. apply (JW_change segsA Zn TZ J rho rho3 tp tr md); [intros i; reflexivity | intros l; reflexivity | | | | exact HJ].
  - intros z _. fold v3 v. rewrite EV. reflexivity.
  - intros z _ Hp. fold v3. rewrite EV. exact Hp.
  - intros a0 NT. apply FRrm. intros Hz. apply NT. apply List.Exists_exists in Hz as (d & Hd & Hz). pose proof (proj1 (Forall_forall _ _) HD d Hd) as X.
    destruct d as [[[[b lo] hi] cs] a]. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & HT). exact (HT _ Hz).
Qed.

Variables (zb zlo zhi : nat -> Z) (ZU : list nat).
Hypothesis Hsep : ltac2:(tb__ "0|3|
S1aS1aS40S1aR2VZU;A3M0G0S4S1S1aR4R3A3A1S3S22S21Vzb;R5A1M1Vzhi;R5A1A2S21Vzb;R4A1M2Vzlo;R4A1A2A2S22S21G2Vzhi;R4A1A2S21G1Vzlo;R5A1A2A2A2F_;F_;F_;Fz';Fz;").

Lemma s_stepW : ltac2:(tb__ "0|8|
S55S18S27A1S18S2eQ40A1M0A1M1SaG1S18S3cA1M2S3aS3bS1S1eS54R8A1S20A3S1S18S8A1SeS37S4aR9A1M3A1A1S1cS8S29G3S53R9A1A2S32S27S8S28R8A4A3A3S1S1aS1dG0R8A2S1dS7S4bRaA1A2A3S35S5VJWn;S4aRbA1R8R7S1bG2S33R6S34R5R4A2A4A6S31S27S48R9A1RbA3S3dRaS32S27S8S28RcA4S3fR6R9R7A3A3SaS58R1S42S7G0S4bReA1RcA4A2SaS1S2bS2aS5SbR2A1A2S2aS5SbRcA1A2A3VJWn;R2RcRbR9A4S0S31S45S59R3A1S4fR11A1M4A3S0S41S8S44S57R3Vzb;Vzlo;Vzhi;VZU;A5M5S32S45S8S46G4A4S51R11A1A5S0S41S8S44G5SeS37S4cR11A1A1M6A1S52R11A1A5S31S12S10R3A1S17G6A1A3S31S12S10R4A1S4dR12A1A3F_;A2A2A2F_;F_;S2SaSaS0S35S5VJWn;S50R11A1R1RdS1bG2S33RcS34RbRaA2A4A6S0S7S9S40S19S7S9A2S1bS7S9R2R1A4S4eR13A1A3S1G0ScR4R3A2SfR6R2A2A3F_;Fe;Fv;S0S1G0S1fS2eQ8A1A1F_;SbR1A1SbR4A1M7A3S0S15S49R3R1A3S1S2bS2aS5G7A2S2aS5SbReA1A2A3A2A2A2A2Lrho5;A2F_;Trho4;Trho3;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fvals;FdsD;Ft;").
Proof.
  intros t dsD vals rho tp tr ms md HOK HOBJ HLEN HS HDC rho3 rho4 HCONT.
  pose proof (JW_stable segsA NPRE Zn TZ J HST) as HSTW. fold JWn in HSTW.
  unfold s_ok in HOK. repeat (apply andb_prop in HOK as [HOK ?]).
  match goal with H : forallb (fun d => forallb _ _) _ = true |- _ => rename H into OKZX end.
  match goal with H : zcheck _ = true |- _ => rename H into OKZC end.
  match goal with H : entsM _ _ _ = true |- _ => rename H into OKENT end.
  match goal with H : forallb (sprop_below _) _ = true |- _ => rename H into OKBEL end.
  match goal with H : swf _ = true |- _ => rename H into OKSWF end.
  match goal with H : forallb _ (s_bs t) = true |- _ => rename H into OKBS end.
  match goal with H : sv_vars_all _ _ = true |- _ => rename H into OKV2 end.
  match goal with H : state_vars_all _ _ = true |- _ => rename H into OKV1 end.
  assert (HX : ax_X (s_C t) = []) by (destruct (ax_X (s_C t)); [reflexivity | discriminate HOK]).
  destruct (ro_dissolveW (s_C t) (keepN (s_C t) (s_k t)) dsD rho tp tr ms md HOBJ HS HDC) as (H1 & RW3 & RL3 & EV).
  fold rho3 in H1, RW3, RL3, EV. change (SPA segsA JWn (s_Cd t) rho3 tp (tr, mkCfg ms md)) in H1.
  assert (MF : map fst (combine (s_bs t) vals) = s_bs t).
  { clear - HLEN. revert vals HLEN. induction (s_bs t) as [|b r IH]; intros vals HLEN; destruct vals as [|x vs]; cbn in *; try reflexivity; try discriminate. f_equal. apply IH. lia. }
  assert (H2 : SPA segsA JWn (s_Cd t) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_bindV segsA _ NPRE (s_Cd t) rho3 tp _ _ HX HSTW); [| rewrite MF; exact OKV1 | rewrite MF; exact OKV2 | exact H1].
    intros v Hv. rewrite MF in Hv. pose proof (proj1 (forallb_forall _ _) OKBS v Hv) as X. apply Pos.leb_le. exact X. }
  destruct (HCONT EV (proj2 H2)) as (CC & ZN & ZO & HFN).
  pose proof (SPA_facts_hold segsA _ rho4 (s_Cd t) tp _ H2) as HFa.
  assert (H3 : SPA segsA JWn (s_Ca t) rho4 tp (tr, mkCfg ms md)).
  { pose proof (SPA_carve_list segsA JWn rho4 (s_Cd t) tp _ (s_N t) (ss_next (ax_S (s_Cd t))) H2) as Y. cbn zeta in Y. apply Y; clear Y.
    - exact OKSWF.
    - apply Pos.le_refl.
    - apply carve_okq_list; [exact HX | exact CC].
    - exact (zonesW_cross rho4 zb zlo zhi ZU Hsep _ _ _ _ ZN ZO OKZX).
    - exact (zonesW_pd rho4 zb zlo zhi ZU Hsep _ _ ZN OKZC). }
  assert (H4 : SPA segsA JWn (s_Cc t) rho4 tp (tr, mkCfg ms md)).
  { unfold s_Cc, addF. apply SPA_refacts; [exact H3 | exact OKBEL |]. intros HF4. apply Forall_app. split; [exact HF4 | apply HFN; exact HFa]. }
  destruct (entM_SPA JWn _ (s_T t) (s_M t) rho4 tp _ OKENT HSTW H4) as (H5 & AG5 & V5 & RM5).
  eexists. split; [exact H5|]. split; [exact V5|]. split; [|split; [exact AG5 | exact EV]]. rewrite RM5. unfold rho4. apply rm_rho_sets.
Qed.
End StepW.

Section DissolveZ.
Variables (Zn TZ : Z -> Prop).
Variable J : jpredA.
Hypothesis HZT : ltac2:(tb__ "0|0|
S6VZn;R1A1VTZ;R2A1F_;Fz;").
Let JWn : jpredA := ltac2:(tb__ "0|0|
S47S5VZn;VTZ;VJ;A4").
Lemma dissolveZW : ltac2:(tb__ "0|5|
S39S18S8A1M0G0SaS18S2eQ40M1A1M2A1S18S3cA1M3S3aS3bS1G0SeS37R8A1A1S1cS8R7R6A3A3S35S5VJWn;R9R6R5S1bG3S33R4S34R3R2A2A4A6G2S3eR8R9R1A3VZn;S30G1R2A2A1F_;Fx;S31S8S8S3S1S11S16R1A1M4S13A3S1S11G4S14A3A2Lo;R9A3S3dR9RaS3fR5R8R6A3A3SaS0S35S5VJWn;S38RdS43S37RdA1RcA2A2R1R9S1bG3S33R8S34R7R6A2A4A6S0S7S1G2ScR2R1A2ScRbR1A2A3Fv;S7S1S18S2eQ8A1A1SdR2R1A2SdRbR1A2A3Fl;A2A2Trho2;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FR;FBASE;FC;").
Proof.
  intros C BASE R rho tp tr ms md HOBJ HS IRZ HD rho2.
  pose proof (proj1 (proj1 HS)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (v := view segsA (rm rho)). set (v2 := view segsA (rm rho2)).
  assert (PRS : forall z, v z <> None -> v2 z <> None).
  { intros z Hd. destruct (IRdec rho R z) as [[Hz Hin]|NI]; [|unfold v2, rho2; rewrite (proj2 (absorb_io rho R (vms md tp ms)) z NI); exact Hd].
    destruct Hin as (o & Ho & Hr). rewrite u64_lit in Hr by lia.
    destruct (SpineMallocS9.absorb_obj rho _ tr (vms md tp ms) (vmd md) BASE R o Hsm HOBJ Ho) as (_ & _ & X3 & _). cbn zeta in X3.
    pose proof (proj1 (Forall_forall _ _) HD o Ho) as Do. unfold obj_range in Hr. cbn [fst snd] in Hr.
    destruct (X3 Do (z - bv_unsigned (eval rho (ob_base o))) ltac:(lia)) as [x Hx].
    unfold v2, rho2. rewrite view_in by lia.
    replace (Z_to_bv 64 z) with (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + (z - bv_unsigned (eval rho (ob_base o))))) by (f_equal; lia).
    rewrite Hx. discriminate. }
  assert (EQF : forall z, ~ Zn z -> v2 z = v z).
  { intros z NC. apply (proj2 (absorb_io rho R (vms md tp ms)) z). intros [Hz Hin]. apply NC. pose proof (IRZ _ Hin) as X0. rewrite u64_lit in X0 by lia. exact X0. }
  pose proof (SPA_unobj segsA JWn rho C BASE R tp tr ms md HOBJ HS) as HU. cbn zeta in HU. fold rho2 in HU.
  split; [|split; [intros v0; reflexivity | intros l; reflexivity]].
  apply HU. intros HJ. apply (JW_change segsA Zn TZ J rho rho2 tp tr md); [intros i; reflexivity | intros l; reflexivity | exact EQF | intros z _ Hp; exact (PRS z Hp) | | exact HJ].
  intros a0 NT. apply (proj1 (absorb_io rho R (vms md tp ms))). intros Hin. apply NT. apply HZT. exact (IRZ _ Hin).
Qed.
End DissolveZ.
End F0A_hbN_step.

(* [comment removed for export] *)
Module MallocHitTail0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "Kc_ok"; "JL_malloc_ok"; "J_alloc_preT"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CertMallocSPc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.SpineMallocS5i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.SpineMallocS6i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.SpineMallocS7i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.SpineMallocS9i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocS9j OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.DepotCallI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocS5t.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section HIT0T.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S9S8VCST;R1A2S8S20R2A2S1dF_;F_;Fa;").

Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S8VCST;R1A2S1eS21R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S17VAInv;VW;Vst;VA;VKc;S1PcA1A6").

Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x17fbdc 4 0) := AInvA_die.
Let law_inv3 : forall A rho tp md, AInv A rho tp md -> inv3 A := AInvA_inv3.
Let W0 : list ulink := Wcan 0.
Let st0 : ustop := UStopLe.

Definition KEEP (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|0|
S1fVCST;VXGL;VA;Va;A4").

Theorem malloc_hit_tail_0_P : ltac2:(tb__ "0|1|
ScOF_;S1aS14S0S5S1cQ40A1A1S5S7SeS10A2M0A1SfVsegs;SdR3R2R1A5SaS22G0S6SeS10S18S13VW0;Vst0;A3S16VAInv;VCST;VXGL;R6R5A5A4R2A3S15R6A1S4Vsegs;R9S2R7A1A3S11Vsegs;RaS2R8A1A3S0SbVsegs;RcS3Vsegs;S1bVW0;Vst0;RbRaR9A5S12VW0;Vst0;Z2A3R1R8A5R6A4FrhoX;F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Posts Q HPin HKc Hokl Hokpl.
  pose proof (depot_call_HD_0 CST XGL HCST HXGL HCSTD ok A Kc rho Q HKc Hokl Hokpl) as HD.
  assert (Hokf : forall A', ok_frameA segs ok (J W0 st0 A' Kc)).
  { intros A' r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  assert (HUS : stopJ_stable W0 st0) by (apply stopJ_stable_le).
  assert (HW : st0 = UStopLeOrPc -> W0 = []) by (intros E; discriminate E).
  set (nv := bv_unsigned (rw rho 12%positive)).

  apply (spine_s3p_tail 0%nat st0 2 SKY_0 YX_0 YF_0 YP_0 WY1_0 WY2_0 WY3_0 WY4_0 WY5_0 WY6_0 WY7_0 s3_0 ENT3_0 SID3_0 ok A Kc rho tp Q HW HUS HKc).
  intros Hcnt HSEP HPRM0 rhoE3.

  apply (spine_s4 0%nat st0 2 Cert4_0 (KEEP A) ok A Kc rho tp Q HUS HKc (Hokf A) HD).
  intros A' rho' rhoX5 tp' HDO HL.
  assert (Enu : bv_unsigned (rw rho' 12%positive) = nv) by (destruct HL as [HLw _]; rewrite (HLw 12%positive); reflexivity).
  assert (HPRM' : prim_room A') by exact (prim_room_same A A' (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HDO)))))) HPRM0).
  assert (Hcnt' : 1 <= cnt_of A' (bv_unsigned (rw rho' 12%positive))).
  { rewrite Enu. unfold cnt_of, cst_of. rewrite (proj1 (proj2 HDO)). exact Hcnt. }
  pose proof Hokl as HokA'.

  assert (K7 : forall tpY rhoY, triple segs ok (SPA segs (JGb W0 st0 A' Kc rho') (C7 W0 st0 2) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (spine_s7 0%nat st0 2 Cert7_0 OV7a_0 OV7b_0 TAB7a_0 TAB7b_0 W7a_0 W7b_0 D7a_0 D7b_0 NX7a_0 NX7b_0 G7a_0 G7b_0 F7a_0 F7b_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8i.s8a_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8i.s8b_0
             ENT8a_0 ENT8b_0 SID8a_0 SID8b_0 G7p_0 F7p_0 W7p_0 D7p_0 NX7p_0 F7an_0 F7bn_0 ok A' Kc rho' tpY Q HUS HKc HokA' Hcnt').
    - intros Hm0 rhoY8.
      apply (spine_s8_gen 0%nat st0 2 (C8 W0 st0 2) (C9 W0 st0 2) (E8a W0 st0 2) (E8b W0 st0 2) CC8ma_0 Cert8_0 HCC8ma_0 W8a_0 D8a_0 NX8a_0 s8_0 sd8_0 R8_0 T8_0 He8_0 Hchk8_0 HT8_0 FBC8_0 FBT8_0 ENT8_0 SID8_0 NXC8_0 i8_0 S8s_0 SPL8_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.SpineMallocS9i.s8b_0 sd8b_0 R8b_0 T8b_0 He8b_0 Hchk8b_0 HT8b_0 FBC8b_0 FBT8b_0 NXC8b_0 i9_0 SU_0 SM_0 ENTU_0 SIDU_0 MRG_0 s9m_0 ENTM_0 SIDM_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY9 tpY9.
      exact (spine_s9_P 0%nat st0 CST XGL HCST HXGL HCSTM law_die false (C9 W0 st0 2) F9a_nf F9b_nf Cert9a_0 Cert9b_0 NX9_0 FGC_0
               swc_a scells_a hcells_a swc_b scells_b hcells_b s9_a s9_b FH_a_0 FH_b_0 ok A A' Kc rho rho' (KEEP A) tp Posts HPin HW HUS HKc HokA' HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm0 rhoY9 tpY9).
    - intros Hm8 rhoY7.
      apply (spine_s7p 0%nat st0 2 Cert7p_0 OV7c_0 OV7d_0 TAB7c_0 TAB7d_0 W7c_0 W7d_0 D7c_0 D7d_0 NX7c_0 NX7d_0 G7c_0 G7d_0 F7c_0 F7d_0 s8c_0 s8d_0
               ENT8c_0 ENT8d_0 SID8c_0 SID8d_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY8.
      apply (spine_s8_gen 0%nat st0 2 (C8p W0 st0 2) (C9p W0 st0 2) (E8pa W0 st0 2) (E8pb W0 st0 2) CC8map_0 Cert8p_0 HCC8map_0 W8ap_0 D8ap_0 NX8ap_0 s8p_0 sd8p_0 R8p_0 T8p_0 He8p_0 Hchk8p_0 HT8p_0 FBC8p_0 FBT8p_0 ENT8p_0 SID8p_0 NXC8p_0 i8p_0 S8sp_0 SPL8p_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j8.SpineMallocS9i.s8bp_0 sd8bp_0 R8bp_0 T8bp_0 He8bp_0 Hchk8bp_0 HT8bp_0 FBC8bp_0 FBT8bp_0 NXC8bp_0 i9p_0 SUp_0 SMp_0 ENTUp_0 SIDUp_0 MRGp_0 s9mp_0 ENTMp_0 SIDMp_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY9 tpY9.
      exact (spine_s9_P 0%nat st0 CST XGL HCST HXGL HCSTM law_die true (C9p W0 st0 2) F9pa_nf F9pb_nf Cert9pa_0 Cert9pb_0 NX9p_0 FGCp_0
               swc_pa scells_pa hcells_pa swc_pb scells_pb hcells_pb s9_pa s9_pb FH_pa_0 FH_pb_0 ok A A' Kc rho rho' (KEEP A) tp Posts HPin HW HUS HKc HokA' HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm8 rhoY9 tpY9). }

  assert (K6 : forall tpY rhoY, triple segs ok (SPA segs (JGb W0 st0 A' Kc rho') (C6 W0 st0 2) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (spine_s6 0%nat st0 2 Cert6_0 k6_0 NTH6s_0 ZC6s_0 s7s_0 ENT7s_0 SID7s_0 G6l_0 W6l_0 D6l_0 NX6l_0 ok A' Kc rho' tpY Q HUS HKc HokA' Hcnt'); [exact (K7 tpY)|].
    intros rhoY6l.
    apply (spine_s6l 0%nat st0 2 Cert6l_0 W6m_0 D6m_0 NX6m_0 s6_0 sd6_0 R6_0 T6_0 He6_0 Hchk6_0 HT6_0 FBC6_0 FBT6_0 ENT6_0 SID6_0 NXC6_0 ok A' Kc rho' tpY Q HUS HKc HokA').
    intros rhoY6b tpY6b.
    apply (spine_s6b 0%nat st0 2 Cert6b_0 s7j_0 ENT7j_0 SID7j_0 ok A' Kc rho' tpY6b Q HUS HKc HokA'). exact (K7 tpY6b). }

  apply (spine_s5 0%nat st0 2 Cert5_0 s6n_0 ENT6n_0 SID6n_0 W5b_0 D5b_0 NX5b_0 F5f64_0 ok A' Kc rho' tp' Q HUS HKc HokA' Hcnt'); [exact (K6 tp')|].
  intros rhoX5b.
  apply (spine_s5b 0%nat st0 2 Cert5b_0 OV1_0 OV2_0 TAB1_0 TAB2_0 W1'_0 W2'_0 D1'_0 D2'_0 NX1'_0 NX2'_0 F1gt_0 F2le_0 F1_64_0 F2_64_0 s1_0 s2_0 ENT1_0 ENT2_0 SID1_0 SID2_0
           ok A' Kc rho' tp' Q HUS HKc HokA').
  intros rhoX5c.
  apply (spine_s5c 0%nat st0 2 Cert5c_0 G5m1_0 W5m1_0 D5m1_0 NX5m1_0 s51_0 sd51_0 R51_0 T51_0 He51_0 Hchk51_0 HT51_0 FBC51_0 FBT51_0 ENT51_0 SID51_0 NXC51_0
           ok A' Kc rho' tp' Q HUS HKc HokA' Hcnt').
  intros rhoX5d tp5d.
  apply (spine_s5d 0%nat st0 2 Cert5d_0 G5m2_0 W5m2_0 D5m2_0 NX5m2_0 s52_0 sd52_0 R52_0 T52_0 He52_0 Hchk52_0 HT52_0 FBC52_0 FBT52_0 ENT52_0 SID52_0 NXC52_0
           ok A' Kc rho' tp5d Q HUS HKc HokA' Hcnt').
  intros rhoX5e tp5e.
  apply (spine_s5e 0%nat st0 2 Cert5e_0 s6j_0 ENT6j_0 SID6j_0 ok A' Kc rho' tp5e Q HUS HKc HokA'). exact (K6 tp5e).
Qed.

Theorem malloc_hit_tail_0 : ltac2:(tb__ "0|0|
ScOF_;S1aS14S0S5S1cQ40A1A1SfVsegs;SdR2R1S19S13VAInv;VCST;VXGL;VW0;Vst0;R4R3A8A5SaS15R4A1S4Vsegs;R7S2R5A1A3S11Vsegs;R8S2R6A1A3S0SbVsegs;RaS3Vsegs;S1bVW0;Vst0;R9R8R7A5S12VW0;Vst0;Z2A3R1R6A5R5A4FrhoX;F_;F_;F_;TQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp. exact (malloc_hit_tail_0_P ok A Kc rho tp (Posts_malloc AE_A AInv CST XGL W0 st0 A Kc) (or_intror (or_introl eq_refl))).
Qed.
End HIT0T.
End MallocHitTail0.

