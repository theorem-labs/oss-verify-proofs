(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From stdpp Require list.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MmapA.

(* [comment removed for export] *)
Module SegQIP.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "list"; "nil"; "false"; "pair"; "prod"; "Some"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "jpredA"; "stableA_mono"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "agree_below"; "ss_next"; "ss_lenient"; "ss_facts"; "rw"; "sprop"; "SLit"; "SPBranch"; "sprop_below"; "sprop_eqb"; "SPNot"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "sdiff"; "one_at"; "JQ"; "entsI"; "two_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states"; "PreQIP"; "PostQIP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states"; "NXI"; "dI0"; "dI1a"; "dI1b"; "dI2"; "dI3"; "dI4"; "dI5"; "dI6"; "MSENTQ"; "PSENT"; "QCENTI"; "QI0"; "QI1"; "QI2"; "QI3"; "vCLS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_CLS"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side"; "QI_side"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SegQIP"; "le_NPRE_240"; "le_NPRE_242"; "le_NPRE_NXI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Lemma le_NPRE_NXI : (NPRE <= NXI)%positive. Proof. unfold NPRE, NXI, Pos.le. cbn. discriminate. Qed.
Lemma le_NPRE_240 : (NPRE <= 240)%positive. Proof. unfold NPRE, Pos.le. cbn. discriminate. Qed.
Lemma le_NPRE_242 : (NPRE <= 242)%positive. Proof. unfold NPRE, Pos.le. cbn. discriminate. Qed.

Section QI.

Variable vb : bool.
Variables (run0 run1 run2 run3 run4 run5 run6 : list leafA).
Variables (E0 C0 E1a E1b E1a' E1b' C1 E2 C2 E3 C3 E4 C4 E5 C5 T5 T5f E6 C6 : axst) (s5 : wsub) (R5 : list sobj).
Hypothesis run0_eq : ltac2:(tb__ "0|0|
S1S6S19A1S10U12cS4SdS44S4SdZ3e63cS7SdA1A3A3S36Vvb;A1A3Vrun0;A3").
Hypothesis chk0 : ltac2:(tb__ "0|0|
S1S3S32Vrun0;S44A2S5A3").
Hypothesis E0_def : leaf 0 run0 = E0.
Hypothesis sd0 : ltac2:(tb__ "0|0|
S1S3S31VE0;VC0;S39A3S5A3").
Hypothesis C0_def : ltac2:(tb__ "0|0|
S1S17S18VE0;S16VC0;A1A2VC0;A3").
Hypothesis nxC0 : ltac2:(tb__ "0|1|
S2S1SeS1dS16VC0;A1M0A1SfA3S1S3S1eG0A1S8A3A2").
Hypothesis run1_eq : ltac2:(tb__ "0|0|
S1S6S19A1S10U12cS4SdS45S4SdZ3e63cS4SdZ3e810S4SdZ3e804S7SdA1A3A3A3A3VC0;A3Vrun1;A3").
Hypothesis chk1 : ltac2:(tb__ "0|0|
S1S3S35Vrun1;S45A2S5A3").
Hypothesis E1a_def : leaf 0 run1 = E1a.
Hypothesis E1b_def : leaf 1 run1 = E1b.
Hypothesis sd1a : ltac2:(tb__ "0|0|
S1S3S31VE1a;VE1a';S3aA3S5A3").
Hypothesis sd1b : ltac2:(tb__ "0|0|
S1S3S31VE1b;VE1b';S3bA3S5A3").
Hypothesis E1a'_def : ltac2:(tb__ "0|0|
S1S17S18VE1a;S16VE1a';A1A2VE1a';A3").
Hypothesis E1b'_def : ltac2:(tb__ "0|0|
S1S17S18VE1b;S16VE1b';A1A2VE1b';A3").
Hypothesis ent1a : ltac2:(tb__ "0|0|
S1S3S34VE1a';VC1;A2S5A3").
Hypothesis ent1b : ltac2:(tb__ "0|0|
S1S3S34VE1b';VC1;A2S5A3").
Hypothesis br1a : ltac2:(tb__ "0|0|
S1S3S51S21S25S23S4fS48S22Z11A1A3A1S1fS16VE1a;A1A1A3S5A3").
Hypothesis br1b : ltac2:(tb__ "0|0|
S1S3S51S21S25S26S23S4fS48S22Z11A1A3A1A1S1fS16VE1b;A1A1A3S5A3").
Hypothesis nxC1 : ltac2:(tb__ "0|1|
S2S1SeS1dS16VC1;A1M0A1S38A3S1S3S1eG0A1S8A3A2").
Hypothesis run2_eq : ltac2:(tb__ "0|0|
S1S6S19A1S10U12cS4SdS46S7SdA1A3VC1;A3Vrun2;A3").
Hypothesis chk2 : ltac2:(tb__ "0|0|
S1S3S32Vrun2;S46A2S5A3").
Hypothesis E2_def : leaf 0 run2 = E2.
Hypothesis sd2 : ltac2:(tb__ "0|0|
S1S3S31VE2;VC2;S3cVvb;A1A3S5A3").
Hypothesis C2_def : ltac2:(tb__ "0|0|
S1S17S18VE2;S16VC2;A1A2VC2;A3").
Hypothesis nxC2 : ltac2:(tb__ "0|1|
S2S1SeS1dS16VC2;A1M0A1S38A3S1S3S1eG0A1S8A3A2").
Hypothesis run3_eq : ltac2:(tb__ "0|0|
S1S6S19A1S10U258S4SdS47S4SdZ3e818S4SdZ3e83cS4SdZ3e73cS7SdA1A3A3A3A3VC2;A3Vrun3;A3").
Hypothesis chk3 : ltac2:(tb__ "0|0|
S1S3S32Vrun3;S47A2S5A3").
Hypothesis E3_def : leaf 0 run3 = E3.
Hypothesis sd3 : ltac2:(tb__ "0|0|
S1S3S31VE3;VC3;S3dA3S5A3").
Hypothesis C3_def : ltac2:(tb__ "0|0|
S1S17S18VE3;S16VC3;A1A2VC3;A3").
Hypothesis nxC3 : ltac2:(tb__ "0|1|
S2S1SeS1dS16VC3;A1M0A1S38A3S1S3S1eG0A1S8A3A2").
Hypothesis run4_eq : ltac2:(tb__ "0|0|
S1S6S19A1S10U320S4SdS42S4SdZ3e818S7SdA1A3A3VC3;A3Vrun4;A3").
Hypothesis chk4 : ltac2:(tb__ "0|0|
S1S3S32Vrun4;S42A2S5A3").
Hypothesis E4_def : leaf 0 run4 = E4.
Hypothesis sd4 : ltac2:(tb__ "0|0|
S1S3S31VE4;VC4;S3eA3S5A3").
Hypothesis C4_def : ltac2:(tb__ "0|0|
S1S17S18VE4;S16VC4;A1A2VC4;A3").
Hypothesis nxC4 : ltac2:(tb__ "0|1|
S2S1SeS1dS16VC4;A1M0A1S38A3S1S3S1eG0A1S8A3A2").
Hypothesis run5_eq : ltac2:(tb__ "0|0|
S1S6S19A1S10U320S4SdS41S4SdZ3e73cS4SdZ5fa44S4SdZ5fa24S4SdZ5fa64S4SdZ5fa84S4SdZ5fa04S7SdA1A3A3A3A3A3A3A3VC4;A3Vrun5;A3").
Hypothesis chk5 : ltac2:(tb__ "0|0|
S1S3S32Vrun5;S41A2S5A3").
Hypothesis E5_def : leaf 0 run5 = E5.
Hypothesis sd5 : ltac2:(tb__ "0|0|
S1S3S31VE5;VC5;S3fA3S5A3").
Hypothesis C5_def : ltac2:(tb__ "0|0|
S1S17S18VE5;S16VC5;A1A2VC5;A3").
Hypothesis nxC5 : ltac2:(tb__ "0|1|
S2S1SeS1dS16VC5;A1M0A1S38A3S1S3S1eG0A1S8A3A2").
Hypothesis He5 : ltac2:(tb__ "0|1|
S1ScS6S27A1M0A1S2fVC5;S4cVs5;A3SbG0VR5;A2A3").
Hypothesis Hchk5 : ltac2:(tb__ "0|0|
S1S3S2eVC5;S4cVs5;VR5;S55S19S17S1aS4dA4A5S5A3").
Hypothesis HT5 : ltac2:(tb__ "0|0|
S1S17S30Vs5;S4cS56S58S4eA1A1VC5;VR5;A5VT5;A3").
Hypothesis FBC5 : ltac2:(tb__ "0|1|
S1S3S52S21S24S1dS16VC5;A1M0A1A1S1fG0A1A3S5A3").
Hypothesis FBT5 : ltac2:(tb__ "0|0|
S1S3S52S21S24S1dS16VT5;A1A1A1S1fS16VC5;A1A1A3S5A3").
Hypothesis T5f_def : ltac2:(tb__ "0|0|
S1S17S57VT5;S1fS16VC5;A1A1A2VT5f;A3").
Hypothesis nxT5f : ltac2:(tb__ "0|1|
S2S1SeS1dS16VT5f;A1M0A1Pf0A3S1S3S1eG0A1S8A3A2").
Hypothesis run6_eq : ltac2:(tb__ "0|0|
S1S6S19A1S10U320S4SdS43S4SdZ3e7b8S4SdZ3e7d8S7SdA1A3A3A3VT5f;A3Vrun6;A3").
Hypothesis chk6 : ltac2:(tb__ "0|0|
S1S3S32Vrun6;S43A2S5A3").
Hypothesis E6_def : leaf 0 run6 = E6.
Hypothesis sd6 : ltac2:(tb__ "0|0|
S1S3S31VE6;VC6;S40Vvb;A1A3S5A3").
Hypothesis C6_def : ltac2:(tb__ "0|0|
S1S17S18VE6;S16VC6;A1A2VC6;A3").
Hypothesis nxC6 : ltac2:(tb__ "0|1|
S2S1SeS1dS16VC6;A1M0A1Pf2A3S1S3S1eG0A1S8A3A2").
Hypothesis ent6 : ltac2:(tb__ "0|0|
S1S3S34VC6;S37Vvb;A1A2S5A3").

Variables (J : jpredA) (ok : world -> Prop) (rho : valuation) (tp : list word).
Hypothesis HOK : ok_frameA segsA ok J.
Hypothesis HST : ltac2:(tb__ "0|0|
S12S0SfVJ;A3").
Hypotheses (HD0 : diffs_ok rho dI0)
           (HD1a : 17 <= bv_unsigned (rw rho V_CLS) -> diffs_ok rho dI1a) (HD1b : bv_unsigned (rw rho V_CLS) < 17 -> diffs_ok rho dI1b)
           (HD2 : diffs_ok rho (dI2 vb))
           (HD3 : diffs_ok rho dI3) (HD4 : diffs_ok rho dI4) (HD5 : diffs_ok rho dI5) (HD6 : diffs_ok rho (dI6 vb)).
Let Q : assn := ltac2:(tb__ "0|1|
S2dS0SfVrho;Vtp;S4SaS17S2cA2M0S9S17S2cS37Vvb;A1S33VJ;A1A4S7G0A1A3A5").
Let ST200 : stableA segsA NXI J := ltac2:(tb__ "0|0|
S14S0SfS38VJ;S5bVHST;A6").
Let ST240 : stableA segsA 240 J := ltac2:(tb__ "0|0|
S14S0SfPf0VJ;S59VHST;A6").
Let ST242 : stableA segsA 242 J := ltac2:(tb__ "0|0|
S14S0SfPf2VJ;S5aVHST;A6").
Let DB := dI_below vb.

Lemma from_C6 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS0Vok;S11S0VJ;VC6;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof. intros rhoC Hag. exact (leaf_post J ok C6 (PostQIP vb) rho rhoC tp [(PostQIP vb, JQ J)] ent6 HST (or_introl eq_refl) Hag). Qed.

Lemma from_T5f : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS0Vok;S11S0VJ;VT5f;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 800%nat [QCENTI; 0x3e7b8; 0x3e7d8] T5f run6 240 E6 (proj2 nxT5f) (proj1 nxT5f) run6_eq E6_def QCENTI J ok rhoC tp Q chk6 HOK ST240).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_240 HagL)) as HagR.
  apply (restate_cont J ok E6 C6 (dI6 vb) rhoL tp Q sd6); [| exact C6_def | apply from_C6; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL (dI6 vb) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DB))))))) HagR HD6).
Qed.

Lemma from_C5 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS0Vok;S11S0VJ;VC5;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag.
  apply (call_cont C5 Pre_memsetA Posts_memsetA s5 R5 T5 NPRE
           (fun ok0 Jx r t Ho Hs => memset_sumA ok0 Jx r t Ho Hs) He5 Hchk5 ltac:(intros P [<-|[]]; exact HT5) FBC5 FBT5 ltac:(rewrite (proj1 nxC5); exact le_NPRE_NXI)
           J ok rhoC tp Q HOK HST).
  intros rho' Hag'. rewrite T5f_def. apply from_T5f. eapply agree_below_trans; [exact Hag | eapply agree_below_le; [| exact Hag']]. rewrite (proj1 nxC5). exact le_NPRE_NXI.
Qed.

Lemma from_C4 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS0Vok;S11S0VJ;VC4;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 800%nat [MSENTQ; 0x3e73c; 0x5fa44; 0x5fa24; 0x5fa64; 0x5fa84; 0x5fa04] C4 run5 NXI E5 (proj2 nxC4) (proj1 nxC4) run5_eq E5_def MSENTQ J ok rhoC tp Q chk5 HOK ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_cont J ok E5 C5 dI5 rhoL tp Q sd5); [| exact C5_def | apply from_C5; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI5 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DB))))))) HagR HD5).
Qed.

Lemma from_C3 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS0Vok;S11S0VJ;VC3;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 800%nat [PSENT; 0x3e818] C3 run4 NXI E4 (proj2 nxC3) (proj1 nxC3) run4_eq E4_def PSENT J ok rhoC tp Q chk4 HOK ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_cont J ok E4 C4 dI4 rhoL tp Q sd4); [| exact C4_def | apply from_C4; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI4 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 DB)))))) HagR HD4).
Qed.

Lemma from_C2 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS0Vok;S11S0VJ;VC2;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 600%nat [QI3; 0x3e818; 0x3e83c; 0x3e73c] C2 run3 NXI E3 (proj2 nxC2) (proj1 nxC2) run3_eq E3_def QI3 J ok rhoC tp Q chk3 HOK ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_cont J ok E3 C3 dI3 rhoL tp Q sd3); [| exact C3_def | apply from_C3; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI3 (proj1 (proj2 (proj2 (proj2 (proj2 DB))))) HagR HD3).
Qed.

Lemma from_C1 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS0Vok;S11S0VJ;VC1;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 300%nat [QI2] C1 run2 NXI E2 (proj2 nxC1) (proj1 nxC1) run2_eq E2_def QI2 J ok rhoC tp Q chk2 HOK ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_cont J ok E2 C2 (dI2 vb) rhoL tp Q sd2); [| exact C2_def | apply from_C2; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL (dI2 vb) (proj1 (proj2 (proj2 (proj2 DB)))) HagR HD2).
Qed.

Lemma from_C0 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS0Vok;S11S0VJ;VC0;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont2 300%nat [QI1; 0x3e63c; 0x3e810; 0x3e804] C0 run1 NPRE E1a E1b (proj2 nxC0) (proj1 nxC0) run1_eq E1a_def E1b_def QI1 J ok rhoC tp Q chk1 HOK HST).
  - intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag HagL) as HagR.
    apply (restate_contF J ok E1a E1a' dI1a rhoL tp Q sd1a); [| exact E1a'_def |].
    + intros HF. apply (diffs_ok_agree NPRE rho rhoL dI1a (proj1 (proj2 DB)) HagR). apply HD1a.
      rewrite (proj1 HagR V_CLS ltac:(unfold V_CLS, NPRE; lia)). exact (fact_geu_lit rhoL V_CLS 17 _ ltac:(lia) br1a HF).
    + apply (ent_cont J ok E1a' C1 rhoL tp Q ent1a HST). intros rho' Hag'. apply from_C1. eapply agree_below_trans; [exact HagR | exact Hag'].
  - intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag HagL) as HagR.
    apply (restate_contF J ok E1b E1b' dI1b rhoL tp Q sd1b); [| exact E1b'_def |].
    + intros HF. apply (diffs_ok_agree NPRE rho rhoL dI1b (proj1 (proj2 (proj2 DB))) HagR). apply HD1b.
      rewrite (proj1 HagR V_CLS ltac:(unfold V_CLS, NPRE; lia)). exact (fact_ltu_lit rhoL V_CLS 17 _ ltac:(lia) br1b HF).
    + apply (ent_cont J ok E1b' C1 rhoL tp Q ent1b HST). intros rho' Hag'. apply from_C1. eapply agree_below_trans; [exact HagR | exact Hag'].
Qed.

Theorem seg_QIP_sound_sec : ltac2:(tb__ "0|0|
S2aS0Vok;S11S0VJ;S36Vvb;A1Vrho;Vtp;A5VQ;A4").
Proof.
  apply (run_cont1 300%nat [QI0; 0x3e63c] (PreQIP vb) run0 NPRE E0 (proj2 (proj2 (proj2 (preQIP_wf vb)))) (proj1 (proj2 (proj2 (preQIP_wf vb)))) run0_eq E0_def QI0 J ok rho tp Q chk0 HOK HST).
  intros rhoL HagL.
  apply (restate_cont J ok E0 C0 dI0 rhoL tp Q sd0); [| exact C0_def | apply from_C0; exact HagL].
  exact (diffs_ok_agree NPRE rho rhoL dI0 (proj1 DB) HagL HD0).
Qed.

Lemma efrom_C6 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S0S11S0VJ;VC6;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof. intros rhoC Hag. exact (leaf_epost J C6 (PostQIP vb) rho rhoC tp [(PostQIP vb, JQ J)] ent6 HST (or_introl eq_refl) Hag). Qed.

Lemma efrom_T5f : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S0S11S0VJ;VT5f;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 800%nat [QCENTI; 0x3e7b8; 0x3e7d8] T5f run6 240 E6 (proj2 nxT5f) (proj1 nxT5f) run6_eq E6_def QCENTI J rhoC tp Q chk6 ST240).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_240 HagL)) as HagR.
  apply (restate_econt J E6 C6 (dI6 vb) rhoL tp Q sd6); [| exact C6_def | apply efrom_C6; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL (dI6 vb) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DB))))))) HagR HD6).
Qed.

Lemma efrom_C5 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S0S11S0VJ;VC5;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag.
  apply (call_econt C5 Pre_memsetA Posts_memsetA s5 R5 T5 NPRE
           (fun Jx r t Hs => memset_sumA_ex Jx r t Hs) He5 Hchk5 ltac:(intros P [<-|[]]; exact HT5) FBC5 FBT5 ltac:(rewrite (proj1 nxC5); exact le_NPRE_NXI)
           J rhoC tp Q HST).
  intros rho' Hag'. rewrite T5f_def. apply efrom_T5f. eapply agree_below_trans; [exact Hag | eapply agree_below_le; [| exact Hag']]. rewrite (proj1 nxC5). exact le_NPRE_NXI.
Qed.

Lemma efrom_C4 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S0S11S0VJ;VC4;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 800%nat [MSENTQ; 0x3e73c; 0x5fa44; 0x5fa24; 0x5fa64; 0x5fa84; 0x5fa04] C4 run5 NXI E5 (proj2 nxC4) (proj1 nxC4) run5_eq E5_def MSENTQ J rhoC tp Q chk5 ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_econt J E5 C5 dI5 rhoL tp Q sd5); [| exact C5_def | apply efrom_C5; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI5 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DB))))))) HagR HD5).
Qed.

Lemma efrom_C3 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S0S11S0VJ;VC3;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 800%nat [PSENT; 0x3e818] C3 run4 NXI E4 (proj2 nxC3) (proj1 nxC3) run4_eq E4_def PSENT J rhoC tp Q chk4 ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_econt J E4 C4 dI4 rhoL tp Q sd4); [| exact C4_def | apply efrom_C4; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI4 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 DB)))))) HagR HD4).
Qed.

Lemma efrom_C2 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S0S11S0VJ;VC2;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 600%nat [QI3; 0x3e818; 0x3e83c; 0x3e73c] C2 run3 NXI E3 (proj2 nxC2) (proj1 nxC2) run3_eq E3_def QI3 J rhoC tp Q chk3 ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_econt J E3 C3 dI3 rhoL tp Q sd3); [| exact C3_def | apply efrom_C3; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI3 (proj1 (proj2 (proj2 (proj2 (proj2 DB))))) HagR HD3).
Qed.

Lemma efrom_C1 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S0S11S0VJ;VC1;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 300%nat [QI2] C1 run2 NXI E2 (proj2 nxC1) (proj1 nxC1) run2_eq E2_def QI2 J rhoC tp Q chk2 ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_econt J E2 C2 (dI2 vb) rhoL tp Q sd2); [| exact C2_def | apply efrom_C2; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL (dI2 vb) (proj1 (proj2 (proj2 (proj2 DB)))) HagR HD2).
Qed.

Lemma efrom_C0 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S0S11S0VJ;VC0;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt2 300%nat [QI1; 0x3e63c; 0x3e810; 0x3e804] C0 run1 NPRE E1a E1b (proj2 nxC0) (proj1 nxC0) run1_eq E1a_def E1b_def QI1 J rhoC tp Q chk1 HST).
  - intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag HagL) as HagR.
    apply (restate_econtF J E1a E1a' dI1a rhoL tp Q sd1a); [| exact E1a'_def |].
    + intros HF. apply (diffs_ok_agree NPRE rho rhoL dI1a (proj1 (proj2 DB)) HagR). apply HD1a.
      rewrite (proj1 HagR V_CLS ltac:(unfold V_CLS, NPRE; lia)). exact (fact_geu_lit rhoL V_CLS 17 _ ltac:(lia) br1a HF).
    + apply (ent_econt J E1a' C1 rhoL tp Q ent1a HST). intros rho' Hag'. apply efrom_C1. eapply agree_below_trans; [exact HagR | exact Hag'].
  - intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag HagL) as HagR.
    apply (restate_econtF J E1b E1b' dI1b rhoL tp Q sd1b); [| exact E1b'_def |].
    + intros HF. apply (diffs_ok_agree NPRE rho rhoL dI1b (proj1 (proj2 (proj2 DB))) HagR). apply HD1b.
      rewrite (proj1 HagR V_CLS ltac:(unfold V_CLS, NPRE; lia)). exact (fact_ltu_lit rhoL V_CLS 17 _ ltac:(lia) br1b HF).
    + apply (ent_econt J E1b' C1 rhoL tp Q ent1b HST). intros rho' Hag'. apply efrom_C1. eapply agree_below_trans; [exact HagR | exact Hag'].
Qed.

Theorem seg_QIP_complete_sec : ltac2:(tb__ "0|0|
S29S0S11S0VJ;S36Vvb;A1Vrho;Vtp;A5VQ;A3").
Proof.
  apply (run_econt1 300%nat [QI0; 0x3e63c] (PreQIP vb) run0 NPRE E0 (proj2 (proj2 (proj2 (preQIP_wf vb)))) (proj1 (proj2 (proj2 (preQIP_wf vb)))) run0_eq E0_def QI0 J rho tp Q chk0 HST).
  intros rhoL HagL.
  apply (restate_econt J E0 C0 dI0 rhoL tp Q sd0); [| exact C0_def | apply efrom_C0; exact HagL].
  exact (diffs_ok_agree NPRE rho rhoL dI0 (proj1 DB) HagL HD0).
Qed.
End QI.

Theorem seg_QIP_sound : ltac2:(tb__ "0|3|
S3S13S2bOF_;S1bS6S4aQ40M0A1A1S15S0R3R4A3S12S0SfR5A3S28R4S39A2S53Z11M1S4bG0S20R5S49A2A2A2S28R6S3aA2F_;S54S4bG0S20R6S49A2A2G1A2S28R7S3bA2F_;S28R7S3cRaA1A2S28R8S3dA2S28R9S3eA2S28RaS3fA2S28RbS40ReA1A2S2aS0RdS11S0ReS36RfA1RcRbA5S2dS0SfRcRbS4SaS17S2cA2M2S9S17S2cS37RfA1S33ReA1A4S7G2A1A3A5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;Fok;FJ;Fvb;").
Proof.
  intros [|]; intros.
  - eapply (seg_QIP_sound_sec true prun0b prun1b prun2b prun3b prun4b prun5b prun6b pE0b pC0b pE1ab pE1bb pE1ab' pE1bb' pC1b pE2b pC2b pE3b pC3b pE4b pC4b pE5b pC5b pT5b pT5fb pE6b pC6b ps5b pR5b
            prun0b_eq pchk0b pE0b_def psd0b eq_refl pnxC0b prun1b_eq pchk1b pE1ab_def pE1bb_def psd1ab psd1bb eq_refl eq_refl pent1ab pent1bb pbr1ab pbr1bb pnxC1b prun2b_eq pchk2b pE2b_def psd2b eq_refl pnxC2b
            prun3b_eq pchk3b pE3b_def psd3b eq_refl pnxC3b prun4b_eq pchk4b pE4b_def psd4b eq_refl pnxC4b prun5b_eq pchk5b pE5b_def psd5b eq_refl pnxC5b
            pHe5b pHchk5b pHT5b pFBC5b pFBT5b eq_refl pnxT5fb prun6b_eq pchk6b pE6b_def psd6b eq_refl pnxC6b pent6b); eassumption.
  - eapply (seg_QIP_sound_sec false prun0a prun1a prun2a prun3a prun4a prun5a prun6a pE0a pC0a pE1aa pE1ba pE1aa' pE1ba' pC1a pE2a pC2a pE3a pC3a pE4a pC4a pE5a pC5a pT5a pT5fa pE6a pC6a ps5a pR5a
            prun0a_eq pchk0a pE0a_def psd0a eq_refl pnxC0a prun1a_eq pchk1a pE1aa_def pE1ba_def psd1aa psd1ba eq_refl eq_refl pent1aa pent1ba pbr1aa pbr1ba pnxC1a prun2a_eq pchk2a pE2a_def psd2a eq_refl pnxC2a
            prun3a_eq pchk3a pE3a_def psd3a eq_refl pnxC3a prun4a_eq pchk4a pE4a_def psd4a eq_refl pnxC4a prun5a_eq pchk5a pE5a_def psd5a eq_refl pnxC5a
            pHe5a pHchk5a pHT5a pFBC5a pFBT5a eq_refl pnxT5fa prun6a_eq pchk6a pE6a_def psd6a eq_refl pnxC6a pent6a); eassumption.
Qed.
Theorem seg_QIP_complete : ltac2:(tb__ "0|3|
S3S13S1bS6S4aQ40M0A1A1S12S0SfR3A3S28R3S39A2S53Z11M1S4bG0S20R4S49A2A2A2S28R5S3aA2F_;S54S4bG0S20R5S49A2A2G1A2S28R6S3bA2F_;S28R6S3cR8A1A2S28R7S3dA2S28R8S3eA2S28R9S3fA2S28RaS40RcA1A2S29S0S11S0RcS36RdA1RbRaA5S2dS0SfRbRaS4SaS17S2cA2M2S9S17S2cS37RdA1S33RcA1A4S7G2A1A3A5A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;FJ;Fvb;").
Proof.
  intros [|]; intros.
  - eapply (seg_QIP_complete_sec true prun0b prun1b prun2b prun3b prun4b prun5b prun6b pE0b pC0b pE1ab pE1bb pE1ab' pE1bb' pC1b pE2b pC2b pE3b pC3b pE4b pC4b pE5b pC5b pT5b pT5fb pE6b pC6b ps5b pR5b
            prun0b_eq pchk0b pE0b_def psd0b eq_refl pnxC0b prun1b_eq pchk1b pE1ab_def pE1bb_def psd1ab psd1bb eq_refl eq_refl pent1ab pent1bb pbr1ab pbr1bb pnxC1b prun2b_eq pchk2b pE2b_def psd2b eq_refl pnxC2b
            prun3b_eq pchk3b pE3b_def psd3b eq_refl pnxC3b prun4b_eq pchk4b pE4b_def psd4b eq_refl pnxC4b prun5b_eq pchk5b pE5b_def psd5b eq_refl pnxC5b
            pHe5b pHchk5b pHT5b pFBC5b pFBT5b eq_refl pnxT5fb prun6b_eq pchk6b pE6b_def psd6b eq_refl pnxC6b pent6b); eassumption.
  - eapply (seg_QIP_complete_sec false prun0a prun1a prun2a prun3a prun4a prun5a prun6a pE0a pC0a pE1aa pE1ba pE1aa' pE1ba' pC1a pE2a pC2a pE3a pC3a pE4a pC4a pE5a pC5a pT5a pT5fa pE6a pC6a ps5a pR5a
            prun0a_eq pchk0a pE0a_def psd0a eq_refl pnxC0a prun1a_eq pchk1a pE1aa_def pE1ba_def psd1aa psd1ba eq_refl eq_refl pent1aa pent1ba pbr1aa pbr1ba pnxC1a prun2a_eq pchk2a pE2a_def psd2a eq_refl pnxC2a
            prun3a_eq pchk3a pE3a_def psd3a eq_refl pnxC3a prun4a_eq pchk4a pE4a_def psd4a eq_refl pnxC4a prun5a_eq pchk5a pE5a_def psd5a eq_refl pnxC5a
            pHe5a pHchk5a pHT5a pFBC5a pFBT5a eq_refl pnxT5fa prun6a_eq pchk6a pE6a_def psd6a eq_refl pnxC6a pent6a); eassumption.
Qed.

Theorem seg_QIP_sound_clean : ltac2:(tb__ "0|1|
S3S13S2bOF_;S1bS6S4aQ40A1A1SdSdS15S0R5R6A3S12S0SfR7A3S50R6R9R4R3A4S2aS0R8S11S0R9S36RaA1R7R6A5S2dS0SfR7R6S4SaS17S2cA2M0S9S17S2cS37RaA1S33R9A1A4S7G0A1A3A5A4F_;F_;F_;Fd;Fx;Ftp;Frho;Fok;FJ;Fvb;").
Proof.
  intros vb J ok rho tp x d HOK HST (Hc & Hsz & Hx & Hd & Hm & Hmu & Hmu2 & Hsb & Hceil & Hm16 & Hhw & Hnlo & Hn8 & Hbg).
  apply (seg_QIP_sound vb J ok rho tp HOK HST).
  - apply (side0 rho x d); assumption.
  - intros H17. apply (side1a rho x d); assumption.
  - intros H17. apply (side1b rho x d); assumption.
  - apply (side2 rho x d); assumption.
  - apply (side3 rho x d); assumption.
  - apply (side4 rho x d); assumption.
  - apply (side5 rho x d); assumption.
  - apply (side6 rho x d); assumption.
Qed.
Theorem seg_QIP_complete_clean : ltac2:(tb__ "0|1|
S3S13S1bS6S4aQ40A1A1SdSdS12S0SfR5A3S50R5R7R3R2A4S29S0S11S0R7S36R8A1R6R5A5S2dS0SfR6R5S4SaS17S2cA2M0S9S17S2cS37R8A1S33R7A1A4S7G0A1A3A5A3F_;F_;Fd;Fx;Ftp;Frho;FJ;Fvb;").
Proof.
  intros vb J rho tp x d HST (Hc & Hsz & Hx & Hd & Hm & Hmu & Hmu2 & Hsb & Hceil & Hm16 & Hhw & Hnlo & Hn8 & Hbg).
  apply (seg_QIP_complete vb J rho tp HST).
  - apply (side0 rho x d); assumption.
  - intros H17. apply (side1a rho x d); assumption.
  - intros H17. apply (side1b rho x d); assumption.
  - apply (side2 rho x d); assumption.
  - apply (side3 rho x d); assumption.
  - apply (side4 rho x d); assumption.
  - apply (side5 rho x d); assumption.
  - apply (side6 rho x d); assumption.
Qed.
End SegQIP.

(* [comment removed for export] *)
Module F0A_laws.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "sub"; "modulo"; "lt"; "mul"; "div"; "leb"; "eqb"; "shiftr"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Datatypes"; "app"; "list"; "pair"; "prod"; "bool"; "true"; "andb"; "Some"; "false"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_live"; "qbatch"; "aa_geom"; "ag_spacebeg"; "aa_cls"; "ageom"; "class_state"; "cs_empty"; "sec_chunk"; "aa_q_global"; "aa_q_thread"; "cs_cache"; "qb_addr"; "aa_sec"; "cs_allocated_user"; "sc_map_beg"; "sc_map_size"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "cls_fits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "rz"; "ClassID"; "Size"; "is_primary"; "region_beg"; "needed"; "kQuarantineBatchSize"; "kMaxSize"; "kSpaceSize"; "round_up"; "@stdpp.base"; "NoDup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "nthZ"; "live_ids"; "fs_footb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "maskv"; "view"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model RtCells SegQ_defs Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N8 (n : Z) : Z := ltac2:(tb__ "0|1|
S6S7S2Vn;Z7A2Z8M0A2G0A2").
Lemma N8_facts : ltac2:(tb__ "0|2|
S0S1Z1R1A2SbSbS1R2S32R2A1M0A2S5G0S2R2Z8M1A2A2A2SbScS0S4G0G1A2Z0A3SbS1G1G0A2ScS0S6S7G0G1A2G1A2G0A3A2A2A2F_;Fn;").
Proof.
  intros n Hn. unfold N8. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
  assert (1 <= (n + 7) / 8) by (apply Z.div_le_lower_bound; lia).
  split; [lia|]. split; [apply Z.mod_mul; lia|]. split; [lia|]. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma N8_below_aligned : ltac2:(tb__ "0|1|
S0S0S0ScS0S4R3Z8A2Z0A3M0S1Z1R3A2G0S1S2R6R5A2R4A2S1S2R7S32R6A1A2R5A2F_;F_;F_;F_;Fx;Fn;Fb;").
Proof.
  intros b n x Hb Hn Hx H. unfold N8. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod x 8 ltac:(lia)) as D2. pose proof (Z.div_mod b 8 ltac:(lia)) as D3.
  set (k := (n + 7) / 8) in *. set (u := x / 8) in *. set (v := b / 8) in *.
  assert (b + n <= 8 * u) by lia. assert (8 * k <= n + 7) by lia.
  destruct (Z_le_dec (b + k * 8) x); [lia|]. exfalso.
  assert (u < v + k) by lia. assert (8 * u <= 8 * (v + k) - 8) by lia. lia.
Qed.

Definition cls_fits (s : Z) : bool := ltac2:(tb__ "0|1|
S17S17S8Vs;S36S35Vs;A1M0A1A2S8Z1G0A2A2S8G0Z1eA2A2").
Lemma cls_fits_all : ltac2:(tb__ "0|0|
S0SbS1Z1R1A2S1R1S3bA2A2ScS15S33R2A1S16A3F_;Fs;").
Proof. intros s Hs. apply (forall_rangeZ_ok cls_fits 1 kMaxSize); [|lia]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma needed_fits : ltac2:(tb__ "0|3|
S0S1Z1M0R1A2ScS15S37R2A1S16A3SbS1S39R3A1M1S36S35G1A1M2A1A2SbSbS1G0G2A2S1G2Z1eA2A2S1S2S32R3A1S34R3A1A2G1A2A2A2F_;F_;Fn;").
Proof.
  intros n Hn Hp. unfold is_primary in Hp. apply Z.leb_le in Hp. pose proof (rz_bound n) as RZ.
  assert (Hnd : 1 <= needed n) by (unfold needed, round_up; pose proof (Z.div_pos (Z.max n kChunkHeader2Size + 8 - 1) 8); nia).
  pose proof (cls_fits_all (needed n) (conj Hnd Hp)) as F. unfold cls_fits in F. apply andb_prop in F as [F F3]. apply andb_prop in F as [F1 F2].
  apply Z.leb_le in F1. apply Z.leb_le in F2. apply Z.leb_le in F3. split; [exact F1|]. split; [lia|].
  unfold needed, N8, round_up, kChunkHeader2Size. pose proof (Z.div_le_mono (n + 7) (Z.max n 16 + 8 - 1) 8 ltac:(lia) ltac:(lia)). nia.
Qed.
Lemma rz_mod16 : ltac2:(tb__ "0|0|
S0ScS0S4S34R1A1Z10A2Z0A3Fn;").
Proof.
  intros n. unfold rz, rz_log. repeat (destruct (n <=? _); [rewrite Z.shiftl_mul_pow2 by lia; cbn; reflexivity|]).
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma round_up_ge : ltac2:(tb__ "0|0|
S0S0S5Z0R1A2S1R3S3dR3R2A2A2F_;Fm;Fx;").
Proof. intros x m Hm. unfold round_up. pose proof (Z.div_mod (x + m - 1) m ltac:(lia)). pose proof (Z.mod_pos_bound (x + m - 1) m ltac:(lia)). nia. Qed.

Lemma multiples_apart : ltac2:(tb__ "0|1|
S0S0S0S5Z0M0R3A2ScS0S4R3R4A2G0A3ScS0S4R3R5A2G0A3SdScS0R5R4A3A1SeS1S2R6R7A2R5A2S1S2R5R7A2R6A2A2F_;F_;F_;F_;Fb;Fa;FS;").
Proof.
  intros S a b HS Ha Hb NE.
  destruct (proj1 (Z.mod_divide a S ltac:(lia)) Ha) as [u Hu]. destruct (proj1 (Z.mod_divide b S ltac:(lia)) Hb) as [v Hv].
  subst a b. assert (u <> v) by (intros ->; apply NE; reflexivity). nia.
Qed.

Lemma NoDup_app_disjoint : ltac2:(tb__ "0|2|
S12S0A1M0G0S0S0S3eS0S11S0R4R3A3A2S10S0R3R5A3M1G1SdScS0R5R4A3A1F_;F_;F_;Fy;Fx;Fk;Fl;").
Proof.
  intros l k x y ND Hx Hy ->. apply (proj1 (list_relations.list.NoDup_app _ _)) in ND as (_ & HD & _).
  apply (HD y); apply (proj2 (list_elem_of_In _ _)); assumption.
Qed.

Lemma NoDup4_34 : ltac2:(tb__ "0|2|
S12S0A1M0G0G0G0S0S0S3eS0S11S0R6S11S0R5S11S0R4R3A3A3A3A2S10S0R3R5A3M1G1SdScS0R5R4A3A1F_;F_;F_;Fy;Fx;Fl4;Fl3;Fl2;Fl1;").
Proof.
  intros l1 l2 l3 l4 x y ND Hx Hy.
  apply (proj1 (list_relations.list.NoDup_app _ _)) in ND as (_ & _ & ND). apply (proj1 (list_relations.list.NoDup_app _ _)) in ND as (_ & _ & ND).
  exact (NoDup_app_disjoint l3 l4 x y ND Hx Hy).
Qed.
Lemma NoDup4_23 : ltac2:(tb__ "0|2|
S12S0A1M0G0G0G0S0S0S3eS0S11S0R6S11S0R5S11S0R4R3A3A3A3A2S10S0R3R6A3M1G1SdScS0R5R4A3A1F_;F_;F_;Fy;Fx;Fl4;Fl3;Fl2;Fl1;").
Proof.
  intros l1 l2 l3 l4 x y ND Hx Hy.
  apply (proj1 (list_relations.list.NoDup_app _ _)) in ND as (_ & _ & ND).
  apply (NoDup_app_disjoint l2 (l3 ++ l4) x y ND Hx). apply in_or_app. left. exact Hy.
Qed.
Lemma NoDup4_24 : ltac2:(tb__ "0|1|
S12S0A1M0G0G0G0S0S0S3eS0S11S0R6S11S0R5S11S0R4R3A3A3A3A2S10S0R3R6A3S10S0R3R5A3SdScS0R5R4A3A1F_;F_;F_;Fy;Fx;Fl4;Fl3;Fl2;Fl1;").
Proof.
  intros l1 l2 l3 l4 x y ND Hx Hy.
  apply (proj1 (list_relations.list.NoDup_app _ _)) in ND as (_ & _ & ND).
  apply (NoDup_app_disjoint l2 (l3 ++ l4) x y ND Hx). apply in_or_app. right. exact Hy.
Qed.

Lemma live_ids_in' : ltac2:(tb__ "0|0|
S21S1bS0S0S0S10S14S0S0A2S13S0S0R3R2A4S1cR4A1A3ScS15S17S37R3A1S9S35S39R3A1A1R2A2A2S16A3S10S0S7S3S3R5S34R4A1A2S38S1fR7A1R3A2A2Z10A2S40R7R6R3A3A3F_;F_;Fc;Fn;Fb;FA;FG;").
Proof.
  intros G A b n c Hin Hb. unfold live_ids. apply in_map_iff. exists (b, n). split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply (proj2 (list_basics.list.list_elem_of_filter _ _ _)).
  split; [cbn [snd]; rewrite Hb; exact I|]. apply list_elem_of_In. exact Hin.
Qed.

Section LAWS.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Lemma shiftr4_of_mul16 : ltac2:(tb__ "0|1|
S0ScS0S4R1Z10M0A2Z0A3ScS0S6SaR2Z4A2G0A2R2A3F_;Fo;").
Proof.
  intros o Ho. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  pose proof (Z.div_mod o 16 ltac:(lia)). lia.
Qed.

Lemma law_G1 : ltac2:(tb__ "0|2|
S1bS30S12S2dQ40A1A1S2fS0S0VAInv;R6R5R4R3A4S10S14S0S0A2S13S0S0R3R2A4S1cR7A1A3SfS0S0SbSbS1Z0R1A2S5R1Z100A2A2SbScS0S4R1Z4A2Z1A3ScS1aS2dQ8M0A1M1A1S43S41S1eR9A1A1S44Vsegs;S31R8A1A2S3R5ZfA2A3S18G1S2eG0R1A2A2A3A2A2Lt;A2F_;F_;Fn;Fb;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md b n HA HL. pose proof HA as (HG & HR & HF & HRest & _). destruct HRest as (_ & HLB & _).
  destruct (HLB b n HL) as (_ & _ & _ & _ & _ & (t & Ht & Hm)).
  exists (bv_unsigned t). pose proof (bv_unsigned_in_range _ t) as R. change (bv_modulus 8%N) with 256 in R.
  split; [lia|]. split; [exact Hm|]. rewrite Z_to_bv_bv_unsigned. exact Ht.
Qed.

Lemma live_slot : ltac2:(tb__ "0|4|
S1bS30S12S2dQ40A1A1S2fS0S0VAInv;R6R5R4R3A4S10S14S0S0A2S13S0S0R3R2A4S1cR7A1A3ScS15S37R3A1S16A3S1eR9A1S21S35S39R5A1A1S0S38S1fR2A1R1A2S0S3S3R8S34R7A1A2R1A2S0SbSbS1Z1R3A2S1R3Z1eA2A2SbS1Z0M0R1A2SbScS0S4R1S36R3A1M1A2G0A3SbS1S2R1G1A2S2aS3fS22S20RdA1R3S23A4A1A2SbS1S2R2R1A2M2S3R9Z10M3A2A2SbS1S2R9S32R8A1A2S2G2G1A2A2SbS10S0S7R1G3A2S40R4RdR3A3A3ScS0S4R1G3A2G0A3A2A2A2A2A2A2A2To;Trb;Tc;TG;F_;F_;F_;Fn;Fb;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md b n HA HL HP. pose proof HA as (HG & HR & HF & HRest & _). destruct HRest as (Hsep & _ & HPR & _).
  destruct (Hsep b n HL) as (S1 & _). destruct (needed_fits n S1 HP) as (F1 & F2 & F3).
  set (c := ClassID (needed n)) in *. destruct HPR as (_ & _ & _ & HCR). specialize (HCR c F2).
  destruct HCR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & M4 & _ & _ & _ & _ & _ & PU & PSH & PE & ND & LV & _).
  destruct (LV b n HL HP eq_refl) as (L1 & L2 & L3). pose proof (rz_bound n) as RB. pose proof (size_ok_all c F2) as [SZ1 SZ2].
  cbn zeta. fold c.
  assert (O16 : (b - rz n - region_beg (ag_spacebeg (aa_geom A)) c) mod 16 = 0).
  { rewrite <- (Z.mod_mod_divide _ (Size c) 16) by (apply Z.mod_divide; lia). rewrite L2. reflexivity. }
  repeat split; try lia.
  apply live_ids_in'; [exact HL|]. rewrite HP. fold c. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma live_sec : ltac2:(tb__ "0|3|
S1bS30S12S2dQ40A1A1S2fS0S0VAInv;R6R5R4R3A4S10S14S0S0A2S13S0S0R3R2A4S1cR7A1A3ScS15S37R3A1S19A3S1eR9A1S21SfS24S24SbS10S24R1S29RbA1A3SbS1S2bR1A1M0S3R7Z10A2A2SbS1S2R7S32R6A1A2S2G0S2cR1A1A2M1A2SeS1G1S1fR2A1M2A2S1S2S2G2S3cA2Z1000A2G0A2A2A2A2A2Lch;A2TG;F_;F_;F_;Fn;Fb;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md b n HA HL HP. pose proof HA as (HG & HR & HF & HRest & HM & HI3 & _). destruct HRest as (Hsep & _ & _ & HSR & _).
  destruct (Hsep b n HL) as (S1 & _). destruct HI3 as (_ & HPS & SEC3 & _).
  destruct (HPS b n HL) as [Hp' | (ch & Hch & Eb & Esz)]; [rewrite HP in Hp'; discriminate|].
  destruct (In_nth_error _ _ Hch) as [i Hi]. destruct HSR as (HS & _). pose proof (HS i ch Hi) as (_ & _ & _ & _ & _ & B1 & B2 & B3 & B4 & B5 & B6 & B7 & _).
  destruct (SEC3 i ch Hi) as (X1 & _).
  pose proof (round_up_ge n 8 ltac:(lia)) as RU. assert (EN : N8 n = round_up n 8) by (unfold N8, round_up; replace (n + 8 - 1) with (n + 7) by lia; reflexivity).
  cbn zeta. exists ch. split; [exact Hch|]. unfold PG in *. split; [lia|]. split; [lia|]. exact X1.
Qed.

Lemma law_G3a : ltac2:(tb__ "0|1|
S1bS30S12S2dQ40A1A1S2fS0S0S1dVAInv;R7R6R5R4A4S10S14S0S0A2S13S0S0R4R3A4S1cR8A1A3S10S1dR3S11S1dS26R9A1S25R9A1A3A3SeS1S2R6S32R5A1A2S28R4A1M0A2S1S2G0S3aA2S3R6Z10A2A2A2F_;F_;F_;Fqb;Fn;Fb;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md b n qb HA HL HQ. pose proof HA as (HG & HR & HF & HRest & HM & HI3 & _).
  pose proof HRest as (Hsep & _ & HPR & _ & HQR & _). destruct (Hsep b n HL) as (S1 & _).
  destruct HQR as (QB & _). pose proof (proj1 (Forall_forall _ _) QB qb HQ) as (R1 & _ & _ & _ & _ & _ & _ & (x & X1 & X2 & XM & X3)).
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB1 & SB2 & SB0 & _).
  destruct HPR as (_ & _ & _ & HCR).
  pose proof (HCR 24 ltac:(lia)) as C24. destruct C24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND24 & _).
  assert (XM' : (16 * x) mod 8192 = 0) by (clear -XM; replace (16 * x) with (x mod 512 * 16 + (x / 512) * 8192) by (pose proof (Z.div_mod x 512); lia); rewrite XM; apply Z_mod_mult).
  assert (IDq : In x (q_ids (aa_geom A) (qall A) 24)).
  { unfold q_ids. rewrite Z.eqb_refl. apply in_or_app. right. apply in_map_iff. exists qb. split; [|exact HQ].
    unfold qb_id, ptr_to_compact, kCompactPtrScale. rewrite X1.
    replace (region_beg (ag_spacebeg (aa_geom A)) 24 + 16 * x - region_beg (ag_spacebeg (aa_geom A)) 24) with (x * 2 ^ 4) by lia.
    rewrite Z.shiftr_div_pow2, Z.div_mul by lia. reflexivity. }
  unfold kQuarantineBatchSize in *. unfold kUserSpaceSize, kUserMapSize, kFreeArraySize in *.
  destruct (is_primary n) eqn:HP.
  - pose proof (live_slot A rho tp md b n HA HL HP) as LS. cbn zeta in LS.
    pose proof (HCR _ (proj1 LS)) as Cc. destruct Cc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _).
    pose proof (size_ok_all _ (proj1 LS)) as [SZ1 SZ2].
    destruct (Z.eq_dec (ClassID (needed n)) 24) as [E24 | NE24].
    +
      rewrite E24 in LS. change (Size 24) with 8192 in LS. destruct LS as (C1 & O0 & OM & OA & LO & HI & IDin & O16).
      set (o := b - rz n - region_beg (ag_spacebeg (aa_geom A)) 24) in *.
      assert (NEQ : o / 16 <> x) by exact (NoDup4_34 _ _ _ _ (o / 16) x ND24 IDin IDq).
      assert (NEO : o <> 16 * x) by (clear -NEQ; intros E; apply NEQ; rewrite E, Z.mul_comm, Z.div_mul by lia; reflexivity).
      pose proof (multiples_apart 8192 o (16 * x) ltac:(clear; lia) OM XM' NEO) as MA.
      unfold o in MA. clear -MA LO HI X1. destruct MA; [left | right]; lia.
    +
      destruct LS as (C1 & O0 & OM & OA & LO & HI & IDin & O16).
      set (c := ClassID (needed n)) in *.
      unfold region_beg, kUserSpaceSize, kUserMapSize, kFreeArraySize, kRegionSize in *. change (2 ^ 32) with 4294967296 in *. change (2 ^ 29) with 536870912 in *. change (2 ^ 18) with 262144 in *.
      assert (CC : c <= 23 \/ 25 <= c) by (clear -C1 NE24; lia).
      clear -CC C1 O0 OA LO HI X1 X2 X3 M2 M3 N2 N3 SZ1.
      destruct CC; [left | right]; lia.
  - destruct (live_sec A rho tp md b n HA HL HP) as (ch & Hch & LO & HI & OFF). rewrite kSpaceSize_val in OFF.
    unfold region_beg, kUserSpaceSize, kUserMapSize, kFreeArraySize, kRegionSize in *. change (2 ^ 32) with 4294967296 in *. change (2 ^ 29) with 536870912 in *. change (2 ^ 18) with 262144 in *.
    clear -LO HI OFF X1 X2 X3 M2 M3 SB1. destruct OFF; [left | right]; lia.
Qed.

Lemma law_G3b : ltac2:(tb__ "0|1|
S1bS30S12S2dQ40A1A1S2fS0S0S0S0VAInv;R8R7R6R5A4S10S14S0S0A2S13S0S0R5R4A4S1cR9A1A3SbS1Z1R4A2S1R4Z1eA2A2S10S0R4S27S3fS22S20RbA1R5S23A4A1A3S2S38S1fS1eRcA1A1R6A2S6Z10M0R5A2A2S0SeS1S2R9S32R8A1A2R1A2S1S2R1S36R7A1A2S3R9G0A2A2A2Tab;F_;F_;F_;F_;Fx;Fc;Fn;Fb;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md b n c x HA HL Hc Hx. pose proof HA as (HG & HR & HF & HRest & HM & HI3 & _).
  pose proof HRest as (Hsep & _ & HPR & _). destruct (Hsep b n HL) as (S1 & _).
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB1 & SB2 & SB0 & _).
  destruct HPR as (_ & _ & _ & HCR).
  pose proof (HCR c Hc) as Cc. destruct Cc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & _ & _ & _ & _ & N7 & _ & _ & _ & NDc & _).
  pose proof (size_ok_all c Hc) as [SZ1 SZ2].
  destruct (N7 x ltac:(apply in_or_app; right; exact Hx)) as (X0 & XM & XA). unfold kCompactPtrScale in XM, XA. rewrite Z.shiftl_mul_pow2 in XM, XA by lia.
  change (2 ^ 4) with 16 in XM, XA.
  cbn zeta. unfold kUserSpaceSize, kUserMapSize, kFreeArraySize in *.
  destruct (is_primary n) eqn:HP.
  - pose proof (live_slot A rho tp md b n HA HL HP) as LS. cbn zeta in LS.
    pose proof (HCR _ (proj1 LS)) as Cc'. destruct Cc' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _).
    pose proof (size_ok_all _ (proj1 LS)) as [SZ1' SZ2'].
    destruct (Z.eq_dec (ClassID (needed n)) c) as [EC | NEC].
    + rewrite EC in LS. destruct LS as (C1 & O0 & OM & OA & LO & HI & IDin & O16).
      set (o := b - rz n - region_beg (ag_spacebeg (aa_geom A)) c) in *.
      assert (NEQ : x <> o / 16) by exact (NoDup4_23 _ _ _ _ x (o / 16) NDc Hx IDin).
      assert (NEO : x * 16 <> o) by (clear -NEQ; intros E; apply NEQ; rewrite <- E, Z.div_mul by lia; reflexivity).
      pose proof (multiples_apart (Size c) (x * 16) o ltac:(clear -SZ1; lia) XM OM NEO) as MA.
      unfold o in MA. clear -MA LO HI. destruct MA; [right | left]; lia.
    + destruct LS as (C1 & O0 & OM & OA & LO & HI & IDin & O16).
      set (c' := ClassID (needed n)) in *.
      unfold region_beg, kUserSpaceSize, kUserMapSize, kFreeArraySize, kRegionSize in *. change (2 ^ 32) with 4294967296 in *. change (2 ^ 29) with 536870912 in *. change (2 ^ 18) with 262144 in *.
      assert (CC : c' + 1 <= c \/ c + 1 <= c') by (clear -NEC; lia).
      clear -CC C1 Hc O0 OA LO HI X0 XA M2 M3 N2 N3 SZ1 SZ1'.
      destruct CC; [left | right]; nia.
  - destruct (live_sec A rho tp md b n HA HL HP) as (ch & Hch & LO & HI & OFF). rewrite kSpaceSize_val in OFF.
    unfold region_beg, kUserSpaceSize, kUserMapSize, kFreeArraySize, kRegionSize in *. change (2 ^ 32) with 4294967296 in *. change (2 ^ 29) with 536870912 in *. change (2 ^ 18) with 262144 in *.
    clear -LO HI OFF Hc X0 XA M2 M3 SB1 SZ1. destruct OFF; [left | right]; nia.
Qed.

Lemma law_G3c : ltac2:(tb__ "0|2|
S1bS30S12S2dQ40A1A1S2fS1dS0VAInv;R6R5R4R3A4S10S1dR3S11S1dS26R7A1S25R7A1A3A3S10S0R3S27S3fS22S20R8A1Z18M0S23A4A1A3S2S38S1fS1eR9A1A1G0A2S6Z10R4A2A2S0SeS1S2S28R6A1M1S3aA2R1A2S1S2R1Z2000A2G1A2A2Tab;F_;F_;F_;Fx;Fqb;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md qb x HA HQ Hx. pose proof HA as (HG & HR & HF & HRest & HM & HI3 & _).
  pose proof HRest as (_ & _ & HPR & _ & HQR & _).
  destruct HQR as (QB & _). pose proof (proj1 (Forall_forall _ _) QB qb HQ) as (R1 & _ & _ & _ & _ & _ & _ & (y & Y1 & Y2 & YM & Y3)).
  destruct HPR as (_ & _ & _ & HCR).
  pose proof (HCR 24 ltac:(lia)) as C24. destruct C24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & _ & _ & _ & _ & N7 & _ & _ & _ & ND24 & _).
  destruct (N7 x ltac:(apply in_or_app; right; exact Hx)) as (X0 & XM & XA). unfold kCompactPtrScale in XM, XA. rewrite Z.shiftl_mul_pow2 in XM, XA by lia.
  change (2 ^ 4) with 16 in XM, XA. change (Size 24) with 8192 in *.
  cbn zeta. unfold kQuarantineBatchSize in *.
  assert (IDq : In y (q_ids (aa_geom A) (qall A) 24)).
  { unfold q_ids. rewrite Z.eqb_refl. apply in_or_app. right. apply in_map_iff. exists qb. split; [|exact HQ].
    unfold qb_id, ptr_to_compact, kCompactPtrScale. rewrite Y1.
    replace (region_beg (ag_spacebeg (aa_geom A)) 24 + 16 * y - region_beg (ag_spacebeg (aa_geom A)) 24) with (y * 2 ^ 4) by lia.
    rewrite Z.shiftr_div_pow2, Z.div_mul by lia. reflexivity. }
  assert (NEQ : x <> y) by exact (NoDup4_24 _ _ _ _ x y ND24 Hx IDq).
  assert (NEO : x * 16 <> 16 * y) by (clear -NEQ; intros E; apply NEQ; lia).
  assert (YM' : (16 * y) mod 8192 = 0) by (clear -YM; replace (16 * y) with (y mod 512 * 16 + (y / 512) * 8192) by (pose proof (Z.div_mod y 512); lia); rewrite YM; apply Z_mod_mult).
  pose proof (multiples_apart 8192 (x * 16) (16 * y) ltac:(clear; lia) XM YM' NEO) as MA.
  clear -MA Y1. destruct MA; [right | left]; lia.
Qed.

Lemma chunk_not_other_live : ltac2:(tb__ "0|0|
S1bS30S12S2dQ40A1A1S2fS0S0S0VAInv;R7R6R5R4A4S10S14S0S0A2S13S0S0R4R3A4S1cR8A1A3SbS1S3R5S34R4A1A2R3A2S5R3S2S2R5R4A2Z8A2A2A2SdSbS1R6R4A2S5R4S2R6R5A2A2A2A1SdS42S1cRbA1R5A2A1F_;F_;F_;F_;Fz;Fn;Fb;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md b n z HA Hin Hz Hnb (b' & n' & Hin' & Hz').
  destruct (In_nth_error _ _ Hin) as [i Hi]. destruct (In_nth_error _ _ Hin') as [j Hj].
  pose proof (rz_bound n) as RB. pose proof (rz_bound n') as RB'.
  destruct (lt_eq_lt_dec i j) as [[L|E]|L].
  - pose proof (live_pair_apart _ A rho tp md i j b n b' n' HA L Hi Hj). lia.
  - subst j. rewrite Hi in Hj. inversion Hj; subst. lia.
  - pose proof (live_pair_apart _ A rho tp md j i b' n' b n HA L Hj Hi). lia.
Qed.

End LAWS.
End F0A_laws.

(* [comment removed for export] *)
Module F0A_sem.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "mul"; "land"; "lt"; "pow"; "div"; "lxor"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "rw"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "zsext"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem"; "aceilF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "casx"; "hw2"; "len_e"; "rup_e"; "usz_e"; "vH3"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Definition aceilF : Z := 140737479966720.
Lemma alloc_ceiling_valF : aceilF = 0x7fffff800000. Proof. reflexivity. Qed.

Lemma land_255 : ltac2:(tb__ "0|0|
S0S4Z0R1A2S2S0S8R2ZffA2S6R2Z100A2A3F_;Fa;").
Proof. intros a Ha. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_3 : ltac2:(tb__ "0|0|
S0S4Z0R1A2S2S0S8R2Z3A2S6R2Z4A2A3F_;Fa;").
Proof. intros a Ha. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma lxor_1_even : ltac2:(tb__ "0|2|
S0S4Z0M0R1A2S2S0S6R2Z2A2G0A3S2S0ScR3Z1M1A2S5R3G1A2A3F_;F_;Fa;").
Proof.
  intros a Ha He. symmetry. apply Z.add_nocarry_lxor. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2. exact He.
Qed.
Lemma land_lxor_distr : ltac2:(tb__ "0|0|
S0S0S0S2S0S8ScR3R2A2R1A2ScS8R3R1A2S8R2R1A2A2A3Fc;Fb;Fa;").
Proof.
  intros a b c. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec. destruct (Z.testbit a i), (Z.testbit b i), (Z.testbit c i); reflexivity.
Qed.
Lemma zsext_small : ltac2:(tb__ "0|0|
S0S0S3S4Z0R1A2S9R1SaZ2SdR2Z1A2A2A2A2S2S0S12R3R2A2R2A3F_;Fm;Fw;").
Proof. intros w m Hm. unfold zsext. destruct (Z.ltb_spec m (2 ^ (w - 1))); [reflexivity | lia]. Qed.

Definition semF (rho : valuation) (t : Z) : Prop := ltac2:(tb__ "0|b|
S1S10Q40SfVrho;R1A2A2Li;S1S0Fi;S3S3S3S4Z0M0Vt;A2S9Vt;Z100M1A2A2S2S0S6Vt;Z4A2Z1M2A3A2S3S2S0S6R1PcA1M3Z10M4A2G0A3S3S4G4G3A2S3S4G2R1PdA1M5A2S3S4S5G3R1P69A1M6A2S13A2S3S2S0R1P67A1S6G5SaZ2M7Z20A2M8A2A3S3S2S0R1P68A1M9S5S5G7S7G1Vt;A2A2S7Z10000SbG5G8A2A2A2A3S3S2S0R1P6bA1S5G9G2A2A3S3S2S0G6S7SbS5G5Z7A2Z8MaA2GaA2A3S2S0R1P6aA1SbG6GaA2A3A2A2A2A2A2A2A2A2A2TU;").

Section SemF.
Variable rho : valuation.
Let U (i : positive) : Z := bv_unsigned (rw rho i).
Variable t : Z.
Hypothesis HH : semF rho t.
Let Ht : 0 <= t < 256 /\ t mod 4 = 1. Proof. exact (proj1 HH). Qed.
Let Hp16 : U 12%positive mod 16 = 0. Proof. exact (proj1 (proj2 HH)). Qed.
Let Hp_lo : 16 <= U 12%positive. Proof. exact (proj1 (proj2 (proj2 HH))). Qed.
Let Hn : 1 <= U 13%positive. Proof. exact (proj1 (proj2 (proj2 (proj2 HH)))). Qed.
Let Hpn : U 12%positive + U 105%positive <= aceilF. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 HH))))). Qed.
Let H103 : U 103%positive = U 13%positive mod 2 ^ 32. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HH)))))). Qed.
Let H104 : U 104%positive = 2 + 256 * t + 65536 * (U 13%positive / 2 ^ 32). Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HH))))))). Qed.
Let H107 : U 107%positive = U 104%positive + 1. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HH)))))))). Qed.
Let H105 : U 105%positive = (U 13%positive + 7) / 8 * 8. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HH))))))))). Qed.
Let H106 : U 106%positive = U 105%positive / 8. Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HH))))))))). Qed.

Let p : Z := U 12%positive.
Let n : Z := U 13%positive.
Let q : Z := U 13%positive / 2 ^ 32.

Lemma n_lt : n < 2 ^ 47.
Proof. pose proof alloc_ceiling_valF. unfold n, p in *. rewrite H105 in Hpn. pose proof (Z.mul_div_le (U 13%positive + 7) 8 ltac:(lia)). lia. Qed.
Lemma q_lt : 0 <= q < 2 ^ 15.
Proof. pose proof n_lt. unfold q, n in *. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma hw_lt : ltac2:(tb__ "0|3|
S3S3S4Z0M0VU;P68A1M1A2S9G1SaZ2M2Z1fA2A2A2S3S2S0S6G1Z100A2G2A3S2S0S6G1G2A2G0A3A2A2").
Proof.
  pose proof q_lt as Q. fold q in H104. rewrite H104. split; [lia|]. split.
  - replace (2 + 256 * t + 65536 * q) with (2 + (t + 256 * q) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
  - replace (2 + 256 * t + 65536 * q) with (0 + (1 + 128 * t + 32768 * q) * 2) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma h3_val : ltac2:(tb__ "0|1|
S3S2S0VU;P6bA1M0S5S5Z3S7Z100Vt;A2A2S7Z10000Vq;A2A2A3S3S4Z0G0A2S9G0SaZ2Z1fA2A2A2A2").
Proof. pose proof q_lt. fold q in H104. rewrite H107, H104. split; lia. Qed.
Lemma n8_facts : ltac2:(tb__ "0|2|
S3S3S4Vn;VU;P69A1M0A2S9G0S5Vn;Z8M1A2A2A2S3S2S0S6G0G1A2Z0A3S3S4G1G0A2S2S0S7VU;P6aA1G1A2G0A3A2A2A2").
Proof.
  unfold n in *. rewrite H106, H105. pose proof (Z.div_mod (U 13%positive + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U 13%positive + 7) 8 ltac:(lia)).
  split; [lia|]. split; [apply Z.mod_mul; lia|]. split; [|rewrite Z.div_mul by lia; lia].
  assert (1 <= (U 13%positive + 7) / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma U_hw2 : ltac2:(tb__ "0|0|
S2S0S10Q40SeVrho;S15A2A2VU;P68A1A3").
Proof.
  pose proof hw_lt as (R & _ & _). unfold hw2, vHW. rewrite U_sext_e by lia. cbn [eval]. fold (U 104%positive). change (Z.of_N 32) with 32.
  rewrite Z.mod_small by lia. apply zsext_small. change (2 ^ (32 - 1)) with (2 ^ 31). lia.
Qed.

Lemma sem_casx : ltac2:(tb__ "0|0|
S2S11Q40A1SeVrho;S14A2SeVrho;S19A2A3").
Proof.
  pose proof hw_lt as (R & M256 & M2). apply bv_eq. unfold casx. rewrite U_xor2, U_and2, U_xor2, !U_hw2, !U_lit. unfold vH3. cbn [eval]. fold (U 107%positive).
  change (3 mod M64v) with 3. change (255 mod M64v) with 255.
  rewrite land_lxor_distr. rewrite !land_255 by lia. rewrite M256. change (3 mod 256) with 3. change (Z.lxor 2 3) with 1.
  rewrite lxor_1_even by lia. symmetry. exact H107.
Qed.

Lemma sem_typ : Forall (holds rho) F_typ.
Proof.
  pose proof h3_val as [E3 R3]. pose proof Ht as [Tt T4]. pose proof q_lt as Q.
  unfold F_typ, vH3. repeat apply Forall_cons; try apply Forall_nil.
  - apply (proj2 (holds_nbne rho _ _)). rewrite U_sext_e, U_lit by lia. cbn [eval]. fold (U 107%positive). change (Z.of_N 8) with 8. change (3 mod M64v) with 3.
    replace (U 107%positive mod 2 ^ 8) with 3.
    2:{ rewrite E3. replace (3 + 256 * t + 65536 * q) with (3 + (t + 256 * q) * 2 ^ 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
    reflexivity.
  - apply (proj2 (holds_nbne rho _ _)). rewrite U_lit, U_and2, U_zext_e, U_srl_lit, U_lit by lia. cbn [eval]. fold (U 107%positive).
    change (Z.of_N 8) with 8. change (8 mod 64) with 8. change (1 mod M64v) with 1. change (3 mod M64v) with 3.
    rewrite E3. replace (3 + 256 * t + 65536 * q) with (3 + (t + 256 * q) * 2 ^ 8) by lia. rewrite Z.div_add by lia. change (3 / 2 ^ 8) with 0.
    rewrite Z.add_0_l. replace (t + 256 * q) with (t + q * 2 ^ 8) by lia. rewrite Z.mod_add by lia. rewrite (Z.mod_small t) by lia.
    rewrite land_3 by lia. symmetry. exact T4.
  - apply (proj2 (holds_ult rho _ _)). rewrite U_lit. cbn [eval]. fold (U 107%positive). change ((2 ^ 32) mod M64v) with (2 ^ 32). lia.
Qed.

Lemma sem_usz : ltac2:(tb__ "0|0|
S2S0S10Q40SeVrho;S18A2A2Vn;A3").
Proof.
  pose proof h3_val as [E3 R3]. pose proof Ht as [Tt T4]. pose proof q_lt as Q. pose proof n_lt as N. pose proof (urange (rw rho 103%positive)) as R103.
  unfold usz_e, vH3, vNLO. rewrite U_or2, U_sll_lit, U_srl_lit, U_zext_e by lia. cbn [eval]. fold (U 107%positive) (U 103%positive).
  change (16 mod 64) with 16. change (32 mod 64) with 32. change (Z.of_N 32) with 32.
  replace (U 107%positive / 2 ^ 16) with q.
  2:{ rewrite E3. replace (3 + 256 * t + 65536 * q) with ((3 + 256 * t) + q * 2 ^ 16) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  unfold M64v. rewrite (Z.mod_small (q * 2 ^ 32)) by lia. rewrite H103. fold n. rewrite (Z.mod_small (n mod 2 ^ 32)) by (pose proof (Z.mod_pos_bound n (2 ^ 32)); lia).
  rewrite lor_disjoint_add; [| lia | pose proof (Z.mod_pos_bound n (2 ^ 32)); lia | rewrite Z.land_comm; apply land_low_high; try lia; pose proof (Z.mod_pos_bound n (2 ^ 32)); lia].
  unfold q, n. pose proof (Z.div_mod (U 13%positive) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma sem_rup : ltac2:(tb__ "0|0|
S2S0S10Q40SeVrho;S17A2A2VU;P69A1A3").
Proof.
  pose proof n_lt as N. pose proof n8_facts as (A & B & C & D).
  unfold rup_e. rewrite (U_and_hmask rho _ 18446744073709551608 8 eq_refl). rewrite U_add, sem_usz, U_lit. change (7 mod M64v) with 7.
  unfold M64v. rewrite Z.mod_small by (unfold n; lia). rewrite H105. fold n.
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). lia.
Qed.
Lemma sem_d3 : diffs_ok rho d3F.
Proof.
  unfold diffs_ok, d3F. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; apply bv_eq.
  - rewrite sem_rup. reflexivity.
  - rewrite sem_usz. reflexivity.
  - rewrite sem_usz. reflexivity.
Qed.

Lemma sem_len : ltac2:(tb__ "0|0|
S2S0S10Q40SeVrho;S16A2A2VU;P6aA1A3").
Proof.
  pose proof n_lt as N. pose proof n8_facts as (A & B & C & D). pose proof alloc_ceiling_valF as ACV.
  unfold len_e, vN8. rewrite U_sub, U_add, !U_srl_lit, !U_add, !U_lit. cbn [eval]. fold (U 12%positive) (U 105%positive). fold p.
  change (3 mod 64) with 3. change ((-8) mod M64v) with (M64v - 8). change (1 mod M64v) with 1.
  rewrite (Z.mod_small (p + U 105%positive)) by (unfold M64v, p in *; lia).
  replace (p + U 105%positive + (M64v - 8)) with ((p + U 105%positive - 8) + 1 * M64v) by lia. rewrite Z.mod_add by (unfold M64v; lia).
  rewrite (Z.mod_small (p + U 105%positive - 8)) by (unfold M64v, p in *; lia).
  pose proof (Z.div_mod p 16 ltac:(lia)) as P16. fold p in Hp16.
  replace (p + U 105%positive - 8) with ((p / 16 * 2 + U 106%positive - 1) * 2 ^ 3) by lia.
  replace p with ((p / 16 * 2) * 2 ^ 3) at 2 by lia.
  rewrite !Z.div_mul by lia. rewrite (Z.mod_small (_ + 1)) by (unfold M64v, p in *; lia).
  replace (p / 16 * 2 + U 106%positive - 1 + 1 - p / 16 * 2) with (U 106%positive) by lia. apply Z.mod_small. unfold M64v; lia.
Qed.
Lemma sem_d4 : diffs_ok rho d4F.
Proof. unfold diffs_ok, d4F. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. apply bv_eq. rewrite sem_len. reflexivity. Qed.

Lemma sem_cas : Forall (holds rho) F_cas.
Proof.
  pose proof hw_lt as (R & M256 & M2). pose proof n_lt as N. pose proof n8_facts as (A & _). pose proof alloc_ceiling_valF as ACV.
  assert (E : forall k, 0 <= k < 2 ^ 31 -> bv_unsigned (eval rho (SAluW ALU_SLL (SLit k) m8)) = k).
  { intros k Hk. unfold m8. rewrite U_sllw, U_sll_lit, U_add, !U_lit. cbn [eval]. fold (U 12%positive). fold p. change (3 mod 64) with 3.
    change ((-16) mod M64v) with (M64v - 16).
    assert (Ep : (p + (M64v - 16)) mod M64v = p - 16).
    { replace (p + (M64v - 16)) with ((p - 16) + 1 * M64v) by lia. rewrite Z.mod_add by (unfold M64v; lia). apply Z.mod_small. unfold M64v, p in *; lia. }
    rewrite Ep.
    set (sh := ((((p - 16) * 2 ^ 3) mod M64v) mod 2 ^ 32) mod 32).
    replace sh with 0.
    2:{ subst sh. unfold M64v. pose proof (Z.div_mod p 16 ltac:(lia)) as P16. fold p in Hp16.
        rewrite (Z.mod_mod_divide _ 18446744073709551616 (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
        rewrite (Z.mod_mod_divide _ (2 ^ 32) 32) by (exists (2 ^ 27); reflexivity).
        replace ((p - 16) * 2 ^ 3) with (0 + (p / 16 - 1) * 4 * 32) by lia. rewrite Z.mod_add by lia. reflexivity. }
    rewrite Z.pow_0_r, Z.mul_1_r. unfold M64v. rewrite !(Z.mod_small k) by (clear - Hk; lia). apply zsext_small. change (2 ^ (32 - 1)) with (2 ^ 31). lia. }
  unfold F_cas. repeat apply Forall_cons; try apply Forall_nil.
  - apply (proj2 (holds_nbne rho _ _)). rewrite U_and2, U_hw2, !U_lit. change (255 mod M64v) with 255. change (2 mod M64v) with 2. rewrite land_255 by lia. exact M256.
  - apply (proj2 (holds_ult rho _ _)). unfold vHW. rewrite U_lit. cbn [eval]. fold (U 104%positive). change ((2 ^ 32) mod M64v) with (2 ^ 32). lia.
  - apply (proj2 (holds_beq rho _ _)). rewrite E, U_lit by lia. reflexivity.
  - apply (proj2 (holds_beq rho _ _)). rewrite E, U_lit by lia. reflexivity.
  - apply (proj2 (holds_beq rho _ _)). rewrite E, U_lit by lia. reflexivity.
Qed.
End SemF.
End F0A_sem.

(* [comment removed for export] *)
Module CertCallocSR.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "app"; "prod"; "false"; "option"; "true"; "list"; "bool"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sv"; "cell"; "sobj"; "mkCell"; "SAlu"; "SVar"; "SPUle"; "mkObj"; "DUnknown"; "ss_objs"; "SPAlign"; "ss_facts"; "SPBranch"; "DZero"; "SMd"; "SPNot"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "SPUlt"; "ss_next"; "ss_pc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_LTU"; "M_MUL"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "leafA"; "cell_eqb"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "vK"; "F_pop"; "pcof"; "updR"; "vMU"; "nxt"; "rst"; "addobjs"; "vNEW"; "vAU"; "vNF"; "F_new"; "O_cell"; "nobj"; "vCHX"; "vMC"; "vMFA"; "F_r0"; "F_r1"; "LNX"; "LV3"; "PV4"; "PV6"; "beg1"; "beg2"; "choffK"; "keepn"; "sMS"; "vRI"; "F_x"; "GR"; "HINT_au"; "HINT_k"; "HINT_map"; "LV0"; "LV2"; "O_pccK"; "O_pckK"; "O_pcm"; "O_ri"; "PNX"; "PNX1"; "PV5"; "PV7"; "cE3a"; "cE3b"; "cR0a"; "idx_rot"; "rMS"; "req_e"; "ri_cells"; "rotM"; "selobjs"; "setobj"; "sh1"; "sh2"; "tMS"; "vFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "V_SIZE"; "pc_base"; "V_CLS"; "O_pcs"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@Corelib.Lists.ListDef"; "firstn"; "seq"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "vSB"; "vRIS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "gsv"; "shb"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA EntailA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Open Scope Z_scope.

Definition GR : positive := 240%positive.
Definition vMC : sv := SVar 220.  Definition vNF : sv := SVar 221.  Definition vMFA : sv := SVar 222.  Definition vAU : sv := SVar 223.
Definition vMU : sv := SVar 224.  Definition vRI : sv := SVar 225.  Definition vFA : sv := SVar 226.   Definition vK : sv := SVar 227.
Definition vNEW : sv := SVar 228.

Definition O_pcm : sobj := ltac2:(tb__ "0|2|
S15S6dScZ4M0A1M1ScZ8A1S0SfS11G1G0S41A3S1SfA1A3S16A5").
Definition O_pch : sobj := ltac2:(tb__ "0|0|
S15S6dScZ10A1ScZ50A1S1SfA1S16A5").

Definition ri_cells : list cell := ltac2:(tb__ "0|2|
S0SfS11ScZ0A1M0Z8M1G0A3S0SfS11ScZ10A1G1S3cA3S0SfS11ScZ18A1G1S42A3S0SfS11ScZ20A1G1S3bA3S0SfS11ScZ28A1G1G0A3S0SfS11ScZ30A1G1S36A3S0SfS11ScZ38A1G1G0A3S0SfS11ScZ44A1Z1G0A3S1SfA1A3A3A3A3A3A3A3A3").
Definition O_ri : sobj := ltac2:(tb__ "0|0|
S15S4eScZ0A1ScZ80A1S64S16A5").

Definition ri_e : sv := ltac2:(tb__ "0|0|
S12S28S7bS12S29S13S6eA1ScZ7A1A3A3").
Definition rb_e : sv := ltac2:(tb__ "0|0|
S12S28S7aS12S29S13S6eA1ScZ20A1A3A3").
Definition fa_e : sv := ltac2:(tb__ "0|0|
S12S28S7aS12S28S12S29S13S6eA1ScZ20A1A3ScZe0000000A1A3A3").
Definition k_e : sv := SAluW ALU_SRL vMC (SLit 1).

Definition F_r0 : list sprop := ltac2:(tb__ "0|0|
S0SdS14ScZ2A1S41A2S0SdS14S41ScZ10A1A2S1SdA1A3A3").
Definition F_r1 : list sprop := ltac2:(tb__ "0|0|
S0SdS18Pe1Z7A2S0SdS18Pe2ZcA2S0SdS14ScZ1A1S32A2S0SdS14S32ScZ8A1A2S0SdS14S3cScZ8000000A1A2S0SdS14S3bS36A2S0SdS18Pe0Z12A2S0SdS18P9bZ10A2S1SdA1A3A3A3A3A3A3A3A3").
Definition req_e : sv := SAlu ALU_SUB vK vNF.

Definition HINT_map : sprop := ltac2:(tb__ "0|0|
S1aS2aS36S12S28S3bS1cS2bS13S6cA1S63A3A3A3").

Definition runC (cutpcs : list Z) (C : axst) : list leafA := ltac2:(tb__ "0|1|
S7S9S2fA1M0A1G0Lx;S31S7fUfa0Vcutpcs;VC;S8A5G0R1Ll;S1S2fA1X7x2").

Definition updR (FR : list sprop) (E : axst) (pc : Z) (ru : list (nat * sv)) (objs : list sobj) (reset : bool) (facts : list sprop) (nx : positive) : axst := ltac2:(tb__ "0|0|
S2dVE;A1S24S2eVE;S1eVpc;S81S22R1A1Vru;A2S20R1A1S1fR1A1S23R1A1S4S10S17R1A1Vobjs;A3S4SdSaS9SdA1Lreset;Vreset;VFR;S19R1A1Xax2Vfacts;A3Vnx;S21R1A1A9A2TS;").
Definition nxt (E : axst) : positive := ss_next (ax_S E).
Definition pcof (E : axst) : Z := ss_pc (ax_S E).

Definition rst (FR : list sprop) (E : axst) (ru : list (nat * sv)) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S35VFR;VE;S34VE;A1Vru;S1S10A1S8Vfacts;S37VE;A1A8").

Definition addobjs (E : axst) (objs : list sobj) (nx : positive) : axst := ltac2:(tb__ "0|0|
S2dVE;A1S24S2eVE;S1eS27R1A1S22R1A1S20R1A1S1fR1A1S23R1A1S4S10S17R1A1Vobjs;A3S19R1A1Vnx;S21R1A1A9A2TS;").

Definition keepn (E : axst) (n : nat) : axst := ltac2:(tb__ "0|1|
S2eVE;S74S2dVE;A1M0S75S10Vn;S17G0A1A3A2A2").

Definition setobj (E : axst) (i : nat) (o : sobj) : axst := ltac2:(tb__ "0|2|
S2eVE;S74S2dVE;A1M0S4S10S75S10Vi;S17G0A1M1A3S0S10Vo;S77S10SbVi;A1G1A3A3A3A2A2").

Definition selobjs (E : axst) (idxs : list nat) : axst := ltac2:(tb__ "0|1|
S2eVE;S74S2dVE;A1M0S83S17G0A1Vidxs;A2A2A2").

Definition factsR (E3 : axst) : list sprop := ltac2:(tb__ "0|0|
S4SdS19S2dVE3;A1A1S4SdS43S44A3A3").

Definition F_pop : list sprop := ltac2:(tb__ "0|0|
S0SdS1aS2aS3cS32A3S0SdS53S0SdS14S36ScZdffc0000A1A2S1SdA1A3A3A3").
Definition F_new : list sprop := ltac2:(tb__ "0|0|
S0SdS14ScZ4A1S3aA2S0SdS14S3aScZ2001A1A2S0SdS14S42ScZ1ffc0000A1A2S0SdS18PdeZ12A2S1SdA1A3A3A3A3").

Definition HINT_au : sprop := ltac2:(tb__ "0|0|
S1dS1aS2aS12S28S36ScZ40000A1A3S12S28S3bS1cS2bS3aS13S6cA1A3A3A3A1").
Definition HINT_k : sprop := ltac2:(tb__ "0|0|
S1dS1aS2aS12S28S3cS3aA3S32A3A1").

Definition beg1 : sv := SAlu ALU_ADD vMU rb_e.
Definition O_up : sobj := ltac2:(tb__ "0|0|
S15S49ScZ0A1ScZ40000A1S1SfA1S1bA5").
Definition sh1 : sv := ltac2:(tb__ "0|0|
S12S28S7cS49A1S7dA3").
Definition O_sh1 : sobj := ltac2:(tb__ "0|0|
S15S68ScZ0A1ScZ8000A1S1SfA1S16A5").
Definition fa_e2 : sv := SAlu ALU_ADD rb_e (SLit 3758096384).
Definition beg2 : sv := SAlu ALU_ADD vMFA fa_e2.
Definition O_fp : sobj := ltac2:(tb__ "0|0|
S15S4aScZ0A1ScZ40000A1S1SfA1S1bA5").
Definition sh2 : sv := ltac2:(tb__ "0|0|
S12S28S7cS4aA1S7dA3").
Definition O_sh2 : sobj := ltac2:(tb__ "0|0|
S15S69ScZ0A1ScZ8000A1S1SfA1S16A5").

Definition cR0a (E3 : axst) : axst := ltac2:(tb__ "0|0|
S39VE3;S0S10S58S0S10S59S1S10A1A3A3S50A3").
Definition cR0 (E3 : axst) : axst := ltac2:(tb__ "0|0|
S79S60VE3;A1S4SdS19S2dVE3;A1A1S4SdS43S44A3A3A2").
Definition cR1 (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU8S4eA4S0G0S3S2SeU14S6bA4S0G0S3S2SeUeS32A4S1G0A1A3A3A3S1SdA1A4").

Definition cPa (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU15S13S6cA1A4S1G0A1A3S33A4").
Definition cPb (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU15S13S6cA1A4S1G0A1A3S33A4").
Definition cP2 (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU13ScZ40000A1A4S0G0S3S2SeU14S36A4S1G0A1A3A3S33A4").

Definition cP2c (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S35VFR;VE;S34VE;A1S0S5S2SeA2M0S3S2SeU13ScZ40000A1A4S0G0S3S2SeU14S36A4S0G0S3S2SeUbS13Pf1A1A4S0G0S3S2SeUfS13Pf5A1A4S0G0S3S2SeU10S13Pf6A1A4S1G0A1A3A3A3A3A3S1S10A1S8S33PfaA8").
Definition cX (E : axst) (eb : sv) : axst := ltac2:(tb__ "0|2|
S35S1SdA1M0VE;S34VE;A1S0S5S2SeA2M1S3S2SeUaVeb;A4S1G1A1A3S1S10A1S6G0S37VE;A1A8").
Definition gX (C : axst) (eb : sv) (o : sobj) : axst := ltac2:(tb__ "0|1|
S2eVC;S82S2dVC;A1M0Veb;S4S10S17G0A1S0S10Vo;S1S10A1A3A3S26G0A1A4A2").
Definition cM (E : axst) (osh : sobj) : axst := ltac2:(tb__ "0|2|
S35S1SdA1M0VE;S34VE;A1S0S5S2SeA2M1S3S2SeUcScZ8000A1A4S1G1A1A3S0S10Vosh;S1S10A1A3S6G0S37VE;A1A8").

Definition sMS (C : axst) : wsub := ltac2:(tb__ "0|0|
S78P1S2dVC;A1S2dS72A1A3").
Definition rMS (C : axst) : list sobj := ltac2:(tb__ "0|1|
S7S9S10A1M0A1G0Lx;S85VC;S72S4dVC;A1A3G0R1LR;S1S10A1X7x2").
Definition tMS (C : axst) : axst := ltac2:(tb__ "0|0|
S86S4dVC;A1S72S80S87S73A1A1VC;S62VC;A1A5").
Definition dMS (C : axst) : axst := ltac2:(tb__ "0|0|
S79S6aVC;A1S19S2dVC;A1A1A2").

Definition nobj (E : axst) : nat := length (ss_objs (ax_S E)).
Definition idx_rot (E : axst) : list nat := ltac2:(tb__ "0|1|
S4S2S76U1M0S70S3fVE;A1G0A2A2S0S2U0S1S2A1A3A3").
Definition rotM (E : axst) : axst := ltac2:(tb__ "0|0|
S66VE;S61VE;A1A2").
Definition relM (E : axst) : axst := ltac2:(tb__ "0|0|
S4cS65VE;A1S70S3fVE;A1U2A2A2").
Definition cD (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|1|
S38VFR;VE;S0S5S2SeA2M0S3S2SeU13S3aA4S1G0A1A3S4SdS33S3dA3A4").
Definition cFm (E : axst) : axst := ltac2:(tb__ "0|2|
S35S1SdA1M0VE;S34VE;A1S0S5S2SeA2M1S3S2SeU8S12S28S42ScZ40000A1A3A4S1G1A1A3S1S10A1S6G0S37VE;A1A8").

Definition LV0 : positive := 400%positive. Definition LV2 : positive := 402%positive. Definition LV3 : positive := 403%positive.
Definition LNX : positive := 410%positive.
Definition O_cell (v : positive) (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S15S13Vv;A1ScZ0A1ScZ4A1Vcs;S16A5").
Definition cL0 (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|2|
S35VFR;VE;S34VE;A1S0S5S2SeA2M0S3S2SeUaS13S54A1A4S0G0S3S2SeUcS13S55A1M1A4S0G0S3S2SeUeS12S2cG1ScZ4A1A3A4S0G0S3S2SeUfS13S46A1A4S1G0A1A3A3A3A3S1S10A1S8S4SdS33S3dA3S45A8").
Definition cL1 (C : axst) : axst := ltac2:(tb__ "0|0|
S39VC;S0S10S3eS46S1SfA1A2S1S10A1A3S45A3").
Definition cXL (FR : list sprop) (E : axst) : axst := ltac2:(tb__ "0|0|
S38VFR;VE;S1S5S2SeA2A1S4SdS33S4SdS3dS0SdS51S0SdS52S1SdA1A3A3A3A3A4").

Definition PV4 : positive := 524%positive. Definition PV5 : positive := 525%positive. Definition PV6 : positive := 526%positive.
Definition PV7 : positive := 527%positive. Definition PNX : positive := 527%positive. Definition PNX1 : positive := 528%positive.
Definition cT0 (E : axst) : axst := ltac2:(tb__ "0|2|
S35S1SdA1M0VE;S34VE;A1S0S5S2SeA2M1S3S2SeUdS13S47A1A4S0G1S3S2SeU14S13S48A1A4S0G1S3S2SeUcS13S5cA1A4S1G1A1A3A3A3S1S10A1S6G0S5aA8").
Definition cT1 (C : axst) : axst := ltac2:(tb__ "0|1|
S39VC;S0S10S3eS48S0SfS11ScZ0A1Z4S13S5dA1A3S1SfA1M0A3A2S0S10S3eS47G0A2S1S10A1A3A3S5bA3").

Definition vCHX : sv := SVar 229.
Definition choffK : sv := ltac2:(tb__ "0|0|
S12S28S12S29S12S28S32ScN1A1A3ScZ2A1A3ScZ10A1A3").
Definition O_pccK : sobj := ltac2:(tb__ "0|2|
S15S6dScZ0A1M0ScZ4M1A1S0SfS11G0G1S32A3S1SfA1A3S16A5").
Definition O_pckK : sobj := ltac2:(tb__ "0|0|
S15S6dS4bScZ50A1S0SfS11S4bZ4S40A3S1SfA1A3S16A5").
Definition F_x : list sprop := ltac2:(tb__ "0|0|
S0SdS25S40ScS8aZ2Z1cA2A1A2S1SdA1A3").
Definition s_exit (E Ep : axst) : wsub := ltac2:(tb__ "0|1|
S0S5S71SeA2M0S3S71SeP95S32A4S0G0S3S71SeP9fS40A4S78S7eS2dVE;A1S2dVEp;A1A3A3A3").

Definition cE1 (E : axst) (ic : nat) : axst := ltac2:(tb__ "0|0|
S67VE;Vic;S56A3").
Definition cE2 (E : axst) : axst := ltac2:(tb__ "0|0|
S4cVE;S70S3fVE;A1U2A2A2").
Definition cE3a (E : axst) : axst := ltac2:(tb__ "0|0|
S39VE;S0S10S6fS1S10A1A3S37VE;A1A3").
Definition cE3b (E : axst) : axst := ltac2:(tb__ "0|0|
S39S5eVE;A1S0S10S57S1S10A1A3S37VE;A1A3").
Definition cE3 (E : axst) : axst := ltac2:(tb__ "0|0|
S84S4fS5fVE;A1A2").

Definition ri_has (cells : list cell) (e16 e24 e32 e48 : sv) : bool := ltac2:(tb__ "0|2|
S89SfSfS88SfS30R1A1Vcells;A3Lcc;S0SfS11ScZ0A1M0Z8M1G0A3S0SfS11ScZ10A1G1Ve16;A3S0SfS11ScZ18A1G1Ve24;A3S0SfS11ScZ20A1G1Ve32;A3S0SfS11ScZ28A1G1G0A3S0SfS11ScZ30A1G1Ve48;A3S0SfS11ScZ38A1G1G0A3S0SfS11ScZ44A1Z1G0A3S1SfA1A3A3A3A3A3A3A3A3A3").
End CertCallocSR.

(* [comment removed for export] *)
Module CertCallocSS.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "nil"; "app"; "prod"; "option"; "false"; "list"; "None"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SVar"; "SPUle"; "sobj"; "SAlu"; "FcsrFrm0"; "SPAlign"; "SPBranch"; "SPUlt"; "mkSS"; "DZero"; "SPNot"; "cell"; "mkObj"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_setS"; "sym_runA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_MS"; "V_NS"; "msx"; "V_NCH"; "V_NRES"; "V_PAB"; "RT_sec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS.W"; "CS1"; "nxS"; "regs_ss"; "ES1"; "ES1f"; "SS0"; "SSa_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayReserve"; "IMG_HI"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "ERRNO_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "E_regs"; "E_s1"; "F_fam"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Stdlib.PArith.BinPos.Pos"; "succ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition V_NS : positive := 141%positive.
Definition V_MS : positive := 142%positive.
Definition V_PAB : positive := 145%positive.
Definition V_NRES : positive := 146%positive.
Definition V_NCH : positive := 147%positive.

Definition N_sec : list carve_spec := ltac2:(tb__ "0|d|
S1S5S5S5ScSbA2M0SbA2M1S8S5S5SbS2A2M2ScA2M3A1M4A2M5S0G1G4S0G0SbS0ScSbSeZ0A1M6S1dA4S1eS1dZ40A2M7A4S1G3S0G2ScS0SbS2S1dU8M8A4SeS3dA1A4S1G3S0G2ScS0SbS2S1eS1dZ8A2G8A4SfS2dA1M9A4S1G3S0G2ScS0SbS2S1eS1dZ10A2G8A4G9A4S1G3S0G2ScS0SbS2S1eS1dZ18A2G8A4SeS3bA1A4S1G3S0G2ScS0SbS2S1eS1dZ30A2G8A4SfS2cA1A4S1G3S0G2ScS0SbS2S1eS1dZ38A2G8A4SfS2bA1A4S3G3A1MaA3A3A3A3A3A3A4S1G5S0G1G4S0G0SbS0ScSbG6G7A4Zee040MbA4GaA4S1G5S0G1G4S0G0SbS0ScSbG6GbA4Zee044A4S1G3S0G2ScS0SbS2GbU4A4G6A4GaA3A4S1G5S0G1G4S0G0SbS0ScSbG6Zee048A4Zee070A4GaA4S1G5S0G1G4S0G0SbS0ScSbG6Ze9b28McA4Ze9b30A4S1G3S0G2ScS0SbS2GcG8A4SeZ1a36fA1A4GaA3A4S1G5S0G1G4S0G0SbS0ScSbG6Z173660A4Z173662A4S1G3S0G2ScS0SbS2Z173661U1A4SeZ1A1A4GaA3A4S1G5S0G1G4S0G0SbS0ScSbG6S3eA4S1eS3eZ4A2A4GaA4S1G5S0G1G4S0G0SbS0ScSbS48Zad0A4Zc60A4GaA4S3G5A1A3A3A3A3A3A3A3A3").
Definition RT_sec : list sobj := map carve_obj N_sec.
Definition O_seci : sobj := nth 0 RT_sec O_st. Definition O_secs : sobj := nth 1 RT_sec O_st. Definition O_secm : sobj := nth 2 RT_sec O_st.
Definition O_secg : sobj := nth 3 RT_sec O_st. Definition O_san : sobj := nth 4 RT_sec O_st. Definition O_oom : sobj := nth 5 RT_sec O_st.
Definition O_errno : sobj := nth 6 RT_sec O_st.

Definition msx : sv := ltac2:(tb__ "0|0|
S12S21S12S23S12S21SfS29A1SeZfffA1A3SeZfffffffffffff000A1A3SeZ1000A1A3").
Definition F_sgen : list sprop := ltac2:(tb__ "0|6|
S1SdS14S29Z3A2S1SdS10SeZ10c08A1SfS29A1M0A2S1SdS16G0SeS1eS1fZ2M1Z27A2Z1008A2A1A2S1SdS14S28ZcA2S1SdS10S12S21G0SeZ1000A1A3SfS28A1M2A2S1SdS10G2S12S21G0SeZ1fffA1A3A2S1SdS16G2SeS1fG1Z28A2A1M3A2S1SdS15S22G2S2aA3S1SdS10SeS3cA1SfS2dA1M4A2S1SdS10G4SeS20Z7fffff800000S3bA2A1A2S1SdS10SfS2bA1SfS2cA1M5A2S1SdS10G5SeS1fG1Z14A2A1A2S1SdS10G0S2aA2S1SdS10S2aG3A2S1SdS19S15S22S12S21SfPaA1SeN9c8A1A3SeZ0A1A3A1S3SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Section W.
Variable W : list ulink.
Variable st : ustop.
Variable tmax : Z.

Let FACTS1 : list sprop := ltac2:(tb__ "0|0|
S4SdS4SdS4SdS4SdS4cVW;Vst;A2S4bS4aA1A3S39A3S44A3S43Vtmax;Z8A2A3").
Let OBJS1 : list sobj := ltac2:(tb__ "0|0|
S4S11S1S11S45S4S11S4dVW;A1S49A3A3S47A3").

Definition regs_ss : list sv := ltac2:(tb__ "0|2|
S37S41Z8A1S1S5S2ScA2M0S0S2ScUcSfS29A1M1A4S1G0S0S2ScU13G1A4S3G0A1A3A3A2").
Definition SSa_S : sstate := ltac2:(tb__ "0|0|
S17Z40a18S31S36S13S9ScA1VOBJS1;VFACTS1;S38S7A9").
Definition SSa : axst := ltac2:(tb__ "0|0|
S25S42VW;Vst;Vtmax;Z8A4S35A2").
Definition SSb_S : sstate := ltac2:(tb__ "0|0|
S17Z40a18S31S36S13S9ScA1S4S11VOBJS1;S2eA3VFACTS1;S38S7A9").
Definition SSb : axst := ax_setS SSa SSb_S.
Definition SS0 : axst := ax_add_facts F_sgen SSb.
Definition runS1 : list leafA := ltac2:(tb__ "0|1|
S6S8S24A1M0A1G0Lx;S26S3aUfa0S1SbZ7050cS3SbA1A3S34SaA5G0R1Ll;S3S24A1X6x2").
Definition ES1 : axst := leaf 0 runS1.

Definition CS1 : axst := ltac2:(tb__ "0|1|
S46VW;Vst;Vtmax;S32Z7050cS1S5S2ScA2M0S0S2ScUbSfS28A1A4S3G0A1A3S3S11A1S7S3SdA1A9").

Definition ES1f : axst := ltac2:(tb__ "0|0|
S40S2fSeS20S1fZ2Z40A2ZcA2A1A2").
Definition runSf : list leafA := ltac2:(tb__ "0|1|
S6S8S24A1M0A1G0Lx;S26S3aUfa0S1SbZ5e5d4S3SbA1A3S33SaA5G0R1Ll;S3S24A1X6x2").
Definition ESn : axst := leaf 0 runSf.

Definition nxS : positive := ss_next (ax_S CS1).
Definition ES1g : axst := ltac2:(tb__ "0|2|
S25S2fS3fS27S2fA1M0SfS30A1M1S4S11S1cG0A1S1S11S1bG1SeZ0A1SfS28A1S3S1aA1S18A5S3S11A1A3A3S4eS30A1A4A2").
End W.

Goal map (fun L => (ss_pc (ax_S (la_state L)), la_reason L)) (runS1 (Wcan 0) UStopLe 2) = [(0x7050c, RsCut)]
  /\ nth 11 (ss_regs (ax_S (ES1 (Wcan 0) UStopLe 2))) (SLit 0) = SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SVar V_NS) (SLit 4095)) (SLit 18446744073709547520)) (SLit 8191)) (SLit 18446744073709547520)
  /\ nth 17 (ss_regs (ax_S (ES1 (Wcan 0) UStopLe 2))) (SLit 0) = SLit 222.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal map (fun L => (ss_pc (ax_S (la_state L)), la_reason L)) (runSf (Wcan 0) UStopLe 2) = [(0x5e5d4, RsCut)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End CertCallocSS.

(* [comment removed for export] *)
Module SecOKInv.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "modulo"; "pow"; "sub"; "div"; "ge"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "vm_maps"; "alloc_top"; "event"; "m_vm_lazy"; "vm_noaccess"; "vm_reserved"; "region_free"; "vm_limit"; "with_vmmaps"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "app"; "cons"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "agree_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "acost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "GN"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "rhoM_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "FS_total"; "IMG_HI"; "IMG_LO"; "dyn_in"; "kPtrArrayReserve"; "kSpaceSize"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_V"; "aa_depot"; "aa_geom"; "aa_sec"; "sec_chunk"; "DG"; "aa_Kf"; "aa_Km"; "aa_cache_inited"; "aa_cls"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "ag_pab"; "ag_spacebeg"; "ag_thread"; "ageom"; "budget_ok_alloc"; "mkAA"; "sc_map_beg"; "sc_map_size"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "MI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv"; "bumpV"; "pendS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_nZ"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "top_high"; "tp_ok"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv.JGS"; "JGs"; "SHC"; "JGsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "depot_vm"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "prim_credit"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA SummaryA LedgerA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MmapA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition bumpV (A : AA) (n : Z) : AA := ltac2:(tb__ "0|0|
S4fS38VA;A1S3fVA;A1S3eVA;A1S39VA;A1S44VA;A1S43VA;A1S46VA;A1S45VA;A1S37VA;A1S41VA;A1S40VA;A1S42VA;A1S5S36VA;A1Vn;A2S3dVA;A1S3cVA;A1Af").

Definition pendS (A : AA) (ua L : Z) (md : Model) : Prop := ltac2:(tb__ "0|6|
S38VA;A1S4dS1S33S1aS20Q40M0A1M1G1A2S19G1G1S21G0Vua;A2S21G0VL;A2A4SfSdVmd;A1A1A3S1S2S0S8Vua;S2cA2Z0M2A3S1S6G2VL;A2S1S30S52R1A1Vua;VL;A3S1S26S19S0S0Vua;VL;A4M3S19S0S0S4cR1A1Z1000M4A4A2S1S26G3S19S0S0S47R1A1G4A4A2S1S26G3S19S0S0S48R1A1G4A4A2S1S26G3S19S0S0S49R1A1S2dA4A2S1S26G3S19S0S0S4bR1A1S5S32G4A2A4A2S1S26G3S19S0S0S4aR1A1S31A4A2S1S3aS33S3aR1S39VA;A1A3S26G3S19S0S0S50R2A1S51R2A1A4A2F_;Fch;S1aS0S0A2M5S33G5R1S66S37VA;A1A1A3S26R2G3A2F_;Fbn;A2A2A2A2A2A2A2A2A2A2A2TG;").

Section S.
Let segs : list Segment := segsA.

Lemma depot_vm_grow : ltac2:(tb__ "0|6|
S3bSeSeS18S20Q40A1M0A1S1aG0G0A2M1S33G1R1SfSdR4A1M2A1M3A3S33G1R2G3A3F_;Fe;S2S18G1A1M4S12R3A1S12R4A1A3S2G4S13G2A1S13SdR5A1M5A1A3S2S0S10G5A1S10SdR6A1A1A3S65R8R7R5A3S65R9R7R6A3F_;F_;F_;F_;F_;Ftp;Fmd';Fmd;FG;").
Proof.
  intros G md md' tp Hm Hl Hna Htop [A B C D E F]. constructor.
  - intros bn Hbn. apply Hm. exact (A bn Hbn).
  - intros b Hb. rewrite Hl. exact (B b Hb).
  - intros b j Hb Hj. rewrite Hna. exact (C b j Hb Hj).
  - exact D.
  - intros bn Hbn. rewrite Htop. exact (E bn Hbn).
  - rewrite Htop. exact F.
Qed.

Lemma AInvA_sec_grant : ltac2:(tb__ "0|a|
S35S0S22S18S20Q40M0A1M1A1SeSeG1G1S0S2S18S1aG1G1A2M2A1M3SfSdR4A1A1S1eG2S19G1G1R3R2A4SfSdR5A1M4A1A3A3S2G3S13G4A1S13SdR6A1M5A1A3S2G3S14G5A1S14SdR7A1M6A1A3S2S0S16G6A1S16SdR8A1M7A1A3S2S0S10G7A1S10SdR9A1A1A3S2G3S12R9A1S12RaA1A3S2S0S1fG0R8A2R7A3S6Z0R8A2S4R9S7Z2R10A2A2S4S27R11A2S2S1bS15S1dG2S14SdRfA1M8A1SfG8A1A3RdRcA3S1cA3S4S53RfR11A2S5S53R10R11A2RcA2A2S4S5S25S36R15A1M9A1RdA2S25S5G9R14A2A1A2S34Vsegs;R16R14R13R12A5S34Vsegs;S57R17R16A2R15R14R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fa;Fmd';Fmd;Ftp;Frho;Fnv;FA;").
Proof.
  intros A nv rho tp md md' a n L Hvm Hna Hrs Hlm Htop Hlz HnL HL HL2 HGN Hfree Hpaid Hac (HG & HR & HF & HRest & HM & HI3 & HB).
  cbn [aa_geom bumpV] in *.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|].
  split.
  { unfold rest_inv in HRest |- *. cbn [aa_geom aa_live aa_cls aa_sec aa_ptr_committed aa_q_thread aa_q_global aa_depot aa_internal_inited aa_cache_inited aa_fs_busy aa_fs_hint bumpV] in HRest |- *.
    exact HRest. }
  split; [|exact (conj HI3 HB)].
  unfold model_inv, ledger_inv in HM |- *.
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec bumpV] in HM |- *.
  destruct HM as (VG & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  assert (INM : forall lo hi, in_maps (m_vmmaps md) lo hi -> in_maps (m_vmmaps md') lo hi).
  { intros lo hi (e & Hin & He). exists e. split; [rewrite Hvm; right; exact Hin | exact He]. }
  split.
  { destruct VG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold vm_geom. cbn [aa_geom aa_sec bumpV]. rewrite Hna, Hlz.
    split; [|split; [apply INM; exact G2 | split; [apply INM; exact G3 | split; [apply INM; exact G4 | split; [apply INM; exact G5 | split; [apply INM; exact G6 | split; [apply INM; exact G7 | split]]]]]]].
    - intros e x He Hx. destruct (G1 e x He Hx) as (e' & He' & Hx'). exists e'. split; [rewrite Hvm; right; exact He' | exact Hx'].
    - intros ch Hch. rewrite Hvm. right. exact (G8 ch Hch).
    - exact G9. }
  split.
  { rewrite (PrimCredit.prim_credit_same A (bumpV A nv) eq_refl).
    unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpV] in V2 |- *. set (pcr := PrimCredit.prim_credit A) in *. clearbody pcr. clear -V2 Hpaid Hac. lia. }
  split; [rewrite Hlm; exact V3|]. split; [clear -V4 HGN; unfold GN in HGN; lia|]. split; [exact V5|]. split; [exact V6|]. split; [rewrite Htop; exact V7|].
  split; [rewrite Hrs; exact L1|]. split; [rewrite Hvm; apply band_covered_cons; exact L2|].
  split.
  { rewrite Hrs, Hvm. apply maps_disjoint_insert; [exact L3|]. intros e' He'. exact (apart_of_region_free _ a n Hfree e' He'). }
  split.
  { unfold gap_ok, gapN_ok, gapS_ok, blocks_left, ledger in L4 |- *. cbn [aa_V aa_depot bumpV] in L4 |- *.
    rewrite Hrs, Hvm. destruct L4 as [N4 S4].
    pose proof (hwN_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IN.
    pose proof (hwS_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IS. cbn [snd] in IS. rewrite HnL in IS.
    split; [clear -N4 IN HGN; unfold GN in *; nia | clear -S4 IS HL2; lia]. }
  split.
  { eapply depot_vm_grow; [| exact Hlz | exact Hna | exact Htop | exact L5]. intros e He. rewrite Hvm. right. exact He. }
  split; [exact L6|]. split; [exact L7 | split; [| rewrite Hna; exact L9]].

  destruct L8 as (L8p & L8a & L8b). split; [|split; [exact (INM _ _ L8a) | exact (INM _ _ L8b)]].
  intros b s Hbs. rewrite Hvm in Hbs. destruct Hbs as [E|Hbs]; [injection E as <- <-; rewrite HnL; exact HL | exact (L8p b s Hbs)].
Qed.

Lemma pendS_intro : ltac2:(tb__ "0|6|
S35S22S18S20Q40M0A1M1A1SeSeG1G1S0S2S18S1aG1G1A2M2A1SfSdR4A1A1S1eG2S19G1G1R3R2A4SfSdR5A1A1A3A3S2S0S1fG0R3A2R2A3S4Z11c01R3A2S2S0S8S1fG0R6A2S2cA2Z0M3A3S6G3S1fG0R7A2A2S4S5S1fG0R8A2R6A2S10SdRaA1A1A2S0S1S4S1fG0RaA2M4R1A2S6R1S5G4R8A2A2A2S3S1S4S2fR2A2S6R2S2eA2A2A1F_;Fx;S2S1bS15S1dG2S14SdRcA1M5A1SfG5A1A3RaR9A3S1cA3S34Vsegs;R10RfReRdA5S58R11S1fG0RcA2RaRdA4F_;F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fa;Fmd';Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md md' a n L Hvm HnL HL Hal Hpos Hceil Himg Hfree (HG & HR & HF & HRest & HM & HI3 & HB).
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.
  destruct HM as (VG & _ & _ & _ & _ & _ & V7 & L1 & L2 & L3 & L4 & L5 & _).
  destruct VG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
  pose proof (geom_top _ HG) as TG. pose proof (topG_range (aa_geom A)) as TGR.
  assert (APT : forall lo sz, in_maps (m_vmmaps md) lo (lo + sz) -> sepZ (ua, L) (lo, sz)).
  { intros lo sz Him. destruct (apart_in_maps _ a n lo (lo + sz) Hfree Him) as [X|X]; unfold sepZ; cbn [fst snd]; lia. }
  unfold pendS. cbn zeta.
  split. { rewrite Hvm. left. unfold ua. rewrite Z_to_bv_bv_unsigned. rewrite <- HnL, Z_to_bv_bv_unsigned. reflexivity. }
  split; [exact Hal|]. split; [lia|].
  split.
  { assert (BC : band_covered (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) Geometry.SHADOW_BAND_LO Geometry.SHADOW_BAND_HI).
    { apply band_covered_app_r. exact L2. }
    pose proof (grant_avoids_band _ _ _ a n BC ltac:(unfold Geometry.SHADOW_BAND_LO, Geometry.SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; lia) Hfree ltac:(lia)) as W.
    rewrite HnL in W. unfold dyn_in. rewrite TG, <- V7. unfold IMG_LO, IMG_HI, PG in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact W].
    right. destruct (Z_lt_le_dec ua 6578176) as [Hlt|Hge]; [|exact Hge]. exfalso.
    destruct (Z_lt_le_dec ua 65536) as [X|X]; [apply (Himg 65536); lia | apply (Himg ua); lia]. }
  split; [apply APT; exact G3|]. split; [apply APT; exact G4|]. split; [apply APT; exact G5|]. split; [apply APT; exact G6|].
  split; [apply APT; replace (ag_spacebeg (aa_geom A) + (kSpaceSize + 4096)) with (ag_spacebeg (aa_geom A) + kSpaceSize + 4096) by lia; exact G2|].
  split; [apply APT; exact G7|].
  split.
  - intros ch Hch. destruct HRest as (_ & _ & _ & HSR & _). pose proof (sec_dyn _ _ ch HSR Hch) as (D1 & D2 & D3 & _).
    pose proof (apart_of_region_free _ a n Hfree (Z_to_bv 64 (sc_map_beg ch), Z_to_bv 64 (sc_map_size ch)) ltac:(apply in_or_app; right; exact (G8 ch Hch))) as X.
    unfold apartW in X. cbn [fst snd] in X. rewrite !u64_of_Z in X by lia. unfold sepZ. cbn [fst snd]. lia.
  - intros bn Hbn. destruct L5 as [DVM _ _ _ DVT DR].
    pose proof (apart_of_region_free _ a n Hfree (wentry bn) ltac:(apply in_or_app; right; exact (DVM bn Hbn))) as X.
    pose proof (DVT bn Hbn) as T. destruct HRest as (_ & _ & _ & _ & _ & HD & _).
    assert (B : IMG_HI <= fst bn /\ 0 < snd bn).
    { unfold dblocks in Hbn. apply in_app_or in Hbn as [Hb|Hb]; apply in_map_iff in Hb as (b & <- & Hb); cbn [fst snd].
      - destruct (dm_nb _ _ HD b Hb) as (_ & Y & _). unfold NBSZ. split; [exact Y | lia].
      - destruct (dm_fbases _ _ HD b Hb) as (_ & Y & _). unfold FBSZ. split; [exact Y | lia]. }
    unfold wentry, apartW in X. cbn [fst snd] in X. unfold IMG_HI in B.
    rewrite !u64_of_Z in X by lia. unfold sepZ. cbn [fst snd]. lia.
Qed.
End S.

Section JGS.
Variable W : list ulink. Variable st : ustop. Variable tmax : Z.
Let segs : list Segment := segsA.

Definition JGs (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|2|
S22S18S20Q40M0A1M1A1S18S11A1SeS1fG0S23Vrho;PcA2A2S0S1S24S56S2bVA;Vrho;A2R5A3S1S2G1S23R5S55VW;Vst;Vtmax;A3A2Va;A3S1S34Vsegs;S57VA;R1A2R5R4R2A5S1S58VA;S1fG0Va;A2S29R1A1R2A4S1VKc;R3R2A2S1S60VA;R5A2S1S61VW;Vst;R5A3S1S1S4Zfc01R1A2S6R1S9Z2Z27A2A2A2S1S5fVA;R5A2S4eVA;R1A2A2A2A2A2A2A2A2A2A2Tnv;Lmd;Ltr;Ltp;Lr;").

Definition SHC (nv : Z) : Z := ltac2:(tb__ "0|0|
S7S2cS5SbS29Vnv;A1S7Z8S2cA2A2Z2A2A2").
Definition JGsC (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|1|
S22S18S20Q40M0A1A1S18S11A1SeS1fG0S23Vrho;PcA2A2S0S1S62VA;VKc;Vrho;Va;R5R4R3R2A8S4S5S5S53R2R4A2S69VA;A1A2S63R1A1A2S28S57VA;R1A2A1A2A2Tnv;Lmd;Ltr;Ltp;Lr;").

Lemma acost_step' : ltac2:(tb__ "0|1|
S0S0S4Z0R2A2M0G0ScS7Z4SaS25S5R4R3A2A1S25R4A1A2A2SaS7Z7R3A2Z3A2A2F_;F_;Fn;FV;").
Proof.
  intros V n HV Hn. unfold acost, ALPHA_NUM, ALPHA_DEN.
  pose proof (Z.div_mod (7 * (V + n) + 4 - 1) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * (V + n) + 4 - 1) 4 ltac:(lia)).
  pose proof (Z.div_mod (7 * V + 4 - 1) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * V + 4 - 1) 4 ltac:(lia)). lia.
Qed.
Lemma acost_pays_map : ltac2:(tb__ "0|0|
S0S0S4Z0R2A2S4Zfc01R2A2S4S5S25R4A1S29R3A1A2S25S5R4R3A2A1A2F_;F_;Fnv;FV;").
Proof.
  intros V nv HV Hn. pose proof (acost_step' V nv HV ltac:(lia)) as AS.
  assert (B : secmapsize nv <= nv + 12295).
  { unfold secmapsize, secneeded, round_up, PG.
    pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)).
    set (r8 := (nv + 8 - 1) / 8 * 8).
    pose proof (Z.div_mod (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). lia. }
  lia.
Qed.

Lemma JGs_grant : ltac2:(tb__ "0|3|
S35S5dS22S22S18S20Q40M0A1M1A1S18S11A1SeG1G1G1G1S2aVW;Vst;A2S5eRbA1S67VW;Vst;RdRcRbRaR9R8R7A9S54Vsegs;R8RaA3S1fG0S23RdPcA2A2S0S1S4Zfc01R1A2S6R1S9Z2Z27A2A2A2S2S0S59R9A1S29R2A1A3S5aR9R8RcRaRbA5S2S1bS68S56S55VW;Vst;Vtmax;A3M2A2S1cA3S62R14R13R12RdS5cR11G2RdA3R10RfS17S5bSdReA1RcRdA3ReA2A8F_;F_;F_;F_;Tnv;F_;F_;F_;F_;Fflags;Faddr;Flen;Fa;Fmd;Ftr;Ftp;FrhoX;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoX tp tr md a len addr flags HUS HKc [Hag HJ] HMI nv Hnv HnZ Hpl Hnx.
  pose proof Hag as (Hagw & Hagl & Hagm). destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & _ & _ & _ & HM & _).
  pose proof HM as (_ & _ & _ & V0 & _ & _ & V7 & L1 & _).
  destruct (grant_facts_A addr flags md len a Hpl L1) as (Gal & Gpos & Gceil & Gimg & Gmaps). rewrite HnZ in Gceil, Gimg, Gmaps.
  pose proof Hpl as (_ & _ & _ & Gfree & _).
  destruct (mmap_nw (m_vmmaps md) a len (proj1 (proj2 (proj2 Hpl)))) as [En Etop]. rewrite HnZ in En, Etop.
  assert (NEQ : forall i, (i < GW)%positive -> i <> nxS W st tmax).
  { intros i Hi E. rewrite <- E in Hnx. apply Pos.leb_le in Hnx. exact (proj1 (Pos.lt_nle _ _) Hi Hnx). }
  set (h' := mmap_rw_vm (m_vmmaps md) len a). set (rho1 := rho_set_rw rhoX (nxS W st tmax) a).
  assert (Hvm : vm_maps h' = (a, mmap_n len) :: vm_maps (m_vmmaps md)) by reflexivity.
  assert (E12 : rw rhoX 12%positive = rw rho 12%positive) by (rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity).
  cbn [eval] in HB, HN. rewrite E12 in HB, HN. fold nv in HB, HN.
  assert (Hag1 : agree_below GW rhoX rho1) by (unfold rho1; apply agree_below_set_rw; apply Pos.leb_le; exact Hnx).
  pose proof Hag1 as (A1w & A1l & A1m).
  assert (SMB : 72705 <= secmapsize nv <= nv + 12295).
  { unfold secmapsize, secneeded, round_up, PG.
    pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)).
    set (r8 := (nv + 8 - 1) / 8 * 8).
    pose proof (Z.div_mod (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). lia. }
  unfold JGs. fold nv. cbn zeta.
  split.
  { split; [|split].
    - intros i Hi. rewrite (Hagw i Hi). apply A1w. exact Hi.
    - intros l. rewrite (Hagl l). apply A1l.
    - intros x. rewrite (Hagm x). apply A1m. }
  split; [unfold rho1; apply rho_set_rw_at|].
  split.
  { assert (Erm : rm rho1 = rm rhoX) by reflexivity.
    unfold AInvA. rewrite Erm. fold (AInvA segs (bumpV A nv) rhoX tp (with_vmmaps h' md)).
    refine (AInvA_sec_grant A nv rhoX tp md (with_vmmaps h' md) a (mmap_n len) (secmapsize nv) _ _ _ _ _ _ En ltac:(lia) ltac:(lia) ltac:(unfold GN; lia) Gfree _ _ HA);
      rewrite ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps; try reflexivity.
    - rewrite paid_with_vmmaps.
      pose proof (used_maps_cons_le md h' a (mmap_n len) (MI_ivs_wf segs _ _ HMI) ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite En; exact Etop) Hvm eq_refl) as U.
      rewrite En in U. lia.
    - unfold budget_ok_alloc, limit_ok_alloc in HB. apply acost_pays_map; [exact V0 | lia]. }
  split.
  { apply (pendS_intro A rhoX tp md (with_vmmaps h' md) a (mmap_n len) (secmapsize nv)); try assumption. clear -SMB. lia. }
  split.
  { replace (with_vmmaps h' md) with (with_vm (mkVmState h' (m_vm_lazy md) (m_vm_materialized md)) md) by (destruct md; reflexivity). apply HKc. exact HK. }
  split; [unfold tp_ok in Htp |- *; unfold rho1; rewrite rho_set_rw_other by (apply NEQ; unfold GW; lia); exact Htp|].
  split; [apply (HUS rhoX rho1); [eapply agree_below_le; [|exact Hag1]; unfold GW, NF; lia | exact HU]|].
  split; [exact Hnv|].
  split; [|exact HB].
  unfold top_high in Htop |- *. unfold rho1. rewrite !rho_set_rw_other by (apply NEQ; unfold GW, V_DEPTH; lia). exact Htop.
Qed.

Lemma secmapsize_bounds : ltac2:(tb__ "0|1|
S0S4Zfc01R1A2S1S1S4Z12000S29R2A1M0A2S4G0S5R2Z3007A2A2A2S2S0S8G0S2cA2Z0A3A2F_;Fnv;").
Proof.
  intros nv Hn. unfold secmapsize, secneeded, round_up, PG.
  pose proof (Z.div_mod (nv + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nv + 8 - 1) 8 ltac:(lia)).
  set (r8 := (nv + 8 - 1) / 8 * 8).
  pose proof (Z.div_mod (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 4096 + 4096 - 1) 4096 ltac:(lia)).
  split; [lia|]. rewrite Z.add_mod, Z_mod_mult by lia. reflexivity.
Qed.

Lemma SHC_pays : ltac2:(tb__ "0|0|
S0S0S4Z0R2A2S4Zfc01R2A2S4S5S5S25R4A1S29R3A1A2S63R3A1A2S25S5R4R3A2A1A2F_;F_;Fnv;FV;").
Proof.
  intros V nv HV Hn. pose proof (acost_step' V nv HV ltac:(lia)) as AS. pose proof (secmapsize_bounds nv Hn) as [B _].
  unfold SHC, PG. pose proof (Z.div_mod (secmapsize nv) (8 * 4096) ltac:(lia)). pose proof (Z.mod_pos_bound (secmapsize nv) (8 * 4096) ltac:(lia)). lia.
Qed.

Lemma JGsC_grant : ltac2:(tb__ "0|3|
S35S5dS22S22S18S20Q40M0A1M1A1S18S11A1SeG1G1G1G1S2aVW;Vst;A2S5eRbA1S67VW;Vst;RdRcRbRaR9R8R7A9S54Vsegs;R8RaA3S1fG0S23RdPcA2A2S0S1S4Zfc01R1A2S6R1S9Z2Z27A2A2A2S2S0S59R9A1S29R2A1A3S5aR9R8RcRaRbA5S2S1bS68S56S55VW;Vst;Vtmax;A3M2A2S1cA3S64R14R13R12RdS5cR11G2RdA3R10RfS17S5bSdReA1RcRdA3ReA2A8F_;F_;F_;F_;Tnv;F_;F_;F_;F_;Fflags;Faddr;Flen;Fa;Fmd;Ftr;Ftp;FrhoX;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoX tp tr md a len addr flags HUS HKc HJG HMI nv Hnv HnZ Hpl Hnx.
  split; [exact (JGs_grant A Kc rho rhoX tp tr md a len addr flags HUS HKc HJG HMI Hnv HnZ Hpl Hnx)|].
  destruct HJG as [Hag HJ]. pose proof Hag as (Hagw & _ & _). destruct HJ as (HA & _ & _ & _ & HB & _).
  pose proof HA as (_ & _ & _ & _ & HM & _). pose proof HM as (_ & V2 & _ & V0 & _ & _ & V7 & L1 & _).
  assert (E12 : rw rhoX 12%positive = rw rho 12%positive) by (rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity).
  cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
  destruct (mmap_nw (m_vmmaps md) a len (proj1 (proj2 (proj2 Hpl)))) as [En Etop]. rewrite HnZ in En, Etop.
  set (h' := mmap_rw_vm (m_vmmaps md) len a).
  assert (Hvm : vm_maps h' = (a, mmap_n len) :: vm_maps (m_vmmaps md)) by reflexivity.
  rewrite paid_with_vmmaps.
  pose proof (used_maps_cons_le md h' a (mmap_n len) (MI_ivs_wf segs _ _ HMI) ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite En; exact Etop) Hvm eq_refl) as U.
  rewrite En in U.
  pose proof (SHC_pays (aa_V A) nv V0 ltac:(lia)) as SP.
  unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpV]. fold nv. set (pcr := PrimCredit.prim_credit A) in *. clearbody pcr. clear -V2 U SP. lia.
Qed.
End JGS.
End SecOKInv.

