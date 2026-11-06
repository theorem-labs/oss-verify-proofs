(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9 ig.
From Stdlib Require NArith PArith FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From stdpp Require list.

(* [comment removed for export] *)
Module SegQIP.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "list"; "nil"; "false"; "pair"; "prod"; "Some"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "jpredA"; "stableA_mono"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "agree_below"; "ss_next"; "ss_lenient"; "ss_facts"; "rw"; "sprop"; "SLit"; "SPBranch"; "sprop_below"; "sprop_eqb"; "SPNot"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "sdiff"; "one_at"; "JQ"; "entsI"; "two_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states"; "PreQIP"; "PostQIP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states"; "NXI"; "dI0"; "dI1a"; "dI1b"; "dI2"; "dI3"; "dI4"; "dI5"; "dI6"; "MSENTQ"; "PSENT"; "QCENTI"; "QI0"; "QI1"; "QI2"; "QI3"; "vCLS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_CLS"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_GEU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side"; "QI_side"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQIP"; "le_NPRE_240"; "le_NPRE_242"; "le_NPRE_NXI"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side.
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
S1S6S19A1S10U12cS4SdS44S4SdZ3e7d0S7SdA1A3A3S36Vvb;A1A3Vrun0;A3").
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
S1S6S19A1S10U12cS4SdS45S4SdZ3e7d0S4SdZ3e9a4S4SdZ3e998S7SdA1A3A3A3A3VC0;A3Vrun1;A3").
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
S1S6S19A1S10U258S4SdS47S4SdZ3e9acS4SdZ3e9d0S4SdZ3e8d0S7SdA1A3A3A3A3VC2;A3Vrun3;A3").
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
S1S6S19A1S10U320S4SdS42S4SdZ3e9acS7SdA1A3A3VC3;A3Vrun4;A3").
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
S1S6S19A1S10U320S4SdS41S4SdZ3e8d0S4SdZ5fbd8S4SdZ5fbb8S4SdZ5fbf8S4SdZ5fc18S4SdZ5fb98S7SdA1A3A3A3A3A3A3A3VC4;A3Vrun5;A3").
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
S1S6S19A1S10U320S4SdS43S4SdZ3e94cS4SdZ3e96cS7SdA1A3A3A3VT5f;A3Vrun6;A3").
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
  intros rhoC Hag. apply (run_cont1 800%nat [QCENTI; 0x3e94c; 0x3e96c] T5f run6 240 E6 (proj2 nxT5f) (proj1 nxT5f) run6_eq E6_def QCENTI J ok rhoC tp Q chk6 HOK ST240).
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
  intros rhoC Hag. apply (run_cont1 800%nat [MSENTQ; 0x3e8d0; 0x5fbd8; 0x5fbb8; 0x5fbf8; 0x5fc18; 0x5fb98] C4 run5 NXI E5 (proj2 nxC4) (proj1 nxC4) run5_eq E5_def MSENTQ J ok rhoC tp Q chk5 HOK ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_cont J ok E5 C5 dI5 rhoL tp Q sd5); [| exact C5_def | apply from_C5; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI5 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DB))))))) HagR HD5).
Qed.

Lemma from_C3 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS0Vok;S11S0VJ;VC3;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 800%nat [PSENT; 0x3e9ac] C3 run4 NXI E4 (proj2 nxC3) (proj1 nxC3) run4_eq E4_def PSENT J ok rhoC tp Q chk4 HOK ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_cont J ok E4 C4 dI4 rhoL tp Q sd4); [| exact C4_def | apply from_C4; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI4 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 DB)))))) HagR HD4).
Qed.

Lemma from_C2 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S2aS0Vok;S11S0VJ;VC2;R2Vtp;A5VQ;A4F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_cont1 600%nat [QI3; 0x3e9ac; 0x3e9d0; 0x3e8d0] C2 run3 NXI E3 (proj2 nxC2) (proj1 nxC2) run3_eq E3_def QI3 J ok rhoC tp Q chk3 HOK ST200).
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
  intros rhoC Hag. apply (run_cont2 300%nat [QI1; 0x3e7d0; 0x3e9a4; 0x3e998] C0 run1 NPRE E1a E1b (proj2 nxC0) (proj1 nxC0) run1_eq E1a_def E1b_def QI1 J ok rhoC tp Q chk1 HOK HST).
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
  apply (run_cont1 300%nat [QI0; 0x3e7d0] (PreQIP vb) run0 NPRE E0 (proj2 (proj2 (proj2 (preQIP_wf vb)))) (proj1 (proj2 (proj2 (preQIP_wf vb)))) run0_eq E0_def QI0 J ok rho tp Q chk0 HOK HST).
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
  intros rhoC Hag. apply (run_econt1 800%nat [QCENTI; 0x3e94c; 0x3e96c] T5f run6 240 E6 (proj2 nxT5f) (proj1 nxT5f) run6_eq E6_def QCENTI J rhoC tp Q chk6 ST240).
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
  intros rhoC Hag. apply (run_econt1 800%nat [MSENTQ; 0x3e8d0; 0x5fbd8; 0x5fbb8; 0x5fbf8; 0x5fc18; 0x5fb98] C4 run5 NXI E5 (proj2 nxC4) (proj1 nxC4) run5_eq E5_def MSENTQ J rhoC tp Q chk5 ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_econt J E5 C5 dI5 rhoL tp Q sd5); [| exact C5_def | apply efrom_C5; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI5 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DB))))))) HagR HD5).
Qed.

Lemma efrom_C3 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S0S11S0VJ;VC3;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 800%nat [PSENT; 0x3e9ac] C3 run4 NXI E4 (proj2 nxC3) (proj1 nxC3) run4_eq E4_def PSENT J rhoC tp Q chk4 ST200).
  intros rhoL HagL. pose proof (agree_below_trans _ _ _ _ Hag (agree_below_le _ _ _ _ le_NPRE_NXI HagL)) as HagR.
  apply (restate_econt J E4 C4 dI4 rhoL tp Q sd4); [| exact C4_def | apply efrom_C4; exact HagR].
  exact (diffs_ok_agree NPRE rho rhoL dI4 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 DB)))))) HagR HD4).
Qed.

Lemma efrom_C2 : ltac2:(tb__ "0|0|
S1bS1cSfVrho;R1A3S29S0S11S0VJ;VC2;R2Vtp;A5VQ;A3F_;FrhoC;").
Proof.
  intros rhoC Hag. apply (run_econt1 600%nat [QI3; 0x3e9ac; 0x3e9d0; 0x3e8d0] C2 run3 NXI E3 (proj2 nxC2) (proj1 nxC2) run3_eq E3_def QI3 J rhoC tp Q chk3 ST200).
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
  intros rhoC Hag. apply (run_econt2 300%nat [QI1; 0x3e7d0; 0x3e9a4; 0x3e998] C0 run1 NPRE E1a E1b (proj2 nxC0) (proj1 nxC0) run1_eq E1a_def E1b_def QI1 J rhoC tp Q chk1 HST).
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
  apply (run_econt1 300%nat [QI0; 0x3e7d0] (PreQIP vb) run0 NPRE E0 (proj2 (proj2 (proj2 (preQIP_wf vb)))) (proj1 (proj2 (proj2 (preQIP_wf vb)))) run0_eq E0_def QI0 J rho tp Q chk0 HST).
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
Module UnwT_glue2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "cell"; "mkCell"; "ob_cells"; "rm"; "dflt_writable"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_objs"; "valuation"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "Some"; "pair"; "app"; "bool"; "cons"; "nil"; "option"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "rd64"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "add"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "drop_lastA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJAF TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Hypothesis HTOP : InitState.segs_top segs <= IMG_HI.

Lemma dissolve_link_same : ltac2:(tb__ "0|6|
S1dS28S10S1A1M0S1S2S2SeS10S2bQ40A1A1S10S26A1M1S24S25S0G0SdS27RaA1A1S13S1R9S15S1R8S16S1A1A3A3A3S0S2ScR9A1S3N10A1M2A3S0S2SbRaA1S3Z0A1A3S0S14S8SaRbA1A1S18A3S1fS4S5G2Z8M3RbA3S6RcA1A3S1fS4S5S3N8A1G3RbA3S6RdA1A3S19RbS9ReA1A2SfS20S22S2aZ10M4A2R1A2S20R2S23Z2Z3eA2A2S0S17SfA1M5S1eS7ReA1S21R3G4A2A2S11SfS19ReR10A2A2A3S0G5S1eS7RfA1S21R4G3A2A2S11SfS19RfR10A2A2A3S1cVsegs;R16R15R10RfS12G1S1aReS1bRdRcA2A4A6S1cVsegs;R17S29R16R15A2R11R10S12G1S1aRfS1bReRdA2A4A6F_;F_;F_;F_;F_;TB;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fv1;Fv0;Fo;Fobjs;FA;FJ;").
Proof using HTOP.
  intros J A objs o v0 v1 rho tp tr ms md Hobjs Hl Hh Hdw Hc0 Hc1 B HBlo HBhi R0 R1 HS.
  assert (Sm16 : soff rho (SLit (-16)) = -16) by (apply soff_lit_small; lia).
  assert (S0 : soff rho (SLit 0) = 0) by (apply soff_lit_small; lia).
  assert (ER : obj_range rho o = (B - 16, B)).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hl, Hh, Sm16, S0. fold (uval rho (ob_base o)). fold B. f_equal; lia. }
  destruct (released_bytesA segs HTOP rho A objs [o] o tp tr ms md Hobjs ltac:(left; reflexivity) (proj1 HS) Hdw
              ltac:(rewrite ER; cbn [fst]; lia) ltac:(rewrite ER; cbn [snd]; lia)) as (_ & CELLS).
  set (rho' := rho_absorb rho [o] (vms md tp ms)) in *.
  assert (Erm : forall a, rm rho' a = rm rho a).
  { intros a. unfold rho', rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho [o] a) as [Hin|Hnin]; [|reflexivity].
    fold (rho_absorb rho [o] (vms md tp ms)).
    assert (Ha : B - 16 <= bv_unsigned a < B).
    { destruct Hin as (o' & [<-|[]] & Hr). rewrite ER in Hr. cbn [fst snd] in Hr. exact Hr. }
    assert (E : rm rho' a = rm rho a).
    { rewrite <- (Z_to_bv_bv_unsigned 64 a).
      destruct (Z_lt_dec (bv_unsigned a) (B - 8)) as [L|L].
      - apply (rd64_bytes_eq (rm rho') (rm rho) (B - 16) (uval rho v0)); [|exact R0 | lia].
        pose proof (CELLS (-16) v0 Hc0 ltac:(lia)) as C0. fold (uval rho (ob_base o)) in C0. fold B in C0. replace (B + -16) with (B - 16) in C0 by lia. exact C0.
      - apply (rd64_bytes_eq (rm rho') (rm rho) (B - 8) (uval rho v1)); [|exact R1 | lia].
        pose proof (CELLS (-8) v1 Hc1 ltac:(lia)) as C1. fold (uval rho (ob_base o)) in C1. fold B in C1. replace (B + -8) with (B - 8) in C1 by lia. exact C1. }
    unfold rho', rho_absorb in E. cbn [rm] in E. destruct (in_ranges_dec rho [o] a) as [_|Hn]; [exact E | exfalso; exact (Hn Hin)]. }
  assert (Erho : rho' = rho).
  { unfold rho', rho_absorb. destruct rho as [w l m]. cbn [rw rl rm] in *. f_equal. apply functional_extensionality. intros a.
    exact (Erm a). }
  pose proof (SPA_unobj segs J rho A objs [o] tp tr ms md Hobjs HS) as SP. cbv zeta in SP. fold rho' in SP.
  rewrite Erho in SP. unfold drop_lastA. apply SP. intros H. exact H.
Qed.
End WithSegs.
End UnwT_glue2.

(* [comment removed for export] *)
Module UnwT_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "app"; "pair"; "prod"; "None"; "false"; "list"; "Some"; "option"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SVar"; "SLit"; "sobj"; "SPUle"; "SAlu"; "cell"; "SPBranch"; "FcsrFrm0"; "mkCell"; "mkSS"; "SPNot"; "ss_facts"; "ss_pc"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "la_state"; "axst"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "vSZt"; "LOOPH"; "vFRt"; "FACTS_T"; "LOOPX"; "PreDv"; "FACTS_Tg"; "F_ext"; "LH1"; "atpc"; "norm_win"; "sDv_of"; "EX"; "EX_of"; "EX_ofg"; "F_loop"; "F_szv"; "LH0"; "LT"; "LT_of"; "LT_ofg"; "P0T"; "P0T_g"; "PostDv"; "RDv_of"; "S1cT_of"; "SZT"; "runT1"; "runT2"; "runT4"; "trace_offs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "DUMMY"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "map_objsF"; "on_obj"; "set_factsF"; "CASX"; "VFACT"; "add_cellsF"; "drop_cellsF"; "updrF"; "F_cas"; "RT_f"; "VOBJ"; "W_full"; "optR"; "@Corelib.Init.Logic"; "eq"; "not"; "@Corelib.Lists.ListDef"; "nth"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "A_globals"; "mkA"; "AE_A"; "V_FREE_A1"; "ae_free"; "free_depth"; "pre_facts"; "stack_win"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SRL"; "BC_EQ"; "BC_GEU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "F_geom_fn"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "F_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "tol_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "F_D"; "O_trD"; "RT_D"; "v12"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "@Stdlib.Lists.List"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "add"; "eqb"; "mul"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue.
Import ListNotations.
Open Scope Z_scope.

Definition LOOPH : Z := 0x7f430.
Definition LOOPX : Z := 0x7f46c.

Definition pFR : positive := 200%positive.
Definition vFRt : sv := SVar pFR.
Definition vSZt : sv := SVar 201.

Definition FACTS_Tg (khi : bool) (VF : list sprop) : list sprop := ltac2:(tb__ "0|0|
S3ScS3ScS3ScS3ScS3ScS71S5dS5cA1A3S6cA3S70Vkhi;A1A3S4cA3VVF;A3").
Definition P0T_g (khi : bool) (VOBJl : list sobj) (VF : list sprop) : axst := ltac2:(tb__ "0|1|
S58S17S5bS59A1S67S66S0S5S1SdA2M0S4S1SdU4SfS6fA1A4S0G0S4S1SdUbSeS5aA1A4S2G0A1A3A3A2S65S15S6SdA1S3S10S3S10S0S10S4fS57A3S4dA3VVOBJl;A3S27Vkhi;VVF;A2S6dS7A9S2S5SdSdA2A1A2").
Definition FACTS_Tc (khi : bool) (q : qvar) : list sprop := ltac2:(tb__ "0|0|
S27Vkhi;S48Vq;A1A2").
Definition P0T_c (khi : bool) (q : qvar) : axst := ltac2:(tb__ "0|0|
S37Vkhi;S4eVq;A1S48Vq;A1A3").
Definition FACTS_T (q : qvar) : list sprop := FACTS_Tc true q.
Definition P0T (q : qvar) : axst := P0T_c true q.
Definition atpc (pc : Z) (l : list leafA) : list leafA := ltac2:(tb__ "0|0|
S77S1cS1cS79S1aS1dS1eR1A1A1A1Vpc;A2LL;Vl;A3").

Definition runT1 (q : qvar) : list leafA := ltac2:(tb__ "0|0|
S40S43S0S1bS22S0S1bS47S2S1bA1A3A3S36Vq;A1A3").
Definition LH0 (q : qvar) : axst := ltac2:(tb__ "0|0|
S1eS53S1cU0S2aS22S3cVq;A1A2S41A4A1").
Definition runT2 (q : qvar) : list leafA := ltac2:(tb__ "0|0|
S40S43S0S1bS22S0S1bS25S2S1bA1A3A3S32Vq;A1A3").
Definition LH1 (q : qvar) : axst := ltac2:(tb__ "0|0|
S1eS53S1cU0S2aS22S3dVq;A1A2S41A4A1").

Definition trace_offs : list Z := ltac2:(tb__ "0|0|
S54S1S1bS1S78N840S7aZ8S7bR1A1A2A2Lk;S55U1U1dA2A4").
Definition F_loop : list sprop := ltac2:(tb__ "0|2|
S0ScS11S12S5fSePaA1SfZ10A1A3S23A2S0ScS14S62S12S60S23SfZ7A1A3SfZ0A1M0A3S0ScS18S14S63S23S12S5fSeP99A1M1SfN10A1A3A3A1S0ScS11SfZ1A1S21A2S0ScS11S21SfZ1eA1A2S0ScS14S64S12S61G1SfZcA1A3G0A3S2ScA1A3A3A3A3A3A3").
Definition F_ext : list sprop := ltac2:(tb__ "0|0|
S0ScS11SfZ1A1S21A2S0ScS11S21SfZ1eA1A2S2ScA1A3A3").
Definition norm_win (o : sobj) : sobj := ltac2:(tb__ "0|1|
S49S0S13S16SfN848M0A1Z4S21A3S2S13A1A3S4aS0S1bG0S3fA3Vo;A2A2").

Definition LT_ofg (L1 : axst) (F0 : list sprop) : axst := ltac2:(tb__ "0|1|
S46S44S4bVL1;S22S0S5S1SdA2M0S4S1SdUcS23A4S0G0S4S1SdUfS21A4S0G0S4S1SdU10SePcaA1A4S0G0S4S1SdU11SePcbA1A4S2G0A1A3A3A3A3A3S45SePaA1SeS56A1S2bA3A2S3ScVF0;S30A3A2").
Definition LT_of (L1 : axst) (q : qvar) : axst := ltac2:(tb__ "0|0|
S35VL1;S24Vq;A1A2").

Definition EX_ofg (L1 : axst) (F0 : list sprop) : axst := ltac2:(tb__ "0|1|
S46S44S4bVL1;S25S0S5S1SdA2M0S4S1SdUcSePceA1A4S0G0S4S1SdUfSePcfA1A4S0G0S4S1SdU10SePcaA1A4S0G0S4S1SdU11SePcbA1A4S2G0A1A3A3A3A3A3S45SePaA1SeS56A1S2bA3A2S3ScVF0;S28A3A2").
Definition EX_of (L1 : axst) (q : qvar) : axst := ltac2:(tb__ "0|0|
S2fVL1;S24Vq;A1A2").
Definition LT (q : qvar) : axst := ltac2:(tb__ "0|0|
S34S29Vq;A1Vq;A2").
Definition EX (q : qvar) : axst := ltac2:(tb__ "0|0|
S2eS29Vq;A1Vq;A2").

Definition runT3 (q : qvar) : list leafA := ltac2:(tb__ "0|0|
S40S43S0S1bS22S0S1bS25S2S1bA1A3A3S76S33Vq;A1S23A2A3").

Definition runT4 (q : qvar) : list leafA := ltac2:(tb__ "0|0|
S40S43S0S1bS47S2S1bA1A3S2dVq;A1A3").
Definition S1cT_of (L1 : axst) (facts0 : list sprop) : axst := ltac2:(tb__ "0|1|
S46S44VL1;S45SePaA1SeS56A1S10S49S0S13S16SfN848M0A1Z4S21A3S2S13A1A3S4aS0S1bG0S0S1bN840S0S1bN838S0S1bN830S0S1bN828S2S1bA1A3A3A3A3A3R1A2A2Lo;A3A2Vfacts0;A2").
Definition S1cT (q : qvar) : axst := ltac2:(tb__ "0|0|
S3aS1eS53S1cU0S3eVq;A1S41A4A1S3ScS24Vq;A1S28A3A2").

Definition SZT : Z := 30.
Definition F_szv : list sprop := ltac2:(tb__ "0|1|
S0ScS11SfZ1A1SePdA1M0A2S0ScS11G0SfS3bA1A2S2ScA1A3A3").
Definition PreDv : axst := ltac2:(tb__ "0|1|
S58S17Z7e9e4S67S66S0S5S1SdA2M0S4S1SdUaS75A4S2G0A1A3A2S65S15S6SdA1S3S10S0S10S5eS0S10S73S2S10A1A3A3S3S10S57S74A3A3S3ScS72S31A3S42S7A9S2S5SdSdA2A1A2").
Definition PostDv : axst := PostD 1.
Definition sDv_of (ED : axst) : wsub := ltac2:(tb__ "0|0|
S68P1S1dVED;A1S1dS26A1A3").
Definition RDv_of (ED : axst) : list sobj := ltac2:(tb__ "0|0|
S50S6aVED;S26S2cVED;A1A3A1").
Definition TDv_of (ED : axst) : axst := ltac2:(tb__ "0|0|
S69S6bS2cVED;A1S26S38VED;S39VED;A1A5S19S1dVED;A1A1A2").

Lemma runT_some : ltac2:(tb__ "0|1|
S1S8S1bA1S1fS8S1cA1M0S51G0S40R4R3R2A3R1A3S52S51G0R2S2S1cA1A3A1S51SaG0A1S20S6eR6R5R4SbA5S9G0R3A2A3F_;F_;Fl;FA;Fcuts;Ffuel;").
Proof.
  intros fuel cuts A l H Hne. unfold runA in H. destruct (sym_runA segsA fuel cuts A true) as [l'|]; [congruence|]. subst. exfalso. apply Hne. reflexivity.
Qed.
End UnwT_states.

(* [comment removed for export] *)
Module SegQ3DM.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "bool"; "list"; "true"; "app"; "false"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "vmap"; "chkNM"; "keepsM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "SVar"; "sobj"; "sprop"; "sv"; "SLit"; "SPBranch"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "JOK"; "@Corelib.Init.Logic"; "eq"; "and"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM"; "MC"; "MI"; "MRET"; "TsD0M"; "TsDBM"; "TsRCM"; "TsRIM"; "MB"; "MT4"; "PostQ3R0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "PD"; "NXR"; "O_mtx00"; "RETR"; "STK"; "SWD"; "cb_cells"; "mkR"; "post_ruR"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "DH"; "DI"; "DQCs"; "DQIs"; "DTs"; "RC"; "RI"; "DH0"; "DHn"; "PostQ3Rs"; "TsDB"; "TsRI"; "runD0"; "runDB"; "runDI"; "runDT"; "runRC"; "runRI"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "DEPTH_R"; "O_gmax"; "regs3"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM.
Import ListNotations.
Open Scope Z_scope.

Definition PostQ3R0 : axst := ltac2:(tb__ "0|2|
S33S2fS49S4eS34A2S7S12S30S32S31S11Pa0A1M0S11Pa1A1S11Pa2A1S11Pa3A1A4A2S0S12S2eS0S12S4dS2S12A1M1A3A3A3G1S7S13S4aS4cA1S0S13S16S48G0S15Z0A1A3S2S13A1A3A3S2dA6").
Definition MRET : vmap := ltac2:(tb__ "0|2|
S0S3S9S14A2M0S1S9S14Pa0S11Pb8A1A4S0G0S1S9S14Pd0M1S11G1A1A4S2G0A1A3A3").
Definition MT4 : vmap := ltac2:(tb__ "0|0|
S21S0S9Pb8S0S9Pb9S0S9PbaS0S9PbbS0S9Pd0S2S9A1A3A3A3A3A3A1").
Definition MB : vmap := ltac2:(tb__ "0|0|
S21S0S9Pa0S0S9Pa1S0S9Pa2S0S9Pb8S0S9Pb9S0S9PbaS0S9PbbS0S9Pd0S2S9A1A3A3A3A3A3A3A3A3A1").
Definition MI : vmap := ltac2:(tb__ "0|0|
S21S0S9Pa0S0S9Pa1S0S9Pa2S0S9Pa3S0S9Pa4S0S9Pa5S0S9Pa6S0S9Pb8S0S9Pb9S0S9PbaS0S9PbbS0S9Pd0S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A1").
Definition MC : vmap := ltac2:(tb__ "0|0|
S21S0S9Pa6S0S9Pb8S0S9Pb9S0S9PbaS0S9PbbS0S9Pd0S2S9A1A3A3A3A3A3A3A1").

Definition TsD0M : list (axst * vmap) := ltac2:(tb__ "0|1|
S0S3SaScA2M0S1SaScS2bS24A4S0G0S1SaScS3dS2aA4S2G0A1A3A3").
Definition TsDBM : list (axst * vmap) := ltac2:(tb__ "0|0|
S35SaS3SaScA2SaS1SaScR1S29A4LT;S40A4").
Definition TsRIM : list (axst * vmap) := ltac2:(tb__ "0|0|
S35SaS3SaScA2SaS1SaScR1S23A4LT;S41A4").
Definition TsRCM : list (axst * vmap) := ltac2:(tb__ "0|1|
S0S3SaScA2M0S1SaScS3eS22A4S0G0S1SaScS3fS24A4S2G0A1A3A3").
Lemma chkD0M : ltac2:(tb__ "0|0|
S1dS4SdS10SbS2cA1A1S42S25A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkDBM : ltac2:(tb__ "0|0|
S1dS4SdS10SbS36A1A1S43S26A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkDIM : ltac2:(tb__ "0|1|
S1dS4SdS10SbS37A1A1S44S0S3SaScA2M0S1SaScS39S23A4S2G0A1A3A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkRIM : ltac2:(tb__ "0|0|
S1dS4SdS10SbS3cA1A1S47S28A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkDTM : ltac2:(tb__ "0|1|
S1dS4SdS10SbS3aA1A1S45S0S3SaScA2M0S1SaScS38S22A4S2G0A1A3A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkRCM : ltac2:(tb__ "0|0|
S1dS4SdS10SbS3bA1A1S46S27A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma nxPD : ltac2:(tb__ "0|1|
S1eS1dS4S17SbS2cA1M0A1S8A3S4fS4bS10G0A1A2A2"). Proof. exact (proj1 nxsD). Qed.

Section TR.
Context {Q : assn} (X : trk Q).
Theorem seg_D_D0M : ltac2:(tb__ "0|0|
S19SfS5S20Q40A1A1S1cVQ;VX;R3A3SaScSfS1fS3SaScA2S1SaScR3R2A4S25A3SeR3R7R2A3S1bVQ;VX;S18S1aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S1bVQ;VX;S18S1aR5S2cR4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 300%nat _ PD runD0 TsD0M runD0_eq chkD0M (proj1 nxPD) (proj2 nxPD) J rho tp HJ HC). Qed.
Theorem seg_D_DBM : ltac2:(tb__ "0|0|
S19SfS5S20Q40A1A1S1cVQ;VX;R3A3SaScSfS1fS3SaScA2S1SaScR3R2A4S26A3SeR3R7R2A3S1bVQ;VX;S18S1aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S1bVQ;VX;S18S1aR5S36R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 300%nat _ DH runDB TsDBM runDB_eq chkDBM (proj1 (proj1 (proj2 nxsD))) (proj2 (proj1 (proj2 nxsD))) J rho tp HJ HC). Qed.
Theorem seg_D_DIM : ltac2:(tb__ "0|1|
S19SfS5S20Q40A1A1S1cVQ;VX;R3A3SaScSfS1fS3SaScA2M0S1SaScR3R2A4S0G0S1SaScS39S23A4S2G0A1A3A3SeR3R7R2A3S1bVQ;VX;S18S1aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S1bVQ;VX;S18S1aR5S37R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 100%nat _ DI runDI [(DQIs, MI)] runDI_eq chkDIM (proj1 (proj1 (proj2 (proj2 nxsD)))) (proj2 (proj1 (proj2 (proj2 nxsD)))) J rho tp HJ HC). Qed.
Theorem seg_D_RIM : ltac2:(tb__ "0|0|
S19SfS5S20Q40A1A1S1cVQ;VX;R3A3SaScSfS1fS3SaScA2S1SaScR3R2A4S28A3SeR3R7R2A3S1bVQ;VX;S18S1aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S1bVQ;VX;S18S1aR5S3cR4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 100%nat _ RI runRI TsRIM runRI_eq chkRIM (proj1 (proj1 (proj2 (proj2 (proj2 nxsD))))) (proj2 (proj1 (proj2 (proj2 (proj2 nxsD))))) J rho tp HJ HC). Qed.
Theorem seg_D_DTM : ltac2:(tb__ "0|1|
S19SfS5S20Q40A1A1S1cVQ;VX;R3A3SaScSfS1fS3SaScA2M0S1SaScR3R2A4S0G0S1SaScS38S22A4S2G0A1A3A3SeR3R7R2A3S1bVQ;VX;S18S1aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S1bVQ;VX;S18S1aR5S3aR4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 100%nat _ DTs runDT [(DQCs, MC)] runDT_eq chkDTM (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 nxsD)))))) (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 nxsD)))))) J rho tp HJ HC). Qed.
Theorem seg_D_RCM : ltac2:(tb__ "0|0|
S19SfS5S20Q40A1A1S1cVQ;VX;R3A3SaScSfS1fS3SaScA2S1SaScR3R2A4S27A3SeR3R7R2A3S1bVQ;VX;S18S1aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S1bVQ;VX;S18S1aR5S3bR4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 300%nat _ RC runRC TsRCM runRC_eq chkRCM (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 nxsD)))))) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 nxsD)))))) J rho tp HJ HC). Qed.
End TR.
End SegQ3DM.

(* [comment removed for export] *)
Module F0A_laws.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "sub"; "modulo"; "lt"; "mul"; "div"; "leb"; "eqb"; "shiftr"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Datatypes"; "app"; "list"; "pair"; "prod"; "bool"; "true"; "andb"; "Some"; "false"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "qbatch"; "aa_geom"; "ag_spacebeg"; "aa_cls"; "ageom"; "class_state"; "cs_empty"; "sec_chunk"; "aa_q_global"; "aa_q_thread"; "cs_cache"; "qb_addr"; "aa_sec"; "cs_allocated_user"; "sc_map_beg"; "sc_map_size"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "cls_fits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "rz"; "ClassID"; "Size"; "is_primary"; "region_beg"; "needed"; "kQuarantineBatchSize"; "kMaxSize"; "kSpaceSize"; "round_up"; "@stdpp.base"; "NoDup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "nthZ"; "live_ids"; "fs_footb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "maskv"; "view"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model RtCells SegQ_defs Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom.
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
Module SegQ3M_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "bool"; "prod"; "nil"; "true"; "list"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "SVar"; "ss_next"; "valuation"; "SPBranch"; "SPNot"; "ss_lenient"; "swf"; "SAlu"; "SMd"; "DUnknown"; "cell"; "mkCell"; "mkObj"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "leafA"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "vmap"; "chkNM"; "keepsM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "ZQ"; "OH"; "mkR"; "NXR"; "vXK"; "vXL"; "F_R"; "LEXIT"; "LHEAD"; "MERGE"; "SW"; "regsM"; "regsR"; "spR"; "sw_cells"; "vXF"; "vXS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "JOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "add"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3M_states"; "MCUTS"; "MC"; "MG"; "MH"; "PM1"; "vMCC"; "vMCS"; "vMNC"; "vMN"; "O_hb"; "SWMe"; "VM"; "objsM"; "regsMH"; "vMC"; "F_MG"; "F_MH"; "MCOPY"; "MHEAD"; "MMRG"; "MRET2"; "SWM"; "TsM0"; "TsMC"; "TsMG"; "TsMH"; "runM0"; "runMC"; "runMG"; "runMH"; "vSRC"; "LM0"; "LMC"; "LMG"; "LMH"; "O_dst"; "O_src"; "O_tlk"; "VM0"; "VMc"; "endC"; "junk_m"; "regsMC"; "regsMG"; "spM"; "swm_cells"; "vCPV"; "vDST"; "vMNN"; "vMNS"; "vMX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "vGN"; "vGS"; "vGF"; "O_gq"; "QG"; "vGB"; "DEPTH_R"; "NX3"; "cbC"; "vMIN"; "vSTKq"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM"; "idm"; "@Stdlib.Lists.List"; "In"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_SLL"; "BC_GEU"; "M_MUL"; "ALU_SRL"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "pre_facts"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition MHEAD : Z := 0x3e4e0.
Definition MCOPY : Z := 0x3e518.
Definition MMRG : Z := 0x3e52c.
Definition MRET2 : Z := 0x3e36c.
Definition spM : sv := add (SVar 10) (SLit (-96)).
Definition vMC := SVar 160. Definition vMCS := SVar 161. Definition vMCC := SVar 162.
Definition vMN := SVar 163. Definition vMNN := SVar 164. Definition vMNS := SVar 165. Definition vMNC := SVar 166. Definition vMX := SVar 167.
Definition vSRC := SVar 169. Definition vDST := SVar 170. Definition vCPV := SVar 188.

Definition swm_cells (tk tf tl ts : sv) : list cell := ltac2:(tb__ "0|0|
S0S18S19SbN58A1Z8SbS53A1A3S34Vtk;Vtf;Vtl;Vts;A4A3").
Definition SWM (tk tf tl ts : sv) : sobj := ltac2:(tb__ "0|0|
S1aSePaA1SbNa8A1SbZ0A1S6cVtk;Vtf;Vtl;Vts;A4S17A5").
Definition SWMe (e : bool) : sobj := ltac2:(tb__ "0|0|
S3ScLe;Ve;S54S2aS35S2bS36A4S54S26S26S26S26A4X3x2").
Definition O_hb (vb : sv) (n s c : sv) : sobj := ltac2:(tb__ "0|4|
S89Vvb;Z0M0Z18S0S4S4S1cS2A2M1SaA2M2S1G1SaS1S1cS2G0U8M3A4Vn;A4S0G2S1G1SaS1S1cS2Z8G3A4Vs;A4S0G2S1G1SaS1S1cS2Z10G3A4Vc;A4S5G2A1A3A3A3A4").
Definition O_tlk (v : sv) : sobj := ltac2:(tb__ "0|3|
S89S2bZ0M0Z8S0S4S4S1cS2A2M1SaA2M2S1G1SaS1S1cS2G0U8A4Vv;A4S5G2A1A3A4").
Definition O_src : sobj := ltac2:(tb__ "0|3|
S89S5dZ0M0Z8S0S4S4S1cS2A2M1SaA2M2S1G1SaS1S1cS2G0U8A4S6dA4S5G2A1A3A4").
Definition O_dst (cells : list (Z * nat * sv)) : sobj := carved vDST 0 8 cells.
Definition endC : sv := ltac2:(tb__ "0|0|
S3dS3dS47SbZ18A1A2S15S83S46SbZ3A1A3A2").
Definition junk_m : list (nat * sv) := ltac2:(tb__ "0|1|
S0S4S2SaA2M0S1S2SaU6SePacA1A4S0G0S1S2SaU7SePadA1A4S0G0S1S2SaUdSePb0A1A4S0G0S1S2SaU1cSePb4A1A4S0G0S1S2SaU1dSePb5A1A4S0G0S1S2SaU1eSePb6A1A4S0G0S1S2SaU1fSePb7A1A4S5G0A1A3A3A3A3A3A3A3").
Definition regsMH : list sv := ltac2:(tb__ "0|2|
S88S32S8S4S2SaA2M0S0G0S1S2SaU1SbS53A1A4S0G0S1S2SaU2S6bA4S0G0S1S2SaU5S47A4S0G0S1S2SaU8SbS8bS76Za0A2A1M1A4S0G0S1S2SaU9S7bA4S0G0S1S2SaUaG1A4S0G0S1S2SaUbS33A4S0G0S1S2SaUcS71A4S0G0S1S2SaUeS4dA4S0G0S1S2SaUfSbZ3fdA1A4S0G0S1S2SaU10SbZffffffffffffe000A1A4S0G0S1S2SaU11SbZ2000A1A4S0G0S1S2SaU12SbS76A1A4S0G0S1S2SaU13S7cA4S0G0S1S2SaU14S7aA4S5G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S68A3A2").
Definition regsMC : list sv := ltac2:(tb__ "0|1|
S88S4cS0S4S2SaA2M0S1S2SaU6S3dS46S44A2A4S0G0S1S2SaU7S5dA4S0G0S1S2SaUdS45A4S0G0S1S2SaU1cS6eA4S0G0S1S2SaU1dS67A4S5G0A1A3A3A3A3A3A2").
Definition regsMG : list sv := ltac2:(tb__ "0|1|
S88S4cS0S4S2SaA2M0S1S2SaU6S3dS46S44A2A4S0G0S1S2SaUdS45A4S5G0A1A3A3A2").

Definition F_MH (e : bool) : list sprop := ltac2:(tb__ "0|2|
S8SdS8aS78A1S8SdS0SdS12S11S82S72SbZ0A1M0A3A1S0SdS12S11S82S15S86S45SbZdA1A3G0A3A1S5SdA1M1A3A3S3S7SdA1Le;Ve;S0SdS12S11S82S2aG0A3A1G1A3G1X3x2A3A3").
Definition F_MG (e : bool) : list sprop := ltac2:(tb__ "0|0|
S8SdS4fVe;A1S0SdS12S11S87SbZ3fdA1S3dS46S44A2A3A1S5SdA1A3A3").
Definition objsM (e : bool) : list sobj := ltac2:(tb__ "0|1|
S8ScS0ScS75S72S74S77S73A4S0ScS48S4dS47S45S44A4S0ScS48S47S6fS70S46A4S5ScA1M0A3A3A3S3S7ScA1Le;Ve;S0ScS64S26A1G0A3G0X3x2A3").

Definition PM1 : axst := ltac2:(tb__ "0|0|
S28S2fS31S27S30S26S26S26S26A4A1S0ScS75S72S74S77S73A4S0ScS48S74S4dS45S44A4S5ScA1A3A3S8SdS2cS0SdS12S11S84S16S85S73SbZ64A1A3S16S85S72SbZ190000A1A3A3A1S0SdS12S11S84S15S83S72SbZdA1A3S73A3A1S5SdA1A3A3A3S79A6").
Definition MH (e : bool) : axst := ltac2:(tb__ "0|0|
S28S51S4cS27S49Ve;A1A1S4bVe;A1S4fVe;A1S29A6").
Definition MC (e : bool) : axst := ltac2:(tb__ "0|0|
S28S50S69S27S49Ve;A1A1S8ScS4bVe;A1S0ScS63S0ScS62S5S4S4S1cS2A2SaA2A1A1S5ScA1A3A3A3S4eVe;A1S29A6").
Definition MG (e : bool) : axst := ltac2:(tb__ "0|0|
S28S52S6aS27S49Ve;A1A1S4bVe;A1S4eVe;A1S29A6").

Definition MCUTS : list Z := ltac2:(tb__ "0|0|
S0S1cS51S0S1cS50S0S1cS52S0S1cS2eS0S1cS2dS5S1cA1A3A3A3A3A3").
Definition runM0 : list leafA := runA 300 MCUTS PM1.
Definition runMH (e : bool) : list leafA := ltac2:(tb__ "0|0|
S3cU190S3fS42Ve;A1A3").
Definition runMC (e : bool) : list leafA := ltac2:(tb__ "0|0|
S3cU64S3fS40Ve;A1A3").
Definition runMG (e : bool) : list leafA := ltac2:(tb__ "0|0|
S3cU190S3fS41Ve;A1A3").
Lemma runM0_eq : ltac2:(tb__ "0|0|
S21S7S20A1S3cU12cS3fS43A3S59A3"). Proof. unfold runM0. reflexivity. Qed.
Lemma runMH_eq : ltac2:(tb__ "0|0|
S3S21S7S20A1S3cU190S3fS42R1A1A3S5cR1A1A3Fe;"). Proof. intros e. unfold runMH. reflexivity. Qed.
Lemma runMC_eq : ltac2:(tb__ "0|0|
S3S21S7S20A1S3cU64S3fS40R1A1A3S5aR1A1A3Fe;"). Proof. intros e. unfold runMC. reflexivity. Qed.
Lemma runMG_eq : ltac2:(tb__ "0|0|
S3S21S7S20A1S3cU190S3fS41R1A1A3S5bR1A1A3Fe;"). Proof. intros e. unfold runMG. reflexivity. Qed.

Definition VM0 : list positive := ltac2:(tb__ "0|0|
S0S1bPa0S0S1bPa1S0S1bPa2S0S1bPccS0S1bPcdS0S1bPceS0S1bPcfS0S1bPd0S5S1bA1A3A3A3A3A3A3A3A3").
Definition VM (e : bool) : list positive := ltac2:(tb__ "0|1|
S8S1bS0S1bPa0S0S1bPa1S0S1bPa2S0S1bPa3S0S1bPa4S0S1bPa5S0S1bPa6S0S1bPa7S0S1bPccS0S1bPcdS0S1bPceS0S1bPcfS0S1bPd0S5S1bA1M0A3A3A3A3A3A3A3A3A3A3A3A3A3S3S7S1bA1Le;Ve;S0S1bPb8S0S1bPb9S0S1bPbaS0S1bPbbG0A3A3A3A3G0X3x2A3").
Definition VMc (e : bool) : list positive := ltac2:(tb__ "0|0|
S8S1bS4aVe;A1S0S1bPa9S0S1bPaaS0S1bPbcS5S1bA1A3A3A3A3").
Definition LM0 : list axst := Eval vm_compute in (map la_state runM0).
Definition LMHt : list axst := Eval vm_compute in (map la_state (runMH true)).
Definition LMHf : list axst := Eval vm_compute in (map la_state (runMH false)).
Definition LMCt : list axst := Eval vm_compute in (map la_state (runMC true)).
Definition LMCf : list axst := Eval vm_compute in (map la_state (runMC false)).
Definition LMGt : list axst := Eval vm_compute in (map la_state (runMG true)).
Definition LMGf : list axst := Eval vm_compute in (map la_state (runMG false)).
Definition LMH (e : bool) : list axst := if e then LMHt else LMHf.
Definition LMC (e : bool) : list axst := if e then LMCt else LMCf.
Definition LMG (e : bool) : list axst := if e then LMGt else LMGf.
Definition TsM0 : list (axst * vmap) := ltac2:(tb__ "0|0|
S7dS1dS4S1dS23A2S1dS1S1dS23R1S7eS65A1A4LT;S5eA4").
Definition TsMH (e : bool) : list (axst * vmap) := ltac2:(tb__ "0|0|
S7dS1dS4S1dS23A2S1dS1S1dS23R1S7eS4aVe;A1A1A4LT;S61Ve;A1A4").
Definition TsMC (e : bool) : list (axst * vmap) := ltac2:(tb__ "0|0|
S7dS1dS4S1dS23A2S1dS1S1dS23R1S7eS66Ve;A1A1A4LT;S5fVe;A1A4").
Definition TsMG (e : bool) : list (axst * vmap) := ltac2:(tb__ "0|0|
S7dS1dS4S1dS23A2S1dS1S1dS23R1S7eS4aVe;A1A1A4LT;S60Ve;A1A4").
Lemma chkM0 : ltac2:(tb__ "0|0|
S21S3S24SfS1eS43A1A1S59S55A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chkMH : ltac2:(tb__ "0|0|
S3S21S3S24SfS1eS42R1A1A1A1S5cR1A1S58R1A1A3S6A3Fe;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma chkMC : ltac2:(tb__ "0|0|
S3S21S3S24SfS1eS40R1A1A1A1S5aR1A1S56R1A1A3S6A3Fe;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma chkMG : ltac2:(tb__ "0|0|
S3S21S3S24SfS1eS41R1A1A1A1S5bR1A1S57R1A1A3S6A3Fe;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma nxM : ltac2:(tb__ "0|4|
S22S22S21S3S13S1eS43A1M0A1S9A3S80S3eSfG0A1A2A2S22S3S22S21S3S13S1eS42R1A1A1M1A1S9A3S80S3eSfG1A1A2A2Fe;S22S3S22S21S3S13S1eS40R1A1A1M2A1S9A3S80S3eSfG2A1A2A2Fe;S3S22S21S3S13S1eS41R1A1A1M3A1S9A3S80S3eSfG3A1A2A2Fe;A2A2A2").
Proof.
  split; [split; [reflexivity | unfold Pos.le; cbn; discriminate]|].
  split; [intros [|]; split; [reflexivity | unfold Pos.le; cbn; discriminate | reflexivity | unfold Pos.le; cbn; discriminate]|].
  split; intros [|]; split; first [reflexivity | (unfold Pos.le; cbn; discriminate)].
Qed.
Lemma presM_wf : ltac2:(tb__ "0|3|
S22S21S3S1fS43A1S6A3S22S21S3S14S1eS43A1A1S6A3S22S3S22S21S3S1fS42R1A1M0A1S6A3S21S3S14S1eG0A1A1S6A3A2Fe;S22S3S22S21S3S1fS40R1A1M1A1S6A3S21S3S14S1eG1A1A1S6A3A2Fe;S3S22S21S3S1fS41R1A1M2A1S6A3S21S3S14S1eG2A1A1S6A3A2Fe;A2A2A2A2").
Proof. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. repeat split; destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section TR.
Context {Q : assn} (X : trk Q).
Theorem seg_M0 : ltac2:(tb__ "0|0|
S38S10S7S81Q40A1A1S3bVQ;VX;R3A3S1dS23S10S7fS4S1dS23A2S1S1dS23R3R2A4S55A3S25R3R7R2A3S3aVQ;VX;S37S39R9R5R3R7A5A3F_;F_;Frho';FM;FT;S3aVQ;VX;S37S39R5S43R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 300%nat _ PM1 runM0 TsM0 runM0_eq chkM0 (proj1 (proj1 nxM)) (proj2 (proj1 nxM)) J rho tp HJ HC). Qed.
Theorem seg_MH : ltac2:(tb__ "0|0|
S3S38S10S7S81Q40A1A1S3bVQ;VX;R3A3S1dS23S10S7fS4S1dS23A2S1S1dS23R3R2A4S58R8A1A3S25R3R7R2A3S3aVQ;VX;S37S39R9R5R3R7A5A3F_;F_;Frho';FM;FT;S3aVQ;VX;S37S39R5S42R6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Fe;").
Proof. intros e J rho tp HJ HC. exact (tr_piece X 400%nat _ (MH e) (runMH e) (TsMH e) (runMH_eq e) (chkMH e) (proj1 (proj1 (proj2 nxM) e)) (proj2 (proj1 (proj2 nxM) e)) J rho tp HJ HC). Qed.
Theorem seg_MC : ltac2:(tb__ "0|0|
S3S38S10S7S81Q40A1A1S3bVQ;VX;R3A3S1dS23S10S7fS4S1dS23A2S1S1dS23R3R2A4S56R8A1A3S25R3R7R2A3S3aVQ;VX;S37S39R9R5R3R7A5A3F_;F_;Frho';FM;FT;S3aVQ;VX;S37S39R5S40R6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Fe;").
Proof. intros e J rho tp HJ HC. exact (tr_piece X 100%nat _ (MC e) (runMC e) (TsMC e) (runMC_eq e) (chkMC e) (proj1 (proj1 (proj2 (proj2 nxM)) e)) (proj2 (proj1 (proj2 (proj2 nxM)) e)) J rho tp HJ HC). Qed.
Theorem seg_MG : ltac2:(tb__ "0|0|
S3S38S10S7S81Q40A1A1S3bVQ;VX;R3A3S1dS23S10S7fS4S1dS23A2S1S1dS23R3R2A4S57R8A1A3S25R3R7R2A3S3aVQ;VX;S37S39R9R5R3R7A5A3F_;F_;Frho';FM;FT;S3aVQ;VX;S37S39R5S41R6A1R4R3A5A3F_;F_;Ftp;Frho;FJ;Fe;").
Proof. intros e J rho tp HJ HC. exact (tr_piece X 400%nat _ (MG e) (runMG e) (TsMG e) (runMG_eq e) (chkMG e) (proj1 (proj2 (proj2 (proj2 nxM)) e)) (proj2 (proj2 (proj2 (proj2 nxM)) e)) J rho tp HJ HC). Qed.
End TR.
End SegQ3M_states.

