(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je i9.

(* [comment removed for export] *)
Module SpineCallocS6iW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "option"; "pair"; "Some"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "C5m1"; "C5m2"; "E5m1"; "E5m2"; "C5d"; "C5e"; "E5j"; "C6"; "F_gen"; "BR"; "C5c"; "LLe"; "LRe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "memset_entryA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "ss_facts"; "ss_next"; "sv"; "sobj"; "sprop_below"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.SpineCallocS6iW1.INST"; "s51_0"; "s52_0"; "R51_0"; "R52_0"; "T51_0"; "T52_0"; "s6j_0"; "sd51_0"; "sd52_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6"; "a0e2"; "len1e"; "len2e"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CallocMemoSPW1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Lemma Cert5c_0 : ltac2:(tb__ "0|1|
S5S6S3eS20Ufa0S8S28Zdb004S9S28A1A3S1fS8S1S19VW;Vst;Vtmax;A3S9S1A1M0A3S8S1S11VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma G5m1_0 : ltac2:(tb__ "0|0|
S3dS21S17S22S0S11VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W5m1_0 : ltac2:(tb__ "0|0|
S5S6S27S0SfVW;Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma D5m1_0 : ltac2:(tb__ "0|4|
S5SbSeSaSeS24S24A2M0A1M1SaS21A1M2A2M3A1S40S0S11VW;Vst;Vtmax;A3A1S0SfVW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS24S24S43S1aA4S9G0A1A3S9S21A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NX5m1_0 : ltac2:(tb__ "0|0|
S5S29S23S0SfVW;Vst;Vtmax;A3A1A1S23S0S11VW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition s51_0 : ltac2:(tb__ "0|0|
S2b") := ltac2:(tb__ "0|0|
S2aP1S0SfVW;Vst;Vtmax;A3A1S0S1cA1A3").
Definition R51_0 : ltac2:(tb__ "0|0|
SaS25A1") := ltac2:(tb__ "0|1|
SbSaS25A1M0A1G0Lx;S38SfVW;Vst;Vtmax;A3S1cS2dA3G0R1LR;S9S25A1Xbx2").
Definition T51_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S39S2dS1cS36S3bS1dA1A1SfVW;Vst;Vtmax;A3S2fA5").
Definition sd51_0 : ltac2:(tb__ "0|0|
S2b") := ltac2:(tb__ "0|0|
S2aS1fS0S37S31S22S0SfVW;Vst;Vtmax;A3A1A1A2A1S0S13VW;Vst;Vtmax;A3A1A3").
Lemma He51_0 : ltac2:(tb__ "0|1|
S5SbSaS25A1M0A1S38SfVW;Vst;Vtmax;A3S1cS2dA3SdG0S2fA2A3").
Proof. unfold s51_0, R51_0. cbv beta zeta delta [W st tmax R51_0 s51_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Hchk51_0 : ltac2:(tb__ "0|0|
S5S6S3aSfVW;Vst;Vtmax;A3S1cS2dS2fS3fS4S1S3S1eA4A5S7A3").
Proof. unfold s51_0, R51_0. cbv beta zeta delta [W st tmax R51_0 s51_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma HT51_0 : ltac2:(tb__ "0|0|
S5S1S39S2dS1cS36S3bS1dA1A1SfVW;Vst;Vtmax;A3S2fA5S31A3").
Proof. reflexivity. Qed.
Lemma FBC51_0 : ltac2:(tb__ "0|1|
S5S6S3cS21S26S23S0SfVW;Vst;Vtmax;A3A1M0A1A1S22G0A1A3S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma FBT51_0 : ltac2:(tb__ "0|0|
S5S6S3cS21S26S23S0S31A1A1A1S22S0SfVW;Vst;Vtmax;A3A1A1A3S7A3").
Proof. unfold T51_0. cbv beta zeta delta [W st tmax R51_0 T51_0 s51_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma ENT51_0 : ltac2:(tb__ "0|0|
S5S6S2S37S31S22S0SfVW;Vst;Vtmax;A3A1A1A2S13VW;Vst;Vtmax;A3S34A3S7A3").
Proof. unfold T51_0, sd51_0. cbv beta zeta delta [W st tmax R51_0 T51_0 s51_0 sd51_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID51_0 : ltac2:(tb__ "0|0|
S5S6S2cS34S1fA2S7A3").
Proof. unfold sd51_0. cbv beta zeta delta [W st tmax R51_0 T51_0 s51_0 sd51_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NXC51_0 : ltac2:(tb__ "0|0|
S41S1fS23S0SfVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Cert5d_0 : ltac2:(tb__ "0|1|
S5S6S3eS20Ufa0S8S28Zdb004S9S28A1A3S1fS8S1S13VW;Vst;Vtmax;A3S9S1A1M0A3S8S1S12VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma G5m2_0 : ltac2:(tb__ "0|0|
S3dS21S17S22S0S12VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W5m2_0 : ltac2:(tb__ "0|0|
S5S6S27S0S10VW;Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma D5m2_0 : ltac2:(tb__ "0|4|
S5SbSeSaSeS24S24A2M0A1M1SaS21A1M2A2M3A1S40S0S12VW;Vst;Vtmax;A3A1S0S10VW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS24S24S42S18A4S8G0ScS24S24S44S1bA4S9G0A1A3A3S9S21A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NX5m2_0 : ltac2:(tb__ "0|0|
S5S29S23S0S10VW;Vst;Vtmax;A3A1A1S23S0S12VW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition s52_0 : ltac2:(tb__ "0|0|
S2b") := ltac2:(tb__ "0|0|
S2aP1S0S10VW;Vst;Vtmax;A3A1S0S1cA1A3").
Definition R52_0 : ltac2:(tb__ "0|0|
SaS25A1") := ltac2:(tb__ "0|1|
SbSaS25A1M0A1G0Lx;S38S10VW;Vst;Vtmax;A3S1cS2eA3G0R1LR;S9S25A1Xbx2").
Definition T52_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S39S2eS1cS36S3bS1dA1A1S10VW;Vst;Vtmax;A3S30A5").
Definition sd52_0 : ltac2:(tb__ "0|0|
S2b") := ltac2:(tb__ "0|0|
S2aS1fS0S37S32S22S0S10VW;Vst;Vtmax;A3A1A1A2A1S0S14VW;Vst;Vtmax;A3A1A3").
Lemma He52_0 : ltac2:(tb__ "0|1|
S5SbSaS25A1M0A1S38S10VW;Vst;Vtmax;A3S1cS2eA3SdG0S30A2A3").
Proof. unfold s52_0, R52_0. cbv beta zeta delta [W st tmax R52_0 s52_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Hchk52_0 : ltac2:(tb__ "0|0|
S5S6S3aS10VW;Vst;Vtmax;A3S1cS2eS30S3fS4S1S3S1eA4A5S7A3").
Proof. unfold s52_0, R52_0. cbv beta zeta delta [W st tmax R52_0 s52_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma HT52_0 : ltac2:(tb__ "0|0|
S5S1S39S2eS1cS36S3bS1dA1A1S10VW;Vst;Vtmax;A3S30A5S32A3").
Proof. reflexivity. Qed.
Lemma FBC52_0 : ltac2:(tb__ "0|1|
S5S6S3cS21S26S23S0S10VW;Vst;Vtmax;A3A1M0A1A1S22G0A1A3S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma FBT52_0 : ltac2:(tb__ "0|0|
S5S6S3cS21S26S23S0S32A1A1A1S22S0S10VW;Vst;Vtmax;A3A1A1A3S7A3").
Proof. unfold T52_0. cbv beta zeta delta [W st tmax R52_0 T52_0 s52_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma ENT52_0 : ltac2:(tb__ "0|0|
S5S6S2S37S32S22S0S10VW;Vst;Vtmax;A3A1A1A2S14VW;Vst;Vtmax;A3S35A3S7A3").
Proof. unfold T52_0, sd52_0. cbv beta zeta delta [W st tmax R52_0 T52_0 s52_0 sd52_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID52_0 : ltac2:(tb__ "0|0|
S5S6S2cS35S1fA2S7A3").
Proof. unfold sd52_0. cbv beta zeta delta [W st tmax R52_0 T52_0 s52_0 sd52_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NXC52_0 : ltac2:(tb__ "0|0|
S41S1fS23S0S10VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Cert5e_0 : ltac2:(tb__ "0|1|
S5S6S3eS20Ufa0S8S28Z3c80cS9S28A1A3S1fS8S1S14VW;Vst;Vtmax;A3S9S1A1M0A3S8S1S15VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition s6j_0 : ltac2:(tb__ "0|0|
S2b") := ltac2:(tb__ "0|0|
S2aS1fS0S15VW;Vst;Vtmax;A3A1S0S16VW;Vst;Vtmax;A3A1A3").
Lemma ENT6j_0 : ltac2:(tb__ "0|0|
S5S6S2S15VW;Vst;Vtmax;A3S16VW;Vst;Vtmax;A3S33A3S7A3").
Proof. unfold s6j_0. cbv beta zeta delta [W st tmax s6j_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID6j_0 : ltac2:(tb__ "0|0|
S5S6S2cS33S1fA2S7A3").
Proof. unfold s6j_0. cbv beta zeta delta [W st tmax s6j_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
End INST.
End SpineCallocS6iW1.

(* [comment removed for export] *)
Module SpineCallocS7iW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "option"; "Some"; "prod"; "pair"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "C6m"; "E6s"; "C6l"; "C7"; "E6l"; "O_U"; "C6b"; "E6j"; "E6m"; "C6"; "F_gen"; "LUe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sv"; "ss_objs"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.SpineCallocS7iW1.INST"; "s6_0"; "R6_0"; "T6_0"; "k6_0"; "s7j_0"; "s7s_0"; "sd6_0"; "E6sz_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zobj"; "zero_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@Stdlib.Lists.List"; "forallb"; "incl"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7"; "len3e"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CallocMemoSPW1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Lemma Cert6_0 : ltac2:(tb__ "0|1|
S6S7S38S27Ufa0S9S28Z5f9f8S9S28Z3c82cSaS28A1A3A3S26S9S1S1bVW;Vst;Vtmax;A3SaS1A1M0A3S9S1S13VW;Vst;Vtmax;A3S9S1S16VW;Vst;Vtmax;A3G0A3A3A6S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition k6_0 : ltac2:(tb__ "0|0|
S11") := ltac2:(tb__ "0|0|
S46S10S1eS23S0S13VW;Vst;Vtmax;A3A1A1A2U3A2").
Lemma NTH6s_0 : ltac2:(tb__ "0|0|
S6ScS1eA1S45S1eS23S0S13VW;Vst;Vtmax;A3A1A1S30A3SdS1eS17A2A3").
Proof. unfold k6_0. cbv beta zeta delta [W st tmax k6_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma ZC6s_0 : ltac2:(tb__ "0|0|
S6S7S3fS21S0S13VW;Vst;Vtmax;A3A1A1S17A2S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition E6sz_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|2|
S3S13VW;Vst;Vtmax;A3M0S3cS0G0A1M1S3bS1eS23G1A1S30S3eS17A1A4A2A2").
Definition s7s_0 : ltac2:(tb__ "0|0|
S36") := ltac2:(tb__ "0|0|
S35S26S0S34A1S0S15VW;Vst;Vtmax;A3A1A3").
Lemma ENT7s_0 : ltac2:(tb__ "0|2|
S6S7S2S3S13VW;Vst;Vtmax;A3M0S3cS0G0A1M1S3bS1eS23G1A1S30S3eS17A1A4A2A2S15VW;Vst;Vtmax;A3S32A3S8A3").
Proof. unfold k6_0, s7s_0. cbv beta zeta delta [W st tmax E6sz_0 k6_0 s7s_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID7s_0 : ltac2:(tb__ "0|0|
S6S7S37S32S26A2S8A3").
Proof. unfold s7s_0. cbv beta zeta delta [W st tmax E6sz_0 k6_0 s7s_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma G6l_0 : ltac2:(tb__ "0|0|
S44S1fS1cS21S0S16VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W6l_0 : ltac2:(tb__ "0|0|
S6S7S25S0S14VW;Vst;Vtmax;A3A1A1S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma D6l_0 : ltac2:(tb__ "0|4|
S6ScSeSbSeS22S22A2M0A1M1SbS1fA1M2A2M3A1S3aS0S16VW;Vst;Vtmax;A3A1S0S14VW;Vst;Vtmax;A3A1A2SdG3SfG1G2S9G0SfS22S22S48S1dA4SaG0A1A3SaS1fA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NX6l_0 : ltac2:(tb__ "0|0|
S6S29S20S0S14VW;Vst;Vtmax;A3A1A1S20S0S16VW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Cert6l_0 : ltac2:(tb__ "0|1|
S6S7S38S27Ufa0S9S28Zdb004SaS28A1A3S26S9S1S14VW;Vst;Vtmax;A3SaS1A1M0A3S9S1S1aVW;Vst;Vtmax;A3G0A3A6S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W6m_0 : ltac2:(tb__ "0|0|
S6S7S25S0S12VW;Vst;Vtmax;A3A1A1S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma D6m_0 : ltac2:(tb__ "0|4|
S6ScSeSbSeS22S22A2M0A1M1SbS1fA1M2A2M3A1S3aS0S1aVW;Vst;Vtmax;A3A1S0S12VW;Vst;Vtmax;A3A1A2SdG3SfG1G2SaG0A1SaS1fA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NX6m_0 : ltac2:(tb__ "0|0|
S6S29S20S0S12VW;Vst;Vtmax;A3A1A1S20S0S1aVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition s6_0 : ltac2:(tb__ "0|0|
S36") := ltac2:(tb__ "0|0|
S35P1S0S12VW;Vst;Vtmax;A3A1S0S2aA1A3").
Definition R6_0 : ltac2:(tb__ "0|0|
SbS1eA1") := ltac2:(tb__ "0|1|
ScSbS1eA1M0A1G0Lx;S40S12VW;Vst;Vtmax;A3S2aS2dA3G0R1LR;SaS1eA1Xcx2").
Definition T6_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S41S2dS2aS39S2bA1S12VW;Vst;Vtmax;A3S2eA5").
Definition sd6_0 : ltac2:(tb__ "0|0|
S36") := ltac2:(tb__ "0|0|
S35S26S0S3dS2fS21S0S12VW;Vst;Vtmax;A3A1A1A2A1S0S18VW;Vst;Vtmax;A3A1A3").
Lemma He6_0 : ltac2:(tb__ "0|1|
S6ScSbS1eA1M0A1S40S12VW;Vst;Vtmax;A3S2aS2dA3SdG0S2eA2A3").
Proof. unfold s6_0, R6_0. cbv beta zeta delta [W st tmax R6_0 s6_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Hchk6_0 : ltac2:(tb__ "0|0|
S6S7S42S12VW;Vst;Vtmax;A3S2aS2dS2eS47S5S1S4S2cA4A5S8A3").
Proof. unfold s6_0, R6_0. cbv beta zeta delta [W st tmax R6_0 s6_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma HT6_0 : ltac2:(tb__ "0|0|
S6S1S41S2dS2aS39S2bA1S12VW;Vst;Vtmax;A3S2eA5S2fA3").
Proof. reflexivity. Qed.
Lemma FBC6_0 : ltac2:(tb__ "0|1|
S6S7S43S1fS24S20S0S12VW;Vst;Vtmax;A3A1M0A1A1S21G0A1A3S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma FBT6_0 : ltac2:(tb__ "0|0|
S6S7S43S1fS24S20S0S2fA1A1A1S21S0S12VW;Vst;Vtmax;A3A1A1A3S8A3").
Proof. unfold T6_0. cbv beta zeta delta [W st tmax R6_0 T6_0 s6_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma ENT6_0 : ltac2:(tb__ "0|0|
S6S7S2S3dS2fS21S0S12VW;Vst;Vtmax;A3A1A1A2S18VW;Vst;Vtmax;A3S33A3S8A3").
Proof. unfold T6_0, sd6_0. cbv beta zeta delta [W st tmax R6_0 T6_0 s6_0 sd6_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID6_0 : ltac2:(tb__ "0|0|
S6S7S37S33S26A2S8A3").
Proof. unfold sd6_0. cbv beta zeta delta [W st tmax R6_0 T6_0 s6_0 sd6_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NXC6_0 : ltac2:(tb__ "0|0|
S49S26S20S0S12VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Cert6b_0 : ltac2:(tb__ "0|1|
S6S7S38S27Ufa0S9S28Z3c82cSaS28A1A3S26S9S1S18VW;Vst;Vtmax;A3SaS1A1M0A3S9S1S19VW;Vst;Vtmax;A3G0A3A6S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition s7j_0 : ltac2:(tb__ "0|0|
S36") := ltac2:(tb__ "0|0|
S35S26S0S19VW;Vst;Vtmax;A3A1S0S15VW;Vst;Vtmax;A3A1A3").
Lemma ENT7j_0 : ltac2:(tb__ "0|0|
S6S7S2S19VW;Vst;Vtmax;A3S15VW;Vst;Vtmax;A3S31A3S8A3").
Proof. unfold s7j_0. cbv beta zeta delta [W st tmax s7j_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID7j_0 : ltac2:(tb__ "0|0|
S6S7S37S31S26A2S8A3").
Proof. unfold s7j_0. cbv beta zeta delta [W st tmax s7j_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
End INST.
End SpineCallocS7iW1.

(* [comment removed for export] *)
Module SpineCallocS5iW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "prod"; "list"; "pair"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "swf"; "SVar"; "ss_facts"; "SLit"; "ss_next"; "SPUle"; "SPBranch"; "SPNot"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E3p"; "E5s1"; "E5s2"; "C5b"; "C5c"; "E5f"; "C3"; "E5n"; "V_CLS"; "sreg1"; "sreg2"; "C6"; "V_SIZE"; "C2p"; "C2r"; "C5"; "E3r"; "E4d"; "F_gen"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "V_CNT"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "E5s1'"; "E5s2'"; "tab1_ok"; "clsp_e"; "clsp_e31"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.SpineCallocS5iW1.INST"; "s1_0"; "s2_0"; "s3_0"; "s6n_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CallocMemoSPW1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Lemma Cert3p_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z40e58S5S33Z3c614S8S33A1A3A3S35S5S1S28VW;Vst;Vtmax;A3S8S1A1M0A3S5S1S1bVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SKY_0 : ltac2:(tb__ "0|1|
S4SaS9S9SfSfA2SfA2M0A1S4aS11G0S4dS1aS0S1bVW;Vst;Vtmax;A3A1A1A4S4aS11G0S4dScS11ScS11S5S11S54ScS11S5aVW;A1S56A3A3S55A3S5S11S2eS5S11S30S5S11S2fS5S11S31S8S11A1A3A3A3A3A3A4A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma YX_0 : ltac2:(tb__ "0|1|
S4SaS9SfSfA2M0A1S3S1bVW;Vst;Vtmax;A3A1S8G0A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma YF_0 : ltac2:(tb__ "0|0|
S38S10ScS10ScS10ScS10S59VW;Vst;A2S58S57A1A3S53A3S2dA3S14S0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma YP_0 : ltac2:(tb__ "0|0|
S37S10S17S15Z1A1S13S32A1A2S14S0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma WY1_0 : ltac2:(tb__ "0|0|
S4S6S12S0S44S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma WY2_0 : ltac2:(tb__ "0|0|
S4S6S12S0S45S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma WY3_0 : ltac2:(tb__ "0|0|
S4S6S12S0S46S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma WY4_0 : ltac2:(tb__ "0|0|
S4S6S12S0S47S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma WY5_0 : ltac2:(tb__ "0|0|
S4S6S12S0S48S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma WY6_0 : ltac2:(tb__ "0|0|
S4S6S12S0S49S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma WY7_0 : ltac2:(tb__ "0|0|
S4S6S12S0S43S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition s3_0 : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S3fS35S0S43S1bVW;Vst;Vtmax;A3A1A1S0S21VW;Vst;Vtmax;A3A1A3").
Lemma ENT3_0 : ltac2:(tb__ "0|0|
S4S6S2S43S1bVW;Vst;Vtmax;A3A1S21VW;Vst;Vtmax;A3S50A3S7A3").
Proof. unfold s3_0. cbv beta zeta delta [W st tmax s3_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID3_0 : ltac2:(tb__ "0|0|
S4S6S41S50S35A2S7A3").
Proof. unfold s3_0. cbv beta zeta delta [W st tmax s3_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Cert3r_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z40e58S5S33Z3c614S8S33A1A3A3S35S5S1S29VW;Vst;Vtmax;A3S8S1A1M0A3S5S1S2bVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Cert4_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z7e9e4S8S33A1A3S35S5S1S21VW;Vst;Vtmax;A3S8S1A1M0A3S5S1S2cVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Cert5_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z3c774S5S33Z3c80cS8S33A1A3A3S35S5S1S2aVW;Vst;Vtmax;A3S8S1A1M0A3S5S1S22VW;Vst;Vtmax;A3S5S1S20VW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition s6n_0 : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S3fS35S0S22VW;Vst;Vtmax;A3A1S0S26VW;Vst;Vtmax;A3A1A3").
Lemma ENT6n_0 : ltac2:(tb__ "0|0|
S4S6S2S22VW;Vst;Vtmax;A3S26VW;Vst;Vtmax;A3S51A3S7A3").
Proof. unfold s6n_0. cbv beta zeta delta [W st tmax s6n_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID6n_0 : ltac2:(tb__ "0|0|
S4S6S41S51S35A2S7A3").
Proof. unfold s6n_0. cbv beta zeta delta [W st tmax s6n_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W5b_0 : ltac2:(tb__ "0|0|
S4S6S12S0S1eVW;Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma D5b_0 : ltac2:(tb__ "0|5|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S42S0S20VW;Vst;Vtmax;A3A1S0S1eVW;Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS3eS13S23A1M4A4S5G0SbSfSfS3dG4A4S8G0A1A3A3S8S10A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NX5b_0 : ltac2:(tb__ "0|0|
S4S34S16S0S1eVW;Vst;Vtmax;A3A1A1S16S0S20VW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma F5f64_0 : ltac2:(tb__ "0|0|
S37S10S17S13PcA1S15Zfc00A1A2S14S0S20VW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Cert5b_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z3c7e0S8S33A1A3S35S5S1S1eVW;Vst;Vtmax;A3S8S1A1M0A3S5S1S1cVW;Vst;Vtmax;A3S5S1S1dVW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma OV1_0 : ltac2:(tb__ "0|0|
S4S6S52P9eS24VW;Vst;Vtmax;A3A2S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma OV2_0 : ltac2:(tb__ "0|0|
S4S6S52P9eS25VW;Vst;Vtmax;A3A2S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma TAB1_0 : ltac2:(tb__ "0|0|
S4S6S3cP9eS24VW;Vst;Vtmax;A3S4cZ11UeA5S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma TAB2_0 : ltac2:(tb__ "0|0|
S4S6S3cP9eS25VW;Vst;Vtmax;A3S4cZ1U10A5S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W1'_0 : ltac2:(tb__ "0|0|
S4S6S12S0S3aU1Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax E5s1']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W2'_0 : ltac2:(tb__ "0|0|
S4S6S12S0S3bU1Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax E5s2']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma D1'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S42S0S1cVW;Vst;Vtmax;A3A1S0S3aU1Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS24VW;Vst;Vtmax;A3S13S27A1A4S8G0A1A3S8S10A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E5s1']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma D2'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S42S0S1dVW;Vst;Vtmax;A3A1S0S3bU1Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS25VW;Vst;Vtmax;A3S13S27A1A4S8G0A1A3S8S10A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E5s2']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NX1'_0 : ltac2:(tb__ "0|0|
S4S34S16S0S3aU1Vst;Vtmax;A3A1A1S16S0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E5s1']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NX2'_0 : ltac2:(tb__ "0|0|
S4S34S16S0S3bU1Vst;Vtmax;A3A1A1S16S0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E5s2']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma F1gt_0 : ltac2:(tb__ "0|0|
S37S10S18S4bS15Z10A1S13S23A1A3S14S0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma F2le_0 : ltac2:(tb__ "0|0|
S37S10S19S18S4bS15Z10A1S13S23A1A3A1S14S0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma F1_64_0 : ltac2:(tb__ "0|0|
S37S10S17S13PcA1S15Zfc00A1A2S14S0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma F2_64_0 : ltac2:(tb__ "0|0|
S37S10S17S13PcA1S15Zfc00A1A2S14S0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition s1_0 : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S3fS35S0S3aU1Vst;Vtmax;A3A1S0S1fVW;Vst;Vtmax;A3A1A3").
Definition s2_0 : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S3fS35S0S3bU1Vst;Vtmax;A3A1S0S1fVW;Vst;Vtmax;A3A1A3").
Lemma ENT1_0 : ltac2:(tb__ "0|0|
S4S6S2S3aU1Vst;Vtmax;A3S1fVW;Vst;Vtmax;A3S4eA3S7A3").
Proof. unfold s1_0. cbv beta zeta delta [W st tmax E5s1' s1_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma ENT2_0 : ltac2:(tb__ "0|0|
S4S6S2S3bU1Vst;Vtmax;A3S1fVW;Vst;Vtmax;A3S4fA3S7A3").
Proof. unfold s2_0. cbv beta zeta delta [W st tmax E5s2' s2_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID1_0 : ltac2:(tb__ "0|0|
S4S6S41S4eS35A2S7A3").
Proof. unfold s1_0. cbv beta zeta delta [W st tmax E5s1' s1_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID2_0 : ltac2:(tb__ "0|0|
S4S6S41S4fS35A2S7A3").
Proof. unfold s2_0. cbv beta zeta delta [W st tmax E5s2' s2_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
End INST.
End SpineCallocS5iW1.

(* [comment removed for export] *)
Module RefillS.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "of_nat"; "div"; "ltb"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "valuation"; "rm"; "rw"; "FcsrFrm0"; "cell"; "mkSS"; "rl"; "DUnknown"; "SVar"; "mkCell"; "mkObj"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "list"; "prod"; "bool"; "None"; "false"; "true"; "app"; "length"; "andb"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kUserMapSize"; "Sh"; "Size"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "free_array"; "kFreeArrayMapSize"; "region_beg"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_mapped_user"; "AA"; "budget_bound"; "cs_free_array"; "cs_mapped_free_array"; "aa_cache_inited"; "aa_geom"; "ag_spacebeg"; "ag_thread"; "class_state"; "cs_allocated_user"; "cs_cache"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "needs_populate"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "NXR"; "nv_q24"; "JLRf"; "JRf"; "L_rf"; "O_stR"; "Pre_rf"; "rf_depth"; "rf_new"; "NXRC"; "NXRP"; "RF_ENT"; "RF_RET"; "cache_e"; "refill_zone"; "regsR"; "rf_grows"; "rfacts"; "vSTR"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_CLS"; "O_pcc0"; "V_SIZE"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG"; "BASEG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "mkA"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC"; "K0C"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "ALLOC_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "MUCAP"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI PrimCredit RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition RF_ENT : Z := 0x412fc.
Definition RF_RET : Z := 0x41354.
Definition NXR : positive := 220%positive.
Definition NXRC : positive := 240%positive.
Definition NXRP : positive := 400%positive.
Definition rf_depth : Z := 512.
Definition vSTR : sv := SVar 160.
Definition O_stR : sobj := ltac2:(tb__ "0|0|
S1bS6bSfZad0A1SfZc60A1S1cS15S1aSfZae0A1Z8S5bA3S1dS15A1A3S18A5").
Definition cache_e : sv := SAlu ALU_ADD vT (SLit 208).
Definition regsR : list sv := ltac2:(tb__ "0|1|
S5fS61S1cS21S1eSeA2M0S1fS1eSeU4SfS6aA1A4S1cG0S1fS1eSeUaS56A4S1cG0S1fS1eSeUbS69A4S1cG0S1fS1eSeUcSfS78A1A4S1cG0S1fS1eSeUdS19S66A1A4S1dG0A1A3A3A3A3A3A2").
Definition Pre_rf : axst := ltac2:(tb__ "0|0|
S6fS16S54S58S5eS14S23SeA1S26S10S6cS1cS10S67S1cS10S4eS1dS10A1A3A3A3S70S50A1S49S24A9S1dS21SeSeA2A1A2").
Definition L_rf : axst := ltac2:(tb__ "0|1|
S6fS16S55S5fS60S52A1S1cS21S1eSeA2M0S1fS1eSeU4SfS6aA1A4S1cG0S1fS1eSeUaSfZ1A1A4S1dG0A1A3A3A2S5eS14S23SeA1S26S10S6cS1cS10S4eS1dS10A1A3A3S70S50A1S53S24A9S1dS21SeSeA2A1A2").

Goal swf (ax_S Pre_rf) = true /\ swf (ax_S L_rf) = true. Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition nv_q24 : Z := 7936.
Lemma cls_of_q24 : ltac2:(tb__ "0|0|
S0S0S5Z1S4aA2S5S4aZfc00A2A2S1ScS73S4aA1Z18A3A2"). Proof. split; [unfold nv_q24; lia | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.

Definition rf_new (c : Z) (cs : class_state) : Z := ltac2:(tb__ "0|0|
S9SbS4S3aVcs;A1S31A2S44Vcs;A1A2S33Vc;A1A2").
Definition rf_grows (c : Z) (cs : class_state) : bool := ltac2:(tb__ "0|0|
S28S46Vc;Vcs;A2SaS3eVcs;A1S7Z4S4S8S27ScS3dVcs;A1A2A1S51Vc;Vcs;A2A2A2A2A2").

Definition refill_zone (G : ageom) (inited : bool) (c : Z) (cs : class_state) (z : Z) : Prop := ltac2:(tb__ "0|5|
S42VG;A1ScS41VG;A1ScS4S4R2Zd0A2S7Z50Vc;A2A2ScS39R2Vc;A2ScS36R3Vc;A2ScS8S27ScS3dVcs;A1A2A1ScS4S38R5Vc;A2S3aVcs;A1A2ScS4R3S3eVcs;A1A2ScS2S0S5R6Vz;A2S6Vz;S4R6Z4M0A2A2A2S2S0S5S4R6Z10A2M1Vz;A2S6Vz;S4G1S7G0S47Vc;A1A2A2A2A2S2S0S5R5Vz;A2S6Vz;S4R5Z80A2A2A2S2S0S1S22S46Vc;Vcs;A2S25A3S2S0S5R2Vz;A2S6Vz;S4R2S31A2A2A2S2S0S5S32R2A1M2Vz;A2S6Vz;S4G2Z8000M3A2A2A2S0S5S4R4S7G0R3A2A2Vz;A2S6Vz;S4R4S7G0S4R3S51Vc;Vcs;A2A2A2A2A2A2A2A2A2S2S0S1S22S59Vc;Vcs;A2S25A3S2S0S5R1Vz;A2S6Vz;S4R1S37A2A2A2S0S5S32R1A1M4Vz;A2S6Vz;S4G4G3A2A2A2A2A2S0S1S22Vinited;S24A3S0S5S4R8Z120A2Vz;A2S6Vz;S4R8Zad0A2A2A2A2A2A2A2A2A2TF0;TU0;Tnf;Tfa;Tri;Tpce;TSB;TT;").

Definition rfacts (A : AA) (c nv : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S72VA;Vc;A2S43S0S0S5Z1Vnv;A2S5Vnv;Zfc00A2A2S0S1ScS73Vnv;A1Vc;A3S0S1S2bQ40M0A1M1S13Vrho;PcA2S2cG0Vnv;A2A3S0S1G1S13Vrho;S66A2S2cG0Vc;A2A3S0S1G1S13Vrho;S68A2S2cG0S33Vc;A1A2A3S0S1S20ScA1S45R1A1S1dScA1A3S1S22S46Vc;R1A2S25A3S5S4S3aR2A1S31A2S79Vc;A1A2F_;A2A2A2A2A2A2Tcs;").
Definition JRf (A : AA) (Kc : KcA) (c nv : Z) : jpredA := ltac2:(tb__ "0|0|
S11S20S2bQ40A1A1S20S5dA1S5cS0S71VKc;VA;R4R3R2R1A6S5aVA;Vc;Vnv;R4A4A2Lmd;Ltr;Ltp;Lrho;").
Definition JLRf (A : AA) (Kc : KcA) (c : Z) : jpostA := ltac2:(tb__ "0|8|
S11S20S2bQ40M0A1M1A1M2S11G2S20S5dA1S5cS0S71VKc;S48VA;Vc;A2R4R3R2R1A6S0G1S3S57S40VA;A1S3fVA;A1Vc;S72VA;Vc;A2S2dG0R1A2M3A5A1S1S29S2bQ8A1M4A1M5S12R6R2A2S12R8R2A2M6A3F_;Fa;S0G1S0S5S35G3A2S6G3S34A2A2S3S1G5G6S23G4A1M7A3A1S3S1G5S12R7R3A2G7A3A1F_;F_;Fa;SdS1S20G4A1S17R5R1A2S17R7R1A2A3Fl;A2A2A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").

Definition refill_contract : Prop := ltac2:(tb__ "0|1|
S76OF_;S3bS6dScScS11S20S2bQ40A1A1S6eR5A1S64S2aR8S63R6A1A3S77S2aR9S63R7A1A3S5S3cR9A1S65A2S75S2aRbS62S2aS4cRaR9R8R7A4S4fR6R5A5S30S2aS49R6R5S1cS21S2eS2fA2M0S1fS2eS2fS4dS4bRaR9R8A3A4S1dG0A1A3A5A4F_;F_;F_;F_;Ftp;Frho;Fnv;Fc;FKc;FA;Fok;").
Definition refill_contractE : Prop := ltac2:(tb__ "0|1|
S3bS6dScScS11S20S2bQ40A1A1S6eR5A1S5S3cR7A1S65A2S74S2aS62S2aS4cR8R7R6R5A4S4fR4R3A5S30S2aS49R4R3S1cS21S2eS2fA2M0S1fS2eS2fS4dS4bR8R7R6A3A4S1dG0A1A3A5A3F_;F_;Ftp;Frho;Fnv;Fc;FKc;FA;").
End RefillS.

(* [comment removed for export] *)
Module RebuildG.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "mul"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "bview"; "maskv"; "view"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_mapped_user"; "AA"; "class_state"; "cs_allocated_user"; "cs_mapped_free_array"; "aa_geom"; "aa_cls"; "aa_sec"; "cs_cache"; "cs_free_array"; "ageom"; "cs_empty"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cache_inited"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "ag_spacebeg"; "ag_thread"; "list_upd"; "mkAA"; "qbatch"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@Corelib.Init.Datatypes"; "length"; "list"; "Some"; "nat"; "option"; "true"; "app"; "bool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qall"; "q_ids"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "IMG_HI"; "IMG_LO"; "RI_allocated_meta"; "RI_allocated_user"; "RI_exhausted"; "RI_mapped_free_array"; "RI_mapped_meta"; "RI_mapped_user"; "RI_mutex"; "RI_num_freed"; "free_array"; "max_count"; "region_beg"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "fs_footb"; "quarantine_repr"; "bandtp_inv"; "live_ids"; "model_inv"; "nthZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "AInvQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RebuildG"; "setclsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "q_pure"; "@Stdlib.Lists.List"; "nth_error"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ"; "envR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "cls_pure"; "refillA"; "refill_cs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue ContractFreeNull SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.RebuildR.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition setclsA (A : AA) (c : Z) (csR : class_state) : AA := ltac2:(tb__ "0|0|
S2cS16VA;A1S2bS13S17VA;A1S6Vc;A1VcsR;A4S36S18VA;A1S26VA;A1S25VA;A1S28VA;A1S27VA;A1S21VA;A1S23VA;A1S22VA;A1S24VA;A1S1fVA;A1S1eVA;A1S1dVA;A1Af").
Lemma refillA_setcls : ltac2:(tb__ "0|0|
S12S0ScS12S5cR2R1A2S52R2R1S5dR1S58S13S6R1A1S17R2A1S1cA4A2A3A3Fc;FA;"). Proof. reflexivity. Qed.

Lemma q_pure_mono : ltac2:(tb__ "0|1|
S12S12ScS1bS16R1A1S16R2A1A3ScS32S2eA1S18R2A1S18R3A1A3ScS32S2dA1S39R3A1S39R4A1A3S0S2S14S53R6R1A2A1S14S53R5R1A2A1A2Fc';S54R6A1M0G0F_;F_;F_;F_;F_;FA';FA;").
Proof.
  intros A A' EG ES EQ EAU (Q1 & Q2). unfold q_pure. rewrite EQ. split; [|exact Q2].
  eapply Forall_impl; [|exact Q1]. intros b (B1 & B2 & (y & E & Y0 & YM & Y1) & B4). unfold batch_pure. rewrite EG.
  split; [exact B1|]. split; [exact B2|]. split; [exists y; split; [exact E|]; split; [exact Y0|]; split; [exact YM|]; pose proof (EAU 24); lia|].
  eapply Forall_impl; [|exact B4]. intros it (I1 & I2 & I3 & I4). unfold item_pure. cbn zeta. rewrite EG, ES.
  split; [exact I1|]. split; [exact I2|]. split; [|exact I4].
  intros HP. destruct (I3 HP) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. pose proof (EAU (ClassID (needed (snd it)))). lia.
Qed.

Section R.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Lemma class_rebuild : ltac2:(tb__ "0|d|
S12S30S30S32S56Q40M0A1A1M1G1S3bS3bS0S13S0OF_;S51RaR9R7R5A4SdS2Z1R4A2S2R4Z1eA2A2ScS38S20RcA1S36A3S16RdA1S1bS2aR1A1S0S29R2A1S0S50S13S17R10A1R9S1cA4S13S52R11RaR9A3S12S1S1R4Zd0A2S5Z50RbA2A2S0S4aR4RcA2S0S47R5RdA2S0S49R6ReA2S0SbVsegs;S2fR14A1A2S9SbVsegs;S2fR16A1A2S9S5bR11R10S37S0S4eRbR18R11A3S3aRbS39R18A1R11A3A3A3S2S14R9A1S14R11A1A2S2S11RaA1S11R12A1A2S2S15RbA1S15R13A1A2S2S3S31S0S19R14A1A2A1S48R15A1A2S0S10R15R1A1M2SeG2A1A2Fz;S0R16R1A1S5aR11R12R19S3S31S0S1aR10A1A2A1S11R10A1R2A6F_;Fz;S0SeR17R1A1A1ScS35S56Q8A1M3A1M4RbR2A1RaR2A1A3F_;Fz;S0R18R1A1SfG3G3ScG4RdR3A1S33G3R1A2A3Lb;A2F_;Fz;S0SdS2S3eR1A2S4R1S3dA2A2ScG4S2fR21S57G0R2A2M5A2S2fR22G5A2A3F_;Fa;S7RcS8S1RfS45A2U8M6Z0M7A3A2S7RdS8S1R10S46A2G6S3S31S0S1aR1bA1A2A1A3A2S7ReS8S1R11S42A2G6S15R1cA1A3A2S7RfS8S1R12S40A2G6S14R1dA1A3A2S7R10S8S1R13S3fA2G6G7A3A2S7R11S8S1R14S44A2G6S11R1fA1M8A3A2S7R12S8S1R15S43A2G6G7A3A2S7R13S8S1R16S41A2U1G7A3A2S34S0ScS35S0A1M9S55S0S1aR24A1R2A3S33S0R1A2MaA3S7R17S8S1R19S5Z4S3R3A1A2MbA2U4McR2A3A2F_;Fx;Fi;S7R15S8R19GcS3S31S0S19R23A1A2A1A3A2S34S0ScG9S55S0S19R26A1R2A3GaA3S7R19S8S1S1R1dZ10A2GbA2GcR2A3A2F_;Fx;Fi;S0SdS2S1R19S11R1eA1A2R1A2S4R1S1R19S11R26A1A2A2A2R26R2A1F_;Fz;S0SdS2S3cS1R1aG8A2A1R1A2S4R1S3cS1R1aS11R27A1A2A1A2A2R27R2A1F_;Fz;S0SdS2S1R1cS15R20A1A2R1A2S4R1S1R1cS15R28A1A2A2A2R28R2A1F_;Fz;S4fVsegs;R1fR2cR2aA4S4dR1bR2dA2SdS51R21R30R2eR2cA4SdS4cSaS4bR25A1R1bA2R32A2S4cSaS4bR26A1R1dA2R22A2F_;S59VCST;VXGL;R32R21S2fR31A1S2fR30A1A6A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TvE;Tv3;Trb;Tfa;Tri;Tpce;TAr;Tcs;TSB;TT;TG;F_;F_;F_;FZN;FcsR;Fc;Fmd;Fmd0;Ftp;Ftp0;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp0 tp md0 md c csR ZN HA C1 Hini G T SB cs Ar pce ri fa rb v3 vE
         HPURE HAUm HMUm HMFm HKC ZND HZE VO PRES HRMI R1' R2' R3' R4' R5' R6' R7' R8' HFA HCN HCC HNU HNS HNF HMD HBT.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB). fold vE in HR, HF, HRest. fold G in HG, HR, HF, HRest.
  pose proof HG as HG0. pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & TG).
  fold G in G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, TG. fold T in G4, G5, G10, G13, G14.
  assert (GS : 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G /\ SB mod 2 ^ 16 = 0
               /\ (ag_fsb G + 11571200 <= SB \/ SB + 2 ^ 37 + 4096 <= ag_fsb G)).
  { pose proof (geom_old _ HG) as X. rewrite FS_total_val, kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G in X. fold SB in X. clear -X. tauto. }
  destruct GS as (S1 & S2 & S3 & S4).
  pose proof (geom_bands _ HG) as (WF & TB & CB & DB & TI & CTI & DTI). fold G T in TB, TI. fold G in WF, CB, DB, CTI, DTI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in WF, TB, CB, DB, TI, CTI, DTI. rewrite FS_total_val in WF.
  pose proof HI3 as HI3c. destruct HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & ND3). fold G in SG3, SEC3, Q3, DEP3.
  pose proof SG3 as SG3c. destruct SG3 as (T3 & CTX3 & DTLS3 & PAB3 & PABT3 & _). rewrite kSpaceSize_val in T3, CTX3, DTLS3, PAB3, SEC3. fold T in T3, PABT3. fold SB in T3, CTX3, DTLS3, PAB3.

  destruct HRest as (Hsep & Hlive & Hprim & Hsec & Hq & Hdep & Hia & HTH & Hmisc). pose proof Hprim as Hprim0.
  destruct Hprim as (PL & P0 & P31 & PC).
  pose proof (PC c C1) as PCc. fold G in PCc. change (nthZ (aa_cls A) c cs_empty) with cs in PCc.
  set (nf := Z.of_nat (length (cs_free_array cs))) in *. set (mu := cs_mapped_user cs) in *.
  unfold class_repr in PCc. cbv zeta in PCc. fold SB in PCc. fold ri fa rb in PCc. fold mu nf in PCc.
  destruct PCc as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & R9 & PR & N7 & PU & PSH & PE & ND & LV & CI & CN' & TI10 & CV10 & MC10 & FC10).
  destruct (cap_facts c C1) as (SZc & SZ16 & MCU & _ & FCU & _).
  destruct HPURE as (Q1 & Q2 & Q3' & Q4 & Q4' & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  assert (GEO : geoR SB T (topG G)).
  { unfold geoR. clear -S1 S2 TG G4 G5 T3 TB. lia. }
  assert (ENVB : 0 <= nf /\ 0 <= mu <= 2 ^ 32 - 2 ^ 29).
  { unfold nf. pose proof (Zle_0_nat (length (cs_free_array cs))). unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in N3. clear -H N2 N3. lia. }
  destruct ENVB as (NF0 & MUB).
  assert (NF4 : 4 * nf <= 2 ^ 29) by (unfold kFreeArraySize in N6; clear -N6; lia).
  assert (NZE : forall z, ~ envR SB T c nf mu z -> v3 z = vE z) by (intros z Hz; apply VO; intros Hc; exact (Hz (HZE z Hc))).

  assert (ENVF : forall z, envR SB T c nf mu z -> fs_footb G z = false).
  { intros z Hz. destruct (env_where SB T (topG G) c nf mu z GEO C1 NF0 MUB Hz) as [W|[W|[W _]]].
    - apply fs_footb_space; [exact HG0 | rewrite kSpaceSize_val; fold G SB; clear -W; lia].
    - apply fs_footb_thread; [exact HG0 | fold G T; clear -W; lia].
    - apply fs_footb_space_sh; [exact HG0 | rewrite kSpaceSize_val; fold G SB].
      pose proof (Geometry.Sh_mono (SB + 2 ^ 37) (SB + 2 ^ 37 + 4096) ltac:(clear; lia)) as SM. clear -W SM. lia. }
  set (m3 := maskv (fs_footb G) v3). set (mE := maskv (fs_footb G) vE).
  assert (AGm : forall z, ~ envR SB T c nf mu z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity | exact (NZE z Hz)]. }
  assert (CHm : forall z, envR SB T c nf mu z -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. exact (ENVF z Hz). }
  assert (MSP : forall z, SB <= z < SB + 2 ^ 37 + 4096 -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. apply fs_footb_space; [exact HG0 | rewrite kSpaceSize_val; fold G SB; exact Hz]. }
  assert (MTH : forall z, T <= z < T + 4096 -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. apply fs_footb_thread; [exact HG0 | fold G T; clear -Hz; lia]. }
  fold mE in Hlive, PC, Hsec, Hdep, Hia, HTH, Hmisc, R1, R2, R3, R4, R5, R6, R7, R8, PRI, R9, PR, PU, PSH, PE, CI.
  assert (PRES3 : forall z, ZN z -> exists b, m3 z = Some b).
  { intros z Hz. rewrite (CHm z (HZE z Hz)). exact (PRES z Hz). }
  assert (AGZ : forall z, ~ ZN z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity | exact (VO z Hz)]. }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc) | rewrite (AGZ z Hn); exact (Hp z Hz)]. }
  assert (PRESB : forall lo hi L, present_but mE lo hi L -> present_but m3 lo hi L).
  { intros lo hi L Hp z Hz HL. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc) | rewrite (AGZ z Hn); exact (Hp z Hz HL)]. }
  assert (CELL : forall a w v, (forall k, (k < w)%nat -> ~ envR SB T c nf mu (a + Z.of_nat k)) -> cell_ok mE (mkACell a w v) -> cell_ok m3 (mkACell a w v)).
  { intros a w v Hn Hc. eapply cell_ok_agree; [|exact Hc]. cbn [c_addr c_w]. intros k Hk. apply AGm. exact (Hn k Hk). }

  assert (Hlenc : (Z.to_nat c < length (aa_cls A))%nat) by (rewrite PL; clear -C1; lia).
  assert (ECS' : nthZ (aa_cls Ar) c cs_empty = csR).
  { unfold Ar, setclsA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_same by exact Hlenc. reflexivity. }
  assert (ECSo : forall c', c' <> c -> 0 <= c' -> nthZ (aa_cls Ar) c' cs_empty = nthZ (aa_cls A) c' cs_empty).
  { intros c' Hc' Hc'0. unfold Ar, setclsA, nthZ. cbn [aa_cls]. rewrite nth_list_upd_other; [reflexivity|]. clear -Hc' Hc'0 C1. lia. }
  assert (EG' : aa_geom Ar = G) by reflexivity.
  destruct Hq as (HQP & HQMIN).
  assert (HAU : forall c', 1 <= c' <= 30 -> 0 <= cs_allocated_user (SegQ_wf2.cls_of A c') <= kUserSpaceSize).
  { intros c' Hc'. pose proof (PC c' Hc') as HC. unfold class_repr in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _). unfold SegQ_wf2.cls_of, kUserMapSize in *. clear -M2 M3. lia. }

  assert (NE_img : forall z, IMG_LO <= z < IMG_HI -> ~ envR SB T c nf mu z).
  { intros z Hz Hc. unfold IMG_LO, IMG_HI in Hz.
    apply (env_out SB T (topG G) c nf mu 65536 6565888 z GEO C1 NF0 MUB Hz); [clear -S1; lia | clear -TI; lia | clear; lia | exact Hc]. }
  assert (NE_T : forall z, (T <= z < T + 208 \/ T + 2688 <= z < T + 4096) -> ~ envR SB T c nf mu z).
  { intros z Hz Hc. destruct Hz as [Hz|Hz].
    - apply (env_out SB T (topG G) c nf mu T (T + 208) z GEO C1 NF0 MUB Hz); [clear -T3; lia | clear; lia | clear -TB; lia | exact Hc].
    - apply (env_out SB T (topG G) c nf mu (T + 2688) (T + 4096) z GEO C1 NF0 MUB Hz); [clear -T3; lia | clear; lia | clear -TB; lia | exact Hc]. }
  assert (NE_sec : forall i ch z, nth_error (aa_sec A) i = Some ch ->
            (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch \/ Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)) -> ~ envR SB T c nf mu z).
  { intros i ch z Hi Hz Hc. destruct (SEC3 i ch Hi) as (E1 & E2 & _). fold T in E2. fold SB in E1.
    destruct Hsec as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D10, D12. unfold PG in D8.
    destruct D10 as (D10a & D10l & _ & _ & D10b). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D10b.
    destruct Hz as [Hz|Hz].
    - apply (env_out SB T (topG G) c nf mu (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z GEO C1 NF0 MUB Hz); [clear -E1; lia | clear -E2; lia | clear -D10b; lia | exact Hc].
    - apply (env_sh_out SB T (topG G) c nf mu (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z GEO C1 NF0 MUB Hz); [clear -D10a; lia | clear -D12 TG; lia | clear -E1; lia | exact Hc]. }

  assert (LIVE_OUT : forall b n z, In (b, n) (aa_live A) ->
            (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> ~ envR SB T c nf mu z).
  { intros b n z Hin Hz Hc. destruct (is_primary n) eqn:HP.
    - pose proof (live_prim_czone A HG SG3c mE Hsep Hprim0 b n Hin HP) as LPC. cbv zeta in LPC. destruct LPC as (D1 & O0 & OM & OE & _ & _ & CZ). fold SB in O0, OM, OE, CZ.
      set (c' := ClassID (needed n)) in *. set (o' := b - rz n - (SB + c' * 2 ^ 32)) in *.
      pose proof (PC c' D1) as PC'. fold G in PC'. unfold class_repr in PC'.
      destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV' & _).
      destruct (LV' b n Hin HP eq_refl) as (V1 & V2 & V3). fold SB in V1, V2, V3. unfold region_beg, kRegionSize in V1, V2, V3. fold o' in V2, V3.
      pose proof (CZ z Hz) as CZz. unfold czone in CZz. cbn zeta in CZz.
      apply (slot_out SB T (topG G) c nf mu c' o' (Size c') z GEO C1 NF0 MUB D1 O0 ltac:(destruct (Size_facts c' D1) as [X _]; clear -X; lia) OE); [|exact CZz|exact Hc].
      destruct (Z.eq_dec c' c) as [EC|NC]; [right | left; exact NC].
      assert (EAU : cs_allocated_user (nthZ (aa_cls A) c' cs_empty) = cs_allocated_user cs) by (rewrite EC; reflexivity).
      rewrite EAU in V3. rewrite EC in V3 |- *. unfold mu. clear -V3 N2. lia.
    - destruct (live_sec_map A mE Hsep Hsec HI3c b n Hin HP) as (i & ch & Hi & Eb & RZ & Hn1 & BN & D6 & D0 & DI). unfold PG in Eb, D6.
      apply (NE_sec i ch z Hi); [|exact Hc]. destruct Hz as [Hz|Hz]; [left; clear -Hz Eb RZ BN; lia | right].
      pose proof (Geometry.Sh_mono (sc_map_beg ch) b ltac:(clear -Eb; lia)) as M1.
      pose proof (Sh_add_le b (n + 7) (sc_map_beg ch + sc_map_size ch) ltac:(clear -Eb DI; destruct DI as (X & _); lia) ltac:(clear -Hn1; lia) ltac:(clear -BN; lia)) as M2.
      clear -Hz M1 M2. lia. }

  assert (QF_OUT : forall z, q_foot A z -> ~ envR SB T c nf mu z).
  { intros z Hz Hc. destruct (qfoot_cases A mE HG HI3c HQP Hsec HAU z Hz) as [(c' & o' & (D1 & O0 & OM & OE & IDin) & CZ)|(i & ch & Hi & Hr)].
    - destruct (q_ids_valid A c' (o' / 16) D1 HQP IDin) as (_ & _ & V3).
      destruct (Size_facts c' D1) as (SZ' & SM').
      rewrite (id16_of o' (Size c') ltac:(clear -SZ'; lia) SM' OM) in V3.
      unfold czone in CZ. cbn zeta in CZ. fold SB in CZ.
      apply (slot_out SB T (topG G) c nf mu c' o' (Size c') z GEO C1 NF0 MUB D1 O0 ltac:(clear -SZ'; lia) OE); [|exact CZ|exact Hc].
      destruct (Z.eq_dec c' c) as [EC|NC]; [right | left; exact NC].
      rewrite EC in V3 |- *. change (nthZ (aa_cls A) c cs_empty) with cs in V3. unfold mu. clear -V3 N2. lia.
    - exact (NE_sec i ch z Hi Hr Hc). }
  assert (NE_cls : forall c' z, 1 <= c' <= 30 -> c' <> c -> cls_foot G c' (nthZ (aa_cls A) c' cs_empty) z -> ~ envR SB T c nf mu z).
  { intros c' z Hc' Hne Hz Hc. pose proof (PC c' Hc') as PC'. unfold class_repr in PC'.
    destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & M6 & _).
    pose proof (Zle_0_nat (length (cs_free_array (nthZ (aa_cls A) c' cs_empty)))) as L0.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3, M6.
    unfold cls_foot in Hz. cbv zeta in Hz. unfold region_info, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kRegionInfoStride in Hz. rewrite kSpaceSize_val in Hz. fold G in Hz. fold SB T in Hz.
    apply (clsfoot_out SB T (topG G) c nf mu c' (cs_mapped_free_array (nthZ (aa_cls A) c' cs_empty)) (cs_mapped_user (nthZ (aa_cls A) c' cs_empty)) z GEO C1 NF0 MUB Hc' Hne
             ltac:(clear -M6 L0; lia) ltac:(clear -M2 M3; lia)); [|exact Hc].
    clear -Hz. destruct Hz as [H|[H|[H|[H|H]]]]; [left | right; left | right; right; left | right; right; right; left | right; right; right; right]; lia. }

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz. apply NZE. intros Hc.
    destruct (rtc_foot_cases G z Hz) as [K|[K|[K|[K|K]]]].
    - exact (NE_img z K Hc).
    - apply (NE_T z); [left; fold T in K; clear -K; lia | exact Hc].
    - apply (env_out SB T (topG G) c nf mu (ag_ctx G) (ag_ctx G + 4096) z GEO C1 NF0 MUB ltac:(clear -K; lia)); [clear -CTX3; lia | clear -G13; lia | clear -CB; lia | exact Hc].
    - apply (env_out SB T (topG G) c nf mu (ag_dtls G) (ag_dtls G + 4096) z GEO C1 NF0 MUB ltac:(clear -K; lia)); [clear -DTLS3; lia | clear -G14; lia | clear -DB; lia | exact Hc].
    - apply (env_out SB T (topG G) c nf mu (ag_fsb G) (ag_fsb G + 11571200) z GEO C1 NF0 MUB ltac:(clear -K; lia)); [clear -S4; lia | clear -G10; lia | clear -WF; lia | exact Hc]. }
  assert (HFS : fs_inv (restrictv (fs_footb G) v3) Ar).
  { rewrite (restrictv_ext (fs_footb G) vE v3) by (intros z Hz; apply NZE; intros Hc; rewrite (ENVF z Hc) in Hz; discriminate).
    exact HF. }
  assert (HLS : live_sep Ar) by exact Hsep.
  assert (HLB : live_block_repr m3 Ar).
  { apply (live_block_repr_agree mE m3 A Ar eq_refl); [|intros b n Hin; exact (proj1 (Hsep b n Hin))|exact Hlive].
    intros b n z Hin Hz. apply AGm. exact (LIVE_OUT b n z Hin Hz). }
  assert (HPR : primary_repr m3 Ar).
  { unfold primary_repr. rewrite EG'. split; [unfold Ar, setclsA; cbn [aa_cls]; rewrite length_list_upd; exact PL|].
    split; [rewrite (ECSo 0) by (clear -C1; lia); exact P0|]. split; [rewrite (ECSo 31) by (clear -C1; lia); exact P31|].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|Hne].
    2: { rewrite (ECSo c' Hne ltac:(clear -Hc'; lia)).
         apply (class_repr_agree mE m3 G A Ar c' _ Hc'); [exact (eq_sym Hini) | reflexivity | reflexivity | intros b n Hin _ _; exact Hin | intros z Hz; exact Hz | | exact (PC c' Hc')].
         intros z Hz. apply AGm. exact (NE_cls c' z Hc' Hne Hz). }

    rewrite ECS'. unfold class_repr. cbv zeta. fold SB. fold ri fa rb.
    change (live_ids G Ar c) with (live_ids G A c). change (qall Ar) with (qall A). change (aa_live Ar) with (aa_live A).
    assert (RIS : forall off w, 0 <= off -> off + Z.of_nat w <= 128 -> forall k, (k < w)%nat -> m3 (ri + off + Z.of_nat k) = v3 (ri + off + Z.of_nat k)).
    { intros off w Ho Hw k Hk. apply MSP. unfold ri, region_info, kRegionInfoStride. rewrite kSpaceSize_val. clear -Ho Hw Hk C1. lia. }
    assert (CRI : forall off w v, 0 <= off -> off + Z.of_nat w <= 128 -> cell_ok v3 (mkACell (ri + off) w v) -> cell_ok m3 (mkACell (ri + off) w v)).
    { intros off w v Ho Hw Hcv. eapply cell_ok_agree; [|exact Hcv]. cbn [c_addr c_w]. intros k Hk. exact (RIS off w Ho Hw k Hk). }
    split; [apply CRI; [unfold RI_mutex; clear; lia | unfold RI_mutex; cbn; clear; lia | exact R1']|].
    split; [apply CRI; [unfold RI_num_freed; clear; lia | unfold RI_num_freed; cbn; clear; lia | exact R2']|].
    split; [apply CRI; [unfold RI_mapped_free_array; clear; lia | unfold RI_mapped_free_array; cbn; clear; lia | exact R3']|].
    split; [apply CRI; [unfold RI_allocated_user; clear; lia | unfold RI_allocated_user; cbn; clear; lia | exact R4']|].
    split; [apply CRI; [unfold RI_allocated_meta; clear; lia | unfold RI_allocated_meta; cbn; clear; lia | exact R5']|].
    split; [apply CRI; [unfold RI_mapped_user; clear; lia | unfold RI_mapped_user; cbn; clear; lia | exact R6']|].
    split; [apply CRI; [unfold RI_mapped_meta; clear; lia | unfold RI_mapped_meta; cbn; clear; lia | exact R7']|].
    split; [apply CRI; [unfold RI_exhausted; clear; lia | unfold RI_exhausted; cbn; clear; lia | exact R8']|].
    split; [apply PRESX; exact PRI|].
    split; [exact Q1|]. split; [exact Q2|].
    split; [unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in *; clear -Q10 MCU; lia|].
    split; [exact Q3'|]. split; [exact Q4|].
    split; [split; [exact Q5 | unfold kFreeArraySize in *; clear -Q11 FCU; lia]|].
    assert (FAR : SB + 2 ^ 32 <= fa /\ fa + 2 ^ 29 <= SB + 2 ^ 37).
    { unfold fa, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. clear -C1. lia. }
    split.
    { intros i x Hi. eapply cell_ok_agree; [|exact (HFA i x Hi)]. cbn [c_addr c_w]. intros k Hk. apply MSP.
      pose proof (nth_error_Some_lt _ _ _ Hi) as L. unfold kFreeArraySize in *. clear -L Hk FAR Q5 Q11 FCU. lia. }
    split.
    {
      intros z Hz. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc)|]. rewrite (AGZ z Hn).
      destruct (Z_lt_dec z (fa + cs_mapped_free_array cs)) as [LT|GE]; [|exfalso; apply Hn; apply HNF; clear -Hz GE; lia].
      destruct (Z_lt_dec z (fa + 4 * nf)) as [LT2|GE2]; [|apply PR; clear -LT GE2; lia].
      assert (Hz0 : fa <= z) by (pose proof (Zle_0_nat (length (cs_free_array csR))); clear -Hz H; lia).
      set (i := Z.to_nat ((z - fa) / 4)).
      assert (Hi : (i < length (cs_free_array cs))%nat).
      { unfold i. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; clear -Hz0; lia). fold nf. apply Z.div_lt_upper_bound; clear -LT2 Hz0; lia. }
      pose proof (R9 i _ (nth_error_nth' (cs_free_array cs) 0 Hi)) as Hcell.
      assert (Ei : Z.of_nat i = (z - fa) / 4) by (unfold i; apply Z2Nat.id; apply Z.div_pos; clear -Hz0; lia).
      pose proof (Z.div_mod (z - fa) 4 ltac:(clear; lia)) as DM. pose proof (Z.mod_pos_bound (z - fa) 4 ltac:(clear; lia)) as MB.
      specialize (Hcell (Z.to_nat ((z - fa) mod 4)) ltac:(cbn [c_w]; clear -MB; lia)). cbn [c_addr c_w] in Hcell.
      rewrite Z2Nat.id in Hcell by (clear -MB; lia). rewrite Ei in Hcell.
      replace (fa + 4 * ((z - fa) / 4) + (z - fa) mod 4) with z in Hcell by (clear -DM; lia).
      eexists. exact Hcell. }
    split.
    { intros x Hx. destruct (Q6 x ltac:(rewrite app_assoc; apply in_or_app; left; exact Hx)) as (X1 & X2 & X3).
      unfold kCompactPtrScale. rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 4) with 16. replace (x * 16) with (16 * x) by (clear; lia).
      split; [exact X1|]. split; [exact X2 | exact X3]. }
    split.
    {
      intros z Hz HL. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc)|]. rewrite (AGZ z Hn).
      destruct (Z_lt_dec z (rb + mu)) as [LT|GE]; [apply PU; [clear -Hz LT; lia | exact HL] | exfalso; apply Hn; apply HNU; fold mu; clear -Hz GE; lia]. }
    split.
    { intros z Hz. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc)|]. rewrite (AGZ z Hn).
      destruct (Z_lt_dec z (Sh (rb + mu))) as [LT|GE]; [apply PSH; clear -Hz LT; lia | exfalso; apply Hn; apply HNS; fold mu; clear -Hz GE; lia]. }
    split; [apply PRESX; exact PE|].
    split; [exact (proj2 (NoDup_ListNoDup _) Q7)|].
    split; [intros b n Hin Hp Hcl; destruct (LV b n Hin Hp Hcl) as (V1 & V2 & V3); split; [exact V1|]; split; [exact V2 | clear -V3 HAUm; lia]|].
    split.
    { intros _. destruct (CI Hini) as (K1 & K2 & K3 & K4 & K5). fold T in K1, K2, K3, K4 |- *. fold pce in K1, K2, K3, K4 |- *.
      assert (PCB : T + 288 <= pce /\ pce + 80 <= T + 2688) by (unfold pce; clear -C1; lia).
      split; [eapply cell_ok_agree; [|exact HCN]; cbn [c_addr c_w]; intros k Hk; apply MTH; clear -Hk PCB; lia|].
      split; [apply CELL; [|exact K2]; intros k Hk Hc; apply (own_out SB T (topG G) c nf mu (pce + 4 + Z.of_nat k) GEO C1 NF0 NF4 MUB); [|exact Hc];
              right; right; right; unfold pce; clear -Hk; lia|].
      split; [apply CELL; [|exact K3]; intros k Hk Hc; apply (own_out SB T (topG G) c nf mu (pce + 8 + Z.of_nat k) GEO C1 NF0 NF4 MUB); [|exact Hc];
              right; right; right; unfold pce; clear -Hk; lia|].
      split; [|exact HKC].
      intros i x Hi. eapply cell_ok_agree; [|exact (HCC i x Hi)]. cbn [c_addr c_w]. intros k Hk. apply MTH.
      pose proof (nth_error_Some_lt _ _ _ Hi) as L. pose proof (max_count_le16 c C1) as M16. clear -L Hk PCB HKC M16. unfold pce in *. lia. }
    split; [intros X; discriminate X|].
    split; [exact Q8|].
    split; [unfold slots; rewrite Q9, length_app; f_equal; clear; lia|].
    exact (conj Q10 Q11). }
  assert (LIVM : forall z, in_rangesZ (aa_live A) z -> in_rangesZ (aa_live Ar) z) by (intros z Hz; exact Hz).
  assert (HSR : secondary_repr m3 Ar).
  { refine (secondary_repr_agree mE m3 A Ar eq_refl eq_refl eq_refl _ _ _ LIVM Hsec).
    - intros i ch z Hi Hz. apply AGm. exact (NE_sec i ch z Hi Hz).
    - intros z Hz. apply AGm. intros Hc. destruct Hsec as (_ & _ & SC2 & _ & SC45 & _). fold G in SC45, Hz. destruct SC45 as [_ (SC4a & _ & SC5 & _ & SC4)].
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in SC4. unfold kPtrArrayReserve in SC2, SC4, PAB3, PABT3.
      apply (env_out SB T (topG G) c nf mu (ag_pab G) (ag_pab G + 2 ^ 23) z GEO C1 NF0 MUB ltac:(clear -Hz SC2; lia)); [clear -PAB3; lia | clear -PABT3; lia | clear -SC4; lia | exact Hc].
    - intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HQR : quarantine_repr mE A -> quarantine_repr m3 Ar).
  { intros HqE. refine (quarantine_repr_agreeR mE m3 A Ar eq_refl eq_refl eq_refl eq_refl _ _ _ _ HqE).
    - intros c'. unfold Ar, setclsA, nthZ. cbn [aa_cls]. destruct (Nat.eq_dec (Z.to_nat c) (Z.to_nat c')) as [E|NE].
      + rewrite <- E. rewrite nth_list_upd_same by exact Hlenc. exact HAUm.
      + rewrite nth_list_upd_other by exact NE. clear; lia.
    - intros z Hz. apply AGm. exact (QF_OUT z Hz).
    - intros z Hz. apply AGm. apply NE_T. left. fold G T in Hz. clear -Hz. lia.
    - intros z Hz. apply AGm. apply NE_img. unfold QG, IMG_LO, IMG_HI in *. clear -Hz. lia. }
  assert (HQP' : q_pure Ar).
  { apply (q_pure_mono A Ar eq_refl eq_refl eq_refl); [|exact HQP].
    intros c'. unfold SegQ_wf2.cls_of, Ar, setclsA, nthZ. cbn [aa_cls]. destruct (Nat.eq_dec (Z.to_nat c) (Z.to_nat c')) as [E|NE].
    - rewrite <- E. rewrite nth_list_upd_same by exact Hlenc. exact HAUm.
    - rewrite nth_list_upd_other by exact NE. clear; lia. }
  assert (HQM : cell_ok m3 (mkACell (QG + 72) 8 kQuarantineMin)).
  { eapply cell_ok_agree; [|exact HQMIN]. cbn [c_addr c_w]. intros k Hk. apply AGm. apply NE_img. unfold QG, IMG_LO, IMG_HI. clear -Hk. lia. }
  assert (HIA : ia_inv m3 Ar).
  { refine (ia_inv_agree mE m3 A Ar eq_refl _ Hia). intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HTI : thread_inv m3 G).
  { destruct HTH as [TH1 TH2]. fold G T in TH1, TH2. unfold thread_inv. fold T. split.
    - rewrite AGm; [exact TH1|]. apply NE_T. right. clear. lia.
    - apply PRESX. exact TH2. }
  assert (HMI : misc_inv m3).
  { refine (misc_inv_agree mE m3 _ Hmisc). intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HDEP : depot_wf m3 Ar).
  { unfold depot_wf in Hdep |- *. change (aa_depot Ar) with (aa_depot A). eapply depot_mem_frame; [|exact Hdep]. intros a Ha. apply AGm. intros Hc.
    assert (BLK : forall bb L, In (bb, L) (dblocks (aa_depot A)) -> bb <= a < bb + L -> False).
    { intros bb L Hbb Hab. destruct (DEP3 (bb, L) Hbb) as (DI & ST & _ & _ & _ & SS & _). unfold sepZ in ST, SS. cbn [fst snd] in DI, ST, SS. fold T in ST. fold SB in SS.
      destruct DI as (_ & _ & _ & _ & WB). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB. rewrite kSpaceSize_val in SS.
      apply (env_out SB T (topG G) c nf mu bb (bb + L) a GEO C1 NF0 MUB Hab); [clear -SS; lia | clear -ST; lia | clear -WB; lia | exact Hc]. }
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - apply (NE_img a); [|exact Hc]. unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. unfold IMG_LO, IMG_HI. clear -Hs. lia.
    - apply (BLK bb NBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
    - apply (BLK bb FBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb]. }
  assert (HI3' : inv3 Ar).
  { pose proof HI3c as (X1' & X2' & X3' & X4' & X5' & X6' & X7' & X8' & X9'). split; [exact X1'|]. split; [exact X2'|]. split; [exact X3'|].
    split.
    { intros z Hz. destruct (X4' z Hz) as [Y1 Y2]. split; [exact Y1|].
      intros c' x' Hc' Hx'. destruct (Z.eq_dec c' c) as [->|Hne]; [|rewrite (ECSo c' Hne ltac:(clear -Hc'; lia)) in Hx'; exact (Y2 c' x' Hc' Hx')].
      rewrite ECS' in Hx'.
      destruct (Q6 x' ltac:(apply in_or_app; right; apply in_or_app; left; exact Hx')) as (V1 & V2 & V3).
      apply (qfoot_slot_out A mE HG HI3c HQP Hsec HAU c x' z C1 V1 V2); [| |exact Hz].
      - unfold kUserSpaceSize, kRegionSize, kFreeArraySize in MCU. clear -V3 Q2 Q10 MCU. lia.
      - intros Hq'. apply NoDup_app_remove_l in Q7. apply (NoDup_app_in _ _ x' Q7 Hx'). apply in_or_app. right. exact Hq'. }
    split; [exact X5'|]. split; [exact X6'|]. split; [exact X7'|]. split; [exact X8'|]. intros _. reflexivity. }
  assert (HA' : AInvQ Ar rho3 tp md).
  { unfold AInvQ. cbv zeta. rewrite EG'. fold v3. split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|].
    split; [|split; [exact HMD | split; [exact HI3' | exact HBT]]].
    fold m3. split; [exact HLS|]. split; [exact HLB|]. split; [exact HPR|]. split; [exact HSR|]. split; [split; [exact HQP' | exact HQM]|].
    split; [exact HDEP|]. split; [exact HIA|]. split; [exact HTI | exact HMI]. }
  split; [exact HA'|]. split; [exact HQR|].

  assert (HFv : fs_inv (restrictv (fs_footb G) vE) A) by exact HF.
  assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ envR SB T c nf mu a -> rm rho3 (Z_to_bv 64 a) = rm rhoE (Z_to_bv 64 a)).
  { intros a Ha Hn. destruct (Z_lt_dec a IMG_LO) as [LO|NLO]; [|destruct (Z_le_dec IMG_HI a) as [HI|NHI]].
    - rewrite <- (view_rm_off (rm rho3) a Ha (or_introl LO)), <- (view_rm_off (rm rhoE) a Ha (or_introl LO)). exact (NZE a Hn).
    - rewrite <- (view_rm_off (rm rho3) a Ha (or_intror HI)), <- (view_rm_off (rm rhoE) a Ha (or_intror HI)). exact (NZE a Hn).
    - apply HRMI. clear -NLO NHI. lia. }
  assert (DEFM : forall a, IMG_HI <= a < 2 ^ 64 -> rm rhoE (Z_to_bv 64 a) <> None -> rm rho3 (Z_to_bv 64 a) <> None).
  { intros a Ha Hd. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold IMG_HI in Ha; clear -Ha; lia).
    rewrite <- (view_rm_off (rm rho3) a Ha' (or_intror (proj1 Ha))). rewrite <- (view_rm_off (rm rhoE) a Ha' (or_intror (proj1 Ha))) in Hd.
    change (v3 a <> None). change (vE a <> None) in Hd. destruct (ZND a) as [Hc|Hn]; [destruct (PRES a Hc) as [b Hb]; rewrite Hb; discriminate | rewrite (VO a Hn); exact Hd]. }
  split.
  2: { intros x0 j Hx Hj Hdef.
       assert (Bx : 0 <= x0 < 2 ^ 47).
       { destruct Hx as [[CX _]|GX]; [exact (proj1 (client_addr_bounds CST HCST A x0 _ HG HFv Hsep CX))|].
         destruct (HXGL x0 GX) as [XG1 XG2]. unfold IMG_HI in XG2. clear -XG1 XG2. lia. }
       unfold word_byte. apply DEFM; [|exact Hdef].
       pose proof (Z.div_mod (Sh x0) 8 ltac:(clear; lia)) as DM. pose proof (Z.mod_pos_bound (Sh x0) 8 ltac:(clear; lia)) as MB.
       unfold Sh, SHADOW_OFF, IMG_HI in DM, MB |- *. pose proof (Z.div_le_mono 0 x0 8 ltac:(clear; lia) ltac:(clear -Bx; lia)) as D0.
       pose proof (Z.div_lt_upper_bound x0 8 (2 ^ 44) ltac:(clear; lia) ltac:(clear -Bx; lia)) as D1. change (0 / 8) with 0 in D0.
       clear -Hj DM MB D0 D1. lia. }
  intros a Ha Hcl.

  assert (NOC : forall y, client_addrA CST A y ->
            (exists b n, In (b, n) (aa_live A) /\ b <= y < b + n)
            \/ (0 <= y < 2 ^ 47 /\ (y + 8 <= SB + 2 ^ 32 \/ SB + 2 ^ 37 + 4096 <= y) /\ (y + 8 <= T + 288 \/ T + 2688 <= y) /\ (y + 8 <= 2147450880 \/ 17594333495296 <= y))).
  { intros y Hy.
    destruct (client_addr_cases CST A y _ HFv Hy) as [S|[L|[FR|[C|FL]]]].
    - right. fold G in S. clear -S S2 G5 TG. lia.
    - left. exact L.
    - right. destruct FR as (c0 & p0 & Hc0 & Hp0 & _ & Hyf). pose proof (fs_geom_nums G c0 p0 HG Hc0 Hp0) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Hyf. clear -Hyf M S4 G10 WF G2 G3 TG. lia.
    - right. destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in X. clear -X S1 TI. lia.
    - right. destruct FL as (c0 & p0 & Hc0 & Hp0 & _ & ->). pose proof (fs_geom_nums G c0 p0 HG Hc0 Hp0) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G. unfold fs_flags. rewrite FS_kFlagsOffset_val.
      unfold fs_flags in M. rewrite FS_kFlagsOffset_val in M. clear -M S4 G10 WF G2 G3 TG. lia. }
  assert (SHY : forall y, 0 <= y < 2 ^ 47 -> (y + 8 <= SB + 2 ^ 32 \/ SB + 2 ^ 37 + 4096 <= y) -> ~ envR SB T c nf mu (Sh y)).
  { intros y By Hy Hc.
    pose proof (Z.div_mod y 8 ltac:(clear; lia)) as DY. pose proof (Z.mod_pos_bound y 8 ltac:(clear; lia)) as MY.
    apply (env_sh_out SB T (topG G) c nf mu (8 * (y / 8)) (8 * (y / 8) + 8) (Sh y) GEO C1 NF0 MUB); [|clear -By DY MY; lia|clear -By DY MY; lia|clear -Hy DY MY; lia|exact Hc].
    unfold Sh. replace (8 * (y / 8) / 8) with (y / 8) by (rewrite Z.mul_comm, Z.div_mul; clear; lia).
    replace ((8 * (y / 8) + 8) / 8) with (y / 8 + 1) by (replace (8 * (y / 8) + 8) with ((y / 8 + 1) * 8) by (clear; lia); rewrite Z.div_mul; clear; lia).
    clear. lia. }
  apply RMO; [exact Ha|].
  destruct Hcl as [[CL1 _]|[CL1 _]].
  - destruct (NOC a CL1) as [(b & n & Hbn & Hab)|(B1 & B2 & B3 & B4)].
    + apply (LIVE_OUT b n a Hbn). left. pose proof (rz_bound n). clear -Hab H. lia.
    + intros Hc. apply (env_out SB T (topG G) c nf mu a (a + 8) a GEO C1 NF0 MUB ltac:(clear; lia)); [exact B2 | exact B3 | exact B4 | exact Hc].
  - destruct CL1 as [(y & Cy & ->)|(y & Gy & ->)].
    + destruct (NOC y Cy) as [(b & n & Hbn & Hyb)|(B1 & B2 & B3 & B4)].
      * apply (LIVE_OUT b n (Sh y) Hbn). right.
        assert (B8 : b mod 8 = 0).
        { destruct (is_primary n) eqn:HP.
          - pose proof (live_prim_czone A HG SG3c mE Hsep Hprim0 b n Hbn HP) as LPC. cbv zeta in LPC. destruct LPC as (D1 & O0 & OM & OE & _ & (RZN & _) & _). fold SB in O0, OM, OE.
            destruct (Size_facts _ D1) as (SZ' & SM'). destruct (mod8_of_slot _ _ (proj1 SZ') SM' OM) as [Mo _].
            pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep.rz_facts n) as (_ & RZ16).
            set (o' := b - rz n - (SB + ClassID (needed n) * 2 ^ 32)) in *.
            assert (Eb : b = SB + ClassID (needed n) * 2 ^ 32 + o' + rz n) by (unfold o'; clear; lia).
            destruct (proj1 (Z.mod_divide SB (2 ^ 16) ltac:(clear; lia)) S3) as [qs Hqs]. destruct (proj1 (Z.mod_divide o' 8 ltac:(clear; lia)) Mo) as [qo Hqo].
            destruct (proj1 (Z.mod_divide (rz n) 16 ltac:(clear; lia)) RZ16) as [qr Hqr].
            rewrite Eb. apply Z.mod_divide; [clear; lia|]. exists (qs * 2 ^ 13 + ClassID (needed n) * 2 ^ 29 + qo + qr * 2). clear -Hqs Hqo Hqr. lia.
          - destruct (live_sec_map A mE Hsep Hsec HI3c b n Hbn HP) as (i & ch & Hi & Eb & _ & _ & _ & D6 & _). unfold PG in Eb, D6.
            destruct (proj1 (Z.mod_divide (sc_map_beg ch) 4096 ltac:(clear; lia)) D6) as [k0 Hk0]. apply Z.mod_divide; [clear; lia|]. exists (k0 * 512 + 768). clear -Eb Hk0. lia. }
        unfold Sh. destruct (proj1 (Z.mod_divide b 8 ltac:(clear; lia)) B8) as [qb Hqb].
        pose proof (Z.div_mod y 8 ltac:(clear; lia)) as DY. pose proof (Z.mod_pos_bound y 8 ltac:(clear; lia)) as MY.
        pose proof (Z.div_mod (n + 7) 8 ltac:(clear; lia)) as DN. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(clear; lia)) as MN.
        rewrite Hqb. rewrite Z.div_mul by (clear; lia). clear -Hyb Hqb DY MY DN MN. lia.
      * exact (SHY y B1 B2).
    + destruct (HXGL y Gy) as [Y1 Y2]. unfold IMG_HI in Y2. apply (SHY y); [clear -Y1 Y2; lia | left; clear -Y2 S1; lia].
Qed.
End R.
End RebuildG.

(* [comment removed for export] *)
Module SpineCallocS8i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "ss_facts"; "SVar"; "ss_next"; "SPBranch"; "SLit"; "swf"; "SPNot"; "SPUle"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "F_gen"; "C7p"; "C8"; "C8p"; "V_CLS"; "V_ND"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "n8e"; "BP"; "C7"; "LPe"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8"; "E7c1'"; "E7c2'"; "E7q1'"; "E7q2'"; "a0e7"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "tab_ok"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.SpineCallocS8i.INST"; "s8a_0"; "s8b_0"; "s8c_0"; "s8d_0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CallocMemoSP.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Lemma Cert7_0 : ltac2:(tb__ "0|1|
S3S4S44S18Ufa0S6S2eZ3c8bcS6S2eZ3ca04S7S2eA1A3A3S17S6S1S2cVW;Vst;Vtmax;A3S7S1A1M0A3S6S1S1bVW;Vst;Vtmax;A3S6S1S1cVW;Vst;Vtmax;A3S6S1S1dVW;Vst;Vtmax;A3G0A3A3A3A6S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma OV7a_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS26VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma OV7b_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS27VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma TAB7a_0 : ltac2:(tb__ "0|0|
S3S4S41P9dS26VW;Vst;Vtmax;A3S3fZ208S42S43S36S37S38S36S39A1A1A1A1A1A1A5S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. refine (eq_ind (CertMallocSP.creg7a (Wcan 0) UStopLe 2) (fun c => tab_ok 157 c ClassID 520 8128%nat = true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8i.TAB7a_0 m_creg7a _). MemoFast.vmc1. Qed.
Lemma TAB7b_0 : ltac2:(tb__ "0|0|
S3S4S41P9dS27VW;Vst;Vtmax;A3S3fZ18U3eA5S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W7a_0 : ltac2:(tb__ "0|0|
S3S4S14S0S31U0Vst;Vtmax;A3A1A1S5A3").
Proof. cbv beta zeta delta [W st tmax E7c1']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W7b_0 : ltac2:(tb__ "0|0|
S3S4S14S0S32U0Vst;Vtmax;A3A1A1S5A3").
Proof. cbv beta zeta delta [W st tmax E7c2']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D7a_0 : ltac2:(tb__ "0|4|
S3ScSaS8SaSeSeA2M0A1M1S8SdA1M2A2M3A1S30S0S1bVW;Vst;Vtmax;A3A1S0S31U0Vst;Vtmax;A3A1A2SbG3S9G1G2S6G0S9SeSeS26VW;Vst;Vtmax;A3S10S24A1A4S7G0A1A3S7SdA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E7c1']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D7b_0 : ltac2:(tb__ "0|4|
S3ScSaS8SaSeSeA2M0A1M1S8SdA1M2A2M3A1S30S0S1cVW;Vst;Vtmax;A3A1S0S32U0Vst;Vtmax;A3A1A2SbG3S9G1G2S6G0S9SeSeS27VW;Vst;Vtmax;A3S10S24A1A4S7G0A1A3S7SdA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E7c2']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S3S2fS11S0S31U0Vst;Vtmax;A3A1A1S11S0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E7c1']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S3S2fS11S0S32U0Vst;Vtmax;A3A1A1S11S0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E7c2']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma G7a_0 : ltac2:(tb__ "0|0|
S1aSdS20SfS0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma G7b_0 : ltac2:(tb__ "0|0|
S1aSdS20SfS0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F7a_0 : ltac2:(tb__ "0|0|
S19SdS12S3aS13Z200A1S10S25A1A3SfS0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F7b_0 : ltac2:(tb__ "0|0|
S19SdS15S12S3aS13Z200A1S10S25A1A3A1SfS0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s8a_0 : ltac2:(tb__ "0|0|
S3d") := ltac2:(tb__ "0|0|
S3cS17S0S31U0Vst;Vtmax;A3A1S0S22VW;Vst;Vtmax;A3A1A3").
Definition s8b_0 : ltac2:(tb__ "0|0|
S3d") := ltac2:(tb__ "0|0|
S3cS17S0S32U0Vst;Vtmax;A3A1S0S22VW;Vst;Vtmax;A3A1A3").
Lemma ENT8a_0 : ltac2:(tb__ "0|0|
S3S4S2S31U0Vst;Vtmax;A3S22VW;Vst;Vtmax;A3S45A3S5A3").
Proof. unfold s8a_0. cbv beta zeta delta [W st tmax E7c1' s8a_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENT8b_0 : ltac2:(tb__ "0|0|
S3S4S2S32U0Vst;Vtmax;A3S22VW;Vst;Vtmax;A3S46A3S5A3").
Proof. unfold s8b_0. cbv beta zeta delta [W st tmax E7c2' s8b_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID8a_0 : ltac2:(tb__ "0|0|
S3S4S3eS45S17A2S5A3").
Proof. unfold s8a_0. cbv beta zeta delta [W st tmax E7c1' s8a_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID8b_0 : ltac2:(tb__ "0|0|
S3S4S3eS46S17A2S5A3").
Proof. unfold s8b_0. cbv beta zeta delta [W st tmax E7c2' s8b_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma G7p_0 : ltac2:(tb__ "0|0|
S1aSdS20SfS0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F7p_0 : ltac2:(tb__ "0|0|
S19SdS15S12S3bS10PcA1S2aA3A1SfS0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W7p_0 : ltac2:(tb__ "0|0|
S3S4S14S0S21VW;Vst;Vtmax;A3A1A1S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D7p_0 : ltac2:(tb__ "0|4|
S3ScSaS8SaSeSeA2M0A1M1S8SdA1M2A2M3A1S30S0S1dVW;Vst;Vtmax;A3A1S0S21VW;Vst;Vtmax;A3A1A2SbG3S9G1G2S6G0S9SeSeS35S2bA4S7G0A1A3S6SdS16S13Z1A1S2dA2S7SdA1A3A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX7p_0 : ltac2:(tb__ "0|0|
S3S2fS11S0S21VW;Vst;Vtmax;A3A1A1S11S0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F7an_0 : ltac2:(tb__ "0|0|
S19SdS12S3bS10PcA1S2aA3SfS0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F7bn_0 : ltac2:(tb__ "0|0|
S19SdS12S3bS10PcA1S2aA3SfS0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert7p_0 : ltac2:(tb__ "0|1|
S3S4S44S18Ufa0S6S2eZ3ca04S7S2eA1A3S17S6S1S21VW;Vst;Vtmax;A3S7S1A1M0A3S6S1S1eVW;Vst;Vtmax;A3S6S1S1fVW;Vst;Vtmax;A3G0A3A3A6S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma OV7c_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS28VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma OV7d_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS29VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma TAB7c_0 : ltac2:(tb__ "0|0|
S3S4S41P9dS28VW;Vst;Vtmax;A3S3fZ208S42S43S36S37S38S36S39A1A1A1A1A1A1A5S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. refine (eq_ind (CertMallocSP.creg7c (Wcan 0) UStopLe 2) (fun c => tab_ok 157 c ClassID 520 8128%nat = true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8i.TAB7c_0 m_creg7c _). MemoFast.vmc1. Qed.
Lemma TAB7d_0 : ltac2:(tb__ "0|0|
S3S4S41P9dS29VW;Vst;Vtmax;A3S3fZ18U3eA5S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W7c_0 : ltac2:(tb__ "0|0|
S3S4S14S0S33U0Vst;Vtmax;A3A1A1S5A3").
Proof. cbv beta zeta delta [W st tmax E7q1']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W7d_0 : ltac2:(tb__ "0|0|
S3S4S14S0S34U0Vst;Vtmax;A3A1A1S5A3").
Proof. cbv beta zeta delta [W st tmax E7q2']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D7c_0 : ltac2:(tb__ "0|4|
S3ScSaS8SaSeSeA2M0A1M1S8SdA1M2A2M3A1S30S0S1eVW;Vst;Vtmax;A3A1S0S33U0Vst;Vtmax;A3A1A2SbG3S9G1G2S6G0S9SeSeS28VW;Vst;Vtmax;A3S10S24A1A4S7G0A1A3S7SdA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E7q1']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D7d_0 : ltac2:(tb__ "0|4|
S3ScSaS8SaSeSeA2M0A1M1S8SdA1M2A2M3A1S30S0S1fVW;Vst;Vtmax;A3A1S0S34U0Vst;Vtmax;A3A1A2SbG3S9G1G2S6G0S9SeSeS29VW;Vst;Vtmax;A3S10S24A1A4S7G0A1A3S7SdA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E7q2']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX7c_0 : ltac2:(tb__ "0|0|
S3S2fS11S0S33U0Vst;Vtmax;A3A1A1S11S0S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E7q1']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX7d_0 : ltac2:(tb__ "0|0|
S3S2fS11S0S34U0Vst;Vtmax;A3A1A1S11S0S1fVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E7q2']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma G7c_0 : ltac2:(tb__ "0|0|
S1aSdS20SfS0S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma G7d_0 : ltac2:(tb__ "0|0|
S1aSdS20SfS0S1fVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F7c_0 : ltac2:(tb__ "0|0|
S19SdS12S3aS13Z200A1S10S25A1A3SfS0S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F7d_0 : ltac2:(tb__ "0|0|
S19SdS15S12S3aS13Z200A1S10S25A1A3A1SfS0S1fVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s8c_0 : ltac2:(tb__ "0|0|
S3d") := ltac2:(tb__ "0|0|
S3cS17S0S33U0Vst;Vtmax;A3A1S0S23VW;Vst;Vtmax;A3A1A3").
Definition s8d_0 : ltac2:(tb__ "0|0|
S3d") := ltac2:(tb__ "0|0|
S3cS17S0S34U0Vst;Vtmax;A3A1S0S23VW;Vst;Vtmax;A3A1A3").
Lemma ENT8c_0 : ltac2:(tb__ "0|0|
S3S4S2S33U0Vst;Vtmax;A3S23VW;Vst;Vtmax;A3S47A3S5A3").
Proof. unfold s8c_0. cbv beta zeta delta [W st tmax E7q1' s8c_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENT8d_0 : ltac2:(tb__ "0|0|
S3S4S2S34U0Vst;Vtmax;A3S23VW;Vst;Vtmax;A3S48A3S5A3").
Proof. unfold s8d_0. cbv beta zeta delta [W st tmax E7q2' s8d_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID8c_0 : ltac2:(tb__ "0|0|
S3S4S3eS47S17A2S5A3").
Proof. unfold s8c_0. cbv beta zeta delta [W st tmax E7q1' s8c_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID8d_0 : ltac2:(tb__ "0|0|
S3S4S3eS48S17A2S5A3").
Proof. unfold s8d_0. cbv beta zeta delta [W st tmax E7q2' s8d_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
End INST.
End SpineCallocS8i.

