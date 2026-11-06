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
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je i9.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.

(* [comment removed for export] *)
Module SpineCallocS8iW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "ss_facts"; "SVar"; "ss_next"; "SPBranch"; "SLit"; "swf"; "SPNot"; "SPUle"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "F_gen"; "C7p"; "C8"; "C8p"; "V_CLS"; "V_ND"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "n8e"; "BP"; "C7"; "LPe"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8"; "E7c1'"; "E7c2'"; "E7q1'"; "E7q2'"; "a0e7"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "tab_ok"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS8iW1.INST"; "s8a_0"; "s8b_0"; "s8c_0"; "s8d_0"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CallocMemoSPW1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Lemma Cert7_0 : ltac2:(tb__ "0|1|
S3S4S44S18Ufa0S6S2eZ3c8bcS6S2eZ3ca04S7S2eA1A3A3S17S6S1S2cVW;Vst;Vtmax;A3S7S1A1M0A3S6S1S1bVW;Vst;Vtmax;A3S6S1S1cVW;Vst;Vtmax;A3S6S1S1dVW;Vst;Vtmax;A3G0A3A3A3A6S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma OV7a_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS26VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma OV7b_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS27VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma TAB7a_0 : ltac2:(tb__ "0|0|
S3S4S41P9dS26VW;Vst;Vtmax;A3S3fZ208S42S43S36S37S38S36S39A1A1A1A1A1A1A5S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. refine (eq_ind (CertMallocSP.creg7a (Wcan 0) UStopLe 2) (fun c => tab_ok 157 c ClassID 520 8128%nat = true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8i.TAB7a_0 m_creg7a _). MemoFast.vmc1. Qed.
Lemma TAB7b_0 : ltac2:(tb__ "0|0|
S3S4S41P9dS27VW;Vst;Vtmax;A3S3fZ18U3eA5S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W7a_0 : ltac2:(tb__ "0|0|
S3S4S14S0S31U1Vst;Vtmax;A3A1A1S5A3").
Proof. cbv beta zeta delta [W st tmax E7c1']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W7b_0 : ltac2:(tb__ "0|0|
S3S4S14S0S32U1Vst;Vtmax;A3A1A1S5A3").
Proof. cbv beta zeta delta [W st tmax E7c2']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma D7a_0 : ltac2:(tb__ "0|4|
S3ScSaS8SaSeSeA2M0A1M1S8SdA1M2A2M3A1S30S0S1bVW;Vst;Vtmax;A3A1S0S31U1Vst;Vtmax;A3A1A2SbG3S9G1G2S6G0S9SeSeS26VW;Vst;Vtmax;A3S10S24A1A4S7G0A1A3S7SdA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E7c1']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma D7b_0 : ltac2:(tb__ "0|4|
S3ScSaS8SaSeSeA2M0A1M1S8SdA1M2A2M3A1S30S0S1cVW;Vst;Vtmax;A3A1S0S32U1Vst;Vtmax;A3A1A2SbG3S9G1G2S6G0S9SeSeS27VW;Vst;Vtmax;A3S10S24A1A4S7G0A1A3S7SdA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E7c2']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S3S2fS11S0S31U1Vst;Vtmax;A3A1A1S11S0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E7c1']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S3S2fS11S0S32U1Vst;Vtmax;A3A1A1S11S0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E7c2']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma G7a_0 : ltac2:(tb__ "0|0|
S1aSdS20SfS0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma G7b_0 : ltac2:(tb__ "0|0|
S1aSdS20SfS0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma F7a_0 : ltac2:(tb__ "0|0|
S19SdS12S3aS13Z200A1S10S25A1A3SfS0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma F7b_0 : ltac2:(tb__ "0|0|
S19SdS15S12S3aS13Z200A1S10S25A1A3A1SfS0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition s8a_0 : ltac2:(tb__ "0|0|
S3d") := ltac2:(tb__ "0|0|
S3cS17S0S31U1Vst;Vtmax;A3A1S0S22VW;Vst;Vtmax;A3A1A3").
Definition s8b_0 : ltac2:(tb__ "0|0|
S3d") := ltac2:(tb__ "0|0|
S3cS17S0S32U1Vst;Vtmax;A3A1S0S22VW;Vst;Vtmax;A3A1A3").
Lemma ENT8a_0 : ltac2:(tb__ "0|0|
S3S4S2S31U1Vst;Vtmax;A3S22VW;Vst;Vtmax;A3S45A3S5A3").
Proof. unfold s8a_0. cbv beta zeta delta [W st tmax E7c1' s8a_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma ENT8b_0 : ltac2:(tb__ "0|0|
S3S4S2S32U1Vst;Vtmax;A3S22VW;Vst;Vtmax;A3S46A3S5A3").
Proof. unfold s8b_0. cbv beta zeta delta [W st tmax E7c2' s8b_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID8a_0 : ltac2:(tb__ "0|0|
S3S4S3eS45S17A2S5A3").
Proof. unfold s8a_0. cbv beta zeta delta [W st tmax E7c1' s8a_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID8b_0 : ltac2:(tb__ "0|0|
S3S4S3eS46S17A2S5A3").
Proof. unfold s8b_0. cbv beta zeta delta [W st tmax E7c2' s8b_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma G7p_0 : ltac2:(tb__ "0|0|
S1aSdS20SfS0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma F7p_0 : ltac2:(tb__ "0|0|
S19SdS15S12S3bS10PcA1S2aA3A1SfS0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W7p_0 : ltac2:(tb__ "0|0|
S3S4S14S0S21VW;Vst;Vtmax;A3A1A1S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma D7p_0 : ltac2:(tb__ "0|4|
S3ScSaS8SaSeSeA2M0A1M1S8SdA1M2A2M3A1S30S0S1dVW;Vst;Vtmax;A3A1S0S21VW;Vst;Vtmax;A3A1A2SbG3S9G1G2S6G0S9SeSeS35S2bA4S7G0A1A3S6SdS16S13Z1A1S2dA2S7SdA1A3A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NX7p_0 : ltac2:(tb__ "0|0|
S3S2fS11S0S21VW;Vst;Vtmax;A3A1A1S11S0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma F7an_0 : ltac2:(tb__ "0|0|
S19SdS12S3bS10PcA1S2aA3SfS0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma F7bn_0 : ltac2:(tb__ "0|0|
S19SdS12S3bS10PcA1S2aA3SfS0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Cert7p_0 : ltac2:(tb__ "0|1|
S3S4S44S18Ufa0S6S2eZ3ca04S7S2eA1A3S17S6S1S21VW;Vst;Vtmax;A3S7S1A1M0A3S6S1S1eVW;Vst;Vtmax;A3S6S1S1fVW;Vst;Vtmax;A3G0A3A3A6S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma OV7c_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS28VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma OV7d_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS29VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma TAB7c_0 : ltac2:(tb__ "0|0|
S3S4S41P9dS28VW;Vst;Vtmax;A3S3fZ208S42S43S36S37S38S36S39A1A1A1A1A1A1A5S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. refine (eq_ind (CertMallocSP.creg7c (Wcan 0) UStopLe 2) (fun c => tab_ok 157 c ClassID 520 8128%nat = true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8i.TAB7c_0 m_creg7c _). MemoFast.vmc1. Qed.
Lemma TAB7d_0 : ltac2:(tb__ "0|0|
S3S4S41P9dS29VW;Vst;Vtmax;A3S3fZ18U3eA5S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W7c_0 : ltac2:(tb__ "0|0|
S3S4S14S0S33U1Vst;Vtmax;A3A1A1S5A3").
Proof. cbv beta zeta delta [W st tmax E7q1']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma W7d_0 : ltac2:(tb__ "0|0|
S3S4S14S0S34U1Vst;Vtmax;A3A1A1S5A3").
Proof. cbv beta zeta delta [W st tmax E7q2']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma D7c_0 : ltac2:(tb__ "0|4|
S3ScSaS8SaSeSeA2M0A1M1S8SdA1M2A2M3A1S30S0S1eVW;Vst;Vtmax;A3A1S0S33U1Vst;Vtmax;A3A1A2SbG3S9G1G2S6G0S9SeSeS28VW;Vst;Vtmax;A3S10S24A1A4S7G0A1A3S7SdA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E7q1']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma D7d_0 : ltac2:(tb__ "0|4|
S3ScSaS8SaSeSeA2M0A1M1S8SdA1M2A2M3A1S30S0S1fVW;Vst;Vtmax;A3A1S0S34U1Vst;Vtmax;A3A1A2SbG3S9G1G2S6G0S9SeSeS29VW;Vst;Vtmax;A3S10S24A1A4S7G0A1A3S7SdA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E7q2']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NX7c_0 : ltac2:(tb__ "0|0|
S3S2fS11S0S33U1Vst;Vtmax;A3A1A1S11S0S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E7q1']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma NX7d_0 : ltac2:(tb__ "0|0|
S3S2fS11S0S34U1Vst;Vtmax;A3A1A1S11S0S1fVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E7q2']. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma G7c_0 : ltac2:(tb__ "0|0|
S1aSdS20SfS0S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma G7d_0 : ltac2:(tb__ "0|0|
S1aSdS20SfS0S1fVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma F7c_0 : ltac2:(tb__ "0|0|
S19SdS12S3aS13Z200A1S10S25A1A3SfS0S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma F7d_0 : ltac2:(tb__ "0|0|
S19SdS15S12S3aS13Z200A1S10S25A1A3A1SfS0S1fVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Definition s8c_0 : ltac2:(tb__ "0|0|
S3d") := ltac2:(tb__ "0|0|
S3cS17S0S33U1Vst;Vtmax;A3A1S0S23VW;Vst;Vtmax;A3A1A3").
Definition s8d_0 : ltac2:(tb__ "0|0|
S3d") := ltac2:(tb__ "0|0|
S3cS17S0S34U1Vst;Vtmax;A3A1S0S23VW;Vst;Vtmax;A3A1A3").
Lemma ENT8c_0 : ltac2:(tb__ "0|0|
S3S4S2S33U1Vst;Vtmax;A3S23VW;Vst;Vtmax;A3S47A3S5A3").
Proof. unfold s8c_0. cbv beta zeta delta [W st tmax E7q1' s8c_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma ENT8d_0 : ltac2:(tb__ "0|0|
S3S4S2S34U1Vst;Vtmax;A3S23VW;Vst;Vtmax;A3S48A3S5A3").
Proof. unfold s8d_0. cbv beta zeta delta [W st tmax E7q2' s8d_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID8c_0 : ltac2:(tb__ "0|0|
S3S4S3eS47S17A2S5A3").
Proof. unfold s8c_0. cbv beta zeta delta [W st tmax E7q1' s8c_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma SID8d_0 : ltac2:(tb__ "0|0|
S3S4S3eS48S17A2S5A3").
Proof. unfold s8d_0. cbv beta zeta delta [W st tmax E7q2' s8d_0]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
End INST.
End SpineCallocS8iW1.

(* [comment removed for export] *)
Module SegQ3D_qis.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "cons"; "bool"; "prod"; "nat"; "snd"; "true"; "S"; "false"; "length"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "qbatch"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "class_fresh"; "cs_cache"; "mkQB"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "JRI"; "JRD"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop"; "INVI"; "QI_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel"; "HVI"; "HVS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop"; "HVX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr"; "TR"; "JOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "is_primary"; "max_count"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "DQIs"; "RI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "it_cls"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SegQ3D_qis.QIStep"; "QI_full_step"; "QI_sec_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section QIStep.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Hypothesis HSBD : KQ_secband K.
Variables (A0 : AA) (rho0 : valuation).
Context {Q : assn} (X : trk Q).
Hypothesis HJD : ltac2:(tb__ "0|1|
ScS1SdA1M0G0S22VQ;VX;S18VK;VA0;Vrho0;R3R2R1A6A3Frest;Ftmp;FA;").
Hypothesis HJI : ltac2:(tb__ "0|1|
ScS0S0S5S1S4S0S0A2A1S1SdA1M0G0S22VQ;VX;S17VK;VA0;Vrho0;R7R6R5R4R3R2R1AaA3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA;").
Variable rest : list qbatch.
Variable TPI : list word -> Prop.

Definition QI_sec_step : Prop := ltac2:(tb__ "0|3|
ScS0S0S5S4S0S0A2M0S1G0A1S1SdA1S16S1S25Q40A1A1M1VTPI;R1A1M2S1cVA0;Vrest;RaR9S2G0R6R5A3R4A6S20R4R5A2S1eR5RbRaR9R8A5S1fR6RcRaR9A4S14S3S23S6S0S0RaA3A1S9A3ScS16G1G2S1cVA0;Vrest;R4R12ReRdA6S20R4ReA2S1eR5R14R13R12R11A5S1fR6R15R13R12A4S21VQ;VX;S1aS1bS17VK;VA0;Vrho0;R8R16R15S8R14A1R12R11Vrest;AaS27R7R6A5A3F_;F_;F_;F_;F_;Ftp';Frho';FA';S21VQ;VX;S1aS1bS17VK;VA0;Vrho0;R10RfReRdS2G0RcRbA3RaVrest;AaS26R9R8A5A3F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;Ftmp';Fits;Fit;Fnd;Fn0;Fa;FA;").
Definition QI_full_step : Prop := ltac2:(tb__ "0|4|
ScS0S0S5S4S0S0A2M0S1G0A1S1SdA1S16S1S25Q40A1A1M1VTPI;R1A1M2S1cVA0;Vrest;RaR9S2G0R6R5A3R4A6S20R4R5A2S1eR5RbRaR9R8A5S1fR6RcRaR9A4S14S3S23S6S0S0RaA3A1S7A3S2eS24S28RbA1M3A1S2fSaS0S12S2dRfG3A2A1A2A1A2ScS16G1G2S1cVA0;Vrest;R4R13RfReA6S20R4RfA2S1eR5R15R14R13R12A5S1fR6R16R14R13A4S21VQ;VX;S1aS1bS17VK;VA0;Vrho0;R8R17R16S8R15A1R13R12Vrest;AaS27R7R6A5A3F_;F_;F_;F_;F_;Ftp';Frho';FA';S21VQ;VX;S1aS1bS17VK;VA0;Vrho0;R11R10RfReS2G0RdRcA3RbVrest;AaS26RaR9A5A3F_;F_;F_;F_;F_;F_;F_;F_;Ftp;Frho;Ftmp';Fits;Fit;Fnd;Fn0;Fa;FA;").

Lemma cls_item_not_fresh : ltac2:(tb__ "0|2|
ScS0S0S4S0S0A2M0S1G0A1S1SdA1M1S16S1S25Q40A1A1S1S2aA1S29S14G1S10RaA1SbSdA1A3S14S3SeRbA1S7A3S19VA0;RcA2VK;RdR7R6R5R4A5S14G1SfReA1S2SdS13RdS2G0RbRaA3RcA3R9A3A3S14S3S23S6S0S0RcA3A1S7A3S15S11VA0;S28RdA1A2A1F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho;Fg;Fits;Fit;Fs;Fa;FA;").
Proof.
  intros A a s it its g rho tp tr md HTH HCI (_ & _ & EF) HK HGL HPR HF. specialize (EF _ HF). unfold class_fresh in HF. rewrite HF in EF.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE. destruct BE as [_ _ _ HAU _ _ _].
  assert (HIN : In it (qitems (qall A))) by (rewrite (qall_A1 A HTH), HGL; unfold qitems; cbn [flat_map qb_items app]; left; reflexivity).
  pose proof (qi_geom A HG HQPU HAU rho it 0 HIN HPR ltac:(lia) HRIG) as GEO. cbv zeta in GEO.
  destruct GEO as (C1 & Z1 & _ & _ & _ & _ & _ & R1 & _ & U1 & _).
  unfold cls_of, nthZ in U1. rewrite EF in U1. change (cs_allocated_user cs_empty) with 0 in U1. lia.
Qed.

Theorem QI_step_of_arms : ltac2:(tb__ "0|0|
S2cS2bS1dVK;VA0;Vrho0;VQ;VX;Vrest;VTPI;A7F_;F_;").
Proof.
  intros HSEC HFULL A a n0 nd it its tmp' rho tp HTP HI HVx HVi HVs HC.
  destruct (is_primary (snd it)) eqn:EPR; [|exact (HSEC A a n0 nd it its tmp' rho tp HTP HI HVx HVi HVs EPR HC)].
  destruct (Z_lt_dec (Z.of_nat (length (cs_cache (cls_of A (it_cls it))))) (max_count (it_cls it))) as [HNF|HFL];
    [|exact (HFULL A a n0 nd it its tmp' rho tp HTP HI HVx HVi HVs EPR ltac:(lia) HC)].
  pose proof HI as (I1 & I2 & I3 & I4 & (s & I5) & I6).
  set (J := JRI K A0 rho0 A a n0 nd (it :: its) tmp' rest).
  apply (tr_pure X _ (~ class_fresh A0 (it_cls it))).
  { intros [tr [ms md]] Hw. destruct (proj2 Hw) as (HK & _). cbn [w_tr w_cfg cfg_model fst snd] in HK.
    exact (cls_item_not_fresh A a s it its (tmp' ++ rest) rho tp tr md I1 I2 I4 HK I5 EPR). }
  intros NFR.
  apply (tr_glue X _ J (Cqi (vb_of it)) tp (fun r => exists t st, qienv A it r t st /\ HVX r tmp' /\ HVI r a n0 nd it /\ HVS r a nd it)).
  { intros w Hw. destruct (qi_pre K HL A0 rho0 A a s n0 nd it its tmp' rest rho tp w I1 I2 I3 I5 EPR HNF Hw HVi HVs) as (rho2 & t & st & Hs & QE & OTH & EV).
    exists rho2. split; [exact Hs|]. exists t, st. split; [exact QE|].
    assert (NB : forall i, (i < 200)%positive \/ i = 208%positive -> ~ In i BLQ) by (intros i Hi Y; unfold BLQ in Y; cbn in Y; lia).
    destruct HVx as (E184 & E185 & E186 & E187 & E208). destruct HVi as (E162 & E163 & E164 & E165 & E166).
    split; [unfold HVX; rewrite !OTH by (apply NB; lia); tauto|]. split; [unfold HVI; rewrite !OTH by (apply NB; lia); tauto|].
    unfold HVS. rewrite EV. exact HVs. }
  intros rhoE (t & st & QE & HVe & HIe & HSe).
  apply (qi_call X (vb_of it) J rhoE tp (HJI _ _ _ _ _ _ _)).
  { pose proof QE as [HG _ _ HRIG HGEO HV _ _ _ [Ht1 _] _ HNF' HQP HAU HIN HPR HMU]. eapply (qi_side A); eassumption. }
  intros rho' Hag.
  assert (AGV : forall i, (i < 216)%positive -> rw rho' i = rw rhoE i) by (intros i Hi; symmetry; exact (proj1 Hag i Hi)).
  assert (ERM : rm rho' = rm rhoE) by (apply functional_extensionality; intros x; symmetry; apply (proj2 (proj2 Hag))).
  pose proof (qienv_agree A it rhoE rho' t st QE AGV ERM) as QE'.
  set (A' := push_cache (set_q A [] (mkQB a its s :: tmp' ++ rest)) (it_cls it) (it_id (aa_geom A) it)).
  apply (tr_glue X _ (JRI K A0 rho0 A' a n0 (S nd) its tmp' rest) RIr tp (fun r => HVX r tmp' /\ HVI r a n0 nd it /\ HVS r a nd it)).
  { intros w Hw. apply (qi_post K HL HSBD A0 rho0 A it a s n0 nd its tmp' rest rho' tp w t st I1 I2 I3 I4 I5 Hw QE').
    - destruct HVe as (E184 & E185 & E186 & E187 & E208). unfold HVX. rewrite !AGV by lia. tauto.
    - destruct HIe as (E162 & E163 & E164 & E165 & E166). unfold HVI. rewrite !AGV by lia. tauto.
    - unfold HVS. rewrite ERM. exact HSe. }
  intros rho5 (HV5 & HI5 & HS5). apply (seg_D_RrM X _ rho5 tp (HJI _ _ _ _ _ _ _)). intros Tx M rho6 HIN HKp. cbn [In] in HIN. destruct HIN as [E|[]]. injection E as <- <-.
  apply (HC A' rho6 tp HTP); [| exact (HVX_keep _ rho5 rho6 tmp' HKp ltac:(cbn; tauto) HV5) | exact (HVI_keep rho5 rho6 a n0 nd it HKp HI5) | exact (HVS_keep _ rho5 rho6 a nd it HKp HS5)].
  split; [reflexivity|]. split; [exact I2|]. split; [|split; [|split; [exists s; reflexivity|]]].
  - intros z Hz. apply I3. exact (QW_push_item A a it its s s (tmp' ++ rest) _ _ z I1 I5 Hz).
  - pose proof QE as [_ _ _ _ HGEO _ _ _ _ _ _ _ _ _ _ _ _]. unfold qgeo in HGEO. destruct HGEO as (C1 & _). apply QP_push; [exact I4 | lia | exact NFR].
  - intros z Hz. apply I6. exact (SF_push_item A a it its s s (tmp' ++ rest) _ _ z I1 I5 Hz).
Qed.
End QIStep.
End SegQ3D_qis.

(* [comment removed for export] *)
Module SpineCallocS9i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "true"; "bool"; "prod"; "false"; "list"; "nat"; "None"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "SVar"; "cell"; "mkCell"; "sv"; "SAlu"; "sobj"; "mkObj"; "DUnknown"; "sprop"; "SPUle"; "DImage"; "SPAlign"; "ss_next"; "DZero"; "SPBranch"; "ss_facts"; "SExt"; "SMd"; "SPUlt"; "FcsrFrm0"; "mkSS"; "sprop_below"; "SPNot"; "swf"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_AND"; "ALU_SLL"; "ALU_SUB"; "ALU_OR"; "M_MUL"; "BC_EQ"; "BC_GE"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "mkAX"; "entailsA"; "la_state"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "C9ma"; "C9mb"; "C9mpa"; "C9mpb"; "C9"; "C9p"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "MSENT"; "V_RZ"; "ube"; "upd"; "C10a"; "C10b"; "C10pa"; "C10pb"; "E8n"; "E8pn"; "F_gen"; "C8"; "C8p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9"; "S2_of"; "fin_hyps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS9i.INST"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"; "Rma_0"; "Rmb_0"; "Rmpa_0"; "Rmpb_0"; "T9a_0"; "T9b_0"; "T9pa_0"; "T9pb_0"; "sma_0"; "smb_0"; "smpa_0"; "smpb_0"; "s9e_0"; "s9ep_0"; "sdma_0"; "sdmb_0"; "sdmpa_0"; "sdmpb_0"; "K_a"; "K_b"; "K_pa"; "K_pb"; "hcells_a"; "hcells_b"; "hcells_pa"; "hcells_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "sf_a"; "sf_b"; "sf_pa"; "sf_pb"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i9.CallocMemoSP.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Local Ltac mc := cbv beta zeta delta [W st tmax]; CallocMemoSP_all; MemoFast.vmc.

Lemma Cert8_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zdb004S0S26Z3ca54S2S26A1A3A3S37S0S32S51VW;Vst;Vtmax;A3S2S32A1M0A3S0S32S4eVW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Definition s9e_0 : wsub := ltac:(let t := constr:(infer_sub GW (ax_S (E8n (Wcan 0) UStopLe 2)) (ax_S (C9 (Wcan 0) UStopLe 2))) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Lemma ENT9e_0 : ltac2:(tb__ "0|0|
S30S4S34S4eVW;Vst;Vtmax;A3S40VW;Vst;Vtmax;A3S75A3S3A3"). Proof. mc. Qed.
Lemma SID9e_0 : ltac2:(tb__ "0|0|
S30S4S57S75S37A2S3A3"). Proof. mc. Qed.
Lemma NX9_0 : ltac2:(tb__ "0|0|
S58S37S19S31S40VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma FGC_0 : ltac2:(tb__ "0|0|
S56S15S50S1cS31S40VW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. mc. Qed.

Lemma Cert8p_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zdb004S0S26Z3ca54S2S26A1A3A3S37S0S32S52VW;Vst;Vtmax;A3S2S32A1M0A3S0S32S4fVW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Definition s9ep_0 : wsub := ltac:(let t := constr:(infer_sub GW (ax_S (E8pn (Wcan 0) UStopLe 2)) (ax_S (C9p (Wcan 0) UStopLe 2))) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Lemma ENT9ep_0 : ltac2:(tb__ "0|0|
S30S4S34S4fVW;Vst;Vtmax;A3S41VW;Vst;Vtmax;A3S76A3S3A3"). Proof. mc. Qed.
Lemma SID9ep_0 : ltac2:(tb__ "0|0|
S30S4S57S76S37A2S3A3"). Proof. mc. Qed.
Lemma NX9p_0 : ltac2:(tb__ "0|0|
S58S37S19S31S41VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma FGCp_0 : ltac2:(tb__ "0|0|
S56S15S50S1cS31S41VW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. mc. Qed.

Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zdb004S2S26A1A3S37S0S32S54S0S15S16ScZ20A1SdS47A1A2S2S15A1A3S40VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S42VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9ma_0 : ltac2:(tb__ "0|1|
S30S32S3cVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S42VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9ma_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3cVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9ma_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S42VW;Vst;Vtmax;A3A1S31S3cVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9ma_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3cVW;Vst;Vtmax;A3A1A1S19S31S42VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition sma_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9ma (Wcan 0) UStopLe 2)) (ax_S Pre_mszA)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition Rma_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9ma (Wcan 0) UStopLe 2) Pre_mszA sma_0 with Some R => R | None => [] end) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition T9a_0 : axst := ltac:(let t := constr:(import_postA sma_0 Pre_mszA (liftA P_msz) (C9ma (Wcan 0) UStopLe 2) Rma_0) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition sdma_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hema_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3cVW;Vst;Vtmax;A3S39S71A3SaG0S69A2A3"). Proof. mc. Qed.
Lemma Hchkma_0 : ltac2:(tb__ "0|0|
S30S4S5fS3cVW;Vst;Vtmax;A3S39S71S69S59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTma_0 : ltac2:(tb__ "0|0|
S30S32S61S71S39S5aS3aA1S3cVW;Vst;Vtmax;A3S69A5S6dA3"). Proof. mc. Qed.
Lemma FBCma_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3cVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTma_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S6dA1A1A1S1cS31S3cVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10a_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS6dS1cS31S3cVW;Vst;Vtmax;A3A1A1A2S4aVW;Vst;Vtmax;A3S77A3S3A3"). Proof. mc. Qed.
Lemma SID10a_0 : ltac2:(tb__ "0|0|
S30S4S57S77S37A2S3A3"). Proof. mc. Qed.
Lemma NXCma_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3cVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10a_nf : axst := ltac:(let t := constr:(leaf 0 (run10a (Wcan 0) UStopLe 2)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10a_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4aVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S65G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_a := ss_objs (ax_S F10a_nf).
Definition swc_a := ob_cells (nth 0 objs_a O_st). Definition scells_a := ob_cells (nth 36 objs_a O_st). Definition hcells_a := ob_cells (nth 37 objs_a O_st).
Definition K_a := KEPT9 W swc_a.
Definition sf_a : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S65S7bA2S31S62VW;Vst;A2A1A3").
Lemma FH_a_0 : ltac2:(tb__ "0|0|
S64U0Vst;S65S8bS83S7fS6S87A8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zdb004S2S26A1A3S37S0S32S54S0S15S16SdS47A1ScZ10A1A2S2S15A1A3S40VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S43VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9mb_0 : ltac2:(tb__ "0|1|
S30S32S3dVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S43VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9mb_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3dVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9mb_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S43VW;Vst;Vtmax;A3A1S31S3dVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9mb_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3dVW;Vst;Vtmax;A3A1A1S19S31S43VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition smb_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9mb (Wcan 0) UStopLe 2)) (ax_S Pre_mszA)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition Rmb_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9mb (Wcan 0) UStopLe 2) Pre_mszA smb_0 with Some R => R | None => [] end) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition T9b_0 : axst := ltac:(let t := constr:(import_postA smb_0 Pre_mszA (liftA P_msz) (C9mb (Wcan 0) UStopLe 2) Rmb_0) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition sdmb_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hemb_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3dVW;Vst;Vtmax;A3S39S72A3SaG0S6aA2A3"). Proof. mc. Qed.
Lemma Hchkmb_0 : ltac2:(tb__ "0|0|
S30S4S5fS3dVW;Vst;Vtmax;A3S39S72S6aS59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTmb_0 : ltac2:(tb__ "0|0|
S30S32S61S72S39S5aS3aA1S3dVW;Vst;Vtmax;A3S6aA5S6eA3"). Proof. mc. Qed.
Lemma FBCmb_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3dVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTmb_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S6eA1A1A1S1cS31S3dVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10b_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS6eS1cS31S3dVW;Vst;Vtmax;A3A1A1A2S4bVW;Vst;Vtmax;A3S78A3S3A3"). Proof. mc. Qed.
Lemma SID10b_0 : ltac2:(tb__ "0|0|
S30S4S57S78S37A2S3A3"). Proof. mc. Qed.
Lemma NXCmb_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3dVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10b_nf : axst := ltac:(let t := constr:(leaf 0 (run10b (Wcan 0) UStopLe 2)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10b_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4bVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S66G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_b := ss_objs (ax_S F10b_nf).
Definition swc_b := ob_cells (nth 0 objs_b O_st). Definition scells_b := ob_cells (nth 36 objs_b O_st). Definition hcells_b := ob_cells (nth 37 objs_b O_st).
Definition K_b := KEPT9 W swc_b.
Definition sf_b : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S66S7cA2S31S62VW;Vst;A2A1A3").
Lemma FH_b_0 : ltac2:(tb__ "0|0|
S64U0Vst;S66S8cS84S80S6S88A8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma Cert9pa_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zdb004S2S26A1A3S37S0S32S54S0S15S16ScZ20A1SdS47A1A2S2S15A1A3S41VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S44VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9mpa_0 : ltac2:(tb__ "0|1|
S30S32S3eVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S44VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9mpa_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3eVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9mpa_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S44VW;Vst;Vtmax;A3A1S31S3eVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9mpa_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3eVW;Vst;Vtmax;A3A1A1S19S31S44VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition smpa_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9mpa (Wcan 0) UStopLe 2)) (ax_S Pre_mszA)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition Rmpa_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9mpa (Wcan 0) UStopLe 2) Pre_mszA smpa_0 with Some R => R | None => [] end) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition T9pa_0 : axst := ltac:(let t := constr:(import_postA smpa_0 Pre_mszA (liftA P_msz) (C9mpa (Wcan 0) UStopLe 2) Rmpa_0) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition sdmpa_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hempa_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3eVW;Vst;Vtmax;A3S39S73A3SaG0S6bA2A3"). Proof. mc. Qed.
Lemma Hchkmpa_0 : ltac2:(tb__ "0|0|
S30S4S5fS3eVW;Vst;Vtmax;A3S39S73S6bS59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTmpa_0 : ltac2:(tb__ "0|0|
S30S32S61S73S39S5aS3aA1S3eVW;Vst;Vtmax;A3S6bA5S6fA3"). Proof. mc. Qed.
Lemma FBCmpa_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3eVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTmpa_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S6fA1A1A1S1cS31S3eVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10pa_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS6fS1cS31S3eVW;Vst;Vtmax;A3A1A1A2S4cVW;Vst;Vtmax;A3S79A3S3A3"). Proof. mc. Qed.
Lemma SID10pa_0 : ltac2:(tb__ "0|0|
S30S4S57S79S37A2S3A3"). Proof. mc. Qed.
Lemma NXCmpa_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3eVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10pa_nf : axst := ltac:(let t := constr:(leaf 0 (run10pa (Wcan 0) UStopLe 2)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10pa_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4cVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S67G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_pa := ss_objs (ax_S F10pa_nf).
Definition swc_pa := ob_cells (nth 0 objs_pa O_st). Definition scells_pa := ob_cells (nth 36 objs_pa O_st). Definition hcells_pa := ob_cells (nth 37 objs_pa O_st).
Definition K_pa := KEPT9 W swc_pa.
Definition sf_pa : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S67S7dA2S31S62VW;Vst;A2A1A3").
Lemma FH_pa_0 : ltac2:(tb__ "0|0|
S64U0Vst;S67S8dS85S81S3S89A8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma Cert9pb_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zdb004S2S26A1A3S37S0S32S54S0S15S16SdS47A1ScZ10A1A2S2S15A1A3S41VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S45VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9mpb_0 : ltac2:(tb__ "0|1|
S30S32S3fVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S45VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9mpb_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3fVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9mpb_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S45VW;Vst;Vtmax;A3A1S31S3fVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9mpb_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3fVW;Vst;Vtmax;A3A1A1S19S31S45VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition smpb_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9mpb (Wcan 0) UStopLe 2)) (ax_S Pre_mszA)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition Rmpb_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9mpb (Wcan 0) UStopLe 2) Pre_mszA smpb_0 with Some R => R | None => [] end) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition T9pb_0 : axst := ltac:(let t := constr:(import_postA smpb_0 Pre_mszA (liftA P_msz) (C9mpb (Wcan 0) UStopLe 2) Rmpb_0) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Definition sdmpb_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hempb_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3fVW;Vst;Vtmax;A3S39S74A3SaG0S6cA2A3"). Proof. mc. Qed.
Lemma Hchkmpb_0 : ltac2:(tb__ "0|0|
S30S4S5fS3fVW;Vst;Vtmax;A3S39S74S6cS59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTmpb_0 : ltac2:(tb__ "0|0|
S30S32S61S74S39S5aS3aA1S3fVW;Vst;Vtmax;A3S6cA5S70A3"). Proof. mc. Qed.
Lemma FBCmpb_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3fVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTmpb_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S70A1A1A1S1cS31S3fVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10pb_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS70S1cS31S3fVW;Vst;Vtmax;A3A1A1A2S4dVW;Vst;Vtmax;A3S7aA3S3A3"). Proof. mc. Qed.
Lemma SID10pb_0 : ltac2:(tb__ "0|0|
S30S4S57S7aS37A2S3A3"). Proof. mc. Qed.
Lemma NXCmpb_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3fVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10pb_nf : axst := ltac:(let t := constr:(leaf 0 (run10pb (Wcan 0) UStopLe 2)) in let t := CallocMemoSP_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10pb_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4dVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S68G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_pb := ss_objs (ax_S F10pb_nf).
Definition swc_pb := ob_cells (nth 0 objs_pb O_st). Definition scells_pb := ob_cells (nth 36 objs_pb O_st). Definition hcells_pb := ob_cells (nth 37 objs_pb O_st).
Definition K_pb := KEPT9 W swc_pb.
Definition sf_pb : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S68S7eA2S31S62VW;Vst;A2A1A3").
Lemma FH_pb_0 : ltac2:(tb__ "0|0|
S64U0Vst;S68S8eS86S82S3S8aA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
End INST.

End SpineCallocS9i.

(* [comment removed for export] *)
Module SpineCallocS9iW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "true"; "bool"; "prod"; "false"; "list"; "nat"; "None"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "SVar"; "cell"; "mkCell"; "sv"; "SAlu"; "sobj"; "mkObj"; "DUnknown"; "sprop"; "SPUle"; "DImage"; "SPAlign"; "ss_next"; "DZero"; "SPBranch"; "ss_facts"; "SExt"; "SMd"; "SPUlt"; "FcsrFrm0"; "mkSS"; "sprop_below"; "SPNot"; "swf"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_AND"; "ALU_SLL"; "ALU_SUB"; "ALU_OR"; "M_MUL"; "BC_EQ"; "BC_GE"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "mkAX"; "entailsA"; "la_state"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "C9ma"; "C9mb"; "C9mpa"; "C9mpb"; "C9"; "C9p"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "MSENT"; "V_RZ"; "ube"; "upd"; "C10a"; "C10b"; "C10pa"; "C10pb"; "E8n"; "E8pn"; "F_gen"; "C8"; "C8p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9"; "S2_of"; "fin_hyps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocS9iW1.INST"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"; "Rma_0"; "Rmb_0"; "Rmpa_0"; "Rmpb_0"; "T9a_0"; "T9b_0"; "T9pa_0"; "T9pb_0"; "sma_0"; "smb_0"; "smpa_0"; "smpb_0"; "s9e_0"; "s9ep_0"; "sdma_0"; "sdmb_0"; "sdmpa_0"; "sdmpb_0"; "K_a"; "K_b"; "K_pa"; "K_pb"; "hcells_a"; "hcells_b"; "hcells_pa"; "hcells_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "sf_a"; "sf_b"; "sf_pa"; "sf_pb"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CallocMemoSPW1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Local Ltac mc := cbv beta zeta delta [W st tmax]; CallocMemoSPW1_all; MemoFast.vmc.

Lemma Cert8_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zdb004S0S26Z3ca54S2S26A1A3A3S37S0S32S51VW;Vst;Vtmax;A3S2S32A1M0A3S0S32S4eVW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Definition s9e_0 : wsub := ltac:(let t := constr:(infer_sub GW (ax_S (E8n (Wcan 1) UStopLeOrPc 3)) (ax_S (C9 (Wcan 1) UStopLeOrPc 3))) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Lemma ENT9e_0 : ltac2:(tb__ "0|0|
S30S4S34S4eVW;Vst;Vtmax;A3S40VW;Vst;Vtmax;A3S75A3S3A3"). Proof. mc. Qed.
Lemma SID9e_0 : ltac2:(tb__ "0|0|
S30S4S57S75S37A2S3A3"). Proof. mc. Qed.
Lemma NX9_0 : ltac2:(tb__ "0|0|
S58S37S19S31S40VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma FGC_0 : ltac2:(tb__ "0|0|
S56S15S50S1cS31S40VW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. mc. Qed.

Lemma Cert8p_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zdb004S0S26Z3ca54S2S26A1A3A3S37S0S32S52VW;Vst;Vtmax;A3S2S32A1M0A3S0S32S4fVW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Definition s9ep_0 : wsub := ltac:(let t := constr:(infer_sub GW (ax_S (E8pn (Wcan 1) UStopLeOrPc 3)) (ax_S (C9p (Wcan 1) UStopLeOrPc 3))) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Lemma ENT9ep_0 : ltac2:(tb__ "0|0|
S30S4S34S4fVW;Vst;Vtmax;A3S41VW;Vst;Vtmax;A3S76A3S3A3"). Proof. mc. Qed.
Lemma SID9ep_0 : ltac2:(tb__ "0|0|
S30S4S57S76S37A2S3A3"). Proof. mc. Qed.
Lemma NX9p_0 : ltac2:(tb__ "0|0|
S58S37S19S31S41VW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Lemma FGCp_0 : ltac2:(tb__ "0|0|
S56S15S50S1cS31S41VW;Vst;Vtmax;A3A1A1A3"). Proof. apply inclb_incl. mc. Qed.

Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zdb004S2S26A1A3S37S0S32S54S0S15S16ScZ20A1SdS47A1A2S2S15A1A3S40VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S42VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9ma_0 : ltac2:(tb__ "0|1|
S30S32S3cVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S42VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9ma_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3cVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9ma_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S42VW;Vst;Vtmax;A3A1S31S3cVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9ma_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3cVW;Vst;Vtmax;A3A1A1S19S31S42VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition sma_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9ma (Wcan 1) UStopLeOrPc 3)) (ax_S Pre_mszA)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition Rma_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9ma (Wcan 1) UStopLeOrPc 3) Pre_mszA sma_0 with Some R => R | None => [] end) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition T9a_0 : axst := ltac:(let t := constr:(import_postA sma_0 Pre_mszA (liftA P_msz) (C9ma (Wcan 1) UStopLeOrPc 3) Rma_0) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition sdma_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hema_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3cVW;Vst;Vtmax;A3S39S71A3SaG0S69A2A3"). Proof. mc. Qed.
Lemma Hchkma_0 : ltac2:(tb__ "0|0|
S30S4S5fS3cVW;Vst;Vtmax;A3S39S71S69S59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTma_0 : ltac2:(tb__ "0|0|
S30S32S61S71S39S5aS3aA1S3cVW;Vst;Vtmax;A3S69A5S6dA3"). Proof. mc. Qed.
Lemma FBCma_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3cVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTma_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S6dA1A1A1S1cS31S3cVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10a_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS6dS1cS31S3cVW;Vst;Vtmax;A3A1A1A2S4aVW;Vst;Vtmax;A3S77A3S3A3"). Proof. mc. Qed.
Lemma SID10a_0 : ltac2:(tb__ "0|0|
S30S4S57S77S37A2S3A3"). Proof. mc. Qed.
Lemma NXCma_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3cVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10a_nf : axst := ltac:(let t := constr:(leaf 0 (run10a (Wcan 1) UStopLeOrPc 3)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10a_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4aVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S65G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_a := ss_objs (ax_S F10a_nf).
Definition swc_a := ob_cells (nth 0 objs_a O_st). Definition scells_a := ob_cells (nth 37 objs_a O_st). Definition hcells_a := ob_cells (nth 38 objs_a O_st).
Definition K_a := KEPT9 W swc_a.
Definition sf_a : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S65S7bA2S31S62VW;Vst;A2A1A3").
Lemma FH_a_0 : ltac2:(tb__ "0|0|
S64U1Vst;S65S8bS83S7fS6S87A8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zdb004S2S26A1A3S37S0S32S54S0S15S16SdS47A1ScZ10A1A2S2S15A1A3S40VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S43VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9mb_0 : ltac2:(tb__ "0|1|
S30S32S3dVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S43VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9mb_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3dVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9mb_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S43VW;Vst;Vtmax;A3A1S31S3dVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9mb_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3dVW;Vst;Vtmax;A3A1A1S19S31S43VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition smb_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9mb (Wcan 1) UStopLeOrPc 3)) (ax_S Pre_mszA)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition Rmb_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9mb (Wcan 1) UStopLeOrPc 3) Pre_mszA smb_0 with Some R => R | None => [] end) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition T9b_0 : axst := ltac:(let t := constr:(import_postA smb_0 Pre_mszA (liftA P_msz) (C9mb (Wcan 1) UStopLeOrPc 3) Rmb_0) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition sdmb_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hemb_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3dVW;Vst;Vtmax;A3S39S72A3SaG0S6aA2A3"). Proof. mc. Qed.
Lemma Hchkmb_0 : ltac2:(tb__ "0|0|
S30S4S5fS3dVW;Vst;Vtmax;A3S39S72S6aS59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTmb_0 : ltac2:(tb__ "0|0|
S30S32S61S72S39S5aS3aA1S3dVW;Vst;Vtmax;A3S6aA5S6eA3"). Proof. mc. Qed.
Lemma FBCmb_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3dVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTmb_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S6eA1A1A1S1cS31S3dVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10b_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS6eS1cS31S3dVW;Vst;Vtmax;A3A1A1A2S4bVW;Vst;Vtmax;A3S78A3S3A3"). Proof. mc. Qed.
Lemma SID10b_0 : ltac2:(tb__ "0|0|
S30S4S57S78S37A2S3A3"). Proof. mc. Qed.
Lemma NXCmb_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3dVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10b_nf : axst := ltac:(let t := constr:(leaf 0 (run10b (Wcan 1) UStopLeOrPc 3)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10b_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4bVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S66G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_b := ss_objs (ax_S F10b_nf).
Definition swc_b := ob_cells (nth 0 objs_b O_st). Definition scells_b := ob_cells (nth 37 objs_b O_st). Definition hcells_b := ob_cells (nth 38 objs_b O_st).
Definition K_b := KEPT9 W swc_b.
Definition sf_b : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S66S7cA2S31S62VW;Vst;A2A1A3").
Lemma FH_b_0 : ltac2:(tb__ "0|0|
S64U1Vst;S66S8cS84S80S6S88A8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma Cert9pa_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zdb004S2S26A1A3S37S0S32S54S0S15S16ScZ20A1SdS47A1A2S2S15A1A3S41VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S44VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9mpa_0 : ltac2:(tb__ "0|1|
S30S32S3eVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S44VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9mpa_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3eVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9mpa_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S44VW;Vst;Vtmax;A3A1S31S3eVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9mpa_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3eVW;Vst;Vtmax;A3A1A1S19S31S44VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition smpa_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9mpa (Wcan 1) UStopLeOrPc 3)) (ax_S Pre_mszA)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition Rmpa_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9mpa (Wcan 1) UStopLeOrPc 3) Pre_mszA smpa_0 with Some R => R | None => [] end) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition T9pa_0 : axst := ltac:(let t := constr:(import_postA smpa_0 Pre_mszA (liftA P_msz) (C9mpa (Wcan 1) UStopLeOrPc 3) Rmpa_0) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition sdmpa_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hempa_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3eVW;Vst;Vtmax;A3S39S73A3SaG0S6bA2A3"). Proof. mc. Qed.
Lemma Hchkmpa_0 : ltac2:(tb__ "0|0|
S30S4S5fS3eVW;Vst;Vtmax;A3S39S73S6bS59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTmpa_0 : ltac2:(tb__ "0|0|
S30S32S61S73S39S5aS3aA1S3eVW;Vst;Vtmax;A3S6bA5S6fA3"). Proof. mc. Qed.
Lemma FBCmpa_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3eVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTmpa_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S6fA1A1A1S1cS31S3eVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10pa_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS6fS1cS31S3eVW;Vst;Vtmax;A3A1A1A2S4cVW;Vst;Vtmax;A3S79A3S3A3"). Proof. mc. Qed.
Lemma SID10pa_0 : ltac2:(tb__ "0|0|
S30S4S57S79S37A2S3A3"). Proof. mc. Qed.
Lemma NXCmpa_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3eVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10pa_nf : axst := ltac:(let t := constr:(leaf 0 (run10pa (Wcan 1) UStopLeOrPc 3)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10pa_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4cVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S67G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_pa := ss_objs (ax_S F10pa_nf).
Definition swc_pa := ob_cells (nth 0 objs_pa O_st). Definition scells_pa := ob_cells (nth 37 objs_pa O_st). Definition hcells_pa := ob_cells (nth 38 objs_pa O_st).
Definition K_pa := KEPT9 W swc_pa.
Definition sf_pa : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S67S7dA2S31S62VW;Vst;A2A1A3").
Lemma FH_pa_0 : ltac2:(tb__ "0|0|
S64U1Vst;S67S8dS85S81S3S89A8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma Cert9pb_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S0S26Zdb004S2S26A1A3S37S0S32S54S0S15S16SdS47A1ScZ10A1A2S2S15A1A3S41VW;Vst;Vtmax;A3A2S2S32A1M0A3S0S32S45VW;Vst;Vtmax;A3G0A3A6S3A3"). Proof. mc. Qed.
Lemma HCC9mpb_0 : ltac2:(tb__ "0|1|
S30S32S3fVW;Vst;Vtmax;A3S49VW;Vst;Vtmax;S45VW;Vst;Vtmax;A3S46S0S5S8S10A2M0S1S8S10UaS48A4S0G0S1S8S10UcSdPcA1A4S2G0A1A3A3S2S12A1S6S2S15A1A9A3"). Proof. reflexivity. Qed.
Lemma W9mpb_0 : ltac2:(tb__ "0|0|
S30S4S24S31S3fVW;Vst;Vtmax;A3A1A1S3A3"). Proof. mc. Qed.
Lemma D9mpb_0 : ltac2:(tb__ "0|4|
S30SbS5S7S5S10S10A2M0A1M1S7S15A1M2A2M3A1S5cS31S45VW;Vst;Vtmax;A3A1S31S3fVW;Vst;Vtmax;A3A1A2SaG3S1G1G2S2G0A1S2S15A1A4A2A3"). Proof. mc. Qed.
Lemma NX9mpb_0 : ltac2:(tb__ "0|0|
S30S25S19S31S3fVW;Vst;Vtmax;A3A1A1S19S31S45VW;Vst;Vtmax;A3A1A1A3"). Proof. mc. Qed.
Definition smpb_0 : wsub := ltac:(let t := constr:(infer_sub 1 (ax_S (C9mpb (Wcan 1) UStopLeOrPc 3)) (ax_S Pre_mszA)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition Rmpb_0 : list sobj := ltac:(let t := constr:(match entails_frA (C9mpb (Wcan 1) UStopLeOrPc 3) Pre_mszA smpb_0 with Some R => R | None => [] end) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition T9pb_0 : axst := ltac:(let t := constr:(import_postA smpb_0 Pre_mszA (liftA P_msz) (C9mpb (Wcan 1) UStopLeOrPc 3) Rmpb_0) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Definition sdmpb_0 : wsub := ltac2:(tb__ "0|9|
S0S5S25S10A2M0S1S25S10PaaM1SdG1A1A4S0G0S1S25S10PddM2SdG2A1A4S0G0S1S25S10PdcM3SdG3A1A4S0G0S1S25S10Pe0M4SdG4A1A4S0G0S1S25S10Pe1M5SdG5A1A4S0G0S1S25S10PdfM6SdG6A1A4S0G0S1S25S10Pe2M7SdG7A1A4S0G0S1S25S10Pc0M8SdG8A1A4S0G0S1S25S10PbfSdP102A1A4S0G0S1S25S10PbeSdP101A1A4S0G0S1S25S10PbdSdP100A1A4S0G0S1S25S10PbcSdPffA1A4S0G0S1S25S10Pb1SdPf4A1A4S0G0S1S25S10Pb0SdPf3A1A4S0G0S1S25S10PafSdPf2A1A4S0G0S1S25S10PaeSdPf1A1A4S0G0S1S25S10PadSdPf0A1A4S0G0S1S25S10PacSdPefA1A4S0G0S1S25S10PabSdPeeA1A4S0G0S1S25S10Pa7SdPeaA1A4S0G0S1S25S10Pa6SdPe9A1A4S0G0S1S25S10Pa5SdPe8A1A4S0G0S1S25S10Pa1SdPe4A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Hempb_0 : ltac2:(tb__ "0|1|
S30SbS7S12A1M0A1S60S3fVW;Vst;Vtmax;A3S39S74A3SaG0S6cA2A3"). Proof. mc. Qed.
Lemma Hchkmpb_0 : ltac2:(tb__ "0|0|
S30S4S5fS3fVW;Vst;Vtmax;A3S39S74S6cS59S36S32S35S3bA4A5S3A3"). Proof. mc. Qed.
Lemma HTmpb_0 : ltac2:(tb__ "0|0|
S30S32S61S74S39S5aS3aA1S3fVW;Vst;Vtmax;A3S6cA5S70A3"). Proof. mc. Qed.
Lemma FBCmpb_0 : ltac2:(tb__ "0|1|
S30S4S55S15S22S19S31S3fVW;Vst;Vtmax;A3A1M0A1A1S1cG0A1A3S3A3"). Proof. mc. Qed.
Lemma FBTmpb_0 : ltac2:(tb__ "0|0|
S30S4S55S15S22S19S31S70A1A1A1S1cS31S3fVW;Vst;Vtmax;A3A1A1A3S3A3"). Proof. mc. Qed.
Lemma ENT10pb_0 : ltac2:(tb__ "0|0|
S30S4S34S5eS70S1cS31S3fVW;Vst;Vtmax;A3A1A1A2S4dVW;Vst;Vtmax;A3S7aA3S3A3"). Proof. mc. Qed.
Lemma SID10pb_0 : ltac2:(tb__ "0|0|
S30S4S57S7aS37A2S3A3"). Proof. mc. Qed.
Lemma NXCmpb_0 : ltac2:(tb__ "0|0|
S58S37S19S31S3fVW;Vst;Vtmax;A3A1A1A2"). Proof. apply Pos.leb_le. mc. Qed.
Definition F10pb_nf : axst := ltac:(let t := constr:(leaf 0 (run10pb (Wcan 1) UStopLeOrPc 3)) in let t := CallocMemoSPW1_subst t in let v := eval vm_compute in t in exact v).
Lemma Cert10pb_0 : ltac2:(tb__ "0|1|
S30S4S53S38Ufa0S2S26A1S37S0S32S4dVW;Vst;Vtmax;A3S2S32A1M0A3S0S32S68G0A3A6S3A3"). Proof. mc. Qed.
Definition objs_pb := ss_objs (ax_S F10pb_nf).
Definition swc_pb := ob_cells (nth 0 objs_pb O_st). Definition scells_pb := ob_cells (nth 37 objs_pb O_st). Definition hcells_pb := ob_cells (nth 38 objs_pb O_st).
Definition K_pb := KEPT9 W swc_pb.
Definition sf_pb : wsub := ltac2:(tb__ "0|0|
S5dS5bS63S68S7eA2S31S62VW;Vst;A2A1A3").
Lemma FH_pb_0 : ltac2:(tb__ "0|0|
S64U1Vst;S68S8eS86S82S3S8aA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
End INST.

End SpineCallocS9iW1.

(* [comment removed for export] *)
Module SpineCallocR8.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "reg_sv"; "SLit"; "valuation"; "ss_next"; "ss_objs"; "eval"; "obj_range"; "ranges_disjoint"; "sprop"; "ss_facts"; "ss_pc"; "sv_below"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "ge"; "modulo"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "prod"; "true"; "app"; "pair"; "fst"; "Some"; "nat"; "nil"; "option"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "apartW"; "maps_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "AA"; "ag_top"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "region_free"; "alloc_top"; "m_vmmaps"; "map_contains"; "vm_limit"; "vm_maps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "mlink"; "entryR"; "frozen"; "ghosts"; "phase"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP"; "pbase"; "ph_get"; "ph_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "GR"; "O_pcm"; "O_ri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "commit_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "BASEF"; "BASEO"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Lemma Rregion_free_of_apart : ltac2:(tb__ "0|2|
S17S1aS16Q40A1M0G0A2M1A1G0G0G1S2cG1R1R4A3S26S1dG0G0R4R3A4R2A2F_;Fe;S0S18S2fR4R3R2A3S1bA3F_;Fn;Fa;Fl;").
Proof.
  induction l as [|[b s] l IH]; intros a n H; [reflexivity|]. cbn [region_free].
  rewrite (IH a n) by (intros e He; apply H; right; exact He). rewrite andb_true_r.
  pose proof (H (b, s) (or_introl eq_refl)) as X. unfold apartW in X. cbn [fst snd] in X.
  unfold iv_overlap. apply negb_true_iff. apply andb_false_iff. destruct X as [X|X]; [right|left]; apply Z.ltb_ge; lia.
Qed.
Lemma RapartW_sub : ltac2:(tb__ "0|4|
S16Q40M0A1M1G1S1aG1G1A2M2G2S12S15G0S1eG1G1R2A3A2S15G0R4A2M3A2S12S11S15G0R5A2G3A2S11S15G0S1eG1G1R3A3A2S15G0S23G1G1R3A3A2A2A2S26R4R3A2S26S1dG1G1R7R6A4R4A2F_;F_;F_;Fe';Fe;Fn;Fa;").
Proof. intros a n e e' H1 H2 [X|X]; unfold apartW in *; cbn [fst snd] in *; [left|right]; lia. Qed.
Lemma Rmaps_disjoint_pick : ltac2:(tb__ "0|4|
S17S1aS16Q40A1M0G0A2M1A1M2G2G1G2S27S1cG1R4S1cG1R3S19G1R2R1A3A3A3A1S1G1S2cG1R1R6A3S26R5R2A2M3F_;Fe';G1S2cG1R1S1cG1R5R3A3A3G3F_;Fe';A2F_;Fl2;Fe;Fl1;FR;").
Proof.
  intros R l1 e l2 H. unfold maps_disjoint in H.
  apply ranges_apart_app in H as (_ & H12 & XR). apply ranges_apart_app in H12 as (_ & H2 & X1). cbn in H2. destruct H2 as [F2 _].
  split.
  - intros e' He'. apply apartW_sym. apply (XR e' e He'). apply in_or_app. right. left. reflexivity.
  - intros e' He'. apply in_app_or in He' as [He'|He'].
    + apply apartW_sym. apply (X1 e' e He'). left. reflexivity.
    + exact (proj1 (Forall_forall _ _) F2 e' He').
Qed.

Lemma space_commit_model : ltac2:(tb__ "0|8|
S2aS7S17S16Q40M0A1M1A1M2S2eS3cG2S2eG1G1S50S25R9R8R7R6A5S38RaR9R8R7R6R5R4A7S12S29S28RbA1A1S15G0R4A2M3A2S12S11S15G0R5A2M4G3A2S11S11S29S28RcA1A1S4fA2Z1000A2A2S1S0S18S2fS35S31R7A1M5A1R6R5A3S1bA3S1S0S18S32S34G5A1M6R6R5A3S1bA3S1S12S44G6S15G0R6A2M7S11G7G4A2A3G4A2S1S0S24S30G5A1S2bS28RdA1A1A3S0S24S33G5A1S46A3A2A2A2A2F_;F_;F_;F_;Fn0;Fa0;Fmd;Ftp;Fph;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 ph tp md a0 n0 HA HM H1 H2.
  unfold mlink in HM. cbn zeta in HM. destruct HM as (M1 & M2 & M3 & M4 & _). rewrite M1, M2, M3, M4.
  destruct HA as (_ & _ & _ & _ & HMI & _). destruct HMI as (VG & _ & LIM & _ & _ & _ & TOPm & LI).
  destruct VG as (_ & N2 & _). destruct LI as (_ & _ & L3 & _).
  destruct N2 as (e & He & B1 & B2).
  destruct (in_split _ _ He) as (l1 & l2 & EM). rewrite EM in L3.
  destruct (Rmaps_disjoint_pick _ _ _ _ L3) as [XR XM].
  assert (SUB : forall e', apartW e e' -> apartW (a0, n0) e') by (intros e' X; apply (RapartW_sub a0 n0 e e'); [lia | lia | exact X]).
  split; [apply Rregion_free_of_apart; intros e' He'; apply SUB; exact (XR e' He')|].
  split.
  { unfold map_contains. apply existsb_exists. exists e. split; [exact He|]. apply andb_true_intro. split; apply Z.leb_le; lia. }
  split; [rewrite EM; apply overlap_sum_split_le; apply Rregion_free_of_apart; intros e' He'; apply SUB; exact (XM e' He')|].
  split; [exact TOPm | exact LIM].
Qed.

Section COMMIT.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S39VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S0S20S48Vp;Vph;A2U0A3").
Hypothesis PORD : pord p ph.
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S47VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
S7S3aVrb;R1A2S3bVA;Vrb;R2A3S0S24S15Q40SaR3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S1S12S11S29S28VA;A1A1M0Z100000000A2VB;A2S1S12S11VB;Z40000A2S11G0Z2000000000A2A2S0S24S14VB;Z1000A2Z0A3A2A2").
Hypothesis HROOM : ltac2:(tb__ "0|0|
S17S16Q40A1A1S2eS38VA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S13S45R2R3A2Z40000A2F_;Fmd;Ftp;").

Variable CX : axst.
Hypothesis SK_x : ltac2:(tb__ "0|1|
S0S17S1aS1aS4S4A2S4A2M0A1S3dS3G0S40S9S2VCX;A1A1A4S3dS3G0S40S1cS3S53VW;A1S19S3S4aS19S3S4bS19S3S4dS19S3S4eS21S3A1A3A3A3A3A3A4A3").
Hypothesis XF_x : ltac2:(tb__ "0|0|
S2dSdS52VW;Vst;A2SeS2VCX;A1A1A3").
Hypothesis XX_x : ax_X CX = [].
Hypothesis NX_x : ltac2:(tb__ "0|0|
S0S18S54S4cS8S2VCX;A1A1A2S1bA3").
Hypothesis IC_x : ltac2:(tb__ "0|0|
S0S22S3eA1S43S25SfS2VCX;A1A1A2S1fS3eS3fA2A3").
Hypothesis R17_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1Z11A2S6ZdeA1A3").
Hypothesis R10_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZaA2Veb;A3").
Hypothesis BEL_x : ltac2:(tb__ "0|0|
S0S18S10S8S2VCX;A1A1Veb;A2S1bA3").
Hypothesis R11_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZbA2S6Z40000A1A3").
Hypothesis R12_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZcA2S6Z3A1A3").
Hypothesis R13_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZdA2S6Z32A1A3").
Hypothesis R14_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15_x : ltac2:(tb__ "0|0|
S0S4S5S2VCX;A1ZfA2S6Z0A1A3").

Lemma commit_objs : ltac2:(tb__ "0|0|
S7S17S16Q40A1A1S42S36S25S37VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VCX;R3R2R1A6S3S2cS3R1S9S2VCX;A1A1A3ScSbR6R2A2S1dS24S24VB;S11VB;Z40000A2A4A2F_;Fo;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w [HsmA HJ]. pose proof HJ as (HFz & HGh & _).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S CX) [O_pcc0; O_st; O_pcm; O_ri] r _ HW HE HFz Hsm SK_x XF_x) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|? ?]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r ori O_ri SKr) in RNr.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
  destruct HBn as (HB1 & HB2 & _).
  apply Forall_forall. rewrite EO. apply Forall_app. split.
  - apply BZ. right; left. rewrite kSpaceSize_val. clear -HB1 HB2. lia.
  - repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
      unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; clear -HB1 HB2 C1 T1 PS1; lia.
Qed.

Theorem piece_commit : ltac2:(tb__ "0|0|
S7S17S16Q40A1A1S41VTR;S36S25S37VA;VKc;Vrb;Vtp0;Vmd0;S49Vp;U1Vph;A3A6S51VCX;Veb;Z40000A3R3R2A5R1A2VTR;S36S25S37VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VCX;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HT.
  apply (tr_pure Kc TR KIT (forall o, In o (ss_objs (ax_S CX)) -> ranges_disjoint (obj_range r o) (B, B + 262144))).
  { intros w Hw. exact (commit_objs r tp w Hw). }
  intros OBJD.
  apply (tr_commit Kc TR KIT (JRp ph) (JRp (ph_set p 1 ph)) CX r tp eb 262144 Q (JR_K A Kc rb tp0 md0 ph)
           (JR_stable A Kc rb tp0 md0 ph _ HKc ltac:(apply Pos.leb_le; exact NX_x)) IC_x R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x eq_refl ltac:(clear; lia)); [|exact HT].
  intros tr ms md Hsp HJ. cbn zeta.
  pose proof HJ as (HFz & HGh & HK & HM & HR & HRM).
  pose proof (HBv r HFz HGh) as EB. destruct HBn as (HB1 & HB2 & HB3).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0.
  destruct CF0 as (_ & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
  pose proof HE as (_ & HA & _).
  assert (Un : bv_unsigned (Z_to_bv 64 262144) = 262144) by (apply u64_lit; clear; lia).
  destruct (space_commit_model A rb tp0 md0 ph tp md (eval r eb) (Z_to_bv 64 262144) HA HM
              ltac:(rewrite EB; clear -HB1; lia) ltac:(rewrite EB, Un, kSpaceSize_val; clear -HB2; lia)) as (RF & MC & OV & ETOP & ELIM).
  rewrite Un in OV. rewrite EB in OV |- *.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  split; [exact HB3|]. split; [clear -HB1 G13; lia|].
  split.
  { rewrite ETOP. destruct HA as (HG & _). rewrite <- (geom_top _ HG). clear -HB2 G14. lia. }
  split; [exact RF|]. split; [exact MC|]. split; [exact OV|].
  split; [exact (HROOM tp md HM)|].
  split; [exact OBJD|].
  split.
  { intros x Hx. unfold ro_addr. rewrite find_segment_A_off; [reflexivity|]. clear -Hx HB1 G13. lia. }
  split; [intros rr y Hin; rewrite XX_x in Hin; destruct Hin|].

  pose proof (MI_ivs_wf segs _ _ HMI) as (Wm & Wn & Wl).
  split; [exact HFz|]. split; [exact HGh|].
  split.
  { unfold vm_forget_range. rewrite with_vm_backing_with_vm. apply HKc.
    match goal with |- Kc _ (with_vmmaps ?h ?m) =>
      replace (with_vmmaps h m) with (with_vm (mkVmState h (m_vm_lazy m) (m_vm_materialized m)) m) by (destruct m; reflexivity) end.
    apply HKc. exact HK. }
  split.
  { apply (mlink_commit A rb tp0 md0 p ph tp md _ HM PH0 PORD); fold B.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
    - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. cbn [mmap_fixed_rw_next vm_noaccess]. rewrite EB, Un. reflexivity.
    - rewrite m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps. reflexivity.
    -
      set (h' := mmap_fixed_rw_next (m_vmmaps md) (eval r eb) (Z_to_bv 64 262144)). set (md1 := with_vmmaps h' md).
      assert (Hwf1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact Wl).
      pose proof (used_commit_le md h' (eval r eb) (Z_to_bv 64 262144) (conj Wm (conj Wn Wl)) eq_refl eq_refl) as PU1. fold md1 in PU1. rewrite EB, Un in PU1.
      pose proof (unpaid_forget_le md1 B (B + 262144) tp Hwf1 (MI_nodupT segs _ _ HMI)) as PU2. apply Nat2Z.inj_le in PU2.
      assert (PU3 : unpaid md1 tp = unpaid md tp) by (unfold md1; apply unpaid_ext; reflexivity). rewrite PU3 in PU2.
      unfold paid. pose proof page_size_pos. fold md1. clear -PU1 PU2 OV H. nia. }
  split; [|exact HRM].
  apply (rlink_grow_quiet A rb ph (ph_set p 1 ph) (fun _ => False) (view segs (rm rb)) (view segs (rm r)) (view segs (rm r)) PQ (ph_quiet_set p 1 ph PQ)); [| | exact HR | |].
  - intros z. rewrite (zone_commit A rb p ph z PH0). tauto.
  - intros z. right. intros X. exact X.
  - intros z _. reflexivity.
  - intros z X. destruct X.
Qed.
End COMMIT.
End SpineCallocR8.

(* [comment removed for export] *)
Module SpineCallocR9.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "lt"; "ge"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "SLit"; "sv"; "cell"; "mkObj"; "ss_objs"; "DUnknown"; "DZero"; "SAlu"; "eval"; "obj_range"; "ranges_disjoint"; "sprop"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "app"; "prod"; "nat"; "option"; "pair"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "gsv"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "entryR"; "frozen"; "ghosts"; "mlink"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "IMG_HI"; "IMG_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "skel"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP"; "pbase"; "ph_get"; "ph_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "O_pcm"; "O_ri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jg.SpineCallocR9"; "O_piece"; "sh_e"; "@Stdlib.Lists.List"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.CRebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Lemma view_rm_hi : ltac2:(tb__ "0|2|
S22Q40M0A1S20S22Q8A1A1M1F_;S0S17S1Z0R1A2S4R1S6Z2Z40A2A2A2S19S4R2S34A2S1S33R2A2A2S16G1S42S25R4R3A3R4S23G0R3A2A1A3F_;F_;Fa;Ff;").
Proof.
  intros f a Ha Hoff. rewrite view_in by exact Ha. unfold rd_of.
  destruct (f (Z_to_bv 64 a)) as [b|]; [reflexivity|]. apply image_byte_A_off2; [exact Ha|]. unfold IMG_LO, IMG_HI in Hoff. lia.
Qed.

Definition O_piece (eb : sv) : sobj := ltac2:(tb__ "0|0|
ScVeb;S9Z0A1S9Z40000A1S1cSbA1SfA5").
Definition sh_e (eb : sv) : sv := ltac2:(tb__ "0|0|
S10S37S26Veb;A1S27A3").
Definition O_shp (eb : sv) : sobj := ltac2:(tb__ "0|0|
ScS46Veb;A1S9Z0A1S9Z8000A1S1cSbA1SeA5").

Lemma sh_run_nums : ltac2:(tb__ "0|7|
S0S0S1Z10007fff8000M0R2A2S1S2R3Z100000000A2R2A2S1S2R3Z40000M1A2S2R4Z2000000000M2A2A2S1S2S2R5G2A2Z1000M3A2Z7fffff800000A2S16S0S3R5Z10000A2Z0M4A3S17S16S0S3S32R6A1M5G3A2G4A3S17S1Z2008fff7000G5A2S17S1S2G5Z8000A2M6G0A2S16S0S32S2R6G1A2A1G6A3A2A2A2F_;F_;F_;F_;F_;FB;FSB;").
Proof.
  intros SB B H1 H2 H3 H4 HM. unfold Sh, SHADOW_OFF.
  destruct (proj1 (Z.mod_divide B 65536 ltac:(lia)) HM) as [q Hq]. subst B.
  replace (q * 65536 / 8) with (q * 8192) by (apply Z.div_unique with 0; lia).
  replace ((q * 65536 + 262144) / 8) with (q * 8192 + 32768) by (apply Z.div_unique with 0; lia).
  split; [|lia]. replace (q * 8192 + 2147450880) with ((q * 2 + 524280) * 4096) by lia. apply Z_mod_mult.
Qed.

Section REVEAL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S2bVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH1 : ltac2:(tb__ "0|0|
S16S1fS3aVp;Vph;A2U1A3").
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S39VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
S8S2cVrb;R1A2S2dVA;Vrb;R2A3S16S0S24Q40S11R3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S17S1S2S41S40VA;A1A1M0Z100000000A2VB;A2S17S1S2VB;Z40000A2S2G0Z2000000000A2A2S16S0S3VB;Z10000A2Z0A3A2A2").
Hypothesis HROOM : ltac2:(tb__ "0|0|
S1bS22Q40A1A1S36S2eVA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S5S38R2R3A2Z8000A2F_;Fmd;Ftp;").

Variable E : axst.
Hypothesis SK_m : ltac2:(tb__ "0|1|
S16S1bS1eS1eSaSaA2SaA2M0A1S2fS7G0S35SdS29VE;A1A1A4S2fS7G0S35S1dS7S44VW;A1S1aS7S3cS1aS7S3dS1aS7S3eS1aS7S3fS1aS7S45Veb;A1S1cS7A1A3A3A3A3A3A3A4A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S47S14S43VW;Vst;A2S15S29VE;A1A1A3").

Lemma reveal_objs : ltac2:(tb__ "0|0|
S8S1bS22Q40A1A1S31S0S0S28S25S2aVA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VE;R5R4R3A6S1Z7fff7000R3A2S1R3Z10007fff8000A2S30S7S7S13S12R9R1A2S21S0S0R6R5A4A2Lo;SdS29VE;A1A1A3F_;F_;F_;Fhi;Flo;Fw;Ftp;Fr;").
Proof.
  intros r tp w lo hi [HsmA HJ] Hlo Hhi. pose proof HJ as (HFz & HGh & _).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S E) [O_pcc0; O_st; O_pcm; O_ri; O_piece eb] r _ HW HE HFz Hsm SK_m XF_m) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|opc [|? ?]]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  assert (SKp : skel opc = skel (O_piece eb)) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r ori O_ri SKr) in RNr.
  assert (RNp : obj_range r opc = (B, B + 262144)).
  { rewrite (obj_range_skel r opc (O_piece eb) SKp). unfold O_piece. rewrite obj_range_mk by (clear; lia). rewrite (HBv r HFz HGh). f_equal; clear; lia. }
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
  destruct HBn as (HB1 & HB2 & _).
  rewrite EO. apply Forall_app. split.
  - apply BZ. right; right. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. clear -Hlo Hhi. lia.
  - repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr, ?RNp; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
      unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; clear -Hlo Hhi HB1 HB2 C1 T1 T2 TB G13; lia.
Qed.

Theorem piece_reveal : ltac2:(tb__ "0|2|
S8S1bS22Q40A1M0A1M1S31S28S25S2aVA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VE;R3R2R1A6S18G1G1S18S8S8S28S25S2aVA;VKc;Vrb;Vtp0;Vmd0;S3bVp;U2Vph;A3A6VE;R1S1dG0R2R5A3R4A6Lr';A2Ltpn;A2F_;Fw;Ftp;Fr;").
Proof.
  intros r tp [tr [ms md]] Hsp.
  pose proof (proj2 Hsp) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. pose proof HJ as (HFz & HGh & HK & HM & HR & HRM).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as (_ & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
  destruct HBn as (HB1 & HB2 & HB3).
  destruct (sh_run_nums (ag_spacebeg (aa_geom A)) B ltac:(clear -G13; lia) HB1 HB2 ltac:(clear -G14 TG; lia) HB3) as (Q1 & Q2 & Q3 & Q4).
  set (q := Sh B) in *.
  pose proof HE as (_ & HA & _ & _ & _ & _ & _ & _ & (Wm0 & Wn0 & Wl0)).
  pose proof HA as (HG & _ & _ & _ & HMI0 & HI3 & HBT0). destruct HMI0 as (VG & _). destruct VG as (_ & _ & _ & _ & _ & _ & _ & _ & N9).

  unfold mlink in HM. cbn zeta in HM. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  change (subF A rb (committed (ph_f ph)) (subU A rb (committed (ph_u ph)) (vm_noaccess (m_vmmaps md0))))
    with (sub2 (committed (ph_u ph)) (U0 A rb) (U0 A rb + kUserMapSize) (committed (ph_f ph)) (F0 A rb) (F0 A rb + kFreeArrayMapSize) (vm_noaccess (m_vmmaps md0))) in M5.
  change (subF A rb (committed (ph_f ph)) (subU A rb (committed (ph_u ph)) (m_vm_lazy md0)))
    with (sub2 (committed (ph_u ph)) (U0 A rb) (U0 A rb + kUserMapSize) (committed (ph_f ph)) (F0 A rb) (F0 A rb + kFreeArrayMapSize) (m_vm_lazy md0)) in M6.
  assert (UF : ag_spacebeg (aa_geom A) <= U0 A rb /\ ag_spacebeg (aa_geom A) <= F0 A rb).
  { unfold U0, F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c.
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF1. unfold cfacts in CF1. cbn zeta in CF1. fold nv c in CF1.
    destruct CF1 as ((_ & C1 & _) & _ & (_ & AU0 & _) & (_ & MF0) & _). pose proof (Zle_0_nat (length (cs_free_array (cst_of A nv)))) as NF0.
    clear -C1 AU0 MF0 NF0. lia. }
  destruct UF as (UL & FL).
  assert (Wn1 : ivs_wf (sub1 (committed (ph_u ph)) (U0 A rb) (U0 A rb + kUserMapSize) (vm_noaccess (m_vmmaps md0)))) by (apply sub1_wf; [exact Wn0 | unfold kUserMapSize; clear; lia]).
  assert (Wl1 : ivs_wf (sub1 (committed (ph_u ph)) (U0 A rb) (U0 A rb + kUserMapSize) (m_vm_lazy md0))) by (apply sub1_wf; [exact Wl0 | unfold kUserMapSize; clear; lia]).
  assert (BAND : forall k, (k < 8)%nat ->
            page_in_ranges (pageZ q k) (m_vm_lazy md) = true /\ forall j, 0 <= j < PG -> covered (vm_noaccess (m_vmmaps md)) (bv_unsigned (pageZ q k) + j) = false).
  { intros k Hk. assert (UP : bv_unsigned (pageZ q k) = q + 4096 * Z.of_nat k) by (apply pageZ_u; clear -Hk Q2 Q3; lia).
    destruct (N9 (pageZ q k)) as [L1 L2].
    { rewrite UP. replace (q + 4096 * Z.of_nat k) with (q + Z.of_nat k * 4096) by (clear; lia). unfold PG. rewrite Z_mod_plus_full. exact Q1. }
    { right. rewrite UP. unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG. clear -Hk Q2 Q3. lia. }
    split.
    - apply page_in_ranges_spec in L1 as (r0 & Hr0 & Hpr). apply page_in_range_spec in Hpr as [X1 X2]. change page_size with 4096 in X2. rewrite UP in X1, X2.
      destruct (sub1_keeps (committed (ph_u ph)) (U0 A rb) (U0 A rb + kUserMapSize) (m_vm_lazy md0) r0 (q + 4096 * Z.of_nat k) (q + 4096 * Z.of_nat k + 4096) Wl0
                  ltac:(unfold kUserMapSize; clear; lia) Hr0 X1 X2 ltac:(clear; lia) ltac:(left; clear -Hk Q3 UL G13; lia)) as (r1 & Hr1 & Y1 & Y2).
      destruct (sub1_keeps (committed (ph_f ph)) (F0 A rb) (F0 A rb + kFreeArrayMapSize) _ r1 (q + 4096 * Z.of_nat k) (q + 4096 * Z.of_nat k + 4096) Wl1
                  ltac:(unfold kFreeArrayMapSize; clear; lia) Hr1 Y1 Y2 ltac:(clear; lia) ltac:(left; clear -Hk Q3 FL G13; lia)) as (r2 & Hr2 & Z1 & Z2).
      rewrite M6. unfold sub2. apply page_in_ranges_spec. exists r2. split; [exact Hr2|]. apply page_in_range_spec. change page_size with 4096. rewrite UP. clear -Z1 Z2. lia.
    - intros j Hj. rewrite M5. unfold sub2. apply sub1_cov_false; [exact Wn1 | unfold kFreeArrayMapSize; clear; lia|].
      apply sub1_cov_false; [exact Wn0 | unfold kUserMapSize; clear; lia | exact (L2 j Hj)]. }
  destruct (SPA_J_out segs _ E r tp _ Hsp) as [HJT _].
  assert (DISJ : Forall (fun o => ranges_disjoint (obj_range r o) (q, q + 4096 * Z.of_nat 8)) (ss_objs (ax_S E))).
  { apply (reveal_objs r tp _ q (q + 4096 * Z.of_nat 8) Hsp); [clear -Q2; lia | clear -Q3; lia]. }
  destruct (SPA_reveal_pages E q 8 r tp tr ms md HJT Q1 ltac:(clear -Q2; lia) ltac:(clear -Q3; lia)
              ltac:(intros k Hk; exact (proj1 (BAND k Hk)))
              ltac:(intros z Hz; destruct (page_base_run q 8 (Z_to_bv 64 z) Q1 ltac:(clear -Q2; lia) ltac:(clear -Q3; lia) ltac:(rewrite u64_lit by (clear -Hz Q2 Q3; lia); exact Hz)) as (k & Hk & Ek & Rk);
                    rewrite u64_lit in Rk by (clear -Hz Q2 Q3; lia);
                    pose proof (proj2 (BAND k Hk) (z - (q + 4096 * Z.of_nat k)) ltac:(unfold PG; clear -Rk; lia)) as X;
                    rewrite pageZ_u in X by (clear -Hk Q2 Q3; lia);
                    replace (q + 4096 * Z.of_nat k + (z - (q + 4096 * Z.of_nat k))) with z in X by (clear; lia); exact X)
              ltac:(pose proof (HROOM tp md (proj1 (proj2 (proj2 (proj2 HJ))))) as X; clear -X; lia) DISJ) as (tpn & r1 & Hsp1 & HRV).
  pose proof HRV as (Rw & Rl & Rtp1 & Rlen & Rvis & Rz & Rk & Ro).
  exists tpn, r1. apply (SPA_J_in segs _ E r1 (tpn ++ tp) _ Hsp1). cbn [w_tr w_cfg cfg_model fst snd].

  assert (RUN : forall z, q <= z < q + 32768 -> 0 <= z < 2 ^ 64 /\ IMG_HI <= z /\ bv_unsigned (Z_to_bv 64 z) = z).
  { intros z Hz. assert (0 <= z < 2 ^ 64) by (clear -Hz Q2 Q3; lia). split; [exact H|]. split; [unfold IMG_HI; clear -Hz Q2; lia | apply u64_lit; exact H]. }
  assert (ZR : forall z, zoneR A rb (ph_set p 2 ph) z <-> (zoneR A rb ph z \/ q <= z < q + 32768)) by (intros z; exact (zone_reveal A rb p ph z PH1)).
  set (m := view segs (rm r)) in *. set (m1 := view segs (rm r1)).
  assert (MO : forall z, ~ (q <= z < q + 32768) -> m1 z = m z).
  { intros z Hz. unfold m1, m, view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:Ez; [|reflexivity].
    apply andb_prop in Ez as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. unfold rd_of.
    rewrite (Ro (Z_to_bv 64 z)); [reflexivity|]. rewrite u64_lit by (clear -E1 E2; lia). clear -Hz. lia. }
  split; [split; [intros i Hi; rewrite Rw; exact (proj1 HFz i Hi) | intros l; rewrite Rl; exact (proj2 HFz l)]|].
  split; [unfold ghosts in *; rewrite !Rw; exact HGh|].
  split; [exact HK|].
  split.
  { apply (mlink_reveal A rb tp0 md0 p ph tp md tpn (proj1 (proj2 (proj2 (proj2 HJ)))) PH1).
    - intros x Hx. destruct (Rtp1 x Hx) as ((k & Hk & ->) & Hnin). split; [exact Hnin|]. exists (Z.of_nat k). split; [clear -Hk; lia|].
      fold B q. rewrite pageZ_u by (clear -Hk Q2 Q3; lia). reflexivity.
    - exact Rlen.
    - pose proof (revealed_paid q 8 r tp r1 tpn md HRV) as RP. clear -RP. lia. }
  split.
  { apply (rlink_quiet_intro A rb ph (ph_set p 2 ph) _ m m1 (ph_quiet_set p 2 ph PQ)); [| exact HR | |].
    - intros z Hz. apply ZR. left. exact Hz.
    - intros z Hz. apply MO. intros X. apply Hz. apply ZR. right. exact X.
    - intros z Hz. apply ZR in Hz.
      assert (ZD : q <= z < q + 32768 \/ ~ (q <= z < q + 32768)) by (clear; lia).
      destruct ZD as [INR|OUTR]; [|rewrite (MO z OUTR); destruct Hz as [Hz|Hz]; [exact (proj1 (proj2 HR) z Hz) | contradiction]].
      destruct (RUN z INR) as (Hz64 & HzI & Uz).
      destruct (reveal_bytes segs q 8 r tp r1 tpn HRV ltac:(clear -Q2; lia) ltac:(clear -Q3; lia)) with (z := z) as [_ [x Hx]]; [|clear -INR; lia|].
      2: { unfold m1. rewrite view_in by exact Hz64. rewrite Hx. discriminate. }

      intros a Ha Hpm. apply (proj1 (page_mem_In _ _)) in Hpm.
      assert (Ha64 : 0 <= bv_unsigned a < 2 ^ 64 /\ IMG_HI <= bv_unsigned a) by (unfold IMG_HI; clear -Ha Q2 Q3; lia).
      assert (DEFm : m (bv_unsigned a) <> None -> rm r a <> None).
      { intros D. unfold m in D. rewrite (view_rm_hi (rm r) (bv_unsigned a) (proj1 Ha64) (or_intror (proj2 Ha64))) in D.
        rewrite Z_to_bv_bv_unsigned in D. exact D. }
      apply DEFm.
      destruct (page_base_run q 8 a Q1 ltac:(clear -Q2; lia) ltac:(clear -Q3; lia) Ha) as (k & Hk & Ek & Rk2).
      assert (UP : bv_unsigned (pageZ q k) = q + 4096 * Z.of_nat k) by (apply pageZ_u; clear -Hk Q2 Q3; lia).
      rewrite Ek in Hpm. rewrite M7 in Hpm. apply in_app_or in Hpm as [Hpm|Hpm].
      +
        apply (proj1 (proj2 HR)). destruct (M8 _ Hpm) as [_ [[RU (j & Hj & Ej)]|[RF (j & Hj & Ej)]]]; rewrite UP in Ej.
        * unfold zoneR. left. split; [exact RU|]. clear -Rk2 Ej Hj. lia.
        * unfold zoneR. right; right; left. split; [exact RF|]. clear -Rk2 Ej Hj. lia.
      +
        assert (BP : band_page (bv_unsigned (pageZ q k))).
        { rewrite UP. unfold band_page. right. unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG. clear -Hk Q2 Q3. lia. }
        destruct (HBT0 _ Hpm BP (bv_unsigned a) ltac:(rewrite UP; unfold PG; clear -Rk2; lia)) as [b0 Hb0].
        assert (ZD0 : zoneR A rb ph (bv_unsigned a) \/ ~ zoneR A rb ph (bv_unsigned a)).
        { unfold zoneR. destruct (revealedp (ph_u ph)), (releasedp (ph_u ph)), (revealedp (ph_f ph)), (releasedp (ph_f ph)), (ph_cnt ph), (ph_ri ph); clear; lia. }
        destruct ZD0 as [ZI|ZO]; [exact (proj1 (proj2 HR) _ ZI)|]. rewrite (proj1 HR _ ZO). rewrite Hb0. discriminate. }
  intros a Ha. rewrite (Ro (Z_to_bv 64 a)); [exact (HRM a Ha)|]. rewrite u64_lit by (unfold IMG_LO, IMG_HI in Ha; clear -Ha; lia). unfold IMG_HI in Ha. clear -Ha Q2. lia.
Qed.
End REVEAL.
End SpineCallocR9.

