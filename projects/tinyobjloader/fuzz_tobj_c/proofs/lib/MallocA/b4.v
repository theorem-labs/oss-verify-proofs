(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From Stdlib Require FunctionalExtensionality Permutation.
From stdpp Require list.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq bf.

(* [comment removed for export] *)
Module RefillS.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "of_nat"; "div"; "ltb"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "valuation"; "rm"; "rw"; "FcsrFrm0"; "cell"; "mkSS"; "rl"; "DUnknown"; "SVar"; "mkCell"; "mkObj"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "list"; "prod"; "bool"; "None"; "false"; "true"; "app"; "length"; "andb"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kUserMapSize"; "Sh"; "Size"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "free_array"; "kFreeArrayMapSize"; "region_beg"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_mapped_user"; "AA"; "budget_bound"; "cs_free_array"; "cs_mapped_free_array"; "aa_cache_inited"; "aa_geom"; "ag_spacebeg"; "ag_thread"; "class_state"; "cs_allocated_user"; "cs_cache"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "needs_populate"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "NXR"; "nv_q24"; "JLRf"; "JRf"; "L_rf"; "O_stR"; "Pre_rf"; "rf_depth"; "rf_new"; "NXRC"; "NXRP"; "RF_ENT"; "RF_RET"; "cache_e"; "refill_zone"; "regsR"; "rf_grows"; "rfacts"; "vSTR"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_CLS"; "O_pcc0"; "V_SIZE"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "BASEG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mkA"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "K0C"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "ALLOC_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "MUCAP"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI PrimCredit RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition RF_ENT : Z := 0x41168.
Definition RF_RET : Z := 0x411c0.
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
Module RebuildI.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "pow"; "sub"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "ag_thread"; "aa_cache_inited"; "aa_geom"; "aa_live"; "ageom"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cls"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "ag_spacebeg"; "class_state"; "cs_mapped_free_array"; "cs_mapped_user"; "mkAA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "bview"; "view"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI"; "ZI"; "initA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "Size"; "max_count"; "IMG_HI"; "IMG_LO"; "free_array"; "region_beg"; "region_info"; "@Corelib.Init.Datatypes"; "bool"; "false"; "option"; "true"; "Some"; "list"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "class_repr"; "bandtp_inv"; "model_inv"; "present_but"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ"; "geoR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "czone"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue ContractFreeNull SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.RebuildR.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition initA (A : AA) : AA := ltac2:(tb__ "0|0|
S24S11VA;A1S17VA;A1S37S1fVA;A1S1cVA;A1S12VA;A1S1eVA;A1S1dVA;A1S18VA;A1S1aVA;A1S19VA;A1S1bVA;A1S16VA;A1S15VA;A1S14VA;A1Af").
Lemma refillA_initA : ltac2:(tb__ "0|0|
SeS0S8SeS42S2bR2A1R1A2S42R2R1A2A3Fc;FA;"). Proof. reflexivity. Qed.
Lemma initA_inited : ltac2:(tb__ "0|0|
SeS8S34S10R1A1S37A3S8SeS2bR2A1R2A3F_;FA;"). Proof. intros [? ? i ? ? ? ? ? ? ? ? ? ? ? ?] H. cbn in H. subst i. reflexivity. Qed.

Definition ZI (T z : Z) : Prop := ltac2:(tb__ "0|0|
S7S2S1VT;Z120A2Vz;A2S3Vz;S1VT;Zad0A2A2A2").

Lemma zi_out : ltac2:(tb__ "0|0|
S0S0S0S0S7S2R3R1A2S3R1R2A2A2SaS2R3S1R5Z120A2A2S2S1R5Zad0A2R4A2A2S9S2aR6R3A2A1F_;F_;Fz;Fhi;Flo;FT;").
Proof. intros T lo hi z Hz HO HZ. unfold ZI in HZ. lia. Qed.
Lemma zi_sh_out : ltac2:(tb__ "0|0|
S0S0S0S0S0S0S41R6R5R4A3S7S2S2cR4A1R2A2S3R2S2cR3A1A2A2S2Z0R5A2S2R5S5Z2Z2fA2A2S9S2aR9R5A2A1F_;F_;F_;F_;Fz;Fhi;Flo;Ftop;FT;FSB;").
Proof.
  intros SB T top lo hi z (S1 & S2 & TG & T1 & T2 & ST & TB) Hz L0 HT HZ. unfold ZI in HZ.
  assert (LH : lo <= hi) by (destruct (Z_le_dec lo hi) as [X|X]; [exact X|]; pose proof (Geometry.Sh_mono hi lo ltac:(lia)); lia).
  pose proof (Sh_band lo ltac:(lia)) as B1. pose proof (Sh_band hi ltac:(lia)) as B2. lia.
Qed.
Lemma zi_czone : ltac2:(tb__ "0|2|
S0S0S0S0S0S0S0S41R7R6R5A3S7S2Z1R5A2S2R5Z1eA2A2S2Z0M0R5A2S3G0R5A2S2S1R7R6A2S6S5Z2M1Z20A2S5G1Z1dA2A2A2S44RcR9R8R7R6A5S9S2aRcR7A2A1F_;F_;F_;F_;F_;F_;Fz;FS;Fo;Fc;Ftop;FT;FSB;").
Proof.
  intros SB T top c o S z HG Hc Ho HS HoS HZ. pose proof HG as (S1 & S2 & TG & T1 & T2 & ST & TB). unfold czone in HZ. cbn zeta in HZ.
  destruct HZ as [H|H].
  - apply (zi_out T (SB + 2 ^ 32) (SB + 2 ^ 37) z); lia.
  - pose proof (Sh_add_le (SB + c * 2 ^ 32 + o) S (SB + c * 2 ^ 32 + o + S) ltac:(lia) ltac:(lia) ltac:(lia)) as M.
    apply (zi_sh_out SB T top (SB + c * 2 ^ 32 + o) (SB + c * 2 ^ 32 + o + S) z HG); lia.
Qed.

Lemma class_repr_init : ltac2:(tb__ "0|9|
S27S27S13SeS0S21S7S2Z1R2A2S2R2Z1eA2A2S8S34S10R4A1S35A3S0SaS7S2S33S20R7A1M0R5A2M1R1A2S3R1S1G1Z80A2A2A2SaS7S2S31G0R5A2M2R1A2S3R1S1G2S22R4A1A2A2A2S7S2S2cS32G0R5A2M3A1R1A2S3R1S2cS1G3S23R4A1A2M4A1A2A2A2A2S8S36S3aQ8A1A1R9R2A1RaR2A1A3F_;Fz;S40R8G3G4S12R6A1A4S29R9S1S1SfR8A1Zd0M5A2S4Z50M6R6A2A2M7S1G7G6A2A3S25RaS26S1S1SfR9A1G5A2S4G6R7A2A2U4M8Z0A3A2S25RbS26S1S1S1SfRaA1G5A2S4G6R8A2A2Z4A2G8S2eR8A1A3A2S25RcS26S1S1S1SfRbA1G5A2S4G6R9A2A2Z8A2U8S2dR9A1A3A2S3dReRcRbRaR9A5S3dReRdS2bRcA1RbRaA5F_;F_;F_;F_;F_;F_;F_;F_;F_;Fcs;Fc;FA;FG;Fm';Fm;").
Proof.
  intros m m' G A c cs Hc Hini AG PU' PE' K1' K2' K3' P4.
  assert (CA : forall cc, (forall k, (k < c_w cc)%nat ->
             (region_info (ag_spacebeg G) c <= c_addr cc + Z.of_nat k < region_info (ag_spacebeg G) c + 128
              \/ free_array (ag_spacebeg G) c <= c_addr cc + Z.of_nat k < free_array (ag_spacebeg G) c + cs_mapped_free_array cs
              \/ Sh (region_beg (ag_spacebeg G) c) <= c_addr cc + Z.of_nat k < Sh (region_beg (ag_spacebeg G) c + cs_mapped_user cs))) -> cell_ok m cc -> cell_ok m' cc).
  { intros cc Hf. apply cell_ok_agree. intros k Hk. apply AG. exact (Hf k Hk). }
  unfold class_repr in P4 |- *.
  change (live_ids G (initA A) c) with (live_ids G A c). change (qall (initA A)) with (qall A). change (aa_live (initA A)) with (aa_live A).
  change (aa_cache_inited (initA A)) with true.
  set (ri := region_info (ag_spacebeg G) c) in *. set (fa := free_array (ag_spacebeg G) c) in *. set (rb := region_beg (ag_spacebeg G) c) in *.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & TI10 & CV10 & MC10 & FC10).
  assert (FRI : forall off w, 0 <= off -> off + Z.of_nat w <= 72 -> forall k, (k < w)%nat ->
            (ri <= ri + off + Z.of_nat k < ri + 128 \/ fa <= ri + off + Z.of_nat k < fa + cs_mapped_free_array cs
             \/ Sh rb <= ri + off + Z.of_nat k < Sh (rb + cs_mapped_user cs))).
  { intros off w Ho Hw k Hk. left. lia. }
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mutex; lia | exact C1]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_exhausted; lia | exact C8]|].
  split; [eapply present_agree; [|exact PRI]; intros z Hz; apply AG; left; unfold kRegionInfoStride in Hz; lia|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split.
  { intros i x Hi. apply CA; [|exact (C9 i x Hi)]. cbn [c_addr c_w]. intros k Hk. right; left.
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. lia. }
  split; [eapply present_agree; [|exact PR]; intros z Hz; apply AG; right; left; lia|].
  split; [exact N7|].
  split; [exact PU'|].
  split; [eapply present_agree; [|exact PS]; intros z Hz; apply AG; right; right; lia|].
  split; [exact PE'|].
  split; [exact ND|].
  split; [exact LV|].
  destruct (CN Hini) as [EC _].
  split.
  - intros _. rewrite EC. cbn [length Z.of_nat]. split; [exact K1'|]. split; [exact K2'|]. split; [exact K3'|].
    split; [intros i x Hi; destruct i; discriminate Hi|]. destruct (kchunks_facts c Hc) as (X1 & X2 & _). lia.
  - split; [intros X; discriminate X|]. exact (conj TI10 (conj CV10 (conj MC10 FC10))).
Qed.

Section RI.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Lemma init_rebuild : ltac2:(tb__ "0|8|
SeSdSdS39S3aQ40M0A1A1M1G1S3cS3cVAInv;R7R6R4R2A4S8S34S10R8A1S35A3S11R9A1S13SfR1A1S0S28Vsegs;ScR9A1A2S27S28Vsegs;ScRbA1A2S27S0S9S2aR4R1A2A1S8S36S3aQ8A1M2A1M3R4R2A1R3R2A1A3F_;Fz;S0S2aR5R1A2SbG2G2S8G3R6R3A1S38G2R1A2A3Lb;A2F_;Fz;S0S7S2S30R1A2S3R1S2fA2A2S8G3ScRfS3bG0R2A2M4A2ScR10G4A2A3F_;Fa;S0S7S2Z1R1A2S2R1Z1eA2A2S7S25R7S26S1S1R8Zd0A2S4Z50R2A2A2M5U4M6Z0A3A2S7S25R7S26S1G5Z4A2G6S2eR2A1A3A2S25R7S26S1G5Z8A2U8S2dR2A1A3A2A2A2F_;Fc;S3fVsegs;S2bR11A1RdRbA4S3eR7ReA2S7VAInv;S2bR13A1M7R11RfRdA4S43VCST;VXGL;R13G7ScR12A1ScR11A1A6A2F_;F_;F_;F_;F_;F_;TvE;Tv3;TT;TG;F_;F_;Fmd;Fmd0;Ftp;Ftp0;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp0 tp md0 md HA Hini G T v3 vE VO PRES HRMI HCELLS HMD HBT.
  set (Ar := initA A).
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB). fold vE in HR, HF, HRest. fold G in HG, HR, HF, HRest.
  pose proof HG as HG0. pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & TG).
  fold G in G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, TG. fold T in G4, G5, G10, G13, G14.
  set (SB := ag_spacebeg G) in *.
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
  assert (GEO : geoR SB T (topG G)).
  { unfold geoR. clear -S1 S2 TG G4 G5 T3 TB. lia. }
  assert (ZND : forall z, ZI T z \/ ~ ZI T z) by (intros z; unfold ZI; clear; lia).

  assert (ENVF : forall z, ZI T z -> fs_footb G z = false).
  { intros z Hz. apply fs_footb_thread; [exact HG0 | fold G T; unfold ZI in Hz; clear -Hz; lia]. }
  set (m3 := maskv (fs_footb G) v3). set (mE := maskv (fs_footb G) vE).
  assert (AGm : forall z, ~ ZI T z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity | exact (VO z Hz)]. }
  assert (MTH : forall z, T <= z < T + 4096 -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. apply fs_footb_thread; [exact HG0 | fold G T; clear -Hz; lia]. }
  fold mE in Hlive, PC, Hsec, Hq, Hdep, Hia, HTH, Hmisc.
  assert (PRES3 : forall z, ZI T z -> exists b, m3 z = Some b).
  { intros z Hz. rewrite MTH by (unfold ZI in Hz; clear -Hz; lia). exact (PRES z Hz). }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc) | rewrite (AGm z Hn); exact (Hp z Hz)]. }
  assert (PRESB : forall lo hi L, present_but mE lo hi L -> present_but m3 lo hi L).
  { intros lo hi L Hp z Hz HL. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc) | rewrite (AGm z Hn); exact (Hp z Hz HL)]. }
  assert (EG' : aa_geom Ar = G) by reflexivity.
  assert (HQP : q_pure A) by exact (proj1 (quarantine_repr_pure mE A HG Hq)).
  assert (HAU : forall c', 1 <= c' <= 30 -> 0 <= cs_allocated_user (SegQ_wf2.cls_of A c') <= kUserSpaceSize).
  { intros c' Hc'. pose proof (PC c' Hc') as HC. unfold class_repr in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _). unfold SegQ_wf2.cls_of, kUserMapSize in *. clear -M2 M3. lia. }

  assert (NE_img : forall z, IMG_LO <= z < IMG_HI -> ~ ZI T z).
  { intros z Hz. unfold IMG_LO, IMG_HI in Hz. apply (zi_out T 65536 6578176 z Hz). clear -TI. lia. }
  assert (NE_space : forall z, SB <= z < SB + 2 ^ 37 + 4096 -> ~ ZI T z).
  { intros z Hz. apply (zi_out T SB (SB + 2 ^ 37 + 4096) z Hz). clear -T3. lia. }
  assert (NE_sec : forall i ch z, nth_error (aa_sec A) i = Some ch ->
            (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch \/ Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)) -> ~ ZI T z).
  { intros i ch z Hi Hz. destruct (SEC3 i ch Hi) as (E1 & E2 & _). fold T in E2. fold SB in E1.
    destruct Hsec as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D10, D12. unfold PG in D8.
    destruct D10 as (D10a & D10l & _ & _ & D10b).
    destruct Hz as [Hz|Hz].
    - apply (zi_out T (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z Hz). clear -E2. lia.
    - apply (zi_sh_out SB T (topG G) (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z GEO Hz); [clear -D10a; lia | clear -D12 TG; lia]. }
  assert (LIVE_OUT : forall b n z, In (b, n) (aa_live A) ->
            (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> ~ ZI T z).
  { intros b n z Hin Hz. destruct (is_primary n) eqn:HP.
    - pose proof (live_prim_czone A HG SG3c mE Hsep Hprim0 b n Hin HP) as LPC. cbv zeta in LPC. destruct LPC as (D1 & O0 & OM & OE & _ & _ & CZ). fold SB in O0, OM, OE, CZ.
      set (c' := ClassID (needed n)) in *. set (o' := b - rz n - (SB + c' * 2 ^ 32)) in *.
      assert (SZ0 : 0 < Size c') by (destruct (Size_facts c' D1) as [X _]; clear -X; lia).
      exact (zi_czone SB T (topG G) c' o' (Size c') z GEO D1 O0 SZ0 OE (CZ z Hz)).
    - destruct (live_sec_map A mE Hsep Hsec HI3c b n Hin HP) as (i & ch & Hi & Eb & RZ & Hn1 & BN & D6 & D0 & DI). unfold PG in Eb, D6.
      apply (NE_sec i ch z Hi). destruct Hz as [Hz|Hz]; [left; clear -Hz Eb RZ BN; lia | right].
      pose proof (Geometry.Sh_mono (sc_map_beg ch) b ltac:(clear -Eb; lia)) as M1.
      pose proof (Sh_add_le b (n + 7) (sc_map_beg ch + sc_map_size ch) ltac:(clear -Eb DI; destruct DI as (X & _); lia) ltac:(clear -Hn1; lia) ltac:(clear -BN; lia)) as M2.
      clear -Hz M1 M2. lia. }
  assert (QF_OUT : forall z, q_foot A z -> ~ ZI T z).
  { intros z Hz. destruct (qfoot_cases A mE HG HI3c HQP Hsec HAU z Hz) as [(c' & o' & (D1 & O0 & OM & OE & IDin) & CZ)|(i & ch & Hi & Hr)].
    - fold SB in CZ. assert (SZ0 : 0 < Size c') by (destruct (Size_facts c' D1) as [X _]; clear -X; lia).
      exact (zi_czone SB T (topG G) c' o' (Size c') z GEO D1 O0 SZ0 OE CZ).
    - exact (NE_sec i ch z Hi Hr). }

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz. apply VO.
    destruct (rtc_foot_cases G z Hz) as [K|[K|[K|[K|K]]]].
    - exact (NE_img z K).
    - fold T in K. apply (zi_out T T (T + 288) z); clear -K; lia.
    - apply (zi_out T (ag_ctx G) (ag_ctx G + 4096) z ltac:(clear -K; lia)). clear -G13. lia.
    - apply (zi_out T (ag_dtls G) (ag_dtls G + 4096) z ltac:(clear -K; lia)). clear -G14. lia.
    - apply (zi_out T (ag_fsb G) (ag_fsb G + 11571200) z ltac:(clear -K; lia)). clear -G10. lia. }
  assert (HFS : fs_inv (restrictv (fs_footb G) v3) Ar).
  { rewrite (restrictv_ext (fs_footb G) vE v3) by (intros z Hz; apply VO; intros Hc; rewrite (ENVF z Hc) in Hz; discriminate).
    exact HF. }
  assert (HLS : live_sep Ar) by exact Hsep.
  assert (HLB : live_block_repr m3 Ar).
  { apply (live_block_repr_agree mE m3 A Ar eq_refl); [|intros b n Hin; exact (proj1 (Hsep b n Hin))|exact Hlive].
    intros b n z Hin Hz. apply AGm. exact (LIVE_OUT b n z Hin Hz). }
  assert (HPR : primary_repr m3 Ar).
  { unfold primary_repr. rewrite EG'. split; [exact PL|]. split; [exact P0|]. split; [exact P31|].
    intros c' Hc'. change (aa_cls Ar) with (aa_cls A).
    pose proof (PC c' Hc') as PC'. pose proof PC' as PCd. unfold class_repr in PCd.
    destruct PCd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & M6 & _ & _ & _ & PU & _ & PE & _).
    pose proof (Zle_0_nat (length (cs_free_array (nthZ (aa_cls A) c' cs_empty)))) as L0.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3, M6.
    destruct (HCELLS c' Hc') as (K1' & K2' & K3').
    assert (PCB : T + 288 <= T + 0xd0 + 80 * c' /\ T + 0xd0 + 80 * c' + 80 <= T + 2768) by (clear -Hc'; lia).
    apply (class_repr_init mE m3 G A c' _ Hc' Hini); [| apply PRESB; exact PU | apply PRESX; exact PE | | | | exact PC'].
    - intros z Hz. apply AGm. fold SB in Hz.
      unfold region_info, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kRegionInfoStride in Hz. rewrite kSpaceSize_val in Hz.
      destruct Hz as [Hz|[Hz|Hz]].
      + apply NE_space. clear -Hz Hc'. lia.
      + apply NE_space. clear -Hz Hc' M6 L0. lia.
      + apply (zi_sh_out SB T (topG G) _ _ z GEO Hz); [clear -S1 Hc'; lia | clear -S2 TG Hc' M2 M3; lia].
    - eapply cell_ok_agree; [|exact K1']. cbn [c_addr c_w]. intros k Hk. apply MTH. clear -Hk PCB G4. lia.
    - eapply cell_ok_agree; [|exact K2']. cbn [c_addr c_w]. intros k Hk. apply MTH. clear -Hk PCB G4. lia.
    - eapply cell_ok_agree; [|exact K3']. cbn [c_addr c_w]. intros k Hk. apply MTH. clear -Hk PCB G4. lia. }
  assert (LIVM : forall z, in_rangesZ (aa_live A) z -> in_rangesZ (aa_live Ar) z) by (intros z Hz; exact Hz).
  assert (HSR : secondary_repr m3 Ar).
  { refine (secondary_repr_agree mE m3 A Ar eq_refl eq_refl eq_refl _ _ _ LIVM Hsec).
    - intros i ch z Hi Hz. apply AGm. exact (NE_sec i ch z Hi Hz).
    - intros z Hz. apply AGm. destruct Hsec as (_ & _ & SC2 & _ & SC45 & _). fold G in SC45, Hz. destruct SC45 as [_ (SC4a & _ & SC5 & _ & SC4)].
      unfold kPtrArrayReserve in SC2, SC4, PAB3, PABT3.
      apply (zi_out T (ag_pab G) (ag_pab G + 2 ^ 23) z ltac:(clear -Hz SC2; lia)). clear -PABT3. lia.
    - intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HQR : quarantine_repr m3 Ar).
  { refine (quarantine_repr_agreeR mE m3 A Ar eq_refl eq_refl eq_refl eq_refl _ _ _ _ Hq).
    - intros c'. change (aa_cls Ar) with (aa_cls A). clear; lia.
    - intros z Hz. apply AGm. exact (QF_OUT z Hz).
    - intros z Hz. apply AGm. fold G T in Hz. apply (zi_out T T (T + 288) z); clear -Hz; lia.
    - intros z Hz. apply AGm. apply NE_img. unfold QG, IMG_LO, IMG_HI in *. clear -Hz. lia. }
  assert (HIA : ia_inv m3 Ar).
  { refine (ia_inv_agree mE m3 A Ar eq_refl _ Hia). intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HTI : thread_inv m3 G).
  { destruct HTH as [TH1 TH2]. fold G T in TH1, TH2. unfold thread_inv. fold T. split.
    - rewrite AGm; [exact TH1|]. unfold ZI. clear. lia.
    - apply PRESX. exact TH2. }
  assert (HMI : misc_inv m3).
  { refine (misc_inv_agree mE m3 _ Hmisc). intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HDEP : depot_wf m3 Ar).
  { unfold depot_wf in Hdep |- *. change (aa_depot Ar) with (aa_depot A). eapply depot_mem_frame; [|exact Hdep]. intros a Ha. apply AGm.
    assert (BLK : forall bb L, In (bb, L) (dblocks (aa_depot A)) -> bb <= a < bb + L -> ~ ZI T a).
    { intros bb L Hbb Hab. destruct (DEP3 (bb, L) Hbb) as (DI & ST & _ & _ & _ & SS & _). unfold sepZ in ST, SS. cbn [fst snd] in DI, ST, SS. fold T in ST.
      apply (zi_out T bb (bb + L) a Hab). clear -ST. lia. }
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - apply (NE_img a). unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. unfold IMG_LO, IMG_HI. clear -Hs. lia.
    - apply (BLK bb NBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
    - apply (BLK bb FBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb]. }
  assert (HI3' : inv3 Ar).
  { pose proof HI3c as (X1' & X2' & X3' & X4' & X5' & X6' & X7' & X8' & X9'). split; [exact X1'|]. split; [exact X2'|]. split; [exact X3'|].
    split; [exact X4'|]. split; [exact X5'|]. split; [exact X6'|]. split; [exact X7'|]. split; [exact X8'|]. intros _. reflexivity. }
  assert (HA' : AInv Ar rho3 tp md).
  { unfold AInv, AInvA. rewrite EG'. fold v3. split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|].
    split; [|split; [exact HMD | split; [exact HI3' | exact HBT]]].
    fold m3. split; [exact HLS|]. split; [exact HLB|]. split; [exact HPR|]. split; [exact HSR|]. split; [exact HQR|].
    split; [exact HDEP|]. split; [exact HIA|]. split; [exact HTI | exact HMI]. }
  split; [exact HA'|].

  assert (HFv : fs_inv (restrictv (fs_footb G) vE) A) by exact HF.
  assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ ZI T a -> rm rho3 (Z_to_bv 64 a) = rm rhoE (Z_to_bv 64 a)).
  { intros a Ha Hn. destruct (Z_lt_dec a IMG_LO) as [LO|NLO]; [|destruct (Z_le_dec IMG_HI a) as [HI|NHI]].
    - rewrite <- (view_rm_off (rm rho3) a Ha (or_introl LO)), <- (view_rm_off (rm rhoE) a Ha (or_introl LO)). exact (VO a Hn).
    - rewrite <- (view_rm_off (rm rho3) a Ha (or_intror HI)), <- (view_rm_off (rm rhoE) a Ha (or_intror HI)). exact (VO a Hn).
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
            \/ (0 <= y < 2 ^ 47 /\ (y < T \/ T + 4096 <= y))).
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
  assert (SHY : forall y, 0 <= y < 2 ^ 47 -> ~ ZI T (Sh y)).
  { intros y By.
    pose proof (Z.div_mod y 8 ltac:(clear; lia)) as DY. pose proof (Z.mod_pos_bound y 8 ltac:(clear; lia)) as MY.
    apply (zi_sh_out SB T (topG G) (8 * (y / 8)) (8 * (y / 8) + 8) (Sh y) GEO); [|clear -By DY MY; lia|clear -By DY MY; lia].
    unfold Sh. replace (8 * (y / 8) / 8) with (y / 8) by (rewrite Z.mul_comm, Z.div_mul; clear; lia).
    replace ((8 * (y / 8) + 8) / 8) with (y / 8 + 1) by (replace (8 * (y / 8) + 8) with ((y / 8 + 1) * 8) by (clear; lia); rewrite Z.div_mul; clear; lia).
    clear. lia. }
  apply RMO; [exact Ha|].
  destruct Hcl as [[CL1 _]|[CL1 _]].
  - destruct (NOC a CL1) as [(b & n & Hbn & Hab)|(B1 & B2)].
    + apply (LIVE_OUT b n a Hbn). left. pose proof (rz_bound n). clear -Hab H. lia.
    + unfold ZI. clear -B2. lia.
  - destruct CL1 as [(y & Cy & ->)|(y & Gy & ->)].
    + apply SHY. destruct (NOC y Cy) as [(b & n & Hbn & Hyb)|(B1 & _)]; [|exact B1].
      exact (proj1 (client_addr_bounds CST HCST A y _ HG HFv Hsep Cy)).
    + destruct (HXGL y Gy) as [Y1 Y2]. unfold IMG_HI in Y2. apply (SHY y). clear -Y1 Y2. lia.
Qed.
End RI.
End RebuildI.

(* [comment removed for export] *)
Module RebuildG.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "mul"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "bview"; "maskv"; "view"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_mapped_user"; "AA"; "class_state"; "cs_allocated_user"; "cs_mapped_free_array"; "aa_geom"; "aa_cls"; "aa_sec"; "cs_cache"; "cs_free_array"; "ageom"; "cs_empty"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cache_inited"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "ag_spacebeg"; "ag_thread"; "list_upd"; "mkAA"; "qbatch"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@Corelib.Init.Datatypes"; "length"; "list"; "Some"; "nat"; "option"; "true"; "app"; "bool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qall"; "q_ids"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "IMG_HI"; "IMG_LO"; "RI_allocated_meta"; "RI_allocated_user"; "RI_exhausted"; "RI_mapped_free_array"; "RI_mapped_meta"; "RI_mapped_user"; "RI_mutex"; "RI_num_freed"; "free_array"; "max_count"; "region_beg"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "fs_footb"; "quarantine_repr"; "bandtp_inv"; "live_ids"; "model_inv"; "nthZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "AInvQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildG"; "setclsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "q_pure"; "@Stdlib.Lists.List"; "nth_error"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ"; "envR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "cls_pure"; "refillA"; "refill_cs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue ContractFreeNull SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.RebuildR.
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
    apply (env_out SB T (topG G) c nf mu 65536 6578176 z GEO C1 NF0 MUB Hz); [clear -S1; lia | clear -TI; lia | clear; lia | exact Hc]. }
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
            pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep.rz_facts n) as (_ & RZ16).
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
Module F0A_limbo.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "pow"; "modulo"; "div"; "mul"; "leb"; "ltb"; "of_nat"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "ag_thread"; "sec_chunk"; "aa_live"; "aa_depot"; "aa_sec"; "topG"; "AA"; "ag_ctx"; "ag_dtls"; "ageom"; "ag_fsb"; "ag_pab"; "cs_mapped_user"; "depot_state"; "sc_map_beg"; "class_state"; "cs_mapped_free_array"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "option"; "bool"; "Some"; "list"; "prod"; "false"; "pair"; "nat"; "andb"; "true"; "app"; "cons"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.F0A_limbo.LIMBO"; "CH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.F0A_limbo"; "LZ0"; "lb_body"; "LZ0b"; "cls_meta2"; "rho_mid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "mkVal"; "rl"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "present"; "bview"; "cell_ok"; "mkACell"; "maskv"; "restrictv"; "rtc_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "rz"; "IMG_HI"; "IMG_LO"; "kPtrArrayReserve"; "region_beg"; "FS_total"; "free_array"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "fs_footb"; "present_but"; "AInvA"; "class_repr"; "fs_inv"; "alloc_magic_ok"; "bandtp_inv"; "geom_ok"; "inv3"; "model_inv"; "shadow_unpoisoned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "rest_invQC"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "blk_geo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "BLK"; "CZA"; "CZI"; "GEO"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SMGlue RebuildM SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition lb_body (m : bview) (b n : Z) : Prop := ltac2:(tb__ "0|5|
SbScS28S25Q8M0A1M1A1M2Vm;S3Vb;Z10A2A1S2aG1S26G0Z2M3A2A2A3SbS43Vm;S44S3Vb;ZcA2U4S5Vn;S4G3Z20A2M4A2A3A2SbS43Vm;S44S3Vb;ZeA2U2S6Vn;G4A2A3A2SbS5dVm;Vb;Vn;A3SbS58Vm;Vb;Vn;A3SfG1G1SbScG2Vm;S3Vb;ZfA2A1S2aG1R1A2A3ScS11S5S27G0R1A2Z4A2Z1A3A2Lt;A2A2A2A2A2A2").
Definition LZ0 (p n : Z) (z : Z) : Prop := ltac2:(tb__ "0|3|
SdSbS0S3Vp;Z10A2Vz;A2S2Vz;S3Vp;Z8M0A2A2A2SdSbS0Vp;Vz;A2S2Vz;S1Vp;S49Vn;A1M1A2A2A2SbS0S4aVp;A1M2Vz;A2S2Vz;S1G2S6G1G0A2A2A2A2A2A2").
Lemma LZ0_dec : ltac2:(tb__ "0|1|
S11S11S11SdS36R3R2R1A3M0SeG0A1A2Fz;Fn;Fp;").
Proof. intros p n z. unfold LZ0. lia. Qed.

Definition cls_meta2 (G : ageom) (c : Z) (cs : class_state) (z : Z) : Prop := ltac2:(tb__ "0|3|
S52S13VG;A1M0Vc;A2S11S51G0Vc;A2S11SdSbS0R2Vz;A2S2Vz;S1R2Z80A2A2A2SdSbS0R1Vz;A2S2Vz;S1R1S24Vcs;A1A2A2A2SbS0S1S1S14VG;A1Zd0A2S7Z50M1Vc;A2A2M2Vz;A2S2Vz;S1G2G1A2A2A2A2A2Tfa;Tri;").
Lemma class_repr_agree_pres : ltac2:(tb__ "0|2|
S42S42S1dS1aS11S23SbS0Z1R2A2S0R2Z1eA2A2S11S39R6R4R3R1A4ScS28S25Q8A1A1R8R2A1R9R2A1A3F_;Fz;S54R7S4fS13R6A1R4A2M0S1G0S20R3A1A2S16R5A1A4S41R8S4aS4fS13R7A1R5A2M1A1S4aS1G1S20R4A1A2A1A3S56RaR8R7R6R5A5S56RaR9R8R7R6A5F_;F_;F_;F_;F_;Fcs;Fc;FA;FG;Fm';Fm;").
Proof.
  intros m m' G A c cs Hc AG PU' PS' P4.
  assert (CA : forall cc, (forall k, (k < c_w cc)%nat -> cls_meta2 G c cs (c_addr cc + Z.of_nat k)) -> cell_ok m cc -> cell_ok m' cc).
  { intros cc Hf. apply cell_ok_agree. intros k Hk. apply AG. exact (Hf k Hk). }
  unfold class_repr in P4 |- *.
  set (ri := region_info (ag_spacebeg G) c) in *. set (fa := free_array (ag_spacebeg G) c) in *. set (rb := region_beg (ag_spacebeg G) c) in *.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & TI10 & CV10 & MC10 & FC10).
  assert (FRI : forall off w, 0 <= off -> off + Z.of_nat w <= 72 -> forall k, (k < w)%nat -> cls_meta2 G c cs (ri + off + Z.of_nat k)).
  { intros off w Ho Hw k Hk. left. unfold ri in *. lia. }
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mutex; lia | exact C1]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CA; [cbn [c_addr c_w]; apply FRI; unfold RI_exhausted; lia | exact C8]|].
  split; [eapply present_agree; [|exact PRI]; intros z Hz; apply AG; left; unfold ri in *; unfold kRegionInfoStride in Hz; lia|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split.
  { intros i x Hi. apply CA; [|exact (C9 i x Hi)]. cbn [c_addr c_w]. intros k Hk. right; left.
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. unfold fa in *. lia. }
  split; [eapply present_agree; [|exact PR]; intros z Hz; apply AG; right; left; unfold fa in *; lia|].
  split; [exact N7|].
  split; [exact PU'|].
  split; [exact PS'|].
  split; [eapply present_agree; [|exact PE]; intros z Hz; apply AG; right; right; lia|].
  split; [exact ND|].
  split; [exact LV|].
  split.
  - intros Hi. destruct (CI Hi) as (K1 & K2 & K3 & K4 & K5). split; [|split; [|split; [|split; [|exact K5]]]].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; lia | exact K1].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; lia | exact K2].
    + apply CA; [cbn [c_addr c_w]; intros k Hk; right; right; lia | exact K3].
    + intros i x Hi'. apply CA; [|exact (K4 i x Hi')]. cbn [c_addr c_w]. intros k Hk. right; right.
      pose proof (nth_error_Some_lt _ _ _ Hi') as L. pose proof (max_count_le16 c Hc). lia.
  - split; [|exact (conj TI10 (conj CV10 (conj MC10 FC10)))].
    intros Hn. destruct (CN Hn) as [K1 K2]. split; [exact K1|]. eapply filled_agree; [|exact K2]. intros z Hz. apply AG. right; right. lia.
Qed.

Section LIMBO.
Let segs : list Segment := segsA.

Variables (A0 : AA) (rho0 : valuation) (tp0 : list word) (md0 : Model) (p n : Z) (l1 l2 : list (Z * Z)).
Hypothesis HA0 : ltac2:(tb__ "0|0|
S55Vsegs;VA0;Vrho0;Vtp0;Vmd0;A5").
Hypothesis HLV : ltac2:(tb__ "0|1|
ScS2bS2cS11S11A2M0A1S16VA0;A1S32G0Vl1;S33G0S2eS11S11Vp;Vn;A4Vl2;A3A3A3").
Hypothesis HCLS : blk_cls p n.
#[local] Abbreviation G := (aa_geom A0).
#[local] Abbreviation T := (ag_thread (aa_geom A0)).
#[local] Abbreviation SB := (ag_spacebeg (aa_geom A0)).
Definition GEO0 := F0A_rebuild.GEO A0 rho0 tp0 md0 n 0 HA0.
Definition BLK0 : ltac2:(tb__ "0|5|
SbS67Vp;S49Vn;A1M0A2SbScS11S5Vp;Z10M1A2Z0M2A3SbS0Z1Vn;A2SbS2S1Vp;G0A2S19S12VA0;A1A1A2SbSbS0Vn;G0A2S2G0S1Vn;Z8M3A2A2A2SbScS11S5G0G3A2G2A3SbS0G3G0A2SbSbS0G1S4bVn;A1M4A2S0G4Z800A2A2SbScS11S5G4G1A2G2A3ScS11S5Vp;G3A2G2A3A2A2A2A2A2A2A2A2A2") := ltac2:(tb__ "0|0|
S68VA0;Vrho0;Vtp0;Vmd0;Vp;Vn;Vl1;Vl2;Z0VHA0;VHLV;VHCLS;Ac").
Definition CZI0 : ltac2:(tb__ "0|10|
SbSdS0S1Vp;S49Vn;A1A2M0S14S12VA0;A1M1A1M2A2S0S1G2Z1000M3A2S3Vp;S4bVn;A1A2M4A2A2SbSdS0G0S1bG1A1M5A2S0S1G5G3A2G4A2A2SbSdS0G0S1cG1A1M6A2S0S1G6G3A2G4A2A2SbSdS0G0S1eG1A1M7A2S0S1G7S50A2G4A2A2SbSdS0G0S1fG1A1M8A2S0S1G8S4eA2G4A2A2SbSdS0G0S1S13G1A1M9S4Z2MaZ25A2A2MbA2S0S1GbG3A2G4A2A2SbS11S11S61S2cS11S11A2S2eS11S11R2R1A4S64S17VA0;A1A1A3SdS0G0R3A2S0S1R3R2A2G4A2A2F_;FL;Fbb;SbS2fS15ScS28S15A1S62S15S18VA0;A1R2A3S2aS15R1A2A3SdS0G0S22R2A1McA2S0S1GcZ20MdA2G4A2A2F_;Fch';Fj;SbS11SbS0Z1R1A2S0R1Z1eA2A2SdS0G0S1S1G9S7R2S4GaGdA2MeA2A2MfS3GeS4GaZ1dA2A2A2A2S0S1GfGeA2G4A2A2F_;Fc';SbSdSbS0S1Z646000G3A2Vp;A2S0G0Z7fff7000A2A2S0S1Z10007fff8000Z10A2Vp;A2A2S2G0S19G1A1A2A2A2A2A2A2A2A2A2A2A2") := ltac2:(tb__ "0|0|
S6aVA0;Vrho0;Vtp0;Vmd0;Vp;Vn;Vl1;Vl2;Z0VHA0;VHLV;VHCLS;Ac").
Definition CZA0 := F0A_rebuild.CZA A0 rho0 tp0 md0 p n l1 l2 0 HA0 HLV HCLS.

Lemma SHZ : ltac2:(tb__ "0|1|
S11SbS0S4aVp;A1M0R1A2S2R1S1G0S6S49Vn;A1Z8A2A2A2A2SbSbS0Z800c0c00R2A2S2R2Z10007fef8000A2A2ScS29S53S12VA0;A1R2A2S2dA3A2F_;Fz;").
Proof.
  intros z Hz. pose proof BLK0 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold blk_geo in B1.
  pose proof GEO0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TG & _).
  pose proof HA0 as (HG & _). pose proof CZI0 as (_ & _ & _ & I4 & _ & _ & _ & _ & _ & I10 & I11). rewrite FS_total_val in I4.
  destruct (proj1 (Z.mod_divide p 8 ltac:(clear; lia)) B10) as [u Hu]. destruct (proj1 (Z.mod_divide (N8 n) 8 ltac:(clear; lia)) B6) as [w Hw].
  assert (Ha : p <= p + 8 * (z - Sh p) < p + N8 n).
  { unfold Sh in Hz |- *. rewrite Hu, Hw in *. rewrite Z.div_mul in * by (clear; lia). clear -Hz. lia. }
  assert (Ea : z = Sh (p + 8 * (z - Sh p))).
  { unfold Sh. rewrite Hu. rewrite Z.div_mul by (clear; lia).
    replace (u * 8 + 8 * (z - (u + SHADOW_OFF))) with ((z - SHADOW_OFF) * 8) by (clear; lia). rewrite Z.div_mul by (clear; lia). clear; lia. }
  split.
  - unfold Sh, SHADOW_OFF in Hz. rewrite Hu, Hw in Hz. rewrite !Z.div_mul in Hz by (clear; lia). clear -Hz Hu Hw I10 I11 TG B7. lia.
  - apply (fs_footb_sh G z (p + 8 * (z - Sh p)) HG); [clear -Ha I10 I11 TG; lia | rewrite FS_total_val; clear -Ha I4 B5 B8; lia | exact Ea].
Qed.
Lemma LZ_cases : ltac2:(tb__ "0|2|
S11S36Vp;Vn;R1A3SdSbS0S3Vp;S4bVn;A1A2R2A2S2R2S1Vp;S49Vn;A1M0A2A2A2SbS0S4aVp;A1M1R2A2S2R2S1G1S6G0Z8A2A2A2A2A2F_;Fz;").
Proof. intros z Hz. pose proof BLK0 as (_ & _ & _ & _ & _ & _ & B7 & B8 & _). unfold LZ0 in Hz. clear -Hz B7 B8. lia. Qed.
Lemma LZF : ltac2:(tb__ "0|0|
S11S36Vp;Vn;R1A3ScS29S53S12VA0;A1R2A2S2dA3F_;Fz;").
Proof. intros z Hz. destruct (LZ_cases z Hz) as [K|K]; [exact (proj1 (proj2 (proj2 (proj2 (CZA0 z K))))) | exact (proj2 (SHZ z K))]. Qed.

Lemma NOUT : ltac2:(tb__ "0|4|
S11S11S11SbS0R3R1A2S2R1R2A2A2SdS0S1Vp;S49Vn;A1A2R4A2S0R3S3Vp;S4bVn;A1A2A2A2SdS0R4Z7fff7000A2S0Z10007fff8000R5A2A2SdS0S1S14S12VA0;A1M0A1M1Z1000M2A2R6A2S0R5G1A2A2SdS0R6S13G0A1M3A2S0S1S1G3S4Z2Z25A2A2G2A2R7A2A2SeS36Vp;Vn;R6A3A1F_;F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hz SP SBD _ _ Hc. destruct (LZ_cases z Hc) as [K|K]; [clear -Hz K SP; lia|]. pose proof (proj1 (SHZ z K)) as X. clear -Hz X SBD. lia.
Qed.
Lemma NIMG : ltac2:(tb__ "0|0|
S11SbS0S4dR1A2S2R1S4cA2A2SeS36Vp;Vn;R2A3A1F_;Fz;").
Proof.
  intros z Hz Hc. destruct (LZ_cases z Hc) as [K|K].
  - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (CZA0 z K)))))))))) Hz).
  - pose proof (proj1 (SHZ z K)) as X. unfold IMG_HI in Hz. clear -Hz X. lia.
Qed.
Lemma NTP : ltac2:(tb__ "0|1|
S11SbS0S14S12VA0;A1A1M0R1A2S2R1S1G0Z1000A2A2A2SeS36Vp;Vn;R2A3A1F_;Fz;").
Proof.
  intros z Hz Hc. destruct (LZ_cases z Hc) as [K|K].
  - exact (proj1 (CZA0 z K) Hz).
  - pose proof (proj1 (SHZ z K)) as X. pose proof GEO0 as (_ & _ & _ & _ & _ & _ & _ & TB & _). clear -Hz X TB. lia.
Qed.
Lemma NMETA : ltac2:(tb__ "0|1|
S11SbS0S1S13S12VA0;A1A1S4Z2Z25A2A2M0R1A2S2R1S1G0Z1000A2A2A2SeS36Vp;Vn;R2A3A1F_;Fz;").
Proof.
  intros z Hz Hc. destruct (LZ_cases z Hc) as [K|K].
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (CZA0 z K)))))) Hz).
  - pose proof (proj1 (SHZ z K)) as X. pose proof GEO0 as (_ & _ & SB1 & _). clear -Hz X SB1. lia.
Qed.
Lemma NFA : ltac2:(tb__ "0|3|
S11S11SbS0Z1R2A2S0R2Z1eA2A2SbS0S1S1S13S12VA0;A1A1S7R3S4Z2M0Z20A2M1A2A2M2S3G1S4G0Z1dA2A2A2R2A2S2R2S1G2G1A2A2A2SeS36Vp;Vn;R3A3A1F_;F_;Fz;Fc';").
Proof.
  intros c' z Hc' Hz Hc. destruct (LZ_cases z Hc) as [K|K].
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (CZA0 z K))))))))) c' Hc' Hz).
  - pose proof (proj1 (SHZ z K)) as X. pose proof GEO0 as (_ & _ & SB1 & _). clear -Hz X SB1 Hc'. lia.
Qed.
Lemma NBAND_U : ltac2:(tb__ "0|0|
S11SbS0Z7fff7000R1A2S2R1Z10007fff8000A2A2SeSbS0Vp;R2A2S2R2S1Vp;Vn;A2A2A2A1F_;Fz;").
Proof.
  intros z Hz Hu. pose proof BLK0 as (_ & _ & _ & _ & B5 & _ & _ & B8 & _).
  assert (K : p - rz n <= z < p + N8 n) by (clear -Hu B5 B8; lia).
  pose proof (CZA0 z K) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (X & _) & _). clear -Hz X. lia.
Qed.

Variables (A : AA) (rho rho' : valuation) (tp : list word) (md : Model).
Hypothesis EG : ltac2:(tb__ "0|0|
ScS1dS12VA;A1S12VA0;A1A3").
Hypothesis ES : ltac2:(tb__ "0|0|
ScS2bS15A1S18VA;A1S18VA0;A1A3").
Hypothesis ED : ltac2:(tb__ "0|0|
ScS21S17VA;A1S17VA0;A1A3").
Hypothesis EL : ltac2:(tb__ "0|0|
ScS2bS2cS11S11A2A1S16VA;A1S16VA0;A1A3").
Hypothesis HA : ltac2:(tb__ "0|0|
S5eVA;Vrho;Vtp;Vmd;A4").
Let v : bview := ltac2:(tb__ "0|0|
S40Vsegs;S3bVrho;A1A2").
Let v' : bview := ltac2:(tb__ "0|0|
S40Vsegs;S3bVrho';A1A2").
Let m : bview := ltac2:(tb__ "0|0|
S45S53S12VA0;A1A1Vv;A2").
Let m' : bview := ltac2:(tb__ "0|0|
S45S53S12VA0;A1A1Vv';A2").

Variable XZ : Z -> Prop.
Hypothesis XZT : ltac2:(tb__ "0|1|
S11VXZ;R1A1SdSbS0S1S14S12VA0;A1A1M0Z50A2R2A2S2R2S1G0Z70A2A2A2SbS0S1G0Za80A2R2A2S2R2S1G0Zc60A2A2A2A2F_;Fz;").
Hypothesis XZD : ltac2:(tb__ "0|1|
S11SdVXZ;R1A1M0SeG0A1A2Fz;").
Definition CH (z : Z) : Prop := ltac2:(tb__ "0|0|
SdS36Vp;Vn;Vz;A3VXZ;Vz;A1A2").
Hypothesis VO : ltac2:(tb__ "0|0|
S11SeS35R1A1A1ScS28S25Q8A1A1Vv';R2A1Vv;R2A1A3F_;Fz;").
Hypothesis PRES : ltac2:(tb__ "0|1|
S11S36Vp;Vn;R1A3SeSbS0Vp;R2A2S2R2S1Vp;Vn;A2A2A2A1SfS25Q8A1M0G0ScS28G0A1Vv';R4A1S2aG0R1A2A3Lb;A2F_;F_;Fz;").
Hypothesis PRESXZ : ltac2:(tb__ "0|1|
S11VXZ;R1A1SfS25Q8A1M0G0ScS28G0A1Vv';R3A1S2aG0R1A2A3Lb;A2F_;Fz;").
Hypothesis BODY : ltac2:(tb__ "0|2|
ScS28S25Q8M0A1M1A1Vv';S3Vp;Z10A2A1S2aG1S26G0Z2A2A2A3S37Vm';Vp;Vn;A3F_;").

Lemma HLin : ltac2:(tb__ "0|0|
S61S2cS11S11A2S2eS11S11Vp;Vn;A4S16VA;A1A3").
Proof. rewrite EL, HLV. apply in_or_app. right. left. reflexivity. Qed.

Lemma CH_dec : ltac2:(tb__ "0|1|
S11SdS35R1A1M0SeG0A1A2Fz;").
Proof. intros z. unfold CH. destruct (LZ0_dec p n z) as [H|H]; [left; left; exact H|]. destruct (XZD z) as [H'|H']; [left; right; exact H' | right; intros [X|X]; tauto]. Qed.
Lemma NXZ_T : ltac2:(tb__ "0|1|
S11SeSbS0S14S12VA0;A1A1M0R1A2S2R1S1G0Z1000A2A2A2A1SeVXZ;R2A1A1F_;Fz;").
Proof. intros z Hz Hx. pose proof (XZT z Hx). lia. Qed.
Lemma NOUTX : ltac2:(tb__ "0|4|
S11S11S11SbS0R3R1A2S2R1R2A2A2SdS0S1Vp;S49Vn;A1A2R4A2S0R3S3Vp;S4bVn;A1A2A2A2SdS0R4Z7fff7000A2S0Z10007fff8000R5A2A2SdS0S1S14S12VA0;A1M0A1M1Z1000M2A2R6A2S0R5G1A2A2SdS0R6S13G0A1M3A2S0S1S1G3S4Z2Z25A2A2G2A2R7A2A2SeS35R6A1A1F_;F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof. intros lo hi z Hz SP SBD ST SS [Hc|Hc]; [exact (NOUT lo hi z Hz SP SBD ST SS Hc) | apply (NXZ_T z); [clear -Hz ST; lia | exact Hc]]. Qed.
Lemma NIMGX : ltac2:(tb__ "0|0|
S11SbS0S4dR1A2S2R1S4cA2A2SeS35R2A1A1F_;Fz;").
Proof.
  intros z Hz [Hc|Hc]; [exact (NIMG z Hz Hc)|]. apply (NXZ_T z); [|exact Hc].
  pose proof GEO0 as (_ & _ & _ & _ & _ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in Hz. clear -Hz TI. lia.
Qed.
Lemma NTPX : ltac2:(tb__ "0|1|
S11SdSbS0S14S12VA0;A1A1M0R1A2S2R1S1G0Z50A2A2A2SdSbS0S1G0Z70A2R1A2S2R1S1G0Za80A2A2A2SbS0S1G0Zc60A2R1A2S2R1S1G0Z1000A2A2A2A2A2SeS35R2A1A1F_;Fz;").
Proof. intros z Hz [Hc|Hc]; [apply (NTP z); [clear -Hz; lia | exact Hc] | pose proof (XZT z Hc) as X; clear -Hz X; lia]. Qed.
Lemma NMETAX : ltac2:(tb__ "0|1|
S11SbS0S1S13S12VA0;A1A1S4Z2Z25A2A2M0R1A2S2R1S1G0Z1000A2A2A2SeS35R2A1A1F_;Fz;").
Proof.
  intros z Hz [Hc|Hc]; [exact (NMETA z Hz Hc)|]. apply (NXZ_T z); [|exact Hc].
  pose proof GEO0 as (_ & _ & _ & _ & _ & _ & ST & _). clear -Hz ST. lia.
Qed.
Lemma NFAX : ltac2:(tb__ "0|3|
S11S11SbS0Z1R2A2S0R2Z1eA2A2SbS0S1S1S13S12VA0;A1A1S7R3S4Z2M0Z20A2M1A2A2M2S3G1S4G0Z1dA2A2A2R2A2S2R2S1G2G1A2A2A2SeS35R3A1A1F_;F_;Fz;Fc';").
Proof.
  intros c' z Hc' Hz [Hc|Hc]; [exact (NFA c' z Hc' Hz Hc)|]. apply (NXZ_T z); [|exact Hc].
  pose proof GEO0 as (_ & _ & _ & _ & _ & _ & ST & _). clear -Hz ST Hc'. lia.
Qed.
Lemma CHF : ltac2:(tb__ "0|0|
S11S35R1A1ScS29S53S12VA0;A1R2A2S2dA3F_;Fz;").
Proof. intros z [Hc|Hc]; [exact (LZF z Hc)|]. pose proof HA0 as (HG & _). apply fs_footb_T; [exact HG | pose proof (XZT z Hc); lia]. Qed.
Lemma AGm : ltac2:(tb__ "0|0|
S11SeS35R1A1A1ScS28S25Q8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").
Proof. intros z Hz. unfold m', m, maskv. rewrite (VO z Hz). reflexivity. Qed.
Lemma CHm : ltac2:(tb__ "0|0|
S11S35R1A1ScS28S25Q8A1A1Vm';R2A1Vv';R2A1A3F_;Fz;").
Proof. intros z Hz. unfold m'. apply maskv_out. exact (CHF z Hz). Qed.
Lemma CELL : ltac2:(tb__ "0|0|
S11S2fS11S2fS65R1R3A2SeS35S1R5SaR2A1A2A1A1F_;Fk;S43Vm;S44R4R3R2A3A2S43Vm';S44R5R4R3A3A2F_;F_;Fx;Fw;Fa;").
Proof. intros a w x Hn Hc. eapply cell_ok_agree; [|exact Hc]. cbn [c_addr c_w]. intros k Hk. apply AGm. exact (Hn k Hk). Qed.
Lemma PRES_AG : ltac2:(tb__ "0|0|
S11S11S11SbS0R3R1A2S2R1R2A2A2SeS35R2A1A1F_;Fz;S41Vm;R3R2A3S41Vm';R4R3A3F_;F_;Fhi;Flo;").
Proof. intros lo hi Hn Hp z Hz. rewrite (AGm z (Hn z Hz)). exact (Hp z Hz). Qed.
Lemma PRES_CH : ltac2:(tb__ "0|1|
S11S35R1A1SeSbS0Vp;R2A2S2R2S1Vp;Vn;A2A2A2A1SfS25Q8A1M0G0ScS28G0A1Vm';R4A1S2aG0R1A2A3Lb;A2F_;F_;Fz;").
Proof. intros z Hc Hu. rewrite (CHm z Hc). destruct Hc as [Hc|Hc]; [exact (PRES z Hc Hu) | exact (PRESXZ z Hc)]. Qed.
Lemma NBAND_UX : ltac2:(tb__ "0|0|
S11SbS0Z7fff7000R1A2S2R1Z10007fff8000A2A2SeVXZ;R2A1A1F_;Fz;").
Proof. intros z Hz Hx. pose proof (XZT z Hx) as X. pose proof GEO0 as (_ & _ & _ & _ & _ & _ & _ & TB & _). clear -Hz X TB. lia. Qed.
Lemma PRES_SH : ltac2:(tb__ "0|0|
S11S11S11SbS0R3R1A2S2R1R2A2A2SbS0Z7fff7000R2A2S2R2Z10007fff8000A2A2F_;Fz;S41Vm;R3R2A3S41Vm';R4R3A3F_;F_;Fhi;Flo;").
Proof.
  intros lo hi Hb Hp z Hz. destruct (CH_dec z) as [Hc|Hn]; [|rewrite (AGm z Hn); exact (Hp z Hz)].
  exact (PRES_CH z Hc (NBAND_U z (Hb z Hz))).
Qed.
Lemma PRESB : ltac2:(tb__ "0|1|
S11S11S54Vm;R2R1S16VA;A1M0A4S54Vm';R3R2G0A4F_;Fhi;Flo;").
Proof.
  intros lo hi Hp z Hz HL. destruct (CH_dec z) as [Hc|Hn]; [|rewrite (AGm z Hn); exact (Hp z Hz HL)].
  apply (PRES_CH z Hc). intros Hu. apply HL. exists p, n. split; [exact HLin | exact Hu].
Qed.

Lemma HAn : ltac2:(tb__ "0|1|
SbS5aS12VA0;A1M0A1SbS47Vv;G0A2SbS57S46S53G0A1Vv;A2VA;A2SbS5fVm;VA;A2SbS5cVsegs;VA;Vtp;Vmd;A4SbS5bVA;A1S59Vv;Vtp;A2A2A2A2A2A2A2").
Proof. pose proof HA as X. unfold AInvQC in X. cbn zeta in X. rewrite EG in X. exact X. Qed.

Lemma HRTC : rtc_inv v' G.
Proof.
  pose proof HAn as (HG & HR & _). unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz. apply VO.
  destruct GEO0 as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & TI & TG & F1 & F2 & FT & FS & FB & C1 & C2 & TC & SC & D1 & D2 & TD & SD).
  pose proof CZI0 as (I1 & I2 & I3 & I4 & I5 & _). rewrite FS_total_val in I4.
  destruct (rtc_foot_cases G z Hz) as [K|[K|[K|[K|K]]]].
  - exact (NIMGX z K).
  - apply NTPX. clear -K. lia.
  - apply (NOUTX (ag_ctx G) (ag_ctx G + 4096) z); [clear -K; lia | exact I2 | exact (proj1 (proj2 (proj2 (geom_bands _ HG)))) | clear -TC; lia | exact SC].
  - apply (NOUTX (ag_dtls G) (ag_dtls G + 4096) z); [clear -K; lia | exact I3 | exact (proj1 (proj2 (proj2 (proj2 (geom_bands _ HG))))) | clear -TD; lia | exact SD].
  - apply (NOUTX (ag_fsb G) (ag_fsb G + 11571200) z); [clear -K; lia | exact I4 | exact FB | clear -FT; lia | exact FS].
Qed.
Lemma HFS : ltac2:(tb__ "0|0|
S57S46S53S12VA0;A1A1Vv';A2VA;A2").
Proof.
  pose proof HAn as (_ & _ & HF & _). rewrite (restrictv_ext (fs_footb G) v v') by (intros z Hz; apply VO; intros Hc; rewrite (CHF z Hc) in Hz; discriminate).
  exact HF.
Qed.
Lemma SH_band : ltac2:(tb__ "0|0|
S11S11S11S0Z0R3A2S0R3Z7fffff800007A2SbS0S4aR5A1R3A2S2R3S4aR4A1A2A2SbS0Z7fff7000R4A2S2R4Z10007fff8000A2A2F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z H0 H1 Hz. unfold Sh, SHADOW_OFF in Hz. pose proof (Z.div_pos lo 8 H0 ltac:(lia)). pose proof (Z.div_le_mono hi 140737479966727 8 ltac:(lia) H1) as X.
  change (140737479966727 / 8) with 17592184995840 in X. lia.
Qed.
Lemma HLB : live_block_reprC m' A.
Proof.
  pose proof HAn as (_ & _ & _ & (Hsep & Hlive & _) & _). intros b sz Hin H2'.
  assert (CASE : (b, sz) = (p, n) \/ In (b, sz) (l1 ++ l2)).
  { rewrite EL, HLV in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[E|Hin]]; [right; apply in_or_app; left; exact Hin | left; symmetry; exact E | right; apply in_or_app; right; exact Hin]. }
  destruct CASE as [E|Hin'].
  - injection E as -> ->. apply BODY. rewrite <- (CHm (p - 16)); [exact H2' | left; left; clear; lia].
  - pose proof (fun z Hz HC => F0A_rebuild.CZ_live A0 rho0 tp0 md0 p n l1 l2 1 HA0 HLV HCLS ltac:(clear; lia) b sz z Hin' Hz HC) as NO0.
    assert (NO : forall z, (b - rz sz <= z < b + sz \/ Sh b <= z < Sh b + (sz + 7) / 8) -> ~ CH z).
    { intros z Hz [Hc|Hc]; [apply (NO0 z Hz); unfold F0A_rebuild.CZ; destruct (LZ_cases z Hc) as [K|K]; [left | right]; exact K|].
      destruct (Hsep b sz Hin) as (L1' & L2' & L3' & _ & _ & _ & _ & L8'). rewrite EG in L3'. pose proof (XZT z Hc) as X.
      destruct Hz as [Hz|Hz].
      - assert (HinA0 : In (b, sz) (aa_live A0)) by (rewrite <- EL; exact Hin). destruct (in_split _ _ HinA0) as (k1 & k2 & Hsplit).
        pose proof (N8_facts sz L1') as (NB1 & _).
        exact (proj1 (F0A_rebuild.CZA A0 rho0 tp0 md0 b sz k1 k2 0 HA0 Hsplit L8' z ltac:(clear -Hz NB1; lia)) ltac:(clear -X; lia)).
      - pose proof GEO0 as (_ & _ & _ & _ & _ & _ & _ & TB & _ & TG' & _).
        assert (SHB : 2147446784 <= z < 17594333495296).
        { apply (SH_band b (b + sz + 7) z); [unfold IMG_HI in L2'; clear -L2'; lia | clear -L3' TG'; lia|]. split; [exact (proj1 Hz)|].
          eapply Z.lt_le_trans; [exact (proj2 Hz)|]. apply RebuildRZ.Sh_add_le; [unfold IMG_HI in L2'; clear -L2'; lia | clear -L1'; lia | clear; lia]. }
        clear -SHB X TB. lia. }
    destruct (Hsep b sz Hin) as (L1 & _). pose proof (rz_bound sz) as RB.
    assert (H2 : m (b - 16) = Some (Z_to_bv 8 2)) by (rewrite <- AGm by (apply NO; left; clear -L1 RB; lia); exact H2').
    destruct (Hlive b sz Hin H2) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
    pose proof (Z.div_le_mono sz (sz + 7) 8 ltac:(lia) ltac:(lia)) as DL. pose proof (Z.div_pos sz 8 ltac:(lia) ltac:(lia)) as D0.
    split; [exact H2'|].
    split; [apply CELL; [intros k Hk; apply NO; left; lia | exact B2]|].
    split; [apply CELL; [intros k Hk; apply NO; left; lia | exact B3]|].
    split; [split|split].
    + intros g Hg. rewrite AGm by (apply NO; right; lia). exact (B4 g Hg).
    + intros Hm. rewrite AGm; [exact (B5 Hm)|]. apply NO. right.
      replace ((sz + 7) / 8) with (sz / 8 + 1) by (apply Z.div_unique with (sz mod 8 - 1); [pose proof (Z.mod_pos_bound sz 8); lia | pose proof (Z.div_mod sz 8); lia]). lia.
    + apply (alloc_magic_ok_agree m m' b sz); [|lia|exact B6]. intros z Hz. apply AGm. apply NO. left. lia.
    + destruct B7 as (tb & Ht' & Hm4). exists tb. split; [|exact Hm4]. rewrite AGm by (apply NO; left; lia). exact Ht'.
Qed.
Lemma HPR : primary_repr m' A.
Proof.
  pose proof HAn as (HG & _ & _ & (_ & _ & (PL & P0 & P31 & PC) & _) & _). unfold primary_repr. rewrite EG.
  split; [exact PL|]. split; [exact P0|]. split; [exact P31|]. intros c Hc. pose proof (PC c Hc) as PCc. rewrite EG in PCc.
  pose proof PCc as PCd. unfold class_repr in PCd.
  destruct PCd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _ & _ & N6 & _ & _ & _ & PU & PS & _).
  destruct GEO0 as (_ & _ & SB1 & SB2 & _ & _ & _ & _ & _ & TG & _).
  apply (class_repr_agree_pres m m' G A c _ Hc); [| | | exact PCc].
  - intros z [Hz|[Hz|Hz]]; apply AGm.
    + apply NMETAX. unfold region_info, kRegionInfoStride in Hz. rewrite kSpaceSize_val in Hz. clear -Hz Hc. lia.
    + apply (NFAX c z Hc). unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in *. clear -Hz N6. lia.
    + apply NTPX. clear -Hz Hc. lia.
  - apply PRESB. exact PU.
  - apply PRES_SH; [|exact PS]. intros z Hz. apply (SH_band _ _ z) in Hz; [exact Hz | |];
      unfold region_beg, kUserSpaceSize, kUserMapSize, kFreeArraySize, kRegionSize in *; clear -N2 N3 SB1 SB2 TG Hc; lia.
Qed.

Lemma HSR : secondary_repr m' A.
Proof.
  pose proof HAn as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & Hsec & _).
  unfold secondary_repr in Hsec |- *. rewrite EG, ES in Hsec |- *.
  destruct Hsec as (S1 & SP & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  assert (CI : forall cc, IMG_LO <= c_addr cc -> c_addr cc + Z.of_nat (c_w cc) <= IMG_HI -> cell_ok m cc -> cell_ok m' cc).
  { intros cc H1 H2. apply cell_ok_agree. intros k Hk. apply AGm. apply NIMGX. lia. }
  destruct GEO0 as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & TI & TG & _). pose proof CZI0 as (_ & _ & _ & _ & I5' & _ & _ & I8' & _).
  pose proof HA0 as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & SEC3 & _). destruct (F0A_rebuild.SG3_pab A0 rho0 tp0 md0 HA0) as [PAB3 PABT3].
  pose proof S45 as [S4m (S4a & _ & S4t & _ & S4b)]. unfold kPtrArrayReserve in *.
  unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in S4b.
  assert (NPAB : forall z, ag_pab G <= z < ag_pab G + 2 ^ 23 -> ~ CH z).
  { intros z Hz. apply (NOUTX (ag_pab G) (ag_pab G + 2 ^ 23) z Hz); [exact I5' | exact S4b | clear -PABT3; lia | exact PAB3]. }
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as MB. pose proof D10 as (D10a & _ & _ & _ & WB).
    destruct (SEC3 i ch Hi) as (X1 & X2 & _). rewrite kSpaceSize_val in X1.
    assert (NH : forall z, sc_map_beg ch <= z < sc_map_beg ch + 32 -> ~ CH z).
    { intros z Hz. apply (NOUTX (sc_map_beg ch) (sc_map_beg ch + 32) z Hz (I8' i ch Hi));
        unfold PG, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; clear -WB X1 X2 D8 D9 MB; lia. }
    assert (CA : forall off w x, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok m (mkACell (sc_map_beg ch + off) w x) -> cell_ok m' (mkACell (sc_map_beg ch + off) w x)).
    { intros off w x Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply AGm. apply NH. clear -Ho Hw Hk. lia. }
    split; [apply CA; [lia| cbn; lia | exact C1]|]. split; [apply CA; [lia| cbn; lia | exact C2]|].
    split; [apply CA; [lia| cbn; lia | exact C3]|]. split; [apply CA; [lia| cbn; lia | exact C4]|].
    split.
    { eapply cell_ok_agree; [|exact C5]. cbn [c_addr c_w]. intros k Hk. apply AGm. pose proof (nth_error_Some_lt _ _ _ Hi) as L.
      apply NPAB. clear -Hk L S2. lia. }
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [apply PRESB; exact D13 |].
    apply PRES_SH; [|exact D14]. intros z Hz. apply (SH_band _ _ z) in Hz; [exact Hz | unfold IMG_HI in MB; clear -MB; lia | clear -D12 TG; lia]. }
  split; [apply PRES_AG; [|exact SP]; intros z Hz; apply NPAB; clear -Hz S2; lia|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S45|].
  unfold SEC_INST, IMG_LO, IMG_HI in *.
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I1]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I2]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I3]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I4]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I5]|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I6]|].
  split; [apply PRES_AG; [|exact I7]; intros z Hz; apply NIMGX; unfold IMG_LO, IMG_HI; clear -Hz; lia|].
  split; [apply CI; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact I8]|].
  apply PRES_AG; [|exact I9]. intros z Hz. apply NIMGX. unfold IMG_LO, IMG_HI. clear -Hz. lia.
Qed.

Lemma HIA : ia_inv m' A.
Proof.
  pose proof HAn as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & _ & Hia & _).
  refine (ia_inv_agree m m' A A eq_refl _ Hia). intros z Hz. apply AGm. exact (NIMGX z Hz).
Qed.
Lemma HTI : thread_inv m' G.
Proof.
  pose proof HAn as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & _ & _ & HTH & _). rewrite EG in HTH. destruct HTH as [TH1 TH2]. split.
  - rewrite AGm; [exact TH1|]. apply NTPX. clear. lia.
  - intros z Hz. destruct (CH_dec z) as [Hc|Hn]; [|rewrite (AGm z Hn); exact (TH2 z Hz)].
    apply (PRES_CH z Hc). intros Hu. destruct Hc as [Hc|Hc]; [exact (NTP z ltac:(clear -Hz; lia) Hc)|].
    pose proof BLK0 as (_ & _ & _ & _ & B5 & _ & _ & B8 & _). assert (K : p - rz n <= z < p + N8 n) by (clear -Hu B5 B8; lia). exact (proj1 (CZA0 z K) ltac:(clear -Hz; lia)).
Qed.
Lemma HMI : misc_inv m'.
Proof.
  pose proof HAn as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & _ & _ & _ & Hmisc).
  refine (misc_inv_agree m m' _ Hmisc). intros z Hz. apply AGm. exact (NIMGX z Hz).
Qed.
Lemma HDEP : depot_wf m' A.
Proof.
  pose proof HAn as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & _ & Hdep & _).
  pose proof HA0 as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & _ & _ & DEP3 & _).
  unfold depot_wf in Hdep |- *. rewrite ED in Hdep |- *. eapply depot_mem_frame; [|exact Hdep]. intros a Ha. apply AGm.
  destruct GEO0 as (T1 & T2 & SB1 & SB2 & SB8 & _ & ST & TB & TI & TG & _). pose proof CZI0 as (_ & _ & _ & _ & _ & _ & I7 & _).
  assert (BLK' : forall bb L, In (bb, L) (dblocks (aa_depot A0)) -> bb <= a < bb + L -> ~ CH a).
  { intros bb L Hbb Hab. destruct (DEP3 (bb, L) Hbb) as (DI & DT & _ & _ & _ & SS & _). unfold sepZ in DT, SS. cbn [fst snd] in DI, DT, SS.
    destruct DI as (_ & _ & _ & _ & WB). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB. rewrite kSpaceSize_val in SS.
    exact (NOUTX bb (bb + L) a Hab (I7 bb L Hbb) WB ltac:(clear -DT; lia) ltac:(clear -SS; lia)). }
  destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
  - apply NIMGX. unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. unfold IMG_LO, IMG_HI. clear -Hs. lia.
  - apply (BLK' bb NBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
  - apply (BLK' bb FBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
Qed.
Lemma HBTP : bandtp_inv v' tp.
Proof.
  pose proof HAn as (_ & _ & _ & _ & _ & _ & HB). eapply bandtp_mono; [|exact HB]. intros z Hz Hd.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Hz.
  destruct (CH_dec z) as [Hc|Hn]; [|rewrite (VO z Hn); exact Hd].
  destruct Hc as [Hc|Hc]; [|exfalso; exact (NBAND_UX z Hz Hc)].
  destruct (PRES z Hc (NBAND_U z Hz)) as [b Hb]. rewrite Hb. discriminate.
Qed.

Theorem limbo_in : ltac2:(tb__ "0|0|
S5eVA;Vrho';Vtp;Vmd;A4").
Proof.
  pose proof HAn as (HG & _ & _ & (R1 & _ & _ & _ & (R5 & R5m) & _) & HM & HI3 & _).
  unfold AInvQC. cbn zeta. rewrite EG. fold segs. fold v'. fold m'.
  split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|]. split; [|exact (conj HM (conj HI3 HBTP))].
  split; [exact R1|]. split; [exact HLB|]. split; [exact HPR|]. split; [exact HSR|].
  split; [split; [exact R5|]; apply CELL; [|exact R5m]; intros k Hk; apply NIMGX; unfold QG, IMG_LO, IMG_HI; cbn in Hk; clear -Hk; lia|].
  split; [exact HDEP|]. split; [exact HIA|]. split; [rewrite EG; exact HTI | exact HMI].
Qed.
End LIMBO.

Theorem AInvQC_frame_top : ltac2:(tb__ "0|0|
S1aS3cS3cS2bS25Q40A1A1S60S5eR5R4R2R1A4S11S2R1S19S12R7A1A1A2ScS28S25Q8A1A1S40S63S3bR6A1R2A3S40S63S3bR7A1R2A3A3F_;Fz;S5eR7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp md HX AV. unfold AInvQC in HX |- *. cbn zeta in HX |- *.
  set (G := aa_geom A) in *. set (m := view InvLaws.segsA (rm rho)) in *. set (m' := view InvLaws.segsA (rm rho')) in *.
  destruct HX as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (R1 & R2 & R3 & R4 & (R5 & R5m) & R6 & R7 & R8 & R9).
  pose proof (geom_old _ HG) as (_ & F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & _ & S1 & S2 & _). fold G in F1, F2, T1, T2, C1, C2, D1, D2, S1, S2.
  pose proof (topG_range G) as TG.
  assert (HPAB : dyn_ok (topG G) (ag_pab G) kPtrArrayReserve) by (destruct R4 as (_ & _ & _ & _ & S4 & _); exact S4).
  set (mk := maskv (fs_footb G) m) in *. set (mk' := maskv (fs_footb G) m').
  assert (MK : forall z, m' z = m z -> mk' z = mk z) by (intros z E; unfold mk, mk', maskv; rewrite E; reflexivity).
  assert (Zimg : forall z, IMG_LO <= z < IMG_HI -> ~ dstatw z -> m' z = m z) by (intros z Hz _; apply AV; unfold IMG_HI in Hz; clear -Hz TG; lia).
  assert (Zimg' : forall z, IMG_LO <= z < IMG_HI -> m' z = m z) by (intros z Hz; apply AV; unfold IMG_HI in Hz; clear -Hz TG; lia).
  assert (Zsp : forall z, ag_spacebeg G <= z < ag_spacebeg G + kSpaceSize + 4096 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz S2; lia).
  assert (Zth : forall z, ag_thread G <= z < ag_thread G + 0x1000 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz T2; lia).
  assert (Zctx : forall z, ag_ctx G <= z < ag_ctx G + 0x1000 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz C2; lia).
  assert (Zdtls : forall z, ag_dtls G <= z < ag_dtls G + 0x1000 -> m' z = m z) by (intros z Hz; apply AV; clear -Hz D2; lia).
  assert (Zfs : forall z, ag_fsb G <= z < ag_fsb G + FS_total -> m' z = m z) by (intros z Hz; apply AV; clear -Hz F2; lia).
  assert (Zpab : forall z, ag_pab G <= z < ag_pab G + kPtrArrayReserve -> m' z = m z).
  { intros z Hz. apply AV. destruct HPAB as [_ (_ & _ & P3 & _)]. clear -Hz P3. lia. }
  assert (Zsec : forall ch z, In ch (aa_sec A) -> sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch -> m' z = m z).
  { intros ch z Hch Hz. apply AV. destruct (In_nth_error _ _ Hch) as [i Hi]. destruct R4 as [S1' _].
    destruct (S1' i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D12 & _). fold G in D12. clear -Hz D12. lia. }
  assert (Zband : forall z, SHADOW_BAND_LO <= z < SHADOW_BAND_HI -> m' z = m z).
  { intros z Hz. apply AV. unfold SHADOW_BAND_HI, HIGH_SHADOW_END in Hz. clear -Hz TG. lia. }
  split; [exact HG|].
  split.
  { eapply (rtc_inv_z G m m'); first [ eassumption | intros; first [ apply Zimg; assumption | apply Zth; assumption | apply Zctx; assumption | apply Zdtls; assumption | apply Zfs; assumption ] ]. }
  split.
  { replace (restrictv (fs_footb G) m') with (restrictv (fs_footb G) m); [exact HF|].
    apply functional_extensionality. intros z. unfold restrictv. destruct (fs_footb G z) eqn:E; [|reflexivity].
    symmetry. apply AV. unfold fs_footb in E. cbn zeta in E.
    pose proof (SpineMallocS4.Sh_lt_HSE (ag_fsb G + FS_total) ltac:(clear -F2 TG; lia)) as SL. unfold HIGH_SHADOW_END in SL.
    apply orb_prop in E as [E|E]; [apply orb_prop in E as [E|E]|]; apply andb_prop in E as [_ E]; apply Z.ltb_lt in E; rewrite ?FS_total_val in *; clear -E F2 SL TG; lia. }
  split; [|split; [exact HM | split; [exact HI3 | eapply bandtp_agree; [exact Zband | exact HB]]]].
  split; [exact R1|].
  Ltac zargQC MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband :=
    first [ eassumption | reflexivity
          | intros; apply MK; first [ apply Zsp; assumption | apply Zth; assumption | apply Zctx; assumption | apply Zdtls; assumption
                                    | apply Zfs; assumption | apply Zpab; assumption | apply Zband; assumption
                                    | eapply Zsec; eassumption | apply Zimg; assumption ] ].
  split.
  {
    intros b n Hin H2'. destruct (R1 b n Hin) as (S1' & S2' & S3' & _). pose proof (rz_bound n) as RZ. pose proof HI3 as (_ & LIV3 & _).
    assert (CZ : (forall z, b - rz n <= z < b -> mk' z = mk z) /\ b + n + 7 < 2 ^ 47).
    { apply (chunk_zone G (aa_sec A) mk mk' (fun z Hz => MK z (Zsp z Hz)) (fun ch z Hch Hz => MK z (Zsec ch z Hch Hz)) HG A b n eq_refl eq_refl R3 R4 ltac:(unfold IMG_HI in *; clear -S2'; lia) ltac:(clear -S1'; lia)).
      - intros EP. destruct R3 as (_ & _ & _ & P4). fold G in P4.
        pose proof (primary_cls n ltac:(clear -S1'; lia) EP) as Hc. pose proof (P4 _ Hc) as X. cbn zeta.
        destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
        exact (LV b n Hin EP eq_refl).
      - intros EP. destruct (LIV3 b n Hin) as [X|X]; [rewrite EP in X; discriminate X | exact X]. }
    destruct CZ as [BEL UB].
    assert (H2 : mk (b - 16) = Some (Z_to_bv 8 2)) by (rewrite <- BEL by (clear -RZ; lia); exact H2').
    destruct (R2 b n Hin H2) as (L1 & L2 & L3 & L4 & L5 & L6).
    split; [exact H2'|].
    split; [eapply (cell_ok_agree mk mk'); [cbn [c_addr c_w]; intros k Hk; apply BEL; clear -Hk RZ; lia | exact L2]|].
    split; [eapply (cell_ok_agree mk mk'); [cbn [c_addr c_w]; intros k Hk; apply BEL; clear -Hk RZ; lia | exact L3]|].
    split.
    - destruct L4 as [L4a L4b]. unfold IMG_HI in *. pose proof (div8_superadd b (n + 7) ltac:(clear -S2'; lia) ltac:(clear -S1'; lia)) as D8.
      pose proof (Z.div_pos n 8 ltac:(clear -S1'; lia) ltac:(clear; lia)). pose proof (Z.div_le_mono n (n + 7) 8 ltac:(clear; lia) ltac:(clear; lia)).
      split.
      + intros g Hg. rewrite (AGsh mk mk' (fun z Hz => MK z (Zband z Hz)) b (b + n + 7)); [exact (L4a g Hg) | clear -S2'; lia | exact UB | unfold Sh in *; rewrite <- Z.add_assoc; clear -Hg D8 H H0; lia].
      + intros Hn. rewrite (AGsh mk mk' (fun z Hz => MK z (Zband z Hz)) b (b + n + 7)); [exact (L4b Hn) | clear -S2'; lia | exact UB | unfold Sh in *; rewrite <- Z.add_assoc; clear -D8 H H0; lia].
    - split; [eapply alloc_magic_ok_z; [exact BEL | exact L5]|].
      destruct L6 as (t & Ht & Hm4). exists t. split; [rewrite BEL by (clear -RZ; lia); exact Ht | exact Hm4]. }
  split; [eapply (primary_repr_z G mk mk'); zargQC MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (secondary_repr_z G (aa_sec A) mk mk'); zargQC MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split.
  { split; [exact R5|]. eapply cell_ok_agree; [|exact R5m]. cbn [c_addr c_w]. intros k Hk. apply MK. apply Zimg'. unfold QG, IMG_LO, IMG_HI. clear -Hk. lia. }
  split.
  { pose proof HI3 as (_ & _ & _ & _ & DEP3 & _). unfold depot_wf in *. eapply depot_mem_frame; [|exact R6]. intros a Ha. apply MK.
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - apply Zimg'. exact (dstat_img a Hs).
    - apply AV. destruct (DEP3 (bb, NBSZ)) as ((_ & _ & W3 & _) & _); [unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb]|].
      cbn [fst snd] in W3. fold G in W3. clear -Hab W3. lia.
    - apply AV. destruct (DEP3 (bb, FBSZ)) as ((_ & _ & W3 & _) & _); [unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb]|].
      cbn [fst snd] in W3. fold G in W3. clear -Hab W3. lia. }
  split; [eapply (ia_inv_z mk mk'); zargQC MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  split; [eapply (thread_inv_z G mk mk'); zargQC MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband|].
  eapply (misc_inv_z mk mk'); zargQC MK Zimg Zsp Zth Zctx Zdtls Zfs Zpab Zsec Zband.
Qed.

Definition LZ0b (p n z : Z) : bool := ltac2:(tb__ "0|3|
S34S34S30S8S3Vp;Z10A2Vz;A2S9Vz;S3Vp;Z8M0A2A2A2S30S8Vp;Vz;A2S9Vz;S1Vp;S49Vn;A1M1A2A2A2A2S30S8S4aVp;A1M2Vz;A2S9Vz;S1G2S6G1G0A2A2A2A2A2").
Lemma LZ0b_spec : ltac2:(tb__ "0|0|
S11S11S11S10ScS29S38R3R2R1A3S31A3S36R3R2R1A3A2Fz;Fn;Fp;").
Proof. intros p n z. unfold LZ0b, LZ0. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt. tauto. Qed.
Definition rho_mid (zb : Z -> bool) (rho rho' : valuation) : valuation := ltac2:(tb__ "0|1|
S3dS3fVrho;A1S3eVrho;A1S25Q40M0A1S29S28S25Q8A1A1L_;Vzb;S27G0R1A2A1S3bVrho';R1A2S3bVrho;R1A2X29x2La;A3").
Lemma view_mid : ltac2:(tb__ "0|1|
S11S29F_;S3cS3cS11ScS28S25Q8A1A1M0S40S48S3bS3aR4R3R2A3A1R1A3S29G0L_;R4R1A1S40S48S3bR2A1R1A3S40S48S3bR3A1R1A3X29x2A3Fz;Frho';Frho;Fzb;").
Proof.
  intros zb rho rho' z. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
  - rewrite !view_in by lia. unfold rd_of, rho_mid. cbn [rm]. rewrite u64_lit by lia. destruct (zb z); reflexivity.
  - rewrite !view_out by lia. destruct (zb z); reflexivity.
  - rewrite !view_out by lia. destruct (zb z); reflexivity.
Qed.

Lemma lb_body_agree : ltac2:(tb__ "0|1|
S42S42S1aS11S11S0Z1R1A2S11SdSbS0S3R4S4bR3A1A2R1A2S2R1S1R4R3A2A2A2SbS0S4aR4A1M0R1A2S2R1S1G0S6S1R3Z7A2Z8A2A2A2A2A2ScS28S25Q8A1A1R7R2A1R8R2A1A3F_;Fz;S37R7R4R3A3S37R7R5R4A3F_;F_;F_;Fn;Fb;FA;Fmb;Fma;").
Proof.
  intros ma mb A b n Hn AG HB.
  set (A1 := mkAA (aa_geom A) (aa_cls A) (aa_cache_inited A) (aa_sec A) (aa_ptr_committed A) [(b, n)]
                  (aa_q_thread A) (aa_q_global A) (aa_depot A) (aa_fs_hint A) (aa_fs_busy A) (aa_internal_inited A) (aa_V A) (aa_Km A) (aa_Kf A)).
  assert (L1 : live_block_repr ma A1) by (intros b0 n0 [E|[]]; injection E as <- <-; exact HB).
  assert (L1' : live_block_repr mb A1).
  { apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP.live_block_repr_agree ma mb A1 A1 eq_refl); [| |exact L1].
    - intros b0 n0 z [E|[]] Hz. injection E as <- <-. exact (AG z Hz).
    - intros b0 n0 [E|[]]. injection E as <- <-. exact Hn. }
  exact (L1' b n (or_introl eq_refl)).
Qed.

Theorem AInvQC_limbo_top : ltac2:(tb__ "0|c|
S1aS3cS2bS25Q40A1A1M0S60S11S11S2bS2cS11S11A2M1A1M2G2S1aS3cS3cG0S60S11S29F_;S55S48ReRdRcRbA5ScG2S16RfA1S32G1R9S33G1S2eS11S11RbRaA4R8A3A3A3S66RcRbA2ScS1dS12R9A1S12R11A1A3ScS2bS15A1S18RaA1S18R12A1A3ScS21S17RbA1S17R13A1A3ScG2S16RcA1S16R14A1A3S5eRdRcRaR9A4S11ScS29RaR1A1S31A3SdSbS0S1S14S12R18A1M3A1M4Z50A2R2A2S2R2S1G4Z70A2A2A2SbS0S1G4Za80A2R2A2S2R2S1G4Zc60A2A2A2A2F_;Fz;S11S2R1S19G3A1A2SeS36R15R14R2A3A1ScS29RdR3A1S2dA3ScS28S25Q8M5A1M6A1M7S40S48S3bR11A1M8R4A3S40S48S3bR12A1M9R4A3MaA3F_;F_;F_;Fz;S11S36R15R14R1A3SeSbS0R16R2A2S2R2S1R16R15A2A2A2A1SfG6G6ScG7GaS2aG6R1A2MbA3Lb;A2F_;F_;Fz;S11ScS29RdR1A1S31A3SfG6G6ScG7S40S48G9R3A3GbA3Lb;A2F_;Fz;ScG7S40S48S3bR10A1S3R16Z10A2A3S2aG6S26G5Z2A2A2A3S37S45S53S12R1bA1A1S40S48G8A2A2R17R16A3F_;S5eR13R11R10RfA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fxzb;Fmd;Ftp;Frho';Frho;FA;Fl2;Fl1;Fn;Fp;Fmd0;Ftp0;Frho0;FA0;").
Proof.
  intros A0 rho0 tp0 md0 p n l1 l2 A rho rho' tp md xzb HA0 HLV HCLS EG ES ED EL HA XZT VO PRES PRESXZ BODY.
  set (zb := fun z => LZ0b p n z || xzb z). set (rmid := rho_mid zb rho rho').
  assert (VM : forall z, view segsA (rm rmid) z = if zb z then view segsA (rm rho') z else view segsA (rm rho) z) by (intros z; apply view_mid).
  assert (ZB : forall z, zb z = true <-> (LZ0 p n z \/ xzb z = true)).
  { intros z. unfold zb. rewrite orb_true_iff, LZ0b_spec. tauto. }
  assert (VMin : forall z, (LZ0 p n z \/ xzb z = true) -> view segsA (rm rmid) z = view segsA (rm rho') z).
  { intros z Hz. rewrite VM. rewrite (proj2 (ZB z) Hz). reflexivity. }
  assert (VMout : forall z, ~ (LZ0 p n z \/ xzb z = true) -> view segsA (rm rmid) z = view segsA (rm rho) z).
  { intros z Hz. rewrite VM. destruct (zb z) eqn:E; [exfalso; exact (Hz (proj1 (ZB z) E)) | reflexivity]. }
  pose proof (F0A_rebuild.BLK A0 rho0 tp0 md0 p n l1 l2 0 HA0 HLV HCLS) as (_ & _ & B3 & B4 & B5 & B6 & _).
  pose proof (F0A_rebuild.GEO A0 rho0 tp0 md0 n 0 HA0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TG & _).
  assert (VMall : forall z, z < topG (aa_geom A0) -> view segsA (rm rmid) z = view segsA (rm rho') z).
  { intros z Hz. destruct (LZ0_dec p n z) as [Hc|Hn]; [exact (VMin z (or_introl Hc))|]. destruct (xzb z) eqn:EX; [exact (VMin z (or_intror EX))|].
    rewrite (VMout z ltac:(intros [X|X]; [exact (Hn X) | rewrite EX in X; discriminate X])). symmetry. exact (VO z Hz Hn EX). }
  assert (HMID : AInvQC A rmid tp md).
  { assert (XZD : forall z, xzb z = true \/ ~ xzb z = true) by (intros z; destruct (xzb z); [left; reflexivity | right; discriminate]).
    apply (limbo_in A0 rho0 tp0 md0 p n l1 l2 HA0 HLV HCLS A rho rmid tp md EG ES ED EL HA (fun z => xzb z = true) XZT XZD VMout).
    - intros z Hz Hu. rewrite (VMin z (or_introl Hz)). exact (PRES z Hz Hu).
    - intros z Hz. rewrite (VMin z (or_intror Hz)). exact (PRESXZ z Hz).
    - intros H2. rewrite (VMin (p - 16) ltac:(left; left; clear; lia)) in H2.
      apply (lb_body_agree (maskv (fs_footb (aa_geom A0)) (view segsA (rm rho'))) _ A p n B3); [|exact (BODY H2)].
      intros z Hz. unfold maskv. rewrite VMall; [reflexivity|].
      destruct Hz as [Hz|Hz]; [clear -Hz B4 B5; lia|].
      assert (E8 : (n + 7) / 8 = N8 n / 8) by (unfold N8; rewrite Z.div_mul by (clear; lia); reflexivity).
      rewrite E8 in Hz. pose proof (proj1 (SHZ A0 rho0 tp0 md0 p n l1 l2 HA0 HLV HCLS z Hz)) as X. clear -X TG. lia. }
  apply (AInvQC_frame_top A rmid rho' tp md HMID). intros z Hz. rewrite EG in Hz. symmetry. exact (VMall z Hz).
Qed.
End F0A_limbo.

(* [comment removed for export] *)
Module SpineCallocS6i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "option"; "pair"; "Some"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "C5m1"; "C5m2"; "E5m1"; "E5m2"; "C5d"; "C5e"; "E5j"; "C6"; "F_gen"; "BR"; "C5c"; "LLe"; "LRe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "memset_entryA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "ss_facts"; "ss_next"; "sv"; "sobj"; "sprop_below"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.SpineCallocS6i.INST"; "s51_0"; "s52_0"; "R51_0"; "R52_0"; "T51_0"; "T52_0"; "s6j_0"; "sd51_0"; "sd52_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6"; "a0e2"; "len1e"; "len2e"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSP.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Lemma Cert5c_0 : ltac2:(tb__ "0|1|
S5S6S3eS20Ufa0S8S28Zde378S9S28A1A3S1fS8S1S19VW;Vst;Vtmax;A3S9S1A1M0A3S8S1S11VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma G5m1_0 : ltac2:(tb__ "0|0|
S3dS21S17S22S0S11VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W5m1_0 : ltac2:(tb__ "0|0|
S5S6S27S0SfVW;Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D5m1_0 : ltac2:(tb__ "0|4|
S5SbSeSaSeS24S24A2M0A1M1SaS21A1M2A2M3A1S40S0S11VW;Vst;Vtmax;A3A1S0SfVW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS24S24S43S1aA4S9G0A1A3S9S21A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX5m1_0 : ltac2:(tb__ "0|0|
S5S29S23S0SfVW;Vst;Vtmax;A3A1A1S23S0S11VW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
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
Proof. unfold s51_0, R51_0. cbv beta zeta delta [W st tmax R51_0 s51_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Hchk51_0 : ltac2:(tb__ "0|0|
S5S6S3aSfVW;Vst;Vtmax;A3S1cS2dS2fS3fS4S1S3S1eA4A5S7A3").
Proof. unfold s51_0, R51_0. cbv beta zeta delta [W st tmax R51_0 s51_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma HT51_0 : ltac2:(tb__ "0|0|
S5S1S39S2dS1cS36S3bS1dA1A1SfVW;Vst;Vtmax;A3S2fA5S31A3").
Proof. reflexivity. Qed.
Lemma FBC51_0 : ltac2:(tb__ "0|1|
S5S6S3cS21S26S23S0SfVW;Vst;Vtmax;A3A1M0A1A1S22G0A1A3S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma FBT51_0 : ltac2:(tb__ "0|0|
S5S6S3cS21S26S23S0S31A1A1A1S22S0SfVW;Vst;Vtmax;A3A1A1A3S7A3").
Proof. unfold T51_0. cbv beta zeta delta [W st tmax R51_0 T51_0 s51_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENT51_0 : ltac2:(tb__ "0|0|
S5S6S2S37S31S22S0SfVW;Vst;Vtmax;A3A1A1A2S13VW;Vst;Vtmax;A3S34A3S7A3").
Proof. unfold T51_0, sd51_0. cbv beta zeta delta [W st tmax R51_0 T51_0 s51_0 sd51_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID51_0 : ltac2:(tb__ "0|0|
S5S6S2cS34S1fA2S7A3").
Proof. unfold sd51_0. cbv beta zeta delta [W st tmax R51_0 T51_0 s51_0 sd51_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NXC51_0 : ltac2:(tb__ "0|0|
S41S1fS23S0SfVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert5d_0 : ltac2:(tb__ "0|1|
S5S6S3eS20Ufa0S8S28Zde378S9S28A1A3S1fS8S1S13VW;Vst;Vtmax;A3S9S1A1M0A3S8S1S12VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma G5m2_0 : ltac2:(tb__ "0|0|
S3dS21S17S22S0S12VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W5m2_0 : ltac2:(tb__ "0|0|
S5S6S27S0S10VW;Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D5m2_0 : ltac2:(tb__ "0|4|
S5SbSeSaSeS24S24A2M0A1M1SaS21A1M2A2M3A1S40S0S12VW;Vst;Vtmax;A3A1S0S10VW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS24S24S42S18A4S8G0ScS24S24S44S1bA4S9G0A1A3A3S9S21A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX5m2_0 : ltac2:(tb__ "0|0|
S5S29S23S0S10VW;Vst;Vtmax;A3A1A1S23S0S12VW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
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
Proof. unfold s52_0, R52_0. cbv beta zeta delta [W st tmax R52_0 s52_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Hchk52_0 : ltac2:(tb__ "0|0|
S5S6S3aS10VW;Vst;Vtmax;A3S1cS2eS30S3fS4S1S3S1eA4A5S7A3").
Proof. unfold s52_0, R52_0. cbv beta zeta delta [W st tmax R52_0 s52_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma HT52_0 : ltac2:(tb__ "0|0|
S5S1S39S2eS1cS36S3bS1dA1A1S10VW;Vst;Vtmax;A3S30A5S32A3").
Proof. reflexivity. Qed.
Lemma FBC52_0 : ltac2:(tb__ "0|1|
S5S6S3cS21S26S23S0S10VW;Vst;Vtmax;A3A1M0A1A1S22G0A1A3S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma FBT52_0 : ltac2:(tb__ "0|0|
S5S6S3cS21S26S23S0S32A1A1A1S22S0S10VW;Vst;Vtmax;A3A1A1A3S7A3").
Proof. unfold T52_0. cbv beta zeta delta [W st tmax R52_0 T52_0 s52_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENT52_0 : ltac2:(tb__ "0|0|
S5S6S2S37S32S22S0S10VW;Vst;Vtmax;A3A1A1A2S14VW;Vst;Vtmax;A3S35A3S7A3").
Proof. unfold T52_0, sd52_0. cbv beta zeta delta [W st tmax R52_0 T52_0 s52_0 sd52_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID52_0 : ltac2:(tb__ "0|0|
S5S6S2cS35S1fA2S7A3").
Proof. unfold sd52_0. cbv beta zeta delta [W st tmax R52_0 T52_0 s52_0 sd52_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NXC52_0 : ltac2:(tb__ "0|0|
S41S1fS23S0S10VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert5e_0 : ltac2:(tb__ "0|1|
S5S6S3eS20Ufa0S8S28Z3c678S9S28A1A3S1fS8S1S14VW;Vst;Vtmax;A3S9S1A1M0A3S8S1S15VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s6j_0 : ltac2:(tb__ "0|0|
S2b") := ltac2:(tb__ "0|0|
S2aS1fS0S15VW;Vst;Vtmax;A3A1S0S16VW;Vst;Vtmax;A3A1A3").
Lemma ENT6j_0 : ltac2:(tb__ "0|0|
S5S6S2S15VW;Vst;Vtmax;A3S16VW;Vst;Vtmax;A3S33A3S7A3").
Proof. unfold s6j_0. cbv beta zeta delta [W st tmax s6j_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID6j_0 : ltac2:(tb__ "0|0|
S5S6S2cS33S1fA2S7A3").
Proof. unfold s6j_0. cbv beta zeta delta [W st tmax s6j_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
End INST.
End SpineCallocS6i.

(* [comment removed for export] *)
Module SpineCallocS7iW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "option"; "Some"; "prod"; "pair"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "C6m"; "E6s"; "C6l"; "C7"; "E6l"; "O_U"; "C6b"; "E6j"; "E6m"; "C6"; "F_gen"; "LUe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sv"; "ss_objs"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.SpineCallocS7iW1.INST"; "s6_0"; "R6_0"; "T6_0"; "k6_0"; "s7j_0"; "s7s_0"; "sd6_0"; "E6sz_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zobj"; "zero_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@Stdlib.Lists.List"; "forallb"; "incl"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7"; "len3e"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3iW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSPW1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Lemma Cert6_0 : ltac2:(tb__ "0|1|
S6S7S38S27Ufa0S9S28Z5f864S9S28Z3c698SaS28A1A3A3S26S9S1S1bVW;Vst;Vtmax;A3SaS1A1M0A3S9S1S13VW;Vst;Vtmax;A3S9S1S16VW;Vst;Vtmax;A3G0A3A3A6S8A3").
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
S6S7S38S27Ufa0S9S28Zde378SaS28A1A3S26S9S1S14VW;Vst;Vtmax;A3SaS1A1M0A3S9S1S1aVW;Vst;Vtmax;A3G0A3A6S8A3").
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
S6S7S38S27Ufa0S9S28Z3c698SaS28A1A3S26S9S1S18VW;Vst;Vtmax;A3SaS1A1M0A3S9S1S19VW;Vst;Vtmax;A3G0A3A6S8A3").
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

