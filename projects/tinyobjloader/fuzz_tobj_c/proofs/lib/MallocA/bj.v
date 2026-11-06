(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq bf.

(* [comment removed for export] *)
Module SpineCallocS7i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "option"; "Some"; "prod"; "pair"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "C6m"; "E6s"; "C6l"; "C7"; "E6l"; "O_U"; "C6b"; "E6j"; "E6m"; "C6"; "F_gen"; "LUe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sv"; "ss_objs"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS7i.INST"; "s6_0"; "R6_0"; "T6_0"; "k6_0"; "s7j_0"; "s7s_0"; "sd6_0"; "E6sz_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zobj"; "zero_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@Stdlib.Lists.List"; "forallb"; "incl"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7"; "len3e"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
Lemma Cert6_0 : ltac2:(tb__ "0|1|
S6S7S38S27Ufa0S9S28Z5f864S9S28Z3c698SaS28A1A3A3S26S9S1S1bVW;Vst;Vtmax;A3SaS1A1M0A3S9S1S13VW;Vst;Vtmax;A3S9S1S16VW;Vst;Vtmax;A3G0A3A3A6S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition k6_0 : ltac2:(tb__ "0|0|
S11") := ltac2:(tb__ "0|0|
S46S10S1eS23S0S13VW;Vst;Vtmax;A3A1A1A2U3A2").
Lemma NTH6s_0 : ltac2:(tb__ "0|0|
S6ScS1eA1S45S1eS23S0S13VW;Vst;Vtmax;A3A1A1S30A3SdS1eS17A2A3").
Proof. unfold k6_0. cbv beta zeta delta [W st tmax k6_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ZC6s_0 : ltac2:(tb__ "0|0|
S6S7S3fS21S0S13VW;Vst;Vtmax;A3A1A1S17A2S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition E6sz_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|2|
S3S13VW;Vst;Vtmax;A3M0S3cS0G0A1M1S3bS1eS23G1A1S30S3eS17A1A4A2A2").
Definition s7s_0 : ltac2:(tb__ "0|0|
S36") := ltac2:(tb__ "0|0|
S35S26S0S34A1S0S15VW;Vst;Vtmax;A3A1A3").
Lemma ENT7s_0 : ltac2:(tb__ "0|2|
S6S7S2S3S13VW;Vst;Vtmax;A3M0S3cS0G0A1M1S3bS1eS23G1A1S30S3eS17A1A4A2A2S15VW;Vst;Vtmax;A3S32A3S8A3").
Proof. unfold k6_0, s7s_0. cbv beta zeta delta [W st tmax E6sz_0 k6_0 s7s_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID7s_0 : ltac2:(tb__ "0|0|
S6S7S37S32S26A2S8A3").
Proof. unfold s7s_0. cbv beta zeta delta [W st tmax E6sz_0 k6_0 s7s_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma G6l_0 : ltac2:(tb__ "0|0|
S44S1fS1cS21S0S16VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W6l_0 : ltac2:(tb__ "0|0|
S6S7S25S0S14VW;Vst;Vtmax;A3A1A1S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D6l_0 : ltac2:(tb__ "0|4|
S6ScSeSbSeS22S22A2M0A1M1SbS1fA1M2A2M3A1S3aS0S16VW;Vst;Vtmax;A3A1S0S14VW;Vst;Vtmax;A3A1A2SdG3SfG1G2S9G0SfS22S22S48S1dA4SaG0A1A3SaS1fA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX6l_0 : ltac2:(tb__ "0|0|
S6S29S20S0S14VW;Vst;Vtmax;A3A1A1S20S0S16VW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert6l_0 : ltac2:(tb__ "0|1|
S6S7S38S27Ufa0S9S28Zde378SaS28A1A3S26S9S1S14VW;Vst;Vtmax;A3SaS1A1M0A3S9S1S1aVW;Vst;Vtmax;A3G0A3A6S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W6m_0 : ltac2:(tb__ "0|0|
S6S7S25S0S12VW;Vst;Vtmax;A3A1A1S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D6m_0 : ltac2:(tb__ "0|4|
S6ScSeSbSeS22S22A2M0A1M1SbS1fA1M2A2M3A1S3aS0S1aVW;Vst;Vtmax;A3A1S0S12VW;Vst;Vtmax;A3A1A2SdG3SfG1G2SaG0A1SaS1fA1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX6m_0 : ltac2:(tb__ "0|0|
S6S29S20S0S12VW;Vst;Vtmax;A3A1A1S20S0S1aVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
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
Proof. unfold s6_0, R6_0. cbv beta zeta delta [W st tmax R6_0 s6_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Hchk6_0 : ltac2:(tb__ "0|0|
S6S7S42S12VW;Vst;Vtmax;A3S2aS2dS2eS47S5S1S4S2cA4A5S8A3").
Proof. unfold s6_0, R6_0. cbv beta zeta delta [W st tmax R6_0 s6_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma HT6_0 : ltac2:(tb__ "0|0|
S6S1S41S2dS2aS39S2bA1S12VW;Vst;Vtmax;A3S2eA5S2fA3").
Proof. reflexivity. Qed.
Lemma FBC6_0 : ltac2:(tb__ "0|1|
S6S7S43S1fS24S20S0S12VW;Vst;Vtmax;A3A1M0A1A1S21G0A1A3S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma FBT6_0 : ltac2:(tb__ "0|0|
S6S7S43S1fS24S20S0S2fA1A1A1S21S0S12VW;Vst;Vtmax;A3A1A1A3S8A3").
Proof. unfold T6_0. cbv beta zeta delta [W st tmax R6_0 T6_0 s6_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENT6_0 : ltac2:(tb__ "0|0|
S6S7S2S3dS2fS21S0S12VW;Vst;Vtmax;A3A1A1A2S18VW;Vst;Vtmax;A3S33A3S8A3").
Proof. unfold T6_0, sd6_0. cbv beta zeta delta [W st tmax R6_0 T6_0 s6_0 sd6_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID6_0 : ltac2:(tb__ "0|0|
S6S7S37S33S26A2S8A3").
Proof. unfold sd6_0. cbv beta zeta delta [W st tmax R6_0 T6_0 s6_0 sd6_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NXC6_0 : ltac2:(tb__ "0|0|
S49S26S20S0S12VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert6b_0 : ltac2:(tb__ "0|1|
S6S7S38S27Ufa0S9S28Z3c698SaS28A1A3S26S9S1S18VW;Vst;Vtmax;A3SaS1A1M0A3S9S1S19VW;Vst;Vtmax;A3G0A3A6S8A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s7j_0 : ltac2:(tb__ "0|0|
S36") := ltac2:(tb__ "0|0|
S35S26S0S19VW;Vst;Vtmax;A3A1S0S15VW;Vst;Vtmax;A3A1A3").
Lemma ENT7j_0 : ltac2:(tb__ "0|0|
S6S7S2S19VW;Vst;Vtmax;A3S15VW;Vst;Vtmax;A3S31A3S8A3").
Proof. unfold s7j_0. cbv beta zeta delta [W st tmax s7j_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID7j_0 : ltac2:(tb__ "0|0|
S6S7S37S31S26A2S8A3").
Proof. unfold s7j_0. cbv beta zeta delta [W st tmax s7j_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
End INST.
End SpineCallocS7i.

(* [comment removed for export] *)
Module SpineCallocS6iW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "option"; "pair"; "Some"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "C5m1"; "C5m2"; "E5m1"; "E5m2"; "C5d"; "C5e"; "E5j"; "C6"; "F_gen"; "BR"; "C5c"; "LLe"; "LRe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "memset_entryA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "ss_facts"; "ss_next"; "sv"; "sobj"; "sprop_below"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS6iW1.INST"; "s51_0"; "s52_0"; "R51_0"; "R52_0"; "T51_0"; "T52_0"; "s6j_0"; "sd51_0"; "sd52_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6"; "a0e2"; "len1e"; "len2e"].
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
Lemma Cert5c_0 : ltac2:(tb__ "0|1|
S5S6S3eS20Ufa0S8S28Zde378S9S28A1A3S1fS8S1S19VW;Vst;Vtmax;A3S9S1A1M0A3S8S1S11VW;Vst;Vtmax;A3G0A3A6S7A3").
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
S5S6S3eS20Ufa0S8S28Zde378S9S28A1A3S1fS8S1S13VW;Vst;Vtmax;A3S9S1A1M0A3S8S1S12VW;Vst;Vtmax;A3G0A3A6S7A3").
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
S5S6S3eS20Ufa0S8S28Z3c678S9S28A1A3S1fS8S1S14VW;Vst;Vtmax;A3S9S1A1M0A3S8S1S15VW;Vst;Vtmax;A3G0A3A6S7A3").
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
Module SpineCallocS5i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "prod"; "list"; "pair"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "swf"; "SVar"; "ss_facts"; "SLit"; "ss_next"; "SPUle"; "SPBranch"; "SPNot"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E3p"; "E5s1"; "E5s2"; "C5b"; "C5c"; "E5f"; "C3"; "E5n"; "V_CLS"; "sreg1"; "sreg2"; "C6"; "V_SIZE"; "C2p"; "C2r"; "C5"; "E3r"; "E4d"; "F_gen"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "V_CNT"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "E5s1'"; "E5s2'"; "tab1_ok"; "clsp_e"; "clsp_e31"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS5i.INST"; "s1_0"; "s2_0"; "s3_0"; "s6n_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"].
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
Lemma Cert3p_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z40cc4S5S33Z3c480S8S33A1A3A3S35S5S1S28VW;Vst;Vtmax;A3S8S1A1M0A3S5S1S1bVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SKY_0 : ltac2:(tb__ "0|1|
S4SaS9S9SfSfA2SfA2M0A1S4aS11G0S4dS1aS0S1bVW;Vst;Vtmax;A3A1A1A4S4aS11G0S4dScS11ScS11S5S11S54ScS11S5aVW;A1S56A3A3S55A3S5S11S2eS5S11S30S5S11S2fS5S11S31S8S11A1A3A3A3A3A3A4A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma YX_0 : ltac2:(tb__ "0|1|
S4SaS9SfSfA2M0A1S3S1bVW;Vst;Vtmax;A3A1S8G0A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma YF_0 : ltac2:(tb__ "0|0|
S38S10ScS10ScS10ScS10S59VW;Vst;A2S58S57A1A3S53A3S2dA3S14S0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma YP_0 : ltac2:(tb__ "0|0|
S37S10S17S15Z1A1S13S32A1A2S14S0S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY1_0 : ltac2:(tb__ "0|0|
S4S6S12S0S44S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY2_0 : ltac2:(tb__ "0|0|
S4S6S12S0S45S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY3_0 : ltac2:(tb__ "0|0|
S4S6S12S0S46S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY4_0 : ltac2:(tb__ "0|0|
S4S6S12S0S47S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY5_0 : ltac2:(tb__ "0|0|
S4S6S12S0S48S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY6_0 : ltac2:(tb__ "0|0|
S4S6S12S0S49S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma WY7_0 : ltac2:(tb__ "0|0|
S4S6S12S0S43S1bVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s3_0 : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S3fS35S0S43S1bVW;Vst;Vtmax;A3A1A1S0S21VW;Vst;Vtmax;A3A1A3").
Lemma ENT3_0 : ltac2:(tb__ "0|0|
S4S6S2S43S1bVW;Vst;Vtmax;A3A1S21VW;Vst;Vtmax;A3S50A3S7A3").
Proof. unfold s3_0. cbv beta zeta delta [W st tmax s3_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID3_0 : ltac2:(tb__ "0|0|
S4S6S41S50S35A2S7A3").
Proof. unfold s3_0. cbv beta zeta delta [W st tmax s3_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert3r_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z40cc4S5S33Z3c480S8S33A1A3A3S35S5S1S29VW;Vst;Vtmax;A3S8S1A1M0A3S5S1S2bVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert4_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z7e850S8S33A1A3S35S5S1S21VW;Vst;Vtmax;A3S8S1A1M0A3S5S1S2cVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert5_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z3c5e0S5S33Z3c678S8S33A1A3A3S35S5S1S2aVW;Vst;Vtmax;A3S8S1A1M0A3S5S1S22VW;Vst;Vtmax;A3S5S1S20VW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s6n_0 : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S3fS35S0S22VW;Vst;Vtmax;A3A1S0S26VW;Vst;Vtmax;A3A1A3").
Lemma ENT6n_0 : ltac2:(tb__ "0|0|
S4S6S2S22VW;Vst;Vtmax;A3S26VW;Vst;Vtmax;A3S51A3S7A3").
Proof. unfold s6n_0. cbv beta zeta delta [W st tmax s6n_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID6n_0 : ltac2:(tb__ "0|0|
S4S6S41S51S35A2S7A3").
Proof. unfold s6n_0. cbv beta zeta delta [W st tmax s6n_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W5b_0 : ltac2:(tb__ "0|0|
S4S6S12S0S1eVW;Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D5b_0 : ltac2:(tb__ "0|5|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S42S0S20VW;Vst;Vtmax;A3A1S0S1eVW;Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS3eS13S23A1M4A4S5G0SbSfSfS3dG4A4S8G0A1A3A3S8S10A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX5b_0 : ltac2:(tb__ "0|0|
S4S34S16S0S1eVW;Vst;Vtmax;A3A1A1S16S0S20VW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F5f64_0 : ltac2:(tb__ "0|0|
S37S10S17S13PcA1S15Zfc00A1A2S14S0S20VW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma Cert5b_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z3c64cS8S33A1A3S35S5S1S1eVW;Vst;Vtmax;A3S8S1A1M0A3S5S1S1cVW;Vst;Vtmax;A3S5S1S1dVW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma OV1_0 : ltac2:(tb__ "0|0|
S4S6S52P9eS24VW;Vst;Vtmax;A3A2S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma OV2_0 : ltac2:(tb__ "0|0|
S4S6S52P9eS25VW;Vst;Vtmax;A3A2S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma TAB1_0 : ltac2:(tb__ "0|0|
S4S6S3cP9eS24VW;Vst;Vtmax;A3S4cZ11UeA5S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma TAB2_0 : ltac2:(tb__ "0|0|
S4S6S3cP9eS25VW;Vst;Vtmax;A3S4cZ1U10A5S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W1'_0 : ltac2:(tb__ "0|0|
S4S6S12S0S3aU0Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax E5s1']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma W2'_0 : ltac2:(tb__ "0|0|
S4S6S12S0S3bU0Vst;Vtmax;A3A1A1S7A3").
Proof. cbv beta zeta delta [W st tmax E5s2']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D1'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S42S0S1cVW;Vst;Vtmax;A3A1S0S3aU0Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS24VW;Vst;Vtmax;A3S13S27A1A4S8G0A1A3S8S10A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E5s1']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma D2'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S42S0S1dVW;Vst;Vtmax;A3A1S0S3bU0Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS25VW;Vst;Vtmax;A3S13S27A1A4S8G0A1A3S8S10A1A4A2A3").
Proof. cbv beta zeta delta [W st tmax E5s2']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX1'_0 : ltac2:(tb__ "0|0|
S4S34S16S0S3aU0Vst;Vtmax;A3A1A1S16S0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E5s1']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma NX2'_0 : ltac2:(tb__ "0|0|
S4S34S16S0S3bU0Vst;Vtmax;A3A1A1S16S0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. cbv beta zeta delta [W st tmax E5s2']. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F1gt_0 : ltac2:(tb__ "0|0|
S37S10S18S4bS15Z10A1S13S23A1A3S14S0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F2le_0 : ltac2:(tb__ "0|0|
S37S10S19S18S4bS15Z10A1S13S23A1A3A1S14S0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F1_64_0 : ltac2:(tb__ "0|0|
S37S10S17S13PcA1S15Zfc00A1A2S14S0S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma F2_64_0 : ltac2:(tb__ "0|0|
S37S10S17S13PcA1S15Zfc00A1A2S14S0S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Definition s1_0 : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S3fS35S0S3aU0Vst;Vtmax;A3A1S0S1fVW;Vst;Vtmax;A3A1A3").
Definition s2_0 : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S3fS35S0S3bU0Vst;Vtmax;A3A1S0S1fVW;Vst;Vtmax;A3A1A3").
Lemma ENT1_0 : ltac2:(tb__ "0|0|
S4S6S2S3aU0Vst;Vtmax;A3S1fVW;Vst;Vtmax;A3S4eA3S7A3").
Proof. unfold s1_0. cbv beta zeta delta [W st tmax E5s1' s1_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma ENT2_0 : ltac2:(tb__ "0|0|
S4S6S2S3bU0Vst;Vtmax;A3S1fVW;Vst;Vtmax;A3S4fA3S7A3").
Proof. unfold s2_0. cbv beta zeta delta [W st tmax E5s2' s2_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID1_0 : ltac2:(tb__ "0|0|
S4S6S41S4eS35A2S7A3").
Proof. unfold s1_0. cbv beta zeta delta [W st tmax E5s1' s1_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma SID2_0 : ltac2:(tb__ "0|0|
S4S6S41S4fS35A2S7A3").
Proof. unfold s2_0. cbv beta zeta delta [W st tmax E5s2' s2_0]. CallocMemoSP_all. MemoFast.vmc. Qed.
End INST.
End SpineCallocS5i.

(* [comment removed for export] *)
Module SpineCallocS5iW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "prod"; "list"; "pair"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "swf"; "SVar"; "ss_facts"; "SLit"; "ss_next"; "SPUle"; "SPBranch"; "SPNot"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E3p"; "E5s1"; "E5s2"; "C5b"; "C5c"; "E5f"; "C3"; "E5n"; "V_CLS"; "sreg1"; "sreg2"; "C6"; "V_SIZE"; "C2p"; "C2r"; "C5"; "E3r"; "E4d"; "F_gen"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "V_CNT"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "E5s1'"; "E5s2'"; "tab1_ok"; "clsp_e"; "clsp_e31"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS5iW1.INST"; "s1_0"; "s2_0"; "s3_0"; "s6n_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "F_s1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"].
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
Lemma Cert3p_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z40cc4S5S33Z3c480S8S33A1A3A3S35S5S1S28VW;Vst;Vtmax;A3S8S1A1M0A3S5S1S1bVW;Vst;Vtmax;A3G0A3A6S7A3").
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
S4S6S39S36Ufa0S5S33Z40cc4S5S33Z3c480S8S33A1A3A3S35S5S1S29VW;Vst;Vtmax;A3S8S1A1M0A3S5S1S2bVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Cert4_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z7e850S8S33A1A3S35S5S1S21VW;Vst;Vtmax;A3S8S1A1M0A3S5S1S2cVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma Cert5_0 : ltac2:(tb__ "0|1|
S4S6S39S36Ufa0S5S33Z3c5e0S5S33Z3c678S8S33A1A3A3S35S5S1S2aVW;Vst;Vtmax;A3S8S1A1M0A3S5S1S22VW;Vst;Vtmax;A3S5S1S20VW;Vst;Vtmax;A3G0A3A3A6S7A3").
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
S4S6S39S36Ufa0S5S33Z3c64cS8S33A1A3S35S5S1S1eVW;Vst;Vtmax;A3S8S1A1M0A3S5S1S1cVW;Vst;Vtmax;A3S5S1S1dVW;Vst;Vtmax;A3G0A3A3A6S7A3").
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
Module SpineCallocS8iW1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "ss_facts"; "SVar"; "ss_next"; "SPBranch"; "SLit"; "swf"; "SPNot"; "SPUle"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "F_gen"; "C7p"; "C8"; "C8p"; "V_CLS"; "V_ND"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "n8e"; "BP"; "C7"; "LPe"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8"; "E7c1'"; "E7c2'"; "E7q1'"; "E7q2'"; "a0e7"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "tab_ok"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8iW1.INST"; "s8a_0"; "s8b_0"; "s8c_0"; "s8d_0"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSPW1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Lemma Cert7_0 : ltac2:(tb__ "0|1|
S3S4S44S18Ufa0S6S2eZ3c728S6S2eZ3c870S7S2eA1A3A3S17S6S1S2cVW;Vst;Vtmax;A3S7S1A1M0A3S6S1S1bVW;Vst;Vtmax;A3S6S1S1cVW;Vst;Vtmax;A3S6S1S1dVW;Vst;Vtmax;A3G0A3A3A3A6S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma OV7a_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS26VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma OV7b_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS27VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma TAB7a_0 : ltac2:(tb__ "0|0|
S3S4S41P9dS26VW;Vst;Vtmax;A3S3fZ208S42S43S36S37S38S36S39A1A1A1A1A1A1A5S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. refine (eq_ind (CertMallocSP.creg7a (Wcan 0) UStopLe 2) (fun c => tab_ok 157 c ClassID 520 8128%nat = true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocS8i.TAB7a_0 m_creg7a _). MemoFast.vmc1. Qed.
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
S3S4S44S18Ufa0S6S2eZ3c870S7S2eA1A3S17S6S1S21VW;Vst;Vtmax;A3S7S1A1M0A3S6S1S1eVW;Vst;Vtmax;A3S6S1S1fVW;Vst;Vtmax;A3G0A3A3A6S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma OV7c_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS28VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma OV7d_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS29VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. MemoFast.vmc. Qed.
Lemma TAB7c_0 : ltac2:(tb__ "0|0|
S3S4S41P9dS28VW;Vst;Vtmax;A3S3fZ208S42S43S36S37S38S36S39A1A1A1A1A1A1A5S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSPW1_all. refine (eq_ind (CertMallocSP.creg7c (Wcan 0) UStopLe 2) (fun c => tab_ok 157 c ClassID 520 8128%nat = true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocS8i.TAB7c_0 m_creg7c _). MemoFast.vmc1. Qed.
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
Module SpineCallocS8i.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "ss_facts"; "SVar"; "ss_next"; "SPBranch"; "SLit"; "swf"; "SPNot"; "SPUle"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "F_gen"; "C7p"; "C8"; "C8p"; "V_CLS"; "V_ND"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "n8e"; "BP"; "C7"; "LPe"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8"; "E7c1'"; "E7c2'"; "E7q1'"; "E7q2'"; "a0e7"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "tab_ok"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8i.INST"; "s8a_0"; "s8b_0"; "s8c_0"; "s8d_0"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.CallocMemoSP.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Lemma Cert7_0 : ltac2:(tb__ "0|1|
S3S4S44S18Ufa0S6S2eZ3c728S6S2eZ3c870S7S2eA1A3A3S17S6S1S2cVW;Vst;Vtmax;A3S7S1A1M0A3S6S1S1bVW;Vst;Vtmax;A3S6S1S1cVW;Vst;Vtmax;A3S6S1S1dVW;Vst;Vtmax;A3G0A3A3A3A6S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma OV7a_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS26VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma OV7b_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS27VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma TAB7a_0 : ltac2:(tb__ "0|0|
S3S4S41P9dS26VW;Vst;Vtmax;A3S3fZ208S42S43S36S37S38S36S39A1A1A1A1A1A1A5S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. refine (eq_ind (CertMallocSP.creg7a (Wcan 0) UStopLe 2) (fun c => tab_ok 157 c ClassID 520 8128%nat = true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocS8i.TAB7a_0 m_creg7a _). MemoFast.vmc1. Qed.
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
S3S4S44S18Ufa0S6S2eZ3c870S7S2eA1A3S17S6S1S21VW;Vst;Vtmax;A3S7S1A1M0A3S6S1S1eVW;Vst;Vtmax;A3S6S1S1fVW;Vst;Vtmax;A3G0A3A3A6S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma OV7c_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS28VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma OV7d_0 : ltac2:(tb__ "0|0|
S3S4S40P9dS29VW;Vst;Vtmax;A3A2S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. MemoFast.vmc. Qed.
Lemma TAB7c_0 : ltac2:(tb__ "0|0|
S3S4S41P9dS28VW;Vst;Vtmax;A3S3fZ208S42S43S36S37S38S36S39A1A1A1A1A1A1A5S5A3").
Proof. cbv beta zeta delta [W st tmax]. CallocMemoSP_all. refine (eq_ind (CertMallocSP.creg7c (Wcan 0) UStopLe 2) (fun c => tab_ok 157 c ClassID 520 8128%nat = true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocS8i.TAB7c_0 m_creg7c _). MemoFast.vmc1. Qed.
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

