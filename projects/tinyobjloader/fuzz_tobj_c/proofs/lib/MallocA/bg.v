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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao ba.

(* [comment removed for export] *)
Module SpineMallocS6i.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "option"; "pair"; "Some"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "C5m1"; "C5m2"; "E5m1"; "E5m2"; "C5d"; "C5e"; "E5j"; "C6"; "C5c"; "F_gen"; "BR"; "LLe"; "LRe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "memset_entryA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "ss_facts"; "ss_next"; "sv"; "sobj"; "sprop_below"; "swf"; "@Corelib.Init.Specif"; "sig"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bg.SpineMallocS6i.INST"; "s51_0"; "s52_0"; "R51_0"; "R52_0"; "T51_0"; "T52_0"; "s6j_0"; "sd51_0"; "sd52_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6"; "a0e2"; "len1e"; "len2e"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S28S0S0S5S0S17VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5c W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5c] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5c]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S28S0S0S5S0S11VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5m1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5m1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5m1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S28S0S0S5S0SfVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5m1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5m1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5m1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S28S0S0S5S0S13VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5d W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5d] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5d]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S28S0S0S5S0S12VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5m2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5m2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5m2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S28S0S0S5S0S10VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5m2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5m2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5m2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S28S0S0S5S0S14VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5e W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5e] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5e]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S28S0S0S5S0S15VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5j W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5j] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5j]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S28S0S0S5S0S16VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C6]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma Cert5c_0 : ltac2:(tb__ "0|1|
S5S6S3fS20Ufa0S8S29Zde378S9S29A1A3S1fS8S0S17VW;Vst;Vtmax;A3S9S0A1M0A3S8S0S11VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C5c W st tmax) memo_0. memo_rw (E5m1 W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma G5m1_0 : ltac2:(tb__ "0|0|
S3eS21S18S22S1S11VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E5m1 W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W5m1_0 : ltac2:(tb__ "0|0|
S5S6S27S1SfVW;Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D5m1_0 : ltac2:(tb__ "0|4|
S5SbSeSaSeS24S24A2M0A1M1SaS21A1M2A2M3A1S41S1S11VW;Vst;Vtmax;A3A1S1SfVW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS24S24S44S1aA4S9G0A1A3S9S21A1A4A2A3").
Proof. memo_rw (E5m1 W st tmax) memo_1. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX5m1_0 : ltac2:(tb__ "0|0|
S5S2aS23S1SfVW;Vst;Vtmax;A3A1A1S23S1S11VW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C5m1 W st tmax) memo_2. memo_rw (E5m1 W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s51_0 : ltac2:(tb__ "0|0|
S2c") := ltac2:(tb__ "0|0|
S2bP1S1SfVW;Vst;Vtmax;A3A1S1S1cA1A3").
Definition R51_0 : ltac2:(tb__ "0|0|
SaS25A1") := ltac2:(tb__ "0|1|
SbSaS25A1M0A1G0Lx;S39SfVW;Vst;Vtmax;A3S1cS2eA3G0R1LR;S9S25A1Xbx2").
Definition T51_0 : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S3aS2eS1cS37S3cS1dA1A1SfVW;Vst;Vtmax;A3S30A5").
Definition sd51_0 : ltac2:(tb__ "0|0|
S2c") := ltac2:(tb__ "0|0|
S2bS1fS1S38S32S22S1SfVW;Vst;Vtmax;A3A1A1A2A1S1S13VW;Vst;Vtmax;A3A1A3").
Lemma He51_0 : ltac2:(tb__ "0|1|
S5SbSaS25A1M0A1S39SfVW;Vst;Vtmax;A3S1cS2eA3SdG0S30A2A3").
Proof. unfold s51_0, R51_0. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk51_0 : ltac2:(tb__ "0|0|
S5S6S3bSfVW;Vst;Vtmax;A3S1cS2eS30S40S4S0S3S1eA4A5S7A3").
Proof. unfold s51_0, R51_0. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT51_0 : ltac2:(tb__ "0|0|
S5S0S3aS2eS1cS37S3cS1dA1A1SfVW;Vst;Vtmax;A3S30A5S32A3").
Proof. reflexivity. Qed.
Lemma FBC51_0 : ltac2:(tb__ "0|1|
S5S6S3dS21S26S23S1SfVW;Vst;Vtmax;A3A1M0A1A1S22G0A1A3S7A3").
Proof. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT51_0 : ltac2:(tb__ "0|0|
S5S6S3dS21S26S23S1S32A1A1A1S22S1SfVW;Vst;Vtmax;A3A1A1A3S7A3").
Proof. unfold T51_0. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT51_0 : ltac2:(tb__ "0|0|
S5S6S2S38S32S22S1SfVW;Vst;Vtmax;A3A1A1A2S13VW;Vst;Vtmax;A3S35A3S7A3").
Proof. unfold T51_0, sd51_0. memo_rw (C5m1 W st tmax) memo_2. memo_rw (C5d W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID51_0 : ltac2:(tb__ "0|0|
S5S6S2dS35S1fA2S7A3").
Proof. unfold sd51_0. memo_rw (C5d W st tmax) memo_3. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC51_0 : ltac2:(tb__ "0|0|
S42S1fS23S1SfVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert5d_0 : ltac2:(tb__ "0|1|
S5S6S3fS20Ufa0S8S29Zde378S9S29A1A3S1fS8S0S13VW;Vst;Vtmax;A3S9S0A1M0A3S8S0S12VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C5d W st tmax) memo_3. memo_rw (E5m2 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma G5m2_0 : ltac2:(tb__ "0|0|
S3eS21S18S22S1S12VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E5m2 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W5m2_0 : ltac2:(tb__ "0|0|
S5S6S27S1S10VW;Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D5m2_0 : ltac2:(tb__ "0|4|
S5SbSeSaSeS24S24A2M0A1M1SaS21A1M2A2M3A1S41S1S12VW;Vst;Vtmax;A3A1S1S10VW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS24S24S43S19A4S8G0ScS24S24S45S1bA4S9G0A1A3A3S9S21A1A4A2A3").
Proof. memo_rw (E5m2 W st tmax) memo_4. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX5m2_0 : ltac2:(tb__ "0|0|
S5S2aS23S1S10VW;Vst;Vtmax;A3A1A1S23S1S12VW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C5m2 W st tmax) memo_5. memo_rw (E5m2 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s52_0 : ltac2:(tb__ "0|0|
S2c") := ltac2:(tb__ "0|0|
S2bP1S1S10VW;Vst;Vtmax;A3A1S1S1cA1A3").
Definition R52_0 : ltac2:(tb__ "0|0|
SaS25A1") := ltac2:(tb__ "0|1|
SbSaS25A1M0A1G0Lx;S39S10VW;Vst;Vtmax;A3S1cS2fA3G0R1LR;S9S25A1Xbx2").
Definition T52_0 : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S3aS2fS1cS37S3cS1dA1A1S10VW;Vst;Vtmax;A3S31A5").
Definition sd52_0 : ltac2:(tb__ "0|0|
S2c") := ltac2:(tb__ "0|0|
S2bS1fS1S38S33S22S1S10VW;Vst;Vtmax;A3A1A1A2A1S1S14VW;Vst;Vtmax;A3A1A3").
Lemma He52_0 : ltac2:(tb__ "0|1|
S5SbSaS25A1M0A1S39S10VW;Vst;Vtmax;A3S1cS2fA3SdG0S31A2A3").
Proof. unfold s52_0, R52_0. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk52_0 : ltac2:(tb__ "0|0|
S5S6S3bS10VW;Vst;Vtmax;A3S1cS2fS31S40S4S0S3S1eA4A5S7A3").
Proof. unfold s52_0, R52_0. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT52_0 : ltac2:(tb__ "0|0|
S5S0S3aS2fS1cS37S3cS1dA1A1S10VW;Vst;Vtmax;A3S31A5S33A3").
Proof. reflexivity. Qed.
Lemma FBC52_0 : ltac2:(tb__ "0|1|
S5S6S3dS21S26S23S1S10VW;Vst;Vtmax;A3A1M0A1A1S22G0A1A3S7A3").
Proof. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT52_0 : ltac2:(tb__ "0|0|
S5S6S3dS21S26S23S1S33A1A1A1S22S1S10VW;Vst;Vtmax;A3A1A1A3S7A3").
Proof. unfold T52_0. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT52_0 : ltac2:(tb__ "0|0|
S5S6S2S38S33S22S1S10VW;Vst;Vtmax;A3A1A1A2S14VW;Vst;Vtmax;A3S36A3S7A3").
Proof. unfold T52_0, sd52_0. memo_rw (C5m2 W st tmax) memo_5. memo_rw (C5e W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID52_0 : ltac2:(tb__ "0|0|
S5S6S2dS36S1fA2S7A3").
Proof. unfold sd52_0. memo_rw (C5e W st tmax) memo_6. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC52_0 : ltac2:(tb__ "0|0|
S42S1fS23S1S10VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert5e_0 : ltac2:(tb__ "0|1|
S5S6S3fS20Ufa0S8S29Z3c678S9S29A1A3S1fS8S0S14VW;Vst;Vtmax;A3S9S0A1M0A3S8S0S15VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C5e W st tmax) memo_6. memo_rw (E5j W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s6j_0 : ltac2:(tb__ "0|0|
S2c") := ltac2:(tb__ "0|0|
S2bS1fS1S15VW;Vst;Vtmax;A3A1S1S16VW;Vst;Vtmax;A3A1A3").
Lemma ENT6j_0 : ltac2:(tb__ "0|0|
S5S6S2S15VW;Vst;Vtmax;A3S16VW;Vst;Vtmax;A3S34A3S7A3").
Proof. unfold s6j_0. memo_rw (E5j W st tmax) memo_7. memo_rw (C6 W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID6j_0 : ltac2:(tb__ "0|0|
S5S6S2dS34S1fA2S7A3").
Proof. unfold s6j_0. memo_rw (C6 W st tmax) memo_8. memo_rw (E5j W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS6i.

(* [comment removed for export] *)
Module SpineMallocS7i.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "ax_setS"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "option"; "Some"; "prod"; "pair"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "C6m"; "E6s"; "C6l"; "C7"; "E6l"; "C6b"; "E6j"; "E6m"; "O_U"; "C6"; "F_gen"; "LUe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sv"; "ss_objs"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Corelib.Init.Specif"; "sig"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bg.SpineMallocS7i.INST"; "s6_0"; "R6_0"; "T6_0"; "k6_0"; "s7j_0"; "s7s_0"; "sd6_0"; "E6sz_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zobj"; "zero_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@Stdlib.Lists.List"; "forallb"; "incl"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7"; "len3e"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S28S0S0S6S0S1bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C6]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S28S0S0S6S0S13VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E6s W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E6s] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E6s]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S28S0S0S6S0S16VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E6l W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E6l] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E6l]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S28S0S0S6S0S15VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C7 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C7] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C7]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S28S0S0S6S0S14VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6l W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6l] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C6l]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S28S0S0S6S0S19VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E6m W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E6m] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E6m]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S28S0S0S6S0S12VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6m W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6m] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C6m]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S28S0S0S6S0S17VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C6b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S28S0S0S6S0S18VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E6j W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E6j] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E6j]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma Cert6_0 : ltac2:(tb__ "0|1|
S6S7S39S27Ufa0S9S29Z5f864S9S29Z3c698SaS29A1A3A3S26S9S0S1bVW;Vst;Vtmax;A3SaS0A1M0A3S9S0S13VW;Vst;Vtmax;A3S9S0S16VW;Vst;Vtmax;A3G0A3A3A6S8A3").
Proof. memo_rw (C6 W st tmax) memo_0. memo_rw (E6s W st tmax) memo_1. memo_rw (E6l W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition k6_0 : ltac2:(tb__ "0|0|
S11") := ltac2:(tb__ "0|0|
S47S10S1eS23S1S13VW;Vst;Vtmax;A3A1A1A2U3A2").
Lemma NTH6s_0 : ltac2:(tb__ "0|0|
S6ScS1eA1S46S1eS23S1S13VW;Vst;Vtmax;A3A1A1S31A3SdS1eS1aA2A3").
Proof. unfold k6_0. memo_rw (E6s W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ZC6s_0 : ltac2:(tb__ "0|0|
S6S7S40S21S1S13VW;Vst;Vtmax;A3A1A1S1aA2S8A3").
Proof. memo_rw (E6s W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E6sz_0 : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|2|
S3S13VW;Vst;Vtmax;A3M0S3dS1G0A1M1S3cS1eS23G1A1S31S3fS1aA1A4A2A2").
Definition s7s_0 : ltac2:(tb__ "0|0|
S37") := ltac2:(tb__ "0|0|
S36S26S1S35A1S1S15VW;Vst;Vtmax;A3A1A3").
Lemma ENT7s_0 : ltac2:(tb__ "0|2|
S6S7S2S3S13VW;Vst;Vtmax;A3M0S3dS1G0A1M1S3cS1eS23G1A1S31S3fS1aA1A4A2A2S15VW;Vst;Vtmax;A3S33A3S8A3").
Proof. unfold k6_0, s7s_0. memo_rw (E6s W st tmax) memo_1. memo_rw (C7 W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID7s_0 : ltac2:(tb__ "0|0|
S6S7S38S33S26A2S8A3").
Proof. unfold s7s_0. memo_rw (C7 W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma G6l_0 : ltac2:(tb__ "0|0|
S45S1fS1cS21S1S16VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E6l W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W6l_0 : ltac2:(tb__ "0|0|
S6S7S25S1S14VW;Vst;Vtmax;A3A1A1S8A3").
Proof. memo_rw (C6l W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D6l_0 : ltac2:(tb__ "0|4|
S6ScSeSbSeS22S22A2M0A1M1SbS1fA1M2A2M3A1S3bS1S16VW;Vst;Vtmax;A3A1S1S14VW;Vst;Vtmax;A3A1A2SdG3SfG1G2S9G0SfS22S22S49S1dA4SaG0A1A3SaS1fA1A4A2A3").
Proof. memo_rw (E6l W st tmax) memo_2. memo_rw (C6l W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX6l_0 : ltac2:(tb__ "0|0|
S6S2aS20S1S14VW;Vst;Vtmax;A3A1A1S20S1S16VW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C6l W st tmax) memo_4. memo_rw (E6l W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert6l_0 : ltac2:(tb__ "0|1|
S6S7S39S27Ufa0S9S29Zde378SaS29A1A3S26S9S0S14VW;Vst;Vtmax;A3SaS0A1M0A3S9S0S19VW;Vst;Vtmax;A3G0A3A6S8A3").
Proof. memo_rw (C6l W st tmax) memo_4. memo_rw (E6m W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W6m_0 : ltac2:(tb__ "0|0|
S6S7S25S1S12VW;Vst;Vtmax;A3A1A1S8A3").
Proof. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D6m_0 : ltac2:(tb__ "0|4|
S6ScSeSbSeS22S22A2M0A1M1SbS1fA1M2A2M3A1S3bS1S19VW;Vst;Vtmax;A3A1S1S12VW;Vst;Vtmax;A3A1A2SdG3SfG1G2SaG0A1SaS1fA1A4A2A3").
Proof. memo_rw (E6m W st tmax) memo_5. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX6m_0 : ltac2:(tb__ "0|0|
S6S2aS20S1S12VW;Vst;Vtmax;A3A1A1S20S1S19VW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C6m W st tmax) memo_6. memo_rw (E6m W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s6_0 : ltac2:(tb__ "0|0|
S37") := ltac2:(tb__ "0|0|
S36P1S1S12VW;Vst;Vtmax;A3A1S1S2bA1A3").
Definition R6_0 : ltac2:(tb__ "0|0|
SbS1eA1") := ltac2:(tb__ "0|1|
ScSbS1eA1M0A1G0Lx;S41S12VW;Vst;Vtmax;A3S2bS2eA3G0R1LR;SaS1eA1Xcx2").
Definition T6_0 : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S42S2eS2bS3aS2cA1S12VW;Vst;Vtmax;A3S2fA5").
Definition sd6_0 : ltac2:(tb__ "0|0|
S37") := ltac2:(tb__ "0|0|
S36S26S1S3eS30S21S1S12VW;Vst;Vtmax;A3A1A1A2A1S1S17VW;Vst;Vtmax;A3A1A3").
Lemma He6_0 : ltac2:(tb__ "0|1|
S6ScSbS1eA1M0A1S41S12VW;Vst;Vtmax;A3S2bS2eA3SdG0S2fA2A3").
Proof. unfold s6_0, R6_0. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk6_0 : ltac2:(tb__ "0|0|
S6S7S43S12VW;Vst;Vtmax;A3S2bS2eS2fS48S5S0S4S2dA4A5S8A3").
Proof. unfold s6_0, R6_0. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT6_0 : ltac2:(tb__ "0|0|
S6S0S42S2eS2bS3aS2cA1S12VW;Vst;Vtmax;A3S2fA5S30A3").
Proof. reflexivity. Qed.
Lemma FBC6_0 : ltac2:(tb__ "0|1|
S6S7S44S1fS24S20S1S12VW;Vst;Vtmax;A3A1M0A1A1S21G0A1A3S8A3").
Proof. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT6_0 : ltac2:(tb__ "0|0|
S6S7S44S1fS24S20S1S30A1A1A1S21S1S12VW;Vst;Vtmax;A3A1A1A3S8A3").
Proof. unfold T6_0. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT6_0 : ltac2:(tb__ "0|0|
S6S7S2S3eS30S21S1S12VW;Vst;Vtmax;A3A1A1A2S17VW;Vst;Vtmax;A3S34A3S8A3").
Proof. unfold T6_0, sd6_0. memo_rw (C6m W st tmax) memo_6. memo_rw (C6b W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID6_0 : ltac2:(tb__ "0|0|
S6S7S38S34S26A2S8A3").
Proof. unfold sd6_0. memo_rw (C6b W st tmax) memo_7. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC6_0 : ltac2:(tb__ "0|0|
S4aS26S20S1S12VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert6b_0 : ltac2:(tb__ "0|1|
S6S7S39S27Ufa0S9S29Z3c698SaS29A1A3S26S9S0S17VW;Vst;Vtmax;A3SaS0A1M0A3S9S0S18VW;Vst;Vtmax;A3G0A3A6S8A3").
Proof. memo_rw (C6b W st tmax) memo_7. memo_rw (E6j W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s7j_0 : ltac2:(tb__ "0|0|
S37") := ltac2:(tb__ "0|0|
S36S26S1S18VW;Vst;Vtmax;A3A1S1S15VW;Vst;Vtmax;A3A1A3").
Lemma ENT7j_0 : ltac2:(tb__ "0|0|
S6S7S2S18VW;Vst;Vtmax;A3S15VW;Vst;Vtmax;A3S32A3S8A3").
Proof. unfold s7j_0. memo_rw (E6j W st tmax) memo_8. memo_rw (C7 W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID7j_0 : ltac2:(tb__ "0|0|
S6S7S38S32S26A2S8A3").
Proof. unfold s7j_0. memo_rw (C7 W st tmax) memo_3. memo_rw (E6j W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS7i.

(* [comment removed for export] *)
Module SpineMallocS6iW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "option"; "pair"; "Some"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "C5m1"; "C5m2"; "E5m1"; "E5m2"; "C5d"; "C5e"; "E5j"; "C6"; "C5c"; "F_gen"; "BR"; "LLe"; "LRe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "memset_entryA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "ss_facts"; "ss_next"; "sv"; "sobj"; "sprop_below"; "swf"; "@Corelib.Init.Specif"; "sig"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bg.SpineMallocS6iW2.INST"; "s51_0"; "s52_0"; "R51_0"; "R52_0"; "T51_0"; "T52_0"; "s6j_0"; "sd51_0"; "sd52_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6"; "a0e2"; "len1e"; "len2e"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S28S0S0S5S0S17VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5c W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5c] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5c]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S28S0S0S5S0S11VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5m1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5m1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5m1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S28S0S0S5S0SfVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5m1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5m1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5m1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S28S0S0S5S0S13VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5d W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5d] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5d]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S28S0S0S5S0S12VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5m2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5m2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5m2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S28S0S0S5S0S10VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5m2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5m2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5m2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S28S0S0S5S0S14VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5e W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5e] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5e]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S28S0S0S5S0S15VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5j W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5j] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5j]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S28S0S0S5S0S16VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C6]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma Cert5c_0 : ltac2:(tb__ "0|1|
S5S6S3fS20Ufa0S8S29Zde378S9S29A1A3S1fS8S0S17VW;Vst;Vtmax;A3S9S0A1M0A3S8S0S11VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C5c W st tmax) memo_0. memo_rw (E5m1 W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma G5m1_0 : ltac2:(tb__ "0|0|
S3eS21S18S22S1S11VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E5m1 W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W5m1_0 : ltac2:(tb__ "0|0|
S5S6S27S1SfVW;Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D5m1_0 : ltac2:(tb__ "0|4|
S5SbSeSaSeS24S24A2M0A1M1SaS21A1M2A2M3A1S41S1S11VW;Vst;Vtmax;A3A1S1SfVW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS24S24S44S1aA4S9G0A1A3S9S21A1A4A2A3").
Proof. memo_rw (E5m1 W st tmax) memo_1. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX5m1_0 : ltac2:(tb__ "0|0|
S5S2aS23S1SfVW;Vst;Vtmax;A3A1A1S23S1S11VW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C5m1 W st tmax) memo_2. memo_rw (E5m1 W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s51_0 : ltac2:(tb__ "0|0|
S2c") := ltac2:(tb__ "0|0|
S2bP1S1SfVW;Vst;Vtmax;A3A1S1S1cA1A3").
Definition R51_0 : ltac2:(tb__ "0|0|
SaS25A1") := ltac2:(tb__ "0|1|
SbSaS25A1M0A1G0Lx;S39SfVW;Vst;Vtmax;A3S1cS2eA3G0R1LR;S9S25A1Xbx2").
Definition T51_0 : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S3aS2eS1cS37S3cS1dA1A1SfVW;Vst;Vtmax;A3S30A5").
Definition sd51_0 : ltac2:(tb__ "0|0|
S2c") := ltac2:(tb__ "0|0|
S2bS1fS1S38S32S22S1SfVW;Vst;Vtmax;A3A1A1A2A1S1S13VW;Vst;Vtmax;A3A1A3").
Lemma He51_0 : ltac2:(tb__ "0|1|
S5SbSaS25A1M0A1S39SfVW;Vst;Vtmax;A3S1cS2eA3SdG0S30A2A3").
Proof. unfold s51_0, R51_0. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk51_0 : ltac2:(tb__ "0|0|
S5S6S3bSfVW;Vst;Vtmax;A3S1cS2eS30S40S4S0S3S1eA4A5S7A3").
Proof. unfold s51_0, R51_0. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT51_0 : ltac2:(tb__ "0|0|
S5S0S3aS2eS1cS37S3cS1dA1A1SfVW;Vst;Vtmax;A3S30A5S32A3").
Proof. reflexivity. Qed.
Lemma FBC51_0 : ltac2:(tb__ "0|1|
S5S6S3dS21S26S23S1SfVW;Vst;Vtmax;A3A1M0A1A1S22G0A1A3S7A3").
Proof. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT51_0 : ltac2:(tb__ "0|0|
S5S6S3dS21S26S23S1S32A1A1A1S22S1SfVW;Vst;Vtmax;A3A1A1A3S7A3").
Proof. unfold T51_0. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT51_0 : ltac2:(tb__ "0|0|
S5S6S2S38S32S22S1SfVW;Vst;Vtmax;A3A1A1A2S13VW;Vst;Vtmax;A3S35A3S7A3").
Proof. unfold T51_0, sd51_0. memo_rw (C5m1 W st tmax) memo_2. memo_rw (C5d W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID51_0 : ltac2:(tb__ "0|0|
S5S6S2dS35S1fA2S7A3").
Proof. unfold sd51_0. memo_rw (C5d W st tmax) memo_3. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC51_0 : ltac2:(tb__ "0|0|
S42S1fS23S1SfVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5m1 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert5d_0 : ltac2:(tb__ "0|1|
S5S6S3fS20Ufa0S8S29Zde378S9S29A1A3S1fS8S0S13VW;Vst;Vtmax;A3S9S0A1M0A3S8S0S12VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C5d W st tmax) memo_3. memo_rw (E5m2 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma G5m2_0 : ltac2:(tb__ "0|0|
S3eS21S18S22S1S12VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E5m2 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W5m2_0 : ltac2:(tb__ "0|0|
S5S6S27S1S10VW;Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D5m2_0 : ltac2:(tb__ "0|4|
S5SbSeSaSeS24S24A2M0A1M1SaS21A1M2A2M3A1S41S1S12VW;Vst;Vtmax;A3A1S1S10VW;Vst;Vtmax;A3A1A2SdG3ScG1G2S8G0ScS24S24S43S19A4S8G0ScS24S24S45S1bA4S9G0A1A3A3S9S21A1A4A2A3").
Proof. memo_rw (E5m2 W st tmax) memo_4. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX5m2_0 : ltac2:(tb__ "0|0|
S5S2aS23S1S10VW;Vst;Vtmax;A3A1A1S23S1S12VW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C5m2 W st tmax) memo_5. memo_rw (E5m2 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s52_0 : ltac2:(tb__ "0|0|
S2c") := ltac2:(tb__ "0|0|
S2bP1S1S10VW;Vst;Vtmax;A3A1S1S1cA1A3").
Definition R52_0 : ltac2:(tb__ "0|0|
SaS25A1") := ltac2:(tb__ "0|1|
SbSaS25A1M0A1G0Lx;S39S10VW;Vst;Vtmax;A3S1cS2fA3G0R1LR;S9S25A1Xbx2").
Definition T52_0 : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S3aS2fS1cS37S3cS1dA1A1S10VW;Vst;Vtmax;A3S31A5").
Definition sd52_0 : ltac2:(tb__ "0|0|
S2c") := ltac2:(tb__ "0|0|
S2bS1fS1S38S33S22S1S10VW;Vst;Vtmax;A3A1A1A2A1S1S14VW;Vst;Vtmax;A3A1A3").
Lemma He52_0 : ltac2:(tb__ "0|1|
S5SbSaS25A1M0A1S39S10VW;Vst;Vtmax;A3S1cS2fA3SdG0S31A2A3").
Proof. unfold s52_0, R52_0. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk52_0 : ltac2:(tb__ "0|0|
S5S6S3bS10VW;Vst;Vtmax;A3S1cS2fS31S40S4S0S3S1eA4A5S7A3").
Proof. unfold s52_0, R52_0. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT52_0 : ltac2:(tb__ "0|0|
S5S0S3aS2fS1cS37S3cS1dA1A1S10VW;Vst;Vtmax;A3S31A5S33A3").
Proof. reflexivity. Qed.
Lemma FBC52_0 : ltac2:(tb__ "0|1|
S5S6S3dS21S26S23S1S10VW;Vst;Vtmax;A3A1M0A1A1S22G0A1A3S7A3").
Proof. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT52_0 : ltac2:(tb__ "0|0|
S5S6S3dS21S26S23S1S33A1A1A1S22S1S10VW;Vst;Vtmax;A3A1A1A3S7A3").
Proof. unfold T52_0. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT52_0 : ltac2:(tb__ "0|0|
S5S6S2S38S33S22S1S10VW;Vst;Vtmax;A3A1A1A2S14VW;Vst;Vtmax;A3S36A3S7A3").
Proof. unfold T52_0, sd52_0. memo_rw (C5m2 W st tmax) memo_5. memo_rw (C5e W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID52_0 : ltac2:(tb__ "0|0|
S5S6S2dS36S1fA2S7A3").
Proof. unfold sd52_0. memo_rw (C5e W st tmax) memo_6. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC52_0 : ltac2:(tb__ "0|0|
S42S1fS23S1S10VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5m2 W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert5e_0 : ltac2:(tb__ "0|1|
S5S6S3fS20Ufa0S8S29Z3c678S9S29A1A3S1fS8S0S14VW;Vst;Vtmax;A3S9S0A1M0A3S8S0S15VW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C5e W st tmax) memo_6. memo_rw (E5j W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s6j_0 : ltac2:(tb__ "0|0|
S2c") := ltac2:(tb__ "0|0|
S2bS1fS1S15VW;Vst;Vtmax;A3A1S1S16VW;Vst;Vtmax;A3A1A3").
Lemma ENT6j_0 : ltac2:(tb__ "0|0|
S5S6S2S15VW;Vst;Vtmax;A3S16VW;Vst;Vtmax;A3S34A3S7A3").
Proof. unfold s6j_0. memo_rw (E5j W st tmax) memo_7. memo_rw (C6 W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID6j_0 : ltac2:(tb__ "0|0|
S5S6S2dS34S1fA2S7A3").
Proof. unfold s6j_0. memo_rw (C6 W st tmax) memo_8. memo_rw (E5j W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS6iW2.

(* [comment removed for export] *)
Module SpineMallocS7iW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "ax_setS"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "option"; "Some"; "prod"; "pair"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "C6m"; "E6s"; "C6l"; "C7"; "E6l"; "C6b"; "E6j"; "E6m"; "O_U"; "C6"; "F_gen"; "LUe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "ss_next"; "ss_facts"; "sv"; "ss_objs"; "sprop_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Corelib.Init.Specif"; "sig"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bg.SpineMallocS7iW2.INST"; "s6_0"; "R6_0"; "T6_0"; "k6_0"; "s7j_0"; "s7s_0"; "sd6_0"; "E6sz_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zobj"; "zero_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@Stdlib.Lists.List"; "forallb"; "incl"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7"; "len3e"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S28S0S0S6S0S1bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C6]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S28S0S0S6S0S13VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E6s W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E6s] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E6s]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S28S0S0S6S0S16VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E6l W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E6l] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E6l]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S28S0S0S6S0S15VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C7 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C7] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C7]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S28S0S0S6S0S14VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6l W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6l] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C6l]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S28S0S0S6S0S19VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E6m W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E6m] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E6m]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S28S0S0S6S0S12VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6m W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6m] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C6m]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S28S0S0S6S0S17VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C6b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S28S0S0S6S0S18VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E6j W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E6j] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E6j]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma Cert6_0 : ltac2:(tb__ "0|1|
S6S7S39S27Ufa0S9S29Z5f864S9S29Z3c698SaS29A1A3A3S26S9S0S1bVW;Vst;Vtmax;A3SaS0A1M0A3S9S0S13VW;Vst;Vtmax;A3S9S0S16VW;Vst;Vtmax;A3G0A3A3A6S8A3").
Proof. memo_rw (C6 W st tmax) memo_0. memo_rw (E6s W st tmax) memo_1. memo_rw (E6l W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition k6_0 : ltac2:(tb__ "0|0|
S11") := ltac2:(tb__ "0|0|
S47S10S1eS23S1S13VW;Vst;Vtmax;A3A1A1A2U3A2").
Lemma NTH6s_0 : ltac2:(tb__ "0|0|
S6ScS1eA1S46S1eS23S1S13VW;Vst;Vtmax;A3A1A1S31A3SdS1eS1aA2A3").
Proof. unfold k6_0. memo_rw (E6s W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ZC6s_0 : ltac2:(tb__ "0|0|
S6S7S40S21S1S13VW;Vst;Vtmax;A3A1A1S1aA2S8A3").
Proof. memo_rw (E6s W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E6sz_0 : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|2|
S3S13VW;Vst;Vtmax;A3M0S3dS1G0A1M1S3cS1eS23G1A1S31S3fS1aA1A4A2A2").
Definition s7s_0 : ltac2:(tb__ "0|0|
S37") := ltac2:(tb__ "0|0|
S36S26S1S35A1S1S15VW;Vst;Vtmax;A3A1A3").
Lemma ENT7s_0 : ltac2:(tb__ "0|2|
S6S7S2S3S13VW;Vst;Vtmax;A3M0S3dS1G0A1M1S3cS1eS23G1A1S31S3fS1aA1A4A2A2S15VW;Vst;Vtmax;A3S33A3S8A3").
Proof. unfold k6_0, s7s_0. memo_rw (E6s W st tmax) memo_1. memo_rw (C7 W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID7s_0 : ltac2:(tb__ "0|0|
S6S7S38S33S26A2S8A3").
Proof. unfold s7s_0. memo_rw (C7 W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma G6l_0 : ltac2:(tb__ "0|0|
S45S1fS1cS21S1S16VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E6l W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W6l_0 : ltac2:(tb__ "0|0|
S6S7S25S1S14VW;Vst;Vtmax;A3A1A1S8A3").
Proof. memo_rw (C6l W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D6l_0 : ltac2:(tb__ "0|4|
S6ScSeSbSeS22S22A2M0A1M1SbS1fA1M2A2M3A1S3bS1S16VW;Vst;Vtmax;A3A1S1S14VW;Vst;Vtmax;A3A1A2SdG3SfG1G2S9G0SfS22S22S49S1dA4SaG0A1A3SaS1fA1A4A2A3").
Proof. memo_rw (E6l W st tmax) memo_2. memo_rw (C6l W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX6l_0 : ltac2:(tb__ "0|0|
S6S2aS20S1S14VW;Vst;Vtmax;A3A1A1S20S1S16VW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C6l W st tmax) memo_4. memo_rw (E6l W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert6l_0 : ltac2:(tb__ "0|1|
S6S7S39S27Ufa0S9S29Zde378SaS29A1A3S26S9S0S14VW;Vst;Vtmax;A3SaS0A1M0A3S9S0S19VW;Vst;Vtmax;A3G0A3A6S8A3").
Proof. memo_rw (C6l W st tmax) memo_4. memo_rw (E6m W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W6m_0 : ltac2:(tb__ "0|0|
S6S7S25S1S12VW;Vst;Vtmax;A3A1A1S8A3").
Proof. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D6m_0 : ltac2:(tb__ "0|4|
S6ScSeSbSeS22S22A2M0A1M1SbS1fA1M2A2M3A1S3bS1S19VW;Vst;Vtmax;A3A1S1S12VW;Vst;Vtmax;A3A1A2SdG3SfG1G2SaG0A1SaS1fA1A4A2A3").
Proof. memo_rw (E6m W st tmax) memo_5. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX6m_0 : ltac2:(tb__ "0|0|
S6S2aS20S1S12VW;Vst;Vtmax;A3A1A1S20S1S19VW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C6m W st tmax) memo_6. memo_rw (E6m W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s6_0 : ltac2:(tb__ "0|0|
S37") := ltac2:(tb__ "0|0|
S36P1S1S12VW;Vst;Vtmax;A3A1S1S2bA1A3").
Definition R6_0 : ltac2:(tb__ "0|0|
SbS1eA1") := ltac2:(tb__ "0|1|
ScSbS1eA1M0A1G0Lx;S41S12VW;Vst;Vtmax;A3S2bS2eA3G0R1LR;SaS1eA1Xcx2").
Definition T6_0 : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|0|
S42S2eS2bS3aS2cA1S12VW;Vst;Vtmax;A3S2fA5").
Definition sd6_0 : ltac2:(tb__ "0|0|
S37") := ltac2:(tb__ "0|0|
S36S26S1S3eS30S21S1S12VW;Vst;Vtmax;A3A1A1A2A1S1S17VW;Vst;Vtmax;A3A1A3").
Lemma He6_0 : ltac2:(tb__ "0|1|
S6ScSbS1eA1M0A1S41S12VW;Vst;Vtmax;A3S2bS2eA3SdG0S2fA2A3").
Proof. unfold s6_0, R6_0. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk6_0 : ltac2:(tb__ "0|0|
S6S7S43S12VW;Vst;Vtmax;A3S2bS2eS2fS48S5S0S4S2dA4A5S8A3").
Proof. unfold s6_0, R6_0. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT6_0 : ltac2:(tb__ "0|0|
S6S0S42S2eS2bS3aS2cA1S12VW;Vst;Vtmax;A3S2fA5S30A3").
Proof. reflexivity. Qed.
Lemma FBC6_0 : ltac2:(tb__ "0|1|
S6S7S44S1fS24S20S1S12VW;Vst;Vtmax;A3A1M0A1A1S21G0A1A3S8A3").
Proof. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT6_0 : ltac2:(tb__ "0|0|
S6S7S44S1fS24S20S1S30A1A1A1S21S1S12VW;Vst;Vtmax;A3A1A1A3S8A3").
Proof. unfold T6_0. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT6_0 : ltac2:(tb__ "0|0|
S6S7S2S3eS30S21S1S12VW;Vst;Vtmax;A3A1A1A2S17VW;Vst;Vtmax;A3S34A3S8A3").
Proof. unfold T6_0, sd6_0. memo_rw (C6m W st tmax) memo_6. memo_rw (C6b W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID6_0 : ltac2:(tb__ "0|0|
S6S7S38S34S26A2S8A3").
Proof. unfold sd6_0. memo_rw (C6b W st tmax) memo_7. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC6_0 : ltac2:(tb__ "0|0|
S4aS26S20S1S12VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C6m W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert6b_0 : ltac2:(tb__ "0|1|
S6S7S39S27Ufa0S9S29Z3c698SaS29A1A3S26S9S0S17VW;Vst;Vtmax;A3SaS0A1M0A3S9S0S18VW;Vst;Vtmax;A3G0A3A6S8A3").
Proof. memo_rw (C6b W st tmax) memo_7. memo_rw (E6j W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s7j_0 : ltac2:(tb__ "0|0|
S37") := ltac2:(tb__ "0|0|
S36S26S1S18VW;Vst;Vtmax;A3A1S1S15VW;Vst;Vtmax;A3A1A3").
Lemma ENT7j_0 : ltac2:(tb__ "0|0|
S6S7S2S18VW;Vst;Vtmax;A3S15VW;Vst;Vtmax;A3S32A3S8A3").
Proof. unfold s7j_0. memo_rw (E6j W st tmax) memo_8. memo_rw (C7 W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID7j_0 : ltac2:(tb__ "0|0|
S6S7S38S32S26A2S8A3").
Proof. unfold s7j_0. memo_rw (C7 W st tmax) memo_3. memo_rw (E6j W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS7iW2.

