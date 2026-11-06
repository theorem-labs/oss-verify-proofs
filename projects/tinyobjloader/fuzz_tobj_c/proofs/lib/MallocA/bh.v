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
Module SpineMallocS9i.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sobj"; "sprop"; "ss_facts"; "ss_next"; "sv"; "SLit"; "sprop_below"; "ss_objs"; "SPBranch"; "SPNot"; "SVar"; "swf"; "@Corelib.Init.Datatypes"; "option"; "bool"; "true"; "nil"; "list"; "cons"; "nat"; "Some"; "prod"; "pair"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "memset_entryA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bh.SpineMallocS9i.INST"; "CC8ma_0"; "CC8map_0"; "X8b_0"; "X8bp_0"; "U8b_0"; "U8bp_0"; "s8_0"; "s8b_0"; "s8bp_0"; "s8p_0"; "R8_0"; "R8b_0"; "R8bp_0"; "R8p_0"; "T8_0"; "T8b_0"; "T8bp_0"; "T8p_0"; "i9_0"; "i9p_0"; "SM_0"; "SMp_0"; "S8s_0"; "S8sp_0"; "U8b0_0"; "U8b0p_0"; "i8_0"; "i8p_0"; "s9m_0"; "s9mp_0"; "sd8_0"; "sd8b_0"; "sd8bp_0"; "sd8p_0"; "SU_0"; "SUp_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "C9"; "C9p"; "E8a"; "E8b"; "E8pa"; "E8pb"; "upd"; "MSENT"; "ube"; "C8"; "C8p"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"].
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
S4cS1S1S6S1S61VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C8]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S5aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E8a W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E8a] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E8a]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S5bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E8b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E8b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E8b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|1|
S4cS1S56S18S1cS1aScA2A1S18S8A1S15S18S9A1S1Ffacts;Freset;Fobjs;Fru;Fpc;FE;M0G0S6G0S5eVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (upd W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [upd] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [upd]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S58VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C9]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S62VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C8p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S5cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E8pa W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E8pa] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E8pa]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S5dVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E8pb W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E8pb] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [E8pb]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S59VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C9p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma Cert8_0 : ltac2:(tb__ "0|1|
S6S15S69S24Ufa0S19S56Zde378S19S56Z3c8c0S17S56A1A3A3S23S19S1S61VW;Vst;Vtmax;A3S17S1A1M0A3S19S1S5aVW;Vst;Vtmax;A3S19S1S5bVW;Vst;Vtmax;A3G0A3A3A6S16A3").
Proof. memo_rw (C8 W st tmax) memo_0. memo_rw (E8a W st tmax) memo_1. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition CC8ma_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|1|
S5eVW;Vst;Vtmax;S5aVW;Vst;Vtmax;A3S5fS19S1cS1aScA2M0S1dS1aScUaS60A4S17G0A1A3S17S8A1S1eS17S9A1A9").
Lemma HCC8ma_0 : ltac2:(tb__ "0|1|
S6S1S25S5eVW;Vst;Vtmax;S5aVW;Vst;Vtmax;A3S5fS19S1cS1aScA2M0S1dS1aScUaS60A4S17G0A1A3S17S8A1S1eS17S9A1A9A3").
Proof. reflexivity. Qed.
Lemma W8a_0 : ltac2:(tb__ "0|0|
S6S15S13S0S25A1A1S16A3").
Proof. unfold CC8ma_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D8a_0 : ltac2:(tb__ "0|4|
S6S14S1cS18S1cScScA2M0A1M1S18S9A1M2A2M3A1S67S0S5aVW;Vst;Vtmax;A3A1S0S25A1A2S1bG3S1dG1G2S17G0A1S17S9A1A4A2A3").
Proof. unfold CC8ma_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S6S57SbS0S25A1A1SbS0S5aVW;Vst;Vtmax;A3A1A1A3").
Proof. unfold CC8ma_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s8_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49P1S0S25A1S0S20A1A3").
Definition R8_0 : ltac2:(tb__ "0|0|
S18S8A1") := ltac2:(tb__ "0|1|
S14S18S8A1M0A1G0Lx;S51S25S20S2bA3G0R1LR;S17S8A1X14x2").
Definition T8_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S52S2bS20S4dS54S21A1A1S25S2fA5").
Definition sd8_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49S23S0S50S33SaS0S25A1A1A2A1S0S58VW;Vst;Vtmax;A3A1A3").
Lemma He8_0 : ltac2:(tb__ "0|1|
S6S14S18S8A1M0A1S51S25S20S2bA3S1bG0S2fA2A3").
Proof. unfold CC8ma_0, s8_0, R8_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk8_0 : ltac2:(tb__ "0|0|
S6S15S53S25S20S2bS2fS64S5S1S4S22A4A5S16A3").
Proof. unfold CC8ma_0, s8_0, R8_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT8_0 : ltac2:(tb__ "0|0|
S6S1S52S2bS20S4dS54S21A1A1S25S2fA5S33A3").
Proof. reflexivity. Qed.
Lemma FBC8_0 : ltac2:(tb__ "0|1|
S6S15S55S9SeSbS0S25A1M0A1A1SaG0A1A3S16A3").
Proof. unfold CC8ma_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT8_0 : ltac2:(tb__ "0|0|
S6S15S55S9SeSbS0S33A1A1A1SaS0S25A1A1A3S16A3").
Proof. unfold CC8ma_0, T8_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT8_0 : ltac2:(tb__ "0|0|
S6S15S3S50S33SaS0S25A1A1A2S58VW;Vst;Vtmax;A3S43A3S16A3").
Proof. unfold CC8ma_0, T8_0, sd8_0. memo_rw (C9 W st tmax) memo_4. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID8_0 : ltac2:(tb__ "0|0|
S6S15S4bS43S23A2S16A3").
Proof. unfold sd8_0. memo_rw (C9 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC8_0 : ltac2:(tb__ "0|0|
S65S23SbS0S25A1A1A2").
Proof. apply Pos.leb_le. unfold CC8ma_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition i8_0 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S63S1fS8SfS0S5bVW;Vst;Vtmax;A3A1A1A2U6A2").
Definition S8s_0 : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S14S7A1S7Lx;S4eS0S5bVW;Vst;Vtmax;A3A1M0S3fSdZ1000A1A3S7R1LSx;G0X14x2").
Lemma SPL8_0 : ltac2:(tb__ "0|0|
S6S14S7A1S4eS0S5bVW;Vst;Vtmax;A3A1S3fSdZ1000A1A3S1bS7S3bA2A3").
Proof. unfold i8_0, S8s_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X8b_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S2S5bVW;Vst;Vtmax;A3S3bA2").
Definition s8b_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49P1S0S27A1S0S20A1A3").
Definition R8b_0 : ltac2:(tb__ "0|0|
S18S8A1") := ltac2:(tb__ "0|1|
S14S18S8A1M0A1G0Lx;S51S27S20S2cA3G0R1LR;S17S8A1X14x2").
Definition T8b_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S52S2cS20S4dS54S21A1A1S27S30A5").
Lemma He8b_0 : ltac2:(tb__ "0|1|
S6S14S18S8A1M0A1S51S27S20S2cA3S1bG0S30A2A3").
Proof. unfold X8b_0, s8b_0, R8b_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S6S15S53S27S20S2cS30S64S5S1S4S22A4A5S16A3").
Proof. unfold X8b_0, s8b_0, R8b_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S6S1S52S2cS20S4dS54S21A1A1S27S30A5S34A3").
Proof. reflexivity. Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S6S15S55S9SeSbS0S27A1M0A1A1SaG0A1A3S16A3").
Proof. unfold X8b_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S6S15S55S9SeSbS0S34A1A1A1SaS0S27A1A1A3S16A3").
Proof. unfold X8b_0, T8b_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S65S23SbS0S27A1A1A2").
Proof. apply Pos.leb_le. unfold X8b_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition i9_0 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S63S1fS8SfS0S58VW;Vst;Vtmax;A3A1A1A2U6A2").
Definition U8b0_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S68S19S9S11S10S66S12PcA1SdZ1000A1A3A1S17S9A1A3S58VW;Vst;Vtmax;A3A2").
Definition SU_0 : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S14S7A1S7Lx;S4eS0S3dA1M0S37SdZ1000A1A3S7R1LSx;G0X14x2").
Lemma SPLU_0 : ltac2:(tb__ "0|0|
S6S14S7A1S4eS0S3dA1S37SdZ1000A1A3S1bS7S47A2A3").
Proof. unfold i9_0, U8b0_0, SU_0. memo_rw (C9 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition U8b_0 := ax_setS U8b0_0 SU_0.
Definition sd8b_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49S23S0S50S34SaS0S27A1A1A2A1S0S29A1A3").
Lemma ENTU_0 : ltac2:(tb__ "0|0|
S6S15S3S50S34SaS0S27A1A1A2S29S44A3S16A3").
Proof. unfold X8b_0, T8b_0, U8b_0, sd8b_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDU_0 : ltac2:(tb__ "0|0|
S6S15S4bS44S23A2S16A3").
Proof. unfold sd8b_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition SM_0 : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S14S7A1S7Lx;S4fS0S29A1M0S37A2S7R1LSx;G0X14x2").
Lemma MRG_0 : ltac2:(tb__ "0|0|
S6S14S7A1S4fS0S29A1S37A2S1bS7S39A2A3").
Proof. unfold i9_0, U8b_0, SM_0. memo_rw (C9 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s9m_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49S23S0S2S29S39A2A1S0S58VW;Vst;Vtmax;A3A1A3").
Lemma ENTM_0 : ltac2:(tb__ "0|0|
S6S15S3S2S29S39A2S58VW;Vst;Vtmax;A3S41A3S16A3").
Proof. unfold U8b_0, SM_0, s9m_0. memo_rw (C9 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDM_0 : ltac2:(tb__ "0|0|
S6S15S4bS41S23A2S16A3").
Proof. unfold s9m_0. memo_rw (C9 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert8p_0 : ltac2:(tb__ "0|1|
S6S15S69S24Ufa0S19S56Zde378S19S56Z3c8c0S17S56A1A3A3S23S19S1S62VW;Vst;Vtmax;A3S17S1A1M0A3S19S1S5cVW;Vst;Vtmax;A3S19S1S5dVW;Vst;Vtmax;A3G0A3A3A6S16A3").
Proof. memo_rw (C8p W st tmax) memo_5. memo_rw (E8pa W st tmax) memo_6. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition CC8map_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|1|
S5eVW;Vst;Vtmax;S5cVW;Vst;Vtmax;A3S5fS19S1cS1aScA2M0S1dS1aScUaS60A4S17G0A1A3S17S8A1S1eS17S9A1A9").
Lemma HCC8map_0 : ltac2:(tb__ "0|1|
S6S1S26S5eVW;Vst;Vtmax;S5cVW;Vst;Vtmax;A3S5fS19S1cS1aScA2M0S1dS1aScUaS60A4S17G0A1A3S17S8A1S1eS17S9A1A9A3").
Proof. reflexivity. Qed.
Lemma W8ap_0 : ltac2:(tb__ "0|0|
S6S15S13S0S26A1A1S16A3").
Proof. unfold CC8map_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D8ap_0 : ltac2:(tb__ "0|4|
S6S14S1cS18S1cScScA2M0A1M1S18S9A1M2A2M3A1S67S0S5cVW;Vst;Vtmax;A3A1S0S26A1A2S1bG3S1dG1G2S17G0A1S17S9A1A4A2A3").
Proof. unfold CC8map_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX8ap_0 : ltac2:(tb__ "0|0|
S6S57SbS0S26A1A1SbS0S5cVW;Vst;Vtmax;A3A1A1A3").
Proof. unfold CC8map_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s8p_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49P1S0S26A1S0S20A1A3").
Definition R8p_0 : ltac2:(tb__ "0|0|
S18S8A1") := ltac2:(tb__ "0|1|
S14S18S8A1M0A1G0Lx;S51S26S20S2eA3G0R1LR;S17S8A1X14x2").
Definition T8p_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S52S2eS20S4dS54S21A1A1S26S32A5").
Definition sd8p_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49S23S0S50S36SaS0S26A1A1A2A1S0S59VW;Vst;Vtmax;A3A1A3").
Lemma He8p_0 : ltac2:(tb__ "0|1|
S6S14S18S8A1M0A1S51S26S20S2eA3S1bG0S32A2A3").
Proof. unfold CC8map_0, s8p_0, R8p_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk8p_0 : ltac2:(tb__ "0|0|
S6S15S53S26S20S2eS32S64S5S1S4S22A4A5S16A3").
Proof. unfold CC8map_0, s8p_0, R8p_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT8p_0 : ltac2:(tb__ "0|0|
S6S1S52S2eS20S4dS54S21A1A1S26S32A5S36A3").
Proof. reflexivity. Qed.
Lemma FBC8p_0 : ltac2:(tb__ "0|1|
S6S15S55S9SeSbS0S26A1M0A1A1SaG0A1A3S16A3").
Proof. unfold CC8map_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT8p_0 : ltac2:(tb__ "0|0|
S6S15S55S9SeSbS0S36A1A1A1SaS0S26A1A1A3S16A3").
Proof. unfold CC8map_0, T8p_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT8p_0 : ltac2:(tb__ "0|0|
S6S15S3S50S36SaS0S26A1A1A2S59VW;Vst;Vtmax;A3S46A3S16A3").
Proof. unfold CC8map_0, T8p_0, sd8p_0. memo_rw (C9p W st tmax) memo_8. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID8p_0 : ltac2:(tb__ "0|0|
S6S15S4bS46S23A2S16A3").
Proof. unfold sd8p_0. memo_rw (C9p W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC8p_0 : ltac2:(tb__ "0|0|
S65S23SbS0S26A1A1A2").
Proof. apply Pos.leb_le. unfold CC8map_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition i8p_0 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S63S1fS8SfS0S5dVW;Vst;Vtmax;A3A1A1A2U6A2").
Definition S8sp_0 : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S14S7A1S7Lx;S4eS0S5dVW;Vst;Vtmax;A3A1M0S40SdZ1000A1A3S7R1LSx;G0X14x2").
Lemma SPL8p_0 : ltac2:(tb__ "0|0|
S6S14S7A1S4eS0S5dVW;Vst;Vtmax;A3A1S40SdZ1000A1A3S1bS7S3cA2A3").
Proof. unfold i8p_0, S8sp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X8bp_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S2S5dVW;Vst;Vtmax;A3S3cA2").
Definition s8bp_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49P1S0S28A1S0S20A1A3").
Definition R8bp_0 : ltac2:(tb__ "0|0|
S18S8A1") := ltac2:(tb__ "0|1|
S14S18S8A1M0A1G0Lx;S51S28S20S2dA3G0R1LR;S17S8A1X14x2").
Definition T8bp_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S52S2dS20S4dS54S21A1A1S28S31A5").
Lemma He8bp_0 : ltac2:(tb__ "0|1|
S6S14S18S8A1M0A1S51S28S20S2dA3S1bG0S31A2A3").
Proof. unfold X8bp_0, s8bp_0, R8bp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk8bp_0 : ltac2:(tb__ "0|0|
S6S15S53S28S20S2dS31S64S5S1S4S22A4A5S16A3").
Proof. unfold X8bp_0, s8bp_0, R8bp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT8bp_0 : ltac2:(tb__ "0|0|
S6S1S52S2dS20S4dS54S21A1A1S28S31A5S35A3").
Proof. reflexivity. Qed.
Lemma FBC8bp_0 : ltac2:(tb__ "0|1|
S6S15S55S9SeSbS0S28A1M0A1A1SaG0A1A3S16A3").
Proof. unfold X8bp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT8bp_0 : ltac2:(tb__ "0|0|
S6S15S55S9SeSbS0S35A1A1A1SaS0S28A1A1A3S16A3").
Proof. unfold X8bp_0, T8bp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC8bp_0 : ltac2:(tb__ "0|0|
S65S23SbS0S28A1A1A2").
Proof. apply Pos.leb_le. unfold X8bp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition i9p_0 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S63S1fS8SfS0S59VW;Vst;Vtmax;A3A1A1A2U6A2").
Definition U8b0p_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S68S19S9S11S10S66S12PcA1SdZ1000A1A3A1S17S9A1A3S59VW;Vst;Vtmax;A3A2").
Definition SUp_0 : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S14S7A1S7Lx;S4eS0S3eA1M0S38SdZ1000A1A3S7R1LSx;G0X14x2").
Lemma SPLUp_0 : ltac2:(tb__ "0|0|
S6S14S7A1S4eS0S3eA1S38SdZ1000A1A3S1bS7S48A2A3").
Proof. unfold i9p_0, U8b0p_0, SUp_0. memo_rw (C9p W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition U8bp_0 := ax_setS U8b0p_0 SUp_0.
Definition sd8bp_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49S23S0S50S35SaS0S28A1A1A2A1S0S2aA1A3").
Lemma ENTUp_0 : ltac2:(tb__ "0|0|
S6S15S3S50S35SaS0S28A1A1A2S2aS45A3S16A3").
Proof. unfold X8bp_0, T8bp_0, U8bp_0, sd8bp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDUp_0 : ltac2:(tb__ "0|0|
S6S15S4bS45S23A2S16A3").
Proof. unfold sd8bp_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition SMp_0 : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S14S7A1S7Lx;S4fS0S2aA1M0S38A2S7R1LSx;G0X14x2").
Lemma MRGp_0 : ltac2:(tb__ "0|0|
S6S14S7A1S4fS0S2aA1S38A2S1bS7S3aA2A3").
Proof. unfold i9p_0, U8bp_0, SMp_0. memo_rw (C9p W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s9mp_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49S23S0S2S2aS3aA2A1S0S59VW;Vst;Vtmax;A3A1A3").
Lemma ENTMp_0 : ltac2:(tb__ "0|0|
S6S15S3S2S2aS3aA2S59VW;Vst;Vtmax;A3S42A3S16A3").
Proof. unfold U8bp_0, SMp_0, s9mp_0. memo_rw (C9p W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDMp_0 : ltac2:(tb__ "0|0|
S6S15S4bS42S23A2S16A3").
Proof. unfold s9mp_0. memo_rw (C9p W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS9i.

(* [comment removed for export] *)
Module SpineMallocS8iW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "SVar"; "ss_next"; "SPBranch"; "SLit"; "swf"; "SPNot"; "SPUle"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "option"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "C7p"; "C8"; "C8p"; "F_gen"; "V_CLS"; "V_ND"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "n8e"; "C7"; "BP"; "LPe"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8"; "E7c1'"; "E7c2'"; "E7q1'"; "E7q2'"; "a0e7"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "tab_ok"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bh.SpineMallocS8iW2.INST"; "s8a_0"; "s8b_0"; "s8c_0"; "s8d_0"].
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
S17S1S1S0S1S2aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C7 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C7] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C7]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7c1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7c1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7c1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7c2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7c2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7c2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S17S4S4S0S4S25VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (creg7a W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [creg7a] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [creg7a]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S17S4S4S0S4S26VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (creg7b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [creg7b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [creg7b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S17S1S1S0S1S2fU2Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7c1' 2%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7c1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7c1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S17S1S1S0S1S30U2Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7c2' 2%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7c2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7c2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S17S1S1S0S1S20VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C8]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1fVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C7p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C7p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C7p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1dVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7q1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7q1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7q1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1eVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7q2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7q2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7q2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S17S4S4S0S4S27VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (creg7c W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [creg7c] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [creg7c]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_13 : ltac2:(tb__ "0|0|
S17S4S4S0S4S28VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (creg7d W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [creg7d] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [creg7d]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_14 : ltac2:(tb__ "0|0|
S17S1S1S0S1S31U2Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7q1' 2%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7q1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7q1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_15 : ltac2:(tb__ "0|0|
S17S1S1S0S1S32U2Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7q2' 2%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7q2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7q2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_16 : ltac2:(tb__ "0|0|
S17S1S1S0S1S21VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C8p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma Cert7_0 : ltac2:(tb__ "0|1|
S0SeS45S19Ufa0S10S34Z3c728S10S34Z3c870S11S34A1A3A3S18S10S1S2aVW;Vst;Vtmax;A3S11S1A1M0A3S10S1S1aVW;Vst;Vtmax;A3S10S1S1bVW;Vst;Vtmax;A3S10S1S1cVW;Vst;Vtmax;A3G0A3A3A3A6SfA3").
Proof. memo_rw (C7 W st tmax) memo_0. memo_rw (E7c1 W st tmax) memo_1. memo_rw (E7c2 W st tmax) memo_2. memo_rw (E7p W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OV7a_0 : ltac2:(tb__ "0|0|
S0SeS41P9dS25VW;Vst;Vtmax;A3A2SfA3").
Proof. memo_rw (creg7a W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OV7b_0 : ltac2:(tb__ "0|0|
S0SeS41P9dS26VW;Vst;Vtmax;A3A2SfA3").
Proof. memo_rw (creg7b W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TAB7a_0 : ltac2:(tb__ "0|0|
S0SeS42P9dS25VW;Vst;Vtmax;A3S40Z208S43S44S37S38S39S37S3aA1A1A1A1A1A1A5SfA3").
Proof. memo_rw (creg7a W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TAB7b_0 : ltac2:(tb__ "0|0|
S0SeS42P9dS26VW;Vst;Vtmax;A3S40Z18U3eA5SfA3").
Proof. memo_rw (creg7b W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W7a_0 : ltac2:(tb__ "0|0|
S0SeSbS2S2fU2Vst;Vtmax;A3A1A1SfA3").
Proof. memo_rw (E7c1' 2%nat st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W7b_0 : ltac2:(tb__ "0|0|
S0SeSbS2S30U2Vst;Vtmax;A3A1A1SfA3").
Proof. memo_rw (E7c2' 2%nat st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D7a_0 : ltac2:(tb__ "0|4|
S0S16S14S12S14S4S4A2M0A1M1S12S5A1M2A2M3A1S36S2S1aVW;Vst;Vtmax;A3A1S2S2fU2Vst;Vtmax;A3A1A2S15G3S13G1G2S10G0S13S4S4S25VW;Vst;Vtmax;A3S7S23A1A4S11G0A1A3S11S5A1A4A2A3").
Proof. memo_rw (E7c1 W st tmax) memo_1. memo_rw (E7c1' 2%nat st tmax) memo_6. memo_rw (creg7a W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D7b_0 : ltac2:(tb__ "0|4|
S0S16S14S12S14S4S4A2M0A1M1S12S5A1M2A2M3A1S36S2S1bVW;Vst;Vtmax;A3A1S2S30U2Vst;Vtmax;A3A1A2S15G3S13G1G2S10G0S13S4S4S26VW;Vst;Vtmax;A3S7S23A1A4S11G0A1A3S11S5A1A4A2A3").
Proof. memo_rw (E7c2 W st tmax) memo_2. memo_rw (E7c2' 2%nat st tmax) memo_7. memo_rw (creg7b W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S35S8S2S2fU2Vst;Vtmax;A3A1A1S8S2S1aVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E7c1' 2%nat st tmax) memo_6. memo_rw (E7c1 W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S35S8S2S30U2Vst;Vtmax;A3A1A1S8S2S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E7c2' 2%nat st tmax) memo_7. memo_rw (E7c2 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma G7a_0 : ltac2:(tb__ "0|0|
S2eS5S22S6S2S1aVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E7c1 W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma G7b_0 : ltac2:(tb__ "0|0|
S2eS5S22S6S2S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E7c2 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F7a_0 : ltac2:(tb__ "0|0|
S2dS5S9S3bSaZ200A1S7S24A1A3S6S2S1aVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E7c1 W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F7b_0 : ltac2:(tb__ "0|0|
S2dS5ScS9S3bSaZ200A1S7S24A1A3A1S6S2S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E7c2 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s8a_0 : ltac2:(tb__ "0|0|
S3e") := ltac2:(tb__ "0|0|
S3dS18S2S2fU2Vst;Vtmax;A3A1S2S20VW;Vst;Vtmax;A3A1A3").
Definition s8b_0 : ltac2:(tb__ "0|0|
S3e") := ltac2:(tb__ "0|0|
S3dS18S2S30U2Vst;Vtmax;A3A1S2S20VW;Vst;Vtmax;A3A1A3").
Lemma ENT8a_0 : ltac2:(tb__ "0|0|
S0SeS3S2fU2Vst;Vtmax;A3S20VW;Vst;Vtmax;A3S46A3SfA3").
Proof. unfold s8a_0. memo_rw (E7c1' 2%nat st tmax) memo_6. memo_rw (C8 W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT8b_0 : ltac2:(tb__ "0|0|
S0SeS3S30U2Vst;Vtmax;A3S20VW;Vst;Vtmax;A3S47A3SfA3").
Proof. unfold s8b_0. memo_rw (E7c2' 2%nat st tmax) memo_7. memo_rw (C8 W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID8a_0 : ltac2:(tb__ "0|0|
S0SeS3fS46S18A2SfA3").
Proof. unfold s8a_0. memo_rw (C8 W st tmax) memo_8. memo_rw (E7c1' 2%nat st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID8b_0 : ltac2:(tb__ "0|0|
S0SeS3fS47S18A2SfA3").
Proof. unfold s8b_0. memo_rw (C8 W st tmax) memo_8. memo_rw (E7c2' 2%nat st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma G7p_0 : ltac2:(tb__ "0|0|
S2eS5S22S6S2S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E7p W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F7p_0 : ltac2:(tb__ "0|0|
S2dS5ScS9S3cS7PcA1S29A3A1S6S2S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E7p W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W7p_0 : ltac2:(tb__ "0|0|
S0SeSbS2S1fVW;Vst;Vtmax;A3A1A1SfA3").
Proof. memo_rw (C7p W st tmax) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D7p_0 : ltac2:(tb__ "0|4|
S0S16S14S12S14S4S4A2M0A1M1S12S5A1M2A2M3A1S36S2S1cVW;Vst;Vtmax;A3A1S2S1fVW;Vst;Vtmax;A3A1A2S15G3S13G1G2S10G0S13S4S4S33S2bA4S11G0A1A3S10S5SdSaZ1A1S2cA2S11S5A1A3A4A2A3").
Proof. memo_rw (E7p W st tmax) memo_3. memo_rw (C7p W st tmax) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX7p_0 : ltac2:(tb__ "0|0|
S0S35S8S2S1fVW;Vst;Vtmax;A3A1A1S8S2S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C7p W st tmax) memo_9. memo_rw (E7p W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F7an_0 : ltac2:(tb__ "0|0|
S2dS5S9S3cS7PcA1S29A3S6S2S1aVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E7c1 W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F7bn_0 : ltac2:(tb__ "0|0|
S2dS5S9S3cS7PcA1S29A3S6S2S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E7c2 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert7p_0 : ltac2:(tb__ "0|1|
S0SeS45S19Ufa0S10S34Z3c870S11S34A1A3S18S10S1S1fVW;Vst;Vtmax;A3S11S1A1M0A3S10S1S1dVW;Vst;Vtmax;A3S10S1S1eVW;Vst;Vtmax;A3G0A3A3A6SfA3").
Proof. memo_rw (C7p W st tmax) memo_9. memo_rw (E7q1 W st tmax) memo_10. memo_rw (E7q2 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OV7c_0 : ltac2:(tb__ "0|0|
S0SeS41P9dS27VW;Vst;Vtmax;A3A2SfA3").
Proof. memo_rw (creg7c W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OV7d_0 : ltac2:(tb__ "0|0|
S0SeS41P9dS28VW;Vst;Vtmax;A3A2SfA3").
Proof. memo_rw (creg7d W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TAB7c_0 : ltac2:(tb__ "0|0|
S0SeS42P9dS27VW;Vst;Vtmax;A3S40Z208S43S44S37S38S39S37S3aA1A1A1A1A1A1A5SfA3").
Proof. memo_rw (creg7c W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TAB7d_0 : ltac2:(tb__ "0|0|
S0SeS42P9dS28VW;Vst;Vtmax;A3S40Z18U3eA5SfA3").
Proof. memo_rw (creg7d W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W7c_0 : ltac2:(tb__ "0|0|
S0SeSbS2S31U2Vst;Vtmax;A3A1A1SfA3").
Proof. memo_rw (E7q1' 2%nat st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W7d_0 : ltac2:(tb__ "0|0|
S0SeSbS2S32U2Vst;Vtmax;A3A1A1SfA3").
Proof. memo_rw (E7q2' 2%nat st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D7c_0 : ltac2:(tb__ "0|4|
S0S16S14S12S14S4S4A2M0A1M1S12S5A1M2A2M3A1S36S2S1dVW;Vst;Vtmax;A3A1S2S31U2Vst;Vtmax;A3A1A2S15G3S13G1G2S10G0S13S4S4S27VW;Vst;Vtmax;A3S7S23A1A4S11G0A1A3S11S5A1A4A2A3").
Proof. memo_rw (E7q1 W st tmax) memo_10. memo_rw (E7q1' 2%nat st tmax) memo_14. memo_rw (creg7c W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D7d_0 : ltac2:(tb__ "0|4|
S0S16S14S12S14S4S4A2M0A1M1S12S5A1M2A2M3A1S36S2S1eVW;Vst;Vtmax;A3A1S2S32U2Vst;Vtmax;A3A1A2S15G3S13G1G2S10G0S13S4S4S28VW;Vst;Vtmax;A3S7S23A1A4S11G0A1A3S11S5A1A4A2A3").
Proof. memo_rw (E7q2 W st tmax) memo_11. memo_rw (E7q2' 2%nat st tmax) memo_15. memo_rw (creg7d W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX7c_0 : ltac2:(tb__ "0|0|
S0S35S8S2S31U2Vst;Vtmax;A3A1A1S8S2S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E7q1' 2%nat st tmax) memo_14. memo_rw (E7q1 W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX7d_0 : ltac2:(tb__ "0|0|
S0S35S8S2S32U2Vst;Vtmax;A3A1A1S8S2S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E7q2' 2%nat st tmax) memo_15. memo_rw (E7q2 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma G7c_0 : ltac2:(tb__ "0|0|
S2eS5S22S6S2S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E7q1 W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma G7d_0 : ltac2:(tb__ "0|0|
S2eS5S22S6S2S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E7q2 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F7c_0 : ltac2:(tb__ "0|0|
S2dS5S9S3bSaZ200A1S7S24A1A3S6S2S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E7q1 W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F7d_0 : ltac2:(tb__ "0|0|
S2dS5ScS9S3bSaZ200A1S7S24A1A3A1S6S2S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E7q2 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s8c_0 : ltac2:(tb__ "0|0|
S3e") := ltac2:(tb__ "0|0|
S3dS18S2S31U2Vst;Vtmax;A3A1S2S21VW;Vst;Vtmax;A3A1A3").
Definition s8d_0 : ltac2:(tb__ "0|0|
S3e") := ltac2:(tb__ "0|0|
S3dS18S2S32U2Vst;Vtmax;A3A1S2S21VW;Vst;Vtmax;A3A1A3").
Lemma ENT8c_0 : ltac2:(tb__ "0|0|
S0SeS3S31U2Vst;Vtmax;A3S21VW;Vst;Vtmax;A3S48A3SfA3").
Proof. unfold s8c_0. memo_rw (E7q1' 2%nat st tmax) memo_14. memo_rw (C8p W st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT8d_0 : ltac2:(tb__ "0|0|
S0SeS3S32U2Vst;Vtmax;A3S21VW;Vst;Vtmax;A3S49A3SfA3").
Proof. unfold s8d_0. memo_rw (E7q2' 2%nat st tmax) memo_15. memo_rw (C8p W st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID8c_0 : ltac2:(tb__ "0|0|
S0SeS3fS48S18A2SfA3").
Proof. unfold s8c_0. memo_rw (C8p W st tmax) memo_16. memo_rw (E7q1' 2%nat st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID8d_0 : ltac2:(tb__ "0|0|
S0SeS3fS49S18A2SfA3").
Proof. unfold s8d_0. memo_rw (C8p W st tmax) memo_16. memo_rw (E7q2' 2%nat st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS8iW2.

(* [comment removed for export] *)
Module SpineMallocS9iW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sobj"; "sprop"; "ss_facts"; "ss_next"; "sv"; "SLit"; "sprop_below"; "ss_objs"; "SPBranch"; "SPNot"; "SVar"; "swf"; "@Corelib.Init.Datatypes"; "option"; "bool"; "true"; "nil"; "list"; "cons"; "nat"; "Some"; "prod"; "pair"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "memset_entryA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bh.SpineMallocS9iW2.INST"; "CC8ma_0"; "CC8map_0"; "X8b_0"; "X8bp_0"; "U8b_0"; "U8bp_0"; "s8_0"; "s8b_0"; "s8bp_0"; "s8p_0"; "R8_0"; "R8b_0"; "R8bp_0"; "R8p_0"; "T8_0"; "T8b_0"; "T8bp_0"; "T8p_0"; "i9_0"; "i9p_0"; "SM_0"; "SMp_0"; "S8s_0"; "S8sp_0"; "U8b0_0"; "U8b0p_0"; "i8_0"; "i8p_0"; "s9m_0"; "s9mp_0"; "sd8_0"; "sd8b_0"; "sd8bp_0"; "sd8p_0"; "SU_0"; "SUp_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "C9"; "C9p"; "E8a"; "E8b"; "E8pa"; "E8pb"; "upd"; "MSENT"; "ube"; "C8"; "C8p"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"].
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
S4cS1S1S6S1S61VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C8]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S5aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E8a W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E8a] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E8a]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S5bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E8b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E8b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E8b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|1|
S4cS1S56S18S1cS1aScA2A1S18S8A1S15S18S9A1S1Ffacts;Freset;Fobjs;Fru;Fpc;FE;M0G0S6G0S5eVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (upd W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [upd] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [upd]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S58VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C9]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S62VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C8p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S5cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E8pa W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E8pa] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E8pa]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S5dVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E8pb W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E8pb] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E8pb]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S59VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C9p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma Cert8_0 : ltac2:(tb__ "0|1|
S6S15S69S24Ufa0S19S56Zde378S19S56Z3c8c0S17S56A1A3A3S23S19S1S61VW;Vst;Vtmax;A3S17S1A1M0A3S19S1S5aVW;Vst;Vtmax;A3S19S1S5bVW;Vst;Vtmax;A3G0A3A3A6S16A3").
Proof. memo_rw (C8 W st tmax) memo_0. memo_rw (E8a W st tmax) memo_1. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition CC8ma_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|1|
S5eVW;Vst;Vtmax;S5aVW;Vst;Vtmax;A3S5fS19S1cS1aScA2M0S1dS1aScUaS60A4S17G0A1A3S17S8A1S1eS17S9A1A9").
Lemma HCC8ma_0 : ltac2:(tb__ "0|1|
S6S1S25S5eVW;Vst;Vtmax;S5aVW;Vst;Vtmax;A3S5fS19S1cS1aScA2M0S1dS1aScUaS60A4S17G0A1A3S17S8A1S1eS17S9A1A9A3").
Proof. reflexivity. Qed.
Lemma W8a_0 : ltac2:(tb__ "0|0|
S6S15S13S0S25A1A1S16A3").
Proof. unfold CC8ma_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D8a_0 : ltac2:(tb__ "0|4|
S6S14S1cS18S1cScScA2M0A1M1S18S9A1M2A2M3A1S67S0S5aVW;Vst;Vtmax;A3A1S0S25A1A2S1bG3S1dG1G2S17G0A1S17S9A1A4A2A3").
Proof. unfold CC8ma_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S6S57SbS0S25A1A1SbS0S5aVW;Vst;Vtmax;A3A1A1A3").
Proof. unfold CC8ma_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s8_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49P1S0S25A1S0S20A1A3").
Definition R8_0 : ltac2:(tb__ "0|0|
S18S8A1") := ltac2:(tb__ "0|1|
S14S18S8A1M0A1G0Lx;S51S25S20S2bA3G0R1LR;S17S8A1X14x2").
Definition T8_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S52S2bS20S4dS54S21A1A1S25S2fA5").
Definition sd8_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49S23S0S50S33SaS0S25A1A1A2A1S0S58VW;Vst;Vtmax;A3A1A3").
Lemma He8_0 : ltac2:(tb__ "0|1|
S6S14S18S8A1M0A1S51S25S20S2bA3S1bG0S2fA2A3").
Proof. unfold CC8ma_0, s8_0, R8_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk8_0 : ltac2:(tb__ "0|0|
S6S15S53S25S20S2bS2fS64S5S1S4S22A4A5S16A3").
Proof. unfold CC8ma_0, s8_0, R8_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT8_0 : ltac2:(tb__ "0|0|
S6S1S52S2bS20S4dS54S21A1A1S25S2fA5S33A3").
Proof. reflexivity. Qed.
Lemma FBC8_0 : ltac2:(tb__ "0|1|
S6S15S55S9SeSbS0S25A1M0A1A1SaG0A1A3S16A3").
Proof. unfold CC8ma_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT8_0 : ltac2:(tb__ "0|0|
S6S15S55S9SeSbS0S33A1A1A1SaS0S25A1A1A3S16A3").
Proof. unfold CC8ma_0, T8_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT8_0 : ltac2:(tb__ "0|0|
S6S15S3S50S33SaS0S25A1A1A2S58VW;Vst;Vtmax;A3S43A3S16A3").
Proof. unfold CC8ma_0, T8_0, sd8_0. memo_rw (C9 W st tmax) memo_4. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID8_0 : ltac2:(tb__ "0|0|
S6S15S4bS43S23A2S16A3").
Proof. unfold sd8_0. memo_rw (C9 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC8_0 : ltac2:(tb__ "0|0|
S65S23SbS0S25A1A1A2").
Proof. apply Pos.leb_le. unfold CC8ma_0. memo_rw (E8a W st tmax) memo_1. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition i8_0 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S63S1fS8SfS0S5bVW;Vst;Vtmax;A3A1A1A2U6A2").
Definition S8s_0 : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S14S7A1S7Lx;S4eS0S5bVW;Vst;Vtmax;A3A1M0S3fSdZ1000A1A3S7R1LSx;G0X14x2").
Lemma SPL8_0 : ltac2:(tb__ "0|0|
S6S14S7A1S4eS0S5bVW;Vst;Vtmax;A3A1S3fSdZ1000A1A3S1bS7S3bA2A3").
Proof. unfold i8_0, S8s_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X8b_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S2S5bVW;Vst;Vtmax;A3S3bA2").
Definition s8b_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49P1S0S27A1S0S20A1A3").
Definition R8b_0 : ltac2:(tb__ "0|0|
S18S8A1") := ltac2:(tb__ "0|1|
S14S18S8A1M0A1G0Lx;S51S27S20S2cA3G0R1LR;S17S8A1X14x2").
Definition T8b_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S52S2cS20S4dS54S21A1A1S27S30A5").
Lemma He8b_0 : ltac2:(tb__ "0|1|
S6S14S18S8A1M0A1S51S27S20S2cA3S1bG0S30A2A3").
Proof. unfold X8b_0, s8b_0, R8b_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S6S15S53S27S20S2cS30S64S5S1S4S22A4A5S16A3").
Proof. unfold X8b_0, s8b_0, R8b_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S6S1S52S2cS20S4dS54S21A1A1S27S30A5S34A3").
Proof. reflexivity. Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S6S15S55S9SeSbS0S27A1M0A1A1SaG0A1A3S16A3").
Proof. unfold X8b_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S6S15S55S9SeSbS0S34A1A1A1SaS0S27A1A1A3S16A3").
Proof. unfold X8b_0, T8b_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S65S23SbS0S27A1A1A2").
Proof. apply Pos.leb_le. unfold X8b_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition i9_0 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S63S1fS8SfS0S58VW;Vst;Vtmax;A3A1A1A2U6A2").
Definition U8b0_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S68S19S9S11S10S66S12PcA1SdZ1000A1A3A1S17S9A1A3S58VW;Vst;Vtmax;A3A2").
Definition SU_0 : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S14S7A1S7Lx;S4eS0S3dA1M0S37SdZ1000A1A3S7R1LSx;G0X14x2").
Lemma SPLU_0 : ltac2:(tb__ "0|0|
S6S14S7A1S4eS0S3dA1S37SdZ1000A1A3S1bS7S47A2A3").
Proof. unfold i9_0, U8b0_0, SU_0. memo_rw (C9 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition U8b_0 := ax_setS U8b0_0 SU_0.
Definition sd8b_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49S23S0S50S34SaS0S27A1A1A2A1S0S29A1A3").
Lemma ENTU_0 : ltac2:(tb__ "0|0|
S6S15S3S50S34SaS0S27A1A1A2S29S44A3S16A3").
Proof. unfold X8b_0, T8b_0, U8b_0, sd8b_0. memo_rw (E8b W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDU_0 : ltac2:(tb__ "0|0|
S6S15S4bS44S23A2S16A3").
Proof. unfold sd8b_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition SM_0 : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S14S7A1S7Lx;S4fS0S29A1M0S37A2S7R1LSx;G0X14x2").
Lemma MRG_0 : ltac2:(tb__ "0|0|
S6S14S7A1S4fS0S29A1S37A2S1bS7S39A2A3").
Proof. unfold i9_0, U8b_0, SM_0. memo_rw (C9 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s9m_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49S23S0S2S29S39A2A1S0S58VW;Vst;Vtmax;A3A1A3").
Lemma ENTM_0 : ltac2:(tb__ "0|0|
S6S15S3S2S29S39A2S58VW;Vst;Vtmax;A3S41A3S16A3").
Proof. unfold U8b_0, SM_0, s9m_0. memo_rw (C9 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDM_0 : ltac2:(tb__ "0|0|
S6S15S4bS41S23A2S16A3").
Proof. unfold s9m_0. memo_rw (C9 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert8p_0 : ltac2:(tb__ "0|1|
S6S15S69S24Ufa0S19S56Zde378S19S56Z3c8c0S17S56A1A3A3S23S19S1S62VW;Vst;Vtmax;A3S17S1A1M0A3S19S1S5cVW;Vst;Vtmax;A3S19S1S5dVW;Vst;Vtmax;A3G0A3A3A6S16A3").
Proof. memo_rw (C8p W st tmax) memo_5. memo_rw (E8pa W st tmax) memo_6. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition CC8map_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|1|
S5eVW;Vst;Vtmax;S5cVW;Vst;Vtmax;A3S5fS19S1cS1aScA2M0S1dS1aScUaS60A4S17G0A1A3S17S8A1S1eS17S9A1A9").
Lemma HCC8map_0 : ltac2:(tb__ "0|1|
S6S1S26S5eVW;Vst;Vtmax;S5cVW;Vst;Vtmax;A3S5fS19S1cS1aScA2M0S1dS1aScUaS60A4S17G0A1A3S17S8A1S1eS17S9A1A9A3").
Proof. reflexivity. Qed.
Lemma W8ap_0 : ltac2:(tb__ "0|0|
S6S15S13S0S26A1A1S16A3").
Proof. unfold CC8map_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D8ap_0 : ltac2:(tb__ "0|4|
S6S14S1cS18S1cScScA2M0A1M1S18S9A1M2A2M3A1S67S0S5cVW;Vst;Vtmax;A3A1S0S26A1A2S1bG3S1dG1G2S17G0A1S17S9A1A4A2A3").
Proof. unfold CC8map_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX8ap_0 : ltac2:(tb__ "0|0|
S6S57SbS0S26A1A1SbS0S5cVW;Vst;Vtmax;A3A1A1A3").
Proof. unfold CC8map_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s8p_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49P1S0S26A1S0S20A1A3").
Definition R8p_0 : ltac2:(tb__ "0|0|
S18S8A1") := ltac2:(tb__ "0|1|
S14S18S8A1M0A1G0Lx;S51S26S20S2eA3G0R1LR;S17S8A1X14x2").
Definition T8p_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S52S2eS20S4dS54S21A1A1S26S32A5").
Definition sd8p_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49S23S0S50S36SaS0S26A1A1A2A1S0S59VW;Vst;Vtmax;A3A1A3").
Lemma He8p_0 : ltac2:(tb__ "0|1|
S6S14S18S8A1M0A1S51S26S20S2eA3S1bG0S32A2A3").
Proof. unfold CC8map_0, s8p_0, R8p_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk8p_0 : ltac2:(tb__ "0|0|
S6S15S53S26S20S2eS32S64S5S1S4S22A4A5S16A3").
Proof. unfold CC8map_0, s8p_0, R8p_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT8p_0 : ltac2:(tb__ "0|0|
S6S1S52S2eS20S4dS54S21A1A1S26S32A5S36A3").
Proof. reflexivity. Qed.
Lemma FBC8p_0 : ltac2:(tb__ "0|1|
S6S15S55S9SeSbS0S26A1M0A1A1SaG0A1A3S16A3").
Proof. unfold CC8map_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT8p_0 : ltac2:(tb__ "0|0|
S6S15S55S9SeSbS0S36A1A1A1SaS0S26A1A1A3S16A3").
Proof. unfold CC8map_0, T8p_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT8p_0 : ltac2:(tb__ "0|0|
S6S15S3S50S36SaS0S26A1A1A2S59VW;Vst;Vtmax;A3S46A3S16A3").
Proof. unfold CC8map_0, T8p_0, sd8p_0. memo_rw (C9p W st tmax) memo_8. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID8p_0 : ltac2:(tb__ "0|0|
S6S15S4bS46S23A2S16A3").
Proof. unfold sd8p_0. memo_rw (C9p W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC8p_0 : ltac2:(tb__ "0|0|
S65S23SbS0S26A1A1A2").
Proof. apply Pos.leb_le. unfold CC8map_0. memo_rw (E8pa W st tmax) memo_6. memo_rw (upd W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition i8p_0 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S63S1fS8SfS0S5dVW;Vst;Vtmax;A3A1A1A2U6A2").
Definition S8sp_0 : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S14S7A1S7Lx;S4eS0S5dVW;Vst;Vtmax;A3A1M0S40SdZ1000A1A3S7R1LSx;G0X14x2").
Lemma SPL8p_0 : ltac2:(tb__ "0|0|
S6S14S7A1S4eS0S5dVW;Vst;Vtmax;A3A1S40SdZ1000A1A3S1bS7S3cA2A3").
Proof. unfold i8p_0, S8sp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X8bp_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S2S5dVW;Vst;Vtmax;A3S3cA2").
Definition s8bp_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49P1S0S28A1S0S20A1A3").
Definition R8bp_0 : ltac2:(tb__ "0|0|
S18S8A1") := ltac2:(tb__ "0|1|
S14S18S8A1M0A1G0Lx;S51S28S20S2dA3G0R1LR;S17S8A1X14x2").
Definition T8bp_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S52S2dS20S4dS54S21A1A1S28S31A5").
Lemma He8bp_0 : ltac2:(tb__ "0|1|
S6S14S18S8A1M0A1S51S28S20S2dA3S1bG0S31A2A3").
Proof. unfold X8bp_0, s8bp_0, R8bp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Hchk8bp_0 : ltac2:(tb__ "0|0|
S6S15S53S28S20S2dS31S64S5S1S4S22A4A5S16A3").
Proof. unfold X8bp_0, s8bp_0, R8bp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HT8bp_0 : ltac2:(tb__ "0|0|
S6S1S52S2dS20S4dS54S21A1A1S28S31A5S35A3").
Proof. reflexivity. Qed.
Lemma FBC8bp_0 : ltac2:(tb__ "0|1|
S6S15S55S9SeSbS0S28A1M0A1A1SaG0A1A3S16A3").
Proof. unfold X8bp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FBT8bp_0 : ltac2:(tb__ "0|0|
S6S15S55S9SeSbS0S35A1A1A1SaS0S28A1A1A3S16A3").
Proof. unfold X8bp_0, T8bp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC8bp_0 : ltac2:(tb__ "0|0|
S65S23SbS0S28A1A1A2").
Proof. apply Pos.leb_le. unfold X8bp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition i9p_0 : ltac2:(tb__ "0|0|
S1a") := ltac2:(tb__ "0|0|
S63S1fS8SfS0S59VW;Vst;Vtmax;A3A1A1A2U6A2").
Definition U8b0p_0 : ltac2:(tb__ "0|0|
S1") := ltac2:(tb__ "0|0|
S68S19S9S11S10S66S12PcA1SdZ1000A1A3A1S17S9A1A3S59VW;Vst;Vtmax;A3A2").
Definition SUp_0 : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S14S7A1S7Lx;S4eS0S3eA1M0S38SdZ1000A1A3S7R1LSx;G0X14x2").
Lemma SPLUp_0 : ltac2:(tb__ "0|0|
S6S14S7A1S4eS0S3eA1S38SdZ1000A1A3S1bS7S48A2A3").
Proof. unfold i9p_0, U8b0p_0, SUp_0. memo_rw (C9p W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition U8bp_0 := ax_setS U8b0p_0 SUp_0.
Definition sd8bp_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49S23S0S50S35SaS0S28A1A1A2A1S0S2aA1A3").
Lemma ENTUp_0 : ltac2:(tb__ "0|0|
S6S15S3S50S35SaS0S28A1A1A2S2aS45A3S16A3").
Proof. unfold X8bp_0, T8bp_0, U8bp_0, sd8bp_0. memo_rw (E8pb W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDUp_0 : ltac2:(tb__ "0|0|
S6S15S4bS45S23A2S16A3").
Proof. unfold sd8bp_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition SMp_0 : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S14S7A1S7Lx;S4fS0S2aA1M0S38A2S7R1LSx;G0X14x2").
Lemma MRGp_0 : ltac2:(tb__ "0|0|
S6S14S7A1S4fS0S2aA1S38A2S1bS7S3aA2A3").
Proof. unfold i9p_0, U8bp_0, SMp_0. memo_rw (C9p W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s9mp_0 : ltac2:(tb__ "0|0|
S4a") := ltac2:(tb__ "0|0|
S49S23S0S2S2aS3aA2A1S0S59VW;Vst;Vtmax;A3A1A3").
Lemma ENTMp_0 : ltac2:(tb__ "0|0|
S6S15S3S2S2aS3aA2S59VW;Vst;Vtmax;A3S42A3S16A3").
Proof. unfold U8bp_0, SMp_0, s9mp_0. memo_rw (C9p W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SIDMp_0 : ltac2:(tb__ "0|0|
S6S15S4bS42S23A2S16A3").
Proof. unfold s9mp_0. memo_rw (C9p W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS9iW2.

