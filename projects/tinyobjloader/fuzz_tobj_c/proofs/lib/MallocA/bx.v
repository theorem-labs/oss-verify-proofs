(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi SpineCallocSec CallocBase2 F0A_rebuild ay.

(* [comment removed for export] *)
Module SpineMallocEi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "SLit"; "sprop"; "SPUle"; "SVar"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "ax_add_facts"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_RZ"; "C9"; "C9p"; "C1g"; "C2p"; "C2r"; "C3"; "C5"; "C5b"; "C5c"; "C5d"; "C5e"; "C6"; "C6b"; "C6l"; "C7"; "C7p"; "C8"; "C8p"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "P0_s1"; "F_hi"; "F_lo"; "s1_cuts"; "s1_exits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocS9j"; "F9a_nf"; "F9b_nf"; "F9pa_nf"; "F9pb_nf"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocS9j.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S5S0S0S2S0S18VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C1g W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C1g] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C1g]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S5S0S0S2S0S19VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C2p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C2p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C2p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S5S0S0S2S0S1aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C2r W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C2r] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C2r]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S5S0S0S2S0S1bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C3 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C3] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C3]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S5S0S0S2S0S1cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S5S0S0S2S0S1dVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S5S0S0S2S0S1eVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5c W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5c] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5c]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S5S0S0S2S0S1fVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5d W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5d] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5d]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S5S0S0S2S0S20VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5e W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5e] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5e]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S5S0S0S2S0S21VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C6]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S5S0S0S2S0S23VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6l W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6l] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C6l]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S5S0S0S2S0S22VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C6b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S5S0S0S2S0S24VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C7 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C7] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C7]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_13 : ltac2:(tb__ "0|0|
S5S0S0S2S0S25VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C7p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C7p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C7p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_14 : ltac2:(tb__ "0|0|
S5S0S0S2S0S26VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C8]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_15 : ltac2:(tb__ "0|0|
S5S0S0S2S0S27VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C8p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_16 : ltac2:(tb__ "0|0|
S5S0S0S2S0S16VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C9]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_17 : ltac2:(tb__ "0|0|
S5S0S0S2S0S17VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C9p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.

Lemma NXhi_0 : ltac2:(tb__ "0|0|
SbS3S6S1S29VW;Vst;S2aA3A1A1A2").
Proof. apply Pos.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXlo_0 : ltac2:(tb__ "0|0|
SbS3S6S1S29VW;Vst;S2bA3A1A1A2").
Proof. apply Pos.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1g_0 : ltac2:(tb__ "0|0|
SbS3S6S1S18VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C1g W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC2p_0 : ltac2:(tb__ "0|0|
SbS3S6S1S19VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C2p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC2r_0 : ltac2:(tb__ "0|0|
SbS3S6S1S1aVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C2r W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC3_0 : ltac2:(tb__ "0|0|
SbS3S6S1S1bVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C3 W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC5_0 : ltac2:(tb__ "0|0|
SbS3S6S1S1cVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC5b_0 : ltac2:(tb__ "0|0|
SbS3S6S1S1dVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5b W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC5c_0 : ltac2:(tb__ "0|0|
SbS3S6S1S1eVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5c W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC5d_0 : ltac2:(tb__ "0|0|
SbS3S6S1S1fVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5d W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC5e_0 : ltac2:(tb__ "0|0|
SbS3S6S1S20VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5e W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC6_0 : ltac2:(tb__ "0|0|
SbS3S6S1S21VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C6 W st tmax) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC6l_0 : ltac2:(tb__ "0|0|
SbS3S6S1S23VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C6l W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
SbS3S6S1S22VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C6b W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC7_0 : ltac2:(tb__ "0|0|
SbS3S6S1S24VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C7 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC7p_0 : ltac2:(tb__ "0|0|
SbS3S6S1S25VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C7p W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXCC8_0 : ltac2:(tb__ "0|0|
SbS3S6S1S26VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C8 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXCC8p_0 : ltac2:(tb__ "0|0|
SbS3S6S1S27VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C8p W st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
S2S12SeS4Ufa0S10S14Z40a18S11S14A1A3S3S28S0ScS0SdR1Z1S7Z0M0A1M1A3Lc;S2cU0M2Vst;A2A4S28S0ScS0SdR1G0G1A3Le;S2dG2Vst;Vtmax;A3A4A6S13A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S2S12SeS4Ufa0S11S14A1S3S10ScSdSfS10S8S9S7Z20A1SaS15A1A2S11S8A1A3S16VW;Vst;Vtmax;A3A2Z1S7Z0M0A1M1A3S11ScA1M2A3S10ScSdS2eG0G1A3G2A3A6S13A3").
Proof. memo_rw (C9 W st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S2S12SeS4Ufa0S11S14A1S3S10ScSdSfS10S8S9SaS15A1S7Z10A1A2S11S8A1A3S16VW;Vst;Vtmax;A3A2Z1S7Z0M0A1M1A3S11ScA1M2A3S10ScSdS2fG0G1A3G2A3A6S13A3").
Proof. memo_rw (C9 W st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECert9pa_0 : ltac2:(tb__ "0|3|
S2S12SeS4Ufa0S11S14A1S3S10ScSdSfS10S8S9S7Z20A1SaS15A1A2S11S8A1A3S17VW;Vst;Vtmax;A3A2Z1S7Z0M0A1M1A3S11ScA1M2A3S10ScSdS30G0G1A3G2A3A6S13A3").
Proof. memo_rw (C9p W st tmax) memo_17. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECert9pb_0 : ltac2:(tb__ "0|3|
S2S12SeS4Ufa0S11S14A1S3S10ScSdSfS10S8S9SaS15A1S7Z10A1A2S11S8A1A3S17VW;Vst;Vtmax;A3A2Z1S7Z0M0A1M1A3S11ScA1M2A3S10ScSdS31G0G1A3G2A3A6S13A3").
Proof. memo_rw (C9p W st tmax) memo_17. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocEi.

(* [comment removed for export] *)
Module SpineCallocSec2.


From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition a1x : sv :=
  SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SVar V_NS) (SLit 4095)) (SLit 18446744073709547520)) (SLit 8191)) (SLit 18446744073709547520).

Lemma acost_step : forall V n, 0 <= V -> 0 <= n -> 4 * (acost (V + n) - acost V) >= 7 * n - 3.
Proof.
  intros V n HV Hn. unfold acost, ALPHA_NUM, ALPHA_DEN.
  pose proof (Z.div_mod (7 * (V + n) + 4 - 1) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * (V + n) + 4 - 1) 4 ltac:(lia)).
  pose proof (Z.div_mod (7 * V + 4 - 1) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (7 * V + 4 - 1) 4 ltac:(lia)). lia.
Qed.

Definition IMG_S : list (Z * Z) := [(SEC_INST, 0xee044 - SEC_INST); (0xee048, 0xee070 - 0xee048); (0xe9b28, 8); (0x173660, 2)].
Lemma IMG_M_lo : forallb (fun r : Z * Z => (0x10000 <=? fst r) && (fst r + snd r <=? IMG_HI)) IMG_M = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IMG_M_range : forall a, in_rangesZ IMG_M a -> 0x10000 <= a < IMG_HI.
Proof.
  intros a (b & n & Hr & Ha). pose proof (proj1 (forallb_forall _ _) IMG_M_lo (b, n) Hr) as X.
  apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. cbn [fst snd] in X1, X2. lia.
Qed.

Lemma rtc_img_lo : forall z, cells_footb (rtc_cells_img RTC_A G0) z = true -> 0x10000 <= z.
Proof.
  intros z Hz. unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin). unfold in_cellb in Hin.
  apply andb_prop in Hin as [X Y]. apply Z.leb_le in X.
  assert (L : forallb (fun c => 0x10000 <=? c_addr c) (rtc_cells_img RTC_A G0) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (proj1 (forallb_forall _ _) L c Hc) as L'. apply Z.leb_le in L'. lia.
Qed.

Definition rt_zoneG (G : ageom) (a : Z) : Prop :=
  (0x10000 <= a < IMG_HI) \/ (ag_thread G <= a < ag_thread G + 0x1000) \/ (ag_ctx G <= a < ag_ctx G + 0x1000)
  \/ (ag_dtls G <= a < ag_dtls G + 0x1000) \/ (ag_fsb G <= a < ag_fsb G + FS_total).
Lemma rt_zoneM_G : forall G a, rt_zoneM G a -> rt_zoneG G a.
Proof.
  intros G a [[[X Y]|R]|R]; unfold rt_zoneG.
  - left. pose proof (rtc_img_lo a Y). lia.
  - rewrite FS_total_val. lia.
  - left. exact (IMG_M_range a R).
Qed.
Lemma N_sec_zone : forall G rho k a,
  rw rho 151%positive = Z_to_bv 64 (ag_thread G) -> 0 <= ag_thread G < 2 ^ 64 ->
  In k N_sec -> fst (spec_range rho k) <= a < snd (spec_range rho k) -> rt_zoneG G a.
Proof.
  intros G rho k a E151 HT Hk Ha. unfold N_sec in Hk. unfold rt_zoneG, IMG_HI. unfold SEC_INST, ERRNO_A, vT in Hk.
  repeat (destruct Hk as [<-|Hk]; [cbn [spec_range fst snd eval] in Ha; rewrite ?E151, ?u64_lit in Ha by lia; lia|]). destruct Hk.
Qed.
Lemma N_m1_zoneG : forall G rho k a,
  geom_ok G -> rw rho 151%positive = Z_to_bv 64 (ag_thread G) -> rw rho 152%positive = Z_to_bv 64 (ag_ctx G) ->
  In k N_m1 -> fst (spec_range rho k) <= a < snd (spec_range rho k) -> rt_zoneG G a.
Proof. intros G rho k a HG E151 E152 Hk Ha. apply rt_zoneM_G. exact (N_m1_zone G rho k a HG E151 E152 Hk Ha). Qed.

Lemma carve_range : forall rho k, spec_small k -> obj_range rho (carve_obj k) = spec_range rho k.
Proof.
  intros rho [[[base lo] hi] cs] (S1 & S2 & S3 & _). cbn [carve_obj]. unfold carved. rewrite obj_range_mk by lia. reflexivity.
Qed.
Lemma N_sec_small : Forall spec_small N_sec.
Proof.
  unfold N_sec, spec_small. unfold SEC_INST, ERRNO_A.
  repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.
Lemma ok_pframeA_liftKA : forall segs (ok : world -> Prop) (Kc : KcA) (Jx : jpredA),
  ok_pframeA segs ok (liftKA Kc) -> (forall rho tp tr md, Jx rho tp tr md -> Kc tr md) -> ok_pframeA segs ok Jx.
Proof. intros segs ok Kc Jx H HJ rho tp tr ms md x8 Hj. apply (H rho tp tr ms md x8). exact (HJ _ _ _ _ Hj). Qed.

Lemma sw_range_holds : forall segs rho ms objs o,
  Forall (obj_holds segs rho ms) objs -> In o objs -> skel o = (SVar 10, SVar V_DEPTH, SLit 0) -> holds rho F_sp_high ->
  140735332483072 <= fst (obj_range rho o) /\ snd (obj_range rho o) = bv_unsigned (rw rho 10%positive)
  /\ fst (obj_range rho o) <= snd (obj_range rho o).
Proof.
  intros segs rho ms objs o Hall Hin Hsk Hf.
  destruct o as [ob olo ohi ocs od]. cbn in Hsk. injection Hsk as -> -> ->.
  pose proof (proj1 (Forall_forall _ _) Hall _ Hin) as Ho.
  unfold obj_holds, obj_lo_of, obj_hi_of in Ho. cbn [ob_base ob_lo ob_hi] in Ho.
  destruct Ho as ((B1 & B2 & B3 & B4) & _).
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
  rewrite soff_lit in *. replace (snorm 0) with 0 in * by reflexivity.
  cbn [eval] in *. unfold holds, F_sp_high in Hf. cbn [eval] in Hf. rewrite add_val in Hf.
  rewrite u64_lit in Hf by lia.
  rewrite soff_snorm in *. unfold U in *. cbn [eval] in *.
  pose proof (urange (rw rho 10%positive)) as R10. pose proof (urange (rw rho V_DEPTH)) as R15.
  unfold snorm in *.
  rewrite (Z.mod_small (bv_unsigned (rw rho V_DEPTH)) (2 ^ 64)) in * by lia.
  destruct (Z.ltb_spec (bv_unsigned (rw rho V_DEPTH)) (2 ^ 63)).
  - assert (bv_unsigned (rw rho V_DEPTH) = 0) by lia. rewrite H0 in *. rewrite Z.add_0_r, Z.mod_small in Hf by lia. lia.
  - replace ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) mod 2 ^ 64)
      with (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) in Hf.
    2:{ symmetry. replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) with
          ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    lia.
Qed.

Lemma skel_head : forall (objs : list sobj) o' l', map skel objs = map skel (o' :: l') ->
  exists o rest, objs = o :: rest /\ skel o = skel o' /\ map skel rest = map skel l'.
Proof.
  intros [|o rest] o' l' E; cbn in E; [discriminate|]. exists o, rest. split; [reflexivity|]. split; congruence.
Qed.

Section SEC2.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : forall a, in_rangesZ CST a -> in_rangesZ IMG_M a -> False.
Hypothesis HCSTS : forall a, in_rangesZ CST a -> in_rangesZ IMG_S a -> False.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := J_alloc_preT AInv W st A Kc (SVar 12).

Hypothesis law_res : forall A rho tp md, AInv A rho tp md -> vm_reserved (m_vmmaps md) = segments_reserved segsA.

Lemma JG_rigidS : forall A Kc rho rhoE tp tr md,
  JG W st A Kc rho rhoE tp tr md ->
  let nv := bv_unsigned (rw rho 12%positive) in let G := aa_geom A in
  rw rhoE 12%positive = rw rho 12%positive
  /\ rw rhoE 141%positive = Z_to_bv 64 (secneeded nv) /\ rw rhoE 142%positive = Z_to_bv 64 (secmapsize nv)
  /\ rw rhoE 151%positive = Z_to_bv 64 (ag_thread G) /\ rw rhoE 152%positive = Z_to_bv 64 (ag_ctx G)
  /\ rw rhoE 153%positive = Z_to_bv 64 (ag_stack_top G) /\ rw rhoE 154%positive = Z_to_bv 64 (ag_stack_bottom G)
  /\ rw rhoE 155%positive = Z_to_bv 64 (ag_spacebeg G) /\ rw rhoE 156%positive = Z_to_bv 64 (ag_spacebeg G + kSpaceSize)
  /\ rw rhoE 145%positive = Z_to_bv 64 (ag_pab G) /\ rw rhoE 146%positive = Z_to_bv 64 (aa_ptr_committed A / 8)
  /\ rw rhoE 147%positive = Z_to_bv 64 (Z.of_nat (length (aa_sec A)))
  /\ rm rhoE = rm rho /\ (forall l, rl rhoE l = rl rho l) /\ (forall i, (i < GW)%positive -> rw rhoE i = rw (rhoM_of A rho) i).
Proof.
  intros A Kc rho rhoE tp tr md [Hag _]. destruct Hag as (Hagw & Hagl & Hagm). cbn zeta.
  repeat match goal with |- _ /\ _ => split end;
    try (rewrite <- (Hagw _) by (unfold GW; lia); reflexivity).
  - apply functional_extensionality. intros a. symmetry. exact (Hagm a).
  - intros l. symmetry. exact (Hagl l).
  - intros i Hi. symmetry. exact (Hagw i Hi).
Qed.

Section C1.
Hypothesis CertS1 : check_cfgA segsA 4000%nat [0x7050c] GW [SS0 W st tmax] [ES1 W st tmax] = true.
Theorem sec_cert1 : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (J W st A Kc) ->
  (forall rhoX, triple segs ok (SPA segs (JG W st A Kc rho) (ES1 W st tmax) rhoX tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (SS0 W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HR rhoE.
  apply (cfg_soundA segs 4000%nat [0x7050c] GW [SS0 W st tmax] [ES1 W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact CertS1.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HR].
  - left. reflexivity.
Qed.
End C1.

Section C2.
Hypothesis WC1 : swf (ax_S (CS1 W st tmax)) = true.
Hypothesis DC1 : state_diff (ax_S (ES1 W st tmax)) (ax_S (CS1 W st tmax)) = Some ([(a1x, SVar V_MS)], []).
Hypothesis NXC1 : ss_next (ax_S (CS1 W st tmax)) = ss_next (ax_S (ES1 W st tmax)).

Lemma sec_cs1 : forall A Kc rho tp w rhoX,
  SPA segs (JG W st A Kc rho) (ES1 W st tmax) rhoX tp w -> SPA segs (JG W st A Kc rho) (CS1 W st tmax) rhoX tp w.
Proof.
  intros A Kc rho tp w rhoX H. destruct w as [tr [ms md]].
  pose proof (JG_rigidS A Kc rho rhoX tp tr md (proj2 H)) as (E12 & E141 & E142 & _).
  destruct (proj2 H) as [_ HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN. rewrite E12 in HN.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  pose proof (round_up_ge' nv 8 ltac:(lia)) as RU1. pose proof (round_up_mod nv 8 ltac:(lia)) as RM1.
  pose proof (round_up_ge' (secneeded nv) PG ltac:(unfold PG; lia)) as RU2. pose proof (round_up_mod (secneeded nv) PG ltac:(unfold PG; lia)) as RM2.
  unfold PG in RU2, RM2.
  assert (NS : secneeded nv = round_up nv 8 + 4096) by reflexivity.
  assert (MS : secmapsize nv = round_up (secneeded nv) 4096 + 4096) by reflexivity.
  assert (EA : eval rhoX a1x = eval rhoX (SVar V_MS)).
  { unfold a1x, V_NS, V_MS. cbn [eval]. rewrite E141, E142. apply bv_eq.
    rewrite and_val, add_val, and_val, add_val, !u64_lit by lia.
    rewrite (Z.mod_small (secneeded nv + 4095)) by lia. rewrite <- round_up_land by lia.
    rewrite (Z.mod_small (round_up (secneeded nv) 4096 + 8191)) by lia.
    rewrite land_page by lia. rewrite MS.
    destruct (proj1 (Z.mod_divide (round_up (secneeded nv) 4096) 4096 ltac:(lia)) RM2) as [q Hq]. rewrite Hq.
    replace (q * 4096 + 8191) with (4095 + (q + 1) * 4096) by lia. rewrite Z.mod_add by lia. change (4095 mod 4096) with 4095. lia. }
  change (CS1 W st tmax) with (upd W st tmax (ES1 W st tmax) 0x7050c [(11%nat, SVar V_MS)] [] false []). unfold upd. cbv zeta.
  revert WC1 DC1 NXC1. unfold CS1, upd. cbv zeta. intros WC1 DC1 NXC1.
  eapply SPA_restate; [exact WC1 | exact DC1 | exact NXC1 | | constructor | exact H].
  constructor; [exact EA | constructor].
Qed.
End C2.

Section C3.
Hypothesis IC1 : instr_at segsA (ss_pc (ax_S (CS1 W st tmax))) = Some Ecall.
Hypothesis R17 : reg_sv (ax_S (CS1 W st tmax)) 17 = SLit 222.
Hypothesis R11 : reg_sv (ax_S (CS1 W st tmax)) 11 = SVar V_MS.
Hypothesis R10 : reg_sv (ax_S (CS1 W st tmax)) 10 = SLit 0.
Hypothesis R12 : reg_sv (ax_S (CS1 W st tmax)) 12 = SLit 3.
Hypothesis R13 : reg_sv (ax_S (CS1 W st tmax)) 13 = SLit 34.
Hypothesis R14 : reg_sv (ax_S (CS1 W st tmax)) 14 = SLit 18446744073709551615.
Hypothesis R15 : reg_sv (ax_S (CS1 W st tmax)) 15 = SLit 0.
Hypothesis NX1 : ss_next (ax_S (CS1 W st tmax)) = NW2.
Hypothesis XC1 : ax_X (CS1 W st tmax) = [].
Hypothesis SK1 : map skel (ss_objs (ax_S (CS1 W st tmax))) = map skel (((sw_s1 :: unwind_objs W ++ A_globals) ++ RT_m1) ++ RT_sec).
Hypothesis FC1 : incl ((((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_geom_fn) ++ F_s1) ++ F_fam tmax 8) (ss_facts (ax_S (CS1 W st tmax))).

Theorem sec_ecall : forall (ok : world -> Prop) (A : AA) (Kc : KcA) (Jo : word -> jpredA) rho tp (Q : assn),
  (stopJ_w W st) -> stopJ_stable W st -> Kc_ok Kc ->
  ok_frameA segs ok (liftKA Kc) -> ok_pframeA segs ok (liftKA Kc) ->
  (forall rhoX tr ms md a, smatch_pendingA segs rhoX tp (CS1 W st tmax) (tr, mkCfg ms md) -> JG W st A Kc rho rhoX tp tr md ->
     mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a ->
     Jo a (rho_set_rw rhoX (ss_next (ax_S (CS1 W st tmax))) a) tp tr (with_vmmaps (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) md)) ->
  (forall rhoX, triple segs ok (SPA segs (JG W st A Kc rho) (ES1f W st tmax) rhoX tp) Q) ->
  (forall rhoX (a : word), triple segs ok (SPA segs (Jo a) (ES1g W st tmax) (rho_set_rw rhoX (nxS W st tmax) a) tp) Q) ->
  forall rhoX, triple segs ok (SPA segs (JG W st A Kc rho) (CS1 W st tmax) rhoX tp) Q.
Proof.
  intros ok A Kc Jo rho tp Q HW HUS HKc Hokl Hokpl HJo HF HGR rhoX.
  set (nv := bv_unsigned (rw rho 12%positive)).
  assert (Hokf : ok_frameA segs ok (JG W st A Kc rho)).
  { intros r t tr ms md msv' [_ HJ]. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  assert (Hokp : ok_pframeA segs ok (JG W st A Kc rho)).
  { apply (ok_pframeA_liftKA segs ok Kc). exact Hokpl. intros r t tr md [_ HJ]. destruct HJ as (_ & HK & _). exact HK. }
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  pose proof (topG_range (aa_geom A)) as ACV.

  apply (triple_pre_pure segs ok _ _ (rw rhoX 142%positive = Z_to_bv 64 (secmapsize nv) /\ 64513 <= nv < 2 ^ 39)).
  { intros w Hw. destruct w as [tr [ms md]]. pose proof (JG_rigidS A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & _ & E142 & _).
    split; [exact E142|]. destruct (proj2 Hw) as [_ HJ]. destruct HJ as (_ & _ & _ & _ & _ & HN & _). cbn [eval] in HN. rewrite E12 in HN.
    pose proof (fact_of_state nW st A Kc rho rhoX tp _ (CS1 W st tmax) (SPUle (SLit (rzf_lo 8)) (SVar 12)) Hw
                  ltac:(apply FC1; apply in_or_app; right; unfold F_fam; cbn; tauto)) as F.
    cbn [holds eval rzf_lo] in F. rewrite E12, u64_lit in F by lia. fold nv in F, HN. clear -F HN. lia. }
  intros [E142 Hnv].
  pose proof (round_up_ge' nv 8 ltac:(lia)) as RU1. pose proof (round_up_ge' (secneeded nv) PG ltac:(unfold PG; lia)) as RU2.
  pose proof (round_up_mod (secneeded nv) PG ltac:(unfold PG; lia)) as RM2. unfold PG in RU2, RM2.
  assert (NS : secneeded nv = round_up nv 8 + 4096) by reflexivity.
  assert (MS : secmapsize nv = round_up (secneeded nv) 4096 + 4096) by reflexivity.
  assert (BMS : nv + 8192 <= secmapsize nv <= nv + 12294 /\ secmapsize nv mod 4096 = 0).
  { rewrite MS. split; [lia|]. rewrite Z.add_mod, RM2 by lia. reflexivity. }
  apply triple1_triple.
  eapply triple1_seq_l.
  2: { apply triple_disj; [exact (HF rhoX)|]. apply triple_ex. intros a. exact (HGR rhoX a). }
  unfold ES1f, ES1g, nxS. replace (SLit (2 ^ 64 - 12)) with (SLit (bv_unsigned (errno_ret ENOMEM))) by reflexivity.
  change (mkObj (SVar (ss_next (ax_S (CS1 W st tmax)))) (SLit 0) (SVar V_MS) [] DZero) with (mmap_obj_sym (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS)).
  assert (HST' : stableA segs (ss_next (ax_S (CS1 W st tmax))) (JG W st A Kc rho)).
  { rewrite NX1. eapply stableA_mono; [|exact HST]. unfold GW, NW2. clear; lia. }
  assert (HB11 : sv_below (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS) = true) by (rewrite NX1; reflexivity).
  assert (HEV : bv_unsigned (eval rhoX (SVar V_MS)) = secmapsize nv).
  { cbn [eval]. unfold V_MS. rewrite E142. apply u64_lit. clear -BMS Hnv. lia. }
  apply (triple1_mmap_rw_symA segs ok (JG W st A Kc rho) (JG W st A Kc rho) Jo (CS1 W st tmax) rhoX tp (SVar V_MS) (secmapsize nv)
           Hokf Hokp HST' IC1 R17 R11 HB11 HEV (proj2 BMS) ltac:(clear -BMS Hnv; lia)).
  intros tr ms md Hsp HJG.
  destruct (pending_argsA segs rhoX tp (CS1 W st tmax) tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite R10 in Q0. rewrite R11 in Q1. rewrite R12 in Q2. rewrite R13 in Q3. rewrite R14 in Q4. rewrite R15 in Q5. cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; apply mmap_modeled_b_intro; reflexivity|].
  split; [rewrite Q3; reflexivity|].
  pose proof (JG_rigidS A Kc rho rhoX tp tr md HJG) as (E12 & E141 & _ & E151 & E152 & E153 & E154 & E155 & E156 & E145 & E146 & E147 & Erm & Erl & Elow).
  pose proof HJG as [_ HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & HR & HFI & HRest & HM & HI3 & HBT).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
  pose proof (geom_top _ HG) as GTOP. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HM))))))) as TOPm.

  split.
  { destruct (AInvA_budget A _ _ _ HA) as (PB & VL & V0 & K0 & F0). unfold headroom. rewrite VL.
    unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
    unfold budget_bound in PB. pose proof (acost_step (aa_V A) nv V0 ltac:(lia)) as AS. unfold BETA_M, BETA_F in *. clear -PB HB AS BMS Hnv. lia. }
  split; [exact HJG|].
  intros a Hpl.
  pose proof (mmap_len_sym segs rhoX tp (CS1 W st tmax) tr ms md (SVar V_MS) (secmapsize nv) Hsp R11 ltac:(cbn [eval]; unfold V_MS; rewrite E142; apply u64_lit; lia) (proj2 BMS) ltac:(lia)) as [_ HnZ].
  pose proof (law_res _ _ _ _ HA) as Hres.
  destruct (grant_facts_A _ _ md _ a Hpl Hres) as (Gal & Gpos & Gceil & Gimg & Gmaps). rewrite HnZ in Gceil, Gimg, Gmaps.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.

  destruct HM as (VG & _). destruct VG as (_ & _ & MT & MC & MD & MF & _).
  assert (MISS : forall lo hi, in_maps (m_vmmaps md) lo hi -> forall x, ua <= x < ua + secmapsize nv -> ~ (lo <= x < hi)).
  { intros lo hi (e & He & Hlo & Hhi) x Hx Hin. destruct e as [b m]. cbn [fst snd] in Hlo, Hhi. apply (Gmaps b m He x Hx). lia. }
  pose proof (MISS _ _ MT) as MT'. pose proof (MISS _ _ MC) as MC'. pose proof (MISS _ _ MD) as MD'. pose proof (MISS _ _ MF) as MF'.
  assert (ZFREE : forall x, rt_zoneG (aa_geom A) x -> ~ (ua <= x < ua + secmapsize nv)).
  { intros x Hz Hx. destruct Hz as [Z1|[Z2|[Z3|[Z4|Z5]]]].
    - apply (Gimg x Hx). unfold IMG_HI in Z1. lia.
    - exact (MT' x Hx Z2). - exact (MC' x Hx Z3). - exact (MD' x Hx Z4). - exact (MF' x Hx Z5). }
  split; [|split; [|split]].
  -
    pose proof (smatch_pendingA_sp segs _ _ _ _ _ _ Hsp) as Hsm0.
    pose proof (smatch_pending_facts segs _ _ _ _ _ Hsm0) as HFall.
    assert (HFX : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rhoX p).
    { intros p Hp. refine (proj1 (Forall_forall _ _) HFall p (FC1 p _)). apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hp. }
    assert (Hhigh : holds rhoX F_sp_high) by (apply HFX; apply in_or_app; right; cbn; tauto).
    assert (Hall : Forall (obj_holds segs rhoX (vms md tp ms)) (ss_objs (ax_S (CS1 W st tmax)))).
    { destruct Hsm0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
    destruct (skel_head _ sw_s1 (((unwind_objs W ++ A_globals) ++ RT_m1) ++ RT_sec) SK1) as (o0 & rest & EO & SK0 & SKR).
    rewrite EO in Hall. rewrite EO.
    pose proof (sw_range_holds segs rhoX _ _ o0 Hall ltac:(left; reflexivity) SK0 Hhigh) as (SW1 & SW2 & SW3).
    assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoX o0)) by (rewrite (sw_lo_gen rhoX o0 SK0); exact Htop).
    assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoX (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
    { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear -SW0 SW2 SW3; lia|clear -ACV; lia]. apply Forall_forall. intros p Hp.
      assert (Hp' : In p (unwind_factsS W st)).
      { destruct st; [apply chain_pre_in; exact Hp|]. exact (chain_pre_factsS' _ _ _ Hp). }
      apply HFX. apply in_or_app; left. exact Hp'. }
    intros o Ho. pattern o. revert o Ho. apply (proj1 (Forall_forall (fun o => ranges_disjoint (obj_range rhoX o) (ua, ua + secmapsize nv)) (o0 :: rest))).
    constructor.
    { unfold ranges_disjoint. right; right; right. cbn [fst snd]. clear -SW0 Gceil TOPm GTOP. lia. }
    apply (Forall_ranges_skel rhoX (fun r => ranges_disjoint r (ua, ua + secmapsize nv)) _ _ SKR).
    rewrite <- !app_assoc. apply Forall_app. split.
    { eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
      unfold ranges_disjoint. rewrite obj_range_mk by (clear -B; lia). cbn [fst snd]. clear -B Gceil TOPm GTOP. lia. }
    apply Forall_app. split.
    { unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil;
        unfold ranges_disjoint; rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite u64_lit by lia.
      - destruct (Z_lt_dec (ua + secmapsize nv) (0xe7bd8 + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec 0xe8978 (ua + 1)) as [L2|L2]; [lia|].
        exfalso. destruct (Z_le_dec ua 0xe7bd8); [apply (Gimg 0xe7bd8); lia | apply (Gimg ua); lia].
      - destruct (Z_lt_dec (ua + secmapsize nv) (0xf13f8 + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec 0xf1404 (ua + 1)) as [L2|L2]; [lia|].
        exfalso. destruct (Z_le_dec ua 0xf13f8); [apply (Gimg 0xf13f8); lia | apply (Gimg ua); lia]. }
    assert (ZR : forall lo hi, (forall x, lo <= x < hi -> rt_zoneG (aa_geom A) x) -> ranges_disjoint (lo, hi) (ua, ua + secmapsize nv)).
    { intros lo hi Hz. unfold ranges_disjoint. cbn [fst snd].
      destruct (Z_lt_dec (ua + secmapsize nv) (lo + 1)) as [L|L]; [lia|]. destruct (Z_lt_dec hi (ua + 1)) as [L2|L2]; [lia|].
      destruct (Z_le_dec hi lo) as [L3|L3]; [lia|]. exfalso.
      destruct (Z_le_dec ua lo); [apply (ZFREE lo); [apply Hz; lia | lia] | apply (ZFREE ua); [apply Hz; lia | lia]]. }
    apply Forall_app. split.
    { rewrite <- N_m1_ok. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
      rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_m1_small k Hk)).
      destruct (spec_range rhoX k) as [lo hi] eqn:ER. apply ZR. intros x Hx. apply (N_m1_zoneG (aa_geom A) rhoX k x HG E151 E152 Hk). rewrite ER. exact Hx. }
    { unfold RT_sec. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
      rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_sec_small k Hk)).
      destruct (spec_range rhoX k) as [lo hi] eqn:ER. apply ZR. intros x Hx. apply (N_sec_zone (aa_geom A) rhoX k x E151 ltac:(lia) Hk). rewrite ER. exact Hx. }
  -
    intros x Hx. apply (grant_no_ro_A a (secmapsize nv)); [exact Gimg | exact Hx].
  -
    rewrite XC1. intros r y [].
  -
    exact (HJo rhoX tr ms md a Hsp HJG Hpl).
Qed.
End C3.

Section C4.
Hypothesis CertSf : check_cfgA segsA 4000%nat [0x5e5d4] GW [ES1f W st tmax] [ESn W st tmax] = true.
Theorem sec_certf : forall (ok : world -> Prop) (A : AA) (Kc : KcA) rho tp (Q : assn),
  stopJ_stable W st -> Kc_ok Kc -> ok_frameA segs ok (J W st A Kc) ->
  (forall rhoX, triple segs ok (SPA segs (JG W st A Kc rho) (ESn W st tmax) rhoX tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (ES1f W st tmax) rhoE tp) Q.
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HR rhoE.
  apply (cfg_soundA segs 4000%nat [0x5e5d4] GW [ES1f W st tmax] [ESn W st tmax] (JG W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. exact (Hokf r t tr ms md msv' HJ HMI Hh Hp Hs).
  - apply JG_stable; [exact HUS | exact HKc].
  - exact CertSf.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | apply HR].
  - left. reflexivity.
Qed.
End C4.

Lemma N_secc_coverb : forallb coverb N_secc = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N_secc_small : Forall spec_small N_secc.
Proof.
  unfold N_secc, spec_small. unfold SEC_INST.
  repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.
Lemma N_secn_small : Forall spec_small N_secn.
Proof.
  unfold N_secn, spec_small. unfold SEC_INST, ERRNO_A.
  repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.
Lemma N_secc_sub : forall k, In k N_secc -> In k N_secn.
Proof. intros k Hk. unfold N_secc in Hk. unfold N_secn. cbn [In] in Hk |- *. tauto. Qed.
Lemma K_seci_in : In K_seci N_secn.
Proof. unfold K_seci, C_seci, N_secn. cbn [In]. tauto. Qed.

Lemma absorb_spec_view_sub : forall sgs rho S tr ms md objs R base lo hi cs rdv lo' hi',
  smatch sgs rho S (tr, mkCfg ms md) -> ss_objs S = objs ++ R -> In (carved base lo hi cs) R -> spec_small (base, lo, hi, cs) ->
  cells_in_view rho rdv (bv_unsigned (eval rho base)) cs ->
  (forall off, lo' <= off < hi' -> exists o n e, In (o, n, e) cs /\ o <= off < o + Z.of_nat n) ->
  forall z, bv_unsigned (eval rho base) + lo' <= z < bv_unsigned (eval rho base) + hi' ->
  rd_of sgs (rm (rho_absorb rho R ms)) (Z_to_bv 64 z) = rdv (Z_to_bv 64 z).
Proof.
  intros sgs rho S tr ms md objs R base lo hi cs rdv lo' hi' Hsm Ho Hin (S1 & S2 & S3 & S4) Hciv Hcov z Hz.
  destruct (absorb_carved_cells sgs rho S tr ms md objs R base lo hi cs Hsm Ho Hin ltac:(lia) ltac:(lia) ltac:(lia) S4) as [C _].
  rewrite eval_absorb in C |- * || idtac.
  replace z with (bv_unsigned (eval rho base) + (z - bv_unsigned (eval rho base))) by lia.
  apply (view_eq_cells (rho_absorb rho R ms) _ rdv (bv_unsigned (eval rho base)) cs lo' hi'); [exact C | | exact Hcov | lia].
  unfold cells_in_view in *. apply Forall_forall. intros [[o n] e] Hin' j Hj. rewrite eval_absorb. exact (proj1 (Forall_forall _ _) Hciv _ Hin' j Hj).
Qed.
Lemma C_seci_cov_lo : forall off, SEC_INST <= off < SEC_INST + 32 -> exists o n e, In (o, n, e) C_seci /\ o <= off < o + Z.of_nat n.
Proof.
  intros off Hoff. unfold C_seci, SEC_INST in *.
  destruct (Z_lt_dec off (0xeddd8 + 8)); [do 3 eexists; split; [cbn; left; reflexivity | cbn; lia]|].
  destruct (Z_lt_dec off (0xeddd8 + 16)); [do 3 eexists; split; [cbn; right; left; reflexivity | cbn; lia]|].
  destruct (Z_lt_dec off (0xeddd8 + 24)); [do 3 eexists; split; [cbn; right; right; left; reflexivity | cbn; lia]|].
  do 3 eexists; split; [cbn; right; right; right; left; reflexivity | cbn; lia].
Qed.
Lemma C_seci_cov_hi : forall off, SEC_INST + 48 <= off < SEC_INST + 64 -> exists o n e, In (o, n, e) C_seci /\ o <= off < o + Z.of_nat n.
Proof.
  intros off Hoff. unfold C_seci, SEC_INST in *.
  destruct (Z_lt_dec off (0xeddd8 + 56)); [do 3 eexists; split; [cbn; do 4 right; left; reflexivity | cbn; lia]|].
  do 3 eexists; split; [cbn; do 5 right; left; reflexivity | cbn; lia].
Qed.

Lemma N_secc_civ : forall A rho tp md,
  AInv A rho tp md ->
  rw rho 145%positive = Z_to_bv 64 (ag_pab (aa_geom A)) -> rw rho 146%positive = Z_to_bv 64 (aa_ptr_committed A / 8) ->
  rw rho 147%positive = Z_to_bv 64 (Z.of_nat (length (aa_sec A))) ->
  Forall (fun k : carve_spec => let '(base, lo, hi, cs) := k in cells_in_view rho (rd_of segs (rm rho)) (bv_unsigned (eval rho base)) cs) N_secc
  /\ cells_in_view rho (rd_of segs (rm rho)) (bv_unsigned (eval rho (SLit 0))) C_seci.
Proof.
  intros A rho tp md HA E145 E146 E147.
  pose proof HA as (HG & HR & HF & HRest & HM & _).
  destruct HRest as (_ & _ & _ & Hsec & _ & _ & _ & _ & HMI).
  destruct Hsec as (_ & _ & SC2 & SC3 & SC45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). destruct HMI as (HMIc & _ & _).
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HMIc))))) as HSAN.
  assert (IMG : forall z, z < 0x646000 -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = view segs (rm rho) z).
  { intros z Hz. apply maskv_out. apply fs_footb_img; [exact HG | exact Hz]. }
  assert (CI : forall a k v, a + Z.of_nat k <= 0x646000 -> cell_ok (maskv (fs_footb (aa_geom A)) (view segs (rm rho))) (mkACell a k v) ->
               cell_ok (view segs (rm rho)) (mkACell (0 + a) k v)).
  { intros a k v Ha Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w c_val] in Hc, Hj |- *. rewrite Z.add_0_l. rewrite IMG in Hc; [exact Hc | lia]. }
  unfold SEC_INST in *.
  pose proof (urange (rw rho 145%positive)) as U145. pose proof (urange (rw rho 146%positive)) as U146. pose proof (urange (rw rho 147%positive)) as U147.
  unfold N_secc, C_seci, SEC_INST. split.
  - repeat apply Forall_cons; try apply Forall_nil; cbv beta iota zeta; cbn [eval]; rewrite (u64_lit 0) by lia;
      unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil.
    + exact (civ_cell rho (rm rho) 0 0xee040 4 0 (SLit 0) (CI 0xee040 4%nat 0 ltac:(cbn; lia) I8) eq_refl ltac:(lia) ltac:(cbn; lia)).
    + exact (civ_cell rho (rm rho) 0 0xe9b28 8 0x1a36f (SLit 0x1a36f) (CI 0xe9b28 8%nat 0x1a36f ltac:(cbn; lia) HSAN) eq_refl ltac:(lia) ltac:(cbn; lia)).
  - cbn [eval]. rewrite (u64_lit 0) by lia. unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
    + exact (civ_cell rho (rm rho) 0 0xeddd8 8 PG (SLit 4096) (CI 0xeddd8 8%nat PG ltac:(cbn; lia) I1) eq_refl ltac:(lia) ltac:(cbn; lia)).
    + refine (civ_cell rho (rm rho) 0 0xedde0 8 (ag_pab (aa_geom A)) (SVar V_PAB) (CI (0xeddd8 + 8) 8%nat (ag_pab (aa_geom A)) ltac:(cbn; lia) I2) _ ltac:(lia) ltac:(cbn; lia)). cbn [eval]. unfold V_PAB. exact E145.
    + refine (civ_cell rho (rm rho) 0 0xedde8 8 (ag_pab (aa_geom A)) (SVar V_PAB) (CI (0xeddd8 + 16) 8%nat (ag_pab (aa_geom A)) ltac:(cbn; lia) I3) _ ltac:(lia) ltac:(cbn; lia)). cbn [eval]. unfold V_PAB. exact E145.
    + exact (civ_cell rho (rm rho) 0 0xeddf0 8 kPtrArrayReserve (SLit (2 ^ 23)) (CI (0xeddd8 + 24) 8%nat kPtrArrayReserve ltac:(cbn; lia) I4) eq_refl ltac:(lia) ltac:(cbn; lia)).
    + refine (civ_cell rho (rm rho) 0 0xede08 8 (aa_ptr_committed A / 8) (SVar V_NRES) (CI (0xeddd8 + 48) 8%nat (aa_ptr_committed A / 8) ltac:(cbn; lia) I5) _ ltac:(lia) ltac:(cbn; lia)). cbn [eval]. unfold V_NRES. exact E146.
    + refine (civ_cell rho (rm rho) 0 0xede10 8 (Z.of_nat (length (aa_sec A))) (SVar V_NCH) (CI (0xeddd8 + 56) 8%nat (Z.of_nat (length (aa_sec A))) ltac:(cbn; lia) I6) _ ltac:(lia) ltac:(cbn; lia)). cbn [eval]. unfold V_NCH. exact E147.
Qed.

Section C5.
Hypothesis RN : R_n W st tmax = RT_m1 ++ map carve_obj N_secn.
Hypothesis WRn : swf (stRn_S W st tmax) = true.
Hypothesis DKRn : state_diff (ax_S (stKn W st tmax)) (stRn_S W st tmax) = Some ([(SLit TP_A, SVar 24)], []).
Hypothesis NXRn : ss_next (stRn_S W st tmax) = ss_next (ax_S (stKn W st tmax)).
Hypothesis ENTn : entailsA (stRn W st tmax) (Lc_null W st) (s_n W st tmax) = true.
Hypothesis IDn : wsub_idc (s_n W st tmax) = true.

Theorem sec_null_finish : forall (A : AA) (Kc : KcA) rho tp w rhoY Posts,
  Kc_ok Kc -> In (Lc_null W st, JLc_null CST XGL A Kc) Posts ->
  SPA segs (JG W st A Kc rho) (ESn W st tmax) rhoY tp w ->
  LQPA segs NF rho tp Posts w.
Proof.
  intros A Kc rho tp w rhoY Posts HKc HPosts H. destruct w as [tr [ms md]].
  pose proof H as [HsmA [Hag HJ]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (JG_rigidS A Kc rho rhoY tp tr md (proj2 H)) as (E12 & E141 & E142 & E151 & E152 & E153 & E154 & E155 & E156 & E145 & E146 & E147 & Erm & Erl & Elow).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN. rewrite E12 in HN.
  set (nv := bv_unsigned (rw rho 12%positive)) in *.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range (aa_geom A)) as ACV.

  set (KJ := (fun (_ : valuation) (_ : list word) (t : list event) (m : Model) => Kc t m) : jpredA).
  assert (Ha : SPA segs KJ (ESn W st tmax) rhoY tp (tr, mkCfg ms md)) by (split; [exact HsmA | exact HK]).
  assert (EOBJ : ss_objs (ax_S (ESn W st tmax)) = firstn (NOBJ W) (ss_objs (ax_S (ESn W st tmax))) ++ R_n W st tmax).
  { unfold R_n. symmetry. apply firstn_skipn. }
  pose proof (SPA_unobj segs KJ rhoY (ESn W st tmax) _ _ tp tr ms md EOBJ Ha (fun k => k)) as Hb.
  cbn zeta in Hb. set (R := R_n W st tmax) in *. set (rho3 := rho_absorb rhoY R (vms md tp ms)) in *.
  change (ax_setS (ESn W st tmax) (set_objs (ax_S (ESn W st tmax)) (firstn (NOBJ W) (ss_objs (ax_S (ESn W st tmax)))))) with (stKn W st tmax) in Hb.
  pose proof (proj1 (proj1 Ha)) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.

  assert (AO : forall o, In o R -> _) by (intros o Ho; exact (absorb_obj rhoY _ tr (vms md tp ms) (vmd md) _ R o Hsm1 EOBJ Ho)).
  assert (NK : forall k, In k (N_m1 ++ N_secc) -> In (carve_obj k) R /\ spec_small k /\ spec_covered k
            /\ cells_in_view rhoY (rd_of segs (rm rhoY)) (fst (spec_range rhoY k) - (let '(_, lo, _, _) := k in lo)) (let '(_, _, _, cs) := k in cs)).
  { intros k Hk. apply in_app_or in Hk as [Hk|Hk].
    - split; [rewrite RN; apply in_or_app; left; rewrite <- N_m1_ok; apply in_map; exact Hk|].
      split; [exact (proj1 (Forall_forall _ _) N_m1_small k Hk)|].
      split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_m1_coverb k Hk)|].
      pose proof (proj1 (Forall_forall _ _) (N_m1_civ AInvA_die A rhoY tp md HA E151 E152 E153 E154 E155 E156) k Hk) as CV. cbn beta in CV.
      destruct k as [[[base lo] hi] cs]. cbn [spec_range fst]. replace (bv_unsigned (eval rhoY base) + lo - lo) with (bv_unsigned (eval rhoY base)) by (clear; lia). exact CV.
    - split; [rewrite RN; apply in_or_app; right; apply in_map; exact (N_secc_sub k Hk)|].
      split; [exact (proj1 (Forall_forall _ _) N_secc_small k Hk)|].
      split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_secc_coverb k Hk)|].
      pose proof (proj1 (Forall_forall _ _) (proj1 (N_secc_civ A rhoY tp md HA E145 E146 E147)) k Hk) as CV. cbn beta in CV.
      destruct k as [[[base lo] hi] cs]. cbn [spec_range fst]. replace (bv_unsigned (eval rhoY base) + lo - lo) with (bv_unsigned (eval rhoY base)) by (clear; lia). exact CV. }

  assert (ET : bv_unsigned (eval rhoY vT) = ag_thread (aa_geom A)) by (unfold vT; cbn [eval]; rewrite E151; apply u64_lit; lia).
  assert (INR : forall a, in_ranges rhoY R a ->
            (exists k, In k (N_m1 ++ N_secc) /\ fst (spec_range rhoY k) <= bv_unsigned a < snd (spec_range rhoY k))
            \/ znull (aa_geom A) (bv_unsigned a) \/ bv_unsigned a = 0x173661
            \/ (SEC_INST <= bv_unsigned a < SEC_INST + 32 \/ SEC_INST + 48 <= bv_unsigned a < SEC_INST + 64)).
  { intros a (o & HoR & Hr). rewrite RN in HoR. apply in_app_or in HoR as [HoR|HoR].
    - left. rewrite <- N_m1_ok in HoR. apply in_map_iff in HoR as (k & <- & Hk). exists k. split; [apply in_or_app; left; exact Hk|].
      rewrite (carve_range rhoY k (proj1 (Forall_forall _ _) N_m1_small k Hk)) in Hr. exact Hr.
    - apply in_map_iff in HoR as (k & <- & Hk). rewrite (carve_range rhoY k (proj1 (Forall_forall _ _) N_secn_small k Hk)) in Hr.
      unfold N_secn in Hk. cbn [In] in Hk. unfold znull.
      destruct Hk as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; subst k; cbn [spec_range fst snd eval] in Hr; rewrite ?(u64_lit 0), ?ET in Hr by lia;
        unfold SEC_INST, ERRNO_A in *.
      +   clear -Hr. lia.
      + right; left. lia.
      + left. eexists. split; [apply in_or_app; right; cbn; left; reflexivity|]. cbn [spec_range fst snd eval]. rewrite (u64_lit 0) by lia. exact Hr.
      + right; left. lia.
      + left. eexists. split; [apply in_or_app; right; cbn; right; left; reflexivity|]. cbn [spec_range fst snd eval]. rewrite (u64_lit 0) by lia. exact Hr.
      + destruct (Z.eq_dec (bv_unsigned a) 0x173661); [right; right; left; assumption | right; left; lia].
      + right; left. lia.
      + right; left. lia. }

  set (vE := view segs (rm rhoY)). set (v3 := view segs (rm rho3)).
  assert (O1 : In (carve_obj (SLit 0, 0x173660, 0x173662, [(0x173660, 1%nat, SLit 1); (0x173661, 1%nat, SLit 1)])) R).
  { rewrite RN. apply in_or_app; right. apply in_map. unfold N_secn. cbn [In]. tauto. }
  assert (VO : forall z, ~ znull (aa_geom A) z -> v3 z = vE z).
  { intros z Hz. unfold v3, vE. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by (clear -n; lia) || rewrite !view_out by (clear -n l; lia); reflexivity.
    rewrite !view_in by (clear -l l0; lia).
    destruct (in_ranges_dec rhoY R (Z_to_bv 64 z)) as [Hin|Hout].
    - destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc|[E1|SC]]]; rewrite ?u64_lit in * by (clear -l l0; lia).
      + unfold rho3. exact (absorb_specs_view rhoY _ tr (vms md tp ms) (vmd md) _ R (N_m1 ++ N_secc) (rd_of segs (rm rhoY)) Hsm1 EOBJ NK z k Hk Hr).
      + exfalso. exact (Hz Hc).
      +
        destruct (AO _ O1) as (_ & CE & _ & _). cbn [ob_cells carve_obj carved lit_cells map] in CE.
        destruct (CE _ ltac:(cbn; right; left; reflexivity)) as (_ & _ & CEj). pose proof (CEj 0%nat ltac:(cbn; lia)) as X. clear CEj.
        cbn [ob_base carved c_off c_width SymState.c_val eval] in X. change (Z.to_nat (Z.of_nat 1)) with 1%nat in X. change (Z.of_nat 0) with 0 in X.
        rewrite soff_lit_small, (u64_lit 0), Z.add_0_r in X by lia. rewrite Z.add_0_l in X. rewrite E1. unfold rho3.
        transitivity (Some (nth 0 (enc_bytes 1 (Z_to_bv 64 1)) (Z_to_bv 8 0))); [exact X|]. symmetry.
        destruct HRest as (_ & _ & _ & _ & _ & _ & _ & _ & (HMIc & _ & _)). pose proof (Forall_inv HMIc) as C9. specialize (C9 0%nat ltac:(cbn; lia)).
        cbn [c_addr c_w c_val Z.of_nat] in C9. rewrite Z.add_0_r in C9. rewrite maskv_out in C9 by (apply fs_footb_img; [exact HG | lia]). rewrite view_in in C9 by lia.
        exact C9.
      +
        pose proof (proj2 (N_secc_civ A rhoY tp md HA E145 E146 E147)) as CIVS.
        assert (HinS : In (carved (SLit 0) SEC_INST (SEC_INST + 64) C_seci) R).
        { rewrite RN. apply in_or_app; right. change (carved (SLit 0) SEC_INST (SEC_INST + 64) C_seci) with (carve_obj K_seci). apply in_map. exact K_seci_in. }
        assert (SMS : spec_small K_seci).
        { unfold K_seci, C_seci, spec_small, SEC_INST. split; [lia|]. split; [lia|]. split; [lia|]. unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia. }
        unfold rho3. destruct SC as [SC|SC].
        * apply (absorb_spec_view_sub segs rhoY _ tr (vms md tp ms) (vmd md) _ R (SLit 0) SEC_INST (SEC_INST + 64) C_seci (rd_of segs (rm rhoY)) SEC_INST (SEC_INST + 32) Hsm1 EOBJ HinS SMS CIVS C_seci_cov_lo).
          cbn [eval]. rewrite (u64_lit 0) by (clear; lia). clear -SC. lia.
        * apply (absorb_spec_view_sub segs rhoY _ tr (vms md tp ms) (vmd md) _ R (SLit 0) SEC_INST (SEC_INST + 64) C_seci (rd_of segs (rm rhoY)) (SEC_INST + 48) (SEC_INST + 64) Hsm1 EOBJ HinS SMS CIVS C_seci_cov_hi).
          cbn [eval]. rewrite (u64_lit 0) by (clear; lia). clear -SC. lia.
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hout. reflexivity. }
  assert (PRES : forall z, znull (aa_geom A) z -> exists b, v3 z = Some b).
  { intros z Hz. unfold v3. unfold znull in Hz. unfold SEC_INST, ERRNO_A in Hz.
    assert (CS : (0xe4000 <= z < 0x646000) \/ (ag_thread (aa_geom A) + 2768 <= z < ag_thread (aa_geom A) + 3168)) by (clear -Hz; lia).
    destruct CS as [CS|CS].
    - rewrite view_in by lia. apply rd_of_imageA. exact CS.
    - assert (OS : In (carve_obj (vT, 2768, 3168, [])) R) by (rewrite RN; apply in_or_app; right; apply in_map; unfold N_secn; cbn [In]; tauto).
      destruct (AO _ OS) as (_ & _ & PR & _). unfold obj_lo_of, obj_hi_of in PR. cbn [ob_dflt carve_obj carved ob_base ob_lo ob_hi] in PR.
      rewrite !soff_lit_small in PR by lia. rewrite ET in PR.
      destruct (PR (or_introl eq_refl) (z - ag_thread (aa_geom A)) ltac:(clear -CS; lia)) as [x Hx].
      exists x. rewrite view_in by lia. replace z with (ag_thread (aa_geom A) + (z - ag_thread (aa_geom A))) by lia. exact Hx. }

  assert (Hc : SPA segs KJ (stRn W st tmax) rho3 tp (tr, mkCfg ms md)).
  { unfold stRn. eapply SPA_restate; [exact WRn | exact DKRn | exact NXRn | | constructor | exact Hb].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. destruct (geom_old _ HG) as (_ & _ & _ & G4' & _). rewrite G4'. reflexivity. }

  pose proof (smatchA_entails segs _ _ _ rho3 tp _ ENTn (proj1 Hc)) as Hsm4.
  set (rho4 := rho_sub rho3 (s_n W st tmax)) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoY k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ (wsub_idc_below _ IDn) Hk). reflexivity. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 (s_n W st tmax)).
  pose proof (rhoM_agree A rho) as (RMw & RMl & RMm).

  apply (LQPA_intro segs NF rho tp _ (Lc_null W st) (JLc_null CST XGL A Kc) rho4 tp _ KJ).
  - exact HPosts.
  - split; [exact Hsm4 | exact HK].
  - split.
    + intros i Hi. rewrite (Hlow i Hi). rewrite (Elow i) by (unfold GW, NF in *; clear -Hi; lia). exact (RMw i Hi).
    + intros l. unfold rho4. cbn [rho_sub rl]. unfold rho3. cbn [rho_absorb rl]. rewrite (Erl l). reflexivity.
  - intros _. unfold JLc_null. split.
    2:{ split; unfold rho4; cbn [rho_sub rw]; [rewrite (wsub_idc_143 _ IDn) | rewrite (wsub_idc_144 _ IDn)]; cbn [eval]; unfold rho3; cbn [rho_absorb rw].
        - rewrite (Elow 143%positive) by (unfold GW; clear; lia). exact (rhoM_of_keep A rho 143%positive ltac:(tauto)).
        - rewrite (Elow 144%positive) by (unfold GW; clear; lia). exact (rhoM_of_keep A rho 144%positive ltac:(tauto)). }
    unfold JL_malloc_null. cbn [w_tr w_cfg cfg_model].
    exists (bumpVK A nv).
    assert (HA' : AInv (bumpVK A nv) rho4 tp md).
    { unfold AInv. apply (null_rebuild A rhoY rho4 tp md nv HA ltac:(clear -HN; lia)).
      - intros z Hz. rewrite Erm4. exact (VO z Hz).
      - intros z Hz. rewrite Erm4. exact (PRES z Hz). }
    split; [exact HA'|]. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn [aa_V bumpVK]; subst nv; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    {
      rewrite Erm4, <- Erm.
      assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ rt_zoneM (aa_geom A) a -> ~ znull (aa_geom A) a -> a <> 0x173661 -> ~ in_rangesZ IMG_S a ->
                      rm rho3 (Z_to_bv 64 a) = rm rhoY (Z_to_bv 64 a)).
      { intros a Ba Hz1 Hz2 Hz3 Hz4. unfold rho3. apply rm_absorb_out. intros Hin.
        destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc'|[E1|SC]]]; rewrite ?u64_lit in * by exact Ba.
        - apply in_app_or in Hk as [Hk|Hk].
          + apply Hz1. exact (N_m1_zone (aa_geom A) rhoY k a HG E151 E152 Hk Hr).
          + apply Hz4. unfold N_secc in Hk. cbn [In] in Hk. unfold IMG_S, in_rangesZ. unfold SEC_INST, ERRNO_A in *.
            destruct Hk as [E|[E|[]]]; subst k; cbn [spec_range fst snd eval] in Hr; rewrite (u64_lit 0) in Hr by lia.
            * exists 0xeddd8, (0xee044 - 0xeddd8). split; [cbn; tauto | lia].
            * exists 0xe9b28, 8. split; [cbn; tauto | lia].
        - exact (Hz2 Hc').
        - exact (Hz3 E1).
        - apply Hz4. unfold IMG_S, in_rangesZ. unfold SEC_INST in *. exists 0xeddd8, (0xee044 - 0xeddd8). split; [cbn; tauto | clear -SC; lia]. }
      destruct HRest as (Hsep & _).
      assert (CA : forall a, client_addrA CST A a -> 0 <= a < 2 ^ 64 -> ~ errno_addrA a -> rm rho3 (Z_to_bv 64 a) = rm rhoY (Z_to_bv 64 a)).
      { intros a Hcl Ba NE. destruct (client_addr_bounds CST HCST A a _ HG HF Hsep Hcl) as [B1 B2].
        apply RMO; [exact Ba | exact (client_not_rtM CST HCST HCSTM A a _ HG HF Hsep Hcl) | | |].
        -
          intros Hz. pose proof (client_not_rt CST HCST A a _ HG HF Hsep Hcl) as NR. unfold znull in Hz. unfold rt_zone in NR.
          assert (HzI : (SEC_INST + 64 <= a < 0xee040) \/ (0xee048 <= a < 0xee070) \/ a = 0x173660 \/ (ERRNO_A <= a < ERRNO_A + 4) \/ (SEC_INST + 32 <= a < SEC_INST + 48))
            by (unfold SEC_INST, ERRNO_A in *; clear -Hz NR; lia).
          clear Hz. unfold SEC_INST, ERRNO_A in HzI.
          destruct (client_addr_cases CST A a _ HF Hcl) as [S|[L|[FR|[C|FL]]]].
          + clear -S HzI ACV. lia.
          + destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in *. clear -Hx S2 HzI. lia.
          + destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M. cbn zeta in M.
            rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in *. clear -Hx M HzI. lia.
          + apply (HCSTS a C). unfold IMG_S, in_rangesZ. unfold SEC_INST, ERRNO_A in *.
            destruct HzI as [Hz|[Hz|[Hz|[Hz|Hz]]]].
            * exists 0xeddd8, (0xee044 - 0xeddd8). split; [cbn; tauto | clear -Hz; lia].
            * exists 0xee048, (0xee070 - 0xee048). split; [cbn; tauto | clear -Hz; lia].
            * exists 0x173660, 2. split; [cbn; tauto | clear -Hz; lia].
            * exfalso. apply NE. unfold errno_addrA, ERRNO_A. clear -Hz. lia.
            * exists 0xeddd8, (0xee044 - 0xeddd8). split; [cbn; tauto | clear -Hz; lia].
          + destruct FL as (c & p & Hcp & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M. cbn zeta in M.
            rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *. unfold IMG_HI in *. clear -M HzI. lia.
        - intros E1.
          destruct (client_addr_cases CST A a _ HF Hcl) as [S|[L|[FR|[C|FL]]]].
          + clear -S E1 ACV. lia.
          + destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in *. clear -Hx S2 E1. lia.
          + destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M. cbn zeta in M.
            rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in *. clear -Hx M E1. lia.
          + apply (HCSTS a C). unfold IMG_S, in_rangesZ. exists 0x173660, 2. split; [cbn; tauto | clear -E1; lia].
          + destruct FL as (c & p & Hcp & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M. cbn zeta in M.
            rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *. unfold IMG_HI in *. clear -M E1. lia.
        - intros HI.
          assert (HIr : 0x10000 <= a < IMG_HI).
          { destruct HI as (b & n & Hbn & Hx). unfold IMG_S in Hbn. unfold SEC_INST, ERRNO_A, IMG_HI in *. cbn [In] in Hbn.
            destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hx; lia. }
          unfold IMG_HI in HIr.
          exact (HCSTS a ltac:(destruct (client_addr_cases CST A a _ HF Hcl) as [S|[L|[FR|[C|FL]]]];
              [ clear -S HIr ACV; exfalso; lia
              | destruct L as (b & n & Hbn & Hx); destruct (Hsep b n Hbn) as (S1 & S2 & _); unfold IMG_HI in *; exfalso; clear -Hx S2 HIr; lia
              | destruct FR as (c & p & Hcp & Hp & _ & Hx); pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M; cbn zeta in M;
                rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M; unfold IMG_HI in *; exfalso; clear -Hx M HIr; lia
              | exact C
              | destruct FL as (c & p & Hcp & Hp & _ & ->); pose proof (fs_geom_nums (aa_geom A) c p HG Hcp Hp) as M; cbn zeta in M;
                rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M; unfold fs_flags in *; rewrite FS_kFlagsOffset_val in *; unfold IMG_HI in *; exfalso; clear -M HIr; lia ]) HI). }
      split.
      - intros a Ba Hcl. destruct Hcl as [(C1 & _ & NE)|[C1 _]]; [exact (CA a C1 Ba NE)|].
        pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B0. unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
        apply RMO; [exact Ba | | | clear -B0; lia |].
        + unfold rt_zoneM, rt_zone, IMG_HI. intros [[R1|[R1|[R1|[R1|R1]]]]|R1].
          * destruct R1 as [R1 _]. clear -R1 B0. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 B0 TB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 B0 CB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 B0 DB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 B0 WF. lia.
          * pose proof (IMG_M_range a R1) as IR. unfold IMG_HI in *. clear -IR B0. lia.
        + pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. unfold znull, SEC_INST, ERRNO_A. clear -B0 TB. lia.
        + intros (b & n & Hbn & Hx). unfold IMG_S in Hbn. unfold SEC_INST, ERRNO_A in *. cbn [In] in Hbn.
          destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hx B0; lia.
      - intros x j Hx Hj Hdef.
        assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
        { destruct Hx as [[C1 C2]|GX].
          - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. clear -B. lia.
          - destruct (HXGL x GX) as [X0 X1]. unfold IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. clear -X0 X1. lia. }
        unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
        destruct (word_byte_range (Sh x) j ltac:(clear -Bx; lia) Hj) as (W1 & W2 & W3).
        unfold word_byte. rewrite RMO; [exact Hdef | clear -W1 W2 W3 Bx Hj; lia | | | clear -W1 W2 W3 Bx Hj; lia |].
        + unfold rt_zoneM, rt_zone, IMG_HI. intros [[R1|[R1|[R1|[R1|R1]]]]|R1].
          * destruct R1 as [R1 _]. clear -R1 W1 W2 W3 Bx Hj. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 W1 W2 W3 Bx Hj TB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 W1 W2 W3 Bx Hj CB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 W1 W2 W3 Bx Hj DB. lia.
          * pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. clear -R1 W1 W2 W3 Bx Hj WF. lia.
          * pose proof (IMG_M_range _ R1) as IR. unfold IMG_HI in *. clear -IR W1 W2 W3 Bx Hj. lia.
        + pose proof (geom_bands _ HG) as (WF & TB & CB & DB & _); rewrite FS_total_val in WF; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WF, TB, CB, DB. unfold znull, SEC_INST, ERRNO_A. clear -W1 W2 W3 Bx Hj TB. lia.
        + intros (b & n & Hbn & Hy). unfold IMG_S in Hbn. unfold SEC_INST, ERRNO_A in *. cbn [In] in Hbn.
          destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hy W1 W2 W3 Bx Hj; lia. }
    split; [exact HK|].
    intros c0 Hc0 Hor Hfr. unfold class_fresh in Hfr |- *. cbn [aa_cls bumpVK]. exact Hfr.
Qed.
End C5.

Section C6.
Hypothesis Wa : swf (SSa_S W st tmax) = true.
Hypothesis Da : state_diff (ax_S (E_s1 W st tmax 8)) (SSa_S W st tmax) = Some ([(neededx 8, SVar V_NS); (neededx 8, SVar V_NS)], []).
Hypothesis Wb : swf (SSb_S W st tmax) = true.
Hypothesis FB : forallb (sprop_below NW2) F_sgen = true.
Hypothesis CertS1 : check_cfgA segsA 4000%nat [0x7050c] GW [SS0 W st tmax] [ES1 W st tmax] = true.
Hypothesis WC1 : swf (ax_S (CS1 W st tmax)) = true.
Hypothesis DC1 : state_diff (ax_S (ES1 W st tmax)) (ax_S (CS1 W st tmax)) = Some ([(a1x, SVar V_MS)], []).
Hypothesis NXC1 : ss_next (ax_S (CS1 W st tmax)) = ss_next (ax_S (ES1 W st tmax)).
Hypothesis IC1 : instr_at segsA (ss_pc (ax_S (CS1 W st tmax))) = Some Ecall.
Hypothesis R17 : reg_sv (ax_S (CS1 W st tmax)) 17 = SLit 222.
Hypothesis R11 : reg_sv (ax_S (CS1 W st tmax)) 11 = SVar V_MS.
Hypothesis R10 : reg_sv (ax_S (CS1 W st tmax)) 10 = SLit 0.
Hypothesis R12 : reg_sv (ax_S (CS1 W st tmax)) 12 = SLit 3.
Hypothesis R13 : reg_sv (ax_S (CS1 W st tmax)) 13 = SLit 34.
Hypothesis R14 : reg_sv (ax_S (CS1 W st tmax)) 14 = SLit 18446744073709551615.
Hypothesis R15 : reg_sv (ax_S (CS1 W st tmax)) 15 = SLit 0.
Hypothesis NX1 : ss_next (ax_S (CS1 W st tmax)) = NW2.
Hypothesis XC1 : ax_X (CS1 W st tmax) = [].
Hypothesis SK1 : map skel (ss_objs (ax_S (CS1 W st tmax))) = map skel (((sw_s1 :: unwind_objs W ++ A_globals) ++ RT_m1) ++ RT_sec).
Hypothesis FC1 : incl ((((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_geom_fn) ++ F_s1) ++ F_fam tmax 8) (ss_facts (ax_S (CS1 W st tmax))).
Hypothesis CertSf : check_cfgA segsA 4000%nat [0x5e5d4] GW [ES1f W st tmax] [ESn W st tmax] = true.
Hypothesis RN : R_n W st tmax = RT_m1 ++ map carve_obj N_secn.
Hypothesis WRn : swf (stRn_S W st tmax) = true.
Hypothesis DKRn : state_diff (ax_S (stKn W st tmax)) (stRn_S W st tmax) = Some ([(SLit TP_A, SVar 24)], []).
Hypothesis NXRn : ss_next (stRn_S W st tmax) = ss_next (ax_S (stKn W st tmax)).
Hypothesis ENTn : entailsA (stRn W st tmax) (Lc_null W st) (s_n W st tmax) = true.
Hypothesis IDn : wsub_idc (s_n W st tmax) = true.

Theorem sec_spine : forall (ok : world -> Prop) (A : AA) (Kc : KcA) (Jo : word -> jpredA) rho tp Posts,
  let Q := LQPA segs NF rho tp Posts in
  (stopJ_w W st) -> stopJ_stable W st -> Kc_ok Kc ->
  ok_frameA segs ok (liftKA Kc) -> ok_pframeA segs ok (liftKA Kc) ->
  In (Lc_null W st, JLc_null CST XGL A Kc) Posts ->
  (forall rhoX tr ms md a, smatch_pendingA segs rhoX tp (CS1 W st tmax) (tr, mkCfg ms md) -> JG W st A Kc rho rhoX tp tr md ->
     mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a ->
     Jo a (rho_set_rw rhoX (ss_next (ax_S (CS1 W st tmax))) a) tp tr (with_vmmaps (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) md)) ->
  (forall rhoX (a : word), triple segs ok (SPA segs (Jo a) (ES1g W st tmax) (rho_set_rw rhoX (nxS W st tmax) a) tp) Q) ->
  forall rhoE, triple segs ok (SPA segs (JG W st A Kc rho) (E_s1 W st tmax 8) rhoE tp) Q.
Proof.
  intros ok A Kc Jo rho tp Posts Q HW HUS HKc Hokl Hokpl HPosts HJo HOK rhoE.
  assert (Hokf : ok_frameA segs ok (J W st A Kc)).
  { intros r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  eapply triple_conseq; [intros w Hw; exact (sec_inst nW st tmax Wa Da Wb FB A Kc rho tp w rhoE HW HUS HKc Hw) | intros w Hw; exact Hw |].
  apply (sec_cert1 CertS1 ok A Kc rho tp Q HUS HKc Hokf). intros rhoX.
  eapply triple_conseq; [intros w Hw; exact (sec_cs1 WC1 DC1 NXC1 A Kc rho tp w rhoX Hw) | intros w Hw; exact Hw |].
  apply (sec_ecall IC1 R17 R11 R10 R12 R13 R14 R15 NX1 XC1 SK1 FC1 ok A Kc Jo rho tp Q HW HUS HKc Hokl Hokpl HJo); [|exact HOK].
  intros rhoY. apply (sec_certf CertSf ok A Kc rho tp Q HUS HKc Hokf). intros rhoZ.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. exact (sec_null_finish RN WRn DKRn NXRn ENTn IDn A Kc rho tp w rhoZ Posts HKc HPosts Hw).
Qed.
End C6.

Section C7.
Hypothesis Wa : swf (SSa_S W st tmax) = true.
Hypothesis Da : state_diff (ax_S (E_s1 W st tmax 8)) (SSa_S W st tmax) = Some ([(neededx 8, SVar V_NS); (neededx 8, SVar V_NS)], []).
Hypothesis Wb : swf (SSb_S W st tmax) = true.
Hypothesis FB : forallb (sprop_below NW2) F_sgen = true.
Hypothesis NXS0 : (GW <= ss_next (ax_S (SS0 W st tmax)))%positive.
Hypothesis ECertS1 : check_ecfgA segsA 4000%nat [0x7050c] GW [mkVNA (SS0 W st tmax) 1 (SLit 0)] [mkVNA (ES1 W st tmax) 0 (SLit 0)] = true.
Hypothesis WC1 : swf (ax_S (CS1 W st tmax)) = true.
Hypothesis DC1 : state_diff (ax_S (ES1 W st tmax)) (ax_S (CS1 W st tmax)) = Some ([(a1x, SVar V_MS)], []).
Hypothesis NXC1 : ss_next (ax_S (CS1 W st tmax)) = ss_next (ax_S (ES1 W st tmax)).
Hypothesis IC1 : instr_at segsA (ss_pc (ax_S (CS1 W st tmax))) = Some Ecall.
Hypothesis R17 : reg_sv (ax_S (CS1 W st tmax)) 17 = SLit 222.
Hypothesis R11 : reg_sv (ax_S (CS1 W st tmax)) 11 = SVar V_MS.
Hypothesis R12 : reg_sv (ax_S (CS1 W st tmax)) 12 = SLit 3.
Hypothesis R13 : reg_sv (ax_S (CS1 W st tmax)) 13 = SLit 34.
Hypothesis R14 : reg_sv (ax_S (CS1 W st tmax)) 14 = SLit 18446744073709551615.
Hypothesis R15 : reg_sv (ax_S (CS1 W st tmax)) 15 = SLit 0.
Hypothesis NX1 : ss_next (ax_S (CS1 W st tmax)) = NW2.
Hypothesis NXS1f : (GW <= ss_next (ax_S (ES1f W st tmax)))%positive.
Hypothesis ECertSf : check_ecfgA segsA 4000%nat [0x5e5d4] GW [mkVNA (ES1f W st tmax) 1 (SLit 0)] [mkVNA (ESn W st tmax) 0 (SLit 0)] = true.
Hypothesis FC1 : incl ((((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_geom_fn) ++ F_s1) ++ F_fam tmax 8) (ss_facts (ax_S (CS1 W st tmax))).
Hypothesis RN : R_n W st tmax = RT_m1 ++ map carve_obj N_secn.
Hypothesis WRn : swf (stRn_S W st tmax) = true.
Hypothesis DKRn : state_diff (ax_S (stKn W st tmax)) (stRn_S W st tmax) = Some ([(SLit TP_A, SVar 24)], []).
Hypothesis NXRn : ss_next (stRn_S W st tmax) = ss_next (ax_S (stKn W st tmax)).
Hypothesis ENTn : entailsA (stRn W st tmax) (Lc_null W st) (s_n W st tmax) = true.
Hypothesis IDn : wsub_idc (s_n W st tmax) = true.

Lemma ecfg_cutS : forall fuel cutpcs g (cuts exits : list vnodeA) (Jx : jpredA) (Q : world -> Prop) tp (C : axst) rho,
  stableA segs g Jx ->
  (forall n, In n cuts -> (g <= ss_next (ax_S (vna_state n)))%positive) ->
  check_ecfgA segs fuel cutpcs g cuts exits = true ->
  (forall E rho', In E exits ->
     etriple segs (SPA segs Jx (vna_state E) rho' tp) (fun w => SPfamEA segs (map (to_enodeA Jx) cuts) tp (vmeasA E rho') w \/ Q w)) ->
  In (mkVNA C 1 (SLit 0)) cuts ->
  etriple segs (SPA segs Jx C rho tp) Q.
Proof. intros fuel cutpcs g cuts exits Jx Q tp C rho HS HN HC HE HI. exact (cfg_complete_autoA segs fuel cutpcs g cuts exits Jx Q tp HS HN HC HE (mkVNA C 1 (SLit 0)) rho HI). Qed.

Theorem esec_tail_null : forall (A : AA) (Kc : KcA) rho tp Posts,
  stopJ_stable W st -> Kc_ok Kc ->
  In (Lc_null W st, JLc_null CST XGL A Kc) Posts ->
  forall rhoX, etriple segs (SPA segs (JG W st A Kc rho) (ES1f W st tmax) rhoX tp) (LQPA segs NF rho tp Posts).
Proof.
  intros A Kc rho tp Posts HUS HKc HPosts rhoX.
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  apply (ecfg_cutS 4000%nat [0x5e5d4] GW [mkVNA (ES1f W st tmax) 1 (SLit 0)] [mkVNA (ESn W st tmax) 0 (SLit 0)] (JG W st A Kc rho) _ tp (ES1f W st tmax) rhoX HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact NXS1f.
  - exact ECertSf.
  - intros E' rhoY HinE. destruct HinE as [<-|[]]. cbn [vna_state].
    intros w Hw. exists w. split; [apply wsteps_refl|]. right.
    exact (sec_null_finish RN WRn DKRn NXRn ENTn IDn A Kc rho tp w rhoY Posts HKc HPosts Hw).
  - left. reflexivity.
Qed.
End C7.

End SEC2.
End SpineCallocSec2.

(* [comment removed for export] *)
Module SpineMallocEiW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "SLit"; "sprop"; "SPUle"; "SVar"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "ax_add_facts"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_RZ"; "C9"; "C9p"; "C1g"; "C2p"; "C2r"; "C3"; "C5"; "C5b"; "C5c"; "C5d"; "C5e"; "C6"; "C6b"; "C6l"; "C7"; "C7p"; "C8"; "C8p"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "P0_s1"; "F_hi"; "F_lo"; "s1_cuts"; "s1_exits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocS9jW2"; "F9a_nf"; "F9b_nf"; "F9pa_nf"; "F9pb_nf"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocS9jW2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S5S0S0S2S0S18VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C1g W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C1g] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C1g]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S5S0S0S2S0S19VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C2p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C2p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C2p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S5S0S0S2S0S1aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C2r W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C2r] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C2r]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S5S0S0S2S0S1bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C3 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C3] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C3]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S5S0S0S2S0S1cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S5S0S0S2S0S1dVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S5S0S0S2S0S1eVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5c W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5c] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5c]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S5S0S0S2S0S1fVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5d W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5d] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5d]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S5S0S0S2S0S20VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5e W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5e] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5e]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S5S0S0S2S0S21VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C6]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S5S0S0S2S0S23VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6l W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6l] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C6l]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S5S0S0S2S0S22VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C6b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S5S0S0S2S0S24VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C7 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C7] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C7]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_13 : ltac2:(tb__ "0|0|
S5S0S0S2S0S25VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C7p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C7p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C7p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_14 : ltac2:(tb__ "0|0|
S5S0S0S2S0S26VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C8]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_15 : ltac2:(tb__ "0|0|
S5S0S0S2S0S27VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C8p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_16 : ltac2:(tb__ "0|0|
S5S0S0S2S0S16VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C9]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_17 : ltac2:(tb__ "0|0|
S5S0S0S2S0S17VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C9p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.

Lemma NXhi_0 : ltac2:(tb__ "0|0|
SbS3S6S1S29VW;Vst;S2aA3A1A1A2").
Proof. apply Pos.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXlo_0 : ltac2:(tb__ "0|0|
SbS3S6S1S29VW;Vst;S2bA3A1A1A2").
Proof. apply Pos.leb_le. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1g_0 : ltac2:(tb__ "0|0|
SbS3S6S1S18VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C1g W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC2p_0 : ltac2:(tb__ "0|0|
SbS3S6S1S19VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C2p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC2r_0 : ltac2:(tb__ "0|0|
SbS3S6S1S1aVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C2r W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC3_0 : ltac2:(tb__ "0|0|
SbS3S6S1S1bVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C3 W st tmax) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC5_0 : ltac2:(tb__ "0|0|
SbS3S6S1S1cVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5 W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC5b_0 : ltac2:(tb__ "0|0|
SbS3S6S1S1dVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5b W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC5c_0 : ltac2:(tb__ "0|0|
SbS3S6S1S1eVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5c W st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC5d_0 : ltac2:(tb__ "0|0|
SbS3S6S1S1fVW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5d W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC5e_0 : ltac2:(tb__ "0|0|
SbS3S6S1S20VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C5e W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC6_0 : ltac2:(tb__ "0|0|
SbS3S6S1S21VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C6 W st tmax) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC6l_0 : ltac2:(tb__ "0|0|
SbS3S6S1S23VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C6l W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
SbS3S6S1S22VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C6b W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC7_0 : ltac2:(tb__ "0|0|
SbS3S6S1S24VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C7 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC7p_0 : ltac2:(tb__ "0|0|
SbS3S6S1S25VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C7p W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXCC8_0 : ltac2:(tb__ "0|0|
SbS3S6S1S26VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C8 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXCC8p_0 : ltac2:(tb__ "0|0|
SbS3S6S1S27VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C8p W st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECert1_0 : ltac2:(tb__ "0|3|
S2S12SeS4Ufa0S10S14Z40a18S11S14A1A3S3S28S0ScS0SdR1Z1S7Z0M0A1M1A3Lc;S2cU2M2Vst;A2A4S28S0ScS0SdR1G0G1A3Le;S2dG2Vst;Vtmax;A3A4A6S13A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S2S12SeS4Ufa0S11S14A1S3S10ScSdSfS10S8S9S7Z20A1SaS15A1A2S11S8A1A3S16VW;Vst;Vtmax;A3A2Z1S7Z0M0A1M1A3S11ScA1M2A3S10ScSdS2eG0G1A3G2A3A6S13A3").
Proof. memo_rw (C9 W st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S2S12SeS4Ufa0S11S14A1S3S10ScSdSfS10S8S9SaS15A1S7Z10A1A2S11S8A1A3S16VW;Vst;Vtmax;A3A2Z1S7Z0M0A1M1A3S11ScA1M2A3S10ScSdS2fG0G1A3G2A3A6S13A3").
Proof. memo_rw (C9 W st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECert9pa_0 : ltac2:(tb__ "0|3|
S2S12SeS4Ufa0S11S14A1S3S10ScSdSfS10S8S9S7Z20A1SaS15A1A2S11S8A1A3S17VW;Vst;Vtmax;A3A2Z1S7Z0M0A1M1A3S11ScA1M2A3S10ScSdS30G0G1A3G2A3A6S13A3").
Proof. memo_rw (C9p W st tmax) memo_17. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECert9pb_0 : ltac2:(tb__ "0|3|
S2S12SeS4Ufa0S11S14A1S3S10ScSdSfS10S8S9SaS15A1S7Z10A1A2S11S8A1A3S17VW;Vst;Vtmax;A3A2Z1S7Z0M0A1M1A3S11ScA1M2A3S10ScSdS31G0G1A3G2A3A6S13A3").
Proof. memo_rw (C9p W st tmax) memo_17. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocEiW2.

(* [comment removed for export] *)
Module F0A_exit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "iff"; "False"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "mul"; "sub"; "modulo"; "of_nat"; "div"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "rw"; "eval"; "sv"; "obj_range"; "cell"; "sprop"; "valuation"; "rm"; "rl"; "soff"; "c_width"; "ss_facts"; "c_off"; "ob_dflt"; "odefault"; "DUnknown"; "SLit"; "c_val"; "ob_base"; "ob_cells"; "ss_next"; "DZero"; "SAlu"; "SVar"; "agree_below"; "dflt_writable"; "enc_bytes"; "obj_hi_of"; "obj_lo_of"; "smatch"; "ss_objs"; "swf"; "@Corelib.Init.Datatypes"; "prod"; "list"; "pair"; "nil"; "bool"; "cons"; "true"; "option"; "Some"; "fst"; "app"; "length"; "nat"; "snd"; "false"; "None"; "andb"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "nocellsF"; "RSHAPE"; "NRTX"; "FQX"; "S_bh"; "S_hdr"; "S_pc"; "LCELLS"; "NBX"; "S_qc"; "ITX"; "rcellb"; "rclsb"; "rshpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "aa_q_thread"; "aa_live"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_geom"; "aa_internal_inited"; "qb_addr"; "qb_items"; "ageom"; "aa_cache_inited"; "aa_cls"; "aa_frames"; "aa_fs_busy"; "aa_fs_hint"; "aa_ptr_committed"; "aa_q_global"; "aa_sec"; "ag_ctx"; "ag_stack_bottom"; "ag_stack_top"; "ag_thread"; "class_state"; "cls_kept_freeA"; "qb_size"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "qvar"; "QA"; "QBf"; "O_blkN"; "O_pckF"; "O_sh"; "O_stQ"; "O_stT1"; "O_stT2"; "QBe"; "VOBJ"; "cA"; "cQ"; "cp_baseF"; "shb"; "vN8"; "vN8g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "lastq"; "cnt24"; "rhoF_of"; "j_min"; "top24"; "cache24"; "junkF"; "qcond"; "firstq"; "hw_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "chg_f"; "freeQ"; "leaf_cells"; "freeA"; "IMG_F"; "nb_addr"; "rt_zoneF"; "AInvB"; "kA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "client_addrA"; "client_shadowA"; "AE_A"; "L_free"; "JL_free"; "KcA"; "tp_ok"; "mem_keptA"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "in_rangesZ"; "view"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"; "IA_BEG"; "IA_END"; "geom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue"; "spec_range"; "spec_small"; "coverb"; "spec_covered"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "cells_in_view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit"; "sv_varsb"; "Pnrtx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "depot_onlyKf"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "HIGH_SHADOW_END"; "kQuarantineMin"; "Sh"; "kQuarantineBatchCount"; "kSpaceSize"; "IMG_HI"; "Size"; "kQuarantineCacheMax"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "O_item"; "O_nb"; "item_base"; "nb_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "vmd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls"; "blk_cls"; "blk_geo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.F0A_exit.EXIT.FIN"; "rebuilt_stmt"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "rho_absorb"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "vT"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundW SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv ReprGlue Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 RebuildM InvLaws SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint sv_varsb (P : positive -> bool) (e : sv) : bool :=
  match e with
  | SLit _ => true
  | SVar i => P i
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => sv_varsb P a && sv_varsb P b
  | SExt _ _ a => sv_varsb P a
  | SLBytes _ i _ => sv_varsb P i
  end.
Lemma eval_agree_P : ltac2:(tb__ "0|1|
S1S38F_;S1aS1aS16S1S2S38R5R1A1S3aA3S2S45Q40A1M0S14R5R2A2S14R4R2A2A3F_;Fi;S1S2S35S45Q8A1A1S1cR5R1A2S1cR4R1A2A3Fl;S2S38Sc0R6R3A2S3aA3S2G0S15R6R4A2S15R5R4A2A3F_;F_;F_;Fe;Fr2;Fr1;FP;").
Proof.
  intros P r1 r2 e HP HL. induction e; cbn; intros Hb; try (apply andb_prop in Hb as [Hb1 Hb2]); try rewrite (IHe1 Hb1); try rewrite (IHe2 Hb2); try reflexivity.
  - apply HP. exact Hb.
  - rewrite (IHe Hb). reflexivity.
  - rewrite HL, (IHe Hb). reflexivity.
Qed.

Lemma nocells_range : ltac2:(tb__ "0|0|
S1aS13S2S34S0S0A2S17R2S4cR1A1A2S17R2R1A2A3Fo;Frho;").
Proof. intros rho [b lo hi cs d]. reflexivity. Qed.

Lemma NRTX_small : Forall spec_small NRTX.
Proof.
  unfold NRTX, N_rest, N_fn, spec_small. cbn [tl app].
  repeat apply Forall_cons; try apply Forall_nil; (split; [unfold QG, DPMCELL, MLIMCELL; lia|]); (split; [unfold QG, DPMCELL, MLIMCELL; lia|]); (split; [unfold QG, DPMCELL, MLIMCELL; lia|]);
    unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.
Lemma NRTX_coverb : ltac2:(tb__ "0|0|
S2S38S4aS87SbaS4eA3S3aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NRTX_lit : ltac2:(tb__ "0|3|
S0S0S35S34S34S0S40A2S16A2A1M0S48S34S34S34S16S0A2M1S0A2M2G0A2S36G2G0S36G1S0S36S16S0S24Z0A1R3A4R2A4R1A4S4eA3S48S34S0S0A2S36S0S0R4SeR3R4A2A4S9cA3F_;Fcs;Fhi;Flo;").
Proof. intros lo hi cs Hk. unfold IMG_F. apply (lit_ranges_in NRT lo hi cs). apply NRTX_sub. exact Hk. Qed.

Lemma NRTX_zone : ltac2:(tb__ "0|4|
S65S1aS87S0Sb7R4A1S2S45Q40M0A1M1S14R4P97A2S46G0S71R5A1A2A3S2G1S14R5P98A2S46G0S6eR6A1A2A3S3SaZ0S47G0S14R6PcA2A2M2A2SbG2ScZ2Z2fA2A2A2S48S87R6S4eA3S3SaS3dS0S0Sb8R8R7A2M3A3R6A2SbR6S41S0S0G3A3A2A2S9eRaR7A2F_;F_;F_;F_;F_;F_;Fa;Fk;Frho;FG;").
Proof.
  intros G rho k a HG E151 E152 B12 Hk Ha.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range G) as TG.
  destruct k as [[[b lo] hi] cs]. destruct (sv_eqb b (SLit 0)) eqn:EB.
  - apply sv_eqb_sound in EB. subst b. right; left. exists lo, (hi - lo). split; [exact (NRTX_lit lo hi cs Hk)|].
    cbn [spec_range fst snd eval] in Ha. rewrite u64_lit in Ha by lia. lia.
  - unfold NRTX, N_rest, N_fn in Hk. cbn [tl app In] in Hk. unfold vT, vCTX, vTOP, vBOT, vSB, vMINq, iam_base in Hk. unfold rt_zoneF, rt_zone.
    repeat (destruct Hk as [E|Hk]; [injection E as <- <- <- <-; cbn in EB; try discriminate; cbn [spec_range fst snd eval] in Ha; rewrite ?E151, ?E152, ?u64_lit in Ha by lia |]).
    all: try (left; right; lia).
    +
      right; right. rewrite sll_val, srl_val in Ha. change (32 mod 64) with 32 in Ha. change (3 mod 64) with 3 in Ha.
      rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 in Ha by lia.
      pose proof (Z.div_lt_upper_bound (bv_unsigned (rw rho 12%positive)) (2 ^ 32) (2 ^ 15) ltac:(lia) ltac:(lia)).
      pose proof (Z.div_pos (bv_unsigned (rw rho 12%positive)) (2 ^ 32) ltac:(lia) ltac:(lia)).
      rewrite Z.mod_small in Ha by lia. unfold IA_BEG, IA_END. lia.
Qed.

Definition Pnrtx (i : positive) : bool := ltac2:(tb__ "0|0|
S4bS1Sd4Vi;A1S39S1PcS39S1P88S39S1P97S39S1P98S39S1P99S39S1P9aS39S1P9bS37S1A1A3A3A3A3A3A3A3A3").
Lemma NRTX_varsb : ltac2:(tb__ "0|5|
S2S38S4aS87S87S34S34S34S16S0A2M0S0A2M1S35S34S34S0S40A2M2S16A2M3A1M4A2S38Lk;R1G1G4G1S38Lp;R2G0S0G0S38Lp0;R2S16S0S44Sc0Sc1R2A2S4aG3G3G3S38Lc;R1G2S16G2S38Lp;R2S0S40Sc0Sc1R3A2Ln;Lz;X34x1Le;Lp;X34x1Lc;R5A3A2Lz0;Lb;X34x1Lz;Lp0;X34x1Lcs;Lp;X34x1Lk;S4eA3S3aA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma cell8_inj : ltac2:(tb__ "0|2|
Sb1S0S0S0SadR4SaeR3U8M0R2A3A2SadR5SaeR4G0R2A3A2S3SaZ0R4A2SbR4ScZ2Z40A2A2A2M1G1S2S0R6R5A3F_;F_;F_;F_;Fv';Fv;Fa;Fm;").
Proof.
  intros m a v v' H1 H2 B1 B2.
  assert (E : enc_bytes 8 (Z_to_bv 64 v) = enc_bytes 8 (Z_to_bv 64 v')).
  { apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [rewrite !enc_bytes_length; reflexivity|]. intros k Hk. rewrite enc_bytes_length in Hk.
    specialize (H1 k Hk). specialize (H2 k Hk). cbn [c_addr c_w c_val] in H1, H2. rewrite H1 in H2. injection H2 as E. exact E. }
  apply enc_bytes_inj_low in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64%N) with (2 ^ 64) in E.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in E. rewrite !Z.mod_mod, !Z.mod_small in E by lia. exact E.
Qed.

Lemma add_lit : ltac2:(tb__ "0|1|
S0S0S2S45Q40M0A1Se1SdaS46G0R2A2S46G0R1A2A3S46G0S9R2R1A2A2A3Fb;Fa;").
Proof.
  intros a b. apply bv_eq. rewrite add_val, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. change (bv_modulus 64%N) with (2 ^ 64).
  rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma eval_add : ltac2:(tb__ "0|3|
S1aS16S16S0S0S2S45Q40M0A1M1S15R5R4A2S46G0R2A2M2A3S2G1S15R6R4A2G2A3S2G1S15R7S2aSdaR6R5A3A2S46G0S9R4R3A2A2A3F_;F_;Fb;Fa;Fe2;Fe1;Frho;").
Proof. intros rho e1 e2 a b H1 H2. cbn [eval]. rewrite H1, H2. apply add_lit. Qed.
Lemma of_unsigned : ltac2:(tb__ "0|2|
S45Q40M0A1M1S0S2S0S47G0R2A2R1A3S2G1R3S46G0R2A2A3F_;Fv;Fx;").
Proof. intros x v <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Section EXIT.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S0SafVCST;R1A2S4SafS9cR2A2S3SaSb5R2A2SbR2Sb6A2A2A2S8F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variable nW : nat. Variable st : ustop. Variable q : qvar.
Let W : list ulink := Wcan nW.

Variables (Xf XM XK XR : axst) (KEPT REST : list sobj) (sX : wsub) (XEX : list axform).
Hypothesis AXE : ltac2:(tb__ "0|0|
S2S3bS8aA1SeaVXf;VXEX;A2S3cS8aVXM;A2A3").
Hypothesis OBJS : ltac2:(tb__ "0|0|
S2S35S13A1S32S89VXM;A1A1S3eS13VKEPT;VREST;A3A3").
Hypothesis EQK : ltac2:(tb__ "0|0|
S2S8aS8bVXM;Se9S89VXM;A1VKEPT;A2A2VXK;A3").
Hypothesis WXR : ltac2:(tb__ "0|0|
S2S38S33S89VXR;A1A1S3aA3").
Hypothesis DXR : ltac2:(tb__ "0|4|
S2S3bS34S35S34S16S16A2M0A1M1S35S19A1M2A2M3A1Se5S89VXK;A1S89VXR;A1A2S3cG3S36G1G2S39G0S36S16S16S24SebA1S2bP18A1A4S37G0A1A3S37S19A1A4A2A3").
Hypothesis NXR : ltac2:(tb__ "0|0|
S2S1S28S89VXR;A1A1S28S89VXK;A1A1A3").
Hypothesis EQR : ltac2:(tb__ "0|0|
S2S8aS8bVXK;S89VXR;A1A2VXR;A3").
Hypothesis ENT : ltac2:(tb__ "0|0|
S2S38S8cVXR;Sa7Sa6VW;Vst;A3VsX;A3S3aA3").
Hypothesis SID : ltac2:(tb__ "0|0|
S2S38Se8VsX;Sb2A2S3aA3").
Hypothesis RCLS : ltac2:(tb__ "0|0|
S2S38S58Vq;VREST;A2S3aA3").
Hypothesis RCIV : rcivb REST = true.
Hypothesis RCELL : ltac2:(tb__ "0|0|
S2S38S57Vq;VREST;A2S3aA3").
Hypothesis RWR : rwrb REST = true.
Hypothesis RSHP : ltac2:(tb__ "0|0|
S2S38S59Vq;VREST;A2S3aA3").

Section FIN.
Variables (A : AA) (Kc : KcA) (rho : valuation) (tp : list word) (p n t : Z) (jv : junkF) (keep : Z -> Prop).
Variables (A' : AA) (rho1' rhoE : valuation) (tpE : list word) (tr : list event) (ms : machine_state) (md : Model).
Let rho1 : valuation := ltac2:(tb__ "0|0|
S90VA;Vrho;Vp;Vn;Vt;Vjv;A6").
Let w : world := ltac2:(tb__ "0|0|
S36S35SbcA1Sd8Vtr;Sd9Vms;Vmd;A2A4").
Hypothesis HKc : Kc_ok Kc.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S2S0S47Q40S14Vrho;PcA2A2Vp;A3").
Hypothesis Hn13 : ltac2:(tb__ "0|0|
S2S0S47Q40S14Vrho;PdA2A2Vn;A3").
Hypothesis HL : ltac2:(tb__ "0|0|
S48S34S0S0A2S36S0S0Vp;Vn;A4S5cVA;A1A3").
Hypothesis HCL : blk_cls p n.
Hypothesis Hii : aa_internal_inited A = true.
Hypothesis QC : qcond q A.
Hypothesis HR : rigF rho rho1.
Hypothesis HJMIN : ltac2:(tb__ "0|0|
S2S0S91Vjv;A1Sc6A3").
Hypothesis HDO : depot_onlyKf A A'.
Hypothesis HLK : ltac2:(tb__ "0|0|
Sd2Vkeep;Vrho1;Vrho1';A3").
Hypothesis HKEEP : ltac2:(tb__ "0|0|
S0S4Sa4VCST;VA;R1A3Sa5VCST;VXGL;VA;R1A4A2Vkeep;R2A1F_;Fa;").
Hypothesis H : ltac2:(tb__ "0|0|
Sa1Vsegs;Sc2VnW;Vst;S42VA';VKc;Vrho1';A6VXf;VrhoE;VtpE;Vw;A6").

Let G : ageom := aa_geom A. Let T : Z := ag_thread G. Let SB : Z := ag_spacebeg G.
Let KJ : jpredA := ltac2:(tb__ "0|0|
S1aS35S45Q40A1A1S35SbcA1SbdVKc;R2R1A2Lm0;Lt0;L_;L_;").
Let rho3 : valuation := ltac2:(tb__ "0|0|
Se7VrhoE;VREST;SdbVmd;VtpE;Vms;A3A3").
Let v3 : bview := ltac2:(tb__ "0|0|
Sb0Vsegs;S1bVrho3;A1A2").
Let vE : bview := ltac2:(tb__ "0|0|
Sb0Vsegs;S1bVrhoE;A1A2").
Let qbF : Z := qb_addr (lastq A).
Let nbF : Z := nb_addr A.

Lemma HAG : ltac2:(tb__ "0|0|
S2cSb3Vrho1';VrhoE;A3"). Proof. destruct H as [_ [Hag _]]. exact Hag. Qed.
Lemma ERW : ltac2:(tb__ "0|0|
S1Sd3R1Sb3A2S2S45Q40A1S14VrhoE;R2A2S14Vrho1;R2A2A3F_;Fi;").
Proof. intros i Hi. destruct HAG as (Hw & _ & _). destruct HLK as (Lw & _). rewrite <- (Hw i Hi). apply Lw. Qed.
Lemma ERL : ltac2:(tb__ "0|0|
S1S2S35S45Q8A1A1S1cVrhoE;R1A2S1cVrho1;R1A2A3Fl;").
Proof. intros l. destruct HAG as (_ & Hl & _). destruct HLK as (_ & Ll & _). rewrite <- (Hl l). apply Ll. Qed.
Lemma HJ' : ltac2:(tb__ "0|0|
S3VAInv;VA';VrhoE;VtpE;Vmd;A4S3VKc;Vtr;Vmd;A2SaaVA';VrhoE;A2A2A2").
Proof. destruct H as [_ [_ HJ]]. destruct HJ as (HA & _ & _ & HK & Htp & _). split; [exact HA | split; [exact HK | exact Htp]]. Qed.

Lemma DEQ : ltac2:(tb__ "0|2|
S3S2S65S61VA';A1S61VA;A1A3S3S2S35S72A1S67VA';A1S67VA;A1A3S3S2S38S66VA';A1S66VA;A1A3S3S2S35S75A1S6dVA';A1S6dVA;A1A3S3S2S0S6bVA';A1S6bVA;A1A3S3S2S35S34S0S0A2A1M0S5cVA';A1S5cVA;A1A3S3S2S35S5aA1M1S5bVA';A1S5bVA;A1A3S3S2G1S6cVA';A1S6cVA;A1A3S3S2S38S62VA';A1S62VA;A1A3S3S2S35G0A1S69VA';A1S69VA;A1A3S3S2S35S0A1S6aVA';A1S6aVA;A1A3S3S2S0S60VA';A1S60VA;A1A3S3S2S0S5fVA';A1S5fVA;A1A3S2S0S5eVA';A1S9S5eVA;A1Z1A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. exact HDO. Qed.
Lemma HL' : ltac2:(tb__ "0|0|
S48S34S0S0A2S36S0S0Vp;Vn;A4S5cVA';A1A3"). Proof. destruct DEQ as (_ & _ & _ & _ & _ & EL & _). rewrite EL. exact HL. Qed.
Lemma QC' : qcond q A'.
Proof.
  destruct DEQ as (EG & EC & ECI & _ & _ & _ & EQT & _). unfold qcond, lastq, cache24 in QC |- *. rewrite EQT, EC, ECI. exact QC.
Qed.
Lemma Hii' : aa_internal_inited A' = true. Proof. destruct DEQ as (_ & _ & _ & _ & _ & _ & _ & _ & EII & _). rewrite EII. exact Hii. Qed.
Lemma Elastq : ltac2:(tb__ "0|0|
S2S5aS8eVA';A1S8eVA;A1A3"). Proof. unfold lastq. destruct DEQ as (_ & _ & _ & _ & _ & _ & EQT & _). rewrite EQT. reflexivity. Qed.
Lemma Enb : ltac2:(tb__ "0|0|
S2S0S9dVA';A1S9dVA;A1A3"). Proof. unfold nb_addr, top24, cache24. destruct DEQ as (EG & EC & _). rewrite EG, EC. reflexivity. Qed.
Lemma Ecnt24 : ltac2:(tb__ "0|0|
S2S0S8fVA';A1S8fVA;A1A3"). Proof. unfold cnt24, cache24. destruct DEQ as (_ & EC & _). rewrite EC. reflexivity. Qed.
Lemma Ecache24 : ltac2:(tb__ "0|0|
S2S35S0A1S93VA';A1S93VA;A1A3"). Proof. unfold cache24. destruct DEQ as (_ & EC & _). rewrite EC. reflexivity. Qed.
Lemma CHG' : ltac2:(tb__ "0|0|
S0S7S98Vq;VA';Vp;Vn;R1A5S98Vq;VA;Vp;Vn;R1A5A2Fz;").
Proof.
  intros z. unfold chg_f. rewrite Enb, Ecnt24. destruct DEQ as (EG & _ & _ & _ & _ & _ & EQT & _). rewrite EG, EQT. tauto.
Qed.

Lemma Ev : ltac2:(tb__ "0|1|
S1S45Q40A1M0Sd3R2Sb3A2S2G0S14Vrho1;R3A2R2A3S2G0S14VrhoE;R4A2R3A3F_;F_;Fv;Fi;").
Proof. intros i v Hi E. rewrite (ERW i Hi). exact E. Qed.
Lemma E12 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;PcA2S46G0Vp;A2A3").
Proof. rewrite (ERW 12%positive) by (unfold GW; lia). change (rw rho1 12%positive) with (rw rho 12%positive). rewrite <- Hp12. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma E13 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;PdA2S46G0Vn;A2A3").
Proof. rewrite (ERW 13%positive) by (unfold GW; lia). change (rw rho1 13%positive) with (rw rho 13%positive). rewrite <- Hn13. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma E151 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P97A2S46G0VT;A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E152 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P98A2S46G0S6eVG;A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E153 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P99A2S46G0S70VG;A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E154 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P9aA2S46G0S6fVG;A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E155 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P9bA2S46G0VSB;A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E105 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P69A2S46G0S8dVn;A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E106 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P6aA2S46G0S11S8dVn;A1Z8A2A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E103 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P67A2S46G0SfVn;ScZ2Z20A2A2A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E107 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P6bA2S46G0S9S97Vt;Vn;A2Z1A2A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E120 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P78A2S46G0S10S3fS5aS5bVA;A1A2A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E121 : ltac2:(tb__ "0|1|
S5S2S35S5aA1S5bVA;A1S37S5aA1A3A1S2S45Q40M0A1S14VrhoE;P79A2S46G0S63S96VA;A1A1A2A3F_;").
Proof. intros HNE. apply Ev; [unfold GW; lia |]. unfold rho1, rhoF_of. cbn [rho_sets rw]. destruct (aa_q_thread A); [congruence | reflexivity]. Qed.
Lemma E122 : ltac2:(tb__ "0|1|
S5S2S35S5aA1S5bVA;A1S37S5aA1A3A1S2S45Q40M0A1S14VrhoE;P7aA2S46G0S63S8eVA;A1A1A2A3F_;").
Proof. intros HNE. apply Ev; [unfold GW; lia |]. unfold rho1, rhoF_of. cbn [rho_sets rw]. destruct (aa_q_thread A); [congruence | reflexivity]. Qed.
Lemma E123 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P7bA2S46G0Sb4S5bVA;A1A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E124 : rw rhoE 124%positive = Z_to_bv 64 0. Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E125 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P7dA2S46G0S74S8eVA;A1A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E126 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P7eA2S46G0S10S3fS34S0S0A2S64S8eVA;A1A1A2A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E127 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P7fA2S46G0S8fVA;A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E128 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P80A2S46G0ScdZ18A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E129 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P81A2S46G0ScbZ18A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E130 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P82A2S46G0S92VA;A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.
Lemma E136 : ltac2:(tb__ "0|1|
S2S45Q40M0A1S14VrhoE;P88A2S46G0S91Vjv;A1A2A3"). Proof. apply Ev; [unfold GW; lia | reflexivity]. Qed.

Lemma E107' : ltac2:(tb__ "0|1|
S6S0S0S3S3SaZ0R1A2SbR1Z100M0A2A2S3S2S0SfR1Z4A2Z1A3S2S0S47Q40S14VrhoE;P6bA2A2S9S9Z3SdG0R1A2A2SdZ10000S11Vn;ScZ2Z20A2A2A2A2A3A2A2Lt';A2").
Proof.
  destruct HR as [HAG (t' & T1 & T2 & T3) _ _ _ _ _ E107r _ _].
  assert (E13r : bv_unsigned (rw rho1 13%positive) = n) by (change (rw rho1 13%positive) with (rw rho 13%positive); exact Hn13).
  rewrite E13r in T3. exists t'. split; [exact T1|]. split; [exact T2|]. rewrite (ERW 107%positive) by (unfold GW; lia). rewrite E107r, T3. lia.
Qed.

Lemma TB : ltac2:(tb__ "0|1|
S3SaZ1000M0VT;A2SaS9VT;G0A2Z7fffff800000A2A2").
Proof.
  pose proof (proj1 HJ') as (HG & _). destruct DEQ as (EG & _). rewrite EG in HG. pose proof (geom_numsS _ HG) as (_ & _ & _ & T1 & T2 & _).
  pose proof (topG_range (aa_geom A)) as TG. unfold T, G. clear -T1 T2 TG. lia.
Qed.
Lemma EvT : ltac2:(tb__ "0|0|
S2S0S47Q40S15VrhoE;SecA2A2VT;A3"). Proof. pose proof TB as [TB1 TB2]. cbn [eval vT]. rewrite E151. apply u64_lit. lia. Qed.
Lemma EcQ : ltac2:(tb__ "0|0|
S2S0S47Q40S15VrhoE;S82A2A2S9VT;Z50A2A3").
Proof. pose proof TB as [TB1 TB2]. cbn [eval cQ vT]. rewrite E151, add_val, !u64_lit by lia. apply Z.mod_small. lia. Qed.
Lemma EcA : ltac2:(tb__ "0|0|
S2S0S47Q40S15VrhoE;S81A2A2S9VT;Zd0A2A3").
Proof. pose proof TB as [TB1 TB2]. cbn [eval cA vT]. rewrite E151, add_val, !u64_lit by lia. apply Z.mod_small. lia. Qed.
Lemma Eshb : ltac2:(tb__ "0|0|
SaZ10Vp;A2SbVp;Z7fffff800000A2S2S0S47Q40S15VrhoE;S84A2A2Sc7Vp;A1A3F_;F_;").
Proof.
  intros P1 P2. cbn [eval shb]. rewrite E12, add_val, srl_val, !u64_lit by (unfold SHADOW_OFF; lia). change (3 mod 64) with 3.
  rewrite Z.shiftr_div_pow2 by lia. unfold Sh, SHADOW_OFF. pose proof (Z.div_lt_upper_bound p (2 ^ 3) (2 ^ 44) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos p (2 ^ 3) ltac:(lia) ltac:(lia)). rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma E105s : ltac2:(tb__ "0|1|
SaZ1Vn;A2SbS9Vp;S8dVn;A1M0A2Z7fffff800000A2SaZ0Vp;A2S2S0S1dVrhoE;S85A2G0A3F_;F_;F_;").
Proof. intros N1 N2 N3. pose proof (N8_facts n N1) as (X1 & X2 & X3 & _). apply soff_of_val; [cbn [eval vN8]; rewrite E105; apply u64_lit; lia | lia]. Qed.
Lemma E106s : ltac2:(tb__ "0|1|
SaZ1Vn;A2SbS9Vp;S8dVn;A1M0A2Z7fffff800000A2SaZ0Vp;A2S2S0S1dVrhoE;S86A2S11G0Z8A2A3F_;F_;F_;").
Proof.
  intros N1 N2 N3. pose proof (N8_facts n N1) as (X1 & X2 & X3 & _). pose proof (Z.div_pos (N8 n) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (N8 n) 8 (N8 n) ltac:(lia) ltac:(lia)).
  apply soff_of_val; [cbn [eval vN8g]; rewrite E106; apply u64_lit; lia | lia].
Qed.
Lemma EITX : ltac2:(tb__ "0|1|
S5S2S35S5aA1S5bVA;A1S37S5aA1A3A1S63S8eVA;A1M0A1S0S10S3fS34S0S0A2S64G0A1A2A1S0SaZ0R2A2SaS9R3Z2000A2Z7fffff800000A2SaR3Sc8A2S2S0S47Q40S15VrhoE;S56A2A2S9R5SdZ8R4A2A2A3F_;F_;F_;Tk;Tqb;F_;").
Proof.
  intros HNE qb k Q1 Q2 Q3. unfold kQuarantineBatchCount in Q3. cbn [eval ITX]. rewrite (E122 HNE), E126. fold qb k.
  rewrite add_val, sll_val, !u64_lit by lia. change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (k * 2 ^ 3)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma Eitem : ltac2:(tb__ "0|1|
S5S2S35S5aA1S5bVA;A1S37S5aA1A3A1S63S8eVA;A1M0A1S0S10S3fS34S0S0A2S64G0A1A2A1S0SaZ0R2A2SaS9R3Z2000A2Z7fffff800000A2SaR3Sc8A2S2S0S47Q40S15VrhoE;Sd0A2A2S9R5SdZ8R4A2A2A3F_;F_;F_;Tk;Tqb;F_;").
Proof.
  intros HNE qb k Q1 Q2 Q3. unfold kQuarantineBatchCount in Q3. cbn [eval item_base add vQB vK]. rewrite (E122 HNE), E126. fold qb k.
  rewrite add_val, sll_val, !u64_lit by lia. change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (k * 2 ^ 3)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma Ecp : ltac2:(tb__ "0|2|
S3SaZ1M0S8fVA;A1M1A2SaG1Z2A2A2S2S0S47Q40S15VrhoE;S83A2A2S9S9VT;Zd0A2SdZ4SeG1G0A2A2A2A3F_;").
Proof.
  intros HC. pose proof TB as [TB1 TB2]. cbn [eval cp_baseF cA vT vPK]. rewrite E151, E127.
  rewrite !add_val, sll_val, add_val, (lit_unsigned (-1)), !u64_lit by lia. change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by lia.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
  replace ((cnt24 A + (2 ^ 64 - 1)) mod 2 ^ 64) with (cnt24 A - 1) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
  rewrite (Z.mod_small ((cnt24 A - 1) * 2 ^ 2)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma ENBX : ltac2:(tb__ "0|2|
S3SaZ0S92VA;A1M0A2SbG0ScZ2M1Z1cA2A2A2SaSc5VSB;A2SaS9S9VSB;Sc9A2Z1000A2Z7fffff800000A2S2S0S47Q40S15VrhoE;S54A2A2S9S9VSB;SdZ18ScG1Z20A2A2A2SdZ10G0A2A2A3F_;F_;F_;").
Proof.
  intros HX S1 S2. rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  cbn [eval NBX]. rewrite E155, E130. rewrite (ext_low_small false 32) by (rewrite ?u64_lit by lia; cbn; lia).
  rewrite !add_val, sll_val, !u64_lit by lia. change (4 mod 64) with 4. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (top24 A * 2 ^ 4)) by lia. rewrite (Z.mod_small (SB + 24 * 2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma Enbb : ltac2:(tb__ "0|2|
S3SaZ0S92VA;A1M0A2SbG0ScZ2M1Z1cA2A2A2SaSc5VSB;A2SaS9S9VSB;Sc9A2Z1000A2Z7fffff800000A2S2S0S47Q40S15VrhoE;Sd1A2A2S9S9VSB;SdZ18ScG1Z20A2A2A2SdZ10G0A2A2A3F_;F_;F_;").
Proof.
  intros HX S1 S2. rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  cbn [eval nb_base add OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states.vSB vCP]. rewrite E155, E130. rewrite (ext_low_small false 32) by (rewrite ?u64_lit by lia; cbn; lia).
  rewrite !add_val, sll_val, !u64_lit by (unfold C24OFF; lia). change (4 mod 64) with 4. rewrite Z.shiftl_mul_pow2 by lia. unfold C24OFF.
  rewrite (Z.mod_small (top24 A * 2 ^ 4)) by lia. rewrite (Z.mod_small (SB + 24 * 2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma Ha : ltac2:(tb__ "0|0|
Sa1Vsegs;VKJ;VXM;VrhoE;VtpE;Vw;A6").
Proof. destruct (SPA_axforms segs KJ XEX rhoE Xf XM tpE w AXE ltac:(destruct H as [Hsm [_ HJ]]; split; [exact Hsm|]; destruct HJ as (_ & _ & _ & HK & _); exact HK)) as [X Y]. split; assumption. Qed.
Lemma Hsm1 : ltac2:(tb__ "0|0|
S31Vsegs;VrhoE;S89VXM;A1S36S35SbcA1Sd8Vtr;Sd9SdbVmd;VtpE;Vms;A3SdcVmd;A1A2A4A4").
Proof. pose proof (proj1 (proj1 Ha)) as X. unfold virt in X. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in X. exact X. Qed.

Lemma Hb : ltac2:(tb__ "0|0|
Sa1Vsegs;VKJ;VXK;Vrho3;VtpE;Vw;A6").
Proof. rewrite <- EQK. exact (SPA_unobj segs KJ rhoE XM KEPT REST tpE tr ms md OBJS Ha (fun k => k)). Qed.

Lemma HA' : ltac2:(tb__ "0|0|
VAInv;VA';VrhoE;VtpE;Vmd;A4"). Proof. exact (proj1 HJ'). Qed.
Lemma HG' : geom_ok G. Proof. pose proof HA' as (HG & _). destruct DEQ as (EG & _). rewrite EG in HG. exact HG. Qed.
Lemma BND : ltac2:(tb__ "0|8|
S3SdeVp;S8dVn;A1M0A2S3S2S0SfVp;Z10M1A2Z0M2A3S3SaZ1Vn;A2S3SbS9Vp;G0A2M3Z7fffff800000M4A2S3SaVn;G0A2S3SaZ8M5G0A2S3S2S0SfG0G5A2G2A3S3SbG0S9Vn;G5A2A2S3S4SaG3VT;A2SaS9VT;Z1000M6A2SeVp;G1A2A2A2S3SaSc5VSB;A2S3SaS9S9VSB;ScZ2M7Z25A2A2G6A2G4A2S2S0SfVSB;ScG7G1A2A2G2A3A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof (blkF_geom A' rhoE tpE md p n HA' HL' HCL) as (B1 & B2 & B3 & B4 & BT & _ & BN & _). destruct DEQ as (EG & _). rewrite EG in B4, BT. fold G T in B4, BT.
  pose proof (topG_range G) as TG. pose proof (N8_facts n B3) as (N1 & N2 & N3 & _).
  pose proof (geom_old _ HG') as X. rewrite kSpaceSize_val in X. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16 & S1 & S2 & _). fold G SB in S16, S1, S2.
  unfold HIGH_SHADOW_END in *. repeat split; try assumption; try lia.
Qed.
Lemma QBND : ltac2:(tb__ "0|2|
S5S2S35S5aA1S5bVA;A1S37S5aA1A3A1S3SaVSB;VqbF;A2S3SaS9VqbF;Z2000A2M0S9VSB;ScZ2Z25A2A2A2S3SaS10S3fS34S0S0A2S64S8eVA;A1A1A2A1Z3fdA2S3S2S0SfVqbF;Z10M1A2Z0A3S3S4SaG0VT;A2SaS9VT;Z1000A2VqbF;A2A2S4SaS9Vp;S8dVn;A1A2VqbF;A2SaG0SeVp;G1A2A2A2A2A2A2A2A2F_;").
Proof.
  intros HNE. destruct DEQ as (EG & _ & _ & _ & _ & _ & EQT & _).
  pose proof (qF A' rhoE tpE md p n HA' HL') as QF. cbn zeta in QF. rewrite EG, EQT in QF. fold G T SB in QF.
  destruct QF as (_ & _ & _ & _ & _ & QL). specialize (QL HNE). change (last (aa_q_thread A) qb_dflt) with (lastq A) in QL. fold qbF in QL.
  destruct QL as (_ & _ & _ & _ & _ & K1 & _ & M16 & S1 & S2 & ST & _ & SP). rewrite kSpaceSize_val in S2. unfold kQuarantineBatchSize, kQuarantineBatchCount in *.
  repeat split; try assumption; lia.
Qed.
Lemma CBND : ltac2:(tb__ "0|6|
S5S2S76Vq;S77A3A1S3S3SaZ1S8fVA;A1M0A2SaG0Z2M1A2A2S3S3SaZ0S92VA;A1M2A2SbG2ScG1Z1cA2A2A2S3S2S0VnbF;S9S9VSB;SdZ18ScG1Z20A2A2A2SdZ10M3G2A2A2A3S3S4SaS9VnbF;Z2000M4A2M5VT;A2SaS9VT;Z1000A2VnbF;A2A2S3S4SaS9Vp;S8dVn;A1A2VnbF;A2SaG5SeVp;G3A2A2A2S5S2S35S5aA1S5bVA;A1S37S5aA1A3A1S4SaS9VqbF;G4A2VnbF;A2SaG5VqbF;A2A2F_;A2A2A2A2A2F_;").
Proof.
  intros HQ. destruct DEQ as (EG & EC & ECI & _ & _ & _ & EQT & _).
  assert (X : aa_cache_inited A = true /\ cache24 A <> []) by (clear -QC HQ; destruct q; cbn in QC; [congruence | tauto | tauto]). destruct X as [HCI HNC].
  pose proof (cF A' rhoE tpE md p n HA' HL' ltac:(rewrite ECI; exact HCI) ltac:(rewrite Ecache24; exact HNC)) as CF. cbn zeta in CF.
  rewrite EG, EQT, Ecnt24 in CF. unfold top24 in CF. rewrite Ecache24 in CF. fold (top24 A) in CF. fold G T SB in CF.
  destruct CF as (_ & _ & _ & _ & CN & CX & _ & NT & _ & NP & NQ & _). change (last (aa_q_thread A) qb_dflt) with (lastq A) in NQ. fold qbF in NQ.
  assert (EN : nbF = SB + 24 * 2 ^ 32 + 16 * top24 A) by (unfold nbF, nb_addr, region_beg, kRegionSize; fold G SB; lia). rewrite <- EN in NT, NP, NQ.
  unfold kQuarantineBatchSize in NQ. repeat split; try assumption; try lia.
Qed.

Lemma R_hdr : ltac2:(tb__ "0|0|
S2S34S0S0A2S17VrhoE;S51A2S36S0S0SeVp;Z10A2SeVp;Z8A2A4A3").
Proof. pose proof BND as (B1 & _ & _ & B4 & _ & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. unfold S_hdr, nocellsF, O_hdr. cbn [ob_base ob_lo ob_hi ob_dflt ob_cells]. rewrite obj_range_mk by lia. cbn [eval]. rewrite E12, u64_lit by lia. f_equal; lia. Qed.
Lemma R_blk : ltac2:(tb__ "0|0|
S2S34S0S0A2S17VrhoE;S4cS79A1A2S36S0S0Vp;S9Vp;S8dVn;A1A2A4A3").
Proof.
  pose proof BND as (B1 & B2 & B3 & B4 & B5 & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. unfold nocellsF, O_blkN, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval].
  rewrite E12, u64_lit, soff_lit_small, E105s by lia. f_equal; lia.
Qed.
Lemma R_sh : ltac2:(tb__ "0|1|
S2S34S0S0A2S17VrhoE;S4cS7bA1A2S36S0S0Sc7Vp;A1M0S9G0S11S8dVn;A1Z8A2A2A4A3").
Proof.
  pose proof BND as (B1 & B2 & B3 & B4 & B5 & B6 & _). unfold blk_geo in B1. unfold nocellsF, O_sh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite Eshb, soff_lit_small, E106s by (unfold blk_geo, IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; lia). f_equal; lia.
Qed.
Lemma R_st1 : ltac2:(tb__ "0|0|
S2S34S0S0A2S17VrhoE;S4cS7dA1A2S36S0S0S9VT;Zad0A2S9VT;Zae0A2A4A3").
Proof. unfold nocellsF, O_stT1. cbn [ob_base ob_lo ob_hi ob_dflt]. rewrite obj_range_mk by lia. rewrite EvT. reflexivity. Qed.
Lemma R_stQ : ltac2:(tb__ "0|0|
S2S34S0S0A2S17VrhoE;S4cS7cA1A2S36S0S0S9VT;Zae0A2S9VT;Zae8A2A4A3").
Proof. unfold nocellsF, O_stQ, carved. cbn [ob_base ob_lo ob_hi ob_dflt]. rewrite obj_range_mk by lia. rewrite EcA. f_equal; lia. Qed.
Lemma R_st2 : ltac2:(tb__ "0|0|
S2S34S0S0A2S17VrhoE;S4cS7eA1A2S36S0S0S9VT;Zae8A2S9VT;Zc60A2A4A3").
Proof. unfold nocellsF, O_stT2. cbn [ob_base ob_lo ob_hi ob_dflt]. rewrite obj_range_mk by lia. rewrite EvT. reflexivity. Qed.
Lemma R_qc : ltac2:(tb__ "0|0|
S2S34S0S0A2S17VrhoE;S55A2S36S0S0S9VT;Z50A2S9VT;Z70A2A4A3").
Proof. unfold S_qc. rewrite obj_range_mk by lia. rewrite EcQ. f_equal; lia. Qed.
Lemma R_bh : ltac2:(tb__ "0|0|
S5S2S35S5aA1S5bVA;A1S37S5aA1A3A1S2S34S0S0A2S17VrhoE;S50A2S36S0S0VqbF;S9VqbF;Z18A2A4A3F_;").
Proof.
  intros HNE. pose proof (QBND HNE) as (Q1 & Q2 & _). pose proof BND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). unfold HIGH_SHADOW_END in S1.
  unfold S_bh. rewrite obj_range_mk by lia. cbn [eval]. rewrite (E122 HNE), u64_lit by lia. fold qbF. f_equal; lia.
Qed.
Lemma R_it : ltac2:(tb__ "0|1|
S5S2S35S5aA1S5bVA;A1S37S5aA1A3A1S2S34S0S0A2S17VrhoE;S4cSceS37S18A1A1A1A2S36S0S0S9S9VqbF;SdZ8Sa0VA;A1A2A2M0Z18A2S9G0Z20A2A4A3F_;").
Proof.
  intros HNE. pose proof (QBND HNE) as (Q1 & Q2 & Q3 & _). pose proof BND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). unfold HIGH_SHADOW_END in S1.
  unfold nocellsF, O_item. cbn [ob_base ob_lo ob_hi ob_dflt]. rewrite obj_range_mk by lia. rewrite (Eitem HNE) by (unfold kQuarantineBatchCount; lia). unfold kA. fold qbF. f_equal; lia.
Qed.
Lemma R_pc : ltac2:(tb__ "0|0|
S2S34S0S0A2S17VrhoE;S52A2S36S0S0S9VT;Z850A2S9VT;Z860A2A4A3").
Proof. unfold S_pc. rewrite obj_range_mk by lia. rewrite EcA. f_equal; lia. Qed.
Lemma R_pck : ltac2:(tb__ "0|1|
S5S2S76Vq;S77A3A1S2S34S0S0A2S17VrhoE;S4cS7aA1A2S36S0S0S9S9VT;Z860A2SdZ4SeS8fVA;A1Z1A2A2M0A2S9S9VT;Z864A2G0A2A4A3F_;").
Proof.
  intros HQ. pose proof (CBND HQ) as (C1 & _). unfold nocellsF, O_pckF. cbn [ob_base ob_lo ob_hi ob_dflt]. rewrite obj_range_mk by lia. rewrite (Ecp C1). f_equal; lia.
Qed.
Lemma R_nb : ltac2:(tb__ "0|0|
S5S2S76Vq;S77A3A1S2S34S0S0A2S17VrhoE;ScfS37S18A1A1A2S36S0S0VnbF;S9VnbF;Z2000A2A4A3F_;").
Proof.
  intros HQ. pose proof (CBND HQ) as (C1 & C2 & C3 & _). pose proof BND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _).
  unfold O_nb. rewrite obj_range_mk by lia. rewrite Enbb by (try rewrite kSpaceSize_val; lia). rewrite <- C3. f_equal; lia.
Qed.

Lemma VOBJ_in : ltac2:(tb__ "0|2|
S13S48S13R1Sd5S13S13S4cS80Vq;A1A4A3S4S2S13R2S55A3S4S3S4S2S76Vq;S77A3M0S2S76Vq;S78A3A2S2S13R2S50A3A2S4S3G0S2S13R2S4cSceS37S18A1M1A1A1A3A2S3S5G0A1S4S2S13R2S52A3S4S2S13R2S4cS7aA1A3S2S13R2ScfG1A1A3A2A2A2A2A2A2F_;Fs;").
Proof.
  intros s Hs. clear -Hs. unfold VOBJ in Hs. destruct q; cbn in Hs; unfold S_qc, S_bh, S_pc;
    repeat (destruct Hs as [<-|Hs]); try (destruct Hs); try (left; reflexivity).
  - right; left. split; [left; reflexivity | reflexivity].
  - right; right; left. split; reflexivity.
  - right; right; right. split; [discriminate | left; reflexivity].
  - right; right; right. split; [discriminate | right; left; reflexivity].
  - right; right; right. split; [discriminate | right; right; reflexivity].
  - right; left. split; [right; reflexivity | reflexivity].
  - right; right; right. split; [discriminate | left; reflexivity].
  - right; right; right. split; [discriminate | right; left; reflexivity].
  - right; right; right. split; [discriminate | right; right; reflexivity].
Qed.
Lemma RS_in : ltac2:(tb__ "0|0|
S13S48S13R1S4dVq;A1A3S4S4S2S13R2S51A3S4S2S13R2S4cS79A1A3S4S2S13R2S4cS7bA1A3S4S2S13R2S4cS7dA1A3S4S2S13R2S4cS7cA1A3S2S13R2S4cS7eA1A3A2A2A2A2A2S48S13R2Sd5S13S13S4cS80Vq;A1A4A3A2F_;Fs;").
Proof.
  intros s Hs. unfold RSHAPE in Hs. rewrite map_app in Hs. apply in_app_or in Hs as [Hs|Hs]; [left | right; exact Hs].
  cbn [map] in Hs. unfold S_hdr. clear -Hs. destruct Hs as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; tauto.
Qed.

Lemma RS_chg : ltac2:(tb__ "0|1|
S13S48S13R1S4dVq;A1A3S0S3SaS3dS0S0S17VrhoE;R3A2M0A3R1A2SbR1S41S0S0G0A3A2A2S98Vq;VA;Vp;Vn;R2A5F_;Fz;F_;Fs;").
Proof.
  intros s Hs z Hz. pose proof BND as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & _). unfold blk_geo in B1.
  assert (CC : chg_common A p n z -> chg_f q A p n z).
  { intros X. destruct (F0A_rebuild.QDEC q) as [HQ|HQ]; [apply (proj2 (F0A_rebuild.CHG_QA q A p n HQ z)) | apply (proj2 (F0A_rebuild.CHG_QB q A p n QC HQ z))]; left; exact X. }
  destruct (RS_in s Hs) as [[->|[->|[->|[->|[->| ->]]]]]|HV].
  - apply CC. rewrite R_hdr in Hz. cbn [fst snd] in Hz. unfold chg_common. clear -Hz. lia.
  - apply CC. rewrite R_blk in Hz. cbn [fst snd] in Hz. unfold chg_common. clear -Hz. lia.
  - apply CC. rewrite R_sh in Hz. cbn [fst snd] in Hz. unfold chg_common. clear -Hz. lia.
  - apply CC. rewrite R_st1 in Hz. cbn [fst snd] in Hz. unfold chg_common. fold G T. clear -Hz. lia.
  - apply CC. rewrite R_stQ in Hz. cbn [fst snd] in Hz. unfold chg_common. fold G T. clear -Hz. lia.
  - apply CC. rewrite R_st2 in Hz. cbn [fst snd] in Hz. unfold chg_common. fold G T. clear -Hz. lia.
  - destruct (VOBJ_in s HV) as [-> | [[HQQ ->] | [[HQ ->] | [HQ [->|[->| ->]]]]]].
    + apply CC. rewrite R_qc in Hz. cbn [fst snd] in Hz. unfold chg_common. fold G T. clear -Hz. lia.
    + assert (HNE : aa_q_thread A <> []) by (clear -QC HQQ; destruct HQQ as [-> | ->]; cbn in QC; tauto).
      rewrite (R_bh HNE) in Hz. cbn [fst snd] in Hz.
      destruct (F0A_rebuild.QDEC q) as [HQ|HQ]; [apply (proj2 (F0A_rebuild.CHG_QA q A p n HQ z)); right; left; exact Hz|].
      apply (proj2 (F0A_rebuild.CHG_QB q A p n QC HQ z)). right; right; right. split; [exact HNE | exact Hz].
    + assert (HNE : aa_q_thread A <> []) by (clear -QC HQ; subst q; cbn in QC; tauto).
      rewrite (R_it HNE) in Hz. cbn [fst snd] in Hz. apply (proj2 (F0A_rebuild.CHG_QA q A p n HQ z)). right; right. unfold F0A_rebuild.kA in *. fold qbF. clear -Hz. lia.
    + rewrite R_pc in Hz. cbn [fst snd] in Hz. apply (proj2 (F0A_rebuild.CHG_QB q A p n QC HQ z)). right; left. unfold pc24. fold G T. left. clear -Hz. lia.
    + rewrite (R_pck HQ) in Hz. cbn [fst snd] in Hz. apply (proj2 (F0A_rebuild.CHG_QB q A p n QC HQ z)). right; left. unfold pc24. fold G T. right. clear -Hz. lia.
    + rewrite (R_nb HQ) in Hz. cbn [fst snd] in Hz. apply (proj2 (F0A_rebuild.CHG_QB q A p n QC HQ z)). right; right; left. fold nbF. exact Hz.
Qed.

Lemma RCLS' : ltac2:(tb__ "0|0|
S13S48S13R1VREST;A3S4S6S87S87S3S48S87R1S4eA3S2S13R3S88R1A1A3A2Lk;A2S48S13S4cR2A1S4dVq;A1A3A2F_;Fo;").
Proof.
  intros o Ho. pose proof (proj1 (forallb_forall _ _) RCLS o Ho) as X. apply orb_prop in X as [X|X].
  - left. apply existsb_exists in X as (o' & Hin & E). apply sobj_eqb_sound in E. subst o'. apply in_map_iff in Hin as (k & <- & Hk). exists k. split; [exact Hk | reflexivity].
  - right. apply existsb_exists in X as (s' & Hin & E). apply sobj_eqb_sound in E. rewrite E. exact Hin.
Qed.
Lemma RCIV' : ltac2:(tb__ "0|0|
S87S48S87R1S4eA3S48S13S88R2A1VREST;A3F_;Fk;").
Proof. intros k Hk. pose proof (proj1 (forallb_forall _ _) RCIV k Hk) as X. apply existsb_exists in X as (o & Ho & E). apply sobj_eqb_sound in E. rewrite E. exact Ho. Qed.
Lemma RWR' : ltac2:(tb__ "0|0|
Sd6S13S13S2S38S2dS21R1A1A1S3aA3Lo;VREST;A3").
Proof. apply Forall_forall. intros o Ho. exact (proj1 (forallb_forall _ _) RWR o Ho). Qed.
Lemma RCELL' : ltac2:(tb__ "0|1|
S34S13S18A2M0S48G0R1S53Vq;A1A3S6S13S13S3S48S13R1VREST;A3S3S2S13S4cR1A1S3dS13S18R3A3A3S48S18S41S13S18R3A3S27R1A1A3A2A2Lo;A2F_;Fsc;").
Proof.
  intros sc Hsc. pose proof (proj1 (forallb_forall _ _) RCELL sc Hsc) as X. apply existsb_exists in X as (o & Ho & E).
  apply andb_prop in E as [E1 E2]. apply sobj_eqb_sound in E1. exists o. split; [exact Ho|]. split; [exact E1|]. exact (In_of_cellb _ _ E2).
Qed.

Lemma carve_range : ltac2:(tb__ "0|0|
S87Sb9R1A1S2S34S0S0A2S17VrhoE;S88R2A1A2Sb8VrhoE;R2A2A3F_;Fk;").
Proof.
  intros [[[b lo] hi] cs] (S1 & S2 & S3 & _). cbn [carve_obj]. unfold carved. rewrite obj_range_mk by lia. reflexivity.
Qed.
Lemma INR : ltac2:(tb__ "0|3|
S45Q40M0A1Se6VrhoE;VREST;R1A3S4S6S87S87S3S48S87R1S4eA3S3SaS3dS0S0Sb8VrhoE;R1A2M1A3S47G0R3A2M2A2SbG2S41S0S0G1A3A2A2A2Lk;A2S98Vq;VA;Vp;Vn;S47G0R2A2A5A2F_;Fa;").
Proof.
  intros a (o & HoR & Hr). destruct (RCLS' o HoR) as [(k & Hk & ->)|Hs].
  - left. exists k. split; [exact Hk|]. rewrite <- (carve_range k (proj1 (Forall_forall _ _) NRTX_small k Hk)). exact Hr.
  - right. apply (RS_chg _ Hs). rewrite nocells_range. exact Hr.
Qed.

Lemma IN_common : ltac2:(tb__ "0|0|
S13S4S2S13R1S51A3S4S2S13R1S4cS79A1A3S4S2S13R1S4cS7bA1A3S4S2S13R1S4cS7dA1A3S4S2S13R1S4cS7cA1A3S2S13R1S4cS7eA1A3A2A2A2A2A2S48S13R2S4dVq;A1A3F_;Fs;").
Proof. intros s Hs. unfold RSHAPE. rewrite map_app. apply in_or_app. left. unfold S_hdr in Hs. cbn [map]. clear -Hs. cbn. intuition (subst; tauto). Qed.
Lemma IN_qc : In S_qc (RSHAPE q).
Proof. unfold RSHAPE. rewrite map_app. apply in_or_app. right. clear. destruct q; cbn; left; reflexivity. Qed.
Lemma IN_bh : ltac2:(tb__ "0|0|
S4S2S76Vq;S77A3S2S76Vq;S78A3A2S48S13S50S4dVq;A1A3F_;").
Proof. intros Hq. unfold RSHAPE. rewrite map_app. apply in_or_app. right. clear -Hq. destruct Hq as [-> | ->]; cbn; right; left; reflexivity. Qed.
Lemma IN_it : ltac2:(tb__ "0|0|
S2S76Vq;S77A3S48S13S4cSceS37S18A1A1A1S4dVq;A1A3F_;").
Proof. intros ->. unfold RSHAPE. rewrite map_app. apply in_or_app. right. cbn. right; right; left. reflexivity. Qed.
Lemma IN_pc : ltac2:(tb__ "0|0|
S5S2S76Vq;S77A3A1S48S13S52S4dVq;A1A3F_;").
Proof. intros Hq. unfold RSHAPE. rewrite map_app. apply in_or_app. right. clear -Hq. destruct q; [congruence| |]; cbn; [right; left | right; right; left]; reflexivity. Qed.
Lemma IN_pck : ltac2:(tb__ "0|0|
S5S2S76Vq;S77A3A1S48S13S4cS7aA1S4dVq;A1A3F_;").
Proof. intros Hq. unfold RSHAPE. rewrite map_app. apply in_or_app. right. clear -Hq. destruct q; [congruence| |]; cbn; [right; right; left | right; right; right; left]; reflexivity. Qed.
Lemma IN_nb : ltac2:(tb__ "0|0|
S5S2S76Vq;S77A3A1S48S13ScfS37S18A1A1S4dVq;A1A3F_;").
Proof. intros Hq. unfold RSHAPE. rewrite map_app. apply in_or_app. right. clear -Hq. destruct q; [congruence| |]; cbn; [right; right; right; left | right; right; right; right; left]; reflexivity. Qed.

Lemma CHG_cov : ltac2:(tb__ "0|1|
S0S98Vq;VA;Vp;Vn;R1A5S6S13S13S3S48S13R1S4dVq;A1A3S3SaS3dS0S0S17VrhoE;R1A2M0A3R3A2SbR3S41S0S0G0A3A2A2A2Ls;A2F_;Fz;").
Proof.
  intros z Hz.
  assert (CC : chg_common A p n z -> exists s, In s (RSHAPE q) /\ fst (obj_range rhoE s) <= z < snd (obj_range rhoE s)).
  { intros X. unfold chg_common in X. fold G T in X.
    destruct X as [X|[X|[X|[X|X]]]].
    - exists S_hdr. split; [apply IN_common; tauto | rewrite R_hdr; cbn; clear -X; lia].
    - exists (nocellsF O_blkN). split; [apply IN_common; tauto | rewrite R_blk; cbn; clear -X; lia].
    - exists (nocellsF O_sh). split; [apply IN_common; tauto | rewrite R_sh; cbn; clear -X; lia].
    - exists S_qc. split; [exact IN_qc | rewrite R_qc; cbn; clear -X; lia].
    - destruct (Z_lt_dec z (T + 2784)); [|destruct (Z_lt_dec z (T + 2792))].
      + exists (nocellsF O_stT1). split; [apply IN_common; tauto | rewrite R_st1; cbn; clear -X l; lia].
      + exists (nocellsF O_stQ). split; [apply IN_common; tauto | rewrite R_stQ; cbn; clear -X n0 l; lia].
      + exists (nocellsF O_stT2). split; [apply IN_common; tauto | rewrite R_st2; cbn; clear -X n0 n1; lia]. }
  destruct (F0A_rebuild.QDEC q) as [HQ|HQ].
  - apply (proj1 (F0A_rebuild.CHG_QA q A p n HQ z)) in Hz. destruct Hz as [X|[X|X]]; [exact (CC X)| |].
    + assert (HNE : aa_q_thread A <> []) by (clear -QC HQ; subst q; cbn in QC; tauto).
      exists S_bh. split; [apply IN_bh; left; exact HQ | rewrite (R_bh HNE); cbn; fold qbF; clear -X; lia].
    + assert (HNE : aa_q_thread A <> []) by (clear -QC HQ; subst q; cbn in QC; tauto).
      exists (nocellsF (O_item [])). split; [exact (IN_it HQ) | rewrite (R_it HNE); cbn; unfold F0A_rebuild.kA in *; fold qbF; clear -X; lia].
  - apply (proj1 (F0A_rebuild.CHG_QB q A p n QC HQ z)) in Hz. destruct Hz as [X|[X|[X|[HNE X]]]]; [exact (CC X)| | |].
    + unfold pc24 in X. fold G T in X. destruct X as [X|X].
      * exists S_pc. split; [exact (IN_pc HQ) | rewrite R_pc; cbn; clear -X; lia].
      * exists (nocellsF O_pckF). split; [exact (IN_pck HQ) | rewrite (R_pck HQ); cbn; clear -X; lia].
    + exists (O_nb []). split; [exact (IN_nb HQ) | rewrite (R_nb HQ); cbn; fold nbF; clear -X; lia].
    + exists S_bh. split; [apply IN_bh; right; clear -HQ HNE QC; destruct q; [congruence | cbn in QC; destruct QC as [E _]; congruence | reflexivity] | rewrite (R_bh HNE); cbn; fold qbF; clear -X; lia].
Qed.

Lemma E12u : ltac2:(tb__ "0|0|
S2S0S47Q40S14VrhoE;PcA2A2Vp;A3").
Proof. pose proof BND as (B1 & _ & _ & B4 & _ & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. rewrite E12. apply u64_lit. lia. Qed.
Lemma E13u : ltac2:(tb__ "0|0|
S2S0S47Q40S14VrhoE;PdA2A2Vn;A3").
Proof. pose proof BND as (B1 & _ & B3 & B4 & B5 & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. rewrite E13. apply u64_lit. lia. Qed.

Lemma NK : ltac2:(tb__ "0|4|
S87S48S87R1S4eA3S3S48S13S88R2A1VREST;A3S3Sb9R2A1S3SbbR2A1SbfVrhoE;SbeVsegs;S1bVrhoE;A1A2SeS3dS0S0Sb8VrhoE;R2A2A3S34S34S34S16S0A2M0S0A2M1S35S34S34S0S40A2S16A2A1M2A2M3S0Lk;R2G1G2G1S0Lp0;R2G0S0G0S0Lp1;R2S16S0R1Llo;Ls;X34x1Lz;Lp1;X34x1Ll;Lp0;X34x1A2G3G2Lk;R2G1G2G1G2Lp0;R2G0S0G0G2Lp1;R2S16S0R5Lz0;Ls;X34x1Lz;Lp1;X34x1Lcs;Lp0;X34x1A4A2A2A2F_;Fk;").
Proof.
  intros k Hk. split; [exact (RCIV' k Hk)|]. split; [exact (proj1 (Forall_forall _ _) NRTX_small k Hk)|].
  split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) NRTX_coverb k Hk)|].
  destruct (blkF_mem A' rhoE tpE md p n HA' HL' HCL) as (t2 & T1 & T2 & HW2 & HL2 & _).
  destruct (junkF_ok A' rhoE tpE md HA') as (jv2 & J1 & J2 & J3 & J4 & JM & JS & JQ).
  pose proof (carve_NRT A' rhoE tpE md p n HA' HL' HCL Hii' E12u t2 (conj T1 (conj T2 (conj HW2 HL2))) jv2
                (conj J1 (conj J2 (conj J3 (conj J4 (conj JM (conj JS JQ))))))) as CN.
  set (rho2 := rhoF_of A' rhoE p n t2 jv2) in CN.
  pose proof (proj1 (Forall_forall _ _) CN k (NRTX_sub k Hk)) as CK.

  assert (EJ : j_min jv2 = kQuarantineMin).
  { pose proof HA' as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & _ & _ & HQR & _). destruct HQR as (_ & _ & _ & _ & _ & _ & QMIN & _).
    apply (cell8_inj (view segs (rm rhoE)) (QG + 72)); [exact JM | | clear -J1; lia | unfold kQuarantineMin; clear; lia].
    intros kk Hkk. specialize (QMIN kk Hkk). cbn [c_addr c_w c_val] in QMIN |- *. rewrite maskv_out in QMIN; [exact QMIN|].
    apply fs_footb_img; [exact HG | unfold QG; cbn in Hkk; clear -Hkk; lia]. }
  assert (HP : forall i, Pnrtx i = true -> rw rho2 i = rw rhoE i).
  { intros i Hi. unfold Pnrtx in Hi. apply existsb_exists in Hi as (j & Hj & Eij). apply Pos.eqb_eq in Eij. subst j.
    destruct DEQ as (EG & _).
    destruct Hj as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; unfold rho2, rhoF_of; cbn [rho_sets rw rho_set_rw Pos.eqb]; rewrite ?EG;
      first [reflexivity | rewrite EJ, E136, HJMIN; reflexivity | symmetry; first [exact E151 | exact E152 | exact E153 | exact E154 | exact E155]]. }
  pose proof (proj1 (forallb_forall _ _) NRTX_varsb k Hk) as VB.
  destruct k as [[[b lo] hi] cs]. apply andb_prop in VB as [VBb VBc].
  unfold carve_ok in CK. destruct CK as (_ & _ & _ & _ & _ & _ & _ & CIV).
  assert (EB : eval rho2 b = eval rhoE b) by (apply (eval_agree_P Pnrtx); [exact HP | intros l; unfold rho2, rhoF_of; rewrite rl_rho_sets; reflexivity | exact VBb]).
  cbn [spec_range fst]. replace (bv_unsigned (eval rhoE b) + lo - lo) with (bv_unsigned (eval rhoE b)) by lia. rewrite <- EB.
  unfold cells_in_view in CIV |- *. apply Forall_forall. intros [[o kk] e] Hc j Hj.
  pose proof (proj1 (Forall_forall _ _) CIV _ Hc j Hj) as X. cbn beta iota in X.
  unfold rho2, rhoF_of in X. rewrite rm_rho_sets in X. fold (rhoF_of A' rhoE p n t2 jv2) in X. fold rho2 in X.
  rewrite (eval_agree_P Pnrtx rho2 rhoE e HP ltac:(intros l; unfold rho2, rhoF_of; rewrite rl_rho_sets; reflexivity) (proj1 (forallb_forall _ _) VBc _ Hc)) in X.
  exact X.
Qed.

Lemma VO : ltac2:(tb__ "0|0|
S0S5S98Vq;VA;Vp;Vn;R1A5A1S2S3bS45Q8A1A1Vv3;R2A1VvE;R2A1A3F_;Fz;").
Proof.
  intros z Hz. unfold v3, vE. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
  2,3: rewrite !view_out by (clear -n0; lia) || rewrite !view_out by (clear -n0 l; lia); reflexivity.
  rewrite !view_in by (clear -l l0; lia).
  destruct (in_ranges_dec rhoE REST (Z_to_bv 64 z)) as [Hin|Hout].
  - destruct (INR _ Hin) as [(k & Hk & Hr)|Hc]; [|rewrite u64_lit in Hc by (clear -l l0; lia); exfalso; exact (Hz Hc)].
    rewrite u64_lit in Hr by (clear -l l0; lia). unfold rho3.
    exact (absorb_specs_view rhoE _ tr (vms md tpE ms) (vmd md) KEPT REST NRTX (rd_of segs (rm rhoE)) Hsm1 OBJS NK z k Hk Hr).
  - unfold rho3, rho_absorb, rd_of. cbn [rm]. destruct (in_ranges_dec rhoE REST (Z_to_bv 64 z)) as [Hin'|]; [exfalso; exact (Hout Hin') | reflexivity].
Qed.
Lemma RMO : ltac2:(tb__ "0|1|
S0S3SaZ0R1A2SbR1ScZ2Z40A2A2A2S5S98Vq;VA;Vp;Vn;R2A5A1S5S9eVG;R3A2A1S2S3bS45Q8A1A1S1bVrho3;S46Q40R4A2M0A2S1bVrhoE;G0A2A3F_;F_;F_;Fa;").
Proof.
  intros a Ha Hc Hrt. unfold rho3, rho_absorb. cbn [rm]. destruct (in_ranges_dec rhoE REST (Z_to_bv 64 a)) as [Hin|]; [exfalso | reflexivity].
  destruct (INR _ Hin) as [(k & Hk & Hr)|Hc']; rewrite u64_lit in * by (clear -Ha; lia); [|exact (Hc Hc')].
  apply Hrt. pose proof BND as (B1 & _ & _ & B4 & _ & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  exact (NRTX_zone G rhoE k a HG' E151 E152 ltac:(rewrite E12u; clear -B1 B4 B6; lia) Hk Hr).
Qed.
Lemma DEFM : ltac2:(tb__ "0|4|
S0S3SaScaR1A2SbR1ScZ2Z40A2A2A2S5S2S3bS45Q8A1M0A1M1S1bVrhoE;S46Q40M2R2A2A2S43G0A1M3A3A1S5S2G1S1bVrho3;S46G2R3A2A2G3A3A1F_;F_;Fa;").
Proof.
  intros a Ha Hd. destruct (in_ranges_dec rhoE REST (Z_to_bv 64 a)) as [Hin|Hout].
  - unfold rho3. apply (absorb_defined rhoE _ tr (vms md tpE ms) (vmd md) KEPT REST _ Hsm1 OBJS RWR' Hin). rewrite u64_lit by (unfold IMG_HI in Ha; clear -Ha; lia). clear -Ha; lia.
  - unfold rho3, rho_absorb. cbn [rm]. destruct (in_ranges_dec rhoE REST (Z_to_bv 64 a)) as [Hin'|]; [exfalso; exact (Hout Hin') | exact Hd].
Qed.
Lemma AO : ltac2:(tb__ "0|8|
S13S48S13R1VREST;A3S47Q40M0S15VrhoE;S26R2A1A2A2S0S30VrhoE;R3A2S0S2fVrhoE;R4A2S0S3S3SaZ0M1S9R3R2A2A2S3SaS9R3R1A2ScZ2Z40A2A2SaR2R1A2A2A2S3S18S48S18R1S27R6A1A3S3SaR4S1dVrhoE;S20R2A1A2M2A2S3SaS9G2S1eR2A1A2R3A2S40Se0R1S12S1eR3A1A1A2S2S3bS45Q8M3A1M4A1M5SbeVsegs;S1bVrho3;A1M6S46G0S9S9R7S1dVrhoE;S20R4A1A2A2S10R2A1A2A2A3S3cG4Sd7G4R2S2eS12S1eR4A1A1S15VrhoE;S25R4A1A2A2S46G3G1A2A4A2A3F_;Fj;A2A2F_;Fc;S4S2S22S21R5A1M7S23A3S2S22G7S29A3A2S0S3SaR4R1A2SbR1R3A2A2S6G4G4S2G5SbeVsegs;G6S46G0S9R7R3A2A2A3S3cG4R1A2A3Lx;A2F_;Foff;F_;A2A2Thi;Tlo;Tb;F_;Fo;").
Proof. intros o Ho. pose proof (absorb_obj rhoE _ tr (vms md tpE ms) (vmd md) KEPT REST o Hsm1 OBJS Ho) as X. cbn zeta in X. destruct X as (X1 & X2 & X3 & _). split; [exact X1 | split; [exact X2 | exact X3]]. Qed.
Lemma RS_dflt : ltac2:(tb__ "0|0|
S13S48S13R1S4dVq;A1A3S2S22S21R2A1S23A3F_;Fs;").
Proof.
  intros s Hs. unfold RSHAPE in Hs. apply in_map_iff in Hs as (o & <- & Ho). apply in_app_or in Ho as [Ho|Ho].
  - clear -Ho. cbn in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; reflexivity.
  - clear -Ho. unfold VOBJ in Ho. destruct q; cbn in Ho; repeat (destruct Ho as [<-|Ho]; [reflexivity|]); destruct Ho.
Qed.
Lemma RSHP' : ltac2:(tb__ "0|0|
S13S48S13R1S4dVq;A1A3S6S13S13S3S48S13R1VREST;A3S2S13S4cR1A1R3A3A2Lo;A2F_;Fs;").
Proof. intros s Hs. pose proof (proj1 (forallb_forall _ _) RSHP s Hs) as X. apply existsb_exists in X as (o & Ho & E). apply sobj_eqb_sound in E. exists o. auto. Qed.
Lemma PRES : ltac2:(tb__ "0|1|
S0S98Vq;VA;Vp;Vn;R1A5S6S45Q8A1M0G0S2S3bG0A1Vv3;R3A1S3cG0R1A2A3Lb;A2F_;Fz;").
Proof.
  intros z Hz. destruct (CHG_cov z Hz) as (s & Hs & Hr). destruct (RSHP' s Hs) as (o & Ho & Es). pose proof (RS_dflt s Hs) as Ds.
  rewrite <- Es, nocells_range in Hr. destruct (AO o Ho) as (X1 & _ & X3). cbn zeta in X1, X3.
  assert (Do : ob_dflt o = DUnknown) by (rewrite <- Es in Ds; destruct o; exact Ds).
  unfold obj_range in Hr. cbn [fst snd] in Hr.
  destruct (X3 (or_introl Do) (z - bv_unsigned (eval rhoE (ob_base o))) ltac:(clear -Hr; lia)) as [x Hx].
  exists x. unfold v3. rewrite view_in by (clear -Hr X1; lia). replace z with (bv_unsigned (eval rhoE (ob_base o)) + (z - bv_unsigned (eval rhoE (ob_base o)))) at 1 by (clear; lia). exact Hx.
Qed.

Lemma CELLV : ltac2:(tb__ "0|1|
S13S18S0S0S0S48S34S13S18A2S36S13S18R5R4A4S53Vq;A1A3S2S0S9S47Q40M0S15VrhoE;S26R6A1A2A2S1dVrhoE;S20R5A1A2A2R4A3S2S0S1eR6A1R4A3S2S45G0A1S15VrhoE;S25R7A1A2S46G0R4A2A3SadVv3;SaeR7S12R6A1R5A3A2F_;F_;F_;F_;FV;Fwd;Fa;Fc;Fs;").
Proof.
  intros s c a wd V Hin Ea Ew Ev. destruct (RCELL' _ Hin) as (o & Ho & Es & Hc). cbn [fst snd] in Es, Hc.
  destruct (AO o Ho) as (X1 & X2 & _). cbn zeta in X1. destruct (X2 c Hc) as (L1 & L2 & RD).
  assert (Eb : ob_base o = ob_base s) by (rewrite <- Es; destruct o; reflexivity). rewrite Eb in X1, RD.
  subst wd. intros k Hk. cbn [c_addr c_w c_val] in Hk |- *. unfold v3. rewrite view_in by (clear -X1 L1 L2 Ea Hk; lia).
  rewrite <- Ea, <- Ev. exact (RD k Hk).
Qed.

Lemma HNE_A : ltac2:(tb__ "0|0|
S2S76Vq;S77A3S5S2S35S5aA1S5bVA;A1S37S5aA1A3A1F_;"). Proof. intros HQ. clear -QC HQ. subst q. cbn in QC. tauto. Qed.
Lemma HNE_Bf : ltac2:(tb__ "0|0|
S2S76Vq;S78A3S5S2S35S5aA1S5bVA;A1S37S5aA1A3A1F_;"). Proof. intros HQ. clear -QC HQ. subst q. cbn in QC. tauto. Qed.
Lemma HE_Be : ltac2:(tb__ "0|0|
S2S76Vq;S7fA3S2S35S5aA1S5bVA;A1S37S5aA1A3F_;"). Proof. intros HQ. clear -QC HQ. subst q. cbn in QC. tauto. Qed.
Lemma ENBX' : ltac2:(tb__ "0|1|
S5S2S76Vq;S77A3A1S2S45Q40M0A1S15VrhoE;S54A2S46G0VnbF;A2A3F_;").
Proof.
  intros HQ. pose proof (CBND HQ) as (C1 & C2 & C3 & _). pose proof BND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _).
  apply of_unsigned. rewrite C3. apply ENBX; [exact C2 | exact S1 | rewrite kSpaceSize_val; exact S2].
Qed.

Lemma LC_A' : ltac2:(tb__ "0|0|
S2S76Vq;S77A3S9aS77VA;Vp;Vn;Vv3;A5F_;").
Proof.
  intros HQ. pose proof (HNE_A HQ) as HNE. pose proof TB as [T1 T2]. pose proof (QBND HNE) as (Q1 & Q2 & Q3 & _).
  pose proof BND as (B1 & _ & B3 & B4 & B5 & B6 & _ & _ & _ & S1 & S2 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1, S1.
  assert (IN : forall sc, In sc (LCELLS QA) -> In sc (LCELLS q)) by (rewrite HQ; intros sc Hsc; exact Hsc).
  unfold leaf_cells. cbn zeta. fold G T. change (last (aa_q_thread A) qb_dflt) with (lastq A). fold qbF.
  assert (EQB : bv_unsigned (eval rhoE (ob_base S_bh)) = qbF) by (cbn [ob_base S_bh eval]; rewrite (E122 HNE); fold qbF; apply u64_lit; lia).
  assert (EIT : bv_unsigned (eval rhoE (ob_base S_it)) = qbF + 8 * Z.of_nat (length (qb_items (lastq A)))) by (cbn [ob_base S_it]; apply (EITX HNE); unfold kQuarantineBatchCount; lia).
  repeat apply conj.
  - apply (CELLV S_qc (c8 0 (SVar 120)) _ 8); [apply IN; cbn; tauto | cbn [ob_base S_qc c_off c8]; rewrite EcQ, soff_lit_small by lia; lia | reflexivity | cbn [eval c8 SymState.c_val]; exact E120].
  - apply (CELLV S_qc (c8 8 (SVar 121)) _ 8); [apply IN; cbn; tauto | cbn [ob_base S_qc c_off c8]; rewrite EcQ, soff_lit_small by lia; lia | reflexivity | cbn [eval c8 SymState.c_val]; exact (E121 HNE)].
  - apply (CELLV S_qc (c8 16 (SVar 122)) _ 8); [apply IN; cbn; tauto | cbn [ob_base S_qc c_off c8]; rewrite EcQ, soff_lit_small by lia; lia | reflexivity | cbn [eval c8 SymState.c_val]; exact (E122 HNE)].
  - apply (CELLV S_qc (c8 24 (SAlu ALU_ADD (SVar 123) (SVar 13))) _ 8); [apply IN; cbn; tauto | cbn [ob_base S_qc c_off c8]; rewrite EcQ, soff_lit_small by lia; lia | reflexivity |].
    cbn [c8 SymState.c_val]. apply eval_add; [exact E123 | exact E13].
  - apply (CELLV S_bh (c8 8 (SAlu ALU_ADD (SVar 125) (SVar 13))) _ 8); [apply IN; cbn; tauto | cbn [c_off c8]; rewrite EQB, soff_lit_small by lia; lia | reflexivity |].
    cbn [c8 SymState.c_val]. apply eval_add; [exact E125 | exact E13].
  - apply (CELLV S_bh (c8 16 (SAlu ALU_ADD (SVar 126) (SLit 1))) _ 8); [apply IN; cbn; tauto | cbn [c_off c8]; rewrite EQB, soff_lit_small by lia; lia | reflexivity |].
    cbn [c8 SymState.c_val]. apply eval_add; [exact E126 | reflexivity].
  - apply (CELLV S_it (c8 24 (SAlu ALU_ADD (SVar 12) (SLit (-16)))) _ 8); [apply IN; cbn; tauto | cbn [c_off c8]; rewrite EIT, soff_lit_small by lia; lia | reflexivity |].
    cbn [c8 SymState.c_val]. replace (p - 16) with (p + -16) by lia. apply eval_add; [exact E12 | reflexivity].
  - apply (CELLV S_bh (c8 0 (SVar 124)) _ 8); [apply IN; cbn; tauto | cbn [c_off c8]; rewrite EQB, soff_lit_small by lia; lia | reflexivity | cbn [eval c8 SymState.c_val]; exact E124].
Qed.

Ltac cellv s c wd IN EB :=
  apply (CELLV s c _ wd); [apply IN; cbn; tauto | cbn [ob_base S_qc S_pc S_nb S_bh S_hdr c_off c8 c4]; rewrite EB, soff_lit_small by lia; lia | reflexivity | cbn [c8 c4 SymState.c_val]].

Lemma LC_Be' : ltac2:(tb__ "0|0|
S2S76Vq;S7fA3S9aS7fVA;Vp;Vn;Vv3;A5F_;").
Proof.
  intros HQ. assert (HQ' : q <> QA) by (rewrite HQ; discriminate). pose proof (HE_Be HQ) as HE. pose proof TB as [T1 T2]. pose proof (CBND HQ') as (C1 & C2 & C3 & C4 & _).
  pose proof BND as (B1 & _ & B3 & B4 & B5 & B6 & _ & _ & _ & S1 & S2 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1, S1.
  assert (IN : forall sc, In sc (LCELLS QBe) -> In sc (LCELLS q)) by (rewrite HQ; intros sc Hsc; exact Hsc).
  pose proof (ENBX' HQ') as ENB.
  assert (ENBu : bv_unsigned (eval rhoE NBX) = nbF) by (rewrite ENB; apply u64_lit; lia).
  unfold leaf_cells. cbn zeta. fold G T nbF. rewrite HE. cbn [qsize fold_right length Z.of_nat].
  repeat apply conj.
  - cellv S_qc (c8 0 (SLit 1)) 8 IN EcQ. reflexivity.
  - cellv S_qc (c8 8 NBX) 8 IN EcQ. exact ENB.
  - cellv S_qc (c8 16 NBX) 8 IN EcQ. exact ENB.
  - cellv S_qc (c8 24 (SAlu ALU_ADD (SVar 123) (SAlu ALU_ADD (SVar 13) (SLit 8192)))) 8 IN EcQ.
    replace (0 + (n + kQuarantineBatchSize)) with (qsize (aa_q_thread A) + (n + 8192)) by (rewrite HE; reflexivity).
    apply eval_add; [exact E123 | apply eval_add; [exact E13 | reflexivity]].
  - cellv S_pc (c4 1920 (SAlu ALU_ADD (SVar 127) (SLit (-1)))) 4 IN EcA. change (Z.of_nat (length (cache24 A))) with (cnt24 A). replace (cnt24 A - 1) with (cnt24 A + -1) by lia.
    apply eval_add; [exact E127 | reflexivity].
  - cellv S_nb (c8 0 (SLit 0)) 8 IN ENBu. reflexivity.
  - cellv S_nb (c8 8 (SAlu ALU_ADD (SVar 13) (SLit 8192))) 8 IN ENBu. unfold kQuarantineBatchSize. apply eval_add; [exact E13 | reflexivity].
  - cellv S_nb (c8 16 (SLit 1)) 8 IN ENBu. reflexivity.
  - cellv S_nb (c8 24 (SAlu ALU_ADD (SVar 12) (SLit (-16)))) 8 IN ENBu. replace (p - 16) with (p + -16) by lia. apply eval_add; [exact E12 | reflexivity].
  - cellv S_pc (c4 1924 (SVar 128)) 4 IN EcA. cbn [eval]. exact E128.
  - cellv S_pc (c8 1928 (SVar 129)) 8 IN EcA. cbn [eval]. exact E129.
Qed.

Lemma LC_Bf' : ltac2:(tb__ "0|0|
S2S76Vq;S78A3S9aS78VA;Vp;Vn;Vv3;A5F_;").
Proof.
  intros HQ. assert (HQ' : q <> QA) by (rewrite HQ; discriminate). pose proof (HNE_Bf HQ) as HNE. pose proof TB as [T1 T2]. pose proof (CBND HQ') as (C1 & C2 & C3 & C4 & _).
  pose proof (QBND HNE) as (Q1 & Q2 & Q3 & _).
  pose proof BND as (B1 & _ & B3 & B4 & B5 & B6 & _ & _ & _ & S1 & S2 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1, S1.
  assert (IN : forall sc, In sc (LCELLS QBf) -> In sc (LCELLS q)) by (rewrite HQ; intros sc Hsc; exact Hsc).
  pose proof (ENBX' HQ') as ENB.
  assert (ENBu : bv_unsigned (eval rhoE NBX) = nbF) by (rewrite ENB; apply u64_lit; lia).
  assert (EQB : bv_unsigned (eval rhoE (SVar 122)) = qbF) by (cbn [eval]; rewrite (E122 HNE); fold qbF; apply u64_lit; lia).
  unfold leaf_cells. cbn zeta. fold G T nbF. change (last (aa_q_thread A) qb_dflt) with (lastq A). fold qbF.
  repeat apply conj.
  - cellv S_qc (c8 0 (SAlu ALU_ADD (SVar 120) (SLit 1))) 8 IN EcQ. apply eval_add; [exact E120 | reflexivity].
  - cellv S_qc (c8 8 (SVar 121)) 8 IN EcQ. cbn [eval]. exact (E121 HNE).
  - cellv S_qc (c8 16 NBX) 8 IN EcQ. exact ENB.
  - cellv S_qc (c8 24 (SAlu ALU_ADD (SVar 123) (SAlu ALU_ADD (SVar 13) (SLit 8192)))) 8 IN EcQ. unfold kQuarantineBatchSize.
    apply eval_add; [exact E123 | apply eval_add; [exact E13 | reflexivity]].
  - cellv S_bh (c8 0 NBX) 8 IN EQB. exact ENB.
  - cellv S_pc (c4 1920 (SAlu ALU_ADD (SVar 127) (SLit (-1)))) 4 IN EcA. change (Z.of_nat (length (cache24 A))) with (cnt24 A). replace (cnt24 A - 1) with (cnt24 A + -1) by lia.
    apply eval_add; [exact E127 | reflexivity].
  - cellv S_nb (c8 0 (SLit 0)) 8 IN ENBu. reflexivity.
  - cellv S_nb (c8 8 (SAlu ALU_ADD (SVar 13) (SLit 8192))) 8 IN ENBu. unfold kQuarantineBatchSize. apply eval_add; [exact E13 | reflexivity].
  - cellv S_nb (c8 16 (SLit 1)) 8 IN ENBu. reflexivity.
  - cellv S_nb (c8 24 (SAlu ALU_ADD (SVar 12) (SLit (-16)))) 8 IN ENBu. replace (p - 16) with (p + -16) by lia. apply eval_add; [exact E12 | reflexivity].
  - cellv S_pc (c4 1924 (SVar 128)) 4 IN EcA. cbn [eval]. exact E128.
  - cellv S_pc (c8 1928 (SVar 129)) 8 IN EcA. cbn [eval]. exact E129.
  - cellv S_bh (c8 8 (SVar 125)) 8 IN EQB. cbn [eval]. exact E125.
  - cellv S_bh (c8 16 (SLit 1021)) 8 IN EQB. cbn [eval]. clear -QC HQ. subst q. cbn in QC. destruct QC as (_ & EK & _). unfold lastq in EK. unfold kQuarantineBatchCount in EK.
    change (last (aa_q_thread A) qb_dflt) with (lastq A) in EK. rewrite EK. reflexivity.
Qed.

Lemma LCE : ltac2:(tb__ "0|0|
S9aVq;VA';Vp;Vn;Vv3;A5").
Proof.
  assert (X : leaf_cells q A p n v3).
  { destruct (F0A_rebuild.QDEC q) as [HQ|HQ]; [rewrite HQ at 1; exact (LC_A' HQ)|].
    assert (HQ3 : q = QBe \/ q = QBf) by (clear -HQ; destruct q; [congruence | left; reflexivity | right; reflexivity]).
    destruct HQ3 as [HQ3|HQ3]; rewrite HQ3 at 1; [exact (LC_Be' HQ3) | exact (LC_Bf' HQ3)]. }
  unfold leaf_cells in X |- *. rewrite Enb, Ecache24. destruct DEQ as (EG & _ & _ & _ & _ & _ & EQT & _). rewrite EG, EQT. exact X.
Qed.

Lemma VHW : ltac2:(tb__ "0|1|
S6S0S0S3S3SaZ0R1A2SbR1Z100M0A2A2S3S2S0SfR1Z4A2Z1A3SadVv3;SaeSeVp;Z10A2U4S9S9Z3SdG0R1A2A2SdZ10000S11Vn;ScZ2Z20A2A2A2A2A3A2A2A2Lt';A2").
Proof.
  destruct E107' as (t' & T1 & T2 & E7). exists t'. split; [exact T1|]. split; [exact T2|].
  pose proof BND as (B1 & _ & B3 & B4 & B5 & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  assert (IN : In (S_hdr, c4 (-16) (SVar 107)) (LCELLS q)) by (unfold LCELLS; apply in_or_app; left; cbn; tauto).
  apply (CELLV S_hdr (c4 (-16) (SVar 107)) _ 4 _ IN); [cbn [ob_base S_hdr nocellsF O_hdr c_off c4 eval]; rewrite E12, u64_lit, soff_lit_small by lia; lia | reflexivity |].
  cbn [c4 SymState.c_val eval]. apply of_unsigned. exact E7.
Qed.
Lemma VHL : ltac2:(tb__ "0|0|
SadVv3;SaeSeVp;ZcA2U4SfVn;ScZ2Z20A2A2A3A2").
Proof.
  pose proof BND as (B1 & _ & B3 & B4 & B5 & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  assert (IN : In (S_hdr, c4 (-12) (SVar 103)) (LCELLS q)) by (unfold LCELLS; apply in_or_app; left; cbn; tauto).
  apply (CELLV S_hdr (c4 (-12) (SVar 103)) _ 4 _ IN); [cbn [ob_base S_hdr nocellsF O_hdr c_off c4 eval]; rewrite E12, u64_lit, soff_lit_small by lia; lia | reflexivity |].
  cbn [c4 SymState.c_val eval]. exact E103.
Qed.
Lemma Efq : ltac2:(tb__ "0|0|
S2S35S5aA1S99Vq;VA';Vp;Vn;A4S99Vq;VA;Vp;Vn;A4A3").
Proof. unfold freeQ. rewrite Enb. destruct DEQ as (_ & _ & _ & _ & _ & _ & EQT & _). rewrite EQT. reflexivity. Qed.
Lemma QSZ : ltac2:(tb__ "0|0|
S2S3bS19A1S49S19S1fS89VXf;A1A1U0A3S3cS19S4fVq;A1A2A3SaSb4S99Vq;VA';Vp;Vn;A4A1SccA2F_;").
Proof.
  intros FQS. rewrite Efq. pose proof (SPA_facts_hold segs _ _ _ _ _ H) as HF. pose proof (nth_error_In _ _ FQS) as HIN. pose proof (proj1 (Forall_forall _ _) HF _ HIN) as X.
  unfold FQX in X. cbn [holds] in X.
  pose proof BND as (B1 & _ & B3 & B4 & B5 & B6 & _). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  destruct DEQ as (EG & _ & _ & _ & _ & _ & EQT & _).
  pose proof (qF A' rhoE tpE md p n HA' HL') as QF. cbn zeta in QF. rewrite EQT in QF. destruct QF as (_ & _ & _ & [QS0 QSM] & QSL & QL).
  unfold kQuarantineCacheMax in *.
  assert (EV : exists v, qsize (freeQ q A p n) = v /\ eval rhoE (QSX q) = Z_to_bv 64 v /\ 0 <= v < 2 ^ 64).
  { destruct (F0A_rebuild.QDEC q) as [HQ|HQ].
    - exists (qsize (aa_q_thread A) + n). rewrite (F0A_rebuild.FQ_A q A p n HQ). pose proof (HNE_A HQ) as HNE.
      split; [rewrite qsize_app; cbn [qsize fold_right lbQ qb_size]; pose proof (qsize_removelast_last (aa_q_thread A) HNE) as QR; unfold lastq; clear -QR; lia|].
      split; [unfold QSX; rewrite HQ; apply eval_add; [exact E123 | exact E13] | clear -QS0 QSM B1 B3 B4 B5; lia].
    - exists (qsize (aa_q_thread A) + (n + 8192)). rewrite (F0A_rebuild.FQ_B q A p n QC HQ).
      split; [rewrite qsize_app; cbn [qsize fold_right nbQ qb_size]; unfold kQuarantineBatchSize; clear; lia|].
      split; [| clear -QS0 QSM B1 B3 B4 B5; lia].
      replace (QSX q) with (SAlu ALU_ADD (SVar 123) (SAlu ALU_ADD (SVar 13) (SLit 8192))) by (clear -HQ; destruct q; [congruence | reflexivity | reflexivity]).
      apply eval_add; [exact E123 | apply eval_add; [exact E13 | reflexivity]]. }
  destruct EV as (v & -> & EVe & Bv). rewrite EVe in X. cbn [eval branch_taken] in X. unfold bv_ltu in X. rewrite !u64_lit in X by (clear -Bv; lia).
  destruct (Z.ltb_spec (2 ^ 20) v) as [L|L]; [exfalso; exact (X eq_refl) | clear -L; lia].
Qed.

Lemma CLA : ltac2:(tb__ "0|0|
S0S7Sa4VCST;VA;R1A3Sa4VCST;VA';R1A3A2Fa;").
Proof.
  intros a. destruct DEQ as (EG & _ & _ & _ & _ & EL & _ & _ & _ & EFB & _). unfold client_addrA, client_mut_addrA, aa_frames. rewrite EG, EL, EFB. tauto.
Qed.
Lemma CLS : ltac2:(tb__ "0|0|
S0S7Sa5VCST;VXGL;VA;R1A4Sa5VCST;VXGL;VA';R1A4A2Fa;").
Proof. intros a. unfold client_shadowA. split; (intros [(x & Hx & E)|R]; [left; exists x; split; [apply CLA; exact Hx | exact E] | right; exact R]). Qed.

Definition rebuilt_stmt (B : Z) (A2 : AA) (l1 l2 : list (Z * Z)) : Prop := ltac2:(tb__ "0|2|
S3S9fVB;VA2;Vrho3;VtpE;Vmd;A5S3S2S5dVA2;S9bVq;VA';Vl1;Vl2;Vp;Vn;A6A3S3S2S35S34S0S0A2M0A1M1S5cVA;A1S3eG0Vl1;S39G0S36S0S0Vp;Vn;A4Vl2;A3A3A3S3S2G1S5cVA2;A1S3eG0Vl1;Vl2;A3A3S3S2G1S68VA2;A1S68VA;A1A3S3S2S0S60VA2;A1S60VA;A1A3S3S2S0S5fVA2;A1S5fVA;A1A3S3S2S0S5eVA2;A1S9S5eVA;A1Z1A2A3S3S2S65S61VA2;A1S61VA;A1A3S3SabVCST;VXGL;VA;VA2;S1bVrho;A1S1bVrho3;A1A6S3VKc;Vtr;Vmd;A2S73VA;VA2;A2A2A2A2A2A2A2A2A2A2A2A2").
Lemma f0_rebuilt : ltac2:(tb__ "0|2|
S0S35S34S0S0A2M0A1M1G1S2G1S5cVA';A1S3eG0R2S39G0S36S0S0Vp;Vn;A4R1A3A3A3SaSb4S99Vq;VA';Vp;Vn;A4A1R4A2SdfR5S9bVq;VA';R4R3Vp;Vn;A6R4R3A4F_;F_;Fl2;Fl1;FB;").
Proof.
  intros B l1 l2 ELV HQB.
  destruct VHW as (t' & T1 & T2 & VH). destruct DEQ as (EG & EC & ECI & ESEC & EPC & EL & EQT & EQG & EII & EFB & EFH & EV & EKM & EKF).
  pose proof HJ' as (_ & HK & Htp). pose proof HA' as HAx. pose proof HAx as (HGx & _).
  assert (RB := free_rebuild_B CST XGL HCST HXGL HCSTF B q A' rhoE rho3 tpE md p n l1 l2 t' HAx ELV HCL Hii' QC' T1 T2 VH VHL
                 (fun z Hc => PRES z (proj1 (CHG' z) Hc)) LCE
                 (fun z Hn => VO z (fun Hc => Hn (proj2 (CHG' z) Hc)))
                 (fun a Ha Hn Hr => RMO a Ha (fun Hc => Hn (proj2 (CHG' a) Hc)) ltac:(rewrite EG in Hr; exact Hr))
                 DEFM HQB).
  cbn zeta in RB. destruct RB as (HA2 & HL2 & HFR2 & HV2 & HKm2 & HKf2 & HGe2 & KEPT2 & CK2).
  set (A2 := freeA q A' l1 l2 p n) in *. unfold rebuilt_stmt.
  split; [exact HA2|]. split; [reflexivity|].
  split; [rewrite <- EL; exact ELV|].
  split; [exact HL2|]. split; [rewrite HFR2; unfold aa_frames; rewrite EFB; reflexivity|].
  split; [rewrite HV2; exact EV|]. split; [rewrite HKm2; exact EKM|]. split; [rewrite HKf2; exact EKF|]. split; [rewrite HGe2; exact EG|].
  split; [|split; [exact HK|]].
  -
    destruct HLK as (_ & _ & Lm & Ld). destruct HAG as (_ & _ & Agm). destruct KEPT2 as [K1 K2].
    assert (Erm1 : rm rho1 = rm rho) by (unfold rho1, rhoF_of; apply rm_rho_sets).
    split.
    + intros a Ha Hcl.

      assert (EQ1 : rm rhoE (Z_to_bv 64 a) = rm rho (Z_to_bv 64 a)).
      { rewrite <- (Agm (Z_to_bv 64 a)). rewrite (Lm (Z_to_bv 64 a)) by (rewrite u64_lit by (clear -Ha; lia); apply HKEEP; clear -Hcl; tauto).
        rewrite Erm1. reflexivity. }
      rewrite (K1 a Ha); [exact EQ1|].
      destruct Hcl as [(C1 & C2 & C3)|(C1 & C2 & C3)];
        [left; split; [apply CLA; exact C1 | split; [exact C2 | exact C3]] | right; split; [apply CLS; exact C1 | split; [exact C2 | rewrite EQ1; exact C3]]].
    + intros x j Hx Hj Hdef. apply (K2 x j); [destruct Hx as [[C1 C2]|GX]; [left; split; [apply CLA; exact C1 | exact C2] | right; exact GX] | exact Hj |].
      rewrite <- (Agm (word_byte (Sh x) j)). apply Ld; [|rewrite Erm1; exact Hdef].
      assert (Bx : 0 <= x < 2 ^ 47).
      { destruct Hx as [[C1 _]|GX]; [| destruct (HXGL x GX) as [X1 X2]; unfold IMG_HI in X2; clear -X1 X2; lia].
        pose proof HAx as (_ & _ & HF & (Hsep & _) & _).
        exact (proj1 (client_addr_bounds CST HCST A' x _ HGx HF Hsep (proj1 (CLA x) C1))). }
      destruct (word_byte_range (Sh x) j ltac:(unfold Sh, SHADOW_OFF; clear -Bx; lia) Hj) as (W1 & W2 & W3). rewrite W2.
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *.
      pose proof (Z.div_pos x 8 ltac:(clear -Bx; lia) ltac:(clear; lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(clear; lia) ltac:(clear -Bx; lia)).
      clear -W3 Hj H0 H1. lia.
  - intros c Hcc NE Hfr. apply (CK2 c Hcc NE). unfold class_fresh in Hfr |- *. rewrite EC. exact Hfr.
Qed.

Lemma f0_released : ltac2:(tb__ "0|2|
S0S35S34S0S0A2M0A1M1G1S2G1S5cVA';A1S3eG0R2S39G0S36S0S0Vp;Vn;A4R1A3A3A3SaSb4S99Vq;VA';Vp;Vn;A4A1R4A2S3Sa1Vsegs;VKJ;VXK;Vrho3;VtpE;Vw;A6S3SdfR5S9bVq;VA';R4R3Vp;Vn;A6R4R3A4S3S1Sd3R1Sb3A2S2S45Q40A1S14Vrho3;R2A2S14Vrho1;R2A2A3F_;Fi;S3S1S2S35S45Q8A1A1S1cVrho3;R1A2S1cVrho1;R1A2A3Fl;S3SaaVA';VrhoE;A2SacVA';VrhoE;A2A2A2A2A2A2F_;F_;Fl2;Fl1;FB;").
Proof.
  intros B l1 l2 ELV HQB. split; [exact Hb|]. split; [exact (f0_rebuilt B l1 l2 ELV HQB)|].
  split; [intros i Hi; unfold rho3; cbn [rho_absorb rw]; exact (ERW i Hi)|]. split; [intros l; unfold rho3; cbn [rho_absorb rl]; exact (ERL l)|].
  destruct H as [_ [_ HJ]]. destruct HJ as (_ & _ & _ & _ & Htp & _ & Htop). exact (conj Htp Htop).
Qed.

Theorem f0_finish : ltac2:(tb__ "0|1|
S2S3bS19A1S49S19S1fS89VXf;A1A1U0A3S3cS19S4fVq;A1A2A3Sa3Vsegs;Sb2Vrho;Vtp;S39S34S8aSa2A2M0S36S8aSa2Sa7Sa6VW;Vst;A3Sa8VAInv;VCST;VXGL;VA;VKc;A5A4S37G0A1A3Vw;A6F_;").
Proof.
  intros FQS. destruct (in_split _ _ HL') as (l1 & l2 & ELV0).
  destruct (f0_rebuilt kQuarantineCacheMax l1 l2 ELV0 (QSZ FQS)) as (HA2 & _ & ELV & HL2 & HFR2 & HV2 & HKm2 & HKf2 & HGe2 & KEPT2 & HK & CK2).
  set (A2 := freeA q A' l1 l2 p n) in *.
  pose proof HJ' as (_ & _ & Htp). pose proof HA' as HAx. pose proof HAx as (HGx & _).

  assert (Hc : SPA segs KJ XR rho3 tpE w).
  { rewrite <- EQR. eapply SPA_restate; [exact WXR | exact DXR | exact NXR | | constructor | exact Hb].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; clear; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. destruct (geom_old _ HGx) as (_ & _ & _ & G4 & _). rewrite G4. reflexivity. }

  pose proof (smatchA_entails segs _ _ _ rho3 tpE _ ENT (proj1 Hc)) as Hsm4.
  set (rho4 := rho_sub rho3 sX) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoE k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ SID Hk). reflexivity. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 sX).
  destruct HR as [[AGw AGl] _ _ _ _ _ _ _ _ _].
  exists (L_free AE_A W st), (JL_free AInv CST XGL A Kc), rho4, tpE.
  split; [left; reflexivity|]. split; [|split; [exact Hsm4|]].
  { split.
    - intros k Hk. rewrite (Hlow k Hk), (ERW k) by (unfold NF, GW in *; clear -Hk; lia). exact (AGw k Hk).
    - intros l. unfold rho4, rho3. cbn [rl rho_sub rho_absorb]. rewrite ERL. exact (AGl l). }
  cbn [w_tr w_cfg cfg_model fst snd]. unfold JL_free. exists A2, l1, l2.
  split; [unfold AInv, AInvA; unfold AInvB in HA2; rewrite Erm4; exact HA2|].
  split; [rewrite Hp12, Hn13; exact ELV|].
  split; [exact HL2|]. split; [exact HFR2|]. split; [exact HV2|]. split; [exact HKm2|]. split; [exact HKf2|]. split; [exact HGe2|].
  split; [rewrite Erm4; exact KEPT2|]. split; [exact HK | exact CK2].
Qed.

End FIN.

Theorem f0_exit : ltac2:(tb__ "0|3|
S2S3bS19A1S49S19S1fS89VXf;A1A1U0A3S3cS19S4fVq;A1A2A3Se4OF_;S5dSa9S1aS35S45Q40M0A1A1M1S0S0S0S94S0OF_;S2S0S47G0S14R7PcA2A2R5A3S2S0S47G0S14R8PdA2A2R5A3S48S34S0S0A2S36S0S0R7R6A4S5cRbA1A3SddR8R7A2S2S38S62RdA1S3aA3S95Vq;ReA2Sc4RdS90RfRdRbRaR9R8A6A2S2S0S91R9A1Sc6A3S0S4Sa4VCST;R12R1A3Sa5VCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S5dS1aS1aG1Sc3R16R4A2Sd2RfS90R17R15R13R12R11R10A6R4A3Se3Vsegs;R19Sa1Vsegs;Sc2VnW;Vst;S42R6R17R5A6VXf;R4R3A5Sa3Vsegs;Sb2R16R15S39S34S8aSa2A2M2S36S8aSa2Sa7Sa6VW;Vst;A3Sa8VAInv;VCST;VXGL;R18R17A5A4S37G2A1A3A5A4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;F_;").
Proof.
  intros FQS ok A Kc rho tp p n t jv keep Hp Hn HL HHI Hii HQ HR HJ HK A' rho1' rhoE tpE HDO HLK.
  eapply triple_conseq; [intros w Hw; exact Hw | | apply triple_refl].
  intros [tr [ms md]] Hw. exact (f0_finish A Kc rho tp p n t jv keep A' rho1' rhoE tpE tr ms md Hp Hn HL HHI Hii HQ HR HJ HDO HLK HK Hw FQS).
Qed.
Theorem ef0_exit : ltac2:(tb__ "0|3|
S2S3bS19A1S49S19S1fS89VXf;A1A1U0A3S3cS19S4fVq;A1A2A3S5dSa9S1aS35S45Q40M0A1A1M1S0S0S0S94S0OF_;S2S0S47G0S14R7PcA2A2R5A3S2S0S47G0S14R8PdA2A2R5A3S48S34S0S0A2S36S0S0R7R6A4S5cRbA1A3SddR8R7A2S2S38S62RdA1S3aA3S95Vq;ReA2Sc4RdS90RfRdRbRaR9R8A6A2S2S0S91R9A1Sc6A3S0S4Sa4VCST;R12R1A3Sa5VCST;VXGL;R12R1A4A2RbR2A1F_;Fa;S5dS1aS1aG1Sc3R16R4A2Sd2RfS90R17R15R13R12R11R10A6R4A3Se2Vsegs;Sa1Vsegs;Sc2VnW;Vst;S42R6R17R5A6VXf;R4R3A5Sa3Vsegs;Sb2R16R15S39S34S8aSa2A2M2S36S8aSa2Sa7Sa6VW;Vst;A3Sa8VAInv;VCST;VXGL;R18R17A5A4S37G2A1A3A5A3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;F_;").
Proof.
  intros FQS A Kc rho tp p n t jv keep Hp Hn HL HHI Hii HQ HR HJ HK A' rho1' rhoE tpE HDO HLK.
  eapply etriple_conseq; [intros w Hw; exact Hw | | apply etriple_refl].
  intros [tr [ms md]] Hw. exact (f0_finish A Kc rho tp p n t jv keep A' rho1' rhoE tpE tr ms md Hp Hn HL HHI Hii HQ HR HJ HDO HLK HK Hw FQS).
Qed.
End EXIT.
End F0A_exit.

