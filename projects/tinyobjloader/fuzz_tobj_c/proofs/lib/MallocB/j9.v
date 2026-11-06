(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModelP RefillBits jc RebuildRZ.

(* [comment removed for export] *)
Module SpineMallocS8iW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "SVar"; "ss_next"; "SPBranch"; "SLit"; "swf"; "SPNot"; "SPUle"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "option"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "C7p"; "C8"; "C8p"; "F_gen"; "V_CLS"; "V_ND"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "n8e"; "C7"; "BP"; "LPe"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8"; "E7c1'"; "E7c2'"; "E7q1'"; "E7q2'"; "a0e7"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "tab_ok"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8iW2.INST"; "s8a_0"; "s8b_0"; "s8c_0"; "s8d_0"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S17S1S1S0S1S2aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C7 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C7] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C7]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7c1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7c1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7c1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7c2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7c2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7c2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S17S4S4S0S4S25VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (creg7a W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [creg7a] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [creg7a]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S17S4S4S0S4S26VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (creg7b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [creg7b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [creg7b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S17S1S1S0S1S2fU2Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7c1' 2%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7c1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7c1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S17S1S1S0S1S30U2Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7c2' 2%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7c2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7c2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S17S1S1S0S1S20VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C8]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1fVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C7p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C7p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C7p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1dVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7q1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7q1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7q1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1eVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7q2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7q2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7q2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S17S4S4S0S4S27VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (creg7c W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [creg7c] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [creg7c]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_13 : ltac2:(tb__ "0|0|
S17S4S4S0S4S28VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (creg7d W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [creg7d] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [creg7d]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_14 : ltac2:(tb__ "0|0|
S17S1S1S0S1S31U2Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7q1' 2%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7q1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7q1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_15 : ltac2:(tb__ "0|0|
S17S1S1S0S1S32U2Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7q2' 2%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7q2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E7q2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_16 : ltac2:(tb__ "0|0|
S17S1S1S0S1S21VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C8p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma Cert7_0 : ltac2:(tb__ "0|1|
S0SeS45S19Ufa0S10S34Z3c8bcS10S34Z3ca04S11S34A1A3A3S18S10S1S2aVW;Vst;Vtmax;A3S11S1A1M0A3S10S1S1aVW;Vst;Vtmax;A3S10S1S1bVW;Vst;Vtmax;A3S10S1S1cVW;Vst;Vtmax;A3G0A3A3A3A6SfA3").
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
S0SeS45S19Ufa0S10S34Z3ca04S11S34A1A3S18S10S1S1fVW;Vst;Vtmax;A3S11S1A1M0A3S10S1S1dVW;Vst;Vtmax;A3S10S1S1eVW;Vst;Vtmax;A3G0A3A3A6SfA3").
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
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "entailsA"; "la_state"; "leafA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sobj"; "sprop"; "ss_facts"; "ss_next"; "sv"; "SLit"; "sprop_below"; "ss_objs"; "SPBranch"; "SPNot"; "SVar"; "swf"; "@Corelib.Init.Datatypes"; "option"; "bool"; "true"; "nil"; "list"; "cons"; "nat"; "Some"; "prod"; "pair"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "memset_entryA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS9iW2.INST"; "CC8ma_0"; "CC8map_0"; "X8b_0"; "X8bp_0"; "U8b_0"; "U8bp_0"; "s8_0"; "s8b_0"; "s8bp_0"; "s8p_0"; "R8_0"; "R8b_0"; "R8bp_0"; "R8p_0"; "T8_0"; "T8b_0"; "T8bp_0"; "T8p_0"; "i9_0"; "i9p_0"; "SM_0"; "SMp_0"; "S8s_0"; "S8sp_0"; "U8b0_0"; "U8b0p_0"; "i8_0"; "i8p_0"; "s9m_0"; "s9mp_0"; "sd8_0"; "sd8b_0"; "sd8bp_0"; "sd8p_0"; "SU_0"; "SUp_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "C9"; "C9p"; "E8a"; "E8b"; "E8pa"; "E8pb"; "upd"; "MSENT"; "ube"; "C8"; "C8p"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "map"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S61VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C8]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S5aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E8a W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E8a] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E8a]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S5bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E8b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E8b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E8b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|1|
S4cS1S56S18S1cS1aScA2A1S18S8A1S15S18S9A1S1Ffacts;Freset;Fobjs;Fru;Fpc;FE;M0G0S6G0S5eVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (upd W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [upd] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [upd]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S58VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C9]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S62VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C8p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S5cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E8pa W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E8pa] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E8pa]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S5dVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E8pb W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E8pb] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E8pb]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S4cS1S1S6S1S59VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C9p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma Cert8_0 : ltac2:(tb__ "0|1|
S6S15S69S24Ufa0S19S56Zdb004S19S56Z3ca54S17S56A1A3A3S23S19S1S61VW;Vst;Vtmax;A3S17S1A1M0A3S19S1S5aVW;Vst;Vtmax;A3S19S1S5bVW;Vst;Vtmax;A3G0A3A3A6S16A3").
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
S6S15S69S24Ufa0S19S56Zdb004S19S56Z3ca54S17S56A1A3A3S23S19S1S62VW;Vst;Vtmax;A3S17S1A1M0A3S19S1S5cVW;Vst;Vtmax;A3S19S1S5dVW;Vst;Vtmax;A3G0A3A3A6S16A3").
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

(* [comment removed for export] *)
Module SpineMallocS8i.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_facts"; "SVar"; "ss_next"; "SPBranch"; "SLit"; "swf"; "SPNot"; "SPUle"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "pair"; "prod"; "Some"; "option"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "C7p"; "C8"; "C8p"; "F_gen"; "V_CLS"; "V_ND"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "n8e"; "C7"; "BP"; "LPe"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8"; "E7c1'"; "E7c2'"; "E7q1'"; "E7q2'"; "a0e7"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "tab_ok"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineMallocS8i.INST"; "s8a_0"; "s8b_0"; "s8c_0"; "s8d_0"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S17S1S1S0S1S2aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C7 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C7] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C7]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7c1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7c1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E7c1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7c2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7c2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E7c2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E7p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S17S4S4S0S4S25VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (creg7a W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [creg7a] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [creg7a]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S17S4S4S0S4S26VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (creg7b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [creg7b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [creg7b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S17S1S1S0S1S2fU0Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7c1' 0%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7c1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E7c1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S17S1S1S0S1S30U0Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7c2' 0%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7c2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E7c2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S17S1S1S0S1S20VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C8]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1fVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C7p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C7p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C7p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1dVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7q1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7q1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E7q1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S17S1S1S0S1S1eVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7q2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7q2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E7q2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S17S4S4S0S4S27VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (creg7c W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [creg7c] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [creg7c]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_13 : ltac2:(tb__ "0|0|
S17S4S4S0S4S28VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (creg7d W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [creg7d] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [creg7d]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_14 : ltac2:(tb__ "0|0|
S17S1S1S0S1S31U0Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7q1' 0%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7q1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E7q1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_15 : ltac2:(tb__ "0|0|
S17S1S1S0S1S32U0Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E7q2' 0%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E7q2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E7q2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_16 : ltac2:(tb__ "0|0|
S17S1S1S0S1S21VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C8p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C8p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C8p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma Cert7_0 : ltac2:(tb__ "0|1|
S0SeS45S19Ufa0S10S34Z3c8bcS10S34Z3ca04S11S34A1A3A3S18S10S1S2aVW;Vst;Vtmax;A3S11S1A1M0A3S10S1S1aVW;Vst;Vtmax;A3S10S1S1bVW;Vst;Vtmax;A3S10S1S1cVW;Vst;Vtmax;A3G0A3A3A3A6SfA3").
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
S0SeSbS2S2fU0Vst;Vtmax;A3A1A1SfA3").
Proof. memo_rw (E7c1' 0%nat st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W7b_0 : ltac2:(tb__ "0|0|
S0SeSbS2S30U0Vst;Vtmax;A3A1A1SfA3").
Proof. memo_rw (E7c2' 0%nat st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D7a_0 : ltac2:(tb__ "0|4|
S0S16S14S12S14S4S4A2M0A1M1S12S5A1M2A2M3A1S36S2S1aVW;Vst;Vtmax;A3A1S2S2fU0Vst;Vtmax;A3A1A2S15G3S13G1G2S10G0S13S4S4S25VW;Vst;Vtmax;A3S7S23A1A4S11G0A1A3S11S5A1A4A2A3").
Proof. memo_rw (E7c1 W st tmax) memo_1. memo_rw (E7c1' 0%nat st tmax) memo_6. memo_rw (creg7a W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D7b_0 : ltac2:(tb__ "0|4|
S0S16S14S12S14S4S4A2M0A1M1S12S5A1M2A2M3A1S36S2S1bVW;Vst;Vtmax;A3A1S2S30U0Vst;Vtmax;A3A1A2S15G3S13G1G2S10G0S13S4S4S26VW;Vst;Vtmax;A3S7S23A1A4S11G0A1A3S11S5A1A4A2A3").
Proof. memo_rw (E7c2 W st tmax) memo_2. memo_rw (E7c2' 0%nat st tmax) memo_7. memo_rw (creg7b W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S35S8S2S2fU0Vst;Vtmax;A3A1A1S8S2S1aVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E7c1' 0%nat st tmax) memo_6. memo_rw (E7c1 W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S35S8S2S30U0Vst;Vtmax;A3A1A1S8S2S1bVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E7c2' 0%nat st tmax) memo_7. memo_rw (E7c2 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
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
S3dS18S2S2fU0Vst;Vtmax;A3A1S2S20VW;Vst;Vtmax;A3A1A3").
Definition s8b_0 : ltac2:(tb__ "0|0|
S3e") := ltac2:(tb__ "0|0|
S3dS18S2S30U0Vst;Vtmax;A3A1S2S20VW;Vst;Vtmax;A3A1A3").
Lemma ENT8a_0 : ltac2:(tb__ "0|0|
S0SeS3S2fU0Vst;Vtmax;A3S20VW;Vst;Vtmax;A3S46A3SfA3").
Proof. unfold s8a_0. memo_rw (E7c1' 0%nat st tmax) memo_6. memo_rw (C8 W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT8b_0 : ltac2:(tb__ "0|0|
S0SeS3S30U0Vst;Vtmax;A3S20VW;Vst;Vtmax;A3S47A3SfA3").
Proof. unfold s8b_0. memo_rw (E7c2' 0%nat st tmax) memo_7. memo_rw (C8 W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID8a_0 : ltac2:(tb__ "0|0|
S0SeS3fS46S18A2SfA3").
Proof. unfold s8a_0. memo_rw (C8 W st tmax) memo_8. memo_rw (E7c1' 0%nat st tmax) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID8b_0 : ltac2:(tb__ "0|0|
S0SeS3fS47S18A2SfA3").
Proof. unfold s8b_0. memo_rw (C8 W st tmax) memo_8. memo_rw (E7c2' 0%nat st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
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
S0SeS45S19Ufa0S10S34Z3ca04S11S34A1A3S18S10S1S1fVW;Vst;Vtmax;A3S11S1A1M0A3S10S1S1dVW;Vst;Vtmax;A3S10S1S1eVW;Vst;Vtmax;A3G0A3A3A6SfA3").
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
S0SeSbS2S31U0Vst;Vtmax;A3A1A1SfA3").
Proof. memo_rw (E7q1' 0%nat st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W7d_0 : ltac2:(tb__ "0|0|
S0SeSbS2S32U0Vst;Vtmax;A3A1A1SfA3").
Proof. memo_rw (E7q2' 0%nat st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D7c_0 : ltac2:(tb__ "0|4|
S0S16S14S12S14S4S4A2M0A1M1S12S5A1M2A2M3A1S36S2S1dVW;Vst;Vtmax;A3A1S2S31U0Vst;Vtmax;A3A1A2S15G3S13G1G2S10G0S13S4S4S27VW;Vst;Vtmax;A3S7S23A1A4S11G0A1A3S11S5A1A4A2A3").
Proof. memo_rw (E7q1 W st tmax) memo_10. memo_rw (E7q1' 0%nat st tmax) memo_14. memo_rw (creg7c W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D7d_0 : ltac2:(tb__ "0|4|
S0S16S14S12S14S4S4A2M0A1M1S12S5A1M2A2M3A1S36S2S1eVW;Vst;Vtmax;A3A1S2S32U0Vst;Vtmax;A3A1A2S15G3S13G1G2S10G0S13S4S4S28VW;Vst;Vtmax;A3S7S23A1A4S11G0A1A3S11S5A1A4A2A3").
Proof. memo_rw (E7q2 W st tmax) memo_11. memo_rw (E7q2' 0%nat st tmax) memo_15. memo_rw (creg7d W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX7c_0 : ltac2:(tb__ "0|0|
S0S35S8S2S31U0Vst;Vtmax;A3A1A1S8S2S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E7q1' 0%nat st tmax) memo_14. memo_rw (E7q1 W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX7d_0 : ltac2:(tb__ "0|0|
S0S35S8S2S32U0Vst;Vtmax;A3A1A1S8S2S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E7q2' 0%nat st tmax) memo_15. memo_rw (E7q2 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
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
S3dS18S2S31U0Vst;Vtmax;A3A1S2S21VW;Vst;Vtmax;A3A1A3").
Definition s8d_0 : ltac2:(tb__ "0|0|
S3e") := ltac2:(tb__ "0|0|
S3dS18S2S32U0Vst;Vtmax;A3A1S2S21VW;Vst;Vtmax;A3A1A3").
Lemma ENT8c_0 : ltac2:(tb__ "0|0|
S0SeS3S31U0Vst;Vtmax;A3S21VW;Vst;Vtmax;A3S48A3SfA3").
Proof. unfold s8c_0. memo_rw (E7q1' 0%nat st tmax) memo_14. memo_rw (C8p W st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT8d_0 : ltac2:(tb__ "0|0|
S0SeS3S32U0Vst;Vtmax;A3S21VW;Vst;Vtmax;A3S49A3SfA3").
Proof. unfold s8d_0. memo_rw (E7q2' 0%nat st tmax) memo_15. memo_rw (C8p W st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID8c_0 : ltac2:(tb__ "0|0|
S0SeS3fS48S18A2SfA3").
Proof. unfold s8c_0. memo_rw (C8p W st tmax) memo_16. memo_rw (E7q1' 0%nat st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID8d_0 : ltac2:(tb__ "0|0|
S0SeS3fS49S18A2SfA3").
Proof. unfold s8d_0. memo_rw (C8p W st tmax) memo_16. memo_rw (E7q2' 0%nat st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS8i.

(* [comment removed for export] *)
Module SpineCallocS7.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "la_state"; "leafA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "Some"; "option"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "ss_next"; "SAlu"; "sv"; "sobj"; "ss_facts"; "SLit"; "eval"; "sprop_below"; "ss_objs"; "swf"; "SVar"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "C6m"; "C6l"; "C6b"; "C7"; "E6l"; "E6s"; "E6m"; "O_U"; "C6"; "E6j"; "LUe"; "ube"; "F_gen"; "n8e"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "JGb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocS7"; "len3e"; "@Stdlib.Lists.List"; "forallb"; "incl"; "nth_error"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "le"; "pow"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zero_covered"; "zobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4"; "pvals_ok"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocS6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition len3e : sv := ltac2:(tb__ "0|1|
S13S3aS13S38S13S39S13S38S13S38S29S2bA3S17N8A1A3S17Z3A1M0A3S17Z1A1A3S13S39S29G0A3A3").

Section PSVals3.
Variable rho : valuation.
Variables SB c x rzv sz n : Z.
Hypothesis PV : ltac2:(tb__ "0|0|
S5aVrho;VSB;Vc;Vx;Vrzv;Vsz;Vn;A7").
Let ab : Z := ltac2:(tb__ "0|0|
S4cS4cVSB;S4dVc;S4fZ2Z20A2A2A2S4dZ10Vx;A2A2").
Ltac pv := pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).

Lemma pv_len3 : ltac2:(tb__ "0|0|
S0S36Q40A1S18Vrho;S48A2S18Vrho;S28A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ub rho _ _ _ _ _ _ PV) as EUB. cbn zeta in EUB. fold ab in EUB.
  pose proof (pv_lu rho _ _ _ _ _ _ PV) as ELU.
  apply bv_eq. rewrite ELU. unfold len3e. cbn [eval]. fold ube. fold n8e.
  assert (EN8 : bv_unsigned (eval rho n8e) = n - n mod 8).
  { unfold n8e. cbn [eval]. rewrite and_val, E12, !u64_lit by (unfold M48; lia). apply land_M48. lia. }
  rewrite sub_val, add_val, srl_val, add_val, add_val, srl_val, EUB, EN8.
  replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity. rewrite !u64_lit by lia. change (3 mod 64) with 3.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  assert (B1 : 17594333495296 <= ab + rzv /\ ab + rzv + n <= 140737479966720) by (unfold ab; lia).
  rewrite (Z.mod_small (ab + rzv + (n - n mod 8))) by lia.
  replace ((ab + rzv + (n - n mod 8) + (2 ^ 64 - 8)) mod 2 ^ 64) with (ab + rzv + (n - n mod 8) - 8).
  2:{ replace (ab + rzv + (n - n mod 8) + (2 ^ 64 - 8)) with ((ab + rzv + (n - n mod 8) - 8) + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add by lia. rewrite (Z.mod_small (ab + rzv + (n - n mod 8) - 8)) by lia. reflexivity. }
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)). pose proof (Z.div_mod rzv 16 ltac:(lia)).
  set (q := SB / 2 ^ 16) in *. set (r := rzv / 16) in *. set (k := n / 8) in *.
  replace (ab + rzv + (n - n mod 8) - 8) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x + 2 * r + k - 1) * 8) by (unfold ab; lia).
  replace (ab + rzv) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x + 2 * r) * 8) by (unfold ab; lia).
  rewrite !Z.div_mul by lia. rewrite (Z.mod_small (_ + 1)) by lia. rewrite (Z.mod_small (_ - _)) by lia. lia.
Qed.
End PSVals3.

Section S7.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S42VAInv;VW;Vst;VA;VKc;S1cPcA1A6").

Section B10aS.
Hypothesis Cert6 : ltac2:(tb__ "0|1|
S0S7S3fS43Ufa0S9S2cZ5f9f8S9S2cZ3c82cSaS2cA1A3A3S34S9S2S26VW;Vst;Vtmax;A3SaS2A1M0A3S9S2S23VW;Vst;Vtmax;A3S9S2S22VW;Vst;Vtmax;A3G0A3A3A6S8A3").

Variable k6 : nat.
Hypothesis NTH6s : ltac2:(tb__ "0|0|
S0SdS15A1S4bS15S1aS1S23VW;Vst;Vtmax;A3A1A1Vk6;A3ScS15S25A2A3").
Hypothesis ZC6s : ltac2:(tb__ "0|0|
S0S7S55S16S1S23VW;Vst;Vtmax;A3A1A1S25A2S8A3").
Variable s7s : wsub.
Hypothesis ENT7s : ltac2:(tb__ "0|2|
S0S7S3S4S23VW;Vst;Vtmax;A3M0S53S1G0A1M1S52S15S1aG1A1Vk6;S56S25A1A4A2A2S21VW;Vst;Vtmax;A3Vs7s;A3S8A3").
Hypothesis SID7s : ltac2:(tb__ "0|0|
S0S7S3eVs7s;S34A2S8A3").

Hypothesis G6l : ltac2:(tb__ "0|0|
S4aS11S2aS16S1S22VW;Vst;Vtmax;A3A1A1A3").
Hypothesis W6l : ltac2:(tb__ "0|0|
S0S7S1bS1S1fVW;Vst;Vtmax;A3A1A1S8A3").
Hypothesis D6l : ltac2:(tb__ "0|4|
S0SdSeSbSeS14S14A2M0A1M1SbS11A1M2A2M3A1S47S1S22VW;Vst;Vtmax;A3A1S1S1fVW;Vst;Vtmax;A3A1A2ScG3SfG1G2S9G0SfS14S14S48S28A4SaG0A1A3SaS11A1A4A2A3").
Hypothesis NX6l : ltac2:(tb__ "0|0|
S0S2dS12S1S1fVW;Vst;Vtmax;A3A1A1S12S1S22VW;Vst;Vtmax;A3A1A1A3").

Theorem spine_s6 : ltac2:(tb__ "0|1|
S30OF_;S44S40S10SbS36Q40M0A1A1S2fS45VW;Vst;A2S41R5A1S33Vsegs;R8S32R6A1A3S4eZ1S46R8S37G0S1dR6PcA2A2A2A2S10S2eVsegs;RbS31Vsegs;S35VW;Vst;RaR9R8A5S21VW;Vst;Vtmax;A3R1R7A5R6A4FrhoX;S10S2eVsegs;RcS31Vsegs;S35VW;Vst;RbRaR9A5S1fVW;Vst;Vtmax;A3R1R8A5R7A4FrhoX;S10S2eVsegs;RdS31Vsegs;S35VW;Vst;RcRbRaA5S26VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt HC7 HC6l rhoE.
  apply (cfg_soundA segs 4000%nat [0x5f9f8; 0x3c82c] GW [C6 W st tmax] [E6s W st tmax; E6l W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert6.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7 (rho_sub rhoX s7s))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW _ (C7 W st tmax) s7s rhoX tp w ENT7s SID7s); [apply JGb_stable; [exact HUS | exact HKc]|].
      apply (SPA_zero_fold segs (JGb W st A Kc rho) rhoX (E6s W st tmax) tp w k6 O_U NTH6s ZC6s Hw).
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC6l rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G6l Hcnt) as PV. cbn zeta in PV.
      unfold C6l, upd. lazy zeta. eapply SPA_restate; [exact W6l | exact D6l | exact NX6l | | constructor | exact Hw].
      unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_len3 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End B10aS.

Section B10bS.
Hypothesis Cert6l : ltac2:(tb__ "0|1|
S0S7S3fS43Ufa0S9S2cZdb004SaS2cA1A3S34S9S2S1fVW;Vst;Vtmax;A3SaS2A1M0A3S9S2S24VW;Vst;Vtmax;A3G0A3A6S8A3").
Hypothesis W6m : ltac2:(tb__ "0|0|
S0S7S1bS1S1eVW;Vst;Vtmax;A3A1A1S8A3").
Hypothesis D6m : ltac2:(tb__ "0|4|
S0SdSeSbSeS14S14A2M0A1M1SbS11A1M2A2M3A1S47S1S24VW;Vst;Vtmax;A3A1S1S1eVW;Vst;Vtmax;A3A1A2ScG3SfG1G2SaG0A1SaS11A1A4A2A3").
Hypothesis NX6m : ltac2:(tb__ "0|0|
S0S2dS12S1S1eVW;Vst;Vtmax;A3A1A1S12S1S24VW;Vst;Vtmax;A3A1A1A3").
Variables (s6 sd6 : wsub) (R6 : list sobj) (T6 : axst).
Hypothesis He6 : ltac2:(tb__ "0|1|
S0SdSbS15A1M0A1S58S1eVW;Vst;Vtmax;A3S3bVs6;A3ScG0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S7S57S1eVW;Vst;Vtmax;A3S3bVs6;VR6;S50S6S2S5S3dA4A5S8A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0S2S59Vs6;S3bS51S3cA1S1eVW;Vst;Vtmax;A3VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S7S49S11S19S12S1S1eVW;Vst;Vtmax;A3A1M0A1A1S16G0A1A3S8A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S7S49S11S19S12S1VT6;A1A1A1S16S1S1eVW;Vst;Vtmax;A3A1A1A3S8A3").
Hypothesis ENT6 : ltac2:(tb__ "0|0|
S0S7S3S54VT6;S16S1S1eVW;Vst;Vtmax;A3A1A1A2S20VW;Vst;Vtmax;A3Vsd6;A3S8A3").
Hypothesis SID6 : ltac2:(tb__ "0|0|
S0S7S3eVsd6;S34A2S8A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S5bS34S12S1S1eVW;Vst;Vtmax;A3A1A1A2").

Theorem spine_s6l : ltac2:(tb__ "0|2|
S30OF_;S44S40S10SbS36Q40A1A1M0S2fS45VW;Vst;A2S41R5A1S33Vsegs;R8S32R6A1A3S10G0S2eVsegs;RbS31Vsegs;S35VW;Vst;RaR9R8A5M1S20VW;Vst;Vtmax;A3R2R1A5R6A4FtpX;FrhoX;S10S2eVsegs;RbS31Vsegs;G1S1fVW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0xdb004] GW [C6l W st tmax] [E6m W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert6l.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (call_gen nW st (C6m W st tmax) T6 (C6b W st tmax) s6 R6 sd6 Pre_mszA Posts_mszA P_msz
                eq_refl (fun ok0 Jx r0 t0 Ho Hs => memsetZ_sumA ok0 Jx Ho Hs r0 t0) He6 Hchk6 HT6 FBC6 FBT6 ENT6 SID6 NXC6 eq_refl
                ok A Kc rho tp rhoX Q HUS HKc Hokf HC). }
    unfold C6m, upd. lazy zeta. eapply SPA_restate; [exact W6m | exact D6m | exact NX6m | constructor | constructor | exact Hw].
  - left. reflexivity.
Qed.
End B10bS.

Section B10cS.
Hypothesis Cert6b : ltac2:(tb__ "0|1|
S0S7S3fS43Ufa0S9S2cZ3c82cSaS2cA1A3S34S9S2S20VW;Vst;Vtmax;A3SaS2A1M0A3S9S2S27VW;Vst;Vtmax;A3G0A3A6S8A3").
Variable s7j : wsub.
Hypothesis ENT7j : ltac2:(tb__ "0|0|
S0S7S3S27VW;Vst;Vtmax;A3S21VW;Vst;Vtmax;A3Vs7j;A3S8A3").
Hypothesis SID7j : ltac2:(tb__ "0|0|
S0S7S3eVs7j;S34A2S8A3").
Theorem spine_s6b : ltac2:(tb__ "0|0|
S30OF_;S44S40S10SbS36Q40A1A1S2fS45VW;Vst;A2S41R5A1S33Vsegs;R8S32R6A1A3S10S2eVsegs;RaS31Vsegs;S35VW;Vst;R9R8R7A5S21VW;Vst;Vtmax;A3R1R6A5R5A4FrhoX;S10S2eVsegs;RbS31Vsegs;S35VW;Vst;RaR9R8A5S20VW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c82c] GW [C6b W st tmax] [E6j W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert6b.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s7j))].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E6j W st tmax) (C7 W st tmax) s7j rhoX tp w ENT7j SID7j); [|exact Hw].
    apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End B10cS.
End S7.
End SpineCallocS7.

(* [comment removed for export] *)
Module SpineCallocR7.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "entailsA"; "sym_runA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SAlu"; "ss_next"; "eval"; "SVar"; "ss_facts"; "swf"; "valuation"; "SPNot"; "holds"; "ss_lenient"; "SPBranch"; "SPUle"; "rw"; "SMd"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "list"; "nil"; "pair"; "prod"; "Some"; "option"; "andb"; "false"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "cP2"; "GR"; "vMU"; "HINT_map"; "cPa"; "cPb"; "req_e"; "vAU"; "vK"; "vNF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "of_nat"; "mul"; "sub"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SRL"; "BC_LTU"; "ALU_SRA"; "ALU_XOR"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "V_CLS"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocR7"; "F_mu0"; "F_hi"; "size_e_hi"; "size_e_lo"; "x19_e0"; "x19_e1"; "popfacts"; "total_e"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "cs_free_array"; "cs_allocated_user"; "cs_mapped_user"; "AA"; "class_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "entryR"; "ph0"; "gh_nf"; "ghosts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5"; "tab1_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "rigids"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws PrimCredit PrimCreditLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.PrimRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition size_e_hi : sv := ltac2:(tb__ "0|4|
SbS37SbS38SbS3cSbS39SeS40A1M0SaZ3fA1M1A3G1A3SbS3aSbS39SaZ200A1SbS3aSbS37G0SaN10A1A3SaZ1A1M2A3A3M3G2A3A3G3A3").
Definition size_e_lo : sv := ltac2:(tb__ "0|0|
SbS39SeS40A1SaZ5A1A3").
Definition tabS_okb : bool := ltac2:(tb__ "0|0|
S22S22S22S5eS40S45S51Z11UeA5S61S40S45A2A2S5eS40S46S51Z1U10A5A2S61S40S46A2A2").
Lemma tabS_ok : tabS_okb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Definition F_hi : sprop := ltac2:(tb__ "0|0|
S15S3bSaZ10A1SeS40A1A3").

Definition total_e : sv := ltac2:(tb__ "0|0|
SbS37S2dS18S3eSeS41A1S2cA3A3").
Definition x19_e0 : sv := ltac2:(tb__ "0|0|
SbS37SbS38SbS37S4aSaN1A1A3SaZfffffffffffc0000A1A3SaZ40000A1A3").
Definition x19_e1 : sv := ltac2:(tb__ "0|0|
SbS37SbS38SbS37S4aSbS3dS28SaZffffffffffffffffA1A3A3SaZfffffffffffc0000A1A3SaZ40000A1A3").
Definition F_mu0 : sprop := SPBranch BC_EQ vMU (SLit 0).

Definition popfacts (A : AA) (rb : valuation) : Prop := ltac2:(tb__ "0|1|
S4eQ40S17Vrb;PcA2A2S25S5fR1A1S25S60VA;R2A2S57S6S31S33S24S25S53R1A1A2A1S52R2A1A2S6S30S32S55R1A1Z40000A2S65R2A1M0A2S30G0Ze0000000A2A2A2Tcs;Tc;Tnv;").

Lemma entry_popfacts : ltac2:(tb__ "0|1|
S56S11S1cS4dQ40M0A1A1S62S1cS63A1S64S11S5aR7R6R5R4R3R2R1A7S31S5cR8R7A2S52S5fS4eG0S17R7PcA2A2A1A1A2S49R9R8A2F_;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE HNP. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & _ & (_ & _ & Hc0) & _).
  destruct HE as (_ & HA & _). unfold popfacts. cbn zeta. unfold gh_nf in HNP. split; [exact HNP|].
  pose proof (populate_room segs A rb tp0 md0 _ HA C1 Hc0 ltac:(unfold cst_of in HNP; lia)) as [R1 R2].
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize in *. unfold cst_of. split; [exact R1 | exact R2].
Qed.

Section VALS.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis PF : popfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S66VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S5dVA;Vrb;Vr;A3").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.

Lemma size_hi_val : ltac2:(tb__ "0|0|
S13Vr;S44A2S5S4dQ40A1SdVr;S45A2SdVr;SeS41A1A2A3F_;").
Proof.
  intros HF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _).
  destruct RG as (_ & E148 & _ & _ & _ & _ & _ & E158). fold nv c in E148, E158.
  unfold F_hi in HF. cbn [holds eval] in HF. unfold branch_taken, bv_ltu in HF. apply Z.ltb_lt in HF. unfold V_CLS in HF. rewrite E158 in HF. rewrite !u64_lit in HF by (clear -C1; lia).
  pose proof tabS_ok as T. unfold tabS_okb in T. apply andb_prop in T as [T _]. apply andb_prop in T as [T _]. apply andb_prop in T as [T1 T2].
  cbn [eval]. unfold V_SIZE. rewrite E148. exact (tab1_ok_sound V_CLS size_e_hi Size 17 14 r c T1 T2 E158 ltac:(clear -C1 HF; lia)).
Qed.
Lemma size_lo_val : ltac2:(tb__ "0|0|
S7S13Vr;S44A2A1S5S4dQ40A1SdVr;S46A2SdVr;SeS41A1A2A3F_;").
Proof.
  intros HF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _).
  destruct RG as (_ & E148 & _ & _ & _ & _ & _ & E158). fold nv c in E148, E158.
  unfold F_hi in HF. cbn [holds eval] in HF. unfold branch_taken, bv_ltu in HF. unfold V_CLS in HF. rewrite E158 in HF. rewrite !u64_lit in HF by (clear -C1; lia).
  assert (C16 : c <= 16) by (destruct (Z.ltb_spec 16 c) as [X|X]; [exfalso; apply HF; reflexivity | exact X]).
  pose proof tabS_ok as T. unfold tabS_okb in T. apply andb_prop in T as [T T4]. apply andb_prop in T as [T T3].
  cbn [eval]. unfold V_SIZE. rewrite E148. exact (tab1_ok_sound V_CLS size_e_lo Size 1 16 r c T3 T4 E158 ltac:(clear -C1 C16; lia)).
Qed.

Lemma pop_nums : ltac2:(tb__ "0|4|
S51Vc;A1S25S52Vc;A1S25S33S24S25S53Vcs;A1A2A1S25S54Vcs;A1S25S55Vcs;A1S25S6S6S30Z20R5A2S30R5Z10000M0A2A2S6S6S30Z1R4A2S30R4Z8A2A2S6S6S30Z0M1R3A2S31R3R4A2A2S6S6S30G1R2A2S30R2R1A2A2S6S30R1Zdffc0000A2S6S31R1S32R2R5A2A2S6S6S31G1S34R5S35R4R3A2A2M2A2S30G2G0A2A2S6S31R1S32R2G2A2M3A2S30G3S32R1G0A2A2A2A2A2A2A2A2A2A2Tmu;Tau;Tnf;Tk;TS;").
Proof.
  intros S k nf au mu.
  unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. fold S k nf au mu in CF.
  destruct CF as ((_ & _ & S1 & _) & (K1 & _ & K3) & (_ & AU0 & _ & _ & TI0) & _).
  destruct PF as (NP & RM & RC). fold nv c cs in NP, RM, RC. fold k nf mu in NP, RM.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. fold nf in NF0.
  clear -S1 K1 K3 AU0 TI0 NP RM RC NF0.
  assert (B1 : 0 < S * (k - nf)) by nia. assert (B2 : S * (k - nf) <= S * k) by nia. assert (B3 : S <= S * (k - nf)) by nia. lia.
Qed.

Lemma total_val : ltac2:(tb__ "0|0|
S5S25S4eQ40SdVr;S4aA2A2S32S54Vcs;A1S34S51Vc;A1S35S52Vc;A1S33S24S25S53Vcs;A1A2A1A2A2A2A3").
Proof.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct RG as (_ & E148 & _). fold nv c in E148.
  destruct GH as (_ & Q221 & _ & Q223 & _ & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q227.
  unfold total_e, req_e, vAU, vK, vNF, V_SIZE. cbn [eval]. rewrite add_val, mul_val, sub_val, E148, Q221, Q223, Q227.
  rewrite !u64_lit by (clear -N1 N2 N3 N4 N5; lia).
  rewrite (Z.mod_small (kchunks c - _)) by (clear -N2 N3; lia). rewrite (Z.mod_small (Size c * _)) by (clear -N7; lia).
  rewrite Z.mod_small by (clear -N4 N5 N7; lia). reflexivity.
Qed.

Lemma F_pop_hold : Forall (holds r) F_pop.
Proof.
  pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & Q221 & _ & Q223 & Q224 & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q224, Q227.
  unfold F_pop. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. unfold branch_taken, bv_ltu, vNF, vK. cbn [eval]. rewrite Q221, Q227. rewrite !u64_lit by (clear -N2 N3; lia). apply Z.ltb_lt. exact (proj2 N3).
  - unfold HINT_map. cbn [holds]. unfold branch_taken, bv_ltu. fold total_e. rewrite TV. unfold vMU. cbn [eval]. rewrite Q224. rewrite u64_lit by (clear -N4 N5; lia).
    apply Z.ltb_lt. exact (proj1 N8).
  - cbn [holds]. unfold vMU. cbn [eval]. rewrite Q224. rewrite !u64_lit by (clear -N4 N5; lia). exact N5.
Qed.

Lemma x19_val1 : ltac2:(tb__ "0|0|
S5S4dQ40A1SdVr;S48A2SdVr;SaZ40000A1A2A3").
Proof.
  pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & _ & _ & _ & Q224 & _). fold nv c cs in Q224.
  set (tot := cs_allocated_user cs + Size c * (kchunks c - Z.of_nat (length (cs_free_array cs)))) in *.
  unfold x19_e1. cbn [eval]. apply bv_eq. rewrite add_val, and_val, add_val, xor_val. fold total_e. rewrite TV. unfold vMU. cbn [eval]. rewrite Q224.
  rewrite !u64_lit by (clear -N4 N5; lia).
  rewrite lxor_ones64 by (clear -N4 N5; lia).
  replace ((tot + (18446744073709551615 - cs_mapped_user cs)) mod 2 ^ 64) with (tot - cs_mapped_user cs - 1).
  2: { apply (Z.mod_unique_pos _ _ 1); clear -N4 N5 N8; lia. }
  rewrite land_m18_small by (clear -N8; lia). rewrite Z.mod_small by (clear; lia). reflexivity.
Qed.
Lemma x19_val0 : ltac2:(tb__ "0|1|
S13Vr;S43A2S6S5S4dQ40A1M0SdVr;S47A2SdVr;SaZ40000A1A2A3S5G0SdVr;SaZ0A1A2SdVr;S28A2A3A2F_;").
Proof.
  intros HF. pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & _ & _ & _ & Q224 & _). fold nv c cs in Q224.
  unfold F_mu0 in HF. cbn [holds] in HF. unfold branch_taken, bv_eqb, vMU in HF. cbn [eval] in HF. rewrite Q224 in HF. rewrite !u64_lit in HF by (clear -N4 N5; lia). apply Z.eqb_eq in HF.
  set (tot := cs_allocated_user cs + Size c * (kchunks c - Z.of_nat (length (cs_free_array cs)))) in *.
  split.
  - unfold x19_e0. cbn [eval]. apply bv_eq. rewrite add_val, and_val, add_val. fold total_e. rewrite TV.
    replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615 by reflexivity. rewrite !u64_lit by (clear; lia).
    replace ((tot + 18446744073709551615) mod 2 ^ 64) with (tot - 1).
    2: { apply (Z.mod_unique_pos _ _ 1); clear -N4 N8 HF; lia. }
    rewrite land_m18_small by (clear -N4 N8 HF; lia). rewrite Z.mod_small by (clear; lia). reflexivity.
  - unfold vMU. cbn [eval]. rewrite Q224, HF. reflexivity.
Qed.
End VALS.

Section POP1.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S5aVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).

Variable F : nat.
Variables (E3 : axst) (LP : axst) (La Lb La0 La1 Lb0 Lb1 : leafA) (CP2C : axst) (sa0 sa1 sb0 sb1 : wsub).
Let FR : list sprop := factsR E3.
Let CPA : axst := ltac2:(tb__ "0|0|
S2aVFR;S1VLa;A1A2").
Let CPB : axst := ltac2:(tb__ "0|0|
S2bVFR;S1VLb;A1A2").
Hypothesis FP_in : ltac2:(tb__ "0|0|
S36S9S15S3bS2fS2eA3SfS0VLP;A1A1A3").
Hypothesis R_p1 : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z41754S1bS25Z41794S1dS25A1A3A3VLP;S1aA5S20G0S1bS2VLa;S1bS2VLb;S1dS2A1A3A3A2A3").
Hypothesis LN_p : ltac2:(tb__ "0|0|
S5S19S14S0VLP;A1A1S23A3").
Hypothesis NX_p : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VLP;A1A1A2S1aA3").
Hypothesis Fa_in : ltac2:(tb__ "0|0|
S36S9S44SfS0S1VLa;A1A1A1A3").
Hypothesis Fb_in : ltac2:(tb__ "0|0|
S36S9S12S44A1SfS0S1VLb;A1A1A1A3").
Hypothesis W_pa : ltac2:(tb__ "0|0|
S5S19S10S0VCPA;A1A1S1aA3").
Hypothesis D_pa : ltac2:(tb__ "0|4|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa;A1A1S0VCPA;A1A2S20G3S1eG1G2S1bG0S1eS8S8S45SeS41A1A4S1dG0A1A3S1bS9S29S1bS9S16S28SaZdffc0000A1A2S1dS9A1A3A3A4A2A3").
Hypothesis NX_pa : ltac2:(tb__ "0|0|
S5S19S4bScS0VCPA;A1A1ScS0S1VLa;A1A1A1A2S1aA3").
Hypothesis W_pb : ltac2:(tb__ "0|0|
S5S19S10S0VCPB;A1A1S1aA3").
Hypothesis D_pb : ltac2:(tb__ "0|4|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb;A1A1S0VCPB;A1A2S20G3S1eG1G2S1bG0S1eS8S8S46SeS41A1A4S1dG0A1A3S1bS9S29S1bS9S16S28SaZdffc0000A1A2S1dS9A1A3A3A4A2A3").
Hypothesis NX_pb : ltac2:(tb__ "0|0|
S5S19S4bScS0VCPB;A1A1ScS0S1VLb;A1A1A1A2S1aA3").
Hypothesis R_p2a : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z417c4S1dS25A1A3VCPA;S1aA5S20G0S1bS2VLa0;S1bS2VLa1;S1dS2A1A3A3A2A3").
Hypothesis LN_pa : ltac2:(tb__ "0|0|
S5S19S14S0VCPA;A1A1S23A3").
Hypothesis NXr_pa : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VCPA;A1A1A2S1aA3").
Hypothesis R_p2b : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z417c4S1dS25A1A3VCPB;S1aA5S20G0S1bS2VLb0;S1bS2VLb1;S1dS2A1A3A3A2A3").
Hypothesis LN_pb : ltac2:(tb__ "0|0|
S5S19S14S0VCPB;A1A1S23A3").
Hypothesis NXr_pb : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VCPB;A1A1A2S1aA3").

Section LEAF.
Variables (L : leafA) (s : wsub) (mu0 : bool).
Let C2 : axst := ltac2:(tb__ "0|0|
S26VFR;S1VL;A1A2").
Hypothesis F_in : ltac2:(tb__ "0|0|
S36S9S19S9Lmu0;Vmu0;S43S12S43A1X19x2SfS0S1VL;A1A1A1A3").
Hypothesis W_2 : ltac2:(tb__ "0|0|
S5S19S10S0VC2;A1A1S1aA3").
Hypothesis D_2 : ltac2:(tb__ "0|6|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VL;A1A1S0VC2;A1A2S20G3S1eG1G2S19G1Lmu0;Vmu0;S1bG0S1eS8S8S47SaZ40000A1M4A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1M5A3A3S1bG0S1eS8S8S48G4A4G5A3X19x2S1dS9A1A4A2A3").
Hypothesis NX_2 : ltac2:(tb__ "0|0|
S5S19S4bScS0VC2;A1A1ScS0S1VL;A1A1A1A2S1aA3").
Hypothesis ENT_2 : ltac2:(tb__ "0|0|
S5S19S3VC2;VCP2C;Vs;A3S1aA3").
Hypothesis SID_2 : ltac2:(tb__ "0|0|
S5S19S4fVs;S27A2S1aA3").

Lemma join_leaf : ltac2:(tb__ "0|1|
S11S1cS4dQ40A1A1S58S49VA;Vrb;A2S11VTR;S50S42S59VA;VKc;Vrb;Vtp0;Vmd0;S5bA6M0VCP2C;R1R4A5R3A2Fr';VTR;S50S42G0S1VL;A1R5R4A5R3A2F_;F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q PF HC.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state L) (ax_S C2) _ _ ph0 r tp Q W_2 D_2 NX_2).
  { intros tr md (HFz & HGh & _) HF. split; [|constructor].
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    pose proof (proj1 (Forall_forall _ _) HF _ F_in) as HB.
    unfold diffs_ok. destruct mu0.
    - destruct (x19_val0 A rb r CF PF RG HGh HB) as [X1 X2]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; assumption.
    - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. exact (x19_val1 A rb r CF PF RG HGh). }
  change (ax_setS (la_state L) (ax_S C2)) with C2.
  apply (tr_pre Kc TR KIT (SPA segs (JRp ph0) CP2C (rho_sub r s) tp)); [|exact (HC _)].
  intros w Hw. apply (SPA_entails_J (JRp ph0) (JRp ph0) C2 CP2C s r tp w ENT_2); [|exact Hw].
  intros HJ. eapply (JR_stable A Kc rb tp0 md0 ph0 GR HKc ltac:(lia)); [exact (rho_sub_agree s GR r SID_2) | apply mat_equiv_refl | exact HJ].
Qed.
End LEAF.

Hypothesis Fa0_in : ltac2:(tb__ "0|0|
S36S9S43SfS0S1VLa0;A1A1A1A3").
Hypothesis Fa1_in : ltac2:(tb__ "0|0|
S36S9S12S43A1SfS0S1VLa1;A1A1A1A3").
Hypothesis Fb0_in : ltac2:(tb__ "0|0|
S36S9S43SfS0S1VLb0;A1A1A1A3").
Hypothesis Fb1_in : ltac2:(tb__ "0|0|
S36S9S12S43A1SfS0S1VLb1;A1A1A1A3").
Hypothesis W_a0 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLa0;A1A2A1A1S1aA3").
Hypothesis W_a1 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLa1;A1A2A1A1S1aA3").
Hypothesis W_b0 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLb0;A1A2A1A1S1aA3").
Hypothesis W_b1 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLb1;A1A2A1A1S1aA3").
Hypothesis D_a0 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa0;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S47SaZ40000A1A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1A3A3S1dS9A1A4A2A3").
Hypothesis D_a1 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa1;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S48SaZ40000A1A4S1dG0A1A3S1dS9A1A4A2A3").
Hypothesis D_b0 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb0;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S47SaZ40000A1A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1A3A3S1dS9A1A4A2A3").
Hypothesis D_b1 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb1;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S48SaZ40000A1A4S1dG0A1A3S1dS9A1A4A2A3").
Hypothesis NX_a0 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLa0;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_a1 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLa1;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_b0 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLb0;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_b1 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLb1;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis ENT_a0 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLa0;A1A2VCP2C;Vsa0;A3S1aA3").
Hypothesis ENT_a1 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLa1;A1A2VCP2C;Vsa1;A3S1aA3").
Hypothesis ENT_b0 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLb0;A1A2VCP2C;Vsb0;A3S1aA3").
Hypothesis ENT_b1 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLb1;A1A2VCP2C;Vsb1;A3S1aA3").
Hypothesis SID_a0 : ltac2:(tb__ "0|0|
S5S19S4fVsa0;S27A2S1aA3").
Hypothesis SID_a1 : ltac2:(tb__ "0|0|
S5S19S4fVsa1;S27A2S1aA3").
Hypothesis SID_b0 : ltac2:(tb__ "0|0|
S5S19S4fVsb0;S27A2S1aA3").
Hypothesis SID_b1 : ltac2:(tb__ "0|0|
S5S19S4fVsb1;S27A2S1aA3").

Theorem populate_head : ltac2:(tb__ "0|1|
S11S1cS4dQ40A1A1S58S49VA;Vrb;A2S11VTR;S50S42S59VA;VKc;Vrb;Vtp0;Vmd0;S5bA6M0VCP2C;R1R4A5R3A2Fr';F_;VTR;S50S42G0VLP;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.

  apply (tr_facts Kc TR KIT). intros HF0. pose proof (proj1 (Forall_forall _ _) HF0 _ FP_in) as BF. cbn [holds] in BF.
  apply (tr_pure Kc TR KIT (popfacts A rb)).
  { intros w [_ (HFz & HGh & _)]. apply (entry_popfacts _ _ _ _ _ _ _ HE).
    destruct HGh as (_ & Q221 & _ & _ & _ & _ & _ & Q227 & _).
    unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _).
    unfold branch_taken, bv_ltu, vNF, vK in BF. cbn [eval] in BF. rewrite Q221, Q227 in BF. unfold gh_nf in *.
    rewrite !u64_lit in BF by lia. apply Z.ltb_lt in BF. exact BF. }
  intros PF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41754; 0x41794] LP [La; Lb] ph0 r tp Q R_p1 LN_p NX_p).
  intros L r1 [<-|[<-|[]]] _.
  -
    apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state La) (ax_S CPA) _ _ ph0 r1 tp Q W_pa D_pa NX_pa).
    { intros tr md (HFz & HGh & _) HF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
      split.
      - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        exact (size_hi_val A rb r1 CF RG (proj1 (Forall_forall _ _) HF _ Fa_in)).
      - pose proof (F_pop_hold A rb r1 CF PF RG HGh) as FPH. unfold F_pop in FPH. inversion FPH as [|? ? _ FPH']; subst. exact FPH'. }
    change (ax_setS (la_state La) (ax_S CPA)) with CPA.
    apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x417c4] CPA [La0; La1] ph0 r1 tp Q R_p2a LN_pa NXr_pa).
    intros L r2 [<-|[<-|[]]] _.
    + exact (join_leaf La0 sa0 true Fa0_in W_a0 D_a0 NX_a0 ENT_a0 SID_a0 r2 tp Q PF (HC PF)).
    + exact (join_leaf La1 sa1 false Fa1_in W_a1 D_a1 NX_a1 ENT_a1 SID_a1 r2 tp Q PF (HC PF)).
  -
    apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state Lb) (ax_S CPB) _ _ ph0 r1 tp Q W_pb D_pb NX_pb).
    { intros tr md (HFz & HGh & _) HF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
      split.
      - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        exact (size_lo_val A rb r1 CF RG (proj1 (Forall_forall _ _) HF _ Fb_in)).
      - pose proof (F_pop_hold A rb r1 CF PF RG HGh) as FPH. unfold F_pop in FPH. inversion FPH as [|? ? _ FPH']; subst. exact FPH'. }
    change (ax_setS (la_state Lb) (ax_S CPB)) with CPB.
    apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x417c4] CPB [Lb0; Lb1] ph0 r1 tp Q R_p2b LN_pb NXr_pb).
    intros L r2 [<-|[<-|[]]] _.
    + exact (join_leaf Lb0 sb0 true Fb0_in W_b0 D_b0 NX_b0 ENT_b0 SID_b0 r2 tp Q PF (HC PF)).
    + exact (join_leaf Lb1 sb1 false Fb1_in W_b1 D_b1 NX_b1 ENT_b1 SID_b1 r2 tp Q PF (HC PF)).
Qed.
End POP1.
End SpineCallocR7.

(* [comment removed for export] *)
Module RebuildRP.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "mul"; "div"; "pow"; "sub"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "AA"; "aa_cls"; "class_state"; "cs_empty"; "sec_chunk"; "cs_allocated_user"; "aa_live"; "aa_sec"; "aa_q_global"; "aa_q_thread"; "ag_spacebeg"; "ag_thread"; "ageom"; "qbatch"; "sc_map_beg"; "sc_map_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "nthZ"; "q_foot"; "QG"; "class_repr"; "live_ids"; "quarantine_repr"; "geom_ok"; "live_block_repr"; "slot_zone"; "@Stdlib.Lists.List"; "In"; "NoDup"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "Sh"; "kUserSpaceSize"; "rz"; "@Corelib.Init.Datatypes"; "list"; "option"; "app"; "nat"; "pair"; "Some"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "q_ids"; "qall"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3"; "qslot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "czone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "cls_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "q_pure"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws RefillModel RebuildRZ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma NoDup_app_in : ltac2:(tb__ "0|1|
S31S0A1M0G0S0S2aS0S33S0R3R2A3A2S29S0R2R4A3S29S0R3R4A3SeF_;F_;F_;Fx;Fl2;Fl1;").
Proof.
  induction l1 as [|a l1 IH]; intros l2 x ND H1 H2; [destruct H1|]. cbn [app] in ND. inversion ND as [|? ? Ha ND']; subst.
  destruct H1 as [->|H1]; [apply Ha; apply in_or_app; right; exact H2 | exact (IH l2 x ND' H1 H2)].
Qed.

Lemma id16_of : ltac2:(tb__ "0|2|
S0S0S3Z0M0R1A2SaS0S4R2Z10M1A2G0A3SaS0S4R4R3A2G0A3SaS0S5G1S6R5G1A2A2R5A3F_;F_;F_;FS;Fo;").
Proof.
  intros o S HS H16 HoS.
  destruct (proj1 (Z.mod_divide o S ltac:(lia)) HoS) as [q Hq]. destruct (proj1 (Z.mod_divide S 16 ltac:(lia)) H16) as [r Hr].
  subst o. rewrite Hr. replace (q * (r * 16)) with (q * r * 16) by ring. rewrite Z.div_mul by lia. ring.
Qed.

Lemma valid_of_off : ltac2:(tb__ "0|4|
S0S0S0S3Z0M0R2A2SaS0S4R3Z10M1A2G0A3S1G0R5A2SaS0S4R6R5A2G0A3S1S2R7R6A2R5A2S9S1G0S6R8G1A2M2A2S9SaS0S4S5G1G2A2M3R7A2G0A3S1S2G3R7A2R6A2A2A2F_;F_;F_;F_;F_;Fau;FS;Fo;").
Proof.
  intros o S au HS H16 Ho HoS Hau. rewrite (id16_of o S HS H16 HoS). split; [apply Z.div_pos; lia|]. split; [exact HoS | exact Hau].
Qed.

Lemma live_ids_valid : ltac2:(tb__ "0|3|
S2cS10S0S0S9S1Z1R2A2S1R2Z1eA2A2S23R5SfR4A1R4R3S20S12S11R4A1R3S13A4A5S29S0R3S24SfR5A1R5R4A3A3S9S1Z0M0R4A2S9SaS0S4S5Z10R4A2M1S2dR5A1M2A2G0A3S1S2G1G2A2S15S20S12S11R6A1R5S13A4A1A2A2A2F_;F_;F_;Fx;Fc;FA;Fm;").
Proof.
  intros m A c x Hc P4 Hx. destruct (Size_facts c Hc) as (SZ & SM).
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _).
  unfold live_ids in Hx. apply in_map_iff in Hx as ([b n] & <- & Hin).

  apply (proj2 (list_elem_of_In _ _)) in Hin. apply (proj1 (list_basics.list.list_elem_of_filter _ _ _)) in Hin as [Hf Hin].
  apply (proj1 (list_elem_of_In _ _)) in Hin. cbn [fst snd] in *.
  destruct (is_primary n) eqn:Hp; [|cbn in Hf; destruct Hf].
  destruct (Z.eqb_spec (ClassID (needed n)) c) as [Hcl|Hcl]; [|cbn in Hf; destruct Hf].
  destruct (LV b n Hin Hp Hcl) as (V1 & V2 & V3).
  apply valid_of_off; [lia | exact SM | lia | exact V2 | exact V3].
Qed.

Lemma q_ids_valid : ltac2:(tb__ "0|3|
S10S0S0S9S1Z1R2A2S1R2Z1eA2A2S3fR4A1S29S0R3S38SfR5A1S39R5A1R4A3A3S9S1Z0M0R4A2S9SaS0S4S5Z10R4A2M1S2dR5A1M2A2G0A3S1S2G1G2A2S15S20S12S11R6A1R5S13A4A1A2A2A2F_;F_;F_;Fx;Fc;FA;").
Proof.
  intros A c x Hc [HBP _] Hx. destruct (Size_facts c Hc) as (SZ & SM).
  unfold q_ids in Hx. apply in_app_or in Hx as [Hx|Hx].
  - apply in_map_iff in Hx as (it & <- & Hin). apply filter_In in Hin as [Hin Hf]. apply andb_prop in Hf as [Hp Hcl]. apply Z.eqb_eq in Hcl.
    unfold qitems in Hin. apply in_flat_map in Hin as (b & Hb & Hit).
    pose proof (proj1 (Forall_forall _ _) HBP b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (_ & _ & I3 & _).
    specialize (I3 Hp). cbv zeta in I3. unfold it_cls in Hcl. rewrite Hcl in I3. destruct I3 as (I3a & I3b & I3c).
    unfold it_id, it_ab, it_cls, ptr_to_compact, kCompactPtrScale. rewrite Hcl. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
    unfold SegQ_wf2.cls_of in I3c.
    apply valid_of_off; [lia | exact SM | lia | exact I3b | exact I3c].
  - destruct (Z.eqb_spec c 24) as [->|Hne]; [|destruct Hx].
    apply in_map_iff in Hx as (b & <- & Hb).
    pose proof (proj1 (Forall_forall _ _) HBP b Hb) as (_ & _ & (y & E & Y0 & YM & Y1) & _).
    unfold qb_id, ptr_to_compact, kCompactPtrScale. rewrite E. replace (region_beg (ag_spacebeg (aa_geom A)) 24 + 16 * y - region_beg (ag_spacebeg (aa_geom A)) 24) with (y * 2 ^ 4) by lia.
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
    unfold SegQ_wf2.cls_of, kQuarantineBatchSize in Y1. change (Size 24) with 8192.
    split; [exact Y0|]. split; [|exact Y1].
    destruct (proj1 (Z.mod_divide y 512 ltac:(lia)) YM) as [k Hk]. subst y. replace (16 * (k * 512)) with (k * 8192) by lia. apply Z_mod_mult.
Qed.

Lemma entry_cls_pure : ltac2:(tb__ "0|1|
S2cS10S0S9S1Z1R1A2S1R1Z1eA2A2S26SfR3A1A1S23R5SfR4A1R4R3S20S12S11R4A1R3S13A4A5S25R6R5A2S3dR5S20S12S11R6A1R5S13A4S33S0S24SfR6A1M0R6R5A3S38G0S39R6A1R5A3A3A3F_;F_;F_;F_;Fc;FA;Fm;").
Proof.
  intros m A c Hc HG P4 HQ. pose proof (fun x => live_ids_valid m A c x Hc P4) as LVV. pose proof (q_ids_valid A c) as QVV.
  destruct (quarantine_repr_pure m A HG HQ) as [HQP _].
  set (cs := nthZ (aa_cls A) c cs_empty) in *. unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & N7 & _ & _ & _ & ND & _ & _ & _ & TI10 & CV10 & MC10 & FC10).
  unfold cls_pure. split; [exact N1|]. split; [exact N2|]. split; [exact N4|]. split; [exact N5|].
  split; [pose proof (Zle_0_nat (length (cs_free_array cs))); lia|]. split; [lia|].
  split.
  { intros x Hx. rewrite app_assoc in Hx. apply in_app_or in Hx as [Hx|Hx].
    - destruct (N7 x Hx) as (X1 & X2 & X3). unfold kCompactPtrScale in X2, X3. rewrite Z.shiftl_mul_pow2 in X2, X3 by lia. change (2 ^ 4) with 16 in X2, X3.
      replace (16 * x) with (x * 16) by lia. split; [exact X1|]. split; [exact X2 | exact X3].
    - apply in_app_or in Hx as [Hx|Hx]; [exact (LVV x Hx) | exact (QVV x Hc HQP Hx)]. }
  split; [exact (proj1 (NoDup_ListNoDup _) ND)|]. split; [exact TI10|].
  split; [unfold slots in CV10; rewrite CV10, length_app; f_equal; lia|].
  exact (conj MC10 FC10).
Qed.

Lemma live_block_repr_agree : ltac2:(tb__ "0|4|
S2cS2cS10S10SaS31S37S0S0A2M0A1S16R1A1S16R2A1A3S0S0S0S29G0S35S0S0R3R2A4S16R6A1M1A3ScS9S1S8R4S30R3A1A2R2A2S3R2S2R4R3A2A2A2S9S1S2eR4A1M2R2A2S3R2S2G2S6S2R3Z7A2Z8A2A2A2A2A2SaS32S3aQ8A1A1R9R3A1RaR3A1A3F_;F_;Fz;Fn;Fb;S0S0S29G0S35S0S0R2R1A4G1A3S1Z1R2A2F_;Fn;Fb;S27R7R5A2M3G3F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EL AG HN HL b n Hin. rewrite EL in Hin. destruct (HL b n Hin) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
  pose proof (HN b n Hin) as Hn1. pose proof (rz_bound n) as RZ.
  assert (AGb : forall z, b - rz n <= z < b + n -> m' z = m z) by (intros z Hz; apply (AG b n z Hin); left; exact Hz).
  assert (AGs : forall z, Sh b <= z < Sh b + (n + 7) / 8 -> m' z = m z) by (intros z Hz; apply (AG b n z Hin); right; exact Hz).
  split; [rewrite AGb by lia; exact B1|].
  split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply AGb; lia|].
  split; [eapply cell_ok_agree; [|exact B3]; cbn [c_addr c_w]; intros k Hk; apply AGb; lia|].
  split; [split|split].
  - intros g Hg. rewrite AGs by lia. exact (B4 g Hg).
  - intros Hm. rewrite AGs by lia. exact (B5 Hm).
  - apply (alloc_magic_ok_agree m m' b n); [|lia|exact B6]. intros z Hz. apply AGb. lia.
  - destruct B7 as (t & Ht & Hm4). exists t. split; [|exact Hm4]. rewrite AGb by lia. exact Ht.
Qed.

Lemma quarantine_repr_agreeR : ltac2:(tb__ "0|6|
S2cS2cS10S10SaS1cSfR1A1SfR2A1A3SaS31S14A1S17R2A1S17R3A1A3SaS31S1dA1M0S19R3A1S19R4A1A3SaG0S18R4A1S18R5A1A3S0S1S15S20S12S11R7A1R1S13A4A1S15S20S12S11R6A1R1S13A4A1A2Fc;S0S21R8R1A2SaS32S3aQ8A1A1M1RaR2A1RbR2A1M2A3F_;Fz;S0S9S1S2S1bSfR9A1A1M3Z50A2R1A2S3R1S2G3Z70A2A2A2SaG1G2RcR2A1M4A3F_;Fz;S0S9S1S2S22Z40A2R1A2S3R1S2S22Zc0A2A2A2SaG1G4RdR2A1A3F_;Fz;S25RcRaA2M5G5F_;F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' EG ES ET EGq EAU AG AGT AGI (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  unfold quarantine_repr. rewrite EG, ET, EGq.
  assert (FQ : forall qb z, In qb (aa_q_thread A ++ aa_q_global A) ->
            (qb_addr qb <= z < qb_addr qb + kQuarantineBatchSize)
            \/ Exists (fun it : Z * Z => (fst it - rz (snd it) <= z < fst it) \/ (Sh (fst it) <= z < Sh (fst it) + (snd it + 7) / 8)) (qb_items qb) -> m' z = m z).
  { intros qb z Hqb Hz. apply AG. unfold q_foot. apply Exists_exists. exists qb. split; [exact Hqb | exact Hz]. }
  split.
  { apply Forall_forall. intros qb Hqb. pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
    unfold batch_repr. rewrite EG. unfold kQuarantineBatchSize in *.
    split; [exact B0|]. split; [eapply cell_ok_agree; [|exact B1]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
    split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
    split; [exact B3|]. split; [exact B4|].
    split; [eapply present_agree; [|exact B5]; intros z Hz; apply (FQ qb); [exact Hqb | left; lia]|].
    split.
    - intros i it Hi. destruct (B6 i it Hi) as [I1 I2]. pose proof (nth_error_Some_lt _ _ _ Hi) as L. pose proof (nth_error_In _ _ Hi) as Hin.
      unfold kQuarantineBatchCount in B3.
      split; [eapply cell_ok_agree; [|exact I1]; cbn [c_addr c_w]; intros k Hk; apply (FQ qb); [exact Hqb | left; lia]|].
      pose proof (rz_bound (snd it)) as RZi.
      unfold q_item_ok in I2 |- *. cbn zeta in I2 |- *. rewrite EG, ES.
      destruct I2 as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11).
      assert (AGi : forall z, fst it - rz (snd it) <= z < fst it -> m' z = m z).
      { intros z Hz. apply (FQ qb); [exact Hqb|]. right. apply Exists_exists. exists it. split; [exact Hin | left; exact Hz]. }
      split; [exact J1|]. split; [exact J2|].
      split; [rewrite AGi by lia; exact J3|].
      split; [eapply present_agree; [|exact J4]; intros z Hz; apply AGi; lia|].
      split; [eapply cell_ok_agree; [|exact J5]; cbn [c_addr c_w]; intros k Hk; apply AGi; lia|].
      split; [eapply cell_ok_agree; [|exact J6]; cbn [c_addr c_w]; intros k Hk; apply AGi; lia|].
      split; [eapply present_agree; [|exact J7]; intros z Hz; apply AGi; lia|].
      split; [apply (alloc_magic_ok_agree m m'); [exact AGi | lia | exact J8]|].
      split; [intros Hp; destruct (J9 Hp) as (K1 & K2 & K3); split; [exact K1|]; split; [exact K2|]; pose proof (EAU (ClassID (needed (snd it)))); lia|].
      split; [exact J10|].
      assert (0 <= (snd it + 7) / 8) by (apply Z.div_pos; lia).
      eapply present_agree; [|exact J11]. intros z Hz. apply (FQ qb); [exact Hqb|]. right. apply Exists_exists. exists it. split; [exact Hin | right; lia].
    - destruct B7 as (x & E1 & E2 & E3 & E4). exists x. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. pose proof (EAU 24). lia. }
  assert (HB : forall b z, In b (aa_q_thread A ++ aa_q_global A) -> qb_addr b <= z < qb_addr b + 8 -> m' z = m z).
  { intros b z Hb Hz. apply (FQ b); [exact Hb | left; unfold kQuarantineBatchSize; lia]. }
  split; [apply (qlinks_agree m m'); [intros b z Hb Hz; apply (HB b); [apply in_or_app; left; exact Hb | exact Hz] | exact Q2]|].
  split; [apply (qlinks_agree m m'); [intros b z Hb Hz; apply (HB b); [apply in_or_app; right; exact Hb | exact Hz] | exact Q3]|].
  split; [apply (qhdr_repr_agree m m'); [intros z Hz; apply AGT; lia | exact Q4]|].
  split; [apply (qhdr_repr_agree m m'); [intros z Hz; apply AGI; unfold QG in *; lia | exact Q5]|].
  split; [eapply cell_ok_agree; [|exact Q6]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold QG; lia|].
  split; [eapply cell_ok_agree; [|exact Q7]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold QG; lia|].
  split; [exact Q8 | exact Q9].
Qed.

Section QSlot.
Variables (A : AA) (mq : bview).
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HI3 : inv3 A.
Hypothesis HQP : q_pure A.
Hypothesis HSR : secondary_repr mq A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S0S9S1Z1R1A2S1R1Z1eA2A2S9S1Z0S15S3eVA;R2A2A1M0A2S1G0S2fA2A2F_;Fc;").

Lemma qfoot_cases : ltac2:(tb__ "0|2|
S0S21VA;R1A2ScSbS0S0SbS0S0S9S3bVA;R2R1A3S3cS1aSfVA;A1A1R2R1S2dR2A1R4A5A2Lo';A2Lc';A2SbS34S34SbS14S14S9SaS32S14A1S2bS14S17VA;A1R2A3S36S14R1A2A3ScS9S1S1eR1A1M0R4A2S3R4S2G0S1fR1A1A2M1A2A2S9S1S2eG0A1R4A2S3R4S2eG1A1A2A2A2A2Lch;A2Li;A2A2F_;Fz;").
Proof.
  intros z Hz. pose proof HI3 as (H3 & _).
  unfold q_foot in Hz. fold (qall A) in Hz.
  apply Exists_exists in Hz as (b & Hb & Hz).
  assert (PRIM : qzone A z -> exists c' o', qslot A c' o' /\ czone (ag_spacebeg (aa_geom A)) c' o' (Size c') z).
  { intros QZ. exact (qzone_czone A HG H3 HQP HAU z QZ). }
  destruct Hz as [Hz|Hz].
  - left. apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | left; exact Hz].
  - apply Exists_exists in Hz as (it & Hit & Hz). destruct (is_primary (snd it)) eqn:EP.
    + left. apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | right]. apply Exists_exists. exists it. split; [exact Hit|]. split; [exact EP | exact Hz].
    + right. destruct HQP as [HQ1 _]. pose proof (proj1 (Forall_forall _ _) HQ1 b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
      destruct (IP4 EP) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [i Hi]. exists i, ch. split; [exact Hi|].
      destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      pose proof (rz_sec (snd it) IP2 EP) as RZ. pose proof (round_up_ge8 (snd it)) as R8. unfold PG in *.
      destruct Hz as [Hz|Hz]; [left; clear -Hz RZ Eu Esz D8 R8 IP2; lia | right].
      assert (B8 : fst it mod 8 = 0).
      { destruct (proj1 (Z.mod_divide (sc_map_beg ch) 4096 ltac:(lia)) D6) as [k0 Hk0]. apply Z.mod_divide; [lia|]. exists (k0 * 512 + 768). lia. }
      pose proof (Sh_SB (fst it) (8 * ((snd it + 7) / 8)) B8) as E8. rewrite (Z.mul_comm 8), Z.div_mul in E8 by lia.
      pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)) as MB.
      pose proof (Geometry.Sh_mono (sc_map_beg ch) (fst it) ltac:(clear -Eu; lia)) as M1.
      pose proof (Geometry.Sh_mono (fst it + (snd it + 7) / 8 * 8) (sc_map_beg ch + sc_map_size ch) ltac:(clear -Eu Esz D8 R8 DM MB; lia)) as M2.
      clear -Hz E8 M1 M2. lia.
Qed.

Lemma qfoot_slot_out : ltac2:(tb__ "0|4|
S0S0S0S9S1Z1R3A2S1R3Z1eA2A2S1Z0M0R3A2SaS0S4S5Z10M1R4A2S2dR5A1A2G0A3S1S2S5G1R5A2S2dR6A1A2S8S7Z2M2Z20A2S7G2Z1dA2A2A2SdS29S0R6S38SfVA;A1M3S39VA;A1R7A3A3A1S21VA;R6A2SdS28G3R9R8R7A4A1F_;F_;F_;F_;F_;F_;Fz;Fx;Fc;").
Proof.
  intros c x z Hc X0 XM XE NX Hz HS. pose proof HI3 as (H3 & _ & SEC3 & _).
  pose proof (geoQ A HG H3) as (T1 & T2 & S1 & S2 & S8 & ST & TB & TI & TG).
  apply (slot_czone A c x z) in HS.
  destruct (qfoot_cases z Hz) as [(c' & o' & (C1' & O0' & OM' & OE' & IDin') & CZ')|(i & ch & Hi & Hr)].
  - apply (czone_slots_disj (ag_spacebeg (aa_geom A)) c (16 * x) c' o' z S1 ltac:(clear -S2 TG; lia) S8 Hc C1' ltac:(clear -X0; lia) O0' XM OM' XE OE'); [|exact HS|exact CZ'].
    destruct (Z.eq_dec c c') as [EC|NC]; [right | left; exact NC]. subst c'. intros EO. apply NX.
    rewrite <- EO in IDin'. replace (16 * x / 16) with x in IDin' by (rewrite Z.mul_comm, Z.div_mul; lia). exact IDin'.
  - destruct HSR as (HS1 & _). destruct (HS1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
    destruct (SEC3 i ch Hi) as (X1 & _). rewrite kSpaceSize_val in X1.
    destruct D10 as (E1 & E2 & E3 & E4 & E5). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in E5.
    destruct Hr as [Hr|Hr].
    + apply (czone_out A HG H3 c (16 * x) (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z Hc ltac:(clear -X0; lia) XM XE);
        [exact Hr | clear -X1; lia | exact E5 | exact HS].
    + apply (czone_sh_out A HG H3 c (16 * x) (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z Hc ltac:(clear -X0; lia) XM XE);
        [exact Hr | clear -E1; lia | clear -E3 TG; lia | clear -X1; lia | exact HS].
Qed.
End QSlot.
End RebuildRP.

