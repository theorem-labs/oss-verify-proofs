(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao ba.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec2 SpineCallocIo.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymG IfaceS.

(* [comment removed for export] *)
Module SpineMallocS9j.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "bool"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "SVar"; "ss_facts"; "ss_next"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "C9"; "C9p"; "V_RZ"; "F_gen"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "L_malloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9"; "S2_of"; "fin_hyps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocS9j.INST"; "F9a_nf"; "F9b_nf"; "F9pa_nf"; "F9pb_nf"; "K_a"; "K_b"; "K_pa"; "K_pb"; "hcells_a"; "hcells_b"; "hcells_pa"; "hcells_pb"; "s9_a"; "s9_b"; "s9_pa"; "s9_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"; "@Corelib.Init.Specif"; "sig"; "@Stdlib.Lists.List"; "incl"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S36S0S0SdS0S10VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C9]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S36S0S0SdS0S11VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all | (cbv delta [C9p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.

Definition F9a_nf : axst := Eval vm_compute in (F9a (Wcan 0) UStopLe 2).
Definition objs_a := ss_objs (ax_S F9a_nf).
Definition swc_a := ob_cells (nth 0 objs_a O_st). Definition scells_a := ob_cells (nth 36 objs_a O_st).
Definition hcells_a := ob_cells (nth 37 objs_a O_st).
Definition K_a := KEPT9 W swc_a.
Definition s9_a : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS1eS22A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_a_0 : ltac2:(tb__ "0|0|
S1dU0Vst;S1eS32S2eS26S6S2aA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Definition F9b_nf : axst := Eval vm_compute in (F9b (Wcan 0) UStopLe 2).
Definition objs_b := ss_objs (ax_S F9b_nf).
Definition swc_b := ob_cells (nth 0 objs_b O_st). Definition scells_b := ob_cells (nth 36 objs_b O_st).
Definition hcells_b := ob_cells (nth 37 objs_b O_st).
Definition K_b := KEPT9 W swc_b.
Definition s9_b : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS1fS23A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_b_0 : ltac2:(tb__ "0|0|
S1dU0Vst;S1fS33S2fS27S6S2bA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Definition F9pa_nf : axst := Eval vm_compute in (F9pa (Wcan 0) UStopLe 2).
Definition objs_pa := ss_objs (ax_S F9pa_nf).
Definition swc_pa := ob_cells (nth 0 objs_pa O_st). Definition scells_pa := ob_cells (nth 36 objs_pa O_st).
Definition hcells_pa := ob_cells (nth 37 objs_pa O_st).
Definition K_pa := KEPT9 W swc_pa.
Definition s9_pa : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS20S24A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_pa_0 : ltac2:(tb__ "0|0|
S1dU0Vst;S20S34S30S28S4S2cA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Definition F9pb_nf : axst := Eval vm_compute in (F9pb (Wcan 0) UStopLe 2).
Definition objs_pb := ss_objs (ax_S F9pb_nf).
Definition swc_pb := ob_cells (nth 0 objs_pb O_st). Definition scells_pb := ob_cells (nth 36 objs_pb O_st).
Definition hcells_pb := ob_cells (nth 37 objs_pb O_st).
Definition K_pb := KEPT9 W swc_pb.
Definition s9_pb : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS21S25A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_pb_0 : ltac2:(tb__ "0|0|
S1dU0Vst;S21S35S31S29S4S2dA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9S8Z20A1SaS12A1A2S3S7A1A3S10VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S1eG0A3A6S4A3").
Proof. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9SaS12A1S8Z10A1A2S3S7A1A3S10VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S1fG0A3A6S4A3").
Proof. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert9pa_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9S8Z20A1SaS12A1A2S3S7A1A3S11VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S20G0A3A6S4A3").
Proof. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert9pb_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9SaS12A1S8Z10A1A2S3S7A1A3S11VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S21G0A3A6S4A3").
Proof. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX9_0 : ltac2:(tb__ "0|0|
S38SeScS1S10VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX9p_0 : ltac2:(tb__ "0|0|
S38SeScS1S11VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FGC_0 : ltac2:(tb__ "0|0|
S37S7S13SbS1S10VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FGCp_0 : ltac2:(tb__ "0|0|
S37S7S13SbS1S11VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS9j.

(* [comment removed for export] *)
Module SpineCallocOv.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "@Corelib.Init.Datatypes"; "list"; "bool"; "pair"; "prod"; "true"; "nil"; "option"; "Some"; "app"; "cons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "sv"; "sobj"; "rl"; "rm"; "sprop"; "ss_next"; "SLit"; "SVar"; "agree_below"; "swf"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "AE_A"; "L_calloc_null"; "JL_calloc_null"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ag_ctx"; "ag_spacebeg"; "ag_stack_bottom"; "ag_stack_top"; "ag_thread"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertCallocOv"; "stRo_S"; "s_o"; "stKo"; "EXo"; "N_ovn"; "R_o"; "stRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineCallocOv.OV"; "JGe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI"; "Jc"; "rho_ce"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "withGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@Stdlib.Lists.List"; "In"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocIo.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocIo OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertCallocOv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma N_ovn_small : Forall spec_small N_ovn.
Proof. unfold N_ovn, spec_small, ERRNO_A. repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia. Qed.

Section OV.
Variable nW : nat. Variable st : ustop.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S2aS28VCST;R1A2S28S4bR2A2S2F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S2aS28VCST;R1A2S28S4cR2A2S2F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition JGe (A : AA) (Kc : KcA) (rho : valuation) : jpredA := ltac2:(tb__ "0|0|
S45SeS17S33S3dVA;Vrho;A2R1A3Lr;S3cVW;Vst;VA;VKc;A4A2").
Lemma JMc_stableA : ltac2:(tb__ "0|0|
S20S1bS3eVW;Vst;A2S1cR2A1S35Vsegs;S33S3cVW;Vst;R4R3A4A3F_;F_;FKc;FA;").
Proof.
  intros A Kc HUS HKc rho rho' tp tr md md' Hag Hme HJ.
  pose proof (JMc_agree W st A Kc rho rho' tp tr md HUS ltac:(eapply agree_below_le; [|exact Hag]; cbv; discriminate) HJ) as (HA & HK & Htp & HU & HB & HN & Htop).
  split; [apply (AInvA_mat segs A rho' tp md md'); [exact HA | exact Hme]|].
  split; [destruct Hme as ((mat' & ->) & _); rewrite with_vm_backing_with_vm; apply HKc; exact HK|].
  split; [exact Htp|]. split; [exact HU|]. split; [|split; [exact HN | exact Htop]].
  destruct Hme as ((mat' & ->) & _). exact HB.
Qed.
Lemma JGe_stable : ltac2:(tb__ "0|0|
S20S1bSeS3eVW;Vst;A2S1cR3A1S35Vsegs;S33S34R5R4R3A3A3F_;F_;Frho;FKc;FA;").
Proof. intros A Kc rho HUS HKc. apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply JMc_stableA; [exact HUS | exact HKc]]. Qed.
Lemma JGe_rigid : ltac2:(tb__ "0|4|
S20S1bSeSeS3S1aQ40M0A1M1A1S3S41A1S40S34R7R6R5R4R3R2R1A7S21R8A1S27S1S0G1SdR6P97A2S19G0S26R1A1A2A3S1S0G1SdR6P98A2S19G0S22R1A1A2A3S1S0G1SdR6P99A2S19G0S25R1A1A2A3S1S0G1SdR6P9aA2S19G0S24R1A1A2A3S1S0G1SdR6P9bA2S19G0S23R1A1M2A2A3S1S0G1SdR6P9cA2S19G0S4fG2S48A2A2A3S1S0G1S9S1aQ8A1M3A1F_;S12R6A1S12R7A1A3S1S29S0S3G3A1S11R7R1A2S11R8R1A2A3Fl;S29S4eR1S2bA2S0G1SdR8R2A2SdR9R2A2A3F_;Fi;A2A2A2A2A2A2A2A2TG;F_;Fmd;Ftr;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp tr md [Hag _]. destruct Hag as (Hagw & Hagl & Hagm). cbn zeta.
  repeat match goal with |- _ /\ _ => split end;
    try (rewrite <- (Hagw _) by (unfold GW; lia); reflexivity).
  - apply functional_extensionality. intros a. symmetry. exact (Hagm a).
  - intros l. symmetry. exact (Hagl l).
  - intros i Hi. rewrite <- (Hagw i) by (unfold GW, NF in *; lia). symmetry. exact (proj1 (rho_ce_agree A rho) i Hi).
Qed.

Section FIN.
Hypothesis RN : ltac2:(tb__ "0|0|
S0S3S10A1S31VW;Vst;A2SbS10S46S3fS4aS10S49S30A4A3A3").
Hypothesis WRn : ltac2:(tb__ "0|0|
S0S4S18S2cVW;Vst;A2A1S7A3").
Hypothesis DKRn : ltac2:(tb__ "0|4|
S0S9S6S3S6SfSfA2M0A1M1S3S13A1M2A2M3A1S43S37S2eVW;Vst;A2A1S2cVW;Vst;A2A2SaG3S5G1G2ScG0S5SfSfS15S47A1S16P18A1A4S8G0A1A3S8S13A1A4A2A3").
Hypothesis NXRn : ltac2:(tb__ "0|0|
S0S29S14S2cVW;Vst;A2A1S14S37S2eVW;Vst;A2A1A1A3").
Hypothesis ENTn : ltac2:(tb__ "0|0|
S0S4S39S32VW;Vst;A2S1eS1dVW;Vst;A3S2dVW;Vst;A2A3S7A3").
Hypothesis IDn : ltac2:(tb__ "0|0|
S0S4S44S2dVW;Vst;A2S2bA2S7A3").

Theorem ov_null_finish : ltac2:(tb__ "0|1|
S20S1bSeS3S1aQ40A1A1S42SeS3S6S38S3aA2M0A1S1cR6A1S4dG0S5S38S3aS1eS1dVW;Vst;A3S1fVAInv;VCST;VXGL;R8R7A5A4R2A3S36Vsegs;S34R9R8R7A3S2fVW;Vst;A2R4R6R5A6S3bVsegs;S2bR8R7R4R6A6F_;F_;F_;FPosts;FrhoY;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoY Posts HKc HPosts H. destruct w as [tr [ms md]].
  pose proof H as [HsmA [Hag HJ]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (JGe_rigid A Kc rho rhoY tp tr md (proj2 H)) as (E151 & E152 & E153 & E154 & E155 & E156 & Erm & Erl & Elow).
  destruct HJ as (HA & HK & Htp & HU & HB & HN0 & Htop).
  set (nv := bv_unsigned (rw rho 12%positive) * bv_unsigned (rw rho 13%positive)).
  assert (HN : 0 <= nv) by (unfold nv; pose proof (urange (rw rho 12%positive)); pose proof (urange (rw rho 13%positive)); nia).
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range (aa_geom A)) as ACV.

  set (KJ := (fun (_ : valuation) (_ : list word) (t : list event) (m : Model) => Kc t m) : jpredA).
  assert (Ha : SPA segs KJ (EXo W st) rhoY tp (tr, mkCfg ms md)) by (split; [exact HsmA | exact HK]).
  assert (EOBJ : ss_objs (ax_S (EXo W st)) = firstn (NOBJo W) (ss_objs (ax_S (EXo W st))) ++ R_o W st).
  { unfold R_n. symmetry. apply firstn_skipn. }
  pose proof (SPA_unobj segs KJ rhoY (EXo W st) _ _ tp tr ms md EOBJ Ha (fun k => k)) as Hb.
  cbn zeta in Hb. set (R := R_o W st) in *. set (rho3 := rho_absorb rhoY R (vms md tp ms)) in *.
  change (ax_setS (EXo W st) (set_objs (ax_S (EXo W st)) (firstn (NOBJo W) (ss_objs (ax_S (EXo W st)))))) with (stKo W st) in Hb.
  pose proof (proj1 (proj1 Ha)) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.

  assert (AO : forall o, In o R -> _) by (intros o Ho; exact (absorb_obj rhoY _ tr (vms md tp ms) (vmd md) _ R o Hsm1 EOBJ Ho)).
  assert (NK : forall k, In k N_m1 -> In (carve_obj k) R /\ spec_small k /\ spec_covered k
            /\ cells_in_view rhoY (rd_of segs (rm rhoY)) (fst (spec_range rhoY k) - (let '(_, lo, _, _) := k in lo)) (let '(_, _, _, cs) := k in cs)).
  { intros k Hk.
    split; [rewrite RN; apply in_or_app; left; rewrite <- N_m1_ok; apply in_map; exact Hk|].
    split; [exact (proj1 (Forall_forall _ _) N_m1_small k Hk)|].
    split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_m1_coverb k Hk)|].
    pose proof (proj1 (Forall_forall _ _) (N_m1_civ AInvA_die A rhoY tp md HA E151 E152 E153 E154 E155 E156) k Hk) as CV. cbn beta in CV.
    destruct k as [[[base lo] hi] cs]. cbn [spec_range fst]. replace (bv_unsigned (eval rhoY base) + lo - lo) with (bv_unsigned (eval rhoY base)) by (clear; lia). exact CV. }

  assert (ET : bv_unsigned (eval rhoY vT) = ag_thread (aa_geom A)) by (unfold vT; cbn [eval]; rewrite E151; apply u64_lit; lia).
  assert (INR : forall a, in_ranges rhoY R a ->
            (exists k, In k N_m1 /\ fst (spec_range rhoY k) <= bv_unsigned a < snd (spec_range rhoY k))
            \/ znull (aa_geom A) (bv_unsigned a) \/ bv_unsigned a = 0x173661).
  { intros a (o & HoR & Hr). rewrite RN in HoR. apply in_app_or in HoR as [HoR|HoR].
    - left. rewrite <- N_m1_ok in HoR. apply in_map_iff in HoR as (k & <- & Hk). exists k. split; [exact Hk|].
      rewrite (carve_range rhoY k (proj1 (Forall_forall _ _) N_m1_small k Hk)) in Hr. exact Hr.
    - apply in_map_iff in HoR as (k & <- & Hk). rewrite (carve_range rhoY k (proj1 (Forall_forall _ _) N_ovn_small k Hk)) in Hr.
      unfold N_ovn in Hk. cbn [In] in Hk. unfold znull.
      destruct Hk as [E|[E|[]]]; subst k; cbn [spec_range fst snd eval] in Hr; rewrite ?(u64_lit 0) in Hr by lia; unfold ERRNO_A in *.
      + destruct (Z.eq_dec (bv_unsigned a) 0x173661); [right; right; assumption | right; left; lia].
      + right; left. lia. }

  set (vE := view segs (rm rhoY)). set (v3 := view segs (rm rho3)).
  assert (O1 : In (carve_obj (SLit 0, 0x173660, 0x173662, [(0x173661, 1%nat, SLit 1)])) R).
  { rewrite RN. apply in_or_app; right. apply in_map. unfold N_ovn. cbn [In]. tauto. }
  assert (VO : forall z, ~ znull (aa_geom A) z -> v3 z = vE z).
  { intros z Hz. unfold v3, vE. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by (clear -n; lia) || rewrite !view_out by (clear -n l; lia); reflexivity.
    rewrite !view_in by (clear -l l0; lia).
    destruct (in_ranges_dec rhoY R (Z_to_bv 64 z)) as [Hin|Hout].
    - destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc|E1]]; rewrite ?u64_lit in * by (clear -l l0; lia).
      + unfold rho3. exact (absorb_specs_view rhoY _ tr (vms md tp ms) (vmd md) _ R N_m1 (rd_of segs (rm rhoY)) Hsm1 EOBJ NK z k Hk Hr).
      + exfalso. exact (Hz Hc).
      +
        destruct (AO _ O1) as (_ & CE & _ & _). cbn [ob_cells carve_obj carved lit_cells map] in CE.
        destruct (CE _ ltac:(cbn; left; reflexivity)) as (_ & _ & CEj). pose proof (CEj 0%nat ltac:(cbn; lia)) as X. clear CEj.
        cbn [ob_base carved c_off c_width SymState.c_val eval] in X. change (Z.to_nat (Z.of_nat 1)) with 1%nat in X. change (Z.of_nat 0) with 0 in X.
        rewrite soff_lit_small, (u64_lit 0), Z.add_0_r in X by lia. rewrite Z.add_0_l in X. rewrite E1. unfold rho3.
        transitivity (Some (nth 0 (enc_bytes 1 (Z_to_bv 64 1)) (Z_to_bv 8 0))); [exact X|]. symmetry.
        destruct HRest as (_ & _ & _ & _ & _ & _ & _ & _ & (HMIc & _ & _)). pose proof (Forall_inv HMIc) as C9. specialize (C9 0%nat ltac:(cbn; lia)).
        cbn [c_addr c_w c_val Z.of_nat] in C9. rewrite Z.add_0_r in C9. rewrite maskv_out in C9 by (apply fs_footb_img; [exact HG | lia]). rewrite view_in in C9 by lia.
        exact C9.
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hout. reflexivity. }
  assert (PRES : forall z, znull (aa_geom A) z -> exists b, v3 z = Some b).
  { intros z Hz. unfold v3. unfold znull in Hz. unfold SEC_INST, ERRNO_A in Hz.
    assert (CS : (0xe4000 <= z < 0x646000) \/ (ag_thread (aa_geom A) + 2768 <= z < ag_thread (aa_geom A) + 3168)) by (clear -Hz; lia).
    destruct CS as [CS|CS].
    - rewrite view_in by lia. apply rd_of_imageA. exact CS.
    - assert (Bz : 0 <= z < 2 ^ 64) by lia.
      destruct (in_ranges_dec rhoY R (Z_to_bv 64 z)) as [Hin|Hout].
      +
        destruct Hin as (o & HoR & Hr). rewrite u64_lit in Hr by exact Bz.
        destruct (AO o HoR) as (Bo & _ & Po & _).
        assert (DU : ob_dflt o = DUnknown \/ ob_dflt o = DZero).
        { rewrite RN, <- N_m1_ok, <- map_app in HoR. apply in_map_iff in HoR as ([[[bk lk] hk] ck] & <- & _). left. reflexivity. }
        unfold obj_range in Hr. cbn [fst snd] in Hr.
        destruct (Po DU (z - bv_unsigned (eval rhoY (ob_base o))) ltac:(clear -Hr; unfold obj_lo_of, obj_hi_of in *; lia)) as [x Hx].
        exists x. rewrite view_in by exact Bz. replace z with (bv_unsigned (eval rhoY (ob_base o)) + (z - bv_unsigned (eval rhoY (ob_base o)))) at 1 by (clear; lia). exact Hx.
      + destruct HRest as (_ & _ & _ & _ & _ & _ & _ & HTH & _). unfold thread_inv in HTH. destruct HTH as [_ HTS].
        destruct (HTS z ltac:(clear -CS; lia)) as [b0 Hb0].
        rewrite maskv_out in Hb0 by (apply fs_footb_thread; [exact HG | clear -CS; lia]).
        exists b0. rewrite <- Hb0. rewrite !view_in by exact Bz. unfold rho3, rd_of. rewrite rm_absorb_out by exact Hout. reflexivity. }

  assert (Hc : SPA segs KJ (stRo W st) rho3 tp (tr, mkCfg ms md)).
  { unfold stRn. eapply SPA_restate; [exact WRn | exact DKRn | exact NXRn | | constructor | exact Hb].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. destruct (geom_old _ HG) as (_ & _ & _ & G4' & _). rewrite G4'. reflexivity. }

  pose proof (smatchA_entails segs _ _ _ rho3 tp _ ENTn (proj1 Hc)) as Hsm4.
  set (rho4 := rho_sub rho3 (s_o W st)) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoY k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ IDn Hk). reflexivity. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 (s_o W st)).
  pose proof (rhoM_agree A rho) as (RMw & RMl & RMm).

  apply (LQPA_intro segs NF rho tp _ (L_calloc_null AE_A W st) (JL_calloc_null AInv CST XGL A Kc) rho4 tp _ KJ).
  - exact HPosts.
  - split; [exact Hsm4 | exact HK].
  - split.
    + intros i Hi. rewrite (Hlow i Hi). symmetry. exact (Elow i Hi).
    + intros l. unfold rho4. cbn [rho_sub rl]. unfold rho3. cbn [rho_absorb rl]. rewrite (Erl l). reflexivity.
  - intros _. unfold JL_calloc_null. cbn [w_tr w_cfg cfg_model].
    exists (bumpVK A nv).
    assert (HA' : AInv (bumpVK A nv) rho4 tp md).
    { unfold AInv. apply (null_rebuild A rhoY rho4 tp md nv HA ltac:(clear -HN; lia)).
      - intros z Hz. rewrite Erm4. exact (VO z Hz).
      - intros z Hz. rewrite Erm4. exact (PRES z Hz). }
    split; [exact HA'|]. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn [aa_V bumpVK]; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    {
      rewrite Erm4, <- Erm.
      assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ rt_zoneM (aa_geom A) a -> ~ znull (aa_geom A) a -> a <> 0x173661 -> ~ in_rangesZ IMG_S a ->
                      rm rho3 (Z_to_bv 64 a) = rm rhoY (Z_to_bv 64 a)).
      { intros a Ba Hz1 Hz2 Hz3 Hz4. unfold rho3. apply rm_absorb_out. intros Hin.
        destruct (INR _ Hin) as [(k & Hk & Hr)|[Hc'|E1]]; rewrite ?u64_lit in * by exact Ba.
        - apply Hz1. exact (N_m1_zone (aa_geom A) rhoY k a HG E151 E152 Hk Hr).
        - exact (Hz2 Hc').
        - exact (Hz3 E1). }
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
End FIN.
End OV.
End SpineCallocOv.

(* [comment removed for export] *)
Module SpineMallocS9jW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "true"; "bool"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "SVar"; "ss_facts"; "ss_next"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "C9"; "C9p"; "V_RZ"; "F_gen"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "L_malloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9"; "S2_of"; "fin_hyps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocS9jW2.INST"; "F9a_nf"; "F9b_nf"; "F9pa_nf"; "F9pb_nf"; "K_a"; "K_b"; "K_pa"; "K_pb"; "hcells_a"; "hcells_b"; "hcells_pa"; "hcells_pb"; "s9_a"; "s9_b"; "s9_pa"; "s9_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"; "@Corelib.Init.Specif"; "sig"; "@Stdlib.Lists.List"; "incl"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.CertMallocSPd OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S36S0S0SdS0S10VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C9]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S36S0S0SdS0S11VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C9p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C9p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C9p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.

Definition F9a_nf : axst := Eval vm_compute in (F9a (Wcan 2) UStopLe 4).
Definition objs_a := ss_objs (ax_S F9a_nf).
Definition swc_a := ob_cells (nth 0 objs_a O_st). Definition scells_a := ob_cells (nth 38 objs_a O_st).
Definition hcells_a := ob_cells (nth 39 objs_a O_st).
Definition K_a := KEPT9 W swc_a.
Definition s9_a : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS1eS22A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_a_0 : ltac2:(tb__ "0|0|
S1dU2Vst;S1eS32S2eS26S6S2aA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Definition F9b_nf : axst := Eval vm_compute in (F9b (Wcan 2) UStopLe 4).
Definition objs_b := ss_objs (ax_S F9b_nf).
Definition swc_b := ob_cells (nth 0 objs_b O_st). Definition scells_b := ob_cells (nth 38 objs_b O_st).
Definition hcells_b := ob_cells (nth 39 objs_b O_st).
Definition K_b := KEPT9 W swc_b.
Definition s9_b : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS1fS23A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_b_0 : ltac2:(tb__ "0|0|
S1dU2Vst;S1fS33S2fS27S6S2bA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Definition F9pa_nf : axst := Eval vm_compute in (F9pa (Wcan 2) UStopLe 4).
Definition objs_pa := ss_objs (ax_S F9pa_nf).
Definition swc_pa := ob_cells (nth 0 objs_pa O_st). Definition scells_pa := ob_cells (nth 38 objs_pa O_st).
Definition hcells_pa := ob_cells (nth 39 objs_pa O_st).
Definition K_pa := KEPT9 W swc_pa.
Definition s9_pa : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS20S24A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_pa_0 : ltac2:(tb__ "0|0|
S1dU2Vst;S20S34S30S28S4S2cA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Definition F9pb_nf : axst := Eval vm_compute in (F9pb (Wcan 2) UStopLe 4).
Definition objs_pb := ss_objs (ax_S F9pb_nf).
Definition swc_pb := ob_cells (nth 0 objs_pb O_st). Definition scells_pb := ob_cells (nth 38 objs_pb O_st).
Definition hcells_pb := ob_cells (nth 39 objs_pb O_st).
Definition K_pb := KEPT9 W swc_pb.
Definition s9_pb : ltac2:(tb__ "0|0|
S17") := ltac2:(tb__ "0|0|
S16S15S1cS21S25A2S1S1bS1aVW;Vst;A3A1A3").
Lemma FH_pb_0 : ltac2:(tb__ "0|0|
S1dU2Vst;S21S35S31S29S4S2dA8").
Proof.
  unfold fin_hyps. cbn zeta.
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [first [left; apply In_of_inclb; vm_compute; reflexivity | right; split; apply In_of_cellb; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]|].
  split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [apply inclb_incl; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
  split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9S8Z20A1SaS12A1A2S3S7A1A3S10VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S1eG0A3A6S4A3").
Proof. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9SaS12A1S8Z10A1A2S3S7A1A3S10VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S1fG0A3A6S4A3").
Proof. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert9pa_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9S8Z20A1SaS12A1A2S3S7A1A3S11VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S20G0A3A6S4A3").
Proof. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert9pb_0 : ltac2:(tb__ "0|1|
SdS5S19SfUfa0S3S14A1SeS2S0S18S2S7S9SaS12A1S8Z10A1A2S3S7A1A3S11VW;Vst;Vtmax;A3A2S3S0A1M0A3S2S0S21G0A3A6S4A3").
Proof. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX9_0 : ltac2:(tb__ "0|0|
S38SeScS1S10VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX9p_0 : ltac2:(tb__ "0|0|
S38SeScS1S11VW;Vst;Vtmax;A3A1A1A2").
Proof. apply Pos.leb_le. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FGC_0 : ltac2:(tb__ "0|0|
S37S7S13SbS1S10VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (C9 W st tmax) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FGCp_0 : ltac2:(tb__ "0|0|
S37S7S13SbS1S11VW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (C9p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS9jW2.

(* [comment removed for export] *)
Module SpineMallocSecE0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_next"; "sprop"; "SLit"; "valuation"; "reg_sv"; "SVar"; "eval"; "swf"; "ss_objs"; "ss_pc"; "obj_range"; "ranges_disjoint"; "ro_addr"; "sprop_below"; "ss_facts"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "ax_setS"; "entailsA"; "shadow_addr"; "@Corelib.Init.Datatypes"; "list"; "nil"; "bool"; "cons"; "prod"; "pair"; "true"; "app"; "Some"; "option"; "false"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "CS1"; "ES1"; "ES1f"; "ES1g"; "SS0"; "SSa_S"; "V_MS"; "nxS"; "ESn"; "F_sgen"; "RT_sec"; "SSb_S"; "V_NS"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "ge"; "modulo"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "with_vmmaps"; "ENOMEM"; "errno_ret"; "vm_reserved"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "AE_A"; "KcA"; "Kc_ok"; "L_malloc_null"; "UStopLeOrPc"; "ustop"; "A_globals"; "JL_malloc_null"; "J_alloc_preT"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN"; "stRn_S"; "s_n"; "stKn"; "N_secn"; "R_n"; "stRn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "RT_m1"; "F_fam"; "F_s1"; "neededx"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "le"; "succ"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_modeled_b"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA"; "mmap_obj_sym"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "a1x"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymComplete SymCall SymExit SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section MANY.
Variable segs : list Segment.
Theorem etriple_mmap_rw_sym_anyA : ltac2:(tb__ "0|10|
S40S40S3eQ40M0A1M1S40F_;S19SbS1fG1A1S6S3bS41Vsegs;S8S18R5A1A1R8A3S0S28S58A1S7fVsegs;S11S18R6A1A1A2S27S58S59A2A3S0S6ScS18R7A1Z11A2SaZdeA1A3S0S6ScS18R8A1ZbA2R5A3S0S21S17S8S18R9A1A1R6A2S25A3S0S3bS3dG0SeR9R7A2A2R6A3S0S3bS4fR7Z1000A2Z0M2A3S1S4bG2R8A2S4bR8S50Z2Z3eA2A2A2S1fS53A1M3S3aS51S72Vsegs;RfReR10S24G3S6cR3S6dR2R1A2A4A5R14R10RfR4R2A4S1S0S21S8eS39R4U2A2S39R4U3M4A2M5S39R4U5A2A3S25A3S1S0S21S8fG5A1S29A3S1S4eS91R3R10A2ReA2S1R14R11R10R5R3A4G1S6fS39R5U0A2S39R5G4A2R4S39R5U1M6A2R1A5S1S7S7bS7R1S10S18R15A1A1A3S13S12R15R2A2S24S3bS3bS3dG0R4A2M7S4cG7R12A2A4A2F_;Fo;S1G1S1S4dS3dG0R3A2M8S3dG0R1A2M9A2S4bG9S4cG8R11A2A2A2S0S21S14Vsegs;R2A2S29A3F_;Fx;S1S23S6S6A2MaS3bS7bGaR2S1aR16A1A3S1S4dS3dG0SeR16S2aS6S6R3A3A2A2MbR2A2S4bR2S4cGbS3dG0SeR16S2bS6S6R3A3A2A2A2A2A2S4S1S4dS3dG0R6A2McS3dG0S1eS3dG0SeR17S1bR18A1A2A2R3A2A2MdA2S4bGdS4cGcR14A2A2A2A1F_;F_;Fy;Fr;R15R2S45R13S8S18R14A1A1R2A3R12R7S54S70S52R5A1S39R6G6A2R2A3R5A2A5A2A2A2F_;Fa;A2A2A2A2F_;F_;Fmd;Fms;Ftr;S42Vsegs;S3fVsegs;R11ReRdRcA5S43S5S3fVsegs;R11S73RfSaS3dG0S56S55A1A2A1A2ReRdR1A6S3G1G1S3fVsegs;R11R1A1S1cR10S46S18R10A1MeSdS8GeA1MfA1S26S7S10GeA1S22S7S95GfRdA2S20S7A1A3A3S8dGfA1A4A2S45RfGfR1A3ReR2A6La;A2A2Lw;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fnlit;Felen;Ftp;Frho;FA;FJo;FJf;FJ;").
Proof.
  intros J Jf Jo A rho tp elen nlit Hst Hi H17 H11 Hbel Helen Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (mmap_len_sym segs rho tp A tr ms md elen nlit Hsp H11 Helen Hmod Hn) as [Hlen HnZ].
  destruct (HJ tr ms md Hsp Hk) as (Hmodb & Hnr & Hroom & HJf & HOK).
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  destruct (mmap_grant_refusable (ms_gpr ms 3) md (mmap_nZ (ms_gpr ms 1))) eqn:Hrf.
  - eexists. split; [exact (wstep_mmap_intro_failA segs ms md _ Hh H222 Hlen Hmodb tr Hp Hrf)|].
    left. split; [|exact HJf]. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
  - destruct (@mmap_rw_not_refusable_place (sys_input segs ms (Z_to_bv 64 222)) md Hrf) as [a Hpl].
    change (mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a) in Hpl.
    eexists. split; [exact (wstep_mmap_intro_okA segs ms md _ Hh H222 Hlen Hmodb tr a Hp Hpl)|].
    right. exists a. destruct (HOK a Hpl) as (Hdisj & Hnro & Hxs & HJo). split.
    + eapply smatchA_after_mmap_obj_sym; eauto.
    + cbn [w_tr w_cfg fst snd cfg_model]. unfold mmap_rw_model. rewrite (with_mmap_backing_plain _ _ _ _ Hnr). exact HJo.
Qed.
End MANY.

Ltac rr X := intros; eapply X; revgoals; [> eassumption ..].

Section SEC2E.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S3bS6aVCST;R1A2S6aS96R2A2S2F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S3bS6aVCST;R1A2S6aS97R2A2S2F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S64VAInv;VW;Vst;VA;VKc;SdPcA1A6").
Hypothesis law_res : ltac2:(tb__ "0|1|
S7aSbS1fS3eQ40A1M0A1S51VAInv;R4R3R2R1A4S0S1fS23G0G0A2A1S57S52R2A1A1S6eS69A1A3F_;Fmd;Ftp;Frho;FA;").
Hypothesis Wa : ltac2:(tb__ "0|0|
S0S21SfS31VW;Vst;Vtmax;A3A1S25A3").
Hypothesis Da : ltac2:(tb__ "0|6|
S0S28S23S1fS23S6S6A2M0A1M1S1fS9A1M2A2M3A1S71S18S84VW;Vst;Vtmax;Z8M4A4A1S31VW;Vst;Vtmax;A3A2S27G3S24G1G2S22G0S24S6S6S88G4A1SdS38A1A4M5S22G0G5S20G0A1A3A3S20S9A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S0S21SfS37VW;Vst;Vtmax;A3A1S25A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S21S7cS9S15S82A1S35A3S25A3").
Hypothesis NXS0 : ltac2:(tb__ "0|0|
S8cS5aS8S18S30VW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECertS1 : ltac2:(tb__ "0|3|
S0S21S49S69Ufa0S22S3bZ7050cS20S3bA1A3S5aS22S47S48S30VW;Vst;Vtmax;A3Z1SaZ0M0A1M1A3S20S47A1M2A3S22S47S48S2dVW;Vst;Vtmax;A3G0G1A3G2A3A6S25A3").
Hypothesis WC1 : ltac2:(tb__ "0|0|
S0S21SfS18S2cVW;Vst;Vtmax;A3A1A1S25A3").
Hypothesis DC1 : ltac2:(tb__ "0|4|
S0S28S23S1fS23S6S6A2M0A1M1S1fS9A1M2A2M3A1S71S18S2dVW;Vst;Vtmax;A3A1S18S2cVW;Vst;Vtmax;A3A1A2S27G3S24G1G2S22G0S24S6S6S98SdS32A1A4S20G0A1A3S20S9A1A4A2A3").
Hypothesis NXC1 : ltac2:(tb__ "0|0|
S0S3cS8S18S2cVW;Vst;Vtmax;A3A1A1S8S18S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis IC1 : ltac2:(tb__ "0|0|
S0S28S58A1S7fS69S11S18S2cVW;Vst;Vtmax;A3A1A1A2S27S58S59A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1Z11A2SaZdeA1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZbA2SdS32A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZcA2SaZ3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZdA2SaZ22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZeA2SaZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZfA2SaZ0A1A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S3cS8S18S2cVW;Vst;Vtmax;A3A1A1S82A3").
Hypothesis NXS1f : ltac2:(tb__ "0|0|
S8cS5aS8S18S2eVW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECertSf : ltac2:(tb__ "0|3|
S0S21S49S69Ufa0S22S3bZ5e398S20S3bA1A3S5aS22S47S48S2eVW;Vst;Vtmax;A3Z1SaZ0M0A1M1A3S20S47A1M2A3S22S47S48S34VW;Vst;Vtmax;A3G0G1A3G2A3A6S25A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S7dS9S26S9S26S9S26S9S26S9S67VW;Vst;A2S66S65A1A3S83A3S87A3S86Vtmax;Z8A2A3S16S18S2cVW;Vst;Vtmax;A3A1A1A3").
Hypothesis RN : ltac2:(tb__ "0|0|
S0S1fS7A1S78VW;Vst;Vtmax;A3S26S7S85S6bS94S7S93S77A4A3A3").
Hypothesis WRn : ltac2:(tb__ "0|0|
S0S21SfS74VW;Vst;Vtmax;A3A1S25A3").
Hypothesis DKRn : ltac2:(tb__ "0|4|
S0S28S23S1fS23S6S6A2M0A1M1S1fS9A1M2A2M3A1S71S18S76VW;Vst;Vtmax;A3A1S74VW;Vst;Vtmax;A3A2S27G3S24G1G2S22G0S24S6S6SaS92A1SdP18A1A4S20G0A1A3S20S9A1A4A2A3").
Hypothesis NXRn : ltac2:(tb__ "0|0|
S0S3cS8S74VW;Vst;Vtmax;A3A1S8S18S76VW;Vst;Vtmax;A3A1A1A3").
Hypothesis ENTn : ltac2:(tb__ "0|0|
S0S21S1dS79VW;Vst;Vtmax;A3S5fS5cVW;Vst;A3S75VW;Vst;Vtmax;A3A3S25A3").
Hypothesis IDn : ltac2:(tb__ "0|0|
S0S21S90S75VW;Vst;Vtmax;A3S7eA2S25A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S6ScS18S2cVW;Vst;Vtmax;A3A1ZaA2SaZ0A1A3").
Hypothesis XC1 : ltac2:(tb__ "0|1|
S0S1fS23S6S6A2M0A1S1aS2cVW;Vst;Vtmax;A3A1S20G0A1A3").
Hypothesis SK1 : ltac2:(tb__ "0|1|
S0S1fS23S23S6S6A2S6A2M0A1S6bS7G0S8bS10S18S2cVW;Vst;Vtmax;A3A1A1A4S6bS7G0S8bS26S7S26S7S22S7S89S26S7S68VW;A1S62A3A3S85A3S36A3A4A3").

Theorem esec_ecall : ltac2:(tb__ "0|4|
S7aS5dS3eQ40A1M0S40F_;SbS1fG0A1S43OF_;S0S61Vst;S60A3S0S1fS5bA1VW;S20S5bA1A3F_;S8aVW;Vst;A2S5eR7A1SbS1fS53A1M1S3aS51G0S72Vsegs;R5RaS2cVW;Vst;Vtmax;A3M2S24G1S6cR4S6dR3R2A2A4A5S4aVW;Vst;RfReRcR6RbR5R3A9S6fS39R5U0A2S39R5U3A2R4S39R5U1M3A2R3A5RfR4S45R8S8S18G2A1A1R4A3RdR7S54S70S52R5A1S39R6G3A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;SbS42Vsegs;S3fVsegs;S4aVW;Vst;RbRaR8A5S2eVW;Vst;Vtmax;A3R1R7A5R6A3FrhoX;SbG0S42Vsegs;S3fVsegs;RbR1A1S2fVW;Vst;Vtmax;A3S45R2S33VW;Vst;Vtmax;A3R1A3R9A5R8A3Fa;FrhoX;SbS42Vsegs;S3fVsegs;S4aVW;Vst;RdRcRaA5G2R1R9A5R8A3FrhoX;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FJo;FKc;FA;").
Proof.

  clear DC1 DKRn Da ECertS1 ECertSf ENTn FB IDn NXC1 NXRn NXS0 NXS1f RN WC1 WRn Wa Wb.
  intros A Kc Jo rho tp Q HW HUS HKc HJo HF HGR rhoX.
  set (nv := bv_unsigned (rw rho 12%positive)).
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  pose proof (topG_range (aa_geom A)) as ACV.

  apply (etriple_pre_pure segs _ _ (rw rhoX 142%positive = Z_to_bv 64 (secmapsize nv) /\ 64513 <= nv < 2 ^ 39)).
  { intros w Hw. destruct w as [tr [ms md]]. pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & _ & E142 & _).
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
  eapply etriple_seq.
  2: { apply etriple_disj; [exact (HF rhoX)|]. apply etriple_ex. intros a. exact (HGR rhoX a). }
  unfold ES1f, ES1g, nxS. replace (SLit (2 ^ 64 - 12)) with (SLit (bv_unsigned (errno_ret ENOMEM))) by reflexivity.
  change (mkObj (SVar (ss_next (ax_S (CS1 W st tmax)))) (SLit 0) (SVar V_MS) [] DZero) with (mmap_obj_sym (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS)).
  assert (HST' : stableA segs (ss_next (ax_S (CS1 W st tmax))) (JG W st A Kc rho)).
  { rewrite NX1. eapply stableA_mono; [|exact HST]. unfold GW, NW2. clear; lia. }
  assert (HB11 : sv_below (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS) = true) by (rewrite NX1; reflexivity).
  assert (HEV : bv_unsigned (eval rhoX (SVar V_MS)) = secmapsize nv).
  { cbn [eval]. unfold V_MS. rewrite E142. apply u64_lit. clear -BMS Hnv. lia. }
  apply (etriple_mmap_rw_sym_anyA segs (JG W st A Kc rho) (JG W st A Kc rho) Jo (CS1 W st tmax) rhoX tp (SVar V_MS) (secmapsize nv)
           HST' IC1 R17 R11 HB11 HEV (proj2 BMS) ltac:(clear -BMS Hnv; lia)).
  intros tr ms md Hsp HJG.
  destruct (pending_argsA segs rhoX tp (CS1 W st tmax) tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite R10 in Q0. rewrite R11 in Q1. rewrite R12 in Q2. rewrite R13 in Q3. rewrite R14 in Q4. rewrite R15 in Q5. cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; apply mmap_modeled_b_intro; reflexivity|].
  split; [rewrite Q3; reflexivity|].
  pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md HJG) as (E12 & E141 & _ & E151 & E152 & E153 & E154 & E155 & E156 & E145 & E146 & E147 & Erm & Erl & Elow).
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
      { destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp. }
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

Theorem esec_spine : ltac2:(tb__ "0|5|
S7aS5dS3eQ40A1M0S40F_;SbS1fG0A1S1fS23S19S80A2M1A1S81Vsegs;S7eR3R2R1A5S44S0S61Vst;S60A3S0S1fS5bA1VW;S20S5bA1A3F_;S8aVW;Vst;A2S5eR8A1S7bG1S24S19S80S5fS5cVW;Vst;A3S63VAInv;VCST;VXGL;RaR9A5A4R5A3SbS1fS53A1M2S3aS51G0S72Vsegs;R5RcS2cVW;Vst;Vtmax;A3M3S24G2S6cR4S6dR3R2A2A4A5S4aVW;Vst;R11R10ReR6RdR5R3A9S6fS39R5U0A2S39R5U3A2R4S39R5U1M4A2R3A5R11R4S45R8S8S18G3A1A1R4A3RfR7S54S70S52R5A1S39R6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;SbG0S42Vsegs;S3fVsegs;RcR1A1S2fVW;Vst;Vtmax;A3S45R2S33VW;Vst;Vtmax;A3R1A3RaA5R8A3Fa;FrhoX;SbS42Vsegs;S3fVsegs;S4aVW;Vst;ReRdRbA5S84VW;Vst;Vtmax;Z8A4R1RaA5R8A3FrhoE;F_;F_;F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FJo;FKc;FA;").
Proof.
  assert (USED := (HCST, HXGL, HCSTM, HCSTS, law_res, Wa, Da, Wb, FB, NXS0, ECertS1, WC1, DC1, NXC1, IC1, R17, R11, R12, R13, R14, R15, NX1, NXS1f, ECertSf, FC1, RN, WRn, DKRn, NXRn, ENTn, IDn, R10, XC1, SK1)); clear USED.
  intros A Kc Jo rho tp Posts Q HW HUS HKc HPosts HJo HOK rhoE.
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  eapply etriple_conseq; [intros w Hw; exact (sec_inst nW st tmax Wa Da Wb FB A Kc rho tp w rhoE HW HUS HKc Hw) | intros w Hw; exact Hw |].
  apply (ecfg_cutS 4000%nat [0x7050c] GW [mkVNA (SS0 W st tmax) 1 (SLit 0)] [mkVNA (ES1 W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (SS0 W st tmax) rhoE HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact NXS0.
  - exact ECertS1.
  - intros E' rhoX HinE. destruct HinE as [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact (sec_cs1 nW st tmax WC1 DC1 NXC1 A Kc rho tp w rhoX Hw) | intros w Hw; right; exact Hw |].
    apply (esec_ecall A Kc Jo rho tp Q HW HUS HKc HJo); [|exact HOK].
    intros rhoY.
    exact (esec_tail_null nW st tmax CST XGL HCST HXGL HCSTM HCSTS NXS1f ECertSf RN WRn DKRn NXRn ENTn IDn A Kc rho tp Posts HUS HKc HPosts rhoY).
  - left. reflexivity.
Qed.
End SEC2E.
End SpineMallocSecE0.

(* [comment removed for export] *)
Module RebuildS.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "modulo"; "pow"; "sub"; "mul"; "of_nat"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "False"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "in_rangesZ"; "bview"; "ERRNO_A"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "PG"; "kPtrArrayReserve"; "kSpaceSize"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "aa_geom"; "aa_sec"; "AA"; "aa_cls"; "aa_ptr_committed"; "ag_pab"; "aa_q_global"; "aa_q_thread"; "ag_spacebeg"; "ageom"; "aa_Km"; "aa_live"; "ag_thread"; "class_state"; "sc_map_beg"; "sc_map_size"; "aa_Kf"; "aa_V"; "aa_cache_inited"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "cs_empty"; "mkAA"; "mkSC"; "qbatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.RebuildS"; "newZ"; "chg_s"; "secA"; "zimg"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "AInvA"; "quarantine_repr"; "kAllocBegMagic"; "nthZ"; "q_foot"; "@Corelib.Init.Datatypes"; "pair"; "Some"; "list"; "option"; "None"; "cons"; "length"; "prod"; "app"; "nat"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "secneeded"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv"; "pendS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "cls_foot"; "rt_zoneM"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition secA (A : AA) (ua nv : Z) : AA := ltac2:(tb__ "0|0|
S36S1eVA;A1S21VA;A1S30VA;A1S50S1dS1fVA;A1S4dS1dS37Vua;S56Vnv;A1S57Vnv;A1A3S52S1dA1A3A3S22VA;A1S4dS4fS0S0A2S48S0S0S2Vua;Z1800A2Vnv;A4S29VA;A1A3S25VA;A1S24VA;A1S31VA;A1S33VA;A1S32VA;A1S34VA;A1S2fVA;A1S28VA;A1S2eVA;A1Af").

Definition newZ (ua L : Z) (z : Z) : Prop := ltac2:(tb__ "0|1|
SdSaS1Vua;Vz;A2S3Vz;S2Vua;VL;A2A2A2SaS1S16Vua;A1M0Vz;A2S3Vz;S2G0S4VL;Z8A2A2A2A2A2").

Definition zimg (z : Z) : Prop := ltac2:(tb__ "0|0|
SdSaS1S42Vz;A2S3Vz;Zee044A2A2SdSaS1Zee048Vz;A2S3Vz;Zee070A2A2SdSbS0Vz;Z173660A3SaS1S14Vz;A2S3Vz;S2S14Z4A2A2A2A2A2A2").
Definition chg_s (G : ageom) (ua L pw blk : Z) (z : Z) : Prop := ltac2:(tb__ "0|1|
SdS3eVz;A1SdSaS1S2S2aVG;A1M0Zad0A2Vz;A2S3Vz;S2G0Zc60A2A2A2SdS3bVua;VL;Vz;A3SaS1Vpw;Vz;A2S3Vz;S2Vpw;Vblk;A2A2A2A2A2A2").

Lemma sh_apart : ltac2:(tb__ "0|6|
S0S0S0S0S0SbS0S5R5Z8M0A2Z0M1A3M2G2S1G1R6A2M3G3G3SdS1S2R8R7A2RaA2S1S2RaR9A2R8A2A2SaS1S16R9A1M4R7A2S3R7S2G4S4S2R8Z7A2G0A2A2A2A2ScSaS1S16RcA1M5R8A2S3R8S2G5S4RbG0A2A2A2A2A1F_;F_;F_;F_;F_;F_;F_;Fz;Flen;Flo;FL;Fua;").
Proof.
  intros ua L lo len z Hu HL HL0 Hlo Hlen Hs Hz X. unfold Sh in *.
  pose proof (Z.div_mod ua 8 ltac:(lia)) as DU. rewrite Hu, Z.add_0_r in DU.
  pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite HL, Z.add_0_r in DL.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (len + 7) 8 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)) as M2.
  destruct Hs as [Hs|Hs]; lia.
Qed.
Lemma sh_apart2 : ltac2:(tb__ "0|4|
S0S0S0S0S0SbS0S5R5Z8M0A2Z0M1A3M2G2S1G1R6A2SdS1R5R8A2S1S2R8R7A2R6A2A2SaS1S16R7A1R5A2S3R5S16R6A1A2A2ScSaS1S16RaA1M3R6A2S3R6S2G3S4R9G0A2A2A2A2A1F_;F_;F_;F_;F_;Fz;Fhi;Flo;FL;Fua;").
Proof.
  intros ua L lo hi z Hu HL HL0 Hs Hz X. unfold Sh in *.
  pose proof (Z.div_mod ua 8 ltac:(lia)) as DU. rewrite Hu, Z.add_0_r in DU.
  pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite HL, Z.add_0_r in DL.
  destruct Hs as [Hs|Hs].
  - pose proof (Z.div_le_mono hi ua 8 ltac:(lia) Hs). lia.
  - pose proof (Z.div_le_mono (ua + L) lo 8 ltac:(lia) Hs) as D. replace (ua + L) with ((ua / 8 + L / 8) * 8) in D by lia. rewrite Z.div_mul in D by lia. lia.
Qed.

Section Foot.
Variables (ua L : Z).
Hypothesis U8 : ua mod 8 = 0.
Hypothesis L8 : L mod 8 = 0.
Hypothesis L0 : 0 < L.
Hypothesis UI : IMG_HI <= ua.
Hypothesis UT : ua + L <= 140737479966720.
Hypothesis UB : ltac2:(tb__ "0|0|
SdS1S2Vua;VL;A2S18A2S1S17Vua;A2A2").

Lemma app_new : ltac2:(tb__ "0|1|
S0S0S0S1Z0R3A2M0G0S1S2R5R4A2Z7fffff800000A2SdS1S2R6R5A2Vua;A2S1S2Vua;VL;A2R6A2A2SdS1S2R7R6A2S18A2S1S17R7A2A2SaS1R8R6A2S3R6S2R8R7A2A2A2ScS3bVua;VL;R7A3A1F_;F_;F_;F_;F_;F_;Fz;Flen;Flo;").
Proof.
  intros lo len z Hlo Hlen Htop Hs Hb Hz [X|X]; [lia|].
  pose proof (sh_run_band2 ua (ua + L) z ltac:(unfold IMG_HI in UI; lia) ltac:(lia)) as BY.
  assert (E : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by lia. lia. }
  rewrite E in BY. specialize (BY X). lia.
Qed.
Lemma sh_new : ltac2:(tb__ "0|2|
S0S0S0S1Z0R3A2M0G0S1S2R5R4A2Z7fffff800000A2SdS1S2R6R5A2Vua;A2S1S2Vua;VL;A2R6A2A2SaS1S16R7A1M1R5A2S3R5S2G1S4S2R6Z7A2Z8A2A2A2A2ScS3bVua;VL;R6A3A1F_;F_;F_;F_;F_;Fz;Flen;Flo;").
Proof.
  intros lo len z Hlo Hlen Htop Hs Hz [X|X].
  - pose proof (sh_run_band lo len z Hlo Hlen Htop Hz) as BY. lia.
  - exact (sh_apart ua L lo len z U8 L8 ltac:(lia) Hlo Hlen Hs Hz X).
Qed.
Lemma sh2_new : ltac2:(tb__ "0|0|
S0S0S0S1Z0R3A2SaS1R4R3A2S1R3Z7fffff800000A2A2SdS1R4Vua;A2S1S2Vua;VL;A2R5A2A2SaS1S16R6A1R4A2S3R4S16R5A1A2A2ScS3bVua;VL;R5A3A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hlo Hhi Hs Hz [X|X].
  - pose proof (sh_run_band2 lo hi z Hlo Hhi Hz) as BY. lia.
  - exact (sh_apart2 ua L lo hi z U8 L8 ltac:(lia) Hs Hz X).
Qed.

Variable A : AA.
Variable m : bview.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis Hsep : live_sep A.
Hypothesis HI3 : inv3 A.
Hypothesis HPR : primary_repr m A.
Hypothesis HSR : secondary_repr m A.
Hypothesis SSP : ltac2:(tb__ "0|0|
S59S48S0S0Vua;VL;A4S48S0S0S26S1eVA;A1A1S2S1bZ1000A2A4A2").
Hypothesis SSX : ltac2:(tb__ "0|0|
S1dS54S1dR1S1fVA;A1A3S59S48S0S0Vua;VL;A4S48S0S0S2cR2A1S2dR2A1A4A2F_;Fch;").

Lemma space_new : ltac2:(tb__ "0|1|
S0SaS1S26S1eVA;A1A1M0R1A2S3R1S2S2G0S6Z2Z25A2A2Z1000A2A2A2ScS3bVua;VL;R2A3A1F_;Fz;").
Proof.
  intros z Hz. pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _ & TG). rewrite kSpaceSize_val in S2.
  unfold HIGH_SHADOW_END in S1. unfold sepZ in SSP. cbn [fst snd] in SSP. rewrite kSpaceSize_val in SSP.
  apply (app_new (ag_spacebeg (aa_geom A)) (2 ^ 37 + 4096) z); unfold SHADOW_BAND_HI, HIGH_SHADOW_END; lia.
Qed.
Lemma space_sh_new : ltac2:(tb__ "0|1|
S0S0S0S1S26S1eVA;A1A1M0R3A2S1R4R3A2S1R4S2S2G0S6Z2Z25A2A2Z1000A2A2SaS1S16R6A1R4A2S3R4S16R5A1A2A2ScS3bVua;VL;R5A3A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z H1 H2 H3 Hz. pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _ & TG). rewrite kSpaceSize_val in S2.
  unfold HIGH_SHADOW_END in S1. unfold sepZ in SSP. cbn [fst snd] in SSP. rewrite kSpaceSize_val in SSP.
  apply (sh2_new lo hi z); lia.
Qed.
Lemma chunk_new : ltac2:(tb__ "0|2|
S51S1dS0SbS4bS1dA1S55S1dS1fVA;A1R3A3S49S1dR2A2A3SdSaS1S2cR3A1M0R2A2S3R2S2G0S2dR3A1A2M1A2A2SaS1S16G0A1R2A2S3R2S16G1A1A2A2A2ScS3bVua;VL;R3A3A1F_;F_;Fz;Fch;Fi;").
Proof.
  intros i ch z Hi Hz. destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
  pose proof (topG_range (aa_geom A)) as TG. pose proof (SSX ch (nth_error_In _ _ Hi)) as SX. unfold sepZ in SX. cbn [fst snd] in SX.
  pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; lia)) as BI. unfold IMG_HI in BI. destruct D10 as (_ & _ & _ & _ & DB). unfold PG in D8.
  destruct Hz as [Hz|Hz].
  - apply (app_new (sc_map_beg ch) (sc_map_size ch) z); lia.
  - apply (sh2_new (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); lia.
Qed.

Lemma live_foot_new : ltac2:(tb__ "0|1|
S0S0S0S54S4fS0S0A2S48S0S0R3R2A4S29VA;A1A3SdSaS1S7R4S1cR3A1A2R2A2S3R2S2R4R3A2A2A2SaS1S16R4A1M0R2A2S3R2S2G0S4S2R3Z7A2Z8A2A2A2A2A2ScS3bVua;VL;R3A3A1F_;F_;Fz;Fn;Fb;").
Proof.
  intros b n z Hin Hz.
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct (Hsep b n Hin) as (L1 & L2 & L3 & _). unfold IMG_HI in L2. fold G in L3.
  pose proof (rz_bound n) as RZB.
  pose proof HI3 as (_ & LIV3 & _).
  unfold sepZ in SSP. cbn [fst snd] in SSP. fold G SB in SSP. rewrite kSpaceSize_val in SSP.
  destruct (LIV3 b n Hin) as [PRM | (ch & Hch & Eb & Esz)].
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact L1|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. set (c := ClassID (needed n)) in D1, D2, D3, Y3.
    destruct HPR as (_ & _ & _ & PC). pose proof (PC c D1) as PC'. fold G in PC'. unfold class_repr in PC'.
    destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _ & _).
    destruct (LV b n Hin PRM eq_refl) as (V1 & V2 & V3). fold SB in V1, V2, V3.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3.
    assert (ERB : region_beg SB c = SB + c * 2 ^ 32) by reflexivity. rewrite ERB in V1, V3.
    assert (BLO : SB <= b - rz n /\ b + n <= SB + 2 ^ 37) by (clear -V1 V3 M2 M3 D1 Y1 Y3 Hn; nia).
    destruct Hz as [Hz|Hz].
    + apply space_new. fold G SB. clear -Hz BLO. lia.
    + pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). fold G SB in S1, S2. rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
      apply (sh_new b n z); [clear -L2; lia | clear -L1; lia | clear -L3 ACV; lia | clear -BLO SSP RZB; lia | exact Hz].
  - destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in D6, D8, D11, Eb.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    pose proof (SSX ch Hch) as SX. unfold sepZ in SX. cbn [fst snd] in SX.
    assert (INB : sc_map_beg ch <= b - rz n /\ b + n <= sc_map_beg ch + sc_map_size ch) by (clear -Eb Esz RZB D8 D11 RU1 RU2 L1; lia).
    destruct Hz as [Hz|Hz].
    + apply (chunk_new i ch z Hi). left. clear -Hz INB. lia.
    + apply (sh_new b n z); [clear -L2; lia | clear -L1; lia | clear -L3 ACV; lia | clear -INB SX RZB; lia | exact Hz].
Qed.

Lemma cls_foot_new : ltac2:(tb__ "0|3|
S0SaS1Z1R1A2S1R1Z1eA2A2S0S5eS1eVA;A1M0R3S46S2bS21VA;A1R3S35A4R1A4ScSaS1S2S2S2aG0A1Zd0A2S8Z50M1R4A2A2M2R2A2S3R2S2G2G1A2A2A2A1ScS3bVua;VL;R3A3A1F_;F_;Fz;F_;Fc;").
Proof.
  intros c Hc z Hz NT.
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as X. fold G in X. unfold class_repr in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
  pose proof (geom_old _ HG) as Y. rewrite kSpaceSize_val in Y. unfold HIGH_SHADOW_END in Y. fold G SB in Y.
  destruct Y as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
  unfold cls_foot in Hz. cbn zeta in Hz. fold G SB in Hz. unfold region_info, free_array, region_beg in Hz.
  unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize, kRegionInfoStride, kSpaceSize in *.
  destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
  - apply space_new. fold G SB. clear -Hz Hc. lia.
  - apply space_new. fold G SB. clear -Hz Hc M5 M6. nia.
  - apply space_new. fold G SB. clear -Hz Hc M1 M2 M3. nia.
  - apply (space_sh_new (SB + c * 2 ^ 32) (SB + c * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) c cs_empty)) z); fold G SB; [clear -Hc; nia | clear -M1 M2; lia | clear -Hc M1 M2 M3; nia | exact Hz].
  - exfalso. exact (NT Hz).
Qed.

Lemma q_foot_new : ltac2:(tb__ "0|0|
S44Vm;VA;A2S0S47VA;R1A2ScS3bVua;VL;R2A3A1F_;Fz;F_;").
Proof.
  intros (Q1 & _) z Hq.
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  pose proof HPR as (_ & _ & _ & PC).
  assert (REG : forall c, 1 <= c <= 30 -> SB <= region_beg SB c /\ region_beg SB c + cs_allocated_user (nthZ (aa_cls A) c cs_empty) <= SB + 2 ^ 37).
  { intros c Hc. pose proof (PC c Hc) as X. fold G SB in X. unfold class_repr in X.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _).
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in *. unfold region_beg, kRegionSize. clear -Hc M1 M2 M3. nia. }
  assert (GSB : 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G).
  { pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G SB in X. clear -X. tauto. }
  unfold sepZ in SSP. cbn [fst snd] in SSP. fold G SB in SSP. rewrite kSpaceSize_val in SSP.
  unfold q_foot in Hq. apply Exists_exists in Hq as (qb & Hqb & Hz).
  pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7). fold G SB in B7.
  destruct Hz as [Hz|Hz].
  { destruct B7 as (x & Ex & X0 & _ & XA). destruct (REG 24 ltac:(lia)) as [R1 R2]. unfold kQuarantineBatchSize in *.
    apply space_new. fold G SB. clear -Hz Ex X0 XA R1 R2. lia. }
  apply Exists_exists in Hz as (it & Hit & Hz). destruct (In_nth_error _ _ Hit) as [i Hi]. destruct (B6 i it Hi) as [_ IT].
  destruct IT as (J1 & J2 & _ & _ & _ & _ & _ & _ & JP & JS & _). unfold IMG_HI in J1. fold G SB in JP.
  pose proof (rz_bound (snd it)) as RZ. set (u := fst it) in *. set (n := snd it) in *.
  destruct (is_primary n) eqn:PRM.
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact J2|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. destruct (JP eq_refl) as (V1 & V2 & V3). fold n in V1, V2, V3.
    set (c := ClassID (needed n)) in *. destruct (REG c D1) as [R1 R2].
    assert (BLO : SB <= u - rz n /\ u + n <= SB + 2 ^ 37) by (clear -V1 V3 R1 R2 Y1 Y3 Hn; nia).
    destruct Hz as [Hz|Hz].
    + apply space_new. fold G SB. clear -Hz BLO J2. lia.
    + apply (sh_new u n z); [clear -J1; lia | clear -J2; lia | clear -BLO GSB ACV; lia | clear -BLO SSP RZ; lia | exact Hz].
  - destruct (JS eq_refl) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [j Hj].
    destruct HSR as (SC1 & _). destruct (SC1 j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D12. unfold PG in *.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    pose proof (SSX ch Hch) as SX. unfold sepZ in SX. cbn [fst snd] in SX.
    assert (INB : sc_map_beg ch <= u - rz n /\ u + n <= sc_map_beg ch + sc_map_size ch) by (clear -Eu Esz RZ D8 D11 RU1 RU2 J2; lia).
    destruct Hz as [Hz|Hz].
    + apply (chunk_new j ch z Hj). left. clear -Hz INB J2. lia.
    + apply (sh_new u n z); [clear -J1; lia | clear -J2; lia | clear -INB D12 ACV; lia | clear -INB SX RZ; lia | exact Hz].
Qed.
End Foot.

Lemma quarantine_repr_sec_mono : ltac2:(tb__ "0|2|
S13S20S20SbS27S1eR1A1S1eR2A1A3SbS4aS2bA1S21R2A1S21R3A1A3SbS4aS38A1M0S25R3A1S25R4A1A3SbG0S24R4A1S24R5A1A3S1dS54S1dR1S1fR7A1M1A3S54S1dR2G1A3F_;Fch;S44R8R7A2S44R9R7A2F_;F_;F_;F_;F_;F_;FA';FA;Fm;").
Proof.
  intros m A A' EG EC ET EGq HS (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  unfold quarantine_repr. rewrite EG, ET, EGq.
  split; [|split; [exact Q2 | split; [exact Q3 | split; [exact Q4 | split; [exact Q5 | split; [exact Q6 | split; [exact Q7 | split; [exact Q8 | exact Q9]]]]]]]].
  apply Forall_forall. intros qb Hqb. pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
  unfold batch_repr. rewrite EG, EC.
  split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [|exact B7].
  intros i it Hi. destruct (B6 i it Hi) as [I1 I2]. split; [exact I1|].
  unfold q_item_ok in I2 |- *. cbn zeta in I2 |- *. rewrite EG, EC.
  destruct I2 as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11).
  split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|]. split; [exact J5|]. split; [exact J6|]. split; [exact J7|]. split; [exact J8|].
  split; [exact J9|]. split; [|exact J11].
  intros HP. destruct (J10 HP) as (ch & Hch & X). exists ch. split; [exact (HS ch Hch) | exact X].
Qed.

Lemma nth_error_snoc : forall {T} (l : list T) (x y : T) i, nth_error (l ++ [x]) i = Some y ->
  (nth_error l i = Some y /\ (i < length l)%nat) \/ (i = length l /\ y = x).
Proof.
  intros T l x y i H. destruct (Nat.lt_ge_cases i (length l)) as [Lt|Ge].
  - rewrite nth_error_app1 in H by exact Lt. left. exact (conj H Lt).
  - rewrite nth_error_app2 in H by exact Ge. destruct (i - length l)%nat as [|k] eqn:E; cbn in H.
    + right. split; [lia | congruence].
    + destruct k; discriminate H.
Qed.

Theorem sec_rebuild : ltac2:(tb__ "0|10|
S20S3aS3aS4aS40Q40M0A1A1S58S0S0S0S43S53R8R7R5R4A5SaS1Zfc01R4A2S3R4S6Z2M1Z27A2A2A2S1eRaA1S27S56R6A1S0S9S4eS1dS1fRcA1A2A1S0S2R7Z1800A2S0S2S23R4A1S8Z8M2R2A2A2S0S15S53S39RdA1A2S13S15S53S39RfA1A2S13S5aR11RbR6RdA4S1G2RbA2S1S2S8G2R7A2RcA2S22R13A1A2S1S2R8Z1M3A2S28R14A1A2S10R6S11RfU8M4RfA3A2S10R7S11S2R10G2A2G4RbA3A2S10R8S11S2R11Z10M5A2G4S57R12A1A3A2S10R9S11S2R12Z18M6A2G4RcA3A2S10RaS11RbG4R13A3A2S10RbS11S42G4S19A3A2S10RcS11S2S42G2A2G4S23R11A1A3A2S10RdS11S2S42G5A2G4S23R12A1A3A2S10ReS11S2S42G6A2G4S1aA3A2S10RfS11S2S42Z30A2G4S4S22R1eA1G2A2A3A2S10R10S11S2S42Z38A2G4S2R13G3A2A3A2S10R11S11Zee040U4M7Z0M8A3A2SbS4bS40Q8M9A1MaA1MbR12S7R14G5A2A1S49GaS3fG9G1A2A2A3S10R13S11S7R15ZcA2G7S5R1dS6G1Z20A2McA2A3A2S10R14S11S7R16ZeA2U2S4R1eGcA2A3A2SfGaGaSaSbGbR16S7R18ZfA2A1S49GaR1A2MdA3SbS0S5S41G9R1A2Z4A2G3A3A2Lt;A2S10R16S11S2R1fZ1000A2G4S45A3A2S10R17S11S2R20Z1008A2G4S7R19G5A2A3A2S0SaS1G8R1A2S3R1S4R23G2A2A2A2SbGbR1aS2S16R1cA1MeR2A2A1S49GaS3fG9G8A2A2A3F_;Fg;ScSbS0S5R23G2A2G8A3A1SbGbR1aS2GeS4R24G2A2A2A1S49GaS3fG9S5R24G2A2A2A2A3F_;S0S3cR20R24R1fR1cR23R1A6SfGaGaSbGbR1dR3A1GdA3Lb;A2F_;Fz;S0ScS3cR21R25R20R1dR24R1A6A1SbGbR1dR2A1R1cR2A1A3F_;Fz;S0SaS1S18R1A2S3R1S17A2A2ScSbGbS39R2cS3fG0R2A2A2S4cGaA1MfA3A1ScSbGbS39R2cS3fG0R3A2A2GfA3A1F_;F_;Fa;S43S53S3dR2cR26R27A3R2aR29R28A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TvE;Tv3;Tpw;Tub;Tidx;TL;TG;F_;F_;Fblk;Fua;Fnv;Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md nv ua blk HA Hnv. cbn zeta.
  intros HPD Hblk HROOM HKM C0 C8 C16 C24 CPW CI0 CI8 CI16 CI24 C48 C56 CMU VH2 VHN VH0 VH1 VMG0 VMG8 VZ VP PRES VO DEFB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  set (vE := view segsA (rm rhoE)) in *. set (v3 := view segsA (rm rho3)) in *.
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (L := secmapsize nv) in *. set (idx := Z.of_nat (length (aa_sec A))) in *.
  set (ub := ua + 6144) in *. set (pw := ag_pab G + 8 * idx) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI). fold G T in TB, TI. fold G in FB, CB, DB, CI, DI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in FB, TB, CB, DB, TI, CI, DI.
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB). fold G L in PM, PL0, PDI, ST, SC, SD, SF, SS, SP, SX, SDB. fold T in ST.
  pose proof (secmapsize_bounds nv ltac:(clear -Hnv; lia)) as [SMB SMM]. fold L in SMB, SMM. unfold PG in SMM, PAL.
  pose proof (dyn_in_big _ _ _ PDI ltac:(clear -SMB; lia)) as UI. destruct PDI as (_ & _ & PDT & _ & PDB).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5). fold G in P1, P2, P3. fold idx in P4.
  assert (U8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X. rewrite PAL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (L8 : L mod 8 = 0).
  { pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (L / 4096)) with ((512 * (L / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (UT : ua + L <= 140737479966720) by (clear -PDT ACV; lia).
  assert (ESHL : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }
  assert (RUNB : forall z, Sh ua <= z < Sh ua + L / 8 -> SHADOW_BAND_LO <= z < SHADOW_BAND_HI).
  { intros z Hz. apply (sh_run_band2 ua (ua + L) z); [unfold IMG_HI in UI; clear -UI; lia | clear -UT PL0; lia | rewrite ESHL; exact Hz]. }
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in RUNB, PDB.

  assert (APPN : forall lo len z, 0 <= lo -> 0 <= len -> lo + len <= 140737479966720 -> sepZ (ua, L) (lo, len) ->
                 (lo + len <= 0x7fff7000 \/ 0x10007fff8000 <= lo) -> lo <= z < lo + len -> ~ newZ ua L z).
  { intros lo len z H1 H2 H3 H4 H5 Hz. apply (app_new ua L L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) lo len z H1 H2 H3);
      [unfold sepZ in H4; cbn [fst snd] in H4; clear -H4; lia | unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact H5 | exact Hz]. }
  assert (NEW_img : forall z, z < IMG_HI -> ~ newZ ua L z).
  { intros z Hz [X|X]; [clear -X UI Hz; lia | pose proof (RUNB z X) as Y; unfold IMG_HI in Hz; clear -Y Hz; lia]. }
  assert (NEW_T : forall z, T <= z < T + 0x1000 -> ~ newZ ua L z).
  { intros z Hz. apply (APPN T 0x1000 z); [clear -G4; lia | clear; lia | clear -G5 ACV; lia | exact ST | clear -TB; lia | exact Hz]. }
  assert (NEW_pab : forall z, ag_pab G <= z < ag_pab G + kPtrArrayReserve -> ~ newZ ua L z).
  { intros z Hz. unfold kPtrArrayReserve in *. apply (APPN (ag_pab G) (2 ^ 23) z); [unfold IMG_HI in P1; clear -P1; lia | clear; lia | clear -P2 ACV; lia | exact SP | | exact Hz].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in P3. clear -P3. lia. }
  assert (PWZ : forall z, pw <= z < pw + blk -> ag_pab G <= z < ag_pab G + kPtrArrayReserve).
  { intros z Hz. unfold pw in Hz. pose proof (Zle_0_nat (length (aa_sec A))) as NN. fold idx in NN. clear -Hz HROOM P4 NN. lia. }
  assert (ZD : forall z, chg_s G ua L pw blk z \/ ~ chg_s G ua L pw blk z) by (intros z; unfold chg_s, zimg, newZ; clear; lia).

  assert (AGI : forall z, z < IMG_HI -> ~ zimg z -> ~ (T + 2768 <= z < T + 3168) -> v3 z = vE z).
  { intros z H1 H2 H3. apply VO. intros [X|[X|[X|X]]]; [exact (H2 X) | exact (H3 X) | exact (NEW_img z H1 X) |].
    pose proof (PWZ z X) as Y. clear -Y H1 P1. lia. }
  assert (AGH : forall z, IMG_HI <= z -> ~ (T + 2768 <= z < T + 3168) -> ~ newZ ua L z -> ~ (pw <= z < pw + blk) -> v3 z = vE z).
  { intros z H1 H2 H3 H4. apply VO. intros [X|[X|[X|X]]]; [|exact (H2 X) | exact (H3 X) | exact (H4 X)].
    unfold zimg, SEC_INST, ERRNO_A, IMG_HI in *. clear -X H1. lia. }
  idtac "sr:1".

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz.
    unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin).
    unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
    unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
    - unfold rtc_cells_img in Hc. apply AGI; unfold IMG_HI, zimg, SEC_INST, ERRNO_A;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; clear -X Y TI; lia|]); destruct Hc.
    - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc.
      assert (ZZ : (T <= z < T + 288) \/ (ag_ctx G <= z < ag_ctx G + 0x1000) \/ (ag_dtls G <= z < ag_dtls G + 0x1000) \/ (ag_fsb G <= z < ag_fsb G + 97)).
      { repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; fold G T in X, Y; clear -X Y; lia|]). destruct Hc. }
      clear Hc X Y.
      assert (NZ : ~ newZ ua L z).
      { destruct ZZ as [Z1|[Z1|[Z1|Z1]]].
        - apply NEW_T. clear -Z1. lia.
        - apply (APPN (ag_ctx G) 0x1000 z); [clear -G6; lia | clear; lia | clear -G7 ACV; lia | exact SC | clear -CB; lia | exact Z1].
        - apply (APPN (ag_dtls G) 0x1000 z); [clear -G8; lia | clear; lia | clear -G9 ACV; lia | exact SD | clear -DB; lia | exact Z1].
        - rewrite FS_total_val in SF, FB. apply (APPN (ag_fsb G) 11571200 z); [clear -G2; lia | clear; lia | clear -G3 ACV; lia | exact SF | clear -FB; lia | clear -Z1; lia]. }
      assert (NP : ~ (pw <= z < pw + blk)).
      { intros X. pose proof (PWZ z X) as Y. destruct HI3 as ((_ & _ & _ & _ & PT & PF & PC & PD) & _). fold G T in PT, PF, PC, PD. rewrite FS_total_val in PF.
        unfold kPtrArrayReserve in *. clear -Y ZZ PT PF PC PD. lia. }
      destruct (Z_lt_dec z IMG_HI) as [LO|HI].
      + apply AGI; [exact LO | | clear -ZZ G10 G13 G14; intros X; unfold IMG_HI in *; lia].
        unfold zimg, SEC_INST, ERRNO_A. unfold IMG_HI in LO. clear -ZZ LO TI CI DI G2. intros X. lia.
      + apply AGH; [clear -HI; lia | | exact NZ | exact NP]. clear -ZZ G10 G13 G14. intros X. lia. }
  idtac "sr:2".

  assert (FZ : forall z, chg_s G ua L pw blk z -> fs_footb G z = false).
  { intros z [X|[X|[X|X]]].
    - apply (fs_footb_img G z HG). unfold zimg, SEC_INST, ERRNO_A in X. clear -X. lia.
    - apply (fs_footb_T G z HG). fold T. clear -X. lia.
    - rewrite FS_total_val in SF, FB. unfold sepZ in SF. cbn [fst snd] in SF.
      apply (fs_footb_false_intro G z); rewrite ?FS_frames_off_val, ?FS_total_val, ?FS_kFlagsOffset_val.
      + destruct X as [X|X]; [clear -X SF; lia | pose proof (RUNB z X) as Y; clear -Y FB; lia].
      + destruct X as [X|X]; [clear -X SF; lia | pose proof (RUNB z X) as Y; clear -Y FB; lia].
      + destruct X as [X|X].
        * pose proof (sh_run_band2 (ag_fsb G + 36864) (ag_fsb G + 11571200)) as BY.
          destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [Lz|Lz]; [left; exact Lz|right].
          destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
          specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -Lz R; lia)).
          unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. clear -BY X PDB. lia.
        * destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [Lz|Lz]; [left; exact Lz|right].
          destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
          apply (sh_apart2 ua L (ag_fsb G + 36864) (ag_fsb G + 11571200) z U8 L8 ltac:(clear -PL0; lia) ltac:(clear -SF; lia) ltac:(clear -Lz R; lia) X).
    - pose proof (PWZ z X) as Y. destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      apply (fs_footb_false_intro G z); rewrite ?FS_frames_off_val, ?FS_total_val, ?FS_kFlagsOffset_val.
      + clear -Y PF. lia.
      + clear -Y PF. lia.
      + pose proof (sh_run_band2 (ag_fsb G + 36864) (ag_fsb G + 11571200)) as BY.
        destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [Lz|Lz]; [left; exact Lz|right].
        destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
        specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -Lz R; lia)).
        clear -BY Y P3. unfold kPtrArrayReserve in *. lia. }

  assert (HFS : fs_inv (restrictv (fs_footb G) v3) (secA A ua nv)).
  { rewrite (restrictv_ext (fs_footb G) vE v3).
    2: { intros z Hz. apply VO. intros Zz. rewrite (FZ z Zz) in Hz. discriminate Hz. }
    exact HF. }
  idtac "sr:3".

  set (mE := maskv (fs_footb G) vE) in *. set (m3 := maskv (fs_footb G) v3).
  assert (AGm : forall z, ~ chg_s G ua L pw blk z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. apply VO. exact Hz. }
  assert (AGmI : forall z, z < IMG_HI -> ~ zimg z -> ~ (T + 2768 <= z < T + 3168) -> m3 z = mE z).
  { intros z H1 H2 H3. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. exact (AGI z H1 H2 H3). }
  assert (AGmH : forall z, IMG_HI <= z -> ~ (T + 2768 <= z < T + 3168) -> ~ newZ ua L z -> ~ (pw <= z < pw + blk) -> m3 z = mE z).
  { intros z H1 H2 H3 H4. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. exact (AGH z H1 H2 H3 H4). }
  assert (CHm : forall z, chg_s G ua L pw blk z -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. exact (FZ z Hz). }
  assert (PRm : forall z, chg_s G ua L pw blk z -> exists b, m3 z = Some b).
  { intros z Hz. rewrite (CHm z Hz). exact (PRES z Hz). }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZD z) as [Hc|Hn].
    - exact (PRm z Hc).
    - rewrite (AGm z Hn). exact (Hp z Hz). }
  assert (CELL3 : forall a w v, (forall k, (k < w)%nat -> chg_s G ua L pw blk (a + Z.of_nat k)) -> cell_ok v3 (mkACell a w v) -> cell_ok m3 (mkACell a w v)).
  { intros a w v Hk Hc k Hkw. cbn [c_addr c_w c_val] in *. rewrite (CHm _ (Hk k Hkw)). exact (Hc k Hkw). }

  assert (SSP' : sepZ (ua, L) (ag_spacebeg (aa_geom A), kSpaceSize + 4096)) by exact SS.
  pose proof (live_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A mE HG Hsep HI3 HPR HSR SSP' SX) as LFN.
  pose proof (cls_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A mE HG HPR SSP') as CFN.
  pose proof (q_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A mE HG HPR HSR SSP' SX HQR) as QFN.
  pose proof (chunk_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A mE HSR SX) as CHN.
  assert (NPWpab : forall z, ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> ~ (pw <= z < pw + blk)) by (intros z H X; exact (H (PWZ z X))).

  assert (NB : ub + nv + 2048 <= ua + L /\ nv / 8 <= L / 8 - 1024 /\ rz nv = 2048 /\ is_primary nv = false).
  { split; [|split; [|split; [apply rz_large; clear -Hnv; lia | apply not_primary_large; clear -Hnv; lia]]].
    - unfold ub, L, secmapsize, secneeded, PG. pose proof (round_up_ge nv 8 ltac:(clear; lia)) as R1.
      pose proof (round_up_ge (round_up nv 8 + 4096) 4096 ltac:(clear; lia)) as R2. clear -R1 R2. lia.
    - unfold L, secmapsize, secneeded, PG. pose proof (round_up_ge nv 8 ltac:(clear; lia)) as R1.
      pose proof (round_up_ge (round_up nv 8 + 4096) 4096 ltac:(clear; lia)) as R2.
      pose proof (Z.div_le_mono (nv + 8192) (round_up (round_up nv 8 + 4096) 4096 + 4096) 8 ltac:(clear; lia) ltac:(clear -R1 R2; lia)) as D.
      replace (nv + 8192) with (nv + 1024 * 8) in D by (clear; lia). rewrite Z.div_add in D by (clear; lia). clear -D. lia. }
  destruct NB as (NB1 & NB2 & ERZ & ENP).
  assert (ESHub : Sh ub = Sh ua + 768).
  { unfold Sh, ub. replace (ua + 6144) with (ua + 768 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear. lia. }
  assert (INnew : forall z, ua <= z < ua + L -> chg_s G ua L pw blk z) by (intros z Hz; right; right; left; left; exact Hz).
  assert (INrun : forall z, Sh ua <= z < Sh ua + L / 8 -> chg_s G ua L pw blk z) by (intros z Hz; right; right; left; right; exact Hz).
  idtac "sr:4".

  assert (HLS : live_sep (secA A ua nv)).
  { intros b n Hin. cbn [aa_live secA] in Hin. cbn [aa_geom secA]. fold G. destruct Hin as [E|Hin]; [|exact (Hsep b n Hin)].
    injection E as <- <-. fold ub. unfold sepZ in SF, ST, SC, SD. cbn [fst snd] in SF, ST, SC, SD. fold T in ST |- *.
    split; [clear -Hnv; lia|]. split; [unfold ub; clear -UI; lia|]. split; [clear -NB1 PDT; lia|].
    split; [unfold ub; clear -SF NB1; lia|]. split; [unfold ub; clear -ST NB1; lia|]. split; [unfold ub; clear -SC NB1; lia|]. split; [unfold ub; clear -SD NB1; lia|].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. unfold ub. clear -PDB NB1. lia. }
  assert (HLB : live_block_repr m3 (secA A ua nv)).
  { intros b n Hin. cbn [aa_live secA] in Hin. destruct Hin as [E|Hin].
    - injection E as <- <-. fold ub.
      assert (CU : forall z, ua <= z < ua + L -> m3 z = v3 z) by (intros z Hz; apply CHm; apply INnew; exact Hz).
      assert (CS : forall z, Sh ua <= z < Sh ua + L / 8 -> m3 z = v3 z) by (intros z Hz; apply CHm; apply INrun; exact Hz).
      pose proof (Z.div_pos nv 8 ltac:(clear -Hnv; lia) ltac:(clear; lia)) as DP.
      split; [rewrite CU by (unfold ub; clear -SMB; lia); exact VH2|].
      split; [apply CELL3; [intros k Hk; apply INnew; unfold ub; clear -Hk SMB; lia | exact VHN]|].
      split; [apply CELL3; [intros k Hk; apply INnew; unfold ub; clear -Hk SMB; lia | exact VH0]|].
      split; [split|split].
      + intros g Hg. rewrite CS by (rewrite ESHub; clear -Hg NB2; lia). exact (VZ g Hg).
      + intros Hm. rewrite CS by (rewrite ESHub; clear -DP NB2; lia). exact (VP Hm).
      + right. rewrite ERZ. replace (ub - 2048) with (ua + 4096) by (unfold ub; clear; lia). replace (ua + 4096 + 8) with (ua + 4104) by (clear; lia).
        split; apply CELL3; first [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | assumption].
      + destruct VH1 as (t & Ht & Hm4). exists t. split; [rewrite CU by (unfold ub; clear -SMB; lia); exact Ht | exact Hm4].
    - destruct (Hlive b n Hin) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
      assert (NO : forall z, (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> m3 z = mE z).
      { intros z Hz. destruct (live_foot mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as (X & Y & _). fold G T in Y.
        pose proof (live_foot_pab mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as Z1. fold G in Z1.
        apply AGmH; [exact X | clear -Y; lia | exact (LFN b n z Hin Hz) | exact (NPWpab z Z1)]. }
      pose proof (rz_bound n) as RZ. destruct (Hsep b n Hin) as (L1 & _).
      pose proof (Z.div_le_mono n (n + 7) 8 ltac:(clear; lia) ltac:(clear; lia)) as DL. pose proof (Z.div_pos n 8 ltac:(clear -L1; lia) ltac:(clear; lia)) as DP.
      split; [rewrite NO by (left; clear -RZ L1; lia); exact B1|].
      split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
      split; [eapply cell_ok_agree; [|exact B3]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
      split; [split|split].
      + intros g Hg. rewrite NO by (right; clear -Hg DL; lia). exact (B4 g Hg).
      + intros Hm. rewrite NO; [exact (B5 Hm)|]. right.
        replace ((n + 7) / 8) with (n / 8 + 1) by (apply Z.div_unique with (n mod 8 - 1); [pose proof (Z.mod_pos_bound n 8); clear -Hm H; lia | pose proof (Z.div_mod n 8); clear -H; lia]).
        clear -DP. lia.
      + apply (alloc_magic_ok_agree mE m3); [intros z Hz; apply NO; left; clear -Hz L1; lia | clear -RZ; lia | exact B6].
      + destruct B7 as (t & Ht & Hm4). exists t. split; [rewrite NO by (left; clear -RZ L1; lia); exact Ht | exact Hm4]. }
  idtac "sr:5".

  assert (LIVM : forall z, in_rangesZ (aa_live A) z -> in_rangesZ (aa_live (secA A ua nv)) z).
  { intros z (b & n & Hbn & Hz). exists b, n. split; [cbn [aa_live secA]; right; exact Hbn | exact Hz]. }
  assert (HPR' : primary_repr m3 (secA A ua nv)).
  { destruct HPR as (Q1 & Q2 & Q3' & P4'). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3'|].
    intros cl Hc. change (aa_geom (secA A ua nv)) with G. change (aa_cls (secA A ua nv)) with (aa_cls A).
    apply (class_repr_agree mE m3 G A (secA A ua nv) cl); [exact Hc | reflexivity | | reflexivity | | exact LIVM | | exact (P4' cl Hc)].
    - unfold secA. rewrite (live_ids_cons G A (ua + 6144) nv cl). rewrite ENP. reflexivity.
    - intros b n Hin HP _. cbn [aa_live secA] in Hin. destruct Hin as [E|Hin]; [|exact Hin]. injection E as <- <-. rewrite ENP in HP. discriminate HP.
    - intros z Hz.
      pose proof (cls_foot_pab mE A cl HG HI3 (conj Q1 (conj Q2 (conj Q3' P4'))) HSR Hc z Hz) as Y. fold G in Y.
      assert (TAIL : ~ (T + 0xd0 + 80 * cl <= z < T + 0xd0 + 80 * cl + 80) -> m3 z = mE z).
      { intros NTe. pose proof (CFN cl Hc z Hz NTe) as NZ.
        assert (ZH : IMG_HI <= z /\ ~ (T + 2768 <= z < T + 3168)).
        { pose proof (P4' cl Hc) as PCX. fold G in PCX. unfold class_repr in PCX.
          destruct PCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
          unfold cls_foot in Hz. cbn zeta in Hz. fold G T in Hz. destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]]; [| | | |exfalso; exact (NTe Hz)].
          all: pose proof (geom_old _ HG) as X; rewrite kSpaceSize_val in X; unfold HIGH_SHADOW_END in X; fold G in X;
               destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _);
               destruct HI3 as ((T3 & _) & _); fold G T in T3; rewrite kSpaceSize_val in T3;
               unfold region_info, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kSpaceSize, kRegionInfoStride, Sh, SHADOW_OFF, IMG_HI in *.
          - clear -Hz Hc GS1 T3. lia.
          - unfold kUserMapSize in *. clear -Hz Hc GS1 T3 M5 M6. nia.
          - unfold kUserMapSize in *. clear -Hz Hc GS1 T3 M1 M2 M3. nia.
          - pose proof (Z.div_pos (ag_spacebeg G + cl * 2 ^ 32) 8 ltac:(clear -Hc GS1; lia) ltac:(clear; lia)) as D2.
            unfold kUserMapSize in *.
            pose proof (Z.div_le_mono (ag_spacebeg G + cl * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) cl cs_empty)) 140737479966720 8 ltac:(clear; lia) ltac:(clear -Hc M1 M2 M3 GS2 ACV; nia)) as D1.
            change (140737479966720 / 8) with 17592184995840 in D1. clear -Hz D1 D2 TB. lia. }
        apply AGmH; [exact (proj1 ZH) | exact (proj2 ZH) | exact NZ | exact (NPWpab z Y)]. }
      destruct (Z_le_dec (T + 0xd0 + 80 * cl) z) as [GE|LT]; [destruct (Z_lt_dec z (T + 0xd0 + 80 * cl + 80)) as [LT2|GE2]|].
      +
        assert (ZT : T <= z < T + 0x1000) by (clear -GE LT2 Hc; lia).
        destruct (Z_lt_dec z IMG_HI) as [LO|HI].
        * apply AGmI; [exact LO | unfold zimg, SEC_INST, ERRNO_A; unfold IMG_HI in LO; clear -ZT LO TI; intros X; lia | clear -GE LT2 Hc; lia].
        * apply AGmH; [clear -HI; lia | clear -GE LT2 Hc; lia | exact (NEW_T z ZT) | exact (NPWpab z Y)].
      + apply TAIL. clear -GE2. lia.
      + apply TAIL. clear -LT. lia. }
  idtac "sr:6".

  assert (AGpabOld : forall z, ag_pab G <= z < pw -> m3 z = mE z).
  { intros z Hz. pose proof (Zle_0_nat (length (aa_sec A))) as NN. fold idx in NN.
    assert (ZP : ag_pab G <= z < ag_pab G + kPtrArrayReserve) by (unfold pw in Hz; clear -Hz HROOM P4 NN Hblk; lia).
    destruct HI3 as ((_ & _ & _ & _ & PT & _) & _). fold G T in PT.
    apply AGmH; [clear -ZP P1; lia | clear -ZP PT; unfold kPtrArrayReserve in *; lia | exact (NEW_pab z ZP) | clear -Hz; lia]. }
  assert (HSR' : secondary_repr m3 (secA A ua nv)).
  { pose proof HSR as (S1 & SPT & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
    unfold secondary_repr. cbn [aa_geom aa_sec aa_ptr_committed aa_live secA]. fold G.
    assert (ELEN : Z.of_nat (length (aa_sec A ++ [mkSC ua L (secneeded nv)])) = idx + 1) by (rewrite length_app; cbn [length]; unfold idx; clear; lia).
    fold L. rewrite ELEN.
    split.
    { intros i ch Hi. apply nth_error_snoc in Hi as [[Hi Lt]|[-> ->]].
      - destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14). fold G in C5, D10, D12.
        assert (MS : 0 <= sc_map_size ch) by (unfold PG in D8; clear -D8 D9; lia).
        assert (AGC : forall z, (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch \/ Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)) -> m3 z = mE z).
        { intros z Hz. pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as BI.
          destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 i ch Hi) as (_ & STh & SPb & _). fold G T in STh, SPb.
          pose proof D10 as (D10a & _ & _ & _ & D10b). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D10b.
          apply AGmH; [| | exact (CHN i ch z Hi Hz) |].
          - destruct Hz as [Hz|Hz]; [clear -Hz BI; lia|]. unfold Sh, SHADOW_OFF, IMG_HI in *. pose proof (Z.div_pos (sc_map_beg ch) 8 ltac:(clear -D10a; lia) ltac:(clear; lia)). clear -Hz H. lia.
          - destruct Hz as [Hz|Hz]; [clear -Hz STh; lia|].
            pose proof (sh_run_band2 (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z ltac:(clear -D10a; lia) ltac:(clear -MS D12 ACV; lia) Hz) as BY.
            unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. clear -BY TB. lia.
          - apply NPWpab. destruct Hz as [Hz|Hz]; [clear -Hz SPb; unfold kPtrArrayReserve in *; lia|].
            pose proof (sh_run_band2 (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z ltac:(clear -D10a; lia) ltac:(clear -MS D12 ACV; lia) Hz) as BY.
            clear -BY P3. unfold kPtrArrayReserve in *. lia. }
        assert (CA : forall off w v, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok mE (mkACell (sc_map_beg ch + off) w v) -> cell_ok m3 (mkACell (sc_map_beg ch + off) w v)).
        { intros off w v Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply AGC. left. unfold PG in D8. clear -Ho Hw Hk D8 D9. lia. }
        split; [apply CA; [clear; lia | cbn; clear; lia | exact C1]|]. split; [apply CA; [clear; lia | cbn; clear; lia | exact C2]|].
        split; [apply CA; [clear; lia | cbn; clear; lia | exact C3]|]. split; [apply CA; [clear; lia | cbn; clear; lia | exact C4]|].
        split; [eapply cell_ok_agree; [|exact C5]; cbn [c_addr c_w]; intros k Hk; apply AGpabOld; unfold pw, idx; cbn in Hk; clear -Hk Lt; lia|].
        split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
        split; [|eapply present_agree; [|exact D14]; intros z Hz; apply AGC; right; exact Hz].
        eapply present_but_mono; [exact LIVM | | exact D13]. intros z Hz _ Hm. rewrite (AGC z (or_introl Hz)). exact Hm.
      - cbn [sc_map_beg sc_map_size sc_size]. replace (Z.of_nat (length (aa_sec A))) with idx by reflexivity.
        split; [replace (ua + 0) with ua by (clear; lia); apply CELL3; [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | exact C0]|].
        split; [apply CELL3; [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | exact C8]|].
        split; [apply CELL3; [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | exact C16]|].
        split; [apply CELL3; [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | exact C24]|].
        split; [apply CELL3; [intros k Hk; right; right; right; fold pw; cbn in Hk; clear -Hk Hblk; lia | exact CPW]|].
        split; [unfold PG; exact PAL|]. split; [unfold PG; exact SMM|].
        split; [unfold L, secmapsize, PG; pose proof (round_up_ge (secneeded nv) 4096 ltac:(clear; lia)) as R; clear -R; lia|].
        split; [unfold secneeded; pose proof (round_up_ge nv 8 ltac:(clear; lia)) as R; clear -R Hnv; lia|].
        split; [unfold dyn_in; unfold IMG_HI in UI; unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; clear -UI PL0 PDT PDB; lia|].
        split; [reflexivity|]. split; [exact PDT|].
        split; [intros z Hz _; apply PRm; apply INnew; exact Hz|].
        intros z Hz. apply PRm. apply INrun. rewrite <- ESHL. exact Hz. }
    split.
    { intros z Hz. destruct (ZD z) as [Hc|Hn]; [exact (PRm z Hc)|]. rewrite (AGm z Hn). apply SPT. fold G idx. clear -Hz. lia. }
    split; [clear -HROOM Hblk P4; lia|]. split; [exact S3|]. split; [exact S45|].
    assert (CZI : forall a w v, SEC_INST <= a -> a + Z.of_nat w <= 0xee044 -> cell_ok v3 (mkACell a w v) -> cell_ok m3 (mkACell a w v)).
    { intros a w v H1 H2. apply CELL3. intros k Hk. left. unfold zimg. clear -H1 H2 Hk. lia. }
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact CI0]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact CI8]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact CI16]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact CI24]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact C48]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact C56]|].
    split; [apply PRESX; exact I7|].
    split; [|apply PRESX; exact I9].
    apply CZI; [unfold SEC_INST; clear; lia | cbn; clear; lia | exact CMU]. }
  idtac "sr:7".
  assert (HQR' : quarantine_repr m3 (secA A ua nv)).
  { apply (quarantine_repr_sec_mono m3 A (secA A ua nv)); try reflexivity.
    - intros ch Hch. cbn [aa_sec secA]. apply in_or_app. left. exact Hch.
    - apply (quarantine_repr_agreeQ mE m3 A A); try reflexivity.
      + exact (q_items_rz A).
      + intros z Hz. pose proof HI3 as (_ & _ & _ & Q3 & _). destruct (Q3 z Hz) as [QT _]. fold G T in QT.
        pose proof (q_foot_high mE A z HQR Hz) as QH. pose proof (q_foot_pab mE A HG HI3 HPR HSR HQR z Hz) as Y. fold G in Y.
        apply AGmH; [exact QH | clear -QT; lia | exact (QFN z Hz) | exact (NPWpab z Y)].
      + intros z Hz. fold G T in Hz. assert (ZT : T <= z < T + 0x1000) by (clear -Hz; lia).
        destruct (Z_lt_dec z IMG_HI) as [LO|HI].
        * apply AGmI; [exact LO | unfold zimg, SEC_INST, ERRNO_A; unfold IMG_HI in LO; clear -ZT LO TI; intros X; lia | clear -Hz; lia].
        * pose proof HI3 as ((_ & _ & _ & _ & PT & _) & _). fold G T in PT.
          apply AGmH; [clear -HI; lia | clear -Hz; lia | exact (NEW_T z ZT) | apply NPWpab; clear -ZT PT; unfold kPtrArrayReserve in *; lia].
      + intros z Hz. apply AGmI; unfold QG, zimg, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz; lia | clear -Hz TI; lia].
      + exact HQR. }
  assert (HIA' : ia_inv m3 (secA A ua nv)).
  { apply (ia_inv_agreeN mE m3 A (secA A ua nv)); [reflexivity | | exact HIA].
    intros z Hz. apply AGmI; unfold IA_BEG, IA_END, zimg, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz; lia | clear -Hz TI; lia]. }
  assert (HTH' : thread_inv m3 G).
  { destruct HTH as [X Y]. fold T in X, Y |- *. split.
    - fold T. assert (ZT : T <= T + 3168 < T + 0x1000) by (clear; lia).
      destruct (Z_lt_dec (T + 3168) IMG_HI) as [LO|HI].
      + rewrite AGmI; [exact X | exact LO | unfold zimg, SEC_INST, ERRNO_A; unfold IMG_HI in LO; clear -LO TI; intros Z1; lia | clear; lia].
      + pose proof HI3 as ((_ & _ & _ & _ & PT & _) & _). fold G T in PT.
        rewrite AGmH; [exact X | clear -HI; lia | clear; lia | exact (NEW_T _ ZT) | apply NPWpab; clear -PT; unfold kPtrArrayReserve in *; lia].
    - fold T. apply PRESX. exact Y. }
  assert (HMI' : misc_inv m3).
  { apply (misc_inv_N mE m3); [| | | exact HMI].
    - intros z Hz. apply AGmI; unfold zimg, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz; lia | clear -Hz TI; lia].
    - intros z Hz. apply PRm. left. unfold zimg. clear -Hz. lia.
    - intros z Hz. apply PRm. left. unfold zimg. clear -Hz. lia. }
  idtac "sr:8".
  assert (HDEP : depot_wf m3 (secA A ua nv)).
  { unfold depot_wf in HDW |- *. change (aa_depot (secA A ua nv)) with (aa_depot A).
    pose proof HI3 as (_ & _ & _ & _ & DEP3 & _).
    eapply depot_mem_frame; [|exact HDW]. intros a Ha.
    assert (BLKZ : forall bb LL, In (bb, LL) (dblocks (aa_depot A)) -> 0xf000 < LL -> bb <= a < bb + LL -> m3 a = mE a).
    { intros bb LL Hb HLL Hab. destruct (DEP3 (bb, LL) Hb) as (DY & STb & _ & _ & _ & _ & SPb & _). cbn [fst snd] in DY.
      unfold sepZ in STb, SPb. cbn [fst snd] in STb, SPb. fold G T in STb, SPb.
      pose proof (dyn_in_big _ _ _ DY HLL) as BB. pose proof DY as (_ & _ & DT & _ & DBb). fold G in DT.
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in DBb.
      pose proof (SDB (bb, LL) Hb) as SN.
      apply AGmH; [clear -BB Hab; lia | clear -STb Hab; lia | | apply NPWpab; clear -SPb Hab; unfold kPtrArrayReserve in *; lia].
      apply (APPN bb LL a); [unfold IMG_HI in BB; clear -BB; lia | clear -HLL; lia | clear -DT ACV; lia | apply sepZ_sym; exact SN | exact DBb | exact Hab]. }
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. apply AGmI; unfold zimg, SEC_INST, ERRNO_A, IMG_HI; [clear -Hs; lia | clear -Hs; lia | clear -Hs TI; lia].
    - apply (BLKZ bb NBSZ); [unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb] | unfold NBSZ; clear; lia | exact Hab].
    - apply (BLKZ bb FBSZ); [unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb] | unfold FBSZ; clear; lia | exact Hab]. }
  idtac "sr:9".

  assert (HMD : model_inv segsA (secA A ua nv) tp md).
  { unfold model_inv in HM |- *. cbn [aa_geom aa_V aa_Km aa_Kf secA]. fold G.
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
    split.
    { unfold vm_geom in V1 |- *. cbn [aa_sec aa_geom secA]. fold G. fold G in V1.
      destruct V1 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
      split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|]. split; [exact N7|]. split; [|exact N9].
      intros ch Hch. apply in_app_or in Hch as [Hch|[<-|[]]]; [exact (N8 ch Hch)|]. cbn [sc_map_beg sc_map_size]. exact PM. }
    split; [exact V2|]. split; [exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|]. split; [exact V7|].
    unfold ledger_inv in V8 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_sec secA] in V8 |- *.
    destruct V8 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8' & L9 & L10).
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8'|].
    split; [|exact L10]. rewrite length_app. cbn [length]. fold idx in HKM. unfold idx in HKM. clear -HKM. lia. }
  idtac "sr:10".
  assert (HI3' : inv3 (secA A ua nv)).
  { pose proof HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & ND3 & CNT3 & SML3 & QCI3).
    unfold inv3. cbn [aa_geom aa_live aa_sec aa_cls aa_depot secA]. fold G.
    split; [exact SG3|].
    split.
    { intros b n Hin. destruct Hin as [E|Hin].
      - injection E as <- <-. right. exists (mkSC ua L (secneeded nv)). split; [apply in_or_app; right; left; reflexivity|].
        cbn [sc_map_beg sc_size]. split; [unfold PG; clear; lia | reflexivity].
      - destruct (LIV3 b n Hin) as [P|(ch & Hch & X)]; [left; exact P | right; exists ch; split; [apply in_or_app; left; exact Hch | exact X]]. }
    split.
    { unfold sepZ in SS, ST, SP, SF, SC, SD. cbn [fst snd] in SS, ST, SP, SF, SC, SD. fold T in ST |- *.
      intros i ch Hi. apply nth_error_snoc in Hi as [[Hi Lt]|[-> ->]].
      - destruct (SEC3 i ch Hi) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). fold G T in X1, X2, X3, X4, X6, X7.
        split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [|exact (conj X6 X7)].
        intros j ch' Hj Hij. apply nth_error_snoc in Hj as [[Hj _]|[-> ->]]; [exact (X5 j ch' Hj Hij)|].
        cbn [sc_map_beg sc_map_size]. pose proof (SX ch (nth_error_In _ _ Hi)) as Y. unfold sepZ in Y. cbn [fst snd] in Y. clear -Y. lia.
      - cbn [sc_map_beg sc_map_size].
        split; [clear -SS; lia|]. split; [clear -ST; lia|]. split; [clear -SP; lia|]. split; [clear -SF; lia|]. split; [|split; [clear -SC; lia | clear -SD; lia]].
        intros j ch' Hj Hij. apply nth_error_snoc in Hj as [[Hj _]|[E _]]; [|exfalso; exact (Hij (eq_sym E))].
        pose proof (SX ch' (nth_error_In _ _ Hj)) as Y. unfold sepZ in Y. cbn [fst snd] in Y. exact Y. }
    split; [exact Q3|].
    split.
    { intros bn Hbn. destruct (DEP3 bn Hbn) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
      split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|]. split; [exact D7|].
      intros ch Hch. apply in_app_or in Hch as [Hch|[<-|[]]]; [exact (D8 ch Hch)|]. cbn [sc_map_beg sc_map_size]. exact (SDB bn Hbn). }
    split.
    {
      cbn [List.filter snd]. rewrite ENP. cbn [negb List.map fst app].
      constructor; [|exact ND3]. intros Hin. apply (proj1 (list_elem_of_In _ _)) in Hin.
      assert (OLDU : exists ch, In ch (aa_sec A) /\ ua + 6144 = sc_map_beg ch + PG + 2048).
      { apply in_app_or in Hin as [Hin|Hin].
        - apply in_map_iff in Hin as ([b n] & Eb & Hf). cbn [fst] in Eb. subst b. apply filter_In in Hf as [Hl Hp]. cbn [snd] in Hp.
          destruct (LIV3 _ _ Hl) as [P|(ch & Hch & X & _)]; [rewrite P in Hp; discriminate Hp | exists ch; exact (conj Hch X)].
        - apply in_map_iff in Hin as ([u n] & Eu & Hf). cbn [fst] in Eu. subst u. apply filter_In in Hf as [Hq Hp]. cbn [snd] in Hp.
          unfold qitems in Hq. apply in_flat_map in Hq as (qb & Hqb & Hit).
          destruct HQR as (QB & _). pose proof (proj1 (Forall_forall _ _) QB qb Hqb) as (_ & _ & _ & _ & _ & _ & B6 & _).
          destruct (In_nth_error _ _ Hit) as [k Hk]. destruct (B6 k _ Hk) as [_ IT]. destruct IT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & JS & _). cbn [fst snd] in JS.
          destruct (is_primary n) eqn:EPn; [discriminate Hp|]. destruct (JS eq_refl) as (ch & Hch & X & _). exists ch. exact (conj Hch X). }
      destruct OLDU as (ch & Hch & Eu). pose proof (SX ch Hch) as Y. unfold sepZ in Y. cbn [fst snd] in Y.
      destruct (In_nth_error _ _ Hch) as [i Hi]. destruct HSR as (S1 & _). destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & _).
      unfold PG in Eu, D8. clear -Y Eu D8 D9 SMB. lia. }
    rewrite length_app. cbn [length].
    assert (ELL : large_live (secA A ua nv) = large_live A + 1).
    { rewrite (large_live_insert A (secA A ua nv) [] (aa_live A) (ua + 6144) nv eq_refl eq_refl).
      destruct (Z.leb_spec 64513 nv) as [_|X]; [reflexivity | exfalso; clear -X Hnv; lia]. }
    split; [rewrite ELL; change (qlarge (secA A ua nv)) with (qlarge A); clear -CNT3; lia|].
    split; [|exact QCI3].

    rewrite (small_live_insert A (secA A ua nv) [] (aa_live A) (ua + 6144) nv eq_refl eq_refl).
    destruct (Z.leb_spec 64513 nv) as [_|X]; [clear -SML3; lia | exfalso; clear -X Hnv; lia]. }
  idtac "sr:11".

  unfold AInvA. change (aa_geom (secA A ua nv)) with G. fold v3.
  split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|]. split.
  { unfold rest_inv. fold m3. change (aa_geom (secA A ua nv)) with G.
    split; [exact HLS|]. split; [exact HLB|]. split; [exact HPR'|]. split; [exact HSR'|]. split; [exact HQR'|].
    split; [exact HDEP|]. split; [exact HIA'|]. split; [exact HTH' | exact HMI']. }
  split; [exact HMD|]. split; [exact HI3'|].
  eapply bandtp_mono_rm; [|exact HB]. exact DEFB.
Qed.

Section Kept.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S12VCST;R1A2S12S5dR2A2SeF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0S12VCST;R1A2S12S5bR2A2SeF_;F_;Fa;").

Theorem sec_kept : ltac2:(tb__ "0|7|
S20S3aS3aS4aS40Q40M0A1A1S58S0S0S0S43S53R8R7R5R4A5SaS1Zfc01R4A2S3R4S6Z2M1Z27A2A2A2S1eRaA1S27S56R6A1S0S9S4eS1dS1fRcA1A2A1S0S2S23R3A1S8Z8M2R1A2A2S0S5aReR8R3RaA4S1G2R8A2S1S2S8G2R4A2R9A2S22R10A1A2S0SaS1Z0R1A2S3R1S6G1Z40A2A2A2ScS5fR9R2A2A1ScS3cRaReR9R7RdR3A6A1ScS12S5bR4A2A1SbS4bS40Q8A1M3A1M4S39R14S3fG0R5A2M5A2S39R15G5A2A3F_;F_;F_;F_;Fa;S0SaS1S18R1A2S3R1S17A2A2ScSbG4S39R13S3fG0R2A2A2S4cG3A1M6A3A1ScSbG4S39R13S3fG0R3A2A2G6A3A1F_;F_;Fa;S5cVCST;VXGL;R13S3dR13RdReA3S39R12A1S39R11A1A6F_;F_;F_;F_;F_;Tpw;Tidx;TL;TG;F_;F_;Fblk;Fua;Fnv;Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md nv ua blk HA Hnv. cbn zeta. intros HPD Hblk HROOM RMO DEFB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (L := secmapsize nv) in *. set (idx := Z.of_nat (length (aa_sec A))) in *. set (pw := ag_pab G + 8 * idx) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI). fold G T in TB, TI. fold G in FB, CB, DB, CI, DI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in FB, TB, CB, DB, TI, CI, DI. rewrite FS_total_val in FB.
  destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB). fold G L in PM, PL0, PDI, ST, SC, SD, SF, SS, SP, SX, SDB. fold T in ST.
  pose proof (secmapsize_bounds nv ltac:(clear -Hnv; lia)) as [SMB SMM]. fold L in SMB, SMM. unfold PG in SMM, PAL.
  pose proof (dyn_in_big _ _ _ PDI ltac:(clear -SMB; lia)) as UI. destruct PDI as (_ & _ & PDT & _ & PDB).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5). fold G in P1, P2, P3. fold idx in P4.
  assert (U8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X. rewrite PAL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (L8 : L mod 8 = 0).
  { pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (L / 4096)) with ((512 * (L / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (UT : ua + L <= 140737479966720) by (clear -PDT ACV; lia).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in PDB, DEFB.
  pose proof (live_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A _ HG Hsep HI3 HPR HSR SS SX) as LFN.
  assert (PWZ : forall z, pw <= z < pw + blk -> ag_pab G <= z < ag_pab G + kPtrArrayReserve).
  { intros z Hz. unfold pw in Hz. pose proof (Zle_0_nat (length (aa_sec A))) as NN. fold idx in NN. clear -Hz HROOM P4 NN. lia. }
  unfold sepZ in SF, ST. cbn [fst snd] in SF, ST. rewrite FS_total_val in SF.

  assert (NOC : forall a, client_addrA CST A a -> ~ errno_addrA a ->
                  ~ chg_s G ua L pw blk a /\ ~ in_rangesZ IMG_S a /\ ~ (ua <= a < ua + L)).
  { intros a Hcl NE.
    pose proof (client_not_rt CST HCST A a _ HG HF Hsep Hcl) as NR. unfold rt_zone in NR. fold G T in NR.
    assert (IMGS : forall x, in_rangesZ IMG_S x -> 0x10000 <= x < IMG_HI).
    { intros x (b & n & Hbn & Hx). unfold IMG_S in Hbn. unfold SEC_INST, IMG_HI in *. cbn [In] in Hbn.
      destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hx; lia. }
    destruct (client_addr_cases CST A a _ HF Hcl) as [S|[Lv|[FR|[C|FL]]]].
    - fold G in S. split; [|split; [intros X; pose proof (IMGS a X) as Y; unfold IMG_HI in Y; clear -S Y ACV; lia | clear -S PDT; lia]].
      intros [X|[X|[[X|X]|X]]].
      + unfold zimg, SEC_INST, ERRNO_A in X. clear -X S ACV. lia.
      + clear -X S G5. lia.
      + clear -X S PDT. lia.
      + unfold Sh, SHADOW_OFF in X. pose proof (Z.div_le_mono (ua + L) 140737479966720 8 ltac:(clear; lia) UT) as D.
        pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. pose proof (Z.div_mod ua 8 ltac:(clear; lia)) as DU. rewrite U8, Z.add_0_r in DU.
        replace (ua + L) with ((ua / 8 + L / 8) * 8) in D by (clear -DL DU; lia). rewrite Z.div_mul in D by (clear; lia). cbn in D. clear -X D S ACV. lia.
      + pose proof (PWZ a X) as Y. clear -Y S P2. lia.
    - destruct Lv as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in S2.
      pose proof (rz_bound n) as RZ.
      pose proof (LFN b n a Hbn ltac:(left; clear -Hx RZ; lia)) as NZ.
      pose proof (live_foot _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as (X1 & X2 & _).
      pose proof (live_foot_pab _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as X3. fold G T in X2, X3.
      split; [|split; [intros X; pose proof (IMGS a X) as Y; clear -X1 Y; lia | intros X; apply NZ; left; exact X]].
      intros [X|[X|[X|X]]]; [unfold zimg, SEC_INST, ERRNO_A, IMG_HI in *; clear -X X1; lia | clear -X X2; lia | exact (NZ X) | exact (X3 (PWZ a X))].
    - destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. fold G in Hx.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|split; [intros X; pose proof (IMGS a X) as Y; unfold IMG_HI in Y; clear -Hx M Y; lia | clear -Hx M SF; lia]].
      intros [X|[X|[[X|X]|X]]].
      + unfold zimg, SEC_INST, ERRNO_A in X. clear -X Hx M. lia.
      + clear -X Hx M G10. lia.
      + clear -X Hx M SF. lia.
      + pose proof (sh_run_band2 ua (ua + L) a ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear -UT PL0; lia)) as BY.
        assert (E : Sh (ua + L) = Sh ua + L / 8).
        { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }
        rewrite E in BY. specialize (BY X). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. clear -BY Hx M FB. lia.
      + pose proof (PWZ a X) as Y. clear -Y Hx M PF. lia.
    - destruct (HCST _ C) as [X0 _]. unfold IMG_LO, IMG_HI in X0.
      split; [|split; [exact (HCSTS a C) | unfold IMG_HI in UI; clear -X0 UI; lia]].
      intros [X|[X|[[X|X]|X]]].
      + apply (HCSTS a C). unfold IMG_S, in_rangesZ. unfold zimg, SEC_INST, ERRNO_A in *.
        destruct X as [Hz|[Hz|[Hz|Hz]]].
        * exists 0xeddd8, (0xee044 - 0xeddd8). split; [left; reflexivity | clear -Hz; lia].
        * exists 0xee048, (0xee070 - 0xee048). split; [right; left; reflexivity | clear -Hz; lia].
        * exists 0x173660, 2. split; [right; right; right; left; reflexivity | clear -Hz; lia].
        * exfalso. apply NE. unfold errno_addrA, ERRNO_A. clear -Hz. lia.
      + apply NR. right. left. clear -X. lia.
      + unfold IMG_HI in UI. clear -X X0 UI. lia.
      + unfold Sh, SHADOW_OFF in X. pose proof (Z.div_pos ua 8 ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear; lia)) as D. clear -X X0 D. lia.
      + pose proof (PWZ a X) as Y. unfold IMG_HI in P1. clear -Y X0 P1. lia.
    - destruct FL as (c & p & Hcp & Hp & _ & Ea). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Ea. unfold fs_flags in M, Ea. rewrite FS_kFlagsOffset_val in M, Ea. unfold IMG_HI in M.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|split; [intros X; pose proof (IMGS _ X) as Y; unfold IMG_HI in Y; clear -M Ea Y; lia | clear -M Ea SF; lia]].
      intros [X|[X|[[X|X]|X]]].
      + unfold zimg, SEC_INST, ERRNO_A in X. clear -X M Ea. lia.
      + clear -X M Ea G10. lia.
      + clear -X M Ea SF. lia.
      + pose proof (sh_run_band2 ua (ua + L) a ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear -UT PL0; lia)) as BY.
        assert (E : Sh (ua + L) = Sh ua + L / 8).
        { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }
        rewrite E in BY. specialize (BY X). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. clear -BY M Ea FB. lia.
      + pose proof (PWZ _ X) as Y. clear -Y M Ea PF. lia. }
  idtac "sk:1".
  assert (ESHL : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }

  assert (NOS : forall a, client_shadowA CST XGL A a ->
                  SHADOW_OFF <= a < HIGH_SHADOW_END /\ ~ chg_s G ua L pw blk a).
  { intros a C1. pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B0. split; [exact B0|].
    unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
    intros [X|[X|[[X|X]|X]]].
    - unfold zimg, SEC_INST, ERRNO_A in X. clear -X B0. lia.
    - clear -X B0 TB G4. lia.
    - clear -X B0 PDB. lia.
    -
      assert (XIN : forall x, a = Sh x -> 0 <= x -> ua <= x < ua + L).
      { intros x -> Hx0. unfold Sh in X. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL.
        pose proof (Z.div_mod ua 8 ltac:(clear; lia)) as DU. rewrite U8, Z.add_0_r in DU.
        pose proof (Z.div_mod x 8 ltac:(clear; lia)) as DX. pose proof (Z.mod_pos_bound x 8 ltac:(clear; lia)) as MX. clear -X DL DU DX MX. lia. }
      destruct C1 as [(y & Cy & Ey)|(y & Gy & Ey)].
      + destruct (client_addr_bounds CST HCST A y _ HG HF Hsep Cy) as [By _]. pose proof (XIN y Ey ltac:(clear -By; lia)) as YIN.
        assert (NEy : ~ errno_addrA y) by (unfold errno_addrA, ERRNO_A; unfold IMG_HI in UI; clear -YIN UI; lia).
        exact (proj2 (proj2 (NOC y Cy NEy)) YIN).
      + destruct (HXGL y Gy) as [Y1 Y2]. pose proof (XIN y Ey ltac:(clear -Y1; unfold IMG_LO in *; lia)) as YIN. clear -YIN Y2 UI. lia.
    - pose proof (PWZ a X) as Y. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, kPtrArrayReserve in *. clear -Y B0 P3. lia. }
  idtac "sk:2".
  split.
  - intros a Ba Hcl. destruct Hcl as [(C1 & _ & NE)|(C1 & _ & _)].
    + destruct (NOC a C1 NE) as (N1 & N2 & _).
      apply RMO; [exact Ba | exact (client_not_rtM CST HCST HCSTM A a _ HG HF Hsep C1) | exact N1 | exact N2].
    + destruct (NOS a C1) as (B0 & N1). unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
      apply RMO; [exact Ba | | exact N1 |].
      * unfold rt_zoneM, rt_zone, IMG_HI. intros [[R1|[R1|[R1|[R1|R1]]]]|R1].
        -- destruct R1 as [R1 _]. clear -R1 B0. lia.
        -- fold G T in R1. clear -R1 B0 TB. lia.
        -- fold G in R1. clear -R1 B0 CB. lia.
        -- fold G in R1. clear -R1 B0 DB. lia.
        -- fold G in R1. clear -R1 B0 FB. lia.
        -- pose proof (IMG_M_range a R1) as IR. unfold IMG_HI in *. clear -IR B0. lia.
      * intros (b & n & Hbn & Hx). unfold IMG_S in Hbn. unfold SEC_INST in *. cbn [In] in Hbn.
        destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hx B0; lia.
  - intros x j Hx Hj Hdef.
    assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
    { destruct Hx as [[C1 C2]|GX].
      - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. clear -B. lia.
      - destruct (HXGL x GX) as [X0 X1]. unfold IMG_LO, IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. clear -X0 X1. lia. }
    unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
    destruct (word_byte_range (Sh x) j ltac:(clear -Bx; lia) Hj) as (W1 & W2 & W3).
    unfold word_byte in *. apply DEFB; [|exact Hdef]. clear -W3 Bx Hj. lia.
Qed.
End Kept.
End RebuildS.

(* [comment removed for export] *)
Module SpineMallocSec2S.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "reg_sv"; "SLit"; "sobj"; "valuation"; "ss_next"; "SVar"; "swf"; "rw"; "ss_facts"; "ss_objs"; "ss_pc"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "CS1"; "ES1"; "V_MS"; "ES1g"; "RT_sec"; "SSa_S"; "nxS"; "SS0"; "F_sgen"; "SSb_S"; "V_NS"; "@Corelib.Init.Datatypes"; "list"; "app"; "prod"; "nil"; "cons"; "pair"; "bool"; "true"; "Some"; "option"; "false"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "pow"; "lt"; "sub"; "ge"; "modulo"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "A_globals"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "ustop"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "with_vmmaps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "F_fam"; "F_s1"; "RT_m1"; "sw_s1"; "neededx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS"; "alloc_roomA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "@Stdlib.Lists.List"; "incl"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "GN"; "FBMAX"; "GAPC"; "GAPF"; "N0"; "NBMAX"; "SLIM"; "VCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "a1x"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_noreserve_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom";
"@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec2 MmapSymG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require IfaceS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma room_gap_closes : ltac2:(tb__ "0|3|
S34S34S34S34S2dZ0M0R4A2M1G1S1G1S2dR4S2fZ2M2Z24A2A2A2S1S30G0R4A2S2dR4S2cS2fG2Z1aA2Z3006A2A2A2S2dS2eS76R8A2S2cS2eS76S2cS2cS2cS7aS7bA2S77A2Z1A2A2R6A2A2S2dR8S31S7cS2eG2S31S7dR7A2A2A2A2S2dS2cS2cS2cS79R7A2R9A2S2eRaS2cR7ZfffA2A2A2S78A2F_;F_;F_;F_;F_;F_;FnZ;FV;FhS;FhN;").
Proof.
  intros hN hS V nZ HN HS HV HnZ H1 H2.
  assert (B1 : hN <= 1335565) by (unfold GN, N0, NBMAX, FBMAX in H1; lia).
  assert (B2 : hN * (nZ + 4095) <= 1335565 * (2 ^ 26 + 12294 + 4095)) by (apply Z.mul_le_mono_nonneg; lia).
  unfold SLIM, VCAP, S0, NBSZ, FBSZ, NBMAX, FBMAX, LIMIT in H2. unfold GAPF, GAPC. lia.
Qed.

Section SEC2S.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S48VAInv;VW;Vst;VA;VKc;SaPcA1A6").

Lemma law_res : ltac2:(tb__ "0|1|
S53S8S1fS57Q40A1M0A1S4cVAInv;R4R3R2R1A4S0S1fS21G0G0A2A1S50S4dR2A1A1S5eS4bA1A3F_;Fmd;Ftp;Frho;FA;").
Proof. intros A rho tp md (_ & _ & _ & _ & HM & _). destruct HM as (_ & _ & _ & _ & _ & _ & _ & HL). exact (proj1 HL). Qed.

Lemma room_place : ltac2:(tb__ "0|4|
S53S8S1fS57Q40M0A1M1A1S4cG1S34VAInv;R6R5R4R3A4S2dS56R7A1S2fZ2M2Z24A2A2S2dS2cS55R8A1S54R8A1A2Z800A2S1S30Z0M3R4A2S2dR4S2cS2fG2Z1aA2Z3006A2A2A2S0S34S33R5Z1000A2G3A3S0S25S7fR7A1S29A3S32S80R9RaA2R7A2S2G1G1S5aS59G0G3A2RaRbS59G0R9A2R1A5La;A2F_;F_;F_;F_;F_;F_;F_;FnZ;Fflags;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md flags nZ HA HV HK HnZ Hal Hnr Hroom.
  pose proof (AInvA_depot A rho tp md HA) as [DM _].
  pose proof HA as (HG & _ & _ & _ & HM & _).
  destruct HM as (_ & _ & _ & V4 & V5 & V6 & V7 & _ & _ & _ & L4 & _ & L6 & _).
  pose proof (dm_map1_len _ _ DM) as [_ M2]. pose proof (dm_fb_len _ _ DM) as [[_ F2] _].
  pose proof (dm_N _ _ DM) as [[N1 _] _]. pose proof (dm_F _ _ DM) as (F0 & _ & F32 & _).
  assert (HB1 : Z.of_nat (length (dNB (aa_depot A))) <= NBMAX).
  { unfold nblk in M2. unfold NBMAX. destruct (Z.eqb_spec (dN (aa_depot A) + 1) 0); [lia|].
    pose proof (Z.div_le_mono (dN (aa_depot A) + 1) (2 ^ 28 + 2) 65536 ltac:(lia) ltac:(lia)) as DV. change ((2 ^ 28 + 2) / 65536) with 4096 in DV. lia. }
  assert (HB2 : Z.of_nat (length (dFB (aa_depot A))) <= FBMAX).
  { unfold fblk in F2. unfold FBMAX.
    pose proof (Z.div_le_mono (dF (aa_depot A) + 1048576 - 1) (2 ^ 32 - 2 ^ 21 + 1048576 - 1) 1048576 ltac:(lia) ltac:(lia)) as DV.
    change ((2 ^ 32 - 2 ^ 21 + 1048576 - 1) / 1048576) with 4094 in DV. lia. }
  destruct (count_of_gap_ok A (m_vmmaps md) L4 HB1 HB2) as [CN CS].
  pose proof (hwN_nonneg (ledger (m_vmmaps md))) as N0'. pose proof (hwS_nonneg (ledger (m_vmmaps md))) as S0'.
  assert (HnZ64 : 0 <= nZ < 2 ^ 64) by lia.
  destruct (place_of_room md nZ ltac:(lia) Hal) as [a Ha].
  - rewrite V7. pose proof (geom_top _ HG) as TG. pose proof (topG_range (aa_geom A)). rewrite GAPC_eq. unfold alloc_ceiling_lo. lia.
  - exact (room_gap_closes _ _ (aa_V A) nZ N0' S0' ltac:(lia) HnZ CN CS).
  - exists a. destruct Ha as (P1 & P2 & P3 & P4). unfold mmap_place_ok. repeat (split; [assumption|]).
    unfold mmap_noreserve_backed_ok. rewrite Hnr. rewrite (mmap_nZ_lit nZ HnZ64 Hal).
    apply Z.leb_le. unfold headroom, paid in Hroom. pose proof (Zle_0_nat (length (unpaid md tp))). unfold page_size in *. lia.
Qed.

Section C3S.
Hypothesis IC1 : ltac2:(tb__ "0|0|
S0S28S37A1S64S4bSfS11S14VW;Vst;Vtmax;A3A1A1A2S27S37S38A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1Z11A2S6ZdeA1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZbA2SaS16A1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZaA2S6Z0A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZdA2S6Z22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZfA2S6Z0A1A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S35S9S11S14VW;Vst;Vtmax;A3A1A1S51A3").
Hypothesis XC1 : ltac2:(tb__ "0|1|
S0S1fS21S3S3A2M0A1S12S14VW;Vst;Vtmax;A3A1S22G0A1A3").
Hypothesis SK1 : ltac2:(tb__ "0|1|
S0S1fS21S21S3S3A2S3A2M0A1S36S7G0S4aSeS11S14VW;Vst;Vtmax;A3A1A1A4S36S7G0S4aS20S7S20S7S23S7S6bS20S7S46VW;A1S3fA3A3S6aA3S18A3A4A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S6fS4S20S4S20S4S20S4S20S4S45VW;Vst;A2S44S43A1A3S52A3S69A3S68Vtmax;Z8A2A3SdS11S14VW;Vst;Vtmax;A3A1A1A3").

Theorem sec_ecall_S : ltac2:(tb__ "0|5|
S61OF_;S53S40S57Q40M0A1M1S3bF_;S8S1fG1A1S62S0S47Vst;S42A3S0S1fS3eA1VW;S22S3eA1A3F_;S6eVW;Vst;A2S41R7A1S3dVsegs;RaS3cR8A1A3S66Vsegs;RbS3cR9A1A3S6dRbS58G0ScR8PcA2A2A2S8S1fS4eA1M2S2bS4cG1S65Vsegs;R5RdS14VW;Vst;Vtmax;A3M3S24G2S5cR4S5dR3R2A2A4A5S49VW;Vst;R12R11RfR6ReR5R3A9S5aS2aR5U0A2S2aR5U3A2R4S2aR5U1M4A2R3A5R12R4S39R8S9S11G3A1A1R4A3R10R7S4fS5bS4dR5A1S2aR6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;S8G1S60Vsegs;R10S3aVsegs;RdR1A1S17VW;Vst;Vtmax;A3S39R2S1aVW;Vst;Vtmax;A3R1A3RbA5RaA4Fa;FrhoX;S8S60Vsegs;R10S3aVsegs;S49VW;Vst;RfReRcA5G3R1RbA5RaA4FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FJo;FKc;FA;Fok;").
Proof.
  intros ok A Kc Jo rho tp Q HW HUS HKc Hokl Hokpl HROOM HJo HGR rhoX.
  set (nv := bv_unsigned (rw rho 12%positive)).
  assert (Hokf : ok_frameA segs ok (JG W st A Kc rho)).
  { intros r t tr ms md msv' [_ HJ]. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  assert (Hokp : ok_pframeA segs ok (JG W st A Kc rho)).
  { apply (ok_pframeA_liftKA segs ok Kc). exact Hokpl. intros r t tr md [_ HJ]. destruct HJ as (_ & HK & _). exact HK. }
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  pose proof (topG_range (aa_geom A)) as ACV.

  apply (triple_pre_pure segs ok _ _ (rw rhoX 142%positive = Z_to_bv 64 (secmapsize nv) /\ 64513 <= nv < 2 ^ 39)).
  { intros w Hw. destruct w as [tr [ms md]]. pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & _ & E142 & _).
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
  2: { apply triple_ex. intros a. exact (HGR rhoX a). }
  unfold ES1g, nxS.
  change (mkObj (SVar (ss_next (ax_S (CS1 W st tmax)))) (SLit 0) (SVar V_MS) [] DZero) with (mmap_obj_sym (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS)).
  assert (HST' : stableA segs (ss_next (ax_S (CS1 W st tmax))) (JG W st A Kc rho)).
  { rewrite NX1. eapply stableA_mono; [|exact HST]. unfold GW, NW2. clear; lia. }
  assert (HB11 : sv_below (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS) = true) by (rewrite NX1; reflexivity).
  assert (HEV : bv_unsigned (eval rhoX (SVar V_MS)) = secmapsize nv).
  { cbn [eval]. unfold V_MS. rewrite E142. apply u64_lit. clear -BMS Hnv. lia. }
  apply (triple1_mmap_rw_symA_granted segs ok (JG W st A Kc rho) Jo (CS1 W st tmax) rhoX tp (SVar V_MS) (secmapsize nv)
           Hokf Hokp HST' IC1 R17 R11 HB11 HEV (proj2 BMS) ltac:(clear -BMS Hnv; lia)).
  intros tr ms md Hsp HJG.
  destruct (pending_argsA segs rhoX tp (CS1 W st tmax) tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite R10 in Q0. rewrite R11 in Q1. rewrite R12 in Q2. rewrite R13 in Q3. rewrite R14 in Q4. rewrite R15 in Q5. cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; apply mmap_modeled_b_intro; reflexivity|].
  split; [rewrite Q3; reflexivity|].
  pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md HJG) as (E12 & E141 & _ & E151 & E152 & E153 & E154 & E155 & E156 & E145 & E146 & E147 & Erm & Erl & Elow).
  pose proof HJG as [_ HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & HR & HFI & HRest & HM & HI3 & HBT).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
  pose proof (geom_top _ HG) as GTOP. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HM))))))) as TOPm.

  split.
  { destruct (AInvA_budget A _ _ _ HA) as (PB & VL & V0 & K0 & F0). unfold headroom. rewrite VL.
    unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
    unfold budget_bound in PB. pose proof (acost_step (aa_V A) nv V0 ltac:(lia)) as AS. unfold BETA_M, BETA_F in *. clear -PB HB AS BMS Hnv. lia. }

  assert (HEADROOM : headroom md tp >= secmapsize nv).
  { destruct (AInvA_budget A _ _ _ HA) as (PB & VL & V0 & K0 & F0). unfold headroom. rewrite VL.
    unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
    unfold budget_bound in PB. pose proof (acost_step (aa_V A) nv V0 ltac:(lia)) as AS. unfold BETA_M, BETA_F in *. clear -PB HB AS BMS Hnv. lia. }
  split.
  { destruct HROOM as (RV & RN & RK). fold nv in RN.
    destruct (room_place A rhoX tp md (ms_gpr ms 3) (secmapsize nv) HA RV RK ltac:(clear -BMS Hnv RN; lia) (proj2 BMS)
                ltac:(rewrite Q3; reflexivity) HEADROOM) as [a0 Ha0].
    assert (E1 : ms_gpr ms 1 = Z_to_bv 64 (secmapsize nv)) by (rewrite Q1; unfold V_MS; exact E142).
    rewrite E1. exact (not_refusable_of_place (Z_to_bv 64 0) (ms_gpr ms 3) md (Z_to_bv 64 (secmapsize nv)) a0 Ha0). }
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
      { destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp. }
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
End C3S.

Section C6S.
Hypothesis Wa : ltac2:(tb__ "0|0|
S0S25SbS19VW;Vst;Vtmax;A3A1S26A3").
Hypothesis Da : ltac2:(tb__ "0|6|
S0S28S21S1fS21S3S3A2M0A1M1S1fS4A1M2A2M3A1S63S11S67VW;Vst;Vtmax;Z8M4A4A1S19VW;Vst;Vtmax;A3A2S27G3S24G1G2S23G0S24S3S3S6cG4A1SaS1eA1A4M5S23G0G5S22G0A1A3A3S22S4A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S0S25SbS1dVW;Vst;Vtmax;A3A1S26A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S25S70S4S10S51A1S1cA3S26A3").
Hypothesis CertS1 : ltac2:(tb__ "0|1|
S0S25S73S4bUfa0S23S34Z7050cS22S34A1A3S75S23S13S1bVW;Vst;Vtmax;A3S22S13A1M0A3S23S13S15VW;Vst;Vtmax;A3G0A3A6S26A3").
Hypothesis WC1 : ltac2:(tb__ "0|0|
S0S25SbS11S14VW;Vst;Vtmax;A3A1A1S26A3").
Hypothesis DC1 : ltac2:(tb__ "0|4|
S0S28S21S1fS21S3S3A2M0A1M1S1fS4A1M2A2M3A1S63S11S15VW;Vst;Vtmax;A3A1S11S14VW;Vst;Vtmax;A3A1A2S27G3S24G1G2S23G0S24S3S3S7eSaS16A1A4S22G0A1A3S22S4A1A4A2A3").
Hypothesis NXC1 : ltac2:(tb__ "0|0|
S0S35S9S11S14VW;Vst;Vtmax;A3A1A1S9S11S15VW;Vst;Vtmax;A3A1A1A3").
Hypothesis IC1 : ltac2:(tb__ "0|0|
S0S28S37A1S64S4bSfS11S14VW;Vst;Vtmax;A3A1A1A2S27S37S38A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1Z11A2S6ZdeA1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZbA2SaS16A1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZaA2S6Z0A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZdA2S6Z22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZfA2S6Z0A1A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S35S9S11S14VW;Vst;Vtmax;A3A1A1S51A3").
Hypothesis XC1 : ltac2:(tb__ "0|1|
S0S1fS21S3S3A2M0A1S12S14VW;Vst;Vtmax;A3A1S22G0A1A3").
Hypothesis SK1 : ltac2:(tb__ "0|1|
S0S1fS21S21S3S3A2S3A2M0A1S36S7G0S4aSeS11S14VW;Vst;Vtmax;A3A1A1A4S36S7G0S4aS20S7S20S7S23S7S6bS20S7S46VW;A1S3fA3A3S6aA3S18A3A4A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S6fS4S20S4S20S4S20S4S20S4S45VW;Vst;A2S44S43A1A3S52A3S69A3S68Vtmax;Z8A2A3SdS11S14VW;Vst;Vtmax;A3A1A1A3").

Theorem sec_spine_S : ltac2:(tb__ "0|5|
S61OF_;S53S40S57Q40M0A1M1S3bF_;S8S1fG1A1S62S0S47Vst;S42A3S0S1fS3eA1VW;S22S3eA1A3F_;S6eVW;Vst;A2S41R7A1S3dVsegs;RaS3cR8A1A3S66Vsegs;RbS3cR9A1A3S6dRbS58G0ScR8PcA2A2A2S8S1fS4eA1M2S2bS4cG1S65Vsegs;R5RdS14VW;Vst;Vtmax;A3M3S24G2S5cR4S5dR3R2A2A4A5S49VW;Vst;R12R11RfR6ReR5R3A9S5aS2aR5U0A2S2aR5U3A2R4S2aR5U1M4A2R3A5R12R4S39R8S9S11G3A1A1R4A3R10R7S4fS5bS4dR5A1S2aR6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;S8G1S60Vsegs;R10S3aVsegs;RdR1A1S17VW;Vst;Vtmax;A3S39R2S1aVW;Vst;Vtmax;A3R1A3RbA5RaA4Fa;FrhoX;S8S60Vsegs;R10S3aVsegs;S49VW;Vst;RfReRcA5S67VW;Vst;Vtmax;Z8A4R1RbA5RaA4FrhoE;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FJo;FKc;FA;Fok;").
Proof.
  intros ok A Kc Jo rho tp Q HW HUS HKc Hokl Hokpl HROOM HJo HOK rhoE.
  assert (Hokf : ok_frameA segs ok (J W st A Kc)).
  { intros r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  eapply triple_conseq; [intros w Hw; exact (sec_inst nW st tmax Wa Da Wb FB A Kc rho tp w rhoE HW HUS HKc Hw) | intros w Hw; exact Hw |].
  apply (sec_cert1 nW st tmax CertS1 ok A Kc rho tp Q HUS HKc Hokf). intros rhoX.
  eapply triple_conseq; [intros w Hw; exact (sec_cs1 nW st tmax WC1 DC1 NXC1 A Kc rho tp w rhoX Hw) | intros w Hw; exact Hw |].
  exact (sec_ecall_S IC1 R17 R11 R10 R12 R13 R14 R15 NX1 XC1 SK1 FC1 ok A Kc Jo rho tp Q HW HUS HKc Hokl Hokpl HROOM HJo HOK rhoX).
Qed.
End C6S.

Section C3SE.
Hypothesis IC1 : ltac2:(tb__ "0|0|
S0S28S37A1S64S4bSfS11S14VW;Vst;Vtmax;A3A1A1A2S27S37S38A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1Z11A2S6ZdeA1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZbA2SaS16A1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZaA2S6Z0A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZdA2S6Z22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZfA2S6Z0A1A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S35S9S11S14VW;Vst;Vtmax;A3A1A1S51A3").
Hypothesis XC1 : ltac2:(tb__ "0|1|
S0S1fS21S3S3A2M0A1S12S14VW;Vst;Vtmax;A3A1S22G0A1A3").
Hypothesis SK1 : ltac2:(tb__ "0|1|
S0S1fS21S21S3S3A2S3A2M0A1S36S7G0S4aSeS11S14VW;Vst;Vtmax;A3A1A1A4S36S7G0S4aS20S7S20S7S23S7S6bS20S7S46VW;A1S3fA3A3S6aA3S18A3A4A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S6fS4S20S4S20S4S20S4S20S4S45VW;Vst;A2S44S43A1A3S52A3S69A3S68Vtmax;Z8A2A3SdS11S14VW;Vst;Vtmax;A3A1A1A3").

Theorem esec_ecall_S : ltac2:(tb__ "0|5|
S53S40S57Q40M0A1M1S3bF_;S8S1fG1A1S61OF_;S0S47Vst;S42A3S0S1fS3eA1VW;S22S3eA1A3F_;S6eVW;Vst;A2S41R7A1S6dR9S58G0ScR6PcA2A2A2S8S1fS4eA1M2S2bS4cG1S65Vsegs;R5RbS14VW;Vst;Vtmax;A3M3S24G2S5cR4S5dR3R2A2A4A5S49VW;Vst;R10RfRdR6RcR5R3A9S5aS2aR5U0A2S2aR5U3A2R4S2aR5U1M4A2R3A5R10R4S39R8S9S11G3A1A1R4A3ReR7S4fS5bS4dR5A1S2aR6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;S8G1S5fVsegs;S3aVsegs;RbR1A1S17VW;Vst;Vtmax;A3S39R2S1aVW;Vst;Vtmax;A3R1A3R9A5R8A3Fa;FrhoX;S8S5fVsegs;S3aVsegs;S49VW;Vst;RdRcRaA5G3R1R9A5R8A3FrhoX;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FJo;FKc;FA;").
Proof.
  intros A Kc Jo rho tp Q HW HUS HKc HROOM HJo HGR rhoX.
  set (nv := bv_unsigned (rw rho 12%positive)).
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  pose proof (topG_range (aa_geom A)) as ACV.

  apply (etriple_pre_pure segs _ _ (rw rhoX 142%positive = Z_to_bv 64 (secmapsize nv) /\ 64513 <= nv < 2 ^ 39)).
  { intros w Hw. destruct w as [tr [ms md]]. pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md (proj2 Hw)) as (E12 & _ & E142 & _).
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
  eapply etriple_seq.
  2: { apply etriple_ex. intros a. exact (HGR rhoX a). }
  unfold ES1g, nxS.
  change (mkObj (SVar (ss_next (ax_S (CS1 W st tmax)))) (SLit 0) (SVar V_MS) [] DZero) with (mmap_obj_sym (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS)).
  assert (HST' : stableA segs (ss_next (ax_S (CS1 W st tmax))) (JG W st A Kc rho)).
  { rewrite NX1. eapply stableA_mono; [|exact HST]. unfold GW, NW2. clear; lia. }
  assert (HB11 : sv_below (ss_next (ax_S (CS1 W st tmax))) (SVar V_MS) = true) by (rewrite NX1; reflexivity).
  assert (HEV : bv_unsigned (eval rhoX (SVar V_MS)) = secmapsize nv).
  { cbn [eval]. unfold V_MS. rewrite E142. apply u64_lit. clear -BMS Hnv. lia. }
  apply (etriple_mmap_rw_symA_granted segs (JG W st A Kc rho) Jo (CS1 W st tmax) rhoX tp (SVar V_MS) (secmapsize nv)
           HST' IC1 R17 R11 HB11 HEV (proj2 BMS) ltac:(clear -BMS Hnv; lia)).
  intros tr ms md Hsp HJG.
  destruct (pending_argsA segs rhoX tp (CS1 W st tmax) tr ms md Hsp) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite R10 in Q0. rewrite R11 in Q1. rewrite R12 in Q2. rewrite R13 in Q3. rewrite R14 in Q4. rewrite R15 in Q5. cbn [eval] in Q0, Q1, Q2, Q3, Q4, Q5.
  split; [rewrite Q2, Q3, Q5; apply mmap_modeled_b_intro; reflexivity|].
  split; [rewrite Q3; reflexivity|].
  pose proof (JG_rigidS nW st A Kc rho rhoX tp tr md HJG) as (E12 & E141 & _ & E151 & E152 & E153 & E154 & E155 & E156 & E145 & E146 & E147 & Erm & Erl & Elow).
  pose proof HJG as [_ HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & HR & HFI & HRest & HM & HI3 & HBT).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
  pose proof (geom_top _ HG) as GTOP. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HM))))))) as TOPm.

  split.
  { destruct (AInvA_budget A _ _ _ HA) as (PB & VL & V0 & K0 & F0). unfold headroom. rewrite VL.
    unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
    unfold budget_bound in PB. pose proof (acost_step (aa_V A) nv V0 ltac:(lia)) as AS. unfold BETA_M, BETA_F in *. clear -PB HB AS BMS Hnv. lia. }

  assert (HEADROOM : headroom md tp >= secmapsize nv).
  { destruct (AInvA_budget A _ _ _ HA) as (PB & VL & V0 & K0 & F0). unfold headroom. rewrite VL.
    unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [eval] in HB. rewrite E12 in HB. fold nv in HB.
    unfold budget_bound in PB. pose proof (acost_step (aa_V A) nv V0 ltac:(lia)) as AS. unfold BETA_M, BETA_F in *. clear -PB HB AS BMS Hnv. lia. }
  split.
  { destruct HROOM as (RV & RN & RK). fold nv in RN.
    destruct (room_place A rhoX tp md (ms_gpr ms 3) (secmapsize nv) HA RV RK ltac:(clear -BMS Hnv RN; lia) (proj2 BMS)
                ltac:(rewrite Q3; reflexivity) HEADROOM) as [a0 Ha0].
    assert (E1 : ms_gpr ms 1 = Z_to_bv 64 (secmapsize nv)) by (rewrite Q1; unfold V_MS; exact E142).
    rewrite E1. exact (not_refusable_of_place (Z_to_bv 64 0) (ms_gpr ms 3) md (Z_to_bv 64 (secmapsize nv)) a0 Ha0). }
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
      { destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp. }
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
End C3SE.

Section C6SE.
Hypothesis Wa : ltac2:(tb__ "0|0|
S0S25SbS19VW;Vst;Vtmax;A3A1S26A3").
Hypothesis Da : ltac2:(tb__ "0|6|
S0S28S21S1fS21S3S3A2M0A1M1S1fS4A1M2A2M3A1S63S11S67VW;Vst;Vtmax;Z8M4A4A1S19VW;Vst;Vtmax;A3A2S27G3S24G1G2S23G0S24S3S3S6cG4A1SaS1eA1A4M5S23G0G5S22G0A1A3A3S22S4A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S0S25SbS1dVW;Vst;Vtmax;A3A1S26A3").
Hypothesis FB : ltac2:(tb__ "0|0|
S0S25S70S4S10S51A1S1cA3S26A3").
Hypothesis NXS0 : ltac2:(tb__ "0|0|
S81S75S9S11S1bVW;Vst;Vtmax;A3A1A1A2").
Hypothesis ECertS1 : ltac2:(tb__ "0|3|
S0S25S74S4bUfa0S23S34Z7050cS22S34A1A3S75S23S71S72S1bVW;Vst;Vtmax;A3Z1S6Z0M0A1M1A3S22S71A1M2A3S23S71S72S15VW;Vst;Vtmax;A3G0G1A3G2A3A6S26A3").
Hypothesis WC1 : ltac2:(tb__ "0|0|
S0S25SbS11S14VW;Vst;Vtmax;A3A1A1S26A3").
Hypothesis DC1 : ltac2:(tb__ "0|4|
S0S28S21S1fS21S3S3A2M0A1M1S1fS4A1M2A2M3A1S63S11S15VW;Vst;Vtmax;A3A1S11S14VW;Vst;Vtmax;A3A1A2S27G3S24G1G2S23G0S24S3S3S7eSaS16A1A4S22G0A1A3S22S4A1A4A2A3").
Hypothesis NXC1 : ltac2:(tb__ "0|0|
S0S35S9S11S14VW;Vst;Vtmax;A3A1A1S9S11S15VW;Vst;Vtmax;A3A1A1A3").
Hypothesis IC1 : ltac2:(tb__ "0|0|
S0S28S37A1S64S4bSfS11S14VW;Vst;Vtmax;A3A1A1A2S27S37S38A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1Z11A2S6ZdeA1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZbA2SaS16A1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZaA2S6Z0A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZcA2S6Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZdA2S6Z22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZeA2S6ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S3S5S11S14VW;Vst;Vtmax;A3A1ZfA2S6Z0A1A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S35S9S11S14VW;Vst;Vtmax;A3A1A1S51A3").
Hypothesis XC1 : ltac2:(tb__ "0|1|
S0S1fS21S3S3A2M0A1S12S14VW;Vst;Vtmax;A3A1S22G0A1A3").
Hypothesis SK1 : ltac2:(tb__ "0|1|
S0S1fS21S21S3S3A2S3A2M0A1S36S7G0S4aSeS11S14VW;Vst;Vtmax;A3A1A1A4S36S7G0S4aS20S7S20S7S23S7S6bS20S7S46VW;A1S3fA3A3S6aA3S18A3A4A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S6fS4S20S4S20S4S20S4S20S4S45VW;Vst;A2S44S43A1A3S52A3S69A3S68Vtmax;Z8A2A3SdS11S14VW;Vst;Vtmax;A3A1A1A3").

Theorem esec_spine_S : ltac2:(tb__ "0|5|
S53S40S57Q40M0A1M1S3bF_;S8S1fG1A1S61OF_;S0S47Vst;S42A3S0S1fS3eA1VW;S22S3eA1A3F_;S6eVW;Vst;A2S41R7A1S6dR9S58G0ScR6PcA2A2A2S8S1fS4eA1M2S2bS4cG1S65Vsegs;R5RbS14VW;Vst;Vtmax;A3M3S24G2S5cR4S5dR3R2A2A4A5S49VW;Vst;R10RfRdR6RcR5R3A9S5aS2aR5U0A2S2aR5U3A2R4S2aR5U1M4A2R3A5R10R4S39R8S9S11G3A1A1R4A3ReR7S4fS5bS4dR5A1S2aR6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;S8G1S5fVsegs;S3aVsegs;RbR1A1S17VW;Vst;Vtmax;A3S39R2S1aVW;Vst;Vtmax;A3R1A3R9A5R8A3Fa;FrhoX;S8S5fVsegs;S3aVsegs;S49VW;Vst;RdRcRaA5S67VW;Vst;Vtmax;Z8A4R1R9A5R8A3FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FJo;FKc;FA;").
Proof.
  intros A Kc Jo rho tp Q HW HUS HKc HROOM HJo HOK rhoE.
  pose proof (JG_stable nW st A Kc rho HUS HKc) as HST.
  eapply etriple_conseq; [intros w Hw; exact (sec_inst nW st tmax Wa Da Wb FB A Kc rho tp w rhoE HW HUS HKc Hw) | intros w Hw; exact Hw |].
  apply (ecfg_cutS 4000%nat [0x7050c] GW [mkVNA (SS0 W st tmax) 1 (SLit 0)] [mkVNA (ES1 W st tmax) 0 (SLit 0)] (JG W st A Kc rho) Q tp (SS0 W st tmax) rhoE HST).
  - intros n Hn. destruct Hn as [<-|[]]. cbn [vna_state]. exact NXS0.
  - exact ECertS1.
  - intros E' rhoX HinE. destruct HinE as [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact (sec_cs1 nW st tmax WC1 DC1 NXC1 A Kc rho tp w rhoX Hw) | intros w Hw; right; exact Hw |].
    exact (esec_ecall_S IC1 R17 R11 R10 R12 R13 R14 R15 NX1 XC1 SK1 FC1 A Kc Jo rho tp Q HW HUS HKc HROOM HJo HOK rhoX).
  - left. reflexivity.
Qed.
End C6SE.
End SEC2S.
End SpineMallocSec2S.

