(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmLibSpecsW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseBridges6W_u5 ParseBridges6WU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseSW Require Import ParseBridgesLW_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PBLWU.
Import PML PMES.
Section WADAPTU.
Context {SCFG_P : ScfgP}.
Variables (L : heap_layout) (HI : heap_iface) (RM : PMW.refmodel).
Lemma gbxlw_EU : forall f MIn inp WFin BBin PAin PAout pc scr Args Rel,
  PMW.ptrans_gbxlwU L HI RM f MIn inp WFin BBin PAin PAout pc scr Args Rel ->
  forall th : PB6W.THW RM, PB6WU.ptrans_gbxEU L HI WFin BBin PAin PAout pc scr (PBLW.argsXLW RM Args MIn th) Rel (PB6W.expostW RM f inp th) (PB6WU.roomW RM f inp th).
Proof.
  intros f MIn inp WFin BBin PAin PAout pc scr Args Rel HW [[w x] c] LBo cr sp r P V E S2 B kx bx g ps eg fx R M model K HH Hmo HK HFP PRE POST.
  apply (HW LBo cr sp r P V E S2 B kx bx g ps eg w x c fx R M model K HH Hmo HK HFP).
  - destruct PRE as (H1 & (HA & HWB & HMI) & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18).
    exact (conj H1 (conj HA (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj HWB (conj HMI H18))))))))))))))))))).
  - intros fx' R' M' model' LB' cr' LBk W0 HFP' PO. apply (POST fx' R' M' model' LB' cr' LBk W0 HFP').
    destruct PO as (ps' & code & g' & eg' & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17).
    exists ps', code, g', eg'.
    exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj Q9 (conj Q10 (conj Q11 (conj Q12 (conj Q13 (conj Q14 (conj Q15 (conj Q16 Q17)))))))))))))))).
Qed.
End WADAPTU.
End PBLWU.
