(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PSU2X.
(* [comment removed for export] *)
Definition wregsx (vb : expr) (lit_lo : Z) (pb : expr) (pk : Z) (eb : expr) (ek : Z) : list SGP.region :=
  (pb, pk, ELit 272) :: (eb, ek, ELit 16) :: PSU.statics_wregs ++ VSX.wregs vb 0 lit_lo.
Definition ptransLx_xsum (vb : expr) (lit_lo : Z) (pc scr : Z) (preg ereg : nat) (fcells : list (Z * Z)) : CAX.xsum :=
  CAX.XSUM pc scr 5%nat
    (fun _ _ => None)
    (fun regs => let '(pb, pk) := split_lit (nth preg regs (ELit 0)) in let '(eb, ek) := split_lit (nth ereg regs (ELit 0)) in wregsx vb lit_lo pb pk eb ek)
    (fun _ _ => [])
    (fun regs cells g BLk => let '(eb, ek) := split_lit (nth ereg regs (ELit 0)) in
                             (PSU.pt_news eb ek g, [(EVar (g + 1), PSU.emul2 (EVar (g + 2))); (EVar (g + 3), EVar (g + 4))]))
    (fun F => match F with r :: _ => r :: map (fun c : Z * Z => let '(pb, pk) := (EVar 10, 0) in (pb, pk + fst c, ELit (snd c))) fcells | [] => [] end).
End PSU2X.
