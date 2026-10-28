(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PSU3C.
Definition ptrans_xsumc (pc scr : Z) (preg ereg : nat) (vb : expr) : CAX.xsum :=
  CAX.XSUM pc scr 5%nat
    (fun _ _ => None)
    (fun regs => let '(pb, pk) := split_lit (nth preg regs (ELit 0)) in let '(eb, ek) := split_lit (nth ereg regs (ELit 0)) in
                 (pb, pk, ELit 272) :: (eb, ek, ELit 16) :: (vb, 8, ELit 40) :: PSU.statics_wregs)
    (fun _ _ => [])
    (fun regs cells g BLk => let '(eb, ek) := split_lit (nth ereg regs (ELit 0)) in
                             (PSU.pt_news eb ek g, [(EVar (g + 1), PSU.emul2 (EVar (g + 2))); (EVar (g + 3), EVar (g + 4))]))
    (fun F => match F with r :: _ => [r] | [] => [] end).
End PSU3C.
