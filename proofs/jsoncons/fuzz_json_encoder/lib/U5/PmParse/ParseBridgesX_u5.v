(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5 ParseSums2X_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PBX.
Section Chk.
Variable NF : nat.
Variable d : CH.hdecl.
Variable EB : expr.
Variable EK : Z.
Variable PBx : expr.
Variable PKx : Z.
Variable CSCR : Z.
Variable VB : expr.        (* [comment removed for export] *)
Variable lit_lo : Z.       (* [comment removed for export] *)
Definition ptrans_chkx (ereg : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  let nx := (CC.cp_nx cj - APC.NCS - 5)%nat in
  match split_lit (nth 10 regs (ELit 0)), split_lit (nth ereg regs (ELit 0)) with
  | (pb, pk), (eb, ek) =>
      if (expr_eqb pb PBx && Z.eqb pk PKx && expr_eqb eb EB && Z.eqb ek EK && Z.leb 0 CSCR
          && CH2.blocks_eqb BLj [(EVar (nx + 1), PSU.emul2 (EVar (nx + 2))); (EVar (nx + 3), EVar (nx + 4))])%bool
      then CH2.custom_chk NF d CSCR 5 [] (PSU2X.wregsx VB lit_lo pb pk eb ek) (PSU.pt_news eb ek nx) None c ps cj BLi
      else None
  end.
End Chk.
End PBX.
