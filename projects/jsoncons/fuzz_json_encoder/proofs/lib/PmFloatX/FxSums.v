(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ESU2N.
(* [comment removed for export] *)
Definition sinkN_xsum (pc scr : Z) (s2e : expr) (a0 : option Z) : CAX.xsum :=
  CAX.XSUM pc scr 0%nat
    (fun _ _ => match a0 with Some z => Some (ELit z) | None => None end)
    (fun regs => [(s2e, 0, ELit 24)])
    (fun regs BL => BL)
    (fun regs cells g BLk => ([], BLk))
    (fun F => F).
(* [comment removed for export] *)
Definition pure0_xsum (pc scr : Z) (wr : list expr -> list SGP.region) (nw : list expr -> nat -> list kentry) : CAX.xsum :=
  CAX.XSUM pc scr 0%nat (fun _ _ => None) wr (fun regs BL => BL) (fun regs cells g BLk => (nw regs g, BLk)) (fun F => F).
End ESU2N.

