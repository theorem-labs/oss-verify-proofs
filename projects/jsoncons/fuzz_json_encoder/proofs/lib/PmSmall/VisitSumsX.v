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

Module VSX.
Definition S2V : expr := EVar 52.          (* [comment removed for export] *)
Definition LIT_LEN : Z := 72.              (* [comment removed for export] *)
Definition wregs (vb : expr) (vk lit_lo : Z) : list SGP.region := [(vb, vk + 264, ELit 40); (vb, vk + 400, ELit 4); (S2V, 0, ELit 24); (ELit 0, lit_lo, ELit LIT_LEN)].
Definition vis_xsum (pc scr lit_lo : Z) : CAX.xsum :=
  CAX.XSUM pc scr 0%nat
    (fun _ _ => Some (ELit 1))
    (fun regs => let '(vb, vk) := split_lit (nth 10 regs (ELit 0)) in wregs vb vk lit_lo)
    (fun _ BL => BL)
    (fun regs cells g BLk => ([], BLk))
    (fun F => F).
End VSX.
