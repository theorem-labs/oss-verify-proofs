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

Module ESU2.
Definition col_region (regs : list expr) : SGP.region := let '(vb, vk) := split_lit (nth 10 regs (ELit 0)) in (vb, vk + 296, ELit 8).

Definition hcall_xsum (pc scr : Z) (s2e : expr) (blk : CA.blocks) (news : list expr -> list kentry -> list kentry) : CAX.xsum :=
  CAX.XSUM pc scr 0%nat
    (fun _ _ => None)
    (fun regs => [col_region regs; (s2e, 0, ELit 24)])
    (fun regs BL => [])
    (fun regs cells g BLk => (news regs cells, blk))
    (fun F => F).

Definition hcol_xsum (pc scr : Z) (s2e : expr) : CAX.xsum :=
  CAX.XSUM pc scr 0%nat
    (fun _ _ => None)
    (fun regs => [col_region regs; (s2e, 0, ELit 24)])
    (fun regs BL => BL)
    (fun regs cells g BLk => ([], BLk))
    (fun F => F).

(* [comment removed for export] *)
Definition lit_news (S TXT LEN : Z) : list kentry :=
  [KWord (SA (ELit 0) (S + 16)) 1 (ELit 1); KWord (SA (ELit 0) (S + 17)) 1 (ELit 1); KWord (SA (ELit 0) S) 8 (ELit TXT); KWord (SA (ELit 0) (S + 8)) 8 (ELit LEN)].
Definition lit_xsum (pc scr S TXT LEN : Z) : CAX.xsum :=
  CAX.XSUM pc scr 0%nat
    (fun _ _ => Some (ELit TXT))
    (fun regs => [(ELit 0, S, ELit 18)])
    (fun regs BL => BL)
    (fun regs cells g BLk => (KRange (EVar (g + 5)) LEN LEN :: lit_news S TXT LEN, BLk))
    (fun F => F).
End ESU2.
