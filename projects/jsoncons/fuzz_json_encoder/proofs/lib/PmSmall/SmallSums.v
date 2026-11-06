(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SSU.
Definition guard_news (gb : expr) (gk : Z) (b0 b1 : Z) : list kentry := [KWord (SA gb gk) 1 (ELit b0); KWord (SA gb (gk + 1)) 1 (ELit b1)].
Definition guard_acq_xsum (pc : Z) : CAX.xsum :=
  CAX.XSUM pc 0 0%nat
    (fun _ _ => Some (ELit 1))
    (fun regs => let '(gb, gk) := split_lit (nth 10 regs (ELit 0)) in [(gb, gk, ELit 2)])
    (fun _ BL => BL)
    (fun regs cells g BLk => let '(gb, gk) := split_lit (nth 10 regs (ELit 0)) in (guard_news gb gk 0 2, BLk))
    (fun F => F).
Definition guard_rel_xsum (pc : Z) : CAX.xsum :=
  CAX.XSUM pc 0 0%nat
    (fun _ _ => None)
    (fun regs => let '(gb, gk) := split_lit (nth 10 regs (ELit 0)) in [(gb, gk, ELit 2)])
    (fun _ BL => BL)
    (fun regs cells g BLk => let '(gb, gk) := split_lit (nth 10 regs (ELit 0)) in (guard_news gb gk 1 1, BLk))
    (fun F => F).
(* [comment removed for export] *)
Definition atexit_news (ax drvf drva : Z) (f a : expr) : list kentry :=     (* [comment removed for export] *)
  [KWord (SA (ELit 0) ax) 1 (ELit 0); KWord (SA (ELit 0) (ax + 4)) 4 (ELit 0); KWord (SA (ELit 0) (ax + 8)) 4 (ELit 2);
   KWord (SA (ELit 0) (ax + 16)) 8 (ELit (ax + 24)); KWord (SA (ELit 0) (ax + 24)) 8 (ELit 0);
   KWord (SA (ELit 0) (ax + 32)) 8 (ELit drvf); KWord (SA (ELit 0) (ax + 288)) 8 (ELit drva);
   KWord (SA (ELit 0) (ax + 40)) 8 f; KWord (SA (ELit 0) (ax + 296)) 8 a].
Definition atexit_xsum (pc scr ax drvf drva : Z) : CAX.xsum :=
  CAX.XSUM pc scr 0%nat
    (fun _ _ => Some (ELit 0))
    (fun regs => [(ELit 0, ax, ELit 544)])
    (fun _ BL => BL)
    (fun regs cells g BLk => (atexit_news ax drvf drva (nth 10 regs (ELit 0)) (nth 11 regs (ELit 0)), BLk))
    (fun F => F).
End SSU.
