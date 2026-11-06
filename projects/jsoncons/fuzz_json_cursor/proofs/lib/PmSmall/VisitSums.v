(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module VSU.
Definition fl (vb : expr) (vk flags : Z) : kentry := KWord (SA vb (vk + 8)) 8 (ELit flags).
Definition const_news (vb : expr) (vk flags : Z) : list kentry := [fl vb vk flags].
Definition bool_news (vb : expr) (vk : Z) (x : expr) : list kentry := [fl vb vk 8; KWord (SA vb (vk + 32)) 1 x].
Definition val_news (vb : expr) (vk flags : Z) (x : expr) : list kentry := [fl vb vk flags; KWord (SA vb (vk + 32)) 8 x].
Definition text_news (vb : expr) (vk flags : Z) (svb : expr) (svk : Z) (cells : list kentry) : list kentry :=
  match CAX.cell_at cells svb svk 8, CAX.cell_at cells svb (svk + 8) 8 with
  | Some p, Some n => [fl vb vk flags; KWord (SA vb (vk + 32)) 8 p; KWord (SA vb (vk + 40)) 8 n]
  | _, _ => [fl vb vk flags]
  end.
Definition dbl_news (vb : expr) (vk : Z) (g : nat) : list kentry := [fl vb vk 128; KWord (SA vb (vk + 32)) 8 (EVar g)].

Definition vxs (pc scr : Z) (ng : nat) (nw : expr -> Z -> list expr -> list kentry -> nat -> list kentry) : CAX.xsum :=
  CAX.XSUM pc scr ng
    (fun _ _ => Some (ELit 1))
    (fun regs => let '(vb, vk) := split_lit (nth 10 regs (ELit 0)) in [(vb, vk + 8, ELit 40)])
    (fun _ BL => BL)
    (fun regs cells g BLk => let '(vb, vk) := split_lit (nth 10 regs (ELit 0)) in (nw vb vk regs cells g, BLk))
    (fun F => F).
Definition const_xsum (pc scr flags : Z) : CAX.xsum := vxs pc scr 0 (fun vb vk _ _ _ => const_news vb vk flags).
Definition bool_xsum (pc scr : Z) : CAX.xsum := vxs pc scr 0 (fun vb vk regs _ _ => bool_news vb vk (nth 11 regs (ELit 0))).
Definition val_xsum (pc scr flags : Z) : CAX.xsum := vxs pc scr 0 (fun vb vk regs _ _ => val_news vb vk flags (nth 11 regs (ELit 0))).
Definition text_xsum (pc scr flags : Z) : CAX.xsum :=
  vxs pc scr 0 (fun vb vk regs cells _ => let '(svb, svk) := split_lit (nth 11 regs (ELit 0)) in text_news vb vk flags svb svk cells).
Definition dbl_xsum (pc scr : Z) : CAX.xsum := vxs pc scr 1 (fun vb vk _ _ g => dbl_news vb vk g).
End VSU.
