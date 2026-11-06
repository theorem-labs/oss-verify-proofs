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

Module SSU2.
(* [comment removed for export] *)
Definition a1var (g ng : nat) : nat := (g + ng + 5)%nat.
Definition validate_news (g : nat) : list kentry := [KRange (EVar (a1var g 1)) 0 6].
Definition validate_xsum (pc scr : Z) : CAX.xsum :=
  CAX.XSUM pc scr 1%nat
    (fun regs g => Some (EVar g))
    (fun regs => [])
    (fun _ BL => BL)
    (fun regs cells g BLk => (validate_news g, BLk))
    (fun F => F).
(* [comment removed for export] *)
Definition decu64_news (vb : expr) (vk : Z) (g : nat) : list kentry := [KWord (SA vb vk) 8 (EVar (g + 1)); KRange (EVar (a1var g 2)) 0 34].
Definition decu64_xsum (pc scr : Z) : CAX.xsum :=
  CAX.XSUM pc scr 2%nat
    (fun regs g => Some (EVar g))
    (fun regs => let '(vb, vk) := split_lit (nth 12 regs (ELit 0)) in [(vb, vk, ELit 8)])
    (fun _ BL => BL)
    (fun regs cells g BLk => let '(vb, vk) := split_lit (nth 12 regs (ELit 0)) in (decu64_news vb vk g, BLk))
    (fun F => F).
(* [comment removed for export] *)
Definition decstr_xsum (pc scr errno : Z) : CAX.xsum :=
  CAX.XSUM pc scr 2%nat
    (fun regs g => Some (EVar g))
    (fun regs => let '(vb, vk) := split_lit (nth 12 regs (ELit 0)) in [(vb, vk, ELit 8); (ELit 0, errno, ELit 4)])
    (fun _ BL => BL)
    (fun regs cells g BLk => let '(vb, vk) := split_lit (nth 12 regs (ELit 0)) in (decu64_news vb vk g, BLk))
    (fun F => F).
(* [comment removed for export] *)
Definition strtod_xsum (pc scr errno : Z) (endreg : nat) : CAX.xsum :=
  CAX.XSUM pc scr 0%nat
    (fun _ _ => None)
    (fun regs => let '(eb, ek) := split_lit (nth 11 regs (ELit 0)) in [(eb, ek, ELit 8); (ELit 0, errno, ELit 4)])
    (fun _ BL => BL)
    (fun regs cells g BLk => let '(eb, ek) := split_lit (nth 11 regs (ELit 0)) in ([KWord (SA eb ek) 8 (nth endreg regs (ELit 0))], BLk))
    (fun F => F).
End SSU2.
