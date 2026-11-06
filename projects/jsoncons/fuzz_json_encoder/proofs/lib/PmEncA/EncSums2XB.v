(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface HeapIfaceA L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsXB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ESA2.
Definition HIB : Z := 2 ^ 47 - 2 ^ 23.
Definition push_news (regs : list expr) (g : nat) : list kentry :=
  let '(vb, vk) := split_lit (nth 10 regs (ELit 0)) in      (* [comment removed for export] *)
  let '(sb, sk) := split_lit (nth 2 regs (ELit 0)) in       (* [comment removed for export] *)
  [KRange (EVar g) 4096 HIB; KAlign (EVar g) 16; KRange (EVar (g + 1)) 32 65536;
   KDisj (SA vb (vk - 264)) (ELit 408) (SA (EVar g) 0) (EVar (g + 1));
   KDisj (SA sb (sk + 112 - 13824)) (ELit 13824) (SA (EVar g) 0) (EVar (g + 1))].      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition push_xsumA (pc scr : Z) (wold : list SGP.region) (wnews : list expr -> nat -> list kentry) (nfoot : nat) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 2%nat
    (fun _ _ => None)
    (fun regs => let '(vb, vk) := split_lit (nth 10 regs (ELit 0)) in (vb, vk, ELit 24) :: wold)
    (fun regs BL => [])
    (fun regs cells g BLk => (ESA.STATICS ++ push_news regs g ++ wnews regs g, [(EVar g, EVar (g + 1)%nat)]))
    (fun F => firstn nfoot F)) (fun _ => []).
Definition hcoln_xsumA (pc scr : Z) (s2e : expr) (news : list expr -> list kentry -> list kentry) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 0%nat
    (fun _ _ => None)
    (fun regs => [ESA.col_region regs; (s2e, 0, ELit 24)])
    (fun regs BL => BL)
    (fun regs cells g BLk => (ESA.STATICS ++ news regs cells, BLk))
    (fun F => F)) (fun _ => []).
(* [comment removed for export] *)
Definition push_xsumXB (pc scr : Z) (wold : list SGP.region) (wnews : list expr -> nat -> list kentry) (nfoot : nat) (a0f : list expr -> nat -> option expr) (fadd : list SGP.region) : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM pc scr 2%nat
    a0f
    (fun regs => let '(vb, vk) := split_lit (nth 10 regs (ELit 0)) in (vb, vk, ELit 24) :: wold)
    (fun regs BL => [])
    (fun regs cells g BLk => let '(vb, vk) := split_lit (nth 10 regs (ELit 0)) in (ESA.STATICS ++ push_news regs g ++ wnews regs g ++ [KWr (SA vb (vk + 8)) (ELit 8)], [(EVar g, EVar (g + 1)%nat)]))
    (fun F => firstn nfoot F ++ fadd)) (fun _ => []).
End ESA2.
