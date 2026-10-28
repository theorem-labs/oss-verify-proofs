(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MXS.
Definition HULL_LO : Z := GK.HULL_LO.  Definition HULL_HI : Z := GK.HULL_HI.
Definition regs_apart (hd : CH.hdecl) (BLk : CA.blocks) : list SGP.region := CH.stack_reg hd :: CH.hd_crs hd ++ CH.hd_wrs hd ++ CH.blk_regs BLk.
Definition blk_facts_n (hd : CH.hdecl) (g : nat) (n : expr) (BLk : CA.blocks) : list kentry :=
  let gp := EVar g in
  [ KRange gp 4096 140737488355328; KAlign gp 16; KUnk (SA gp 0) n; KWr (SA gp 0) n;
    KDisj (SA gp 0) n (SA (ELit 0) HULL_LO) (ELit (HULL_HI - HULL_LO)) ]
  ++ map (fun r : SGP.region => let '(b, o, m) := r in KDisj (SA gp 0) n (SA b o) m) (regs_apart hd BLk).
Definition mallocx_xsum (hd : CH.hdecl) (pc scr : Z) (G0 : nat) (N : expr) : CAX.xsum :=
  CAX.XSUM pc scr 1%nat
    (fun _ g => Some (EVar g))
    (fun _ => [])
    (fun regs BL => BL)
    (fun regs cells g BLk => let n := nth 10 regs (ELit 0) in (blk_facts_n hd g n BLk, (EVar g, n) :: BLk))
    (fun F => F ++ [(EVar G0, 0, N)]).
End MXS.
