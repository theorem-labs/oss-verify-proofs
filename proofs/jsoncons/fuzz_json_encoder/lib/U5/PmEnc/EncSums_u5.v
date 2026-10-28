(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ESU.
(* [comment removed for export] *)
Definition sink_xsum (pc scr : Z) : CAX.xsum :=
  CAX.XSUM pc scr 0%nat
    (fun _ _ => None)
    (fun regs => let '(ob, ok) := split_lit (nth 10 regs (ELit 0)) in [(ob, ok, ELit 24)])
    (fun regs BL => BL)
    (fun regs cells g BLk => ([], BLk))
    (fun F => F).
(* [comment removed for export] *)
Definition sinkret_xsum (pc scr : Z) (s2e : expr) : CAX.xsum :=
  CAX.XSUM pc scr 1%nat
    (fun _ g => Some (EVar g))
    (fun regs => [(s2e, 0, ELit 24)])
    (fun regs BL => BL)
    (fun regs cells g BLk => ([KRange (EVar g) 0 1125899906842624], BLk))
    (fun F => F).
(* [comment removed for export] *)
Definition cp_xsum (pc scr : Z) (breg : nat) : CAX.xsum :=
  CAX.XSUM pc scr 0%nat
    (fun regs _ => Some (APC.eaddz (nth 10 regs (ELit 0)) 1))
    (fun regs => let '(ob, ok) := split_lit (nth 12 regs (ELit 0)) in [(ob, ok, ELit 4)])
    (fun regs BL => BL)
    (fun regs cells g BLk => let '(ob, ok) := split_lit (nth 12 regs (ELit 0)) in
       ([KWord (SA ob ok) 4 (nth breg regs (ELit 0)); KRange (EVar (g + 5)) 0 0], BLk))
    (fun F => F).
(* [comment removed for export] *)
Definition tail_xsum (pc scr : Z) : CAX.xsum :=
  CAX.XSUM pc scr 0%nat (fun _ _ => None) (fun _ => []) (fun regs BL => BL) (fun regs cells g BLk => ([], BLk)) (fun F => F).

(* [comment removed for export] *)
Definition HULL_LO : Z := 0x10000.  Definition HULL_HI : Z := 0xfe000.
Definition regs_apart (hd : CH.hdecl) (BLk : CA.blocks) : list SGP.region := CH.stack_reg hd :: CH.hd_crs hd ++ CH.hd_wrs hd ++ CH.blk_regs BLk.
Definition blk_facts_n (hd : CH.hdecl) (g : nat) (n : expr) (BLk : CA.blocks) : list kentry :=
  let gp := EVar g in
  [ KRange gp 4096 140737488355328; KAlign gp 16; KUnk (SA gp 0) n; KWr (SA gp 0) n;
    KDisj (SA gp 0) n (SA (ELit 0) HULL_LO) (ELit (HULL_HI - HULL_LO)) ]
  ++ map (fun r : SGP.region => let '(b, o, m) := r in KDisj (SA gp 0) n (SA b o) m) (regs_apart hd BLk).
Definition opnew_xsum (hd : CH.hdecl) (pc scr : Z) (G0 : nat) (N : expr) : CAX.xsum :=
  CAX.XSUM pc scr 1%nat
    (fun _ g => Some (EVar g))
    (fun _ => [])
    (fun regs BL => BL)
    (fun regs cells g BLk => let n := nth 10 regs (ELit 0) in (blk_facts_n hd g n BLk, (EVar g, n) :: BLk))
    (fun F => F ++ [(EVar G0, 0, N)]).
End ESU.
