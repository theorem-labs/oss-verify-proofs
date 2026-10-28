(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PSU2.
Definition eadd := PSU.eadd.  Definition esub := PSU.esub.

Definition vec_cells (ob : expr) (ok : Z) (slen' : expr) (g : nat) : list kentry :=
  let gb := EVar g in let gc := EVar (g + 1) in
  [ KWord (SA ob ok) 8 gb; KWord (SA ob (ok + 8)) 8 (eadd gb slen'); KWord (SA ob (ok + 16)) 8 (eadd gb gc);
    KRange gc 66 1056; KRange (esub gc slen') 0 1056 ].
Definition vblk_facts (hd : CH.hdecl) (g : nat) (BLk : CA.blocks) : list kentry :=
  let gb := EVar g in let gc := EVar (g + 1) in
  [ KRange gb 4096 140737488355328; KAlign gb 16; KUnk (SA gb 0) gc; KWr (SA gb 0) gc;
    KDisj (SA gb 0) gc (SA (ELit 0) PSU.HULL_LO) (ELit (PSU.HULL_HI - PSU.HULL_LO)) ]
  ++ map (fun r : SGP.region => let '(b, o, m) := r in KDisj (SA gb 0) gc (SA b o) m) (PSU.regs_apart hd BLk).
Definition vec_xsum (hd : CH.hdecl) (pc scr : Z) (oreg : nat) : CAX.xsum :=
  CAX.XSUM pc scr 2%nat
    (fun _ _ => None)
    (fun regs => let '(ob, ok) := split_lit (nth oreg regs (ELit 0)) in [(ob, ok, ELit 24)])
    (fun regs BL => firstn 1 BL)
    (fun regs cells g BLk =>
       let '(ob, ok) := split_lit (nth oreg regs (ELit 0)) in
       let c0 := match CAX.cell_at cells ob ok 8 with Some e => e | None => ELit 0 end in
       let c8 := match CAX.cell_at cells ob (ok + 8) 8 with Some e => e | None => ELit 0 end in
       let slen' := APC.eaddz (esub c8 c0) 1 in
       (vec_cells ob ok slen' g ++ vblk_facts hd g BLk, BLk ++ [(EVar g, EVar (g + 1))]))
    (fun F => F).

Definition pop_xsum (pc scr : Z) : CAX.xsum :=
  CAX.XSUM pc scr 1%nat
    (fun regs g => Some (EVar g))
    (fun regs => let '(pb, pk) := split_lit (nth 10 regs (ELit 0)) in [(pb, pk + 256, ELit 8)])
    (fun _ BL => BL)
    (fun regs cells g BLk =>
       let '(pb, pk) := split_lit (nth 10 regs (ELit 0)) in
       let c8 := match CAX.cell_at cells pb (pk + 256) 8 with Some e => e | None => ELit 0 end in
       ([KWord (SA pb (pk + 256)) 8 (APC.eaddz c8 (-1)); KRange (EVar g) 0 255], BLk))
    (fun F => F).

Definition parent_xsum (pc scr : Z) : CAX.xsum :=
  CAX.XSUM pc scr 1%nat
    (fun regs g => Some (EVar g))
    (fun regs => [])
    (fun _ BL => BL)
    (fun regs cells g BLk => ([KRange (EVar g) 0 255], BLk))
    (fun F => F).

Definition ptransL_xsum (pc scr : Z) (preg ereg : nat) (fcells : list (Z * Z)) : CAX.xsum :=
  CAX.XSUM pc scr 5%nat
    (fun _ _ => None)
    (fun regs => let '(pb, pk) := split_lit (nth preg regs (ELit 0)) in let '(eb, ek) := split_lit (nth ereg regs (ELit 0)) in
                 (pb, pk, ELit 272) :: (eb, ek, ELit 16) :: PSU.statics_wregs)
    (fun _ _ => [])
    (fun regs cells g BLk => let '(eb, ek) := split_lit (nth ereg regs (ELit 0)) in
                             (PSU.pt_news eb ek g, [(EVar (g + 1), PSU.emul2 (EVar (g + 2))); (EVar (g + 3), EVar (g + 4))]))
    (fun F => match F with r :: _ => r :: map (fun c : Z * Z => let '(pb, pk) := (EVar 10, 0) in (pb, pk + fst c, ELit (snd c))) fcells | [] => [] end).

Definition with_F (x : CAX.xsum) (f : list SGP.region -> list SGP.region) : CAX.xsum :=
  CAX.XSUM (CAX.xs_pc x) (CAX.xs_scr x) (CAX.xs_ng x) (CAX.xs_a0 x) (CAX.xs_wregs x) (CAX.xs_keep x) (CAX.xs_new x) f.
End PSU2.
