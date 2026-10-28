(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto HeapIface L5Defs L5Core.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PSU.
Definition eadd (a b : expr) : expr := APC.eadd a b.
Definition esub (a b : expr) : expr := APC.esub a b.
Definition emul2 (k : expr) : expr := APC.escale 2 k.
Definition HULL_LO : Z := 0x10000.  Definition HULL_HI : Z := 0xfe000.

(* [comment removed for export] *)
Inductive szkind : Type :=
| SzAdd1                      (* [comment removed for export] *)
| SzAddReg (r : nat)          (* [comment removed for export] *)
| SzGhost (d : Z)             (* [comment removed for export] *)
| SzSubReg (r1 r2 : nat).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition str_cells (ob : expr) (ok : Z) (size' : expr) (g : nat) (KMIN : Z) : list kentry :=
  let gp := EVar g in let gk := EVar (g + 1) in let cap := emul2 gk in
  [ KWord (SA ob ok) 8 (APC.eaddz cap 1); KWord (SA ob (ok + 8)) 8 size'; KWord (SA ob (ok + 16)) 8 gp;
    KWord (SA (eadd size' gp) 0) 1 (ELit 0);
    KRange gk KMIN 67108864; KRange (esub (APC.eaddz cap (-1)) size') 0 140737488355328; KAlign cap 8 ].
Definition regs_apart (hd : CH.hdecl) (BLk : CA.blocks) : list SGP.region := CH.stack_reg hd :: CH.hd_crs hd ++ CH.hd_wrs hd ++ CH.blk_regs BLk.
Definition blk_facts (hd : CH.hdecl) (g : nat) (BLk : CA.blocks) : list kentry :=
  let gp := EVar g in let cap := emul2 (EVar (g + 1)) in
  [ KRange gp 4096 140737488355328; KAlign gp 16; KUnk (SA gp 0) cap; KWr (SA gp 0) cap;
    KDisj (SA gp 0) cap (SA (ELit 0) HULL_LO) (ELit (HULL_HI - HULL_LO)) ]
  ++ map (fun r : SGP.region => let '(b, o, m) := r in KDisj (SA gp 0) cap (SA b o) m) (regs_apart hd BLk).
(* [comment removed for export] *)
Definition nul_facts (hd : CH.hdecl) (size' : expr) (g : nat) (BLk : CA.blocks) : list kentry :=
  map (fun r : SGP.region => let '(b, o, m) := r in KDisj (SA (eadd size' (EVar g)) 0) (ELit 1) (SA b o) m) (regs_apart hd BLk).
Definition str_news (hd : CH.hdecl) (ob : expr) (ok : Z) (size' : expr) (g : nat) (KMIN : Z) (BLk : CA.blocks) : list kentry :=
  str_cells ob ok size' g KMIN ++ blk_facts hd g BLk ++ nul_facts hd size' g BLk.

Definition str_xsum (hd : CH.hdecl) (pc scr : Z) (oreg : nat) (sz : szkind) (KMIN : Z) : CAX.xsum :=
  CAX.XSUM pc scr (match sz with SzGhost _ => 3%nat | _ => 2%nat end)
    (fun _ _ => None)
    (fun regs => let '(ob, ok) := split_lit (nth oreg regs (ELit 0)) in [(ob, ok, ELit 24)])
    (fun regs BL => tl BL)                                                    (* [comment removed for export] *)
    (fun regs cells g BLk =>
       let '(ob, ok) := split_lit (nth oreg regs (ELit 0)) in
       let size := match CAX.cell_at cells ob (ok + 8) 8 with Some e => e | None => ELit 0 end in
       let size' := match sz with SzAdd1 => APC.eaddz size 1 | SzAddReg r => eadd size (nth r regs (ELit 0)) | SzGhost _ => EVar (g + 2)
                                  | SzSubReg r1 r2 => eadd size (esub (nth r1 regs (ELit 0)) (nth r2 regs (ELit 0))) end in
       let extra := match sz with
                    | SzGhost d => [KRange (EVar (g + 2)) 0 67108864; KRange (esub (EVar (g + 2)) size) 0 d]
                    | _ => [] end in
       (str_news hd ob ok size' g KMIN BLk ++ extra, (EVar g, emul2 (EVar (g + 1))) :: BLk))
    (fun F => F).

(* [comment removed for export] *)
Definition OBJ_JSON_CATEGORY : Z := 0xcb278.
Definition statics_wregs : list SGP.region := [(ELit 0, 0xdb5c0, ELit 2); (ELit 0, 0xfd058, ELit 544)].
Definition setec_news (eb : expr) (ek : Z) (code : expr) : list kentry :=
  [KWord (SA eb ek) 4 code; KWord (SA eb (ek + 8)) 8 (ELit OBJ_JSON_CATEGORY)].
Definition setec_xsum (pc scr : Z) : CAX.xsum :=
  CAX.XSUM pc scr 0%nat
    (fun regs _ => Some (nth 10 regs (ELit 0)))
    (fun regs => let '(eb, ek) := split_lit (nth 10 regs (ELit 0)) in (eb, ek, ELit 16) :: statics_wregs)
    (fun _ BL => BL)
    (fun regs cells g BLk => let '(eb, ek) := split_lit (nth 10 regs (ELit 0)) in (setec_news eb ek (nth 11 regs (ELit 0)), BLk))
    (fun F => F).

(* [comment removed for export] *)
Definition pt_news (eb : expr) (ek : Z) (g : nat) : list kentry := [KWord (SA eb ek) 4 (EVar g); KRange (EVar g) 0 31].
Definition ptrans_xsum (pc scr : Z) (preg ereg : nat) : CAX.xsum :=
  CAX.XSUM pc scr 5%nat
    (fun _ _ => None)
    (fun regs => let '(pb, pk) := split_lit (nth preg regs (ELit 0)) in let '(eb, ek) := split_lit (nth ereg regs (ELit 0)) in
                 (pb, pk, ELit 272) :: (eb, ek, ELit 16) :: statics_wregs)
    (fun _ _ => [])
    (fun regs cells g BLk => let '(eb, ek) := split_lit (nth ereg regs (ELit 0)) in
                             (pt_news eb ek g, [(EVar (g + 1), emul2 (EVar (g + 2))); (EVar (g + 3), EVar (g + 4))]))
    (fun F => match F with r :: _ => [r] | [] => [] end).
End PSU.
