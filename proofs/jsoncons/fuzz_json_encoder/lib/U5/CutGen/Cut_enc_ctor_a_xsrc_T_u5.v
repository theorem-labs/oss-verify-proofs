(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(240064, 36%nat); (242720, 84%nat); (243056, 123%nat); (243740, 56%nat); (244008, 55%nat); (254880, 163%nat); (288164, 14%nat); (436872, 83%nat); (713980, 3%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [244100; 240168; 427124; 255532; 681628; 434060].
Definition HDECL : CH.hdecl := CH.HD (0) (8224) [] [] [].
Definition CSUMS : list CA.callsum := [].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 240064 [EVar 0; (EVar 33); (EVar 2); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KUnk (SA (EVar 2) (-400)) (ELit (400));
   KWr (SA (EVar 2) (-400)) (ELit (400));
   KRange (EVar 42) (1099511627776) (140737488355328);
   KRange (EVar 43) (1099511627776) (140737488355328);
   KRange (EVar 64) (1099511627776) (140737488355328);
   KImg (65536) (827984);
   KWord (SA (EVar 43) (0)) 8 (EVar 64);
   KWr (SA (EVar 43) (0)) (ELit (8));
   KAlign (EVar 42) (8);
   KUnk (SA (EVar 42) (0)) (ELit (408));
   KWr (SA (EVar 42) (0)) (ELit (408));
   KDisj (SA (EVar 2) (-400)) (ELit (400)) (SA (EVar 42) (0)) (ELit (408));
   KDisj (SA (EVar 2) (-400)) (ELit (400)) (SA (EVar 43) (0)) (ELit (8));
   KDisj (SA (EVar 42) (0)) (ELit (408)) (SA (EVar 43) (0)) (ELit (8))]
  65 [((EVar 2), (-400), ELit 400); ((EVar 42), (0), ELit 408); ((EVar 43), (0), ELit 8)] [] (ELit (10)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 900 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
