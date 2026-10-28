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
Definition ITR : list (Z * nat) := [(291032, 64%nat); (798592, 40%nat); (427116, 4%nat); (778312, 400%nat); (290624, 37%nat); (290772, 46%nat); (290956, 19%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [291252].
Definition HDECL : CH.hdecl := CH.HD (8352) (8224) [((EVar 11), (0), ELit 1)] [((EVar 10), (0), ELit 24)] [].
Definition CSUMS : list CA.callsum := [CA.cs_malloc 719096; CA.cs_free_ 718776].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 291032 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KWord (SA (EVar 10) (0)) 8 (EVar 32);
   KWord (SA (EVar 10) (8)) 8 (APC.eadd (EVar 32) (EVar 34));
   KWord (SA (EVar 10) (16)) 8 (APC.eadd (EVar 32) (EVar 34));
   KRange (EVar 34) (1) (1026);
   KWord (SA (EVar 11) (0)) 1 (EVar 35);
   KRange (EVar 35) (0) (255);
   KRange (EVar 11) (1099511627776) (140737488355328);
   KBlob (SA (EVar 32) (0)) (EVar 34) 0;
   KUnk (SA (EVar 32) (0)) (EVar 34);
   KWr (SA (EVar 32) (0)) (EVar 34);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (16);
   KWr (SA (EVar 10) (0)) (ELit (24));
   KRange (EVar 10) (1099511627776) (140737488355328);
   KAlign (EVar 10) (8);
   KUnk (SA (EVar 2) (-8352)) (ELit (8352));
   KWr (SA (EVar 2) (-8352)) (ELit (8352));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8352)) (ELit (8352)) (SA (EVar 10) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-8352)) (ELit (8352)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 2) (-8352)) (ELit (8352)) (SA (EVar 11) (0)) (ELit (1));
   KDisj (SA (EVar 10) (0)) (ELit (24)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 11) (0)) (ELit (1)) (SA (EVar 32) (0)) (EVar 34)]
  48 [((EVar 2), (-8352), ELit 8352); ((EVar 10), (0), ELit 24); ((EVar 32), (0), ((EVar 34)))] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [((EVar 32), (EVar 34))].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 300 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
