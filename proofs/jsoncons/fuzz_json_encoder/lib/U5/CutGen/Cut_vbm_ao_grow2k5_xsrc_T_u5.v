(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(247904, 235%nat); (285100, 25%nat); (285484, 19%nat); (285200, 71%nat); (285560, 42%nat); (285728, 56%nat); (285952, 20%nat); (286056, 13%nat); (427116, 4%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [248696].
Definition HDECL : CH.hdecl := CH.HD (8384) (8224) [((EVar 8), (0), ELit 264); ((EVar 8), (288), ELit 120)] [((EVar 8), (264), ELit 24); ((EVar 2), (0), ELit 24)] [].
Definition CSUMS : list CA.callsum := [CAX.xs_cs (ESU.opnew_xsum HDECL 798592 8240 48%nat (ELit 2048)); CA.cs_copy 778312; CA.cs_free_ 718776].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 248304 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; (APC.eaddz (EVar 8) (264)); EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; (APC.eaddz (EVar 32) (1024)); EVar 32; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KWord (SA (EVar 8) (264)) 8 (EVar 32);
   KWord (SA (EVar 8) (272)) 8 (APC.eaddz (EVar 32) (1024));
   KWord (SA (EVar 8) (280)) 8 (APC.eaddz (EVar 32) (1024));
   KWr (SA (EVar 8) (264)) (ELit (24));
   KWord (SA (EVar 8) (296)) 8 (EVar 35);
   KRange (EVar 35) (0) (18446744073709551615);
   KWord (SA (EVar 8) (376)) 8 (ELit (1));
   KWord (SA (EVar 8) (28)) 1 (ELit (0));
   KWord (SA (EVar 8) (30)) 1 (ELit (0));
   KRange (EVar 8) (1099511627776) (140737488355328);
   KAlign (EVar 8) (8);
   KUnk (SA (EVar 2) (-8384)) (ELit (8384));
   KWr (SA (EVar 2) (-8384)) (ELit (8384));
   KUnk (SA (EVar 2) (0)) (ELit (24));
   KWr (SA (EVar 2) (0)) (ELit (24));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8384)) (ELit (8408)) (SA (EVar 8) (0)) (ELit (408));
   KUnk (SA (EVar 32) (0)) (ELit (1024));
   KWr (SA (EVar 32) (0)) (ELit (1024));
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (16);
   KDisj (SA (EVar 2) (-8384)) (ELit (8408)) (SA (EVar 32) (0)) (ELit (1024));
   KDisj (SA (EVar 8) (0)) (ELit (408)) (SA (EVar 32) (0)) (ELit (1024));
   KWord (SA (EVar 32) (996)) 1 (ELit (0));
   KBlob (SA (EVar 32) (0)) (ELit (1024)) 0]
  48 [((EVar 2), (-8384), ((ELit (8384)))); ((EVar 2), (0), ((ELit (24)))); ((EVar 8), (264), ((ELit (24)))); ((EVar 32), (0), ((ELit (1024))))] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [((EVar 32), (ELit (1024)))].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 400 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
