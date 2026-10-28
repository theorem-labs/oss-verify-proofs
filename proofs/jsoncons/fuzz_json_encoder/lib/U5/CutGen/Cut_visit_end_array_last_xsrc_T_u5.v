(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(244408, 100%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [244668].
Definition HDECL : CH.hdecl := CH.HD (10624) (8224) [((EVar 10), (0), ELit 272); ((EVar 10), (280), ELit 8); ((EVar 10), (304), ELit 96)] [((EVar 10), (272), ELit 8); ((EVar 10), (288), ELit 4); ((EVar 10), (296), ELit 8); ((EVar 10), (400), ELit 4); ((EVar 32), (0), ELit 24)] [(65536, 827984)].
Definition CSUMS : list CA.callsum := [CAX.xs_cs (ESU.sink_xsum 436288 8496); CAX.xs_cs (ESU2.hcol_xsum 256028 8576 (EVar 32))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 244408 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (36)) 1 (ELit (4));
   KWord (SA (EVar 10) (288)) 4 (APC.escale (4) (EVar 33));
   KWord (SA (EVar 10) (400)) 4 (EVar 33);
   KWr (SA (EVar 10) (288)) (ELit (4));
   KWr (SA (EVar 10) (400)) (ELit (4));
   KWr (SA (EVar 10) (272)) (ELit (8));
   KWord (SA (EVar 10) (296)) 8 (EVar 37);
   KRange (EVar 37) (0) (18446744073709551615);
   KWr (SA (EVar 10) (296)) (ELit (8));
   KWord (SA (EVar 10) (384)) 8 (ELit (83694));
   KWord (SA (EVar 10) (392)) 8 (ELit (1));
   KRange (EVar 10) (1099511627776) (140737488355328);
   KAlign (EVar 10) (8);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KUnk (SA (EVar 2) (-10624)) (ELit (10576));
   KUnk (SA (EVar 2) (-48)) (ELit (48));
   KWr (SA (EVar 2) (-10624)) (ELit (10624));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-10624)) (ELit (10624)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EVar 2) (-10624)) (ELit (10624)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 32) (0)) (ELit (24));
   KImg (65536) (827984);
   KWord (SA (EVar 10) (264)) 8 (EVar 34);
   KWord (SA (EVar 10) (272)) 8 (APC.eadd (EVar 34) (APC.escale (32) (EVar 33)));
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) 4 (EVar 38);
   KRange (EVar 38) (0) (1);
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-28)) 1 (ELit (0));
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-27)) 1 (EVar 39);
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) 1 (EVar 40);
   KRange (EVar 40) (0) (1);
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-8)) 8 (EVar 36);
   KUnk (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) (ELit (32));
   KRange (APC.esub (EVar 35) (APC.escale (32) (EVar 33))) (0) (32768);
   KRange (EVar 35) (32) (32768);
   KRange (EVar 34) (4096) (140737488355328);
   KAlign (EVar 34) (16);
   KRange (EVar 36) (0) (18446744073709551615);
   KDisj (SA (EVar 2) (-10624)) (ELit (10624)) (SA (EVar 34) (0)) (EVar 35);
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 34) (0)) (EVar 35);
   KDisj (SA (EVar 32) (0)) (ELit (24)) (SA (EVar 34) (0)) (EVar 35);
   KRange (EVar 33) (1) (1)]
  48 [((EVar 2), (-10624), ((ELit (10624)))); ((EVar 10), (272), ((ELit (8)))); ((EVar 10), (288), ((ELit (4)))); ((EVar 10), (296), ((ELit (8)))); ((EVar 10), (400), ((ELit (4))))] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [((EVar 34), (EVar 35))].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
