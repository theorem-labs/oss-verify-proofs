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
Definition ITR : list (Z * nat) := [(256028, 64%nat); (256412, 20%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [256280].
Definition HDECL : CH.hdecl := CH.HD (8576) (8224) [((EVar 10), (0), ELit 296); ((EVar 10), (304), ELit 104)] [((EVar 10), (296), ELit 8); ((EVar 32), (0), ELit 24)] [].
Definition CSUMS : list CA.callsum := [CAX.xs_cs (ESU.sink_xsum 436288 8496); CAX.xs_cs (ESU.sink_xsum 436872 8496)].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 256028 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (48)) 8 (ELit (2562));
   KWord (SA (EVar 10) (56)) 8 (ELit (0));
   KWord (SA (EVar 10) (64)) 8 (ELit (0));
   KWord (SA (EVar 10) (248)) 1 (ELit (32));
   KWord (SA (EVar 10) (288)) 4 (APC.escale (4) (EVar 33));
   KRange (EVar 33) (0) (1024);
   KUnk (SA (EVar 10) (296)) (ELit (8));
   KWr (SA (EVar 10) (296)) (ELit (8));
   KRange (EVar 10) (1099511627776) (140737488355328);
   KAlign (EVar 10) (8);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KUnk (SA (EVar 2) (-8576)) (ELit (8496));
   KWr (SA (EVar 2) (-8576)) (ELit (8576));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8576)) (ELit (8576)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EVar 2) (-8576)) (ELit (8576)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-80)) (ELit (80))]
  48 [((EVar 2), (-8576), ELit 8576); ((EVar 10), (296), ELit 8)] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 256220 [EVar 0; (EVar 49); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 50); (EVar 51); (EVar 52); (EVar 10); (APC.esub (APC.escale (4) (EVar 33)) (EVar 48)); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (APC.eaddz (EVar 10) (16)); EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 61); (EVar 62); (EVar 63); (EVar 64)]
  [KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (48)) 8 (ELit (2562));
   KWord (SA (EVar 10) (56)) 8 (ELit (0));
   KWord (SA (EVar 10) (64)) 8 (ELit (0));
   KWord (SA (EVar 10) (248)) 1 (ELit (32));
   KWord (SA (EVar 10) (288)) 4 (APC.escale (4) (EVar 33));
   KRange (EVar 33) (0) (1024);
   KUnk (SA (EVar 10) (296)) (ELit (8));
   KWr (SA (EVar 10) (296)) (ELit (8));
   KRange (EVar 10) (1099511627776) (140737488355328);
   KAlign (EVar 10) (8);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KUnk (SA (EVar 2) (-8576)) (ELit (8496));
   KWr (SA (EVar 2) (-8576)) (ELit (8576));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8576)) (ELit (8576)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EVar 2) (-8576)) (ELit (8576)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KUnk (SA (EVar 2) (-80)) (ELit (48));
   KRange (EVar 48) (1) (4096);
   KRange (APC.esub (APC.escale (4) (EVar 33)) (EVar 48)) (0) (4096)]
  65 [((EVar 2), (-8576), ELit 8576); ((EVar 10), (296), ELit 8)] [] (APC.eaddz (APC.escale (4) (EVar 48)) (2)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 400 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
