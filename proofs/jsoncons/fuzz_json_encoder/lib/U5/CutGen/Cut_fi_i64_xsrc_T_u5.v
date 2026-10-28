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
Definition ITR : list (Z * nat) := [(257096, 88%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [257444].
Definition HDECL : CH.hdecl := CH.HD (8816) (8224) [((EVar 11), (0), ELit 8)] [((EVar 32), (0), ELit 24)] [].
Definition CSUMS : list CA.callsum := [CAX.xs_cs (ESU.sink_xsum 436872 8496)].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 257304 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-320)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 11); (EVar 54); (EVar 10); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 33); EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 11) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KRange (EVar 33) (1) (19);
   KWr (SA (EVar 2) (-8816)) (ELit (8816));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8816)) (ELit (8816)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8816)) (ELit (8816)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KUnk (SA (EVar 2) (-320)) (ELit (25));
   KUnk (SA (EVar 2) (-295)) (ELit (255));
   KUnk (SA (EVar 2) (-8816)) (ELit (8496))]
  66 [((EVar 2), (-8816), ELit 8816)] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 257380 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-320)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 11); (EVar 33); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (APC.eadd (APC.eaddz (EVar 2) (-295)) (EVar 48)); (APC.eaddz (EVar 2) (-295)); EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 11) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KRange (EVar 33) (1) (19);
   KWr (SA (EVar 2) (-8816)) (ELit (8816));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8816)) (ELit (8816)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8816)) (ELit (8816)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KUnk (SA (EVar 2) (-320)) (ELit (25));
   KUnk (SA (EVar 2) (-295)) (ELit (255));
   KUnk (SA (EVar 2) (-8816)) (ELit (8496));
   KRange (EVar 48) (0) (19);
   KRange (APC.esub (EVar 33) (EVar 48)) (1) (20)]
  66 [((EVar 2), (-8816), ELit 8816)] [] (APC.escale (4) (APC.eaddz (EVar 48) (1))).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 257380 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-320)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 11); (APC.eaddz (EVar 33) (1)); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (APC.eadd (APC.eaddz (EVar 2) (-295)) (EVar 48)); (APC.eaddz (EVar 2) (-295)); EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 11) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KRange (EVar 33) (1) (19);
   KWr (SA (EVar 2) (-8816)) (ELit (8816));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8816)) (ELit (8816)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8816)) (ELit (8816)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KUnk (SA (EVar 2) (-320)) (ELit (25));
   KUnk (SA (EVar 2) (-295)) (ELit (255));
   KUnk (SA (EVar 2) (-8816)) (ELit (8496));
   KRange (EVar 48) (0) (19);
   KRange (APC.esub (EVar 33) (EVar 48)) (1) (20)]
  66 [((EVar 2), (-8816), ELit 8816)] [] (APC.escale (4) (APC.eaddz (EVar 48) (1))).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [257396] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
