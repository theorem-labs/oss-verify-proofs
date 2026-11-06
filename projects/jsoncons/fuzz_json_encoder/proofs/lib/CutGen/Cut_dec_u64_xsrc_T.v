(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(291980, 50%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [292080; 292164; 292176].
Definition HDECL : CH.hdecl := CH.HD (0) (8224) [] [] [].
Definition CSUMS : list CA.callsum := [].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 291980 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KBlob (SA (EVar 10) (0)) (EVar 11) 0;
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737488355328);
   KUnk (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 12) (0)) (ELit (8));
   KRange (EVar 12) (1099511627776) (140737488355328);
   KImg (65536) (813152);
   KDisj (SA (EVar 12) (0)) (ELit (8)) (SA (ELit (0)) (65536)) (ELit (962560))]
  32 [((EVar 12), (0), ((ELit (8))))] [] (ELit (1099511627776)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 292024 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; (ELit (10)); (EVar 35); EVar 7; EVar 8; EVar 9; EVar 10; (APC.esub (APC.eadd (EVar 10) (EVar 11)) (EVar 32)); EVar 12; (APC.eadd (EVar 32) (EVar 33)); (APC.eadd (EVar 10) (EVar 11)); (EVar 34); (APC.esub (APC.esub (APC.eadd (EVar 10) (EVar 11)) (EVar 32)) (EVar 33)); (ELit (9)); EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 33) (1) (19);
   KRange (EVar 32) (0) (134217728);
   KBlob (SA (EVar 10) (0)) (EVar 11) 0;
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737488355328);
   KUnk (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 12) (0)) (ELit (8));
   KRange (EVar 12) (1099511627776) (140737488355328);
   KImg (65536) (813152);
   KDisj (SA (EVar 12) (0)) (ELit (8)) (SA (ELit (0)) (65536)) (ELit (962560));
   KRange (APC.esub (APC.esub (EVar 11) (EVar 32)) (EVar 33)) (0) (19);
   KRange (APC.esub (EVar 11) (EVar 32)) (1) (19)]
  36 [((EVar 12), (0), ((ELit (8))))] [] (EVar 33).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [292024; 292084; 292100] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 400 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
