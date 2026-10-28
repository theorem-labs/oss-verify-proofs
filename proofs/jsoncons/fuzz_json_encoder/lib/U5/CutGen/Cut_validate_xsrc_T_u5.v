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
Definition ITR : list (Z * nat) := [(308272, 152%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [308872].
Definition HDECL : CH.hdecl := CH.HD (0) (8224) [] [] [].
Definition CSUMS : list CA.callsum := [].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 308272 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KBlob (SA (EVar 10) (0)) (EVar 11) 0;
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737488355328);
   KWr (SA (EVar 2) (-96)) (ELit (96));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KDisj (SA (EVar 2) (-96)) (ELit (96)) (SA (EVar 10) (0)) (EVar 11);
   KUnk (SA (EVar 2) (-96)) (ELit (96));
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737488355328)]
  32 [((EVar 2), (-96), ((ELit (96))))] [] (ELit (1099511627776)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 308432 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-96)); EVar 3; EVar 4; (ELit (2)); (ELit (18446744073709551551)); (ELit (239)); (ELit (240)); (ELit (144)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 32))); (EVar 33); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (245)); (ELit (244)); (ELit (143)); (ELit (84398)); (ELit (18446744073709467217)); (ELit (3)); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (ELit (224)); (ELit (160)); (ELit (237)); (ELit (159))]
  [KWord (SA (EVar 2) (-8)) 8 (EVar 8);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-80)) 8 (EVar 25);
   KWord (SA (EVar 2) (-88)) 8 (EVar 26);
   KWord (SA (EVar 2) (-96)) 8 (EVar 27);
   KBlob (SA (EVar 10) (0)) (EVar 11) 0;
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737488355328);
   KWr (SA (EVar 2) (-96)) (ELit (96));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KDisj (SA (EVar 2) (-96)) (ELit (96)) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (1) (134217728);
   KRange (APC.esub (EVar 11) (EVar 32)) (0) (134217728);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737488355328)]
  40 [((EVar 2), (-96), ((ELit (96))))] [] (EVar 32).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [308444; 308460; 308476; 308492; 308508; 308524; 308540; 308556; 308584; 308596; 308664; 308680; 308696] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 400 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
