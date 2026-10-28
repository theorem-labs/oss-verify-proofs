(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(757664, 1442%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 34.
Definition ENDS : list Z := [760520].
Definition CSUMS : list CAD.callsum := [(CAD.CSUM 765872 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false); CAD.cs_inline 760352 4 []; CAD.cs_inline 760360 4 []; CAD.cs_inline 760364 4 []; CAD.cs_inline 759768 4 []; CAD.cs_inline 762520 4 []; CAD.cs_inline 762532 4 []; CAD.cs_inline 762572 4 []; CAD.cs_inline 762812 4 []; CAD.cs_inline 762816 4 []; CAD.cs_inline 762768 4 []; CAD.cs_inline 762832 4 []; CAD.cs_inline 759996 4 []; CAD.cs_inline 760000 4 []; CAD.cs_inline 760004 4 []].
Definition ASSUME : list (Z * (list expr -> list kentry -> list (list kentry * kentry))) := [].
Definition CASES : list (Z * list (nat * Z)) := [].
Definition RESPELL : list (Z * (list expr -> list kentry -> list (nat * expr))) := [].
Definition ECASES : list (Z * list ((list expr -> expr) * Z)) := [].
Definition NAMEB : list (Z * nat) := [].
Definition XSTOPS : list Z := [].
Definition HDECL : CH.hdecl := CH.HD (0) (8224) [] [] [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 757664 [EVar 0; EVar 1; EVar 2; EVar 3; (ELit (905232)); EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (ELit (1)); (ELit (1)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332491744) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-8672)) (ELit (8672));
   KUnk (SA (EVar 2) (-8672)) (ELit (8672));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-8672)) (ELit (8672));
   KRange (EVar 32) (4096) (140737488355328);
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KWord (SA (ELit (0)) (1036928)) 8 (EVar 33);
   KDisj (SA (EVar 32) (0)) (ELit (4)) (SA (EVar 2) (-8672)) (ELit (8672));
   KDisj (SA (EVar 32) (0)) (ELit (4)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 32) (0)) 1 (ELit (105));
   KWord (SA (EVar 32) (1)) 1 (ELit (110));
   KWord (SA (EVar 32) (2)) 1 (ELit (102));
   KWord (SA (EVar 32) (3)) 1 (ELit (0))]
  34 [((EVar 2), (-8672), ELit 8672); ((EVar 10), (8), ELit 8)] [] (ELit (1152921504606846976)).
Definition BL0 : CAD.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 757664 [EVar 0; EVar 1; EVar 2; EVar 3; (ELit (905232)); EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (ELit (1)); (ELit (1)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332491744) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-8672)) (ELit (8672));
   KUnk (SA (EVar 2) (-8672)) (ELit (8672));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-8672)) (ELit (8672));
   KRange (EVar 32) (4096) (140737488355328);
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KWord (SA (ELit (0)) (1036928)) 8 (EVar 33);
   KDisj (SA (EVar 32) (0)) (ELit (5)) (SA (EVar 2) (-8672)) (ELit (8672));
   KDisj (SA (EVar 32) (0)) (ELit (5)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 32) (0)) 1 (ELit (45));
   KWord (SA (EVar 32) (1)) 1 (ELit (105));
   KWord (SA (EVar 32) (2)) 1 (ELit (110));
   KWord (SA (EVar 32) (3)) 1 (ELit (102));
   KWord (SA (EVar 32) (4)) 1 (ELit (0))]
  34 [((EVar 2), (-8672), ELit 8672); ((EVar 10), (8), ELit 8)] [] (ELit (1152921504606846976)).
Definition BL1 : CAD.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 757664 [EVar 0; EVar 1; EVar 2; EVar 3; (ELit (905232)); EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (ELit (1)); (ELit (1)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332491744) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-8672)) (ELit (8672));
   KUnk (SA (EVar 2) (-8672)) (ELit (8672));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-8672)) (ELit (8672));
   KRange (EVar 32) (4096) (140737488355328);
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KWord (SA (ELit (0)) (1036928)) 8 (EVar 33);
   KDisj (SA (EVar 32) (0)) (ELit (4)) (SA (EVar 2) (-8672)) (ELit (8672));
   KDisj (SA (EVar 32) (0)) (ELit (4)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 32) (0)) 1 (ELit (110));
   KWord (SA (EVar 32) (1)) 1 (ELit (97));
   KWord (SA (EVar 32) (2)) 1 (ELit (110));
   KWord (SA (EVar 32) (3)) 1 (ELit (0))]
  34 [((EVar 2), (-8672), ELit 8672); ((EVar 10), (8), ELit 8)] [] (ELit (1152921504606846976)).
Definition BL2 : CAD.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 757664 [EVar 0; EVar 1; EVar 2; EVar 3; (ELit (905232)); EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (ELit (1)); (ELit (1)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332491744) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-8672)) (ELit (8672));
   KUnk (SA (EVar 2) (-8672)) (ELit (8672));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-8672)) (ELit (8672));
   KRange (EVar 32) (4096) (140737488355328);
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KWord (SA (ELit (0)) (1036928)) 8 (EVar 33);
   KDisj (SA (EVar 32) (0)) (ELit (5)) (SA (EVar 2) (-8672)) (ELit (8672));
   KDisj (SA (EVar 32) (0)) (ELit (5)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 32) (0)) 1 (ELit (45));
   KWord (SA (EVar 32) (1)) 1 (ELit (110));
   KWord (SA (EVar 32) (2)) 1 (ELit (97));
   KWord (SA (EVar 32) (3)) 1 (ELit (110));
   KWord (SA (EVar 32) (4)) 1 (ELit (0))]
  34 [((EVar 2), (-8672), ELit 8672); ((EVar 10), (8), ELit 8)] [] (ELit (1152921504606846976)).
Definition BL3 : CAD.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CAD.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] XSTOPS ASSUME CASES NAMEB RESPELL ECASES (CC.cp_F c) (CC.cp_meas c) h 600 first false 2%nat
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CAD.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CAD.po_leaves o)) (CC.cp_meas c).
