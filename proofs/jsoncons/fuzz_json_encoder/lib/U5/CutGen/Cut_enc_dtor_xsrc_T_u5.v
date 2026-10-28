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
Definition ITR : list (Z * nat) := [(240580, 18%nat); (288164, 14%nat); (243740, 56%nat); (255692, 19%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [255712; 427124; 240648; 243960].
Definition HDECL : CH.hdecl := CH.HD (0) (8224) [] [] [].
Definition CSUMS : list CA.callsum := [].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 240580 [EVar 0; (EVar 33); (EVar 2); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KUnk (SA (EVar 2) (-32)) (ELit (32));
   KWr (SA (EVar 2) (-32)) (ELit (32));
   KRange (EVar 42) (1099511627776) (140737488355328);
   KAlign (EVar 42) (8);
   KWord (SA (EVar 42) (264)) 8 (EVar 64);
   KDisj (SA (EVar 2) (-32)) (ELit (32)) (SA (EVar 42) (0)) (ELit (408))]
  65 [((EVar 2), (-32), ELit 32)] [] (ELit (10)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 255712 [EVar 0; (ELit (240612)); (APC.eaddz (EVar 2) (-32)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (APC.eaddz (EVar 40) (264)); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KRange (EVar 40) (1099511627776) (140737488355328);
   KRange (EVar 42) (4096) (140737488355328);
   KWord (SA (EVar 40) (280)) 8 (EVar 64);
   KWord (SA (EVar 40) (272)) 8 (APC.eadd (EVar 42) (APC.escale (32) (EVar 65)));
   KWr (SA (EVar 40) (272)) (ELit (8));
   KRange (EVar 65) (0) (1024);
   KRange (APC.escale (32) (EVar 65)) (0) (32768);
   KDisj (SA (EVar 2) (-32)) (ELit (32)) (SA (EVar 40) (0)) (ELit (408))]
  66 [((EVar 40), (272), ELit 8)] [] (ELit (2000)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [(4%nat, [(65%nat, (EVar 65))])].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 255712 [EVar 0; (ELit (240612)); (APC.eaddz (EVar 2) (-32)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (ELit (0)); (EVar 43); (APC.eaddz (EVar 40) (264)); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KRange (EVar 40) (1099511627776) (140737488355328);
   KImg (65536) (827984);
   KWord (SA (EVar 40) (48)) 8 (ELit (2562));
   KWord (SA (EVar 40) (96)) 8 (ELit (0));
   KWord (SA (EVar 40) (120)) 8 (ELit (0));
   KWord (SA (EVar 40) (144)) 8 (ELit (0));
   KWord (SA (EVar 40) (168)) 8 (ELit (0));
   KWord (SA (EVar 40) (192)) 8 (ELit (0));
   KWord (SA (EVar 40) (216)) 8 (ELit (0));
   KWord (SA (EVar 2) (-8)) 8 (EVar 64);
   KWord (SA (EVar 2) (-16)) 8 (EVar 65);
   KUnk (SA (EVar 2) (-48)) (ELit (32));
   KUnk (SA (EVar 40) (16)) (ELit (8));
   KWr (SA (EVar 40) (16)) (ELit (8));
   KUnk (SA (EVar 40) (80)) (ELit (8));
   KWr (SA (EVar 40) (80)) (ELit (8));
   KDisj (SA (EVar 2) (-48)) (ELit (48)) (SA (EVar 40) (0)) (ELit (408))]
  66 [((EVar 2), (-48), ELit 48); ((EVar 40), (16), ELit 8); ((EVar 40), (80), ELit 8)] [] (ELit (9)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 240612 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-32)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KRange (EVar 40) (1099511627776) (140737488355328);
   KImg (65536) (827984);
   KWord (SA (EVar 40) (48)) 8 (ELit (2562));
   KWord (SA (EVar 40) (96)) 8 (ELit (0));
   KWord (SA (EVar 40) (120)) 8 (ELit (0));
   KWord (SA (EVar 40) (144)) 8 (ELit (0));
   KWord (SA (EVar 40) (168)) 8 (ELit (0));
   KWord (SA (EVar 40) (192)) 8 (ELit (0));
   KWord (SA (EVar 40) (216)) 8 (ELit (0));
   KWord (SA (EVar 2) (-8)) 8 (EVar 64);
   KWord (SA (EVar 2) (-16)) 8 (EVar 65);
   KUnk (SA (EVar 2) (-48)) (ELit (32));
   KUnk (SA (EVar 40) (16)) (ELit (8));
   KWr (SA (EVar 40) (16)) (ELit (8));
   KUnk (SA (EVar 40) (80)) (ELit (8));
   KWr (SA (EVar 40) (80)) (ELit (8));
   KDisj (SA (EVar 2) (-48)) (ELit (48)) (SA (EVar 40) (0)) (ELit (408))]
  66 [((EVar 2), (-48), ELit 48); ((EVar 40), (16), ELit 8); ((EVar 40), (80), ELit 8)] [] (ELit (8)).
Definition BL3 : CA.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
Definition t4 : CC.cutpoint := CC.CP 255728 [EVar 0; (ELit (240612)); (APC.eaddz (EVar 2) (-32)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (APC.eadd (EVar 42) (APC.escale (32) (EVar 65))); (APC.eaddz (EVar 40) (264)); (ELit (32)); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KRange (EVar 40) (1099511627776) (140737488355328);
   KRange (EVar 42) (4096) (140737488355328);
   KWord (SA (EVar 40) (280)) 8 (EVar 64);
   KUnk (SA (EVar 40) (272)) (ELit (8));
   KWr (SA (EVar 40) (272)) (ELit (8));
   KRange (EVar 65) (1) (1024);
   KRange (APC.eaddz (EVar 65) (100)) (0) (4611686018427387904);
   KDisj (SA (EVar 2) (-32)) (ELit (32)) (SA (EVar 40) (0)) (ELit (408))]
  66 [((EVar 40), (272), ELit 8)] [] (APC.eaddz (EVar 65) (100)).
Definition BL4 : CA.blocks := [].
Definition hints4 : list (nat * CC.subst) := [(4%nat, [(65%nat, (APC.eaddz (EVar 65) (-1)))])].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 300 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
