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
Definition ITR : list (Z * nat) := [(240208, 66%nat); (288220, 29%nat); (243740, 56%nat); (288924, 8%nat); (288956, 1%nat); (289032, 138%nat); (289804, 34%nat); (289964, 44%nat); (258584, 42%nat); (290468, 33%nat); (258292, 20%nat); (258008, 20%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [457768; 608000; 798592; 435744; 290348; 291032; 240468; 255532; 436872; 436288; 427124; 241896].
Definition HDECL : CH.hdecl := CH.HD (0) (8224) [] [] [].
Definition CSUMS : list CA.callsum := [].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 240208 [EVar 0; (EVar 33); (EVar 2); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KUnk (SA (EVar 2) (-416)) (ELit (416));
   KWr (SA (EVar 2) (-416)) (ELit (416));
   KRange (EVar 42) (1099511627776) (140737488355328);
   KImg (65536) (827984);
   KUnk (SA (EVar 42) (8)) (ELit (16));
   KWr (SA (EVar 42) (8)) (ELit (16));
   KUnk (SA (EVar 42) (88)) (ELit (8));
   KWr (SA (EVar 42) (88)) (ELit (8));
   KUnk (SA (EVar 42) (136)) (ELit (8));
   KWr (SA (EVar 42) (136)) (ELit (8));
   KDisj (SA (EVar 2) (-416)) (ELit (416)) (SA (EVar 42) (0)) (ELit (592))]
  64 [((EVar 2), (-416), ELit 416); ((EVar 42), (8), ELit 16); ((EVar 42), (88), ELit 8); ((EVar 42), (136), ELit 8)] [] (ELit (10)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 290032 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-416)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KRange (EVar 40) (1099511627776) (140737488355328);
   KImg (65536) (827984);
   KUnk (SA (EVar 40) (216)) (ELit (12));
   KWr (SA (EVar 40) (216)) (ELit (12));
   KUnk (SA (EVar 40) (80)) (ELit (8));
   KWr (SA (EVar 40) (80)) (ELit (8));
   KUnk (SA (EVar 40) (0)) (ELit (8));
   KWr (SA (EVar 40) (0)) (ELit (8));
   KUnk (SA (EVar 40) (16)) (ELit (8));
   KWr (SA (EVar 40) (16)) (ELit (8))]
  64 [((EVar 40), (216), ELit 12); ((EVar 40), (80), ELit 8); ((EVar 40), (0), ELit 8); ((EVar 40), (16), ELit 8)] [] (ELit (9)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 290092 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-416)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KWord (SA (EVar 2) (-392)) 8 (ELit (289844));
   KWord (SA (EVar 2) (-400)) 8 (EVar 40);
   KWord (SA (EVar 2) (-408)) 8 (APC.eaddz (EVar 40) (-8));
   KRange (EVar 40) (1099511627776) (140737488355328);
   KRange (EVar 50) (1099511627776) (140737488355328);
   KImg (65536) (827984);
   KWord (SA (EVar 50) (0)) 8 (ELit (818632));
   KWord (SA (EVar 50) (160)) 8 (EVar 64);
   KUnk (SA (EVar 40) (32)) (ELit (48));
   KWr (SA (EVar 40) (32)) (ELit (48));
   KUnk (SA (EVar 40) (16)) (ELit (8));
   KWr (SA (EVar 40) (16)) (ELit (8));
   KUnk (SA (EVar 40) (232)) (ELit (56));
   KWr (SA (EVar 40) (232)) (ELit (56));
   KDisj (SA (EVar 2) (-416)) (ELit (416)) (SA (EVar 40) (-8)) (ELit (592));
   KDisj (SA (EVar 50) (0)) (ELit (272)) (SA (EVar 40) (-8)) (ELit (592));
   KAlign (EVar 50) (8)]
  65 [((EVar 40), (32), ELit 48); ((EVar 40), (16), ELit 8); ((EVar 40), (232), ELit 56)] [] (ELit (8)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 289908 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-384)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KWord (SA (EVar 2) (-360)) 8 (ELit (288268));
   KWord (SA (EVar 2) (-368)) 8 (EVar 41);
   KWord (SA (EVar 2) (-376)) 8 (EVar 64);
   KWord (SA (EVar 2) (-384)) 8 (APC.eaddz (EVar 2) (-304));
   KWr (SA (EVar 2) (-480)) (ELit (128));
   KWord (SA (EVar 2) (-304)) 8 (ELit (804416));
   KWord (SA (EVar 2) (-296)) 4 (ELit (65792));
   KWord (SA (EVar 2) (-288)) 8 (ELit (804528));
   KWord (SA (EVar 2) (-256)) 8 (APC.eaddz (EVar 2) (-288));
   KWord (SA (EVar 2) (-232)) 2 (ELit (0));
   KZero (SA (EVar 2) (-224)) (ELit (144));
   KWord (SA (EVar 2) (-80)) 4 (ELit (1024));
   KRange (EVar 41) (1099511627776) (140737488355328);
   KImg (65536) (827984);
   KUnk (SA (EVar 41) (264)) (ELit (8));
   KWr (SA (EVar 41) (264)) (ELit (8));
   KUnk (SA (EVar 41) (280)) (ELit (8));
   KWr (SA (EVar 41) (280)) (ELit (8));
   KUnk (SA (EVar 41) (296)) (ELit (24));
   KWr (SA (EVar 41) (296)) (ELit (24));
   KUnk (SA (EVar 41) (320)) (ELit (272));
   KWr (SA (EVar 41) (320)) (ELit (272));
   KDisj (SA (EVar 2) (-480)) (ELit (480)) (SA (EVar 41) (0)) (ELit (592));
   KAlign (EVar 41) (8)]
  65 [((EVar 2), (-480), ELit 128); ((EVar 41), (264), ELit 8); ((EVar 41), (280), ELit 8); ((EVar 41), (296), ELit 24); ((EVar 41), (320), ELit 272)] [] (ELit (7)).
Definition BL3 : CA.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 289476 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-448)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KRange (EVar 51) (1099511627776) (140737488355328);
   KImg (65536) (827984);
   KWord (SA (EVar 51) (0)) 8 (ELit (804416));
   KWord (SA (EVar 51) (224)) 4 (ELit (1024));
   KAlign (EVar 51) (8)]
  64 [] [] (ELit (6)).
Definition BL4 : CA.blocks := [].
Definition hints4 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 289524 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-448)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KUnk (SA (EVar 2) (-433)) (ELit (1));
   KWr (SA (EVar 2) (-433)) (ELit (1))]
  64 [((EVar 2), (-433), ELit 1)] [] (ELit (5)).
Definition BL5 : CA.blocks := [].
Definition hints5 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CC.CP 289540 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-448)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KWord (SA (EVar 2) (-360)) 8 (ELit (288308));
   KWord (SA (EVar 2) (-368)) 8 (EVar 64);
   KWord (SA (EVar 2) (-376)) 8 (EVar 65);
   KWord (SA (EVar 2) (-384)) 8 (EVar 66);
   KWord (SA (EVar 2) (-392)) 8 (EVar 67);
   KWord (SA (EVar 2) (-400)) 8 (APC.eaddz (EVar 2) (-288));
   KWord (SA (EVar 2) (-408)) 8 (EVar 68);
   KWord (SA (EVar 2) (-416)) 8 (EVar 69);
   KWord (SA (EVar 2) (-424)) 8 (EVar 70);
   KWord (SA (EVar 2) (-312)) 8 (ELit (240368));
   KWord (SA (EVar 2) (-320)) 8 (EVar 71);
   KWord (SA (EVar 2) (-328)) 8 (EVar 72);
   KWord (SA (EVar 2) (-336)) 8 (EVar 73);
   KWord (SA (EVar 2) (-344)) 8 (EVar 74);
   KWord (SA (EVar 2) (-8)) 8 (EVar 75);
   KWord (SA (EVar 2) (-16)) 8 (EVar 76);
   KWord (SA (EVar 2) (-24)) 8 (EVar 77);
   KWord (SA (EVar 2) (-32)) 8 (EVar 78);
   KWord (SA (EVar 2) (-40)) 8 (EVar 79);
   KWord (SA (EVar 2) (-48)) 8 (EVar 80);
   KWord (SA (EVar 2) (-56)) 8 (EVar 81);
   KWord (SA (EVar 2) (-64)) 8 (EVar 82);
   KWr (SA (EVar 2) (-320)) (ELit (16));
   KWord (SA (EVar 2) (-288)) 8 (ELit (804528));
   KWord (SA (EVar 2) (-256)) 8 (APC.eaddz (EVar 2) (-288));
   KZero (SA (EVar 2) (-224)) (ELit (144));
   KImg (65536) (827984);
   KUnk (SA (EVar 2) (-304)) (ELit (8));
   KWr (SA (EVar 2) (-304)) (ELit (8));
   KUnk (SA (EVar 2) (-240)) (ELit (8));
   KWr (SA (EVar 2) (-240)) (ELit (8))]
  83 [((EVar 2), (-320), ELit 16); ((EVar 2), (-304), ELit 8); ((EVar 2), (-240), ELit 8)] [] (ELit (4)).
Definition BL6 : CA.blocks := [].
Definition hints6 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5; t6].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
