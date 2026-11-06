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
Definition ITR : list (Z * nat) := [(238296, 22%nat); (278368, 194%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [278112; 279144; 280396; 279344; 274112; 295216; 278368; 278840; 278504; 278644; 278988; 279080; 278800; 279120; 238348; 278836; 279140].
Definition HDECL : CH.hdecl := CH.HD (0) (8224) [] [] [].
Definition CSUMS : list CA.callsum := [].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 278368 [EVar 0; (EVar 33); (EVar 2); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KUnk (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 42) (4096) (140737488355328);
   KWord (SA (EVar 42) (240)) 8 (EVar 64);
   KWord (SA (EVar 64) (0)) 8 (ELit (803800));
   KWord (SA (EVar 64) (152)) 1 (EVar 65);
   KImg (65536) (813152);
   KRange (EVar 64) (4096) (140737488355328);
   KRange (EVar 65) (0) (255);
   KWord (SA (EVar 42) (568)) 8 (EVar 66);
   KUnk (SA (EVar 42) (576)) (ELit (8));
   KWr (SA (EVar 42) (576)) (ELit (8));
   KDisj (SA (EVar 2) (-80)) (ELit (80)) (SA (EVar 42) (0)) (ELit (592));
   KDisj (SA (EVar 2) (-80)) (ELit (80)) (SA (EVar 64) (0)) (ELit (272));
   KDisj (SA (EVar 42) (576)) (ELit (8)) (SA (EVar 64) (0)) (ELit (272))]
  67 [((EVar 2), (-80), ELit 80); ((EVar 42), (576), ELit 8)] [] (ELit (98)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 278468 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-80)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KRange (EVar 41) (4096) (140737488355328);
   KUnk (SA (EVar 41) (464)) (ELit (4));
   KWr (SA (EVar 41) (464)) (ELit (4));
   KUnk (SA (EVar 41) (480)) (ELit (24));
   KWr (SA (EVar 41) (480)) (ELit (24));
   KUnk (SA (EVar 41) (528)) (ELit (1));
   KWr (SA (EVar 41) (528)) (ELit (1));
   KUnk (SA (EVar 41) (531)) (ELit (2));
   KWr (SA (EVar 41) (531)) (ELit (2))]
  64 [((EVar 41), (464), ELit 4); ((EVar 41), (480), ELit 24); ((EVar 41), (528), ELit 1); ((EVar 41), (531), ELit 2)] [] (ELit (97)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 278528 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-80)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KRange (EVar 41) (4096) (140737488355328);
   KRange (EVar 40) (4096) (140737488355328);
   KWord (SA (EVar 40) (0)) 4 (EVar 64);
   KWord (SA (EVar 41) (312)) 8 (EVar 65);
   KWord (SA (EVar 41) (512)) 8 (EVar 66);
   KWord (SA (EVar 41) (520)) 8 (EVar 67);
   KWr (SA (EVar 41) (512)) (ELit (16));
   KDisj (SA (EVar 41) (0)) (ELit (592)) (SA (EVar 40) (0)) (ELit (16))]
  68 [((EVar 41), (512), ELit 16)] [] (ELit (96)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 278584 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-80)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (ELit (1)); (ELit (2)); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KRange (EVar 41) (4096) (140737488355328);
   KRange (EVar 40) (4096) (140737488355328);
   KWord (SA (EVar 40) (0)) 4 (EVar 64);
   KWord (SA (EVar 41) (528)) 1 (EVar 65);
   KWord (SA (EVar 41) (532)) 1 (EVar 66);
   KWord (SA (EVar 41) (531)) 1 (EVar 67)]
  68 [] [] (ELit (95)).
Definition BL3 : CA.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 278688 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-80)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KRange (EVar 41) (4096) (140737488355328);
   KWord (SA (EVar 41) (512)) 8 (EVar 64);
   KWord (SA (EVar 41) (520)) 8 (EVar 65)]
  66 [] [] (ELit (94)).
Definition BL4 : CA.blocks := [].
Definition hints4 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 278712 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-80)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KRange (EVar 41) (4096) (140737488355328);
   KRange (EVar 40) (4096) (140737488355328);
   KWord (SA (EVar 40) (0)) 4 (EVar 64);
   KWord (SA (EVar 41) (512)) 8 (EVar 65);
   KWord (SA (EVar 41) (520)) 8 (EVar 66);
   KWr (SA (EVar 41) (512)) (ELit (16));
   KDisj (SA (EVar 41) (0)) (ELit (592)) (SA (EVar 40) (0)) (ELit (16))]
  67 [((EVar 41), (512), ELit 16)] [] (ELit (93)).
Definition BL5 : CA.blocks := [].
Definition hints5 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CC.CP 278840 [EVar 0; (EVar 33); (EVar 2); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KUnk (SA (EVar 2) (-32)) (ELit (32));
   KWr (SA (EVar 2) (-32)) (ELit (32));
   KRange (EVar 42) (4096) (140737488355328);
   KWord (SA (EVar 42) (240)) 8 (EVar 64);
   KWord (SA (EVar 64) (0)) 8 (ELit (803800));
   KWord (SA (EVar 64) (152)) 4 (EVar 65);
   KImg (65536) (813152);
   KRange (EVar 64) (4096) (140737488355328);
   KRange (EVar 65) (0) (255);
   KWord (SA (EVar 42) (288)) 8 (ELit (0));
   KWord (SA (EVar 42) (512)) 8 (EVar 66);
   KWord (SA (EVar 42) (520)) 8 (EVar 67);
   KDisj (SA (EVar 2) (-32)) (ELit (32)) (SA (EVar 42) (0)) (ELit (592));
   KDisj (SA (EVar 2) (-32)) (ELit (32)) (SA (EVar 64) (0)) (ELit (272))]
  68 [((EVar 2), (-32), ELit 32)] [] (ELit (92)).
Definition BL6 : CA.blocks := [].
Definition hints6 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CC.CP 279004 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-32)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KRange (EVar 40) (4096) (140737488355328);
   KRange (EVar 41) (4096) (140737488355328);
   KWord (SA (EVar 41) (0)) 4 (EVar 64);
   KWord (SA (EVar 40) (512)) 8 (EVar 65);
   KWord (SA (EVar 40) (520)) 8 (EVar 66);
   KWr (SA (EVar 40) (512)) (ELit (16));
   KDisj (SA (EVar 40) (0)) (ELit (592)) (SA (EVar 41) (0)) (ELit (16))]
  67 [((EVar 40), (512), ELit 16)] [] (ELit (91)).
Definition BL7 : CA.blocks := [].
Definition hints7 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CC.CP 279064 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-32)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KRange (EVar 40) (4096) (140737488355328);
   KRange (EVar 41) (4096) (140737488355328);
   KWord (SA (EVar 41) (0)) 4 (EVar 64);
   KWord (SA (EVar 40) (512)) 8 (EVar 65);
   KWord (SA (EVar 40) (520)) 8 (EVar 66)]
  67 [] [] (ELit (90)).
Definition BL8 : CA.blocks := [].
Definition hints8 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5; t6; t7; t8].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 400 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
