(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(824664, 234%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 40.
Definition ENDS : list Z := [825288].
Definition HDECL : CH.hdecl := CH.HD (9120) (8224) [((EAlu Instr.ALU_SRL (EVar 12) (ELit 3)), (2147450880), ELit 1)] [((EVar 12), (0), ELit 8)] [(1444792, 1448528)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880); (1482496, 4, 1)].
Definition GLO : Z := 1444792.
Definition GHI : Z := 1448528.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 417764 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1); KRange (EVar (g + 5)) 7077888 140737479966592; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 128); KWr (SA (EVar (g + 5)) 0) (ELit 128); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 128); KDisj (SA (EVar 2) (-9120)) (ELit 9120) (SA (EVar (g + 5)) 0) (ELit 128); KWord (SA (EVar (g + 5)) 120) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7077888 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-9120)) (ELit 9120) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 12) (0)) (ELit (8)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 12) (0)) (ELit (8)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) (2147450880)) (ELit (1))], BLk)) (fun F => let g := 40%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 88); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 16)]))) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1383752 8944 0%nat (fun _ _ => None) (fun regs => [((nth 26 regs (ELit 0)), 32, ELit 8); ((ELit 0), 6938412, ELit 4)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [KWord (SA (nth 26 regs (ELit 0)) 32) 8 (EAlu Instr.ALU_ADD (nth 22 regs (ELit 0)) (nth 20 regs (ELit 0)))] ++ match CAX.cell_at cells (nth 26 regs (ELit 0)) 120 8 with Some fl => [KWord (SA (nth 26 regs (ELit 0)) 120) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun regs => [((nth 26 regs (ELit 0)), 1, -160)])); CA.CSUM 825032 (fun _ => []) (fun _ => None) (fun _ _ => [KWr (SA (EVar 40) 0) (ELit 1)]) (fun _ => None) false (Some (4, [10%nat])) 0 false false].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 824664 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KRange (EVar 11) (0) (67108864);
   KRange (EVar 10) (4096) (140737479966719);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966719);
   KUnk (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 12) (0)) (ELit (8));
   KRange (EVar 12) (7077888) (140737488355320);
   KAlign (EVar 12) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 12) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-9120)) (ELit (9120));
   KWr (SA (EVar 2) (-9120)) (ELit (9120));
   KRange (EVar 2) (140735332492192) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9120)) (ELit (9120)) (SA (EVar 12) (0)) (ELit (8))]
  40 [((EVar 2), (-9120), ELit 9120); ((EVar 12), (0), ELit 8)] [] (ELit (10)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
