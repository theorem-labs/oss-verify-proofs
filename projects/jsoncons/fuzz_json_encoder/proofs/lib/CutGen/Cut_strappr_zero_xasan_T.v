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
Definition ITR : list (Z * nat) := [(911564, 318%nat); (912836, 82%nat); (1040960, 82%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 40.
Definition ENDS : list Z := [912524].
Definition HDECL : CH.hdecl := CH.HD (4880) (8224) [((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 3); ((EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-192)) (ELit 3)), (2147450880), ELit 3)] [((EVar 10), (0), ELit 24)] [(1444792, 1448528)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880); (1482496, 4, 1)].
Definition GLO : Z := 1444792.
Definition GHI : Z := 1448528.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 417764 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1); KRange (EVar (g + 5)) 7077888 140737479966592; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 128); KWr (SA (EVar (g + 5)) 0) (ELit 128); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 128); KDisj (SA (EVar 2) (-4880)) (ELit 4880) (SA (EVar (g + 5)) 0) (ELit 128); KWord (SA (EVar (g + 5)) 120) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7077888 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-4880)) (ELit 4880) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (0)) (ELit (24)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (0)) (ELit (24)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit (3)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 34) (0)) (APC.escale (2) (EVar 32)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 34) (0)) (APC.escale (2) (EVar 32)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-192)) (ELit 3)) (2147450880)) (ELit (3))], BLk)) (fun F => let g := 40%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 88); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 16); ((EVar g), 0, ELit 1)]))) (fun _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 911564 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (EVar 11); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KWord (SA (EVar 10) (0)) 8 (APC.eaddz (APC.escale (2) (EVar 32)) (1));
   KWord (SA (EVar 10) (8)) 8 (EVar 33);
   KWord (SA (EVar 10) (16)) 8 (EVar 34);
   KRange (EVar 32) (12) (70368744177664);
   KRange (EVar 33) (0) (67108864);
   KBlob (SA (EVar 34) (0)) (EVar 33) 0;
   KWord (SA (APC.eadd (EVar 33) (EVar 34)) (0)) 1 (ELit (0));
   KUnk (SA (EVar 34) (0)) (APC.escale (2) (EVar 32));
   KWr (SA (EVar 34) (0)) (APC.escale (2) (EVar 32));
   KRange (EVar 34) (4096) (140737488355328);
   KAlign (EVar 34) (16);
   KRange (APC.esub (APC.eaddz (APC.escale (2) (EVar 32)) (-1)) (EVar 33)) (0) (140737488355328);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 34) (0)) (APC.escale (2) (EVar 32));
   KUnk (SA (EVar 10) (0)) (ELit (24));
   KWr (SA (EVar 10) (0)) (ELit (24));
   KRange (EVar 10) (7077888) (140737488351232);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4880)) (ELit (4880));
   KWr (SA (EVar 2) (-4880)) (ELit (4880));
   KRange (EVar 2) (140735332487952) (140737488355328);
   KAlign (EVar 2) (32);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-192)) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (EVar 2) (-4880)) (ELit (4880)) (SA (EVar 10) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-4880)) (ELit (4880)) (SA (EVar 34) (0)) (APC.escale (2) (EVar 32));
   KDisj (SA (EVar 10) (0)) (ELit (24)) (SA (EVar 34) (0)) (APC.escale (2) (EVar 32));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-192)) (ELit 3)) (2147450880)) (ELit 3)]
  40 [((EVar 2), (-4880), ELit 4880); ((EVar 10), (0), ELit 24); ((EVar 34), (0), ((APC.escale (2) (EVar 32))))] [] (ELit (100)).
Definition BL0 : CA.blocks := [((EVar 34), (APC.escale (2) (EVar 32)))].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 1500 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
