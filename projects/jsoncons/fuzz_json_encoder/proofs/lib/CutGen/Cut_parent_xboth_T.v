(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(914208, 221%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [914732].
Definition HDECL : CH.hdecl := CH.HD (640) (8224) [((EVar 10), (248), ELit 16); ((EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (248)) (ELit 3)), (2147450880), ELit 2); ((APC.eadd (EVar 32) (EVar 33)), (-1), ELit 1); ((EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (-1)) (ELit 3)), (2147450880), ELit 1)] [] [(1459384, 1463120)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880); (1497024, 4, 1)].
Definition GLO : Z := 1459384.
Definition GHI : Z := 1463120.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 420020 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1); KRange (EVar (g + 5)) 7094272 140737479966592; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 128); KWr (SA (EVar (g + 5)) 0) (ELit 128); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 128); KDisj (SA (EVar 2) (-640)) (ELit 640) (SA (EVar (g + 5)) 0) (ELit 128); KWord (SA (EVar (g + 5)) 120) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7094272 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-640)) (ELit 640) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (248)) (ELit (16)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (248)) (ELit (16)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (APC.eadd (EVar 32) (EVar 33)) (-1)) (ELit (1)); KDisj (SA (EVar g) 0) (ELit 1) (SA (APC.eadd (EVar 32) (EVar 33)) (-1)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (248)) (ELit 3)) (2147450880)) (ELit (2)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (-1)) (ELit 3)) (2147450880)) (ELit (1))], BLk)) (fun F => let g := 48%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 88); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 16); ((EVar g), 0, ELit 1)]))) (fun _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 914208 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1497024) 4 (ELit 1);
   KWord (SA (EVar 10) (248)) 8 (EVar 32);
   KWord (SA (EVar 10) (256)) 8 (APC.eadd (EVar 32) (EVar 33));
   KRange (EVar 10) (1048576) (140737488354816);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (248)) (ELit 3)) 2147450880) (ELit (2));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (248)) (ELit (16));
   KWord (SA (APC.eadd (EVar 32) (EVar 33)) (-1)) 1 (EVar 35);
   KRange (EVar 35) (0) (255);
   KWord (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (-1)) (ELit 3)) 2147450880) 1 (EVar 34);
   KRange (EVar 32) (17594333495296) (140737479966720);
   KAlign (EVar 32) (16);
   KRange (EVar 33) (1) (4096);
   KUnk (SA (EVar 2) (-640)) (ELit (640));
   KWr (SA (EVar 2) (-640)) (ELit (640));
   KRange (EVar 2) (140735332483712) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-640)) (ELit (640)) (SA (EVar 10) (248)) (ELit (16));
   KDisj (SA (EVar 2) (-640)) (ELit 640) (SA (APC.eadd (EVar 32) (EVar 33)) (-1)) (ELit 1);
   KDisj (SA (EVar 10) 248) (ELit 16) (SA (APC.eadd (EVar 32) (EVar 33)) (-1)) (ELit 1);
   KRange (EVar 34) (0) (0)]
  48 [((EVar 2), (-640), ELit 640)] [] (ELit (16)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 914208 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1497024) 4 (ELit 1);
   KWord (SA (EVar 10) (248)) 8 (EVar 32);
   KWord (SA (EVar 10) (256)) 8 (APC.eadd (EVar 32) (EVar 33));
   KRange (EVar 10) (1048576) (140737488354816);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (248)) (ELit 3)) 2147450880) (ELit (2));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (248)) (ELit (16));
   KWord (SA (APC.eadd (EVar 32) (EVar 33)) (-1)) 1 (EVar 35);
   KRange (EVar 35) (0) (255);
   KWord (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (-1)) (ELit 3)) 2147450880) 1 (EVar 34);
   KRange (EVar 32) (17594333495296) (140737479966720);
   KAlign (EVar 32) (16);
   KRange (EVar 33) (1) (4096);
   KUnk (SA (EVar 2) (-640)) (ELit (640));
   KWr (SA (EVar 2) (-640)) (ELit (640));
   KRange (EVar 2) (140735332483712) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-640)) (ELit (640)) (SA (EVar 10) (248)) (ELit (16));
   KDisj (SA (EVar 2) (-640)) (ELit 640) (SA (APC.eadd (EVar 32) (EVar 33)) (-1)) (ELit 1);
   KDisj (SA (EVar 10) 248) (ELit 16) (SA (APC.eadd (EVar 32) (EVar 33)) (-1)) (ELit 1);
   KRange (EVar 34) (1) (7);
   KRange (APC.esub (EVar 34) (EAlu Instr.ALU_AND (APC.eaddz (EVar 33) (7)) (ELit 7))) (1) (7)]
  48 [((EVar 2), (-640), ELit 640)] [] (ELit (16)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 200 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
