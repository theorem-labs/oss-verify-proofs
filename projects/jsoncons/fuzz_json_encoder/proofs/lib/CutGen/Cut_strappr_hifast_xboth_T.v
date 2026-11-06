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
Definition ITR : list (Z * nat) := [(926224, 332%nat); (927552, 91%nat); (1055672, 82%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 40.
Definition ENDS : list Z := [927236].
Definition HDECL : CH.hdecl := CH.HD (4880) (8224) [((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 3); ((EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-192)) (ELit 3)), (2147450880), ELit 3); ((APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)), (0), ((EVar 35)))] [((EVar 10), (0), ELit 24)] [(1459384, 1463120)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880); (1497024, 4, 1)].
Definition GLO : Z := 1459384.
Definition GHI : Z := 1463120.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 420020 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1); KRange (EVar (g + 5)) 7094272 140737479966592; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 128); KWr (SA (EVar (g + 5)) 0) (ELit 128); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 128); KDisj (SA (EVar 2) (-4880)) (ELit 4880) (SA (EVar (g + 5)) 0) (ELit 128); KWord (SA (EVar (g + 5)) 120) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7094272 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-4880)) (ELit 4880) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (0)) (ELit (24)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (0)) (ELit (24)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit (3)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 34) (0)) (APC.escale (2) (EVar 32)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 34) (0)) (APC.escale (2) (EVar 32)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-192)) (ELit 3)) (2147450880)) (ELit (3)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)) (0)) (EVar 35); KDisj (SA (EVar g) 0) (ELit 1) (SA (APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)) (0)) (EVar 35)], BLk)) (fun F => let g := 40%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 88); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 16)]))) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 528876 2560 0%nat (fun regs g => Some (nth 10 regs (ELit 0))) (fun regs => [((nth 10 regs (ELit 0)), 0, (nth 12 regs (ELit 0)))]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1)] ++ [KBlob (SA (nth 10 regs (ELit 0)) 0) (nth 12 regs (ELit 0)) 1; KWord (SA (EAlu Instr.ALU_SRL (APC.eadd (nth 10 regs (ELit 0)) (nth 12 regs (ELit 0))) (ELit 3)) (2147450880)) 1 (ELit 0)] ++ match CAX.cell_at cells (nth 26 regs (ELit 0)) 120 8 with Some fl => [KWord (SA (nth 26 regs (ELit 0)) 120) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F ++ [((EVar 40), 0, ELit 1)])) (fun regs => [((nth 26 regs (ELit 0)), 1, -160)]))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 926224 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)); (APC.eadd (APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)) (EVar 35)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1497024) 4 (ELit 1);
   KWord (SA (EVar 10) (0)) 8 (APC.eaddz (APC.escale (2) (EVar 32)) (1));
   KWord (SA (EVar 10) (8)) 8 (EVar 33);
   KWord (SA (EVar 10) (16)) 8 (EVar 34);
   KRange (EVar 32) (12) (70368744177664);
   KRange (EVar 33) (0) (67108864);
   KBlob (SA (EVar 34) (0)) (EVar 33) 0;
   KUnk (SA (EVar 34) (0)) (APC.escale (2) (EVar 32));
   KWr (SA (EVar 34) (0)) (APC.escale (2) (EVar 32));
   KRange (EVar 34) (4096) (140737488355328);
   KAlign (EVar 34) (16);
   KRange (APC.esub (APC.eaddz (APC.escale (2) (EVar 32)) (-1)) (EVar 33)) (0) (140737488355328);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 34) (0)) (APC.escale (2) (EVar 32));
   KUnk (SA (EVar 10) (0)) (ELit (24));
   KWr (SA (EVar 10) (0)) (ELit (24));
   KRange (EVar 10) (7094272) (140737488351232);
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
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-192)) (ELit 3)) (2147450880)) (ELit 3);
   KRange (EVar 35) (1) (67108864);
   KRange (APC.eadd (EVar 33) (EVar 35)) (1) (67108863);
   KBlob (SA (APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)) (0)) (EVar 35) 1;
   KUnk (SA (APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)) (0)) (EVar 35);
   KRange (APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)) (4096) (140737488355328);
   KRange (APC.eadd (APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)) (EVar 35)) (4096) (140737488355328);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)) (0)) (EVar 35);
   KDisj (SA (EVar 2) (-4880)) (ELit (4880)) (SA (APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)) (0)) (EVar 35);
   KDisj (SA (EVar 10) (0)) (ELit (24)) (SA (APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)) (0)) (EVar 35);
   KDisj (SA (EVar 34) (0)) (APC.escale (2) (EVar 32)) (SA (APC.eadd (APC.eadd (EVar 34) (APC.escale (2) (EVar 32))) (EVar 37)) (0)) (EVar 35);
   KRange (EVar 37) (0) (140737488355328);
   KRange (APC.esub (APC.esub (APC.eaddz (APC.escale (2) (EVar 32)) (-1)) (EVar 33)) (EVar 35)) (0) (140737488355328)]
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
