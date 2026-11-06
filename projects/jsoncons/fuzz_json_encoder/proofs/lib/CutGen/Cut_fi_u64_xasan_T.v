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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(766156, 408%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [767228; 766620; 766896].
Definition HDECL : CH.hdecl := CH.HD (4864) (8224) [((EVar 11), (0), ELit 8); ((EAlu Instr.ALU_SRL (EVar 11) (ELit 3)), (2147450880), ELit 1); ((EVar 2), (0), ELit 16)] [((EVar 32), (0), ELit 24); ((EVar 2), (0), ELit 16)] [(1444792, 1448528); (65536, 1449984)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880); (1482496, 4, 1)].
Definition GLO : Z := 1444792.
Definition GHI : Z := 1448528.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 418576 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1); KRange (EVar (g + 5)) 7077888 140737479966208; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 512); KWr (SA (EVar (g + 5)) 0) (ELit 512); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 64); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 64); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 512); KDisj (SA (EVar 2) (-4864)) (ELit 4864) (SA (EVar (g + 5)) 0) (ELit 512); KWord (SA (EVar (g + 5)) 504) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7077888 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-4864)) (ELit 4864) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 512) (SA (EVar 11) (0)) (ELit (8)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 11) (0)) (ELit (8)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 64) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EVar (g + 5)) 0) (ELit 512) (SA (EVar 32) (0)) (ELit (24)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 32) (0)) (ELit (24)); KDisj (SA (EVar (g + 5)) 0) (ELit 512) (SA (EVar 2) (0)) (ELit (16)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 2) (0)) (ELit (16))], BLk)) (fun F => let g := 48%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 472); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 64)]))) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1041292 4368 0%nat (fun _ _ => None) (fun regs => [((EVar 32), 0, ELit 24)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (nth 19 regs (ELit 0)) 504 8 with Some fl => [KWord (SA (nth 19 regs (ELit 0)) 504) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun regs => [((nth 19 regs (ELit 0)), 3, -128)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 540344 256 0%nat (fun _ _ => None) (fun regs => [((EAlu Instr.ALU_SRL (nth 19 regs (ELit 0)) (ELit 3)), 2147450880, ELit 64)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (nth 19 regs (ELit 0)) 504 8 with Some fl => [KWord (SA (nth 19 regs (ELit 0)) 504) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F ++ [((EVar 48), 0, ELit 1)])) (fun regs => [((nth 19 regs (ELit 0)), 3, -128)]))].
Definition XSTOPS : list Z := [766620; 766888; 766904; 766896].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 766156 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (16)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (EVar 11); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KImg (65536) (1449984);
   KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 11) (7077888) (140737488355320);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (8));
   KRange (EVar 32) (7077888) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4864)) (ELit (4864));
   KUnk (SA (EVar 2) (0)) (ELit (16));
   KWr (SA (EVar 2) (-4864)) (ELit (4864));
   KWr (SA (EVar 2) (0)) (ELit (16));
   KRange (EVar 2) (140735332487936) (140737488355312);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4864)) (ELit (4880));
   KDisj (SA (EVar 2) (-4864)) (ELit (4880)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4864)) (ELit (4880)) (SA (EVar 32) (0)) (ELit (24))]
  48 [((EVar 2), (-4864), ELit 4864); ((EVar 2), (0), ELit 16)] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 766888 [EVar 0; (EVar 67); (APC.eaddz (EVar 2) (-128)); EVar 3; EVar 4; (EVar 68); (EVar 69); (EVar 70); (APC.eaddz (EVar 2) (16)); (APC.eaddz (EVar 2) (-128)); (EVar 71); (EVar 72); (EVar 73); (EVar 74); (EVar 75); (EVar 76); (EVar 77); (EVar 78); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (ELit 2147450880)); (EVar 53); (EVar 66); (EVar 11); (APC.eadd (APC.eaddz (EVar 53) (32)) (EVar 65)); (APC.eadd (APC.eaddz (EVar 53) (32)) (EVar 65)); (EVar 53); (ELit (2147450880)); (APC.eaddz (EVar 53) (32)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (ELit 2147450880)); (EVar 79); (EVar 80); (EVar 81); (EVar 82)]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KImg (65536) (1449984);
   KRange (EVar 53) (7077888) (140737479966208);
   KAlign (EVar 53) (64);
   KUnk (SA (EVar 53) (24)) (ELit (488));
   KWr (SA (EVar 53) (0)) (ELit (512));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450884) (ELit 31);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 53) (32)) (ELit 3)) 2147450880) (ELit (3));
   KWr (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 64);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 53) (0)) (ELit (512));
   KDisj (SA (EVar 2) (-4864)) (ELit (4880)) (SA (EVar 53) (0)) (ELit (512));
   KWord (SA (EVar 53) (504)) 8 (EVar 48);
   KWr (SA (EVar 48) (0)) (ELit (1));
   KRange (EVar 48) (7077888) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) (0)) (ELit (1));
   KDisj (SA (EVar 53) (0)) (ELit (512)) (SA (EVar 48) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-4864)) (ELit (4880)) (SA (EVar 48) (0)) (ELit (1));
   KDisj (SA (EVar 53) (0)) (ELit (512)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 48) (0)) (ELit (1)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 64) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 1);
   KDisj (SA (EVar 53) (0)) (ELit (512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 48) (0)) (ELit (1)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 2) (-112)) 8 (EVar 53);
   KWord (SA (EVar 2) (-88)) 8 (EVar 27);
   KWord (SA (EVar 2) (-80)) 8 (EVar 26);
   KWord (SA (EVar 2) (-72)) 8 (EVar 25);
   KWord (SA (EVar 2) (-64)) 8 (EVar 24);
   KWord (SA (EVar 2) (-56)) 8 (EVar 23);
   KWord (SA (EVar 2) (-48)) 8 (EVar 22);
   KWord (SA (EVar 2) (-40)) 8 (EVar 21);
   KWord (SA (EVar 2) (-32)) 8 (EVar 20);
   KWord (SA (EVar 2) (-24)) 8 (EVar 19);
   KWord (SA (EVar 2) (-16)) 8 (EVar 18);
   KWord (SA (EVar 2) (-8)) 8 (EVar 9);
   KWord (SA (EVar 2) (0)) 8 (EVar 8);
   KWord (SA (EVar 2) (8)) 8 (EVar 1);
   KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 11) (7077888) (140737488355320);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (8));
   KRange (EVar 32) (7077888) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4864)) (ELit (4752));
   KUnk (SA (EVar 2) (-104)) (ELit (16));
   KWr (SA (EVar 2) (-4864)) (ELit (4864));
   KWr (SA (EVar 2) (0)) (ELit (16));
   KRange (EVar 2) (140735332487936) (140737488355312);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4864)) (ELit (4880));
   KDisj (SA (EVar 2) (-4864)) (ELit (4880)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4864)) (ELit (4880)) (SA (EVar 32) (0)) (ELit (24));
   KRange (EVar 65) (0) (19);
   KRange (EVar 66) (1) (20);
   KRange (APC.esub (EVar 66) (EVar 65)) (1) (20)]
  83 [((EVar 2), (-4864), ELit 4864); ((EVar 2), (0), ELit 16); ((EVar 53), (0), ELit 24); ((EVar 53), (32), ELit 472); ((EAlu Instr.ALU_SRL (EVar 53) (ELit 3)), (2147450880), ELit 64)] [] (APC.eaddz (APC.escale (64) (EVar 65)) (8)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 766904 [EVar 0; (EVar 67); (APC.eaddz (EVar 2) (-128)); EVar 3; EVar 4; (EVar 68); (EVar 69); (EVar 70); (APC.eaddz (EVar 2) (16)); (APC.eaddz (EVar 2) (-128)); (ELit (0)); (EVar 72); (EVar 73); (EVar 74); (EVar 75); (EVar 76); (EVar 77); (EVar 78); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (ELit 2147450880)); (EVar 53); (EVar 66); (EVar 11); (APC.eadd (APC.eaddz (EVar 53) (32)) (EVar 65)); (APC.eadd (APC.eaddz (EVar 53) (32)) (EVar 65)); (EVar 53); (ELit (2147450880)); (APC.eaddz (EVar 53) (32)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (ELit 2147450880)); (EVar 79); (EVar 80); (EVar 81); (EVar 82)]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KImg (65536) (1449984);
   KRange (EVar 53) (7077888) (140737479966208);
   KAlign (EVar 53) (64);
   KUnk (SA (EVar 53) (24)) (ELit (488));
   KWr (SA (EVar 53) (0)) (ELit (512));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450884) (ELit 31);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 53) (32)) (ELit 3)) 2147450880) (ELit (3));
   KWr (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 64);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 53) (0)) (ELit (512));
   KDisj (SA (EVar 2) (-4864)) (ELit (4880)) (SA (EVar 53) (0)) (ELit (512));
   KWord (SA (EVar 53) (504)) 8 (EVar 48);
   KWr (SA (EVar 48) (0)) (ELit (1));
   KRange (EVar 48) (7077888) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) (0)) (ELit (1));
   KDisj (SA (EVar 53) (0)) (ELit (512)) (SA (EVar 48) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-4864)) (ELit (4880)) (SA (EVar 48) (0)) (ELit (1));
   KDisj (SA (EVar 53) (0)) (ELit (512)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 48) (0)) (ELit (1)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 64) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 1);
   KDisj (SA (EVar 53) (0)) (ELit (512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 48) (0)) (ELit (1)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 2) (-112)) 8 (EVar 53);
   KWord (SA (EVar 2) (-88)) 8 (EVar 27);
   KWord (SA (EVar 2) (-80)) 8 (EVar 26);
   KWord (SA (EVar 2) (-72)) 8 (EVar 25);
   KWord (SA (EVar 2) (-64)) 8 (EVar 24);
   KWord (SA (EVar 2) (-56)) 8 (EVar 23);
   KWord (SA (EVar 2) (-48)) 8 (EVar 22);
   KWord (SA (EVar 2) (-40)) 8 (EVar 21);
   KWord (SA (EVar 2) (-32)) 8 (EVar 20);
   KWord (SA (EVar 2) (-24)) 8 (EVar 19);
   KWord (SA (EVar 2) (-16)) 8 (EVar 18);
   KWord (SA (EVar 2) (-8)) 8 (EVar 9);
   KWord (SA (EVar 2) (0)) 8 (EVar 8);
   KWord (SA (EVar 2) (8)) 8 (EVar 1);
   KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 11) (7077888) (140737488355320);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (8));
   KRange (EVar 32) (7077888) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4864)) (ELit (4752));
   KUnk (SA (EVar 2) (-104)) (ELit (16));
   KWr (SA (EVar 2) (-4864)) (ELit (4864));
   KWr (SA (EVar 2) (0)) (ELit (16));
   KRange (EVar 2) (140735332487936) (140737488355312);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4864)) (ELit (4880));
   KDisj (SA (EVar 2) (-4864)) (ELit (4880)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4864)) (ELit (4880)) (SA (EVar 32) (0)) (ELit (24));
   KRange (EVar 65) (0) (19);
   KRange (EVar 66) (1) (20);
   KRange (APC.esub (EVar 66) (EVar 65)) (1) (20)]
  83 [((EVar 2), (-4864), ELit 4864); ((EVar 2), (0), ELit 16); ((EVar 53), (0), ELit 24); ((EVar 53), (32), ELit 472); ((EAlu Instr.ALU_SRL (EVar 53) (ELit 3)), (2147450880), ELit 64)] [] (APC.eaddz (APC.escale (64) (EVar 65)) (6)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [766912] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 3000 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
