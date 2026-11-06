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
Definition ITR : list (Z * nat) := [(913528, 219%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [914336; 913932].
Definition HDECL : CH.hdecl := CH.HD (9792) (8224) [((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 34); ((EAlu Instr.ALU_SRL (EVar 11) (ELit 3)), (2147450880), ELit 2); ((EVar 32), (0), ((EVar 33))); ((EAlu Instr.ALU_SRL (EVar 36) (ELit 3)), (2147450880), ((EVar 38)))] [((EVar 10), (0), ELit 272); ((EVar 11), (0), ELit 16)] [(1444792, 1448528); (1419712, 1421408)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880); (1482496, 4, 1)].
Definition GLO : Z := 1444792.
Definition GHI : Z := 1448528.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 417392 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1); KRange (EVar (g + 5)) 7077888 140737479966656; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 64); KWr (SA (EVar (g + 5)) 0) (ELit 64); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 64); KDisj (SA (EVar 2) (-9792)) (ELit 9792) (SA (EVar (g + 5)) 0) (ELit 64); KWord (SA (EVar (g + 5)) 56) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7077888 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 64) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-9792)) (ELit 9792) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 64) (SA (EVar 10) (0)) (ELit (272)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (0)) (ELit (272)); KDisj (SA (EVar (g + 5)) 0) (ELit 64) (SA (EVar 11) (0)) (ELit (16)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 11) (0)) (ELit (16)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit (34)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit (2)); KDisj (SA (EVar (g + 5)) 0) (ELit 64) (SA (EVar 32) (0)) (EVar 33); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 32) (0)) (EVar 33); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) (2147450880)) (EVar 38); KZero (SA (ELit 0) 2147628550) (ELit 1)], BLk)) (fun F => let g := 48%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 24); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 8)]))) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 836392 16 0%nat (fun regs g => Some (ELit 0)) (fun regs => []) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (nth 5 regs (ELit 0)) 56 8 with Some fl => [KWord (SA (nth 5 regs (ELit 0)) 56) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun regs => [((nth 5 regs (ELit 0)), 0, -192)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 827600 1024 0%nat (fun _ _ => None) (fun regs => [((nth 10 regs (ELit 0)), 0, ELit 16); ((ELit 0), 6931840, ELit 2); ((ELit 0), 7069728, ELit 544)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (APC.eaddz (nth 25 regs (ELit 0)) (-32)) 56 8 with Some fl => [KWord (SA (APC.eaddz (nth 25 regs (ELit 0)) (-32)) 56) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun regs => [((APC.eaddz (nth 25 regs (ELit 0)) (-32)), 0, -192)]))].
Definition XSTOPS : list Z := [913924; 913932; 913940; 914000; 914180].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 913528 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KZero (SA (ELit 0) 2147628550) (ELit 1);
   KImg (1419712) (1421408);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 10) (96)) 8 (ELit (1421312));
   KWord (SA (EVar 10) (128)) 8 (APC.eaddz (EVar 10) (96));
   KRange (EVar 10) (7077888) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 11) (7077888) (140737479966704);
   KAlign (EVar 11) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (16));
   KWr (SA (EVar 2) (-9792)) (ELit (9792));
   KRange (EVar 2) (140735332492864) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 11) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 7069728) (ELit 544);
   KWord (SA (EVar 10) (211)) 1 (EVar 37);
   KRange (EVar 37) (0) (1);
   KWord (SA (EVar 11) (0)) 4 (ELit (0));
   KWr (SA (EVar 11) (0)) (ELit (16));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (2));
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (EVar 32);
   KRange (EVar 33) (1) (16384);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 32) (4096) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (EVar 38);
   KRange (EVar 38) (2048) (2048);
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16383);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (1) (16384);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 11) (0)) (ELit (16)) (SA (EVar 32) (0)) (EVar 33);
   KUnk (SA (EVar 2) (-9792)) (ELit (9792))]
  48 [((EVar 2), (-9792), ELit 9792); ((EVar 10), (200), ELit 8); ((EVar 10), (211), ELit 1)] [] (ELit (1073741824)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 913528 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KZero (SA (ELit 0) 2147628550) (ELit 1);
   KImg (1419712) (1421408);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 10) (96)) 8 (ELit (1421312));
   KWord (SA (EVar 10) (128)) 8 (APC.eaddz (EVar 10) (96));
   KRange (EVar 10) (7077888) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 11) (7077888) (140737479966704);
   KAlign (EVar 11) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (16));
   KWr (SA (EVar 2) (-9792)) (ELit (9792));
   KRange (EVar 2) (140735332492864) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 11) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 7069728) (ELit 544);
   KWord (SA (EVar 10) (211)) 1 (EVar 37);
   KRange (EVar 37) (0) (1);
   KWord (SA (EVar 11) (0)) 4 (ELit (0));
   KWr (SA (EVar 11) (0)) (ELit (16));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (2));
   KWord (SA (EVar 10) (192)) 8 (EVar 39);
   KWord (SA (EVar 10) (200)) 8 (EVar 39);
   KRange (EVar 39) (0) (140737488355328);
   KRange (EVar 32) (4096) (140737479966719);
   KRange (EVar 33) (1) (1);
   KRange (EVar 36) (4096) (140737488355328);
   KRange (EVar 38) (1) (1);
   KUnk (SA (EVar 2) (-9792)) (ELit (9792))]
  48 [((EVar 2), (-9792), ELit 9792); ((EVar 10), (200), ELit 8); ((EVar 10), (211), ELit 1)] [] (ELit (1073741824)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [(5%nat, [(86%nat, (ELit (1)))])].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 913924 [EVar 0; (EVar 49); (APC.eaddz (EVar 2) (-192)); EVar 3; EVar 4; (EVar 53); (EVar 51); (EVar 52); (EVar 2); (APC.eaddz (EVar 2) (-192)); (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 54)); (EVar 55); (EVar 10); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) (ELit (2147450880))); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (128)) (ELit 3)) (ELit (2147450880))); (ELit (3)); (ELit (1102416563)); (ELit (913528)); (ELit (2147450880)); (APC.eadd (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (ELit (2147450880))); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (200)) (ELit 3)) (ELit (2147450880))); (APC.eaddz (EVar 10) (200)); (APC.eaddz (EVar 10) (192)); (ELit (32)); (ELit (4294977024)); (APC.eaddz (EVar 53) (32)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (192)) (ELit 3)) (ELit (2147450880))); EVar 27; (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KZero (SA (ELit 0) 2147628550) (ELit 1);
   KImg (1419712) (1421408);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 10) (96)) 8 (ELit (1421312));
   KWord (SA (EVar 10) (128)) 8 (APC.eaddz (EVar 10) (96));
   KRange (EVar 10) (7077888) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 11) (7077888) (140737479966704);
   KAlign (EVar 11) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (16));
   KWr (SA (EVar 2) (-9792)) (ELit (9792));
   KRange (EVar 2) (140735332492864) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 11) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 7069728) (ELit 544);
   KWord (SA (EVar 10) (211)) 1 (EVar 37);
   KRange (EVar 37) (0) (1);
   KWord (SA (EVar 11) (0)) 4 (ELit (0));
   KWr (SA (EVar 11) (0)) (ELit (16));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (2));
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 54));
   KRange (EVar 33) (1) (16384);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 32) (4096) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (EVar 38);
   KRange (EVar 38) (2048) (2048);
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16383);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (1) (16384);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 11) (0)) (ELit (16)) (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 53) (0)) 8 (ELit (1102416563));
   KWord (SA (EVar 53) (8)) 8 (ELit (110998));
   KWord (SA (EVar 53) (16)) 8 (ELit (913528));
   KUnk (SA (EVar 53) (24)) (ELit (32));
   KWr (SA (EVar 53) (0)) (ELit (64));
   KWr (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 8);
   KWord (SA (EVar 53) (56)) 8 (EVar 48);
   KWr (SA (EVar 48) (0)) (ELit (1));
   KUnk (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 8);
   KRange (EVar 53) 7077888 140737479966656;
   KAlign (EVar 53) 64;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 53) 0) (ELit 64);
   KDisj (SA (EVar 2) (-9792)) (ELit 9792) (SA (EVar 53) 0) (ELit 64);
   KRange (EVar 48) 7077888 140737479966719;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 2) (-9792)) (ELit 9792) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 48) 0) (ELit 1) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 48) 0) (ELit 1) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit (34));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit (2));
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 48) 0) (ELit 1) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) (2147450880)) (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-96)) 8 (EVar 26);
   KWord (SA (EVar 2) (-104)) 8 (EVar 27);
   KWord (SA (EVar 2) (-192)) 8 (ELit (3));
   KWord (SA (EVar 2) (-184)) 8 (EVar 11);
   KWord (SA (EVar 2) (-176)) 8 (EVar 53);
   KWord (SA (EVar 2) (-168)) 8 (EVar 53);
   KWord (SA (EVar 2) (-160)) 8 (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) (ELit (2147450880)));
   KWord (SA (EVar 2) (-152)) 8 (APC.eaddz (EVar 10) (211));
   KWord (SA (EVar 2) (-144)) 8 (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (128)) (ELit 3)) (ELit (2147450880)));
   KWord (SA (EVar 2) (-136)) 8 (APC.eaddz (EVar 10) (128));
   KWord (SA (EVar 2) (-112)) 8 (EVar 53);
   KUnk (SA (EVar 2) (-9792)) (ELit (9600));
   KUnk (SA (EVar 2) (-128)) (ELit (16));
   KRange (EVar 54) (1) (16384);
   KRange (APC.esub (EVar 33) (EVar 54)) (0) (16383)]
  60 [((EVar 2), (-9792), ELit 9792); ((EVar 10), (200), ELit 8); ((EVar 10), (211), ELit 1); ((EVar 53), (0), ELit 24); ((EVar 53), (32), ELit 24); ((EAlu Instr.ALU_SRL (EVar 53) (ELit 3)), (2147450880), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 54)) (8)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 913940 [EVar 0; (EVar 49); (APC.eaddz (EVar 2) (-192)); EVar 3; EVar 4; (EVar 53); (EVar 51); (EVar 52); (EVar 2); (APC.eaddz (EVar 2) (-192)); (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 54)); (ELit (0)); (EVar 10); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) (ELit (2147450880))); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (128)) (ELit 3)) (ELit (2147450880))); (ELit (3)); (ELit (1102416563)); (ELit (913528)); (ELit (2147450880)); (APC.eadd (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (ELit (2147450880))); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (200)) (ELit 3)) (ELit (2147450880))); (APC.eaddz (EVar 10) (200)); (APC.eaddz (EVar 10) (192)); (ELit (32)); (ELit (4294977024)); (APC.eaddz (EVar 53) (32)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (192)) (ELit 3)) (ELit (2147450880))); EVar 27; (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KZero (SA (ELit 0) 2147628550) (ELit 1);
   KImg (1419712) (1421408);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 10) (96)) 8 (ELit (1421312));
   KWord (SA (EVar 10) (128)) 8 (APC.eaddz (EVar 10) (96));
   KRange (EVar 10) (7077888) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 11) (7077888) (140737479966704);
   KAlign (EVar 11) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (16));
   KWr (SA (EVar 2) (-9792)) (ELit (9792));
   KRange (EVar 2) (140735332492864) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 11) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 7069728) (ELit 544);
   KWord (SA (EVar 10) (211)) 1 (EVar 37);
   KRange (EVar 37) (0) (1);
   KWord (SA (EVar 11) (0)) 4 (ELit (0));
   KWr (SA (EVar 11) (0)) (ELit (16));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (2));
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 54));
   KRange (EVar 33) (1) (16384);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 32) (4096) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (EVar 38);
   KRange (EVar 38) (2048) (2048);
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16383);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (1) (16384);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 11) (0)) (ELit (16)) (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 53) (0)) 8 (ELit (1102416563));
   KWord (SA (EVar 53) (8)) 8 (ELit (110998));
   KWord (SA (EVar 53) (16)) 8 (ELit (913528));
   KUnk (SA (EVar 53) (24)) (ELit (32));
   KWr (SA (EVar 53) (0)) (ELit (64));
   KWr (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 8);
   KWord (SA (EVar 53) (56)) 8 (EVar 48);
   KWr (SA (EVar 48) (0)) (ELit (1));
   KUnk (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 8);
   KRange (EVar 53) 7077888 140737479966656;
   KAlign (EVar 53) 64;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 53) 0) (ELit 64);
   KDisj (SA (EVar 2) (-9792)) (ELit 9792) (SA (EVar 53) 0) (ELit 64);
   KRange (EVar 48) 7077888 140737479966719;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 2) (-9792)) (ELit 9792) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 48) 0) (ELit 1) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 48) 0) (ELit 1) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit (34));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit (2));
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 48) 0) (ELit 1) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) (2147450880)) (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-96)) 8 (EVar 26);
   KWord (SA (EVar 2) (-104)) 8 (EVar 27);
   KWord (SA (EVar 2) (-192)) 8 (ELit (3));
   KWord (SA (EVar 2) (-184)) 8 (EVar 11);
   KWord (SA (EVar 2) (-176)) 8 (EVar 53);
   KWord (SA (EVar 2) (-168)) 8 (EVar 53);
   KWord (SA (EVar 2) (-160)) 8 (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) (ELit (2147450880)));
   KWord (SA (EVar 2) (-152)) 8 (APC.eaddz (EVar 10) (211));
   KWord (SA (EVar 2) (-144)) 8 (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (128)) (ELit 3)) (ELit (2147450880)));
   KWord (SA (EVar 2) (-136)) 8 (APC.eaddz (EVar 10) (128));
   KWord (SA (EVar 2) (-112)) 8 (EVar 53);
   KUnk (SA (EVar 2) (-9792)) (ELit (9600));
   KUnk (SA (EVar 2) (-128)) (ELit (16));
   KRange (EVar 54) (1) (16384);
   KRange (APC.esub (EVar 33) (EVar 54)) (0) (16383);
   KRange (APC.eaddz (APC.escale (64) (EVar 54)) (6)) (0) (4611686018427387904)]
  60 [((EVar 2), (-9792), ELit 9792); ((EVar 10), (200), ELit 8); ((EVar 10), (211), ELit 1); ((EVar 53), (0), ELit 24); ((EVar 53), (32), ELit 24); ((EAlu Instr.ALU_SRL (EVar 53) (ELit 3)), (2147450880), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 54)) (6)).
Definition BL3 : CA.blocks := [].
Definition hints3 : list (nat * CC.subst) := [(5%nat, [(86%nat, (EVar 54))])].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 914000 [EVar 0; (EVar 49); (APC.eaddz (EVar 2) (-192)); EVar 3; EVar 4; (EVar 53); (EVar 51); (EVar 52); (EVar 2); (APC.eaddz (EVar 2) (-192)); (EVar 55); (ELit (0)); (EVar 10); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) (ELit (2147450880))); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (128)) (ELit 3)) (ELit (2147450880))); (ELit (3)); (ELit (1102416563)); (ELit (913528)); (ELit (2147450880)); (APC.eadd (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (ELit (2147450880))); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (200)) (ELit 3)) (ELit (2147450880))); (APC.eaddz (EVar 10) (200)); (APC.eaddz (EVar 10) (192)); (ELit (32)); (ELit (4294977024)); (APC.eaddz (EVar 53) (32)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (192)) (ELit 3)) (ELit (2147450880))); EVar 27; (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KZero (SA (ELit 0) 2147628550) (ELit 1);
   KImg (1419712) (1421408);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 10) (96)) 8 (ELit (1421312));
   KWord (SA (EVar 10) (128)) 8 (APC.eaddz (EVar 10) (96));
   KRange (EVar 10) (7077888) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 11) (7077888) (140737479966704);
   KAlign (EVar 11) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (16));
   KWr (SA (EVar 2) (-9792)) (ELit (9792));
   KRange (EVar 2) (140735332492864) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 11) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 7069728) (ELit 544);
   KWord (SA (EVar 10) (211)) 1 (EVar 37);
   KRange (EVar 37) (0) (1);
   KWord (SA (EVar 11) (0)) 4 (ELit (0));
   KWr (SA (EVar 11) (0)) (ELit (16));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (2));
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 54));
   KRange (EVar 33) (1) (16384);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 32) (4096) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (EVar 38);
   KRange (EVar 38) (2048) (2048);
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16383);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (1) (16384);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 11) (0)) (ELit (16)) (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 53) (0)) 8 (ELit (1102416563));
   KWord (SA (EVar 53) (8)) 8 (ELit (110998));
   KWord (SA (EVar 53) (16)) 8 (ELit (913528));
   KUnk (SA (EVar 53) (24)) (ELit (32));
   KWr (SA (EVar 53) (0)) (ELit (64));
   KWr (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 8);
   KWord (SA (EVar 53) (56)) 8 (EVar 48);
   KWr (SA (EVar 48) (0)) (ELit (1));
   KUnk (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 8);
   KRange (EVar 53) 7077888 140737479966656;
   KAlign (EVar 53) 64;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 53) 0) (ELit 64);
   KDisj (SA (EVar 2) (-9792)) (ELit 9792) (SA (EVar 53) 0) (ELit 64);
   KRange (EVar 48) 7077888 140737479966719;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 2) (-9792)) (ELit 9792) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 48) 0) (ELit 1) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 48) 0) (ELit 1) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit (34));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit (2));
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 48) 0) (ELit 1) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) (2147450880)) (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-96)) 8 (EVar 26);
   KWord (SA (EVar 2) (-104)) 8 (EVar 27);
   KWord (SA (EVar 2) (-192)) 8 (ELit (3));
   KWord (SA (EVar 2) (-184)) 8 (EVar 11);
   KWord (SA (EVar 2) (-176)) 8 (EVar 53);
   KWord (SA (EVar 2) (-168)) 8 (EVar 53);
   KWord (SA (EVar 2) (-160)) 8 (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) (ELit (2147450880)));
   KWord (SA (EVar 2) (-152)) 8 (APC.eaddz (EVar 10) (211));
   KWord (SA (EVar 2) (-144)) 8 (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (128)) (ELit 3)) (ELit (2147450880)));
   KWord (SA (EVar 2) (-136)) 8 (APC.eaddz (EVar 10) (128));
   KWord (SA (EVar 2) (-112)) 8 (EVar 53);
   KUnk (SA (EVar 2) (-9792)) (ELit (9600));
   KUnk (SA (EVar 2) (-128)) (ELit (16));
   KRange (EVar 54) (1) (16384);
   KRange (APC.esub (EVar 33) (EVar 54)) (0) (16383);
   KRange (APC.eaddz (APC.escale (64) (EVar 54)) (6)) (0) (4611686018427387904)]
  60 [((EVar 2), (-9792), ELit 9792); ((EVar 10), (200), ELit 8); ((EVar 10), (211), ELit 1); ((EVar 53), (0), ELit 24); ((EVar 53), (32), ELit 24); ((EAlu Instr.ALU_SRL (EVar 53) (ELit 3)), (2147450880), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 54)) (4)).
Definition BL4 : CA.blocks := [].
Definition hints4 : list (nat * CC.subst) := [(5%nat, [(86%nat, (EVar 54))])].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 914180 [EVar 0; (EVar 60); (APC.eaddz (EVar 2) (-192)); EVar 3; EVar 4; (EVar 61); (EVar 62); (EVar 63); (EVar 2); (APC.eaddz (EVar 2) (-192)); (ELit (1172321806)); (EVar 65); (EVar 66); (EVar 67); (EVar 68); (EVar 69); (EVar 70); (EVar 71); (EVar 72); (APC.eadd (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (ELit (2147450880))); (EVar 73); (EVar 74); (EVar 75); (EVar 76); (EVar 77); (EVar 78); (EVar 79); (EVar 80); (EVar 81); (EVar 82); (EVar 83); (EVar 84)]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KImg (1419712) (1421408);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 10) (96)) 8 (ELit (1421312));
   KWord (SA (EVar 10) (128)) 8 (APC.eaddz (EVar 10) (96));
   KRange (EVar 10) (7077888) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 11) (7077888) (140737479966704);
   KAlign (EVar 11) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (16));
   KWr (SA (EVar 2) (-9792)) (ELit (9792));
   KRange (EVar 2) (140735332492864) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 11) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 7069728) (ELit 544);
   KWord (SA (EVar 10) (211)) 1 (EVar 85);
   KRange (EVar 85) (0) (1);
   KWord (SA (EVar 10) (200)) 8 (EVar 87);
   KWord (SA (EVar 53) (0)) 8 (ELit (1102416563));
   KWord (SA (EVar 53) (8)) 8 (ELit (110998));
   KWord (SA (EVar 53) (16)) 8 (ELit (913528));
   KUnk (SA (EVar 53) (24)) (ELit (32));
   KWr (SA (EVar 53) (0)) (ELit (64));
   KWr (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 8);
   KWord (SA (EVar 53) (56)) 8 (EVar 48);
   KWr (SA (EVar 48) (0)) (ELit (1));
   KUnk (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 8);
   KRange (EVar 53) 7077888 140737479966656;
   KAlign (EVar 53) 64;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 53) 0) (ELit 64);
   KDisj (SA (EVar 2) (-9792)) (ELit 9792) (SA (EVar 53) 0) (ELit 64);
   KRange (EVar 48) 7077888 140737479966719;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 2) (-9792)) (ELit 9792) (SA (EVar 48) 0) (ELit 1);
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 48) 0) (ELit 1) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 48) 0) (ELit 1) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit (34));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit (2));
   KDisj (SA (EVar 53) 0) (ELit 64) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 48) 0) (ELit 1) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) (2147450880)) (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-96)) 8 (EVar 26);
   KWord (SA (EVar 2) (-104)) 8 (EVar 27);
   KWord (SA (EVar 2) (-176)) 8 (EVar 53);
   KWord (SA (EVar 2) (-168)) 8 (EVar 53);
   KUnk (SA (EVar 2) (-9792)) (ELit (9600))]
  88 [((EVar 2), (-9792), ELit 9792); ((EVar 10), (200), ELit 8); ((EVar 10), (211), ELit 1); ((EVar 53), (0), ELit 24); ((EVar 53), (32), ELit 24); ((EAlu Instr.ALU_SRL (EVar 53) (ELit 3)), (2147450880), ELit 8); ((EVar 48), (0), ELit 1)] [] (APC.escale (64) (EVar 86)).
Definition BL5 : CA.blocks := [].
Definition hints5 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [913940] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 800 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
