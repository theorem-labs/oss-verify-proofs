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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsXB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(770716, 360%nat); (772204, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [771748].
Definition HDECL : CH.hdecl := CH.HD (4560) (8224) [((EVar 10), (0), ELit 296); ((EVar 10), (304), ELit 104); ((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 51); ((EAlu Instr.ALU_SRL (EVar 32) (ELit 3)), (2147450880), ELit 3)] [((EVar 10), (296), ELit 8); ((EVar 32), (0), ELit 24)] [(1459384, 1463120)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880); (1497024, 4, 1)].
Definition GLO : Z := 1459384.
Definition GHI : Z := 1463120.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 420420 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1); KRange (EVar (g + 5)) 7094272 140737479966464; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 256); KWr (SA (EVar (g + 5)) 0) (ELit 256); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 32); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 32); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 256); KDisj (SA (EVar 2) (-4560)) (ELit 4560) (SA (EVar (g + 5)) 0) (ELit 256); KWord (SA (EVar (g + 5)) 248) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7094272 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 256) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-4560)) (ELit 4560) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 256) (SA (EVar 10) (0)) (ELit (296)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (0)) (ELit (296)); KDisj (SA (EVar (g + 5)) 0) (ELit 256) (SA (EVar 10) (296)) (ELit (8)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (296)) (ELit (8)); KDisj (SA (EVar (g + 5)) 0) (ELit 256) (SA (EVar 10) (304)) (ELit (104)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (304)) (ELit (104)); KDisj (SA (EVar (g + 5)) 0) (ELit 256) (SA (EVar 32) (0)) (ELit (24)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 32) (0)) (ELit (24)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 32) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit (51)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 32) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (ELit (3))], BLk)) (fun F => let g := 48%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 216); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 32)]))) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 527120 2560 0%nat (fun _ _ => None) (fun regs => (match split_lit (nth 10 regs (ELit 0)) with (b, o) => [(b, o, ELit 24)] end)) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1)] ++ (match split_lit (nth 10 regs (ELit 0)) with (b, o) => [KWord (SA b o) 8 (ELit 2562); KWord (SA b (o + 8)) 8 (ELit 0); KWord (SA b (o + 16)) 8 (ELit 0)] end) ++ match CAX.cell_at cells (EVar 53) 248 8 with Some fl => [KWord (SA (EVar 53) 248) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun _ => [((EVar 53), 2, -160)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1055420 4368 0%nat (fun _ _ => None) (fun regs => [((EVar 32), 0, ELit 24)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (EVar 53) 248 8 with Some fl => [KWord (SA (EVar 53) 248) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun _ => [((EVar 53), 2, -160)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1056004 4368 0%nat (fun _ _ => None) (fun regs => [((EVar 32), 0, ELit 24)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (EVar 53) 248 8 with Some fl => [KWord (SA (EVar 53) 248) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun _ => [((EVar 53), 2, -160)]))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 770716 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1497024) 4 (ELit 1);
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (48)) 8 (ELit (2562));
   KWord (SA (EVar 10) (56)) 8 (ELit (0));
   KWord (SA (EVar 10) (64)) 8 (ELit (0));
   KWord (SA (EVar 10) (248)) 1 (ELit (32));
   KWord (SA (EVar 10) (288)) 4 (APC.escale (4) (EVar 33));
   KUnk (SA (EVar 10) (296)) (ELit (8));
   KWr (SA (EVar 10) (296)) (ELit (8));
   KRange (EVar 10) (7094272) (140737479966312);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (51));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (408));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-4560)) (ELit (4560)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EVar 2) (-4560)) (ELit (4560)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4560)) (ELit (4560));
   KWr (SA (EVar 2) (-4560)) (ELit (4560));
   KRange (EVar 2) (140735332487632) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4560)) (ELit (4560));
   KRange (EVar 33) (1) (1024)]
  48 [((EVar 2), (-4560), ELit 4560); ((EVar 10), (296), ELit 8)] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 771324 [EVar 0; (EVar 66); (APC.eaddz (EVar 2) (-160)); EVar 3; EVar 4; (EVar 67); (EVar 68); (EVar 69); (EVar 2); (APC.eaddz (EVar 2) (-160)); (EVar 70); (EVar 71); (EVar 72); (EVar 73); (EVar 74); (EVar 75); (EVar 76); (EVar 77); (APC.esub (APC.escale (4) (EVar 33)) (EVar 65)); (ELit (2147450880)); (APC.eaddz (EVar 10) (288)); (APC.eaddz (EVar 10) (8)); (APC.eaddz (EVar 10) (248)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (288)) (ELit 3)) (ELit 2147450880)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (ELit 2147450880)); (EVar 53); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (248)) (ELit 3)) (ELit 2147450880)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (8)) (ELit 3)) (ELit 2147450880)); (EVar 78); (EVar 79); (EVar 80); (EVar 81)]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1497024) 4 (ELit 1);
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (48)) 8 (ELit (2562));
   KWord (SA (EVar 10) (56)) 8 (ELit (0));
   KWord (SA (EVar 10) (64)) 8 (ELit (0));
   KWord (SA (EVar 10) (248)) 1 (ELit (32));
   KWord (SA (EVar 10) (288)) 4 (APC.escale (4) (EVar 33));
   KUnk (SA (EVar 10) (296)) (ELit (8));
   KWr (SA (EVar 10) (296)) (ELit (8));
   KRange (EVar 10) (7094272) (140737479966312);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (51));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (408));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-4560)) (ELit (4560)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EVar 2) (-4560)) (ELit (4560)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4560)) (ELit (4384));
   KUnk (SA (EVar 2) (-160)) (ELit (16));
   KUnk (SA (EVar 2) (-128)) (ELit (16));
   KWr (SA (EVar 2) (-4560)) (ELit (4560));
   KRange (EVar 2) (140735332487632) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4560)) (ELit (4560));
   KRange (EVar 53) (7094272) (140737479966464);
   KAlign (EVar 53) (64);
   KUnk (SA (EVar 53) (0)) (ELit (248));
   KWr (SA (EVar 53) (0)) (ELit (256));
   KWr (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 53) (0)) (ELit (256));
   KDisj (SA (EVar 2) (-4560)) (ELit (4560)) (SA (EVar 53) (0)) (ELit (256));
   KWord (SA (EVar 53) (248)) 8 (EVar 48);
   KWr (SA (EVar 48) (0)) (ELit (1));
   KRange (EVar 48) (7094272) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) (0)) (ELit (1));
   KDisj (SA (EVar 53) (0)) (ELit (256)) (SA (EVar 48) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-4560)) (ELit (4560)) (SA (EVar 48) (0)) (ELit (1));
   KDisj (SA (EVar 53) (0)) (ELit (256)) (SA (EVar 10) (0)) (ELit (296));
   KDisj (SA (EVar 48) (0)) (ELit (1)) (SA (EVar 10) (0)) (ELit (296));
   KDisj (SA (EVar 53) (0)) (ELit (256)) (SA (EVar 10) (296)) (ELit (8));
   KDisj (SA (EVar 48) (0)) (ELit (1)) (SA (EVar 10) (296)) (ELit (8));
   KDisj (SA (EVar 53) (0)) (ELit (256)) (SA (EVar 10) (304)) (ELit (104));
   KDisj (SA (EVar 48) (0)) (ELit (1)) (SA (EVar 10) (304)) (ELit (104));
   KDisj (SA (EVar 53) (0)) (ELit (256)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 48) (0)) (ELit (1)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 32) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 51);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 32) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 3);
   KWord (SA (EVar 2) (-144)) 8 (EVar 53);
   KWord (SA (EVar 2) (-136)) 8 (EVar 10);
   KWord (SA (EVar 2) (-112)) 8 (EVar 53);
   KWord (SA (EVar 2) (-104)) 8 (EVar 27);
   KWord (SA (EVar 2) (-96)) 8 (EVar 26);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KRange (EVar 33) (1) (1024);
   KRange (EVar 65) (1) (4096);
   KRange (APC.esub (APC.escale (4) (EVar 33)) (EVar 65)) (0) (4096)]
  82 [((EVar 2), (-4560), ELit 4560); ((EVar 10), (296), ELit 8); ((EVar 53), (0), ELit 24); ((EVar 53), (32), ELit 216); ((EAlu Instr.ALU_SRL (EVar 53) (ELit 3)), (2147450880), ELit 32)] [] (APC.eaddz (APC.escale (4) (EVar 65)) (2)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 771416 [EVar 0; (EVar 66); (APC.eaddz (EVar 2) (-160)); EVar 3; EVar 4; (EVar 67); (EVar 68); (EVar 69); (EVar 2); (APC.eaddz (EVar 2) (-160)); (EVar 70); (APC.escale (4) (EVar 33)); (EVar 72); (EVar 73); (EVar 74); (EVar 75); (EVar 76); (EVar 77); (APC.eaddz (APC.esub (APC.escale (4) (EVar 33)) (EVar 65)) (1)); (ELit (2147450880)); (APC.eaddz (EVar 10) (288)); (APC.eaddz (EVar 10) (8)); (APC.eaddz (EVar 10) (248)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (288)) (ELit 3)) (ELit 2147450880)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) (ELit 2147450880)); (EVar 53); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (248)) (ELit 3)) (ELit 2147450880)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (8)) (ELit 3)) (ELit 2147450880)); (EVar 78); (EVar 79); (EVar 80); (EVar 81)]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1497024) 4 (ELit 1);
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (48)) 8 (ELit (2562));
   KWord (SA (EVar 10) (56)) 8 (ELit (0));
   KWord (SA (EVar 10) (64)) 8 (ELit (0));
   KWord (SA (EVar 10) (248)) 1 (ELit (32));
   KWord (SA (EVar 10) (288)) 4 (APC.escale (4) (EVar 33));
   KUnk (SA (EVar 10) (296)) (ELit (8));
   KWr (SA (EVar 10) (296)) (ELit (8));
   KRange (EVar 10) (7094272) (140737479966312);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (51));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (408));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-4560)) (ELit (4560)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EVar 2) (-4560)) (ELit (4560)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4560)) (ELit (4384));
   KUnk (SA (EVar 2) (-160)) (ELit (16));
   KUnk (SA (EVar 2) (-128)) (ELit (16));
   KWr (SA (EVar 2) (-4560)) (ELit (4560));
   KRange (EVar 2) (140735332487632) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4560)) (ELit (4560));
   KRange (EVar 53) (7094272) (140737479966464);
   KAlign (EVar 53) (64);
   KUnk (SA (EVar 53) (0)) (ELit (248));
   KWr (SA (EVar 53) (0)) (ELit (256));
   KWr (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 53) (0)) (ELit (256));
   KDisj (SA (EVar 2) (-4560)) (ELit (4560)) (SA (EVar 53) (0)) (ELit (256));
   KWord (SA (EVar 53) (248)) 8 (EVar 48);
   KWr (SA (EVar 48) (0)) (ELit (1));
   KRange (EVar 48) (7094272) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 48) (0)) (ELit (1));
   KDisj (SA (EVar 53) (0)) (ELit (256)) (SA (EVar 48) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-4560)) (ELit (4560)) (SA (EVar 48) (0)) (ELit (1));
   KDisj (SA (EVar 53) (0)) (ELit (256)) (SA (EVar 10) (0)) (ELit (296));
   KDisj (SA (EVar 48) (0)) (ELit (1)) (SA (EVar 10) (0)) (ELit (296));
   KDisj (SA (EVar 53) (0)) (ELit (256)) (SA (EVar 10) (296)) (ELit (8));
   KDisj (SA (EVar 48) (0)) (ELit (1)) (SA (EVar 10) (296)) (ELit (8));
   KDisj (SA (EVar 53) (0)) (ELit (256)) (SA (EVar 10) (304)) (ELit (104));
   KDisj (SA (EVar 48) (0)) (ELit (1)) (SA (EVar 10) (304)) (ELit (104));
   KDisj (SA (EVar 53) (0)) (ELit (256)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 48) (0)) (ELit (1)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 32) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 51);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 53) (ELit 3)) 2147450880) (ELit 32) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 3);
   KWord (SA (EVar 2) (-144)) 8 (EVar 53);
   KWord (SA (EVar 2) (-136)) 8 (EVar 10);
   KWord (SA (EVar 2) (-112)) 8 (EVar 53);
   KWord (SA (EVar 2) (-104)) 8 (EVar 27);
   KWord (SA (EVar 2) (-96)) 8 (EVar 26);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KRange (EVar 33) (1) (1024);
   KRange (EVar 65) (1) (1)]
  82 [((EVar 2), (-4560), ELit 4560); ((EVar 10), (296), ELit 8); ((EVar 53), (0), ELit 24); ((EVar 53), (32), ELit 216); ((EAlu Instr.ALU_SRL (EVar 53) (ELit 3)), (2147450880), ELit 32); ((EVar 48), (0), ELit 1)] [] (ELit (0)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 1500 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
