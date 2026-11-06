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
Definition ITR : list (Z * nat) := [(754188, 478%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [755544].
Definition HDECL : CH.hdecl := CH.HD (13824) (8224) [((EVar 10), (0), ELit 296); ((EVar 10), (304), ELit 104); ((EVar 11), (0), ELit 16); ((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 51); ((EAlu Instr.ALU_SRL (EVar 32) (ELit 3)), (2147450880), ELit 3); ((EAlu Instr.ALU_SRL (EVar 11) (ELit 3)), (2147450880), ELit 2)] [((EVar 10), (296), ELit 8); ((EVar 32), (0), ELit 24)] [(1459384, 1463120)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880); (1497024, 4, 1)].
Definition GLO : Z := 1459384.
Definition GHI : Z := 1463120.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 420020 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1); KRange (EVar (g + 5)) 7094272 140737479966592; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 128); KWr (SA (EVar (g + 5)) 0) (ELit 128); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 128); KDisj (SA (EVar 2) (-13824)) (ELit 13824) (SA (EVar (g + 5)) 0) (ELit 128); KWord (SA (EVar (g + 5)) 120) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7094272 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-13824)) (ELit 13824) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (0)) (ELit (296)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (0)) (ELit (296)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (296)) (ELit (8)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (296)) (ELit (8)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (304)) (ELit (104)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (304)) (ELit (104)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 32) (0)) (ELit (24)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 32) (0)) (ELit (24)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 11) (0)) (ELit (16)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 11) (0)) (ELit (16)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit (51)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (ELit (3)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit (2)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 34) (0)) (EVar 35); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 34) (0)) (EVar 35); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 35) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-28)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-16)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-8)) (ELit 3)) (2147450880)) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-28)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-16)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-8)) (ELit 3)) 2147450880) (ELit (1))], BLk)) (fun F => let g := 48%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 88); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 16)]))) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 770716 4560 0%nat (fun _ _ => None) (fun regs => [(ESA.col_region regs); ((EVar 32), 0, ELit 24)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1)] ++ [KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-28)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-16)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-8)) (ELit 3)) 2147450880) (ELit (1))] ++ match CAX.cell_at cells (EVar 53) 120 8 with Some fl => [KWord (SA (EVar 53) 120) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun _ => [((EVar 53), 1, -160)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1056004 4368 0%nat (fun _ _ => None) (fun regs => [((EVar 32), 0, ELit 24)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (EVar 53) 120 8 with Some fl => [KWord (SA (EVar 53) 120) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun _ => [((EVar 53), 1, -160)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 785716 4528 1%nat (fun regs g => Some (EVar g)) (fun regs => [((EVar 32), 0, ELit 24)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1)] ++ [KRange (EVar g) 0 1125899906842624] ++ match CAX.cell_at cells (EVar 53) 120 8 with Some fl => [KWord (SA (EVar 53) 120) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F ++ [((EVar 2), -8, ELit 8)])) (fun _ => [((EVar 53), 1, -160)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1055420 4368 0%nat (fun _ _ => None) (fun regs => [((EVar 32), 0, ELit 24)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1)] ++ (if expr_eqb (nth 11 regs (ELit 0)) (ELit 150396) then [KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-28)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-16)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-8)) (ELit 3)) 2147450880) (ELit (1))] else []) ++ match CAX.cell_at cells (EVar 53) 120 8 with Some fl => [KWord (SA (EVar 53) 120) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => if existsb (fun r : expr * Z * expr => (expr_eqb (fst (fst r)) (EVar 2) && Z.eqb (snd (fst r)) (-8) && expr_eqb (snd r) (ELit 8))%bool) F then F ++ [((EVar 48), 0, ELit 1)] else F)) (fun _ => [((EVar 53), 1, -160)]))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 754188 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1497024) 4 (ELit 1);
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (24)) 1 (APC.escale (16) (EVar 43));
   KRange (EVar 43) (0) (15);
   KWord (SA (EVar 10) (40)) 8 (ELit (120));
   KWord (SA (EVar 10) (296)) 8 (EVar 37);
   KRange (EVar 37) (0) (18446744073709551615);
   KWr (SA (EVar 10) (296)) (ELit (8));
   KWord (SA (EVar 10) (304)) 8 (ELit (150388));
   KWord (SA (EVar 10) (312)) 8 (ELit (2));
   KWord (SA (EVar 10) (320)) 8 (ELit (150396));
   KWord (SA (EVar 10) (328)) 8 (ELit (2));
   KRange (EVar 10) (7094272) (140737479966312);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (51));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (408));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-13824)) (ELit (13824)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EVar 2) (-13824)) (ELit (13824)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 11) (0)) 8 (EVar 41);
   KWord (SA (EVar 11) (8)) 8 (EVar 42);
   KRange (EVar 42) (0) (140737488355328);
   KRange (EVar 11) (7094272) (140737479966704);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (2));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 2) (-13824)) (ELit (13824)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 32) (0)) (ELit (24)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 11) (0)) (ELit (16)) (SA (EVar 34) (0)) (EVar 35);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 35) (7)) (ELit 3)) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 2);
   KUnk (SA (EVar 2) (-13824)) (ELit (13824));
   KWr (SA (EVar 2) (-13824)) (ELit (13824));
   KRange (EVar 2) (140735332496896) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-13824)) (ELit (13824));
   KWord (SA (EVar 10) (264)) 8 (EVar 34);
   KWord (SA (EVar 10) (272)) 8 (APC.eadd (EVar 34) (APC.escale (32) (EVar 33)));
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) 4 (EVar 38);
   KRange (EVar 38) (0) (1);
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-28)) 1 (ELit (0));
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-27)) 1 (EVar 39);
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) 1 (EVar 40);
   KRange (EVar 40) (0) (1);
   KWr (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) (ELit (1));
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-8)) 8 (EVar 36);
   KWr (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-16)) (ELit (8));
   KUnk (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) (ELit (32));
   KRange (EVar 33) (1) (1024);
   KRange (APC.esub (EVar 35) (APC.escale (32) (EVar 33))) (0) (32768);
   KRange (EVar 35) (32) (32768);
   KRange (EVar 34) (4096) (140737479966688);
   KAlign (EVar 34) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 34) (0)) (EVar 35);
   KRange (EVar 36) (0) (0);
   KDisj (SA (EVar 2) (-13824)) (ELit (13824)) (SA (EVar 34) (0)) (EVar 35);
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 34) (0)) (EVar 35);
   KDisj (SA (EVar 32) (0)) (ELit (24)) (SA (EVar 34) (0)) (EVar 35);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 35) (7)) (ELit 3)) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 51);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 35) (7)) (ELit 3)) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 3);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) (ELit 3)) 2147450880) (ELit (1));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-28)) (ELit 3)) 2147450880) (ELit (1));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) (ELit 3)) 2147450880) (ELit (1));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-16)) (ELit 3)) 2147450880) (ELit (1));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-8)) (ELit 3)) 2147450880) (ELit (1))]
  48 [((EVar 2), (-13824), ELit 13824); ((EVar 10), (296), ELit 8); ((APC.eadd (EVar 34) (APC.escale (32) (EVar 33))), (-26), ELit 1); ((APC.eadd (EVar 34) (APC.escale (32) (EVar 33))), (-16), ELit 8)] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [((EVar 34), (EVar 35))].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 1500 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
