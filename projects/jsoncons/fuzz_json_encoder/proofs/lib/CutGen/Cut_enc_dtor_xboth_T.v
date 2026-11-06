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
Definition ITR : list (Z * nat) := [(731020, 18%nat); (769296, 72%nat); (769584, 37%nat); (769732, 47%nat); (769920, 46%nat); (770104, 34%nat); (850580, 73%nat); (738756, 176%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 40.
Definition ENDS : list Z := [731088].
Definition HDECL : CH.hdecl := CH.HD (4224) (8224) [((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 51); ((EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)), (2147450880), ELit 1)] [((EVar 10), (0), ELit 408)] [(1433600, 1466368)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880)].
Definition GLO : Z := 1433600.
Definition GHI : Z := 1466368.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 542968 4096 0%nat (fun _ _ => None) (fun _ => [((EAlu Instr.ALU_SRL (EVar 32) (ELit 3)), 2147450880, (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3)))]) (fun _ BL => BL) (fun _ _ _ BLk => ([KImg (1433600) (1466368); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)], BLk)) (fun F => F)) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1046256 4096 0%nat (fun _ _ => None) (fun _ => []) (fun regs BL => List.filter (fun be => negb (expr_eqb (fst be) (nth 10 regs (ELit 0)))) BL) (fun _ _ _ BLk => ([KImg (1433600) (1466368); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)] ++ [KZero (SA (ELit 0) 2147630265) (ELit 2); KZero (SA (ELit 0) 2147630255) (ELit 1)], BLk)) (fun F => F)) (fun _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 731020 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1433600) (1466368);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KZero (SA (ELit 0) 2147630265) (ELit 2);
   KZero (SA (ELit 0) 2147630255) (ELit 1);
   KWord (SA (EVar 10) (48)) 1 (ELit (2));
   KWord (SA (EVar 10) (96)) 1 (ELit (0));
   KWord (SA (EVar 10) (120)) 1 (ELit (0));
   KWord (SA (EVar 10) (144)) 1 (ELit (0));
   KWord (SA (EVar 10) (168)) 1 (ELit (0));
   KWord (SA (EVar 10) (192)) 1 (ELit (0));
   KWord (SA (EVar 10) (216)) 1 (ELit (0));
   KWord (SA (EVar 10) (264)) 8 (ELit (0));
   KWord (SA (EVar 10) (272)) 8 (ELit (0));
   KWord (SA (EVar 10) (280)) 8 (ELit (0));
   KUnk (SA (EVar 10) (0)) (ELit (408));
   KWr (SA (EVar 10) (0)) (ELit (408));
   KRange (EVar 10) 7094272 140737479966312;
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (51));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (408));
   KUnk (SA (EVar 2) (-4224)) (ELit (4224));
   KWr (SA (EVar 2) (-4224)) (ELit (4224));
   KRange (EVar 2) (140735332487296) (140737488355328);
   KAlign (EVar 2) (16);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (EVar 2) (-4224)) (ELit (4224)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 51) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) (2147450880)) (ELit 1)]
  40 [((EVar 2), (-4224), ELit 4224); ((EVar 10), (0), ELit 408)] [] (ELit (20)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 731020 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1433600) (1466368);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KZero (SA (ELit 0) 2147630265) (ELit 2);
   KZero (SA (ELit 0) 2147630255) (ELit 1);
   KWord (SA (EVar 10) (48)) 1 (ELit (2));
   KWord (SA (EVar 10) (96)) 1 (ELit (0));
   KWord (SA (EVar 10) (120)) 1 (ELit (0));
   KWord (SA (EVar 10) (144)) 1 (ELit (0));
   KWord (SA (EVar 10) (168)) 1 (ELit (0));
   KWord (SA (EVar 10) (192)) 1 (ELit (0));
   KWord (SA (EVar 10) (216)) 1 (ELit (0));
   KWord (SA (EVar 10) (264)) 8 (EVar 32);
   KWord (SA (EVar 10) (272)) 8 (APC.eadd (EVar 32) (APC.escale (32) (EVar 33)));
   KWord (SA (EVar 10) (280)) 8 (APC.eadd (EVar 32) (EVar 34));
   KRange (EVar 32) (4096) (140737479966720);
   KAlign (EVar 32) (16);
   KRange (EVar 34) (32) (32768);
   KRange (EVar 33) (0) (1024);
   KRange (APC.escale (32) (EVar 33)) (0) (32768);
   KRange (APC.esub (EVar 34) (APC.escale (32) (EVar 33))) (0) (32768);
   KRange (EAlu Instr.ALU_AND (EVar 34) (ELit 31)) 0 0;
   KDisj (SA (EVar 2) (-4224)) (ELit (4224)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 51) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) (2147450880)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 10) (0)) (ELit 408) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 2) (-4224)) (ELit 4224) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KUnk (SA (EVar 10) (0)) (ELit (408));
   KWr (SA (EVar 10) (0)) (ELit (408));
   KRange (EVar 10) 7094272 140737479966312;
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (51));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (408));
   KUnk (SA (EVar 2) (-4224)) (ELit (4224));
   KWr (SA (EVar 2) (-4224)) (ELit (4224));
   KRange (EVar 2) (140735332487296) (140737488355328);
   KAlign (EVar 2) (16);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (EVar 2) (-4224)) (ELit (4224)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 51) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) (2147450880)) (ELit 1)]
  40 [((EVar 2), (-4224), ELit 4224); ((EVar 10), (0), ELit 408)] [] (ELit (2000)).
Definition BL1 : CA.blocks := [((EVar 32), (EVar 34))].
Definition hints1 : list (nat * CC.subst) := [(2%nat, [(40%nat, (EVar 33))])].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 769660 [EVar 0; (ELit (769392)); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (APC.eaddz (EVar 2) (-24)); (ELit (2147450880)); (APC.eaddz (EVar 10) (264)); (APC.eaddz (EVar 10) (272)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (272)) (ELit 3)) (ELit (2147450880))); (EVar 32); (APC.eadd (EVar 32) (APC.escale (32) (EVar 33))); (ELit (32)); (APC.eadd (EVar 32) (APC.escale (32) (EVar 40))); EVar 17; (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) (ELit (2147450880))); EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1433600) (1466368);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KZero (SA (ELit 0) 2147630265) (ELit 2);
   KZero (SA (ELit 0) 2147630255) (ELit 1);
   KWord (SA (EVar 10) (48)) 1 (ELit (2));
   KWord (SA (EVar 10) (96)) 1 (ELit (0));
   KWord (SA (EVar 10) (120)) 1 (ELit (0));
   KWord (SA (EVar 10) (144)) 1 (ELit (0));
   KWord (SA (EVar 10) (168)) 1 (ELit (0));
   KWord (SA (EVar 10) (192)) 1 (ELit (0));
   KWord (SA (EVar 10) (216)) 1 (ELit (0));
   KWord (SA (EVar 10) (264)) 8 (EVar 32);
   KWord (SA (EVar 10) (272)) 8 (APC.eadd (EVar 32) (APC.escale (32) (EVar 33)));
   KWord (SA (EVar 10) (280)) 8 (APC.eadd (EVar 32) (EVar 34));
   KRange (EVar 32) (4096) (140737479966720);
   KAlign (EVar 32) (16);
   KRange (EVar 34) (32) (32768);
   KRange (EVar 33) (0) (1024);
   KRange (APC.escale (32) (EVar 33)) (0) (32768);
   KRange (APC.esub (EVar 34) (APC.escale (32) (EVar 33))) (0) (32768);
   KRange (EAlu Instr.ALU_AND (EVar 34) (ELit 31)) 0 0;
   KDisj (SA (EVar 2) (-4224)) (ELit (4224)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 51) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) (2147450880)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 10) (0)) (ELit 408) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 2) (-4224)) (ELit 4224) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KUnk (SA (EVar 10) (0)) (ELit (408));
   KWr (SA (EVar 10) (0)) (ELit (408));
   KRange (EVar 10) 7094272 140737479966312;
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (51));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (408));
   KWr (SA (EVar 2) (-4224)) (ELit (4224));
   KRange (EVar 2) (140735332487296) (140737488355328);
   KAlign (EVar 2) (16);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (EVar 2) (-4224)) (ELit (4224)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 51) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) (2147450880)) (ELit 1);
   KUnk (SA (EVar 2) (-4224)) (ELit (4144));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KUnk (SA (EVar 2) (-32)) (ELit (8));
   KRange (EVar 33) (1) (1024);
   KRange (EVar 40) (1) (1024);
   KRange (APC.eaddz (EVar 40) (100)) (0) (4611686018427387904);
   KWord (SA (EVar 2) (-72)) 8 (ELit (769392));
   KWord (SA (EVar 2) (-40)) 8 (ELit (731052));
   KWord (SA (EVar 2) (-24)) 8 (APC.eaddz (EVar 10) (264));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-48)) 8 (EVar 10);
   KWord (SA (EVar 2) (-56)) 8 (EVar 9);
   KWord (SA (EVar 2) (-64)) 8 (EVar 18)]
  41 [((EVar 2), (-4224), ELit 4224); ((EVar 10), (0), ELit 408)] [] (APC.eaddz (EVar 40) (100)).
Definition BL2 : CA.blocks := [((EVar 32), (EVar 34))].
Definition hints2 : list (nat * CC.subst) := [(2%nat, [(40%nat, (APC.eaddz (EVar 40) (-1)))])].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 769676 [EVar 0; (ELit (769392)); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (APC.eaddz (EVar 2) (-24)); (ELit (2147450880)); (APC.eaddz (EVar 10) (264)); (APC.eaddz (EVar 10) (272)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (272)) (ELit 3)) (ELit (2147450880))); (EVar 32); (APC.eadd (EVar 32) (APC.escale (32) (EVar 33))); (EVar 40); (EVar 41); EVar 17; (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) (ELit (2147450880))); EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1433600) (1466368);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KZero (SA (ELit 0) 2147630265) (ELit 2);
   KZero (SA (ELit 0) 2147630255) (ELit 1);
   KWord (SA (EVar 10) (48)) 1 (ELit (2));
   KWord (SA (EVar 10) (96)) 1 (ELit (0));
   KWord (SA (EVar 10) (120)) 1 (ELit (0));
   KWord (SA (EVar 10) (144)) 1 (ELit (0));
   KWord (SA (EVar 10) (168)) 1 (ELit (0));
   KWord (SA (EVar 10) (192)) 1 (ELit (0));
   KWord (SA (EVar 10) (216)) 1 (ELit (0));
   KWord (SA (EVar 10) (264)) 8 (EVar 32);
   KWord (SA (EVar 10) (272)) 8 (APC.eadd (EVar 32) (APC.escale (32) (EVar 33)));
   KWord (SA (EVar 10) (280)) 8 (APC.eadd (EVar 32) (EVar 34));
   KRange (EVar 32) (4096) (140737479966720);
   KAlign (EVar 32) (16);
   KRange (EVar 34) (32) (32768);
   KRange (EVar 33) (0) (1024);
   KRange (APC.escale (32) (EVar 33)) (0) (32768);
   KRange (APC.esub (EVar 34) (APC.escale (32) (EVar 33))) (0) (32768);
   KRange (EAlu Instr.ALU_AND (EVar 34) (ELit 31)) 0 0;
   KDisj (SA (EVar 2) (-4224)) (ELit (4224)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 51) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) (2147450880)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 10) (0)) (ELit 408) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 2) (-4224)) (ELit 4224) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KUnk (SA (EVar 10) (0)) (ELit (408));
   KWr (SA (EVar 10) (0)) (ELit (408));
   KRange (EVar 10) 7094272 140737479966312;
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (51));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (408));
   KWr (SA (EVar 2) (-4224)) (ELit (4224));
   KRange (EVar 2) (140735332487296) (140737488355328);
   KAlign (EVar 2) (16);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (EVar 2) (-4224)) (ELit (4224)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 51) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-24)) (ELit 3)) (2147450880)) (ELit 1);
   KUnk (SA (EVar 2) (-4224)) (ELit (4144));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KUnk (SA (EVar 2) (-32)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (ELit (769392));
   KWord (SA (EVar 2) (-40)) 8 (ELit (731052));
   KWord (SA (EVar 2) (-24)) 8 (APC.eaddz (EVar 10) (264));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-48)) 8 (EVar 10);
   KWord (SA (EVar 2) (-56)) 8 (EVar 9);
   KWord (SA (EVar 2) (-64)) 8 (EVar 18)]
  42 [((EVar 2), (-4224), ELit 4224); ((EVar 10), (0), ELit 408)] [] (ELit (90)).
Definition BL3 : CA.blocks := [((EVar 32), (EVar 34))].
Definition hints3 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
