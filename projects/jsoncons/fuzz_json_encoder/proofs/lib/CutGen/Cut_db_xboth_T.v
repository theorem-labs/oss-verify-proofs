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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(828952, 145%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [829484; 829104].
Definition HDECL : CH.hdecl := CH.HD (4480) (8224) [((EVar 10), (0), ELit 32); ((EVar 13), (0), ELit 8); ((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 4); ((EAlu Instr.ALU_SRL (EVar 13) (ELit 3)), (2147450880), ELit 1)] [((EVar 32), (0), ELit 24)] [(1459384, 1463120)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880)].
Definition GLO : Z := 1459384.
Definition GHI : Z := 1463120.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (ESA.sink_xsumA 1056004 4368)].
Definition XSTOPS : list Z := [829104; 829092; 829112; 829132; 829236].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 828952 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 13) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (25);
   KRange (EVar 12) (0) (255);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 13) (7094272) (140737488355320);
   KAlign (EVar 13) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 13) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 13) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4480)) (ELit (4368));
   KWr (SA (EVar 2) (-4480)) (ELit (4480));
   KRange (EVar 2) (140735332487552) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4480)) (ELit (4480));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 13) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 13) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 13) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-112)) (ELit (112))]
  48 [((EVar 2), (-4480), ELit 4480)] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 829092 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 13); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 48))); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 12); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 48))); (APC.eadd (EVar 10) (EVar 11)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 13) (ELit 3)) (ELit 2147450880)); (ELit (10)); (ELit (18446744073709551615)); (ELit (68)); (ELit (2147450880)); (EVar 49); (ELit (69)); (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 13) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (25);
   KRange (EVar 12) (0) (255);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 13) (7094272) (140737488355320);
   KAlign (EVar 13) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 13) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 13) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4480)) (ELit (4368));
   KWr (SA (EVar 2) (-4480)) (ELit (4480));
   KRange (EVar 2) (140735332487552) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4480)) (ELit (4480));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 13) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 13) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 13) (0)) (ELit (8));
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
   KRange (EVar 48) (1) (25);
   KRange (APC.esub (EVar 11) (EVar 48)) (0) (24);
   KRange (EVar 49) (0) (1)]
  66 [((EVar 2), (-4480), ELit 4480)] [] (APC.eaddz (APC.escale (64) (EVar 48)) (8)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 829112 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 13); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 48))); (ELit (0)); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 12); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 48))); (APC.eadd (EVar 10) (EVar 11)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 13) (ELit 3)) (ELit 2147450880)); (ELit (10)); (ELit (18446744073709551615)); (ELit (68)); (ELit (2147450880)); (EVar 49); (ELit (69)); (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 13) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (25);
   KRange (EVar 12) (0) (255);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 13) (7094272) (140737488355320);
   KAlign (EVar 13) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 13) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 13) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4480)) (ELit (4368));
   KWr (SA (EVar 2) (-4480)) (ELit (4480));
   KRange (EVar 2) (140735332487552) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4480)) (ELit (4480));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 13) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 13) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 13) (0)) (ELit (8));
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
   KRange (EVar 48) (1) (25);
   KRange (APC.esub (EVar 11) (EVar 48)) (0) (24);
   KRange (EVar 49) (0) (1)]
  66 [((EVar 2), (-4480), ELit 4480)] [] (APC.eaddz (APC.escale (64) (EVar 48)) (6)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 829132 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 13); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 48))); (ELit (0)); (EVar 66); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 12); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 48))); (APC.eadd (EVar 10) (EVar 11)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 13) (ELit 3)) (ELit 2147450880)); (ELit (10)); (ELit (18446744073709551615)); (ELit (68)); (ELit (2147450880)); (EVar 49); (ELit (69)); (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 13) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (25);
   KRange (EVar 12) (0) (255);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 13) (7094272) (140737488355320);
   KAlign (EVar 13) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 13) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 13) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4480)) (ELit (4368));
   KWr (SA (EVar 2) (-4480)) (ELit (4480));
   KRange (EVar 2) (140735332487552) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4480)) (ELit (4480));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 13) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 13) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 13) (0)) (ELit (8));
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
   KRange (EVar 48) (1) (25);
   KRange (APC.esub (EVar 11) (EVar 48)) (0) (24);
   KRange (EVar 49) (0) (1);
   KRange (EVar 66) (0) (255)]
  68 [((EVar 2), (-4480), ELit 4480)] [] (APC.eaddz (APC.escale (64) (EVar 48)) (4)).
Definition BL3 : CA.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 829236 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 13); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 48))); (EVar 32); (EVar 66); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 12); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 48))); (APC.eadd (EVar 10) (EVar 11)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 13) (ELit 3)) (ELit 2147450880)); (ELit (10)); (ELit (18446744073709551615)); (ELit (68)); (ELit (2147450880)); (EVar 49); (ELit (69)); (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 13) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (25);
   KRange (EVar 12) (0) (255);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 13) (7094272) (140737488355320);
   KAlign (EVar 13) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 13) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 13) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4480)) (ELit (4368));
   KWr (SA (EVar 2) (-4480)) (ELit (4480));
   KRange (EVar 2) (140735332487552) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4480)) (ELit (4480));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 13) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4480)) (ELit (4480)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 13) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 13) (0)) (ELit (8));
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
   KRange (EVar 48) (1) (25);
   KRange (APC.esub (EVar 11) (EVar 48)) (0) (24);
   KRange (EVar 49) (0) (1);
   KRange (EVar 66) (0) (255)]
  68 [((EVar 2), (-4480), ELit 4480)] [] (APC.eaddz (APC.escale (64) (EVar 48)) (4)).
Definition BL4 : CA.blocks := [].
Definition hints4 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [829112] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 400 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
