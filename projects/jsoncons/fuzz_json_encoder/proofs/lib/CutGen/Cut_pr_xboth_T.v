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
Definition ITR : list (Z * nat) := [(833108, 391%nat); (837340, 144%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [834116; 833292; 833428; 834004; 833864; 834352].
Definition HDECL : CH.hdecl := CH.HD (4512) (8224) [((EVar 10), (0), ELit 32); ((EVar 15), (0), ELit 8); ((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 4); ((EAlu Instr.ALU_SRL (EVar 15) (ELit 3)), (2147450880), ELit 1)] [((EVar 32), (0), ELit 24)] [(1459384, 1463120)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880)].
Definition GLO : Z := 1459384.
Definition GHI : Z := 1463120.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (ESA.sink_xsumA 1056004 4368)].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 833108 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (EVar 12); (ELit (18446744073709551612)); (ELit (17)); (EVar 15); EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 12) (0) (16);
   KRange (APC.eadd (EVar 11) (EVar 12)) (1) (17);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4512))]
  48 [((EVar 2), (-4512), ELit 4512)] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [(5%nat, [(66%nat, (EVar 11))])].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 833108 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (APC.esub (EVar 33) (EVar 11)); (ELit (18446744073709551612)); (ELit (17)); (EVar 15); EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 33) (1) (17);
   KRange (APC.esub (EVar 11) (EVar 33)) (1) (20);
   KRange (APC.esub (EVar 33) (EVar 11)) (18446744073709551596) (18446744073709551615);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4512))]
  48 [((EVar 2), (-4512), ELit 4512)] [] (ELit (1048576)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [(8%nat, [(66%nat, (APC.eaddz (EVar 33) (24)))])].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 833108 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (APC.esub (ELit (0)) (APC.eadd (EVar 33) (EVar 11))); (ELit (18446744073709551612)); (ELit (17)); (EVar 15); EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 33) (0) (3);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4512))]
  48 [((EVar 2), (-4512), ELit 4512)] [] (ELit (1048576)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [(12%nat, [(66%nat, (EVar 33))]); (13%nat, [(66%nat, (EVar 11))])].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 833108 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (APC.esub (EVar 33) (EVar 11)); (ELit (18446744073709551612)); (ELit (17)); (EVar 15); EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 33) (18) (330);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4512))]
  48 [((EVar 2), (-4512), ELit 4512)] [] (ELit (1048576)).
Definition BL3 : CA.blocks := [].
Definition hints3 : list (nat * CC.subst) := [(15%nat, [(66%nat, (APC.eaddz (EVar 11) (-1)))]); (19%nat, [(70%nat, (ELit (8192))); (69%nat, (ELit (3)))])].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 833108 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (APC.esub (ELit (0)) (APC.eadd (EVar 33) (EVar 11))); (ELit (18446744073709551612)); (ELit (17)); (EVar 15); EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 33) (4) (342);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4512))]
  48 [((EVar 2), (-4512), ELit 4512)] [] (ELit (1048576)).
Definition BL4 : CA.blocks := [].
Definition hints4 : list (nat * CC.subst) := [(17%nat, [(66%nat, (APC.eaddz (EVar 11) (-1)))]); (19%nat, [(70%nat, (ELit (8192))); (69%nat, (ELit (3)))])].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 833240 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 11); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 10); (EVar 12); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (ELit (2147450880)); (APC.eadd (EVar 11) (EVar 12)); (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)); (ELit (1)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (EVar 66); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 12) (0) (16);
   KRange (APC.eadd (EVar 11) (EVar 12)) (1) (17);
   KRange (EVar 66) (1) (21);
   KRange (APC.esub (EVar 11) (EVar 66)) (0) (20);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  67 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (8)).
Definition BL5 : CA.blocks := [].
Definition hints5 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CC.CP 833300 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 11); (EVar 32); (ELit (0)); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 10); (EVar 12); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (ELit (2147450880)); (APC.eadd (EVar 11) (EVar 12)); (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)); (ELit (1)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (EVar 66); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 12) (0) (16);
   KRange (APC.eadd (EVar 11) (EVar 12)) (1) (17);
   KRange (EVar 66) (1) (21);
   KRange (APC.esub (EVar 11) (EVar 66)) (0) (20);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  67 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (6)).
Definition BL6 : CA.blocks := [].
Definition hints6 : list (nat * CC.subst) := [(7%nat, [(66%nat, (EVar 12))])].
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CC.CP 833488 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 10); (EVar 66); (EVar 67); (ELit (2147450880)); (APC.eadd (EVar 11) (EVar 12)); (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)); (EVar 71); (EVar 72); (EVar 73); (EVar 74); (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 12) (1) (16);
   KRange (APC.eadd (EVar 11) (EVar 12)) (2) (17);
   KRange (EVar 66) (1) (16);
   KRange (APC.esub (EVar 12) (EVar 66)) (0) (15);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  75 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (2) (EVar 66)) (8)).
Definition BL7 : CA.blocks := [].
Definition hints7 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CC.CP 833376 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 11); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 10); (APC.eadd (EVar 10) (APC.esub (EVar 33) (APC.eaddz (EVar 66) (-24)))); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (ELit (2147450880)); (EVar 33); (ELit (1)); (APC.eaddz (EVar 66) (-24)); (APC.eadd (EVar 10) (APC.esub (EVar 33) (APC.eaddz (EVar 66) (-24)))); EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (1) (17);
   KRange (APC.esub (EVar 11) (EVar 33)) (1) (20);
   KRange (APC.esub (EVar 33) (EVar 11)) (18446744073709551596) (18446744073709551615);
   KRange (EVar 66) (25) (41);
   KRange (APC.esub (EVar 33) (APC.eaddz (EVar 66) (-24))) (0) (16);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  67 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (8)).
Definition BL8 : CA.blocks := [].
Definition hints8 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CC.CP 833436 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 11); (EVar 32); (ELit (0)); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 10); (APC.eadd (EVar 10) (APC.esub (EVar 33) (APC.eaddz (EVar 66) (-24)))); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (ELit (2147450880)); (EVar 33); (ELit (1)); (APC.eaddz (EVar 66) (-24)); (APC.eadd (EVar 10) (APC.esub (EVar 33) (APC.eaddz (EVar 66) (-24)))); EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (1) (17);
   KRange (APC.esub (EVar 11) (EVar 33)) (1) (20);
   KRange (APC.esub (EVar 33) (EVar 11)) (18446744073709551596) (18446744073709551615);
   KRange (EVar 66) (25) (41);
   KRange (APC.esub (EVar 33) (APC.eaddz (EVar 66) (-24))) (0) (16);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  67 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (6)).
Definition BL9 : CA.blocks := [].
Definition hints9 : list (nat * CC.subst) := [(10%nat, [(66%nat, (APC.esub (EVar 11) (EVar 33)))])].
(* [comment removed for export] *)
Definition t10 : CC.cutpoint := CC.CP 833968 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 11); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (ELit (2147450880)); (APC.esub (EVar 11) (EVar 66)); (APC.esub (ELit (18446744073709551615)) (EVar 10)); (APC.esub (EVar 11) (EVar 66)); (EVar 67); EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (1) (17);
   KRange (APC.esub (EVar 11) (EVar 33)) (1) (20);
   KRange (APC.esub (EVar 33) (EVar 11)) (18446744073709551596) (18446744073709551615);
   KRange (EVar 66) (1) (20);
   KRange (APC.esub (EVar 11) (EVar 66)) (1) (20);
   KRange (APC.esub (APC.esub (EVar 11) (EVar 66)) (EVar 33)) (0) (19);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  73 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (8)).
Definition BL10 : CA.blocks := [].
Definition hints10 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t11 : CC.cutpoint := CC.CP 834012 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 11); (EVar 32); (ELit (0)); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (ELit (2147450880)); (APC.esub (EVar 11) (EVar 66)); (APC.esub (ELit (18446744073709551615)) (EVar 10)); (APC.esub (EVar 11) (EVar 66)); (EVar 67); EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (1) (17);
   KRange (APC.esub (EVar 11) (EVar 33)) (1) (20);
   KRange (APC.esub (EVar 33) (EVar 11)) (18446744073709551596) (18446744073709551615);
   KRange (EVar 66) (1) (20);
   KRange (APC.esub (EVar 11) (EVar 66)) (1) (20);
   KRange (APC.esub (APC.esub (EVar 11) (EVar 66)) (EVar 33)) (0) (19);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  73 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (6)).
Definition BL11 : CA.blocks := [].
Definition hints11 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t12 : CC.cutpoint := CC.CP 833756 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 11); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 10); (APC.eaddz (EVar 33) (2)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (ELit (2147450880)); (APC.esub (ELit (0)) (EVar 66)); EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (0) (3);
   KRange (EVar 33) (1) (3);
   KRange (EVar 66) (1) (3);
   KRange (APC.esub (EVar 33) (EVar 66)) (0) (2);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  67 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (APC.eaddz (EVar 66) (24))) (8)).
Definition BL12 : CA.blocks := [].
Definition hints12 : list (nat * CC.subst) := [(13%nat, [(66%nat, (EVar 11))])].
(* [comment removed for export] *)
Definition t13 : CC.cutpoint := CC.CP 833812 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 66); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 10); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (ELit (2147450880)); (ELit (1)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (0) (3);
   KRange (EVar 66) (1) (21);
   KRange (APC.esub (EVar 11) (EVar 66)) (0) (20);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  67 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (8)).
Definition BL13 : CA.blocks := [].
Definition hints13 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t14 : CC.cutpoint := CC.CP 833872 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 66); (EVar 32); (ELit (0)); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 10); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (ELit (2147450880)); (ELit (1)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (0) (3);
   KRange (EVar 66) (1) (21);
   KRange (APC.esub (EVar 11) (EVar 66)) (0) (20);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  67 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (6)).
Definition BL14 : CA.blocks := [].
Definition hints14 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t15 : CC.cutpoint := CC.CP 834316 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (EVar 66); (ELit (2147450880)); (EVar 33); EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (18) (330);
   KRange (EVar 11) (2) (21);
   KRange (EVar 66) (1) (20);
   KRange (APC.esub (EVar 11) (EVar 66)) (1) (20);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  67 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (8)).
Definition BL15 : CA.blocks := [].
Definition hints15 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t16 : CC.cutpoint := CC.CP 834360 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EVar 32); (ELit (0)); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (EVar 66); (ELit (2147450880)); (EVar 33); EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (18) (330);
   KRange (EVar 11) (2) (21);
   KRange (EVar 66) (1) (20);
   KRange (APC.esub (EVar 11) (EVar 66)) (1) (20);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  67 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (6)).
Definition BL16 : CA.blocks := [].
Definition hints16 : list (nat * CC.subst) := [(19%nat, [(70%nat, (APC.eaddz (EVar 66) (-1))); (69%nat, (APC.eaddz (EVar 11) (3)))])].
(* [comment removed for export] *)
Definition t17 : CC.cutpoint := CC.CP 834316 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (EVar 66); (ELit (2147450880)); (APC.esub (ELit (0)) (EVar 33)); EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (4) (342);
   KRange (EVar 11) (2) (21);
   KRange (EVar 66) (1) (20);
   KRange (APC.esub (EVar 11) (EVar 66)) (1) (20);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  67 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (8)).
Definition BL17 : CA.blocks := [].
Definition hints17 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t18 : CC.cutpoint := CC.CP 834360 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EVar 32); (ELit (0)); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); (EVar 66); (ELit (2147450880)); (APC.esub (ELit (0)) (EVar 33)); EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (4) (342);
   KRange (EVar 11) (2) (21);
   KRange (EVar 66) (1) (20);
   KRange (APC.esub (EVar 11) (EVar 66)) (1) (20);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-104)) 8 (EVar 27)]
  67 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (6)).
Definition BL18 : CA.blocks := [].
Definition hints18 : list (nat * CC.subst) := [(19%nat, [(70%nat, (APC.eaddz (EVar 66) (-1))); (69%nat, (APC.eaddz (EVar 11) (3)))])].
(* [comment removed for export] *)
Definition t19 : CC.cutpoint := CC.CP 837468 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 68); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 71); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (ELit 2147450880)); EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 68) (5) (343);
   KRange (EVar 69) (3) (24);
   KRange (EVar 70) (0) (1048576);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (7094272) (140737479966688);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (4));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (32));
   KRange (EVar 15) (7094272) (140737488355320);
   KAlign (EVar 15) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit (8));
   KRange (EVar 32) (7094272) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KWr (SA (EVar 2) (-4512)) (ELit (4512));
   KRange (EVar 2) (140735332487584) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4512)) (ELit (4512));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 10) (0)) (ELit (32));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4512)) (ELit (4512)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (32)) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-4512)) (ELit (4400));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19)]
  73 [((EVar 2), (-4512), ELit 4512)] [] (APC.eaddz (APC.escale (64) (EVar 70)) (40)).
Definition BL19 : CA.blocks := [].
Definition hints19 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13; t14; t15; t16; t17; t18; t19].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [833300; 833436; 834012; 833872; 834360; 834180; 834256] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
