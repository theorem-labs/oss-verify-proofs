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
Definition ITR : list (Z * nat) := [(858048, 45%nat); (858228, 55%nat); (858844, 56%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [858196].
Definition HDECL : CH.hdecl := CH.HD (8240) (8224) [((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 3); ((EVar 11), (0), ELit 1); ((EAlu Instr.ALU_SRL (EVar 11) (ELit 3)), (2147450880), ELit 1); ((EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)), (2147450880), ELit 3)] [((EVar 10), (0), ELit 24)] [(1459384, 1463120)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880)].
Definition GLO : Z := 1459384.
Definition GHI : Z := 1463120.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 859068 4128 0%nat (fun _ _ => None) (fun _ => [((EAlu Instr.ALU_SRL (EVar 32) (ELit 3)), 2147450880, (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3)))]) (fun _ BL => BL) (fun _ _ _ BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)] ++ [KWord (SA (EAlu Instr.ALU_SRL (APC.eadd (EVar 32) (EVar 33)) (ELit 3)) (2147450880)) 1 (EVar 36)], BLk)) (fun F => F)) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 858448 8192 3%nat (fun _ g => Some (APC.eadd (EVar g) (EVar (g + 2)))) (fun _ => [((EVar 10), 0, ELit 24)]) (fun _ _ => []) (fun _ _ g _ => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)] ++ [KWord (SA (EVar 10) 0) 8 (EVar g); KWord (SA (EVar 10) 16) 8 (APC.eadd (EVar g) (EVar (g + 1))); KRange (EVar g) 17594333495296 140737479966720; KRange (EVar (g + 2)) 0 134217728], [(EVar g, EVar (g + 1))])) (fun _ => [((EVar 2), -8240, ELit 8240); ((EVar 10), 0, ELit 24)])) (fun _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 858048 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 10) (0)) 8 (EVar 32);
   KWord (SA (EVar 10) (8)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (16)) 8 (APC.eadd (EVar 32) (EVar 34));
   KWr (SA (EVar 10) (0)) (ELit (24));
   KRange (EVar 10) (1048576) (140737488354816);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (24));
   KWord (SA (EVar 11) (0)) 1 (EVar 37);
   KRange (EVar 37) (0) (255);
   KRange (EVar 11) (1048576) (140737488355327);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (1));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) 1 (EVar 35);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KWr (SA (EVar 32) (0)) (EVar 34);
   KRange (EVar 32) (17594333495296) (140737479966720);
   KAlign (EVar 32) (16);
   KRange (EVar 33) (0) (134217728);
   KRange (APC.esub (EVar 34) (EVar 33)) (0) (134217728);
   KRange (EVar 34) (1) (134217728);
   KUnk (SA (EVar 2) (-8240)) (ELit (8240));
   KWr (SA (EVar 2) (-8240)) (ELit (8240));
   KRange (EVar 2) (140735332491312) (140737488355328);
   KAlign (EVar 2) (16);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (EVar 2) (-8240)) (ELit (8240)) (SA (EVar 10) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-8240)) (ELit (8240)) (SA (EVar 11) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-8240)) (ELit (8240)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (24)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 11) (0)) (ELit (1)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (24)) (SA (EVar 11) (0)) (ELit (1));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 10) (0)) (ELit 24) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 11) (0)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)) (2147450880)) (ELit 3);
   KRange (EVar 35) (0) (0);
   KRange (EVar 36) (0) (0)]
  48 [((EVar 2), (-8240), ELit 8240); ((EVar 10), (0), ELit 24); ((EVar 32), (0), ((EVar 34)))] [] (ELit (16)).
Definition BL0 : CA.blocks := [((EVar 32), (EVar 34))].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 858048 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 10) (0)) 8 (EVar 32);
   KWord (SA (EVar 10) (8)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (16)) 8 (APC.eadd (EVar 32) (EVar 34));
   KWr (SA (EVar 10) (0)) (ELit (24));
   KRange (EVar 10) (1048576) (140737488354816);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (24));
   KWord (SA (EVar 11) (0)) 1 (EVar 37);
   KRange (EVar 37) (0) (255);
   KRange (EVar 11) (1048576) (140737488355327);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (1));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) 1 (EVar 35);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KWr (SA (EVar 32) (0)) (EVar 34);
   KRange (EVar 32) (17594333495296) (140737479966720);
   KAlign (EVar 32) (16);
   KRange (EVar 33) (0) (134217728);
   KRange (APC.esub (EVar 34) (EVar 33)) (0) (134217728);
   KRange (EVar 34) (1) (134217728);
   KUnk (SA (EVar 2) (-8240)) (ELit (8240));
   KWr (SA (EVar 2) (-8240)) (ELit (8240));
   KRange (EVar 2) (140735332491312) (140737488355328);
   KAlign (EVar 2) (16);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (EVar 2) (-8240)) (ELit (8240)) (SA (EVar 10) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-8240)) (ELit (8240)) (SA (EVar 11) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-8240)) (ELit (8240)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (24)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 11) (0)) (ELit (1)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (24)) (SA (EVar 11) (0)) (ELit (1));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 10) (0)) (ELit 24) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 11) (0)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)) (2147450880)) (ELit 3);
   KRange (EVar 35) (0) (0);
   KRange (EVar 36) (1) (7);
   KRange (APC.esub (EVar 36) (EAlu Instr.ALU_AND (EVar 33) (ELit 7))) (1) (7)]
  48 [((EVar 2), (-8240), ELit 8240); ((EVar 10), (0), ELit 24); ((EVar 32), (0), ((EVar 34)))] [] (ELit (16)).
Definition BL1 : CA.blocks := [((EVar 32), (EVar 34))].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 858048 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 10) (0)) 8 (EVar 32);
   KWord (SA (EVar 10) (8)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (16)) 8 (APC.eadd (EVar 32) (EVar 34));
   KWr (SA (EVar 10) (0)) (ELit (24));
   KRange (EVar 10) (1048576) (140737488354816);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (24));
   KWord (SA (EVar 11) (0)) 1 (EVar 37);
   KRange (EVar 37) (0) (255);
   KRange (EVar 11) (1048576) (140737488355327);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (1));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) 1 (EVar 35);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KWr (SA (EVar 32) (0)) (EVar 34);
   KRange (EVar 32) (17594333495296) (140737479966720);
   KAlign (EVar 32) (16);
   KRange (EVar 33) (0) (134217728);
   KRange (APC.esub (EVar 34) (EVar 33)) (0) (134217728);
   KRange (EVar 34) (1) (134217728);
   KUnk (SA (EVar 2) (-8240)) (ELit (8240));
   KWr (SA (EVar 2) (-8240)) (ELit (8240));
   KRange (EVar 2) (140735332491312) (140737488355328);
   KAlign (EVar 2) (16);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (EVar 2) (-8240)) (ELit (8240)) (SA (EVar 10) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-8240)) (ELit (8240)) (SA (EVar 11) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-8240)) (ELit (8240)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (24)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 11) (0)) (ELit (1)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (24)) (SA (EVar 11) (0)) (ELit (1));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 10) (0)) (ELit 24) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 11) (0)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)) (2147450880)) (ELit 3);
   KRange (EVar 35) (1) (7);
   KRange (APC.esub (EVar 35) (EAlu Instr.ALU_AND (EVar 11) (ELit 7))) (1) (7);
   KRange (EVar 36) (0) (0)]
  48 [((EVar 2), (-8240), ELit 8240); ((EVar 10), (0), ELit 24); ((EVar 32), (0), ((EVar 34)))] [] (ELit (16)).
Definition BL2 : CA.blocks := [((EVar 32), (EVar 34))].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 858048 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 10) (0)) 8 (EVar 32);
   KWord (SA (EVar 10) (8)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (16)) 8 (APC.eadd (EVar 32) (EVar 34));
   KWr (SA (EVar 10) (0)) (ELit (24));
   KRange (EVar 10) (1048576) (140737488354816);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (24));
   KWord (SA (EVar 11) (0)) 1 (EVar 37);
   KRange (EVar 37) (0) (255);
   KRange (EVar 11) (1048576) (140737488355327);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (1));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) 1 (EVar 35);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KWr (SA (EVar 32) (0)) (EVar 34);
   KRange (EVar 32) (17594333495296) (140737479966720);
   KAlign (EVar 32) (16);
   KRange (EVar 33) (0) (134217728);
   KRange (APC.esub (EVar 34) (EVar 33)) (0) (134217728);
   KRange (EVar 34) (1) (134217728);
   KUnk (SA (EVar 2) (-8240)) (ELit (8240));
   KWr (SA (EVar 2) (-8240)) (ELit (8240));
   KRange (EVar 2) (140735332491312) (140737488355328);
   KAlign (EVar 2) (16);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (EVar 2) (-8240)) (ELit (8240)) (SA (EVar 10) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-8240)) (ELit (8240)) (SA (EVar 11) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-8240)) (ELit (8240)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (24)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 11) (0)) (ELit (1)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (24)) (SA (EVar 11) (0)) (ELit (1));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 10) (0)) (ELit 24) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EVar 11) (0)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 3) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-80)) (ELit 3)) (2147450880)) (ELit 3);
   KRange (EVar 35) (1) (7);
   KRange (APC.esub (EVar 35) (EAlu Instr.ALU_AND (EVar 11) (ELit 7))) (1) (7);
   KRange (EVar 36) (1) (7);
   KRange (APC.esub (EVar 36) (EAlu Instr.ALU_AND (EVar 33) (ELit 7))) (1) (7)]
  48 [((EVar 2), (-8240), ELit 8240); ((EVar 10), (0), ELit 24); ((EVar 32), (0), ((EVar 34)))] [] (ELit (16)).
Definition BL3 : CA.blocks := [((EVar 32), (EVar 34))].
Definition hints3 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 300 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
