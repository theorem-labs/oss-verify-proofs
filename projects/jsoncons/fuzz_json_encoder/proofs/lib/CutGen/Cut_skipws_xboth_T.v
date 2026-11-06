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
Definition ITR : list (Z * nat) := [(861724, 173%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [862316; 861980; 862096].
Definition HDECL : CH.hdecl := CH.HD (9952) (8224) [((EVar 32), (0), ((EVar 33))); ((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 34); ((EAlu Instr.ALU_SRL (EVar 36) (ELit 3)), (2147450880), ((EVar 34)))] [((EVar 10), (0), ELit 272)] [(1459384, 1463120)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880)].
Definition GLO : Z := 1459384.
Definition GHI : Z := 1463120.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 893820 4256 0%nat (fun _ _ => Some (ELit 29)) (fun regs => [((EVar 10), 256, ELit 8); ((ELit 0), 2201439137792, ELit 15392894357504)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)); KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (EVar 34)], BLk)) (fun F => F)) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 894716 9792 6%nat (fun _ _ => None) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 40), 0, ELit 16); ((ELit 0), 6946368, ELit 2); ((ELit 0), 7084256, ELit 544)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWr (SA (EVar 10) (0)) (ELit (272)); KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33)); KWord (SA (EVar 10) (200)) 8 (APC.eadd (EVar 32) (APC.eadd (EVar 33) (APC.escale (-1) (EVar g)))); KWord (SA (EVar 10) (208)) 1 (EVar (g + 1)); KRange (EVar (g + 1)) (28) (29); KUnk (SA (EVar 10) (160)) (ELit (24)); KWord (SA (EVar 10) (248)) 8 (EVar (g + 2)); KWord (SA (EVar 10) (264)) 8 (APC.eadd (EVar (g + 2)) (EVar (g + 3))); KRange (EVar (g + 2)) (17594333495296) (140737479966720); KAlign (EVar (g + 2)) (16); KRange (EVar (g + 3)) (1) (1056); KWord (SA (EVar 10) (224)) 8 (APC.eaddz (EVar (g + 5)) (1)); KWord (SA (EVar 10) (240)) 8 (EVar (g + 4)); KRange (EVar (g + 4)) (4096) (140737479966719); KAlign (EVar (g + 4)) (16); KRange (EVar (g + 5)) (264) (134217728); KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)); KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (EVar 34); KRange (EVar g) (0) (16383); KRange (APC.esub (EVar 33) (EVar g)) (0) (16384); KRange (APC.esub (EVar 48) (EVar g)) (1) (16384)], [((EVar (g + 4)), (EVar (g + 5))); ((EVar (g + 2)), (EVar (g + 3)))])) (fun F => F)) (fun _ => []))].
Definition XSTOPS : list Z := [861980; 862096; 861924; 861988; 862104].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 861724 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 10) (7094272) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 40) (7094272) (140737479966704);
   KAlign (EVar 40) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 40) (0)) (ELit (16));
   KWr (SA (EVar 2) (-9952)) (ELit (9952));
   KRange (EVar 2) (140735332493024) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 40) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 40) (0)) (ELit (16));
   KWord (SA (EVar 10) (248)) 8 (EVar 38);
   KWord (SA (EVar 10) (264)) 8 (APC.eadd (EVar 38) (EVar 39));
   KRange (EVar 38) (17594333495296) (140737479966720);
   KAlign (EVar 38) (16);
   KRange (EVar 39) (1) (1056);
   KWord (SA (EVar 10) (224)) 8 (APC.eaddz (EVar 42) (1));
   KWord (SA (EVar 10) (240)) 8 (EVar 41);
   KRange (EVar 41) (4096) (140737479966719);
   KAlign (EVar 41) (16);
   KRange (EVar 42) (264) (134217728);
   KWord (SA (EVar 10) (192)) 8 (EVar 37);
   KWord (SA (EVar 10) (200)) 8 (EVar 37);
   KRange (EVar 37) (0) (140737488355328);
   KWord (SA (EVar 10) (208)) 1 (EVar 35);
   KRange (EVar 35) (0) (255);
   KUnk (SA (EVar 2) (-9952)) (ELit (9952));
   KUnk (SA (EVar 10) (160)) (ELit (24))]
  48 [((EVar 2), (-9952), ELit 9952); ((EVar 10), (160), ELit 24); ((EVar 10), (200), ELit 8); ((EVar 10), (208), ELit 1)] [] (ELit (1073741824)).
Definition BL0 : CA.blocks := [((EVar 41), (EVar 42)); ((EVar 38), (EVar 39))].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 861724 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 10) (7094272) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 40) (7094272) (140737479966704);
   KAlign (EVar 40) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 40) (0)) (ELit (16));
   KWr (SA (EVar 2) (-9952)) (ELit (9952));
   KRange (EVar 2) (140735332493024) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 40) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 40) (0)) (ELit (16));
   KRange (EVar 32) (4096) (140737479966719);
   KRange (EVar 33) (0) (16384);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (ELit 0) 6946368) (ELit 2) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (ELit 0) 7084256) (ELit 544) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (EVar 34);
   KRange (EVar 34) (2048) (2048);
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16384);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (0) (16384);
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 40) (0)) (ELit (16)) (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 10) (248)) 8 (EVar 38);
   KWord (SA (EVar 10) (264)) 8 (APC.eadd (EVar 38) (EVar 39));
   KRange (EVar 38) (17594333495296) (140737479966720);
   KAlign (EVar 38) (16);
   KRange (EVar 39) (1) (1056);
   KWord (SA (EVar 10) (224)) 8 (APC.eaddz (EVar 42) (1));
   KWord (SA (EVar 10) (240)) 8 (EVar 41);
   KRange (EVar 41) (4096) (140737479966719);
   KAlign (EVar 41) (16);
   KRange (EVar 42) (264) (134217728);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (EVar 32);
   KWord (SA (EVar 10) (208)) 1 (EVar 35);
   KRange (EVar 35) (28) (29);
   KUnk (SA (EVar 2) (-9952)) (ELit (9952));
   KUnk (SA (EVar 10) (160)) (ELit (24))]
  48 [((EVar 2), (-9952), ELit 9952); ((EVar 10), (160), ELit 24); ((EVar 10), (200), ELit 8); ((EVar 10), (208), ELit 1)] [] (ELit (1073741824)).
Definition BL1 : CA.blocks := [((EVar 41), (EVar 42)); ((EVar 38), (EVar 39))].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 861924 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-128)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 10); (APC.eaddz (EVar 10) (200)); (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48)); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (APC.eaddz (EVar 10) (208)); (APC.eaddz (EVar 10) (168)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (168)) (ELit 3)) (ELit (2147450880))); (APC.eaddz (EVar 10) (160)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (208)) (ELit 3)) (ELit (2147450880))); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (200)) (ELit 3)) (ELit (2147450880))); (APC.eadd (EVar 32) (EVar 33)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (176)) (ELit 3)) (ELit (2147450880))); (ELit (4294977024)); (ELit (2147450880)); (EVar 61); (EVar 62); (EVar 63); (EVar 64)]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 10) (7094272) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 40) (7094272) (140737479966704);
   KAlign (EVar 40) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 40) (0)) (ELit (16));
   KWr (SA (EVar 2) (-9952)) (ELit (9952));
   KRange (EVar 2) (140735332493024) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 40) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 40) (0)) (ELit (16));
   KRange (EVar 32) (4096) (140737479966719);
   KRange (EVar 33) (0) (16384);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (ELit 0) 6946368) (ELit 2) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (ELit 0) 7084256) (ELit 544) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (EVar 34);
   KRange (EVar 34) (2048) (2048);
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16384);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (0) (16384);
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 40) (0)) (ELit (16)) (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 10) (248)) 8 (EVar 65);
   KWord (SA (EVar 10) (264)) 8 (APC.eadd (EVar 65) (EVar 66));
   KRange (EVar 65) (17594333495296) (140737479966720);
   KAlign (EVar 65) (16);
   KRange (EVar 66) (1) (1056);
   KWord (SA (EVar 10) (224)) 8 (APC.eaddz (EVar 68) (1));
   KWord (SA (EVar 10) (240)) 8 (EVar 67);
   KRange (EVar 67) (4096) (140737479966719);
   KAlign (EVar 67) (16);
   KRange (EVar 68) (264) (134217728);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48));
   KWord (SA (EVar 10) (208)) 1 (EVar 49);
   KRange (EVar 49) (28) (29);
   KUnk (SA (EVar 2) (-9952)) (ELit (9824));
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
   KWord (SA (EVar 2) (-128)) 8 (APC.eaddz (EVar 10) (176));
   KWord (SA (EVar 2) (-120)) 8 (ELit (0));
   KWord (SA (EVar 2) (-112)) 8 (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (160)) (ELit 3)) (ELit (2147450880)));
   KUnk (SA (EVar 10) (160)) (ELit (24));
   KRange (EVar 48) (1) (16384);
   KRange (APC.esub (EVar 33) (EVar 48)) (0) (16383)]
  69 [((EVar 2), (-9952), ELit 9952); ((EVar 10), (160), ELit 24); ((EVar 10), (200), ELit 8); ((EVar 10), (208), ELit 1)] [] (APC.eaddz (APC.escale (64) (EVar 48)) (40)).
Definition BL2 : CA.blocks := [((EVar 67), (EVar 68)); ((EVar 65), (EVar 66))].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 861924 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-128)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 10); (APC.eaddz (EVar 10) (200)); (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48)); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (APC.eaddz (EVar 10) (208)); (APC.eaddz (EVar 10) (168)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (168)) (ELit 3)) (ELit (2147450880))); (APC.eaddz (EVar 10) (160)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (208)) (ELit 3)) (ELit (2147450880))); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (200)) (ELit 3)) (ELit (2147450880))); (APC.eadd (EVar 32) (EVar 33)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (176)) (ELit 3)) (ELit (2147450880))); (ELit (4294977024)); (ELit (2147450880)); (EVar 61); (EVar 62); (EVar 63); (EVar 64)]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 10) (7094272) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 40) (7094272) (140737479966704);
   KAlign (EVar 40) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 40) (0)) (ELit (16));
   KWr (SA (EVar 2) (-9952)) (ELit (9952));
   KRange (EVar 2) (140735332493024) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 40) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 40) (0)) (ELit (16));
   KRange (EVar 32) (4096) (140737479966719);
   KRange (EVar 33) (0) (16384);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (ELit 0) 6946368) (ELit 2) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (ELit 0) 7084256) (ELit 544) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (EVar 34);
   KRange (EVar 34) (2048) (2048);
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16384);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (0) (16384);
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 40) (0)) (ELit (16)) (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 10) (248)) 8 (EVar 65);
   KWord (SA (EVar 10) (264)) 8 (APC.eadd (EVar 65) (EVar 66));
   KRange (EVar 65) (17594333495296) (140737479966720);
   KAlign (EVar 65) (16);
   KRange (EVar 66) (1) (1056);
   KWord (SA (EVar 10) (224)) 8 (APC.eaddz (EVar 68) (1));
   KWord (SA (EVar 10) (240)) 8 (EVar 67);
   KRange (EVar 67) (4096) (140737479966719);
   KAlign (EVar 67) (16);
   KRange (EVar 68) (264) (134217728);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48));
   KWord (SA (EVar 10) (208)) 1 (ELit (29));
   KUnk (SA (EVar 2) (-9952)) (ELit (9824));
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
   KWord (SA (EVar 2) (-128)) 8 (APC.eaddz (EVar 10) (176));
   KWord (SA (EVar 2) (-120)) 8 (ELit (0));
   KWord (SA (EVar 2) (-112)) 8 (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (160)) (ELit 3)) (ELit (2147450880)));
   KUnk (SA (EVar 10) (160)) (ELit (24));
   KRange (EVar 48) (1) (16384);
   KRange (APC.esub (EVar 33) (EVar 48)) (0) (16383)]
  69 [((EVar 2), (-9952), ELit 9952); ((EVar 10), (160), ELit 24); ((EVar 10), (200), ELit 8); ((EVar 10), (208), ELit 1)] [] (APC.eaddz (APC.escale (64) (EVar 48)) (24)).
Definition BL3 : CA.blocks := [((EVar 67), (EVar 68)); ((EVar 65), (EVar 66))].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 861988 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-128)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 10); (APC.eaddz (EVar 10) (200)); (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48)); (ELit (0)); (ELit (28)); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (APC.eaddz (EVar 10) (208)); (APC.eaddz (EVar 10) (168)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (168)) (ELit 3)) (ELit (2147450880))); (APC.eaddz (EVar 10) (160)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (208)) (ELit 3)) (ELit (2147450880))); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (200)) (ELit 3)) (ELit (2147450880))); (APC.eadd (EVar 32) (EVar 33)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (176)) (ELit 3)) (ELit (2147450880))); (ELit (4294977024)); (ELit (2147450880)); (EVar 61); (EVar 62); (EVar 63); (EVar 64)]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 10) (7094272) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 40) (7094272) (140737479966704);
   KAlign (EVar 40) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 40) (0)) (ELit (16));
   KWr (SA (EVar 2) (-9952)) (ELit (9952));
   KRange (EVar 2) (140735332493024) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 40) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 40) (0)) (ELit (16));
   KRange (EVar 32) (4096) (140737479966719);
   KRange (EVar 33) (0) (16384);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (ELit 0) 6946368) (ELit 2) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (ELit 0) 7084256) (ELit 544) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (EVar 34);
   KRange (EVar 34) (2048) (2048);
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16384);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (0) (16384);
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 40) (0)) (ELit (16)) (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 10) (248)) 8 (EVar 65);
   KWord (SA (EVar 10) (264)) 8 (APC.eadd (EVar 65) (EVar 66));
   KRange (EVar 65) (17594333495296) (140737479966720);
   KAlign (EVar 65) (16);
   KRange (EVar 66) (1) (1056);
   KWord (SA (EVar 10) (224)) 8 (APC.eaddz (EVar 68) (1));
   KWord (SA (EVar 10) (240)) 8 (EVar 67);
   KRange (EVar 67) (4096) (140737479966719);
   KAlign (EVar 67) (16);
   KRange (EVar 68) (264) (134217728);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48));
   KWord (SA (EVar 10) (208)) 1 (EVar 49);
   KRange (EVar 49) (28) (29);
   KRange (EVar 49) (28) (28);
   KUnk (SA (EVar 2) (-9952)) (ELit (9824));
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
   KWord (SA (EVar 2) (-128)) 8 (APC.eaddz (EVar 10) (176));
   KWord (SA (EVar 2) (-120)) 8 (ELit (0));
   KWord (SA (EVar 2) (-112)) 8 (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (160)) (ELit 3)) (ELit (2147450880)));
   KWord (SA (EVar 10) (160)) 8 (APC.eaddz (EVar 69) (1));
   KUnk (SA (EVar 10) (168)) (ELit (16));
   KRange (EVar 48) (1) (16384);
   KRange (APC.esub (EVar 33) (EVar 48)) (0) (16383)]
  70 [((EVar 2), (-9952), ELit 9952); ((EVar 10), (160), ELit 24); ((EVar 10), (200), ELit 8); ((EVar 10), (208), ELit 1)] [] (APC.eaddz (APC.escale (64) (EVar 48)) (32)).
Definition BL4 : CA.blocks := [((EVar 67), (EVar 68)); ((EVar 65), (EVar 66))].
Definition hints4 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 862104 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-128)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 10); (APC.eaddz (EVar 10) (200)); (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48)); (ELit (0)); (ELit (28)); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (APC.eaddz (EVar 10) (208)); (APC.eaddz (EVar 10) (168)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (168)) (ELit 3)) (ELit (2147450880))); (APC.eaddz (EVar 10) (160)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (208)) (ELit 3)) (ELit (2147450880))); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (200)) (ELit 3)) (ELit (2147450880))); (APC.eadd (EVar 32) (EVar 33)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (176)) (ELit 3)) (ELit (2147450880))); (ELit (4294977024)); (ELit (2147450880)); (EVar 61); (EVar 62); (EVar 63); (EVar 64)]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 10) (7094272) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 40) (7094272) (140737479966704);
   KAlign (EVar 40) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 40) (0)) (ELit (16));
   KWr (SA (EVar 2) (-9952)) (ELit (9952));
   KRange (EVar 2) (140735332493024) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 40) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 40) (0)) (ELit (16));
   KRange (EVar 32) (4096) (140737479966719);
   KRange (EVar 33) (0) (16384);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (ELit 0) 6946368) (ELit 2) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (ELit 0) 7084256) (ELit 544) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (EVar 34);
   KRange (EVar 34) (2048) (2048);
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16384);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (0) (16384);
   KDisj (SA (EVar 2) (-9952)) (ELit (9952)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 40) (0)) (ELit (16)) (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 10) (248)) 8 (EVar 65);
   KWord (SA (EVar 10) (264)) 8 (APC.eadd (EVar 65) (EVar 66));
   KRange (EVar 65) (17594333495296) (140737479966720);
   KAlign (EVar 65) (16);
   KRange (EVar 66) (1) (1056);
   KWord (SA (EVar 10) (224)) 8 (APC.eaddz (EVar 68) (1));
   KWord (SA (EVar 10) (240)) 8 (EVar 67);
   KRange (EVar 67) (4096) (140737479966719);
   KAlign (EVar 67) (16);
   KRange (EVar 68) (264) (134217728);
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48));
   KWord (SA (EVar 10) (208)) 1 (EVar 49);
   KRange (EVar 49) (28) (29);
   KRange (EVar 49) (29) (29);
   KUnk (SA (EVar 2) (-9952)) (ELit (9824));
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
   KWord (SA (EVar 2) (-128)) 8 (APC.eaddz (EVar 10) (176));
   KWord (SA (EVar 2) (-120)) 8 (ELit (0));
   KWord (SA (EVar 2) (-112)) 8 (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (160)) (ELit 3)) (ELit (2147450880)));
   KUnk (SA (EVar 10) (160)) (ELit (24));
   KRange (EVar 48) (1) (16384);
   KRange (APC.esub (EVar 33) (EVar 48)) (0) (16383)]
  69 [((EVar 2), (-9952), ELit 9952); ((EVar 10), (160), ELit 24); ((EVar 10), (200), ELit 8); ((EVar 10), (208), ELit 1)] [] (APC.eaddz (APC.escale (64) (EVar 48)) (16)).
Definition BL5 : CA.blocks := [((EVar 67), (EVar 68)); ((EVar 65), (EVar 66))].
Definition hints5 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [861988; 862104] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 800 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
