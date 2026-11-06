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
Definition ITR : list (Z * nat) := [(894716, 187%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [895252; 894932; 895096].
Definition HDECL : CH.hdecl := CH.HD (9792) (8224) [((EVar 32), (0), ((EVar 33))); ((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 34); ((EAlu Instr.ALU_SRL (EVar 36) (ELit 3)), (2147450880), ELit 2048)] [((EVar 10), (0), ELit 272)] [(1459384, 1463120)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880)].
Definition GLO : Z := 1459384.
Definition GHI : Z := 1463120.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 858048 8240 2%nat (fun _ _ => None) (fun regs => [((EVar 10), 248, ELit 24)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)], [(EVar g, EVar (g + 1))])) (fun F => F)) (fun _ => []))].
Definition XSTOPS : list Z := [894932; 895096; 894920; 894940; 895104].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 894716 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (APC.eaddz (EVar 10) (200)); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 10) (144)) 4 (EVar 34);
   KRange (EVar 34) (0) (1024);
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (EVar 32);
   KWord (SA (EVar 10) (208)) 1 (EVar 35);
   KRange (EVar 35) (0) (255);
   KRange (EVar 10) (7094272) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 33) (1) (16384);
   KRange (EVar 32) (4096) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit (2048));
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16383);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (1) (16384);
   KRange (EVar 38) (17594333495296) (140737479966720);
   KAlign (EVar 38) (16);
   KRange (EVar 39) (1) (1056);
   KWr (SA (EVar 2) (-9792)) (ELit (9792));
   KRange (EVar 2) (140735332492864) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KUnk (SA (EVar 2) (-9792)) (ELit (9792));
   KUnk (SA (EVar 10) (160)) (ELit (24))]
  48 [((EVar 2), (-9792), ELit 9792); ((EVar 10), (160), ELit 24); ((EVar 10), (200), ELit 8); ((EVar 10), (208), ELit 1)] [] (ELit (1073741824)).
Definition BL0 : CA.blocks := [((EVar 38), (EVar 39))].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 894920 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-96)); EVar 3; EVar 4; (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (160)) (ELit 3)) (ELit (2147450880))); (EVar 49); (ELit (12)); (APC.eaddz (EVar 10) (200)); (EVar 51); EVar 10; (APC.eaddz (EVar 10) (168)); (APC.eaddz (EVar 10) (160)); (APC.eaddz (EVar 10) (176)); (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48)); (ELit (2147450880)); (APC.eadd (EVar 32) (EVar 33)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (168)) (ELit 3)) (ELit (2147450880))); (ELit (13)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (200)) (ELit 3)) (ELit (2147450880))); (ELit (32)); (EVar 50); (EVar 52); (EVar 53); (EVar 54); EVar 25; EVar 26; EVar 27; (ELit (9)); (ELit (10)); (ELit (18446744073709551615)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (176)) (ELit 3)) (ELit (2147450880)))]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 10) (144)) 4 (EVar 34);
   KRange (EVar 34) (0) (1024);
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (EVar 32);
   KWord (SA (EVar 10) (208)) 1 (EVar 35);
   KRange (EVar 35) (0) (255);
   KRange (EVar 10) (7094272) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 33) (1) (16384);
   KRange (EVar 32) (4096) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit (2048));
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16383);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (1) (16384);
   KRange (EVar 38) (17594333495296) (140737479966720);
   KAlign (EVar 38) (16);
   KRange (EVar 39) (1) (1056);
   KWr (SA (EVar 2) (-9792)) (ELit (9792));
   KRange (EVar 2) (140735332492864) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KUnk (SA (EVar 2) (-9792)) (ELit (9712));
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
   KUnk (SA (EVar 10) (160)) (ELit (24));
   KRange (EVar 48) (1) (16384);
   KRange (APC.esub (EVar 33) (EVar 48)) (0) (16383);
   KRange (APC.eadd (EVar 32) (EVar 33)) (4097) (140737479966720)]
  55 [((EVar 2), (-9792), ELit 9792); ((EVar 10), (160), ELit 24); ((EVar 10), (200), ELit 8); ((EVar 10), (208), ELit 1)] [] (APC.eaddz (APC.escale (64) (EVar 48)) (8)).
Definition BL1 : CA.blocks := [((EVar 38), (EVar 39))].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 894940 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-96)); EVar 3; EVar 4; (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (160)) (ELit 3)) (ELit (2147450880))); (EVar 49); (ELit (12)); (APC.eaddz (EVar 10) (200)); (ELit (0)); EVar 10; (APC.eaddz (EVar 10) (168)); (APC.eaddz (EVar 10) (160)); (APC.eaddz (EVar 10) (176)); (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48)); (ELit (2147450880)); (APC.eadd (EVar 32) (EVar 33)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (168)) (ELit 3)) (ELit (2147450880))); (ELit (13)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (200)) (ELit 3)) (ELit (2147450880))); (ELit (32)); (EVar 50); (EVar 52); (EVar 53); (EVar 54); EVar 25; EVar 26; EVar 27; (ELit (9)); (ELit (10)); (ELit (18446744073709551615)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (176)) (ELit 3)) (ELit (2147450880)))]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 10) (144)) 4 (EVar 34);
   KRange (EVar 34) (0) (1024);
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (EVar 32);
   KWord (SA (EVar 10) (208)) 1 (EVar 35);
   KRange (EVar 35) (0) (255);
   KRange (EVar 10) (7094272) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 33) (1) (16384);
   KRange (EVar 32) (4096) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit (2048));
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16383);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (1) (16384);
   KRange (EVar 38) (17594333495296) (140737479966720);
   KAlign (EVar 38) (16);
   KRange (EVar 39) (1) (1056);
   KWr (SA (EVar 2) (-9792)) (ELit (9792));
   KRange (EVar 2) (140735332492864) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KUnk (SA (EVar 2) (-9792)) (ELit (9712));
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
   KUnk (SA (EVar 10) (160)) (ELit (24));
   KRange (EVar 48) (1) (16384);
   KRange (APC.esub (EVar 33) (EVar 48)) (0) (16383);
   KRange (APC.eadd (EVar 32) (EVar 33)) (4097) (140737479966720)]
  55 [((EVar 2), (-9792), ELit 9792); ((EVar 10), (160), ELit 24); ((EVar 10), (200), ELit 8); ((EVar 10), (208), ELit 1)] [] (APC.eaddz (APC.escale (64) (EVar 48)) (6)).
Definition BL2 : CA.blocks := [((EVar 38), (EVar 39))].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 895104 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-96)); EVar 3; EVar 4; (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (160)) (ELit 3)) (ELit (2147450880))); (APC.eaddz (EVar 49) (1)); (ELit (12)); (APC.eaddz (EVar 10) (200)); (APC.eaddz (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48)) (1)); EVar 10; (APC.eaddz (EVar 10) (168)); (APC.eaddz (EVar 10) (160)); (APC.eaddz (EVar 10) (176)); (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48)); (ELit (2147450880)); (APC.eadd (EVar 32) (EVar 33)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (168)) (ELit 3)) (ELit (2147450880))); (ELit (13)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (200)) (ELit 3)) (ELit (2147450880))); (ELit (32)); (EVar 50); (APC.eaddz (EVar 50) (1)); (ELit (0)); (EVar 54); EVar 25; EVar 26; EVar 27; (ELit (9)); (ELit (10)); (ELit (18446744073709551615)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (176)) (ELit 3)) (ELit (2147450880)))]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 10) (144)) 4 (EVar 34);
   KRange (EVar 34) (0) (1024);
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (EVar 32);
   KWord (SA (EVar 10) (208)) 1 (EVar 35);
   KRange (EVar 35) (0) (255);
   KRange (EVar 10) (7094272) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 33) (1) (16384);
   KRange (EVar 32) (4096) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit (2048));
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16383);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (1) (16384);
   KRange (EVar 38) (17594333495296) (140737479966720);
   KAlign (EVar 38) (16);
   KRange (EVar 39) (1) (1056);
   KWr (SA (EVar 2) (-9792)) (ELit (9792));
   KRange (EVar 2) (140735332492864) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KUnk (SA (EVar 2) (-9792)) (ELit (9712));
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
   KWord (SA (EVar 10) (160)) 8 (APC.eaddz (EVar 49) (1));
   KWord (SA (EVar 10) (168)) 8 (APC.eaddz (EVar 50) (1));
   KUnk (SA (EVar 10) (176)) (ELit (8));
   KRange (EVar 48) (2) (16384);
   KRange (APC.esub (EVar 33) (EVar 48)) (0) (16383);
   KRange (APC.eadd (EVar 32) (EVar 33)) (4097) (140737479966720)]
  55 [((EVar 2), (-9792), ELit 9792); ((EVar 10), (160), ELit 24); ((EVar 10), (200), ELit 8); ((EVar 10), (208), ELit 1)] [] (APC.eaddz (APC.escale (64) (EVar 48)) (4)).
Definition BL3 : CA.blocks := [((EVar 38), (EVar 39))].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 895112 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-96)); EVar 3; EVar 4; (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (160)) (ELit 3)) (ELit (2147450880))); (APC.eaddz (EVar 49) (1)); (ELit (12)); (APC.eaddz (EVar 10) (200)); (APC.eaddz (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48)) (1)); EVar 10; (APC.eaddz (EVar 10) (168)); (APC.eaddz (EVar 10) (160)); (APC.eaddz (EVar 10) (176)); (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 48)); (ELit (2147450880)); (APC.eadd (EVar 32) (EVar 33)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (168)) (ELit 3)) (ELit (2147450880))); (ELit (13)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (200)) (ELit 3)) (ELit (2147450880))); (ELit (32)); (EVar 50); (APC.eaddz (EVar 50) (1)); (EVar 55); (EVar 54); EVar 25; EVar 26; EVar 27; (ELit (9)); (ELit (10)); (ELit (18446744073709551615)); (APC.eadd (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (176)) (ELit 3)) (ELit (2147450880)))]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 10) (144)) 4 (EVar 34);
   KRange (EVar 34) (0) (1024);
   KWord (SA (EVar 10) (192)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (200)) 8 (EVar 32);
   KWord (SA (EVar 10) (208)) 1 (EVar 35);
   KRange (EVar 35) (0) (255);
   KRange (EVar 10) (7094272) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KBlob (SA (EVar 32) (0)) (EVar 33) 0;
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 33) (1) (16384);
   KRange (EVar 32) (4096) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 36) (4096) (140737479950336);
   KAlign (EVar 36) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit (2048));
   KRange (APC.esub (EVar 32) (EVar 36)) (0) (16383);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 32) (EVar 36)) (EVar 33)) (ELit (0))) (1) (16384);
   KRange (EVar 38) (17594333495296) (140737479966720);
   KAlign (EVar 38) (16);
   KRange (EVar 39) (1) (1056);
   KWr (SA (EVar 2) (-9792)) (ELit (9792));
   KRange (EVar 2) (140735332492864) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9792)) (ELit (9792)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 33);
   KUnk (SA (EVar 2) (-9792)) (ELit (9712));
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
   KWord (SA (EVar 10) (160)) 8 (APC.eaddz (EVar 49) (1));
   KWord (SA (EVar 10) (168)) 8 (APC.eaddz (EVar 50) (1));
   KUnk (SA (EVar 10) (176)) (ELit (8));
   KRange (EVar 48) (2) (16384);
   KRange (APC.esub (EVar 33) (EVar 48)) (0) (16383);
   KRange (EVar 55) (10) (10);
   KRange (APC.eadd (EVar 32) (EVar 33)) (4097) (140737479966720)]
  56 [((EVar 2), (-9792), ELit 9792); ((EVar 10), (160), ELit 24); ((EVar 10), (200), ELit 8); ((EVar 10), (208), ELit 1)] [] (APC.eaddz (APC.escale (64) (EVar 48)) (3)).
Definition BL4 : CA.blocks := [((EVar 38), (EVar 39))].
Definition hints4 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [894940; 895104] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
