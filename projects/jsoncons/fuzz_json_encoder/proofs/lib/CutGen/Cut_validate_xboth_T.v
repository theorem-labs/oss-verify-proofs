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
Definition ITR : list (Z * nat) := [(924200, 273%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 40.
Definition ENDS : list Z := [925196; 924396; 924428; 924460; 924492; 924524; 924556; 924588; 924620; 924664; 924692; 924776; 924812; 924844].
Definition HDECL : CH.hdecl := CH.HD (128) (8224) [((EVar 10), (0), ((EVar 11))); ((EAlu Instr.ALU_SRL (EVar 32) (ELit 3)), (2147450880), ((EVar 33)))] [] [(1459384, 1463120); (151552, 152064)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880)].
Definition GLO : Z := 1459384.
Definition GHI : Z := 1463120.
Definition CSUMS : list CA.callsum := [].
Definition XSTOPS : list Z := [924396; 924428; 924460; 924492; 924524; 924556; 924588; 924620; 924664; 924692; 924776; 924812; 924844; 924376; 924652; 924400; 924432; 924464; 924496; 924528; 924560; 924592; 924624; 924668; 924696; 924780; 924816; 924848].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 924200 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
   KUnk (SA (EVar 2) (-128)) (ELit (128));
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  40 [((EVar 2), (-128), ELit 128)] [] (ELit (1099511627776)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 924376 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (EVar 41); (EVar 42); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 45); (EVar 46); (EVar 47); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (1) (134217728);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (40)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (40)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 924400 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (ELit (0)); (EVar 42); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 45); (EVar 46); (EVar 47); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (8) (134217728);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (38)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (38)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 924432 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (1)); (ELit (0)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 45); (EVar 46); (EVar 47); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (8) (134217728);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (36)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (36)).
Definition BL3 : CA.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 924464 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (2)); (ELit (0)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 45); (EVar 46); (EVar 47); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (8) (134217728);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (34)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (34)).
Definition BL4 : CA.blocks := [].
Definition hints4 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 924496 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (3)); (ELit (0)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 45); (EVar 46); (EVar 47); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (8) (134217728);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (32)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (32)).
Definition BL5 : CA.blocks := [].
Definition hints5 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CC.CP 924528 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (4)); (ELit (0)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 45); (EVar 46); (EVar 47); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (8) (134217728);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (30)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (30)).
Definition BL6 : CA.blocks := [].
Definition hints6 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CC.CP 924560 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (5)); (ELit (0)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 45); (EVar 46); (EVar 47); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (8) (134217728);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (28)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (28)).
Definition BL7 : CA.blocks := [].
Definition hints7 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CC.CP 924592 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (6)); (ELit (0)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 45); (EVar 46); (EVar 47); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (8) (134217728);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (26)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (26)).
Definition BL8 : CA.blocks := [].
Definition hints8 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CC.CP 924624 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (7)); (ELit (0)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 45); (EVar 46); (EVar 47); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (8) (134217728);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (24)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (24)).
Definition BL9 : CA.blocks := [].
Definition hints9 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t10 : CC.cutpoint := CC.CP 924652 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (EVar 41); (EVar 42); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 45); (EVar 46); (EVar 47); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (1) (134217728);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (30)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (30)).
Definition BL10 : CA.blocks := [].
Definition hints10 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t11 : CC.cutpoint := CC.CP 924668 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (ELit (0)); (EVar 42); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 45); (EVar 46); (EVar 47); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (1) (134217728);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (28)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (28)).
Definition BL11 : CA.blocks := [].
Definition hints11 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t12 : CC.cutpoint := CC.CP 924696 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (APC.eaddz (EVar 44) (151798)); (ELit (0)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 44); (EVar 46); (EVar 47); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (1) (134217728);
   KRange (EVar 44) (0) (255);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (22)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (22)).
Definition BL12 : CA.blocks := [].
Definition hints12 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t13 : CC.cutpoint := CC.CP 924780 [EVar 0; (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (4)); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (ELit (0)); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (3)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 44); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (4)); (ELit (3)); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (4) (134217728);
   KRange (EVar 44) (0) (255);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (20)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (20)).
Definition BL13 : CA.blocks := [].
Definition hints13 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t14 : CC.cutpoint := CC.CP 924816 [EVar 0; (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (3)); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (ELit (0)); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (2)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 44); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (4)); (ELit (3)); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (4) (134217728);
   KRange (EVar 44) (0) (255);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (18)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (18)).
Definition BL14 : CA.blocks := [].
Definition hints14 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t15 : CC.cutpoint := CC.CP 924848 [EVar 0; (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (3)); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (ELit (0)); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (1)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 44); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (4)); (ELit (3)); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (4) (134217728);
   KRange (EVar 44) (0) (255);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (16)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (16)).
Definition BL15 : CA.blocks := [].
Definition hints15 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t16 : CC.cutpoint := CC.CP 924816 [EVar 0; (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (3)); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (ELit (0)); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (2)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 44); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (3)); (ELit (2)); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (3) (134217728);
   KRange (EVar 44) (0) (255);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (20)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (20)).
Definition BL16 : CA.blocks := [].
Definition hints16 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t17 : CC.cutpoint := CC.CP 924848 [EVar 0; (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (3)); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (ELit (0)); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (1)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 44); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (3)); (ELit (2)); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (3) (134217728);
   KRange (EVar 44) (0) (255);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (18)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (18)).
Definition BL17 : CA.blocks := [].
Definition hints17 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t18 : CC.cutpoint := CC.CP 924848 [EVar 0; (EVar 43); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (ELit (245)); (ELit (2)); (ELit (18446744073709551551)); (ELit (159)); (ELit (240)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))); (ELit (0)); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (1)); (APC.eadd (EVar 10) (EVar 11)); (ELit (8)); (ELit (18446744073709551615)); (ELit (1)); (ELit (18446744073709551554)); (ELit (151798)); (ELit (18446744073709399817)); (ELit (2147450880)); (ELit (144)); (ELit (244)); (ELit (143)); (ELit (3)); (EVar 44); (APC.eaddz (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 40))) (2)); (ELit (1)); (ELit (239)); (ELit (224)); (ELit (160)); (ELit (237))]
  [KRange (EVar 40) (2) (134217728);
   KRange (EVar 44) (0) (255);
   KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (151552) (152064);
   KZero (SA (ELit 0) 2147469854) (ELit 33);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KWr (SA (EVar 2) (-128)) (ELit (128));
   KRange (EVar 2) (140735332483200) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-128)) (ELit (128)) (SA (EVar 10) (0)) (EVar 11);
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
   KUnk (SA (EVar 2) (-128)) (ELit (24));
   KRange (APC.esub (EVar 11) (EVar 40)) (0) (134217728);
   KRange (APC.eaddz (APC.escale (64) (EVar 40)) (20)) (0) (4611686018427387904);
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737479966720)]
  48 [((EVar 2), (-128), ELit 128)] [] (APC.eaddz (APC.escale (64) (EVar 40)) (20)).
Definition BL18 : CA.blocks := [].
Definition hints18 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13; t14; t15; t16; t17; t18].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [924404; 924436; 924468; 924500; 924532; 924564; 924596; 924628; 924672; 924700; 924784; 924820; 924852] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 800 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
