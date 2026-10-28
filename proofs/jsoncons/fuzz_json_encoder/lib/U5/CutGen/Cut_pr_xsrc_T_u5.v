(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(280656, 235%nat); (283004, 113%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [281348].
Definition HDECL : CH.hdecl := CH.HD (8592) (8224) [((EVar 10), (0), ((EVar 11))); ((EVar 15), (0), ELit 8)] [((EVar 32), (0), ELit 24)] [].
Definition CSUMS : list CA.callsum := [CAX.xs_cs (ESU.sink_xsum 436872 8496)].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 280656 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (EVar 12); (ELit (18446744073709551612)); (ELit (17)); (EVar 15); EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 12) (0) (16);
   KRange (APC.eadd (EVar 11) (EVar 12)) (1) (17);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8592))]
  48 [((EVar 2), (-8592), ELit 8592)] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [(5%nat, [(66%nat, (EVar 11))])].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 280656 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (APC.esub (EVar 33) (EVar 11)); (ELit (18446744073709551612)); (ELit (17)); (EVar 15); EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 33) (1) (17);
   KRange (APC.esub (EVar 11) (EVar 33)) (1) (20);
   KRange (APC.esub (EVar 33) (EVar 11)) (18446744073709551596) (18446744073709551615);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8592))]
  48 [((EVar 2), (-8592), ELit 8592)] [] (ELit (1048576)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [(7%nat, [(66%nat, (EVar 33))])].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 280656 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (APC.esub (ELit (0)) (APC.eadd (EVar 33) (EVar 11))); (ELit (18446744073709551612)); (ELit (17)); (EVar 15); EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 33) (0) (3);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8592))]
  48 [((EVar 2), (-8592), ELit 8592)] [] (ELit (1048576)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [(9%nat, [(66%nat, (EVar 33))]); (10%nat, [(66%nat, (EVar 11))])].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 280656 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (APC.esub (EVar 33) (EVar 11)); (ELit (18446744073709551612)); (ELit (17)); (EVar 15); EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 33) (18) (330);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8592))]
  48 [((EVar 2), (-8592), ELit 8592)] [] (ELit (1048576)).
Definition BL3 : CA.blocks := [].
Definition hints3 : list (nat * CC.subst) := [(11%nat, [(66%nat, (APC.eaddz (EVar 11) (-1)))]); (13%nat, [(70%nat, (ELit (8192))); (69%nat, (ELit (3)))])].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 280656 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (APC.esub (ELit (0)) (APC.eadd (EVar 33) (EVar 11))); (ELit (18446744073709551612)); (ELit (17)); (EVar 15); EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 33) (4) (342);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8592))]
  48 [((EVar 2), (-8592), ELit 8592)] [] (ELit (1048576)).
Definition BL4 : CA.blocks := [].
Definition hints4 : list (nat * CC.subst) := [(12%nat, [(66%nat, (APC.eaddz (EVar 11) (-1)))]); (13%nat, [(70%nat, (ELit (8192))); (69%nat, (ELit (3)))])].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 280756 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 11); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 10); (EVar 12); (APC.eadd (EVar 11) (EVar 12)); (ELit (1)); (EVar 66); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 12) (0) (16);
   KRange (APC.eadd (EVar 11) (EVar 12)) (1) (17);
   KRange (EVar 66) (1) (21);
   KRange (APC.esub (EVar 11) (EVar 66)) (0) (20);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8512));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24)]
  67 [((EVar 2), (-8592), ELit 8592)] [] (APC.eaddz (APC.escale (64) (APC.eaddz (EVar 66) (20))) (8)).
Definition BL5 : CA.blocks := [].
Definition hints5 : list (nat * CC.subst) := [(6%nat, [(66%nat, (EVar 12))])].
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CC.CP 280820 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 11); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 67); (EVar 66); (APC.eadd (EVar 11) (EVar 12)); (EVar 68); (EVar 69); (EVar 70); (EVar 71); EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 12) (1) (16);
   KRange (APC.eadd (EVar 11) (EVar 12)) (2) (17);
   KRange (EVar 66) (1) (16);
   KRange (APC.esub (EVar 12) (EVar 66)) (0) (15);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8512));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24)]
  72 [((EVar 2), (-8592), ELit 8592)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (8)).
Definition BL6 : CA.blocks := [].
Definition hints6 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CC.CP 280968 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 11); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 10); (ELit (1)); (EVar 33); (EVar 66); (APC.eadd (EVar 10) (APC.esub (EVar 33) (EVar 66))); (APC.eadd (EVar 10) (APC.esub (EVar 33) (EVar 66))); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (1) (17);
   KRange (APC.esub (EVar 11) (EVar 33)) (1) (20);
   KRange (APC.esub (EVar 33) (EVar 11)) (18446744073709551596) (18446744073709551615);
   KRange (EVar 66) (1) (17);
   KRange (APC.esub (EVar 33) (EVar 66)) (0) (16);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8512));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24)]
  67 [((EVar 2), (-8592), ELit 8592)] [] (APC.eaddz (APC.escale (64) (APC.eaddz (EVar 66) (24))) (8)).
Definition BL7 : CA.blocks := [].
Definition hints7 : list (nat * CC.subst) := [(8%nat, [(66%nat, (APC.esub (EVar 11) (EVar 33)))])].
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CC.CP 281068 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 11); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 10)) (ELit (-1))); (APC.esub (EVar 11) (EVar 66)); (APC.esub (EVar 11) (EVar 66)); (EVar 68); (EVar 69); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (1) (17);
   KRange (APC.esub (EVar 11) (EVar 33)) (1) (20);
   KRange (APC.esub (EVar 33) (EVar 11)) (18446744073709551596) (18446744073709551615);
   KRange (EVar 66) (1) (20);
   KRange (APC.esub (EVar 11) (EVar 66)) (1) (20);
   KRange (APC.esub (APC.esub (EVar 11) (EVar 66)) (EVar 33)) (0) (19);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8512));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24)]
  70 [((EVar 2), (-8592), ELit 8592)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (8)).
Definition BL8 : CA.blocks := [].
Definition hints8 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CC.CP 281196 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 11); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 10); (EVar 67); (APC.esub (ELit (0)) (EVar 66)); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (0) (3);
   KRange (EVar 33) (1) (3);
   KRange (EVar 66) (1) (3);
   KRange (APC.esub (EVar 33) (EVar 66)) (0) (2);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8512));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24)]
  68 [((EVar 2), (-8592), ELit 8592)] [] (APC.eaddz (APC.escale (64) (APC.eaddz (EVar 66) (24))) (8)).
Definition BL9 : CA.blocks := [].
Definition hints9 : list (nat * CC.subst) := [(9%nat, [(66%nat, (APC.eaddz (EVar 66) (-1)))]); (10%nat, [(66%nat, (EVar 11))])].
(* [comment removed for export] *)
Definition t10 : CC.cutpoint := CC.CP 281244 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 66); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 10); (ELit (1)); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (0) (3);
   KRange (EVar 66) (1) (21);
   KRange (APC.esub (EVar 11) (EVar 66)) (0) (20);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8512));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24)]
  68 [((EVar 2), (-8592), ELit 8592)] [] (APC.eaddz (APC.escale (64) (EVar 66)) (8)).
Definition BL10 : CA.blocks := [].
Definition hints10 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t11 : CC.cutpoint := CC.CP 281464 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 66); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (EVar 33); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (18) (330);
   KRange (EVar 11) (2) (21);
   KRange (EVar 66) (1) (20);
   KRange (APC.esub (EVar 11) (EVar 66)) (1) (20);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8512));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24)]
  67 [((EVar 2), (-8592), ELit 8592)] [] (APC.eaddz (APC.escale (64) (APC.eaddz (EVar 66) (24))) (8)).
Definition BL11 : CA.blocks := [].
Definition hints11 : list (nat * CC.subst) := [(13%nat, [(70%nat, (APC.eaddz (EVar 66) (20))); (69%nat, (APC.eaddz (EVar 11) (3)))])].
(* [comment removed for export] *)
Definition t12 : CC.cutpoint := CC.CP 281464 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 66); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (APC.eadd (EVar 10) (APC.esub (EVar 11) (EVar 66))); (APC.esub (ELit (0)) (EVar 33)); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 33) (4) (342);
   KRange (EVar 11) (2) (21);
   KRange (EVar 66) (1) (20);
   KRange (APC.esub (EVar 11) (EVar 66)) (1) (20);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8512));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24)]
  67 [((EVar 2), (-8592), ELit 8592)] [] (APC.eaddz (APC.escale (64) (APC.eaddz (EVar 66) (24))) (8)).
Definition BL12 : CA.blocks := [].
Definition hints12 : list (nat * CC.subst) := [(13%nat, [(70%nat, (APC.eaddz (EVar 66) (20))); (69%nat, (APC.eaddz (EVar 11) (3)))])].
(* [comment removed for export] *)
Definition t13 : CC.cutpoint := CC.CP 283100 [EVar 0; (EVar 50); (APC.eaddz (EVar 2) (-32)); EVar 3; EVar 4; (EVar 51); (EVar 52); (EVar 53); (EVar 15); (EVar 71); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 68); EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 62); (EVar 63); (EVar 64); (EVar 65)]
  [KRange (EVar 68) (5) (343);
   KRange (EVar 69) (3) (24);
   KRange (EVar 70) (0) (1048576);
   KWord (SA (EVar 15) (0)) 8 (EVar 32);
   KRange (EVar 11) (1) (21);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 10) (1099511627776) (140737488355328);
   KRange (EVar 15) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-8592)) (ELit (8592));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 10) (0)) (EVar 11);
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-8592)) (ELit (8592)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 15) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (EVar 11) (SA (EVar 15) (0)) (ELit (8));
   KUnk (SA (EVar 2) (-8592)) (ELit (8512));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18)]
  72 [((EVar 2), (-8592), ELit 8592)] [] (APC.eaddz (APC.escale (64) (EVar 70)) (40)).
Definition BL13 : CA.blocks := [].
Definition hints13 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [280792; 281004; 281088; 281280; 281380; 281412; 281484] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
