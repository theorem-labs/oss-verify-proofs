(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(751308, 577%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [753276].
Definition CSUMS : list CAD.callsum := [].
Definition ASSUME : list (Z * (list expr -> list kentry -> list (list kentry * kentry))) := [].
Definition CASES : list (Z * list (nat * Z)) := [].
Definition RESPELL : list (Z * (list expr -> list kentry -> list (nat * expr))) := [].
Definition ECASES : list (Z * list ((list expr -> expr) * Z)) := [].
Definition NAMEB : list (Z * nat) := [].
Definition XSTOPS : list Z := [751308; 751332; 751356; 751380; 751404; 751428; 751452; 751476; 751500; 751524; 751548; 751572; 751596; 751620; 751644; 751668; 751692; 751716; 751740; 751764; 751788; 751812; 751836; 751860; 751884; 751908; 751932; 751956; 751980; 752004; 752028; 752052; 752076; 752100; 752124; 752148; 752172; 752196; 752220; 752244; 752268; 752292; 752316; 752340; 752364; 752388; 752412; 752436; 752460; 752484; 752508; 752532; 752556; 752580; 752604; 752628; 752652; 752676; 752700; 752724; 752748; 752772; 752796; 752820; 752844; 752868; 752892; 752916; 752940; 752964; 752988; 753012; 753036; 753060; 753084; 753108; 753132; 753156; 753180; 753204; 753228; 753252; 753276; 753300; 753324; 753348; 753372; 753396; 753420; 753444; 753468; 753492; 753516; 753540; 753564; 753588; 753612].
Definition HDECL : CH.hdecl := CH.HD (112) (8224) [] [] [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 751308 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (112))]
  32 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511627776)).
Definition BL0 : CAD.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 751444 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511614080)).
Definition BL1 : CAD.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 752208 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511601856)).
Definition BL2 : CAD.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 752280 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511625600)).
Definition BL3 : CAD.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 752308 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511624768)).
Definition BL4 : CAD.blocks := [].
Definition hints4 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 752332 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511623936)).
Definition BL5 : CAD.blocks := [].
Definition hints5 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CC.CP 752460 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511592576)).
Definition BL6 : CAD.blocks := [].
Definition hints6 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CC.CP 752480 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511599424)).
Definition BL7 : CAD.blocks := [].
Definition hints7 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CC.CP 752536 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511595136)).
Definition BL8 : CAD.blocks := [].
Definition hints8 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CC.CP 752552 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511625024)).
Definition BL9 : CAD.blocks := [].
Definition hints9 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t10 : CC.cutpoint := CC.CP 752576 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511624256)).
Definition BL10 : CAD.blocks := [].
Definition hints10 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t11 : CC.cutpoint := CC.CP 752652 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511591936)).
Definition BL11 : CAD.blocks := [].
Definition hints11 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t12 : CC.cutpoint := CC.CP 752700 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511622336)).
Definition BL12 : CAD.blocks := [].
Definition hints12 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t13 : CC.cutpoint := CC.CP 752920 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511597504)).
Definition BL13 : CAD.blocks := [].
Definition hints13 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t14 : CC.cutpoint := CC.CP 752976 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511596608)).
Definition BL14 : CAD.blocks := [].
Definition hints14 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t15 : CC.cutpoint := CC.CP 753064 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511595200)).
Definition BL15 : CAD.blocks := [].
Definition hints15 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t16 : CC.cutpoint := CC.CP 753068 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511595008)).
Definition BL16 : CAD.blocks := [].
Definition hints16 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t17 : CC.cutpoint := CC.CP 753136 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511593920)).
Definition BL17 : CAD.blocks := [].
Definition hints17 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t18 : CC.cutpoint := CC.CP 753200 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511592896)).
Definition BL18 : CAD.blocks := [].
Definition hints18 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t19 : CC.cutpoint := CC.CP 753220 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511591808)).
Definition BL19 : CAD.blocks := [].
Definition hints19 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t20 : CC.cutpoint := CC.CP 753328 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511618816)).
Definition BL20 : CAD.blocks := [].
Definition hints20 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t21 : CC.cutpoint := CC.CP 753348 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511618368)).
Definition BL21 : CAD.blocks := [].
Definition hints21 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t22 : CC.cutpoint := CC.CP 753372 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511617984)).
Definition BL22 : CAD.blocks := [].
Definition hints22 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t23 : CC.cutpoint := CC.CP 753592 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-112)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (8));
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
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  60 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511614464)).
Definition BL23 : CAD.blocks := [].
Definition hints23 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13; t14; t15; t16; t17; t18; t19; t20; t21; t22; t23].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CAD.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 40%nat [2%nat; 4%nat] XSTOPS ASSUME CASES NAMEB RESPELL ECASES (CC.cp_F c) (CC.cp_meas c) h 4000 first false 2%nat
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CAD.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CAD.po_leaves o)) (CC.cp_meas c).
