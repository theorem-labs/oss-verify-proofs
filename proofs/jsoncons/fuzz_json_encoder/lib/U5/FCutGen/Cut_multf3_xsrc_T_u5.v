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
Definition ITR : list (Z * nat) := [(746628, 448%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [748104].
Definition CSUMS : list CAD.callsum := [].
Definition ASSUME : list (Z * (list expr -> list kentry -> list (list kentry * kentry))) := [].
Definition CASES : list (Z * list (nat * Z)) := [].
Definition RESPELL : list (Z * (list expr -> list kentry -> list (nat * expr))) := [].
Definition ECASES : list (Z * list ((list expr -> expr) * Z)) := [].
Definition NAMEB : list (Z * nat) := [].
Definition XSTOPS : list Z := [746628; 746652; 746676; 746700; 746724; 746748; 746772; 746796; 746820; 746844; 746868; 746892; 746916; 746940; 746964; 746988; 747012; 747036; 747060; 747084; 747108; 747132; 747156; 747180; 747204; 747228; 747252; 747276; 747300; 747324; 747348; 747372; 747396; 747420; 747444; 747468; 747492; 747516; 747540; 747564; 747588; 747612; 747636; 747660; 747684; 747708; 747732; 747756; 747780; 747804; 747828; 747852; 747876; 747900; 747924; 747948; 747972; 747996; 748020; 748044; 748068; 748092; 748116; 748140; 748164; 748188; 748212; 748236; 748260; 748284; 748308; 748332; 748356; 748380; 748404].
Definition HDECL : CH.hdecl := CH.HD (80) (8224) [] [] [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 746628 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (80))]
  32 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511627776)).
Definition BL0 : CAD.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 746756 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511614208)).
Definition BL1 : CAD.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 747224 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511625728)).
Definition BL2 : CAD.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 747252 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511624896)).
Definition BL3 : CAD.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 747276 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511624192)).
Definition BL4 : CAD.blocks := [].
Definition hints4 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 747328 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511606464)).
Definition BL5 : CAD.blocks := [].
Definition hints5 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CC.CP 747348 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511606144)).
Definition BL6 : CAD.blocks := [].
Definition hints6 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CC.CP 747380 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511601152)).
Definition BL7 : CAD.blocks := [].
Definition hints7 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CC.CP 747396 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511600896)).
Definition BL8 : CAD.blocks := [].
Definition hints8 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CC.CP 747444 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511625152)).
Definition BL9 : CAD.blocks := [].
Definition hints9 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t10 : CC.cutpoint := CC.CP 747468 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511624384)).
Definition BL10 : CAD.blocks := [].
Definition hints10 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t11 : CC.cutpoint := CC.CP 747480 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511600256)).
Definition BL11 : CAD.blocks := [].
Definition hints11 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t12 : CC.cutpoint := CC.CP 747548 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511604096)).
Definition BL12 : CAD.blocks := [].
Definition hints12 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t13 : CC.cutpoint := CC.CP 747588 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511623296)).
Definition BL13 : CAD.blocks := [].
Definition hints13 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t14 : CC.cutpoint := CC.CP 747636 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511622528)).
Definition BL14 : CAD.blocks := [].
Definition hints14 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t15 : CC.cutpoint := CC.CP 747844 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511599936)).
Definition BL15 : CAD.blocks := [].
Definition hints15 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t16 : CC.cutpoint := CC.CP 747884 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511604160)).
Definition BL16 : CAD.blocks := [].
Definition hints16 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t17 : CC.cutpoint := CC.CP 747888 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511603776)).
Definition BL17 : CAD.blocks := [].
Definition hints17 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t18 : CC.cutpoint := CC.CP 747948 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511602112)).
Definition BL18 : CAD.blocks := [].
Definition hints18 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t19 : CC.cutpoint := CC.CP 748008 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511602176)).
Definition BL19 : CAD.blocks := [].
Definition hints19 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t20 : CC.cutpoint := CC.CP 748012 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511601792)).
Definition BL20 : CAD.blocks := [].
Definition hints20 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t21 : CC.cutpoint := CC.CP 748040 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511601344)).
Definition BL21 : CAD.blocks := [].
Definition hints21 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t22 : CC.cutpoint := CC.CP 748052 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511600128)).
Definition BL22 : CAD.blocks := [].
Definition hints22 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t23 : CC.cutpoint := CC.CP 748064 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511599808)).
Definition BL23 : CAD.blocks := [].
Definition hints23 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t24 : CC.cutpoint := CC.CP 748136 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511618880)).
Definition BL24 : CAD.blocks := [].
Definition hints24 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t25 : CC.cutpoint := CC.CP 748152 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511618496)).
Definition BL25 : CAD.blocks := [].
Definition hints25 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t26 : CC.cutpoint := CC.CP 748176 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511618112)).
Definition BL26 : CAD.blocks := [].
Definition hints26 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t27 : CC.cutpoint := CC.CP 748396 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (8));
   KWord (SA (EVar 2) (-72)) 8 (EVar 24);
   KWord (SA (EVar 2) (-64)) 8 (EVar 23);
   KWord (SA (EVar 2) (-56)) 8 (EVar 22);
   KWord (SA (EVar 2) (-48)) 8 (EVar 21);
   KWord (SA (EVar 2) (-40)) 8 (EVar 20);
   KWord (SA (EVar 2) (-32)) 8 (EVar 19);
   KWord (SA (EVar 2) (-24)) 8 (EVar 18);
   KWord (SA (EVar 2) (-16)) 8 (EVar 9);
   KWord (SA (EVar 2) (-8)) 8 (EVar 8)]
  56 [((EVar 2), (-80), ELit 80)] [] (ELit (1099511614592)).
Definition BL27 : CAD.blocks := [].
Definition hints27 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13; t14; t15; t16; t17; t18; t19; t20; t21; t22; t23; t24; t25; t26; t27].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CAD.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 40%nat [2%nat; 4%nat] XSTOPS ASSUME CASES NAMEB RESPELL ECASES (CC.cp_F c) (CC.cp_meas c) h 4000 first false 2%nat
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CAD.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CAD.po_leaves o)) (CC.cp_meas c).
