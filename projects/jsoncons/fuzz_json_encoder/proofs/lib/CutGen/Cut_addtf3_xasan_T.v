(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm4CutKitD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutVFT.
Definition ITR : list (Z * nat) := [(1335696, 499%nat); (1337692, 12%nat); (1337740, 3%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [1337656].
Definition CSUMS : list CAD.callsum := [(CAD.CSUM 1337692 (fun _ => []) (fun _ => Some (ELit 0)) (fun _ _ => []) (fun _ => None) false (Some (4, [])) 0 false false); CAD.cs_inline 1337740 4 []].
Definition ASSUME : list (Z * (list expr -> list kentry -> list (list kentry * kentry))) := [].
Definition CASES : list (Z * list (nat * Z)) := [].
Definition RESPELL : list (Z * (list expr -> list kentry -> list (nat * expr))) := [].
Definition ECASES : list (Z * list ((list expr -> expr) * Z)) := [].
Definition NAMEB : list (Z * nat) := [].
Definition XSTOPS : list Z := [1335696; 1335720; 1335744; 1335768; 1335792; 1335816; 1335840; 1335864; 1335888; 1335912; 1335936; 1335960; 1335984; 1336008; 1336032; 1336056; 1336080; 1336104; 1336128; 1336152; 1336176; 1336200; 1336224; 1336248; 1336272; 1336296; 1336320; 1336344; 1336368; 1336392; 1336416; 1336440; 1336464; 1336488; 1336512; 1336536; 1336560; 1336584; 1336608; 1336632; 1336656; 1336680; 1336704; 1336728; 1336752; 1336776; 1336800; 1336824; 1336848; 1336872; 1336896; 1336920; 1336944; 1336968; 1336992; 1337016; 1337040; 1337064; 1337088; 1337112; 1337136; 1337160; 1337184; 1337208; 1337232; 1337256; 1337280; 1337304; 1337328; 1337352; 1337376; 1337400; 1337424; 1337448; 1337472; 1337496; 1337520; 1337544; 1337568; 1337592; 1337616; 1337640; 1337664; 1337688; 1337692; 1337716; 1337740].
Definition HDECL : CH.hdecl := CH.HD (48) (8224) [] [] [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 1335696 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KUnk (SA (EVar 2) (-48)) (ELit (48))]
  32 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511627776)).
Definition BL0 : CAD.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 1335788 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511626304)).
Definition BL1 : CAD.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 1335824 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511622400)).
Definition BL2 : CAD.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 1335844 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511621312)).
Definition BL3 : CAD.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 1335884 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511620672)).
Definition BL4 : CAD.blocks := [].
Definition hints4 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 1335896 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511625728)).
Definition BL5 : CAD.blocks := [].
Definition hints5 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CC.CP 1335916 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511624960)).
Definition BL6 : CAD.blocks := [].
Definition hints6 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CC.CP 1335936 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511624256)).
Definition BL7 : CAD.blocks := [].
Definition hints7 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CC.CP 1335996 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511623296)).
Definition BL8 : CAD.blocks := [].
Definition hints8 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CC.CP 1336024 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511621888)).
Definition BL9 : CAD.blocks := [].
Definition hints9 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t10 : CC.cutpoint := CC.CP 1336060 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511620480)).
Definition BL10 : CAD.blocks := [].
Definition hints10 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t11 : CC.cutpoint := CC.CP 1336076 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511620224)).
Definition BL11 : CAD.blocks := [].
Definition hints11 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t12 : CC.cutpoint := CC.CP 1336284 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511625280)).
Definition BL12 : CAD.blocks := [].
Definition hints12 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t13 : CC.cutpoint := CC.CP 1336312 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511624512)).
Definition BL13 : CAD.blocks := [].
Definition hints13 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t14 : CC.cutpoint := CC.CP 1336348 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511616704)).
Definition BL14 : CAD.blocks := [].
Definition hints14 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t15 : CC.cutpoint := CC.CP 1336376 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511616256)).
Definition BL15 : CAD.blocks := [].
Definition hints15 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t16 : CC.cutpoint := CC.CP 1336392 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511616000)).
Definition BL16 : CAD.blocks := [].
Definition hints16 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t17 : CC.cutpoint := CC.CP 1336612 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511612480)).
Definition BL17 : CAD.blocks := [].
Definition hints17 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t18 : CC.cutpoint := CC.CP 1336632 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511612160)).
Definition BL18 : CAD.blocks := [].
Definition hints18 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t19 : CC.cutpoint := CC.CP 1336764 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511608256)).
Definition BL19 : CAD.blocks := [].
Definition hints19 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t20 : CC.cutpoint := CC.CP 1336832 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511607168)).
Definition BL20 : CAD.blocks := [].
Definition hints20 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t21 : CC.cutpoint := CC.CP 1337052 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511609984)).
Definition BL21 : CAD.blocks := [].
Definition hints21 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t22 : CC.cutpoint := CC.CP 1337116 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511608960)).
Definition BL22 : CAD.blocks := [].
Definition hints22 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t23 : CC.cutpoint := CC.CP 1337144 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511603072)).
Definition BL23 : CAD.blocks := [].
Definition hints23 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t24 : CC.cutpoint := CC.CP 1337196 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511602240)).
Definition BL24 : CAD.blocks := [].
Definition hints24 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t25 : CC.cutpoint := CC.CP 1337216 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511601920)).
Definition BL25 : CAD.blocks := [].
Definition hints25 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t26 : CC.cutpoint := CC.CP 1337296 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511603648)).
Definition BL26 : CAD.blocks := [].
Definition hints26 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t27 : CC.cutpoint := CC.CP 1337332 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511601600)).
Definition BL27 : CAD.blocks := [].
Definition hints27 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t28 : CC.cutpoint := CC.CP 1337400 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511600512)).
Definition BL28 : CAD.blocks := [].
Definition hints28 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t29 : CC.cutpoint := CC.CP 1337468 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511599424)).
Definition BL29 : CAD.blocks := [].
Definition hints29 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t30 : CC.cutpoint := CC.CP 1337480 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511599232)).
Definition BL30 : CAD.blocks := [].
Definition hints30 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t31 : CC.cutpoint := CC.CP 1337588 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511597312)).
Definition BL31 : CAD.blocks := [].
Definition hints31 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t32 : CC.cutpoint := CC.CP 1337596 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511597184)).
Definition BL32 : CAD.blocks := [].
Definition hints32 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t33 : CC.cutpoint := CC.CP 1337612 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511596928)).
Definition BL33 : CAD.blocks := [].
Definition hints33 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t34 : CC.cutpoint := CC.CP 1337616 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511596864)).
Definition BL34 : CAD.blocks := [].
Definition hints34 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t35 : CC.cutpoint := CC.CP 1337620 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-48)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 49); (EVar 50); (EVar 51); (EVar 52)]
  [KRange (EVar 2) (140735332483120) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-48)) (ELit (48));
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  53 [((EVar 2), (-48), ELit 48)] [] (ELit (1099511596480)).
Definition BL35 : CAD.blocks := [].
Definition hints35 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t12; t13; t14; t15; t16; t17; t18; t19; t20; t21; t22; t23; t24; t25; t26; t27; t28; t29; t30; t31; t32; t33; t34; t35].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CAD.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 40%nat [2%nat; 4%nat] XSTOPS ASSUME CASES NAMEB RESPELL ECASES (CC.cp_F c) (CC.cp_meas c) h 4000 first false 2%nat
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CAD.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CAD.po_leaves o)) (CC.cp_meas c).
