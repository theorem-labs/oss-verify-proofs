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
Definition ITR : list (Z * nat) := [(765248, 156%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 34.
Definition ENDS : list Z := [765868].
Definition CSUMS : list CAD.callsum := [].
Definition ASSUME : list (Z * (list expr -> list kentry -> list (list kentry * kentry))) := [(765540, (CAD.A_both (CAD.A_range 18 48 57) (CAD.A_range 9 0 214748363))); (765648, (CAD.A_both (CAD.A_range 19 48 57) (CAD.A_range 9 0 92233720368547757))); (765764, (fun regs kn => match nth 10 regs (ELit 0) with EAluw Instr.ALU_ADD v (ELit _) => CAD.A_expr (fun _ => v) 48 57 regs kn | EAlu Instr.ALU_ADD v (ELit _) => CAD.A_expr (fun _ => v) 48 57 regs kn | ELit 9 => CAD.A_range 19 48 57 regs kn | _ => [] end))].
Definition CASES : list (Z * list (nat * Z)) := [].
Definition RESPELL : list (Z * (list expr -> list kentry -> list (nat * expr))) := [].
Definition ECASES : list (Z * list ((list expr -> expr) * Z)) := [].
Definition NAMEB : list (Z * nat) := [(765316, 1%nat); (765384, 1%nat); (765560, 1%nat); (765668, 1%nat); (765784, 1%nat)].
Definition XSTOPS : list Z := [765540; 765648; 765764; 765316; 765384; 765560; 765668; 765784].
Definition HDECL : CH.hdecl := CH.HD (0) (8224) [] [] [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 765248 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (ELit (1)); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 32) (4096) (140737488355328);
   KRange (EVar 33) (0) (0);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KZero (SA (APC.eadd (EVar 32) (EVar 33)) (0)) (ELit (1));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 2) (-80)) (ELit (80));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KUnk (SA (EVar 2) (-80)) (ELit (80))]
  34 [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8)] [] (ELit (1152921504606846976)).
Definition BL0 : CAD.blocks := [].
Definition hints0 : list (nat * CC.subst) := [(3%nat, [(34%nat, (EVar 33))]); (4%nat, [(34%nat, (EVar 33))]); (5%nat, [(34%nat, (EVar 33))]); (6%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (7%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (8%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (9%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (10%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (11%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))])].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 765248 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (ELit (1)); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 32) (4096) (140737488355328);
   KRange (EVar 33) (1) (1);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KZero (SA (APC.eadd (EVar 32) (EVar 33)) (0)) (ELit (1));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 2) (-80)) (ELit (80));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KUnk (SA (EVar 2) (-80)) (ELit (80))]
  34 [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8)] [] (ELit (1152921504606846976)).
Definition BL1 : CAD.blocks := [].
Definition hints1 : list (nat * CC.subst) := [(3%nat, [(34%nat, (EVar 33))]); (4%nat, [(34%nat, (EVar 33))]); (5%nat, [(34%nat, (EVar 33))]); (6%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (7%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (8%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (9%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (10%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (11%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))])].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 765248 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (ELit (1)); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 32) (4096) (140737488355328);
   KRange (EVar 33) (2) (67108864);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KZero (SA (APC.eadd (EVar 32) (EVar 33)) (0)) (ELit (1));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 2) (-80)) (ELit (80));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KUnk (SA (EVar 2) (-80)) (ELit (80))]
  34 [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8)] [] (ELit (1152921504606846976)).
Definition BL2 : CAD.blocks := [].
Definition hints2 : list (nat * CC.subst) := [(3%nat, [(34%nat, (EVar 33))]); (4%nat, [(34%nat, (EVar 33))]); (5%nat, [(34%nat, (EVar 33))]); (6%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (7%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (8%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (9%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (10%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))]); (11%nat, [(34%nat, (APC.eaddz (EVar 33) (-1)))])].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 765540 [EVar 0; (EVar 39); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 40); (EVar 41); (EVar 42); (EVar 10); (EVar 36); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 35); (EVar 51); (EVar 37); (ELit (9)); (ELit (10)); (ELit (214748364)); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 34) (1) (67108864);
   KRange (EVar 35) (48) (57);
   KRange (EVar 36) (0) (214748363);
   KRange (EVar 37) (0) (1);
   KRange (EVar 38) (48) (57);
   KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 32) (4096) (140737488355328);
   KRange (EVar 33) (1) (134217728);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KZero (SA (APC.eadd (EVar 32) (EVar 33)) (0)) (ELit (1));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 2) (-80)) (ELit (80));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 10) (8)) 8 (APC.esub (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (1)) (EVar 34));
   KRange (APC.esub (EVar 33) (EVar 34)) (0) (268435456);
   KWord (SA (APC.eaddz (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 34)) (-1)) (1)) 1 (EVar 35);
   KWord (SA (EVar 32) (0)) 1 (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KUnk (SA (EVar 2) (-80)) (ELit (8))]
  56 [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 34)) (576460752303423493)).
Definition BL3 : CAD.blocks := [].
Definition hints3 : list (nat * CC.subst) := [(3%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (4%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (5%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (6%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (7%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (8%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (9%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (10%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (11%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))])].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 765648 [EVar 0; (EVar 39); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 40); (EVar 41); (EVar 42); (EVar 10); (EVar 36); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (ELit (9)); (EVar 35); (EVar 37); (ELit (92233720368547758)); (ELit (10)); (EVar 51); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 34) (1) (67108864);
   KRange (EVar 35) (48) (57);
   KRange (EVar 36) (0) (92233720368547757);
   KRange (EVar 37) (0) (1);
   KRange (EVar 38) (48) (57);
   KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 32) (4096) (140737488355328);
   KRange (EVar 33) (1) (134217728);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KZero (SA (APC.eadd (EVar 32) (EVar 33)) (0)) (ELit (1));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 2) (-80)) (ELit (80));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 10) (8)) 8 (APC.esub (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (1)) (EVar 34));
   KRange (APC.esub (EVar 33) (EVar 34)) (0) (268435456);
   KWord (SA (APC.eaddz (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 34)) (-1)) (1)) 1 (EVar 35);
   KWord (SA (EVar 32) (0)) 1 (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KUnk (SA (EVar 2) (-80)) (ELit (8))]
  56 [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 34)) (576460752303423492)).
Definition BL4 : CAD.blocks := [].
Definition hints4 : list (nat * CC.subst) := [(3%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (4%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (5%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (6%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (7%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (8%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (9%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (10%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (11%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))])].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 765764 [EVar 0; (EVar 39); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 40); (EVar 41); (EVar 42); (EVar 10); (EVar 36); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (ELit (10)); (EVar 51); (EVar 37); (EVar 52); (EVar 53); (EVar 54); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 55); (EVar 56); (EVar 57); (EVar 58)]
  [KRange (EVar 34) (1) (67108864);
   KRange (EVar 35) (48) (57);
   KRange (EVar 36) (0) (9223372036854775806);
   KRange (EVar 37) (0) (1);
   KRange (EVar 38) (48) (57);
   KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 32) (4096) (140737488355328);
   KRange (EVar 33) (1) (134217728);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KZero (SA (APC.eadd (EVar 32) (EVar 33)) (0)) (ELit (1));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 2) (-80)) (ELit (80));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 10) (8)) 8 (APC.esub (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (1)) (EVar 34));
   KRange (APC.esub (EVar 33) (EVar 34)) (0) (268435456);
   KWord (SA (APC.eaddz (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 34)) (-1)) (1)) 1 (EVar 35);
   KWord (SA (EVar 32) (0)) 1 (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KUnk (SA (EVar 2) (-80)) (ELit (8))]
  59 [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 34)) (576460752303423491)).
Definition BL5 : CAD.blocks := [].
Definition hints5 : list (nat * CC.subst) := [(3%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (4%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (5%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (6%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (7%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (8%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (9%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (10%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (11%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))])].
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CC.CP 765540 [EVar 0; (EVar 39); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 40); (EVar 41); (EVar 42); (EVar 10); (EVar 36); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 35); (EVar 51); (EVar 37); (ELit (9)); (ELit (10)); (ELit (214748364)); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 34) (1) (67108864);
   KRange (EVar 35) (48) (57);
   KRange (EVar 36) (0) (214748363);
   KRange (EVar 37) (0) (1);
   KRange (EVar 38) (43) (43);
   KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 32) (4096) (140737488355328);
   KRange (EVar 33) (1) (134217728);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KZero (SA (APC.eadd (EVar 32) (EVar 33)) (0)) (ELit (1));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 2) (-80)) (ELit (80));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 10) (8)) 8 (APC.esub (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (1)) (EVar 34));
   KRange (APC.esub (EVar 33) (EVar 34)) (0) (268435456);
   KWord (SA (APC.eaddz (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 34)) (-1)) (1)) 1 (EVar 35);
   KWord (SA (EVar 32) (0)) 1 (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KUnk (SA (EVar 2) (-80)) (ELit (8))]
  56 [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 34)) (576460752303423493)).
Definition BL6 : CAD.blocks := [].
Definition hints6 : list (nat * CC.subst) := [(3%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (4%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (5%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (6%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (7%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (8%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (9%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (10%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (11%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))])].
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CC.CP 765648 [EVar 0; (EVar 39); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 40); (EVar 41); (EVar 42); (EVar 10); (EVar 36); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (ELit (9)); (EVar 35); (EVar 37); (ELit (92233720368547758)); (ELit (10)); (EVar 51); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 34) (1) (67108864);
   KRange (EVar 35) (48) (57);
   KRange (EVar 36) (0) (92233720368547757);
   KRange (EVar 37) (0) (1);
   KRange (EVar 38) (43) (43);
   KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 32) (4096) (140737488355328);
   KRange (EVar 33) (1) (134217728);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KZero (SA (APC.eadd (EVar 32) (EVar 33)) (0)) (ELit (1));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 2) (-80)) (ELit (80));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 10) (8)) 8 (APC.esub (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (1)) (EVar 34));
   KRange (APC.esub (EVar 33) (EVar 34)) (0) (268435456);
   KWord (SA (APC.eaddz (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 34)) (-1)) (1)) 1 (EVar 35);
   KWord (SA (EVar 32) (0)) 1 (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KUnk (SA (EVar 2) (-80)) (ELit (8))]
  56 [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 34)) (576460752303423492)).
Definition BL7 : CAD.blocks := [].
Definition hints7 : list (nat * CC.subst) := [(3%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (4%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (5%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (6%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (7%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (8%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (9%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (10%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (11%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))])].
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CC.CP 765764 [EVar 0; (EVar 39); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 40); (EVar 41); (EVar 42); (EVar 10); (EVar 36); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (ELit (10)); (EVar 51); (EVar 37); (EVar 52); (EVar 53); (EVar 54); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 55); (EVar 56); (EVar 57); (EVar 58)]
  [KRange (EVar 34) (1) (67108864);
   KRange (EVar 35) (48) (57);
   KRange (EVar 36) (0) (9223372036854775806);
   KRange (EVar 37) (0) (1);
   KRange (EVar 38) (43) (43);
   KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 32) (4096) (140737488355328);
   KRange (EVar 33) (1) (134217728);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KZero (SA (APC.eadd (EVar 32) (EVar 33)) (0)) (ELit (1));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 2) (-80)) (ELit (80));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 10) (8)) 8 (APC.esub (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (1)) (EVar 34));
   KRange (APC.esub (EVar 33) (EVar 34)) (0) (268435456);
   KWord (SA (APC.eaddz (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 34)) (-1)) (1)) 1 (EVar 35);
   KWord (SA (EVar 32) (0)) 1 (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KUnk (SA (EVar 2) (-80)) (ELit (8))]
  59 [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 34)) (576460752303423491)).
Definition BL8 : CAD.blocks := [].
Definition hints8 : list (nat * CC.subst) := [(3%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (4%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (5%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (6%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (7%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (8%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (9%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (10%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (11%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))])].
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CC.CP 765540 [EVar 0; (EVar 39); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 40); (EVar 41); (EVar 42); (EVar 10); (EVar 36); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 35); (EVar 51); (EVar 37); (ELit (9)); (ELit (10)); (ELit (214748364)); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 34) (1) (67108864);
   KRange (EVar 35) (48) (57);
   KRange (EVar 36) (0) (214748363);
   KRange (EVar 37) (0) (1);
   KRange (EVar 38) (45) (45);
   KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 32) (4096) (140737488355328);
   KRange (EVar 33) (1) (134217728);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KZero (SA (APC.eadd (EVar 32) (EVar 33)) (0)) (ELit (1));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 2) (-80)) (ELit (80));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 10) (8)) 8 (APC.esub (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (1)) (EVar 34));
   KRange (APC.esub (EVar 33) (EVar 34)) (0) (268435456);
   KWord (SA (APC.eaddz (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 34)) (-1)) (1)) 1 (EVar 35);
   KWord (SA (EVar 32) (0)) 1 (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KUnk (SA (EVar 2) (-80)) (ELit (8))]
  56 [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 34)) (576460752303423493)).
Definition BL9 : CAD.blocks := [].
Definition hints9 : list (nat * CC.subst) := [(3%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (4%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (5%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (6%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (7%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (8%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (9%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (10%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (11%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))])].
(* [comment removed for export] *)
Definition t10 : CC.cutpoint := CC.CP 765648 [EVar 0; (EVar 39); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 40); (EVar 41); (EVar 42); (EVar 10); (EVar 36); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (ELit (9)); (EVar 35); (EVar 37); (ELit (92233720368547758)); (ELit (10)); (EVar 51); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 52); (EVar 53); (EVar 54); (EVar 55)]
  [KRange (EVar 34) (1) (67108864);
   KRange (EVar 35) (48) (57);
   KRange (EVar 36) (0) (92233720368547757);
   KRange (EVar 37) (0) (1);
   KRange (EVar 38) (45) (45);
   KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 32) (4096) (140737488355328);
   KRange (EVar 33) (1) (134217728);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KZero (SA (APC.eadd (EVar 32) (EVar 33)) (0)) (ELit (1));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 2) (-80)) (ELit (80));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 10) (8)) 8 (APC.esub (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (1)) (EVar 34));
   KRange (APC.esub (EVar 33) (EVar 34)) (0) (268435456);
   KWord (SA (APC.eaddz (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 34)) (-1)) (1)) 1 (EVar 35);
   KWord (SA (EVar 32) (0)) 1 (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KUnk (SA (EVar 2) (-80)) (ELit (8))]
  56 [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 34)) (576460752303423492)).
Definition BL10 : CAD.blocks := [].
Definition hints10 : list (nat * CC.subst) := [(3%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (4%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (5%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (6%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (7%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (8%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (9%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (10%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (11%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))])].
(* [comment removed for export] *)
Definition t11 : CC.cutpoint := CC.CP 765764 [EVar 0; (EVar 39); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 40); (EVar 41); (EVar 42); (EVar 10); (EVar 36); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (ELit (10)); (EVar 51); (EVar 37); (EVar 52); (EVar 53); (EVar 54); EVar 24; EVar 25; EVar 26; EVar 27; (EVar 55); (EVar 56); (EVar 57); (EVar 58)]
  [KRange (EVar 34) (1) (67108864);
   KRange (EVar 35) (48) (57);
   KRange (EVar 36) (0) (9223372036854775806);
   KRange (EVar 37) (0) (1);
   KRange (EVar 38) (45) (45);
   KRange (EVar 2) (140735332483152) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 10) (8)) (ELit (8));
   KRange (EVar 10) (140735332483072) (140737488355072);
   KDisj (SA (EVar 10) (8)) (ELit (192)) (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 32) (4096) (140737488355328);
   KRange (EVar 33) (1) (134217728);
   KWord (SA (EVar 10) (184)) 8 (ELit (18446744073709551615));
   KWord (SA (EVar 10) (192)) 8 (ELit (0));
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KZero (SA (APC.eadd (EVar 32) (EVar 33)) (0)) (ELit (1));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 2) (-80)) (ELit (80));
   KDisj (SA (EVar 32) (0)) (APC.eaddz (EVar 33) (1)) (SA (EVar 10) (8)) (ELit (192));
   KWord (SA (EVar 10) (8)) 8 (APC.esub (APC.eaddz (APC.eadd (EVar 32) (EVar 33)) (1)) (EVar 34));
   KRange (APC.esub (EVar 33) (EVar 34)) (0) (268435456);
   KWord (SA (APC.eaddz (APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 34)) (-1)) (1)) 1 (EVar 35);
   KWord (SA (EVar 32) (0)) 1 (EVar 38);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KUnk (SA (EVar 2) (-80)) (ELit (8))]
  59 [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 34)) (576460752303423491)).
Definition BL11 : CAD.blocks := [].
Definition hints11 : list (nat * CC.subst) := [(3%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (4%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (5%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (6%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (7%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (8%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (9%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (10%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))]); (11%nat, [(34%nat, (APC.eaddz (EVar 34) (-1)))])].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CAD.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] XSTOPS ASSUME CASES NAMEB RESPELL ECASES (CC.cp_F c) (CC.cp_meas c) h 400 first false 2%nat
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CAD.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CAD.po_leaves o)) (CC.cp_meas c).
