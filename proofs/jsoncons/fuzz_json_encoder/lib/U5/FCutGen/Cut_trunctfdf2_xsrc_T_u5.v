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
Definition ITR : list (Z * nat) := [(767864, 122%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [768076].
Definition CSUMS : list CAD.callsum := [CAD.cs_inline 768072 4 []].
Definition ASSUME : list (Z * (list expr -> list kentry -> list (list kentry * kentry))) := [].
Definition CASES : list (Z * list (nat * Z)) := [].
Definition RESPELL : list (Z * (list expr -> list kentry -> list (nat * expr))) := [].
Definition ECASES : list (Z * list ((list expr -> expr) * Z)) := [].
Definition NAMEB : list (Z * nat) := [].
Definition XSTOPS : list Z := [767864; 767888; 767912; 767936; 767960; 767984; 768008; 768032; 768056; 768080; 768104; 768128; 768152; 768176; 768200; 768224; 768248; 768272; 768296; 768320; 768344].
Definition HDECL : CH.hdecl := CH.HD (0) (8224) [] [] [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 767864 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332483072) (140737488355328);
   KAlign (EVar 2) (16)]
  32 [] [] (ELit (1099511627776)).
Definition BL0 : CAD.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 768000 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (0)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); EVar 8; EVar 9; (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 43); (EVar 44); (EVar 45); (EVar 46)]
  [KRange (EVar 2) (140735332483072) (140737488355328);
   KAlign (EVar 2) (16)]
  47 [] [] (ELit (1099511625152)).
Definition BL1 : CAD.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 768036 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (0)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); EVar 8; EVar 9; (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 43); (EVar 44); (EVar 45); (EVar 46)]
  [KRange (EVar 2) (140735332483072) (140737488355328);
   KAlign (EVar 2) (16)]
  47 [] [] (ELit (1099511626240)).
Definition BL2 : CAD.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 768052 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (0)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); EVar 8; EVar 9; (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 43); (EVar 44); (EVar 45); (EVar 46)]
  [KRange (EVar 2) (140735332483072) (140737488355328);
   KAlign (EVar 2) (16)]
  47 [] [] (ELit (1099511620416)).
Definition BL3 : CAD.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 768204 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (0)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); EVar 8; EVar 9; (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 43); (EVar 44); (EVar 45); (EVar 46)]
  [KRange (EVar 2) (140735332483072) (140737488355328);
   KAlign (EVar 2) (16)]
  47 [] [] (ELit (1099511622784)).
Definition BL4 : CAD.blocks := [].
Definition hints4 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 768260 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (0)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); EVar 8; EVar 9; (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 43); (EVar 44); (EVar 45); (EVar 46)]
  [KRange (EVar 2) (140735332483072) (140737488355328);
   KAlign (EVar 2) (16)]
  47 [] [] (ELit (1099511621888)).
Definition BL5 : CAD.blocks := [].
Definition hints5 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CC.CP 768332 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (0)); EVar 3; EVar 4; (EVar 32); (EVar 33); (EVar 34); EVar 8; EVar 9; (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 43); (EVar 44); (EVar 45); (EVar 46)]
  [KRange (EVar 2) (140735332483072) (140737488355328);
   KAlign (EVar 2) (16)]
  47 [] [] (ELit (1099511620736)).
Definition BL6 : CAD.blocks := [].
Definition hints6 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5; t6].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CAD.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 40%nat [2%nat; 4%nat] XSTOPS ASSUME CASES NAMEB RESPELL ECASES (CC.cp_F c) (CC.cp_meas c) h 4000 first false 2%nat
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CAD.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CAD.po_leaves o)) (CC.cp_meas c).
