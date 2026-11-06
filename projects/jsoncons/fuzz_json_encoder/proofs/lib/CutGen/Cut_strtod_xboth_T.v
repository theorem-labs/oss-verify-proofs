(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm5CutKitD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import StrtodAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutVFT.
Definition ITR : list (Z * nat) := [(1398624, 41%nat); (1380936, 14%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 34.
Definition ENDS : list Z := [1398780].
Definition CSUMS : list CAD.callsum := [(CAD.CSUM 1381192 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 8672 false false); (CAD.CSUM 1350012 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)].
Definition ASSUME : list (Z * (list expr -> list kentry -> list (list kentry * kentry))) := [].
Definition CASES : list (Z * list (nat * Z)) := [].
Definition RESPELL : list (Z * (list expr -> list kentry -> list (nat * expr))) := [].
Definition ECASES : list (Z * list ((list expr -> expr) * Z)) := [].
Definition NAMEB : list (Z * nat) := [].
Definition XSTOPS : list Z := [].
Definition HDECL : CH.hdecl := CH.HD (8944) (8224) [((EVar 10), (0), ((APC.eaddz (EVar 33) (1)))); ((ELit (0)), (7084240), ELit 8)] [((EVar 11), (0), ELit 8); ((EVar 4), (-164), ELit 4)] [(65536, 1466368)].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 1398624 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332492016) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (1466368);
   KWr (SA (EVar 2) (-8944)) (ELit (8944));
   KUnk (SA (EVar 2) (-8944)) (ELit (8944));
   KWord (SA (ELit (0)) (7084240)) 8 (EVar 32);
   KRange (EVar 10) (4096) (140737488355328);
   KRange (EVar 33) (1) (67108864);
   KWr (SA (EVar 11) (0)) (ELit (8));
   KUnk (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 2) (-8944)) (ELit (8944));
   KRange (EVar 11) (32) (140737488355320);
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (ELit (0)) (7084240)) (ELit (8));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 4) (-164)) (ELit (4));
   KDisj (SA (EVar 4) (-164)) (ELit (4)) (SA (EVar 2) (-8944)) (ELit (8944));
   KRange (EVar 4) (6953104) (6953105)]
  34 [((EVar 2), (-8944), ELit 8944); ((EVar 11), (0), ELit 8); ((EVar 4), (-164), ELit 4)] [] (ELit (1152921504606846976)).
Definition BL0 : CAD.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CAD.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] XSTOPS ASSUME CASES NAMEB RESPELL ECASES (CC.cp_F c) (CC.cp_meas c) h 400 first false 2%nat
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CAD.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CAD.po_leaves o)) (CC.cp_meas c).
