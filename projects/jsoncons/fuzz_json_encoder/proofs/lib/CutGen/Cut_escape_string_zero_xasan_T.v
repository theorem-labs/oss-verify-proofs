(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA EncSums3A.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(777944, 437%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [779328].
Definition HDECL : CH.hdecl := CH.HD (4528) (8224) [((EVar 14), (0), ELit 8); ((EAlu Instr.ALU_SRL (EVar 14) (ELit 3)), (2147450880), ELit 1); ((EAlu Instr.ALU_SRL (EVar 32) (ELit 3)), (2147450880), ELit 3); ((EAlu Instr.ALU_SRL (EVar 33) (ELit 3)), (2147450880), ((EVar 34)))] [((EVar 32), (0), ELit 24)] [(1444792, 1448528); (65536, 1449984)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880)].
Definition GLO : Z := 1444792.
Definition GHI : Z := 1448528.
Definition CSUMS : list CA.callsum := [].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 777944 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KImg (65536) (1449984);
   KWord (SA (EVar 14) (0)) 8 (EVar 32);
   KRange (EVar 12) (0) (0);
   KRange (EVar 13) (0) (0);
   KRange (EVar 14) (7077888) (140737488355320);
   KAlign (EVar 14) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 14) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 14) (0)) (ELit (8));
   KRange (EVar 32) (7077888) (140737479966696);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-4528)) (ELit (4368));
   KWr (SA (EVar 2) (-4528)) (ELit (4528));
   KRange (EVar 2) (140735332487600) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4528)) (ELit (4528));
   KDisj (SA (EVar 2) (-4528)) (ELit (4528)) (SA (EVar 14) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4528)) (ELit (4528)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 14) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KRange (EVar 33) (4096) (140737479966720);
   KAlign (EVar 33) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (EVar 34);
   KRange (EVar 34) (1) (17592186044416);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) (2147450880)) (EVar 34) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) (2147450880)) (EVar 34) (SA (EVar 2) (-4528)) (ELit (4528));
   KRange (EVar 11) (0) (0);
   KUnk (SA (EVar 2) (-144)) (ELit (144))]
  48 [((EVar 2), (-4528), ELit 4528)] [] (ELit (4611686018427387904)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 700 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
