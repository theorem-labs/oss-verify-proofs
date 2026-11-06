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
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(1040708, 63%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 40.
Definition ENDS : list Z := [1040956].
Definition HDECL : CH.hdecl := CH.HD (4368) (8224) [((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 3)] [((EVar 10), (0), ELit 24)] [(1417216, 1449984)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880)].
Definition GLO : Z := 1417216.
Definition GHI : Z := 1449984.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 524856 2560 0%nat (fun regs _ => Some (nth 10 regs (ELit 0))) (fun regs => [((nth 10 regs (ELit 0)), 0, (nth 12 regs (ELit 0)))]) (fun _ BL => BL) (fun regs _ _ BLk => ([KImg (1417216) (1449984); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880)] ++ [KBlob (SA (nth 10 regs (ELit 0)) 0) (nth 12 regs (ELit 0)) 1], BLk)) (fun F => F)) (fun _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 1040708 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1417216) (1449984);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (EVar 10) (0)) 1 (APC.escale (2) (EVar 32));
   KWord (SA (EVar 10) (0)) 8 (APC.eadd (APC.escale (2) (EVar 32)) (APC.escale (256) (EVar 33)));
   KRange (EVar 32) (0) (22);
   KRange (EVar 33) (0) (72057594037927935);
   KRange (EVar 12) (1) (22);
   KRange (APC.eadd (EVar 32) (EVar 12)) (1) (22);
   KBlob (SA (EVar 10) (1)) (EVar 32) 0;
   KUnk (SA (EVar 10) (0)) (ELit (24));
   KWr (SA (EVar 10) (0)) (ELit (24));
   KRange (EVar 10) (7077888) (140737488351232);
   KAlign (EVar 10) (8);
   KUnk (SA (EVar 2) (-4368)) (ELit (4368));
   KWr (SA (EVar 2) (-4368)) (ELit (4368));
   KRange (EVar 2) (140735332487440) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-4368)) (ELit (4368)) (SA (EVar 10) (0)) (ELit (24))]
  40 [((EVar 2), (-4368), ELit 4368); ((EVar 10), (0), ELit 24)] [] (ELit (100)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 800 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
