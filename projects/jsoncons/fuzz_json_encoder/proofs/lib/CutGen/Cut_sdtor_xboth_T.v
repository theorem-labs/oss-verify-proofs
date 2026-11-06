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
Definition ITR : list (Z * nat) := [(733456, 71%nat); (1078620, 1%nat); (1077872, 1%nat); (1076420, 54%nat); (1227348, 9%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 40.
Definition ENDS : list Z := [].
Definition HDECL : CH.hdecl := CH.HD (4224) (8224) [((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 74)] [((EVar 10), (0), ELit 592)] [(1433600, 1466368)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880)].
Definition GLO : Z := 1433600.
Definition GHI : Z := 1466368.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1046256 4096 0%nat (fun _ _ => None) (fun _ => []) (fun regs BL => List.filter (fun be => negb (expr_eqb (fst be) (nth 10 regs (ELit 0)))) BL) (fun _ _ _ BLk => ([KImg (1433600) (1466368); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)], BLk)) (fun F => F)) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 534160 4096 0%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ _ BLk => ([KImg (1433600) (1466368); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)], BLk)) (fun F => F)) (fun _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 733456 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1433600) (1466368);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 10) (32)) 8 (ELit (6948560));
   KWord (SA (EVar 10) (264)) 8 (EVar 32);
   KWord (SA (EVar 10) (272)) 8 (ELit (16384));
   KWord (SA (EVar 10) (136)) 8 (ELit (6948560));
   KWord (SA (EVar 10) (144)) 8 (ELit (0));
   KWord (SA (EVar 10) (152)) 8 (ELit (0));
   KWord (SA (EVar 10) (160)) 8 (ELit (0));
   KWord (SA (EVar 10) (176)) 8 (ELit (0));
   KWord (SA (EVar 10) (200)) 8 (ELit (0));
   KUnk (SA (EVar 10) (0)) (ELit (32));
   KUnk (SA (EVar 10) (88)) (ELit (8));
   KWr (SA (EVar 10) (0)) (ELit (592));
   KRange (EVar 10) (7094272) (140737488351232);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (74));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (592));
   KRange (EVar 32) (4096) (140737479966720);
   KAlign (EVar 32) (16);
   KUnk (SA (EVar 2) (-4224)) (ELit (4224));
   KWr (SA (EVar 2) (-4224)) (ELit (4224));
   KRange (EVar 2) (140735332487296) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-4224)) (ELit (4224)) (SA (EVar 10) (0)) (ELit (592));
   KDisj (SA (EVar 2) (-4224)) (ELit (4224)) (SA (EVar 32) (0)) (ELit (16384));
   KDisj (SA (EVar 10) (0)) (ELit (592)) (SA (EVar 32) (0)) (ELit (16384));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit 16384)]
  40 [((EVar 2), (-4224), ELit 4224); ((EVar 10), (0), ELit 592)] [] (ELit (12)).
Definition BL0 : CA.blocks := [((EVar 32), (ELit (16384)))].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 400 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
