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
Definition ITR : list (Z * nat) := [(731512, 157%nat); (852440, 1%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 40.
Definition ENDS : list Z := [732012].
Definition HDECL : CH.hdecl := CH.HD (4272) (8224) [((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 34); ((EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-32)) (ELit 3)), (2147450880), ELit 1)] [((EVar 10), (0), ELit 272)] [(1433600, 1466368)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880)].
Definition GLO : Z := 1433600.
Definition GHI : Z := 1466368.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 732544 4192 0%nat (fun _ _ => None) (fun regs => [((EVar 10), 248, ELit 24)]) (fun regs BL => List.filter (fun be => negb (expr_eqb (fst be) (EVar 32))) BL) (fun _ _ _ BLk => ([KImg (1433600) (1466368); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)], BLk)) (fun F => F)) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1046256 4096 0%nat (fun _ _ => None) (fun _ => []) (fun regs BL => List.filter (fun be => negb (expr_eqb (fst be) (nth 10 regs (ELit 0)))) BL) (fun _ _ _ BLk => ([KImg (1433600) (1466368); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)] ++ [KWord (SA (ELit 0) 2147630408) 1 (ELit 0)], BLk)) (fun F => F)) (fun _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 731512 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1433600) (1466368);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 10) (24)) 1 (ELit (0));
   KWord (SA (EVar 10) (48)) 1 (ELit (0));
   KWord (SA (EVar 10) (72)) 1 (ELit (0));
   KWord (SA (EVar 10) (96)) 8 (ELit (1436192));
   KWord (SA (EVar 10) (128)) 8 (APC.eaddz (EVar 10) (96));
   KWord (SA (EVar 10) (224)) 8 (EVar 36);
   KWord (SA (EVar 10) (240)) 8 (EVar 35);
   KRange (EAlu Instr.ALU_AND (EExt false 0%nat 1%nat (EVar 36)) (ELit 1)) (1) (1);
   KRange (EVar 36) (265) (140737488355328);
   KWord (SA (EVar 10) (248)) 8 (EVar 32);
   KWord (SA (EVar 10) (256)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (264)) 8 (APC.eadd (EVar 32) (EVar 34));
   KUnk (SA (EVar 10) (0)) (ELit (24));
   KUnk (SA (EVar 10) (232)) (ELit (8));
   KWr (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 10) (1048576) (140737488351232);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 32) (17594333495296) (140737479966720);
   KAlign (EVar 32) (16);
   KRange (EVar 34) (1) (4096);
   KRange (EVar 33) (0) (4096);
   KRange (APC.esub (EVar 34) (EVar 33)) (0) (4096);
   KRange (EVar 35) (4096) (140737479966720);
   KAlign (EVar 35) (16);
   KUnk (SA (EVar 2) (-4272)) (ELit (4272));
   KWr (SA (EVar 2) (-4272)) (ELit (4272));
   KRange (EVar 2) (140735332487344) (140737488355328);
   KAlign (EVar 2) (16);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 2) (-32)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (EVar 2) (-4272)) (ELit (4272)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-4272)) (ELit (4272)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 2) (-4272)) (ELit (4272)) (SA (EVar 35) (0)) (APC.eaddz (EVar 36) (-1));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 35) (0)) (APC.eaddz (EVar 36) (-1));
   KDisj (SA (EVar 32) (0)) (EVar 34) (SA (EVar 35) (0)) (APC.eaddz (EVar 36) (-1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 35) (0)) (APC.eaddz (EVar 36) (-1))]
  40 [((EVar 2), (-4272), ELit 4272); ((EVar 10), (0), ELit 272)] [] (ELit (10)).
Definition BL0 : CA.blocks := [((EVar 35), (APC.eaddz (EVar 36) (-1))); ((EVar 32), (EVar 34))].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 300 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
