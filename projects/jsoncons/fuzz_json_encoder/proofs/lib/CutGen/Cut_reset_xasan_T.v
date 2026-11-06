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
Definition ITR : list (Z * nat) := [(844500, 89%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 35.
Definition ENDS : list Z := [844784].
Definition HDECL : CH.hdecl := CH.HD (8288) (8224) [((EVar 10), (0), ELit 272); ((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 34); ((EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)), (2147450880), ELit 1); ((EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)), (2147450880), ELit 1)] [((EVar 10), (144), ELit 4); ((EVar 10), (160), ELit 8); ((EVar 10), (208), ELit 1); ((EVar 10), (211), ELit 2); ((EVar 10), (256), ELit 8)] [(1444792, 1448528)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880)].
Definition GLO : Z := 1444792.
Definition GHI : Z := 1448528.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 730684 4112 0%nat (fun _ _ => None) (fun _ => [((EAlu Instr.ALU_SRL (EVar 32) (ELit 3)), 2147450880, (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3)))]) (fun _ BL => BL) (fun _ _ _ BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880)], BLk)) (fun F => F)) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 841320 8240 0%nat (fun _ _ => None) (fun regs => [((nth 10 regs (ELit 0)), 0, ELit 24)]) (fun _ _ => []) (fun regs _ _ _ => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880)] ++ [KWord (SA (nth 10 regs (ELit 0)) 0) 8 (EVar 32); KWord (SA (nth 10 regs (ELit 0)) 8) 8 (EAlu Instr.ALU_ADD (EVar 32) (ELit 1)); KWord (SA (nth 10 regs (ELit 0)) 16) 8 (EAlu Instr.ALU_ADD (EVar 32) (EVar 34))], [((EVar 32), (EVar 34))])) (fun F => F)) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 526044 2560 0%nat (fun regs _ => Some (nth 10 regs (ELit 0))) (fun regs => [((nth 10 regs (ELit 0)), 0, (nth 12 regs (ELit 0)))]) (fun _ BL => BL) (fun _ _ _ BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880)], BLk)) (fun F => F)) (fun _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 844500 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (EVar 10) (248)) 8 (EVar 32);
   KWord (SA (EVar 10) (256)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWord (SA (EVar 10) (264)) 8 (APC.eadd (EVar 32) (EVar 34));
   KUnk (SA (EVar 10) (144)) (ELit (4));
   KUnk (SA (EVar 10) (160)) (ELit (8));
   KUnk (SA (EVar 10) (168)) (ELit (16));
   KUnk (SA (EVar 10) (208)) (ELit (1));
   KUnk (SA (EVar 10) (211)) (ELit (2));
   KUnk (SA (EVar 10) (256)) (ELit (8));
   KWr (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 10) (7077888) (140737488351232);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 32) (17594333495296) (140737479966720);
   KAlign (EVar 32) (16);
   KRange (EVar 33) (0) (4096);
   KRange (EVar 34) (1) (4096);
   KRange (APC.esub (EVar 34) (EVar 33)) (0) (4096);
   KUnk (SA (EVar 2) (-8288)) (ELit (8288));
   KWr (SA (EVar 2) (-8288)) (ELit (8288));
   KRange (EVar 2) (140735332491360) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8288)) (ELit (8288)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-8288)) (ELit (8288)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 32) (0)) (EVar 34);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 10) (0)) (ELit 272);
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit 1) (SA (EVar 10) (0)) (ELit 272);
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit 1) (SA (EVar 10) (0)) (ELit 272);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 34) (7)) (ELit 3))]
  35 [((EVar 2), (-8288), ELit 8288); ((EVar 10), (144), ELit 4); ((EVar 10), (160), ELit 8); ((EVar 10), (208), ELit 1); ((EVar 10), (211), ELit 2); ((EVar 10), (256), ELit 8)] [] (ELit (40)).
Definition BL0 : CA.blocks := [((EVar 32), (EVar 34))].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
