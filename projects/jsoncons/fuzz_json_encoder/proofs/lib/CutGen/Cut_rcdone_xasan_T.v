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
Definition ITR : list (Z * nat) := [(843556, 236%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 35.
Definition ENDS : list Z := [844344; 843960].
Definition HDECL : CH.hdecl := CH.HD (9920) (8224) [((EVar 10), (0), ELit 592); ((EVar 32), (0), ELit 272); ((EVar 11), (0), ELit 16); ((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 74); ((EAlu Instr.ALU_SRL (EVar 32) (ELit 3)), (2147450880), ELit 34); ((EAlu Instr.ALU_SRL (EVar 11) (ELit 3)), (2147450880), ELit 2)] [((EVar 10), (512), ELit 16)] [(1444792, 1448528); (1435760, 1435792)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880)].
Definition GLO : Z := 1444792.
Definition GHI : Z := 1448528.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 844856 8304 5%nat (fun _ g => Some (EVar g)) (fun regs => [((nth 10 regs (ELit 0)), 256, ELit 8); ((nth 10 regs (ELit 0)), 280, ELit 17); ((EVar 32), 40, ELit 8); ((EVar 32), 152, ELit 4); ((EVar 11), 0, ELit 16); ((ELit 0), 6931840, ELit 2); ((ELit 0), 7069728, ELit 544)]) (fun _ BL => firstn 2 BL) (fun regs _ g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KZero (SA (ELit 0) 2147630350) (ELit 1)] ++ [KWord (SA (nth 10 regs (ELit 0)) 288) 8 (ELit 0); KWord (SA (EVar 32) 40) 8 (EVar (g + 1)); KWord (SA (EVar 32) 152) 4 (EVar (g + 2)); KRange (EVar (g + 2)) 0 2; KUnk (SA (EVar 11) 0) (ELit 16); KWord (SA (EVar 11) 0) 4 (EVar (g + 3)); KRange (EVar (g + 3)) 0 31; KRange (EVar (g + 4)) 4 1099511627775], BLk ++ [((EVar 33), ELit 16384)])) (fun F => F)) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 913528 9792 8%nat (fun _ _ => None) (fun regs => [((nth 10 regs (ELit 0)), 0, ELit 272); ((EVar 11), 0, ELit 16); ((ELit 0), 6931840, ELit 2); ((ELit 0), 7069728, ELit 544)]) (fun _ BL => skipn 2 BL) (fun regs _ g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KZero (SA (ELit 0) 2147630350) (ELit 1)] ++ [KWord (SA (EVar 10) 512) 8 (EVar (g + 4)); KWord (SA (EVar 10) 520) 8 (EVar (g + 5)); KWr (SA (EVar 10) 512) (ELit 16); KUnk (SA (EVar 10) 512) (ELit 16); KRange (EVar (g + 4)) 0 140737488355327; KRange (EVar (g + 5)) 0 140737488355327; KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 74); KUnk (SA (EVar 11) 0) (ELit 16); KWord (SA (EVar 11) 0) 4 (EVar (g + 6)); KRange (EVar (g + 6)) 0 31; KRange (EVar (g + 7)) 4 1099511627775], [(EVar g, EVar (g + 1)); (EVar (g + 2), EVar (g + 3))] ++ BLk)) (fun F => F)) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 827600 1024 0%nat (fun regs _ => Some (nth 10 regs (ELit 0))) (fun regs => [((nth 10 regs (ELit 0)), 0, ELit 16); ((ELit 0), 6931840, ELit 2); ((ELit 0), 7069728, ELit 544)]) (fun _ BL => BL) (fun _ _ _ BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880)], BLk)) (fun F => F)) (fun _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 843556 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KZero (SA (ELit 0) 2147630350) (ELit 1);
   KImg (1435760) (1435792);
   KWord (SA (EVar 10) (240)) 8 (EVar 32);
   KWord (SA (EVar 10) (288)) 8 (ELit (0));
   KRange (EVar 10) (7077888) (140737488351232);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (74));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (592));
   KWr (SA (EVar 10) (512)) (ELit (16));
   KUnk (SA (EVar 10) (512)) (ELit (16));
   KWord (SA (EVar 32) (0)) 8 (ELit (1435784));
   KWord (SA (EVar 32) (40)) 8 (EVar 41);
   KWord (SA (EVar 32) (152)) 4 (EVar 42);
   KRange (EVar 42) (0) (2);
   KRange (EVar 32) (7077888) (140737488351232);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (272));
   KRange (EVar 11) (7077888) (140737488351232);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (2));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (16));
   KUnk (SA (EVar 11) (0)) (ELit (16));
   KWord (SA (EVar 10) (512)) 8 (EVar 40);
   KWord (SA (EVar 10) (520)) 8 (EVar 39);
   KRange (EVar 39) (0) (140737488355328);
   KRange (EVar 40) (0) (140737488355328);
   KRange (EVar 33) (4096) (140737479950336);
   KAlign (EVar 33) (16);
   KWr (SA (EVar 2) (-9920)) (ELit (9920));
   KRange (EVar 2) (140735332492992) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9920)) (ELit (9920)) (SA (EVar 10) (0)) (ELit (592));
   KDisj (SA (EVar 2) (-9920)) (ELit (9920)) (SA (EVar 32) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9920)) (ELit (9920)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (592)) (SA (EVar 32) (0)) (ELit (272));
   KDisj (SA (EVar 10) (0)) (ELit (592)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 32) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (ELit 0) 1435760) (ELit 32) (SA (EVar 32) (0)) (ELit 272);
   KDisj (SA (ELit 0) 1435760) (ELit 32) (SA (EVar 10) (0)) (ELit 592);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 74) (SA (EVar 11) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 74) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 74) (SA (ELit 0) 7069728) (ELit 544);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 11) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 7069728) (ELit 544);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 2) (SA (EVar 11) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 2) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 2) (SA (ELit 0) 7069728) (ELit 544);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 74) (SA (EVar 32) (0)) (ELit 272);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 32) (0)) (ELit 272);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 2) (SA (EVar 32) (0)) (ELit 272);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 74) (SA (EVar 10) (0)) (ELit 592);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 10) (0)) (ELit 592);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 2) (SA (EVar 10) (0)) (ELit 592);
   KUnk (SA (EVar 2) (-9920)) (ELit (9920));
   KRange (EVar 34) (4) (1099511627775)]
  43 [((EVar 2), (-9920), ELit 9920); ((EVar 10), (512), ELit 16)] [] (ELit (1099511627776)).
Definition BL0 : CA.blocks := [((EVar 35), (EVar 36)); ((EVar 37), (EVar 38)); ((EVar 33), (ELit (16384)))].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 843960 [EVar 0; (EVar 44); (APC.eaddz (EVar 2) (-128)); EVar 3; EVar 4; (EVar 45); (EVar 46); (EVar 47); (EVar 11); (APC.eaddz (EVar 10) (240)); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 10); (APC.eaddz (EVar 10) (288)); (APC.eaddz (EVar 10) (320)); (APC.eaddz (EVar 10) (520)); (APC.eaddz (EVar 10) (512)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (512)) (ELit 3)) (ELit 2147450880)); (ELit (2147450880)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (288)) (ELit 3)) (ELit 2147450880)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (ELit 2147450880)); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (520)) (ELit 3)) (ELit 2147450880)); (EVar 56); (EVar 57); (EVar 58); (EVar 59)]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KZero (SA (ELit 0) 2147630350) (ELit 1);
   KImg (1435760) (1435792);
   KWord (SA (EVar 10) (240)) 8 (EVar 32);
   KWord (SA (EVar 10) (288)) 8 (ELit (0));
   KRange (EVar 10) (7077888) (140737488351232);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (74));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (592));
   KWr (SA (EVar 10) (512)) (ELit (16));
   KUnk (SA (EVar 10) (512)) (ELit (16));
   KWord (SA (EVar 32) (0)) 8 (ELit (1435784));
   KWord (SA (EVar 32) (40)) 8 (EVar 41);
   KWord (SA (EVar 32) (152)) 4 (EVar 42);
   KRange (EVar 42) (0) (2);
   KRange (EVar 32) (7077888) (140737488351232);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (272));
   KRange (EVar 11) (7077888) (140737488351232);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (2));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (16));
   KUnk (SA (EVar 11) (0)) (ELit (16));
   KWord (SA (EVar 10) (512)) 8 (EVar 40);
   KWord (SA (EVar 10) (520)) 8 (EVar 39);
   KRange (EVar 39) (0) (140737488355328);
   KRange (EVar 40) (0) (140737488355328);
   KRange (EVar 33) (4096) (140737479950336);
   KAlign (EVar 33) (16);
   KWr (SA (EVar 2) (-9920)) (ELit (9920));
   KRange (EVar 2) (140735332492992) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-9920)) (ELit (9920)) (SA (EVar 10) (0)) (ELit (592));
   KDisj (SA (EVar 2) (-9920)) (ELit (9920)) (SA (EVar 32) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-9920)) (ELit (9920)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (592)) (SA (EVar 32) (0)) (ELit (272));
   KDisj (SA (EVar 10) (0)) (ELit (592)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (EVar 32) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (16));
   KDisj (SA (ELit 0) 1435760) (ELit 32) (SA (EVar 32) (0)) (ELit 272);
   KDisj (SA (ELit 0) 1435760) (ELit 32) (SA (EVar 10) (0)) (ELit 592);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 74) (SA (EVar 11) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 74) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 74) (SA (ELit 0) 7069728) (ELit 544);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 11) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 7069728) (ELit 544);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 2) (SA (EVar 11) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 2) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 2) (SA (ELit 0) 7069728) (ELit 544);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 74) (SA (EVar 32) (0)) (ELit 272);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 32) (0)) (ELit 272);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 2) (SA (EVar 32) (0)) (ELit 272);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 74) (SA (EVar 10) (0)) (ELit 592);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 10) (0)) (ELit 592);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 2) (SA (EVar 10) (0)) (ELit 592);
   KUnk (SA (EVar 2) (-9920)) (ELit (9800));
   KWord (SA (EVar 2) (-120)) 8 (ELit (3));
   KWord (SA (EVar 2) (-112)) 8 (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (240)) (ELit 3)) (ELit 2147450880));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-96)) 8 (EVar 26);
   KWord (SA (EVar 2) (-104)) 8 (EVar 27);
   KRange (EVar 43) (4) (1099511627775)]
  60 [((EVar 2), (-9920), ELit 9920); ((EVar 10), (512), ELit 16)] [] (EVar 43).
Definition BL1 : CA.blocks := [((EVar 35), (EVar 36)); ((EVar 37), (EVar 38)); ((EVar 33), (ELit (16384)))].
Definition hints1 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 800 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
