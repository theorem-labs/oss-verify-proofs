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
Definition ITR : list (Z * nat) := [(880092, 225%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [880716].
Definition HDECL : CH.hdecl := CH.HD (16896) (8224) [((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 34); ((EAlu Instr.ALU_SRL (EVar 12) (ELit 3)), (2147450880), ELit 2); ((EVar 11), (0), ELit 408); ((EVar 36), (0), ELit 24); ((EAlu Instr.ALU_SRL (EVar 11) (ELit 3)), (2147450880), ELit 51); ((EAlu Instr.ALU_SRL (EVar 36) (ELit 3)), (2147450880), ELit 3)] [((EVar 10), (0), ELit 272); ((EVar 12), (0), ELit 16)] [(1444792, 1448528); (1419712, 1421408)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880); (1482496, 4, 1)].
Definition GLO : Z := 1444792.
Definition GHI : Z := 1448528.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 417392 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1); KRange (EVar (g + 5)) 7077888 140737479966656; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 64); KWr (SA (EVar (g + 5)) 0) (ELit 64); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 64); KDisj (SA (EVar 2) (-16896)) (ELit 16896) (SA (EVar (g + 5)) 0) (ELit 64); KWord (SA (EVar (g + 5)) 56) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7077888 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 64) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-16896)) (ELit 16896) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 64) (SA (EVar 10) (0)) (ELit (272)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (0)) (ELit (272)); KDisj (SA (EVar (g + 5)) 0) (ELit 64) (SA (EVar 12) (0)) (ELit (16)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 12) (0)) (ELit (16)); KDisj (SA (EVar (g + 5)) 0) (ELit 64) (SA (EVar 11) (0)) (ELit (408)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 11) (0)) (ELit (408)); KDisj (SA (EVar (g + 5)) 0) (ELit 64) (SA (EVar 36) (0)) (ELit (24)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 36) (0)) (ELit (24)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit (34)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) (2147450880)) (ELit (2)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit (51)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) (2147450880)) (ELit (3)); KZero (SA (ELit 0) 2147628428) (ELit 1); KZero (SA (ELit 0) 2147628550) (ELit 1)], BLk)) (fun F => let g := 48%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 24); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 8)]))) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 841320 8240 2%nat (fun _ _ => None) (fun regs => [((EVar 10), 248, ELit 24)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [KZero (SA (ELit 0) 2147628428) (ELit 1); KZero (SA (ELit 0) 2147628550) (ELit 1)] ++ match CAX.cell_at cells (nth 18 regs (ELit 0)) 56 8 with Some fl => [KWord (SA (nth 18 regs (ELit 0)) 56) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [(EVar g, EVar (g + 1))])) (fun F => F)) (fun regs => [((nth 18 regs (ELit 0)), 0, -128)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 744592 16384 0%nat (fun regs g => Some (ELit 1)) (fun regs => [((EVar 11), 264, ELit 40); ((EVar 11), 400, ELit 4); ((EVar 36), 0, ELit 24); ((ELit 0), 6931848, ELit 72)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (nth 18 regs (ELit 0)) 56 8 with Some fl => [KWord (SA (nth 18 regs (ELit 0)) 56) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F ++ [((EVar 48), 0, ELit 1)])) (fun regs => [((nth 18 regs (ELit 0)), 0, -128)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 836392 16 0%nat (fun regs g => Some (ELit 0)) (fun regs => []) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (nth 18 regs (ELit 0)) 56 8 with Some fl => [KWord (SA (nth 18 regs (ELit 0)) 56) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun regs => [((nth 18 regs (ELit 0)), 0, -128)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 827600 1024 0%nat (fun _ _ => None) (fun regs => [((nth 10 regs (ELit 0)), 0, ELit 16); ((ELit 0), 6931840, ELit 2); ((ELit 0), 7069728, ELit 544)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (nth 18 regs (ELit 0)) 56 8 with Some fl => [KWord (SA (nth 18 regs (ELit 0)) 56) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F ++ [((EVar 48), 0, ELit 1)])) (fun regs => [((nth 18 regs (ELit 0)), 0, -128)]))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 880092 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KZero (SA (ELit 0) 2147628428) (ELit 1);
   KZero (SA (ELit 0) 2147628550) (ELit 1);
   KImg (1419712) (1421408);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 10) (8)) 4 (ELit (1024));
   KWord (SA (EVar 10) (96)) 8 (ELit (1421312));
   KWord (SA (EVar 10) (128)) 8 (APC.eaddz (EVar 10) (96));
   KWord (SA (EVar 10) (144)) 4 (EVar 34);
   KRange (EVar 34) (0) (1024);
   KWord (SA (EVar 10) (208)) 1 (EVar 35);
   KWord (SA (EVar 10) (211)) 1 (ELit (1));
   KWord (SA (EVar 10) (213)) 1 (ELit (0));
   KRange (EVar 10) (7077888) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 11) (0)) 8 (ELit (1420320));
   KRange (EVar 11) 7077888 140737479966312;
   KAlign (EVar 11) 8;
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (51));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (408));
   KRange (EVar 36) 7077888 140737479966696;
   KAlign (EVar 36) 8;
   KZero (SA (EAlu Instr.ALU_SRL (EVar 36) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-16896)) (ELit (16896)) (SA (EVar 11) (0)) (ELit (408));
   KDisj (SA (EVar 2) (-16896)) (ELit (16896)) (SA (EVar 36) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (408));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 36) (0)) (ELit (24));
   KDisj (SA (EVar 12) (0)) (ELit (16)) (SA (EVar 11) (0)) (ELit (408));
   KDisj (SA (EVar 12) (0)) (ELit (16)) (SA (EVar 36) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (408)) (SA (EVar 36) (0)) (ELit (24));
   KWord (SA (EVar 12) (0)) 4 (ELit (0));
   KWr (SA (EVar 12) (0)) (ELit (16));
   KRange (EVar 12) (7077888) (140737479966704);
   KAlign (EVar 12) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 12) (0)) (ELit (16));
   KUnk (SA (EVar 2) (-16896)) (ELit (16896));
   KWr (SA (EVar 2) (-16896)) (ELit (16896));
   KRange (EVar 2) (140735332499968) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-16896)) (ELit (16896)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-16896)) (ELit (16896)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (EVar 12) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 6931840) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 34) (SA (ELit 0) 7069728) (ELit 544)]
  48 [((EVar 2), (-16896), ELit 16896); ((EVar 10), (144), ELit 4); ((EVar 10), (208), ELit 1); ((EVar 10), (211), ELit 1)] [] (ELit (100)).
Definition BL0 : CA.blocks := [((EVar 32), (EVar 33))].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
