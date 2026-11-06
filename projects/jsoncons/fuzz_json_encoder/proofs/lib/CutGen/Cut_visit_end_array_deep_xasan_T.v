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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(737520, 339%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [738412].
Definition HDECL : CH.hdecl := CH.HD (13824) (8224) [((EVar 10), (0), ELit 272); ((EVar 10), (280), ELit 8); ((EVar 10), (304), ELit 96); ((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 51); ((EAlu Instr.ALU_SRL (EVar 32) (ELit 3)), (2147450880), ELit 3)] [((EVar 10), (272), ELit 8); ((EVar 10), (288), ELit 4); ((EVar 10), (296), ELit 8); ((EVar 10), (400), ELit 4); ((EVar 32), (0), ELit 24)] [(1444792, 1448528)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880); (1482496, 4, 1)].
Definition GLO : Z := 1444792.
Definition GHI : Z := 1448528.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 417764 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1); KRange (EVar (g + 5)) 7077888 140737479966592; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 128); KWr (SA (EVar (g + 5)) 0) (ELit 128); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 128); KDisj (SA (EVar 2) (-13824)) (ELit 13824) (SA (EVar (g + 5)) 0) (ELit 128); KWord (SA (EVar (g + 5)) 120) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7077888 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-13824)) (ELit 13824) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (0)) (ELit (272)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (0)) (ELit (272)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (280)) (ELit (8)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (280)) (ELit (8)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (304)) (ELit (96)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (304)) (ELit (96)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (272)) (ELit (8)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (272)) (ELit (8)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (288)) (ELit (4)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (288)) (ELit (4)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (296)) (ELit (8)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (296)) (ELit (8)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 10) (400)) (ELit (4)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (400)) (ELit (4)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 32) (0)) (ELit (24)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 32) (0)) (ELit (24)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit (51)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (ELit (3)); KDisj (SA (EVar (g + 5)) 0) (ELit 128) (SA (EVar 34) (0)) (EVar 35); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 34) (0)) (EVar 35); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 35) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-28)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-8)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 16) (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-40)) (ELit 3)) (2147450880)) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-28)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-8)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-40)) (ELit 3)) 2147450880) (ELit (1))], BLk)) (fun F => let g := 48%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 88); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 16)]))) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 763924 4560 0%nat (fun _ _ => None) (fun regs => [(ESA.col_region regs); ((EVar 32), 0, ELit 24)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-28)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-8)) (ELit 3)) 2147450880) (ELit (1)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-40)) (ELit 3)) 2147450880) (ELit (1))] ++ match CAX.cell_at cells (EVar 53) 120 8 with Some fl => [KWord (SA (EVar 53) 120) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun _ => [((EVar 53), 1, -160)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 763296 4112 0%nat (fun _ _ => None) (fun regs => [((EAlu Instr.ALU_SRL (EVar 34) (ELit 3)), 2147450880, (EAlu Instr.ALU_SRL (APC.eaddz (EVar 35) (7)) (ELit 3)))]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-40)) (ELit 3)) 2147450880) (ELit (1))] ++ match CAX.cell_at cells (EVar 53) 120 8 with Some fl => [KWord (SA (EVar 53) 120) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun _ => [((EVar 53), 1, -160)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1040708 4368 0%nat (fun _ _ => None) (fun regs => [((EVar 32), 0, ELit 24)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-40)) (ELit 3)) 2147450880) (ELit (1))] ++ match CAX.cell_at cells (EVar 53) 120 8 with Some fl => [KWord (SA (EVar 53) 120) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F ++ [((EVar 48), 0, ELit 1)])) (fun _ => [((EVar 53), 1, -160)]))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 737520 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (36)) 1 (ELit (4));
   KWord (SA (EVar 10) (288)) 4 (APC.escale (4) (EVar 33));
   KWord (SA (EVar 10) (400)) 4 (EVar 33);
   KWr (SA (EVar 10) (288)) (ELit (4));
   KWr (SA (EVar 10) (400)) (ELit (4));
   KWr (SA (EVar 10) (272)) (ELit (8));
   KWord (SA (EVar 10) (296)) 8 (EVar 37);
   KRange (EVar 37) (0) (18446744073709551615);
   KWr (SA (EVar 10) (296)) (ELit (8));
   KWord (SA (EVar 10) (384)) 8 (ELit (150319));
   KWord (SA (EVar 10) (392)) 8 (ELit (1));
   KRange (EVar 10) (7077888) (140737479966312);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (51));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (408));
   KRange (EVar 32) (7077888) (140737479966696);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-13824)) (ELit (13824)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EVar 2) (-13824)) (ELit (13824)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-13824)) (ELit (13824));
   KWr (SA (EVar 2) (-13824)) (ELit (13824));
   KRange (EVar 2) (140735332496896) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-13824)) (ELit (13824));
   KWord (SA (EVar 10) (264)) 8 (EVar 34);
   KWord (SA (EVar 10) (272)) 8 (APC.eadd (EVar 34) (APC.escale (32) (EVar 33)));
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) 4 (EVar 38);
   KRange (EVar 38) (0) (1);
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-28)) 1 (ELit (0));
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-27)) 1 (EVar 39);
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) 1 (EVar 40);
   KRange (EVar 40) (0) (1);
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-8)) 8 (EVar 36);
   KUnk (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) (ELit (32));
   KRange (APC.esub (EVar 35) (APC.escale (32) (EVar 33))) (0) (32768);
   KRange (EVar 35) (32) (32768);
   KRange (EVar 34) (4096) (140737479966688);
   KAlign (EVar 34) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 34) (0)) (EVar 35);
   KRange (EVar 36) (0) (18446744073709551615);
   KDisj (SA (EVar 2) (-13824)) (ELit (13824)) (SA (EVar 34) (0)) (EVar 35);
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 34) (0)) (EVar 35);
   KDisj (SA (EVar 32) (0)) (ELit (24)) (SA (EVar 34) (0)) (EVar 35);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 35) (7)) (ELit 3)) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit 51);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 35) (7)) (ELit 3)) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 3);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-32)) (ELit 3)) 2147450880) (ELit (1));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-28)) (ELit 3)) 2147450880) (ELit (1));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-26)) (ELit 3)) 2147450880) (ELit (1));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-8)) (ELit 3)) 2147450880) (ELit (1));
   KRange (EVar 33) (2) (1024);
   KWord (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-40)) 8 (EVar 41);
   KRange (EVar 41) (0) (18446744073709551615);
   KWr (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-40)) (ELit (8));
   KUnk (SA (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-64)) (ELit (32));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 34) (APC.escale (32) (EVar 33))) (-40)) (ELit 3)) 2147450880) (ELit (1))]
  48 [((EVar 2), (-13824), ELit 13824); ((EVar 10), (272), ELit 8); ((EVar 10), (288), ELit 4); ((EVar 10), (296), ELit 8); ((EVar 10), (400), ELit 4); ((APC.eadd (EVar 34) (APC.escale (32) (EVar 33))), (-40), ELit 8)] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [((EVar 34), (EVar 35))].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 1500 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
