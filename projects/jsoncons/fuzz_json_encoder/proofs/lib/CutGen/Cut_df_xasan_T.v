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
Definition ITR : list (Z * nat) := [(826584, 254%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [827572].
Definition HDECL : CH.hdecl := CH.HD (12416) (8224) [((EVar 11), (0), ELit 8); ((EAlu Instr.ALU_SRL (EVar 11) (ELit 3)), (2147450880), ELit 1)] [((EVar 32), (0), ELit 24)] [(1444792, 1448528)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880); (1482496, 4, 1)].
Definition GLO : Z := 1444792.
Definition GHI : Z := 1448528.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 418164 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1); KRange (EVar (g + 5)) 7077888 140737479966464; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 256); KWr (SA (EVar (g + 5)) 0) (ELit 256); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 32); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 32); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 256); KDisj (SA (EVar 2) (-12416)) (ELit 12416) (SA (EVar (g + 5)) 0) (ELit 256); KWord (SA (EVar (g + 5)) 248) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7077888 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 256) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-12416)) (ELit 12416) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 256) (SA (EVar 11) (0)) (ELit (8)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 11) (0)) (ELit (8)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 32) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EVar (g + 5)) 0) (ELit 256) (SA (EVar 32) (0)) (ELit (24)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 32) (0)) (ELit (24))], BLk)) (fun F => let g := 49%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 216); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 32)]))) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 440684 12288 0%nat (fun _ _ => None) (fun regs => [((nth 10 regs (ELit 0)), 0, ELit 100)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [KRange (EVar (g + 4)) 1 25; KUnk (SA (nth 10 regs (ELit 0)) 0) (ELit 100)] ++ match CAX.cell_at cells (nth 18 regs (ELit 0)) 248 8 with Some fl => [KWord (SA (nth 18 regs (ELit 0)) 248) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => List.filter (fun r : expr * Z * expr => negb (expr_eqb (fst (fst r)) (EVar 54) && Z.eqb (snd (fst r)) 32)%bool) F)) (fun regs => [((nth 18 regs (ELit 0)), 2, -128)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 824664 9120 0%nat (fun _ _ => None) (fun regs => [((EVar 2), -104, ELit 8); ((ELit 0), 6938412, ELit 4)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [KRange (EVar (g + 5)) 0 34; KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EVar (g + 5)) (ELit 22)) (ELit 1)) 0 0] ++ match CAX.cell_at cells (nth 18 regs (ELit 0)) 248 8 with Some fl => [KWord (SA (nth 18 regs (ELit 0)) 248) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun regs => [((nth 18 regs (ELit 0)), 2, -128)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 815348 4480 0%nat (fun _ _ => None) (fun regs => [((EVar 32), 0, ELit 24)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (nth 18 regs (ELit 0)) 248 8 with Some fl => [KWord (SA (nth 18 regs (ELit 0)) 248) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun regs => [((nth 18 regs (ELit 0)), 2, -128)])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1041292 4368 0%nat (fun _ _ => None) (fun regs => [((EVar 32), 0, ELit 24)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1444792) (1448528); KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880); KWord (SA (ELit 0) 1482496) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (nth 18 regs (ELit 0)) 248 8 with Some fl => [KWord (SA (nth 18 regs (ELit 0)) 248) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun regs => [((nth 18 regs (ELit 0)), 2, -128)])); CA.cs_inline 826684 4 []; CA.cs_inline 826804 4 []; CA.cs_inline 826828 4 [12%nat]; CA.cs_inline 827052 4 [22%nat]; CA.cs_inline 827136 4 [10%nat]].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 826584 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (EVar 11); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KRange (EVar 10) (0) (255);
   KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 11) (7077888) (140737488355320);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (8));
   KRange (EVar 32) (7077888) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-12416)) (ELit (12416));
   KWr (SA (EVar 2) (-12416)) (ELit (12416));
   KRange (EVar 2) (140735332495488) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-12416)) (ELit (12416));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 32) (0)) (ELit (24))]
  48 [((EVar 2), (-12416), ELit 12416)] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 826992 [EVar 0; (EVar 70); (APC.eaddz (EVar 2) (-128)); EVar 3; EVar 4; (EVar 71); (EVar 72); (EVar 73); (EVar 2); (APC.eaddz (EVar 2) (-128)); (EVar 74); (EVar 75); (EVar 76); (EVar 77); (EVar 78); (EVar 79); (EVar 80); (EVar 81); (EVar 54); (EVar 11); (EVar 10); (ELit (2147450880)); EVar 22; EVar 23; (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) (ELit 2147450880)); (EVar 54); EVar 26; EVar 27; (EVar 82); (EVar 83); (EVar 84); (EVar 85)]
  [KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450881) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450882) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450883) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450884) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450885) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450886) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450887) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450888) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450889) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450890) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450891) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450892) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450893) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450894) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450895) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450896) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450897) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450898) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450899) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450900) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450901) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450902) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450903) 1 (ELit (18446744073709551603));
   KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KWord (SA (EVar 54) (16)) 8 (ELit (826584));
   KWord (SA (EVar 54) (8)) 8 (ELit (122929));
   KWord (SA (EVar 54) (0)) 8 (ELit (1102416563));
   KWord (SA (EVar 2) (-112)) 8 (EVar 54);
   KRange (EVar 54) (7077888) (140737479966464);
   KAlign (EVar 54) (64);
   KUnk (SA (EVar 54) (24)) (ELit (232));
   KWr (SA (EVar 54) (0)) (ELit (256));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450904) (ELit 8);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) (ELit 32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 54) (0)) (ELit (256));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 54) (0)) (ELit (256));
   KWord (SA (EVar 54) (248)) 8 (EVar 49);
   KWr (SA (EVar 49) (0)) (ELit (1));
   KRange (EVar 49) (7077888) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 49) (0)) (ELit (1)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) (ELit 32) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 1);
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 49) (0)) (ELit (1)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 2) (-96)) 8 (EVar 48);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-128)) 8 (ELit (0));
   KRange (EVar 10) (0) (255);
   KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 11) (7077888) (140737488355320);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (8));
   KRange (EVar 32) (7077888) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-12416)) (ELit (12288));
   KUnk (SA (EVar 2) (-120)) (ELit (8));
   KUnk (SA (EVar 2) (-104)) (ELit (8));
   KWr (SA (EVar 2) (-12416)) (ELit (12416));
   KRange (EVar 2) (140735332495488) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-12416)) (ELit (12416));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 32) (0)) (ELit (24))]
  86 [((EVar 2), (-12416), ELit 12416); ((EVar 54), (0), ELit 24); ((EVar 54), (32), ELit 216); ((EAlu Instr.ALU_SRL (EVar 54) (ELit 3)), (2147450880), ELit 32)] [] (ELit (524288)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 826916 [EVar 0; (EVar 70); (APC.eaddz (EVar 2) (-128)); EVar 3; EVar 4; (EVar 71); (EVar 72); (EVar 73); (EVar 2); (APC.eaddz (EVar 2) (-128)); (EVar 74); (EVar 75); (EVar 76); (EVar 77); (EVar 78); (EVar 79); (EVar 80); (EVar 81); (EVar 54); (EVar 11); (EVar 10); (ELit (2147450880)); EVar 22; EVar 23; (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) (ELit 2147450880)); (EVar 54); EVar 26; EVar 27; (EVar 82); (EVar 83); (EVar 84); (EVar 85)]
  [KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450881) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450882) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450883) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450884) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450885) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450886) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450887) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450888) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450889) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450890) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450891) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450892) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450893) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450894) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450895) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450896) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450897) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450898) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450899) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450900) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450901) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450902) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450903) 1 (ELit (18446744073709551603));
   KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KWord (SA (EVar 54) (16)) 8 (ELit (826584));
   KWord (SA (EVar 54) (8)) 8 (ELit (122929));
   KWord (SA (EVar 54) (0)) 8 (ELit (1102416563));
   KWord (SA (EVar 2) (-112)) 8 (EVar 54);
   KRange (EVar 54) (7077888) (140737479966464);
   KAlign (EVar 54) (64);
   KUnk (SA (EVar 54) (24)) (ELit (232));
   KWr (SA (EVar 54) (0)) (ELit (256));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450904) (ELit 8);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) (ELit 32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 54) (0)) (ELit (256));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 54) (0)) (ELit (256));
   KWord (SA (EVar 54) (248)) 8 (EVar 49);
   KWr (SA (EVar 49) (0)) (ELit (1));
   KRange (EVar 49) (7077888) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 49) (0)) (ELit (1)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) (ELit 32) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 1);
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 49) (0)) (ELit (1)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 2) (-96)) 8 (EVar 48);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-128)) 8 (ELit (0));
   KRange (EVar 10) (0) (255);
   KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 11) (7077888) (140737488355320);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (8));
   KRange (EVar 32) (7077888) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-12416)) (ELit (12288));
   KUnk (SA (EVar 2) (-120)) (ELit (8));
   KUnk (SA (EVar 2) (-104)) (ELit (8));
   KWr (SA (EVar 2) (-12416)) (ELit (12416));
   KRange (EVar 2) (140735332495488) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-12416)) (ELit (12416));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 32) (0)) (ELit (24))]
  86 [((EVar 2), (-12416), ELit 12416); ((EVar 54), (0), ELit 24); ((EVar 54), (32), ELit 216); ((EAlu Instr.ALU_SRL (EVar 54) (ELit 3)), (2147450880), ELit 32)] [] (ELit (524289)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 827144 [EVar 0; (EVar 70); (APC.eaddz (EVar 2) (-128)); EVar 3; EVar 4; (EVar 71); (EVar 72); (EVar 73); (EVar 2); (APC.eaddz (EVar 2) (-128)); (EVar 74); (EVar 75); (EVar 76); (EVar 77); (EVar 78); (EVar 79); (EVar 80); (EVar 81); (EVar 54); (EVar 11); (EVar 10); (APC.eaddz (EVar 54) (32)); (EVar 87); (EVar 86); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) (ELit 2147450880)); (EVar 54); EVar 26; EVar 27; (EVar 82); (EVar 83); (EVar 84); (EVar 85)]
  [KRange (EVar 86) (1) (25);
   KUnk (SA (APC.eaddz (EVar 54) (32)) (0)) (ELit (100));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450881) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450882) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450883) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450884) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450885) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450886) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450887) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450888) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450889) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450890) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450891) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450892) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450893) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450894) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450895) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450896) 1 (ELit (4));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450897) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450898) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450899) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450900) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450901) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450902) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450903) 1 (ELit (18446744073709551603));
   KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KWord (SA (EVar 54) (16)) 8 (ELit (826584));
   KWord (SA (EVar 54) (8)) 8 (ELit (122929));
   KWord (SA (EVar 54) (0)) 8 (ELit (1102416563));
   KWord (SA (EVar 2) (-112)) 8 (EVar 54);
   KRange (EVar 54) (7077888) (140737479966464);
   KAlign (EVar 54) (64);
   KUnk (SA (EVar 54) (24)) (ELit (232));
   KWr (SA (EVar 54) (0)) (ELit (256));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450904) (ELit 8);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) (ELit 32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 54) (0)) (ELit (256));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 54) (0)) (ELit (256));
   KWord (SA (EVar 54) (248)) 8 (EVar 49);
   KWr (SA (EVar 49) (0)) (ELit (1));
   KRange (EVar 49) (7077888) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 49) (0)) (ELit (1)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) (ELit 32) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 1);
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 49) (0)) (ELit (1)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 2) (-96)) 8 (EVar 48);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-128)) 8 (ELit (0));
   KRange (EVar 10) (0) (255);
   KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 11) (7077888) (140737488355320);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (8));
   KRange (EVar 32) (7077888) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-12416)) (ELit (12288));
   KUnk (SA (EVar 2) (-120)) (ELit (8));
   KWr (SA (EVar 2) (-12416)) (ELit (12416));
   KRange (EVar 2) (140735332495488) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-12416)) (ELit (12416));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 32) (0)) (ELit (24))]
  88 [((EVar 2), (-12416), ELit 12416); ((EVar 54), (0), ELit 24); ((EVar 54), (32), ELit 216); ((EAlu Instr.ALU_SRL (EVar 54) (ELit 3)), (2147450880), ELit 32)] [] (ELit (262144)).
Definition BL3 : CA.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 827180 [EVar 0; (EVar 70); (APC.eaddz (EVar 2) (-128)); EVar 3; EVar 4; (EVar 71); (EVar 72); (EVar 73); (EVar 2); (APC.eaddz (EVar 2) (-128)); (EVar 74); (EVar 75); (EVar 76); (EVar 77); (EVar 78); (EVar 79); (EVar 80); (EVar 81); (EVar 54); (EVar 11); (EVar 10); (APC.eaddz (EVar 54) (32)); (EVar 87); (EVar 86); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) (ELit 2147450880)); (EVar 54); EVar 26; EVar 27; (EVar 82); (EVar 83); (EVar 84); (EVar 85)]
  [KRange (EVar 86) (1) (25);
   KUnk (SA (APC.eaddz (EVar 54) (32)) (0)) (ELit (100));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450881) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450882) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450883) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450884) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450885) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450886) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450887) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450888) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450889) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450890) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450891) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450892) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450893) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450894) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450895) 1 (ELit (0));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450896) 1 (ELit (4));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450897) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450898) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450899) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450900) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450901) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450902) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450903) 1 (ELit (18446744073709551603));
   KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KWord (SA (EVar 54) (16)) 8 (ELit (826584));
   KWord (SA (EVar 54) (8)) 8 (ELit (122929));
   KWord (SA (EVar 54) (0)) 8 (ELit (1102416563));
   KWord (SA (EVar 2) (-112)) 8 (EVar 54);
   KRange (EVar 54) (7077888) (140737479966464);
   KAlign (EVar 54) (64);
   KUnk (SA (EVar 54) (24)) (ELit (232));
   KWr (SA (EVar 54) (0)) (ELit (256));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450904) (ELit 8);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) (ELit 32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 54) (0)) (ELit (256));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 54) (0)) (ELit (256));
   KWord (SA (EVar 54) (248)) 8 (EVar 49);
   KWr (SA (EVar 49) (0)) (ELit (1));
   KRange (EVar 49) (7077888) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 49) (0)) (ELit (1)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) (ELit 32) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 1);
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 49) (0)) (ELit (1)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 2) (-96)) 8 (EVar 48);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-128)) 8 (ELit (0));
   KRange (EVar 10) (0) (255);
   KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 11) (7077888) (140737488355320);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (8));
   KRange (EVar 32) (7077888) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-12416)) (ELit (12288));
   KUnk (SA (EVar 2) (-120)) (ELit (8));
   KWr (SA (EVar 2) (-12416)) (ELit (12416));
   KRange (EVar 2) (140735332495488) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-12416)) (ELit (12416));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 32) (0)) (ELit (24))]
  88 [((EVar 2), (-12416), ELit 12416); ((EVar 54), (0), ELit 24); ((EVar 54), (32), ELit 216); ((EAlu Instr.ALU_SRL (EVar 54) (ELit 3)), (2147450880), ELit 32)] [] (ELit (131072)).
Definition BL4 : CA.blocks := [].
Definition hints4 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 827260 [EVar 0; (EVar 70); (APC.eaddz (EVar 2) (-128)); EVar 3; EVar 4; (EVar 71); (EVar 72); (EVar 73); (EVar 2); (APC.eaddz (EVar 2) (-128)); (ELit (1)); (EVar 75); (EVar 76); (EVar 77); (EVar 78); (EVar 79); (EVar 80); (EVar 81); (EVar 54); (EVar 11); (EVar 10); (EVar 86); (EVar 87); (EVar 88); (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) (ELit 2147450880)); (EVar 54); EVar 26; EVar 27; (EVar 82); (EVar 83); (EVar 84); (EVar 85)]
  [KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450881) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450882) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450883) 1 (ELit (18446744073709551601));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450884) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450885) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450886) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450887) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450888) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450889) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450890) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450891) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450892) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450893) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450894) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450895) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450896) 1 (ELit (18446744073709551608));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450897) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450898) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450899) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450900) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450901) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450902) 1 (ELit (18446744073709551603));
   KWord (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450903) 1 (ELit (18446744073709551603));
   KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1482496) 4 (ELit 1);
   KWord (SA (EVar 54) (16)) 8 (ELit (826584));
   KWord (SA (EVar 54) (8)) 8 (ELit (122929));
   KWord (SA (EVar 54) (0)) 8 (ELit (1102416563));
   KWord (SA (EVar 2) (-112)) 8 (EVar 54);
   KRange (EVar 54) (7077888) (140737479966464);
   KAlign (EVar 54) (64);
   KUnk (SA (EVar 54) (24)) (ELit (232));
   KWr (SA (EVar 54) (0)) (ELit (256));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450904) (ELit 8);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) (ELit 32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 54) (0)) (ELit (256));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 54) (0)) (ELit (256));
   KWord (SA (EVar 54) (248)) 8 (EVar 49);
   KWr (SA (EVar 49) (0)) (ELit (1));
   KRange (EVar 49) (7077888) (140737479966719);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 49) (0)) (ELit (1));
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 49) (0)) (ELit (1)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 54) (ELit 3)) 2147450880) (ELit 32) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit 1);
   KDisj (SA (EVar 54) (0)) (ELit (256)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 49) (0)) (ELit (1)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 2) (-96)) 8 (EVar 48);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-128)) 8 (ELit (0));
   KRange (EVar 10) (0) (255);
   KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 11) (7077888) (140737488355320);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (8));
   KRange (EVar 32) (7077888) (140737479966696);
   KAlign (EVar 32) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-12416)) (ELit (12288));
   KWr (SA (EVar 2) (-12416)) (ELit (12416));
   KRange (EVar 2) (140735332495488) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-12416)) (ELit (12416));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-12416)) (ELit (12416)) (SA (EVar 32) (0)) (ELit (24))]
  89 [((EVar 2), (-12416), ELit 12416); ((EVar 54), (0), ELit 24); ((EVar 54), (32), ELit 216); ((EAlu Instr.ALU_SRL (EVar 54) (ELit 3)), (2147450880), ELit 32); ((EVar 49), (0), ELit 1)] [] (ELit (65536)).
Definition BL5 : CA.blocks := [].
Definition hints5 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 3000 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
