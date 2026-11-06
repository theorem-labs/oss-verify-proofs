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
Definition ITR : list (Z * nat) := [(904392, 81%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 40.
Definition ENDS : list Z := [904712; 904472; 904572; 904604].
Definition HDECL : CH.hdecl := CH.HD (64) (8224) [((EVar 10), (0), ((EVar 11))); ((EAlu Instr.ALU_SRL (EVar 12) (ELit 3)), (2147450880), ELit 1); ((EAlu Instr.ALU_SRL (EVar 32) (ELit 3)), (2147450880), ((EVar 33)))] [((EVar 12), (0), ELit 8)] [(1444792, 1448528); (65536, 66592); (154048, 166016)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880)].
Definition GLO : Z := 1444792.
Definition GHI : Z := 1448528.
Definition CSUMS : list CA.callsum := [].
Definition XSTOPS : list Z := [904472; 904572; 904604; 904464; 904476; 904576; 904608].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 904392 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KImg (65536) (66592);
   KImg (154048) (166016);
   KZero (SA (ELit 0) 2147471596) (ELit 32);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KUnk (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 12) (0)) (ELit (8));
   KRange (EVar 12) (4096) (140737488355320);
   KAlign (EVar 12) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 2) (-64)) (ELit (64));
   KRange (EVar 2) (140735332483136) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-64)) (ELit (64)) (SA (EVar 12) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-64)) (ELit (64)) (SA (EVar 10) (0)) (EVar 11);
   KUnk (SA (EVar 2) (-64)) (ELit (64))]
  40 [((EVar 2), (-64), ELit 64); ((EVar 12), (0), ELit 8)] [] (ELit (1073741824)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 904464 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-16)); EVar 3; EVar 4; (APC.esub (APC.esub (APC.eadd (EVar 10) (EVar 11)) (EVar 40)) (EVar 41)); (ELit (9)); (ELit (10)); EVar 8; EVar 9; EVar 10; (APC.esub (APC.eadd (EVar 10) (EVar 11)) (EVar 40)); EVar 12; (APC.eadd (EVar 40) (EVar 41)); (APC.esub (APC.esub (APC.eadd (EVar 10) (EVar 11)) (EVar 40)) (EVar 41)); (APC.eadd (EVar 10) (EVar 11)); (ELit (2147450880)); (EVar 42); EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 43); (EVar 44); EVar 30; EVar 31]
  [KRange (EVar 41) (1) (19);
   KRange (EVar 40) (0) (134217728);
   KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KImg (65536) (66592);
   KImg (154048) (166016);
   KZero (SA (ELit 0) 2147471596) (ELit 32);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KUnk (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 12) (0)) (ELit (8));
   KRange (EVar 12) (4096) (140737488355320);
   KAlign (EVar 12) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 2) (-64)) (ELit (64));
   KRange (EVar 2) (140735332483136) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-64)) (ELit (64)) (SA (EVar 12) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-64)) (ELit (64)) (SA (EVar 10) (0)) (EVar 11);
   KUnk (SA (EVar 2) (-64)) (ELit (48));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KUnk (SA (EVar 2) (-16)) (ELit (8));
   KRange (APC.esub (APC.esub (EVar 11) (EVar 40)) (EVar 41)) (0) (19);
   KRange (APC.esub (EVar 11) (EVar 40)) (1) (19)]
  45 [((EVar 2), (-64), ELit 64); ((EVar 12), (0), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 41)) (8)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 904476 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-16)); EVar 3; EVar 4; (APC.esub (APC.esub (APC.eadd (EVar 10) (EVar 11)) (EVar 40)) (EVar 41)); (ELit (9)); (ELit (10)); EVar 8; EVar 9; EVar 10; (APC.esub (APC.eadd (EVar 10) (EVar 11)) (EVar 40)); EVar 12; (APC.eadd (EVar 40) (EVar 41)); (APC.esub (APC.esub (APC.eadd (EVar 10) (EVar 11)) (EVar 40)) (EVar 41)); (APC.eadd (EVar 10) (EVar 11)); (ELit (2147450880)); (EVar 42); EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (ELit (0)); (EVar 44); EVar 30; EVar 31]
  [KRange (EVar 41) (1) (19);
   KRange (EVar 40) (0) (134217728);
   KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KImg (65536) (66592);
   KImg (154048) (166016);
   KZero (SA (ELit 0) 2147471596) (ELit 32);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KUnk (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 12) (0)) (ELit (8));
   KRange (EVar 12) (4096) (140737488355320);
   KAlign (EVar 12) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 2) (-64)) (ELit (64));
   KRange (EVar 2) (140735332483136) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-64)) (ELit (64)) (SA (EVar 12) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-64)) (ELit (64)) (SA (EVar 10) (0)) (EVar 11);
   KUnk (SA (EVar 2) (-64)) (ELit (48));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KUnk (SA (EVar 2) (-16)) (ELit (8));
   KRange (APC.esub (APC.esub (EVar 11) (EVar 40)) (EVar 41)) (0) (19);
   KRange (APC.esub (EVar 11) (EVar 40)) (1) (19);
   KRange (APC.eaddz (APC.escale (64) (EVar 41)) (8)) (0) (4611686018427387904)]
  45 [((EVar 2), (-64), ELit 64); ((EVar 12), (0), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 41)) (6)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 904576 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-16)); EVar 3; EVar 4; (APC.eaddz (APC.esub (APC.esub (APC.eadd (EVar 10) (EVar 11)) (EVar 40)) (EVar 41)) (1)); (ELit (1)); (ELit (10)); EVar 8; EVar 9; EVar 10; (ELit (34)); EVar 12; (ELit (0)); (APC.eaddz (APC.esub (APC.esub (APC.eadd (EVar 10) (EVar 11)) (EVar 40)) (EVar 41)) (1)); (APC.eadd (EVar 10) (EVar 11)); (ELit (2147450880)); (EVar 42); EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 43); (EVar 44); EVar 30; EVar 31]
  [KRange (EVar 41) (1) (1);
   KRange (EVar 40) (1) (1);
   KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KImg (65536) (66592);
   KImg (154048) (166016);
   KZero (SA (ELit 0) 2147471596) (ELit 32);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KUnk (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 12) (0)) (ELit (8));
   KRange (EVar 12) (4096) (140737488355320);
   KAlign (EVar 12) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 2) (-64)) (ELit (64));
   KRange (EVar 2) (140735332483136) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-64)) (ELit (64)) (SA (EVar 12) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-64)) (ELit (64)) (SA (EVar 10) (0)) (EVar 11);
   KUnk (SA (EVar 2) (-64)) (ELit (48));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KUnk (SA (EVar 2) (-16)) (ELit (8));
   KRange (APC.esub (APC.esub (EVar 11) (EVar 40)) (EVar 41)) (0) (19);
   KRange (APC.esub (EVar 11) (EVar 40)) (1) (19)]
  45 [((EVar 2), (-64), ELit 64); ((EVar 12), (0), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 41)) (4)).
Definition BL3 : CA.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 904608 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-16)); EVar 3; EVar 4; (APC.eaddz (APC.esub (APC.esub (APC.eadd (EVar 10) (EVar 11)) (EVar 40)) (EVar 41)) (1)); (ELit (0)); (ELit (10)); EVar 8; EVar 9; EVar 10; (ELit (34)); EVar 12; (APC.eaddz (EVar 45) (165728)); (EVar 45); (APC.eadd (EVar 10) (EVar 11)); (ELit (2147450880)); (EVar 42); EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 43); (EVar 44); EVar 30; EVar 31]
  [KRange (EVar 41) (1) (1);
   KRange (EVar 40) (1) (1);
   KRange (EVar 45) (0) (255);
   KWord (SA (APC.esub (APC.esub (APC.eadd (EVar 10) (EVar 11)) (EVar 40)) (EVar 41)) (1)) 1 (EVar 45);
   KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KImg (65536) (66592);
   KImg (154048) (166016);
   KZero (SA (ELit 0) 2147471596) (ELit 32);
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (0) (134217728);
   KRange (EVar 10) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 32) (4096) (140737488355328);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (EVar 33);
   KRange (EVar 33) (1) (17592186044416);
   KUnk (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 12) (0)) (ELit (8));
   KRange (EVar 12) (4096) (140737488355320);
   KAlign (EVar 12) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 2) (-64)) (ELit (64));
   KRange (EVar 2) (140735332483136) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-64)) (ELit (64)) (SA (EVar 12) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-64)) (ELit (64)) (SA (EVar 10) (0)) (EVar 11);
   KUnk (SA (EVar 2) (-64)) (ELit (48));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KUnk (SA (EVar 2) (-16)) (ELit (8));
   KRange (APC.esub (APC.esub (EVar 11) (EVar 40)) (EVar 41)) (0) (19);
   KRange (APC.esub (EVar 11) (EVar 40)) (1) (19)]
  46 [((EVar 2), (-64), ELit 64); ((EVar 12), (0), ELit 8)] [] (APC.eaddz (APC.escale (64) (EVar 41)) (2)).
Definition BL4 : CA.blocks := [].
Definition hints4 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [904480; 904580; 904612] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
