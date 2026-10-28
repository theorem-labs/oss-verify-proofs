(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import FmodlAssume.
Definition ITR : list (Z * nat) := [(766260, 183%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [766428].
Definition CSUMS : list CAD.callsum := [(CAD.CSUM 748420 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false); (CAD.CSUM 746240 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false); (CAD.CSUM 746628 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 80 false false); (CAD.CSUM 751308 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 112 false false); (CAD.CSUM 745956 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false); (CAD.CSUM 765872 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false); CAD.cs_inline 766564 4 []; CAD.cs_inline 766716 4 []; CAD.cs_inline 766960 4 []].
Definition ASSUME : list (Z * (list expr -> list kentry -> list (list kentry * kentry))) := [(766608, (FAS.a_j1 51 52)); (766668, (FAS.a_f1 58)); (766772, (FAS.a_nz)); (766828, (FAS.a_ent)); (766840, (FAS.a_f2 47 57))].
Definition CASES : list (Z * list (nat * Z)) := [(766828, [(10%nat, 0)]); (766844, [(19%nat, 9223372036854775807)])].
Definition RESPELL : list (Z * (list expr -> list kentry -> list (nat * expr))) := [].
Definition ECASES : list (Z * list ((list expr -> expr) * Z)) := [].
Definition NAMEB : list (Z * nat) := [].
Definition XSTOPS : list Z := [766608; 766668; 766772; 766828; 766840; 766828; 766844].
Definition HDECL : CH.hdecl := CH.HD (192) (8224) [] [] [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 766260 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332483264) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-192)) (ELit (192));
   KUnk (SA (EVar 2) (-192)) (ELit (192))]
  32 [((EVar 2), (-192), ELit 192)] [] (ELit (1152921504606846976)).
Definition BL0 : CAD.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 766352 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); EVar 25; EVar 26; EVar 27; (EVar 53); (EVar 54); (EVar 55); (EVar 56)]
  [KRange (EVar 2) (140735332483264) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-192)) (ELit (192));
   KUnk (SA (EVar 2) (-192)) (ELit (112));
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  57 [((EVar 2), (-192), ELit 192)] [] (ELit (576460752303423488)).
Definition BL1 : CAD.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 766608 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); EVar 25; EVar 26; EVar 27; (EVar 53); (EVar 54); (EVar 55); (EVar 56)]
  [KRange (EAlu Instr.ALU_ADD (EVar 51) (ELit (120))) (0) (65535);
   KRange (EAlu Instr.ALU_ADD (EVar 52) (ELit (120))) (0) (65535);
   KRange (EVar 2) (140735332483264) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-192)) (ELit (192));
   KUnk (SA (EVar 2) (-192)) (ELit (112));
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  57 [((EVar 2), (-192), ELit 192)] [] (ELit (288230376151711744)).
Definition BL2 : CAD.blocks := [].
Definition hints2 : list (nat * CC.subst) := [(3%nat, [(57%nat, (EAlu Instr.ALU_ADD (EVar 52) (ELit (120)))); (58%nat, (APC.esub (EVar 51) (EVar 52)))])].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 766668 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (APC.eadd (APC.eaddz (EVar 57) (-120)) (EVar 58)); (APC.eaddz (EVar 57) (-120)); EVar 25; EVar 26; EVar 27; (EVar 53); (EVar 54); (EVar 55); (EVar 56)]
  [KRange (EVar 58) (1) (70000);
   KRange (EVar 57) (0) (65535);
   KRange (EVar 38) (281474976710656) (562949953421311);
   KRange (EAlu Instr.ALU_SLTU (ELit (0)) (EAlu Instr.ALU_OR (EVar 39) (EVar 47))) (1) (1);
   KRange (EVar 2) (140735332483264) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-192)) (ELit (192));
   KUnk (SA (EVar 2) (-192)) (ELit (112));
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  59 [((EVar 2), (-192), ELit 192)] [] (APC.eaddz (EVar 58) (144115188075855872)).
Definition BL3 : CAD.blocks := [].
Definition hints3 : list (nat * CC.subst) := [(3%nat, [(57%nat, (EVar 57)); (58%nat, (EAlu Instr.ALU_ADD (EVar 58) (ELit (-1))))])].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 766772 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); EVar 25; EVar 26; EVar 27; (EVar 53); (EVar 54); (EVar 55); (EVar 56)]
  [KRange (EVar 38) (281474976710656) (562949953421311);
   KRange (EAlu Instr.ALU_SLTU (ELit (0)) (EAlu Instr.ALU_OR (EVar 39) (EVar 47))) (1) (1);
   KRange (EVar 2) (140735332483264) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-192)) (ELit (192));
   KUnk (SA (EVar 2) (-192)) (ELit (112));
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  57 [((EVar 2), (-192), ELit 192)] [] (ELit (72057594037927936)).
Definition BL4 : CAD.blocks := [].
Definition hints4 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CC.CP 766840 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); EVar 25; EVar 26; EVar 27; (EVar 53); (EVar 54); (EVar 55); (EVar 56)]
  [KRange (EVar 38) (1) (281474976710655);
   KRange (EVar 2) (140735332483264) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-192)) (ELit (192));
   KUnk (SA (EVar 2) (-192)) (ELit (112));
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  57 [((EVar 2), (-192), ELit 192)] [] (APC.esub (ELit (36591746972385280)) (EVar 38)).
Definition BL5 : CAD.blocks := [].
Definition hints5 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CC.CP 766840 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); EVar 25; EVar 26; EVar 27; (EVar 53); (EVar 54); (EVar 55); (EVar 56)]
  [KRange (EVar 57) (1) (64);
   KRange (EVar 38) (0) (0);
   KRange (EVar 47) (1) (18446744073709551615);
   KRange (EAlu Instr.ALU_SRL (EVar 47) (APC.esub (ELit (64)) (EVar 57))) (1) (18446744073709551615);
   KRange (EVar 2) (140735332483264) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-192)) (ELit (192));
   KUnk (SA (EVar 2) (-192)) (ELit (112));
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  58 [((EVar 2), (-192), ELit 192)] [] (APC.eaddz (EVar 57) (37154696925806592)).
Definition BL6 : CAD.blocks := [].
Definition hints6 : list (nat * CC.subst) := [(6%nat, [(57%nat, (EAlu Instr.ALU_ADD (EVar 57) (ELit (-1))))])].
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CC.CP 766868 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); EVar 25; EVar 26; EVar 27; (EVar 53); (EVar 54); (EVar 55); (EVar 56)]
  [KRange (EVar 2) (140735332483264) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-192)) (ELit (192));
   KUnk (SA (EVar 2) (-192)) (ELit (112));
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  57 [((EVar 2), (-192), ELit 192)] [] (ELit (18014398509481984)).
Definition BL7 : CAD.blocks := [].
Definition hints7 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CC.CP 766828 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); EVar 25; EVar 26; EVar 27; (EVar 53); (EVar 54); (EVar 55); (EVar 56)]
  [KRange (EAlu Instr.ALU_SLTU (ELit (0)) (EAlu Instr.ALU_OR (EVar 38) (EVar 47))) (1) (1);
   KRange (EVar 38) (0) (18446744073709551615);
   KRange (EVar 2) (140735332483264) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-192)) (ELit (192));
   KUnk (SA (EVar 2) (-192)) (ELit (112));
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  57 [((EVar 2), (-192), ELit 192)] [] (ELit (40532396646334464)).
Definition BL8 : CAD.blocks := [].
Definition hints8 : list (nat * CC.subst) := [(6%nat, [(57%nat, (ELit (64)))])].
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CC.CP 766384 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-80)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); EVar 25; EVar 26; EVar 27; (EVar 53); (EVar 54); (EVar 55); (EVar 56)]
  [KRange (EVar 2) (140735332483264) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-192)) (ELit (192));
   KUnk (SA (EVar 2) (-192)) (ELit (112));
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  57 [((EVar 2), (-192), ELit 192)] [] (ELit (1125899906842624)).
Definition BL9 : CAD.blocks := [].
Definition hints9 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4; t5; t6; t7; t8; t9].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CAD.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] XSTOPS ASSUME CASES NAMEB RESPELL ECASES (CC.cp_F c) (CC.cp_meas c) h 4000 first false 2%nat
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CAD.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CAD.po_leaves o)) (CC.cp_meas c).
