(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(292172, 46%nat); (292692, 30%nat); (293052, 73%nat); (457552, 8%nat); (292624, 17%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [458904; 292812; 284948; 292328].
Definition HDECL : CH.hdecl := CH.HD (0) (8224) [] [] [].
Definition CSUMS : list CA.callsum := [].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 292172 [EVar 0; (EVar 33); (EVar 2); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KUnk (SA (EVar 2) (-96)) (ELit (96));
   KWr (SA (EVar 2) (-96)) (ELit (96));
   KRange (EVar 42) (1099511627776) (140737488355328);
   KWord (SA (EVar 42) (240)) 8 (EVar 64);
   KWord (SA (EVar 42) (248)) 8 (APC.eaddz (EVar 64) (16));
   KWord (SA (EVar 64) (0)) 8 (ELit (818632));
   KWord (SA (EVar 64) (16)) 8 (ELit (818392));
   KWord (SA (EVar 64) (152)) 1 (EVar 65);
   KImg (65536) (827984);
   KRange (EVar 64) (1099511627776) (140737488355328);
   KRange (EVar 65) (0) (255);
   KWord (SA (EVar 42) (288)) 8 (ELit (0));
   KWord (SA (EVar 42) (264)) 8 (EVar 66);
   KWord (SA (EVar 42) (272)) 8 (ELit (16384));
   KWord (SA (EVar 42) (280)) 8 (EVar 67);
   KWr (SA (EVar 42) (280)) (ELit (8));
   KDisj (SA (EVar 2) (-96)) (ELit (96)) (SA (EVar 42) (0)) (ELit (320));
   KDisj (SA (EVar 2) (-96)) (ELit (96)) (SA (EVar 64) (0)) (ELit (272));
   KDisj (SA (EVar 42) (280)) (ELit (8)) (SA (EVar 64) (0)) (ELit (272));
   KAlign (EVar 64) (8);
   KRange (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_AND (EVar 65) (ELit 2)) (ELit 0)) (ELit 1)) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit (4611686018427387904)) (EVar 65)) (ELit 63)) (ELit 0)) (ELit 1))) 0 0]
  68 [((EVar 2), (-96), ELit 96); ((EVar 42), (280), ELit 8)] [] (ELit (20)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 293156 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-96)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (ELit (16384)); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-96)) (ELit (96));
   KRange (EVar 40) (1099511627776) (140737488355328);
   KRange (EVar 42) (0) (16384);
   KWord (SA (EVar 2) (-96)) 8 (EVar 40);
   KWord (SA (EVar 2) (-88)) 8 (EVar 67);
   KWord (SA (EVar 2) (-80)) 8 (EVar 40);
   KWord (SA (EVar 2) (-72)) 8 (ELit (292736));
   KWord (SA (EVar 2) (-64)) 8 (EVar 68);
   KWord (SA (EVar 2) (-56)) 8 (ELit (292220));
   KWord (SA (EVar 2) (-8)) 8 (EVar 69);
   KWord (SA (EVar 2) (-16)) 8 (EVar 70);
   KWord (SA (EVar 2) (-24)) 8 (EVar 71);
   KWord (SA (EVar 2) (-32)) 8 (EVar 72);
   KWord (SA (EVar 2) (-40)) 8 (EVar 73);
   KWord (SA (EVar 40) (240)) 8 (EVar 64);
   KWord (SA (EVar 40) (248)) 8 (APC.eaddz (EVar 64) (16));
   KWord (SA (EVar 64) (0)) 8 (ELit (818632));
   KWord (SA (EVar 64) (16)) 8 (ELit (818392));
   KWord (SA (EVar 64) (152)) 4 (ELit (0));
   KImg (65536) (827984);
   KRange (EVar 64) (1099511627776) (140737488355328);
   KWord (SA (EVar 64) (156)) 4 (ELit (0));
   KWord (SA (EVar 64) (160)) 8 (APC.eaddz (EVar 64) (16));
   KWr (SA (EVar 64) (152)) (ELit (4));
   KUnk (SA (EVar 40) (256)) (ELit (8));
   KWr (SA (EVar 40) (256)) (ELit (8));
   KWord (SA (EVar 40) (280)) 8 (EVar 66);
   KWord (SA (EVar 40) (296)) 1 (EVar 65);
   KRange (EVar 65) (0) (1);
   KWr (SA (EVar 40) (280)) (ELit (16));
   KRange (EVar 66) (4096) (140737488355328);
   KDisj (SA (EVar 2) (-96)) (ELit (96)) (SA (EVar 40) (0)) (ELit (320));
   KDisj (SA (EVar 2) (-96)) (ELit (96)) (SA (EVar 64) (0)) (ELit (272));
   KDisj (SA (EVar 40) (0)) (ELit (320)) (SA (EVar 64) (0)) (ELit (272));
   KAlign (EVar 64) (8)]
  74 [((EVar 2), (-96), ELit 96); ((EVar 64), (152), ELit 4); ((EVar 40), (256), ELit 8); ((EVar 40), (280), ELit 16)] [] (ELit (19)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 292264 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-48)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KWord (SA (EVar 2) (-8)) 8 (EVar 64);
   KWord (SA (EVar 2) (-16)) 8 (EVar 65);
   KWord (SA (EVar 2) (-24)) 8 (EVar 66);
   KWord (SA (EVar 2) (-32)) 8 (EVar 67);
   KWord (SA (EVar 2) (-40)) 8 (EVar 68);
   KRange (EVar 50) (1099511627776) (140737488355328);
   KWord (SA (EVar 50) (296)) 1 (EVar 69);
   KRange (EVar 69) (0) (1);
   KWr (SA (EVar 50) (296)) (ELit (1));
   KDisj (SA (EVar 2) (-48)) (ELit (48)) (SA (EVar 50) (0)) (ELit (320))]
  70 [((EVar 50), (296), ELit 1)] [] (ELit (18)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 400 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
