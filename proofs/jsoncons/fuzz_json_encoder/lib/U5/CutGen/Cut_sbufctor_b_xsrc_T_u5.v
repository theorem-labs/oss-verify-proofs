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
Definition ITR : list (Z * nat) := [(242124, 46%nat); (242360, 90%nat); (437948, 28%nat); (438060, 50%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [242304].
Definition HDECL : CH.hdecl := CH.HD (0) (8224) [] [] [].
Definition CSUMS : list CA.callsum := [].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 242264 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-64)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KWord (SA (EVar 2) (-8)) 8 (EVar 64);
   KWord (SA (EVar 2) (-16)) 8 (EVar 65);
   KWord (SA (EVar 2) (-24)) 8 (EVar 66);
   KWord (SA (EVar 2) (-32)) 8 (EVar 67);
   KWord (SA (EVar 2) (-40)) 8 (EVar 68);
   KWord (SA (EVar 2) (-48)) 8 (EVar 69);
   KWord (SA (EVar 2) (-56)) 8 (EVar 70);
   KUnk (SA (EVar 2) (-112)) (ELit (48));
   KWr (SA (EVar 2) (-112)) (ELit (48));
   KRange (EVar 40) (1099511627776) (140737488355328);
   KWord (SA (EVar 40) (64)) 8 (EVar 71);
   KWord (SA (EVar 40) (72)) 8 (EVar 72);
   KWord (SA (EVar 40) (80)) 8 (EVar 73);
   KWord (SA (EVar 40) (96)) 4 (ELit (8));
   KUnk (SA (EVar 40) (16)) (ELit (24));
   KWr (SA (EVar 40) (16)) (ELit (24));
   KUnk (SA (EVar 40) (88)) (ELit (8));
   KWr (SA (EVar 40) (88)) (ELit (8));
   KDisj (SA (EVar 2) (-112)) (ELit (112)) (SA (EVar 40) (0)) (ELit (104));
   KRange (EAlu Instr.ALU_AND (EExt false 0%nat 1%nat (EVar 71)) (ELit 1)) (0) (0)]
  74 [((EVar 2), (-112), ELit 48); ((EVar 40), (16), ELit 24); ((EVar 40), (88), ELit 8)] [] (ELit (4)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
Definition t1 : CC.cutpoint := CC.CP 242264 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-64)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KWord (SA (EVar 2) (-8)) 8 (EVar 64);
   KWord (SA (EVar 2) (-16)) 8 (EVar 65);
   KWord (SA (EVar 2) (-24)) 8 (EVar 66);
   KWord (SA (EVar 2) (-32)) 8 (EVar 67);
   KWord (SA (EVar 2) (-40)) 8 (EVar 68);
   KWord (SA (EVar 2) (-48)) 8 (EVar 69);
   KWord (SA (EVar 2) (-56)) 8 (EVar 70);
   KUnk (SA (EVar 2) (-112)) (ELit (48));
   KWr (SA (EVar 2) (-112)) (ELit (48));
   KRange (EVar 40) (1099511627776) (140737488355328);
   KWord (SA (EVar 40) (64)) 8 (EVar 71);
   KWord (SA (EVar 40) (72)) 8 (EVar 72);
   KWord (SA (EVar 40) (80)) 8 (EVar 73);
   KWord (SA (EVar 40) (96)) 4 (ELit (8));
   KUnk (SA (EVar 40) (16)) (ELit (24));
   KWr (SA (EVar 40) (16)) (ELit (24));
   KUnk (SA (EVar 40) (88)) (ELit (8));
   KWr (SA (EVar 40) (88)) (ELit (8));
   KDisj (SA (EVar 2) (-112)) (ELit (112)) (SA (EVar 40) (0)) (ELit (104));
   KRange (EAlu Instr.ALU_AND (EExt false 0%nat 1%nat (EVar 71)) (ELit 1)) (1) (1);
   KRange (EVar 72) (0) (67108864);
   KRange (EVar 73) (4096) (140737488355328)]
  74 [((EVar 2), (-112), ELit 48); ((EVar 40), (16), ELit 24); ((EVar 40), (88), ELit 8)] [] (ELit (4)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 400 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
