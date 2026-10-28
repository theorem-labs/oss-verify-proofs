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
Definition ITR : list (Z * nat) := [(458904, 69%nat); (459180, 21%nat); (459624, 18%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [779340; 459168].
Definition HDECL : CH.hdecl := CH.HD (0) (8224) [] [] [].
Definition CSUMS : list CA.callsum := [].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 458904 [EVar 0; (EVar 33); (EVar 2); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (ELit (16384)); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (EVar 54); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KUnk (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KRange (EVar 42) (1099511627776) (140737488355328);
   KWord (SA (EVar 42) (0)) 8 (ELit (818392));
   KWord (SA (EVar 42) (24)) 8 (EVar 64);
   KWord (SA (EVar 42) (32)) 8 (APC.eadd (EVar 64) (EVar 65));
   KWord (SA (EVar 42) (48)) 8 (ELit (0));
   KWord (SA (EVar 42) (88)) 8 (APC.eadd (EVar 64) (EVar 65));
   KWord (SA (EVar 42) (96)) 1 (ELit (8));
   KImg (65536) (827984);
   KRange (EVar 64) (4096) (140737488355328);
   KRange (EVar 65) (0) (67108864);
   KDisj (SA (EVar 2) (-80)) (ELit (80)) (SA (EVar 42) (0)) (ELit (104))]
  66 [((EVar 2), (-80), ELit 80)] [] (ELit (10)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 459116 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-64)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (ELit (0)); (ELit (16384)); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (ELit (16384)); (EVar 53); (ELit (18446744073709551615)); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (16));
   KWord (SA (EVar 2) (-8)) 8 (EVar 66);
   KWord (SA (EVar 2) (-16)) 8 (EVar 67);
   KWord (SA (EVar 2) (-24)) 8 (EVar 68);
   KWord (SA (EVar 2) (-32)) 8 (EVar 69);
   KWord (SA (EVar 2) (-40)) 8 (EVar 70);
   KWord (SA (EVar 2) (-48)) 8 (EVar 71);
   KWord (SA (EVar 2) (-56)) 8 (EVar 72);
   KWord (SA (EVar 2) (-64)) 8 (EVar 73);
   KRange (EVar 51) (1099511627776) (140737488355328);
   KWord (SA (EVar 51) (24)) 8 (EVar 64);
   KRange (EVar 64) (4096) (140737488355328);
   KWr (SA (EVar 51) (24)) (ELit (8));
   KDisj (SA (EVar 2) (-80)) (ELit (80)) (SA (EVar 51) (0)) (ELit (104))]
  74 [((EVar 2), (-80), ELit 80); ((EVar 51), (24), ELit 8)] [] (ELit (9)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 459116 [EVar 0; (EVar 33); (APC.eaddz (EVar 2) (-64)); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (ELit (0)); (ELit (16384)); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); (EVar 47); (EVar 48); (EVar 49); (EVar 50); (EVar 51); (EVar 52); (EVar 53); (ELit (18446744073709551615)); (EVar 55); (EVar 56); (EVar 57); (EVar 58); (EVar 59); (EVar 60); (EVar 61); (EVar 62); (EVar 63)]
  [KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KWr (SA (EVar 2) (-80)) (ELit (80));
   KUnk (SA (EVar 2) (-80)) (ELit (16));
   KWord (SA (EVar 2) (-8)) 8 (EVar 66);
   KWord (SA (EVar 2) (-16)) 8 (EVar 67);
   KWord (SA (EVar 2) (-24)) 8 (EVar 68);
   KWord (SA (EVar 2) (-32)) 8 (EVar 69);
   KWord (SA (EVar 2) (-40)) 8 (EVar 70);
   KWord (SA (EVar 2) (-48)) 8 (EVar 71);
   KWord (SA (EVar 2) (-56)) 8 (EVar 72);
   KWord (SA (EVar 2) (-64)) 8 (EVar 73);
   KRange (EVar 51) (1099511627776) (140737488355328);
   KWord (SA (EVar 51) (0)) 8 (ELit (818392));
   KWord (SA (EVar 51) (24)) 8 (EVar 64);
   KWord (SA (EVar 51) (32)) 8 (APC.eadd (EVar 64) (EVar 52));
   KWord (SA (EVar 51) (48)) 8 (ELit (0));
   KWord (SA (EVar 51) (88)) 8 (APC.eadd (EVar 64) (EVar 52));
   KWord (SA (EVar 51) (96)) 1 (ELit (8));
   KImg (65536) (827984);
   KRange (EVar 64) (4096) (140737488355328);
   KRange (EVar 52) (1) (16383);
   KWr (SA (EVar 51) (24)) (ELit (8));
   KDisj (SA (EVar 2) (-80)) (ELit (80)) (SA (EVar 51) (0)) (ELit (104))]
  74 [((EVar 2), (-80), ELit 80); ((EVar 51), (24), ELit 8)] [] (ELit (8)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 400 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
