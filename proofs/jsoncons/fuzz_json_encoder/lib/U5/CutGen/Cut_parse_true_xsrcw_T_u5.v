(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallKn.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallKnX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(303272, 85%nat); (288968, 4%nat); (306288, 11%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 53.
Definition ENDS : list Z := [303568].
Definition HDECL : CH.hdecl := CH.HD (10672) (8224) [((EVar 12), (0), ELit 8); ((EVar 50), (0), ((EVar 51)))] [((EVar 10), (0), ELit 272); ((EVar 13), (0), ELit 16)] [(65536, 827984)].
Definition CSUMS : list CA.callsum := [CAX.xs_cs (PSU.setec_xsum 284948 256); CAX.xs_cs (VSX.vis_xsum 249664 10624 898504)].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 303272 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (EVar 50); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  (SPKX.knx (PSK.CONSTS (803024) (804528) (803536) (65536) (1040384) (65536) (827984) (10672) [((-8), 1%nat); ((-16), 8%nat); ((-24), 9%nat); ((-32), 18%nat)] (32)) false (EVar 10) (EVar 12) (EVar 13) (EVar 2) (APC.eadd (EVar 50) (EVar 51)) (PSK.PX (EVar 41) (EVar 50) (EVar 42) (EVar 43) (EVar 44) (ELit (1)) (EVar 46) (EVar 35) (EVar 36) (EVar 37) (EVar 38) (EVar 39) (EVar 40) (EVar 47) (EVar 48) (ELit (0))) ++ SPKX.win_fx (PSK.CONSTS (803024) (804528) (803536) (65536) (1040384) (65536) (827984) (10672) [((-8), 1%nat); ((-16), 8%nat); ((-24), 9%nat); ((-32), 18%nat)] (32)) (EVar 10) (EVar 12) (EVar 13) (EVar 2) (EVar 50) (EVar 51) (PSK.PX (EVar 41) (EVar 50) (EVar 42) (EVar 43) (EVar 44) (ELit (1)) (EVar 46) (EVar 35) (EVar 36) (EVar 37) (EVar 38) (EVar 39) (EVar 40) (EVar 47) (EVar 48) (ELit (0))) ++ [KRange (EVar 51) (1) (16384)])
  53 [((EVar 2), (-10672), ELit 10672); ((EVar 10), (0), ELit 272)] [] (ELit (100)).
Definition BL0 : CA.blocks := [((EVar 37), (APC.escale (2) (EVar 35))); ((EVar 38), (EVar 40))].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [303344; 303364; 303384] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
