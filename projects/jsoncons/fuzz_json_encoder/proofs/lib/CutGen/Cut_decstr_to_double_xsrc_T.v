(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallSums2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(273320, 76%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [273440].
Definition HDECL : CH.hdecl := CH.HD (9040) (8224) [] [((EVar 12), (0), ELit 8); ((ELit (0)), (890236), ELit 4)] [(65536, 813152)].
Definition CSUMS : list CA.callsum := [CAX.xs_cs (SSU2.strtod_xsum 760068 8944 890236 20%nat); CA.cs_inline 273388 4 [10%nat]].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 273320 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 11) (0) (67108864);
   KRange (EVar 10) (4096) (140737488355328);
   KBlob (SA (EVar 10) (0)) (EVar 11) 0;
   KWord (SA (APC.eadd (EVar 10) (EVar 11)) (0)) 1 (ELit (0));
   KUnk (SA (EVar 10) (0)) (APC.eadd (EVar 11) (ELit (1)));
   KUnk (SA (EVar 2) (-9040)) (ELit (9040));
   KWr (SA (EVar 2) (-9040)) (ELit (9040));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KUnk (SA (EVar 12) (0)) (ELit (8));
   KWr (SA (EVar 12) (0)) (ELit (8));
   KRange (EVar 12) (1099511627776) (140737488355328);
   KWr (SA (ELit (0)) (890236)) (ELit (4));
   KImg (65536) (813152);
   KDisj (SA (EVar 2) (-9040)) (ELit (9040)) (SA (EVar 12) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-9040)) (ELit (9040)) (SA (EVar 10) (0)) (APC.eadd (EVar 11) (ELit (1)));
   KDisj (SA (ELit (0)) (890236)) (ELit (4)) (SA (EVar 10) (0)) (APC.eadd (EVar 11) (ELit (1)));
   KRange (APC.eadd (EVar 10) (EVar 11)) (4096) (140737488355328)]
  32 [((EVar 2), (-9040), ((ELit (9040)))); ((EVar 12), (0), ((ELit (8)))); ((ELit (0)), (890236), ((ELit (4))))] [] (ELit (10)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 400 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
