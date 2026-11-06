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
Definition ITR : list (Z * nat) := [(739428, 138%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [739864].
Definition HDECL : CH.hdecl := CH.HD (13824) (8224) [((EVar 10), (0), ELit 296); ((EVar 10), (304), ELit 104); ((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 51); ((EAlu Instr.ALU_SRL (EVar 32) (ELit 3)), (2147450880), ELit 3)] [((EVar 10), (296), ELit 8); ((EVar 32), (0), ELit 24)] [(1444792, 1448528); (65536, 1449984)].
Definition SCELLS : list (Z * Z * Z) := [(1482488, 8, 2147450880)].
Definition GLO : Z := 1444792.
Definition GHI : Z := 1448528.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (ESA.hcall_xsumA 765616 4624 (EVar 32) [] (fun _ _ => [])); CAXA.xs_cs (ESA.sink_xsumA 1040708 4368); CAXA.xs_cs (ESA.lit_xsumA 770528 80 6931848 154272 4); CAXA.xs_cs (ESA.lit_xsumA 832876 80 6931872 165024 4); CAXA.xs_cs (ESA.lit_xsumA 832992 80 6931896 165056 5); CAXA.xs_cs (ESA.sinkret_xsumA 766156 4880 (EVar 32)); CAXA.xs_cs (ESA.sinkret_xsumA 767788 4880 (EVar 32)); CAXA.xs_cs (ESA.hcall_xsumA 769828 4592 (EVar 32) [] (fun _ _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 739428 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1444792) (1448528);
   KWord (SA (ELit 0) 1482488) 8 (ELit 2147450880);
   KImg (65536) (1449984);
   KWord (SA (EVar 10) (8)) 8 (EVar 32);
   KWord (SA (EVar 10) (40)) 8 (ELit (120));
   KWord (SA (EVar 10) (296)) 8 (EVar 37);
   KRange (EVar 37) (0) (18446744073709551615);
   KWr (SA (EVar 10) (296)) (ELit (8));
   KRange (EVar 10) (7077888) (140737479966312);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (51));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (408));
   KRange (EVar 32) (7077888) (140737479966696);
   KAlign (EVar 32) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit (3));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-13824)) (ELit (13744));
   KUnk (SA (EVar 2) (-80)) (ELit (80));
   KWr (SA (EVar 2) (-13824)) (ELit (13824));
   KRange (EVar 2) (140735332496896) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-13824)) (ELit (13824));
   KDisj (SA (EVar 2) (-13824)) (ELit (13824)) (SA (EVar 10) (0)) (ELit (408));
   KDisj (SA (EVar 2) (-13824)) (ELit (13824)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (408)) (SA (EVar 32) (0)) (ELit (24));
   KWord (SA (EVar 10) (264)) 8 (EVar 34);
   KWord (SA (EVar 10) (272)) 8 (EVar 34)]
  48 [((EVar 2), (-13824), ((ELit (13824)))); ((EVar 10), (296), ((ELit (8))))] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
