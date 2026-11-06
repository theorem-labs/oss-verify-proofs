(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(863032, 130%nat); (864280, 75%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [863436].
Definition HDECL : CH.hdecl := CH.HD (8256) (8224) [((EVar 10), (0), ((EVar 11))); ((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 2048); ((EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (1)) (ELit 3)), (2147450880), ELit 1); ((EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (2)) (ELit 3)), (2147450880), ELit 1); ((EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (3)) (ELit 3)), (2147450880), ELit 1)] [] [(1459384, 1463120); (166014, 166030)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880)].
Definition GLO : Z := 1459384.
Definition GHI : Z := 1463120.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 442880 8192 0%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)], BLk)) (fun F => F)) (fun _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 863032 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KImg (166014) (166030);
   KRange (EVar 10) (4096) (140737479950336);
   KAlign (EVar 10) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (2048));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (1)) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (2)) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (3)) (ELit 3)) 2147450880) (ELit 1);
   KBlob (SA (EVar 10) (0)) (EVar 11) 0;
   KUnk (SA (EVar 10) (0)) (EVar 11);
   KRange (EVar 11) (1) (16384);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit 16384);
   KWr (SA (EVar 2) (-8256)) (ELit (8256));
   KUnk (SA (EVar 2) (-8256)) (ELit (8256));
   KRange (EVar 2) (140735332491328) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-8256)) (ELit (8256)) (SA (EVar 10) (0)) (ELit (16384))]
  32 [((EVar 2), (-8256), ELit 8256)] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
