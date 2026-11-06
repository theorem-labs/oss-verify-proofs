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
Definition ITR : list (Z * nat) := [(843104, 62%nat); (843988, 46%nat); (770104, 34%nat); (844172, 113%nat); (843760, 57%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [843340].
Definition HDECL : CH.hdecl := CH.HD (4304) (8224) [((EVar 10), (24), ELit 16); ((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 5); ((EVar 11), (0), ELit 4); ((EVar 12), (0), ELit 1); ((EVar 13), (0), ELit 1); ((EVar 15), (0), ELit 8); ((EAlu Instr.ALU_SRL (EVar 11) (ELit 3)), (2147450880), ELit 1); ((EAlu Instr.ALU_SRL (EVar 12) (ELit 3)), (2147450880), ELit 1); ((EAlu Instr.ALU_SRL (EVar 13) (ELit 3)), (2147450880), ELit 1); ((EAlu Instr.ALU_SRL (EVar 15) (ELit 3)), (2147450880), ELit 1); ((EAlu Instr.ALU_SRL (EVar 2) (ELit 3)), (2147450869), ELit 3)] [((EVar 10), (0), ELit 24)] [(1433600, 1466368)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880)].
Definition GLO : Z := 1433600.
Definition GHI : Z := 1466368.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 542968 4096 0%nat (fun _ _ => None) (fun regs => [((EAlu Instr.ALU_SRL (nth 10 regs (ELit 0)) (ELit 3)), 2147450880, (EAlu Instr.ALU_SRL (APC.eaddz (APC.esub (nth 11 regs (ELit 0)) (nth 10 regs (ELit 0))) (7)) (ELit 3)))]) (fun _ BL => BL) (fun regs _ _ BLk => ([KImg (1433600) (1466368); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KZero (SA (EAlu Instr.ALU_SRL (EVar 2) (ELit 3)) (2147450869)) (ELit 3)] ++ [KZero (SA (EAlu Instr.ALU_SRL (APC.eadd (EVar 32) (EVar 38)) (ELit 3)) 2147450880) (ELit (4)); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 32) (EVar 38)) (4)) (ELit 3)) (2147450880)) (ELit 1); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 32) (EVar 38)) (5)) (ELit 3)) (2147450880)) (ELit 1); KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (APC.eadd (EVar 32) (EVar 38)) (6)) (ELit 3)) (2147450880)) (ELit 1)], BLk)) (fun F => F)) (fun _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 843104 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; (APC.eaddz (EVar 10) (32)); EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1433600) (1466368);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (EVar 10) (0)) 8 (EVar 32);
   KWord (SA (EVar 10) (8)) 8 (APC.eadd (EVar 32) (EVar 38));
   KWord (SA (EVar 10) (16)) 8 (APC.eadd (EVar 32) (EVar 33));
   KWr (SA (EVar 10) (0)) (ELit (24));
   KUnk (SA (EVar 10) (0)) (ELit (24));
   KWord (SA (EVar 10) (32)) 8 (EVar 37);
   KRange (EVar 37) (0) (18446744073709551615);
   KRange (EVar 10) (7094272) (140737479966576);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (5));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (40));
   KWord (SA (EVar 11) (0)) 4 (EVar 34);
   KRange (EVar 34) (0) (1);
   KWord (SA (EVar 12) (0)) 1 (ELit (0));
   KWord (SA (EVar 13) (0)) 1 (EVar 35);
   KRange (EVar 35) (0) (1);
   KWord (SA (EVar 15) (0)) 8 (EVar 36);
   KRange (EVar 36) (0) (18446744073709551615);
   KUnk (SA (EVar 2) (-4304)) (ELit (4304));
   KWr (SA (EVar 2) (-4304)) (ELit (4304));
   KRange (EVar 2) (140735332487376) (140737488355264);
   KAlign (EVar 2) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 2) (-4304)) (ELit (4368));
   KDisj (SA (EVar 2) (-4304)) (ELit (4368)) (SA (EVar 10) (0)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 2) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 5);
   KRange (EAlu Instr.ALU_SUB (EVar 11) (EVar 2)) 0 60;
   KRange (EVar 11) (140735332487376) (140737488355324);
   KDisj (SA (EVar 10) (0)) (ELit (40)) (SA (EVar 11) (0)) (ELit (4));
   KDisj (SA (EVar 2) (-4304)) (ELit (4304)) (SA (EVar 11) (0)) (ELit (4));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit 4);
   KRange (EAlu Instr.ALU_SUB (EVar 12) (EVar 2)) 0 63;
   KRange (EVar 12) (140735332487376) (140737488355327);
   KDisj (SA (EVar 10) (0)) (ELit (40)) (SA (EVar 12) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-4304)) (ELit (4304)) (SA (EVar 12) (0)) (ELit (1));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) (2147450880)) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 12) (0)) (ELit 1);
   KRange (EAlu Instr.ALU_SUB (EVar 13) (EVar 2)) 0 63;
   KRange (EVar 13) (140735332487376) (140737488355327);
   KDisj (SA (EVar 10) (0)) (ELit (40)) (SA (EVar 13) (0)) (ELit (1));
   KDisj (SA (EVar 2) (-4304)) (ELit (4304)) (SA (EVar 13) (0)) (ELit (1));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 13) (ELit 3)) (2147450880)) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 13) (0)) (ELit 1);
   KRange (EAlu Instr.ALU_SUB (EVar 15) (EVar 2)) 0 56;
   KRange (EVar 15) (140735332487376) (140737488355320);
   KDisj (SA (EVar 10) (0)) (ELit (40)) (SA (EVar 15) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-4304)) (ELit (4304)) (SA (EVar 15) (0)) (ELit (8));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (2147450880)) (ELit 1);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 15) (0)) (ELit 8);
   KRange (EVar 33) (32) (32768);
   KAlign (EVar 33) (32);
   KRange (EVar 38) (0) (32736);
   KAlign (EVar 38) (32);
   KRange (EAlu Instr.ALU_SUB (EVar 33) (EVar 38)) (32) (32768);
   KAlign (APC.eadd (EVar 32) (EVar 38)) (8);
   KRange (APC.eadd (EVar 32) (EVar 38)) (4096) (140737479966720);
   KUnk (SA (EVar 32) (0)) (EVar 33);
   KWr (SA (EVar 32) (0)) (EVar 33);
   KRange (EVar 32) (4096) (140737479966720);
   KAlign (EVar 32) (16);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 2) (-4304)) (ELit (4368)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EVar 10) (0)) (ELit (40)) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (ELit 0) (1433600)) (ELit 36864) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (ELit 0) (1497016)) (ELit 8) (SA (EVar 32) (0)) (EVar 33);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit 5) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 33) (7)) (ELit 3));
   KDisj (SA (EVar 10) (0)) (ELit 24) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 33) (7)) (ELit 3));
   KDisj (SA (EVar 10) (24)) (ELit 16) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 33) (7)) (ELit 3));
   KDisj (SA (EVar 2) (-4304)) (ELit 4304) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 33) (7)) (ELit 3));
   KBlob (SA (EVar 32) (0)) (EVar 38) 0;
   KBlob (SA (APC.eadd (EVar 32) (EVar 38)) (32)) (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SUB (EVar 33) (EVar 38)) (ELit 32)) 1;
   KRange (EAlu Instr.ALU_SUB (EAlu Instr.ALU_SUB (EVar 33) (EVar 38)) (ELit 32)) (0) (32736);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 33) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) (2147450880)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 33) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 13) (ELit 3)) (2147450880)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 33) (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 15) (ELit 3)) (2147450880)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 33) (7)) (ELit 3));
   KDisj (SA (EVar 11) (0)) (ELit 4) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 33) (7)) (ELit 3));
   KDisj (SA (EVar 12) (0)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 33) (7)) (ELit 3));
   KDisj (SA (EVar 13) (0)) (ELit 1) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 33) (7)) (ELit 3));
   KDisj (SA (EVar 15) (0)) (ELit 8) (SA (EAlu Instr.ALU_SRL (EVar 32) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 33) (7)) (ELit 3));
   KZero (SA (EAlu Instr.ALU_SRL (EVar 2) (ELit 3)) (2147450869)) (ELit 3)]
  48 [((EVar 2), (-4304), ELit 4304); ((EVar 10), (0), ELit 24); ((EVar 32), (0), ((EVar 33)))] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [((EVar 32), (EVar 33))].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 800 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
