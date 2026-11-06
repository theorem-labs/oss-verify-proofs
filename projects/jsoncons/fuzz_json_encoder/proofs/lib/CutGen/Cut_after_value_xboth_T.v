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
Definition ITR : list (Z * nat) := [(918320, 148%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [918784; 918788].
Definition HDECL : CH.hdecl := CH.HD (1152) (8224) [((EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (208)) (ELit 3)), (2147450880), ELit 1)] [((EVar 10), (208), ELit 1)] [(1459384, 1463120)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880); (1497024, 4, 1)].
Definition GLO : Z := 1459384.
Definition GHI : Z := 1463120.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 419648 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1); KRange (EVar (g + 5)) 7094272 140737479966656; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 64); KWr (SA (EVar (g + 5)) 0) (ELit 64); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 64); KDisj (SA (EVar 2) (-1152)) (ELit 1152) (SA (EVar (g + 5)) 0) (ELit 64); KWord (SA (EVar (g + 5)) 56) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7094272 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 64) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-1152)) (ELit 1152) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 64) (SA (EVar 10) (208)) (ELit (1)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (208)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 8) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (208)) (ELit 3)) (2147450880)) (ELit (1))], BLk)) (fun F => let g := 32%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 24); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 8)]))) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 914208 640 1%nat (fun regs g => Some (EVar g)) (fun regs => []) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1459384) (1463120); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KWord (SA (ELit 0) 1497024) 4 (ELit 1)] ++ [KRange (EVar g) 0 255] ++ match CAX.cell_at cells (nth 21 regs (ELit 0)) 56 8 with Some fl => [KWord (SA (nth 21 regs (ELit 0)) 56) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F ++ [((EVar 32), 0, ELit 1)])) (fun regs => [((nth 21 regs (ELit 0)), 0, -96)]))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 918320 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1459384) (1463120);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1497024) 4 (ELit 1);
   KWr (SA (EVar 10) (208)) (ELit (1));
   KRange (EVar 10) (7094272) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (208)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (208)) (ELit (1));
   KUnk (SA (EVar 2) (-1152)) (ELit (1152));
   KWr (SA (EVar 2) (-1152)) (ELit (1152));
   KRange (EVar 2) (140735332484224) (140737488355328);
   KAlign (EVar 2) (32);
   KDisj (SA (EVar 2) (-1152)) (ELit (1152)) (SA (EVar 10) (208)) (ELit (1))]
  32 [((EVar 2), (-1152), ELit 1152); ((EVar 10), (208), ELit 1)] [] (ELit (100)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 300 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
