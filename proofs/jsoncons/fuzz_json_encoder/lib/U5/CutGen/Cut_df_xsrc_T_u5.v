(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(284632, 79%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 48.
Definition ENDS : list Z := [284868].
Definition HDECL : CH.hdecl := CH.HD (9200) (8224) [((EVar 11), (0), ELit 8)] [((EVar 32), (0), ELit 24)] [(73728, 77824)].
Definition CSUMS : list CA.callsum := [CAX.xs_cs (ESU.sink_xsum 436872 8496); CAX.xs_cs (ESU2N.pure0_xsum 734396 6144 (fun regs => let '(b, k) := split_lit (nth 10 regs (ELit 0)) in [(b, k, ELit 100)]) (fun regs g => let '(b, k) := split_lit (nth 10 regs (ELit 0)) in [KRange (EVar (g + 4)%nat) 1 25; KUnk (SA b k) (ELit 100)])); CAX.xs_cs (ESU2N.pure0_xsum 283948 9040 (fun regs => let '(b, k) := split_lit (nth 12 regs (ELit 0)) in [(b, k, ELit 8); (ELit 0, 905068, ELit 4)]) (fun regs g => let '(b, k) := split_lit (nth 12 regs (ELit 0)) in [KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EVar (g + 5)%nat) (ELit 22)) (ELit 1)) 0 0; KRange (EVar (g + 5)%nat) 0 34; KUnk (SA b k) (ELit 8)])); CAX.xs_cs (ESU2N.sinkN_xsum 278544 8608 (EVar 32) None); CA.cs_inline 284664 4 []; CA.cs_inline 284668 4 [11%nat]; CA.cs_inline 284756 4 []; CA.cs_inline 284764 4 [18%nat]; CA.cs_inline 284876 4 [10%nat]].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 284632 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; (EVar 11); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 10) (0) (255);
   KRange (EVar 11) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-9200)) (ELit (9200));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-9200)) (ELit (9200)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-9200)) (ELit (9200)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-9200)) (ELit (9200))]
  48 [((EVar 2), (-9200), ELit 9200)] [] (ELit (1048576)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 284772 [EVar 0; EVar 1; (APC.eaddz (EVar 2) (-160)); EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (EVar 11); (EVar 10); (EVar 10); (EVar 50); (ELit (75872)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; (EVar 48); EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KRange (EVar 10) (0) (255);
   KRange (EVar 11) (1099511627776) (140737488355328);
   KRange (EVar 32) (1099511627776) (140737488355328);
   KAlign (EVar 32) (8);
   KWr (SA (EVar 2) (-9200)) (ELit (9200));
   KRange (EVar 2) (1099511627776) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-9200)) (ELit (9200)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-9200)) (ELit (9200)) (SA (EVar 32) (0)) (ELit (24));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 32) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-9200)) (ELit (9040));
   KUnk (SA (EVar 2) (-160)) (ELit (112));
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KUnk (SA (EVar 2) (-48)) (ELit (8))]
  51 [((EVar 2), (-160), ELit 8)] [] (ELit (524288)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 600 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
