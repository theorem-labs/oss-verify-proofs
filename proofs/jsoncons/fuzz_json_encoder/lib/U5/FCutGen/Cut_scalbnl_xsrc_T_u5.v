(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(767004, 84%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 32.
Definition ENDS : list Z := [767336].
Definition CSUMS : list CAD.callsum := [(CAD.CSUM 745548 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false); (CAD.CSUM 746628 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 80 false false)].
Definition ASSUME : list (Z * (list expr -> list kentry -> list (list kentry * kentry))) := [].
Definition CASES : list (Z * list (nat * Z)) := [].
Definition RESPELL : list (Z * (list expr -> list kentry -> list (nat * expr))) := [].
Definition ECASES : list (Z * list ((list expr -> expr) * Z)) := [].
Definition NAMEB : list (Z * nat) := [].
Definition XSTOPS : list Z := [767004; 767028; 767052; 767076; 767100; 767124; 767148; 767172; 767196; 767220; 767244; 767268; 767292; 767316].
Definition HDECL : CH.hdecl := CH.HD (112) (8224) [] [] [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 767004 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (112))]
  32 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511627776)).
Definition BL0 : CAD.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 767104 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-32)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 47); (EVar 48); (EVar 49); (EVar 50)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (80));
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  51 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511626176)).
Definition BL1 : CAD.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 767196 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-32)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 47); (EVar 48); (EVar 49); (EVar 50)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (80));
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  51 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511624384)).
Definition BL2 : CAD.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CC.CP 767256 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-32)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 47); (EVar 48); (EVar 49); (EVar 50)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (80));
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  51 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511623936)).
Definition BL3 : CAD.blocks := [].
Definition hints3 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CC.CP 767260 [EVar 0; (EVar 32); (APC.eaddz (EVar 2) (-32)); EVar 3; EVar 4; (EVar 33); (EVar 34); (EVar 35); (EVar 36); (EVar 37); (EVar 38); (EVar 39); (EVar 40); (EVar 41); (EVar 42); (EVar 43); (EVar 44); (EVar 45); (EVar 46); EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; (EVar 47); (EVar 48); (EVar 49); (EVar 50)]
  [KRange (EVar 2) (140735332483184) (140737488355328);
   KAlign (EVar 2) (16);
   KImg (65536) (827984);
   KWr (SA (EVar 2) (-112)) (ELit (112));
   KUnk (SA (EVar 2) (-112)) (ELit (80));
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1)]
  51 [((EVar 2), (-112), ELit 112)] [] (ELit (1099511623680)).
Definition BL4 : CAD.blocks := [].
Definition hints4 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2; t3; t4].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CAD.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 40%nat [2%nat; 4%nat] XSTOPS ASSUME CASES NAMEB RESPELL ECASES (CC.cp_F c) (CC.cp_meas c) h 4000 first false 2%nat
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CAD.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CAD.po_leaves o)) (CC.cp_meas c).
