(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncBridges_u5 EncHcol_u5 EncTail_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_visit_end_array_deep_xsrc_T_u5 Cut_visit_end_array_deep_xsrc_u5 Cut_visit_end_array_last_xsrc_T_u5 Cut_visit_end_array_last_xsrc_u5
                    Cut_visit_end_object_deep_xsrc_T_u5 Cut_visit_end_object_deep_xsrc_u5 Cut_visit_end_object_last_xsrc_T_u5 Cut_visit_end_object_last_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVEB.
Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Definition S2E : expr := EVar 32.
Definition ENDE : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34).
Definition ENDP : expr := EAlu ALU_ADD ENDE (ELit (-32)).
Definition INDE : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 33)) (ELit (-4)).
Definition DEPE : expr := EAlu ALU_ADD (EVar 33) (ELit (-1)).
Definition SCRW : Z := 10624.
Definition NLSCR : Z := 8576.
Definition BL1 : CA.blocks := [(EVar 34, EVar 35)].
Definition F0D : list SGP.region := [(EVar 2, -10624, ELit 10624); (EVar 10, 272, ELit 8); (EVar 10, 288, ELit 4); (EVar 10, 296, ELit 8); (EVar 10, 400, ELit 4); (ENDE, -40, ELit 8)].
Definition F0L : list SGP.region := [(EVar 2, -10624, ELit 10624); (EVar 10, 272, ELit 8); (EVar 10, 288, ELit 4); (EVar 10, 296, ELit 8); (EVar 10, 400, ELit 4)].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition call_j (RETS : list (nat * nat * nat * Z)) (CPS : list CC.cutpoint) (BLS : list CA.blocks)
           (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (cond : nat -> CC.cutpoint -> bool) (i k : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  match CH2.ret_of RETS i k with
  | Some j => match nth_error CPS j with
              | Some cj => (isSome (f c ps cj (nth i BLS []) (nth j BLS [])) && cond j cj)%bool
              | None => false end
  | None => false
  end.
(* [comment removed for export] *)
Definition NLP (i : nat) (pc : Z) : bool := match i with 0%nat => Z.eqb pc PC_NEW_LINE | 1%nat => false | _ => true end.
Definition nla_k (i : nat) (pc : Z) : kentry := if NLP i pc then KRange (EVar 40) 1 1 else KRange (EVar 40) 0 0.

Module AD.
Module GN := Cut_visit_end_array_deep_xsrc_u5.  Module GNT := Cut_visit_end_array_deep_xsrc_T_u5.
Definition RETPC : Z := Eval vm_compute in hd 0 GNT.ENDS.
Definition CLOSE_TXT : Z := TXT_CBRACKET.
Definition F0 : list SGP.region := F0D.
Lemma heap_ok3 : CH2.heap_chk3 GNT.NF GN.HDECL GN.BLS GN.CPS GN.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
    (SP.F_sub (CC.cp_F c) F0 && Nat.leb GNT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GN.BLS []) BL1 && Z.eqb (SR.ps_pc ps) pc &&
     PB.has cells (KWord (SA (EVar 10) 288) 4 INDE) && PB.has cells (KWord (SA (EVar 10) 400) 4 DEPE) && PB.has cells (nla_k i pc) && PB.has cells (KWord (SA ENDE (-40)) 8 (if Z.eqb pc RETPC then EAlu ALU_ADD (EVar 41) (ELit 1) else EVar 41))) &&
    (if Z.eqb pc PC_NEW_LINE then
        (Nat.eqb i 0 && PB.has cells (KWord (SA (EVar 10) 272) 8 ENDE) &&
         call_j GN.RETS GN.CPS GN.BLS (EHC.hcol_chk GNT.NF GN.HDECL S2E NLSCR) (fun j cj => Nat.eqb j 2 && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps)%bool
      else if Z.eqb pc PML.PC_STR_APPEND then
        ((Nat.eqb i 0 || Nat.eqb i 2) && PB.has cells (KWord (SA (EVar 10) 272) 8 ENDP) &&
         call_j GN.RETS GN.CPS GN.BLS (EB.sink_chk GNT.NF GN.HDECL S2E 0) (fun j cj => Nat.eqb j (if Nat.eqb i 0 then 1 else 3)%nat && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (ELit CLOSE_TXT) && expr_eqb (nth 12 regs (ELit 0)) (ELit 1))%bool
      else
        (Z.eqb pc RETPC && (Nat.eqb i 1 || Nat.eqb i 3) && PB.has cells (KWord (SA (EVar 10) 272) 8 ENDP) && PB.exit_base_chk GNT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1) )%bool)
  end%bool.
Lemma leaf_ok : CH2.leaves_all GN.CPS GN.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
End AD.

Module AL.
Module GN := Cut_visit_end_array_last_xsrc_u5.  Module GNT := Cut_visit_end_array_last_xsrc_T_u5.
Definition RETPC : Z := Eval vm_compute in hd 0 GNT.ENDS.
Definition CLOSE_TXT : Z := TXT_CBRACKET.
Definition F0 : list SGP.region := F0L.
Lemma heap_ok3 : CH2.heap_chk3 GNT.NF GN.HDECL GN.BLS GN.CPS GN.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
    (SP.F_sub (CC.cp_F c) F0 && Nat.leb GNT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GN.BLS []) BL1 && Z.eqb (SR.ps_pc ps) pc &&
     PB.has cells (KWord (SA (EVar 10) 288) 4 (ELit 0)) && PB.has cells (KWord (SA (EVar 10) 400) 4 (ELit 0)) && PB.has cells (nla_k i pc) ) &&
    (if Z.eqb pc PC_NEW_LINE then
        (Nat.eqb i 0 && PB.has cells (KWord (SA (EVar 10) 272) 8 ENDE) &&
         call_j GN.RETS GN.CPS GN.BLS (EHC.hcol_chk GNT.NF GN.HDECL S2E NLSCR) (fun j cj => Nat.eqb j 2 && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps)%bool
      else if Z.eqb pc PML.PC_STR_APPEND then
        ((Nat.eqb i 0 || Nat.eqb i 2) && PB.has cells (KWord (SA (EVar 10) 272) 8 ENDP) &&
         call_j GN.RETS GN.CPS GN.BLS (EB.sink_chk GNT.NF GN.HDECL S2E 0) (fun j cj => Nat.eqb j (if Nat.eqb i 0 then 1 else 3)%nat && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (ELit CLOSE_TXT) && expr_eqb (nth 12 regs (ELit 0)) (ELit 1))%bool
      else
        (Z.eqb pc RETPC && (Nat.eqb i 1 || Nat.eqb i 3) && PB.has cells (KWord (SA (EVar 10) 272) 8 ENDP) && PB.exit_base_chk GNT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1) )%bool)
  end%bool.
Lemma leaf_ok : CH2.leaves_all GN.CPS GN.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
End AL.

Module OD.
Module GN := Cut_visit_end_object_deep_xsrc_u5.  Module GNT := Cut_visit_end_object_deep_xsrc_T_u5.
Definition RETPC : Z := Eval vm_compute in hd 0 GNT.ENDS.
Definition CLOSE_TXT : Z := TXT_CBRACE.
Definition F0 : list SGP.region := F0D.
Lemma heap_ok3 : CH2.heap_chk3 GNT.NF GN.HDECL GN.BLS GN.CPS GN.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
    (SP.F_sub (CC.cp_F c) F0 && Nat.leb GNT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GN.BLS []) BL1 && Z.eqb (SR.ps_pc ps) pc &&
     PB.has cells (KWord (SA (EVar 10) 288) 4 INDE) && PB.has cells (KWord (SA (EVar 10) 400) 4 DEPE) && PB.has cells (nla_k i pc) && PB.has cells (KWord (SA ENDE (-40)) 8 (if Z.eqb pc RETPC then EAlu ALU_ADD (EVar 41) (ELit 1) else EVar 41))) &&
    (if Z.eqb pc PC_NEW_LINE then
        (Nat.eqb i 0 && PB.has cells (KWord (SA (EVar 10) 272) 8 ENDE) &&
         call_j GN.RETS GN.CPS GN.BLS (EHC.hcol_chk GNT.NF GN.HDECL S2E NLSCR) (fun j cj => Nat.eqb j 2 && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps)%bool
      else if Z.eqb pc PML.PC_STR_APPEND then
        ((Nat.eqb i 0 || Nat.eqb i 2) && PB.has cells (KWord (SA (EVar 10) 272) 8 ENDP) &&
         call_j GN.RETS GN.CPS GN.BLS (EB.sink_chk GNT.NF GN.HDECL S2E 0) (fun j cj => Nat.eqb j (if Nat.eqb i 0 then 1 else 3)%nat && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (ELit CLOSE_TXT) && expr_eqb (nth 12 regs (ELit 0)) (ELit 1))%bool
      else
        (Z.eqb pc RETPC && (Nat.eqb i 1 || Nat.eqb i 3) && PB.has cells (KWord (SA (EVar 10) 272) 8 ENDP) && PB.exit_base_chk GNT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1) )%bool)
  end%bool.
Lemma leaf_ok : CH2.leaves_all GN.CPS GN.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
End OD.

Module OL.
Module GN := Cut_visit_end_object_last_xsrc_u5.  Module GNT := Cut_visit_end_object_last_xsrc_T_u5.
Definition RETPC : Z := Eval vm_compute in hd 0 GNT.ENDS.
Definition CLOSE_TXT : Z := TXT_CBRACE.
Definition F0 : list SGP.region := F0L.
Lemma heap_ok3 : CH2.heap_chk3 GNT.NF GN.HDECL GN.BLS GN.CPS GN.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
    (SP.F_sub (CC.cp_F c) F0 && Nat.leb GNT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GN.BLS []) BL1 && Z.eqb (SR.ps_pc ps) pc &&
     PB.has cells (KWord (SA (EVar 10) 288) 4 (ELit 0)) && PB.has cells (KWord (SA (EVar 10) 400) 4 (ELit 0)) && PB.has cells (nla_k i pc) ) &&
    (if Z.eqb pc PC_NEW_LINE then
        (Nat.eqb i 0 && PB.has cells (KWord (SA (EVar 10) 272) 8 ENDE) &&
         call_j GN.RETS GN.CPS GN.BLS (EHC.hcol_chk GNT.NF GN.HDECL S2E NLSCR) (fun j cj => Nat.eqb j 2 && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps)%bool
      else if Z.eqb pc PML.PC_STR_APPEND then
        ((Nat.eqb i 0 || Nat.eqb i 2) && PB.has cells (KWord (SA (EVar 10) 272) 8 ENDP) &&
         call_j GN.RETS GN.CPS GN.BLS (EB.sink_chk GNT.NF GN.HDECL S2E 0) (fun j cj => Nat.eqb j (if Nat.eqb i 0 then 1 else 3)%nat && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (ELit CLOSE_TXT) && expr_eqb (nth 12 regs (ELit 0)) (ELit 1))%bool
      else
        (Z.eqb pc RETPC && (Nat.eqb i 1 || Nat.eqb i 3) && PB.has cells (KWord (SA (EVar 10) 272) 8 ENDP) && PB.exit_base_chk GNT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1) )%bool)
  end%bool.
Lemma leaf_ok : CH2.leaves_all GN.CPS GN.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.
End OL.
End EVEB.
