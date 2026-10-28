(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmFloatXSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncBridges_u5 EncHtrans_u5 EncTail_u5 EncVisitNullB_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require Import FxKitX_u5 EncStransN_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_visit_double_nested_xsrc_T_u5 Cut_visit_double_nested_xsrc_u5 Cut_visit_double_root_xsrc_T_u5 Cut_visit_double_root_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVDB.
Import PMES.
(* [comment removed for export] *)
Import EVNB.
Module GN := Cut_visit_double_nested_xsrc_u5.  Module GNT := Cut_visit_double_nested_xsrc_T_u5.
Module GR := Cut_visit_double_root_xsrc_u5.    Module GRT := Cut_visit_double_root_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Definition RETPC : Z := 0x3c1fc.
Definition PCWD : Z := PC_WRITE_DOUBLE.
Definition WDSCR : Z := 9600.
(* [comment removed for export] *)
Definition WDA0 : expr := EAlu ALU_ADD (EVar 10) (ELit 252).
Definition WDA1 : expr := EAlu ALU_ADD (EVar 10) (ELit 8).
(* [comment removed for export] *)
Definition DEADPC (pc : Z) : bool := existsb (Z.eqb pc) [0x3bf70; 0x3bf0c; 0x3bf54; 0x3c03c; 0x3c220; 0x3c2c0].
Definition DMASK (m : Z) : kentry := KRange (EAlu ALU_SLTU (EAlu ALU_SUB (EAlu ALU_AND (EVar 41) (ELit m)) (ELit 0)) (ELit 1)) 0 0.
Definition dead_chk (cells : list kentry) : bool := existsb (fun m => PB.has cells (DMASK m)) [1; 2; 6; 8; 16; 48].
(* [comment removed for export] *)
Definition INL (pc : Z) : option (list nat) :=
  match pc with 0x3be50 => Some [] | 0x3bebc => Some [10%nat] | 0x3bec8 => Some [10%nat] | 0x3bee4 => Some [12%nat] | 0x3bf34 => Some [] | _ => None end.
Definition wd_chk (NF : nat) (hd : CH.hdecl) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  if (expr_eqb (nth 10 regs (ELit 0)) WDA0 && expr_eqb (nth 11 regs (ELit 0)) WDA1)%bool then ESTN.strans_chkN NF hd S2E 0 WDSCR (Some 0) c ps cj BLi BLj else None.

(* [comment removed for export] *)
Definition inl_j (RETS : list (nat * nat * nat * Z)) (CPS : list CC.cutpoint) (BLS : list CA.blocks) (NF : nat) (hv : list nat) (cond : nat -> bool) (i k : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  match CH2.ret_of RETS i k with
  | Some j => match nth_error CPS j with
              | Some cj => (FXK.inlF_chk NF c ps cj 4 hv && CH2.blocks_eqb (nth j BLS []) (nth i BLS []) && CH2.blocks_vars_lt (CC.cp_nx c) (nth i BLS []) && cond j)%bool
              | None => false end
  | None => false
  end.
Definition site_ok (pc : Z) (hv : list nat) : bool := match FXK.fp_site RSEGS pc with Some hv' => CA.regs_eqb (map EVar hv') (map EVar hv) | None => false end.

Lemma heap_ok3n : CH2.heap_chk3 GNT.NF GN.HDECL GN.BLS GN.CPS GN.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok3r : CH2.heap_chk3 GRT.NF GR.HDECL GR.BLS GR.CPS GR.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition inset (i : nat) (l : list nat) : bool := existsb (Nat.eqb i) l.
(* [comment removed for export] *)
Definition PA (i : nat) : bool := inset i [2; 4; 7; 8; 12; 13; 14; 18; 19; 20; 24; 25; 26; 30; 31; 32; 35; 36]%nat.
Definition PRE (i : nat) : bool := Nat.leb i 1.
Definition LD (i : nat) : bool := inset i [10; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36]%nat.
Definition AD (i : nat) : bool := inset i [21; 24; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36]%nat.
Definition WDD (i : nat) : bool := inset i [9; 12]%nat.
(* [comment removed for export] *)
Definition INLJ (i j : nat) : bool := (match i, j with 0, 1 | 1, 3 | 2, 4 | 3, 5 | 3, 6 | 4, 7 | 4, 8 | 6, 11 | 8, 14 => true | _, _ => false end)%nat.
(* [comment removed for export] *)
Definition tychk (i : nat) (pc : Z) (cells : list kentry) : bool :=
  if Nat.eqb i 0 then true else
  let tv := (if PA i || (Nat.eqb i 1 && Z.eqb pc PC_BEGIN_SCALAR) then 1 else 0)%bool in PB.has cells (KRange (EVar 38) tv tv).

Definition leaf_chkn (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (SP.F_sub (CC.cp_F c) F0N && Nat.leb GNT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GN.BLS []) BL1 && tychk i (SR.ps_pc ps) cells &&
   PB.has cells (KWord (SA ENDE (-8)) 8 (if Z.eqb (SR.ps_pc ps) RETPC then EAlu ALU_ADD (EVar 36) (ELit 1) else EVar 36))) &&
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc PC_BEGIN_SCALAR then
        (Nat.eqb i 1 && Z.eqb (SR.ps_pc ps) PC_BEGIN_SCALAR && call_j GN.RETS GN.CPS GN.BLS (EHT.hcall_chk GNT.NF GN.HDECL S2E BSSCR NEWS_BS) (fun j cj => Nat.eqb j 2 && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         PB.has cells (KWord (SA ENDE (-26)) 1 (EVar 40)))%bool
      else if Z.eqb pc PC_NULL_LIT then
        (Z.eqb (SR.ps_pc ps) PC_NULL_LIT && negb (PRE i) && negb (WDD i) &&
         call_j GN.RETS GN.CPS GN.BLS (lit_chk GNT.NF GN.HDECL) (fun j cj => Bool.eqb (PA j) (PA i) && Nat.leb 64 (CC.cp_nx cj) && Bool.eqb (AD j) (AD i) && negb (PRE j) && negb (WDD j) && LD j &&
                                                               (PB.has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40))))%bool i k c ps)%bool
      else if Z.eqb pc PML.PC_STR_APPEND then
        (Z.eqb (SR.ps_pc ps) PML.PC_STR_APPEND && LD i && negb (PRE i) && negb (WDD i) &&
         call_j GN.RETS GN.CPS GN.BLS (EB.sink_chk GNT.NF GN.HDECL S2E 0) (fun j cj => Bool.eqb (PA j) (PA i) && AD j && negb (AD i) && LD j && negb (PRE j) && negb (WDD j) && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (ELit LTXT) && expr_eqb (nth 12 regs (ELit 0)) (ELit 4) &&
         PB.has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40)))%bool
      else if Z.eqb pc PCWD then
        (Z.eqb (SR.ps_pc ps) PCWD && negb (PRE i) && negb (WDD i) && negb (AD i) && negb (LD i) &&
         call_j GN.RETS GN.CPS GN.BLS (wd_chk GNT.NF GN.HDECL) (fun j cj => Bool.eqb (PA j) (PA i) && WDD j && negb (AD j) && negb (LD j) && negb (PRE j) && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         PB.has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40)))%bool
      else if DEADPC pc then (negb (PRE i) && dead_chk cells)%bool
      else match INL pc with
      | Some hv => (Z.eqb (SR.ps_pc ps) pc && Z.leb 0 pc && Z.ltb (pc + 4) (2 ^ 64) && site_ok pc hv && inl_j GN.RETS GN.CPS GN.BLS GNT.NF hv (INLJ i) i k c ps &&
                    (PRE i || PB.has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40))))%bool
      | None =>
        (Z.eqb pc RETPC && (AD i || WDD i) && PB.exit_base_chk GNT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1) &&
         PB.has cells (KWord (SA ENDE (-8)) 8 (EAlu ALU_ADD (EVar 36) (ELit 1))) && PB.has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40)) &&
         PB.has cells (KWord (SA ENDE (-32)) 4 (EVar 38)) && PB.has cells (KWord (SA ENDE (-28)) 1 (ELit 0)))%bool
      end
  end.
Lemma leaf_okn : CH2.leaves_all GN.CPS GN.TAGS leaf_chkn = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition LDr (i : nat) : bool := inset i [6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%nat.
Definition ADr (i : nat) : bool := inset i [11; 14; 15; 16; 17; 18]%nat.
Definition WDDr (i : nat) : bool := Nat.eqb i 5.
Definition INLJr (i j : nat) : bool := (match i, j with 0, 1 | 1, 2 | 2, 3 | 2, 4 | 4, 7 => true | _, _ => false end)%nat.
Definition leaf_chkr (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (SP.F_sub (CC.cp_F c) F0R && Nat.leb GRT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GR.BLS []) []) &&
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc PC_NULL_LIT then
        (Z.eqb (SR.ps_pc ps) PC_NULL_LIT && negb (WDDr i) &&
         call_j GR.RETS GR.CPS GR.BLS (lit_chk GRT.NF GR.HDECL) (fun j cj => Nat.leb 64 (CC.cp_nx cj) && Bool.eqb (ADr j) (ADr i) && LDr j && negb (WDDr j))%bool i k c ps)%bool
      else if Z.eqb pc PML.PC_STR_APPEND then
        (Z.eqb (SR.ps_pc ps) PML.PC_STR_APPEND && LDr i && negb (ADr i) && negb (WDDr i) &&
         call_j GR.RETS GR.CPS GR.BLS (EB.sink_chk GRT.NF GR.HDECL S2E 0) (fun j cj => ADr j && LDr j && negb (WDDr j) && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (ELit LTXT) && expr_eqb (nth 12 regs (ELit 0)) (ELit 4))%bool
      else if Z.eqb pc PCWD then
        (Z.eqb (SR.ps_pc ps) PCWD && negb (WDDr i) && negb (ADr i) && negb (LDr i) &&
         call_j GR.RETS GR.CPS GR.BLS (wd_chk GRT.NF GR.HDECL) (fun j cj => WDDr j && negb (ADr j) && negb (LDr j) && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps)%bool
      else if DEADPC pc then dead_chk cells
      else match INL pc with
      | Some hv => (Z.eqb (SR.ps_pc ps) pc && Z.leb 0 pc && Z.ltb (pc + 4) (2 ^ 64) && site_ok pc hv && inl_j GR.RETS GR.CPS GR.BLS GRT.NF hv (INLJr i) i k c ps)%bool
      | None => (Z.eqb pc RETPC && (ADr i || WDDr i) && PB.exit_base_chk GRT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1))%bool
      end
  end.
Lemma leaf_okr : CH2.leaves_all GR.CPS GR.TAGS leaf_chkr = true.
Proof. vm_compute. reflexivity. Qed.

Ltac inlj_solve H := first [discriminate H | (repeat match goal with |- _ \/ _ => first [left; split; reflexivity | right] end; split; reflexivity)].
Lemma INLJ_cases : forall i j, INLJ i j = true ->
  ((i = 0 /\ j = 1) \/ (i = 1 /\ j = 3) \/ (i = 2 /\ j = 4) \/ (i = 3 /\ j = 5) \/ (i = 3 /\ j = 6) \/ (i = 4 /\ j = 7) \/ (i = 4 /\ j = 8) \/ (i = 6 /\ j = 11) \/ (i = 8 /\ j = 14))%nat.
Proof. intros i j H. unfold INLJ in H. do 9 (destruct i as [|i]; [do 15 (destruct j as [|j]; [inlj_solve H|]); discriminate H|]). discriminate H. Qed.
Lemma INLJr_cases : forall i j, INLJr i j = true -> ((i = 0 /\ j = 1) \/ (i = 1 /\ j = 2) \/ (i = 2 /\ j = 3) \/ (i = 2 /\ j = 4) \/ (i = 4 /\ j = 7))%nat.
Proof. intros i j H. unfold INLJr in H. do 5 (destruct i as [|i]; [do 8 (destruct j as [|j]; [inlj_solve H|]); discriminate H|]). discriminate H. Qed.
End EVDB.
