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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncBridges_u5 EncHtrans_u5 EncTail_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_visit_null_nested_xsrc_T_u5 Cut_visit_null_nested_xsrc_u5 Cut_visit_null_root_xsrc_T_u5 Cut_visit_null_root_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVNB.
Import PMES.
Module GN := Cut_visit_null_nested_xsrc_u5.  Module GNT := Cut_visit_null_nested_xsrc_T_u5.
Module GR := Cut_visit_null_root_xsrc_u5.    Module GRT := Cut_visit_null_root_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Definition RETPC : Z := Eval vm_compute in hd 0 GNT.ENDS.
Definition S2E : expr := EVar 32.
Definition ENDE : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34).
Definition SCRW : Z := 10624.
Definition BSSCR : Z := 8592.       (* [comment removed for export] *)
Definition LITSCR : Z := 64.
Definition LS_ : Z := PML.LIT_NULL_S.  Definition LTXT : Z := PML.LIT_NULL_TXT.  Definition LLEN : Z := 4.
Definition F0N : list SGP.region := [(EVar 2, -10624, ELit 10624); (EVar 10, 296, ELit 8); (ENDE, -8, ELit 8)].
Definition F0R : list SGP.region := [(EVar 2, -10624, ELit 10624); (EVar 10, 296, ELit 8)].
Definition BL1 : CA.blocks := [(EVar 34, EVar 35)].
(* [comment removed for export] *)
Definition NEWS_BS : list kentry :=
  [KWord (SA ENDE (-32)) 4 (EVar 38); KWord (SA ENDE (-28)) 1 (ELit 0); KWord (SA ENDE (-26)) 1 (ELit 1); KWord (SA ENDE (-8)) 8 (EVar 36); KWr (SA ENDE (-8)) (ELit 8); KUnk (SA ENDE (-32)) (ELit 32)].
(* [comment removed for export] *)
Definition lit_chk (NF : nat) (hd : CH.hdecl) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let nx := (CC.cp_nx cj - APC.NCS)%nat in
  if CH2.blocks_eqb BLj BLi then CH2.custom_chk NF hd LITSCR 0 BLi [(ELit 0, LS_, ELit 18)] (KRange (EVar (nx + 5)) LLEN LLEN :: ESU2.lit_news LS_ LTXT LLEN) (Some (ELit LTXT)) c ps cj BLi
  else None.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
(* [comment removed for export] *)
Definition PA (i : nat) : bool := match i with 1 | 3 | 5 | 7 | 9 => true | _ => false end%nat.
(* [comment removed for export] *)
Definition LD (i : nat) : bool := Nat.leb 2 i.
(* [comment removed for export] *)
Definition AD (i : nat) : bool := Nat.leb 6 i.

Lemma heap_ok3n : CH2.heap_chk3 GNT.NF GN.HDECL GN.BLS GN.CPS GN.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok3r : CH2.heap_chk3 GRT.NF GR.HDECL GR.BLS GR.CPS GR.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition call_j (RETS : list (nat * nat * nat * Z)) (CPS : list CC.cutpoint) (BLS : list CA.blocks)
           (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (cond : nat -> CC.cutpoint -> bool) (i k : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  match CH2.ret_of RETS i k with
  | Some j => match nth_error CPS j with
              | Some cj => (isSome (f c ps cj (nth i BLS []) (nth j BLS [])) && cond j cj)%bool
              | None => false end
  | None => false
  end.

(* [comment removed for export] *)
Definition leaf_chkn (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (SP.F_sub (CC.cp_F c) F0N && Nat.leb GNT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GN.BLS []) BL1 &&
   PB.has cells (KRange (EVar 38) (if PA i || (Nat.eqb i 0 && Z.eqb (SR.ps_pc ps) PC_BEGIN_SCALAR) then 1 else 0)%bool (if PA i || (Nat.eqb i 0 && Z.eqb (SR.ps_pc ps) PC_BEGIN_SCALAR) then 1 else 0)%bool) &&
   PB.has cells (KWord (SA ENDE (-8)) 8 (if Z.eqb (SR.ps_pc ps) RETPC then EAlu ALU_ADD (EVar 36) (ELit 1) else EVar 36))) &&
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc PC_BEGIN_SCALAR then
        (Nat.eqb i 0 && Z.eqb (SR.ps_pc ps) PC_BEGIN_SCALAR && call_j GN.RETS GN.CPS GN.BLS (EHT.hcall_chk GNT.NF GN.HDECL S2E BSSCR NEWS_BS) (fun j cj => Nat.eqb j 1 && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         PB.has cells (KWord (SA ENDE (-26)) 1 (EVar 40)))%bool
      else if Z.eqb pc PC_NULL_LIT then
        (Z.eqb (SR.ps_pc ps) PC_NULL_LIT &&
         call_j GN.RETS GN.CPS GN.BLS (lit_chk GNT.NF GN.HDECL) (fun j cj => Bool.eqb (PA j) (PA i || Nat.eqb i 0 && false)%bool && Nat.leb 64 (CC.cp_nx cj) && Bool.eqb (AD j) (AD i) && negb (Nat.eqb j 0) &&
                                                               (PB.has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40))))%bool i k c ps)%bool
      else if Z.eqb pc PML.PC_STR_APPEND then
        (Z.eqb (SR.ps_pc ps) PML.PC_STR_APPEND && LD i &&
         call_j GN.RETS GN.CPS GN.BLS (EB.sink_chk GNT.NF GN.HDECL S2E 0) (fun j cj => Bool.eqb (PA j) (PA i) && AD j && negb (AD i) && Nat.leb 64 (CC.cp_nx cj) && negb (Nat.eqb j 0) && negb (Nat.eqb i 0))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (ELit LTXT) && expr_eqb (nth 12 regs (ELit 0)) (ELit 4) &&
         PB.has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40)))%bool
      else
        (Z.eqb pc RETPC && AD i && PB.exit_base_chk GNT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1) &&
         PB.has cells (KWord (SA ENDE (-8)) 8 (EAlu ALU_ADD (EVar 36) (ELit 1))) && PB.has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40)) &&
         PB.has cells (KWord (SA ENDE (-32)) 4 (EVar 38)) && PB.has cells (KWord (SA ENDE (-28)) 1 (ELit 0)))%bool
  end.
Lemma leaf_okn : CH2.leaves_all GN.CPS GN.TAGS leaf_chkn = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition leaf_chkr (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (SP.F_sub (CC.cp_F c) F0R && Nat.leb GRT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GR.BLS []) []) &&
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc PC_NULL_LIT then
        (Z.eqb (SR.ps_pc ps) PC_NULL_LIT &&
         call_j GR.RETS GR.CPS GR.BLS (lit_chk GRT.NF GR.HDECL) (fun j cj => Nat.leb 64 (CC.cp_nx cj) && Bool.eqb (Nat.leb 3 j) (Nat.leb 3 i))%bool i k c ps)%bool
      else if Z.eqb pc PML.PC_STR_APPEND then
        (Z.eqb (SR.ps_pc ps) PML.PC_STR_APPEND && Nat.eqb i 2 &&
         call_j GR.RETS GR.CPS GR.BLS (EB.sink_chk GRT.NF GR.HDECL S2E 0) (fun j cj => Nat.eqb j 3 && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (ELit LTXT) && expr_eqb (nth 12 regs (ELit 0)) (ELit 4))%bool
      else
        (Z.eqb pc RETPC && Nat.eqb i 4 && PB.exit_base_chk GRT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1))%bool
  end.
Lemma leaf_okr : CH2.leaves_all GR.CPS GR.TAGS leaf_chkr = true.
Proof. vm_compute. reflexivity. Qed.
End EVNB.
