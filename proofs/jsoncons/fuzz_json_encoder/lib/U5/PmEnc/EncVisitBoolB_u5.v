(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core StreamSim. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncBridges_u5 EncHtrans_u5 EncTail_u5 EncVisitNullB_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_visit_bool_nested_xsrc_T_u5 Cut_visit_bool_nested_xsrc_u5 Cut_visit_bool_root_xsrc_T_u5 Cut_visit_bool_root_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVBB.
Import PMES.
(* [comment removed for export] *)
Import EVNB.
Module GN := Cut_visit_bool_nested_xsrc_u5.  Module GNT := Cut_visit_bool_nested_xsrc_T_u5.
Module GR := Cut_visit_bool_root_xsrc_u5.    Module GRT := Cut_visit_bool_root_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Definition RETPC : Z := Eval vm_compute in hd 0 GNT.ENDS.
(* [comment removed for export] *)
Definition PCf (f : bool) : Z := if f then PC_TRUE_LIT else PC_FALSE_LIT.
Definition LSf (f : bool) : Z := if f then PML.LIT_TRUE_S else PML.LIT_FALSE_S.
Definition LGf (f : bool) : Z := if f then PML.LIT_TRUE_G else PML.LIT_FALSE_G.
Definition LTXTf (f : bool) : Z := if f then PML.LIT_TRUE_TXT else PML.LIT_FALSE_TXT.
Definition LLENf (f : bool) : Z := if f then 4 else 5.
Definition TXTB (f : bool) : list Z := if f then [116; 114; 117; 101] else [102; 97; 108; 115; 101].
Lemma LGf_eq : forall f, LGf f = LSf f + 16. Proof. intros []; reflexivity. Qed.
Lemma LLENf_len : forall f, len (TXTB f) = LLENf f. Proof. intros []; reflexivity. Qed.
(* [comment removed for export] *)
Definition lit_chk (f : bool) (NF : nat) (hd : CH.hdecl) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let nx := (CC.cp_nx cj - APC.NCS)%nat in
  if CH2.blocks_eqb BLj BLi then CH2.custom_chk NF hd LITSCR 0 BLi [(ELit 0, LSf f, ELit 18)] (KRange (EVar (nx + 5)) (LLENf f) (LLENf f) :: ESU2.lit_news (LSf f) (LTXTf f) (LLENf f)) (Some (ELit (LTXTf f))) c ps cj BLi
  else None.
(* [comment removed for export] *)
Definition famK (f : bool) : kentry := KRange (EVar 11) (PML.b2z f) (PML.b2z f).

Lemma heap_ok3n : CH2.heap_chk3 GNT.NF GN.HDECL GN.BLS GN.CPS GN.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma heap_ok3r : CH2.heap_chk3 GRT.NF GR.HDECL GR.BLS GR.CPS GR.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

(* [comment removed for export] *)
Definition PA (i : nat) : bool := match i with 1 | 4 | 5 | 8 | 9 | 12 | 13 | 16 | 17 => true | _ => false end%nat.
(* [comment removed for export] *)
Definition TFn (i : nat) : bool := match i with 3 | 5 | 7 | 9 | 11 | 13 | 15 | 17 => true | _ => false end%nat.
(* [comment removed for export] *)
Definition LD (i : nat) : bool := Nat.leb 2 i.
Definition AD (i : nat) : bool := Nat.leb 10 i.

Definition lit_leaf_n (f : bool) (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (Z.eqb (SR.ps_pc ps) (PCf f) && PB.has cells (famK f) && implb (LD i) (Bool.eqb (TFn i) f) &&
   call_j GN.RETS GN.CPS GN.BLS (lit_chk f GNT.NF GN.HDECL)
      (fun j cj => Bool.eqb (PA j) (PA i) && Nat.leb 64 (CC.cp_nx cj) && Bool.eqb (AD j) (AD i) && negb (Nat.eqb j 0) && Bool.eqb (TFn j) f && LD j &&
                   (PB.has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40))))%bool i k c ps)%bool.

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
      else if Z.eqb pc PC_TRUE_LIT then lit_leaf_n true i c k ps
      else if Z.eqb pc PC_FALSE_LIT then lit_leaf_n false i c k ps
      else if Z.eqb pc PML.PC_STR_APPEND then
        (Z.eqb (SR.ps_pc ps) PML.PC_STR_APPEND && LD i && PB.has cells (famK (TFn i)) &&
         call_j GN.RETS GN.CPS GN.BLS (EB.sink_chk GNT.NF GN.HDECL S2E 0) (fun j cj => Bool.eqb (PA j) (PA i) && AD j && negb (AD i) && Nat.leb 64 (CC.cp_nx cj) && negb (Nat.eqb j 0) && negb (Nat.eqb i 0) &&
                                                                         Bool.eqb (TFn j) (TFn i))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (ELit (LTXTf (TFn i))) && expr_eqb (nth 12 regs (ELit 0)) (ELit (LLENf (TFn i))) &&
         PB.has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40)))%bool
      else
        (Z.eqb pc RETPC && AD i && PB.exit_base_chk GNT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1) && PB.has cells (famK (TFn i)) &&
         PB.has cells (KWord (SA ENDE (-8)) 8 (EAlu ALU_ADD (EVar 36) (ELit 1))) && PB.has cells (KWord (SA ENDE (-26)) 1 (if PA i then ELit 1 else EVar 40)) &&
         PB.has cells (KWord (SA ENDE (-32)) 4 (EVar 38)) && PB.has cells (KWord (SA ENDE (-28)) 1 (ELit 0)))%bool
  end.
Lemma leaf_okn : CH2.leaves_all GN.CPS GN.TAGS leaf_chkn = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition TFr (i : nat) : bool := match i with 2 | 4 | 6 | 8 => true | _ => false end%nat.
Definition LDr (i : nat) : bool := Nat.leb 1 i.
Definition ADr (i : nat) : bool := Nat.leb 5 i.
Definition lit_leaf_r (f : bool) (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (Z.eqb (SR.ps_pc ps) (PCf f) && PB.has cells (famK f) && implb (LDr i) (Bool.eqb (TFr i) f) &&
   call_j GR.RETS GR.CPS GR.BLS (lit_chk f GRT.NF GR.HDECL)
      (fun j cj => Nat.leb 64 (CC.cp_nx cj) && Bool.eqb (ADr j) (ADr i) && negb (Nat.eqb j 0) && Bool.eqb (TFr j) f && LDr j)%bool i k c ps)%bool.
Definition leaf_chkr (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  (SP.F_sub (CC.cp_F c) F0R && Nat.leb GRT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GR.BLS []) []) &&
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if Z.eqb pc PC_TRUE_LIT then lit_leaf_r true i c k ps
      else if Z.eqb pc PC_FALSE_LIT then lit_leaf_r false i c k ps
      else if Z.eqb pc PML.PC_STR_APPEND then
        (Z.eqb (SR.ps_pc ps) PML.PC_STR_APPEND && LDr i && negb (ADr i) && PB.has cells (famK (TFr i)) &&
         call_j GR.RETS GR.CPS GR.BLS (EB.sink_chk GRT.NF GR.HDECL S2E 0) (fun j cj => ADr j && Nat.leb 64 (CC.cp_nx cj) && Bool.eqb (TFr j) (TFr i))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (ELit (LTXTf (TFr i))) && expr_eqb (nth 12 regs (ELit 0)) (ELit (LLENf (TFr i))))%bool
      else
        (Z.eqb pc RETPC && ADr i && PB.exit_base_chk GRT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1) && PB.has cells (famK (TFr i)))%bool
  end.
Lemma leaf_okr : CH2.leaves_all GR.CPS GR.TAGS leaf_chkr = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Ltac ulit := unfold LSf, LGf, LTXTf, LLENf, PCf, PML.LIT_LO, PML.LIT_HI, PML.LIT_NULL_S, PML.LIT_NULL_G, PML.LIT_NULL_TXT, PML.LIT_TRUE_S, PML.LIT_TRUE_G, PML.LIT_TRUE_TXT, PML.LIT_FALSE_S, PML.LIT_FALSE_G, PML.LIT_FALSE_TXT.
Ltac ulit_in H := unfold LSf, LGf, LTXTf, LLENf, PCf, PML.LIT_LO, PML.LIT_HI, PML.LIT_NULL_S, PML.LIT_NULL_G, PML.LIT_NULL_TXT, PML.LIT_TRUE_S, PML.LIT_TRUE_G, PML.LIT_TRUE_TXT, PML.LIT_FALSE_S, PML.LIT_FALSE_G, PML.LIT_FALSE_TXT in H.
Ltac lit_tac := intros i Hi; cbn [length] in Hi; repeat (destruct i as [|i]; [vm_compute; reflexivity|]); exfalso; lia.
Lemma txt_f : forall f, L5.bytes_at RSEGS (fun _ => None) (LTXTf f) (TXTB f).
Proof. intros [|]; ulit; cbn [TXTB]; lit_tac. Qed.
Lemma lit_wrf : forall f, StreamSim.wseg_ok RSEGS (Z_to_bv 64 (LSf f)) 18 = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma LSf_range : forall f, PML.LIT_LO + 24 <= LSf f /\ LSf f + 18 <= PML.LIT_HI /\ (LSf f = 898528 \/ LSf f = 898552).
Proof. intros [|]; ulit; lia. Qed.
Lemma LTXTf_range : forall f, 0x10000 <= LTXTf f /\ LTXTf f + LLENf f <= 0x12000.
Proof. intros [|]; ulit; lia. Qed.
(* [comment removed for export] *)
Lemma LITKf : forall f (M1 M2 : word -> option byte), (forall a, PML.LIT_LO <= a < PML.LIT_HI -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (PML.lits_ok M1 -> PML.lits_ok M2) /\ (lit_done M1 (LSf f) (LGf f) (LTXTf f) (LLENf f) -> lit_done M2 (LSf f) (LGf f) (LTXTf f) (LLENf f)).
Proof.
  intros f M1 M2 HE. split; [exact (PML.lits_ok_agree M1 M2 HE)|]. rewrite LGf_eq. pose proof (LSf_range f) as (R1 & R2 & _). intros (Q1 & Q2 & Q3 & Q4). unfold lit_done.
  assert (AGL : forall a n, LSf f <= a -> a + n <= LSf f + 18 -> L5C.agree_on M1 M2 a n).
  { intros a n Ha Hn z Hz. apply HE. unfold PML.LIT_LO, PML.LIT_HI in *. lia. }
  unfold PML.LIT_LO, PML.LIT_HI in *.
  split; [apply (EK.u8_agree M1 M2); [apply AGL; lia | lia | lia | exact Q1]|]. split; [apply (EK.u8_agree M1 M2); [apply AGL; lia | lia | lia | exact Q2]|].
  split; [apply (EK.u64_agree M1 M2); [apply AGL; lia | lia | lia | exact Q3] | apply (EK.u64_agree M1 M2); [apply AGL; lia | lia | lia | exact Q4]].
Qed.
(* [comment removed for export] *)
Lemma lits_upd : forall f (M1 M2 : word -> option byte), PML.lits_ok M1 ->
  (forall a, PML.LIT_LO <= a < PML.LIT_HI -> ~ (LSf f <= a < LSf f + 18) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  lit_done M2 (LSf f) (LGf f) (LTXTf f) (LLENf f) -> PML.lits_ok M2.
Proof.
  intros f M1 M2 (LN & LT & LF) HE HD. unfold lit_done in HD. rewrite LGf_eq in HD.
  assert (FRM : forall S G txt n, PML.LIT_LO <= S -> S + 18 <= PML.LIT_HI -> G = S + 16 -> (S + 18 <= LSf f \/ LSf f + 18 <= S) -> PML.lit_ok M1 S G txt n -> PML.lit_ok M2 S G txt n).
  { intros S G txt n H1 H2 -> H4 HL. assert (AG : L5C.agree_on M1 M2 S 18) by (intros z Hz; apply HE; lia).
    destruct HL as [(Y1 & Y2 & Y3 & Y4)|(Y1 & Y2 & Y3 & Y4)]; [left|right]; repeat split;
      first [apply (EK.u8_agree M1 M2); [intros z Hz; apply AG; lia | unfold PML.LIT_LO in *; lia | unfold PML.LIT_HI in *; lia | assumption]
            | apply (EK.u64_agree M1 M2); [intros z Hz; apply AG; lia | unfold PML.LIT_LO in *; lia | unfold PML.LIT_HI in *; lia | assumption]]. }
  Ltac frm FRM H := apply FRM; [ulit; lia | ulit; lia | ulit; reflexivity | ulit; lia | exact H].
  destruct f; cbn [LSf LGf LTXTf LLENf] in *; unfold PML.lits_ok.
  - split; [frm FRM LN|]. split; [right; exact HD | frm FRM LF].
  - split; [frm FRM LN|]. split; [frm FRM LT | right; exact HD].
Qed.
End EVBB.
