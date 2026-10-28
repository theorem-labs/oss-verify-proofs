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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncBridges_u5 EncHtrans_u5 EncStrans_u5 EncTail_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_visit_key_nested_xsrc_T_u5 Cut_visit_key_nested_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EVKB.
Import PMES.
Module GN := Cut_visit_key_nested_xsrc_u5.  Module GNT := Cut_visit_key_nested_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Definition RETPC : Z := Eval vm_compute in hd 0 GNT.ENDS.
Definition S2E : expr := EVar 32.
Definition SKE : expr := EAlu ALU_ADD (EVar 10) (ELit 8).
Definition ENDE : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (EVar 34).
Definition SCRW : Z := 10624.
Definition NLSCR : Z := 8576.       (* [comment removed for export] *)
Definition ESCSCR : Z := 8640.      (* [comment removed for export] *)
Definition F0N : list SGP.region := [(EVar 2, -10624, ELit 10624); (EVar 10, 296, ELit 8); (ENDE, -26, ELit 1); (ENDE, -16, ELit 8)].
Definition BL1 : CA.blocks := [(EVar 34, EVar 35)].
(* [comment removed for export] *)
Definition NEWS_NL : list kentry :=
  [KWord (SA ENDE (-32)) 4 (EVar 38); KWord (SA ENDE (-28)) 1 (ELit 0); KWord (SA ENDE (-26)) 1 (ELit 1); KWord (SA ENDE (-8)) 8 (EVar 36); KWr (SA ENDE (-16)) (ELit 8); KUnk (SA ENDE (-32)) (ELit 32)].

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
(* [comment removed for export] *)
Definition CP (i : nat) : bool := match i with 2 | 4 | 6 | 8 | 10 | 11 => true | _ => false end%nat.
(* [comment removed for export] *)
Definition NLD (i : nat) : bool := match i with 0 | 2 => false | _ => true end%nat.
(* [comment removed for export] *)
Definition Q1D (i : nat) : bool := match i with 0 | 1 | 2 | 4 => false | _ => true end%nat.
Definition ESD (i : nat) : bool := match i with 5 | 7 | 8 | 9 | 10 | 11 => true | _ => false end%nat.
Definition Q2D (i : nat) : bool := match i with 7 | 9 | 10 | 11 => true | _ => false end%nat.
Definition COLD (i : nat) : bool := match i with 9 | 11 => true | _ => false end%nat.
(* [comment removed for export] *)
Definition nla_e (i : nat) (pc : Z) : expr := if (NLD i || Z.eqb pc PC_NEW_LINE)%bool then ELit 1 else EVar 40.
(* [comment removed for export] *)
Definition cnt_k (i : nat) (pc : Z) : kentry :=
  if (CP i || (Nat.eqb i 0 && Z.eqb pc PML.PC_STR_APPEND))%bool then KRange (EVar 36) 1 18446744073709551615 else KRange (EVar 36) 0 0.

Lemma cnt_k_cases : forall i pc,
  (cnt_k i pc = KRange (EVar 36) 1 18446744073709551615 /\ (CP i = true \/ (i = 0%nat /\ pc = PML.PC_STR_APPEND))) \/
  (cnt_k i pc = KRange (EVar 36) 0 0 /\ CP i = false).
Proof.
  intros i pc. unfold cnt_k. destruct (CP i); [left; split; [reflexivity | left; reflexivity]|].
  destruct (Nat.eqb_spec i 0) as [->|Hi]; [|right; split; reflexivity].
  destruct (Z.eqb_spec pc PML.PC_STR_APPEND) as [->|Hp]; [left; split; [reflexivity | right; split; reflexivity] | right; split; reflexivity].
Qed.

Lemma cnt_k_sound : forall E (M : word -> option byte) cells i pc, know_ok RSEGS E M cells -> PB.has cells (cnt_k i pc) = true ->
  (CP i = true /\ 1 <= PB.uv E (EVar 36)) \/ (CP i = false /\ PB.uv E (EVar 36) = 0) \/ (i = 0%nat /\ pc = PML.PC_STR_APPEND).
Proof.
  intros E M cells i pc HK H. unfold cnt_k in H.
  destruct (CP i) eqn:EC.
  - left. split; [reflexivity|]. cbn [orb] in H. pose proof (PB.has_ok E M _ _ HK H) as Y. cbn [kentry_ok] in Y. unfold PB.uv. lia.
  - cbn [orb] in H. destruct (Nat.eqb_spec i 0) as [->|Hi].
    + destruct (Z.eqb_spec pc PML.PC_STR_APPEND) as [->|Hp]; [right; right; split; reflexivity|].
      cbn [andb] in H. right. left. split; [reflexivity|]. pose proof (PB.has_ok E M _ _ HK H) as Y. cbn [kentry_ok] in Y. unfold PB.uv. lia.
    + cbn [andb] in H. right. left. split; [reflexivity|]. pose proof (PB.has_ok E M _ _ HK H) as Y. cbn [kentry_ok] in Y. unfold PB.uv. lia.
Qed.

Lemma heap_ok3n : CH2.heap_chk3 GNT.NF GN.HDECL GN.BLS GN.CPS GN.TAGS = true.
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
Definition succ_ok (i : nat) (pc : Z) (j : nat) : bool :=
  (Bool.eqb (CP j) (CP i || Z.eqb pc PML.PC_STR_APPEND && Nat.eqb i 0) &&
   Bool.eqb (NLD j) (NLD i || Z.eqb pc PC_NEW_LINE) &&
   Bool.eqb (Q1D j) (Q1D i || Z.eqb pc PML.PC_STR_PUSH_BACK && negb (ESD i)) &&
   Bool.eqb (ESD j) (ESD i || Z.eqb pc PC_ESCAPE_STRING) &&
   Bool.eqb (Q2D j) (Q2D i || Z.eqb pc PML.PC_STR_PUSH_BACK && ESD i) &&
   Bool.eqb (COLD j) (COLD i || Z.eqb pc PML.PC_STR_APPEND && negb (Nat.eqb i 0)) && negb (Nat.eqb j 0))%bool.

Definition leaf_chkn (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
    (SP.F_sub (CC.cp_F c) F0N && Nat.leb GNT.NF (CC.cp_nx c) && CH2.blocks_eqb (nth i GN.BLS []) BL1 && Z.eqb (SR.ps_pc ps) pc &&
     PB.has cells (KWord (SA ENDE (-26)) 1 (nla_e i pc)) && PB.has cells (cnt_k i pc) &&
     PB.has cells (KWord (SA ENDE (-32)) 4 (EVar 38)) && PB.has cells (KWord (SA ENDE (-28)) 1 (ELit 0)) && PB.has cells (KWord (SA ENDE (-8)) 8 (EVar 36))) &&
    (if Z.eqb pc PC_NEW_LINE then
        (negb (NLD i) && call_j GN.RETS GN.CPS GN.BLS (EHT.hcall_chk GNT.NF GN.HDECL S2E NLSCR NEWS_NL) (fun j cj => succ_ok i pc j && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps)%bool
      else if Z.eqb pc PML.PC_STR_APPEND then
        (call_j GN.RETS GN.CPS GN.BLS (EB.sink_chk GNT.NF GN.HDECL S2E 0) (fun j cj => succ_ok i pc j && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         (if Nat.eqb i 0 then expr_eqb (nth 11 regs (ELit 0)) (ELit TXT_COMMA) else NLD i && Q2D i && negb (COLD i) && expr_eqb (nth 11 regs (ELit 0)) (ELit TXT_COLON)) &&
         expr_eqb (nth 12 regs (ELit 0)) (ELit 2))%bool
      else if Z.eqb pc PML.PC_STR_PUSH_BACK then
        (NLD i && Bool.eqb (Q1D i) (ESD i) && negb (Q2D i) && call_j GN.RETS GN.CPS GN.BLS (EB.pushb_chk GNT.NF GN.HDECL S2E 0) (fun j cj => succ_ok i pc j && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         expr_eqb (nth 11 regs (ELit 0)) (ELit 34))%bool
      else if Z.eqb pc PC_ESCAPE_STRING then
        (NLD i && Q1D i && negb (ESD i) &&
         call_j GN.RETS GN.CPS GN.BLS (EST.strans_chk GNT.NF GN.HDECL S2E 0 ESCSCR) (fun j cj => succ_ok i pc j && Nat.leb 64 (CC.cp_nx cj))%bool i k c ps &&
         expr_eqb (nth 10 regs (ELit 0)) (EVar 41) && expr_eqb (nth 11 regs (ELit 0)) (EVar 42) && expr_eqb (nth 12 regs (ELit 0)) (ELit 0) &&
         expr_eqb (nth 13 regs (ELit 0)) (ELit 0) && expr_eqb (nth 14 regs (ELit 0)) SKE)%bool
      else
        (Z.eqb pc RETPC && COLD i && PB.exit_base_chk GNT.NF RETPC c ps && CL.ps_reg_is ps 10 (ELit 1))%bool)
  end%bool.
Lemma leaf_okn : CH2.leaves_all GN.CPS GN.TAGS leaf_chkn = true.
Proof. vm_compute. reflexivity. Qed.
End EVKB.
