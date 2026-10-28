(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseBridges5_u ParseSomeAt_u ParseSomeSem_u ParseSomeChk_u ParseSomeChk2_u ParseSomeChk3_u ParseSomeA_u ParseSomeB_u ParseSomeC_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PSR.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Definition slot_of (regs : list expr) (v : nat) : option nat := find (fun r => expr_eqb (nth r regs (ELit 0)) (EVar v)) (seq 1 31).
Definition mkE2 (regs : list expr) (E' : env) (R' : bvmap 5 word) (sem : list word) : env :=
  Env (fun v => if Nat.ltb v 49 then ev E' v else if Nat.ltb v 66 then nth (v - 49) sem (Z_to_bv 64 0)
                else match slot_of regs v with Some r => getr R' (Z_to_bv 5 (Z.of_nat r)) | None => Z_to_bv 64 0 end) (eb E').

Definition slots_chk (regs : list expr) (hpc : bool) : bool :=
  (Nat.eqb (length regs) 32 &&
   forallb (fun n => match nth n regs (ELit 0) with
                     | EVar v => if Nat.leb 66 v then match slot_of regs v with Some r => Nat.eqb r n | None => false end else Nat.ltb v 49
                     | e => (APC.expr_vars_lt 49 e || (hpc && Nat.eqb n 11))%bool
                     end) (seq 1 31))%bool.
Lemma slots_ok : forallb (fun j => slots_chk (CC.cp_regs (PSM2.cutn j)) ((Nat.eqb j I_HLO || Nat.eqb j I_HHI || Nat.eqb j I_HN)%bool)) [1; 2; 3; 4; 5; 6]%nat = true.
Proof. vmc_refl. Qed.
Lemma hregs_eq : CC.cp_regs (PSM2.cutn I_HHI) = CC.cp_regs (PSM2.cutn I_HLO) /\ CC.cp_regs (PSM2.cutn I_HN) = CC.cp_regs (PSM2.cutn I_HLO).
Proof. split; vm_compute; reflexivity. Qed.

Lemma mkE2_agree : forall regs E' R' sem, env_agree 49 E' (mkE2 regs E' R' sem).
Proof. intros regs E' R' sem. split; [|reflexivity]. intros n Hn. unfold mkE2. cbn [ev]. apply Nat.ltb_lt in Hn. rewrite Hn. reflexivity. Qed.
Lemma mkE2_sem : forall regs E' R' sem k, (k < 17)%nat -> ev (mkE2 regs E' R' sem) (49 + k) = nth k sem (Z_to_bv 64 0).
Proof.
  intros regs E' R' sem k Hk. unfold mkE2. cbn [ev]. destruct (Nat.ltb_spec (49 + k) 49) as [X|_]; [lia|]. destruct (Nat.ltb_spec (49 + k) 66) as [_|X]; [|lia].
  replace (49 + k - 49)%nat with k by lia. reflexivity.
Qed.
Lemma reg_of_idx : forall r : reg, Z_to_bv 5 (Z.of_nat (ridx r)) = r.
Proof. intros r. unfold ridx. pose proof (bv_unsigned_in_range _ r) as Hr. rewrite Z2Nat.id by lia. apply Z_to_bv_bv_unsigned. Qed.
Lemma mkE2_regs : forall regs hpc E' R' sem leafregs, slots_chk regs hpc = true -> regs_ok E' leafregs R' ->
  (forall n, In n (seq 1 31) -> (hpc && Nat.eqb n 11)%bool = false -> live_reg_chk (nth n regs (ELit 0)) (nth n leafregs (ELit 0)) = true) ->
  (hpc = true -> getr R' 11%bv = edenot (mkE2 regs E' R' sem) (nth 11 regs (ELit 0))) ->
  regs_ok (mkE2 regs E' R' sem) regs R'.
Proof.
  intros regs hpc E' R' sem leafregs HS HR HL H11 r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
  - pose proof (HR r) as X. unfold sr_get in X. rewrite Er in X. exact X.
  - apply andb_prop in HS as [_ HS]. rewrite forallb_forall in HS.
    assert (Hn : In (ridx r) (seq 1 31)).
    { apply in_seq. unfold ridx. pose proof (bv_unsigned_in_range _ r) as Hr. unfold bv_eqb in Er. apply Z.eqb_neq in Er. change (bv_unsigned (0 : bv 5)) with 0 in Er. change (bv_modulus 5) with 32 in Hr. lia. }
    specialize (HS _ Hn). set (n := ridx r) in *.
    destruct ((hpc && Nat.eqb n 11)%bool) eqn:H11b.
    { apply andb_prop in H11b as [Hh Hn11]. apply Nat.eqb_eq in Hn11. rewrite Hn11. rewrite <- (H11 Hh). f_equal. apply bv_eq. unfold n, ridx in Hn11. pose proof (bv_unsigned_in_range _ r) as Hr.
      change (bv_unsigned (11 : bv 5)) with 11. lia. }
    specialize (HL _ Hn H11b). pose proof (HR r) as X. unfold sr_get in X. rewrite Er in X. fold n in X.
    assert (FROZEN : forall e, APC.expr_vars_lt 49 e = true -> expr_eqb e (nth n leafregs (ELit 0)) = true -> getr R' r = edenot (mkE2 regs E' R' sem) e).
    { intros e Hv He. apply expr_eqb_eq in He. rewrite X, <- He. exact (SR.edenot_agree_AP 49 E' _ e (mkE2_agree regs E' R' sem) Hv). }
    destruct (nth n regs (ELit 0)) as [z|v| | | | | |] eqn:Hreg.
    + apply FROZEN; [reflexivity|]. cbn [live_reg_chk] in HL. apply andb_prop in HL as [_ HL]. exact HL.
    + destruct (Nat.leb_spec 66 v) as [Hv|Hv].
      * destruct (slot_of regs v) as [r0|] eqn:Hs; [|discriminate]. apply Nat.eqb_eq in HS. subst r0. cbn [edenot]. unfold mkE2. cbn [ev].
        destruct (Nat.ltb_spec v 49) as [Q|_]; [lia|]. destruct (Nat.ltb_spec v 66) as [Q|_]; [lia|]. rewrite Hs. unfold n. rewrite reg_of_idx. reflexivity.
      * apply Nat.ltb_lt in HS. apply FROZEN; [change (Nat.ltb v 49 = true); apply Nat.ltb_lt; exact HS|]. cbn [live_reg_chk] in HL. unfold GT.NF in HL. destruct (Nat.leb_spec 49 v) as [Q|_]; [lia | exact HL].
    + rewrite orb_false_r in HS. apply FROZEN; [exact HS|]. cbn [live_reg_chk] in HL. apply andb_prop in HL as [_ HL]. exact HL.
    + rewrite orb_false_r in HS. apply FROZEN; [exact HS|]. cbn [live_reg_chk] in HL. apply andb_prop in HL as [_ HL]. exact HL.
    + rewrite orb_false_r in HS. apply FROZEN; [exact HS|]. cbn [live_reg_chk] in HL. apply andb_prop in HL as [_ HL]. exact HL.
    + rewrite orb_false_r in HS. apply FROZEN; [exact HS|]. cbn [live_reg_chk] in HL. apply andb_prop in HL as [_ HL]. exact HL.
    + rewrite orb_false_r in HS. apply FROZEN; [exact HS|]. cbn [live_reg_chk] in HL. apply andb_prop in HL as [_ HL]. exact HL.
    + rewrite orb_false_r in HS. apply FROZEN; [exact HS|]. cbn [live_reg_chk] in HL. apply andb_prop in HL as [_ HL]. exact HL.
Qed.

Definition CURJ : expr := APC.esub (APC.eadd (EVar 32) (EVar 33)) (EVar 49).
Definition stx (j : nat) : expr := if Nat.eqb j I_HN then ELit 17 else EVar 52.
Definition PXJ (j : nat) : PSK.pexprs := PSK.PX (EVar 51) CURJ (stx j) (EVar 53) (EVar 54) (EVar 55) (EVar 56) (EVar 57) (EVar 58) (EVar 59) (EVar 60) (EVar 61) (EVar 62) (EVar 63) (EVar 64) (ELit 0).
Definition MEASX (j : nat) : expr :=
  if Nat.eqb j I_L0 then ELit 1073741824 else if Nat.eqb j I_L then APC.eaddz (APC.eadd (APC.escale 64 (EVar 49)) (APC.escale 8 (EVar 50))) 9
  else if Nat.eqb j I_L2 then APC.eaddz (APC.escale 64 (EVar 49)) (-24) else APC.eaddz (APC.eadd (APC.escale 64 (EVar 49)) (APC.escale 8 (EVar 50))) 8.
Definition jmin (j : nat) : Z := if (Nat.eqb j I_L0 || Nat.eqb j I_L)%bool then 0 else 1.
Definition EXT (j : nat) : list kentry :=
  [KRange (EVar 49) (jmin j) 16384; KRange (APC.esub (EVar 33) (EVar 49)) 0 16384; KRange (EVar 50) 0 3; KRange (MEASX j) 0 4611686018427387904]
  ++ (if Nat.eqb j I_HLO then [KRange (EVar 52) 0 16] else if Nat.eqb j I_HHI then [KRange (EVar 52) 18 255] else [])
  ++ [KRange (APC.esub (APC.escale 4 CURJ) (EVar 49)) 0 2251799813685248].
Definition PVJ (j : nat) : PB4.pvals2 :=
  PB4.PV2 (EVar 51) WEND CURJ (stx j) (EVar 53) (EVar 54) (EVar 55) (EVar 56) (EVar 58) (EVar 60) (APC.eadd (EVar 60) (EVar 61)) (APC.eadd (EVar 60) (EVar 62)).
Definition PEJ : expr := EVar 59.
Definition CEJ : expr := APC.escale 2 (EVar 57).
Definition tgt (j : nat) : Prop := In j [1; 2; 3; 4; 5; 6]%nat.
Lemma tmpl_eq : forall j, tgt j -> CC.cp_know (PSM2.cutn j) = PSK.pkn CONSTS true Pb Vb Eb (EVar 2) SEG WLEN (PXJ j) ++ EXT j.
Proof. intros j [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; vm_compute; reflexivity. Qed.
Lemma tmpl_meas : forall j, tgt j -> CC.cp_meas (PSM2.cutn j) = MEASX j.
Proof. intros j [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; vm_compute; reflexivity. Qed.
Lemma tmpl_vw : forall j, tgt j -> PSM2.vw j = Some (PVJ j, PEJ, CEJ) /\ nth j G.BLS [] = [(PEJ, CEJ); (EVar 60, EVar 62)] /\ kind_of j = KInv /\ nth_error G.CPS j = Some (PSM2.cutn j).
Proof. intros j [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; vm_compute; repeat split; reflexivity. Qed.
Lemma tmpl_pc : forall j, tgt j -> CC.cp_pc (PSM2.cutn j) = (if Nat.eqb j I_L0 then L0PC else if Nat.eqb j I_L then LPC else if Nat.eqb j I_L2 then L2PC else HPC).
Proof. intros j [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; vm_compute; reflexivity. Qed.

Definition is_fkunk (X : kentry) : bool := match X with KUnk (SA (EVar 2) _) _ => true | _ => false end.
Lemma frz_split : forall X, In X (PSK.pkn_frz CONSTS true Pb Vb Eb (EVar 2) SEG WLEN) -> X = KUnk (SA (EVar 2) (-10096)) (ELit 10000) \/ In X FRZ.
Proof.
  intros X HX. destruct (is_fkunk X) eqn:Hk.
  - left. assert (Hf : In X (List.filter is_fkunk (PSK.pkn_frz CONSTS true Pb Vb Eb (EVar 2) SEG WLEN))) by (apply filter_In; split; assumption).
    change (List.filter is_fkunk (PSK.pkn_frz CONSTS true Pb Vb Eb (EVar 2) SEG WLEN)) with [KUnk (SA (EVar 2) (-10096)) (ELit 10000)] in Hf. destruct Hf as [<-|[]]. reflexivity.
  - right. unfold FRZ. apply filter_In. split; [exact HX|]. unfold is_fkunk in Hk. destruct X as [| | | | | | | | |[b o] n]; try reflexivity. destruct b as [|v| | | | | |]; try reflexivity. destruct v as [|[|[|v]]]; try reflexivity. discriminate Hk.
Qed.
End PSR.
