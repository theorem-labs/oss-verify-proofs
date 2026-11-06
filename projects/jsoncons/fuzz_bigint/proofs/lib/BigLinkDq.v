(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore Src0_code_22348_22f60 BigBranchSrc0 BigContractSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkInlA BigLinkInl.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_BigLinkDq.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BDQ.
Abbreviation RSEGS := Plain.M.loaded_segments.
Module QA := LibSegZ_dq_A.
Module QB1 := LibSegZ_dq_B1.
Module QC := LibSegZ_dq_C.
Module QB2a := LibSegZ_dq_B2a.
Module QB2 := LibSegZ_dq_B2.
Module QE := LibSegZ_dq_E.

Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Ltac inK := apply BIL.In_of_existsb; vm_compute; reflexivity.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zraw (V : nat -> Z) (t : BL.za) : Z :=
  match t with
  | BL.ZV n => V n
  | BL.ZL z => z
  | BL.ZAddM a b => zraw V a + zraw V b
  | BL.ZSubM a b => zraw V a - zraw V b
  | BL.ZMulM a b => zraw V a * zraw V b
  | BL.ZShlC a c => zraw V a * c
  | _ => BL.zden V t
  end.

Lemma MM_nz : BL.MM <> 0. Proof. unfold BL.MM. lia. Qed.

Lemma zraw_ok V t : BL.zden V t mod BL.MM = zraw V t mod BL.MM.
Proof.
  induction t; cbn [BL.zden zraw]; fold (BL.zden V); try reflexivity.
  - rewrite Z.mod_mod by apply MM_nz. rewrite Z.add_mod, IHt1, IHt2, <- Z.add_mod by apply MM_nz. reflexivity.
  - rewrite Z.mod_mod by apply MM_nz. rewrite Zminus_mod, IHt1, IHt2, <- Zminus_mod. reflexivity.
  - rewrite Z.mod_mod by apply MM_nz. rewrite Z.mul_mod, IHt1, IHt2, <- Z.mul_mod by apply MM_nz. reflexivity.
  - rewrite Z.mod_mod by apply MM_nz. rewrite Z.mul_mod, IHt, <- Z.mul_mod by apply MM_nz. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma uns_tree E e t : BL.zcomp e = Some t -> bv_unsigned (edenot E e) = zraw (BL.uv E) t mod BL.MM.
Proof.
  intros Ht. rewrite (BL.zcomp_sound E e t Ht). rewrite <- zraw_ok. symmetry. apply Z.mod_small.
  rewrite <- (BL.zcomp_sound E e t Ht). apply (BL.bvu_range (edenot E e)).
Qed.

Lemma modM_congr a b k : a = b + k * BL.MM -> a mod BL.MM = b mod BL.MM.
Proof. intros ->. unfold BL.MM. rewrite Z_mod_plus_full. reflexivity. Qed.

Lemma uns_small (w : word) : bv_unsigned w mod BL.MM = bv_unsigned w.
Proof. apply Z.mod_small. apply (BL.bvu_range w). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ER (R : bvmap 5 word) : env := BG.E_R R (fun _ => Z_to_bv 64 0) (fun _ => []).

Lemma ER_reg R i : (i < 32)%nat -> ev (ER R) i = getr R (reg i).
Proof. intros. apply BG.E_R_reg. exact H. Qed.
Lemma ER_uv R i : (i < 32)%nat -> BL.uv (ER R) i = bv_unsigned (getr R (reg i)).
Proof. intros. unfold BL.uv. rewrite ER_reg; auto. Qed.

Definition SR_ID : list expr := Eval vm_compute in QB1.regs0.
Lemma regs_ok_id R : regs_ok (ER R) SR_ID R.
Proof. apply BG.regs_ok_slots. reflexivity. cbn. repeat split; try (left; reflexivity); try apply getr_zero. Qed.

Definition NC : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.   (* [comment removed for export] *)
Definition keptNC (R R' : bvmap 5 word) : Prop := forall i, In i NC -> getr R' (reg i) = getr R (reg i).
Lemma keptNC_refl R : keptNC R R. Proof. intros i _; reflexivity. Qed.
Lemma keptNC_trans R1 R2 R3 : keptNC R1 R2 -> keptNC R2 R3 -> keptNC R1 R3.
Proof. intros A B i Hi. rewrite (B i Hi). apply A. exact Hi. Qed.
Lemma keptNC_of (KS : list nat) R R' : forallb (fun i => existsb (Nat.eqb i) KS) NC = true ->
  (forall i, In i KS -> getr R' (reg i) = getr R (reg i)) -> keptNC R R'.
Proof. intros HB K i Hi. apply K. rewrite forallb_forall in HB. apply BIL.In_of_existsb. apply HB. exact Hi. Qed.

(* [comment removed for export] *)
Definition KS_A : list nat := Eval vm_compute in (BG.kept_list 48 QA.regs0 QA.regs_out).
Lemma KS_A_ok : BG.kept_ok 48 QA.regs0 QA.regs_out KS_A = true. Proof. vm_compute. reflexivity. Qed.
Lemma regs0_A : QA.regs0 = SR_ID. Proof. vm_compute. reflexivity. Qed.
Lemma vars_A : forallb (expr_vars_lt 48) QA.regs_out = true. Proof. vm_compute. reflexivity. Qed.

Lemma out_of (ro : list expr) E E' R' i :
  forallb (expr_vars_lt 48) ro = true -> env_agree 48 E E' ->
  (forall i e, In (i, e) (map (fun i => (i, nth i ro (ELit 0))) (seq 1 31)) -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e) ->
  (0 < i < 32)%nat -> (i < length ro)%nat -> getr R' (reg i) = edenot E (nth i ro (ELit 0)).
Proof.
  intros HV HA HO Hi Hl. rewrite (BG.out_reg ro E' R' i HO Hi). apply (BG.edenot_kept 48 E E'). exact HA.
  rewrite forallb_forall in HV. apply HV. apply nth_In. exact Hl.
Qed.

Lemma A_conc fx R M d :
  bv_unsigned (getr R (reg 13)) = d -> 2 ^ 63 <= d < 2 ^ 64 ->
  exists fx' R' M',
    msteps RSEGS (st fx R 0x22578 M) (st fx' R' 0x225bc M')
    /\ (forall i, In i KS_A -> getr R' (reg i) = getr R (reg i))
    /\ (forall i, (0 < i < 32)%nat -> getr R' (reg i) = edenot (ER R) (nth i QA.regs_out (ELit 0)))
    /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  intros Hd Rd.
  assert (HR: regs_ok (ER R) QA.regs0 R). { rewrite regs0_A. apply regs_ok_id. }
  assert (HK: know_ok RSEGS (ER R) M QA.kn0).
  { unfold know_ok. apply Forall_cons. { eapply BG.kentry_KRange_var. rewrite ER_reg by lia. exact Hd. lia. } apply Forall_nil. }
  destruct (QA.seg_sound_ax fx (ER R) R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps0 & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  apply BIA.nth_error_single in Hnth. subst ps0. change QA.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hms.
  split. { intros j Hj. apply (BG.kept_regs (ER R) E' R R' QA.regs0 QA.regs_out 48 KS_A KS_A_ok HR Hag Hregs j Hj). }
  split. { intros j Hj. apply (out_of QA.regs_out (ER R) E' R' j vars_A Hag Hregs Hj). change (length QA.regs_out) with 32%nat. lia. }
  split. { intros a. apply Hfr. constructor. } exact Hgr.
Qed.

(* [comment removed for export] *)
Section PurePiece.
  (* [comment removed for export] *)
  Lemma pure_conc
    (regs0 : list expr) (kn0 : list kentry) (regs_out : list expr) (NX0 : nat) (pc0 pc1 : Z) (ps0 : SR.post_spec) (KS : list nat)
    (SOUND : forall (fx : FPState) E R M, regs_ok E regs0 R -> know_ok RSEGS E M kn0 -> SGP.bfacts_ok [] E ->
       exists (fx' : FPState) E' R' M' i ps, nth_error [ps0] i = Some ps /\ env_agree NX0 E E'
         /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom RSEGS))
         /\ (forall i e, In (i, e) (SR.ps_regs ps) -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e)
         /\ getr R' (Z_to_bv 5 0) = Z_to_bv 64 0 /\ SGP.regions_ok E' [] /\ (forall a : word, SGP.outside E' [] a -> M' a = M a)
         /\ (forall K, In K (SR.ps_cells ps) -> kentry_ok RSEGS E' M' K) /\ mem_grows M M') :
    regs0 = SR_ID -> kn0 = [] -> NX0 = 48%nat -> SR.ps_pc ps0 = pc1 ->
    SR.ps_regs ps0 = map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31) ->
    BG.kept_ok 48 regs0 regs_out KS = true -> forallb (expr_vars_lt 48) regs_out = true -> length regs_out = 32%nat ->
    forall fx R M, exists fx' R' M',
      msteps RSEGS (st fx R pc0 M) (st fx' R' pc1 M')
      /\ (forall i, In i KS -> getr R' (reg i) = getr R (reg i))
      /\ (forall i, (0 < i < 32)%nat -> getr R' (reg i) = edenot (ER R) (nth i regs_out (ELit 0)))
      /\ (forall a, M' a = M a) /\ mem_grows M M'.
  Proof.
    intros H0 Hk Hn Hpc Hps HKS HV HL fx R M.
    assert (HR: regs_ok (ER R) regs0 R). { rewrite H0. apply regs_ok_id. }
    assert (HK: know_ok RSEGS (ER R) M kn0). { rewrite Hk. constructor. }
    destruct (SOUND fx (ER R) R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & i & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
    apply BIA.nth_error_single in Hnth. subst ps. rewrite Hn in Hag. rewrite Hpc in Hms. rewrite Hps in Hregs.
    exists fx', R', M'. split. exact Hms.
    split. { intros j Hj. apply (BG.kept_regs (ER R) E' R R' regs0 regs_out 48 KS HKS HR Hag Hregs j Hj). }
    split. { intros j Hj. apply (out_of regs_out (ER R) E' R' j HV Hag Hregs Hj). rewrite HL. lia. }
    split. { intros a. apply Hfr. constructor. } exact Hgr.
  Qed.
End PurePiece.

Definition KS_B1 : list nat := Eval vm_compute in (BG.kept_list 48 QB1.regs0 QB1.regs_out).
Definition KS_C : list nat := Eval vm_compute in (BG.kept_list 48 QC.regs0 QC.regs_out).
Definition KS_B2a : list nat := Eval vm_compute in (BG.kept_list 48 QB2a.regs0 QB2a.regs_out).
Definition KS_B2 : list nat := Eval vm_compute in (BG.kept_list 48 QB2.regs0 QB2.regs_out).
Definition KS_E : list nat := Eval vm_compute in (BG.kept_list 48 QE.regs0 QE.regs_out).

Definition B1_conc := pure_conc QB1.regs0 QB1.kn0 QB1.regs_out QB1.NX0 0x225c8 0x225e0 QB1.ps0 KS_B1 QB1.seg_sound_ax
  eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl.
Definition C_conc := pure_conc QC.regs0 QC.kn0 QC.regs_out QC.NX0 0x225e8 0x22634 QC.ps0 KS_C QC.seg_sound_ax
  eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl.
Definition B2a_conc := pure_conc QB2a.regs0 QB2a.kn0 QB2a.regs_out QB2a.NX0 0x2263c 0x2264c QB2a.ps0 KS_B2a QB2a.seg_sound_ax
  eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl.
Definition B2_conc := pure_conc QB2.regs0 QB2.kn0 QB2.regs_out QB2.NX0 0x2264c 0x22664 QB2.ps0 KS_B2 QB2.seg_sound_ax
  eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl.
Definition E_conc := pure_conc QE.regs0 QE.kn0 QE.regs_out QE.NX0 0x2266c 0x22670 QE.ps0 KS_E QE.seg_sound_ax
  eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Br.
  Context {fx : FPState}.
  Variable M : word -> option byte.

  Lemma reg_litZ (n : Z) : 0 <= n < 32 -> (Z_to_bv 5 n : bv 5) = Z_to_bv 5 (Z.of_nat (Z.to_nat n)).
  Proof. intros. rewrite Z2Nat.id by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma br_site R (pc tk : Z) (wpc : word) w c (rs1 rs2 : bv 5) (imm : bv 13) :
    bv_unsigned wpc = pc -> fetch_word RSEGS wpc = Some w -> is_ecall w = false -> decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
    bv_unsigned (btgt wpc (bv_signed imm)) = tk ->
    msteps RSEGS (st fx R pc M) (st fx R (if branch_taken c (getr R rs1) (getr R rs2) then tk else pc + 4) M).
  Proof.
    intros Hpc HF HE HD Htk. rewrite (BI.pc_lit pc wpc Hpc).
    pose proof (br_any M (seg_rom RSEGS) R wpc w c rs1 rs2 imm HF HE HD) as ST.
    destruct (branch_taken c (getr R rs1) (getr R rs2)).
    - rewrite (BI.pc_lit tk _ Htk). exact ST.
    - replace (Z_to_bv 64 (pc + 4)) with (v_addi wpc 4). exact ST. unfold v_addi. rewrite Hpc. reflexivity.
  Qed.

  Lemma br22514 R : msteps RSEGS (st fx R 0x225bc M) (st fx R (if bv_ltu (getr R (reg 14)) (getr R (reg 17)) then 0x225c8 else 0x225c0) M).
  Proof. apply (br_site R 0x225bc 0x225c8 (0x225bc%bv : word) _ BC_LTU 14 17 _ eq_refl F_225bc eq_refl D_225bc). reflexivity. Qed.
  Lemma br22518 R : msteps RSEGS (st fx R 0x225c0 M) (st fx R (if negb (bv_eqb (getr R (reg 17)) (getr R (reg 14))) then 0x225e8 else 0x225c4) M).
  Proof. apply (br_site R 0x225c0 0x225e8 (0x225c0%bv : word) _ BC_NE 17 14 _ eq_refl F_225c0 eq_refl D_225c0). reflexivity. Qed.
  Lemma br2251c R : msteps RSEGS (st fx R 0x225c4 M) (st fx R (if bv_ltu (getr R (reg 11)) (getr R (reg 5)) then 0x225e8 else 0x225c8) M).
  Proof. apply (br_site R 0x225c4 0x225e8 (0x225c4%bv : word) _ BC_LTU 11 5 _ eq_refl F_225c4 eq_refl D_225c4). reflexivity. Qed.
  Lemma br22538 R : msteps RSEGS (st fx R 0x225e0 M) (st fx R (if bv_ltu (getr R (reg 14)) (getr R (reg 17)) then 0x225c8 else 0x225e4) M).
  Proof. apply (br_site R 0x225e0 0x225c8 (0x225e0%bv : word) _ BC_LTU 14 17 _ eq_refl F_225e0 eq_refl D_225e0). reflexivity. Qed.
  Lemma j2253c R : msteps RSEGS (st fx R 0x225e4 M) (st fx R 0x225c0 M).
  Proof.
    rewrite (BI.pc_lit 0x225e4 (0x225e4%bv : word)) by reflexivity.
    eapply mst_step; [reflexivity | | apply mst_refl].
    rewrite (step_jal_x0 RSEGS R _ M (seg_rom RSEGS) _ _ F_225e4 eq_refl D_225e4). first [reflexivity | f_equal; f_equal; apply bv_eq; reflexivity].
  Qed.
  Lemma br2258c R : msteps RSEGS (st fx R 0x22634 M) (st fx R (if negb (bv_eqb (getr R (reg 14)) (getr R (reg 0))) then 0x2263c else 0x22638) M).
  Proof. apply (br_site R 0x22634 0x2263c (0x22634%bv : word) _ BC_NE 14 0 _ eq_refl F_22634 eq_refl D_22634). reflexivity. Qed.
  Lemma br22590 R : msteps RSEGS (st fx R 0x22638 M) (st fx R (if bv_ltu (getr R (reg 15)) (getr R (reg 13)) then 0x2266c else 0x2263c) M).
  Proof. apply (br_site R 0x22638 0x2266c (0x22638%bv : word) _ BC_LTU 15 13 _ eq_refl F_22638 eq_refl D_22638). reflexivity. Qed.
  Lemma br225bc R : msteps RSEGS (st fx R 0x22664 M) (st fx R (if negb (bv_eqb (getr R (reg 14)) (getr R (reg 0))) then 0x2264c else 0x22668) M).
  Proof. apply (br_site R 0x22664 0x2264c (0x22664%bv : word) _ BC_NE 14 0 _ eq_refl F_22664 eq_refl D_22664). reflexivity. Qed.
  Lemma br225c0 R : msteps RSEGS (st fx R 0x22668 M) (st fx R (if negb (bv_ltu (getr R (reg 16)) (getr R (reg 13))) then 0x2264c else 0x2266c) M).
  Proof. apply (br_site R 0x22668 0x2264c (0x22668%bv : word) _ BC_GEU 16 13 _ eq_refl F_22668 eq_refl D_22668). reflexivity. Qed.
End Br.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition U (R : bvmap 5 word) (i : nat) : Z := bv_unsigned (getr R (reg i)).
Lemma U_range R i : 0 <= U R i < BL.MM. Proof. apply (BL.bvu_range (getr R (reg i))). Qed.
Lemma U_0 R : U R 0 = 0. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition tB1_17 : expr := Eval vm_compute in (nth 17 QB1.regs_out (ELit 0)).
Definition zB1_17 : BL.za := Eval vm_compute in (BL.zc tB1_17).
Lemma zB1_17_ok : BL.zcomp tB1_17 = Some zB1_17. Proof. vm_compute. reflexivity. Qed.
Lemma nB1_17 : nth 17 QB1.regs_out (ELit 0) = tB1_17. Proof. reflexivity. Qed.
Definition tB1_11 : expr := Eval vm_compute in (nth 11 QB1.regs_out (ELit 0)).
Definition zB1_11 : BL.za := Eval vm_compute in (BL.zc tB1_11).
Lemma zB1_11_ok : BL.zcomp tB1_11 = Some zB1_11. Proof. vm_compute. reflexivity. Qed.
Lemma nB1_11 : nth 11 QB1.regs_out (ELit 0) = tB1_11. Proof. reflexivity. Qed.
Definition tB2_11 : expr := Eval vm_compute in (nth 11 QB2.regs_out (ELit 0)).
Definition zB2_11 : BL.za := Eval vm_compute in (BL.zc tB2_11).
Lemma zB2_11_ok : BL.zcomp tB2_11 = Some zB2_11. Proof. vm_compute. reflexivity. Qed.
Lemma nB2_11 : nth 11 QB2.regs_out (ELit 0) = tB2_11. Proof. reflexivity. Qed.
Definition tB2_14 : expr := Eval vm_compute in (nth 14 QB2.regs_out (ELit 0)).
Definition zB2_14 : BL.za := Eval vm_compute in (BL.zc tB2_14).
Lemma zB2_14_ok : BL.zcomp tB2_14 = Some zB2_14. Proof. vm_compute. reflexivity. Qed.
Lemma nB2_14 : nth 14 QB2.regs_out (ELit 0) = tB2_14. Proof. reflexivity. Qed.
Definition tB2_15 : expr := Eval vm_compute in (nth 15 QB2.regs_out (ELit 0)).
Definition zB2_15 : BL.za := Eval vm_compute in (BL.zc tB2_15).
Lemma zB2_15_ok : BL.zcomp tB2_15 = Some zB2_15. Proof. vm_compute. reflexivity. Qed.
Lemma nB2_15 : nth 15 QB2.regs_out (ELit 0) = tB2_15. Proof. reflexivity. Qed.
Definition tB2_16 : expr := Eval vm_compute in (nth 16 QB2.regs_out (ELit 0)).
Definition zB2_16 : BL.za := Eval vm_compute in (BL.zc tB2_16).
Lemma zB2_16_ok : BL.zcomp tB2_16 = Some zB2_16. Proof. vm_compute. reflexivity. Qed.
Lemma nB2_16 : nth 16 QB2.regs_out (ELit 0) = tB2_16. Proof. reflexivity. Qed.
Definition tB2a_11 : expr := Eval vm_compute in (nth 11 QB2a.regs_out (ELit 0)).
Definition zB2a_11 : BL.za := Eval vm_compute in (BL.zc tB2a_11).
Lemma zB2a_11_ok : BL.zcomp tB2a_11 = Some zB2a_11. Proof. vm_compute. reflexivity. Qed.
Lemma nB2a_11 : nth 11 QB2a.regs_out (ELit 0) = tB2a_11. Proof. reflexivity. Qed.
Definition tC_15 : expr := Eval vm_compute in (nth 15 QC.regs_out (ELit 0)).
Definition zC_15 : BL.za := Eval vm_compute in (BL.zc tC_15).
Lemma zC_15_ok : BL.zcomp tC_15 = Some zC_15. Proof. vm_compute. reflexivity. Qed.
Lemma nC_15 : nth 15 QC.regs_out (ELit 0) = tC_15. Proof. reflexivity. Qed.
Definition tC_12 : expr := Eval vm_compute in (nth 12 QC.regs_out (ELit 0)).
Definition zC_12 : BL.za := Eval vm_compute in (BL.zc tC_12).
Lemma zC_12_ok : BL.zcomp tC_12 = Some zC_12. Proof. vm_compute. reflexivity. Qed.
Lemma nC_12 : nth 12 QC.regs_out (ELit 0) = tC_12. Proof. reflexivity. Qed.
Definition tC_5 : expr := Eval vm_compute in (nth 5 QC.regs_out (ELit 0)).
Definition zC_5 : BL.za := Eval vm_compute in (BL.zc tC_5).
Lemma zC_5_ok : BL.zcomp tC_5 = Some zC_5. Proof. vm_compute. reflexivity. Qed.
Lemma nC_5 : nth 5 QC.regs_out (ELit 0) = tC_5. Proof. reflexivity. Qed.
Definition tA_14 : expr := Eval vm_compute in (nth 14 QA.regs_out (ELit 0)).
Definition zA_14 : BL.za := Eval vm_compute in (BL.zc tA_14).
Lemma zA_14_ok : BL.zcomp tA_14 = Some zA_14. Proof. vm_compute. reflexivity. Qed.
Lemma nA_14 : nth 14 QA.regs_out (ELit 0) = tA_14. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac tree_val OUT i nEQ t z zOK :=
  unfold U at 1; rewrite (OUT i) by lia; rewrite nEQ; rewrite (uns_tree _ t z zOK); cbn [zraw BL.zden z]; rewrite ?ER_uv by lia.

(* [comment removed for export] *)
Lemma B1_step fx R M :
  exists fx' R' M',
    msteps RSEGS (st fx R 0x225c8 M) (st fx' R' 0x225e0 M')
    /\ keptNC R R' /\ getr R' (reg 13) = getr R (reg 13) /\ getr R' (reg 14) = getr R (reg 14) /\ getr R' (reg 5) = getr R (reg 5)
    /\ U R' 17 = (U R 17 - U R 14 - BL.zb (U R 11 <? U R 5)) mod BL.MM
    /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  destruct (B1_conc fx R M) as (fx' & R' & M' & MS & K & OUT & MM & Hg).
  exists fx', R', M'. split. exact MS.
  split. { apply (keptNC_of KS_B1 R R'); [vm_compute; reflexivity | exact K]. }
  split. { apply K. inK. } split. { apply K. inK. } split. { apply K. inK. }
  split. { tree_val OUT 17%nat nB1_17 tB1_17 zB1_17 zB1_17_ok.
           unfold U. apply modM_congr with (k := bv_unsigned (getr R (reg 14)) + (if bv_unsigned (getr R (reg 11)) <? bv_unsigned (getr R (reg 5)) then 1 else 0)).
           unfold BL.zb. rewrite BL.MM_val. destruct (_ <? _); ring. }
  split. exact MM. exact Hg.
Qed.

(* [comment removed for export] *)
Lemma A_step fx R M d :
  U R 13 = d -> 2 ^ 63 <= d < 2 ^ 64 ->
  exists fx' R' M',
    msteps RSEGS (st fx R 0x22578 M) (st fx' R' 0x225bc M')
    /\ keptNC R R' /\ getr R' (reg 13) = getr R (reg 13) /\ U R' 14 = d / 2 ^ 32
    /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  intros Hd Rd. destruct (A_conc fx R M d Hd Rd) as (fx' & R' & M' & MS & K & OUT & MM & Hg).
  exists fx', R', M'. split. exact MS.
  split. { apply (keptNC_of KS_A R R'); [vm_compute; reflexivity | exact K]. }
  split. { apply K. inK. }
  split. { tree_val OUT 14%nat nA_14 tA_14 zA_14 zA_14_ok. fold (U R 13). rewrite Hd. rewrite (Z.mod_small) . reflexivity.
           split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; unfold BL.MM; lia. }
  split. exact MM. exact Hg.
Qed.

(* [comment removed for export] *)
Lemma C_step fx R M :
  exists fx' R' M',
    msteps RSEGS (st fx R 0x225e8 M) (st fx' R' 0x22634 M')
    /\ keptNC R R' /\ getr R' (reg 13) = getr R (reg 13) /\ getr R' (reg 11) = getr R (reg 11)
    /\ U R' 15 = (U R 11 - U R' 12 * U R' 5) mod BL.MM
    /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  destruct (C_conc fx R M) as (fx' & R' & M' & MS & K & OUT & MM & Hg).
  exists fx', R', M'. split. exact MS.
  split. { apply (keptNC_of KS_C R R'); [vm_compute; reflexivity | exact K]. }
  split. { apply K. inK. } split. { apply K. inK. }
  split. { assert (E12: U R' 12 = BL.zden (BL.uv (ER R)) zC_12).
           { unfold U. rewrite (OUT 12%nat) by lia. rewrite nC_12. apply (BL.zcomp_sound (ER R) tC_12 zC_12 zC_12_ok). }
           assert (E5: U R' 5 = BL.zden (BL.uv (ER R)) zC_5).
           { unfold U. rewrite (OUT 5%nat) by lia. rewrite nC_5. apply (BL.zcomp_sound (ER R) tC_5 zC_5 zC_5_ok). }
           tree_val OUT 15%nat nC_15 tC_15 zC_15 zC_15_ok. rewrite E12, E5. cbn [BL.zden zC_12 zC_5]. rewrite ?ER_uv by lia. fold (U R 11) (U R 17) (U R 16) (U R 15) (U R 14).
           set (q := if U R 16 =? 0 then BL.MM - 1 else Z.lor ((4294967296 * U R 17) mod BL.MM) (U R 11 / 4294967296) / U R 16).
           set (T := Z.lor (U R 15) ((4294967296 * U R 14) mod BL.MM)).
           apply modM_congr with (k := q * T). rewrite BL.MM_val. ring. }
  split. exact MM. exact Hg.
Qed.

(* [comment removed for export] *)
Lemma B2a_step fx R M :
  exists fx' R' M',
    msteps RSEGS (st fx R 0x2263c M) (st fx' R' 0x2264c M')
    /\ keptNC R R' /\ getr R' (reg 13) = getr R (reg 13) /\ getr R' (reg 14) = getr R (reg 14) /\ getr R' (reg 15) = getr R (reg 15)
    /\ U R' 11 = (U R 11 - U R 13 - U R 12 * U R 5) mod BL.MM
    /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  destruct (B2a_conc fx R M) as (fx' & R' & M' & MS & K & OUT & MM & Hg).
  exists fx', R', M'. split. exact MS.
  split. { apply (keptNC_of KS_B2a R R'); [vm_compute; reflexivity | exact K]. }
  split. { apply K. inK. } split. { apply K. inK. } split. { apply K. inK. }
  split. { tree_val OUT 11%nat nB2a_11 tB2a_11 zB2a_11 zB2a_11_ok. fold (U R 11) (U R 13) (U R 12) (U R 5).
           apply modM_congr with (k := U R 13 + U R 12 * U R 5). rewrite BL.MM_val. ring. }
  split. exact MM. exact Hg.
Qed.

(* [comment removed for export] *)
Lemma B2_step fx R M :
  exists fx' R' M',
    msteps RSEGS (st fx R 0x2264c M) (st fx' R' 0x22664 M')
    /\ keptNC R R' /\ getr R' (reg 13) = getr R (reg 13)
    /\ U R' 14 = (U R 14 - BL.zb (U R 15 <? U R 13)) mod BL.MM
    /\ U R' 15 = (U R 15 - U R 13) mod BL.MM
    /\ U R' 16 = U R 11
    /\ U R' 11 = (U R 11 - U R 13) mod BL.MM
    /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  destruct (B2_conc fx R M) as (fx' & R' & M' & MS & K & OUT & MM & Hg).
  exists fx', R', M'. split. exact MS.
  split. { apply (keptNC_of KS_B2 R R'); [vm_compute; reflexivity | exact K]. }
  split. { apply K. inK. }
  split. { tree_val OUT 14%nat nB2_14 tB2_14 zB2_14 zB2_14_ok. fold (U R 14) (U R 15) (U R 13).
           apply modM_congr with (k := BL.zb (U R 15 <? U R 13)). unfold BL.zb. rewrite BL.MM_val. destruct (_ <? _); ring. }
  split. { tree_val OUT 15%nat nB2_15 tB2_15 zB2_15 zB2_15_ok. fold (U R 15) (U R 13).
           apply modM_congr with (k := U R 13). rewrite BL.MM_val. ring. }
  split. { unfold U at 1. rewrite (OUT 16%nat) by lia. rewrite nB2_16. unfold tB2_16. cbn [edenot]. rewrite ER_reg by lia. reflexivity. }
  split. { tree_val OUT 11%nat nB2_11 tB2_11 zB2_11 zB2_11_ok. fold (U R 11) (U R 13).
           apply modM_congr with (k := U R 13). rewrite BL.MM_val. ring. }
  split. exact MM. exact Hg.
Qed.

(* [comment removed for export] *)
Lemma E_step fx R M :
  exists fx' R' M',
    msteps RSEGS (st fx R 0x2266c M) (st fx' R' 0x22670 M')
    /\ keptNC R R' /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  destruct (E_conc fx R M) as (fx' & R' & M' & MS & K & OUT & MM & Hg).
  exists fx', R', M'. split. exact MS.
  split. { apply (keptNC_of KS_E R R'); [vm_compute; reflexivity | exact K]. } split. exact MM. exact Hg.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition post1 fx R M : Prop :=
  exists fx' R' M',
    msteps RSEGS (st fx R 0 M) (st fx' R' 0x225e8 M') /\ True.  (* [comment removed for export] *)

Lemma ltu_U R i j : bv_ltu (getr R (reg i)) (getr R (reg j)) = (U R i <? U R j).
Proof. reflexivity. Qed.
Lemma eqb_U R i j : bv_eqb (getr R (reg i)) (getr R (reg j)) = (U R i =? U R j).
Proof. reflexivity. Qed.
Lemma U_eq_of_getr R R' i : getr R' (reg i) = getr R (reg i) -> U R' i = U R i.
Proof. intros H. unfold U. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma loop1_tail fx R M :
  U R 17 <= U R 14 -> 1 <= U R 14 ->
  exists fx' R' M',
    msteps RSEGS (st fx R 0x225c0 M) (st fx' R' 0x225e8 M')
    /\ keptNC R R' /\ getr R' (reg 13) = getr R (reg 13) /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  intros LE D1.
  pose proof (br22518 M R) as T2. rewrite eqb_U in T2.
  destruct (Z.eqb_spec (U R 17) (U R 14)) as [EQ|NE]; cbn [negb] in T2.
  - pose proof (br2251c M R) as T3. rewrite ltu_U in T3.
    destruct (Z.ltb_spec (U R 11) (U R 5)) as [LT|GE].
    + exists fx, R, M. split. eapply msteps_trans; eauto. split. apply keptNC_refl. split. reflexivity. split. intros; reflexivity. apply mem_grows_refl.
    + destruct (B1_step fx R M) as (fx1 & R1 & M1 & MS1 & K1 & E13 & E14 & E5 & V17 & MM1 & Hg1).
      assert (Z17: U R1 17 = 0).
      { rewrite V17. replace (BL.zb (U R 11 <? U R 5)) with 0 by (unfold BL.zb; destruct (Z.ltb_spec (U R 11) (U R 5)); lia). rewrite EQ. rewrite Z.sub_diag, Z.sub_0_r. reflexivity. }
      pose proof (br22538 M1 R1) as T4. rewrite ltu_U, (U_eq_of_getr R R1 14 E14), Z17 in T4.
      replace (U R 14 <? 0) with false in T4 by (symmetry; apply Z.ltb_ge; lia).
      pose proof (j2253c M1 R1) as T5.
      pose proof (br22518 M1 R1) as T6. rewrite eqb_U, (U_eq_of_getr R R1 14 E14), Z17 in T6.
      replace (0 =? U R 14) with false in T6 by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in T6.
      exists fx1, R1, M1. split.
      { eapply msteps_trans. exact T2. eapply msteps_trans. exact T3. eapply msteps_trans. exact MS1.
        eapply msteps_trans. exact T4. eapply msteps_trans. exact T5. exact T6. }
      split. exact K1. split. exact E13. split. exact MM1. exact Hg1.
  - exists fx, R, M. split. exact T2. split. apply keptNC_refl. split. reflexivity. split. intros; reflexivity. apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
Lemma loop1_main (n : nat) : forall fx R M,
  (Z.to_nat (U R 17) <= n)%nat -> U R 14 + BL.zb (U R 11 <? U R 5) <= U R 17 -> 1 <= U R 14 ->
  exists fx' R' M',
    msteps RSEGS (st fx R 0x225c8 M) (st fx' R' 0x225e8 M')
    /\ keptNC R R' /\ getr R' (reg 13) = getr R (reg 13) /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  induction n as [n IH] using lt_wf_ind. intros fx R M Hn COND D1.
  pose proof (U_range R 17) as R17. pose proof (U_range R 14) as R14.
  assert (Zb: 0 <= BL.zb (U R 11 <? U R 5) <= 1) by (unfold BL.zb; destruct (U R 11 <? U R 5); lia).
  destruct (B1_step fx R M) as (fx1 & R1 & M1 & MS1 & K1 & E13 & E14 & E5 & V17 & MM1 & Hg1).
  assert (V17': U R1 17 = U R 17 - U R 14 - BL.zb (U R 11 <? U R 5)).
  { rewrite V17. apply Z.mod_small. unfold BL.MM in *. lia. }
  pose proof (br22538 M1 R1) as T4. rewrite ltu_U, (U_eq_of_getr R R1 14 E14) in T4.
  destruct (Z.ltb_spec (U R 14) (U R1 17)) as [LT|GE].
  - (* [comment removed for export] *)
    destruct (IH (Z.to_nat (U R1 17)) ltac:(lia) fx1 R1 M1 ltac:(lia)
                 ltac:(rewrite (U_eq_of_getr R R1 14 E14); unfold BL.zb; destruct (U R1 11 <? U R1 5); lia) ltac:(rewrite (U_eq_of_getr R R1 14 E14); lia))
      as (fx2 & R2 & M2 & MS2 & K2 & F13 & MM2 & Hg2).
    exists fx2, R2, M2. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact T4. exact MS2. }
    split. eapply keptNC_trans; eauto. split. rewrite F13; exact E13. split. intros a; rewrite MM2; apply MM1. eapply mem_grows_trans; eauto.
  - (* [comment removed for export] *)
    pose proof (j2253c M1 R1) as T5.
    destruct (loop1_tail fx1 R1 M1 ltac:(rewrite (U_eq_of_getr R R1 14 E14); lia) ltac:(rewrite (U_eq_of_getr R R1 14 E14); lia)) as (fx2 & R2 & M2 & MS2 & K2 & F13 & MM2 & Hg2).
    exists fx2, R2, M2. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact T4. eapply msteps_trans. exact T5. exact MS2. }
    split. eapply keptNC_trans; eauto. split. rewrite F13; exact E13. split. intros a; rewrite MM2; apply MM1. eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma loop2_main (n : nat) : forall fx R M,
  (Z.to_nat (U R 14 * BL.MM + U R 15) <= n)%nat ->
  (U R 14 <> 0 \/ U R 13 <= U R 15) -> U R 11 = (U R 15 - U R 13) mod BL.MM -> 2 ^ 63 <= U R 13 ->
  exists fx' R' M',
    msteps RSEGS (st fx R 0x2264c M) (st fx' R' 0x2266c M')
    /\ keptNC R R' /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  induction n as [n IH] using lt_wf_ind. intros fx R M Hn COND INV D63.
  pose proof (U_range R 14) as R14. pose proof (U_range R 15) as R15. pose proof (U_range R 13) as R13. pose proof (U_range R 11) as R11.
  destruct (B2_step fx R M) as (fx1 & R1 & M1 & MS1 & K1 & E13 & V14 & V15 & V16 & V11 & MM1 & Hg1).
  set (b := BL.zb (U R 15 <? U R 13)) in *.
  assert (Hb: (U R 13 <= U R 15 /\ b = 0) \/ (U R 15 < U R 13 /\ b = 1 /\ 1 <= U R 14)).
  { subst b. unfold BL.zb. destruct (Z.ltb_spec (U R 15) (U R 13)); [right|left]; lia. }
  assert (V14': U R1 14 = U R 14 - b). { rewrite V14. apply Z.mod_small. unfold BL.MM in *. lia. }
  assert (V15': U R1 15 = U R 15 - U R 13 + b * BL.MM).
  { rewrite V15. destruct Hb as [[A B0]|(A & B1 & C1)]; rewrite ?B0, ?B1.
    - rewrite Z.mod_small; unfold BL.MM in *; lia.
    - replace (U R 15 - U R 13) with ((U R 15 - U R 13 + BL.MM) + (-1) * BL.MM) by lia. unfold BL.MM in *. rewrite Z_mod_plus_full. rewrite Z.mod_small; lia. }
  assert (MEAS: U R1 14 * BL.MM + U R1 15 = U R 14 * BL.MM + U R 15 - U R 13). { rewrite V14', V15'. lia. }
  assert (INV1: U R1 11 = (U R1 15 - U R1 13) mod BL.MM).
  { rewrite V11, INV, (U_eq_of_getr R R1 13 E13), V15. rewrite <- Zminus_mod_idemp_l. reflexivity. }
  pose proof (U_range R1 14) as S14. pose proof (U_range R1 15) as S15.
  pose proof (br225bc M1 R1) as T1. rewrite eqb_U, U_0 in T1.
  destruct (Z.eqb_spec (U R1 14) 0) as [A0|ANZ]; cbn [negb] in T1.
  - pose proof (br225c0 M1 R1) as T2. rewrite ltu_U, V16, INV, (U_eq_of_getr R R1 13 E13) in T2.
    rewrite <- V15 in T2.
    destruct (Z.ltb_spec (U R1 15) (U R 13)) as [BLT|BGE]; cbn [negb] in T2.
    + (* [comment removed for export] *)
      exists fx1, R1, M1. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact T1. exact T2. }
      split. exact K1. split. exact MM1. exact Hg1.
    + destruct (IH (Z.to_nat (U R1 14 * BL.MM + U R1 15)) ltac:(unfold BL.MM in *; lia) fx1 R1 M1 ltac:(lia)
                   ltac:(right; rewrite (U_eq_of_getr R R1 13 E13); lia) INV1 ltac:(rewrite (U_eq_of_getr R R1 13 E13); lia))
        as (fx2 & R2 & M2 & MS2 & K2 & MM2 & Hg2).
      exists fx2, R2, M2. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact T1. eapply msteps_trans. exact T2. exact MS2. }
      split. eapply keptNC_trans; eauto. split. intros a; rewrite MM2; apply MM1. eapply mem_grows_trans; eauto.
  - destruct (IH (Z.to_nat (U R1 14 * BL.MM + U R1 15)) ltac:(unfold BL.MM in *; lia) fx1 R1 M1 ltac:(lia)
                 ltac:(left; exact ANZ) INV1 ltac:(rewrite (U_eq_of_getr R R1 13 E13); lia))
      as (fx2 & R2 & M2 & MS2 & K2 & MM2 & Hg2).
    exists fx2, R2, M2. split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact T1. exact MS2. }
    split. eapply keptNC_trans; eauto. split. intros a; rewrite MM2; apply MM1. eapply mem_grows_trans; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem ddq_run fx R M d :
  U R 13 = d -> 2 ^ 63 <= d < 2 ^ 64 ->
  exists fx' R' M',
    msteps RSEGS (st fx R 0x22578 M) (st fx' R' 0x22670 M')
    /\ keptNC R R' /\ (forall a, M' a = M a) /\ mem_grows M M'.
Proof.
  intros Hd Rd.
  (* [comment removed for export] *)
  destruct (A_step fx R M d Hd Rd) as (fx1 & R1 & M1 & MS1 & K1 & E13a & V14 & MM1 & Hg1).
  assert (D1: 1 <= U R1 14). { rewrite V14. apply Z.div_le_lower_bound; lia. }
  assert (U13a: U R1 13 = d) by (rewrite (U_eq_of_getr R R1 13 E13a); exact Hd).
  (* [comment removed for export] *)
  pose proof (br22514 M1 R1) as T1. rewrite ltu_U in T1.
  assert (L1: exists fx2 R2 M2, msteps RSEGS (st fx1 R1 0x225bc M1) (st fx2 R2 0x225e8 M2)
            /\ keptNC R1 R2 /\ getr R2 (reg 13) = getr R1 (reg 13) /\ (forall a, M2 a = M1 a) /\ mem_grows M1 M2).
  { destruct (Z.ltb_spec (U R1 14) (U R1 17)) as [LT|GE].
    - destruct (loop1_main (Z.to_nat (U R1 17)) fx1 R1 M1 ltac:(lia) ltac:(unfold BL.zb; destruct (U R1 11 <? U R1 5); lia) D1) as (fx2 & R2 & M2 & MS2 & K2 & F13 & MM2 & Hg2).
      exists fx2, R2, M2. split. eapply msteps_trans; eauto. repeat split; auto.
    - destruct (loop1_tail fx1 R1 M1 ltac:(lia) D1) as (fx2 & R2 & M2 & MS2 & K2 & F13 & MM2 & Hg2).
      exists fx2, R2, M2. split. eapply msteps_trans; eauto. repeat split; auto. }
  destruct L1 as (fx2 & R2 & M2 & MS2 & K2 & E13b & MM2 & Hg2).
  assert (U13b: U R2 13 = d) by (rewrite (U_eq_of_getr R1 R2 13 E13b); exact U13a).
  (* [comment removed for export] *)
  destruct (C_step fx2 R2 M2) as (fx3 & R3 & M3 & MS3 & K3 & E13c & E11c & V15 & MM3 & Hg3).
  assert (U13c: U R3 13 = d) by (rewrite (U_eq_of_getr R2 R3 13 E13c); exact U13b).
  pose proof (br2258c M3 R3) as T3. rewrite eqb_U, U_0 in T3.
  (* [comment removed for export] *)
  assert (L2: exists fx5 R5 M5, msteps RSEGS (st fx3 R3 0x22634 M3) (st fx5 R5 0x2266c M5)
            /\ keptNC R3 R5 /\ (forall a, M5 a = M3 a) /\ mem_grows M3 M5).
  { assert (ENTER: (U R3 14 <> 0 \/ U R3 13 <= U R3 15) ->
              exists fx5 R5 M5, msteps RSEGS (st fx3 R3 0x2263c M3) (st fx5 R5 0x2266c M5)
                /\ keptNC R3 R5 /\ (forall a, M5 a = M3 a) /\ mem_grows M3 M5).
    { intros COND. destruct (B2a_step fx3 R3 M3) as (fx4 & R4 & M4 & MS4 & K4 & E13d & E14d & E15d & V11 & MM4 & Hg4).
      pose proof (U_range R4 14) as S14. pose proof (U_range R4 15) as S15.
      destruct (loop2_main (Z.to_nat (U R4 14 * BL.MM + U R4 15)) fx4 R4 M4 ltac:(lia)
                  ltac:(rewrite (U_eq_of_getr R3 R4 14 E14d), (U_eq_of_getr R3 R4 13 E13d), (U_eq_of_getr R3 R4 15 E15d); exact COND)
                  ltac:(rewrite V11, (U_eq_of_getr R3 R4 15 E15d), (U_eq_of_getr R3 R4 13 E13d), V15, (U_eq_of_getr R2 R3 11 E11c);
                        rewrite !Zminus_mod_idemp_l; apply modM_congr with (k := 0); ring)
                  ltac:(rewrite (U_eq_of_getr R3 R4 13 E13d), U13c; lia))
        as (fx5 & R5 & M5 & MS5 & K5 & MM5 & Hg5).
      exists fx5, R5, M5. split. eapply msteps_trans; eauto. split. eapply keptNC_trans; eauto.
      split. intros a; rewrite MM5; apply MM4. eapply mem_grows_trans; eauto. }
    destruct (Z.eqb_spec (U R3 14) 0) as [A0|ANZ]; cbn [negb] in T3.
    - pose proof (br22590 M3 R3) as T4. rewrite ltu_U in T4.
      destruct (Z.ltb_spec (U R3 15) (U R3 13)) as [BLT|BGE].
      + exists fx3, R3, M3. split. eapply msteps_trans; eauto. split. apply keptNC_refl. split. intros; reflexivity. apply mem_grows_refl.
      + destruct (ENTER ltac:(right; lia)) as (fx5 & R5 & M5 & MS5 & K5 & MM5 & Hg5).
        exists fx5, R5, M5. split. { eapply msteps_trans. exact T3. eapply msteps_trans. exact T4. exact MS5. } repeat split; auto.
    - destruct (ENTER ltac:(left; exact ANZ)) as (fx5 & R5 & M5 & MS5 & K5 & MM5 & Hg5).
      exists fx5, R5, M5. split. { eapply msteps_trans. exact T3. exact MS5. } repeat split; auto. }
  destruct L2 as (fx5 & R5 & M5 & MS5 & K5 & MM5 & Hg5).
  destruct (E_step fx5 R5 M5) as (fx6 & R6 & M6 & MS6 & K6 & MM6 & Hg6).
  exists fx6, R6, M6.
  split. { eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. eapply msteps_trans. exact MS3.
           eapply msteps_trans. exact MS5. exact MS6. }
  split. { repeat (eapply keptNC_trans; [eassumption|]). apply keptNC_refl. }
  split. { intros a. rewrite MM6, MM5, MM3, MM2. apply MM1. }
  repeat (eapply mem_grows_trans; [eassumption|]). apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
Lemma reg_lit13 : (13%bv : bv 5) = Z_to_bv 5 (Z.of_nat 13). Proof. apply bv_eq. reflexivity. Qed.

Theorem ddquotient_src0_ok : ddquotient_src0.
Proof.
  intros fx R M d. rewrite reg_lit13. intros H13 Rd. unfold DQ_ENTRY, DQ_RET.
  destruct (ddq_run fx R M d ltac:(unfold U; rewrite H13; apply BG.unsigned_lit; lia) Rd) as (fx' & R' & M' & MS & K & MM & Hg).
  assert (EM: M' = M). { apply FunctionalExtensionality.functional_extensionality. exact MM. }
  subst M'.
  exists fx', R', M. split. exact MS. split.
  - intros r Hr. pose proof (ridx_range r) as RR. rewrite <- (ridx_roundtrip r). set (n := ridx r) in *. clearbody n.
    destruct (Nat.eq_dec n 0) as [->|NZ]. { replace (Z_to_bv 5 (Z.of_nat 0)) with (0%bv : bv 5) by (apply bv_eq; reflexivity). rewrite !getr_zero. reflexivity. }
    apply K. unfold dq_clob in Hr. unfold NC. simpl in Hr. simpl. lia.
  - reflexivity.
Qed.

End BDQ.
