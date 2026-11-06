(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg FPSteps
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SPI.
(* [comment removed for export] *)
Definition kn_eqb (a b : list kentry) : bool :=
  (Nat.eqb (length a) (length b) && forallb (fun p : kentry * kentry => APC.kentry_eqb (fst p) (snd p)) (combine a b))%bool.
Lemma kn_eqb_eq : forall a b, kn_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; unfold kn_eqb in H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [Hl H]. apply andb_prop in H as [Hxy H].
  apply APS.kentry_eqb_eq in Hxy. subst y. f_equal. apply IH. unfold kn_eqb. rewrite Hl, H. reflexivity.
Qed.
Lemma regs_eqb_eq : forall a b, CA.regs_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [Hxy H]. apply AX2S.expr_eqb_eq in Hxy. subst y. f_equal. exact (IH _ H).
Qed.

Definition all_regs_chk (ps : SR.post_spec) : bool :=
  forallb (fun r => existsb (fun ie : nat * expr => Nat.eqb (fst ie) r) (SR.ps_regs ps)) (seq 1 31).

Definition inl_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (len : Z) (hv : list nat) (a0 : option Z) : bool :=
  let regs := CA.ps_reglist ps in
  let nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps) in
  let regs1 := APC.sr_fresh regs hv nx in
  let regs2 := match a0 with Some z => sr_upd regs1 10 (ELit z) | None => regs1 end in
  (all_regs_chk ps && Z.eqb (CC.cp_pc cj) (SR.ps_pc ps + len) && CA.regs_eqb (CC.cp_regs cj) regs2
   && kn_eqb (CC.cp_know cj) (SR.ps_cells ps) && Nat.eqb (CC.cp_nx cj) (nx + length hv)
   && expr_eqb (CC.cp_meas cj) (APC.esub (CC.cp_meas c) (ELit 1))
   && CA.has (SR.ps_cells ps) (KRange (CC.cp_meas c) 1 CC.MB)
   && APC.sr_vars_lt nx regs && APC.kn_vars_lt nx (SR.ps_cells ps) && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c)
   && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) hv
   && match a0 with Some z => (Z.leb 0 z && Z.ltb z (2 ^ 64) && match hv with [] => true | _ => false end)%bool | None => true end)%bool.

Section WithSegs.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Variable CPS : list CC.cutpoint.
Variable NF : nat.
Variable E0 : env.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variable F0 : list SGP.region.
Variable K : ShapeAlg.TSet.
Hypothesis Hhalt : m_halted model0 = None.
Hypothesis Hlazy : m_vm_lazy model0 = [].
Variable FPI : FPState -> Prop.

Abbreviation Amb := (CL.pure_amb NF E0 M0 model0 F0).
Abbreviation mk fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).

Lemma leaf_regs_ok : forall c ps E' R' M M', all_regs_chk ps = true -> CC.leaf_facts segs c ps E' R' M M' ->
  regs_ok E' (CA.ps_reglist ps) R'.
Proof.
  intros c ps E' R' M M' H HLF r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
  - assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er).
    cbn [edenot]. replace (0%bv : bv 5) with (Z_to_bv 5 0) by (apply bv_eq; reflexivity). exact (CC.lf_x0 _ _ _ _ _ _ _ HLF).
  - assert (Hr : (1 <= ridx r < 32)%nat).
    { unfold ridx. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B.
      unfold bv_eqb in Er. apply Z.eqb_neq in Er. change (bv_unsigned (0%bv : bv 5)) with 0 in Er. lia. }
    unfold CA.ps_reglist. destruct (ridx r) as [|m] eqn:Em; [lia|]. cbn [nth].
    rewrite (nth_indep _ (ELit 0) (CA.ps_reg ps 0%nat)) by (rewrite length_map, length_seq; lia).
    rewrite (map_nth (CA.ps_reg ps) (seq 1 31) 0%nat m). rewrite seq_nth by lia.
    unfold all_regs_chk in H. rewrite forallb_forall in H. specialize (H (1 + m)%nat ltac:(apply in_seq; lia)).
    unfold CA.ps_reg. destruct (find (fun ie : nat * expr => Nat.eqb (fst ie) (1 + m)) (SR.ps_regs ps)) as [[i e]|] eqn:Hf.
    + apply find_some in Hf as [Hin Hi]. cbn [fst snd] in *. apply Nat.eqb_eq in Hi. subst i.
      destruct (CC.lf_regs _ _ _ _ _ _ _ HLF _ _ Hin) as [_ Hg]. rewrite <- Hg. f_equal. rewrite <- (CC.reg_of_ridx r). rewrite Em. reflexivity.
    + exfalso. apply existsb_exists in H as (ie & Hin & Hb). rewrite (find_none _ _ Hf ie Hin) in Hb. discriminate.
Qed.

(* [comment removed for export] *)
Lemma inl_common : forall i c ps j cj len hv a0,
  nth_error CPS j = Some cj -> inl_chk c ps cj len hv a0 = true -> CL.sub_F NF E0 F0 c -> (NF <= CC.cp_nx c)%nat ->
  forall (fx2 : FPState) E R M model E' R' R2 M',
    CC.At segs c E R M -> Amb i E M model -> FPI fx2 ->
    env_agree (CC.cp_nx c) E E' -> CC.leaf_facts segs c ps E' R' M M' ->
    CC.IH segs CPS Amb K FPI (CC.meas c E) ->
    (forall r : reg, ~ In (ridx r) hv -> getr R2 r = match a0 with Some z => if bv_eqb r 10 then Z_to_bv 64 z else getr R' r | None => getr R' r end) ->
    srealizes segs SCFG (mkCfg (mk fx2 R2 (SR.ps_pc ps + len) M') model) K.
Proof.
  intros i c ps j cj len hv a0 Hcj Hchk Hsub Hnf fx2 E R M model E' R' R2 M' HAt HAmb HFP Hag HLF HIH Hkeep.
  unfold inl_chk in Hchk. do 11 (apply andb_prop in Hchk as [Hchk ?X]).
  rename Hchk into Xall. apply Z.eqb_eq in X9. apply regs_eqb_eq in X8. apply kn_eqb_eq in X7. apply Nat.eqb_eq in X6. apply AX2S.expr_eqb_eq in X5.
  set (nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps)) in *.
  set (regs := CA.ps_reglist ps) in *.
  pose proof (leaf_regs_ok c ps E' R' M M' Xall HLF) as HR. fold regs in HR.
  set (E2 := APS.ext_list E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) hv)).
  pose proof (APS.ext_list_agree E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) hv) : env_agree nx E' E2) as Hag2.
  assert (Hnxc : (CC.cp_nx c <= nx)%nat) by (unfold nx; lia).
  assert (HagNF : env_agree NF E' E2) by (eapply CC.env_agree_le; [exact Hag2 | lia]).
  assert (Hhv : Forall (fun r => (0 < r < 32)%nat) hv).
  { apply Forall_forall. intros r Hr. rewrite forallb_forall in X0. specialize (X0 r Hr). apply andb_prop in X0 as [A B].
    apply Nat.ltb_lt in A. apply Nat.ltb_lt in B. lia. }
  rewrite <- X9.
  apply (HIH j cj fx2 E2 R2 M' model Hcj).
  - (* [comment removed for export] *)
    split.
    + rewrite X8. destruct a0 as [z|].
      * (* [comment removed for export] *)
        apply andb_prop in X as [X Xhv]. apply andb_prop in X as [Xz0 Xz1]. apply Z.leb_le in Xz0. apply Z.ltb_lt in Xz1.
        destruct hv; [|discriminate]. cbn [APC.sr_fresh].
        intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er0.
        { assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er0; apply Z.eqb_eq in Er0; exact Er0). cbn [edenot]. apply getr_zero. }
        rewrite nth_sr_upd. rewrite (Hkeep r (fun X => X)).
        destruct (bv_eqb r 10) eqn:Er10.
        { assert (r = 10%bv) as -> by (apply bv_eq; unfold bv_eqb in Er10; apply Z.eqb_eq in Er10; exact Er10).
          change (ridx 10%bv) with 10%nat. cbn [Nat.eqb edenot]. reflexivity. }
        assert (Hne : Nat.eqb (ridx r) 10 = false).
        { apply Nat.eqb_neq. intros Hx. unfold bv_eqb in Er10. apply Z.eqb_neq in Er10. apply Er10.
          unfold ridx in Hx. pose proof (bv_unsigned_in_range _ r). change (bv_unsigned (10%bv : bv 5)) with 10. lia. }
        rewrite Hne. rewrite (HR r). unfold sr_get. rewrite Er0.
        apply (SR.edenot_agree_AP nx); [exact Hag2 | apply CH.nth_vars_lt; exact X3].
      * apply CH.fresh_regs_ok; [| exact X3 | exact Hhv].
        intros r Hn. rewrite (Hkeep r Hn). exact (HR r).
    + rewrite X7. unfold know_ok. apply Forall_forall. intros Y HY.
      eapply SGP.kentry_ok_agree1; [exact Hag2 | exact (SGP.kn_vars_lt_In nx _ Y X2 HY) | exact (CC.lf_cells _ _ _ _ _ _ _ HLF Y HY)].
  - (* [comment removed for export] *)
    eapply CL.pure_amb_step; [exact Hsub | exact Hnf | exact HAmb | exact Hag | exact HLF | exact HagNF].
  - exact HFP.
  - (* [comment removed for export] *)
    unfold CC.meas. rewrite X5. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
    assert (Em : edenot E2 (CC.cp_meas c) = edenot E (CC.cp_meas c)).
    { rewrite <- (SR.edenot_agree_AP _ E' E2 _ (CC.env_agree_le _ _ _ _ Hag2 Hnxc) X1). symmetry. exact (SR.edenot_agree_AP _ E E' _ Hag X1). }
    rewrite Em. unfold CA.has in X4. apply existsb_exists in X4 as (Y & HY & Heq). apply APS.kentry_eqb_eq in Heq. subst Y.
    pose proof (CC.lf_cells _ _ _ _ _ _ _ HLF _ HY) as HM. cbn [kentry_ok] in HM.
    rewrite <- (SR.edenot_agree_AP _ E E' _ Hag X1) in HM. unfold CC.MB in HM.
    rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition inl_step (pc len : Z) (hv : list nat) : Prop :=
  forall (fx : FPState) R M, exists R', msteps segs (mk fx R pc M) (mk fx R' (pc + len) M) /\ (forall r : reg, ~ In (ridx r) hv -> getr R' r = getr R r).

Theorem inl_leaf_ok : forall i c ps j cj len hv,
  nth_error CPS j = Some cj -> inl_chk c ps cj len hv None = true -> CL.sub_F NF E0 F0 c -> (NF <= CC.cp_nx c)%nat ->
  inl_step (SR.ps_pc ps) len hv ->
  CC.leaf_ok segs CPS Amb K FPI i c ps.
Proof.
  intros i c ps j cj len hv Hcj Hchk Hsub Hnf Hstep fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct (Hstep fx' R' M') as (R2 & Hms & Hkeep).
  pose proof HAmb as (-> & _).
  eapply L5.cps_of_msteps; [exact Hhalt | exact Hlazy | exact Hms |].
  eapply (inl_common i c ps j cj len hv None Hcj Hchk Hsub Hnf fx' E R M model0 E' R' R2 M'); try eassumption.
Qed.
End WithSegs.

(* [comment removed for export] *)
Lemma fp_step_fclass : forall (fx : FPState) segs regs pc mem rom w fmt rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fclass fmt rd rs1, 4%Z) ->
  exists v, RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
            MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w fmt rd rs1 Hf He Hd.
  destruct fx as [fr cs]. eexists. fp_pipeline Hf He Hd.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

Definition site_fclass_chk (segs : list Segment) (pc : Z) : option nat :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w => if is_ecall w then None else
              match decode_any w with
              | Some (Fclass _ rd _, sz) => if Z.eqb sz 4 then Some (ridx rd) else None
              | _ => None
              end
  | None => None
  end.
Lemma pc4 : forall pc, 0 <= pc < 2 ^ 64 -> v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4).
Proof.
  intros pc Hpc. unfold v_addi. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by exact Hpc. reflexivity.
Qed.
Theorem fclass_step : forall segs pc rd, 0 <= pc < 2 ^ 64 -> site_fclass_chk segs pc = Some rd -> inl_step segs pc 4 [rd].
Proof.
  intros segs pc rd0 Hpc H fx R M. unfold site_fclass_chk in H.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [discriminate|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|discriminate].
  destruct i; try discriminate. destruct (Z.eqb_spec sz 4) as [->|]; [|discriminate]. injection H as <-.
  destruct (fp_step_fclass fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w fmt rd rs1 Hf He Hd) as (v & Hs).
  eexists. split; [rewrite <- pc4 by exact Hpc; apply msteps_one; [reflexivity | exact Hs]|].
  intros r Hn. destruct (bv_eqb rd 0); [reflexivity|]. apply getr_other. intros ->. apply Hn. left. reflexivity.
Qed.
End SPI.
