(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VWord2 VState VLogic VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VGamma.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_Z_to_bv64 z : bv_unsigned (Z_to_bv 64 z) = zwrap 64 z.
Proof. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma bv_signed_zswrap (x : bv 64) : bv_signed x = zswrap 64 (bv_unsigned x).
Proof. unfold bv_signed, bv_swrap, zswrap. reflexivity. Qed.

Lemma bv_swrap32_zswrap z : bv_swrap 32 z = zswrap 32 z.
Proof. reflexivity. Qed.

Lemma bv_wrap64_zwrap z : bv_wrap 64 z = zwrap 64 z.
Proof. reflexivity. Qed.
Lemma bv_wrap32_zwrap z : bv_wrap 32 z = zwrap 32 z.
Proof. reflexivity. Qed.

Lemma rz_zero (r : reg) : Z.eqb (rz r) 0 = true <-> r = 0%bv.
Proof.
  unfold rz. rewrite Z.eqb_eq. split.
  - intros H. apply bv_eq. rewrite H. reflexivity.
  - intros ->. reflexivity.
Qed.

Lemma rz_nonzero (r : reg) : Z.eqb (rz r) 0 = false -> r <> 0%bv.
Proof. intros H E. apply (proj2 (rz_zero r)) in E. congruence. Qed.

Lemma bv_eqb_rz (r : reg) : bv_eqb r 0 = Z.eqb (rz r) 0.
Proof. unfold bv_eqb, rz. reflexivity. Qed.

Lemma reg_key_inj (r r' : reg) : rz r <> 0 -> rz r' <> 0 -> reg_key (rz r') = reg_key (rz r) -> r' = r.
Proof.
  unfold reg_key, rz. intros H1 H2 E. apply bv_eq.
  pose proof (bv_unsigned_in_range 5 r). pose proof (bv_unsigned_in_range 5 r').
  apply (f_equal Zpos) in E. rewrite !Z2Pos.id in E by lia. exact E.
Qed.

Lemma zwrap64_u (x : bv 64) : zwrap 64 (bv_unsigned x) = bv_unsigned x.
Proof. apply zwrap_id. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. simpl in H. lia. Qed.

Lemma wval_const nu c : wval nu (Some (lconst c)) (zwrap 64 c).
Proof. split; [apply zwrap_range; lia|]. rewrite eval_lconst. reflexivity. Qed.

Section Sound.
  Variable SEGS : list Segment.
  Variable P : vparams.
  Variable E : venv.
  Variable mem0 : word -> option byte.

  Notation gammaP := (gamma SEGS P E mem0).

  Definition step_post (A : vstate) (nu : val) (succs : list vstate)
             (regs : bvmap 5 word) (mem : word -> option byte) (pc : word) (rom : word -> option byte) : Prop :=
    exists regs' pc' mem' A' nu',
      RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst regs' pc' mem' rom)
      /\ In A' succs /\ vs_pc A' = bv_unsigned pc'
      /\ ext (vs_next A) nu nu' /\ (vs_next A <= vs_next A')%positive
      /\ frame_mod mem mem' (unit_regions P E)
      /\ gammaP A' nu' regs' mem'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma gamma_lgamma A nu regs mem : gammaP A nu regs mem -> lgamma A nu.
  Proof. intros (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB). split; [exact HS|]. split; [exact HC|]. split; [exact HMo|]. split; [exact HV|exact HB]. Qed.

  Lemma gamma_get_reg A nu regs mem r :
    gammaP A nu regs mem ->
    wval nu (get_reg A (rz r)) (bv_unsigned (getr regs r)) /\ vbelow (get_reg A (rz r)) (vs_next A).
  Proof.
    intros HGm. pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hr. unfold bv_modulus in Hr. simpl in Hr.
    unfold get_reg. destruct (Z.eqb (rz r) 0) eqn:Ez.
    - apply (proj1 (rz_zero r)) in Ez. subst r. split; [|reflexivity].
      split; [lia|]. rewrite eval_lzero. unfold getr. rewrite PropExec.bv_eqb_refl. reflexivity.
    - destruct (pm_get (reg_key (rz r)) (vs_regs A)) as [e|] eqn:Eg.
      + split; [split; [lia|]|].
        * apply HR; auto. unfold rz in Ez. intros X; rewrite X in Ez; discriminate.
        * simpl. destruct HB as (_&_&RB&_). exact (RB _ _ Eg).
      + split; [split; [lia|exact I]|exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma gamma_upd A A1 nu nu1 regs mem (r : reg) (w : word) v p :
    gammaP A nu regs mem -> aext A A1 nu nu1 -> lgamma A1 nu1 ->
    rz r <> 0 -> denotes nu1 (vs_next A1) v (bv_unsigned w) ->
    gammaP (set_pc (set_reg A1 (rz r) v) p) nu1 (regupd regs r w) mem.
  Proof.
    intros HGm (HX&HLe&HSh) HL1 Hr Hv.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    destruct HSh as (SR&SS&SG&SNu&SP&SC&SGh).
    destruct HL1 as (S1&C1&M1&V1&B1). destruct B1 as (B10&B11&B12&B13&B14&B15).
    assert (Hr0 : r <> 0%bv) by (intros ->; apply Hr; reflexivity).
    unfold set_reg. rewrite (proj2 (Z.eqb_neq (rz r) 0) Hr).
    split; [exact HE|]. split; [exact HM|]. split; [eapply gamma_fix_ext; [|exact HX|exact HF]; destruct HB; auto|].
    split; [exact S1|]. split; [exact C1|]. split; [exact M1|]. split; [exact V1|].
    split; [|split; [|split; [|split]]].
    - (* [comment removed for export] *)
      intros r' e Hr' Hg. cbn [vs_regs set_pc set_regs] in Hg.
      destruct (Pos.eqb_spec (reg_key (rz r')) (reg_key (rz r))) as [Ek|Nk].
      + assert (r' = r) by (apply reg_key_inj; auto; unfold rz; auto). subst r'.
        rewrite getr_same by exact Hr0.
        destruct v as [e'|].
        * rewrite pm_get_set_same in Hg. inversion Hg; subst. destruct Hv as [Hv _]. exact Hv.
        * rewrite pm_get_remove_same in Hg. discriminate.
      + assert (Hg' : pm_get (reg_key (bv_unsigned r')) (vs_regs A) = Some e).
        { rewrite <- SR. destruct v; [rewrite pm_get_set_other in Hg by (intros X; apply Nk; symmetry; exact X)
                                     |rewrite pm_get_remove_other in Hg by (intros X; apply Nk; symmetry; exact X)]; exact Hg. }
        rewrite getr_other by (intros ->; apply Nk; reflexivity).
        rewrite (eval_ext_below (vs_next A) nu nu1 e HX); [now apply HR|].
        destruct HB as (_&_&RB&_). exact (RB _ _ Hg').
    - intros off w0 v0 Hin. cbn [vs_slots set_pc set_regs] in Hin. rewrite SS in Hin.
      specialize (HSl _ _ _ Hin). destruct HSl as [HRg HSl]. split; [exact HRg|]. destruct v0 as [e0|]; [|exact I]. cbn [cell_holds] in *.
      rewrite (eval_ext_below (vs_next A) nu nu1 e0 HX); [exact HSl|].
      destruct HB as (_&_&_&CB&_). exact (CB _ _ _ Hin).
    - intros a w0 v0 Hin. cbn [vs_globs set_pc set_regs] in Hin. rewrite SG in Hin.
      specialize (HG _ _ _ Hin). destruct HG as [HRg HG]. split; [exact HRg|]. destruct v0 as [e0|]; [|exact I]. cbn [cell_holds] in *.
      rewrite (eval_ext_below (vs_next A) nu nu1 e0 HX); [exact HG|].
      destruct HB as (_&_&_&_&GB&_). exact (GB _ _ _ Hin).
    - intros lo hi Hin. cbn [vs_nul set_pc set_regs] in Hin. rewrite SNu in Hin. exact (HN _ _ Hin).
    - (* [comment removed for export] *)
      split; [exact B10|]. split; [exact B11|]. split; [|split; [exact B13|split; [exact B14|exact B15]]].
      intros r' e Hg. cbn [vs_regs vs_next set_pc set_regs] in Hg |- *.
      destruct (Pos.eqb_spec r' (reg_key (rz r))) as [->|Nk].
      + destruct v as [e'|]; [rewrite pm_get_set_same in Hg; inversion Hg; subst; exact (proj2 Hv)|rewrite pm_get_remove_same in Hg; discriminate].
      + destruct v; [rewrite pm_get_set_other in Hg by (intros X; apply Nk; symmetry; exact X)
                      |rewrite pm_get_remove_other in Hg by (intros X; apply Nk; symmetry; exact X)]; exact (B12 _ _ Hg).
  Qed.

  (* [comment removed for export] *)
  Lemma gamma_keep A A1 nu nu1 regs mem p :
    gammaP A nu regs mem -> aext A A1 nu nu1 -> lgamma A1 nu1 ->
    gammaP (set_pc A1 p) nu1 regs mem.
  Proof.
    intros HGm (HX&HLe&HSh) HL1.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    destruct HSh as (SR&SS&SG&SNu&SP&SC&SGh).
    destruct HL1 as (S1&C1&M1&V1&B1).
    split; [exact HE|]. split; [exact HM|]. split; [eapply gamma_fix_ext; [|exact HX|exact HF]; destruct HB; auto|].
    split; [exact S1|]. split; [exact C1|]. split; [exact M1|]. split; [exact V1|].
    split; [|split; [|split; [|split; [|exact B1]]]].
    - intros r' e Hr' Hg. cbn [vs_regs set_pc] in Hg. rewrite SR in Hg.
      rewrite (eval_ext_below (vs_next A) nu nu1 e HX); [now apply HR|]. destruct HB as (_&_&RB&_). exact (RB _ _ Hg).
    - intros off w0 v0 Hin. cbn [vs_slots set_pc] in Hin. rewrite SS in Hin.
      specialize (HSl _ _ _ Hin). destruct HSl as [HRg HSl]. split; [exact HRg|]. destruct v0 as [e0|]; [|exact I]. cbn [cell_holds] in *.
      rewrite (eval_ext_below (vs_next A) nu nu1 e0 HX); [exact HSl|]. destruct HB as (_&_&_&CB&_). exact (CB _ _ _ Hin).
    - intros a w0 v0 Hin. cbn [vs_globs set_pc] in Hin. rewrite SG in Hin.
      specialize (HG _ _ _ Hin). destruct HG as [HRg HG]. split; [exact HRg|]. destruct v0 as [e0|]; [|exact I]. cbn [cell_holds] in *.
      rewrite (eval_ext_below (vs_next A) nu nu1 e0 HX); [exact HG|]. destruct HB as (_&_&_&_&GB&_). exact (GB _ _ _ Hin).
    - intros lo hi Hin. cbn [vs_nul set_pc] in Hin. rewrite SNu in Hin. exact (HN _ _ Hin).
  Qed.

  Lemma vs_next_set_reg A r v : vs_next (set_reg A r v) = vs_next A.
  Proof. unfold set_reg. destruct (Z.eqb r 0); reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma step_post_finish A A1 nu nu1 regs mem pc rom (rd : reg) w v :
    gammaP A nu regs mem -> aext A A1 nu nu1 -> lgamma A1 nu1 -> rz rd <> 0 ->
    denotes nu1 (vs_next A1) v (bv_unsigned w) ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd w) (v_addi pc 4) mem rom) ->
    vs_pc A = bv_unsigned pc ->
    step_post A nu [finish A1 (rz rd) v] regs mem pc rom.
  Proof.
    intros HGm HX HL Hr Hv Hstep Hpc.
    exists (regupd regs rd w), (v_addi pc 4), mem, (finish A1 (rz rd) v), nu1.
    split; [exact Hstep|]. split; [left; reflexivity|]. split.
    { unfold finish, npc_of. cbn [vs_pc set_pc]. destruct HX as (_&_&(_&_&_&_&SP&_)). rewrite SP, Hpc.
      unfold v_addi. rewrite u_Z_to_bv64. apply wrap64_zwrap. }
    split; [exact (proj1 HX)|]. split.
    { unfold finish. cbn [vs_next set_pc]. rewrite vs_next_set_reg. exact (proj1 (proj2 HX)). }
    split; [apply frame_mod_refl|].
    unfold finish. eapply gamma_upd; eauto.
  Qed.

  Lemma step_post_res A nu regs mem pc rom (rd : reg) w (rA : absval * vstate) :
    gammaP A nu regs mem -> rz rd <> 0 ->
    res_word A nu rA (bv_unsigned w) ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd w) (v_addi pc 4) mem rom) ->
    vs_pc A = bv_unsigned pc ->
    step_post A nu [let '(v, A1) := rA in finish A1 (rz rd) v] regs mem pc rom.
  Proof.
    intros HGm Hr HR Hstep Hpc. destruct rA as [v A1]. destruct HR as [nu1 (HX&HL&Hv)].
    eapply (step_post_finish A A1 nu nu1); try eassumption.
    all: try exact Hv.
  Qed.

  (* [comment removed for export] *)
  Lemma step_post_nop A nu regs mem pc rom :
    gammaP A nu regs mem ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom) ->
    vs_pc A = bv_unsigned pc ->
    step_post A nu [set_pc A (npc_of A)] regs mem pc rom.
  Proof.
    intros HGm Hstep Hpc.
    exists regs, (v_addi pc 4), mem, (set_pc A (npc_of A)), nu.
    split; [exact Hstep|]. split; [left; reflexivity|]. split.
    { unfold npc_of. cbn [vs_pc set_pc]. rewrite Hpc. unfold v_addi. rewrite u_Z_to_bv64. apply wrap64_zwrap. }
    split; [apply ext_refl|]. split; [cbn; lia|]. split; [apply frame_mod_refl|].
    apply (gamma_keep A A nu nu); auto; [apply aext_refl|eapply gamma_lgamma; eauto].
  Qed.

  Definition succs_of (r : vresult) : list vstate :=
    match r with VR_next l => l | VR_fail _ => [] end.

  (* [comment removed for export] *)
  Lemma step_post_fork A nu regs mem pc rom (rd : reg) w r :
    gammaP A nu regs mem -> rz rd <> 0 -> ares_sound A nu r (bv_unsigned w) ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd w) (v_addi pc 4) mem rom) ->
    vs_pc A = bv_unsigned pc ->
    step_post A nu (succs_of (post_fork A (rz rd) r)) regs mem pc rom.
  Proof.
    intros HGm Hr HR Hstep Hpc. pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    destruct r as [v A'|bsym v0 v1 blo A'].
    - cbn [succs_of post_fork one]. eapply (step_post_res A nu regs mem pc rom rd w (v, A')); eauto.
    - destruct HR as (->&Sb&Cases&D0&D1). unfold post_fork, succs_of.
      set (mk := fun (bv : Z) (v : absval) =>
        let nb := itv_meet (agetbox A bsym) (Some bv, Some bv) in
        if itv_empty nb then []
        else let A1 := asetbox A bsym nb in let A2 := trigger (trigger_fuel A1) A1 in [finish A2 (rz rd) v]).
      change (step_post A nu (mk blo v0 ++ mk (blo + 1) v1) regs mem pc rom).
      assert (ONE : forall bv v, nu bsym = bv -> denotes nu (vs_next A) v (bv_unsigned w) ->
                exists A2, mk bv v = [finish A2 (rz rd) v] /\ aext A A2 nu nu /\ lgamma A2 nu).
      { intros bv v Hbv Hd. unfold mk.
        pose proof (agetbox_sound A nu bsym HL) as Hbox.
        assert (Hnb : in_itv (nu bsym) (itv_meet (agetbox A bsym) (Some bv, Some bv))).
        { apply in_itv_meet; auto. rewrite Hbv. apply in_itv_const. }
        destruct (itv_empty _) eqn:Ee; [exfalso; exact (itv_empty_sound _ _ Ee Hnb)|].
        pose proof (asetbox_sound A nu bsym _ HL Hnb Sb) as [L1 X1].
        destruct (trigger_sound (trigger_fuel (asetbox A bsym (itv_meet (agetbox A bsym) (Some bv, Some bv))))
                    (asetbox A bsym (itv_meet (agetbox A bsym) (Some bv, Some bv))) nu L1) as (L2&X2&N2).
        eexists. split; [reflexivity|]. split; [exact (aext_trans _ _ _ _ _ _ X1 X2)|exact L2]. }
      destruct Cases as [Hb|Hb].
      + destruct (ONE blo v0 Hb (D0 Hb)) as [A2 (Emk&X2&L2)]. rewrite Emk.
        destruct (step_post_finish A A2 nu nu regs mem pc rom rd w v0 HGm X2 L2 Hr) as (regs'&pc'&mem'&A3&nu3&HH); auto.
        { pose proof (D0 Hb) as D. destruct v0 as [e|]; [|exact I]. destruct D as [D' B']. split; [exact D'|].
          eapply lin_below_mono; [|exact B']. exact (proj1 (proj2 X2)). }
        exists regs', pc', mem', A3, nu3. destruct HH as (S1&S2&S3). split; [exact S1|]. split; [|exact S3].
        apply in_app_iff. left. exact S2.
      + destruct (ONE (blo + 1) v1 Hb (D1 Hb)) as [A2 (Emk&X2&L2)]. rewrite Emk.
        destruct (step_post_finish A A2 nu nu regs mem pc rom rd w v1 HGm X2 L2 Hr) as (regs'&pc'&mem'&A3&nu3&HH); auto.
        { pose proof (D1 Hb) as D. destruct v1 as [e|]; [|exact I]. destruct D as [D' B']. split; [exact D'|].
          eapply lin_below_mono; [|exact B']. exact (proj1 (proj2 X2)). }
        exists regs', pc', mem', A3, nu3. destruct HH as (S1&S2&S3). split; [exact S1|]. split; [|exact S3].
        apply in_app_iff. right. exact S2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem x_opimm_sound A nu regs mem pc rom w op (rd rs1 : reg) (imm : bv 12) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (OpImm op rd rs1 imm, 4) ->
    x_opimm A op (rz rd) (rz rs1) (bv_signed imm) = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. unfold x_opimm in Hx.
    pose proof (gamma_get_reg A nu regs mem rs1 HGm) as [Wa Ba].
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    destruct (Z.eqb (rz rd) 0) eqn:Erd.
    { inversion Hx; subst. apply (proj1 (rz_zero rd)) in Erd.
      eapply step_post_nop; eauto.
      erewrite step_opimm_gen; eauto. subst rd. rewrite PropExec.bv_eqb_refl. reflexivity. }
    pose proof (rz_nonzero rd Erd) as Hrd. assert (Hrz : rz rd <> 0) by (intros X; rewrite X in Erd; discriminate).
    assert (Hbe : bv_eqb rd 0 = false) by (rewrite bv_eqb_rz; exact Erd).
    destruct op; try discriminate.
    - (* [comment removed for export] *)
      inversion Hx; subst; clear Hx.
      eapply step_post_finish with (nu1 := nu) (w := v_addi (getr regs rs1) (bv_signed imm)); eauto.
      + apply aext_refl.
      + destruct (get_reg A (rz rs1)) as [e|]; [|exact I]. split.
        * unfold v_addi. rewrite u_Z_to_bv64, anorm_sound, eval_laddc by exact HL.
          rewrite (wval_some _ _ _ Wa). apply zwrap_add_l. lia.
        * apply anorm_below, lin_below_laddc. exact Ba.
      + erewrite step_addi; eauto. rewrite Hbe. reflexivity.
    - (* [comment removed for export] *)
      destruct (do_slt A _ _ true) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_slt_sound A nu (get_reg A (rz rs1)) (Some (lconst (bv_signed imm))) (bv_unsigned (getr regs rs1))
                    (zwrap 64 (bv_signed imm)) true HL Wa (wval_const nu (bv_signed imm)) Ba (lin_below_lconst _ _)) as R.
      rewrite Es in R.
      eapply (step_post_res A nu regs mem pc rom rd (v_slti (getr regs rs1) (bv_signed imm)) (v, A1)); eauto.
      + unfold v_slti, zsig. rewrite bv_signed_zswrap. cbn [rdg] in R.
        rewrite zswrap_zwrap in R by lia.
        pose proof (bv_signed_in_range 12 imm) as Hi. unfold bv_half_modulus, bv_modulus in Hi. simpl in Hi.
        rewrite (zswrap_id 64 (bv_signed imm)) in R by (simpl; lia).
        destruct (_ <? _); rewrite u_Z_to_bv64; exact R.
      + erewrite step_slti; eauto. rewrite Hbe. reflexivity.
    - (* [comment removed for export] *)
      destruct (do_slt A _ _ false) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_slt_sound A nu (get_reg A (rz rs1)) (Some (lconst (zm64 (bv_signed imm)))) (bv_unsigned (getr regs rs1))
                    (zwrap 64 (zm64 (bv_signed imm))) false HL Wa (wval_const nu (zm64 (bv_signed imm))) Ba (lin_below_lconst _ _)) as R.
      rewrite Es in R. rewrite zm64_zwrap, zwrap64_idem in R.
      eapply (step_post_res A nu regs mem pc rom rd (v_sltiu (getr regs rs1) (bv_signed imm)) (v, A1)); eauto.
      + unfold v_sltiu. rewrite bv_wrap64_zwrap. cbn [rdg] in R.
        destruct (_ <? _); rewrite u_Z_to_bv64; exact R.
      + erewrite step_sltiu; eauto. rewrite Hbe. reflexivity.
    - (* [comment removed for export] *)
      destruct (do_xor A _ _) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_xor_sound A nu (get_reg A (rz rs1)) (Some (lconst (bv_signed imm))) (bv_unsigned (getr regs rs1))
                    (zwrap 64 (bv_signed imm)) HL Wa (wval_const nu (bv_signed imm)) Ba (lin_below_lconst _ _)) as R.
      rewrite Es in R.
      eapply (step_post_res A nu regs mem pc rom rd (v_xori (getr regs rs1) (bv_signed imm)) (v, A1)); eauto.
      + unfold v_xori. rewrite u_Z_to_bv64, bv_wrap64_zwrap.
        rewrite zwrap_id; [exact R|]. apply lxor_upper; [lia| |apply zwrap_range; lia].
        pose proof (bv_unsigned_in_range 64 (getr regs rs1)) as Hu. unfold bv_modulus in Hu; simpl in Hu; lia.
      + erewrite step_xori; eauto. rewrite Hbe. reflexivity.
    - (* [comment removed for export] *)
      pose proof (do_or_sound A nu (get_reg A (rz rs1)) (Some (lconst (bv_signed imm))) (bv_unsigned (getr regs rs1))
                    (zwrap 64 (bv_signed imm)) HL Wa (wval_const nu (bv_signed imm)) Ba (lin_below_lconst _ _)) as R.
      replace succs with (succs_of (post_fork A (rz rd) (do_or A (get_reg A (rz rs1)) (Some (lconst (bv_signed imm))))))
        by (rewrite Hx; reflexivity).
      eapply (step_post_fork A nu regs mem pc rom rd (v_ori (getr regs rs1) (bv_signed imm))); eauto.
      + unfold v_ori. rewrite u_Z_to_bv64, bv_wrap64_zwrap.
        rewrite zwrap_id; [exact R|]. apply lor_upper; [lia| |apply zwrap_range; lia].
        pose proof (bv_unsigned_in_range 64 (getr regs rs1)) as Hu. unfold bv_modulus in Hu; simpl in Hu; lia.
      + erewrite step_ori; eauto. rewrite Hbe. reflexivity.
    - (* [comment removed for export] *)
      pose proof (do_and_sound A nu (get_reg A (rz rs1)) (Some (lconst (bv_signed imm))) (bv_unsigned (getr regs rs1))
                    (zwrap 64 (bv_signed imm)) HL Wa (wval_const nu (bv_signed imm)) Ba (lin_below_lconst _ _)) as R.
      replace succs with (succs_of (post_fork A (rz rd) (do_and A (get_reg A (rz rs1)) (Some (lconst (bv_signed imm))))))
        by (rewrite Hx; reflexivity).
      eapply (step_post_fork A nu regs mem pc rom rd (v_andi (getr regs rs1) (bv_signed imm))); eauto.
      + unfold v_andi. rewrite u_Z_to_bv64, bv_wrap64_zwrap.
        rewrite zwrap_id; [exact R|]. apply land_upper64; [|apply zwrap_range; lia].
        pose proof (bv_unsigned_in_range 64 (getr regs rs1)) as Hu. unfold bv_modulus in Hu; simpl in Hu; lia.
      + erewrite step_andi; eauto. rewrite Hbe. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma u_range (x : word) : 0 <= bv_unsigned x < 2 ^ 64.
  Proof. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. simpl in H. lia. Qed.

  Lemma branch_taken_wcond c x y :
    branch_taken c x y = xorb (wcond (fst (bcond_of c)) (bv_unsigned x) (bv_unsigned y)) (snd (bcond_of c)).
  Proof.
    destruct c; cbn [branch_taken bcond_of fst snd wcond]; unfold bv_eqb, bv_lts, bv_ltu; rewrite ?bv_signed_zswrap;
      try reflexivity; destruct (_ =? _) || destruct (_ <? _); reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma step_post_value A nu regs mem pc rom (rd : reg) (wv : word) rA :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc -> rz rd <> 0 ->
    res_word A nu rA (bv_unsigned wv) ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd wv) (v_addi pc 4) mem rom) ->
    step_post A nu [let '(v, A1) := rA in finish A1 (rz rd) v] regs mem pc rom.
  Proof. intros. eapply step_post_res; eauto. Qed.

  Ltac rd_cases rd Hx Erd Hrz Hbe :=
    destruct (Z.eqb (rz rd) 0) eqn:Erd;
    [ inversion Hx; subst
    | pose proof (rz_nonzero rd Erd) as Hrd0;
      assert (Hrz : rz rd <> 0) by (intros X; rewrite X in Erd; discriminate);
      assert (Hbe : bv_eqb rd 0%bv = false) by (rewrite bv_eqb_rz; exact Erd) ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem x_lui_sound A nu regs mem pc rom w (rd : reg) (imm : bv 20) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Lui rd imm, 4) ->
    vstep_core (fun _ _ _ _ _ _ => VR_fail "") (fun _ _ _ _ _ => VR_fail "") A (Lui rd imm) = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. cbn [vstep_core] in Hx. rewrite ?bvs_eq in Hx.
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    rd_cases rd Hx Erd Hrz Hbe.
    { apply (proj1 (rz_zero rd)) in Erd. eapply step_post_nop; eauto. erewrite step_lui; eauto. subst rd. rewrite PropExec.bv_eqb_refl. reflexivity. }
    inversion Hx; subst; clear Hx.
    eapply (step_post_finish A A nu nu regs mem pc rom rd (v_lui (Z.shiftl (bv_signed imm) 12)));
      [exact HGm|apply aext_refl|exact HL|exact Hrz| | |exact Hpc].
    - split; [|reflexivity]. unfold v_lui. rewrite u_Z_to_bv64, eval_lconst. reflexivity.
    - erewrite step_lui; eauto. rewrite Hbe. reflexivity.
  Qed.

  Theorem x_auipc_sound A nu regs mem pc rom w (rd : reg) (imm : bv 20) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Auipc rd imm, 4) ->
    vstep_core (fun _ _ _ _ _ _ => VR_fail "") (fun _ _ _ _ _ => VR_fail "") A (Auipc rd imm) = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. cbn [vstep_core] in Hx. rewrite ?bvs_eq in Hx.
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    rd_cases rd Hx Erd Hrz Hbe.
    { apply (proj1 (rz_zero rd)) in Erd. eapply step_post_nop; eauto. erewrite step_auipc; eauto. subst rd. rewrite PropExec.bv_eqb_refl. reflexivity. }
    inversion Hx; subst; clear Hx.
    eapply (step_post_finish A A nu nu regs mem pc rom rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)));
      [exact HGm|apply aext_refl|exact HL|exact Hrz| | |exact Hpc].
    - split; [|reflexivity]. unfold v_auipc. rewrite u_Z_to_bv64, eval_lconst, wrap64_zwrap, zwrap_idem, Hpc by lia. reflexivity.
    - erewrite step_auipc; eauto. rewrite Hbe. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Theorem x_op_sound A nu regs mem pc rom w op (rd rs1 rs2 : reg) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Op op rd rs1 rs2, 4) ->
    x_op A op (rz rd) (rz rs1) (rz rs2) = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. unfold x_op in Hx.
    pose proof (gamma_get_reg A nu regs mem rs1 HGm) as [Wa Ba].
    pose proof (gamma_get_reg A nu regs mem rs2 HGm) as [Wb Bb].
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    pose proof (u_range (getr regs rs1)) as Ra. pose proof (u_range (getr regs rs2)) as Rb.
    rd_cases rd Hx Erd Hrz Hbe.
    { apply (proj1 (rz_zero rd)) in Erd. eapply step_post_nop; eauto.
      erewrite step_op_gen; eauto. subst rd. rewrite PropExec.bv_eqb_refl. reflexivity. }
    assert (STEP : forall v, alu64 op (getr regs rs1) (getr regs rs2) = v ->
              RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom)).
    { intros v Hv. erewrite step_op_gen; eauto. rewrite Hbe, Hv. reflexivity. }
    destruct op.
    - inversion Hx; subst; clear Hx.
      eapply (step_post_finish A A nu nu regs mem pc rom rd (v_add (getr regs rs1) (getr regs rs2)));
        [exact HGm|apply aext_refl|exact HL|exact Hrz| |apply STEP; apply alu_add|exact Hpc].
      destruct (get_reg A (rz rs1)) as [ea|]; [|exact I]. destruct (get_reg A (rz rs2)) as [eb|]; [|exact I].
      split; [|apply anorm_below; apply lin_below_ladd; auto].
      unfold v_add. rewrite u_Z_to_bv64, anorm_sound, eval_ladd by exact HL.
      rewrite (wval_some _ _ _ Wa), (wval_some _ _ _ Wb). apply zwrap_add. lia.
    - inversion Hx; subst; clear Hx.
      eapply (step_post_finish A A nu nu regs mem pc rom rd (v_sub (getr regs rs1) (getr regs rs2)));
        [exact HGm|apply aext_refl|exact HL|exact Hrz| |apply STEP; apply alu_sub|exact Hpc].
      destruct (get_reg A (rz rs1)) as [ea|]; [|exact I]. destruct (get_reg A (rz rs2)) as [eb|]; [|exact I].
      split; [|apply anorm_below; apply lin_below_lsub; auto].
      unfold v_sub. rewrite u_Z_to_bv64, anorm_sound, eval_lsub by exact HL.
      rewrite (wval_some _ _ _ Wa), (wval_some _ _ _ Wb). apply zwrap_sub. lia.
    - destruct (do_shift A _ _ SH_sll 64) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_shift_sound A nu _ _ _ _ SH_sll 64 HL Wa Wb Ba Bb ltac:(lia)) as R. rewrite Es in R.
      eapply (step_post_value A nu regs mem pc rom rd (v_sll (getr regs rs1) (getr regs rs2)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |apply STEP; apply alu_sll].
      unfold v_sll. rewrite u_Z_to_bv64, Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia). exact R.
    - destruct (do_slt A _ _ true) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_slt_sound A nu _ _ _ _ true HL Wa Wb Ba Bb) as R. rewrite Es in R.
      eapply (step_post_value A nu regs mem pc rom rd (v_slt (getr regs rs1) (getr regs rs2)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |apply STEP; apply alu_slt].
      unfold v_slt, c_lts, bv_lts. rewrite !bv_signed_zswrap. cbn [rdg] in R. destruct (_ <? _); rewrite u_Z_to_bv64; exact R.
    - destruct (do_slt A _ _ false) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_slt_sound A nu _ _ _ _ false HL Wa Wb Ba Bb) as R. rewrite Es in R.
      eapply (step_post_value A nu regs mem pc rom rd (v_sltu (getr regs rs1) (getr regs rs2)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |apply STEP; apply alu_sltu].
      unfold v_sltu, c_ltu, bv_ltu. cbn [rdg] in R. destruct (_ <? _); rewrite u_Z_to_bv64; exact R.
    - destruct (do_xor A _ _) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_xor_sound A nu _ _ _ _ HL Wa Wb Ba Bb) as R. rewrite Es in R.
      eapply (step_post_value A nu regs mem pc rom rd (v_xor (getr regs rs1) (getr regs rs2)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |apply STEP; apply alu_xor].
      unfold v_xor. rewrite u_Z_to_bv64. rewrite zwrap_id; [exact R|]. apply lxor_upper; lia.
    - destruct (do_shift A _ _ SH_srl 64) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_shift_sound A nu _ _ _ _ SH_srl 64 HL Wa Wb Ba Bb ltac:(lia)) as R. rewrite Es in R.
      eapply (step_post_value A nu regs mem pc rom rd (v_srl (getr regs rs1) (getr regs rs2)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |apply STEP; apply alu_srl].
      unfold v_srl. rewrite u_Z_to_bv64, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
      unfold shift_conc in R. cbn [Z.eqb Pos.eqb] in R.
      pose proof (Z.mod_pos_bound (bv_unsigned (getr regs rs2)) 64 ltac:(lia)).
      pose proof (pow2_pos (bv_unsigned (getr regs rs2) mod 64) ltac:(lia)).
      rewrite zwrap_id; [exact R|]. split; [apply Z.div_pos; (ltac2:(LK.k [@Ra; @Rb; @H; @H0; @Erd; @Hrz]); lia)|]. apply Z.div_lt_upper_bound; [lia|nia].
    - destruct (do_shift A _ _ SH_sra 64) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_shift_sound A nu _ _ _ _ SH_sra 64 HL Wa Wb Ba Bb ltac:(lia)) as R. rewrite Es in R.
      eapply (step_post_value A nu regs mem pc rom rd (v_sra (getr regs rs1) (getr regs rs2)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |apply STEP; apply alu_sra].
      unfold v_sra. rewrite u_Z_to_bv64, bv_signed_zswrap. exact R.
    - pose proof (do_or_sound A nu _ _ _ _ HL Wa Wb Ba Bb) as R.
      replace succs with (succs_of (post_fork A (rz rd) (do_or A (get_reg A (rz rs1)) (get_reg A (rz rs2))))) by (rewrite Hx; reflexivity).
      eapply (step_post_fork A nu regs mem pc rom rd (v_or (getr regs rs1) (getr regs rs2))); [exact HGm|exact Hrz| |apply STEP; apply alu_or|exact Hpc].
      unfold v_or. rewrite u_Z_to_bv64. rewrite zwrap_id; [exact R|]. apply lor_upper; lia.
    - pose proof (do_and_sound A nu _ _ _ _ HL Wa Wb Ba Bb) as R.
      replace succs with (succs_of (post_fork A (rz rd) (do_and A (get_reg A (rz rs1)) (get_reg A (rz rs2))))) by (rewrite Hx; reflexivity).
      eapply (step_post_fork A nu regs mem pc rom rd (v_and (getr regs rs1) (getr regs rs2))); [exact HGm|exact Hrz| |apply STEP; apply alu_and|exact Hpc].
      unfold v_and. rewrite u_Z_to_bv64. rewrite zwrap_id; [exact R|]. apply land_upper64; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma kconst_amt (k : Z) (width : Z) :
    0 <= k < width -> (width = 32 \/ width = 64) -> zwrap 64 k mod width = k.
  Proof.
    intros Hk Hw. assert (zwrap 64 k = k) as -> by (apply zwrap_id; lia). apply Z.mod_small. lia.
  Qed.

  Theorem x_shiftimm64_sound A nu regs mem pc rom w op (rd rs1 : reg) (sh : bv 6) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (ShiftImm op rd rs1 sh, 4) ->
    x_shiftimm A op (rz rd) (rz rs1) (bv_unsigned sh) 64 = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. unfold x_shiftimm in Hx.
    pose proof (gamma_get_reg A nu regs mem rs1 HGm) as [Wa Ba].
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    pose proof (u_range (getr regs rs1)) as Ra.
    pose proof (bv_unsigned_in_range 6 sh) as Hsh. unfold bv_modulus in Hsh. simpl in Hsh.
    rd_cases rd Hx Erd Hrz Hbe.
    { apply (proj1 (rz_zero rd)) in Erd. eapply step_post_nop; eauto.
      erewrite step_shiftimm_gen; eauto. subst rd. rewrite PropExec.bv_eqb_refl. reflexivity. }
    pose proof (wval_const nu (bv_unsigned sh)) as Wk.
    destruct op; try discriminate; cbn [shop_of] in Hx.
    - destruct (do_shift A _ _ SH_sll 64) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_shift_sound A nu _ _ _ _ SH_sll 64 HL Wa Wk Ba (lin_below_lconst _ _) ltac:(lia)) as R. rewrite Es in R.
      rewrite kconst_amt in R by lia.
      eapply (step_post_value A nu regs mem pc rom rd (v_slli (getr regs rs1) (bv_unsigned sh)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |].
      + unfold v_slli. rewrite u_Z_to_bv64, Z.shiftl_mul_pow2 by lia. exact R.
      + erewrite step_slli; eauto. rewrite Hbe. reflexivity.
    - destruct (do_shift A _ _ SH_srl 64) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_shift_sound A nu _ _ _ _ SH_srl 64 HL Wa Wk Ba (lin_below_lconst _ _) ltac:(lia)) as R. rewrite Es in R.
      rewrite kconst_amt in R by lia.
      eapply (step_post_value A nu regs mem pc rom rd (v_srli (getr regs rs1) (bv_unsigned sh)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |].
      + unfold v_srli. rewrite u_Z_to_bv64, Z.shiftr_div_pow2 by lia. unfold shift_conc in R. cbn [Z.eqb Pos.eqb] in R.
        pose proof (pow2_pos (bv_unsigned sh) ltac:(lia)).
        rewrite zwrap_id; [exact R|]. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|nia].
      + erewrite step_srli; eauto. rewrite Hbe. reflexivity.
    - destruct (do_shift A _ _ SH_sra 64) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_shift_sound A nu _ _ _ _ SH_sra 64 HL Wa Wk Ba (lin_below_lconst _ _) ltac:(lia)) as R. rewrite Es in R.
      rewrite kconst_amt in R by lia.
      eapply (step_post_value A nu regs mem pc rom rd (v_srai (getr regs rs1) (bv_unsigned sh)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |].
      + unfold v_srai. rewrite u_Z_to_bv64, bv_signed_zswrap. exact R.
      + erewrite step_srai; eauto. rewrite Hbe. reflexivity.
  Qed.

  Theorem x_shiftimm32_sound A nu regs mem pc rom w op (rd rs1 : reg) (sh : bv 5) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (ShiftImm32 op rd rs1 sh, 4) ->
    x_shiftimm A op (rz rd) (rz rs1) (bv_unsigned sh) 32 = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. unfold x_shiftimm in Hx.
    pose proof (gamma_get_reg A nu regs mem rs1 HGm) as [Wa Ba].
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    pose proof (u_range (getr regs rs1)) as Ra.
    pose proof (bv_unsigned_in_range 5 sh) as Hsh. unfold bv_modulus in Hsh. simpl in Hsh.
    rd_cases rd Hx Erd Hrz Hbe.
    { apply (proj1 (rz_zero rd)) in Erd. eapply step_post_nop; eauto.
      erewrite step_shiftimm32_gen; eauto. subst rd. rewrite PropExec.bv_eqb_refl. reflexivity. }
    pose proof (wval_const nu (bv_unsigned sh)) as Wk.
    destruct op; try discriminate; cbn [shop_of] in Hx.
    - destruct (do_shift A _ _ SH_sll 32) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_shift_sound A nu _ _ _ _ SH_sll 32 HL Wa Wk Ba (lin_below_lconst _ _) ltac:(lia)) as R. rewrite Es in R.
      rewrite kconst_amt in R by lia.
      eapply (step_post_value A nu regs mem pc rom rd (v_slliw (getr regs rs1) (bv_unsigned sh)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |].
      + unfold v_slliw. rewrite u_Z_to_bv64, bv_swrap32_zswrap, Z.shiftl_mul_pow2 by lia. exact R.
      + erewrite step_slliw; eauto. rewrite Hbe. reflexivity.
    - destruct (do_shift A _ _ SH_srl 32) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_shift_sound A nu _ _ _ _ SH_srl 32 HL Wa Wk Ba (lin_below_lconst _ _) ltac:(lia)) as R. rewrite Es in R.
      rewrite kconst_amt in R by lia.
      eapply (step_post_value A nu regs mem pc rom rd (v_srliw (getr regs rs1) (bv_unsigned sh)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |].
      + unfold v_srliw. rewrite u_Z_to_bv64, bv_swrap32_zswrap, bv_wrap32_zwrap, Z.shiftr_div_pow2 by lia. exact R.
      + erewrite step_srliw; eauto. rewrite Hbe. reflexivity.
    - destruct (do_shift A _ _ SH_sra 32) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_shift_sound A nu _ _ _ _ SH_sra 32 HL Wa Wk Ba (lin_below_lconst _ _) ltac:(lia)) as R. rewrite Es in R.
      rewrite kconst_amt in R by lia.
      eapply (step_post_value A nu regs mem pc rom rd (v_sraiw (getr regs rs1) (bv_unsigned sh)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |].
      + unfold v_sraiw. rewrite u_Z_to_bv64, !bv_swrap32_zswrap. exact R.
      + erewrite step_sraiw; eauto. rewrite Hbe. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma zswrap32_congr64 a b : zwrap 64 a = zwrap 64 b -> zswrap 32 a = zswrap 32 b.
  Proof.
    intros H. apply zswrap_congr; [lia|]. apply (zwrap_eq_iff 64 a b) in H; [|lia].
    destruct H as [q Hq]. exists (q * 2 ^ 32). change (2 ^ 64) with (2 ^ 32 * 2 ^ 32) in Hq. lia.
  Qed.

  Lemma asext32_word A nu v (x u : Z) :
    lgamma A nu ->
    match v with Some e => zwrap 64 (eval nu e) = zwrap 64 x /\ lin_below e (vs_next A) = true | None => True end ->
    u = zwrap 64 (zswrap 32 x) ->
    res_word A nu (asext32 A v) u.
  Proof.
    intros HL Hv Hu. subst u.
    destruct v as [e|].
    - destruct Hv as [He Hb].
      pose proof (asext32_sound A nu (Some e) (eval nu e) HL ltac:(split; auto)) as R.
      apply res_exact_word in R. rewrite (zswrap32_congr64 (eval nu e) x He) in R. exact R.
    - pose proof (asext32_sound A nu None x HL I) as R. apply res_exact_word in R. exact R.
  Qed.

  Theorem x_opimm32_sound A nu regs mem pc rom w (rd rs1 : reg) (imm : bv 12) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (OpImm32 rd rs1 imm, 4) ->
    x_opimm32 A (rz rd) (rz rs1) (bv_signed imm) = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. unfold x_opimm32 in Hx.
    pose proof (gamma_get_reg A nu regs mem rs1 HGm) as [Wa Ba].
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    rd_cases rd Hx Erd Hrz Hbe.
    { apply (proj1 (rz_zero rd)) in Erd. eapply step_post_nop; eauto.
      erewrite step_opimm32_gen; eauto. subst rd. rewrite PropExec.bv_eqb_refl. reflexivity. }
    destruct (asext32 A _) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
    assert (R : res_word A nu (v, A1) (bv_unsigned (v_addiw (getr regs rs1) (bv_signed imm)))).
    { rewrite <- Es. apply asext32_word with (x := bv_unsigned (getr regs rs1) + bv_signed imm); [exact HL| |].
      - destruct (get_reg A (rz rs1)) as [e|]; [|exact I]. split; [|apply lin_below_laddc; exact Ba].
        rewrite eval_laddc, (wval_some _ _ _ Wa). symmetry. apply zwrap_add_l. lia.
      - unfold v_addiw. rewrite u_Z_to_bv64, bv_swrap32_zswrap. reflexivity. }
    eapply (step_post_value A nu regs mem pc rom rd (v_addiw (getr regs rs1) (bv_signed imm)) (v, A1)); [exact HGm|exact Hpc|exact Hrz|exact R|].
    erewrite step_addiw; eauto. rewrite Hbe. reflexivity.
  Qed.

  Theorem x_op32_sound A nu regs mem pc rom w op (rd rs1 rs2 : reg) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Op32 op rd rs1 rs2, 4) ->
    x_op32 A op (rz rd) (rz rs1) (rz rs2) = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. unfold x_op32 in Hx.
    pose proof (gamma_get_reg A nu regs mem rs1 HGm) as [Wa Ba].
    pose proof (gamma_get_reg A nu regs mem rs2 HGm) as [Wb Bb].
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    pose proof (u_range (getr regs rs1)) as Ra. pose proof (u_range (getr regs rs2)) as Rb.
    rd_cases rd Hx Erd Hrz Hbe.
    { apply (proj1 (rz_zero rd)) in Erd. eapply step_post_nop; eauto.
      erewrite step_op32_gen; eauto. subst rd. rewrite PropExec.bv_eqb_refl. reflexivity. }
    destruct op; try discriminate.
    - destruct (asext32 A _) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      assert (R : res_word A nu (v, A1) (bv_unsigned (v_addw (getr regs rs1) (getr regs rs2)))).
      { rewrite <- Es. apply asext32_word with (x := bv_unsigned (getr regs rs1) + bv_unsigned (getr regs rs2)); [exact HL| |].
        - destruct (get_reg A (rz rs1)) as [ea|]; [|exact I]. destruct (get_reg A (rz rs2)) as [eb|]; [|exact I].
          split; [|apply lin_below_ladd; auto].
          rewrite eval_ladd, (wval_some _ _ _ Wa), (wval_some _ _ _ Wb). symmetry. apply zwrap_add. lia.
        - unfold v_addw. rewrite u_Z_to_bv64, bv_swrap32_zswrap. reflexivity. }
      eapply (step_post_value A nu regs mem pc rom rd (v_addw (getr regs rs1) (getr regs rs2)) (v, A1)); [exact HGm|exact Hpc|exact Hrz|exact R|].
      erewrite step_addw; eauto. rewrite Hbe. reflexivity.
    - destruct (asext32 A _) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      assert (R : res_word A nu (v, A1) (bv_unsigned (v_subw (getr regs rs1) (getr regs rs2)))).
      { rewrite <- Es. apply asext32_word with (x := bv_unsigned (getr regs rs1) - bv_unsigned (getr regs rs2)); [exact HL| |].
        - destruct (get_reg A (rz rs1)) as [ea|]; [|exact I]. destruct (get_reg A (rz rs2)) as [eb|]; [|exact I].
          split; [|apply lin_below_lsub; auto].
          rewrite eval_lsub, (wval_some _ _ _ Wa), (wval_some _ _ _ Wb). symmetry. apply zwrap_sub. lia.
        - unfold v_subw. rewrite u_Z_to_bv64, bv_swrap32_zswrap. reflexivity. }
      eapply (step_post_value A nu regs mem pc rom rd (v_subw (getr regs rs1) (getr regs rs2)) (v, A1)); [exact HGm|exact Hpc|exact Hrz|exact R|].
      erewrite step_subw; eauto. rewrite Hbe. reflexivity.
    - destruct (do_shift A _ _ SH_sll 32) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_shift_sound A nu _ _ _ _ SH_sll 32 HL Wa Wb Ba Bb ltac:(lia)) as R. rewrite Es in R.
      eapply (step_post_value A nu regs mem pc rom rd (v_sllw (getr regs rs1) (getr regs rs2)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |].
      + unfold v_sllw. rewrite u_Z_to_bv64, bv_swrap32_zswrap, Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia). exact R.
      + erewrite step_sllw; eauto. rewrite Hbe. reflexivity.
    - destruct (do_shift A _ _ SH_srl 32) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_shift_sound A nu _ _ _ _ SH_srl 32 HL Wa Wb Ba Bb ltac:(lia)) as R. rewrite Es in R.
      eapply (step_post_value A nu regs mem pc rom rd (v_srlw (getr regs rs1) (getr regs rs2)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |].
      + unfold v_srlw. rewrite u_Z_to_bv64, bv_swrap32_zswrap, bv_wrap32_zwrap, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia). exact R.
      + erewrite step_srlw; eauto. rewrite Hbe. reflexivity.
    - destruct (do_shift A _ _ SH_sra 32) as [v A1] eqn:Es. inversion Hx; subst; clear Hx.
      pose proof (do_shift_sound A nu _ _ _ _ SH_sra 32 HL Wa Wb Ba Bb ltac:(lia)) as R. rewrite Es in R.
      eapply (step_post_value A nu regs mem pc rom rd (v_sraw (getr regs rs1) (getr regs rs2)) (v, A1)); [exact HGm|exact Hpc|exact Hrz| |].
      + unfold v_sraw. rewrite u_Z_to_bv64, !bv_swrap32_zswrap. exact R.
      + erewrite step_sraw; eauto. rewrite Hbe. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma mul_div_conc op (x y : word) :
    match op with M_MULH | M_MULHSU => False | _ => True end ->
    bv_unsigned (mul_div op x y) = muldiv_conc (mop_of op) (bv_unsigned x) (bv_unsigned y).
  Proof.
    intros Hop. pose proof (u_range x) as Rx. pose proof (u_range y) as Ry.
    destruct op; try contradiction; cbn [mop_of muldiv_conc].
    - rewrite m_mul. unfold v_mul. apply u_Z_to_bv64.
    - rewrite m_mulhu. unfold v_mulhu. rewrite u_Z_to_bv64, Z.shiftr_div_pow2 by lia. apply zwrap_id.
      split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. apply Z.mul_lt_mono_nonneg; lia.
    - rewrite m_div. unfold v_div, zsig. rewrite !bv_signed_zswrap.
      destruct (bv_unsigned y =? 0); apply u_Z_to_bv64.
    - unfold mul_div. destruct (Z.eqb_spec (bv_unsigned y) 0).
      + rewrite u_Z_to_bv64. reflexivity.
      + change (bv_divu x y) with (mul_div M_DIVU x y) at 1 || idtac.
        pose proof (m_divu x y n) as Em. unfold mul_div in Em. rewrite (proj2 (Z.eqb_neq _ _) n) in Em.
        rewrite Em. unfold v_divu. rewrite u_Z_to_bv64. apply zwrap_id.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|nia].
    - rewrite m_rem. unfold v_rem, zsig. rewrite !bv_signed_zswrap.
      destruct (bv_unsigned y =? 0); [|apply u_Z_to_bv64].
      rewrite zwrap_of_zswrap by lia. symmetry. apply zwrap64_u.
    - unfold mul_div. destruct (Z.eqb_spec (bv_unsigned y) 0); [reflexivity|].
      pose proof (m_remu x y n) as Em. unfold mul_div in Em. rewrite (proj2 (Z.eqb_neq _ _) n) in Em.
      rewrite Em. unfold v_remu. rewrite u_Z_to_bv64. apply zwrap_id.
      pose proof (Z.mod_pos_bound (bv_unsigned x) (bv_unsigned y) ltac:(lia)). lia.
  Qed.

  Theorem x_mul_sound A nu regs mem pc rom w op (rd rs1 rs2 : reg) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Mul op rd rs1 rs2, 4) ->
    x_mul A op (rz rd) (rz rs1) (rz rs2) = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. unfold x_mul in Hx.
    pose proof (gamma_get_reg A nu regs mem rs1 HGm) as [Wa Ba].
    pose proof (gamma_get_reg A nu regs mem rs2 HGm) as [Wb Bb].
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    rd_cases rd Hx Erd Hrz Hbe.
    { apply (proj1 (rz_zero rd)) in Erd. eapply step_post_nop; eauto.
      erewrite step_mul_gen; eauto. subst rd. rewrite PropExec.bv_eqb_refl. reflexivity. }
    assert (STEP : RiscvSemantics.step SEGS (mkst regs pc mem rom) =
                   MachineOk (mkst (regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom)).
    { erewrite step_mul_gen; eauto. rewrite Hbe. reflexivity. }
    assert (GEN : match op with M_MULH | M_MULHSU => False | _ => True end ->
              forall v A1, do_muldiv A (mop_of op) (get_reg A (rz rs1)) (get_reg A (rz rs2)) 64 = (v, A1) ->
              succs = [finish A1 (rz rd) v] -> step_post A nu succs regs mem pc rom).
    { intros Hop v A1 Edm ->.
      pose proof (do_muldiv_sound A nu (mop_of op) _ _ _ _ 64 HL Wa Wb Ba Bb ltac:(destruct op; exact Hop)) as R.
      rewrite Edm in R. rewrite <- mul_div_conc in R by exact Hop.
      eapply (step_post_value A nu regs mem pc rom rd _ (v, A1)); [exact HGm|exact Hpc|exact Hrz|exact R|exact STEP]. }
    destruct op; cbn [mop_of] in Hx, GEN;
      try (destruct (do_muldiv A _ _ _ 64) as [v A1] eqn:Edm; inversion Hx; subst; clear Hx; apply (GEN I v A1 eq_refl eq_refl)).
    - inversion Hx; subst; clear Hx.
      eapply (step_post_finish A A nu nu regs mem pc rom rd (mul_div M_MULH (getr regs rs1) (getr regs rs2)) None);
        [exact HGm|apply aext_refl|exact HL|exact Hrz|exact I|exact STEP|exact Hpc].
    - inversion Hx; subst; clear Hx.
      eapply (step_post_finish A A nu nu regs mem pc rom rd (mul_div M_MULHSU (getr regs rs1) (getr regs rs2)) None);
        [exact HGm|apply aext_refl|exact HL|exact Hrz|exact I|exact STEP|exact Hpc].
  Qed.

  Lemma sext32_word (b : bv 32) : bv_unsigned (sext 64 b) = zwrap 64 (zswrap 32 (bv_unsigned b)).
  Proof. rewrite sext32_unsigned. reflexivity. Qed.

  #[using="Type"] Theorem x_mul32_sound A nu regs mem pc rom w op (rd rs1 rs2 : reg) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Mul32 op rd rs1 rs2, 4) ->
    x_mul32 A op (rz rd) (rz rs1) (rz rs2) = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. unfold x_mul32 in Hx.
    pose proof (gamma_get_reg A nu regs mem rs1 HGm) as [Wa Ba].
    pose proof (gamma_get_reg A nu regs mem rs2 HGm) as [Wb Bb].
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    pose proof (u_range (getr regs rs1)) as Ra. pose proof (u_range (getr regs rs2)) as Rb.
    rd_cases rd Hx Erd Hrz Hbe.
    { apply (proj1 (rz_zero rd)) in Erd. eapply step_post_nop; eauto.
      erewrite step_mul32_gen; eauto. subst rd. rewrite PropExec.bv_eqb_refl. reflexivity. }
    assert (STEP : RiscvSemantics.step SEGS (mkst regs pc mem rom) =
                   MachineOk (mkst (regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2))))) (v_addi pc 4) mem rom)).
    { erewrite step_mul32_gen; eauto. rewrite Hbe. reflexivity. }
    set (wres := sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))) in *.
    assert (Hs32 : exists sv, bv_unsigned wres = zwrap 64 sv /\ - 2 ^ 31 <= sv < 2 ^ 31).
    { exists (bv_signed (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))). split.
      - unfold wres. rewrite sext32_unsigned. unfold bv_signed. reflexivity.
      - pose proof (bv_signed_in_range 32 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2))) ltac:(discriminate)) as X.
        unfold bv_half_modulus, bv_modulus in X. simpl in X. lia. }
    assert (FRESH : forall v A1, afresh A s32range = (v, A1) -> succs = [finish A1 (rz rd) v] -> step_post A nu succs regs mem pc rom).
    { intros v A1 Ef ->. destruct Hs32 as [sv [Hsv Rsv]].
      pose proof (res_exact_fresh A nu s32range sv HL (s32range_itv sv Rsv)) as R. rewrite Ef in R.
      apply res_exact_word in R. rewrite <- Hsv in R.
      eapply (step_post_value A nu regs mem pc rom rd wres (v, A1)); [exact HGm|exact Hpc|exact Hrz|exact R|exact STEP]. }
    destruct op; cbn [mop_of] in Hx;
      try (destruct (afresh A s32range) as [v A1] eqn:Ef; inversion Hx; subst; clear Hx; apply (FRESH v A1 eq_refl eq_refl)).
    all: (* [comment removed for export] *)
      destruct (match get_reg A (rz rs1) with Some e => azext A (Some e) 32 | None => (None, A) end) as [a32 A1] eqn:E1;
      destruct (match get_reg A1 (rz rs2) with Some e => azext A1 (Some e) 32 | None => (None, A1) end) as [b32 A2] eqn:E2;
      destruct (do_muldiv A2 _ a32 b32 32) as [r A3] eqn:E3;
      destruct (asext32 A3 r) as [v A4] eqn:E4; inversion Hx; subst; clear Hx.
    all: set (ua := bv_unsigned (getr regs rs1)) in *; set (ub := bv_unsigned (getr regs rs2)) in *.
    all: assert (X1 : exists nu1, aext A A1 nu nu1 /\ lgamma A1 nu1 /\ wval nu1 a32 (zwrap 32 ua) /\ vbelow a32 (vs_next A1))
      by (destruct (get_reg A (rz rs1)) as [ea|];
          [ pose proof (azext_sound A nu (Some ea) (eval nu ea) 32 HL ltac:((ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Ba]); lia)) ltac:(split; [reflexivity|exact Ba])) as Z1;
            rewrite E1 in Z1; destruct Z1 as [nu1 (X&L&R)]; exists nu1; split; [exact X|]; split; [exact L|];
            destruct a32 as [e1|]; [|destruct (azext_some A (Some ea) 32) as [? [? EE]]; rewrite E1 in EE; discriminate];
            destruct R as [R1 R2]; split; [|exact R2]; split; [pose proof (zwrap_range 32 ua ltac:((ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Ba]); lia))); (ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Ba]); lia)|];
            rewrite R1, (wval_some _ _ _ Wa); unfold ua; rewrite (zwrap_zwrap 32 64) by (ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Ba]); lia); symmetry; apply zwrap_id; pose proof (zwrap_range 32 (eval nu ea) ltac:((ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Ba]); lia))); (ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Ba]); lia)
          | inversion E1; subst; exists nu; split; [apply aext_refl|]; split; [exact HL|]; split; [apply wval_none; pose proof (zwrap_range 32 ua ltac:((ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Ba]); lia))); (ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Ba]); lia)|exact I] ]).
    all: destruct X1 as [nu1 (XA1&L1&W1&B1)].
    all: assert (Wb1 : wval nu1 (get_reg A1 (rz rs2)) ub /\ vbelow (get_reg A1 (rz rs2)) (vs_next A1))
      by (destruct XA1 as (XE&XL&(XR&_)); unfold get_reg in *; rewrite XR;
          destruct (rz rs2 =? 0); [split; [exact Wb|reflexivity]|];
          destruct (pm_get (reg_key (rz rs2)) (vs_regs A)) as [eb|] eqn:Eg; [|split; [exact Wb|exact I]];
          simpl in Bb; split; [eapply wval_ext; [exact XE|exact Bb|exact Wb]|simpl; eapply lin_below_mono; [exact XL|exact Bb]]).
    all: destruct Wb1 as [Wb1 Bb1].
    all: assert (X2 : exists nu2, aext A1 A2 nu1 nu2 /\ lgamma A2 nu2 /\ wval nu2 b32 (zwrap 32 ub) /\ vbelow b32 (vs_next A2))
      by (destruct (get_reg A1 (rz rs2)) as [eb|];
          [ pose proof (azext_sound A1 nu1 (Some eb) (eval nu1 eb) 32 L1 ltac:((ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Bb1]); lia)) ltac:(split; [reflexivity|exact Bb1])) as Z2;
            rewrite E2 in Z2; destruct Z2 as [nu2 (X&L&R)]; exists nu2; split; [exact X|]; split; [exact L|];
            destruct b32 as [e2|]; [|destruct (azext_some A1 (Some eb) 32) as [? [? EE]]; rewrite E2 in EE; discriminate];
            destruct R as [R1 R2]; split; [|exact R2]; split; [pose proof (zwrap_range 32 ub ltac:((ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Bb1]); lia))); (ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Bb1]); lia)|];
            rewrite R1, (wval_some _ _ _ Wb1); unfold ub; rewrite (zwrap_zwrap 32 64) by (ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Bb1]); lia); symmetry; apply zwrap_id; pose proof (zwrap_range 32 (eval nu1 eb) ltac:((ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Bb1]); lia))); (ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Bb1]); lia)
          | inversion E2; subst; exists nu1; split; [apply aext_refl|]; split; [exact L1|]; split; [apply wval_none; pose proof (zwrap_range 32 ub ltac:((ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Bb1]); lia))); (ltac2:(LK.k [@Ra; @Rb; @Erd; @Hrz; @H; @Bb1]); lia)|exact I] ]).
    all: destruct X2 as [nu2 (XA2&L2&W2&B2)].
    all: assert (W1' : wval nu2 a32 (zwrap 32 ua)) by (eapply wval_ext; [exact (proj1 XA2)|destruct a32; [exact B1|exact I]|exact W1]).
    all: assert (B1' : vbelow a32 (vs_next A2)) by (destruct a32; [simpl; eapply lin_below_mono; [exact (proj1 (proj2 XA2))|exact B1]|exact I]).
    - pose proof (do_muldiv_sound A2 nu2 MO_mul a32 b32 _ _ 32 L2 W1' W2 B1' B2 I) as R3. rewrite E3 in R3.
      destruct R3 as [nu3 (XA3&L3&R3)].
      assert (R4 : res_word A3 nu3 (asext32 A3 r) (bv_unsigned wres)).
      { apply asext32_word with (x := muldiv_conc MO_mul (zwrap 32 ua) (zwrap 32 ub)); [exact L3| |].
        - destruct r as [e|]; [|exact I]. destruct R3 as [R3a R3b]. split; [|exact R3b]. rewrite <- R3a. cbn [muldiv_conc]. now rewrite zwrap_idem.
        - unfold wres. rewrite w_mulw. unfold v_mulw. rewrite u_Z_to_bv64, bv_swrap32_zswrap. f_equal. cbn [muldiv_conc].
          rewrite zswrap_zwrap by lia. apply zswrap_congr; [lia|]. unfold ua, ub, zwrap.
          pose proof (Z.div_mod (bv_unsigned (getr regs rs1)) (2 ^ 32) ltac:(lia)). pose proof (Z.div_mod (bv_unsigned (getr regs rs2)) (2 ^ 32) ltac:(lia)).
          set (qa := bv_unsigned (getr regs rs1) / 2 ^ 32) in *. set (qb := bv_unsigned (getr regs rs2) / 2 ^ 32) in *.
          set (ra := bv_unsigned (getr regs rs1) mod 2 ^ 32) in *. set (rb := bv_unsigned (getr regs rs2) mod 2 ^ 32) in *.
          exists (qa * qb * 2 ^ 32 + qa * rb + qb * ra). (ltac2:(LK.k [@Erd; @Ra; @Rb; @Hrz; @H; @H0]); nia). }
      rewrite E4 in R4. destruct R4 as [nu4 (XA4&L4&R4)].
      eapply (step_post_finish A A4 nu nu4 regs mem pc rom rd wres v); [exact HGm| |exact L4|exact Hrz|exact R4|exact STEP|exact Hpc].
      eapply aext_trans; [exact XA1|]. eapply aext_trans; [exact XA2|]. eapply aext_trans; [exact XA3|exact XA4].
    - pose proof (do_muldiv_sound A2 nu2 MO_divu a32 b32 _ _ 32 L2 W1' W2 B1' B2 I) as R3. rewrite E3 in R3.
      destruct R3 as [nu3 (XA3&L3&R3)].
      assert (R4 : res_word A3 nu3 (asext32 A3 r) (bv_unsigned wres)).
      { apply asext32_word with (x := if Z.eqb (zwrap 32 ub) 0 then -1 else zwrap 32 ua / zwrap 32 ub); [exact L3| |].
        - destruct r as [e|]; [|exact I]. destruct R3 as [R3a R3b]. split; [|exact R3b]. rewrite <- R3a. cbn [muldiv_conc].
          pose proof (zwrap_range 32 ua ltac:(lia)). pose proof (zwrap_range 32 ub ltac:(lia)).
          destruct (Z.eqb_spec (zwrap 32 ub) 0); [reflexivity|]. symmetry. apply zwrap_id.
          split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|nia].
        - unfold wres. rewrite w_divuw. unfold v_divuw. rewrite !bv_wrap32_zwrap. fold ua ub.
          destruct (zwrap 32 ub =? 0); rewrite u_Z_to_bv64, ?bv_swrap32_zswrap; reflexivity. }
      rewrite E4 in R4. destruct R4 as [nu4 (XA4&L4&R4)].
      eapply (step_post_finish A A4 nu nu4 regs mem pc rom rd wres v); [exact HGm| |exact L4|exact Hrz|exact R4|exact STEP|exact Hpc].
      eapply aext_trans; [exact XA1|]. eapply aext_trans; [exact XA2|]. eapply aext_trans; [exact XA3|exact XA4].
    - pose proof (do_muldiv_sound A2 nu2 MO_remu a32 b32 _ _ 32 L2 W1' W2 B1' B2 I) as R3. rewrite E3 in R3.
      destruct R3 as [nu3 (XA3&L3&R3)].
      assert (R4 : res_word A3 nu3 (asext32 A3 r) (bv_unsigned wres)).
      { apply asext32_word with (x := if Z.eqb (zwrap 32 ub) 0 then zwrap 32 ua else zwrap 32 ua mod zwrap 32 ub); [exact L3| |].
        - destruct r as [e|]; [|exact I]. destruct R3 as [R3a R3b]. split; [|exact R3b]. rewrite <- R3a. cbn [muldiv_conc].
          pose proof (zwrap_range 32 ua ltac:(lia)). pose proof (zwrap_range 32 ub ltac:(lia)).
          destruct (Z.eqb_spec (zwrap 32 ub) 0); symmetry; apply zwrap_id; [lia|].
          pose proof (Z.mod_pos_bound (zwrap 32 ua) (zwrap 32 ub) ltac:(lia)). lia.
        - unfold wres. rewrite w_remuw. unfold v_remuw. rewrite !bv_wrap32_zwrap. fold ua ub.
          destruct (zwrap 32 ub =? 0); rewrite u_Z_to_bv64, ?bv_swrap32_zswrap; [|reflexivity].
          f_equal. unfold ua. symmetry. apply zswrap_zwrap. lia. }
      rewrite E4 in R4. destruct R4 as [nu4 (XA4&L4&R4)].
      eapply (step_post_finish A A4 nu nu4 regs mem pc rom rd wres v); [exact HGm| |exact L4|exact Hrz|exact R4|exact STEP|exact Hpc].
      eapply aext_trans; [exact XA1|]. eapply aext_trans; [exact XA2|]. eapply aext_trans; [exact XA3|exact XA4].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem x_branch_sound A nu regs mem pc rom w c (rs1 rs2 : reg) (imm : bv 13) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Branch c rs1 rs2 imm, 4) ->
    x_branch A c (rz rs1) (rz rs2) (bv_signed imm) = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. unfold x_branch in Hx.
    pose proof (gamma_get_reg A nu regs mem rs1 HGm) as [Wa Ba].
    pose proof (gamma_get_reg A nu regs mem rs2 HGm) as [Wb Bb].
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    set (taken := branch_taken c (getr regs rs1) (getr regs rs2)).
    assert (Htk : taken = xorb (wcond (fst (bcond_of c)) (bv_unsigned (getr regs rs1)) (bv_unsigned (getr regs rs2))) (snd (bcond_of c)))
      by apply branch_taken_wcond.
    assert (TGT : bv_unsigned (btgt pc (bv_signed imm)) = wrap64 (vs_pc A + bv_signed imm)).
    { unfold btgt, v_addi. rewrite u_Z_to_bv64, wrap64_zwrap, Hpc. reflexivity. }
    assert (NPC : bv_unsigned (v_addi pc 4) = npc_of A).
    { unfold npc_of, v_addi. rewrite u_Z_to_bv64, wrap64_zwrap, Hpc. reflexivity. }
    assert (POST : forall A1 (pc' : word) p, aext A A1 nu nu -> lgamma A1 nu -> p = bv_unsigned pc' ->
              RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst regs pc' mem rom) ->
              forall l, In (set_pc A1 p) l -> step_post A nu l regs mem pc rom).
    { intros A1 pc' p X1 L1 Hp Hstep l Hin. exists regs, pc', mem, (set_pc A1 p), nu.
      split; [exact Hstep|]. split; [exact Hin|]. split; [exact Hp|]. split; [apply ext_refl|].
      split; [cbn; exact (proj1 (proj2 X1))|]. split; [apply frame_mod_refl|]. apply (gamma_keep A A1 nu nu); auto. }
    destruct (eval_cond A (bcond_of c) _ _) as [r|] eqn:Ec.
    - pose proof (eval_cond_sound A nu (bcond_of c) _ _ _ _ r HL Wa Wb Ec) as Hr. rewrite <- Htk in Hr.
      destruct r; inversion Hx; subst; clear Hx.
      + eapply (POST A (btgt pc (bv_signed imm))); [apply aext_refl|exact HL|symmetry; exact TGT| |left; reflexivity].
        eapply step_branch_tk_gen; eauto.
      + eapply (POST A (v_addi pc 4)); [apply aext_refl|exact HL|symmetry; exact NPC| |left; reflexivity].
        eapply step_branch_ft_gen; eauto.
    - destruct (refine A (bcond_of c) _ _) as [ok_t At] eqn:Et.
      destruct (refine A (negc (bcond_of c)) _ _) as [ok_f Af] eqn:Ef. inversion Hx; subst; clear Hx.
      destruct taken eqn:Etk.
      + pose proof (refine_sound A nu (bcond_of c) _ _ _ _ HL Wa Wb Ba Bb ltac:(rewrite <- Htk; reflexivity)) as (F&L&X&N).
        rewrite Et in F, L, X. cbn [fst snd] in F, L, X. subst ok_t.
        eapply (POST At (btgt pc (bv_signed imm))); [exact X|exact L|symmetry; exact TGT| |].
        * eapply step_branch_tk_gen; eauto.
        * apply in_app_iff. right. left. reflexivity.
      + pose proof (refine_sound A nu (negc (bcond_of c)) _ _ _ _ HL Wa Wb Ba Bb) as RS.
        unfold negc in RS. cbn [fst snd] in RS. rewrite <- xorb_negb in RS || idtac.
        assert (Hneg : xorb (wcond (fst (bcond_of c)) (bv_unsigned (getr regs rs1)) (bv_unsigned (getr regs rs2))) (negb (snd (bcond_of c))) = true).
        { destruct (wcond _ _ _); destruct (snd (bcond_of c)); simpl in *; congruence. }
        specialize (RS Hneg). destruct RS as (F&L&X&N). unfold negc in Ef. rewrite Ef in F, L, X. cbn [fst snd] in F, L, X. subst ok_f.
        eapply (POST Af (v_addi pc 4)); [exact X|exact L|symmetry; exact NPC| |left; reflexivity].
        eapply step_branch_ft_gen; eauto.
  Qed.

  Theorem x_jal_sound A nu regs mem pc rom w (rd : reg) (imm : bv 21) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Jal rd imm, 4) ->
    x_jal A (rz rd) (bv_signed imm) = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. unfold x_jal in Hx. inversion Hx; subst; clear Hx.
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    assert (TGT : bv_unsigned (btgt pc (bv_signed imm)) = wrap64 (vs_pc A + bv_signed imm)).
    { unfold btgt, v_addi. rewrite u_Z_to_bv64, wrap64_zwrap, Hpc. reflexivity. }
    exists (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4)), (btgt pc (bv_signed imm)), mem,
      (set_pc (set_reg A (rz rd) (Some (lconst (npc_of A)))) (wrap64 (vs_pc A + bv_signed imm))), nu.
    split; [eapply step_jal_link; eauto|]. split; [left; reflexivity|]. split; [cbn; symmetry; exact TGT|].
    split; [apply ext_refl|]. split; [cbn; rewrite vs_next_set_reg; lia|]. split; [apply frame_mod_refl|].
    rewrite bv_eqb_rz. destruct (Z.eqb (rz rd) 0) eqn:Erd.
    - unfold set_reg. rewrite Erd. apply (gamma_keep A A nu nu); auto. apply aext_refl.
    - apply (gamma_upd A A nu nu); [exact HGm|apply aext_refl|exact HL|intros X; rewrite X in Erd; discriminate|].
      split; [|reflexivity]. unfold v_addi, npc_of. rewrite u_Z_to_bv64, eval_lconst, wrap64_zwrap, zwrap_idem, Hpc by lia. reflexivity.
  Qed.

  Theorem x_jalr_sound A nu regs mem pc rom w (rd rs1 : reg) (imm : bv 12) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Jalr rd rs1 imm, 4) ->
    x_jalr A (rz rd) (rz rs1) (bv_signed imm) = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. unfold x_jalr in Hx.
    pose proof (gamma_get_reg A nu regs mem rs1 HGm) as [Wa Ba].
    pose proof (gamma_lgamma _ _ _ _ HGm) as HL.
    destruct (get_reg A (rz rs1)) as [e|] eqn:Eg; [|discriminate]. simpl in Ba.
    pose proof (wval_some _ _ _ Wa) as Hua.
    assert (LINK : denotes nu (vs_next A) (Some (lconst (npc_of A))) (bv_unsigned (v_addi pc 4))).
    { split; [|reflexivity]. unfold v_addi, npc_of. rewrite u_Z_to_bv64, eval_lconst, wrap64_zwrap, zwrap_idem, Hpc by lia. reflexivity. }
    assert (GOAL : forall A1 t, aext A A1 nu nu -> lgamma A1 nu -> bv_unsigned (getr regs rs1) = zwrap 64 t ->
       forall l, In (set_pc (set_reg A1 (rz rd) (Some (lconst (npc_of A)))) (wrap64 (Z.land (zwrap 64 t + bv_signed imm) (-2)))) l ->
       step_post A nu l regs mem pc rom).
    { intros A1 t X1 L1 Ht l Hin.
      exists (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4)), (v_jalr (getr regs rs1) (bv_signed imm)), mem,
        (set_pc (set_reg A1 (rz rd) (Some (lconst (npc_of A)))) (wrap64 (Z.land (zwrap 64 t + bv_signed imm) (-2)))), nu.
      split; [eapply step_jalr; eauto|]. split; [exact Hin|]. split.
      { cbn. unfold v_jalr, jalr_tgtZ. rewrite u_Z_to_bv64, wrap64_zwrap, Ht. reflexivity. }
      split; [apply ext_refl|]. split; [cbn; rewrite vs_next_set_reg; exact (proj1 (proj2 X1))|]. split; [apply frame_mod_refl|].
      rewrite bv_eqb_rz. destruct (Z.eqb (rz rd) 0) eqn:Erd.
      - unfold set_reg. rewrite Erd. apply (gamma_keep A A1 nu nu); auto.
      - apply (gamma_upd A A1 nu nu); [exact HGm|exact X1|exact L1|intros X; rewrite X in Erd; discriminate|].
        destruct LINK as [L' _]. split; [exact L'|reflexivity]. }
    destruct (lin_is_const e) eqn:Ec.
    - inversion Hx; subst; clear Hx.
      eapply (GOAL A (lc e)); [apply aext_refl|exact HL| |left; rewrite !wrap64_zwrap; reflexivity].
      rewrite Hua, (eval_is_const nu e Ec). reflexivity.
    - destruct (enum_values A e) as [ts|] eqn:Een; [|discriminate].
      destruct (qwithin A e 0 M64) eqn:Eq; [|discriminate]. cbn [negb] in Hx. inversion Hx; subst; clear Hx.
      pose proof (qwithin_sound A nu e 0 M64 HL Eq) as Hr. unfold M64 in Hr.
      pose proof (enum_values_sound A nu e ts HL Een ltac:(lia)) as Hin.
      pose proof (assume_eq_sound A nu e (eval nu e) HL eq_refl Ba) as (F&L&X).
      destruct (assume_eq A e (eval nu e)) as [ok A1] eqn:Eas. cbn [fst snd] in F, L, X. subst ok.
      eapply (GOAL A1 (eval nu e)); [exact X|exact L|exact Hua|].
      apply in_flat_map. exists (eval nu e). split; [exact Hin|]. rewrite Eas.
      rewrite (zwrap_id 64 (eval nu e)) by lia. left. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition is_mem_instr (i : instr) : bool :=
    match i with Load _ _ _ _ _ | Store _ _ _ _ => true | _ => false end.

  Theorem vstep_core_sound_nomem xl xs A nu regs mem pc rom w i succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    is_mem_instr i = false ->
    vstep_core xl xs A i = VR_next succs ->
    step_post A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hm Hx.
    destruct i; try discriminate; cbn [vstep_core] in Hx.
    - eapply x_lui_sound; eauto.
    - eapply x_auipc_sound; eauto.
    - eapply x_jal_sound; eauto.
    - eapply x_jalr_sound; eauto.
    - rewrite ?bvs_eq in Hx. eapply x_branch_sound; eauto.
    - rewrite ?bvs_eq in Hx. eapply x_opimm_sound; eauto.
    - eapply x_shiftimm64_sound; eauto.
    - eapply x_op_sound; eauto.
    - rewrite ?bvs_eq in Hx. eapply x_opimm32_sound; eauto.
    - eapply x_shiftimm32_sound; eauto.
    - eapply x_op32_sound; eauto.
    - eapply x_mul_sound; eauto.
    - eapply x_mul32_sound; eauto.
  Qed.
End Sound.
