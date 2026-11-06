(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VCert VItab VDriverMatch VContract VDriver VSoundMatch VSound VSoundStep VSoundCall VSoundCall2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section Iface.
  Variable SEGS : list Segment.
  Variable P : vparams.
  Variable E : venv.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.

  Definition contract_post (c : contract) (tgt : Z) : Prop :=
    forall A spoff A1 v nu regs mem (ra : word),
      contract_apply P CI c A spoff = CROk A1 v ->
      gamma SEGS P E mem0 A nu regs mem ->
      get_reg A 2 = Some (lsymc SP0 spoff) ->
      (contract_K c = 0 \/ in_ranges (vp_wstack P) (spoff - contract_K c) (contract_K c) = true) ->
      ret_ok ra -> getr regs 1%bv = ra ->
      exists regs' mem' nu',
           msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra mem' rom)
        /\ gamma SEGS P E mem0 (contract_frame c A1 spoff v) nu' regs' mem'
        /\ getr regs' 1%bv = ra
        /\ ext (vs_next A) nu nu' /\ (vs_next A <= vs_next (contract_frame c A1 spoff v))%positive
        /\ frame_mod mem mem' (unit_regions P E).

  Definition contract_dead (c : contract) : Prop :=
    forall A spoff nu regs mem,
      contract_apply P CI c A spoff = CRDead -> gamma SEGS P E mem0 A nu regs mem -> False.

  Definition ctab_sound (ctab : pmap contract) : Prop :=
    forall tgt c, 0 < tgt -> pm_get (zkey tgt) ctab = Some c -> contract_post c tgt /\ contract_dead c.
End Iface.

Section Contract.
  Variable SEGS : list Segment.
  Variable G : genv.
  Variable rom : word -> option byte.
  Variable done : list vunit.
  Variable U : vunit.
  Variable E : venv.
  Variable mem0 : word -> option byte.

  Let D := mk_denv G done U.
  Let P := unit_params G U.
  Local Notation gammaP := (gamma SEGS P E mem0).

  Hypothesis CTAB : ctab_sound SEGS P E mem0 rom (ge_CI G) (ge_ctab G).
  Hypothesis RET : ret_ok (wordZ (unit_ret U E)).
  Hypothesis STATIC : unit_static_ok G P U = None.
  Hypothesis VSTEP : forall A i succs nu regs mem (pc : word) w,
    vstep P A i = VR_next succs ->
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    step_post SEGS P E mem0 A nu succs regs mem pc rom.

  Lemma sp_offset_get A spoff : sp_offset A = Some spoff -> get_reg A 2 = Some (lsymc SP0 spoff).
  Proof.
    unfold sp_offset. destruct (get_reg A 2) as [e|]; [|discriminate].
    destruct e as [c [|[s k] [|? ?]]]; cbn [lt lc]; try discriminate.
    destruct (Pos.eqb_spec s SP0); [|discriminate]. destruct (Z.eqb_spec k 1); [|discriminate].
    cbn. intros X; injection X as <-. subst. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma gamma_set_reg1 A2 nu' regs' mem' (v : absval) :
    gammaP A2 nu' regs' mem' ->
    (forall e, v = Some e -> bv_unsigned (getr regs' 1%bv) = zwrap 64 (eval nu' e) /\ lin_below e (vs_next A2) = true) ->
    gammaP (set_reg A2 1 v) nu' regs' mem'.
  Proof.
    intros HG2 Hv.
    pose proof HG2 as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HGl&HN&HB). destruct HB as (B0&B1&B2&B3&B4&B5).
    unfold set_reg. cbn [Z.eqb].
    split; [exact HE|]. split; [exact HM|]. split; [exact HF|]. split; [exact HS|]. split; [exact HC|].
    split; [exact HMo|]. split; [exact HV|]. split.
    { intros r e' Hr0 Hg. cbn [vs_regs set_regs] in Hg.
      destruct (Pos.eqb_spec (reg_key (bv_unsigned r)) (reg_key 1)) as [Ek|Nk].
      - assert (r = 1%bv) by (apply (reg_key_inj 1%bv r); unfold rz; auto; discriminate). subst r.
        destruct v as [e|].
        + rewrite pm_get_set_same in Hg. injection Hg as <-. exact (proj1 (Hv e eq_refl)).
        + rewrite pm_get_remove_same in Hg. discriminate.
      - destruct v as [e|].
        + rewrite pm_get_set_other in Hg by (intros X; apply Nk; symmetry; exact X). apply HR; auto.
        + rewrite pm_get_remove_other in Hg by (intros X; apply Nk; symmetry; exact X). apply HR; auto. }
    split; [exact HSl|]. split; [exact HGl|]. split; [exact HN|].
    split; [exact B0|]. split; [exact B1|]. split; [|split; [exact B3|split; [exact B4|exact B5]]].
    intros r e' Hg. cbn [vs_regs vs_next set_regs] in Hg |- *.
    destruct (Pos.eqb_spec r (reg_key 1)) as [->|Nk].
    + destruct v as [e|]; [rewrite pm_get_set_same in Hg; injection Hg as <-; exact (proj2 (Hv e eq_refl))| rewrite pm_get_remove_same in Hg; discriminate].
    + destruct v; [rewrite pm_get_set_other in Hg by (intros X; apply Nk; symmetry; exact X)| rewrite pm_get_remove_other in Hg by (intros X; apply Nk; symmetry; exact X)]; exact (B2 _ _ Hg).
  Qed.

  Lemma gamma_to_set_pc X p nu regs mem : gammaP X nu regs mem -> gammaP (set_pc X p) nu regs mem.
  Proof. intros H. destruct X. exact H. Qed.

  Lemma get_reg_set_reg_same A r v : 0 < r -> get_reg (set_reg A r v) r = v.
  Proof.
    intros Hr. unfold get_reg, set_reg. destruct (Z.eqb_spec r 0); [lia|]. simpl.
    destruct v; [now rewrite pm_get_set_same|now rewrite pm_get_remove_same].
  Qed.

  Lemma zwrap64_mod2 x : zwrap 64 x mod 2 = x mod 2.
  Proof. unfold zwrap. apply Z.mod_mod_divide. exists (2 ^ 63). reflexivity. Qed.

  Theorem contract_sound A c (rd : reg) (imm : bv 21) succs nu regs mem (pc : word) w :
    do_contract D A c (rz rd) (npc_of A) = SN succs ->
    (if Z.ltb 0 (wrap64 (vs_pc A + bv_signed imm))
     then pm_get (zkey (wrap64 (vs_pc A + bv_signed imm))) (ge_ctab G) else None) = Some c ->
    (JOIN0 <= vs_next A)%positive ->
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4) ->
    dstep_post SEGS G rom U E mem0 A succs nu regs pc mem.
  Proof.
    intros Hx Hct HJ HG Hpc Hf He Hd.
    set (tgt := wrap64 (vs_pc A + bv_signed imm)) in *. set (npc := npc_of A) in *.
    destruct (Z.ltb_spec 0 tgt) as [Htgt|]; [|discriminate].
    destruct (CTAB tgt c Htgt Hct) as [POST DEAD].
    unfold do_contract in Hx. change (de_P D) with P in Hx. change (de_G D) with G in Hx. change (de_U D) with U in Hx.
    destruct (Z.eqb (rz rd) 0 || Z.eqb (rz rd) 1) eqn:RD; [|discriminate]. cbn [negb] in Hx.
    set (tail := Z.eqb (rz rd) 0) in *.
    set (A' := if tail then A else set_reg A 1 (Some (lconst npc))) in *.
    destruct (sp_offset A') as [spoff|] eqn:SPO; [|discriminate].
    destruct (negb (Z.eqb (contract_K c) 0) && negb (in_ranges (vp_wstack P) (spoff - contract_K c) (contract_K c))) eqn:KW; [discriminate|].
    assert (KW' : contract_K c = 0 \/ in_ranges (vp_wstack P) (spoff - contract_K c) (contract_K c) = true).
    { destruct (Z.eqb_spec (contract_K c) 0); [now left|]. right. cbn [negb andb] in KW. destruct (in_ranges _ _ _); [reflexivity|discriminate]. }
    assert (NPC : 0 <= npc < 2 ^ 64) by (unfold npc, npc_of; rewrite wrap64_zwrap; apply zwrap64_range).
    (* [comment removed for export] *)
    assert (Ej : vstep P A (Jal rd imm) = VR_next [set_pc (set_reg A (rz rd) (Some (lconst npc))) tgt]) by reflexivity.
    destruct (VSTEP _ _ _ _ _ _ _ _ Ej HG Hpc Hf He Hd) as (regs1 & pc1 & mem1 & A1j & nu1 & Hst & Hin1 & Hpc1 & X1 & L1 & FM1 & HG1).
    destruct Hin1 as [<-|[]]. cbn [vs_pc set_pc] in Hpc1. apply gamma_set_pc in HG1.
    assert (HG1' : gammaP A' nu1 regs1 mem1 /\ vs_next A' = vs_next A).
    { unfold A', tail. destruct (Z.eqb_spec (rz rd) 0) as [R0|R0].
      - rewrite R0 in HG1. unfold set_reg in HG1. cbn [Z.eqb] in HG1. split; [exact HG1|reflexivity].
      - apply Bool.orb_prop in RD as [RD|RD]; [unfold tail in RD; first [discriminate | apply Z.eqb_eq in RD; lia]|]. apply Z.eqb_eq in RD. rewrite RD in HG1.
        split; [exact HG1|apply vs_next_set_reg]. }
    destruct HG1' as [HG1' NX'].
    destruct (contract_apply P (ge_CI G) c A' spoff) as [A1 v| |m] eqn:CA; [|exfalso; exact (DEAD _ _ _ _ _ CA HG1')|discriminate].
    set (A2 := contract_frame c A1 spoff v) in *.
    assert (GR1 : forall e, get_reg A' 1 = Some e -> bv_unsigned (getr regs1 1%bv) = zwrap 64 (eval nu1 e) /\ lin_below e (vs_next A') = true).
    { intros e He1. pose proof HG1' as (_&_&_&_&_&_&_&HR1&_&_&_&HB1). destruct HB1 as (_&_&RB1&_).
      unfold get_reg in He1. cbn [Z.eqb] in He1. split; [apply (HR1 1%bv e); [discriminate|exact He1]|exact (RB1 _ _ He1)]. }
    (* [comment removed for export] *)
    assert (MAIN : forall ra, getr regs1 1%bv = ra -> ret_ok ra ->
              exists regs' mem' nu',
                   msteps SEGS (mkst regs pc mem rom) (mkst regs' ra mem' rom)
                /\ gammaP (set_reg A2 1 (get_reg A' 1)) nu' regs' mem'
                /\ getr regs' 1%bv = ra
                /\ ext (vs_next A) nu nu' /\ (vs_next A <= vs_next (set_reg A2 1 (get_reg A' 1)))%positive
                /\ frame_mod mem mem' (unit_regions P E)).
    { intros ra Hra Hok.
      destruct (POST A' spoff A1 v nu1 regs1 mem1 ra CA HG1' (sp_offset_get _ _ SPO) KW' Hok Hra)
        as (regs' & mem' & nu' & Hrun & HG2 & Hra' & X2 & L2 & FM2).
      exists regs', mem', nu'. split.
      { eapply msteps_trans; [eapply msteps_one; [reflexivity|exact Hst]|].
        replace pc1 with (wordZ tgt); [exact Hrun|]. rewrite <- (wordZ_u pc1), <- Hpc1. reflexivity. }
      split.
      { apply (gamma_set_reg1 A2 nu' regs' mem' (get_reg A' 1) HG2). intros e Hge. destruct (GR1 e Hge) as [Q1 Q2]. split.
        - rewrite Hra', <- Hra, Q1. f_equal. symmetry. exact (eval_ext_below _ _ _ _ X2 Q2).
        - eapply lin_below_mono; [exact L2|exact Q2]. }
      split; [exact Hra'|]. split; [|split].
      - eapply (ext_trans (vs_next A) (vs_next A)); [lia|exact X1|]. rewrite <- NX'. exact X2.
      - rewrite vs_next_set_reg. rewrite <- NX'. exact L2.
      - eapply frame_mod_trans_same; [exact FM1|exact FM2]. }
    unfold after_return in Hx. change (de_U D) with U in Hx.
    unfold tail in *. destruct (Z.eqb_spec (rz rd) 0) as [R0|R0].
    - (* [comment removed for export] *)
      cbn [negb] in Hx.
      pose proof (rz_is0 rd ltac:(apply Z.eqb_eq; exact R0)) as Erd.
      assert (Eregs : regs1 = regs /\ mem1 = mem).
      { rewrite Erd in Hd. pose proof (step_jal_x0 SEGS regs pc mem rom w imm Hf He Hd) as Hst'.
        rewrite Hst in Hst'. inversion Hst'. auto. }
      destruct Eregs as [-> ->].
      rewrite get_reg_set_reg_same in Hx by lia.
      destruct (ra_is_exit U (get_reg A' 1)) eqn:RX.
      + (* [comment removed for export] *)
        destruct (vs_ctx _); [|discriminate].
        assert (R1 : getr regs 1%bv = wordZ (unit_ret U E)).
        { eapply (ra_is_exit_sound SEGS G U E mem0 A'); [exact HG1'|reflexivity|exact RX]. }
        destruct (MAIN _ R1 RET) as (regs' & mem' & nu' & Hrun & HG3 & Hra' & X3 & L3 & FM3).
        destruct (unit_exit_exit SEGS G done U E mem0 STATIC _ _ _ _ _ Hx ltac:(rewrite get_reg_set_reg_same by lia; exact RX) HG3)
          as (-> & _ & XR & X & nu'' & HinX & HGX & EXT).
        right. exists regs', mem'. split; [exact Hrun|].
        exists X, nu''. split; [exact HinX|]. split; [exact HGX|]. split.
        { eapply (ext_trans JOIN0 JOIN0); [lia|eapply ext_mono; [exact HJ|exact X3]|exact EXT]. }
        split; [exact Hra'|]. split; [|exact FM3].
        eapply exit_regs_ext; [eapply ext_mono; [exact HJ|exact X3]|exact XR].
      + (* [comment removed for export] *)
        destruct (get_reg A' 1) as [e|] eqn:G1; [|discriminate].
        destruct (lin_is_const e) eqn:Hc; [|discriminate].
        destruct (Z.eqb (lc e mod 2) 0 && Z.leb 0 (lc e) && Z.ltb (lc e) (2 ^ 64)) eqn:CK; [|discriminate]. cbn [negb] in Hx.
        apply andb_prop in CK as [CK C3]. apply andb_prop in CK as [C1 C2].
        apply Z.eqb_eq in C1. apply Z.leb_le in C2. apply Z.ltb_lt in C3.
        destruct (vs_ctx _) as [|c' rest] eqn:CTX; [discriminate|].
        destruct (Z.eqb_spec c' (lc e)); [|discriminate]. inversion Hx; subst succs. subst c'.
        assert (R1 : getr regs 1%bv = wordZ (lc e)).
        { destruct (GR1 e eq_refl) as [R1 _]. rewrite (eval_is_const _ _ Hc) in R1. rewrite zwrap64_id in R1 by lia.
          rewrite <- (wordZ_u (getr regs 1%bv)). now rewrite R1. }
        assert (ROK : ret_ok (wordZ (lc e))) by (apply ret_ok_even; rewrite u_wordZ by lia; exact C1).
        destruct (MAIN _ R1 ROK) as (regs' & mem' & nu' & Hrun & HG3 & Hra' & X3 & L3 & FM3).
        left. exists regs', (wordZ (lc e)), mem', (set_ctx (set_pc (set_reg A2 1 (Some e)) (lc e)) rest), nu'.
        split; [exact Hrun|]. split; [now left|]. split; [cbn; rewrite u_wordZ by lia; reflexivity|].
        split; [exact X3|]. split; [first [exact L3 | rewrite G1 in L3; exact L3]|]. split; [exact FM3|].
        apply gamma_set_ctx. apply gamma_to_set_pc. first [exact HG3 | rewrite G1 in HG3; exact HG3].
    - (* [comment removed for export] *)
      cbn [negb] in Hx. inversion Hx; subst succs.
      assert (G1 : get_reg A' 1 = Some (lconst npc)).
      { unfold A'. apply get_reg_set_reg_same. lia. }
      assert (R1 : getr regs1 1%bv = wordZ npc).
      { destruct (GR1 _ G1) as [R1 _]. rewrite eval_lconst, zwrap64_id in R1 by lia.
        rewrite <- (wordZ_u (getr regs1 1%bv)). now rewrite R1. }
      assert (ROK : ret_ok (wordZ npc)).
      { apply ret_ok_even. rewrite u_wordZ by lia. unfold npc, npc_of. rewrite wrap64_zwrap, zwrap64_mod2.
        pose proof (fetch_word_even SEGS pc w Hf) as Ev. rewrite <- Hpc in Ev.
        replace (vs_pc A + 4) with (vs_pc A + 2 * 2) by lia. rewrite Z_mod_plus_full. exact Ev. }
      destruct (MAIN _ R1 ROK) as (regs' & mem' & nu' & Hrun & HG3 & Hra' & X3 & L3 & FM3).
      left. exists regs', (wordZ npc), mem', (set_pc (set_reg A2 1 (get_reg A' 1)) npc), nu'.
      split; [exact Hrun|]. split; [now left|]. split; [cbn; rewrite u_wordZ by lia; reflexivity|].
      split; [exact X3|]. split; [exact L3|]. split; [exact FM3|].
      apply gamma_to_set_pc. exact HG3.
  Qed.
End Contract.
