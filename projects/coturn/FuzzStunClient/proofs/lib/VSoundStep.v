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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VStep VStepMem VStepSound VStepMemSound VCert VItab VDriverMatch VContract VDriver VSoundMatch VSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Section Step.
  Variable SEGS : list Segment.
  Variable G : genv.
  Variable rom : word -> option byte.
  Variable done : list vunit.
  Variable U : vunit.
  Variable E : venv.
  Variable mem0 : word -> option byte.

  Let D := mk_denv G done U.
  Let P := unit_params G U.

  Notation gammaP := (gamma SEGS P E mem0).

  Hypothesis ITAB : itab_ok SEGS (ge_itab G).
  Hypothesis RET : ret_ok (wordZ (unit_ret U E)).
  Hypothesis STATIC : unit_static_ok G P U = None.

  (* [comment removed for export] *)
  Hypothesis VSTEP : forall A i succs nu regs mem (pc : word) w,
    vstep P A i = VR_next succs ->
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    step_post SEGS P E mem0 A nu succs regs mem pc rom.

  (* [comment removed for export] *)
  Hypothesis CONTRACT : forall A c (rd : reg) (imm : bv 21) succs nu regs mem (pc : word) w,
    do_contract D A c (rz rd) (npc_of A) = SN succs ->
    (if Z.ltb 0 (wrap64 (vs_pc A + bv_signed imm))
     then pm_get (zkey (wrap64 (vs_pc A + bv_signed imm))) (ge_ctab G) else None) = Some c ->
    (JOIN0 <= vs_next A)%positive ->
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4) ->
    dstep_post SEGS G rom U E mem0 A succs nu regs pc mem.

  Hypothesis CALL : forall A (rd : reg) (imm : bv 21) vs succs nu regs mem (pc : word) w,
    do_call D A (wrap64 (vs_pc A + bv_signed imm)) (npc_of A) vs = SN succs ->
    vs <> [] -> vs = call_variants D (vs_pc A) (wrap64 (vs_pc A + bv_signed imm)) ->
    rz rd = 1 ->
    (JOIN0 <= vs_next A)%positive ->
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4) ->
    dstep_post SEGS G rom U E mem0 A succs nu regs pc mem.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma gamma_set_ctx A c nu regs mem : gammaP A nu regs mem -> gammaP (set_ctx A c) nu regs mem.
  Proof. intros H. exact H. Qed.

  Lemma step_post_dstep A nu succs regs mem pc :
    step_post SEGS P E mem0 A nu succs regs mem pc rom ->
    dstep_post SEGS G rom U E mem0 A succs nu regs pc mem.
  Proof.
    intros (regs' & pc' & mem' & A' & nu' & Hst & Hin & Hpc & Hext & Hle & Hfm & HG).
    left. exists regs', pc', mem', A', nu'. split; [eapply msteps_one; [reflexivity|exact Hst]|].
    split; [exact Hin|]. split; [exact Hpc|]. split; [exact Hext|]. split; [exact Hle|]. split; [exact Hfm|exact HG].
  Qed.

  Lemma lift_sound A i succs nu regs mem (pc : word) w :
    lift (vstep P A i) = SN succs ->
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    dstep_post SEGS G rom U E mem0 A succs nu regs pc mem.
  Proof.
    unfold lift. destruct (vstep P A i) as [l|m] eqn:Ev; [|discriminate]. intros X; inversion X; subst.
    intros. apply step_post_dstep. eapply VSTEP; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma single_ctx_sound A i A' c nu regs mem (pc : word) w :
    vstep P A i = VR_next [A'] ->
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    dstep_post SEGS G rom U E mem0 A [set_ctx A' c] nu regs pc mem.
  Proof.
    intros Ev HG Hpc Hf He Hd.
    destruct (VSTEP _ _ _ _ _ _ _ _ Ev HG Hpc Hf He Hd) as (regs' & pc' & mem' & A'' & nu' & Hst & Hin & Hpc' & Hext & Hle & Hfm & HG').
    destruct Hin as [<-|[]].
    left. exists regs', pc', mem', (set_ctx A' c), nu'. split; [eapply msteps_one; [reflexivity|exact Hst]|].
    split; [now left|]. split; [exact Hpc'|]. split; [exact Hext|]. split; [exact Hle|]. split; [exact Hfm|].
    apply gamma_set_ctx. exact HG'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma try_exits_none A : forall l k msgs,
    try_exits l A k msgs = None ->
    exists X sigma, In X l /\ match_state isv_join no_skip false pm_empty (load_cstate X (vs_pc A) []) A = MOk sigma.
  Proof.
    induction l as [|X t IH]; simpl; intros k msgs H; [discriminate|].
    destruct (match_state isv_join no_skip false pm_empty (load_cstate X (vs_pc A) []) A) as [sigma|m] eqn:M.
    - exists X, sigma. auto.
    - destruct (IH _ _ H) as (X' & sigma & Hin & M'). exists X', sigma. auto.
  Qed.

  Lemma Z_to_bv_zwrap z : Z_to_bv 64 (zwrap 64 z) = (Z_to_bv 64 z : word).
  Proof.
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold zwrap, bv_wrap, bv_modulus.
    rewrite Z.mod_mod; [reflexivity|]. apply Z.pow_nonzero; lia.
  Qed.

  Lemma ra_is_exit_sound A nu regs mem v :
    gammaP A nu regs mem -> get_reg A 1 = v -> ra_is_exit U v = true ->
    getr regs 1%bv = wordZ (unit_ret U E).
  Proof.
    intros HG Hv Hx. pose proof HG as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HGl&HN&HB).
    unfold ra_is_exit in Hx. unfold get_reg in Hv. simpl in Hv.
    assert (R1 : forall e, pm_get 1%positive (vs_regs A) = Some e -> bv_unsigned (getr regs 1%bv) = zwrap 64 (eval nu e)).
    { intros e He. apply (HR 1%bv e); [discriminate|exact He]. }
    rewrite <- (wordZ_u (getr regs 1%bv)). unfold unit_ret.
    destruct (u_root U) as [c|] eqn:Er; destruct v as [e|]; try discriminate; simpl in Hx;
      apply lin_eqb_eq in Hx; subst e; rewrite (R1 _ Hv).
    - rewrite eval_lconst. unfold wordZ. apply Z_to_bv_zwrap.
    - rewrite eval_lsym. rewrite (HF RA (e_ra E)) by reflexivity. unfold wordZ. apply Z_to_bv_zwrap.
  Qed.

  Lemma absval_eqb_reg A nu regs mem (r : reg) e :
    gammaP A nu regs mem -> rz r <> 0 -> absval_eqb (get_reg A (rz r)) e = true ->
    bv_unsigned (getr regs r) = zwrap 64 (eval nu e).
  Proof.
    intros HG Hr Hb. pose proof HG as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HGl&HN&HB).
    unfold absval_eqb, get_reg in Hb. destruct (Z.eqb_spec (rz r) 0); [lia|].
    destruct (pm_get (reg_key (rz r)) (vs_regs A)) as [e'|] eqn:G0; [|discriminate].
    apply lin_eqb_eq in Hb. subst e'. apply HR; auto.
  Qed.

  Lemma sregs_intact_sound A nu regs mem :
    gammaP A nu regs mem -> sregs_intact A = true ->
    forall r i, In (r, i) sreg_idx -> bv_unsigned (getr regs (Z_to_bv 5 r)) = zwrap 64 (nu (SREG i)).
  Proof.
    intros HG Hs r i Hin. unfold sregs_intact in Hs. rewrite forallb_forall in Hs.
    specialize (Hs _ Hin). simpl in Hs.
    rewrite <- (eval_lsym nu (SREG i)).
    assert (Hr : rz (Z_to_bv 5 r) = r).
    { unfold sreg_idx in Hin. simpl in Hin.
      repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; reflexivity|]). destruct Hin. }
    apply (absval_eqb_reg A nu regs mem (Z_to_bv 5 r)); auto; rewrite Hr; [|exact Hs].
    unfold sreg_idx in Hin. simpl in Hin.
    repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; lia|]). destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma unit_exit_exit A succs nu regs mem :
    unit_exit D A = SN succs ->
    ra_is_exit U (get_reg A 1) = true ->
    gammaP A nu regs mem ->
    succs = []
    /\ getr regs 1%bv = wordZ (unit_ret U E)
    /\ exit_regs G U nu regs
    /\ exists X nu'', In X (u_exits U)
         /\ gamma SEGS P E mem0 (load_cstate X (unit_ret U E) []) nu'' regs mem
         /\ ext JOIN0 nu nu''.
  Proof.
    intros Hx Hra HG.
    pose proof (ra_is_exit_sound _ _ _ _ _ HG eq_refl Hra) as R1.
    unfold unit_exit in Hx. change (de_U D) with U in Hx. change (de_G D) with G in Hx.
    destruct (absval_eqb (get_reg A 2) (lsymc SP0 (u_sp U))) eqn:Esp; [|discriminate].
    destruct (sregs_intact A) eqn:Esr; [|discriminate].
    destruct (absval_eqb (get_reg A 3) (lsym GP)) eqn:Egp; [|discriminate].
    destruct (absval_eqb (get_reg A 4) (lconst (ge_tp G))) eqn:Etp; [|discriminate].
    simpl in Hx.
    match type of Hx with (if ?b then _ else _) = _ => destruct b; [discriminate|] end.
    destruct (try_exits (u_exits U) A 0 []) as [msgs|] eqn:T; [discriminate|].
    inversion Hx; subst succs.
    destruct (try_exits_none _ _ _ _ T) as (X & sigma & HinX & M).
    assert (HX : cstate_ok P X = true).
    { unfold unit_static_ok in STATIC.
      destruct (cstate_ok P (u_pre U)); [|discriminate].
      destruct (pre_canonical G U); [|discriminate].
      destruct (forallb (fun c => pc_ok (cut_pc c) && forallb (cstate_ok P) (cut_states c)) (u_cuts U)); [|discriminate].
      destruct (pc_ok (u_entry U)); [|discriminate].
      destruct (forallb (cstate_ok P) (u_exits U)) eqn:EX; [|discriminate].
      rewrite forallb_forall in EX. apply EX. exact HinX. }
    destruct (gamma_stored SEGS G U E mem0 A X (vs_pc A) [] sigma nu regs mem HG HX M) as [HG' EXT].
    split; [reflexivity|]. split; [exact R1|]. split.
    - split; [|split; [|split]].
      + rewrite (absval_eqb_reg A nu regs mem 2%bv _ HG ltac:(discriminate) Esp). rewrite eval_lsymc. reflexivity.
      + rewrite (absval_eqb_reg A nu regs mem 3%bv _ HG ltac:(discriminate) Egp). rewrite eval_lsym. reflexivity.
      + rewrite (absval_eqb_reg A nu regs mem 4%bv _ HG ltac:(discriminate) Etp). rewrite eval_lconst. reflexivity.
      + eapply sregs_intact_sound; eauto.
    - exists X, (vsubst nu sigma). split; [exact HinX|]. split; [exact HG'|exact EXT].
  Qed.

  Lemma unit_exit_sound A succs nu regs mem (pc : word) w (imm : bv 12) :
    unit_exit D A = SN succs ->
    ra_is_exit U (get_reg A 1) = true ->
    bv_signed imm = 0 ->
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Jalr 0%bv 1%bv imm, 4) ->
    dstep_post SEGS G rom U E mem0 A succs nu regs pc mem.
  Proof.
    intros Hx Hra Himm HG Hpc Hf He Hd.
    destruct (unit_exit_exit _ _ _ _ _ Hx Hra HG) as (-> & R1 & XR & X & nu'' & HinX & HG' & EXT).
    right. exists regs, mem. split.
    - eapply msteps_one; [reflexivity|].
      rewrite (step_jalr_gen SEGS regs pc mem rom w 0%bv 1%bv imm Hf He Hd).
      simpl. rewrite Himm, R1.
      change (jalr_tgt (wordZ (unit_ret U E)) 0) with (v_jalr (wordZ (unit_ret U E)) 0).
      rewrite RET. reflexivity.
    - exists X, nu''. split; [exact HinX|]. split; [exact HG'|]. split; [exact EXT|].
      split; [exact R1|]. split; [exact XR|apply frame_mod_refl].
  Qed.

  Lemma pop_ctx_sound A i succs nu regs mem (pc : word) w :
    pop_ctx P A i = SN succs ->
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    dstep_post SEGS G rom U E mem0 A succs nu regs pc mem.
  Proof.
    unfold pop_ctx. destruct (vs_ctx A) as [|c rest]; [discriminate|].
    destruct (vstep P A i) as [[|A' [|? ?]]|m] eqn:Ev; try discriminate.
    destruct (Z.eqb (vs_pc A') c); [|discriminate]. intros X; inversion X; subst.
    intros. eapply single_ctx_sound; eauto.
  Qed.

  Lemma rz_is0 (r : reg) : Z.eqb (rz r) 0 = true -> r = 0%bv.
  Proof. intros H. apply Z.eqb_eq in H. unfold rz in H. apply bv_eq. rewrite H. reflexivity. Qed.
  Lemma rz_is1 (r : reg) : Z.eqb (rz r) 1 = true -> r = 1%bv.
  Proof. intros H. apply Z.eqb_eq in H. unfold rz in H. apply bv_eq. rewrite H. reflexivity. Qed.

  Theorem dstep_sound A succs nu regs (pc : word) mem :
    dstep D A = SN succs -> (JOIN0 <= vs_next A)%positive -> vs_pc A = bv_unsigned pc ->
    gammaP A nu regs mem -> dstep_post SEGS G rom U E mem0 A succs nu regs pc mem.
  Proof.
    intros Hx HJ Hpc HG. unfold dstep in Hx.
    change (de_G D) with G in Hx. change (de_P D) with P in Hx.
    destruct (itab_get (ge_itab G) (vs_pc A)) as [i|] eqn:IT; [|discriminate].
    destruct (ITAB _ _ IT) as (w & Hf & He & Hd).
    rewrite Hpc, Z_to_bv_bv_unsigned in Hf.
    destruct i; try (eapply lift_sound; eauto; fail).
    - (* [comment removed for export] *)
      destruct (if Z.ltb 0 (wrap64 (vs_pc A + bv_signed imm))
                then pm_get (zkey (wrap64 (vs_pc A + bv_signed imm))) (ge_ctab G) else None) as [c|] eqn:CT.
      + eapply CONTRACT; eauto.
      + destruct (Z.eqb (rz rd) 1) eqn:R1.
        * destruct (call_variants D (vs_pc A) (wrap64 (vs_pc A + bv_signed imm))) as [|v vs] eqn:CV.
          -- destruct (vstep P A (Jal rd imm)) as [[|A' [|? ?]]|m] eqn:Ev; try discriminate.
             inversion Hx; subst. eapply single_ctx_sound; eauto.
          -- eapply (CALL A rd imm (v :: vs)); [exact Hx|discriminate|symmetry; exact CV|apply Z.eqb_eq; exact R1
                                                |exact HJ|exact HG|exact Hpc|exact Hf|exact He|exact Hd].
        * destruct (Z.eqb (rz rd) 0); [|discriminate]. eapply lift_sound; eauto.
    - (* [comment removed for export] *)
      destruct (Z.eqb (rz rd) 0 && Z.eqb (rz rs1) 1 && Z.eqb (bv_signed imm) 0) eqn:RT.
      + apply andb_prop in RT as [RT Himm]. apply andb_prop in RT as [Hrd Hrs1].
        pose proof (rz_is0 _ Hrd) as ->. pose proof (rz_is1 _ Hrs1) as ->. apply Z.eqb_eq in Himm.
        unfold do_ret in Hx. change (de_U D) with U in Hx. change (de_P D) with P in Hx.
        destruct (ra_is_exit U (get_reg A 1)) eqn:RX.
        * destruct (vs_ctx A); [|discriminate].
          eapply unit_exit_sound; eauto.
        * destruct (get_reg A 1) as [e|]; [|discriminate].
          destruct (lin_is_const e); [|discriminate].
          eapply pop_ctx_sound; eauto.
      + eapply lift_sound; eauto.
  Qed.

End Step.
