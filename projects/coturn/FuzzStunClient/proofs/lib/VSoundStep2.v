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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VStep VStepMem VStepSound VStepMemSound VCert VItab VDriverMatch VContract VDriver VSoundMatch VSound VSoundStep VState2 VStepMem2 VCert2 VContract2 VDriverMatch2 VDriver2 VGamma2 VSound2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition genv1_of (G : genv2) : genv :=
  mkGE (p1 (ge2_P0 G)) (ge2_itab G) pm_empty (ge2_CI G) (ge2_tp G) (ge2_prng G) (ge2_ranks G).

Lemma unit_params2_p1 G U : p1 (unit_params2 G U) = unit_params (genv1_of G) (u1 U).
Proof. reflexivity. Qed.

Section Step2.
  Variable SEGS : list Segment.
  Variable G : genv2.
  Variable rom : word -> option byte.
  Variable done : list vunit2.
  Variable U : vunit2.
  Variable E : venv2.
  Variables mem0 mem_e : word -> option byte.

  Let D := mk_denv2 G done U.
  Let P := unit_params2 G U.
  Let G1 := genv1_of G.

  Local Notation gammaP := (gamma2 SEGS P E mem0).
  Local Notation gammaPE := (gammaE SEGS G U E mem0 mem_e).

  Hypothesis ITAB : itab_ok SEGS (ge2_itab G).
  Hypothesis RET : ret_ok (wordZ (unit_ret2 U E)).
  Hypothesis STATIC : unit_static_ok2 G P U = None.

  Hypothesis VSTEP2 : forall A i succs nu regs mem (pc : word) w,
    vstep2 P A i = VR2_next succs ->
    gammaP A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.

  Hypothesis CONTRACT2 : forall A c (rd : reg) (imm : bv 21) succs nu regs mem (pc : word) w,
    do_contract2 D A c (rz rd) (npc_of (v1 A)) = SN2 succs ->
    (if Z.ltb 0 (wrap64 (vs2_pc A + bv_signed imm))
     then pm_get (zkey (wrap64 (vs2_pc A + bv_signed imm))) (ge2_ctab G) else None) = Some c ->
    (FIRST_FRESH2 <= vs2_next A)%positive ->
    gammaPE A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4) ->
    dstep_post2 SEGS G rom U E mem0 mem_e A succs nu regs pc mem.

  Hypothesis CALL2 : forall A (rd : reg) (imm : bv 21) vs succs nu regs mem (pc : word) w,
    do_call2 D A (wrap64 (vs2_pc A + bv_signed imm)) (npc_of (v1 A)) vs = SN2 succs ->
    vs <> [] -> vs = call_variants2 D (vs2_pc A) (wrap64 (vs2_pc A + bv_signed imm)) ->
    rz rd = 1 ->
    (FIRST_FRESH2 <= vs2_next A)%positive ->
    gammaPE A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4) ->
    dstep_post2 SEGS G rom U E mem0 mem_e A succs nu regs pc mem.

  (* [comment removed for export] *)
  Hypothesis MATCH : forall A X pc ctx sigma nu regs mem,
    gammaP A nu regs mem ->
    cstate2_ok P X = true ->
    match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 P X pc ctx) A = MOk sigma ->
    gammaP (load_cstate2 P X pc ctx) (vsubst nu sigma) regs mem /\ ext FIRST_FRESH2 nu (vsubst nu sigma)
    /\ (forall a, In a (own_flags (load_cstate2 P X pc ctx) (vsubst nu sigma)) <-> In a (own_flags A nu)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma gammaE_set_ctx2 A c nu regs mem : gammaPE A nu regs mem -> gammaPE (set_ctx2 A c) nu regs mem.
  Proof. intros H. destruct A as [A1 rg lv dd]. destruct A1. exact H. Qed.

  Lemma gammaE_set_pc2 A p nu regs mem : gammaPE A nu regs mem -> gammaPE (set_pc2 A p) nu regs mem.
  Proof. intros H. destruct A as [A1 rg lv dd]. destruct A1. exact H. Qed.

  Lemma own_flags_set_ctx2 A c nu : own_flags (set_ctx2 A c) nu = own_flags A nu.
  Proof. reflexivity. Qed.

  Lemma gammaE_gamma1 A nu regs mem :
    gammaPE A nu regs mem -> gamma SEGS (unit_params G1 (u1 U)) (ev1 E) (zpatch P E mem0 mem) (v1 A) nu regs mem.
  Proof. intros [H _]. exact (gamma2_v1 _ _ _ _ _ _ _ _ H). Qed.

  Lemma step_post2_dstep A nu succs regs mem pc :
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom ->
    fl_inv G U E A nu mem_e mem ->
    dstep_post2 SEGS G rom U E mem0 mem_e A succs nu regs pc mem.
  Proof.
    intros (regs' & pc' & mem' & A' & nu' & Hst & Hin & Hpc & Hext & Hle & Hfm & Hfl & HG) HFI.
    left. exists regs', pc', mem', A', nu'. split; [eapply msteps_one; [reflexivity|exact Hst]|].
    split; [exact Hin|]. split; [exact Hpc|]. split; [exact Hext|]. split; [exact Hle|]. split; [exact Hfm|].
    split; [exact HG|]. eapply fl_inv_step; [exact HFI|exact Hfl].
  Qed.

  Lemma lift2_sound A i succs nu regs mem (pc : word) w :
    lift2 (vstep2 P A i) = SN2 succs ->
    gammaPE A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    dstep_post2 SEGS G rom U E mem0 mem_e A succs nu regs pc mem.
  Proof.
    unfold lift2. destruct (vstep2 P A i) as [l|m] eqn:Ev; [|discriminate]. intros X; inversion X; subst.
    intros [HG HFI] Hpc Hf He Hd. eapply step_post2_dstep; [|exact HFI]. eapply VSTEP2; eauto.
  Qed.

  Lemma single_ctx2_sound A i A' c nu regs mem (pc : word) w :
    vstep2 P A i = VR2_next [A'] ->
    gammaPE A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    dstep_post2 SEGS G rom U E mem0 mem_e A [set_ctx2 A' c] nu regs pc mem.
  Proof.
    intros Ev [HG HFI] Hpc Hf He Hd.
    destruct (VSTEP2 _ _ _ _ _ _ _ _ Ev HG Hpc Hf He Hd) as (regs' & pc' & mem' & A'' & nu' & Hst & Hin & Hpc' & Hext & Hle & Hfm & Hfl & HG').
    destruct Hin as [<-|[]].
    left. exists regs', pc', mem', (set_ctx2 A' c), nu'. split; [eapply msteps_one; [reflexivity|exact Hst]|].
    split; [now left|]. split; [exact Hpc'|]. split; [exact Hext|]. split; [exact Hle|]. split; [exact Hfm|].
    apply gammaE_set_ctx2. split; [exact HG'|]. eapply fl_inv_step; [exact HFI|exact Hfl].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma try_exits2_none A : forall l msgs,
    try_exits2 P l A msgs = None ->
    exists X sigma, In X l /\ match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 P X (vs2_pc A) []) A = MOk sigma.
  Proof.
    induction l as [|X t IH]; intros msgs H; cbn [try_exits2] in H; [discriminate|].
    destruct (match_state2 isv_join2 no_skip false MM_cut pm_empty (load_cstate2 P X (vs2_pc A) []) A) as [sigma|m] eqn:M.
    - exists X, sigma. split; [now left|exact M].
    - destruct (IH _ H) as (X' & sigma & Hin & M'). exists X', sigma. split; [now right|exact M'].
  Qed.

  Lemma exits_ok X : In X (u2_exits U) -> cstate2_ok P X = true /\ cstate2_iface_b X = true.
  Proof.
    intros HX. unfold unit_static_ok2 in STATIC.
    destruct (cstate2_ok P (u2_pre U) && cstate2_iface_b (u2_pre U) && wrgn_ok U (u2_pre U)); [|discriminate].
    destruct (pre_canonical2 G P U); [|discriminate].
    destruct (forallb (fun c => pc_ok (cut2_pc c) && forallb (fun cs => cstate2_ok P cs && wrgn_ok U cs) (cut2_states c)) (u2_cuts U)); [|discriminate].
    destruct (pc_ok (u_entry (u1 U))); [|discriminate].
    destruct (forallb (fun cs => cstate2_ok P cs && cstate2_iface_b cs && wrgn_ok U cs) (u2_exits U)) eqn:EX; [|discriminate].
    rewrite forallb_forall in EX. specialize (EX _ HX). apply andb_prop in EX as [EX _]. apply andb_prop in EX as [E1 E2]. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma own_flags_iface X pc ctx nu : cstate2_iface_b X = true -> own_flags (load_cstate2 P X pc ctx) nu = [].
  Proof.
    unfold cstate2_iface_b. intros H. apply andb_prop in H as [H NF]. apply andb_prop in H as [_ _].
    unfold own_flags, load_cstate2. cbn [vs_rgn]. unfold load_regions.
    rewrite flat_map_app.
    assert (A1 : flat_map (fun r => match vr_kind r with RK_fake _ fl => [nu fl] | _ => [] end) (map vregion_of (cs_rgn X)) = []).
    { rewrite forallb_forall in NF.
      assert (NF' : forall s, In s (cs_rgn X) -> is_fake s = false).
      { intros s Hs. specialize (NF s Hs). apply andb_prop in NF as [NF _]. now destruct (is_fake s). }
      clear - NF'. induction (cs_rgn X) as [|s t IH]; [reflexivity|]. cbn [map flat_map].
      rewrite IH by (intros; apply NF'; now right).
      specialize (NF' s (or_introl eq_refl)). unfold is_fake in NF'. cbn [vregion_of vr_kind].
      destruct (sr_kind s); cbn; try reflexivity. discriminate. }
    rewrite A1. unfold std_regions. destruct (has_asan P); reflexivity.
  Qed.

  Lemma unit_exit2_exit A succs nu regs mem :
    unit_exit2 D A = SN2 succs ->
    ra_is_exit2 U (get_reg (v1 A) 1) = true ->
    gammaPE A nu regs mem ->
    succs = []
    /\ getr regs 1%bv = wordZ (unit_ret2 U E)
    /\ exit_regs2 G U nu regs
    /\ exists X nu'', In X (u2_exits U)
         /\ gammaPE (load_cstate2 P X (unit_ret2 U E) []) nu'' regs mem
         /\ ext FIRST_FRESH2 nu nu''
         /\ (forall a, in_flags_zone P E a -> mem (wordZ a) = mem_e (wordZ a)).
  Proof.
    intros Hx Hra HGE. pose proof HGE as [HG HFI].
    pose proof (gammaE_gamma1 _ _ _ _ HGE) as HG1.
    pose proof (ra_is_exit_sound SEGS G1 (u1 U) (ev1 E) _ (v1 A) nu regs mem _ HG1 eq_refl Hra) as R1.
    unfold unit_exit2 in Hx. change (de2_U D) with U in Hx. change (de2_G D) with G in Hx. change (de2_P D) with P in Hx.
    destruct (absval_eqb (get_reg (v1 A) 2) (lsymc SP0 (u_sp (u1 U)))) eqn:Esp; [|discriminate].
    destruct (sregs_intact (v1 A)) eqn:Esr; [|discriminate].
    destruct (absval_eqb (get_reg (v1 A) 3) (lsym GP)) eqn:Egp; [|discriminate].
    destruct (absval_eqb (get_reg (v1 A) 4) (lconst (ge2_tp G))) eqn:Etp; [|discriminate].
    cbn [negb] in Hx.
    match type of Hx with (if negb ?b then _ else _) = _ => destruct b; [|discriminate] end. cbn [negb] in Hx.
    destruct (no_local_regions A); [|discriminate]. cbn [negb] in Hx.
    destruct (try_exits2 P (u2_exits U) A []) as [msgs|] eqn:T; [discriminate|].
    inversion Hx; subst succs.
    destruct (try_exits2_none _ _ _ T) as (X & sigma & HinX & M).
    destruct (exits_ok _ HinX) as [HX HXI].
    destruct (MATCH _ _ _ _ _ _ _ _ HG HX M) as (HG' & EXT & OWN).
    split; [reflexivity|]. split; [exact R1|]. split.
    - split; [|split; [|split]].
      + rewrite (absval_eqb_reg SEGS G1 (u1 U) (ev1 E) _ (v1 A) nu regs mem 2%bv _ HG1 ltac:(discriminate) Esp). rewrite eval_lsymc. reflexivity.
      + rewrite (absval_eqb_reg SEGS G1 (u1 U) (ev1 E) _ (v1 A) nu regs mem 3%bv _ HG1 ltac:(discriminate) Egp). rewrite eval_lsym. reflexivity.
      + rewrite (absval_eqb_reg SEGS G1 (u1 U) (ev1 E) _ (v1 A) nu regs mem 4%bv _ HG1 ltac:(discriminate) Etp). rewrite eval_lconst. reflexivity.
      + eapply (sregs_intact_sound SEGS G1 (u1 U) (ev1 E)); eauto.
    - exists X, (vsubst nu sigma).
      assert (FI' : fl_inv G U E (load_cstate2 P X (unit_ret2 U E) []) (vsubst nu sigma) mem_e mem).
      { unfold vs2_pc in HG'. eapply fl_inv_same; [exact OWN|exact HFI]. }
      split; [exact HinX|]. split; [split; [exact HG'|exact FI']|]. split; [exact EXT|].
      eapply fl_inv_exit; [exact FI'|]. apply own_flags_iface. exact HXI.
  Qed.

  Lemma unit_exit2_sound A succs nu regs mem (pc : word) w (imm : bv 12) :
    unit_exit2 D A = SN2 succs ->
    ra_is_exit2 U (get_reg (v1 A) 1) = true ->
    bv_signed imm = 0 ->
    gammaPE A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Jalr 0%bv 1%bv imm, 4) ->
    dstep_post2 SEGS G rom U E mem0 mem_e A succs nu regs pc mem.
  Proof.
    intros Hx Hra Himm HG Hpc Hf He Hd.
    destruct (unit_exit2_exit _ _ _ _ _ Hx Hra HG) as (-> & R1 & XR & X & nu'' & HinX & HG' & EXT & FL).
    right. exists regs, mem. split.
    - eapply msteps_one; [reflexivity|].
      rewrite (step_jalr_gen SEGS regs pc mem rom w 0%bv 1%bv imm Hf He Hd).
      simpl. rewrite Himm, R1.
      change (jalr_tgt (wordZ (unit_ret2 U E)) 0) with (v_jalr (wordZ (unit_ret2 U E)) 0).
      rewrite RET. reflexivity.
    - exists X, nu''. split; [exact HinX|]. split; [exact HG'|]. split; [exact EXT|].
      split; [exact R1|]. split; [exact XR|]. split; [apply frame_mod_refl|exact FL].
  Qed.

  Lemma pop_ctx2_sound A i succs nu regs mem (pc : word) w :
    pop_ctx2 P A i = SN2 succs ->
    gammaPE A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    dstep_post2 SEGS G rom U E mem0 mem_e A succs nu regs pc mem.
  Proof.
    unfold pop_ctx2. destruct (vs_ctx (v1 A)) as [|c rest]; [discriminate|].
    destruct (vstep2 P A i) as [[|A' [|? ?]]|m] eqn:Ev; try discriminate.
    destruct (Z.eqb (vs2_pc A') c); [|discriminate]. intros X; inversion X; subst.
    intros. eapply single_ctx2_sound; eauto.
  Qed.

  Theorem dstep2_sound A succs nu regs (pc : word) mem :
    dstep2 D A = SN2 succs -> (FIRST_FRESH2 <= vs2_next A)%positive -> vs2_pc A = bv_unsigned pc ->
    gammaPE A nu regs mem -> dstep_post2 SEGS G rom U E mem0 mem_e A succs nu regs pc mem.
  Proof.
    intros Hx HJ Hpc HG. unfold dstep2 in Hx.
    change (de2_G D) with G in Hx. change (de2_P D) with P in Hx.
    unfold vs2_pc in Hpc.
    destruct (itab_get (ge2_itab G) (vs_pc (v1 A))) as [i|] eqn:IT; [|discriminate].
    destruct (ITAB _ _ IT) as (w & Hf & He & Hd).
    rewrite Hpc, Z_to_bv_bv_unsigned in Hf.
    destruct i; try (eapply lift2_sound; eauto; fail).
    - (* [comment removed for export] *)
      destruct (if Z.ltb 0 (wrap64 (vs_pc (v1 A) + bv_signed imm))
                then pm_get (zkey (wrap64 (vs_pc (v1 A) + bv_signed imm))) (ge2_ctab G) else None) as [c|] eqn:CT.
      + eapply CONTRACT2; eauto.
      + destruct (Z.eqb (rz rd) 1) eqn:R1.
        * destruct (call_variants2 D (vs_pc (v1 A)) (wrap64 (vs_pc (v1 A) + bv_signed imm))) as [|v vs] eqn:CV.
          -- destruct (vstep2 P A (Jal rd imm)) as [[|A' [|? ?]]|m] eqn:Ev; try discriminate.
             inversion Hx; subst. eapply single_ctx2_sound; eauto.
          -- eapply (CALL2 A rd imm (v :: vs)); [exact Hx|discriminate|symmetry; exact CV|apply Z.eqb_eq; exact R1
                                                 |exact HJ|exact HG|exact Hpc|exact Hf|exact He|exact Hd].
        * destruct (Z.eqb (rz rd) 0); [|discriminate]. eapply lift2_sound; eauto.
    - (* [comment removed for export] *)
      destruct (Z.eqb (rz rd) 0 && Z.eqb (rz rs1) 1 && Z.eqb (bv_signed imm) 0) eqn:RT.
      + apply andb_prop in RT as [RT Himm]. apply andb_prop in RT as [Hrd Hrs1].
        pose proof (rz_is0 _ Hrd) as ->. pose proof (rz_is1 _ Hrs1) as ->. apply Z.eqb_eq in Himm.
        unfold do_ret2 in Hx. change (de2_U D) with U in Hx. change (de2_P D) with P in Hx.
        destruct (ra_is_exit2 U (get_reg (v1 A) 1)) eqn:RX.
        * destruct (vs_ctx (v1 A)); [|discriminate].
          eapply unit_exit2_sound; eauto.
        * destruct (get_reg (v1 A) 1) as [e|]; [|discriminate].
          destruct (lin_is_const e); [|discriminate].
          eapply pop_ctx2_sound; eauto.
      + eapply lift2_sound; eauto.
  Qed.

End Step2.
