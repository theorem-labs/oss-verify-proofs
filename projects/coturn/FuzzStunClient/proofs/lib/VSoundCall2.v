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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VCert VItab VDriverMatch VContract VDriver VSoundMatch VSound VSoundCall.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeepCb.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Section Call2.
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

  Hypothesis DONE : Forall (unit_okS SEGS G rom) done.
  Hypothesis PO : params_ok SEGS P.
  Hypothesis VSTEP : forall A i succs nu regs mem (pc : word) w,
    vstep P A i = VR_next succs ->
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    step_post SEGS P E mem0 A nu succs regs mem pc rom.

  (* [comment removed for export] *)
  Lemma fetch_word_even pc w : fetch_word SEGS pc = Some w -> bv_unsigned pc mod 2 = 0.
  Proof.
    unfold fetch_word. destruct (Z.eqb_spec (bv_unsigned pc mod 2) 0); simpl; [auto|discriminate].
  Qed.

  Lemma vs_pc_materialize1 A r : vs_pc (materialize1 A r) = vs_pc A.
  Proof.
    unfold materialize1. destruct (get_reg A r); [reflexivity|].
    unfold afresh, fresh_lin; simpl. unfold set_reg. destruct (Z.eqb r 0); destruct A; reflexivity.
  Qed.

  Lemma vs_pc_materialize : forall l A, vs_pc (materialize A l) = vs_pc A.
  Proof. induction l as [|[r i] t IH]; intros A; simpl; [reflexivity|]. rewrite IH. apply vs_pc_materialize1. Qed.

  Lemma apply_exits_in B sigma spoff npc : forall l X B',
    In X l -> apply_exit B sigma spoff (load_cstate X npc []) = Some B' -> In B' (apply_exits B sigma spoff npc l).
  Proof.
    induction l as [|Y t IH]; intros X B' Hin HB; simpl; [destruct Hin|].
    destruct Hin as [<-|Hin].
    - rewrite HB. now left.
    - destruct (apply_exit B sigma spoff (load_cstate Y npc [])); [right|]; eauto.
  Qed.

  Lemma try_variant_inv A V spoff npc succs :
    try_variant D A V spoff npc = SN succs ->
    exists sigma,
      footprint_ok D V spoff = true /\ u_root V = None
      /\ match_state isv_call is_sreg_key true
           (sigma_sregs (set_reg (materialize A sreg_idx) 1 (Some (lconst npc))) sreg_idx (pm_set RA (lconst npc) pm_empty))
           (load_cstate (u_pre V) (u_entry V) []) (set_reg (materialize A sreg_idx) 1 (Some (lconst npc))) = MOk sigma
      /\ pm_forallb (fun _ e => lin_below e (vs_next (set_reg (materialize A sreg_idx) 1 (Some (lconst npc))))) sigma = true
      /\ succs = apply_exits (call_base D (set_reg (materialize A sreg_idx) 1 (Some (lconst npc))) V spoff npc) sigma spoff npc (u_exits V)
      /\ forallb vstate_below_b succs = true.
  Proof.
    (* [comment removed for export] *)
    unfold try_variant. cbv zeta.
    set (A0 := set_reg (materialize A sreg_idx) 1 (Some (lconst npc))).
    set (ms := match_state isv_call is_sreg_key true _ _ A0).
    set (cb := call_base D A0 V spoff npc).
    clearbody cb.
    destruct (footprint_ok D V spoff); [|discriminate].
    destruct (u_root V); [discriminate|].
    destruct ms as [sigma|m]; [|discriminate].
    destruct (pm_forallb _ sigma) eqn:PB; [|discriminate].
    set (ae := apply_exits cb sigma spoff npc (u_exits V)).
    cbn [negb].
    destruct (forallb vstate_below_b ae) eqn:WB; [|discriminate].
    intros X; injection X as <-. exists sigma. repeat split; first [reflexivity | exact PB | exact WB].
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS rom mem0 PO VSTEP"] Lemma regions_sub V spoff npc nuV (a : word) :
    footprint_ok D V spoff = true ->
    env_ok P E ->
    outside a (unit_regions P E) -> outside a (unit_regions (unit_params G V) (callee_env E npc nuV)).
  Proof.
    intros FP HE Hout. pose proof PO as (P0&P1&_&PF&PWC&PW&_).
    destruct HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11).
    unfold P, unit_params in *. cbn [vp_frame vp_wstack vp_wcells vp_splo vp_sphi] in *.
    unfold footprint_ok in FP. apply andb_prop in FP as [FP FE]. apply andb_prop in FP as [FP FG].
    apply andb_prop in FP as [FP FS]. apply andb_prop in FP as [F1 F2]. apply Z.leb_le in F1. apply Z.eqb_eq in F2.
    change (de_U D) with U in *. change (de_P D) with (unit_params G U) in *.
    unfold unit_params in FS, FG. cbn [vp_wstack vp_wcells] in FS, FG.
    unfold unit_regions, callee_env in *. cbn [vp_wstack vp_wcells e_sp0] in *.
    apply outside_app in Hout as [HS HC]. simpl in HS. destruct HS as [HS0 HS].
    pose proof (PW (- vp_frame (ge_P0 G), u_sp U) (or_introl eq_refl)) as W0. simpl in W0.
    apply outside_app. split.
    - simpl. split.
      + (* [comment removed for export] *)
        unfold in_rng in *. rewrite F2.
        pose proof (bv_unsigned_in_range 64 a).
        destruct (Z.lt_decidable (- vp_frame (ge_P0 G)) spoff); [|lia].
        rewrite u_wordZ in HS0 |- * by lia. lia.
      + rewrite forallb_forall in FS.
        assert (GEN : forall l, (forall r, In r l -> in_ranges ((- vp_frame (ge_P0 G), u_sp U) :: u_wstack U) (fst r) (snd r - fst r) = true) ->
                      outside a (map (fun r : Z * Z => (wordZ (e_sp0 E + fst r), snd r - fst r)) l)).
        { induction l as [|[lo hi] t IH]; intros Hl; simpl; [exact I|]. split; [|apply IH; intros; apply Hl; now right].
          pose proof (Hl (lo, hi) ltac:(now left)) as X. cbn [fst snd] in X. apply in_ranges_sound in X as (lo' & hi' & Hin' & L1 & L2).
          unfold in_rng. pose proof (bv_unsigned_in_range 64 a) as Ra.
          destruct (Z.lt_decidable lo hi); [|lia].
          destruct Hin' as [Y|Y].
          * inversion Y; subst. unfold in_rng in HS0. rewrite u_wordZ in HS0 |- * by lia. lia.
          * (* [comment removed for export] *)
            pose proof (PW _ (or_intror Y)) as W. simpl in W.
            assert (HSr : ~ in_rng a (wordZ (e_sp0 E + lo')) (hi' - lo')).
            { clear -HS Y. induction (u_wstack U) as [|[l2 h2] t2 IH2]; simpl in *; [destruct Y|].
              destruct HS as [HS1 HS2]. destruct Y as [Y|Y]; [inversion Y; subst; exact HS1|apply IH2; auto]. }
            unfold in_rng in HSr. rewrite u_wordZ in HSr |- * by (ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @P1; @L1; @L2; @Ra; @H; @W]); lia). lia. }
        apply GEN. exact FS.
    - (* [comment removed for export] *)
      unfold unit_wcells in *. simpl in FE.
      assert (GENC : forall l, (forall c, In c l -> exists c', In c' ((if u_errno U then [(ci_errno (ge_CI G), 4)] else []) ++ u_wglobs U)%list
                                               /\ fst c' <= fst c /\ fst c + snd c <= fst c' + snd c') ->
                     outside a (cells_regions l)).
      { induction l as [|c t IH]; intros Hl; simpl; [exact I|]. split; [|apply IH; intros; apply Hl; now right].
        destruct (Hl c ltac:(now left)) as [c' (C1&C2&C3)].
        destruct (PWC _ C1) as [f (G1&G2&G3)]. destruct (PF _ G1) as (K1&K2&_).
        assert (HCr : ~ in_rng a (wordZ (fst c')) (snd c')).
        { clear -HC C1. unfold cells_regions in HC. induction ((if u_errno U then [(ci_errno (ge_CI G), 4)] else []) ++ u_wglobs U)%list as [|c2 t2 IH2];
            simpl in *; [destruct C1|]. destruct HC as [HC1 HC2]. destruct C1 as [<-|C1]; [exact HC1|apply IH2; auto]. }
        unfold in_rng in *. pose proof (bv_unsigned_in_range 64 a).
        destruct (Z.lt_decidable 0 (snd c)); [|lia].
        rewrite u_wordZ in HCr |- * by (ltac2:(LK.k [@E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E10; @E11; @P0; @P1; @C2; @C3; @G2; @G3; @K1; @K2; @H; @H0]); lia). lia. }
      apply GENC. intros c Hc. apply in_app_iff in Hc as [Hc|Hc].
      + destruct (u_errno V) eqn:EV'; [|destruct Hc]. destruct Hc as [<-|[]].
        destruct (u_errno U); [|discriminate]. exists (ci_errno (ge_CI G), 4). simpl. split; [now left|lia].
      + rewrite forallb_forall in FG. specialize (FG _ Hc). apply in_cells_sound in FG as [c' (X1&X2&X3)].
        exists c'. split; [exact X1|auto].
  Qed.

  Lemma zwrap64_mod2 x : zwrap 64 x mod 2 = x mod 2.
  Proof. unfold zwrap. apply Z.mod_mod_divide. exists (2 ^ 63). reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pos_le_add_aux : forall (r q p s : positive) (n : nat), (r <= q)%positive -> p = q -> Z.pos s = Z.pos p + Z.of_nat n -> (r <= s)%positive.
  Proof. intros r q p s n H1 H2 H3. lia. Qed.

  #[using="DONE PO VSTEP"] Theorem call_sound A (rd : reg) (imm : bv 21) vs succs nu regs mem (pc : word) w :
    do_call D A (wrap64 (vs_pc A + bv_signed imm)) (npc_of A) vs = SN succs ->
    vs <> [] -> vs = call_variants D (vs_pc A) (wrap64 (vs_pc A + bv_signed imm)) ->
    rz rd = 1 ->
    (JOIN0 <= vs_next A)%positive ->
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4) ->
    dstep_post SEGS G rom U E mem0 A succs nu regs pc mem.
  Proof.
    intros Hx Hne Hvs Hrd HJ HG Hpc Hf He Hd.
    set (tgt := wrap64 (vs_pc A + bv_signed imm)) in *. set (npc := npc_of A) in *.
    unfold do_call in Hx. destruct (sp_offset A) as [spoff|] eqn:SPO; [|discriminate].
    destruct (try_variants_sound _ _ _ _ _ _ _ _ _ Hx) as [V [HinV HTV]].
    rewrite Hvs in HinV. destruct (call_variants_in _ _ _ _ _ _ HinV) as [VIN EV].
    destruct (try_variant_inv _ _ _ _ _ HTV) as (sigma & FP & ROOT & MATCH & PB & -> & WB).
    (* [comment removed for export] *)
    destruct (materialize_sound SEGS G U E mem0 A nu regs mem sreg_idx sreg_idx_range HG) as (num & HGm & Xm & Lm).
    set (Am := materialize A sreg_idx) in *.
    (* [comment removed for export] *)
    assert (Hpcm : vs_pc Am = bv_unsigned pc) by (unfold Am; rewrite vs_pc_materialize; exact Hpc).
    assert (Ej : vstep P Am (Jal rd imm) = VR_next [set_pc (set_reg Am (rz rd) (Some (lconst (npc_of Am)))) (wrap64 (vs_pc Am + bv_signed imm))]) by reflexivity.
    destruct (VSTEP _ _ _ _ _ _ _ _ Ej HGm Hpcm Hf He Hd) as (regs1 & pc1 & mem1 & A1 & nu1 & Hst & Hin1 & Hpc1 & X1 & L1 & FM1 & HG1).
    destruct Hin1 as [<-|[]].
    assert (Enpc : npc_of Am = npc) by (unfold npc, npc_of; unfold Am; rewrite vs_pc_materialize; reflexivity).
    assert (Etgt : wrap64 (vs_pc Am + bv_signed imm) = tgt) by (unfold tgt, Am; rewrite vs_pc_materialize; reflexivity).
    rewrite Hrd, Enpc, Etgt in HG1, Hpc1. cbn [vs_pc set_pc] in Hpc1.
    apply gamma_set_pc in HG1.
    set (A0 := set_reg Am 1 (Some (lconst npc))) in *.
    assert (NPC : 0 <= npc < 2 ^ 64) by (unfold npc, npc_of; rewrite wrap64_zwrap; apply zwrap64_range).
    (* [comment removed for export] *)
    destruct (callee_entry SEGS G rom done U E mem0 DONE V VIN A npc sigma MATCH NPC nu1 regs1 mem1 HG1) as (GV & Sub & BO).
    pose proof (V_ok SEGS G rom done DONE V VIN) as [STV OKV].
    assert (RET : ret_ok (wordZ (unit_ret V (callee_env E npc (vsubst nu1 sigma))))).
    { unfold unit_ret. rewrite ROOT. cbn [e_ra callee_env]. apply ret_ok_even. rewrite u_wordZ by (ltac2:(LK.k [@NPC]); lia).
      unfold npc, npc_of. pose proof (fetch_word_even _ _ Hf) as Ev. rewrite <- Hpc in Ev.
      rewrite wrap64_zwrap, zwrap64_mod2. replace (vs_pc A + 4) with (vs_pc A + 2 * 2) by (ltac2:(LK.k [@NPC]); lia).
      rewrite Z_mod_plus_full. exact Ev. }
    destruct (OKV (callee_env E npc (vsubst nu1 sigma)) mem0 (vsubst nu1 sigma) regs1 mem1 RET GV) as (regs2 & mem2 & Hrun & HEXIT).
    destruct HEXIT as (X & nuV' & XIN & XG & XEXT & XRA & XREGS & XFM).
    unfold unit_ret in Hrun, XG, XRA. rewrite ROOT in Hrun, XG, XRA. cbn [e_ra callee_env] in Hrun, XG, XRA.
    (* [comment removed for export] *)
    assert (SIGB : sigma_below sigma (vs_next A0)).
    { intros s e Hs. exact (pm_forallb_sound _ _ PB s Hs). }
    assert (HJ0 : (JOIN0 <= vs_next A0)%positive).
    { unfold A0. rewrite vs_next_set_reg. clear -HJ Lm. eapply Pos.le_trans; eauto. }
    destruct (load_cstate_below X npc [] (cstate_ok_wf _ _ (X_static SEGS G rom done DONE V VIN X XIN))) as [_ J0].
    set (b := vs_next A0). set (nJ := (Pos.to_nat (cs_next X) - Pos.to_nat JOIN0)%nat). set (b' := Pos.of_nat (Pos.to_nat b + nJ)).
    assert (NX : Z.pos (cs_next X) = Z.pos JOIN0 + Z.of_nat nJ) by (unfold nJ; clear -J0; unfold JOIN0 in *; lia).
    assert (HB' : Z.pos b' = Z.pos b + Z.of_nat nJ) by (unfold b'; clear; lia).
    destruct (apply_exit_sound SEGS G rom done U E mem0 DONE V VIN A spoff npc sigma MATCH NPC SIGB FP PO nu1 regs1 mem1 HG1
                X nuV' regs2 mem2 XIN XG XEXT XRA XREGS XFM b b' nJ eq_refl HJ0 NX HB')
      as (B' & HBe & HGB & HpcB & HnB).
    assert (HinB : In B' (apply_exits (call_base D A0 V spoff npc) sigma spoff npc (u_exits V))).
    { eapply apply_exits_in; [exact XIN|exact HBe]. }
    assert (WBB : vstate_below_b B' = true).
    { rewrite forallb_forall in WB. apply WB. exact HinB. }
    specialize (HGB WBB).
    (* [comment removed for export] *)
    left. exists regs2, (wordZ npc), mem2, B', (nu2 nu1 nuV' b nJ).
    split.
    { eapply msteps_trans; [eapply msteps_one; [reflexivity|exact Hst]|].
      replace pc1 with (wordZ (u_entry V)); [exact Hrun|].
      rewrite EV. rewrite <- (wordZ_u pc1), <- Hpc1. reflexivity. }
    split; [exact HinB|]. split; [rewrite HpcB; rewrite u_wordZ by (ltac2:(LK.k [@NPC; @HnB]); lia); reflexivity|].
    split.
    { eapply ext_trans; [exact Lm| exact Xm|]. eapply ext_trans; [|exact X1|].
      - apply Pos.le_refl.
      - intros s Hs. apply (nu2_old nu1 nuV' b nJ). unfold b, A0. rewrite vs_next_set_reg. exact Hs. }
    split.
    { rewrite HnB. assert (Hb : b = vs_next Am) by (unfold b, A0; rewrite vs_next_set_reg; reflexivity).
      exact (pos_le_add_aux (vs_next A) (vs_next Am) b b' nJ Lm Hb HB'). }   (* [comment removed for export] *)
    split; [|exact HGB].
    eapply frame_mod_trans_same; [exact FM1|].
    eapply frame_mod_weaken; [|exact XFM]. intros a Ha. eapply regions_sub; eauto. exact (proj1 HG).
  Qed.
End Call2.
