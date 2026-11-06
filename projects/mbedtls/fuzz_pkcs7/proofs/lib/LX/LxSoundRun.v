(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec Arr AEvt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA AShadow.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxSum LxStep LxRun LxDenot LxSoundExpr LxSoundDec LxSoundMem LxSoundStep.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section LXH.
Context {lxHT : lx_hints}.

Section RunSound.
  Variable segs : list Segment.
  Variable G : gl.
  Variable C : lxcfg.
  Variable pl : plan.
  Variable genv : list expr.    (* [comment removed for export] *)
  Variable GS : list Z.         (* [comment removed for export] *)
  Variable OPS : list (mem -> Prop).  (* [comment removed for export] *)
  Variable LAWS : list (list (Z * Z) -> mem -> mem -> Prop).  (* [comment removed for export] *)
  Variable PROPS : list (list Z -> Prop).  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable LB0 : lx_blks.
  Variable HEAPP : lx_hpred.
  Variable HEAPCW : lx_cwpred.
  Variable LAWH : lx_hlaws.
  Variable HRS : lx_hress.      (* [comment removed for export] *)

  Definition genv_ok (E : env) : Prop := Forall2 (fun g v => zden E g = v) genv GS
    /\ ((eol E = OPS /\ elw E = LAWS /\ epr E = PROPS) /\ (elb0 E = LB0 /\ ehp E = HEAPP /\ ecw E = HEAPCW /\ elh E = LAWH /\ ehr E = HRS)
        /\ (hp_frame segs (ehp E) (ecw E) /\ hp_blk (ecw E) /\ Forall (hlaw_ok segs) (elh E))).
  Lemma genv_ok_hlaw : forall E, genv_ok E -> Forall (hlaw_ok segs) (elh E).
  Proof. intros E [_ [_ [_ [_ [_ X]]]]]. exact X. Qed.
  Lemma genv_ok_hpf : forall E, genv_ok E -> hp_frame segs (ehp E) (ecw E).
  Proof. intros E [_ [_ [_ [X _]]]]. exact X. Qed.
  Lemma genv_ok_hbk : forall E, genv_ok E -> hp_blk (ecw E).
  Proof. intros E [_ [_ [_ [_ [X _]]]]]. exact X. Qed.


  Notation L := (g_L G).
  Notation CS := (g_CS G).

  Lemma evtA_mstepA : forall Q ms ms', mstepA segs L CS ms ms' -> evtA segs L CS Q ms' -> evtA segs L CS Q ms.
  Proof.
    intros Q ms ms' [Hs (acc & Hst & OK)] H. eapply evtA_step; [split; [exact Hs| exact Hst] | exact OK | exact H].
  Qed.

  (* [comment removed for export] *)
  Variable TGT : Model -> machine_state -> Prop.
  Hypothesis TGT_evtA : forall mo (P : machine_state -> Prop) ms,
    evtA segs L CS P ms -> (forall ms', P ms' -> TGT mo ms') -> TGT mo ms.
  Lemma TGT_mstepA : forall mo ms ms', mstepA segs L CS ms ms' -> TGT mo ms' -> TGT mo ms.
  Proof.
    intros mo ms ms' ST H. apply (TGT_evtA mo (fun x => x = ms') ms).
    - eapply evtA_mstepA; [exact ST| apply evtA_done; reflexivity].
    - intros ms1 ->. exact H.
  Qed.

  Lemma leaf_sound : forall E ss ms (K : Model -> machine_state -> Prop),
    st_ok segs G E ss ms -> leaf_oblig segs G E ss K -> K (ecur E) ms.
  Proof.
    intros E ss ms K (m & -> & HM & HP & MU & WM & MI & SM) H. unfold leaf_oblig in H.
    assert (MF : forall mf P, Forall (mfact_ok segs L CS E m) mf -> mf_tele segs G E m mf P -> P).
    { induction mf as [|f mf IH]; intros P HF HT; [exact HT|]. inversion HF; subst. apply (IH P); [assumption|]. apply HT. assumption. }
    assert (PF : forall pf P, Forall (pfact_ok CS E) pf -> pf_tele G E pf P -> P).
    { induction pf as [|f pf IH]; intros P HF HT; [exact HT|]. inversion HF; subst. apply (IH P); [assumption|]. apply HT. assumption. }
    specialize (H m). pose proof (PF (s_pf ss) _ HP (MF (s_mf ss) _ HM H) MU WM MI) as X.
    destruct (s_same ss) eqn:SS; [exact (X (SM eq_refl))| exact X].
  Qed.

  Lemma cfg_ok_setz : forall E ss n v, cfg_ok G C E -> ss_wf C ss = true -> n = s_nx ss -> cfg_ok G C (env_setz E n v).
  Proof.
    intros E ss n v CFG WF ->. unfold cfg_ok in CFG |- *. unfold ss_wf in WF.
    destruct (c_acc C) as [A|]; [|exact CFG]. apply andb_prop in WF as [_ WSB].
    destruct CFG as (C1 & C2 & S1 & S2). split; [exact C1|]. split; [exact C2|]. split; [|exact S2].
    rewrite !zdenp_ok in S1 |- *. rewrite (zden_setz E (s_nx ss) v (ac_sb A) WSB). exact S1.
  Qed.

  Lemma guard_dead : forall E ss ms, st_ok segs G E ss ms -> contradictory (s_pf ss) = true -> False.
  Proof.
    intros E ss ms (m & _ & _ & HP & _) H. unfold contradictory in H.
    apply (lin_ge_sound CS E) in H; [|exact HP]. cbn in H. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Rel.
    Variable E : env.
    Variable m : mem.
    Notation mok := (mfact_ok segs L CS E m).

    Lemma absorb_sound : forall hi mf hi' rest,
      Forall mok mf -> absorb hi mf = Some (hi', rest) ->
      Forall mok rest /\
      forall lo, stk segs m (zden E lo) (zden E hi) -> zden E lo <= zden E hi -> zden E hi <= zden E hi' -> stk segs m (zden E lo) (zden E hi').
    Proof.
      intros hi mf. induction mf as [|f mf IH]; intros hi' rest HM H; [discriminate|].
      inversion HM as [|f' mf'' Hf HM']; subst f' mf''. cbn [absorb] in H.
      assert (SKIP : match absorb hi mf with Some (h, r) => Some (h, f :: r) | None => None end = Some (hi', rest) ->
                     Forall mok rest /\ forall lo, stk segs m (zden E lo) (zden E hi) -> zden E lo <= zden E hi -> zden E hi <= zden E hi' -> stk segs m (zden E lo) (zden E hi')).
      { intros HS. destruct (absorb hi mf) as [[h r]|] eqn:AB; [|discriminate]. injection HS; intros <- <-.
        destruct (IH h r HM' eq_refl) as [R1 R2]. split; [constructor; assumption| exact R2]. }
      destruct f as [b cs|b cs|b n k|b h2|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try (apply SKIP; exact H).
      - destruct (ediff_lit b hi) as [[|p|p]|] eqn:HD; try (apply SKIP; exact H). injection H; intros <- <-.
        apply ediff_lit_den with (E := E) in HD. split; [exact HM'|].
        intros lo ST LE1 LE2. cbn in Hf. rewrite zdenp_ok in Hf.
        rewrite eadd_den. cbn [zden].
        replace (zden E hi + Z.of_N (cells_sizeN cs)) with (zden E b + Z.of_nat (cells_size (csden E cs))) by (rewrite csden_size; lia).
        eapply stk_release; [| exact Hf | lia]. rewrite HD, Z.add_0_r. exact ST.
      - destruct (ediff_lit b hi) as [[|p|p]|] eqn:HD; try (apply SKIP; exact H). injection H; intros <- <-.
        apply ediff_lit_den with (E := E) in HD. split; [exact HM'|].
        intros lo ST LE1 LE2. cbn in Hf. rewrite !zdenp_ok in Hf. rewrite HD, Z.add_0_r in Hf.
        eapply stk_merge; [exact ST| exact Hf| lia].
    Qed.

    Lemma release_pass_sound : forall spx pf mf acc,
      Forall (pfact_ok CS E) pf -> Forall mok mf -> Forall mok acc -> Forall mok (release_pass spx pf mf acc).
    Proof.
      intros spx pf mf. induction mf as [|f mf IH]; intros acc HP HM HA; cbn [release_pass].
      - apply Forall_rev. exact HA.
      - inversion HM as [|f' mf'' Hf HM']; subst f' mf''.
        assert (REST : Forall mok (rev acc ++ mf)) by (apply Forall_app; split; [apply Forall_rev; exact HA| exact HM']).
        destruct f as [b cs|b cs|b n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok]; try (apply IH; [exact HP| exact HM'| constructor; assumption]).
        destruct (absorb hi (rev acc ++ mf)) as [[hi' rest]|] eqn:AB; [|apply IH; [exact HP| exact HM'| constructor; assumption]].
        destruct (dec_le pf lo hi) eqn:D1; [destruct (dec_le pf hi hi') eqn:D2; [destruct (dec_le pf hi' spx) eqn:D3|]|]; cbn [andb];
          try (apply IH; [exact HP| exact HM'| constructor; assumption]).
        apply (dec_le_sound CS E _ _ _ HP) in D1. apply (dec_le_sound CS E _ _ _ HP) in D2.
        destruct (absorb_sound hi _ hi' rest REST AB) as [R1 R2].
        constructor; [|exact R1]. cbn. cbn in Hf. rewrite !zdenp_ok in Hf |- *. apply R2; assumption.
    Qed.

  End Rel.

  (* [comment removed for export] *)
  Lemma gc_var_sub : forall pf v f, In f (gc_var pf v) -> In f pf.
  Proof.
    intros pf v f H. unfold gc_var in H.
    match type of H with In f (if ?c then _ else _) => destruct c end; [apply filter_In in H as [H _]; exact H| exact H].
  Qed.

  Lemma gc_vars_sub : forall cands pf f, In f (fold_left gc_var cands pf) -> In f pf.
  Proof.
    induction cands as [|v cands IH]; intros pf f H; cbn in H; [exact H|]. apply IH in H. apply gc_var_sub in H. exact H.
  Qed.

  Lemma gc_facts_shape : forall nx ss, exists pf',
    gc_facts nx ss = set_pf ss pf' /\ (forall f, In f pf' -> In f (s_pf ss)).
  Proof.
    intros nx ss. unfold gc_facts.
    match goal with |- context [match ?cs with [] => _ | _ => _ end] => destruct cs as [|v cands] eqn:CE end.
    - exists (s_pf ss). split; [destruct ss; reflexivity| intros f H; exact H].
    - eexists. split; [reflexivity|]. intros f H. apply gc_vars_sub in H. exact H.
  Qed.

  Lemma gc_facts_INV : forall nx E ss m, INV segs G E ss m -> INV segs G E (gc_facts nx ss) m.
  Proof.
    intros nx E ss m HI. destruct (gc_facts_shape nx ss) as (pf' & -> & SUB).
    destruct HI as (HM & HP & REST). unfold set_pf. split; [exact HM|]. split; [|exact REST].
    apply List.Forall_forall. intros f Hf. rewrite List.Forall_forall in HP. apply HP, SUB, Hf.
  Qed.

  Lemma gc_facts_rs : forall nx ss, s_rs (gc_facts nx ss) = s_rs ss.
  Proof. intros nx ss. destruct (gc_facts_shape nx ss) as (pf' & -> & _). reflexivity. Qed.

  Lemma gc_facts_den : forall nx E ss m, ms_den segs G E (gc_facts nx ss) m = ms_den segs G E ss m.
  Proof. intros nx E ss m. destruct (gc_facts_shape nx ss) as (pf' & -> & _). reflexivity. Qed.

  Lemma release_stk_ok : forall E ss ms, st_ok segs G E ss ms -> st_ok segs G E (release_stk ss) ms.
  Proof.
    intros E ss ms (mm & -> & HM & HP & REST). unfold release_stk, set_mf. exists mm. split; [reflexivity|]. cbn.
    split; [| split; [exact HP| exact REST]].
    assert (IT : forall n mf, Forall (mfact_ok segs L CS E mm) mf -> Forall (mfact_ok segs L CS E mm) (release_iter n (rd_expr ss 2) (s_pf ss) mf)).
    { induction n as [|n IH]; intros mf H; cbn; [exact H|]. apply IH. apply release_pass_sound; [exact HP| exact H| constructor]. }
    apply IT. exact HM.
  Qed.

  (* [comment removed for export] *)
  Lemma mf_bounds_ok : forall E m f, mfact_ok segs L CS E m f -> Forall (pfact_ok CS E) (mf_bounds f).
  Proof.
    intros E m f Hf.
    assert (TWO : forall b k, 0 <= zden E b -> zden E b + k <= 2 ^ 64 ->
              Forall (pfact_ok CS E) [FGe b; FGe (eadd (ELit (two64 - k)) (emulc (-1) b))]).
    { intros b k H1 H2. constructor; [unfold pfact_ok; rewrite zdenp_ok; exact H1|].
      constructor; [|constructor]. unfold pfact_ok. rewrite zdenp_ok, eadd_den, emulc_den. cbn [zden]. unfold two64. lia. }
    assert (TWO' : forall b hi, 0 <= zden E b -> zden E hi <= 2 ^ 64 ->
              Forall (pfact_ok CS E) [FGe b; FGe (eadd (ELit two64) (emulc (-1) hi))]).
    { intros b hi H1 H2. constructor; [unfold pfact_ok; rewrite zdenp_ok; exact H1|].
      constructor; [|constructor]. unfold pfact_ok. rewrite zdenp_ok, eadd_den, emulc_den. cbn [zden]. unfold two64. lia. }
    assert (THREE : forall b n hi, 0 <= zden E b -> 0 <= zden E n -> zden E hi <= 2 ^ 64 ->
              Forall (pfact_ok CS E) [FGe b; FGe n; FGe (eadd (ELit two64) (emulc (-1) hi))]).
    { intros b n hi H1 H2 H3. constructor; [unfold pfact_ok; rewrite zdenp_ok; exact H1|]. apply TWO'; assumption. }
    destruct f as [b cs|b cs|b n k|lo hi|oa on|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok].
    7:{ (* [comment removed for export] *)
        destruct (marr_bytes segs L CS E _ _ _ _ _ _ Hf) as (bs0 & HB & HL & _). pose proof (bytes_at_bound _ _ _ _ HB) as B.
        assert (NN : 0 <= zden E rn_).
        { destruct (marr_cases rw_) as [-> |[-> |[-> |(N1 & N4 & N8)]]]; cbn [Z.of_N] in HL; try lia.
          exfalso. cbn in Hf. destruct rw_ as [|p]; [exact Hf|]. repeat (destruct p as [p|p|]; try exact (proj1 Hf); try exact Hf; try congruence). }
        cbn [mf_bounds]. apply THREE; [lia| exact NN|]. rewrite eadd_den, emulc_den. lia. }
    all: unfold mfact_ok in Hf; rewrite ?zdenp_ok in Hf; cbn [mf_bounds].
    - pose proof (rw_cells_bound _ _ _ _ Hf) as B. rewrite csden_size in B. apply TWO; lia.
    - pose proof (ro_cells_bound _ _ _ _ Hf) as B. rewrite csden_size in B. apply TWO; lia.
    - destruct Hf as [HB HL]. pose proof (bytes_at_bound _ _ _ _ HB) as B.
      apply THREE; [lia| lia |]. rewrite eadd_den. lia.
    - destruct Hf as (S1 & S2 & _). apply TWO'; lia.
    - constructor.
    - constructor.
    - constructor. - constructor. - constructor. - constructor. - constructor.
    - constructor. - constructor. - constructor. - constructor. - constructor. - constructor.
  Qed.

  Lemma with_bounds_ok : forall E ss ms, st_ok segs G E ss ms -> st_ok segs G E (with_bounds ss) ms.
  Proof.
    intros E ss ms (m & -> & HM & HP & REST). unfold with_bounds.
    destruct (add_pfs_rs ss (flat_map mf_bounds (s_mf ss))) as (P1 & P2 & P3 & P4 & P5).
    exists m. split; [unfold ms_den; rewrite P1, P2; reflexivity|].
    assert (HB : Forall (pfact_ok CS E) (flat_map mf_bounds (s_mf ss))).
    { clear REST P1 P2 P3 P4 P5. induction HM as [|f mf Hf HM IH]; [constructor|]. cbn [flat_map]. apply Forall_app. split; [|exact IH].
      eapply mf_bounds_ok. exact Hf. }
    pose proof (INV_pf segs G E ss m _ (conj HM (conj HP REST)) HB) as HI'.
    destruct HI' as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2| exact X3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Norm.
    Variable E : env.

    Lemma enorm_den : forall e, zden E (enorm e) = zden E e.
    Proof.
      induction e as [z|i|i|a IHa b IHb|c a IHa|o a IHa b IHb]; cbn [enorm]; try reflexivity.
      - cbn. lia. - cbn. lia.
      - rewrite eadd_den, IHa, IHb. reflexivity.
      - rewrite emulc_den, IHa. reflexivity.
      - assert (GEN : zden E (eatom (EOp o (enorm a) (enorm b))) = opden o (zden E a) (zden E b)) by (cbn; rewrite IHa, IHb; lia).
        destruct (enorm a) as [x| | | | |]; try exact GEN. destruct (enorm b) as [y| | | | |]; try exact GEN.
        cbn in IHa, IHb. subst. cbn. destruct o; reflexivity.
    Qed.

    Lemma norm_reg_den : forall r, rden E (norm_reg r) = rden E r.
    Proof. intros [i|e]; cbn -[mkreg enorm zdenp]; [reflexivity|]. rewrite mkreg_den, enorm_den, zdenp_ok. reflexivity. Qed.

    Lemma norm_cell_den : forall c, cden E (norm_cell c) = cden E c.
    Proof. intros [i|w e|w k|w i|c o l|wr er]; cbn -[zdenp enorm N.to_nat cden]; cbn [cden]; try reflexivity; rewrite !zdenp_ok, enorm_den; reflexivity. Qed.

    Lemma norm_cells_den : forall cs, csden E (map norm_cell cs) = csden E cs.
    Proof. induction cs as [|c cs IH]; [reflexivity|]. cbn. rewrite norm_cell_den. unfold csden in IH. rewrite IH. reflexivity. Qed.

    Lemma norm_w_den : forall W, wden E (map (fun lh : expr * expr => (enorm (fst lh), enorm (snd lh))) W) = wden E W.
    Proof. intros W. unfold wden. rewrite map_map. apply map_ext. intros [l h]. cbn [fst snd]. rewrite !zdenp_ok, !enorm_den. reflexivity. Qed.

    Lemma norm_lexpr_denw : forall l, ldenw E (norm_lexpr l) = ldenw E l.
    Proof. induction l as [k|l IH i w v]; cbn -[zdenp]; [reflexivity|]. rewrite IH, !zdenp_ok, !enorm_den. reflexivity. Qed.
    Lemma norm_lexpr_denb : forall l, ldenb E (norm_lexpr l) = ldenb E l.
    Proof. induction l as [k|l IH i w v]; cbn -[zdenp wbytes upd_bytes]; [reflexivity|]. rewrite IH, !zdenp_ok, !enorm_den. reflexivity. Qed.

    Lemma norm_bl_den : forall bl, blden E (norm_bl bl) = blden E bl.
    Proof. induction bl as [|a n bl IH|kv]; cbn -[zdenp]; [reflexivity| |reflexivity]. rewrite IH, !zdenp_ok, !enorm_den. reflexivity. Qed.
    Lemma norm_mf_ok : forall m f, mfact_ok segs L CS E m f -> mfact_ok segs L CS E m (norm_mf f).
    Proof.
      intros m f H.
      destruct f as [fa fcs|fa fcs|fa fn fk|flo fhi|foa fon|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok];
        [ .. | cbn [norm_mf mfact_ok] in H |- *; rewrite (norm_bl_den qbl), (norm_w_den qok); exact H
             | cbn [norm_mf mfact_ok] in H |- *; rewrite (norm_bl_den qbl), (norm_w_den qX), !zdenp_ok, enorm_den; rewrite !zdenp_ok in H; exact H
             | cbn [norm_mf mfact_ok] in H |- *; rewrite !zdenp_ok, !enorm_den; rewrite !zdenp_ok in H; exact H
             | cbn [norm_mf mfact_ok] in H |- *; rewrite (norm_bl_den qbl), !zdenp_ok, !enorm_den; rewrite !zdenp_ok in H; exact H
             | cbn [norm_mf mfact_ok] in H |- *; exact H
             | cbn [norm_mf mfact_ok] in H |- *; rewrite (norm_bl_den qo), (norm_bl_den qn), (norm_w_den qok), map_map;
               rewrite (map_ext _ _ (fun e => eq_trans (zdenp_ok E (enorm e)) (eq_trans (enorm_den e) (eq_sym (zdenp_ok E e))))); exact H ];
        try solve [cbn [norm_mf mfact_ok] in H |- *; rewrite !norm_w_den; exact H];
        try solve [cbn [norm_mf mfact_ok] in H |- *; exact H];
        try solve [cbn [norm_mf mfact_ok] in H |- *; rewrite !norm_lexpr_denw, !norm_lexpr_denb, !zdenp_ok, !enorm_den; rewrite !zdenp_ok in H; exact H];
        cbn [norm_mf mfact_ok] in H |- *; rewrite ?norm_cells_den; rewrite !zdenp_ok, ?enorm_den in H |- *;
        rewrite ?enorm_den; exact H.
    Qed.

    Lemma norm_pf_ok : forall f, pfact_ok CS E f -> Forall (pfact_ok CS E) (norm_pf f).
    Proof.
      intros f H.
      assert (Z1 : forall e, zdenp E (enorm e) = zdenp E e) by (intros e; rewrite !zdenp_ok; apply enorm_den).
      destruct f; cbn [norm_pf]; unfold pfact_ok in H |- *.
      - apply List.Forall_cons; [|apply List.Forall_nil]. rewrite Z1. exact H.
      - apply List.Forall_cons; [|apply List.Forall_nil]. rewrite !Z1. exact H.
      - apply List.Forall_cons; [|apply List.Forall_nil]. rewrite !Z1. exact H.
      - (* [comment removed for export] *) pose proof (lin_of_den E (enorm a)) as LD. rewrite enorm_den in LD.
        destruct (lin_of (enorm a)) as [ts c] eqn:LO. cbn [fst snd] in LD.
        assert (DFLT : Forall (fun f : pfact => pfact_ok CS E f) [FAl a k]) by (apply List.Forall_cons; [exact H| apply List.Forall_nil]).
        destruct ts as [|[k1 b] ts']; [exact DFLT|].
        destruct k1 as [|p|p]; [exact DFLT| |exact DFLT]. destruct p as [p|p|]; [exact DFLT| exact DFLT|].
        destruct ts' as [|t ts'']; [|exact DFLT].
        destruct (Z.eqb_spec (c mod 2 ^ Z.of_N k) 0) as [HC0|]; [|exact DFLT].
        apply List.Forall_cons; [|apply List.Forall_nil]. unfold pfact_ok. rewrite zdenp_ok. rewrite zdenp_ok in H.
        cbn [tden] in LD. assert (P2 : 0 < 2 ^ Z.of_N k) by (apply Z.pow_pos_nonneg; lia).
        replace (zden E b) with (zden E a - c) by lia. rewrite Zminus_mod, H, HC0. cbn. rewrite Z.mod_0_l; lia.
      - apply List.Forall_cons; [|apply List.Forall_nil]. rewrite !Z1. exact H.
      - apply List.Forall_cons; [|apply List.Forall_nil]. intros n' Hn H1 H2. rewrite !Z1 in H1. rewrite !Z1 in H2. rewrite !Z1. apply H; assumption.
      - apply List.Forall_cons; [|apply List.Forall_nil]. rewrite zdenp_ok, esub_den, !enorm_den. rewrite !zdenp_ok in H. lia.
      - apply List.Forall_cons; [|apply List.Forall_nil]. rewrite zdenp_ok, eadd_den, esub_den, !enorm_den. cbn [zden]. rewrite !zdenp_ok in H. lia.
      - apply List.Forall_cons; [|apply List.Forall_cons; [|apply List.Forall_nil]]; rewrite zdenp_ok, esub_den, !enorm_den; rewrite !zdenp_ok in H; lia.
      - apply List.Forall_cons; [|apply List.Forall_nil]. rewrite !zdenp_ok, !esub_den, !enorm_den. rewrite !zdenp_ok in H. lia.
      - apply List.Forall_cons; [|apply List.Forall_nil]. rewrite !zdenp_ok, !esub_den, !enorm_den. rewrite !zdenp_ok in H. lia.
      - (* [comment removed for export] *) apply List.Forall_cons; [|apply List.Forall_nil].
        replace (map (zdenp E) (map enorm args)) with (map (zdenp E) args); [exact H|].
        rewrite map_map. apply map_ext. intros e. symmetry. apply Z1.
    Qed.

    Definition rdw (ws : list word) : bvmap 5 word :=
      match ws with
      | [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
         x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31] =>
          mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      | _ => bvmap_empty
      end.

    Lemma regs_den_rdw : forall E' rs, regs_den E' rs = rdw (map (rden E') rs).
    Proof. intros E' rs. do 31 (destruct rs as [|? rs]; [reflexivity|]). destruct rs; reflexivity. Qed.

    Lemma norm_regs_den : forall rs, regs_den E (map norm_reg rs) = regs_den E rs.
    Proof.
      intros rs. rewrite !regs_den_rdw, map_map. f_equal. apply map_ext. intros r. apply norm_reg_den.
    Qed.

    Lemma norm_ss_ok : forall ss ms, st_ok segs G E ss ms -> st_ok segs G E (norm_ss ss) ms.
    Proof.
      intros ss ms (m & -> & HM & HP & MU & REST). exists m. unfold norm_ss, ms_den. cbn [s_rs s_pc s_mf s_pf s_W].
      split. { rewrite norm_regs_den. destruct (s_pc ss) as [z|r]; cbn [norm_pc pc_den]; [reflexivity|]. rewrite norm_reg_den. reflexivity. }
      split. { apply List.Forall_forall. intros f Hf. apply in_map_iff in Hf as (g & <- & Hg). apply norm_mf_ok. rewrite List.Forall_forall in HM. apply HM. exact Hg. }
      split; [|split; [|exact REST]].
      2:{ assert (WN : forall W, wden E (map (fun lh : expr * expr => (enorm (fst lh), enorm (snd lh))) W) = wden E W).
          { intros W. unfold wden. rewrite map_map. apply map_ext. intros [l h]. cbn [fst snd]. rewrite !zdenp_ok, !enorm_den. reflexivity. }
          rewrite WN. exact MU. }
      assert (ND : forall l f, In f (pf_nodup l) -> In f l).
      { induction l as [|g l IHl]; intros f Hf; cbn in Hf; [exact Hf|]. unfold pf_add in Hf at 1. fold (pf_nodup l) in Hf.
        destruct (pf_mem g (pf_nodup l)); [right; apply IHl; exact Hf|]. destruct Hf as [<-|Hf]; [left; reflexivity| right; apply IHl; exact Hf]. }
      apply List.Forall_forall. intros f Hf. apply ND in Hf. apply in_flat_map in Hf as (g & Hg & Hfg).
      rewrite List.Forall_forall in HP. pose proof (norm_pf_ok g (HP g Hg)) as X. rewrite List.Forall_forall in X. apply X. exact Hfg.
    Qed.

    Lemma norm_ss_len : forall ss, length (s_rs (norm_ss ss)) = length (s_rs ss).
    Proof. intros ss. unfold norm_ss. cbn. apply map_length. Qed.
  End Norm.

  Lemma frame_sep1_ok : forall E pf W f,
    Forall (pfact_ok CS E) pf -> pfact_ok CS E f -> Forall (pfact_ok CS E) (frame_sep1 pf W f).
  Proof.
    intros E pf W f HF Hf.
    assert (GE : forall x y, lin_ge0 pf (esub x y) = true -> zden E y <= zden E x).
    { intros x y H. apply (lin_ge0_sound CS E) in H; [|exact HF]. unfold esub in H. rewrite eadd_den, emulc_den in H. lia. }
    destruct f; cbn [frame_sep1]; try (constructor; fail); try apply Forall_nil.
    - (* [comment removed for export] *)
      unfold pfact_ok in Hf. rewrite !zdenp_ok in Hf.
      induction W as [|[l h] W IH]; [apply Forall_nil|]. cbn [flat_map].
      apply Forall_app. split; [|exact IH].
      destruct (lin_ge0 pf (esub l _)) eqn:G1; [|apply Forall_nil]. destruct (lin_ge0 pf (esub _ h)) eqn:G2; [|apply Forall_nil].
      cbn [andb]. constructor; [|apply Forall_nil]. apply GE in G1. apply GE in G2.
      unfold pfact_ok. rewrite !zdenp_ok, !enorm_den. unfold esub. rewrite !eadd_den, !emulc_den. lia.
    - (* [comment removed for export] *)
      unfold pfact_ok in Hf. rewrite !zdenp_ok in Hf.
      induction W as [|[l h] W IH]; [apply Forall_nil|]. cbn [flat_map].
      apply Forall_app. split; [|exact IH].
      destruct (lin_ge0 pf (esub l _)) eqn:G1; [|apply Forall_nil]. destruct (lin_ge0 pf (esub _ h)) eqn:G2; [|apply Forall_nil].
      cbn [andb]. constructor; [|apply Forall_nil]. apply GE in G1. apply GE in G2.
      unfold pfact_ok. rewrite !zdenp_ok, !enorm_den. unfold esub. rewrite !eadd_den, !emulc_den. lia.
  Qed.

  Lemma with_frame_seps_ok : forall E ss ms, st_ok segs G E ss ms -> st_ok segs G E (with_frame_seps ss) ms.
  Proof.
    intros E ss ms (m & -> & HM & HP & REST). unfold with_frame_seps.
    destruct (add_pfs_rs ss (flat_map (frame_sep1 (s_pf ss) (s_W ss)) (s_pf ss))) as (P1 & P2 & P3 & P4 & P5).
    exists m. split; [unfold ms_den; rewrite P1, P2; reflexivity|].
    assert (HB : Forall (pfact_ok CS E) (flat_map (frame_sep1 (s_pf ss) (s_W ss)) (s_pf ss))).
    { clear REST P1 P2 P3 P4 P5.
      assert (GEN : forall fs, Forall (pfact_ok CS E) fs -> Forall (pfact_ok CS E) (flat_map (frame_sep1 (s_pf ss) (s_W ss)) fs)).
      { intros fs Hfs. induction Hfs as [|f fs' Hf Hfs' IH]; [constructor|]. cbn [flat_map]. apply Forall_app. split; [|exact IH].
        eapply frame_sep1_ok; [exact HP| exact Hf]. }
      apply GEN. exact HP. }
    pose proof (INV_pf segs G E ss m _ (conj HM (conj HP REST)) HB) as HI'.
    destruct HI' as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2| exact X3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Fixpoint setzs (E : env) (nx : positive) (vs : list Z) : env :=
    match vs with [] => E | v :: vs' => setzs (env_setz E nx v) (Pos.succ nx) vs' end.

  (* [comment removed for export] *)
  Fixpoint setls (E : env) (nl : positive) (ls : list (list word)) : env :=
    match ls with [] => E | l :: ls' => setls (env_setl E nl l) (Pos.succ nl) ls' end.
  (* [comment removed for export] *)
  Definition env_call (E : env) (nx : positive) (vs : list Z) (nl : positive) (ls : list (list word)) : env :=
    setls (setzs E nx vs) nl ls.
  (* [comment removed for export] *)
  Definition env_law (E : env) (nx : positive) (vs : list Z) (nl : positive) (ls : list (list word)) (nm : nat) (mc mp : mem) : env :=
    env_setm (env_setm (env_call E nx vs nl ls) nm mc) (S nm) mp.
  (* [comment removed for export] *)
  Definition env_heap (E : env) (nx : positive) (vs : list Z) (nl : positive) (ls : list (list word)) (nm : nat) (mc mp : mem) (mo : Model)
      (lb : list (Z * Z)) : env :=
    env_setbl (env_setcur (env_law E nx vs nl ls nm mc mp) mo) (S nm) lb.

  Fixpoint binds (E : env) (nx : positive) (k : nat) (P : env -> Prop) : Prop :=
    match k with
    | O => P E
    | S k' => forall v : Z, binds (env_setz E nx v) (Pos.succ nx) k' P
    end.
  Fixpoint lbinds (E : env) (nl : positive) (kl : nat) (P : env -> Prop) : Prop :=
    match kl with
    | O => P E
    | S kl' => forall l : list word, lbinds (env_setl E nl l) (Pos.succ nl) kl' P
    end.

  Lemma oblig_join : forall E c nx k t K, oblig segs G E (RJoin c nx k t) K -> binds E nx k (fun E1 => oblig segs G E1 t K).
  Proof.
    intros E c nx k t K. cbn [oblig]. revert E nx. induction k as [|k IH]; intros E nx H; cbn in H |- *; [exact H|].
    intros v. apply IH. apply H.
  Qed.

  Lemma oblig_call : forall E pc nx k nl kl t K,
    oblig segs G E (RCall pc nx k nl kl t) K -> binds E nx k (fun E1 => lbinds E1 nl kl (fun E2 => oblig segs G E2 t K)).
  Proof.
    intros E pc nx k nl kl t K. cbn [oblig]. revert E nx. induction k as [|k IH]; intros E nx H; cbn in H |- *.
    - revert E nl H. induction kl as [|kl IHl]; intros E nl H; cbn in H |- *; [exact H|]. intros l. apply IHl. apply H.
    - intros v. apply IH. apply H.
  Qed.

  Lemma oblig_callL : forall E pc nx k nl kl nm t K,
    oblig segs G E (RCallL pc nx k nl kl nm t) K ->
    binds E nx k (fun E1 => lbinds E1 nl kl (fun E2 => forall mc mp : mem, oblig segs G (env_setm (env_setm E2 nm mc) (S nm) mp) t K)).
  Proof.
    intros E pc nx k nl kl nm t K. cbn [oblig]. revert E nx. induction k as [|k IH]; intros E nx H; cbn in H |- *.
    - revert E nl H. induction kl as [|kl IHl]; intros E nl H; cbn in H |- *; [exact H|]. intros l. apply IHl. apply H.
    - intros v. apply IH. apply H.
  Qed.

  Lemma oblig_callM : forall E pc nx k nl kl nm t1 t2 K,
    oblig segs G E (RCallM pc nx k nl kl nm t1 t2) K ->
    binds E nx k (fun E1 => lbinds E1 nl kl (fun E2 => forall mc mp : mem, forall mo : Model, forall lb : list (Z * Z),
        oblig segs G (env_setbl (env_setcur (env_setm (env_setm E2 nm mc) (S nm) mp) mo) (S nm) lb) t1 K
        /\ oblig segs G (env_setbl (env_setcur (env_setm (env_setm E2 nm mc) (S nm) mp) mo) (S nm) lb) t2 K)).
  Proof.
    intros E pc nx k nl kl nm t1 t2 K. cbn [oblig]. revert E nx. induction k as [|k IH]; intros E nx H; cbn in H |- *.
    - revert E nl H. induction kl as [|kl IHl]; intros E nl H; cbn in H |- *; [exact H|]. intros l. apply IHl. apply H.
    - intros v. apply IH. apply H.
  Qed.

  Lemma binds_apply : forall k E nx P vs, binds E nx k P -> length vs = k -> P (setzs E nx vs).
  Proof.
    induction k as [|k IH]; intros E nx P [|v vs] H Hl; cbn in Hl |- *; try discriminate; [exact H|].
    apply IH; [apply H| lia].
  Qed.
  Lemma lbinds_apply : forall kl E nl P ls, lbinds E nl kl P -> length ls = kl -> P (setls E nl ls).
  Proof.
    induction kl as [|kl IH]; intros E nl P [|l ls] H Hl; cbn in Hl |- *; try discriminate; [exact H|].
    apply IH; [apply H| lia].
  Qed.
  Lemma call_apply : forall k kl E nx nl t K vs ls,
    binds E nx k (fun E1 => lbinds E1 nl kl (fun E2 => oblig segs G E2 t K)) -> length vs = k -> length ls = kl ->
    oblig segs G (env_call E nx vs nl ls) t K.
  Proof.
    intros k kl E nx nl t K vs ls H Hv Hl. unfold env_call.
    exact (lbinds_apply kl _ nl (fun E2 => oblig segs G E2 t K) ls (binds_apply k E nx _ vs H Hv) Hl).
  Qed.
  Lemma callL_apply : forall k kl E nx nl nm t K vs ls mc mp,
    binds E nx k (fun E1 => lbinds E1 nl kl (fun E2 => forall mc mp : mem, oblig segs G (env_setm (env_setm E2 nm mc) (S nm) mp) t K)) ->
    length vs = k -> length ls = kl ->
    oblig segs G (env_law E nx vs nl ls nm mc mp) t K.
  Proof.
    intros k kl E nx nl nm t K vs ls mc mp H Hv Hl. unfold env_law, env_call.
    exact (lbinds_apply kl _ nl (fun E2 => forall mc mp : mem, oblig segs G (env_setm (env_setm E2 nm mc) (S nm) mp) t K) ls
             (binds_apply k E nx _ vs H Hv) Hl mc mp).
  Qed.

  Lemma callM_apply : forall k kl E nx nl nm t1 t2 K vs ls mc mp mo lb,
    binds E nx k (fun E1 => lbinds E1 nl kl (fun E2 => forall mc mp : mem, forall mo : Model, forall lb : list (Z * Z),
        oblig segs G (env_setbl (env_setcur (env_setm (env_setm E2 nm mc) (S nm) mp) mo) (S nm) lb) t1 K
        /\ oblig segs G (env_setbl (env_setcur (env_setm (env_setm E2 nm mc) (S nm) mp) mo) (S nm) lb) t2 K)) ->
    length vs = k -> length ls = kl ->
    oblig segs G (env_heap E nx vs nl ls nm mc mp mo lb) t1 K /\ oblig segs G (env_heap E nx vs nl ls nm mc mp mo lb) t2 K.
  Proof.
    intros k kl E nx nl nm t1 t2 K vs ls mc mp mo lb H Hv Hl. unfold env_heap, env_law, env_call.
    exact (lbinds_apply kl _ nl (fun E2 => forall mc mp : mem, forall mo : Model, forall lb : list (Z * Z),
             oblig segs G (env_setbl (env_setcur (env_setm (env_setm E2 nm mc) (S nm) mp) mo) (S nm) lb) t1 K
             /\ oblig segs G (env_setbl (env_setcur (env_setm (env_setm E2 nm mc) (S nm) mp) mo) (S nm) lb) t2 K) ls
             (binds_apply k E nx _ vs H Hv) Hl mc mp mo lb).
  Qed.

  (* [comment removed for export] *)
  Lemma evars_lt_mono : forall n n' e, (n <= n')%positive -> evars_lt n e = true -> evars_lt n' e = true.
  Proof.
    intros n n' e Hn. induction e; cbn -[Pos.ltb]; intros H; try reflexivity; try exact H.
    - apply Pos.ltb_lt in H. apply Pos.ltb_lt. lia.
    - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
    - apply IHe. exact H.
    - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  Qed.

  Lemma forallb_mono : forall {X} (p q : X -> bool) l, (forall x, p x = true -> q x = true) -> forallb p l = true -> forallb q l = true.
  Proof.
    intros X p q l Hpq. induction l as [|x l IH]; cbn; intros H; [reflexivity|].
    apply andb_prop in H as [H1 H2]. rewrite (Hpq x H1), (IH H2). reflexivity.
  Qed.

  Lemma rvars_lt_mono : forall n n' r, (n <= n')%positive -> rvars_lt n r = true -> rvars_lt n' r = true.
  Proof. intros n n' [i|e] Hn H; cbn in H |- *; [reflexivity| eapply evars_lt_mono; eauto]. Qed.

  Lemma cvars_lt_mono : forall n n' c, (n <= n')%positive -> cvars_lt n c = true -> cvars_lt n' c = true.
  Proof. intros n n' c; induction c as [i|w e|w k|w i|c IH o l|wr er]; intros Hn H; cbn in H |- *; try reflexivity; [eapply evars_lt_mono; eauto| apply IH; assumption| eapply evars_lt_mono; eauto]. Qed.

  Ltac mono_tac n n' Hn :=
    repeat match goal with
      | H : _ && _ = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat match goal with
      | H : evars_lt n ?e = true |- _ => apply (evars_lt_mono n n' e Hn) in H
      | H : forallb (cvars_lt n) ?cs = true |- _ => apply (forallb_mono _ _ cs (cvars_lt_mono n n' ^~ Hn)) in H || fail 1
      end.

  Lemma lvars_lt_mono : forall n n' l, (n <= n')%positive -> lvars_lt n l = true -> lvars_lt n' l = true.
  Proof.
    intros n n' l Hn. induction l as [k|l IH i w v]; cbn -[evars_lt]; intros H; [reflexivity|].
    repeat (apply andb_prop in H; destruct H as [H ?]).
    rewrite (IH H), (evars_lt_mono n n' _ Hn H1), (evars_lt_mono n n' _ Hn H0). reflexivity.
  Qed.

  Lemma mfvars_lt_mono : forall n n' f, (n <= n')%positive -> mfvars_lt n f = true -> mfvars_lt n' f = true.
  Proof.
    intros n n' f Hn H.
    assert (BLM : forall bl, blvars_lt n bl = true -> blvars_lt n' bl = true).
    { induction bl as [|a k bl IH|kv]; cbn -[evars_lt]; intros X; [reflexivity| |reflexivity].
      apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. rewrite (evars_lt_mono n n' _ Hn X1), (evars_lt_mono n n' _ Hn X2), (IH X3). reflexivity. }
    assert (WM : forall W, forallb (fun lh : expr * expr => evars_lt n (fst lh) && evars_lt n (snd lh)) W = true ->
                           forallb (fun lh : expr * expr => evars_lt n' (fst lh) && evars_lt n' (snd lh)) W = true).
    { intros W X. eapply forallb_mono; [|exact X]. intros [l h] Y; cbn in Y |- *; apply andb_prop in Y as [Y1 Y2].
      rewrite (evars_lt_mono n n' _ Hn Y1), (evars_lt_mono n n' _ Hn Y2); reflexivity. }
    destruct f as [fa fcs|fa fcs|fa fn fk|flo fhi|foa fon|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok];
      [ .. | cbn [mfvars_lt] in H |- *; apply andb_prop in H as [H1 H2]; rewrite (BLM _ H1), (WM _ H2); reflexivity
           | cbn [mfvars_lt] in H |- *; apply andb_prop in H as [H H3]; apply andb_prop in H as [H1 H2];
             rewrite (BLM _ H1), (evars_lt_mono n n' _ Hn H2), (WM _ H3); reflexivity
           | cbn [mfvars_lt] in H |- *; apply andb_prop in H as [H H3]; apply andb_prop in H as [H1 H2];
             rewrite (evars_lt_mono n n' _ Hn H1), (evars_lt_mono n n' _ Hn H2), (evars_lt_mono n n' _ Hn H3); reflexivity
           | cbn [mfvars_lt] in H |- *; apply andb_prop in H as [H H3]; apply andb_prop in H as [H1 H2];
             rewrite (evars_lt_mono n n' _ Hn H1), (evars_lt_mono n n' _ Hn H2), (BLM _ H3); reflexivity
           | reflexivity
           | cbn [mfvars_lt] in H |- *; apply andb_prop in H as [H H4]; apply andb_prop in H as [H H3]; apply andb_prop in H as [H1 H2];
             rewrite (BLM _ H1), (BLM _ H2), (WM _ H4), (forallb_mono _ _ qxs (fun e => evars_lt_mono n n' e Hn) H3); reflexivity ];
      try solve [cbn [mfvars_lt] in H |- *; eapply forallb_mono; [|exact H]; intros [l h] X; cbn in X |- *; apply andb_prop in X as [X1 X2];
                 rewrite (evars_lt_mono n n' _ Hn X1), (evars_lt_mono n n' _ Hn X2); reflexivity];
      try solve [cbn -[evars_lt lvars_lt] in H |- *; repeat (apply andb_prop in H; destruct H as [H ?]);
                 rewrite (evars_lt_mono n n' _ Hn H), (lvars_lt_mono n n' _ Hn H1), (evars_lt_mono n n' _ Hn H0); reflexivity];
      cbn -[evars_lt forallb cvars_lt] in H |- *;
      repeat (apply andb_prop in H; destruct H as [H ?]);
      repeat match goal with
        | H : evars_lt n ?e = true |- _ => apply (evars_lt_mono n n' e Hn) in H
        | H : forallb (cvars_lt n) ?cs = true |- _ => apply (forallb_mono _ _ cs (fun c => cvars_lt_mono n n' c Hn)) in H
        end;
      rewrite ?H, ?H0, ?H1; reflexivity.
  Qed.

  Lemma pfvars_lt_mono : forall n n' f, (n <= n')%positive -> pfvars_lt n f = true -> pfvars_lt n' f = true.
  Proof.
    intros n n' f Hn H. destruct f; cbn -[evars_lt Pos.ltb forallb] in H |- *;
      repeat (apply andb_prop in H; destruct H as [H ?]);
      repeat match goal with
        | H : evars_lt n ?e = true |- _ => apply (evars_lt_mono n n' e Hn) in H
        | H : Pos.ltb ?k n = true |- _ => assert (Pos.ltb k n' = true) by (apply Pos.ltb_lt in H; apply Pos.ltb_lt; lia); clear H
        | H : forallb (evars_lt n) ?xs = true |- _ => apply (forallb_mono (evars_lt n) (evars_lt n') xs (fun e => evars_lt_mono n n' e Hn)) in H
        end;
      repeat match goal with | H : _ = true |- _ => rewrite H; clear H end; reflexivity.
  Qed.

  Lemma pcvars_lt_mono : forall n n' p, (n <= n')%positive -> pcvars_lt n p = true -> pcvars_lt n' p = true.
  Proof. intros n n' [z|r] Hn H; cbn -[rvars_lt] in H |- *; [reflexivity| eapply rvars_lt_mono; eauto]. Qed.

  (* [comment removed for export] *)
  Definition wf_at (n : positive) (ss : sstate) : bool :=
    pcvars_lt n (s_pc ss) && forallb (rvars_lt n) (s_rs ss)
    && forallb (mfvars_lt n) (s_mf ss) && forallb (pfvars_lt n) (s_pf ss)
    && forallb (fun lh => evars_lt n (fst lh) && evars_lt n (snd lh)) (s_W ss)
    && match c_acc C with Some A => evars_lt n (ac_sb A) | None => true end.

  Lemma ss_wf_at : forall ss, ss_wf C ss = wf_at (s_nx ss) ss.
  Proof. reflexivity. Qed.

  Lemma wf_at_mono : forall n n' ss, (n <= n')%positive -> wf_at n ss = true -> wf_at n' ss = true.
  Proof.
    intros n n' ss Hn H. unfold wf_at in H |- *.
    apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    rewrite (pcvars_lt_mono n n' _ Hn H1).
    rewrite (forallb_mono _ _ _ (fun r => rvars_lt_mono n n' r Hn) H2).
    rewrite (forallb_mono _ _ _ (fun f => mfvars_lt_mono n n' f Hn) H3).
    rewrite (forallb_mono _ _ _ (fun f => pfvars_lt_mono n n' f Hn) H4).
    assert (H6' : match c_acc C with Some A => evars_lt n' (ac_sb A) | None => true end = true)
      by (destruct (c_acc C) as [A|]; [exact (evars_lt_mono n n' _ Hn H6)| reflexivity]).
    rewrite H6'.
    assert (H5' : forallb (fun lh : expr * expr => evars_lt n' (fst lh) && evars_lt n' (snd lh)) (s_W ss) = true).
    { eapply forallb_mono; [|exact H5]. intros [l h] Hx. cbn in Hx |- *. apply andb_prop in Hx as [Hl Hh].
      rewrite (evars_lt_mono n n' _ Hn Hl), (evars_lt_mono n n' _ Hn Hh). reflexivity. }
    rewrite H5'. reflexivity.
  Qed.

  Section Setzs.
    Variable E : env.

    Lemma zden_setzs : forall vs E0 nx e, evars_lt nx e = true -> zden (setzs E0 nx vs) e = zden E0 e.
    Proof.
      induction vs as [|v vs IH]; intros E0 nx e H; cbn; [reflexivity|].
      rewrite IH by (eapply evars_lt_mono; [|exact H]; lia). apply zden_setz. exact H.
    Qed.

    Lemma zdenp_setzs : forall vs nx e, evars_lt nx e = true -> zdenp (setzs E nx vs) e = zdenp E e.
    Proof. intros. rewrite !zdenp_ok. apply zden_setzs. assumption. Qed.

    Lemma ew_setzs : forall vs E0 nx i, ew (setzs E0 nx vs) i = ew E0 i.
    Proof. induction vs; intros; cbn; [reflexivity|]. rewrite IHvs. reflexivity. Qed.
    Lemma eb_setzs : forall vs E0 nx i, eb (setzs E0 nx vs) i = eb E0 i.
    Proof. induction vs; intros; cbn; [reflexivity|]. rewrite IHvs. reflexivity. Qed.

    Lemma ez_setzs_old : forall vs E0 nx i, (i < nx)%positive -> ez (setzs E0 nx vs) i = ez E0 i.
    Proof.
      induction vs as [|v vs IH]; intros E0 nx i Hi; cbn; [reflexivity|].
      rewrite IH by lia. rewrite ez_setz. destruct (Pos.eqb_spec i nx); [lia| reflexivity].
    Qed.

    Lemma ez_setzs_here : forall vs v E0 nx, ez (setzs E0 nx (v :: vs)) nx = v.
    Proof. intros. cbn. rewrite ez_setzs_old by lia. rewrite ez_setz, Pos.eqb_refl. reflexivity. Qed.

    Lemma rden_setzs : forall vs nx r, rvars_lt nx r = true -> rden (setzs E nx vs) r = rden E r.
    Proof. intros vs nx [i|e] H; cbn -[zdenp ew]; [apply ew_setzs|]. rewrite zdenp_setzs by exact H. reflexivity. Qed.

    Lemma regs_den_setzs : forall vs nx rs, forallb (rvars_lt nx) rs = true -> regs_den (setzs E nx vs) rs = regs_den E rs.
    Proof.
      intros vs nx rs H. rewrite !regs_den_rdw. f_equal. apply map_ext_in. intros r Hr. apply rden_setzs.
      rewrite forallb_forall in H. apply H. exact Hr.
    Qed.

    Lemma pc_den_setzs : forall vs nx p, pcvars_lt nx p = true -> pc_den (setzs E nx vs) p = pc_den E p.
    Proof. intros vs nx [z|r] H; cbn -[rden Z_to_bv ret_pc]; [reflexivity|]. rewrite rden_setzs by exact H. reflexivity. Qed.

    Lemma cden_setzs : forall vs nx c, cvars_lt nx c = true -> cden (setzs E nx vs) c = cden E c.
    Proof.
      intros vs nx c; induction c as [i|w e|w k|w i|c IH o l|wr er]; intros H; cbn -[zdenp N.to_nat ew eb cden]; cbn [cden]; rewrite ?ew_setzs, ?eb_setzs; try reflexivity.
      - cbn in H. rewrite !zdenp_setzs by exact H. reflexivity.
      - cbn in H. fold (cden (setzs E nx vs) c) (cden E c). rewrite (IH H). reflexivity.
      - cbn in H. rewrite !zdenp_setzs by exact H. reflexivity.
    Qed.

    Lemma csden_setzs : forall vs nx cs, forallb (cvars_lt nx) cs = true -> csden (setzs E nx vs) cs = csden E cs.
    Proof.
      intros vs nx cs H. unfold csden. induction cs as [|c cs IH]; [reflexivity|]. cbn in H. apply andb_prop in H as [H1 H2].
      cbn. rewrite cden_setzs, IH by assumption. reflexivity.
    Qed.

    Lemma epr_setzs : forall vs E0 nx, epr (setzs E0 nx vs) = epr E0.
    Proof. induction vs as [|v vs IH]; intros E0 nx; cbn [setzs]; [reflexivity|]. rewrite IH. reflexivity. Qed.
    Lemma elb0_setzs : forall vs E0 nx, elb0 (setzs E0 nx vs) = elb0 E0.
    Proof. induction vs as [|v vs IH]; intros E0 nx; cbn [setzs]; [reflexivity|]. rewrite IH. reflexivity. Qed.
    Lemma ehp_setzs : forall vs E0 nx, ehp (setzs E0 nx vs) = ehp E0.
    Proof. induction vs as [|v vs IH]; intros E0 nx; cbn [setzs]; [reflexivity|]. rewrite IH. reflexivity. Qed.
    Lemma ecw_setzs : forall vs E0 nx, ecw (setzs E0 nx vs) = ecw E0.
    Proof. induction vs as [|v vs IH]; intros E0 nx; cbn [setzs]; [reflexivity|]. rewrite IH. reflexivity. Qed.
    Lemma elh_setzs : forall vs E0 nx, elh (setzs E0 nx vs) = elh E0.
    Proof. induction vs as [|v vs IH]; intros E0 nx; cbn [setzs]; [reflexivity|]. rewrite IH. reflexivity. Qed.
    Lemma ehlaw_setzs : forall vs E0 nx l, ehlaw (setzs E0 nx vs) l = ehlaw E0 l.
    Proof. intros. unfold ehlaw. rewrite elh_setzs. reflexivity. Qed.
    Lemma elbl_setzs : forall vs E0 nx, elbl (setzs E0 nx vs) = elbl E0.
    Proof. induction vs as [|v vs IH]; intros E0 nx; cbn [setzs]; [reflexivity|]. rewrite IH. reflexivity. Qed.
    Lemma ehr_setzs : forall vs E0 nx, ehr (setzs E0 nx vs) = ehr E0.
    Proof. induction vs as [|v vs IH]; intros E0 nx; cbn [setzs]; [reflexivity|]. rewrite IH. reflexivity. Qed.
    Lemma blden_setzs : forall vs nx bl, blvars_lt nx bl = true -> blden (setzs E nx vs) bl = blden E bl.
    Proof.
      intros vs nx bl. induction bl as [|a k bl IH|kv]; cbn -[zdenp evars_lt setzs]; intros H;
        [rewrite elb0_setzs; reflexivity| | unfold eblv; rewrite elbl_setzs; reflexivity].
      apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. rewrite !zdenp_setzs, IH by assumption. reflexivity.
    Qed.
    Lemma zdenps_setzs : forall vs nx xs, forallb (evars_lt nx) xs = true -> map (zdenp (setzs E nx vs)) xs = map (zdenp E) xs.
    Proof.
      intros vs nx xs. induction xs as [|x xs IH]; cbn -[zdenp evars_lt setzs]; intros H; [reflexivity|].
      apply andb_prop in H as [H1 H2]. rewrite zdenp_setzs, IH by assumption. reflexivity.
    Qed.
    Lemma pfact_ok_setzs : forall vs nx f, pfvars_lt nx f = true -> pfact_ok CS (setzs E nx vs) f <-> pfact_ok CS E f.
    Proof.
      intros vs nx f H.
      destruct f as [| | | | | | | | | | |pj pxs]; [| | | | | | | | | | | unfold pfact_ok, eprop; rewrite epr_setzs; cbn [pfvars_lt] in H; rewrite (zdenps_setzs vs nx pxs H); tauto].
      all: cbn -[zdenp Z.pow Z.of_N ez env_setz setzs] in H |- *;
        repeat (apply andb_prop in H; destruct H as [H ?]); rewrite ?zdenp_setzs by assumption; try tauto.
      rewrite !ez_setzs_old by (apply Pos.ltb_lt in H; lia). tauto.
    Qed.

    Lemma wden_setzs : forall vs nx W, forallb (fun lh => evars_lt nx (fst lh) && evars_lt nx (snd lh)) W = true ->
      wden (setzs E nx vs) W = wden E W.
    Proof.
      intros vs nx W H. unfold wden. induction W as [|[l h] W IH]; [reflexivity|]. cbn in H.
      apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [Hl Hh]. cbn. rewrite !zdenp_setzs, IH by assumption. reflexivity.
    Qed.

    Lemma eml_setzs_gen : forall vs E0 nx, eml (setzs E0 nx vs) = eml E0.
    Proof. induction vs as [|v vs IH]; intros E0 nx; cbn [setzs]; [reflexivity|]. rewrite IH. reflexivity. Qed.
    Lemma eml_setzs : forall vs nx, eml (setzs E nx vs) = eml E.
    Proof. intros. apply eml_setzs_gen. Qed.
    Lemma refm_setzs : forall vs nx ss, refm (setzs E nx vs) ss = refm E ss.
    Proof. intros. unfold refm, em. rewrite eml_setzs. reflexivity. Qed.

    Lemma eo_setzs : forall vs E0 nx k, eo (setzs E0 nx vs) k = eo E0 k.
    Proof. induction vs; intros; cbn; [reflexivity|]. rewrite IHvs. reflexivity. Qed.
    Lemma em_setzs : forall vs E0 nx k, em (setzs E0 nx vs) k = em E0 k.
    Proof. intros. unfold em. rewrite eml_setzs_gen. reflexivity. Qed.
    Lemma elw_setzs : forall vs E0 nx, elw (setzs E0 nx vs) = elw E0.
    Proof. induction vs as [|v vs IH]; intros E0 nx; cbn [setzs]; [reflexivity|]. rewrite IH. reflexivity. Qed.
    Lemma elaw_setzs : forall vs E0 nx l, elaw (setzs E0 nx vs) l = elaw E0 l.
    Proof. intros. unfold elaw. rewrite elw_setzs. reflexivity. Qed.
    Lemma ecur_setzs : forall vs E0 nx, ecur (setzs E0 nx vs) = ecur E0.
    Proof. induction vs as [|v vs IH]; intros E0 nx; cbn [setzs]; [reflexivity|]. rewrite IH. reflexivity. Qed.

    Lemma el_setzs : forall vs E0 nx i, el (setzs E0 nx vs) i = el E0 i.
    Proof. induction vs; intros; cbn; [reflexivity|]. rewrite IHvs. reflexivity. Qed.

    Lemma ldenw_setzs : forall vs nx l, lvars_lt nx l = true -> ldenw (setzs E nx vs) l = ldenw E l.
    Proof.
      intros vs nx l. induction l as [k|l IH i w e]; intros H; cbn -[zdenp setzs el] in H |- *; [apply el_setzs|].
      repeat (apply andb_prop in H; destruct H as [H ?]). rewrite IH, !zdenp_setzs by assumption. reflexivity.
    Qed.

    Lemma ldenb_setzs : forall vs nx l, lvars_lt nx l = true -> ldenb (setzs E nx vs) l = ldenb E l.
    Proof.
      intros vs nx l. induction l as [k|l IH i w e]; intros H; cbn -[zdenp wbytes upd_bytes setzs eb] in H |- *; [apply eb_setzs|].
      repeat (apply andb_prop in H; destruct H as [H ?]). rewrite IH, !zdenp_setzs by assumption. reflexivity.
    Qed.

    Lemma mfact_ok_setzs : forall vs nx mm f, mfvars_lt nx f = true -> mfact_ok segs L CS (setzs E nx vs) mm f <-> mfact_ok segs L CS E mm f.
    Proof.
      intros vs nx mm f H. destruct f as [fa fcs|fa fcs|fa fn fk|flo fhi|foa fon|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok].
      7:{ cbn [mfvars_lt] in H. repeat (apply andb_prop in H; destruct H as [H ?]).
          cbn [mfact_ok]. rewrite !zdenp_setzs, ?ldenw_setzs, ?ldenb_setzs by assumption. tauto. }
      7:{ cbn [mfvars_lt] in H. cbn [mfact_ok]. rewrite (wden_setzs vs nx mW H), !em_setzs. tauto. }
      7:{ cbn [mfact_ok]. rewrite !em_setzs. tauto. }
      7:{ cbn [mfvars_lt] in H. cbn [mfact_ok]. rewrite (wden_setzs vs nx mX H), !em_setzs, elaw_setzs. tauto. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H1 H2]. cbn [mfact_ok]. rewrite !zdenp_setzs by assumption. rewrite elaw_setzs. tauto. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H1 H2]. cbn [mfact_ok]. rewrite !zdenp_setzs by assumption. rewrite elaw_setzs. tauto. }
      (* [comment removed for export] *)
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H1 H2].
          apply mheap_ok_ext; [exact (blden_setzs vs nx qbl H1)| exact (wden_setzs vs nx qok H2)| apply ehp_setzs| apply ecw_setzs| apply elb0_setzs| apply elh_setzs| apply ecur_setzs]. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. cbn [mfact_ok].
          rewrite (blden_setzs vs nx qbl H1), (zdenp_setzs vs nx qsp H2), (wden_setzs vs nx qX H3), !em_setzs, ehlaw_setzs. tauto. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. cbn [mfact_ok]. rewrite !zdenp_setzs by assumption. rewrite ehlaw_setzs.
          unfold hlawcli. rewrite elb0_setzs. tauto. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. cbn [mfact_ok].
          rewrite !zdenp_setzs, (blden_setzs vs nx qbl H3) by assumption. tauto. }
      7:{ cbn [mfact_ok]. rewrite ehlaw_setzs, eo_setzs. unfold hlawopq. rewrite elb0_setzs. tauto. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. cbn [mfact_ok].
          rewrite (blden_setzs vs nx qo H1), (blden_setzs vs nx qn H2), (wden_setzs vs nx qok H4).
          rewrite (map_ext_in (zdenp (setzs E nx vs)) (zdenp E) qxs) by (intros e He; apply zdenp_setzs; rewrite forallb_forall in H3; auto).
          unfold ehres. rewrite ecw_setzs, elb0_setzs, ehr_setzs. tauto. }
      all: try solve [cbn [mfvars_lt] in H; rewrite forallb_app in H; apply andb_prop in H as [H1 H2];
                   cbn [mfact_ok]; rewrite (wden_setzs vs nx ok_l H1), (wden_setzs vs nx sh_l H2), eo_setzs; tauto].
      all: cbn -[zdenp csden eb setzs rw_cells ro_cells bytes_at stk aobj Z.of_nat] in H |- *;
        repeat (apply andb_prop in H; destruct H as [H ?]); rewrite ?zdenp_setzs, ?csden_setzs, ?eb_setzs by assumption; try tauto.
    Qed.

    Lemma Forall_pf_setzs : forall vs nx pf, forallb (pfvars_lt nx) pf = true ->
      Forall (pfact_ok CS E) pf -> Forall (pfact_ok CS (setzs E nx vs)) pf.
    Proof.
      intros vs nx pf H HF. induction HF as [|f pf Hf HF IH]; [constructor|]. cbn in H. apply andb_prop in H as [H1 H2].
      constructor; [apply (pfact_ok_setzs vs nx f H1); exact Hf| apply IH; exact H2].
    Qed.

    Lemma Forall_mf_setzs : forall vs nx mm mf, forallb (mfvars_lt nx) mf = true ->
      Forall (mfact_ok segs L CS E mm) mf -> Forall (mfact_ok segs L CS (setzs E nx vs) mm) mf.
    Proof.
      intros vs nx mm mf H HF. induction HF as [|f mf Hf HF IH]; [constructor|]. cbn in H. apply andb_prop in H as [H1 H2].
      constructor; [apply (mfact_ok_setzs vs nx mm f H1); exact Hf| apply IH; exact H2].
    Qed.


    Lemma INV_setzs : forall vs nx ss m, wf_at nx ss = true -> INV segs G E ss m ->
      INV segs G (setzs E nx vs) ss m /\ ms_den segs G (setzs E nx vs) ss m = ms_den segs G E ss m.
    Proof.
      intros vs nx ss m WF (HM & HP & MU & WM & MI & SM). unfold wf_at in WF.
      apply andb_prop in WF as [WF W6]. apply andb_prop in WF as [WF W5]. apply andb_prop in WF as [WF W4].
      apply andb_prop in WF as [WF W3]. apply andb_prop in WF as [W1 W2].
      split.
      - split; [apply Forall_mf_setzs; assumption|]. split; [apply Forall_pf_setzs; assumption|].
        rewrite (wden_setzs vs nx (s_W ss) W5), refm_setzs. exact (conj MU (conj WM (conj MI SM))).
      - unfold ms_den. rewrite (regs_den_setzs vs nx _ W2), (pc_den_setzs vs nx _ W1). reflexivity.
    Qed.

    Lemma cfg_ok_setzs : forall vs nx, cfg_ok G C E ->
      match c_acc C with Some A => evars_lt nx (ac_sb A) | None => true end = true -> cfg_ok G C (setzs E nx vs).
    Proof.
      intros vs nx CFG H. unfold cfg_ok in CFG |- *. destruct (c_acc C) as [A|]; [|exact CFG].
      destruct CFG as (C1 & C2 & S1 & S2). split; [exact C1|]. split; [exact C2|]. split; [|exact S2].
      rewrite (zdenp_setzs vs nx (ac_sb A) H). exact S1.
    Qed.
  End Setzs.
  Lemma ecur_setls : forall ls E nl, ecur (setls E nl ls) = ecur E.
  Proof. induction ls as [|l ls IH]; intros E nl; cbn [setls]; [reflexivity|]. rewrite IH. reflexivity. Qed.
  Lemma ecur_env_call : forall E nx vs nl ls, ecur (env_call E nx vs nl ls) = ecur E.
  Proof. intros. unfold env_call. rewrite ecur_setls. apply ecur_setzs. Qed.
  Lemma ecur_env_law : forall E nx vs nl ls nm mc mp, ecur (env_law E nx vs nl ls nm mc mp) = ecur E.
  Proof. intros. unfold env_law. cbn [ecur env_setm]. apply ecur_env_call. Qed.
  (* [comment removed for export] *)
  Lemma sreg_eqb_eq : forall a b, sreg_eqb a b = true -> a = b.
  Proof.
    intros [i|e] [j|f] H; cbn in H; try discriminate.
    - apply Pos.eqb_eq in H. subst. reflexivity.
    - apply expr_eqb_eq in H. subst. reflexivity.
  Qed.

  Lemma cellx_eqb_eq : forall a b, cellx_eqb a b = true -> a = b.
  Proof.
    intros a; induction a as [i|w e|w k|w i|c IH o l|wr er]; intros [j|w' e'|w' k'|w' j|c' o' l'|wr' er'] H; cbn in H; try discriminate.
    - apply Pos.eqb_eq in H. subst. reflexivity.
    - apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. apply expr_eqb_eq in H2. subst. reflexivity.
    - apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. apply Pos.eqb_eq in H2. subst. reflexivity.
    - apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. apply Pos.eqb_eq in H2. subst. reflexivity.
    - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply IH in H1. apply N.eqb_eq in H2. apply N.eqb_eq in H3. subst. reflexivity.
    - apply andb_prop in H as [H1 H2]. apply N.eqb_eq in H1. apply expr_eqb_eq in H2. subst. reflexivity.
  Qed.

  Lemma cells_eqb_eq : forall xs ys, cells_eqb xs ys = true -> xs = ys.
  Proof.
    induction xs as [|x xs IH]; intros [|y ys] H; cbn in H; try discriminate; [reflexivity|].
    apply andb_prop in H as [H1 H2]. apply cellx_eqb_eq in H1. apply IH in H2. subst. reflexivity.
  Qed.

  Lemma ws_eqb_eq : forall a b, ws_eqb a b = true -> a = b.
  Proof.
    induction a as [|[l h] a IH]; intros [|[l' h'] b] H; cbn -[expr_eqb] in H; try discriminate; [reflexivity|].
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. apply IH in H3. subst. reflexivity.
  Qed.

  Lemma lexpr_eqb_eq : forall a b, lexpr_eqb a b = true -> a = b.
  Proof.
    induction a as [k|l IH i w v]; intros [k'|l' i' w' v'] H; cbn -[expr_eqb Pos.eqb N.eqb] in H; try discriminate.
    - apply Pos.eqb_eq in H. subst. reflexivity.
    - repeat (apply andb_prop in H; destruct H as [H ?]). apply IH in H. apply expr_eqb_eq in H2. apply N.eqb_eq in H1. apply expr_eqb_eq in H0.
      subst. reflexivity.
  Qed.

  Lemma bklist_eqb_eq : forall a b, bklist_eqb a b = true -> a = b.
  Proof. exact (LxSoundMem.bklist_eqb_eq). Qed.
  Lemma exprs_eqb_eq : forall a b, exprs_eqb a b = true -> a = b.
  Proof.
    induction a as [|x a IH]; intros [|y b] H; cbn -[expr_eqb] in H; try discriminate; [reflexivity|].
    apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply IH in H2. subst. reflexivity.
  Qed.
  Lemma mfact_eqb_eq : forall a b, mfact_eqb a b = true -> a = b.
  Proof.
    intros a b H. destruct a, b; cbn -[expr_eqb cells_eqb Pos.eqb ws_eqb Nat.eqb lexpr_eqb N.eqb Bool.eqb bklist_eqb exprs_eqb] in H; try discriminate;
      repeat (apply andb_prop in H; destruct H as [H ?]);
      repeat match goal with
        | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
        | H : cells_eqb _ _ = true |- _ => apply cells_eqb_eq in H
        | H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H
        | H : ws_eqb _ _ = true |- _ => apply ws_eqb_eq in H
        | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
        | H : lexpr_eqb _ _ = true |- _ => apply lexpr_eqb_eq in H
        | H : N.eqb _ _ = true |- _ => apply N.eqb_eq in H
        | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
        | H : bklist_eqb _ _ = true |- _ => apply bklist_eqb_eq in H
        | H : exprs_eqb _ _ = true |- _ => apply exprs_eqb_eq in H
        end; subst; reflexivity.
  Qed.

  Lemma mfs_eqb_eq : forall xs ys, mfs_eqb xs ys = true -> xs = ys.
  Proof.
    induction xs as [|x xs IH]; intros [|y ys] H; cbn -[mfact_eqb] in H; try discriminate; [reflexivity|].
    apply andb_prop in H as [H1 H2]. apply mfact_eqb_eq in H1. apply IH in H2. subst. reflexivity.
  Qed.

  Lemma pfact_eqb_eq : forall a b, pfact_eqb a b = true -> a = b.
  Proof.
    intros a b H. destruct a, b; cbn -[expr_eqb exprs_eqb Pos.eqb N.eqb Nat.eqb] in H; try discriminate;
      repeat (apply andb_prop in H; destruct H as [H ?]);
      repeat match goal with
        | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
        | H : exprs_eqb _ _ = true |- _ => apply exprs_eqb_eq in H
        | H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H
        | H : N.eqb _ _ = true |- _ => apply N.eqb_eq in H
        | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
        end; subst; reflexivity.
  Qed.

  Lemma pf_mem_In : forall f l, pf_mem f l = true -> In f l.
  Proof.
    intros f l. induction l as [|g l IH]; cbn -[pfact_eqb]; intros H; [discriminate|].
    apply orb_prop in H as [H|H]; [left; symmetry; apply pfact_eqb_eq; exact H| right; apply IH; exact H].
  Qed.

  Lemma pf_inter_l : forall (P : pfact -> Prop) a b, Forall P a -> Forall P (pf_inter a b).
  Proof. intros P a b H. unfold pf_inter. apply Forall_forall. intros f Hf. apply filter_In in Hf as [Hf _]. exact (proj1 (List.Forall_forall P a) H f Hf). Qed.

  Lemma pf_inter_r : forall (P : pfact -> Prop) a b, Forall P b -> Forall P (pf_inter a b).
  Proof.
    intros P a b H. unfold pf_inter. apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [_ Hf].
    apply pf_mem_In in Hf. exact (proj1 (List.Forall_forall P b) H f Hf).
  Qed.


  (* [comment removed for export] *)
  Lemma merge_regs_len : forall r1 r2 nx rs k, merge_regs r1 r2 nx = (rs, k) -> length r1 = length r2 -> length rs = length r1.
  Proof.
    induction r1 as [|a r1 IH]; intros [|b r2] nx rs k H Hl; cbn in H, Hl; try discriminate.
    - injection H; intros; subst; reflexivity.
    - destruct (sreg_eqb a b);
        [destruct (merge_regs r1 r2 nx) as [rs' k'] eqn:M| destruct (merge_regs r1 r2 (Pos.succ nx)) as [rs' k'] eqn:M];
        injection H; intros Ek Ers; subst rs; subst k; cbn; f_equal; eapply IH; eauto.
  Qed.

  Lemma fresh_fact_ok : forall E nx (w : word), ez E nx = bv_unsigned w ->
    pfact_ok CS E (FGe (eatom (EZv nx))) /\ pfact_ok CS E (FGe (eadd (ELit (two64 - 1)) (emulc (-1) (eatom (EZv nx))))).
  Proof.
    intros E nx w H. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
    split; cbn -[zdenp eatom eadd emulc two64]; rewrite zdenp_ok, ?eadd_den, ?emulc_den, eatom_den; cbn [zden]; rewrite H; [lia|].
    unfold two64. lia.
  Qed.

  Lemma merge_regs_sound : forall r1 r2 nx rs k E (sel : bool),
    merge_regs r1 r2 nx = (rs, k) -> length r1 = length r2 ->
    forallb (rvars_lt nx) r1 = true -> forallb (rvars_lt nx) r2 = true ->
    exists vs, length vs = k /\ map (rden (setzs E nx vs)) rs = map (rden E) (if sel then r1 else r2)
          /\ Forall (pfact_ok CS (setzs E nx vs)) (fresh_facts nx k).
  Proof.
    induction r1 as [|a r1 IH]; intros [|b r2] nx rs k E sel H Hl W1 W2; cbn in H, Hl; try discriminate.
    - injection H; intros; subst. exists []. split; [reflexivity|]. split; [destruct sel; reflexivity| constructor].
    - cbn in W1, W2. apply andb_prop in W1 as [Wa W1]. apply andb_prop in W2 as [Wb W2].
      destruct (sreg_eqb a b) eqn:EQ.
      + destruct (merge_regs r1 r2 nx) as [rs' k'] eqn:M. injection H; intros Ek Ers. subst rs. subst k.
        destruct (IH r2 nx rs' k' E sel M ltac:(lia) W1 W2) as (vs & Hlen & Hmap & HF).
        exists vs. split; [exact Hlen|]. split; [|exact HF].
        apply sreg_eqb_eq in EQ. subst b. destruct sel; cbn [map]; rewrite Hmap, (rden_setzs E vs nx a Wa); reflexivity.
      + destruct (merge_regs r1 r2 (Pos.succ nx)) as [rs' k'] eqn:M. injection H; intros Ek Ers. subst rs. subst k.
        set (w := rden E (if sel then a else b)).
        set (E1 := env_setz E nx (bv_unsigned w)).
        assert (W1' : forallb (rvars_lt (Pos.succ nx)) r1 = true) by (eapply forallb_mono; [|exact W1]; intros r Hr; eapply rvars_lt_mono; [|exact Hr]; lia).
        assert (W2' : forallb (rvars_lt (Pos.succ nx)) r2 = true) by (eapply forallb_mono; [|exact W2]; intros r Hr; eapply rvars_lt_mono; [|exact Hr]; lia).
        destruct (IH r2 (Pos.succ nx) rs' k' E1 sel M ltac:(lia) W1' W2') as (vs & Hlen & Hmap & HF).
        exists (bv_unsigned w :: vs). split; [cbn; lia|].
        assert (HZ : ez (setzs E nx (bv_unsigned w :: vs)) nx = bv_unsigned w) by apply ez_setzs_here.
        split.
        * cbn [map setzs]. fold E1. rewrite Hmap.
          assert (R1 : map (rden E1) (if sel then r1 else r2) = map (rden E) (if sel then r1 else r2)).
          { apply map_ext_in. intros r Hr. subst E1. apply rden_setz. destruct sel; [rewrite forallb_forall in W1; apply W1| rewrite forallb_forall in W2; apply W2]; exact Hr. }
          rewrite R1. cbn [setzs] in HZ. fold E1 in HZ.
          assert (R0 : rden (setzs E1 (Pos.succ nx) vs) (RZ (eatom (EZv nx))) = w).
          { cbn -[zdenp setzs Z_to_bv]. rewrite zdenp_ok, eatom_den. cbn [zden]. rewrite HZ. apply w64_of_unsigned. }
          rewrite R0. subst w. destruct sel; reflexivity.
        * cbn [fresh_facts]. destruct (fresh_fact_ok (setzs E nx (bv_unsigned w :: vs)) nx w HZ) as [F1 F2].
          constructor; [exact F1|]. constructor; [exact F2|]. cbn [setzs]. fold E1. exact HF.
  Qed.

  Lemma merge_sound : forall s1 s2 sm nx k E m (sel : bool),
    merge C s1 s2 = Some (sm, nx, k) -> cfg_ok G C E ->
    INV segs G E (if sel then s1 else s2) m ->
    exists vs, length vs = k /\ INV segs G (setzs E nx vs) sm m
      /\ ms_den segs G (setzs E nx vs) sm m = ms_den segs G E (if sel then s1 else s2) m
      /\ cfg_ok G C (setzs E nx vs) /\ length (s_rs sm) = 31%nat.
  Proof.
    intros s1 s2 sm nx k E m sel H CFG HI. unfold merge in H.
    destruct (ss_wf C s1) eqn:WF1; [|discriminate]. destruct (ss_wf C s2) eqn:WF2; [|discriminate].
    destruct (mfs_eqb (s_mf s1) (s_mf s2)) eqn:MF; [|discriminate]. destruct (spc_eqb (s_pc s1) (s_pc s2)) eqn:PCQ; [|discriminate].
    destruct (ws_eqb (s_W s1) (s_W s2)) eqn:WSQ; [|discriminate]. apply ws_eqb_eq in WSQ.
    destruct (Nat.eqb_spec (s_ref s1) (s_ref s2)) as [RQ|]; [|discriminate]. destruct (Nat.eqb_spec (s_nm s1) (s_nm s2)) as [NQ|]; [|discriminate].
    destruct (Pos.eqb_spec (s_nl s1) (s_nl s2)) as [NLQ|]; [|discriminate].
    destruct (bklist_eqb (s_bl s1) (s_bl s2)) eqn:BLQ; [|discriminate]. apply bklist_eqb_eq in BLQ.
    destruct (Nat.eqb_spec (length (s_rs s1)) 31) as [L1|]; [|discriminate]. destruct (Nat.eqb_spec (length (s_rs s2)) 31) as [L2|]; [|discriminate].
    cbn [andb] in H.
    destruct (merge_regs (s_rs s1) (s_rs s2) (Pos.max (s_nx s1) (s_nx s2))) as [rs k0] eqn:MR.
    injection H; intros <- <- <-.
    set (NX := Pos.max (s_nx s1) (s_nx s2)) in *.
    apply mfs_eqb_eq in MF.
    assert (PCE : s_pc s1 = s_pc s2).
    { destruct (s_pc s1), (s_pc s2); cbn in PCQ; try discriminate. apply Z.eqb_eq in PCQ. subst; reflexivity. }
    rewrite ss_wf_at in WF1, WF2.
    assert (WF1' : wf_at NX s1 = true) by (eapply wf_at_mono; [|exact WF1]; lia).
    assert (WF2' : wf_at NX s2 = true) by (eapply wf_at_mono; [|exact WF2]; lia).
    pose proof WF1' as X1. pose proof WF2' as X2. unfold wf_at in X1, X2.
    apply andb_prop in X1 as [X1 A6]. apply andb_prop in X1 as [X1 A5]. apply andb_prop in X1 as [X1 A4]. apply andb_prop in X1 as [X1 A3]. apply andb_prop in X1 as [A1 A2].
    apply andb_prop in X2 as [X2 B6]. apply andb_prop in X2 as [X2 B5]. apply andb_prop in X2 as [X2 B4]. apply andb_prop in X2 as [X2 B3]. apply andb_prop in X2 as [B1 B2].
    destruct (merge_regs_sound (s_rs s1) (s_rs s2) NX rs k0 E sel MR ltac:(lia) A2 B2) as (vs & Hlen & Hmap & HF).
    exists vs. split; [exact Hlen|].
    destruct (INV_setzs E vs NX (if sel then s1 else s2) m ltac:(destruct sel; assumption) HI) as [HI' DEN].
    destruct HI' as (HM & HP & REST).
    split; [|split; [|split; [apply cfg_ok_setzs; [exact CFG| exact A6]| cbn; rewrite (merge_regs_len _ _ _ _ _ MR ltac:(lia)); exact L1]]].
    - split; [|split].
      + cbn [s_mf]. destruct sel; [exact HM| rewrite MF; exact HM].
      + cbn [s_pf]. apply Forall_app. split; [|exact HF].
        destruct sel; [apply pf_inter_l; exact HP| apply pf_inter_r; exact HP].
      + cbn [s_W s_same]. destruct REST as (R1 & R2 & R3 & R4).
        match goal with |- context [refm ?E1 ?S1] =>
          replace (refm E1 S1) with (refm E1 (if sel then s1 else s2))
            by (unfold refm; cbn [s_ref]; destruct sel; [reflexivity| rewrite RQ; reflexivity]) end.
        split; [destruct sel; [exact R1| rewrite WSQ; exact R1]|]. split; [exact R2|]. split; [exact R3|].
        intros SS. apply andb_prop in SS as [SS1 SS2]. apply R4. destruct sel; assumption.
    - unfold ms_den. cbn [s_rs s_pc]. f_equal.
      + rewrite !regs_den_rdw, Hmap. destruct sel; reflexivity.
      + rewrite (pc_den_setzs E vs NX _ A1). destruct sel; [reflexivity|]. rewrite PCE. reflexivity.
  Qed.
  Lemma lin_run_sound : forall D fuel tgt ss ss' E m (mo : Model),
    hp_frame segs (ehp E) (ecw E) -> hp_blk (ecw E) ->
    cfg_ok G C E -> length (s_rs ss) = 31%nat -> INV segs G E ss m ->
    lin_run segs C D fuel tgt ss = Some ss' ->
    (forall m', length (s_rs ss') = 31%nat -> INV segs G E ss' m' -> TGT mo (ms_den segs G E ss' m')) ->
    TGT mo (ms_den segs G E ss m).
  Proof.
    intros D. induction fuel as [|fuel IH]; intros tgt ss ss' E m mo HPFE HBKE CFG Hlen HI H K; cbn [lin_run] in H; [discriminate|].
    destruct (s_pc ss) as [pc|r] eqn:Hpc; [|discriminate].
    destruct (Z.eqb_spec pc tgt) as [->|NE].
    { injection H; intros <-. apply K; assumption. }
    destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:HFW; [|discriminate].
    destruct (is_ecall w) eqn:HEC; [discriminate|].
    destruct (decode_any w) as [[i sz]|] eqn:HDEC; [|discriminate].
    pose proof (sym_step_sound segs G C E CFG HPFE HBKE D i sz ss pc w m Hpc Hlen HFW HEC HDEC HI) as SS.
    destruct (sym_step C D i sz ss) as [ss1|ss1|c st sf|ss1|code]; try discriminate. cbn [sres_ok] in SS.
    destruct SS as (Hlen1 & m1 & STEP & HI1). eapply TGT_mstepA; [exact STEP|].
    eapply IH; eauto.
  Qed.

  Lemma genv_ok_setz : forall E n v, genv_ok E -> forallb (evars_lt n) genv = true -> genv_ok (env_setz E n v).
  Proof.
    intros E n v [H HO] W. unfold genv_ok in *. split; [|exact HO]. revert W. induction H as [|g x l l' Hg H IH]; intros W; [constructor|].
    cbn in W. apply andb_prop in W as [W1 W2]. constructor; [rewrite zden_setz by exact W1; exact Hg| apply IH; exact W2].
  Qed.

  Lemma genv_ok_setzs : forall vs E n, genv_ok E -> forallb (evars_lt n) genv = true -> genv_ok (setzs E n vs).
  Proof.
    induction vs as [|v vs IH]; intros E n H W; cbn; [exact H|].
    apply IH; [apply genv_ok_setz; assumption|]. eapply forallb_mono; [|exact W]. intros g Hg. eapply evars_lt_mono; [|exact Hg]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma zden_setm : forall E k m e, zden (env_setm E k m) e = zden E e.
  Proof. intros E k m e. induction e; cbn; try reflexivity; try (rewrite IHe1, IHe2; reflexivity); try (rewrite IHe; reflexivity). Qed.
  Lemma genv_ok_setm : forall E k m, genv_ok E -> genv_ok (env_setm E k m).
  Proof.
    intros E k m [H HO]. unfold genv_ok in *. split; [|exact HO].
    eapply Forall2_impl; [|exact H]. intros g v Hg. rewrite zden_setm. exact Hg.
  Qed.
  Lemma cfg_ok_setm : forall E k m, cfg_ok G C E -> cfg_ok G C (env_setm E k m).
  Proof.
    intros E k m CFG. unfold cfg_ok in CFG |- *. destruct (c_acc C) as [A|]; [|exact CFG].
    destruct CFG as (C1 & C2 & S1 & S2). split; [exact C1|]. split; [exact C2|]. split; [|exact S2].
    rewrite !zdenp_ok in S1 |- *. rewrite zden_setm. exact S1.
  Qed.
  Lemma zden_setls : forall ls E nl e, zden (setls E nl ls) e = zden E e.
  Proof. induction ls as [|l ls IH]; intros E nl e; cbn; [reflexivity|]. rewrite IH. apply zden_setl. Qed.
  Lemma genv_ok_setls : forall ls E nl, genv_ok E -> genv_ok (setls E nl ls).
  Proof.
    induction ls as [|l ls IH]; intros E nl GVx; cbn; [exact GVx|]. apply IH.
    destruct GVx as [H HO]. unfold genv_ok. split; [|exact HO]. eapply Forall2_impl; [|exact H]. intros g v Hg. rewrite zden_setl. exact Hg.
  Qed.
  Lemma cfg_ok_setls : forall ls E nl, cfg_ok G C E -> cfg_ok G C (setls E nl ls).
  Proof.
    induction ls as [|l ls IH]; intros E nl CFG; cbn; [exact CFG|]. apply IH.
    unfold cfg_ok in CFG |- *. destruct (c_acc C) as [A|]; [|exact CFG].
    destruct CFG as (C1 & C2 & S1 & S2). split; [exact C1|]. split; [exact C2|]. split; [|exact S2].
    rewrite !zdenp_ok in S1 |- *. rewrite zden_setl. exact S1.
  Qed.
  Lemma genv_ok_call : forall E nx vs nl ls, genv_ok E -> forallb (evars_lt nx) genv = true -> genv_ok (env_call E nx vs nl ls).
  Proof. intros. unfold env_call. apply genv_ok_setls, genv_ok_setzs; assumption. Qed.
  Lemma genv_ok_law : forall E nx vs nl ls nm mc mp, genv_ok E -> forallb (evars_lt nx) genv = true -> genv_ok (env_law E nx vs nl ls nm mc mp).
  Proof. intros. unfold env_law. apply genv_ok_setm, genv_ok_setm, genv_ok_call; assumption. Qed.
  Lemma zden_setcur : forall E mo e, zden (env_setcur E mo) e = zden E e.
  Proof. intros E mo e. induction e; cbn; try reflexivity; try (rewrite IHe1, IHe2; reflexivity); try (rewrite IHe; reflexivity). Qed.
  Lemma genv_ok_setcur : forall E mo, genv_ok E -> genv_ok (env_setcur E mo).
  Proof.
    intros E mo [H HO]. unfold genv_ok in *. split; [|exact HO].
    eapply Forall2_impl; [|exact H]. intros g v Hg. rewrite zden_setcur. exact Hg.
  Qed.
  Lemma zden_setbl : forall E k lb e, zden (env_setbl E k lb) e = zden E e.
  Proof. intros E k lb e. induction e; cbn; try reflexivity; try (rewrite IHe1, IHe2; reflexivity); try (rewrite IHe; reflexivity). Qed.
  Lemma genv_ok_setbl : forall E k lb, genv_ok E -> genv_ok (env_setbl E k lb).
  Proof.
    intros E k lb [H HO]. unfold genv_ok in *. split; [|exact HO].
    eapply Forall2_impl; [|exact H]. intros g v Hg. rewrite zden_setbl. exact Hg.
  Qed.
  Lemma cfg_ok_setbl : forall E k lb, cfg_ok G C E -> cfg_ok G C (env_setbl E k lb).
  Proof.
    intros E k lb CFG. unfold cfg_ok in CFG |- *. destruct (c_acc C) as [A|]; [|exact CFG].
    destruct CFG as (C1 & C2 & S1 & S2). split; [exact C1|]. split; [exact C2|]. split; [|exact S2].
    rewrite !zdenp_ok in S1 |- *. rewrite zden_setbl. exact S1.
  Qed.
  Lemma cfg_ok_setcur : forall E mo, cfg_ok G C E -> cfg_ok G C (env_setcur E mo).
  Proof.
    intros E mo CFG. unfold cfg_ok in CFG |- *. destruct (c_acc C) as [A|]; [|exact CFG].
    destruct CFG as (C1 & C2 & S1 & S2). split; [exact C1|]. split; [exact C2|]. split; [|exact S2].
    rewrite !zdenp_ok in S1 |- *. rewrite zden_setcur. exact S1.
  Qed.
  Lemma genv_ok_heap : forall E nx vs nl ls nm mc mp mo lb, genv_ok E -> forallb (evars_lt nx) genv = true -> genv_ok (env_heap E nx vs nl ls nm mc mp mo lb).
  Proof. intros. unfold env_heap. apply genv_ok_setbl, genv_ok_setcur, genv_ok_law; assumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Inductive akind : Set := AkOk | AkLaw | AkHeap (oss2 : option sstate).
  Definition sum_answer (a : akind) (k kl : nat) (ss' : sstate) : sumres :=
    match a with AkOk => SumOk k kl ss' | AkLaw => SumOkL k kl ss' | AkHeap o => SumOkM k kl ss' o end.
  (* [comment removed for export] *)
  Definition heap_kont (E : env) (ss : sstate) (k kl : nat) (ss' : sstate) : Prop :=
    forall vs ls mc mp mo lb m', length vs = k -> length ls = kl -> length (s_rs ss') = 31%nat -> s_nm ss' = S (S (s_nm ss)) ->
      INV segs G (env_heap E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp mo lb) ss' m' ->
      TGT mo (ms_den segs G (env_heap E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp mo lb) ss' m').
  Definition summary_at (su : summary) : Prop :=
    forall E ss m,
      genv_ok E ->
      cfg_ok G C E -> length (s_rs ss) = 31%nat -> ss_wf C ss = true -> INV segs G E ss m ->
      forall (a : akind) k kl ss', apply_summary C genv su ss = sum_answer a k kl ss' ->
         match a with
         | AkLaw => evtA segs L CS (fun ms' =>
                                      exists vs ls mc mp m', length vs = k /\ length ls = kl /\ length (s_rs ss') = 31%nat
                                        /\ s_nm ss' = S (S (s_nm ss))
                                        /\ ms' = ms_den segs G (env_law E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp) ss' m'
                                        /\ INV segs G (env_law E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp) ss' m') (ms_den segs G E ss m)
         | AkOk => evtA segs L CS (fun ms' =>
                                      exists vs ls m', length vs = k /\ length ls = kl /\ length (s_rs ss') = 31%nat
                                        /\ ms' = ms_den segs G (env_call E (s_nx ss) vs (s_nl ss) ls) ss' m'
                                        /\ INV segs G (env_call E (s_nx ss) vs (s_nl ss) ls) ss' m') (ms_den segs G E ss m)
         | AkHeap oss2 =>
             heap_kont E ss k kl ss' ->
             match oss2 with Some ss2 => heap_kont E ss k kl ss2 | None => True end ->
             TGT (ecur E) (ms_den segs G E ss m)
         end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Agree.
    Variable n : positive.
    Variable nl : positive.    (* [comment removed for export] *)
    Variables E1 E2 : env.
    (* [comment removed for export] *)
    Definition agree : Prop := (forall i, (i < n)%positive -> ez E1 i = ez E2 i) /\ ewl E1 = ewl E2 /\ ebl E1 = ebl E2 /\ eol E1 = eol E2
                               /\ (forall i, (i < nl)%positive -> el E1 i = el E2 i) /\ em E1 0 = em E2 0 /\ elw E1 = elw E2
                               /\ epr E1 = epr E2 /\ elb0 E1 = elb0 E2 /\ ehp E1 = ehp E2 /\ ecw E1 = ecw E2 /\ elh E1 = elh E2
                               /\ (ecur E1, elbl E1, ehr E1) = (ecur E2, elbl E2, ehr E2).   (* [comment removed for export] *)
    Hypothesis AG : agree.

    Lemma ew_agree : forall i, ew E1 i = ew E2 i.
    Proof. intros i. unfold ew. rewrite (proj1 (proj2 AG)). reflexivity. Qed.
    Lemma eb_agree : forall i, eb E1 i = eb E2 i.
    Proof. intros i. unfold eb. rewrite (proj1 (proj2 (proj2 AG))). reflexivity. Qed.
    Lemma eo_agree : forall k, eo E1 k = eo E2 k.
    Proof. intros k. unfold eo. rewrite (proj1 (proj2 (proj2 (proj2 AG)))). reflexivity. Qed.
    Lemma el_agree : forall k, (k < nl)%positive -> el E1 k = el E2 k.
    Proof. intros k Hk. exact (proj1 (proj2 (proj2 (proj2 (proj2 AG)))) k Hk). Qed.
    Lemma em0_agree : em E1 0 = em E2 0.
    Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 AG)))))). Qed.
    Lemma elaw_agree : forall l, elaw E1 l = elaw E2 l.
    Proof. intros l. unfold elaw. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AG))))))). reflexivity. Qed.
    Lemma epr_agree : epr E1 = epr E2.
    Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AG)))))))). Qed.
    Lemma elb0_agree : elb0 E1 = elb0 E2.
    Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AG))))))))). Qed.
    Lemma ehp_agree : ehp E1 = ehp E2.
    Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AG)))))))))). Qed.
    Lemma ecw_agree : ecw E1 = ecw E2.
    Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AG))))))))))). Qed.
    Lemma elh_agree : elh E1 = elh E2.
    Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AG)))))))))))). Qed.
    Lemma ehlaw_agree : forall l, ehlaw E1 l = ehlaw E2 l.
    Proof. intros l. unfold ehlaw. rewrite elh_agree. reflexivity. Qed.
    Lemma ecur_agree : ecur E1 = ecur E2.
    Proof. pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AG)))))))))))) as X. injection X. auto. Qed.
    Lemma elbl_agree : elbl E1 = elbl E2.
    Proof. pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AG)))))))))))) as X. injection X. auto. Qed.
    Lemma ehr_agree : ehr E1 = ehr E2.
    Proof. pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AG)))))))))))) as X. injection X. auto. Qed.
    Lemma refm_agree : forall ss, s_ref ss = 0%nat -> refm E1 ss = refm E2 ss.
    Proof. intros ss H. unfold refm. rewrite H. apply em0_agree. Qed.

    Lemma zden_agree : forall e, evars_lt n e = true -> zden E1 e = zden E2 e.
    Proof.
      induction e as [z|i|i|a IHa b IHb|c a IHa|o a IHa b IHb]; cbn -[Pos.ltb ez ew]; intros H; try reflexivity.
      - apply (proj1 AG). apply Pos.ltb_lt. exact H.
      - rewrite ew_agree. reflexivity.
      - apply andb_prop in H as [H1 H2]. rewrite IHa, IHb by assumption. reflexivity.
      - rewrite IHa by assumption. reflexivity.
      - apply andb_prop in H as [H1 H2]. rewrite IHa, IHb by assumption. reflexivity.
    Qed.
    Lemma zdenp_agree : forall e, evars_lt n e = true -> zdenp E1 e = zdenp E2 e.
    Proof. intros. rewrite !zdenp_ok. apply zden_agree. assumption. Qed.
    Lemma rden_agree : forall r, rvars_lt n r = true -> rden E1 r = rden E2 r.
    Proof. intros [i|e] H; cbn -[zdenp ew]; [apply ew_agree|]. rewrite zdenp_agree by exact H. reflexivity. Qed.
    Lemma regs_den_agree : forall rs, forallb (rvars_lt n) rs = true -> regs_den E1 rs = regs_den E2 rs.
    Proof.
      intros rs H. rewrite !regs_den_rdw. f_equal. apply map_ext_in. intros r Hr. apply rden_agree.
      rewrite forallb_forall in H. apply H. exact Hr.
    Qed.
    Lemma pc_den_agree : forall p, pcvars_lt n p = true -> pc_den E1 p = pc_den E2 p.
    Proof. intros [z|r] H; cbn -[rden Z_to_bv ret_pc]; [reflexivity|]. rewrite rden_agree by exact H. reflexivity. Qed.
    Lemma cden_agree : forall c, cvars_lt n c = true -> cden E1 c = cden E2 c.
    Proof.
      induction c as [i|w e|w k|w i|c IH o l|wr er]; intros H; cbn -[zdenp N.to_nat ew eb cden]; cbn [cden]; rewrite ?ew_agree, ?eb_agree; try reflexivity.
      - cbn in H. rewrite !zdenp_agree by exact H. reflexivity.
      - cbn in H. fold (cden E1 c) (cden E2 c). rewrite (IH H). reflexivity.
      - cbn in H. rewrite !zdenp_agree by exact H. reflexivity.
    Qed.
    Lemma csden_agree : forall cs, forallb (cvars_lt n) cs = true -> csden E1 cs = csden E2 cs.
    Proof.
      intros cs H. unfold csden. induction cs as [|c cs IH]; [reflexivity|]. cbn in H. apply andb_prop in H as [H1 H2].
      cbn. rewrite cden_agree, IH by assumption. reflexivity.
    Qed.
    Lemma zdenps_agree : forall xs, forallb (evars_lt n) xs = true -> map (zdenp E1) xs = map (zdenp E2) xs.
    Proof.
      induction xs as [|x xs IH]; cbn -[zdenp evars_lt]; intros H; [reflexivity|].
      apply andb_prop in H as [H1 H2]. rewrite zdenp_agree, IH by assumption. reflexivity.
    Qed.
    Lemma pfact_ok_agree : forall f, pfvars_lt n f = true -> pfact_ok CS E1 f <-> pfact_ok CS E2 f.
    Proof.
      intros f H.
      destruct f as [| | | | | | | | | | |pj pxs]; [| | | | | | | | | | | unfold pfact_ok, eprop; rewrite epr_agree; cbn [pfvars_lt] in H; rewrite (zdenps_agree pxs H); tauto].
      all: cbn -[zdenp Z.pow Z.of_N ez] in H |- *;
        repeat (apply andb_prop in H; destruct H as [H ?]); rewrite ?zdenp_agree by assumption; try tauto.
      rewrite !(proj1 AG k) by (apply Pos.ltb_lt in H; lia). tauto.
    Qed.
    Lemma wden_agree : forall W, forallb (fun lh => evars_lt n (fst lh) && evars_lt n (snd lh)) W = true -> wden E1 W = wden E2 W.
    Proof.
      intros W H. unfold wden. induction W as [|[l h] W IH]; [reflexivity|]. cbn in H.
      apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [Hl Hh]. cbn. rewrite !zdenp_agree, IH by assumption. reflexivity.
    Qed.
    Lemma ldenw_agree : forall l, lvars_lt n l = true -> llvars_lt nl l = true -> ldenw E1 l = ldenw E2 l.
    Proof.
      induction l as [k|l IH i w e]; intros H HL; cbn -[zdenp el Pos.ltb] in H, HL |- *; [apply el_agree; apply Pos.ltb_lt; exact HL|].
      repeat (apply andb_prop in H; destruct H as [H ?]). rewrite IH, !zdenp_agree by assumption. try (rewrite (zdenp_agree e) by assumption). reflexivity.
    Qed.
    Lemma ldenb_agree : forall l, lvars_lt n l = true -> llvars_lt nl l = true -> ldenb E1 l = ldenb E2 l.
    Proof.
      induction l as [k|l IH i w e]; intros H HL; cbn -[zdenp wbytes upd_bytes eb Pos.ltb] in H, HL |- *; [apply eb_agree|].
      repeat (apply andb_prop in H; destruct H as [H ?]). rewrite IH, !zdenp_agree by assumption. try (rewrite (zdenp_agree e) by assumption). reflexivity.
    Qed.
    Lemma blden_agree : forall bl, blvars_lt n bl = true -> blden E1 bl = blden E2 bl.
    Proof.
      induction bl as [|a k bl IH|kv]; cbn -[zdenp evars_lt]; intros H; [exact elb0_agree| | unfold eblv; rewrite elbl_agree; reflexivity].
      apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. rewrite !zdenp_agree, IH by assumption. reflexivity.
    Qed.
    Lemma mfact_ok_agree : forall mm f, mfvars_lt n f = true -> mrefs_lt 1 f = true -> mflvars_lt nl f = true -> mfact_ok segs L CS E1 mm f <-> mfact_ok segs L CS E2 mm f.
    Proof.
      intros mm f H MR ML. destruct f as [fa fcs|fa fcs|fa fn fk|flo fhi|foa fon|ok_k ok_l sh_l|ra_ rw_ rl_ rn_ rwr_|mW mi mj|mi mj|ml mX mi mj|ml ma mn|ml ma mn|qbl qok|ql qbl qsp qX qi qj|ql qs qa qn|qa qn qbl|ql qk|qj qo qn qxs qok].
      7:{ cbn [mfvars_lt] in H. cbn [mflvars_lt] in ML. repeat (apply andb_prop in H; destruct H as [H ?]).
          cbn [mfact_ok]. rewrite !zdenp_agree, ?ldenw_agree, ?ldenb_agree by assumption. try (rewrite (zdenp_agree rn_) by assumption). tauto. }
      (* [comment removed for export] *)
      7:{ cbn [mfvars_lt] in H. cbn [mrefs_lt] in MR. apply andb_prop in MR as [M1 M2]. apply Nat.ltb_lt in M1. apply Nat.ltb_lt in M2.
          replace mi with 0%nat by lia. replace mj with 0%nat by lia.
          cbn [mfact_ok]. rewrite (wden_agree mW H), !em0_agree. tauto. }
      7:{ cbn [mrefs_lt] in MR. apply andb_prop in MR as [M1 M2]. apply Nat.ltb_lt in M1. apply Nat.ltb_lt in M2.
          replace mi with 0%nat by lia. replace mj with 0%nat by lia. cbn [mfact_ok]. rewrite !em0_agree. tauto. }
      7:{ cbn [mfvars_lt] in H. cbn [mrefs_lt] in MR. apply andb_prop in MR as [M1 M2]. apply Nat.ltb_lt in M1. apply Nat.ltb_lt in M2.
          replace mi with 0%nat by lia. replace mj with 0%nat by lia.
          cbn [mfact_ok]. rewrite (wden_agree mX H), !em0_agree, elaw_agree. tauto. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H1 H2]. cbn [mfact_ok]. rewrite !zdenp_agree by assumption. rewrite elaw_agree. tauto. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H1 H2]. cbn [mfact_ok]. rewrite !zdenp_agree by assumption. rewrite elaw_agree. tauto. }
      (* [comment removed for export] *)
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H1 H2].
          apply mheap_ok_ext; [exact (blden_agree qbl H1)| exact (wden_agree qok H2)| apply ehp_agree| apply ecw_agree| apply elb0_agree| apply elh_agree| apply ecur_agree]. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
          cbn [mrefs_lt] in MR. apply andb_prop in MR as [MR M3]. apply andb_prop in MR as [M1 M2]. apply Nat.ltb_lt in M1. apply Nat.ltb_lt in M2.
          replace qi with 0%nat by lia. replace qj with 0%nat by lia.
          cbn [mfact_ok]. rewrite (blden_agree qbl H1), (zdenp_agree qsp H2), (wden_agree qX H3), !em0_agree, ehlaw_agree. tauto. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. cbn [mfact_ok]. rewrite !zdenp_agree by assumption. rewrite ehlaw_agree.
          unfold hlawcli. rewrite elb0_agree. tauto. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. cbn [mfact_ok].
          rewrite !zdenp_agree, (blden_agree qbl H3) by assumption. tauto. }
      7:{ cbn [mfact_ok]. rewrite ehlaw_agree, eo_agree. unfold hlawopq. rewrite elb0_agree. tauto. }
      7:{ cbn [mfvars_lt] in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. cbn [mfact_ok].
          rewrite (blden_agree qo H1), (blden_agree qn H2), (wden_agree qok H4).
          rewrite (map_ext_in (zdenp E1) (zdenp E2) qxs) by (intros e He; apply zdenp_agree; rewrite forallb_forall in H3; auto).
          unfold ehres. rewrite ecw_agree, elb0_agree, ehr_agree. tauto. }
      all: try solve [cbn [mfvars_lt] in H; rewrite forallb_app in H; apply andb_prop in H as [H1 H2];
                   cbn [mfact_ok]; rewrite (wden_agree ok_l H1), (wden_agree sh_l H2), eo_agree; tauto].
      all: cbn -[zdenp csden eb rw_cells ro_cells bytes_at stk aobj Z.of_nat] in H |- *;
        repeat (apply andb_prop in H; destruct H as [H ?]); rewrite ?zdenp_agree, ?csden_agree, ?eb_agree by assumption; try tauto.
    Qed.
    Lemma INV_agree : forall ss m, wf_at n ss = true -> mrefs_ok ss = true -> lrefs_ok nl ss = true -> INV segs G E1 ss m ->
      INV segs G E2 ss m /\ ms_den segs G E2 ss m = ms_den segs G E1 ss m.
    Proof.
      intros ss m WF MR ML (HM & HP & MU & WM & MI & SM). unfold wf_at in WF. unfold mrefs_ok in MR. apply andb_prop in MR as [MR0 MRF]. apply Nat.eqb_eq in MR0.
      unfold lrefs_ok in ML. apply andb_prop in ML as [_ MLF].
      apply andb_prop in WF as [WF W6]. apply andb_prop in WF as [WF W5]. apply andb_prop in WF as [WF W4].
      apply andb_prop in WF as [WF W3]. apply andb_prop in WF as [W1 W2].
      split.
      - split. { apply List.Forall_forall. intros f Hf. apply (mfact_ok_agree m f). { rewrite forallb_forall in W3. apply W3. exact Hf. } { rewrite forallb_forall in MRF. apply MRF. exact Hf. } { rewrite forallb_forall in MLF. apply MLF. exact Hf. } rewrite List.Forall_forall in HM. apply HM. exact Hf. }
        split. { apply List.Forall_forall. intros f Hf. apply (pfact_ok_agree f). { rewrite forallb_forall in W4. apply W4. exact Hf. } rewrite List.Forall_forall in HP. apply HP. exact Hf. }
        rewrite <- (wden_agree (s_W ss) W5), <- (refm_agree ss MR0). exact (conj MU (conj WM (conj MI SM))).
      - unfold ms_den. rewrite (regs_den_agree _ W2), (pc_den_agree _ W1). reflexivity.
    Qed.
    Lemma st_ok_agree : forall ss ms, wf_at n ss = true -> mrefs_ok ss = true -> lrefs_ok nl ss = true -> st_ok segs G E1 ss ms -> st_ok segs G E2 ss ms.
    Proof.
      intros ss ms WF MR ML ST. apply (st_ok_INV segs G) in ST as (m & -> & HI). destruct (INV_agree ss m WF MR ML HI) as [HI' DEN].
      apply st_ok_INV. exists m. split; [symmetry; exact DEN| exact HI'].
    Qed.
    Lemma cfg_ok_agree : cfg_ok G C E1 ->
      match c_acc C with Some A => evars_lt n (ac_sb A) | None => true end = true -> cfg_ok G C E2.
    Proof.
      intros CFG H. unfold cfg_ok in CFG |- *. destruct (c_acc C) as [A|]; [|exact CFG].
      destruct CFG as (C1 & C2 & S1 & S2). split; [exact C1|]. split; [exact C2|]. split; [|exact S2].
      rewrite <- (zdenp_agree (ac_sb A) H). exact S1.
    Qed.
    Lemma genv_ok_agree : genv_ok E1 -> forallb (evars_lt n) genv = true -> genv_ok E2.
    Proof.
      intros [H HO] W. unfold genv_ok in *. split; [| rewrite <- (proj1 (proj2 (proj2 (proj2 AG)))), <- (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AG))))))), <- epr_agree, <- elb0_agree, <- ehp_agree, <- ecw_agree, <- elh_agree, <- ehr_agree; exact HO].
      revert W. induction H as [|g x l l' Hg H IH]; intros W; [constructor|].
      cbn in W. apply andb_prop in W as [W1 W2]. constructor; [rewrite <- (zden_agree g W1); exact Hg| apply IH; exact W2].
    Qed.
  End Agree.

  Lemma agree_refl : forall n nl E, agree n nl E E.
  Proof. intros. unfold agree. refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))))))))))); intros; reflexivity. Qed.
  Lemma agree_sym : forall n nl E1 E2, agree n nl E1 E2 -> agree n nl E2 E1.
  Proof.
    intros n nl E1 E2 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13). unfold agree.
    refine (conj _ (conj (eq_sym A2) (conj (eq_sym A3) (conj (eq_sym A4) (conj _ (conj (eq_sym A6) (conj (eq_sym A7) (conj (eq_sym A8) (conj (eq_sym A9) (conj (eq_sym A10) (conj (eq_sym A11) (conj (eq_sym A12) (eq_sym A13)))))))))))));
      intros i Hi; symmetry; [apply A1| apply A5]; exact Hi.
  Qed.
  Lemma agree_trans : forall n nl E1 E2 E3, agree n nl E1 E2 -> agree n nl E2 E3 -> agree n nl E1 E3.
  Proof.
    intros n nl E1 E2 E3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13). unfold agree.
    refine (conj _ (conj (eq_trans A2 B2) (conj (eq_trans A3 B3) (conj (eq_trans A4 B4) (conj _ (conj (eq_trans A6 B6) (conj (eq_trans A7 B7) (conj (eq_trans A8 B8) (conj (eq_trans A9 B9) (conj (eq_trans A10 B10) (conj (eq_trans A11 B11) (conj (eq_trans A12 B12) (eq_trans A13 B13)))))))))))));
      intros i Hi; [rewrite (A1 i Hi); apply B1| rewrite (A5 i Hi); apply B5]; exact Hi.
  Qed.
  Lemma agree_mono : forall n nl n' E1 E2, agree n nl E1 E2 -> (n' <= n)%positive -> agree n' nl E1 E2.
  Proof.
    intros n nl n' E1 E2 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13) Hn. unfold agree.
    refine (conj _ (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 (conj A11 (conj A12 A13)))))))))))). intros i Hi; apply A1; lia.
  Qed.
  Lemma agree_setz_hi : forall n nl E i v, (n <= i)%positive -> agree n nl E (env_setz E i v).
  Proof.
    intros n nl E i v Hi. unfold agree. refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))))))))))); [|intros; reflexivity].
    intros j Hj. rewrite ez_setz. destruct (Pos.eqb_spec j i); [lia| reflexivity].
  Qed.
  Lemma agree_setzs_hi : forall vs n nl E i, (n <= i)%positive -> agree n nl E (setzs E i vs).
  Proof.
    induction vs as [|v vs IH]; intros n nl E i Hi; cbn; [apply agree_refl|].
    eapply agree_trans; [apply (agree_setz_hi n nl E i v Hi)| apply IH; lia].
  Qed.
  Lemma agree_setl_hi : forall n nl E i l, (nl <= i)%positive -> agree n nl E (env_setl E i l).
  Proof.
    intros n nl E i l Hi. unfold agree. refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))))))))))); [intros; reflexivity|].
    intros j Hj. rewrite el_setl. destruct (Pos.eqb_spec j i); [lia| reflexivity].
  Qed.
  Lemma agree_setls_hi : forall ls n nl E i, (nl <= i)%positive -> agree n nl E (setls E i ls).
  Proof.
    induction ls as [|l ls IH]; intros n nl E i Hi; cbn; [apply agree_refl|].
    eapply agree_trans; [apply (agree_setl_hi n nl E i l Hi)| apply IH; lia].
  Qed.
  Lemma agree_call : forall n nl E nx vs nl1 ls, (n <= nx)%positive -> (nl <= nl1)%positive -> agree n nl E (env_call E nx vs nl1 ls).
  Proof.
    intros n nl E nx vs nl1 ls Hn Hl. unfold env_call.
    eapply agree_trans; [apply agree_setzs_hi; exact Hn| apply agree_setls_hi; exact Hl].
  Qed.
  Lemma agree_setz_both : forall n nl E1 E2 v, agree n nl E1 E2 -> agree (Pos.succ n) nl (env_setz E1 n v) (env_setz E2 n v).
  Proof.
    intros n nl E1 E2 v (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13). unfold agree.
    refine (conj _ (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 (conj A11 (conj A12 A13)))))))))))). intros i Hi. rewrite !ez_setz.
    destruct (Pos.eqb_spec i n); [reflexivity|]. apply A1. lia.
  Qed.
  Lemma agree_setzs_both : forall vs n nl E1 E2, agree n nl E1 E2 -> agree (paddn n (length vs)) nl (setzs E1 n vs) (setzs E2 n vs).
  Proof.
    induction vs as [|v vs IH]; intros n nl E1 E2 AG; cbn [setzs length paddn]; [exact AG|].
    apply IH. apply agree_setz_both. exact AG.
  Qed.
  Lemma agree_setm_hi : forall n nl E k m, k <> 0%nat -> agree n nl E (env_setm E k m).
  Proof.
    intros n nl E k m Hk. unfold agree. refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))))))))))); [intros; reflexivity| intros; reflexivity|].
    rewrite em_setm. destruct (Nat.eqb_spec 0 k); [lia| reflexivity].
  Qed.
  Lemma agree_law : forall n nl E nx vs nl1 ls nm mc mp, (n <= nx)%positive -> (nl <= nl1)%positive -> nm <> 0%nat ->
    agree n nl E (env_law E nx vs nl1 ls nm mc mp).
  Proof.
    intros n nl E nx vs nl1 ls nm mc mp Hn Hl Hnm. unfold env_law.
    eapply agree_trans; [apply agree_call; [exact Hn| exact Hl]|].
    eapply agree_trans; [apply agree_setm_hi; exact Hnm| apply agree_setm_hi; lia].
  Qed.

  Lemma paddn_ge : forall k n, (n <= paddn n k)%positive.
  Proof. induction k as [|k IH]; intros n; cbn; [lia|]. specialize (IH (Pos.succ n)). lia. Qed.
  Lemma paddn_gt : forall k n, (n < paddn (Pos.succ n) k)%positive.
  Proof. intros k n. pose proof (paddn_ge k (Pos.succ n)). lia. Qed.

  Hypothesis SUMS : Forall summary_at (p_sums pl).

  Lemma sums_at_ok : forall l pc, Forall summary_at l -> Forall summary_at (sums_at l pc).
  Proof.
    induction l as [|x l IH]; intros pc HF; cbn; [constructor|].
    inversion HF; subst. destruct (Z.eqb (su_pc x) pc); [constructor; [assumption|]|]; apply IH; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma apply_sums_ok : forall l E ss m k kl ss',
    Forall summary_at l -> genv_ok E ->
    cfg_ok G C E -> length (s_rs ss) = 31%nat -> ss_wf C ss = true -> INV segs G E ss m ->
    apply_sums C genv l ss = SumOk k kl ss' ->
    evtA segs L CS (fun ms' => exists vs ls m', length vs = k /\ length ls = kl /\ length (s_rs ss') = 31%nat
                               /\ ms' = ms_den segs G (env_call E (s_nx ss) vs (s_nl ss) ls) ss' m'
                               /\ INV segs G (env_call E (s_nx ss) vs (s_nl ss) ls) ss' m') (ms_den segs G E ss m).
  Proof.
    induction l as [|su l IH]; intros E ss m k kl ss' HF GV CFG Hlen WF HI H; cbn [apply_sums] in H; [discriminate|].
    inversion HF as [|su' l' SOK HF']; subst su' l'.
    destruct l as [|su2 l2].
    - exact (SOK E ss m GV CFG Hlen WF HI AkOk k kl ss' H).
    - destruct (apply_summary C genv su ss) as [k1 kl1 ss1|k1 kl1 ss1|k1 kl1 ss1 oss2|code] eqn:AP.
      + injection H; intros <- <- <-. exact (SOK E ss m GV CFG Hlen WF HI AkOk k1 kl1 ss1 AP).
      + discriminate.
      + discriminate.
      + exact (IH E ss m k kl ss' HF' GV CFG Hlen WF HI H).
  Qed.

  (* [comment removed for export] *)
  Lemma apply_sums_okL : forall l E ss m k kl ss',
    Forall summary_at l -> genv_ok E ->
    cfg_ok G C E -> length (s_rs ss) = 31%nat -> ss_wf C ss = true -> INV segs G E ss m ->
    apply_sums C genv l ss = SumOkL k kl ss' ->
    evtA segs L CS (fun ms' => exists vs ls mc mp m', length vs = k /\ length ls = kl /\ length (s_rs ss') = 31%nat
                               /\ s_nm ss' = S (S (s_nm ss))
                               /\ ms' = ms_den segs G (env_law E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp) ss' m'
                               /\ INV segs G (env_law E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp) ss' m') (ms_den segs G E ss m).
  Proof.
    induction l as [|su l IH]; intros E ss m k kl ss' HF GV CFG Hlen WF HI H; cbn [apply_sums] in H; [discriminate|].
    inversion HF as [|su' l' SOK HF']; subst su' l'.
    destruct l as [|su2 l2].
    - exact (SOK E ss m GV CFG Hlen WF HI AkLaw k kl ss' H).
    - destruct (apply_summary C genv su ss) as [k1 kl1 ss1|k1 kl1 ss1|k1 kl1 ss1 oss2|code] eqn:AP.
      + discriminate.
      + injection H; intros <- <- <-. exact (SOK E ss m GV CFG Hlen WF HI AkLaw k1 kl1 ss1 AP).
      + discriminate.
      + exact (IH E ss m k kl ss' HF' GV CFG Hlen WF HI H).
  Qed.

  (* [comment removed for export] *)
  Lemma apply_sums_okM : forall l E ss m k kl ss1 oss2,
    Forall summary_at l -> genv_ok E ->
    cfg_ok G C E -> length (s_rs ss) = 31%nat -> ss_wf C ss = true -> INV segs G E ss m ->
    apply_sums C genv l ss = SumOkM k kl ss1 oss2 ->
    heap_kont E ss k kl ss1 -> match oss2 with Some ss2 => heap_kont E ss k kl ss2 | None => True end ->
    TGT (ecur E) (ms_den segs G E ss m).
  Proof.
    induction l as [|su l IH]; intros E ss m k kl ss1 oss2 HF GV CFG Hlen WF HI H; cbn [apply_sums] in H; [discriminate|].
    inversion HF as [|su' l' SOK HF']; subst su' l'.
    destruct l as [|su2 l2].
    - exact (SOK E ss m GV CFG Hlen WF HI (AkHeap oss2) k kl ss1 H).
    - destruct (apply_summary C genv su ss) as [k1 kl1 ss1'|k1 kl1 ss1'|k1 kl1 ss1' oss2'|code] eqn:AP.
      + discriminate.
      + discriminate.
      + injection H; intros <- <- <- <-. exact (SOK E ss m GV CFG Hlen WF HI (AkHeap oss2') k1 kl1 ss1' AP).
      + exact (IH E ss m k kl ss1 oss2 HF' GV CFG Hlen WF HI H).
  Qed.

  (* [comment removed for export] *)
  Lemma apply_summary_genv : forall su ss k kl ss', apply_summary C genv su ss = SumOk k kl ss' -> forallb (evars_lt (s_nx ss)) genv = true.
  Proof.
    intros su ss k kl ss' H. unfold apply_summary in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:X; [|discriminate] end.
    apply andb_prop in X as [_ X]. exact X.
  Qed.

  Lemma apply_summary_genvL : forall su ss k kl ss', apply_summary C genv su ss = SumOkL k kl ss' -> forallb (evars_lt (s_nx ss)) genv = true.
  Proof.
    intros su ss k kl ss' H. unfold apply_summary in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:X; [|discriminate] end.
    apply andb_prop in X as [_ X]. exact X.
  Qed.

  Lemma apply_sums_genv : forall l ss k kl ss', apply_sums C genv l ss = SumOk k kl ss' -> forallb (evars_lt (s_nx ss)) genv = true.
  Proof.
    induction l as [|su l IH]; intros ss k kl ss' H; cbn [apply_sums] in H; [discriminate|].
    destruct l as [|su2 l2]; [eapply apply_summary_genv; exact H|].
    destruct (apply_summary C genv su ss) as [k1 kl1 ss1|k1 kl1 ss1|k1 kl1 ss1 oss2|code] eqn:AP; [eapply apply_summary_genv; exact AP| discriminate| discriminate| eapply IH; exact H].
  Qed.

  Lemma apply_summary0_nm : forall su ss k kl ss', apply_summary0 C genv su ss = SumOkL k kl ss' -> s_nm ss <> 0%nat.
  Proof.
    intros su ss k kl ss' H. unfold apply_summary0 in H.
    destruct (negb (su_wf su)); [discriminate|].
    destruct (negb (Bool.eqb (su_acc su) (acc_mode C))); [discriminate|].
    destruct (negb (Nat.eqb (length (s_rs ss)) 31)); [discriminate|].
    destruct (negb (forallb (mflvars_lt (s_nl ss)) (s_mf ss))); [discriminate|].
    destruct (s_pc ss) as [pc|r]; [|discriminate].
    destruct (negb (Z.eqb pc (su_pc su))); [discriminate|].
    match type of H with (match ?x with Some _ => _ | None => _ end) = _ => destruct x as [ra|]; [|discriminate] end.
    destruct (sum_match C genv su ss) as [[[th tb] tl] code]. destruct code; try discriminate.
    destruct (negb (forallb (post_blobs_ok tb) (su_req su ++ su_mpost su))); [discriminate|].
    destruct (opq_required (s_mf ss) (su_oreq su)); [|discriminate].
    destruct (su_heap su) as [hc|].
    { destruct (Nat.ltb (s_ref ss) (s_nm ss) && Nat.ltb 0 (s_nm ss) && forallb (mrefs_lt (s_nm ss)) (s_mf ss)); [|discriminate].
      destruct (negb (hc_wf su hc tb)); [discriminate|].
      destruct (sum_postH su hc ss th tb tl ra (su_post su) (su_mpost su) (hc_eff hc)); [|discriminate].
      destruct (hc_alt hc) as [[[p2 m2] e2]|]; [destruct e2; try discriminate; destruct (sum_postH su hc ss th tb tl ra p2 m2 _); discriminate| discriminate]. }
    destruct (su_law su); [|discriminate].
    destruct (Nat.ltb (s_ref ss) (s_nm ss) && Nat.ltb 0 (s_nm ss) && forallb (mrefs_lt (s_nm ss)) (s_mf ss)) eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hc]. apply Nat.ltb_lt in Hc. lia.
  Qed.
  Lemma apply_summary_nm : forall su ss k kl ss', apply_summary C genv su ss = SumOkL k kl ss' -> s_nm ss <> 0%nat.
  Proof.
    intros su ss k kl ss' H. unfold apply_summary in H.
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
    apply apply_summary0_nm in H. cbn [s_nm set_mf] in H. exact H.
  Qed.
  Lemma apply_sums_nm : forall l ss k kl ss', apply_sums C genv l ss = SumOkL k kl ss' -> s_nm ss <> 0%nat.
  Proof.
    induction l as [|su l IH]; intros ss k kl ss' H; cbn [apply_sums] in H; [discriminate|].
    destruct l as [|su2 l2]; [eapply apply_summary_nm; exact H|].
    destruct (apply_summary C genv su ss) as [k1 kl1 ss1|k1 kl1 ss1|k1 kl1 ss1 oss2|code] eqn:AP; [discriminate| eapply apply_summary_nm; exact AP| discriminate| eapply IH; exact H].
  Qed.

  Lemma apply_summary_genvM : forall su ss k kl ss1 oss2, apply_summary C genv su ss = SumOkM k kl ss1 oss2 -> forallb (evars_lt (s_nx ss)) genv = true.
  Proof.
    intros su ss k kl ss1 oss2 H. unfold apply_summary in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:X; [|discriminate] end.
    apply andb_prop in X as [_ X]. exact X.
  Qed.
  Lemma apply_sums_genvM : forall l ss k kl ss1 oss2, apply_sums C genv l ss = SumOkM k kl ss1 oss2 -> forallb (evars_lt (s_nx ss)) genv = true.
  Proof.
    induction l as [|su l IH]; intros ss k kl ss1 oss2 H; cbn [apply_sums] in H; [discriminate|].
    destruct l as [|su2 l2]; [eapply apply_summary_genvM; exact H|].
    destruct (apply_summary C genv su ss) as [k1 kl1 ss1'|k1 kl1 ss1'|k1 kl1 ss1' oss2'|code] eqn:AP; [discriminate| discriminate| eapply apply_summary_genvM; exact AP| eapply IH; exact H].
  Qed.
  Lemma apply_sums_genvL : forall l ss k kl ss', apply_sums C genv l ss = SumOkL k kl ss' -> forallb (evars_lt (s_nx ss)) genv = true.
  Proof.
    induction l as [|su l IH]; intros ss k kl ss' H; cbn [apply_sums] in H; [discriminate|].
    destruct l as [|su2 l2]; [eapply apply_summary_genvL; exact H|].
    destruct (apply_summary C genv su ss) as [k1 kl1 ss1|k1 kl1 ss1|k1 kl1 ss1 oss2|code] eqn:AP; [discriminate| eapply apply_summary_genvL; exact AP| discriminate| eapply IH; exact H].
  Qed.



  Section Go.
  Variable nx0 : positive.      (* [comment removed for export] *)
  Variable nl0 : positive.      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mf_mem_In : forall f l, mf_mem f l = true -> In f l.
  Proof.
    intros f l. induction l as [|g l IH]; cbn; intros H; [discriminate|].
    apply orb_prop in H as [H|H]; [left; symmetry; apply mfact_eqb_eq; exact H| right; apply IH; exact H].
  Qed.

  (* [comment removed for export] *)
  Definition regval (E : env) (r : sreg) : Z :=
    match r with RZ e => zden E e | RW i => bv_unsigned (ew E i) end.

  Lemma regval_rden : forall E r, Z_to_bv 64 (regval E r) = rden E r.
  Proof. intros E [i|e]; cbn -[zdenp Z_to_bv]; [apply w64_of_unsigned| rewrite zdenp_ok; reflexivity]. Qed.

  Lemma lits_of_spec : forall rs zs, lits_of rs = Some zs -> map (fun r => match r with RZ e => is_lit e | RW _ => None end) rs = map Some zs.
  Proof.
    induction rs as [|[i|e] rs IH]; intros zs H; cbn in H.
    - injection H; intros <-. reflexivity.
    - discriminate.
    - destruct (is_lit e) as [z|] eqn:L; [|discriminate]. destruct (lits_of rs) as [zs'|] eqn:LS; [|discriminate].
      injection H; intros <-. cbn. rewrite L. f_equal. apply IH. reflexivity.
  Qed.

  Lemma fold_min_le' : forall zs a, fold_left Z.min zs a <= a /\ forall x, In x zs -> fold_left Z.min zs a <= x.
  Proof.
    induction zs as [|y zs IH]; intros a; cbn; [split; [lia| intros x []]|].
    destruct (IH (Z.min a y)) as [H1 H2]. split; [lia|]. intros x [<-|Hx]; [lia| apply H2; exact Hx].
  Qed.
  Lemma fold_min_le : forall zs z x, In x (z :: zs) -> fold_left Z.min zs z <= x.
  Proof. intros zs z x [<-|Hx]; destruct (fold_min_le' zs z) as [H1 H2]; [exact H1| apply H2; exact Hx]. Qed.
  Lemma fold_max_ge' : forall zs a, a <= fold_left Z.max zs a /\ forall x, In x zs -> x <= fold_left Z.max zs a.
  Proof.
    induction zs as [|y zs IH]; intros a; cbn; [split; [lia| intros x []]|].
    destruct (IH (Z.max a y)) as [H1 H2]. split; [lia|]. intros x [<-|Hx]; [lia| apply H2; exact Hx].
  Qed.
  Lemma fold_max_ge : forall zs z x, In x (z :: zs) -> x <= fold_left Z.max zs z.
  Proof. intros zs z x [<-|Hx]; destruct (fold_max_ge' zs z) as [H1 H2]; [exact H1| apply H2; exact Hx]. Qed.

  (* [comment removed for export] *)
  Lemma havoc_facts_ok : forall sts col v i p r E E',
    length col = length sts -> nth_error sts i = Some p -> nth_error col i = Some r ->
    Forall (pfact_ok CS E) (s_pf p) ->
    ez E' v = regval E r ->
    Forall (pfact_ok CS E') (havoc_facts sts col v).
  Proof.
    intros sts col v i p r E E' LEN HP HR PF EV. unfold havoc_facts.
    assert (EVD : zden E' (eatom (EZv v)) = regval E r) by (rewrite eatom_den; cbn; exact EV).
    destruct (lits_of col) as [[|z zs]|] eqn:LITS.
    - (* [comment removed for export] *) apply lits_of_spec in LITS. destruct col; [|discriminate]. apply nth_error_In in HR. destruct HR.
    - apply lits_of_spec in LITS.
      assert (Hz : exists z0, r = RZ (ELit z0) /\ In z0 (z :: zs)).
      { assert (X : In (match r with RZ e => is_lit e | RW _ => None end) (map Some (z :: zs))).
        { rewrite <- LITS. apply in_map_iff. exists r. split; [reflexivity| eapply nth_error_In; exact HR]. }
        apply in_map_iff in X as (z0 & Hz0 & Hin). exists z0. split; [|exact Hin].
        destruct r as [j|e]; [discriminate|]. destruct e; cbn in Hz0; try discriminate. injection Hz0; intros ->. reflexivity. }
      destruct Hz as (z0 & -> & Hin). cbn [regval zden] in EVD.
      pose proof (fold_min_le zs z z0 Hin) as LO. pose proof (fold_max_ge zs z z0 Hin) as HI.
      constructor. { cbn -[eadd eatom]. rewrite zdenp_ok, eadd_den, EVD. cbn [zden]. lia. }
      constructor. { cbn -[eadd eatom emulc]. rewrite zdenp_ok, eadd_den, emulc_den, EVD. cbn [zden]. lia. }
      match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:NZ; [|constructor] end.
      apply andb_prop in NZ as [NZ ALL]. rewrite forallb_forall in ALL. specialize (ALL z0 Hin). apply negb_true_iff in ALL. apply Z.eqb_neq in ALL.
      constructor; [|constructor]. cbn -[eatom]. rewrite !zdenp_ok, EVD. cbn [zden]. lia.
    - destruct (all_u64 sts col) eqn:U; [|constructor].
      unfold all_u64 in U. rewrite forallb_forall in U.
      assert (IN : In (p, r) (combine sts col)).
      { clear - HP HR LEN. revert i sts col HP HR LEN. induction i as [|i IH]; intros [|s sts] [|c col] HP HR LEN; cbn in HP, HR; try discriminate.
        - injection HP; injection HR; intros -> ->. left. reflexivity.
        - right. apply (IH sts col HP HR). cbn in LEN. lia. }
      specialize (U _ IN). cbn in U.
      assert (RNG : 0 <= regval E r <= two64 - 1).
      { destruct r as [j|e]; cbn [regval].
        - pose proof (bv_unsigned_in_range 64 (ew E j)) as X. unfold bv_modulus, two64 in *. cbn [Z.of_N] in X. lia.
        - exact (e_in_sound E (oracle_of p) e 0 (two64 - 1) (mk_oracle_sound CS E (s_pf p) PF) U). }
      constructor. { cbn -[eatom]. rewrite zdenp_ok, EVD. lia. }
      constructor; [|constructor]. cbn -[eadd eatom emulc two64]. rewrite zdenp_ok, eadd_den, emulc_den, EVD. cbn [zden]. lia.
  Qed.
  Lemma reg_cols_spec : forall n rss i rs, nth_error rss i = Some rs -> length rs = n ->
    Forall2 (fun col r => nth_error col i = Some r) (reg_cols n rss) rs
    /\ Forall (fun col => length col = length rss) (reg_cols n rss).
  Proof.
    induction n as [|n IH]; intros rss i rs Hi Hlen; cbn.
    - destruct rs; [|discriminate]. split; constructor.
    - destruct rs as [|r rs']; [discriminate|]. cbn in Hlen.
      destruct (IH (map (fun rs0 => tl rs0) rss) i rs') as [A B].
      { rewrite nth_error_map, Hi. reflexivity. } { lia. }
      split.
      + constructor; [|exact A]. rewrite nth_error_map, Hi. reflexivity.
      + constructor; [apply map_length|]. eapply Forall_impl; [|exact B]. intros col Hc. rewrite Hc. apply map_length.
  Qed.

  Lemma reg_keep_all : forall r rs x, reg_keep nx0 r rs = true -> In x (r :: rs) -> x = r /\ rvars_lt nx0 r = true.
  Proof.
    intros r rs x H Hx. unfold reg_keep in H. apply andb_prop in H as [W A]. split; [|exact W].
    destruct Hx as [<-|Hx]; [reflexivity|]. rewrite forallb_forall in A. symmetry. apply sreg_eqb_eq. apply A. exact Hx.
  Qed.

  Lemma havoc_facts_vars : forall sts col v n, (v < n)%positive -> forallb (pfvars_lt n) (havoc_facts sts col v) = true.
  Proof.
    intros sts col v n Hv. assert (V : (v <? n)%positive = true) by (apply Pos.ltb_lt; exact Hv).
    unfold havoc_facts. destruct (lits_of col) as [[|z zs]|]; cbn -[Z.ltb Z.eqb forallb Z.min Z.max fold_left]; rewrite ?V; cbn [andb forallb];
      try reflexivity.
    - destruct (all_u64 sts col); cbn; rewrite ?V; reflexivity.
    - match goal with |- context [if ?c then _ else _] => destruct c end; cbn; rewrite ?V; reflexivity.
    - destruct (all_u64 sts col); cbn; rewrite ?V; reflexivity.
  Qed.

  Lemma merge_cols_sound : forall sts i p E, nth_error sts i = Some p -> Forall (pfact_ok CS E) (s_pf p) ->
    forall cols v E' rs, agree nx0 nl0 E E' -> (nx0 <= v)%positive ->
    Forall (fun col => length col = length sts) cols ->
    Forall2 (fun col r => nth_error col i = Some r) cols rs ->
    let '(ms, fs, k) := merge_cols nx0 sts cols v in
    exists vs, length vs = k /\ map (rden (setzs E' v vs)) ms = map (rden E) rs
       /\ Forall (pfact_ok CS (setzs E' v vs)) fs
       /\ forallb (rvars_lt (paddn v k)) ms = true /\ forallb (pfvars_lt (paddn v k)) fs = true.
  Proof.
    intros sts i p E Hp PF. induction cols as [|col cols IH]; intros v E' rs AG Hv LEN F2.
    - inversion F2; subst. cbn. exists []. repeat split; reflexivity || constructor.
    - inversion F2 as [|col' r cols' rs' Hr F2']; subst col' cols' rs. inversion LEN as [|c0 cs0 LENc LEN']; subst c0 cs0.
      cbn [merge_cols]. destruct col as [|r0 rest] eqn:COL; [destruct i; discriminate|].
      destruct (reg_keep nx0 r0 rest) eqn:KEEP.
      + specialize (IH v E' rs' AG Hv LEN' F2'). destruct (merge_cols nx0 sts cols v) as [[ms fs] k].
        destruct IH as (vs & Hlen & Hmap & HF & WR & WP). exists vs.
        destruct (reg_keep_all r0 rest r KEEP ltac:(eapply nth_error_In; exact Hr)) as [-> W0].
        split; [exact Hlen|]. split.
        { cbn [map]. rewrite Hmap. f_equal. rewrite rden_setzs by (eapply rvars_lt_mono; [|exact W0]; lia).
          symmetry. apply (rden_agree nx0 nl0 E E' AG). exact W0. }
        split; [exact HF|]. split; [|exact WP]. cbn [forallb]. rewrite WR. pose proof (paddn_ge k v) as PG. rewrite (rvars_lt_mono nx0 (paddn v k) r0 ltac:(lia) W0). reflexivity.
      + set (x := regval E r).
        specialize (IH (Pos.succ v) (env_setz E' v x) rs' ltac:(eapply agree_trans; [exact AG| apply agree_setz_hi; exact Hv]) ltac:(lia) LEN' F2').
        destruct (merge_cols nx0 sts cols (Pos.succ v)) as [[ms fs] k].
        destruct IH as (vs & Hlen & Hmap & HF & WR & WP). exists (x :: vs).
        split; [cbn; lia|]. cbn [setzs map paddn].
        assert (EV : ez (setzs (env_setz E' v x) (Pos.succ v) vs) v = x) by (rewrite ez_setzs_old by lia; rewrite ez_setz, Pos.eqb_refl; reflexivity).
        split.
        { rewrite Hmap. f_equal. cbn -[zdenp setzs env_setz Z_to_bv]. rewrite zdenp_ok, eatom_den. cbn [zden]. rewrite EV. apply regval_rden. }
        split.
        { apply Forall_app. split; [|exact HF]. rewrite <- COL in *. eapply (havoc_facts_ok sts col v i p r E); [exact LENc| exact Hp| exact Hr| exact PF| exact EV]. }
        split.
        { cbn. rewrite WR. cbn. replace (v <? paddn (Pos.succ v) k)%positive with true; [reflexivity|]. symmetry. apply Pos.ltb_lt. apply paddn_gt. }
        rewrite forallb_app, WP, andb_true_r. apply havoc_facts_vars. apply paddn_gt.
  Qed.
  Lemma w_mem_In : forall lh W, w_mem lh W = true -> In lh W.
  Proof.
    intros [l h] W. induction W as [|[l' h'] W IH]; cbn; intros H; [discriminate|].
    apply orb_prop in H as [H|H]; [|right; apply IH; exact H].
    apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. cbn in H1, H2. subst. left. reflexivity.
  Qed.

  Lemma w_union_In : forall W acc x, (In x acc \/ In x W) -> In x (w_union W acc).
  Proof.
    induction W as [|lh W IH]; intros acc x Hx; cbn.
    - destruct Hx as [Hx|[]]. exact Hx.
    - apply IH. destruct Hx as [Hx|[<-|Hx]].
      + left. destruct (w_mem lh acc); [exact Hx| apply in_app_iff; left; exact Hx].
      + left. destruct (w_mem lh acc) eqn:M; [apply w_mem_In; exact M| apply in_app_iff; right; left; reflexivity].
      + right. exact Hx.
  Qed.

  Lemma w_all_In : forall sts p lh, In p sts -> In lh (s_W p) -> In lh (w_all sts).
  Proof.
    intros sts p lh Hp Hlh. unfold w_all.
    assert (GEN : forall l acc, (In lh acc \/ (In p l)) -> In lh (fold_left (fun acc ss => w_union (s_W ss) acc) l acc)).
    { induction l as [|s l IH]; intros acc H; cbn.
      - destruct H as [H|[]]. exact H.
      - apply IH. destruct H as [H|[<-|H]].
        + left. apply w_union_In. left. exact H.
        + left. apply w_union_In. right. exact Hlh.
        + right. exact H. }
    apply GEN. right. exact Hp.
  Qed.

  Lemma outside_Forall : forall W x, outside W x <-> Forall (fun lh : ivl => ~ (fst lh <= x < snd lh)) W.
  Proof.
    intros W x. induction W as [|[l h] W IH]; cbn.
    - split; [intros _; constructor| intros _; exact I].
    - split.
      + intros [H1 H2]. constructor; [exact H1| apply IH; exact H2].
      + intros H. inversion H; subst. split; [assumption| apply IH; assumption].
  Qed.

  Lemma In_nth_error' : forall {A} (l : list A) x, In x l -> exists i, nth_error l i = Some x.
  Proof. intros A l x H. apply In_nth_error in H. exact H. Qed.

  Fixpoint evals (E : env) (n : positive) (k : nat) : list Z :=
    match k with O => [] | S k' => ez E n :: evals E (Pos.succ n) k' end.

  Lemma evals_ext : forall k n E1 E2, (forall i, ez E1 i = ez E2 i) -> evals E1 n k = evals E2 n k.
  Proof. induction k as [|k IH]; intros n E1 E2 H; cbn; [reflexivity|]. rewrite H, (IH (Pos.succ n) E1 E2 H). reflexivity. Qed.

  Lemma ez_setzs_evals : forall k n E i, ez (setzs E n (evals E n k)) i = ez E i.
  Proof.
    induction k as [|k IH]; intros n E i; cbn; [reflexivity|].
    rewrite <- (evals_ext k (Pos.succ n) (env_setz E n (ez E n)) E).
    2:{ intros j. rewrite ez_setz. destruct (Pos.eqb_spec j n); [subst; reflexivity| reflexivity]. }
    rewrite IH. rewrite ez_setz. destruct (Pos.eqb_spec i n); [subst; reflexivity| reflexivity].
  Qed.

  Lemma setzs_wl : forall vs E n, ewl (setzs E n vs) = ewl E /\ ebl (setzs E n vs) = ebl E /\ eol (setzs E n vs) = eol E /\ ell (setzs E n vs) = ell E /\ eml (setzs E n vs) = eml E /\ elw (setzs E n vs) = elw E.
  Proof. induction vs as [|v vs IH]; intros E n; cbn; [repeat split; reflexivity|]. destruct (IH (env_setz E n v) (Pos.succ n)) as (A & B & C0 & D0 & M0 & L0). rewrite A, B, C0, D0, M0, L0. repeat split; reflexivity. Qed.

  Lemma agree_setzs_evals : forall N NL k n E, agree N NL E (setzs E n (evals E n k)).
  Proof.
    intros N NL k n E. unfold agree.
    destruct (setzs_wl (evals E n k) E n) as (A & B & C0 & D0 & M0 & L0). unfold em, el. rewrite A, B, C0, D0, M0, L0, ecur_setzs, epr_setzs, elb0_setzs, ehp_setzs, ecw_setzs, elh_setzs, elbl_setzs, ehr_setzs.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))))))))))); [intros i _; symmetry; apply ez_setzs_evals| intros; reflexivity].
  Qed.

  Lemma evals_length : forall k n E, length (evals E n k) = k.
  Proof. induction k; intros; cbn; [reflexivity|]. rewrite IHk. reflexivity. Qed.

  Lemma pdist_spec : forall fuel n m, (n <= m)%positive -> (Pos.to_nat m - Pos.to_nat n < fuel)%nat -> paddn n (pdist n m fuel) = m.
  Proof.
    induction fuel as [|fuel IH]; intros n m Hnm Hf; [lia|]. cbn.
    destruct (Pos.leb_spec m n) as [Hle|Hlt]; cbn; [lia|].
    apply IH; lia.
  Qed.

  Lemma merge_n_sound : forall sts sm k p E m,
    merge_n C nx0 nl0 sts = Some (sm, k) -> In p sts -> INV segs G E p m ->
    exists vs, length vs = k /\ INV segs G (setzs E nx0 vs) sm m
      /\ ms_den segs G (setzs E nx0 vs) sm m = ms_den segs G E p m
      /\ length (s_rs sm) = 31%nat
      /\ (pcvars_lt (paddn nx0 k) (s_pc sm) && forallb (rvars_lt (paddn nx0 k)) (s_rs sm)
         && forallb (mfvars_lt (paddn nx0 k)) (s_mf sm) && forallb (pfvars_lt (paddn nx0 k)) (s_pf sm)
         && forallb (fun lh => evars_lt (paddn nx0 k) (fst lh) && evars_lt (paddn nx0 k) (snd lh)) (s_W sm) = true
          /\ mrefs_ok sm = true /\ lrefs_ok nl0 sm = true).
  Proof.
    intros sts sm k p E m H Hp HI. unfold merge_n in H. destruct sts as [|s1 rest] eqn:STS; [discriminate|].
    destruct rest as [|s2 rest'].
    { (* [comment removed for export] *)
      destruct Hp as [Hp|[]]. subst s1.
      match type of H with (if ?c then _ else _) = _ => destruct c eqn:CHK; [|discriminate] end.
      apply andb_prop in CHK as [CHK MLP]. apply andb_prop in CHK as [CHK MRP].
      apply andb_prop in CHK as [CHK PC1]. apply andb_prop in CHK as [CHK NX]. apply andb_prop in CHK as [WF LEN].
      apply Nat.eqb_eq in LEN. apply Pos.leb_le in NX.
      injection H; intros Ek Esm. subst sm.
      assert (PK : paddn nx0 k = s_nx p) by (subst k; apply pdist_spec; lia).
      exists (evals E nx0 k). split; [apply evals_length|].
      rewrite ss_wf_at in WF.
      destruct (INV_agree (s_nx p) nl0 E (setzs E nx0 (evals E nx0 k)) (agree_setzs_evals _ nl0 k nx0 E) p m WF MRP MLP HI) as [HI' DEN].
      split; [exact HI'|]. split; [exact DEN|]. split; [exact LEN|]. split; [|split; [exact MRP| exact MLP]].
      rewrite PK. unfold wf_at in WF. repeat (apply andb_prop in WF as [WF ?X]). rewrite WF. cbn [andb]. repeat match goal with H : ?x = true |- _ => rewrite H end. reflexivity. }
    revert STS Hp H; generalize (s2 :: rest') as rest; clear s2 rest'; intros rest STS Hp H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:CHK; [|discriminate] end.
    apply andb_prop in CHK as [CHK WW]. apply andb_prop in CHK as [ALL PC1].
    rewrite <- STS in ALL, H, Hp, WW. rewrite forallb_forall in ALL.
    pose proof (ALL p Hp) as Xp. apply andb_prop in Xp as [Xp MLp]. apply andb_prop in Xp as [Xp MRp]. apply andb_prop in Xp as [Xp RFp]. apply andb_prop in Xp as [LENp PCp]. apply Nat.eqb_eq in LENp.
    apply Nat.eqb_eq in RFp.
    destruct (In_nth_error' sts p Hp) as [i Hi].
    destruct (reg_cols_spec 31 (map s_rs sts) i (s_rs p) ltac:(rewrite nth_error_map, Hi; reflexivity) LENp) as [F2 LENS].
    pose proof HI as (HM & HP & MU & WM & MI & SM).
    pose proof (merge_cols_sound sts i p E Hi HP (reg_cols 31 (map s_rs sts)) nx0 E (s_rs p) (agree_refl nx0 nl0 E) ltac:(lia)
                  ltac:(eapply Forall_impl; [|exact LENS]; intros col Hc; rewrite Hc; apply map_length) F2) as MC.
    destruct (merge_cols nx0 sts (reg_cols 31 (map s_rs sts)) nx0) as [[rs hf] k0].
    injection H; intros Esm Ek. subst sm k0. destruct MC as (vs & Hlen & Hmap & HF & WR & WP).
    exists vs. split; [exact Hlen|].
    assert (PCE : s_pc p = s_pc s1).
    { destruct (s_pc p), (s_pc s1); cbn in PCp; try discriminate. apply Z.eqb_eq in PCp. subst; reflexivity. }
    (* [comment removed for export] *)
    assert (PFC : forall f, In f (pf_common nx0 rest (s_pf s1)) -> pfvars_lt nx0 f = true /\ In f (s_pf p)).
    { intros f Hf. unfold pf_common in Hf. apply filter_In in Hf as [Hin Hc]. apply andb_prop in Hc as [Hv Hall].
      split; [exact Hv|]. rewrite STS in Hp. destruct Hp as [<-|Hp']; [exact Hin|].
      rewrite forallb_forall in Hall. apply pf_mem_In. apply Hall. exact Hp'. }
    assert (MFC : forall f, In f (mf_common nx0 rest (s_mf s1)) -> mfvars_lt nx0 f = true /\ In f (s_mf p)).
    { intros f Hf. unfold mf_common in Hf. apply filter_In in Hf as [Hin Hc]. apply andb_prop in Hc as [Hv Hall].
      split; [exact Hv|]. rewrite STS in Hp. destruct Hp as [<-|Hp']; [exact Hin|].
      rewrite forallb_forall in Hall. apply mf_mem_In. apply Hall. exact Hp'. }
    pose proof (paddn_ge k nx0) as PG.
    split; [|split; [|split]].
    - (* [comment removed for export] *) unfold INV. cbn [s_mf s_pf s_W s_same].
      match goal with |- context [refm ?E1 ?S1] =>
        replace (refm E1 S1) with (refm E p) by (unfold refm, em; cbn [s_ref]; rewrite RFp, eml_setzs_gen; reflexivity) end.
      split; [|split; [|split; [|split; [exact WM| split; [exact MI|]]]]].
      + apply List.Forall_forall. intros f Hf. destruct (MFC f Hf) as [Hv Hin].
        apply (mfact_ok_setzs E vs nx0 m f Hv). rewrite List.Forall_forall in HM. apply HM. exact Hin.
      + apply Forall_app. split; [|exact HF]. apply List.Forall_forall. intros f Hf. destruct (PFC f Hf) as [Hv Hin].
        apply (pfact_ok_setzs E vs nx0 f Hv). rewrite List.Forall_forall in HP. apply HP. exact Hin.
      + rewrite (wden_setzs E vs nx0 (w_all sts) WW). eapply munch_weaken; [|exact MU].
        intros x Hx. apply outside_Forall. apply outside_Forall in Hx. unfold wden in Hx |- *.
        apply List.Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (lh & <- & Hlh).
        rewrite List.Forall_forall in Hx. apply Hx. apply in_map_iff. exists lh. split; [reflexivity|]. exact (w_all_In sts p lh Hp Hlh).
      + intros SS. apply SM. rewrite forallb_forall in SS. apply SS. exact Hp.
    - (* [comment removed for export] *) unfold ms_den. cbn [s_rs s_pc]. rewrite !regs_den_rdw, Hmap, PCE.
      rewrite <- PCE. rewrite (pc_den_setzs E vs nx0 (s_pc p)) by (rewrite PCE; destruct (s_pc s1); [reflexivity| discriminate]). reflexivity.
    - cbn [s_rs]. pose proof (Forall2_length F2) as L2. rewrite <- (map_length (rden (setzs E nx0 vs)) rs), Hmap, map_length. exact LENp.
    - assert (MR1 : mrefs_ok s1 = true /\ lrefs_ok nl0 s1 = true).
      { pose proof (ALL s1 ltac:(rewrite STS; left; reflexivity)) as X1. apply andb_prop in X1 as [X1 X2]. apply andb_prop in X1 as [_ X1]. split; [exact X1| exact X2]. }
      destruct MR1 as [MR1 ML1].
      split.
      2:{ split.
          - unfold mrefs_ok in MR1 |- *. cbn [s_ref s_mf]. apply andb_prop in MR1 as [R1 F1]. rewrite R1. cbn [andb].
            apply forallb_forall. intros f Hf. unfold mf_common in Hf. apply filter_In in Hf as [Hin _].
            rewrite forallb_forall in F1. apply F1. exact Hin.
          - unfold lrefs_ok in ML1 |- *. cbn [s_nl s_mf]. apply andb_prop in ML1 as [R1 F1]. rewrite R1. cbn [andb].
            apply forallb_forall. intros f Hf. unfold mf_common in Hf. apply filter_In in Hf as [Hin _].
            rewrite forallb_forall in F1. apply F1. exact Hin. }
      cbn [s_pc s_rs s_mf s_pf s_W]. rewrite WR.
      assert (P1 : pcvars_lt (paddn nx0 k) (s_pc s1) = true) by (destruct (s_pc s1); [reflexivity| discriminate]). rewrite P1.
      assert (P3 : forallb (mfvars_lt (paddn nx0 k)) (mf_common nx0 rest (s_mf s1)) = true).
      { apply forallb_forall. intros f Hf. destruct (MFC f Hf) as [Hv _]. exact (mfvars_lt_mono nx0 _ f PG Hv). }
      assert (P4 : forallb (pfvars_lt (paddn nx0 k)) (pf_common nx0 rest (s_pf s1) ++ hf) = true).
      { rewrite forallb_app, WP, andb_true_r. apply forallb_forall. intros f Hf. destruct (PFC f Hf) as [Hv _]. exact (pfvars_lt_mono nx0 _ f PG Hv). }
      assert (P5 : forallb (fun lh : expr * expr => evars_lt (paddn nx0 k) (fst lh) && evars_lt (paddn nx0 k) (snd lh)) (w_all sts) = true).
      { eapply forallb_mono; [|exact WW]. intros [l h] Hx. cbn in Hx |- *. apply andb_prop in Hx as [Hl Hh].
        rewrite (evars_lt_mono nx0 _ _ PG Hl), (evars_lt_mono nx0 _ _ PG Hh). reflexivity. }
      rewrite P3, P4, P5. reflexivity.
  Qed.
  Lemma rt_parks_app : forall t acc, rt_parks t acc = rt_parks t [] ++ acc.
  Proof.
    induction t as [ss|c a IHa b IHb|i a IHa|c nx k a IHa|cpc nx k cnl ckl a IHa|lpc lnx lk lnl lkl lnm la IHla|hpc hnx hk hnl hkl hnm ha IHha hb IHhb|ss|nx k a IHa b IHb| |pc code]; intros acc; cbn; try reflexivity.
    - rewrite IHa, IHb, (IHa (rt_parks b [])), <- app_assoc. reflexivity.
    - apply IHa. - apply IHa. - apply IHa. - apply IHla.
    - rewrite IHha, IHhb, (IHha (rt_parks hb [])), <- app_assoc. reflexivity.
    - rewrite IHa, IHb, (IHa (rt_parks b [])), <- app_assoc. reflexivity.
  Qed.

  Lemma parks_at_spec : forall pc t acc ss,
    In ss (parks_at pc t acc) <-> (In ss (rt_parks t []) /\ s_pc ss = PCz pc) \/ In ss acc.
  Proof.
    intros pc t. induction t as [s0|c a IHa b IHb|i a IHa|c nx k a IHa|cpc nx k cnl ckl a IHa|lpc lnx lk lnl lkl lnm la IHla|hpc hnx hk hnl hkl hnm ha IHha hb IHhb|s0|nx k a IHa b IHb| |p code]; intros acc ss; cbn -[Z.eqb];
      try (split; [intros H; right; exact H| intros [[[] _]|H]; exact H]).
    - rewrite IHa, IHb, (rt_parks_app a (rt_parks b [])), in_app_iff. tauto.
    - apply IHa. - apply IHa. - apply IHa. - apply IHla.
    - rewrite IHha, IHhb, (rt_parks_app ha (rt_parks hb [])), in_app_iff. tauto.
    - destruct (s_pc s0) as [z|r] eqn:PC.
      + destruct (Z.eqb_spec z pc) as [->|NE]; cbn.
        * split; [intros [<-|H]; [left; split; [left; reflexivity| exact PC]| right; exact H]|].
          intros [[[<-|[]] _]|H]; [left; reflexivity| right; exact H].
        * split; [intros H; right; exact H|]. intros [[[<-|[]] X]|H]; [|exact H]. rewrite PC in X. injection X; intros ->. congruence.
      + split; [intros H; right; exact H|]. intros [[[<-|[]] X]|H]; [|exact H]. rewrite PC in X. discriminate.
    - rewrite IHa, IHb, (rt_parks_app a (rt_parks b [])), in_app_iff. tauto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition parked_ok (E0 : env) (ss : sstate) : Prop :=
    forall E' ms', agree nx0 nl0 E0 E' -> length (s_rs ss) = 31%nat -> st_ok segs G E' ss ms' -> TGT (ecur E') ms'.

  Theorem lx_go_sound : forall fuel E0 mps first ss E ms,
    agree nx0 nl0 E0 E -> genv_ok E ->
    cfg_ok G C E -> length (s_rs ss) = 31%nat -> st_ok segs G E ss ms ->
    (forall ss' pc', In ss' (rt_parks (lx_go segs C pl genv nx0 nl0 mps fuel first ss) []) -> s_pc ss' = PCz pc' -> zmem pc' mps = true -> parked_ok E0 ss') ->
    oblig segs G E (lx_go segs C pl genv nx0 nl0 mps fuel first ss) TGT ->
    TGT (ecur E) ms.
  Proof.
    induction fuel as [|fuel IH]; intros E0 mps first ss E ms AG GV CFG Hlen ST PK OB; [destruct OB|].
    cbn [lx_go] in OB, PK.
    destruct (s_pc ss) as [pc|r] eqn:Hpc.
    2:{ exact (leaf_sound E ss ms _ ST OB). }
    destruct (negb first && zmem pc (p_stops pl)); [exact (leaf_sound E ss ms _ ST OB)|].
    destruct (negb first && zmem pc mps && Nat.eqb (s_nm ss) 1 && mrefs_ok ss && lrefs_ok nl0 ss) eqn:PARK.
    { (* [comment removed for export] *)
      apply andb_prop in PARK as [PARK _]. apply andb_prop in PARK as [PARK _]. apply andb_prop in PARK as [PARK _]. apply andb_prop in PARK as [_ PARK].
      apply (PK ss pc ltac:(left; reflexivity) Hpc PARK E ms AG Hlen ST). }
    clear PARK.
    destruct (sums_at (p_sums pl) pc) as [|su more] eqn:SUM.
    2:{ (* [comment removed for export] *)
      pose proof (sums_at_ok _ pc SUMS) as SOK. rewrite SUM in SOK.
      destruct (ss_wf C ss && Pos.leb nx0 (s_nx ss) && Pos.leb nl0 (s_nl ss)) eqn:WF; [|destruct OB].
      apply andb_prop in WF as [WF NL]. apply andb_prop in WF as [WF NX]. apply Pos.leb_le in NX. apply Pos.leb_le in NL.
      destruct (apply_sums C genv (su :: more) ss) as [k kl ss'|k kl ss'|k kl ss' oss2|code] eqn:AP; [| | |destruct OB].
      - apply oblig_call in OB.
        pose proof ST as ST0. apply (st_ok_INV segs G) in ST as (m & -> & HI).
        eapply TGT_evtA; [exact (apply_sums_ok _ E ss m k kl ss' SOK GV CFG Hlen WF HI AP)|].
        intros ms' (vs & ls & m' & Hvs & Hls & Hlen' & -> & HI'). rewrite <- (ecur_env_call E (s_nx ss) vs (s_nl ss) ls).
        eapply (IH E0 mps false ss' (env_call E (s_nx ss) vs (s_nl ss) ls)); [| | | exact Hlen' | apply st_ok_INV; eexists; split; [reflexivity| exact HI'] | exact PK | exact (call_apply k kl E (s_nx ss) (s_nl ss) _ _ vs ls OB Hvs Hls)].
        { eapply agree_trans; [exact AG| apply agree_call; [exact NX| exact NL]]. }
        { apply genv_ok_call; [exact GV| eapply apply_sums_genv; exact AP]. }
        unfold env_call. apply cfg_ok_setls. apply cfg_ok_setzs; [exact CFG|]. unfold ss_wf in WF. repeat (apply andb_prop in WF as [WF ?X]). assumption.
      - (* [comment removed for export] *)
        apply oblig_callL in OB.
        pose proof ST as ST0. apply (st_ok_INV segs G) in ST as (m & -> & HI).
        eapply TGT_evtA; [exact (apply_sums_okL _ E ss m k kl ss' SOK GV CFG Hlen WF HI AP)|].
        intros ms' (vs & ls & mc & mp & m' & Hvs & Hls & Hlen' & NM' & -> & HI'). rewrite <- (ecur_env_law E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp).
        eapply (IH E0 mps false ss' (env_law E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp)); [| | | exact Hlen' | apply st_ok_INV; eexists; split; [reflexivity| exact HI'] | exact PK | exact (callL_apply k kl E (s_nx ss) (s_nl ss) (s_nm ss) _ _ vs ls mc mp OB Hvs Hls)].
        { eapply agree_trans; [exact AG| apply agree_law; [exact NX| exact NL|]]. eapply apply_sums_nm; exact AP. }
        { apply genv_ok_law; [exact GV| eapply apply_sums_genvL; exact AP]. }
        unfold env_law, env_call. apply cfg_ok_setm, cfg_ok_setm. apply cfg_ok_setls. apply cfg_ok_setzs; [exact CFG|]. unfold ss_wf in WF. repeat (apply andb_prop in WF as [WF ?X]). assumption.
      - (* [comment removed for export] *)
        apply oblig_callM in OB.
        pose proof ST as ST0. apply (st_ok_INV segs G) in ST as (m & -> & HI).
        assert (CFGh : forall vs ls mc mp mo lb, cfg_ok G C (env_heap E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp mo lb)).
        { intros vs ls mc mp mo lb. unfold env_heap, env_law, env_call. apply cfg_ok_setbl, cfg_ok_setcur, cfg_ok_setm, cfg_ok_setm. apply cfg_ok_setls.
          apply cfg_ok_setzs; [exact CFG|]. unfold ss_wf in WF. repeat (apply andb_prop in WF as [WF ?X]). assumption. }
        assert (KONT : forall ssi (OBi : forall vs ls mc mp mo lb, length vs = k -> length ls = kl ->
                                     oblig segs G (env_heap E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp mo lb) (lx_go segs C pl genv nx0 nl0 [] fuel false ssi) TGT),
                   heap_kont E ss k kl ssi).
        { intros ssi OBi vs ls mc mp mo lb m' Hvs Hls Hlen' NM' HI'.
          change mo with (ecur (env_heap E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp mo lb)) at 1.
          eapply (IH (env_heap E (s_nx ss) vs (s_nl ss) ls (s_nm ss) mc mp mo lb) [] false ssi);
            [apply agree_refl| | apply CFGh| exact Hlen'| apply st_ok_INV; eexists; split; [reflexivity| exact HI']| | exact (OBi vs ls mc mp mo lb Hvs Hls)].
          { apply genv_ok_heap; [exact GV| eapply apply_sums_genvM; exact AP]. }
          intros s2 pc2 _ _ Hz. discriminate. }
        apply (apply_sums_okM _ E ss m k kl ss' oss2 SOK GV CFG Hlen WF HI AP).
        + apply KONT. intros vs ls mc mp mo lb Hvs Hls. exact (proj1 (callM_apply k kl E (s_nx ss) (s_nl ss) (s_nm ss) _ _ _ vs ls mc mp mo lb OB Hvs Hls)).
        + destruct oss2 as [ss2|]; [|exact I].
          apply KONT. intros vs ls mc mp mo lb Hvs Hls. exact (proj2 (callM_apply k kl E (s_nx ss) (s_nl ss) (s_nm ss) _ _ _ vs ls mc mp mo lb OB Hvs Hls)). }
    destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:HFW; [|destruct OB].
    destruct (is_ecall w) eqn:HEC; [destruct OB|].
    destruct (decode_any w) as [[i sz]|] eqn:HDEC; [|destruct OB].
    pose proof ST as ST0. apply (st_ok_INV segs G) in ST as (m & -> & HI).
    pose proof (sym_step_sound segs G C E CFG (genv_ok_hpf E GV) (genv_ok_hbk E GV) (dir_at (p_dirs pl)) i sz ss pc w m Hpc Hlen HFW HEC HDEC HI) as SS.
    destruct (sym_step C (dir_at (p_dirs pl)) i sz ss) as [ss'|ss'|c st sf|ss'|code]; cbn [sres_ok] in SS.
    - destruct SS as (Hlen' & m' & STEP & HI'). eapply TGT_mstepA; [exact STEP|].
      eapply (IH E0 mps false ss' E); [exact AG| exact GV| exact CFG| exact Hlen'| apply st_ok_INV; exists m'; split; [reflexivity| exact HI'] | exact PK | exact OB].
    - destruct (ss_wf C ss && forallb (evars_lt (s_nx ss)) genv && Pos.leb nx0 (s_nx ss)) eqn:WFG; [|destruct OB].
      apply andb_prop in WFG as [WFG NX]. apply andb_prop in WFG as [WF WG]. apply Pos.leb_le in NX.
      destruct SS as (Hlen' & SS). destruct (SS WF) as (m' & v & STEP & HI').
      cbn [oblig] in OB. specialize (OB v).
      eapply TGT_mstepA; [exact STEP|].
      rewrite <- (gc_facts_den nx0). change (ecur E) with (ecur (env_setz E (s_nx ss) v)).
      eapply (IH E0 mps false (gc_facts nx0 ss') (env_setz E (s_nx ss) v)); [| apply genv_ok_setz; assumption| eapply cfg_ok_setz; eauto| rewrite gc_facts_rs; exact Hlen'| apply st_ok_INV; exists m'; split; [reflexivity| apply gc_facts_INV; exact HI'] | exact PK | exact OB].
      eapply agree_trans; [exact AG| apply agree_setz_hi; exact NX].
    - destruct SS as (HlenT & HlenF & m' & STEP & HI').
      eapply TGT_mstepA; [exact STEP|].
      assert (ST' : st_ok segs G E (if cnden E c then st else sf) (ms_den segs G E (if cnden E c then st else sf) m')).
      { apply st_ok_INV. exists m'. split; [reflexivity| exact HI']. }
      (* [comment removed for export] *)
      assert (BR : forall PKx,
                   (forall ss' pc', In ss' (rt_parks (RBr c (guard (lx_go segs C pl genv nx0 nl0 mps fuel false) st) (guard (lx_go segs C pl genv nx0 nl0 mps fuel false) sf)) []) ->
                      s_pc ss' = PCz pc' -> zmem pc' mps = true -> parked_ok E0 ss') ->
                   PKx = tt ->
                   oblig segs G E (RBr c (guard (lx_go segs C pl genv nx0 nl0 mps fuel false) st) (guard (lx_go segs C pl genv nx0 nl0 mps fuel false) sf))
                     TGT ->
                   TGT (ecur E) (ms_den segs G E (if cnden E c then st else sf) m')).
      { clear OB PK. intros u PK _ OB. cbn [oblig] in OB. destruct OB as [OBT OBF]. cbn [rt_parks] in PK. rewrite rt_parks_app in PK.
        destruct (cnden E c).
        + specialize (OBT eq_refl). unfold guard in OBT, PK. destruct (contradictory (s_pf st)) eqn:CT.
          * exfalso. eapply guard_dead; eauto.
          * eapply (IH E0 mps false st E); eauto. intros ss' pc' Hin. apply PK. apply in_app_iff. left. exact Hin.
        + specialize (OBF eq_refl). unfold guard in OBF, PK. destruct (contradictory (s_pf sf)) eqn:CT.
          * exfalso. eapply guard_dead; eauto.
          * eapply (IH E0 mps false sf E); eauto. intros ss' pc' Hin. apply PK. apply in_app_iff. right.
            destruct (contradictory (s_pf st)); [exact Hin|]. rewrite rt_parks_app, app_nil_r in Hin. exact Hin. }
      destruct (dir_at (p_dirs pl) pc) as [[| |]|]; try (apply (BR tt PK eq_refl); exact OB).
      destruct (s_pc sf) as [tgt|rr] eqn:PCF; try (apply (BR tt PK eq_refl); exact OB).
      destruct (s_pc st) as [tgt'|rr'] eqn:PCT; try (apply (BR tt PK eq_refl); exact OB).
      destruct (lin_run segs C (dir_at (p_dirs pl)) 16 tgt st) as [st'|] eqn:LR.
      * destruct (merge C st' sf) as [[[sm nx] k]|] eqn:MG; [|apply (BR tt PK eq_refl); exact OB].
        clear BR. destruct (forallb (evars_lt nx) genv && Pos.leb nx0 nx) eqn:WG; [|destruct OB]. apply andb_prop in WG as [WG NX]. apply Pos.leb_le in NX.
        apply oblig_join in OB. cbn [rt_parks] in PK.
        assert (AGm : forall vs, agree nx0 nl0 E0 (setzs E nx vs)) by (intros vs; eapply agree_trans; [exact AG| apply agree_setzs_hi; exact NX]).
        destruct (cnden E c).
        + eapply (lin_run_sound (dir_at (p_dirs pl)) 16 tgt st st' E m' (ecur E) (genv_ok_hpf E GV) (genv_ok_hbk E GV) CFG HlenT HI' LR).
          intros m'' Hlen'' HI''.
          destruct (merge_sound st' sf sm nx k E m'' true MG CFG HI'') as (vs & Hvs & INVm & DENm & CFGm & Hlenm).
          rewrite <- DENm, <- (gc_facts_den nx0), <- (ecur_setzs vs E nx). eapply (IH E0 mps false (gc_facts nx0 sm) (setzs E nx vs)); [apply AGm| apply genv_ok_setzs; assumption| exact CFGm| rewrite gc_facts_rs; exact Hlenm| apply st_ok_INV; eexists; split; [reflexivity| apply gc_facts_INV; exact INVm]| exact PK|].
          exact (binds_apply k E nx _ vs OB Hvs).
        + destruct (merge_sound st' sf sm nx k E m' false MG CFG HI') as (vs & Hvs & INVm & DENm & CFGm & Hlenm).
          rewrite <- DENm, <- (gc_facts_den nx0), <- (ecur_setzs vs E nx). eapply (IH E0 mps false (gc_facts nx0 sm) (setzs E nx vs)); [apply AGm| apply genv_ok_setzs; assumption| exact CFGm| rewrite gc_facts_rs; exact Hlenm| apply st_ok_INV; eexists; split; [reflexivity| apply gc_facts_INV; exact INVm]| exact PK|].
          exact (binds_apply k E nx _ vs OB Hvs).
      * (* [comment removed for export] *)
        destruct (lin_run segs C (dir_at (p_dirs pl)) 16 tgt' sf) as [sf'|] eqn:LR2; [|apply (BR tt PK eq_refl); exact OB].
        destruct (merge C st sf') as [[[sm nx] k]|] eqn:MG; [|apply (BR tt PK eq_refl); exact OB].
        clear BR. destruct (forallb (evars_lt nx) genv && Pos.leb nx0 nx) eqn:WG; [|destruct OB]. apply andb_prop in WG as [WG NX]. apply Pos.leb_le in NX.
        apply oblig_join in OB. cbn [rt_parks] in PK.
        assert (AGm : forall vs, agree nx0 nl0 E0 (setzs E nx vs)) by (intros vs; eapply agree_trans; [exact AG| apply agree_setzs_hi; exact NX]).
        destruct (cnden E c).
        + destruct (merge_sound st sf' sm nx k E m' true MG CFG HI') as (vs & Hvs & INVm & DENm & CFGm & Hlenm).
          rewrite <- DENm, <- (gc_facts_den nx0), <- (ecur_setzs vs E nx). eapply (IH E0 mps false (gc_facts nx0 sm) (setzs E nx vs)); [apply AGm| apply genv_ok_setzs; assumption| exact CFGm| rewrite gc_facts_rs; exact Hlenm| apply st_ok_INV; eexists; split; [reflexivity| apply gc_facts_INV; exact INVm]| exact PK|].
          exact (binds_apply k E nx _ vs OB Hvs).
        + eapply (lin_run_sound (dir_at (p_dirs pl)) 16 tgt' sf sf' E m' (ecur E) (genv_ok_hpf E GV) (genv_ok_hbk E GV) CFG HlenF HI' LR2).
          intros m'' Hlen'' HI''.
          destruct (merge_sound st sf' sm nx k E m'' false MG CFG HI'') as (vs & Hvs & INVm & DENm & CFGm & Hlenm).
          rewrite <- DENm, <- (gc_facts_den nx0), <- (ecur_setzs vs E nx). eapply (IH E0 mps false (gc_facts nx0 sm) (setzs E nx vs)); [apply AGm| apply genv_ok_setzs; assumption| exact CFGm| rewrite gc_facts_rs; exact Hlenm| apply st_ok_INV; eexists; split; [reflexivity| apply gc_facts_INV; exact INVm]| exact PK|].
          exact (binds_apply k E nx _ vs OB Hvs).
    - destruct SS as (Hlen' & m' & STEP & HI'). eapply TGT_mstepA; [exact STEP|].
      apply (leaf_sound E (release_stk ss') _ _ ltac:(apply release_stk_ok; apply st_ok_INV; exists m'; split; [reflexivity| exact HI']) OB).
    - destruct OB.
  Qed.
  Lemma oblig_merge : forall E nx k t tm K, oblig segs G E (RMerge nx k t tm) K -> oblig segs G E t K /\ binds E nx k (fun E1 => oblig segs G E1 tm K).
  Proof.
    intros E nx k t tm K [H1 H2]. split; [exact H1|]. clear H1. revert E nx H2. induction k as [|k IH]; intros E nx H; cbn in H |- *; [exact H|].
    intros v. apply IH. apply H.
  Qed.

  Lemma group_states_cover : forall r sts ss, In ss sts -> exists g, In g (group_states nx0 r sts) /\ In ss g.
  Proof.
    intros r.
    assert (INS : forall ss gs, (exists g, In g (group_insert nx0 r ss gs) /\ In ss g)
                                /\ (forall g x, In g gs -> In x g -> exists g', In g' (group_insert nx0 r ss gs) /\ In x g')).
    { intros ss gs. induction gs as [|g gs IH]; cbn.
      - split; [exists [ss]; split; [left; reflexivity| left; reflexivity]| intros g x []].
      - destruct g as [|s1 g1].
        + destruct IH as [(g0 & H0 & H0') IH2]. split; [exists g0; split; [right; exact H0| exact H0']|].
          intros g x [<-|Hg] Hx; [destruct Hx|]. destruct (IH2 g x Hg Hx) as (g' & H1 & H2). exists g'. split; [right; exact H1| exact H2].
        + destruct (same_key nx0 r ss s1).
          * split; [exists (ss :: s1 :: g1); split; [left; reflexivity| left; reflexivity]|].
            intros g x [<-|Hg] Hx; [exists (ss :: s1 :: g1); split; [left; reflexivity| right; exact Hx]|].
            exists g. split; [right; exact Hg| exact Hx].
          * destruct IH as [(g0 & H0 & H0') IH2]. split; [exists g0; split; [right; exact H0| exact H0']|].
            intros g x [<-|Hg] Hx; [exists (s1 :: g1); split; [left; reflexivity| exact Hx]|].
            destruct (IH2 g x Hg Hx) as (g' & H1 & H2). exists g'. split; [right; exact H1| exact H2]. }
    induction sts as [|s sts IH]; intros ss Hss; [destruct Hss|]. cbn. destruct Hss as [Hs|Hss].
    - subst s. apply (proj1 (INS ss (group_states nx0 r sts))).
    - destruct (IH ss Hss) as (g & Hg & Hx). apply (proj2 (INS s (group_states nx0 r sts)) g ss Hg Hx).
  Qed.

  Section Phase.
    Variable E0 : env.            (* [comment removed for export] *)
    Hypothesis GV0 : genv_ok E0.
    Hypothesis CFG0 : cfg_ok G C E0.
    Hypothesis ACNX : match c_acc C with Some A => evars_lt nx0 (ac_sb A) | None => true end = true.
    Notation K := TGT.

    (* [comment removed for export] *)
    Lemma merge_groups_sound : forall fuel pc mps' gs t,
      let t' := merge_groups segs C pl genv nx0 nl0 fuel pc mps' gs t in
      oblig segs G E0 t' K ->
      (forall ss' pc', In ss' (rt_parks t' []) -> s_pc ss' = PCz pc' -> zmem pc' mps' = true -> parked_ok E0 ss') ->
      oblig segs G E0 t K
      /\ (forall g ss', In g gs -> In ss' g -> parked_ok E0 ss')
      /\ (forall ss', In ss' (rt_parks t []) -> In ss' (rt_parks t' [])).
    Proof.
      intros fuel pc mps'. induction gs as [|g gs IH]; intros t t' OB PJ; subst t'; cbn [merge_groups] in OB, PJ |- *.
      - split; [exact OB|]. split; [intros g ss' []| intros ss' H; exact H].
      - match type of OB with oblig _ _ _ (merge_groups _ _ _ _ _ _ _ _ _ _ ?t1) _ => set (T1 := t1) in OB, PJ |- * end.
        destruct (IH T1 OB PJ) as (OB1 & JG & INCL).
        assert (INCLt : forall ss', In ss' (rt_parks t []) -> In ss' (rt_parks T1 [])).
        { intros ss' H. subst T1. destruct (merge_n C nx0 nl0 g) as [[sm k]|]; [destruct (forallb (evars_lt nx0) genv)|]; cbn; rewrite rt_parks_app, in_app_iff; left; exact H. }
        destruct (merge_n C nx0 nl0 g) as [[sm k]|] eqn:MG.
        2:{ subst T1. apply oblig_merge in OB1 as [_ F]. cbn in F. destruct F. }
        destruct (forallb (evars_lt nx0) genv) eqn:GW.
        2:{ subst T1. apply oblig_merge in OB1 as [_ F]. cbn in F. destruct F. }
        subst T1. apply oblig_merge in OB1 as [OBt OBm].
        split; [exact OBt|]. split; [| intros ss' H; apply INCL, INCLt, H].
        intros g0 ss' [<-|Hg0] INs; [| exact (JG g0 ss' Hg0 INs)].
        (* [comment removed for export] *)
        intros E' ms' AG' Hlen' ST'.
        apply (st_ok_INV segs G) in ST' as (m' & -> & HI').
        destruct (merge_n_sound g sm k ss' E' m' MG INs HI') as (vs & Hvs & INVm & DENm & Hlenm & (WFm & MRm & MLm)).
        set (Em := setzs E0 nx0 vs).
        assert (AGE : agree (paddn nx0 k) nl0 (setzs E' nx0 vs) Em).
        { subst Em. rewrite <- Hvs. apply agree_setzs_both. apply agree_sym. exact AG'. }
        assert (WFA : wf_at (paddn nx0 k) sm = true).
        { unfold wf_at. rewrite WFm. cbn [andb]. destruct (c_acc C) as [A|]; [|reflexivity].
          eapply evars_lt_mono; [|exact ACNX]. apply paddn_ge. }
        destruct (INV_agree (paddn nx0 k) nl0 (setzs E' nx0 vs) Em AGE sm m' WFA MRm MLm INVm) as [INVe DENe].
        rewrite <- DENm, <- DENe, <- (ecur_agree nx0 nl0 E0 E' AG'), <- (ecur_setzs vs E0 nx0).
        assert (AG0 : agree nx0 nl0 E0 Em) by (subst Em; apply agree_setzs_hi; lia).
        eapply (lx_go_sound fuel E0 mps' false sm Em _ AG0).
        * apply (genv_ok_agree nx0 nl0 E0 Em AG0 GV0 GW).
        * apply (cfg_ok_agree nx0 nl0 E0 Em AG0 CFG0 ACNX).
        * exact Hlenm.
        * apply st_ok_INV. eexists. split; [reflexivity| exact INVe].
        * intros s2 pc2 Hin2 Hpc2 Hz2. apply (PJ s2 pc2); [| exact Hpc2| exact Hz2]. apply INCL. cbn. rewrite rt_parks_app, in_app_iff. right. exact Hin2.
        * subst Em. exact (binds_apply k E0 nx0 _ vs OBm Hvs).
    Qed.

    (* [comment removed for export] *)
    Lemma phase_sound : forall fuel mrs t,
      oblig segs G E0 (lx_phase segs C pl genv nx0 nl0 fuel mrs t) K ->
      oblig segs G E0 t K
      /\ (forall ss' pc', In ss' (rt_parks t []) -> s_pc ss' = PCz pc' -> zmem pc' (map fst mrs) = true -> parked_ok E0 ss').
    Proof.
      intros fuel mrs. induction mrs as [|[pc r] mrs IH]; intros t OB; cbn [lx_phase] in OB.
      - split; [exact OB|]. intros ss' pc' _ _ X. discriminate.
      - destruct (IH _ OB) as [OBt' PJ'].
        destruct (merge_groups_sound fuel pc (map fst mrs) (group_states nx0 r (parks_at pc t [])) t OBt' PJ') as (OBt & JG & INCL).
        split; [exact OBt|].
        intros ss' pc' Hin Hpc Hz. cbn in Hz. destruct (Z.eqb_spec pc' pc) as [->|NE].
        + assert (INs : In ss' (parks_at pc t [])) by (apply parks_at_spec; left; split; assumption).
          destruct (group_states_cover r _ _ INs) as (g & Hg & Hssg). exact (JG g ss' Hg Hssg).
        + apply (PJ' ss' pc'); [apply INCL; exact Hin| exact Hpc| exact Hz].
    Qed.
  End Phase.
  End Go.
  Lemma pf_tele_forall : forall E pf P, (Forall (pfact_ok CS E) pf -> P) -> pf_tele G E pf P.
  Proof.
    intros E pf. induction pf as [|f pf IH]; intros P H; cbn; [apply H; constructor|].
    intros Hf. apply IH. intros HF. apply H. constructor; assumption.
  Qed.

  Lemma pf_tele_apply : forall E pf P, pf_tele G E pf P -> Forall (pfact_ok CS E) pf -> P.
  Proof.
    intros E pf. induction pf as [|f pf IH]; intros P H HF; cbn in H; [exact H|].
    inversion HF; subst. apply (IH P); [apply H|]; assumption.
  Qed.

  Lemma mf_tele_mono : forall E m mf P Q, (P -> Q) -> mf_tele segs G E m mf P -> mf_tele segs G E m mf Q.
  Proof. intros E m mf. induction mf as [|f mf IH]; intros P Q HPQ H; cbn in H |- *; [apply HPQ, H|]. intros Hf. apply (IH P Q HPQ). apply H, Hf. Qed.

  Lemma mf_tele_forall : forall E m mf P, (Forall (mfact_ok segs L CS E m) mf -> P) -> mf_tele segs G E m mf P.
  Proof.
    intros E m mf. induction mf as [|f mf IH]; intros P H; cbn; [apply H; constructor|].
    intros Hf. apply IH. intros HF. apply H. constructor; assumption.
  Qed.

  Lemma mf_tele_apply : forall E m mf P, mf_tele segs G E m mf P -> Forall (mfact_ok segs L CS E m) mf -> P.
  Proof.
    intros E m mf. induction mf as [|f mf IH]; intros P H HF; cbn in H; [exact H|].
    inversion HF; subst. apply (IH P); [apply H|]; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition ALS (E : env) (als : list (expr * positive)) : Prop :=
    Forall (fun p => zden E (eatom (EZv (snd p))) = zden E (fst p)) als.

  Lemma alias_e_den : forall E als e, ALS E als -> zden E (alias_e als e) = zden E e.
  Proof.
    intros E als e HA. unfold alias_e. destruct (find (fun p => expr_eqb (fst p) e) als) as [p|] eqn:F; [|reflexivity].
    apply find_some in F as [Hin Heq]. apply expr_eqb_eq in Heq. unfold ALS in HA. rewrite List.Forall_forall in HA.
    rewrite (HA p Hin), Heq. reflexivity.
  Qed.

  Lemma alias_r_den : forall E als r, ALS E als -> rden E (alias_r als r) = rden E r.
  Proof.
    intros E als r HA. destruct r as [i|e]; [reflexivity|]. unfold alias_r.
    assert (X : rden E (RZ (alias_e als e)) = rden E (RZ e)) by (cbn [rden]; rewrite !zdenp_ok, (alias_e_den E als e HA); reflexivity).
    destruct e as [z|v|v|a b|c a|o a b]; try exact X; try reflexivity.
    destruct a as [| | | |c1 a1|]; try exact X. destruct c1 as [|p|]; try exact X. destruct p; try exact X.
    destruct a1; try exact X; destruct b as [zb| | | | |]; try exact X; destruct zb; try exact X; reflexivity.
  Qed.

  Lemma alias_rs_den : forall E als rs, ALS E als -> regs_den E (map (alias_r als) rs) = regs_den E rs.
  Proof.
    intros E als rs HA. rewrite !regs_den_rdw, map_map. f_equal. apply map_ext. intros r. apply alias_r_den. exact HA.
  Qed.

  Lemma alias_W_den : forall E als W, ALS E als ->
    wden E (map (fun lh => (alias_e als (fst lh), alias_e als (snd lh))) W) = wden E W.
  Proof.
    intros E als W HA. unfold wden. rewrite map_map. apply map_ext. intros [l h]. cbn [fst snd].
    rewrite !zdenp_ok, !(alias_e_den E als _ HA). reflexivity.
  Qed.

  Lemma ALS_setz : forall E als i v, als_below i als = true -> ALS E als -> ALS (env_setz E i v) als.
  Proof.
    intros E als i v HB HA. unfold ALS, als_below in *. rewrite forallb_forall in HB. rewrite List.Forall_forall in HA |- *.
    intros p Hp. specialize (HA p Hp). specialize (HB p Hp). apply andb_prop in HB as [H1 H2].
    rewrite !zden_setz; [exact HA| exact H1|]. cbn. rewrite H2. reflexivity.
  Qed.

  Lemma ALS_setm : forall E als k m, ALS E als -> ALS (env_setm E k m) als.
  Proof.
    intros E als k m HA. unfold ALS in *. rewrite List.Forall_forall in HA |- *.
    intros p Hp. rewrite !zden_setm. apply HA. exact Hp.
  Qed.

  Lemma ALS_setcur : forall E als mo, ALS E als -> ALS (env_setcur E mo) als.
  Proof.
    intros E als mo HA. unfold ALS in *. rewrite List.Forall_forall in HA |- *.
    intros p Hp. rewrite !zden_setcur. apply HA. exact Hp.
  Qed.
  Lemma ALS_setbl : forall E als k lb, ALS E als -> ALS (env_setbl E k lb) als.
  Proof.
    intros E als k lb HA. unfold ALS in *. rewrite List.Forall_forall in HA |- *.
    intros p Hp. rewrite !zden_setbl. apply HA. exact Hp.
  Qed.

  Lemma ALS_setl : forall E als k l, ALS E als -> ALS (env_setl E k l) als.
  Proof.
    intros E als k l HA. unfold ALS in *. rewrite List.Forall_forall in HA |- *.
    intros p Hp. rewrite !zden_setl. apply HA. exact Hp.
  Qed.

  Lemma als_at_ok : forall E als i, ALS E als -> ALS E (als_at i als) /\ als_below i (als_at i als) = true.
  Proof.
    intros E als i HA. unfold als_at. destruct (als_below i als) eqn:B; [split; [exact HA| exact B]|]. split; [constructor| reflexivity].
  Qed.

  Lemma als_below_mono : forall i i' als, (i <= i')%positive -> als_below i als = true -> als_below i' als = true.
  Proof.
    intros i i' als Hi H. unfold als_below in *. rewrite forallb_forall in H |- *. intros p Hp. specialize (H p Hp).
    apply andb_prop in H as [H1 H2]. rewrite (evars_lt_mono i i' _ Hi H1). cbn [andb]. apply Pos.ltb_lt. apply Pos.ltb_lt in H2. lia.
  Qed.

  Lemma prune_leaves_sound : forall E pf0 mf0 als t K,
    ALS E als -> oblig segs G E (prune_leaves pf0 mf0 als t) K -> oblig segs G E t K.
  Proof.
    intros E pf0 mf0 als t. revert E als.
    (* [comment removed for export] *)
    assert (BINDS : forall (P1 P2 : env -> Prop) k E als nx,
      (forall E, ALS E als -> P1 E -> P2 E) ->
      ALS E als -> als_below nx als = true ->
      (fix binds (E : env) (nx : positive) (k : nat) {struct k} : Prop :=
         match k with O => P1 E | S k' => forall v : Z, binds (env_setz E nx v) (Pos.succ nx) k' end) E nx k ->
      (fix binds (E : env) (nx : positive) (k : nat) {struct k} : Prop :=
         match k with O => P2 E | S k' => forall v : Z, binds (env_setz E nx v) (Pos.succ nx) k' end) E nx k).
    { intros P1 P2 k. induction k as [|k IH]; intros E als nx IMP HA HB H; cbn in H |- *; [exact (IMP E HA H)|].
      intros v. apply (IH (env_setz E nx v) als (Pos.succ nx) IMP).
      - apply ALS_setz; assumption.
      - eapply als_below_mono; [|exact HB]. lia.
      - apply H. }
    (* [comment removed for export] *)
    assert (LBINDS : forall (P1 P2 : env -> Prop) kl E als nl,
      (forall E, ALS E als -> P1 E -> P2 E) -> ALS E als ->
      (fix lbinds (E : env) (nl : positive) (kl : nat) {struct kl} : Prop :=
         match kl with O => P1 E | S kl' => forall l : list word, lbinds (env_setl E nl l) (Pos.succ nl) kl' end) E nl kl ->
      (fix lbinds (E : env) (nl : positive) (kl : nat) {struct kl} : Prop :=
         match kl with O => P2 E | S kl' => forall l : list word, lbinds (env_setl E nl l) (Pos.succ nl) kl' end) E nl kl).
    { intros P1 P2 kl. induction kl as [|kl IH]; intros E als nl IMP HA H; cbn in H |- *; [exact (IMP E HA H)|].
      intros l. apply (IH (env_setl E nl l) als (Pos.succ nl) IMP); [apply ALS_setl; exact HA| apply H]. }
    induction t as [ss|c a IHa b IHb|i a IHa|c nx k a IHa|cpc nx k cnl ckl a IHa|lpc lnx lk lnl lkl lnm la IHla|hpc hnx hk hnl hkl hnm ha IHha hb IHhb|ss|nx k a IHa b IHb| |pc code]; intros E als K HA H; cbn [prune_leaves oblig] in H |- *; try exact H.
    - unfold leaf_oblig in H |- *. cbn [s_mf s_pf s_rs s_pc s_nx s_same s_W] in H.
      assert (SUBP : Forall (pfact_ok CS E) (s_pf ss) -> Forall (pfact_ok CS E) (List.filter (fun f => negb (pf_mem f pf0)) (s_pf ss))).
      { intros HF. apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin _]. rewrite List.Forall_forall in HF. apply HF. exact Hin. }
      assert (SUBM : forall m, Forall (mfact_ok segs L CS E m) (s_mf ss) -> Forall (mfact_ok segs L CS E m) (List.filter (fun f => negb (mf_mem f mf0)) (s_mf ss))).
      { intros m HF. apply List.Forall_forall. intros f Hf. apply filter_In in Hf as [Hin _]. rewrite List.Forall_forall in HF. apply HF. exact Hin. }
      intros m. apply mf_tele_forall. intros HM. apply pf_tele_forall. intros HF.
      specialize (H m). rewrite (alias_W_den E als (s_W ss) HA) in H.
      unfold ms_den in H |- *. cbn [s_rs s_pc] in H. rewrite (alias_rs_den E als (s_rs ss) HA) in H.
      destruct (s_same ss).
      + exact (pf_tele_apply E _ _ (mf_tele_apply E m _ _ H (SUBM m HM)) (SUBP HF)).
      + exact (pf_tele_apply E _ _ (mf_tele_apply E m _ _ H HM) (SUBP HF)).
    - destruct H as [H1 H2]. split; intros Hc; [apply (IHa E als); [exact HA| apply H1; exact Hc]| apply (IHb E als); [exact HA| apply H2; exact Hc]].
    - intros v. destruct (als_at_ok E als i HA) as [HA' HB']. apply (IHa (env_setz E i v) (als_at i als)); [apply ALS_setz; assumption| apply H].
    - destruct (als_at_ok E als nx HA) as [HA' HB'].
      exact (BINDS (fun E0 => oblig segs G E0 (prune_leaves pf0 mf0 (als_at nx als) a) K) (fun E0 => oblig segs G E0 a K) k E (als_at nx als) nx
               (fun E0 HA0 H0 => IHa E0 (als_at nx als) K HA0 H0) HA' HB' H).
    - (* [comment removed for export] *)
      destruct (als_at_ok E als nx HA) as [HA' HB'].
      refine (BINDS _ _ k E (als_at nx als) nx _ HA' HB' H). intros E1 HA1 H1.
      exact (LBINDS (fun E0 => oblig segs G E0 (prune_leaves pf0 mf0 (als_at nx als) a) K) (fun E0 => oblig segs G E0 a K) ckl E1 (als_at nx als) cnl
               (fun E0 HA0 H0 => IHa E0 (als_at nx als) K HA0 H0) HA1 H1).
    - (* [comment removed for export] *)
      destruct (als_at_ok E als lnx HA) as [HA' HB'].
      refine (BINDS _ _ lk E (als_at lnx als) lnx _ HA' HB' H). intros E1 HA1 H1.
      refine (LBINDS _ _ lkl E1 (als_at lnx als) lnl _ HA1 H1). intros E2 HA2 H2 mc mp.
      apply (IHla _ (als_at lnx als) K (ALS_setm _ _ _ _ (ALS_setm _ _ _ _ HA2))). apply H2.
    - (* [comment removed for export] *)
      destruct (als_at_ok E als hnx HA) as [HA' HB'].
      refine (BINDS _ _ hk E (als_at hnx als) hnx _ HA' HB' H). intros E1 HA1 H1.
      refine (LBINDS _ _ hkl E1 (als_at hnx als) hnl _ HA1 H1). intros E2 HA2 H2 mc mp mo lb.
      destruct (H2 mc mp mo lb) as [X1 X2]. split.
      + apply (IHha _ (als_at hnx als) K (ALS_setbl _ _ _ _ (ALS_setcur _ _ _ (ALS_setm _ _ _ _ (ALS_setm _ _ _ _ HA2))))). exact X1.
      + apply (IHhb _ (als_at hnx als) K (ALS_setbl _ _ _ _ (ALS_setcur _ _ _ (ALS_setm _ _ _ _ (ALS_setm _ _ _ _ HA2))))). exact X2.
    - destruct H as [H1 H2]. split; [apply (IHa E als); [exact HA| exact H1]|].
      destruct (als_at_ok E als nx HA) as [HA' HB'].
      exact (BINDS (fun E0 => oblig segs G E0 (prune_leaves pf0 mf0 (als_at nx als) b) K) (fun E0 => oblig segs G E0 b K) k E (als_at nx als) nx
               (fun E0 HA0 H0 => IHb E0 (als_at nx als) K HA0 H0) HA' HB' H2).
  Qed.

  Lemma alias_of_sound : forall E pf, Forall (pfact_ok CS E) pf -> ALS E (alias_of pf).
  Proof.
    intros E pf HF. unfold ALS. induction HF as [|f pf Hf HF IH]; cbn; [constructor|].
    destruct f as [| | | | | | | |a b| | |]; try exact IH. destruct a as [|j| | | |]; try exact IH.
    assert (X : zden E (eatom (EZv j)) = zden E (enorm b)).
    { rewrite eatom_den, enorm_den. cbn [zden]. unfold pfact_ok in Hf. rewrite !zdenp_ok in Hf. cbn [zden] in Hf. exact Hf. }
    destruct b; try exact IH; (constructor; [exact X| exact IH]).
  Qed.

  Theorem lx_sound : forall pm E ss ms,
    genv_ok E ->
    cfg_ok G C E -> length (s_rs ss) = 31%nat -> st_ok segs G E ss ms ->
    oblig segs G E (lx_runp segs C pl genv pm ss) TGT ->
    TGT (ecur E) ms.
  Proof.
    intros pm E ss ms GV CFG Hlen ST OB. unfold lx_runp in OB.
    set (ss1 := with_frame_seps (with_bounds (norm_ss ss))) in OB.
    match type of OB with oblig _ _ _ (if ?c then _ else _) _ => destruct c eqn:ACNX; [|destruct OB] end.
    pose proof ST as (mST & _ & _ & PFST & _). pose proof (proj1 (als_at_ok E _ (s_nx ss1) (alias_of_sound E (s_pf ss) PFST))) as ALSH. clear mST PFST.
    apply (prune_leaves_sound E _ _ _ _ _ ALSH) in OB.
    apply (phase_sound (s_nx ss1) (s_nl ss1) E GV CFG ACNX) in OB as [OB PJ].
    assert (Hlen1 : length (s_rs ss1) = 31%nat).
    { subst ss1. unfold with_frame_seps, with_bounds.
      destruct (add_pfs_rs (add_pfs (norm_ss ss) (flat_map mf_bounds (s_mf (norm_ss ss))))
                  (flat_map (frame_sep1 (s_pf (add_pfs (norm_ss ss) (flat_map mf_bounds (s_mf (norm_ss ss)))))
                                        (s_W (add_pfs (norm_ss ss) (flat_map mf_bounds (s_mf (norm_ss ss))))))
                            (s_pf (add_pfs (norm_ss ss) (flat_map mf_bounds (s_mf (norm_ss ss))))))) as (P0 & _).
      rewrite P0.
      destruct (add_pfs_rs (norm_ss ss) (flat_map mf_bounds (s_mf (norm_ss ss)))) as (P1 & _). rewrite P1, norm_ss_len. exact Hlen. }
    eapply (lx_go_sound (s_nx ss1) (s_nl ss1) _ E _ true ss1 E ms (agree_refl _ _ E) GV CFG Hlen1); [| exact PJ| exact OB].
    subst ss1. apply with_frame_seps_ok, with_bounds_ok, norm_ss_ok. exact ST.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma pf_tele_mono : forall E pf P Q, (P -> Q) -> pf_tele G E pf P -> pf_tele G E pf Q.
  Proof. intros E pf. induction pf as [|f pf IH]; intros P Q HPQ H; cbn in H |- *; [apply HPQ, H|]. intros Hf. apply (IH P Q HPQ). apply H, Hf. Qed.

  Lemma oblig_mono : forall E t (K K' : Model -> machine_state -> Prop),
    (forall mo ms, K mo ms -> K' mo ms) -> oblig segs G E t K -> oblig segs G E t K'.
  Proof.
    intros E t. revert E. induction t as [ss|c a IHa b IHb|i a IHa|c nx k a IHa|cpc nx k cnl ckl a IHa|lpc lnx lk lnl lkl lnm la IHla|hpc hnx hk hnl hkl hnm ha IHha hb IHhb|ss|nx k a IHa b IHb| |pc code]; intros E K K' HK H; cbn [oblig] in H |- *; try exact H.
    - unfold leaf_oblig in H |- *. intros m. eapply mf_tele_mono; [|exact (H m)]. intros HT.
      eapply pf_tele_mono; [|exact HT]. intros X MU WM MI. specialize (X MU WM MI).
      destruct (s_same ss); [intros Hm; apply HK; exact (X Hm)| apply HK; exact X].
    - destruct H as [H1 H2]. split; intros Hc; [eapply IHa; [exact HK| exact (H1 Hc)]| eapply IHb; [exact HK| exact (H2 Hc)]].
    - intros v. eapply IHa; [exact HK| exact (H v)].
    - revert E nx H. induction k as [|k IH]; intros E nx H; cbn in H |- *; [eapply IHa; [exact HK| exact H]|].
      intros v. apply IH. apply H.
    - revert E nx H. induction k as [|k IH]; intros E nx H; cbn in H |- *; [|intros v; apply IH; apply H].
      revert E cnl H. induction ckl as [|kl IHl]; intros E nl H; cbn in H |- *; [eapply IHa; [exact HK| exact H]|].
      intros l. apply IHl. apply H.
    - revert E lnx H. induction lk as [|k IH]; intros E nx H; cbn in H |- *; [|intros v; apply IH; apply H].
      revert E lnl H. induction lkl as [|kl IHl]; intros E nl H; cbn in H |- *; [|intros l; apply IHl; apply H].
      intros mc mp. eapply IHla; [exact HK| exact (H mc mp)].
    - revert E hnx H. induction hk as [|k IH]; intros E nx H; cbn in H |- *; [|intros v; apply IH; apply H].
      revert E hnl H. induction hkl as [|kl IHl]; intros E nl H; cbn in H |- *; [|intros l; apply IHl; apply H].
      intros mc mp mo lb. destruct (H mc mp mo lb) as [X1 X2]. split; [eapply IHha; [exact HK| exact X1]| eapply IHhb; [exact HK| exact X2]].
    - destruct H as [H1 H2]. split; [eapply IHa; [exact HK| exact H1]|].
      clear H1. revert E nx H2. induction k as [|k IH]; intros E nx H; cbn in H |- *; [eapply IHb; [exact HK| exact H]|].
      intros v. apply IH. apply H.
  Qed.

End RunSound.

(* [comment removed for export] *)
Lemma tgt_law_evtA : forall segs L CS (Q : machine_state -> Prop) (mo : Model) (P : machine_state -> Prop) ms,
  evtA segs L CS P ms -> (forall ms', P ms' -> evtA segs L CS Q ms') -> evtA segs L CS Q ms.
Proof. intros segs L CS Q mo P ms H K. eapply evtA_cut; [exact H| exact K]. Qed.
(* [comment removed for export] *)
Lemma tgt_law_evt : forall segs L (CS : Z -> Prop) (Q : machine_state -> Prop) (mo : Model) (P : machine_state -> Prop) ms,
  evtA segs L CS P ms -> (forall ms', P ms' -> evt segs Q ms') -> evt segs Q ms.
Proof.
  intros segs L CS Q mo P ms (ms1 & ST1 & HP) K. destruct (K _ HP) as (ms2 & ST2 & HQ). exists ms2. split; [|exact HQ].
  eapply msteps_trans; [eapply mstepsA_msteps; exact ST1| exact ST2].
Qed.
(* [comment removed for export] *)
Definition tgt_aevtM (segs : list Segment) (Q : config -> Prop) (mo : Model) (ms : machine_state) : Prop :=
  MOK mo -> aevtM segs mo Q ms.
Lemma tgt_law_aevtM : forall segs L (CS : Z -> Prop) (Q : config -> Prop) (mo : Model) (P : machine_state -> Prop) ms,
  evtA segs L CS P ms -> (forall ms', P ms' -> tgt_aevtM segs Q mo ms') -> tgt_aevtM segs Q mo ms.
Proof.
  intros segs L CS Q mo P ms (ms1 & ST1 & HP) K MK. eapply aevtM_msteps; [exact MK| eapply mstepsA_msteps; exact ST1| exact (K _ HP MK)].
Qed.

End LXH.
