(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec ShapeAlg SpinAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanAcctShapeCfg AsanPlanSoundCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesY.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Unset Lia Cache.
Open Scope Z_scope.
Section WithFP1. Context {FP : PropExec.FPState}.
Section YNodes.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Hypothesis SHADOW_ok : shadow_ok A.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.

  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).

  (* [comment removed for export] *)
  Lemma shdisj_all_sound : forall ms cs b0 n0 E R FULL model,
    CSOK E cs R FULL model ->
    CSOK E (YN.shdisj_all A cs b0 n0 ms) R FULL model
    /\ pc (YN.shdisj_all A cs b0 n0 ms) = pc cs /\ nxt (YN.shdisj_all A cs b0 n0 ms) = nxt cs.
  Proof.
    induction ms as [|m rest IH]; intros cs b0 n0 E R FULL model HC; cbn [YN.shdisj_all].
    - split; [exact HC | split; reflexivity].
    - destruct (is_fog m).
      + exact (IH cs b0 n0 E R FULL model HC).
      + destruct (node_shdisj A cs b0 n0 (am_base m) (am_len m)) as [cs'|] eqn:Hn.
        * destruct (shdisj_sound SEGS A LIMIT SHADOW_ok SINV argH FS0 cs b0 n0 (am_base m) (am_len m) cs' E R FULL model HC Hn) as [HC' Hpc].
          assert (Hnx : nxt cs' = nxt cs).
          { rewrite node_shdisj_eq in Hn. unfold node_shdisj_ref in Hn.
            destruct (split_lit b0), (split_lit (am_base m)), (shadow_of A (kn cs) b0 n0) as [[? ?] ?], (shadow_of A (kn cs) (am_base m) (am_len m)) as [[? ?] ?].
            match type of Hn with (if ?c then _ else _) = _ => destruct c; [|discriminate] end. injection Hn as <-. reflexivity. }
          destruct (IH cs' b0 n0 E R FULL model HC') as (H1 & H2 & H3). rewrite Hpc in H2. rewrite Hnx in H3.
          split; [exact H1 | split; [exact H2 | exact H3]].
        * exact (IH cs b0 n0 E R FULL model HC).
  Qed.

  Theorem node_shdisj_maps_sound : APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (YN.node_shdisj_maps A).
  Proof.
    intros cs cs' E R FULL model T HC _ Hn Hk. unfold YN.node_shdisj_maps in Hn.
    destruct (a_maps cs) as [|m0 rest]; [discriminate|]. destruct (is_fog m0); [discriminate|]. injection Hn as <-.
    destruct (shdisj_all_sound rest cs (am_base m0) (am_len m0) E R FULL model HC) as (HC' & Hpc & Hnx).
    specialize (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E)) HC' eq_refl).
    rewrite Hpc in Hk. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma kn_node_sound : forall (node : acs -> option acs),
    (forall cs cs' E R FULL model, CSOK E cs R FULL model -> node cs = Some cs' ->
        exists k', cs' = set_kn cs k' /\ know_ok SEGS E (Mr A argH E cs model FULL) k') ->
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always node.
  Proof.
    intros node Hnode cs cs' E R FULL model T HC _ Hn Hk.
    destruct (Hnode cs cs' E R FULL model HC Hn) as (k' & -> & HK').
    specialize (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    rewrite pc_set_kn in Hk. apply Hk; [|reflexivity]. apply cs_ok_set_kn; [exact HC | exact HK'].
  Qed.

  #[local] Notation u := bv_unsigned.
  Lemma kr_ok : forall E M e lo hi, lo <= u (edenot E e) <= hi -> kentry_ok SEGS E M (KRange e lo hi).
  Proof. intros E M e lo hi [H1 H2]. cbn [kentry_ok]. split; assumption. Qed.
  Lemma xt1 : forall E e c, xt_den E [(e, c)] = u (edenot E e) + c.
  Proof. intros. cbn [xt_den]. lia. Qed.
  Lemma xt2 : forall E e1 c1 e2 c2, xt_den E [(e1, c1); (e2, c2)] = u (edenot E e1) + c1 + u (edenot E e2) + c2.
  Proof. intros. cbn [xt_den]. lia. Qed.
  Lemma u_esub : forall E a b, u (edenot E (esub a b)) = (u (edenot E a) - u (edenot E b)) mod 2 ^ 64.
  Proof. intros. unfold esub. rewrite mkAlu_denot. apply u_sub64. Qed.
  Lemma u_eadd : forall E a b, u (edenot E (eadd a b)) = (u (edenot E a) + u (edenot E b)) mod 2 ^ 64.
  Proof. intros. unfold eadd. rewrite mkAlu_denot. apply u_add64. Qed.
  Lemma u_eaddz : forall E a z, 0 <= z -> u (edenot E a) + z < 2 ^ 64 -> u (edenot E (eaddz a z)) = u (edenot E a) + z.
  Proof.
    intros E a z Hz Hnw. unfold eaddz. rewrite mkAlu_denot. rewrite u_add64. cbn [edenot].
    pose proof (u64_range (edenot E a)). rewrite (u64_lit z) by lia. apply Z.mod_small. lia.
  Qed.
  Lemma u_mkSrl : forall E M k e s, know_ok SEGS E M k -> 1 <= s <= 62 ->
    u (edenot E (mkSrl k e s)) = u (edenot E e) / 2 ^ s.
  Proof.
    intros E M k e s HK Hs.
    rewrite (mkSrl_denot SEGS E M k e s (Z_to_bv 64 s) HK) by (rewrite u64_lit by lia; apply Z.mod_small; lia).
    rewrite alu_srl. unfold v_srl. rewrite (u64_lit s) by lia. rewrite (Z.mod_small s 64) by lia.
    rewrite Z.shiftr_div_pow2 by lia. pose proof (u64_range (edenot E e)) as He.
    assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
    apply u64_lit. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
  Qed.

  (* [comment removed for export] *)
  Theorem node_linkrange_sound : forall e1 e2,
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => YN.node_linkrange cs e1 e2).
  Proof.
    intros e1 e2. apply kn_node_sound. intros cs cs' E R FULL model HC Hn. rewrite YN.node_linkrange_eq in Hn. unfold YN.node_linkrange_ref in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (xlo (kn cs) e2) as [lo|] eqn:Hlo; [|discriminate]. destruct (xhi (kn cs) e2) as [hi|] eqn:Hhi; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
    apply andb_prop in Hc as [G1 G2].
    pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G1) as L1. pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G2) as L2.
    rewrite !xt1 in L1, L2.
    pose proof (xlo_sound SEGS E _ (kn cs) _ _ HK Hlo). pose proof (xhi_sound SEGS E _ (kn cs) _ _ HK Hhi).
    eexists. split; [reflexivity|]. constructor; [apply kr_ok; lia | exact HK].
  Qed.

  (* [comment removed for export] *)
  Theorem node_summeet_sound : forall e1 ea eb,
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => YN.node_summeet cs e1 ea eb).
  Proof.
    intros e1 ea eb. apply kn_node_sound. intros cs cs' E R FULL model HC Hn. rewrite YN.node_summeet_eq in Hn. unfold YN.node_summeet_ref in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (xlo (kn cs) e1) as [lo1|] eqn:Hlo1; [|discriminate]. destruct (xhi (kn cs) e1) as [hi1|] eqn:Hhi1; [|discriminate].
    destruct (xlo (kn cs) ea) as [loa|] eqn:Hloa; [|discriminate]. destruct (xhi (kn cs) ea) as [hia|] eqn:Hhia; [|discriminate].
    destruct (xlo (kn cs) eb) as [lob|] eqn:Hlob; [|discriminate]. destruct (xhi (kn cs) eb) as [hib|] eqn:Hhib; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
    apply andb_prop in Hc as [G1 G2].
    pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G1) as L1. pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G2) as L2.
    rewrite xt1, xt2 in L1, L2.
    pose proof (xlo_sound SEGS E _ (kn cs) _ _ HK Hlo1). pose proof (xhi_sound SEGS E _ (kn cs) _ _ HK Hhi1).
    pose proof (xlo_sound SEGS E _ (kn cs) _ _ HK Hloa). pose proof (xhi_sound SEGS E _ (kn cs) _ _ HK Hhia).
    pose proof (xlo_sound SEGS E _ (kn cs) _ _ HK Hlob). pose proof (xhi_sound SEGS E _ (kn cs) _ _ HK Hhib).
    eexists. split; [reflexivity|]. constructor; [apply kr_ok; lia | exact HK].
  Qed.

  (* [comment removed for export] *)
  Lemma take_kzero_lit_sound : forall E M k a L rest,
    know_ok SEGS E M k -> YN.take_kzero_lit k a = Some (L, rest) ->
    know_ok SEGS E M rest /\ kentry_ok SEGS E M (KZero (SA (ELit 0) a) (ELit L)).
  Proof.
    intros E M k a L rest. revert rest. induction k as [|K k IH]; intros rest HK H; [discriminate|].
    apply Forall_cons_iff in HK as [HKK Hk]. cbn [YN.take_kzero_lit] in H.
    assert (DFLT : (match YN.take_kzero_lit k a with Some (L', r') => Some (L', K :: r') | None => None end) = Some (L, rest) ->
                   know_ok SEGS E M rest /\ kentry_ok SEGS E M (KZero (SA (ELit 0) a) (ELit L))).
    { intros H'. destruct (YN.take_kzero_lit k a) as [[L' r']|] eqn:Ht; [|discriminate]. injection H' as <- <-.
      destruct (IH r' Hk eq_refl) as [H1 H2]. split; [constructor; assumption | exact H2]. }
    destruct K as [ | za zl | | | | | | | |  | kinv_id kinv_args]; try (exact (DFLT H)).
    destruct za as [[lit| | | | | | | ] o]; try (exact (DFLT H)). destruct lit; try (exact (DFLT H)).
    destruct zl as [Lz| | | | | | | ]; try (exact (DFLT H)).
    destruct (Z.eqb_spec o a) as [->|Hne]; [|exact (DFLT H)].
    injection H as <- <-. split; [exact Hk | exact HKK].
  Qed.
  Theorem node_splitzero_sound : forall a m,
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => YN.node_splitzero cs a m).
  Proof.
    intros a m. apply kn_node_sound. intros cs cs' E R FULL model HC Hn. unfold YN.node_splitzero in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (YN.take_kzero_lit (kn cs) a) as [[L rest]|] eqn:Ht; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
    apply andb_prop in Hc as [Hc HL]. apply andb_prop in Hc as [Hc Ha]. apply andb_prop in Hc as [Hm0 HmL].
    apply Z.ltb_lt in Hm0. apply Z.ltb_lt in HmL. apply Z.leb_le in Ha. apply Z.ltb_lt in HL. unfold two64 in HL.
    destruct (take_kzero_lit_sound E _ (kn cs) a L rest HK Ht) as [Hrest HZ].
    cbn [kentry_ok] in HZ. destruct HZ as [Hfl Hz]. unfold flat, estart, elenZ in Hfl, Hz. cbn [a_base a_off edenot] in Hfl, Hz.
    rewrite !u64_lit in Hfl by lia. rewrite !u64_lit in Hz by lia.
    eexists. split; [reflexivity|].
    constructor; [|constructor; [|exact Hrest]]; cbn [kentry_ok]; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite !u64_lit by lia.
    - split; [lia|]. intros i Hi. apply Hz. lia.
    - split; [lia|]. intros i Hi. replace (0 + (a + m) + i) with (0 + a + (m + i)) by lia. apply Hz. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma disj_len_scan_sound : forall E M allk k x y z m,
    know_ok SEGS E M allk -> know_ok SEGS E M k ->
    u (edenot E y) + 1 <= u (edenot E x) ->
    YN.disj_len_scan k allk x y z m = true ->
    u (edenot E y) + u (edenot E z) + m <= u (edenot E x).
  Proof.
    intros E M allk k x y z m HA HK Hxy. induction k as [|K rest IH]; [discriminate|].
    inversion HK as [|K' rest' HK1 HKr]; subst K' rest'.
    assert (CASE : forall b1 o1 n1 b2 o2 n2,
      kentry_ok SEGS E M (KDisj (SA b1 o1) n1 (SA b2 o2) n2) ->
      ((if (expr_eqb b1 x && Z.eqb o1 0 && expr_eqb b2 y && Z.eqb o2 0)%bool then lin_ge0 allk [(n2, 0)] [(z, m)]
        else if (expr_eqb b1 y && Z.eqb o1 0 && expr_eqb b2 x && Z.eqb o2 0)%bool then lin_ge0 allk [(n1, 0)] [(z, m)]
        else false) || YN.disj_len_scan rest allk x y z m)%bool = true ->
      u (edenot E y) + u (edenot E z) + m <= u (edenot E x)).
    { intros b1 o1 n1 b2 o2 n2 HD H. apply orb_prop in H as [H|H]; [|exact (IH HKr H)].
      cbn [kentry_ok] in HD.
      pose proof (u64_range (edenot E n1)) as R1. pose proof (u64_range (edenot E n2)) as R2.
      destruct (expr_eqb b1 x && Z.eqb o1 0 && expr_eqb b2 y && Z.eqb o2 0)%bool eqn:C1.
      - apply andb_prop in C1 as [C1 C4]. apply andb_prop in C1 as [C1 C3]. apply andb_prop in C1 as [C1 C2].
        apply expr_eqb_eq in C1. apply expr_eqb_eq in C3. apply Z.eqb_eq in C2. apply Z.eqb_eq in C4. subst b1 b2 o1 o2.
        pose proof (lin_ge0_sound SEGS E _ allk _ _ HA H) as L. rewrite xt1, xt1 in L. unfold AX2S.estart, AX2S.elenZ in HD. cbn [a_base a_off] in HD. lia.
      - destruct (expr_eqb b1 y && Z.eqb o1 0 && expr_eqb b2 x && Z.eqb o2 0)%bool eqn:C2; [|discriminate].
        apply andb_prop in C2 as [C2 C5]. apply andb_prop in C2 as [C2 C4]. apply andb_prop in C2 as [C2 C3].
        apply expr_eqb_eq in C2. apply expr_eqb_eq in C4. apply Z.eqb_eq in C3. apply Z.eqb_eq in C5. subst b1 b2 o1 o2.
        pose proof (lin_ge0_sound SEGS E _ allk _ _ HA H) as L. rewrite xt1, xt1 in L. unfold AX2S.estart, AX2S.elenZ in HD. cbn [a_base a_off] in HD. lia. }
    cbn [YN.disj_len_scan]. destruct K as [| | | | | | |[b1 o1] n1 [b2 o2] n2| | | kinv_id kinv_args]; try exact (IH HKr).
    exact (CASE b1 o1 n1 b2 o2 n2 HK1).
  Qed.
  Theorem node_disjdom_sound : forall x y z m,
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => YN.node_disjdom cs x y z m).
  Proof.
    intros x y z m. apply kn_node_sound. intros cs cs' E R FULL model HC Hn. rewrite YN.node_disjdom_eq in Hn. unfold YN.node_disjdom_ref in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (xhi (kn cs) x) as [hx|] eqn:Hx; [|discriminate]. destruct (xhi (kn cs) y) as [hy|] eqn:Hy; [|discriminate].
    destruct (xhi (kn cs) z) as [hz|] eqn:Hz; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
    apply andb_prop in Hc as [Hc G]. apply andb_prop in Hc as [Hm Hnw]. apply Z.leb_le in Hm. apply Z.ltb_lt in Hnw. unfold two64 in Hnw.
    pose proof (xhi_sound SEGS E _ (kn cs) _ _ HK Hx). pose proof (xhi_sound SEGS E _ (kn cs) _ _ HK Hy). pose proof (xhi_sound SEGS E _ (kn cs) _ _ HK Hz).
    pose proof (u64_range (edenot E x)). pose proof (u64_range (edenot E y)). pose proof (u64_range (edenot E z)).
    assert (L : u (edenot E y) + u (edenot E z) + m <= u (edenot E x)).
    { apply orb_prop in G as [G|G].
      - pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G) as L. rewrite xt1, xt2 in L. lia.
      - apply andb_prop in G as [G1 G2]. pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G1) as L1. rewrite xt1, xt1 in L1.
        apply (disj_len_scan_sound E _ (kn cs) (kn cs) x y z m HK HK); [lia | exact G2]. }
    eexists. split; [reflexivity|]. constructor; [|exact HK]. apply kr_ok.
    rewrite u_esub, u_eadd. rewrite (Z.mod_small (u (edenot E y) + u (edenot E z))) by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma clip_kzero_sound : forall E M allk k sb sk Lnew k',
    know_ok SEGS E M allk -> know_ok SEGS E M k -> YN.clip_kzero k sb sk Lnew allk = Some k' -> know_ok SEGS E M k'.
  Proof.
    intros E M allk k sb sk Lnew. induction k as [|K k IH]; intros k' Hall HK H; [discriminate|].
    apply Forall_cons_iff in HK as [HKK Hk]. cbn [YN.clip_kzero] in H.
    assert (DFLT : (match YN.clip_kzero k sb sk Lnew allk with Some r' => Some (K :: r') | None => None end) = Some k' -> know_ok SEGS E M k').
    { intros H'. destruct (YN.clip_kzero k sb sk Lnew allk) as [r'|] eqn:Ht; [|discriminate]. injection H' as <-.
      constructor; [exact HKK | exact (IH r' Hall Hk eq_refl)]. }
    destruct K as [ | za zl | | | | | | | |  | kinv_id kinv_args]; try (exact (DFLT H)). destruct za as [b o].
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end; [|exact (DFLT H)].
    injection H as <-. apply andb_prop in Hc as [_ G].
    pose proof (lin_ge0_sound SEGS E _ allk _ _ Hall G) as L. rewrite !xt1 in L.
    constructor; [|exact Hk]. cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz].
    unfold flat, elenZ in *. pose proof (u64_range (edenot E Lnew)).
    split; [lia|]. intros i Hi. apply Hz. lia.
  Qed.
  Theorem node_zeroprefix_sound : forall b Lnew,
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => YN.node_zeroprefix cs b Lnew).
  Proof.
    intros b Lnew. apply kn_node_sound. intros cs cs' E R FULL model HC Hn. unfold YN.node_zeroprefix in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (split_lit b) as [sb sk]. destruct (YN.clip_kzero (kn cs) sb sk Lnew (kn cs)) as [k'|] eqn:Hcl; [|discriminate].
    injection Hn as <-. eexists. split; [reflexivity|]. exact (clip_kzero_sound E _ (kn cs) (kn cs) sb sk Lnew k' HK HK Hcl).
  Qed.

  (* [comment removed for export] *)
  Theorem node_srlstep_sound : forall x a s,
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => YN.node_srlstep cs x a s).
  Proof.
    intros x a s. apply kn_node_sound. intros cs cs' E R FULL model HC Hn. unfold YN.node_srlstep in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (xhi (kn cs) x) as [hx|] eqn:Hx; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
    apply andb_prop in Hc as [Hc Hnw]. apply andb_prop in Hc as [Hc Hs2]. apply andb_prop in Hc as [Ha Hs1].
    apply Z.leb_le in Ha. apply Z.leb_le in Hs1. apply Z.leb_le in Hs2. apply Z.ltb_lt in Hnw. unfold two64 in Hnw.
    pose proof (xhi_sound SEGS E _ (kn cs) _ _ HK Hx) as X. pose proof (u64_range (edenot E x)) as Rx.
    set (M := Mr A argH E cs model FULL) in *.
    eexists. split; [reflexivity|]. constructor; [|exact HK]. apply kr_ok.
    rewrite u_esub. rewrite (u_mkSrl E M (kn cs) (eaddz x a) s HK) by lia. rewrite (u_mkSrl E M (kn cs) x s HK) by lia.
    rewrite (u_eaddz E x a) by lia.
    set (v := u (edenot E x)) in *. set (q := 2 ^ s) in *.
    assert (Hq : 2 <= q) by (subst q; change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
    assert (D1 : v / q <= (v + a) / q) by (apply Z.div_le_mono; lia).
    assert (D2 : (v + a) / q - v / q <= (a + q - 1) / q).
    { pose proof (Z.div_mod v q ltac:(lia)) as E1. pose proof (Z.mod_pos_bound v q ltac:(lia)) as B1.
      replace (v + a) with (q * (v / q) + (v mod q + a)) by lia. rewrite Z.add_comm, (Z.mul_comm q), Z.div_add by lia.
      assert ((v mod q + a) / q <= (a + q - 1) / q) by (apply Z.div_le_mono; lia). lia. }
    assert (D3 : (a + q - 1) / q < 2 ^ 64).
    { apply Z.div_lt_upper_bound; [lia|]. nia. }
    rewrite Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem node_srlrange_sound : forall e s,
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => YN.node_srlrange cs e s).
  Proof.
    intros e s. apply kn_node_sound. intros cs cs' E R FULL model HC Hn. unfold YN.node_srlrange in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (erange (kn cs) e) as [[lo hi]|] eqn:He; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
    apply andb_prop in Hc as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.leb_le in Hs2.
    pose proof (erange_sound SEGS E _ (kn cs) e lo hi HK He) as X.
    set (M := Mr A argH E cs model FULL) in *.
    eexists. split; [reflexivity|]. constructor; [|exact HK]. apply kr_ok.
    rewrite (u_mkSrl E M (kn cs) e s HK) by lia. assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
    split; apply Z.div_le_mono; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma zbv8_of_lit64 : forall c, Z_to_bv 8 (u (Z_to_bv 64 c)) = Z_to_bv 8 c.
  Proof.
    intros c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with (2 ^ 8).
    rewrite Z.mod_mod_divide; [reflexivity | exists (2 ^ 56); reflexivity].
  Qed.
  Lemma rdn1_of_M : forall M (a : word) b, M a = Some b -> rdn SEGS M a 1 = Some [b].
  Proof. intros M a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma find_byte_sound : forall E M allk k ab off w,
    know_ok SEGS E M allk -> know_ok SEGS E M k -> YN.find_byte k allk ab off = Some w ->
    flat E (SA ab off) 1 ->
    rdn SEGS M (adenot E (SA ab off)) 1 = Some (word_to_le_bytes 1 (edenot E w)).
  Proof.
    intros E M allk k ab off w Hall. induction k as [|K k IH]; intros HK H Hfl; [discriminate|].
    apply Forall_cons_iff in HK as [HKK Hk]. cbn [YN.find_byte] in H.
    destruct K as [a n v | | | | | | | | fa fl c |  | kinv_id kinv_args]; try (exact (IH Hk H Hfl)).
    - (* [comment removed for export] *) destruct a as [b o]. destruct n as [|[|n]]; try (exact (IH Hk H Hfl)).
      destruct (expr_eqb b ab) eqn:Hb; [|exact (IH Hk H Hfl)]. destruct (Z.eqb_spec o off) as [Ho|Ho]; [|exact (IH Hk H Hfl)].
      cbn [andb] in H. injection H as <-. apply expr_eqb_eq in Hb. subst b o.
      cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & HR). exact HR.
    - (* [comment removed for export] *) destruct fa as [b o].
      destruct (expr_eqb b ab) eqn:Hb; [|exact (IH Hk H Hfl)]. destruct (Z.leb_spec o off) as [Ho|Ho]; [|exact (IH Hk H Hfl)].
      destruct (xlo allk fl) as [lo|] eqn:Hlo; [|exact (IH Hk H Hfl)].
      destruct (Z.ltb_spec (off - o) lo) as [Hol|Hol]; [|exact (IH Hk H Hfl)].
      cbn [andb] in H. injection H as <-. apply expr_eqb_eq in Hb. subst b.
      pose proof (xlo_sound SEGS E M allk fl lo Hall Hlo) as Xlo.
      cbn [kentry_ok] in HKK. destruct HKK as [Hff HF]. unfold elenZ in HF, Hff.
      specialize (HF (off - o) ltac:(lia)). unfold estart in HF. cbn [a_base a_off] in HF.
      replace (u (edenot E ab) + o + (off - o)) with (u (edenot E ab) + off) in HF by lia.
      assert (Ha : adenot E (SA ab off) = Z_to_bv 64 (u (edenot E ab) + off)).
      { rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E (SA ab off))). rewrite (flat_u E (SA ab off) 1 Hfl). reflexivity. }
      rewrite Ha. rewrite (rdn1_of_M M _ _ HF). cbn [word_to_le_bytes Z_to_le_bytes edenot]. rewrite zbv8_of_lit64. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma find_byte2_sound : forall E M k ab off w,
    know_ok SEGS E M k -> YN.find_byte2 SEGS k ab off = Some w ->
    flat E (SA ab off) 1 ->
    rdn SEGS M (adenot E (SA ab off)) 1 = Some (word_to_le_bytes 1 (edenot E w)).
  Proof.
    intros E M k ab off w HK H Hfl. unfold YN.find_byte2 in H.
    destruct (YN.find_byte k k ab off) as [w0|] eqn:Hfb.
    - injection H as <-. exact (find_byte_sound E M k k ab off w0 HK HK Hfb Hfl).
    - destruct (know_byte_lit SEGS k ab off) as [z|] eqn:Hz; [|discriminate]. injection H as <-.
      destruct (know_byte_lit_sound SEGS E M k ab off z HK Hz Hfl) as [HR _].
      rewrite HR. cbn [word_to_le_bytes Z_to_le_bytes edenot]. rewrite zbv8_of_lit64. reflexivity.
  Qed.

  Theorem node_bytespell_sound : forall a off V,
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => YN.node_bytespell SEGS cs a off V).
  Proof.
    intros a off V. apply kn_node_sound. intros cs cs' E R FULL model HC Hn. rewrite YN.node_bytespell_eq in Hn. unfold YN.node_bytespell_ref in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (split_lit (eaddz a off)) as [ab ao].
    destruct (YN.find_byte2 SEGS (kn cs) ab ao) as [w|] eqn:Hfb; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
    apply andb_prop in Hc as [Hc G2]. apply andb_prop in Hc as [Hfl G1].
    set (M := Mr A argH E cs model FULL) in *.
    pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G1) as L1. pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G2) as L2.
    rewrite !xt1 in L1, L2. rewrite (extK_denot SEGS E M (kn cs) w HK) in L1, L2.
    assert (HV : edenot E V = edenot E w) by (apply bv_eq; lia).
    destruct (flat_x_sound SEGS E M (kn cs) ab ao (ELit 1) HK Hfl) as (F1 & F2 & _).
    replace (u (edenot E (ELit 1))) with 1 in F2 by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    assert (Hflat : flat E (SA ab ao) 1) by (unfold flat; lia).
    eexists. split; [reflexivity|]. constructor; [|exact HK].
    cbn [kentry_ok]. split; [lia|]. split; [exact Hflat|].
    rewrite HV. exact (find_byte2_sound E M (kn cs) ab ao w HK Hfb Hflat).
  Qed.

  (* [comment removed for export] *)
  Lemma find_word_sound : forall E M k ab off n w,
    know_ok SEGS E M k -> YN.find_word k ab off n = Some w -> kentry_ok SEGS E M (KWord (SA ab off) n w).
  Proof.
    intros E M k ab off n w. induction k as [|K k IH]; intros HK H; [discriminate|].
    apply Forall_cons_iff in HK as [HKK Hk]. cbn [YN.find_word] in H.
    destruct K as [a m v | | | | | | | | |  | ]; try (exact (IH Hk H)).
    destruct a as [b o].
    destruct (expr_eqb b ab) eqn:Hb; [|exact (IH Hk H)]. destruct (Z.eqb_spec o off) as [Ho|Ho]; [|exact (IH Hk H)].
    destruct (Nat.eqb_spec m n) as [Hm|Hm]; [|exact (IH Hk H)].
    cbn [andb] in H. injection H as <-. apply expr_eqb_eq in Hb. subst b o m. exact HKK.
  Qed.

  Theorem node_wordspell_sound : forall a off n V,
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => YN.node_wordspell cs a off n V).
  Proof.
    intros a off n V. apply kn_node_sound. intros cs cs' E R FULL model HC Hn. rewrite YN.node_wordspell_eq in Hn. unfold YN.node_wordspell_ref in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (split_lit (eaddz a off)) as [ab ao].
    destruct (YN.find_word (kn cs) ab ao (Z.to_nat n)) as [w|] eqn:Hfw; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
    apply andb_prop in Hc as [G1 G2].
    set (M := Mr A argH E cs model FULL) in *.
    pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G1) as L1. pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G2) as L2.
    rewrite !xt1 in L1, L2.
    assert (HV : edenot E V = edenot E w) by (apply bv_eq; lia).
    pose proof (find_word_sound E M (kn cs) ab ao (Z.to_nat n) w HK Hfw) as HW.
    eexists. split; [reflexivity|]. constructor; [|exact HK].
    cbn [kentry_ok] in HW |- *. rewrite HV. exact HW.
  Qed.

  (* [comment removed for export] *)
  Theorem node_bytespell_alt_sound : forall a off V a2,
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => YN.node_bytespell_alt SEGS cs a off V a2).
  Proof.
    intros a off V a2. apply kn_node_sound. intros cs cs' E R FULL model HC Hn. rewrite YN.node_bytespell_alt_eq in Hn. unfold YN.node_bytespell_alt_ref in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (split_lit (eaddz a off)) as [ab ao]. destruct (split_lit (eaddz a2 off)) as [ab2 ao2].
    destruct (YN.find_byte2 SEGS (kn cs) ab2 ao2) as [w|] eqn:Hfb; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
    apply andb_prop in Hc as [Hc G2]. apply andb_prop in Hc as [Hc G1]. apply andb_prop in Hc as [Hc A2].
    apply andb_prop in Hc as [Hc A1]. apply andb_prop in Hc as [Hfl Hfl2].
    set (M := Mr A argH E cs model FULL) in *.
    pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G1) as L1. pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK G2) as L2.
    pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK A1) as LA1. pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK A2) as LA2.
    rewrite !xt1 in L1, L2, LA1, LA2. rewrite (extK_denot SEGS E M (kn cs) w HK) in L1, L2.
    assert (HV : edenot E V = edenot E w) by (apply bv_eq; lia).
    destruct (flat_x_sound SEGS E M (kn cs) ab ao (ELit 1) HK Hfl) as (F1 & F2 & _).
    destruct (flat_x_sound SEGS E M (kn cs) ab2 ao2 (ELit 1) HK Hfl2) as (F1' & F2' & _).
    replace (u (edenot E (ELit 1))) with 1 in F2, F2' by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    assert (Hflat : flat E (SA ab ao) 1) by (unfold flat; lia).
    assert (Hflat2 : flat E (SA ab2 ao2) 1) by (unfold flat; lia).
    assert (HA : adenot E (SA ab ao) = adenot E (SA ab2 ao2)).
    { rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E (SA ab ao))), <- (Z_to_bv_bv_unsigned 64 (adenot E (SA ab2 ao2))).
      rewrite (flat_u E (SA ab ao) 1 Hflat), (flat_u E (SA ab2 ao2) 1 Hflat2). unfold estart. cbn [a_base a_off]. f_equal. lia. }
    eexists. split; [reflexivity|]. constructor; [|exact HK].
    cbn [kentry_ok]. split; [lia|]. split; [exact Hflat|].
    rewrite HV, HA. exact (find_byte2_sound E M (kn cs) ab2 ao2 w HK Hfb Hflat2).
  Qed.

  (* [comment removed for export] *)
  Lemma andrange1_sound : forall E M k x, know_ok SEGS E M k -> know_ok SEGS E M (YN.andrange1 k x).
  Proof.
    intros E M k x HK. unfold YN.andrange1.
    destruct (xlo k x) as [lo|] eqn:Hlo; [|constructor]. destruct (xhi k x) as [hi|] eqn:Hhi; [|constructor].
    match goal with |- know_ok _ _ _ (if ?c then _ else _) => destruct c eqn:Hc; [|constructor] end.
    apply andb_prop in Hc as [Hc Hb]. apply andb_prop in Hc as [H0 H64]. apply Z.leb_le in H0. apply Z.ltb_lt in H64. apply Z.eqb_eq in Hb.
    pose proof (xlo_sound SEGS E M k _ _ HK Hlo) as L. pose proof (xhi_sound SEGS E M k _ _ HK Hhi) as Hh.
    constructor; [|constructor]. apply kr_ok.
    rewrite (mkAnd_denot SEGS E M k x (ELit 7) HK). rewrite u_and64. cbn [edenot]. rewrite (u64_lit 7) by lia.
    change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    set (v := u (edenot E x)) in *.
    assert (Dv : v / 8 = lo / 8).
    { assert (lo / 8 <= v / 8) by (apply Z.div_le_mono; lia). assert (v / 8 <= hi / 8) by (apply Z.div_le_mono; lia). lia. }
    pose proof (Z.div_mod v 8 ltac:(lia)) as Ev. pose proof (Z.div_mod lo 8 ltac:(lia)) as Elo. pose proof (Z.div_mod hi 8 ltac:(lia)) as Ehi.
    pose proof (Z.mod_pos_bound v 8 ltac:(lia)). pose proof (Z.mod_pos_bound lo 8 ltac:(lia)). pose proof (Z.mod_pos_bound hi 8 ltac:(lia)).
    rewrite Dv in Ev. rewrite Hb in Ev, Elo. lia.
  Qed.
  Theorem node_andrange_sound : APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (YN.node_andrange).
  Proof.
    apply kn_node_sound. intros cs cs' E R FULL model HC Hn. unfold YN.node_andrange in Hn. injection Hn as <-.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    eexists. split; [reflexivity|].
    unfold know_ok. apply Forall_app. split; [apply andrange1_sound; exact HK|].
    apply Forall_app. split; [apply andrange1_sound; exact HK | exact HK].
  Qed.

  Theorem y_xn_sound : forall id args, APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (YN.xn SEGS A id args).
  Proof.
    intros id args.
    assert (NONE : APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun _ => None)) by (intros cs cs' E R FULL model TT _ _ H; discriminate H).
    unfold YN.xn.
    do 27 (destruct id as [|id]; [exact NONE|]).
    destruct id as [|id]; [apply node_shdisj_maps_sound|].
    destruct id as [|id]. { destruct args as [|e1 [|e2 [|? ?]]]; try exact NONE. apply node_linkrange_sound. }
    destruct id as [|id]. { destruct args as [|[a| | | | | | | ] [|[m| | | | | | | ] [|? ?]]]; try exact NONE. apply node_splitzero_sound. }
    destruct id as [|id]. { destruct args as [|x [|y [|z [|[m| | | | | | | ] [|? ?]]]]]; try exact NONE. apply node_disjdom_sound. }
    destruct id as [|id]. { destruct args as [|b [|L [|? ?]]]; try exact NONE. apply node_zeroprefix_sound. }
    destruct id as [|id]. { destruct args as [|x [|[a| | | | | | | ] [|[s'| | | | | | | ] [|? ?]]]]; try exact NONE. apply node_srlstep_sound. }
    destruct id as [|id]. { destruct args as [|e [|[s'| | | | | | | ] [|? ?]]]; try exact NONE. apply node_srlrange_sound. }
    destruct id as [|id]. { destruct args as [|a [|[off| | | | | | | ] [|v [|? ?]]]]; try exact NONE. apply node_bytespell_sound. }
    destruct id as [|id]. { apply node_andrange_sound. }
    destruct id as [|id]. { destruct args as [|a [|[off| | | | | | | ] [|[n| | | | | | | ] [|v [|? ?]]]]]; try exact NONE. apply node_wordspell_sound. }
    destruct id as [|id]. { destruct args as [|a [|[off| | | | | | | ] [|v [|a2 [|? ?]]]]]; try exact NONE. apply node_bytespell_alt_sound. }
    destruct id as [|id]. { destruct args as [|e1 [|ea [|eb [|? ?]]]]; try exact NONE. apply node_summeet_sound. }
    exact NONE.
  Qed.
End YNodes.
End WithFP1.

