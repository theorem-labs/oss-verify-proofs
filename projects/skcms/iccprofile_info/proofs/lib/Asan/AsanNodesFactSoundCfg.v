(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec ShapeAlg SpinAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanAcctShapeCfg AsanPlanSoundCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesArg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import AN.
Unset Lia Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section WithFP1. Context {FP : PropExec.FPState}.
Section FactNodes.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.

  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).
  #[local] Notation u := bv_unsigned.

  (* [comment removed for export] *)
  Lemma fact_node_sound : forall cs (facts : list kentry) E R FULL model T,
    CSOK E cs R FULL model ->
    know_ok SEGS E (Mr A argH E cs model FULL) facts ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' (add_kn cs facts) R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes_cfg SEGS (APSC.cfg_fp SEGS R' (pc (add_kn cs facts)) FULL' model') T) ->
    srealizes_cfg SEGS (APSC.cfg_fp SEGS R (pc cs) FULL model) T.
  Proof.
    intros cs facts E R FULL model T HC HF Hk.
    specialize (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    unfold add_kn in Hk. rewrite pc_set_kn in Hk. apply Hk; [|reflexivity].
    apply cs_ok_set_kn; [exact HC|].
    unfold know_ok in *. apply Forall_app. split; [exact HF | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC)].
  Qed.

  Lemma kr_ok : forall E M e lo hi, lo <= u (edenot E e) <= hi -> kentry_ok SEGS E M (KRange e lo hi).
  Proof. intros E M e lo hi [H1 H2]. cbn [kentry_ok]. split; assumption. Qed.

  Lemma u_eaddz0 : forall E e, u (edenot E (eaddz e 0)) = u (edenot E e).
  Proof.
    intros E e. unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64, u_lit64.
    pose proof (u64_range (edenot E e)). unfold two64. rewrite (Z.mod_small 0) by lia. rewrite Z.add_0_r. apply Z.mod_small. lia.
  Qed.

  Lemma u_esub : forall E a b, u (edenot E (esub a b)) = (u (edenot E a) - u (edenot E b)) mod 2 ^ 64.
  Proof. intros E a b. unfold esub. rewrite mkAlu_denot. cbn [edenot]. apply u_sub64. Qed.

  (* [comment removed for export] *)
  Lemma deand_val : forall E M k e e' w lo hi,
    know_ok SEGS E M k -> deand e = (e', w) ->
    xlo1 k (eaddz e' 0) = Some lo -> xhi1 k (eaddz e' 0) = Some hi -> w <= lo ->
    exists rho, 0 <= rho <= w /\ u (edenot E e) = u (edenot E e') - rho /\ lo <= u (edenot E e') <= hi.
  Proof.
    intros E M k e e' w lo hi HK Hd Hlo Hhi Hw.
    destruct (deand_sound E e e' w Hd) as [Hw0 [rho [Hr He]]].
    pose proof (xlo1_sound SEGS E M k _ lo HK Hlo) as L. pose proof (xhi1_sound SEGS E M k _ hi HK Hhi) as H.
    rewrite u_eaddz0 in L, H. pose proof (u64_range (edenot E e')) as R'.
    exists rho. split; [exact Hr|]. split; [|lia]. rewrite He. apply Z.mod_small. lia.
  Qed.

  Theorem xn_sound_reldiff : forall args, APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => node_reldiff cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_reldiff in Hn.
    destruct args as [|X [|Y [|[s| | | | | | |] [|]]]]; try discriminate.
    destruct (deand X) as [X' wX] eqn:HdX. destruct (deand Y) as [Y' wY] eqn:HdY.
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    destruct (xlo1 (kn cs) (eaddz X' 0)) as [xlo'|] eqn:E1; [|discriminate].
    destruct (xhi1 (kn cs) (eaddz X' 0)) as [xhi'|] eqn:E2; [|discriminate].
    destruct (xlo1 (kn cs) (eaddz Y' 0)) as [ylo'|] eqn:E3; [|discriminate].
    destruct (xhi1 (kn cs) (eaddz Y' 0)) as [yhi'|] eqn:E4; [|discriminate].
    destruct (xlo1 (kn cs) (esub (eaddz Y' 0) (eaddz X' 0))) as [l|] eqn:E5; [|discriminate].
    destruct (xhi1 (kn cs) (esub (eaddz Y' 0) (eaddz X' 0))) as [h|] eqn:E6; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate] end.
    injection Hn as <-.
    apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hs0 Hs64].
    apply Z.leb_le in Hs0. apply Z.ltb_lt in Hs64.
    repeat match type of Hg with (_ && _)%bool = true => apply andb_prop in Hg as [Hg ?X] end.
    apply Z.leb_le in Hg. apply Z.leb_le in X4. apply Z.ltb_lt in X3. apply Z.ltb_lt in X2. apply Z.ltb_lt in X1. apply Z.leb_le in X0.
    unfold two63 in *.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    set (M := Mr A argH E cs model FULL) in HK.
    destruct (deand_val E M (kn cs) X X' wX xlo' xhi' HK HdX E1 E2 Hg) as [rX (RX & UX & BX)].
    destruct (deand_val E M (kn cs) Y Y' wY ylo' yhi' HK HdY E3 E4 X4) as [rY (RY & UY & BY)].
    pose proof (xlo1_sound SEGS E M (kn cs) _ l HK E5) as DL. pose proof (xhi1_sound SEGS E M (kn cs) _ h HK E6) as DH.
    rewrite u_esub, !u_eaddz0 in DL, DH.
    (* [comment removed for export] *)
    assert (D' : l <= u (edenot E Y') - u (edenot E X') <= h) by lia.
    assert (D : l - wY <= u (edenot E Y) - u (edenot E X) <= h + wX) by lia.
    eapply fact_node_sound; [exact HC | | exact Hk].
    constructor; [apply kr_ok; lia|]. constructor; [apply kr_ok; lia|]. constructor; [|constructor].
    apply kr_ok.
    (* [comment removed for export] *)
    rewrite u_esub.
    rewrite (mkSrl_denot SEGS E M (kn cs) Y s (Z_to_bv 64 s) HK) by (rewrite u64_lit by lia; apply Z.mod_small; lia).
    rewrite (mkSrl_denot SEGS E M (kn cs) X s (Z_to_bv 64 s) HK) by (rewrite u64_lit by lia; apply Z.mod_small; lia).
    rewrite !u_srl64, !u64_lit by lia. rewrite (Z.mod_small s 64) by lia.
    set (m := 2 ^ s) in *. assert (Hm : 0 < m) by (subst m; apply Z.pow_pos_nonneg; lia).
    set (x := u (edenot E X)) in *. set (y := u (edenot E Y)) in *.
    pose proof (u64_range (edenot E X)) as RX'. pose proof (u64_range (edenot E Y)) as RY'. fold x in RX'. fold y in RY'.
    clearbody x y m. clear UX UY BX BY DL DH D' Hk HC HK E1 E2 E3 E4 E5 E6 HdX HdY.
    assert (B1 : m * (x / m) <= x) by (apply Z.mul_div_le; lia).
    assert (B2 : x < m * (x / m + 1)) by (pose proof (Z.mul_succ_div_gt x m Hm); lia).
    assert (B3 : m * (y / m) <= y) by (apply Z.mul_div_le; lia).
    assert (B4 : y < m * (y / m + 1)) by (pose proof (Z.mul_succ_div_gt y m Hm); lia).
    assert (Hyx : x / m <= y / m) by (apply Z.div_le_mono; lia).
    assert (Hy64 : y / m < 2 ^ 64) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_pos x m ltac:(lia) Hm) as Hx0.
    set (qx := x / m) in *. set (qy := y / m) in *. clearbody qx qy.
    rewrite Z.mul_add_distr_l, Z.mul_1_r in B2, B4.
    remember (m * qx) as px eqn:Hpx. remember (m * qy) as py eqn:Hpy.
    rewrite (Z.mod_small (qy - qx) (2 ^ 64)) by lia.
    split.
    - enough ((l - wY) / m < qy - qx + 1) by lia.
      apply Z.div_lt_upper_bound; [lia|]. replace (m * (qy - qx + 1)) with (py - px + m) by (subst; ring). lia.
    - apply Z.div_le_lower_bound; [lia|]. replace (m * (qy - qx)) with (py - px) by (subst; ring). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma zone_covers_sound : forall E M k bb bk N K,
    know_ok SEGS E M k -> kentry_ok SEGS E M K -> zone_covers k bb bk N K = true ->
    kentry_ok SEGS E M (KZero (SA bb bk) N).
  Proof.
    intros E M k bb bk N K HK HKK H. unfold zone_covers in H.
    destruct K as [| [zb zk] zn | | | | | | | | | kinv_id kinv_args]; try discriminate H.
    destruct zb as [z| | | | | | |]; try discriminate H. destruct zn as [zn| | | | | | |]; try discriminate H.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.ltb_lt in H3.
    pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as G1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as G2.
    cbn [xt_den] in G1, G2. rewrite edenot_lit, u_lit64 in G1, G2. unfold two64 in *.
    rewrite (Z.mod_small 0) in G1, G2 by lia.
    cbn [kentry_ok] in HKK. destruct HKK as [ZF ZB].
    unfold flat, estart, elenZ in *. cbn [a_base a_off] in *. rewrite !edenot_lit, !u_lit64 in ZF, ZB.
    rewrite <- !zlit64_eq in *.
    pose proof (u64_range (edenot E N)) as RN. pose proof (u64_range (edenot E bb)) as RB.
    cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off].
    split; [lia|].
    intros i Hi.
    replace (u (edenot E bb) + bk + i) with (zlit64 z + zk + (u (edenot E bb) + bk + i - (zlit64 z + zk))) by lia.
    apply ZB. lia.
  Qed.

  Lemma zone_covers_sym_sound : forall E M k bb bk N K,
    know_ok SEGS E M k -> kentry_ok SEGS E M K -> zone_covers_sym k bb bk N K = true ->
    kentry_ok SEGS E M (KZero (SA bb bk) N).
  Proof.
    intros E M k bb bk N K HK HKK H. unfold zone_covers_sym in H.
    destruct K as [| [zb zk] zn | | | | | | | | | kinv_id kinv_args]; try discriminate H.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as G1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as G2.
    pose proof (lin_ge0_sound SEGS E M k _ _ HK H3) as G3.
    cbn [xt_den] in G1, G2, G3. rewrite edenot_lit, u_lit64 in G3. unfold two64 in *.
    rewrite (Z.mod_small 0) in G3 by lia.
    cbn [kentry_ok] in HKK. destruct HKK as [ZF ZB].
    unfold flat, estart, elenZ in *. cbn [a_base a_off] in *.
    pose proof (u64_range (edenot E N)) as RN. pose proof (u64_range (edenot E bb)) as RB.
    pose proof (u64_range (edenot E zb)) as RZ. pose proof (u64_range (edenot E zn)) as RZN.
    cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off].
    split; [lia|].
    intros i Hi.
    replace (u (edenot E bb) + bk + i) with (u (edenot E zb) + zk + (u (edenot E bb) + bk + i - (u (edenot E zb) + zk))) by lia.
    apply ZB. lia.
  Qed.

  Theorem xn_sound_zerocover : forall args, APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => node_zerocover cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. rewrite node_zerocover_eq in Hn. (* [comment removed for export] *) unfold node_zerocover_ref in Hn.
    destruct args as [|B [|N [|]]]; try discriminate.
    destruct (split_lit B) as [bb bk] eqn:Hsl.
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection Hn as <-.
    apply andb_prop in Hc as [_ Hex]. rewrite zc_find_eq in Hex.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    apply existsb_exists in Hex as [K [HinK HzK]].
    eapply fact_node_sound; [exact HC | | exact Hk].
    constructor; [|constructor].
    apply orb_prop in HzK as [HzK|HzK].
    - eapply zone_covers_sound; [exact HK | | exact HzK].
      exact (proj1 (Forall_forall _ _) HK K HinK).
    - eapply zone_covers_sym_sound; [exact HK | | exact HzK].
      exact (proj1 (Forall_forall _ _) HK K HinK).
  Qed.
  (* [comment removed for export] *)
  Lemma take_srl_sound : forall E ts co r s rest,
    take_srl ts = Some (co, r, s, rest) ->
    tden E ts = tden E rest + co * u (edenot E (EAlu ALU_SRL r (ELit s))).
  Proof.
    intros E ts. induction ts as [|[co0 a] ts IH]; intros co r s rest H; [discriminate H|].
    cbn [take_srl] in H.
    match type of H with (match ?c with _ => _ end) = _ => destruct c as [[r0 s0]|] eqn:Hc end.
    - destruct a; try discriminate Hc. destruct op; try discriminate Hc. destruct a2; try discriminate Hc.
      injection Hc as <- <-. injection H as <- <- <- <-. cbn [tden]. unfold AX2S.uE in *. lia.
    - destruct (take_srl ts) as [[[[co1 r1] s1] rest1]|] eqn:Ht; [|discriminate H].
      injection H as E1 E2 E3 E4. subst. cbn [tden]. rewrite (IH _ _ _ _ eq_refl). unfold AX2S.uE in *. lia.
  Qed.

  Lemma eqm_both_small : forall a b, eqm a b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
  Proof. intros a b [q Hq] Ha Hb. assert (q = 0) by nia. subst q. lia. Qed.

  Theorem xn_sound_srlbound : forall args, APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => node_srlbound cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_srlbound in Hn.
    destruct args as [|e [|]]; try discriminate Hn.
    destruct (take_srl (snd (lin_of e))) as [[[[co r] s] rest]|] eqn:Ht; [|discriminate Hn].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate Hn] end.
    apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hs0 Hs64]. apply Z.leb_le in Hs0. apply Z.ltb_lt in Hs64.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK. set (M := Mr A argH E cs model FULL) in HK.
    set (e' := unlin (fst (lin_of e), rest)) in *. set (m := 2 ^ s) in *.
    assert (Hm : 0 < m) by (subst m; apply Z.pow_pos_nonneg; lia).
    assert (Hm64 : m < 2 ^ 64) by (subst m; apply Z.pow_lt_mono_r; lia).
    pose proof (u64_range (edenot E e)) as Re. pose proof (u64_range (edenot E e')) as Re'. pose proof (u64_range (edenot E r)) as Rr.
    (* [comment removed for export] *)
    assert (Usrl : u (edenot E (EAlu ALU_SRL r (ELit s))) = u (edenot E r) / m).
    { rewrite u_srl_lit. unfold two64. rewrite (Z.mod_small s (2 ^ 64)) by lia. rewrite (Z.mod_small s 64) by lia. reflexivity. }
    pose proof (Z.div_pos (u (edenot E r)) m ltac:(lia) Hm) as D0.
    assert (D1 : u (edenot E r) / m <= u (edenot E r)) by (apply Z.div_le_upper_bound; [lia|]; nia).
    assert (D2 : m * (u (edenot E r) / m) <= u (edenot E r)) by (apply Z.mul_div_le; lia).
    assert (D3 : u (edenot E r) < m * (u (edenot E r) / m + 1)) by (pose proof (Z.mul_succ_div_gt (u (edenot E r)) m Hm); lia).
    (* [comment removed for export] *)
    assert (Ue : eqm (u (edenot E e)) (u (edenot E e') + co * (u (edenot E r) / m))).
    { pose proof (lin_of_sound E e) as L1. pose proof (unlin_sound E (fst (lin_of e), rest)) as L2. fold e' in L2.
      unfold lden in L1, L2. cbn [fst snd] in L2. unfold AX2S.uE in L1, L2.
      rewrite (take_srl_sound E _ co r s rest Ht) in L1. rewrite Usrl in L1.
      destruct L1 as [q1 H1]. destruct L2 as [q2 H2]. exists (- q1 - q2). lia. }
    destruct (Z.eqb co 1) eqn:Hco1.
    - (* [comment removed for export] *)
      apply Z.eqb_eq in Hco1. subst co.
      destruct (xhi1 (kn cs) e') as [he|] eqn:E1; [|discriminate Hn].
      destruct (xhi1 (kn cs) r) as [hr|] eqn:E2; [|discriminate Hn].
      destruct (xlo1 (kn cs) (eadd (escale m e') r)) as [lo|] eqn:E3; [|discriminate Hn].
      destruct (xhi1 (kn cs) (eadd (escale m e') r)) as [hi|] eqn:E4; [|discriminate Hn].
      destruct (Z.ltb (m * he + hr) two64) eqn:Hw; [|discriminate Hn]. apply Z.ltb_lt in Hw. unfold two64 in Hw.
      injection Hn as <-.
      set (J := eadd (escale m e') r) in *.
      pose proof (xhi1_sound SEGS E M (kn cs) e' he HK E1) as He. pose proof (xhi1_sound SEGS E M (kn cs) r hr HK E2) as Hr.
      pose proof (xlo1_sound SEGS E M (kn cs) J lo HK E3) as HJl. pose proof (xhi1_sound SEGS E M (kn cs) J hi HK E4) as HJh.
      assert (Hmh : he <= m * he) by nia.
      assert (Ue' : u (edenot E e) = u (edenot E e') + u (edenot E r) / m).
      { apply eqm_both_small; [|lia|lia]. rewrite Z.mul_1_l in Ue. exact Ue. }
      assert (UJ : u (edenot E J) = m * u (edenot E e') + u (edenot E r)).
      { subst J. unfold eadd, escale. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64, mkMd_denot, u_mul64, edenot_lit, u_lit64.
        unfold two64. rewrite (Z.mod_small m (2 ^ 64)) by lia.
        assert (Hme : m * u (edenot E e') <= m * he) by (apply Z.mul_le_mono_nonneg_l; lia).
        assert (Hme0 : 0 <= m * u (edenot E e')) by (apply Z.mul_nonneg_nonneg; lia).
        rewrite (Z.mod_small (m * _)) by lia. apply Z.mod_small. lia. }
      eapply fact_node_sound; [exact HC | | exact Hk].
      constructor; [|constructor]. apply kr_ok. rewrite Ue'.
      assert (Q : (m * u (edenot E e') + u (edenot E r)) / m = u (edenot E e') + u (edenot E r) / m).
      { rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
      rewrite <- Q, <- UJ. split; apply Z.div_le_mono; lia.
    - (* [comment removed for export] *)
      destruct (Z.ltb 0 co && Z.ltb co two64 && Z.eqb (co mod m) 0)%bool eqn:Hq; [|discriminate Hn].
      apply andb_prop in Hq as [Hq1 Hq2]. apply andb_prop in Hq1 as [Hq1 Hq3]. apply Z.ltb_lt in Hq1. apply Z.ltb_lt in Hq3. apply Z.eqb_eq in Hq2.
      unfold two64 in Hq3.
      destruct (xhi1 (kn cs) e') as [he|] eqn:E1; [|discriminate Hn].
      destruct (xhi1 (kn cs) r) as [hr|] eqn:E2; [|discriminate Hn].
      destruct (xlo1 (kn cs) (eadd e' (escale (co / m) r))) as [lo|] eqn:E3; [|discriminate Hn].
      destruct (xhi1 (kn cs) (eadd e' (escale (co / m) r))) as [hi|] eqn:E4; [|discriminate Hn].
      match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hw; [|discriminate Hn] end.
      apply andb_prop in Hw as [Hw1 Hw2]. apply Z.ltb_lt in Hw1. apply Z.leb_le in Hw2. unfold two64 in Hw1.
      injection Hn as <-.
      set (q := co / m) in *. set (J := eadd e' (escale q r)) in *.
      assert (Hcoq : co = q * m) by (subst q; pose proof (Z.div_mod co m ltac:(lia)); lia).
      assert (Hq0 : 0 < q) by nia.
      pose proof (xhi1_sound SEGS E M (kn cs) e' he HK E1) as He. pose proof (xhi1_sound SEGS E M (kn cs) r hr HK E2) as Hr.
      pose proof (xlo1_sound SEGS E M (kn cs) J lo HK E3) as HJl. pose proof (xhi1_sound SEGS E M (kn cs) J hi HK E4) as HJh.
      assert (Hqr : q * u (edenot E r) <= q * hr) by nia.
      assert (Hq64 : q < 2 ^ 64) by nia.
      assert (UJ : u (edenot E J) = u (edenot E e') + q * u (edenot E r)).
      { subst J. unfold eadd, escale. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64, mkMd_denot, u_mul64, edenot_lit, u_lit64.
        unfold two64. rewrite (Z.mod_small q (2 ^ 64)) by lia.
        rewrite (Z.mod_small (q * _)) by nia. apply Z.mod_small. nia. }
      set (V := u (edenot E e') + q * (u (edenot E r) - (u (edenot E r) - m * (u (edenot E r) / m)))).
      assert (HV : u (edenot E J) - q * (m - 1) <= V <= u (edenot E J)).
      { assert (A1 : q * (m * (u (edenot E r) / m)) <= q * u (edenot E r)) by (apply Z.mul_le_mono_nonneg_l; lia).
        assert (A2 : q * (u (edenot E r) - (m - 1)) <= q * (m * (u (edenot E r) / m))) by (apply Z.mul_le_mono_nonneg_l; lia).
        subst V; rewrite UJ; lia. }
      assert (Ue' : u (edenot E e) = V).
      { apply eqm_both_small; [|lia|pose proof (u64_range (edenot E J)); lia].
        subst V. rewrite Hcoq in Ue. destruct Ue as [q1 H1]. exists q1. nia. }
      eapply fact_node_sound; [exact HC | | exact Hk].
      constructor; [|constructor]. apply kr_ok. rewrite Ue'. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma node1_fp_bind : forall (f : acs -> option acs) (g : acs -> acs -> option acs),
    (forall cs c1, f cs = Some c1 -> nxt c1 = nxt cs) ->
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always f ->
    (forall c0, APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (g c0)) ->
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => match f cs with Some c1 => g cs c1 | None => None end).
  Proof.
    intros f g Hnx Hf Hg cs cs' E R FULL model T HC _ Hn Hk.
    destruct (f cs) as [c1|] eqn:Hf1; [|discriminate Hn].
    apply (Hf cs c1 E R FULL model T HC eq_refl Hf1).
    intros E1 R1 FULL1 model1 [Ha1 Hb1] HC1 Hfs1.
    apply (Hg cs c1 cs' E1 R1 FULL1 model1 T HC1 eq_refl Hn).
    intros E2 R2 FULL2 model2 [Ha2 Hb2] HC2 Hfs2.
    rewrite (Hnx _ _ Hf1) in Hb2.
    apply (Hk E2 R2 FULL2 model2); [split; eapply env_agree_trans; eassumption | exact HC2 | congruence].
  Qed.


  (* [comment removed for export] *)
  Lemma node1_fp_otry : forall (f : acs -> option acs),
    (forall cs c1, f cs = Some c1 -> nxt c1 = nxt cs) ->
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always f ->
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => Some (otry (f cs) cs)).
  Proof.
    intros f Hnx Hf cs cs' E R FULL model T HC Hpre Hn Hk.
    injection Hn as <-. unfold otry. destruct (f cs) as [c1|] eqn:Hf1.
    - exact (Hf cs c1 E R FULL model T HC Hpre Hf1 Hk).
    - apply (Hk E R FULL model); [split; apply env_agree_refl | exact HC | reflexivity].
  Qed.
  (* [comment removed for export] *)
  Lemma node1_fp_seq : forall (F : acs -> acs) (G : acs -> acs -> acs),
    (forall cs, nxt (F cs) = nxt cs) ->
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => Some (F cs)) ->
    (forall c0, APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun c => Some (G c0 c))) ->
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => Some (G cs (F cs))).
  Proof.
    intros F G Hnx HF HG.
    refine (node1_fp_bind (fun cs => Some (F cs)) (fun c0 c1 => Some (G c0 c1)) _ HF HG).
    intros cs c1 H. injection H as <-. apply Hnx.
  Qed.
  Lemma add_kn_nxt : forall cs facts, nxt (add_kn cs facts) = nxt cs.
  Proof. reflexivity. Qed.
  Lemma reldiff_nxt : forall cs args c1, node_reldiff cs args = Some c1 -> nxt c1 = nxt cs.
  Proof.
    intros c args c1 H. unfold node_reldiff in H.
    repeat match type of H with
           | (let '(_, _) := ?x in _) = _ => destruct x
           | match ?x with _ => _ end = _ => destruct x; try discriminate H
           | (if ?c then _ else _) = _ => destruct c; try discriminate H
           end.
    injection H as <-. apply add_kn_nxt.
  Qed.
  Lemma srlbound_nxt : forall cs args c1, node_srlbound cs args = Some c1 -> nxt c1 = nxt cs.
  Proof.
    intros c args c1 H. unfold node_srlbound in H.
    repeat match type of H with
           | (let '(_, _) := ?x in _) = _ => destruct x
           | match ?x with _ => _ end = _ => destruct x; try discriminate H
           | (if ?c then _ else _) = _ => destruct c; try discriminate H
           end;
    injection H as <-; apply add_kn_nxt.
  Qed.
  Lemma zerocover_nxt : forall cs args c1, node_zerocover cs args = Some c1 -> nxt c1 = nxt cs.
  Proof.
    intros c args c1 H. rewrite node_zerocover_eq in H. (* [comment removed for export] *) unfold node_zerocover_ref in H.
    repeat match type of H with
           | (let '(_, _) := ?x in _) = _ => destruct x
           | match ?x with _ => _ end = _ => destruct x; try discriminate H
           | (if ?c then _ else _) = _ => destruct c; try discriminate H
           end;
    injection H as <-; apply add_kn_nxt.
  Qed.
  Lemma otry_nxt : forall o cs, (forall c1, o = Some c1 -> nxt c1 = nxt cs) -> nxt (otry o cs) = nxt cs.
  Proof. intros o cs H. unfold otry. destruct o as [c1|]; [apply H; reflexivity | reflexivity]. Qed.

  Theorem xn_sound_argregion : APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always node_argregion.
  Proof.
    set (X0 := fun cs => srl_addr (reg cs 10)).
    set (Y0 := fun cs => match srl1 (snd (lin_of (reg cs 11))) with Some r => r | None => ELit 0 end).
    set (F1 := fun cs => otry (node_reldiff cs [X0 cs; Y0 cs; ELit 3]) cs).
    set (G2 := fun c0 c => otry (node_srlbound c [eadd (reg c0 10) (reg c0 11)]) c).
    set (G3 := fun c0 c => otry (node_zerocover c [reg c0 10; reg c0 11]) c).
    assert (E : node_argregion = fun cs => Some (G3 cs (G2 cs (F1 cs)))) by reflexivity.
    rewrite E.
    apply (node1_fp_seq (fun cs => G2 cs (F1 cs)) G3).
    - intros cs. unfold G2, F1. rewrite otry_nxt by (intros c1 H; apply (srlbound_nxt _ _ _ H)).
      apply otry_nxt. intros c1 H. apply (reldiff_nxt _ _ _ H).
    - apply (node1_fp_seq F1 G2).
      + intros cs. unfold F1. apply otry_nxt. intros c1 H. apply (reldiff_nxt _ _ _ H).
      + unfold F1. apply (node1_fp_otry (fun cs => node_reldiff cs [X0 cs; Y0 cs; ELit 3])).
        * intros cs c1 H. apply (reldiff_nxt _ _ _ H).
        * intros cs cs' E0 R FULL model T HC Hpre Hn Hk. exact (xn_sound_reldiff _ cs cs' E0 R FULL model T HC Hpre Hn Hk).
      + intros c0. apply (node1_fp_otry (fun c => node_srlbound c [eadd (reg c0 10) (reg c0 11)])).
        * intros cs c1 H. apply (srlbound_nxt _ _ _ H).
        * apply xn_sound_srlbound.
    - intros c0. apply (node1_fp_otry (fun c => node_zerocover c [reg c0 10; reg c0 11])).
      + intros cs c1 H. apply (zerocover_nxt _ _ _ H).
      + apply xn_sound_zerocover.
  Qed.

  Theorem xn_sound_argregion_b : APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always node_argregion_b.
  Proof.
    apply (node1_fp_otry (fun cs => node_reldiff cs [srl_addr (reg cs 19); srl_addr (reg cs 10); ELit 3])).
    - intros cs c1 H. apply (reldiff_nxt _ _ _ H).
    - intros cs cs' E0 R FULL model T HC Hpre Hn Hk. exact (xn_sound_reldiff _ cs cs' E0 R FULL model T HC Hpre Hn Hk).
  Qed.
End FactNodes.
End WithFP1.

