(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec ShapeAlg SpinAlg AgentLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesArg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ flia2 | Zify.zify; xlia zchecker ].  (* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import AN.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section FactNodes.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : N.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.

  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).
  #[local] Notation u := bv_unsigned.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fact_node_sound : forall cs (facts : list kentry) E R FULL model T,
    CSOK E cs R FULL model ->
    know_ok SEGS E (Mr A argH E cs model FULL) facts ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' (add_kn cs facts) R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg_of SEGS R' (pc (add_kn cs facts)) FULL' model') T) ->
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) T.
  Proof.
    intros cs facts E R FULL model T HC HF Hk.
    specialize (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    unfold add_kn in Hk. rewrite pc_set_kn in Hk. apply Hk; [|reflexivity].
    apply cs_ok_set_kn; [exact HC|].
    unfold know_ok in *. apply Forall_app. split; [exact HF | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC)].
  Qed.

  #[using="Type"] Lemma kr_ok : forall E M e lo hi, lo <= u (edenot E e) <= hi -> kentry_ok SEGS E M (KRange e lo hi).
  Proof. intros E M e lo hi [H1 H2]. cbn [kentry_ok]. split; assumption. Qed.

  #[using="SINV argH"] Lemma u_eaddz0 : forall E e, u (edenot E (eaddz e 0)) = u (edenot E e).
  Proof.
    intros E e. unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64, u_lit64.
    pose proof (u64_range (edenot E e)). unfold two64. rewrite (Z.mod_small 0) by lia. rewrite Z.add_0_r. apply Z.mod_small. lia.
  Qed.

  #[using="Type"] Lemma u_esub : forall E a b, u (edenot E (esub a b)) = (u (edenot E a) - u (edenot E b)) mod 2 ^ 64.
  Proof. intros E a b. unfold esub. rewrite mkAlu_denot. cbn [edenot]. apply u_sub64. Qed.

  (* [comment removed for export] *)
  #[using="SINV argH"] Lemma deand_val : forall E M k e e' w lo hi,
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

  #[using="Type"] Theorem xn_sound_reldiff : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_reldiff cs args).
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
  #[using="SINV argH"] Lemma zone_covers_sound : forall E M k bb bk N K,
    know_ok SEGS E M k -> kentry_ok SEGS E M K -> zone_covers k bb bk N K = true ->
    kentry_ok SEGS E M (KZero (SA bb bk) N).
  Proof.
    intros E M k bb bk N K HK HKK H. unfold zone_covers in H.
    destruct K as [| [zb zk] zn | | | | | | | | |pt prs pargs pk]; try discriminate H.
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

  #[using="Type"] Theorem xn_sound_zerocover : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_zerocover cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_zerocover in Hn.
    destruct args as [|B [|N [|]]]; try discriminate.
    destruct (split_lit B) as [bb bk] eqn:Hsl.
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection Hn as <-.
    apply andb_prop in Hc as [_ Hex].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    apply existsb_exists in Hex as [K [HinK HzK]].
    eapply fact_node_sound; [exact HC | | exact Hk].
    constructor; [|constructor].
    eapply zone_covers_sound; [exact HK | | exact HzK].
    exact (proj1 (Forall_forall _ _) HK K HinK).
  Qed.
  (* [comment removed for export] *)
  #[using="SINV argH"] Lemma take_srl_sound : forall E ts co r s rest,
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

  #[using="Type"] Lemma eqm_both_small : forall a b, eqm a b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
  Proof. intros a b [q Hq] Ha Hb. assert (q = 0) by nia. subst q. lia. Qed.

  #[using="Type"] Theorem xn_sound_srlbound1 : forall e, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_srlbound1 cs e).
  Proof.
    intros e cs cs' E R FULL model T HC _ Hn Hk. unfold node_srlbound1 in Hn. cbv zeta in Hn.
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
        rewrite (Z.mod_small (m * _)) by nia. apply Z.mod_small. nia. }
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
      assert (HV : u (edenot E J) - q * (m - 1) <= V <= u (edenot E J)) by (subst V; rewrite UJ; nia).
      assert (Ue' : u (edenot E e) = V).
      { apply eqm_both_small; [|lia|pose proof (u64_range (edenot E J)); lia].
        subst V. rewrite Hcoq in Ue. destruct Ue as [q1 H1]. exists q1. nia. }
      eapply fact_node_sound; [exact HC | | exact Hk].
      constructor; [|constructor]. apply kr_ok. rewrite Ue'. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Theorem xn_sound_srlbound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_srlbound cs args).
  Proof.
    intros args cs cs' E R FULL model T HC Hpre Hn Hk.
    assert (Hd : (exists e, node_srlbound1 cs e = Some cs') \/ cs' = cs).
    { unfold node_srlbound in Hn. destruct args as [|e [|e' l]]; [discriminate Hn | | destruct e; discriminate Hn].
      destruct e as [r| | | | | | | ]; cbv beta iota in Hn; try (left; eexists; exact Hn).
      destruct (node_srlbound1 cs (reg cs (Z.to_nat r))) as [cs1|] eqn:H1; injection Hn as <-;
        [left; exists (reg cs (Z.to_nat r)); exact H1 | right; reflexivity]. }
    destruct Hd as [[e He]| ->].
    - exact (xn_sound_srlbound1 e cs cs' E R FULL model T HC Hpre He Hk).
    - apply (Hk E R FULL model); [split; apply env_agree_refl | exact HC | reflexivity].
  Qed.
End FactNodes.
