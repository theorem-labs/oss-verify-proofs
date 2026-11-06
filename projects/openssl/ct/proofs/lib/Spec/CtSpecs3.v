(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc BnModel BnTree BgState ApBase ApState ApLogic ApErr ApParse
  CtSizes CtWire CtTime CtModel CtLogic CtInv CtTac CtSpecs1 CtSpecs2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
Definition GROWTH : list Z := [4; 6; 9; 14; 22; 35; 56; 89; 142; 227; 363; 580; 928; 1484; 2374; 3798; 6076; 9721; 15553; 24884].
Definition growth_okb : bool :=
  forallb (fun na => (4 <=? na) && (na <=? 24884) && ((21844 <? na) || (existsb (Z.eqb (na * 8 / 5)) GROWTH && (na + 1 <=? na * 8 / 5)))) GROWTH.
Lemma growth_okb_true : growth_okb = true. Proof. vm_compute. reflexivity. Qed.
Lemma GROWTH_next na : In na GROWTH -> na <= 21844 -> In (na * 8 / 5) GROWTH /\ na + 1 <= na * 8 / 5 /\ 4 <= na.
Proof.
  intros H Hle. pose proof growth_okb_true as G. unfold growth_okb in G. rewrite forallb_forall in G. specialize (G na H).
  apply andb_prop in G as [G1 G2]. apply andb_prop in G1 as [G0 G1]. apply orb_prop in G2 as [G2|G2]; [apply Z.ltb_lt in G2; lia|].
  apply andb_prop in G2 as [G2 G3]. rewrite existsb_exists in G2. destruct G2 as (x & Hx & Ex). apply Z.eqb_eq in Ex. subst x.
  apply Z.leb_le in G0. apply Z.leb_le in G3. repeat split; assumption.
Qed.
Lemma GROWTH_bound na : In na GROWTH -> 4 <= na <= 24884.
Proof.
  intros H. pose proof growth_okb_true as G. unfold growth_okb in G. rewrite forallb_forall in G. specialize (G na H).
  apply andb_prop in G as [G1 _]. apply andb_prop in G1 as [G0 G1]. apply Z.leb_le in G0. apply Z.leb_le in G1. lia.
Qed.
Lemma GROWTH_4 : In 4 GROWTH. Proof. left. reflexivity. Qed.

Section S3.
Context {ptr : Type}.
Variables rcrit rcritS rcritI : Z -> Z -> Prop.
Variable spre : sysop -> Prop.
Local Notation ST := (ap_st ptr) (only parsing).
Local Notation BL := (list (ptr * Z)) (only parsing).
Local Notation awp := (awp (@okC ptr) rcrit rcritS rcritI spre) (only parsing).
Local Notation raise_then := (raise_then rcrit rcritS rcritI spre) (only parsing).
Implicit Types (s : ap_st ptr) (R X F : list (ptr * Z)).
Hypothesis Hgrow : forall na, In na GROWTH -> na <= 21844 -> rcrit (8 * na) (8 * (na * 8 / 5)).

Definition imeas_ok (u : Z) (M : meas) : Prop :=
  3 * m_cnt M <= 2 * u /\ 3 * m_sm M <= 107 * u /\ m_n63 M = 0 /\ m_r63 M = 0 /\ 64513 * m_nsec M <= u.
Lemma imeas_ok_add u1 u2 M1 M2 : imeas_ok u1 M1 -> imeas_ok u2 M2 -> imeas_ok (u1 + u2) (madd M1 M2).
Proof. unfold imeas_ok, madd; cbn; lia. Qed.
Lemma imeas_ok_0 : imeas_ok 0 m0.
Proof. unfold imeas_ok, m0; cbn; lia. Qed.
Lemma imeas_ok_mono u1 u2 M : imeas_ok u1 M -> u1 <= u2 -> imeas_ok u2 M.
Proof. unfold imeas_ok; lia. Qed.

Lemma meas_of X : bnonneg X -> 0 <= m_cnt (measure X) /\ 0 <= m_sm (measure X) /\ 0 <= m_n63 (measure X) /\ 0 <= m_r63 (measure X) /\ 0 <= m_nsec (measure X).
Proof. intros H. pose proof (measure_nonneg X H) as (A1 & A2 & A3 & A4 & A5 & A6). unfold m0 in *; cbn in *. lia. Qed.

(* [comment removed for export] *)
Lemma mblk1 n : 0 <= n < MMAP_THRESHOLD ->
  smsz n = n /\ isbig n = 0 /\ bigb n = 0 /\ 0 <= issec n <= 1 /\ (n < ASAN_SEC_MIN -> issec n = 0) /\ (issec n = 1 -> ASAN_SEC_MIN <= n).
Proof.
  intros Hn. rewrite smsz_small, isbig_small, bigb_small by lia. pose proof (issec_01 n).
  repeat split; try lia; [intros; apply issec_small; assumption|].
  unfold issec. destruct (Z.leb_spec ASAN_SEC_MIN n); [lia| discriminate].
Qed.

Ltac meas_simpl := rewrite ?measure_app, ?measure_cons, ?(@measure_nil ptr); cbn [madd mblk m0 m_cnt m_sum m_sm m_n63 m_r63 m_nsec snd fst].
Ltac small_consts := rewrite ?(smsz_small 104), ?(isbig_small 104), ?(bigb_small 104), ?(issec_small 104),
                             ?(smsz_small 32), ?(isbig_small 32), ?(bigb_small 32), ?(issec_small 32),
                             ?(smsz_small 56), ?(isbig_small 56), ?(bigb_small 56), ?(issec_small 56),
                             ?(smsz_small 24), ?(isbig_small 24), ?(bigb_small 24), ?(issec_small 24) by (unfold MMAP_THRESHOLD, ASAN_SEC_MIN; lia).

(* [comment removed for export] *)
Definition osz (o : option (ptr * Z)) : Z := match o with Some (_, m) => m | None => 0 end.
Definition obm (o : option (ptr * Z)) (n : Z) : Prop :=
  bnonneg (optb o) /\ m_cnt (measure (optb o)) <= 1 /\ m_sm (measure (optb o)) <= n /\ m_n63 (measure (optb o)) = 0 /\ m_r63 (measure (optb o)) = 0
  /\ m_nsec (measure (optb o)) <= 1 /\ 64513 * m_nsec (measure (optb o)) <= n /\ 0 <= osz o <= n.
Lemma obm_some q n : 0 <= n < MMAP_THRESHOLD -> obm (Some (q, n)) n.
Proof.
  intros Hn. pose proof (mblk1 n Hn) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). unfold obm. cbn [optb osz]. meas_simpl. rewrite Q1, Q2, Q3.
  split; [repeat constructor; cbn; lia|]. repeat split; try lia.
  destruct (Z.eq_dec (issec n) 1) as [E|E]; [pose proof (Q6 E); unfold ASAN_SEC_MIN in *; lia| lia].
Qed.
Lemma obm_none n : 0 <= n -> obm None n.
Proof. intros Hn. unfold obm. cbn [optb osz]. rewrite (@measure_nil ptr). cbn. split; [apply Forall_nil| lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RFs (L : Z) R : Prop :=
  bnonneg R /\ m_cnt (measure R) + 57 <= CT_NBT /\ m_sm (measure R) + 1767 + 136 + 2 * L <= CT_SMB
  /\ m_n63 (measure R) <= CT_NB63 /\ m_r63 (measure R) <= CT_BIGB /\ m_nsec (measure R) + 2 <= CT_NSEC.

(* [comment removed for export] *)
Lemma RFc_part L R P : 0 <= L -> RFs L R -> bnonneg P ->
  m_cnt (measure P) <= 4 -> m_sm (measure P) <= 136 + L -> m_n63 (measure P) = 0 -> m_r63 (measure P) = 0 -> m_nsec (measure P) <= 1 ->
  RFc (P ++ R).
Proof.
  intros HL (F0 & F1 & F2 & F3 & F4 & F5) HP C1 C2 C3 C4 C5. unfold RFc. rewrite measure_app. cbn [madd m_cnt m_sum m_sm m_n63 m_r63 m_nsec].
  split; [apply bnonneg_app; assumption| lia].
Qed.

Lemma o2i_sct_spec c p L s R X : rel s R X -> RFs L R -> 1 <= L <= 65533 ->
  awp (o2i_sct c p L s) X (fun r X' =>
    match fst r with
    | None => rel (snd r) R X'
    | Some x => rel (snd r) (sctb x ++ R) X' /\ bnonneg (sctb x) /\ imeas_ok (L + 2) (measure (sctb x)) /\ 0 <= i2o_sct_len x <= L
    end).
Proof.
  intros HR HF HL. pose proof HF as (F0 & F1 & F2 & F3 & F4 & F5).
  assert (HFc : RFc R) by (apply (RFc_part L R []); try assumption; try lia; [apply Forall_nil| | | | |]; rewrite (@measure_nil ptr); cbn; lia).
  unfold o2i_sct.
  destruct (Z.eqb_spec L 0); [lia|]. destruct (Z.ltb_spec MAX_SCT_SIZE L); [unfold MAX_SCT_SIZE in *; lia|]. cbn [orb].
  (* [comment removed for export] *)
  apply awp_abind. apply awp_amalloc; [apply lt62; unfold SZ_SCT; lia| |].
  { destruct HR as [Hs HP]. apply (ok_frame s R X SZ_SCT Hs ltac:(exact HP) F0); unfold SZ_SCT; small_consts; lia. }
  intros blk Hblk. cbn [fst snd].
  assert (HR1 : rel s ([(blk, SZ_SCT)] ++ R) ((blk, SZ_SCT) :: X)).
  { destruct HR as [Hs HP]. split; [exact Hs|]. perm_via (perm_skip (blk, SZ_SCT) HP). }
  assert (B104 : bnonneg [(blk, SZ_SCT)]) by (repeat constructor; cbn; unfold SZ_SCT; lia).
  destruct (Z.eqb_spec (byte c p) 0) as [V0|V0].
  - (* [comment removed for export] *)
    destruct (Z.ltb_spec L 43) as [L43|L43].
    { eapply raise_then; [exact HR1| apply (RFc_part L R); try assumption; try lia; meas_simpl; unfold SZ_SCT; small_consts; lia| cbn; lia| cbn; lia|].
      intros s1 X1 HR2 _. eapply seq_unit; [apply (sct_free_spec _ _ _ _ _ s1 R X1); cbn; exact HR2|]. intros X2 HR3. cbn. exact HR3. }
    (* [comment removed for export] *)
    apply awp_abind. apply awp_amalloc; [apply lt62; unfold CT_V1_HASHLEN; lia| |].
    { destruct HR1 as [Hs HP]. apply (ok_frame s ([(blk, SZ_SCT)] ++ R) _ CT_V1_HASHLEN Hs HP); [apply bnonneg_app; assumption| unfold CT_V1_HASHLEN; lia| | | | |];
        meas_simpl; unfold SZ_SCT, CT_V1_HASHLEN; small_consts; lia. }
    intros lg Hlg. cbn [fst snd].
    assert (HR2 : rel s ([(lg, CT_V1_HASHLEN); (blk, SZ_SCT)] ++ R) ((lg, CT_V1_HASHLEN) :: (blk, SZ_SCT) :: X)).
    { destruct HR1 as [Hs HP]. split; [exact Hs|]. perm_via (perm_skip (lg, CT_V1_HASHLEN) HP). }
    assert (B2 : bnonneg [(lg, CT_V1_HASHLEN); (blk, SZ_SCT)]) by (repeat constructor; cbn; unfold SZ_SCT, CT_V1_HASHLEN; lia).
    set (len2 := u16be c (p + 1 + CT_V1_HASHLEN + 8)). pose proof (u16be_range c (p + 1 + CT_V1_HASHLEN + 8)) as Hl2. fold len2 in Hl2.
    destruct (Z.ltb_spec (L - 43) len2) as [E2|E2].
    { eapply raise_then; [exact HR2| apply (RFc_part L R); try assumption; try lia; meas_simpl; unfold SZ_SCT, CT_V1_HASHLEN; small_consts; lia| cbn; lia| cbn; lia|].
      intros s1 X1 HR3 _. eapply seq_unit; [apply (sct_free_spec _ _ _ _ _ s1 R X1); cbn; exact HR3|]. intros X2 HR4. cbn. exact HR4. }
    (* [comment removed for export] *)
    apply awp_abind.
    set (x2 := set_ts (u64be c (p + 1 + CT_V1_HASHLEN)) (set_logid (Some lg) (set_version (byte c p) (sct_new blk)))).
    (* [comment removed for export] *)
    assert (EXT : awp ((if 0 <? len2 then e <- amalloc len2;; aret (set_ext (Some (e, len2)) len2 x2) else aret (set_ext None 0 x2)) s)
                      ((lg, CT_V1_HASHLEN) :: (blk, SZ_SCT) :: X)
                      (fun r X' => exists oe, fst r = set_ext oe len2 x2 /\ snd r = s /\ obm oe len2
                                   /\ rel s (([(lg, CT_V1_HASHLEN)] ++ optb oe ++ [(blk, SZ_SCT)]) ++ R) X')).
    { destruct (Z.ltb_spec 0 len2) as [Z2|Z2].
      - apply awp_abind. apply awp_amalloc; [apply lt62c; assert (E40 : 2^40 = 1099511627776) by reflexivity; lia| |].
        { destruct HR2 as [Hs HP]. apply (ok_frame s ([(lg, CT_V1_HASHLEN); (blk, SZ_SCT)] ++ R) _ len2 Hs HP); [apply bnonneg_app; assumption| lia| | | | |];
            meas_simpl; unfold SZ_SCT, CT_V1_HASHLEN; small_consts; pose proof (mblk1 len2 ltac:(unfold MMAP_THRESHOLD; lia)) as (Q1 & Q2 & Q3 & Q4 & _); rewrite ?Q1, ?Q2, ?Q3; lia. }
        intros e He. cbn [fst snd]. apply awp_aret. exists (Some (e, len2)). split; [reflexivity|]. split; [reflexivity|].
        split; [apply obm_some; unfold MMAP_THRESHOLD; lia|].
        destruct HR2 as [Hs HP]. split; [exact Hs|]. cbn [optb app]. perm_via (perm_skip (e, len2) HP).
      - apply awp_aret. exists None. split; [cbn [fst]; f_equal; lia|]. split; [reflexivity|]. split; [apply obm_none; lia|].
        cbn [optb app]. exact HR2. }
    eapply awp_mono; [exact EXT|]. clear EXT.
    intros [x3 s3] X3 (oe & Ex3 & Es3 & (Boe & C1 & C2 & C3 & C4 & C5 & C6 & C7) & HR3). cbn [fst snd] in Ex3, Es3. subst x3 s3.
    set (P3 := [(lg, CT_V1_HASHLEN)] ++ optb oe ++ [(blk, SZ_SCT)]) in *.
    assert (BP3 : bnonneg P3) by (unfold P3; apply bnonneg_app; [repeat constructor; cbn; unfold CT_V1_HASHLEN; lia| apply bnonneg_app; [exact Boe| exact B104]]).
    assert (MP3 : m_cnt (measure P3) <= 3 /\ m_sm (measure P3) <= 136 + len2 /\ m_n63 (measure P3) = 0 /\ m_r63 (measure P3) = 0 /\ m_nsec (measure P3) <= 1
                  /\ m_nsec (measure P3) = m_nsec (measure (optb oe))).
    { unfold P3. meas_simpl. unfold SZ_SCT, CT_V1_HASHLEN. small_consts. lia. }
    assert (Esctb : forall sg, sctb (set_sig sg (set_algs (byte c (p + 1 + CT_V1_HASHLEN + 8 + 2 + len2)) (byte c (p + 1 + CT_V1_HASHLEN + 8 + 2 + len2 + 1)) (set_ext oe len2 x2)))
                              = [(lg, CT_V1_HASHLEN)] ++ optb oe ++ optb sg ++ [(blk, SZ_SCT)]).
    { intros sg. unfold x2. cbn. destruct oe; destruct sg; reflexivity. }
    assert (Esctb0 : sctb (set_ext oe len2 x2) = P3) by (unfold x2, P3; cbn; destruct oe; reflexivity).
    assert (HFcP : RFc (P3 ++ R)) by (apply (RFc_part L R P3); try assumption; lia).
    (* [comment removed for export] *)
    cbn [fst snd]. unfold o2i_sct_signature.
    replace (sc_version (set_ext oe len2 x2)) with 0 by (unfold x2; cbn; symmetry; exact V0). cbn [Z.eqb negb].
    set (len' := L - 43 - len2).
    destruct (Z.leb_spec len' 4) as [L4|L4].
    { apply awp_abind. eapply raise_then; [exact HR3| exact HFcP| cbn; lia| cbn; lia|]. intros s1 X1 HR4 _. cbn [aret apbind fst snd Z.leb].
      eapply raise_then; [exact HR4| exact HFcP| cbn; lia| cbn; lia|]. intros s2 X2 HR5 _.
      eapply seq_unit; [apply (sct_free_spec _ _ _ _ _ s2 R X2); rewrite Esctb0; exact HR5|]. intros X4 HR6. cbn. exact HR6. }
    set (x4 := set_algs (byte c (p + 1 + CT_V1_HASHLEN + 8 + 2 + len2)) (byte c (p + 1 + CT_V1_HASHLEN + 8 + 2 + len2 + 1)) (set_ext oe len2 x2)).
    assert (Ex4 : sctb x4 = P3) by (unfold x4; rewrite <- (Esctb None) at 1 || idtac; unfold x2, P3; cbn; destruct oe; reflexivity).
    destruct (Z.eqb_spec (sct_nid x4) NID_undef) as [N0|N0].
    { apply awp_abind. eapply raise_then; [exact HR3| exact HFcP| cbn; lia| cbn; lia|]. intros s1 X1 HR4 _. cbn [aret apbind fst snd Z.leb].
      eapply raise_then; [exact HR4| exact HFcP| cbn; lia| cbn; lia|]. intros s2 X2 HR5 _.
      eapply seq_unit; [apply (sct_free_spec _ _ _ _ _ s2 R X2); rewrite Ex4; exact HR5|]. intros X4 HR6. cbn. exact HR6. }
    set (siglen := u16be c (p + 1 + CT_V1_HASHLEN + 8 + 2 + len2 + 2)). pose proof (u16be_range c (p + 1 + CT_V1_HASHLEN + 8 + 2 + len2 + 2)) as Hsl. fold siglen in Hsl.
    destruct (Z.ltb_spec (len' - 4) siglen) as [SO|SO].
    { apply awp_abind. eapply raise_then; [exact HR3| exact HFcP| cbn; lia| cbn; lia|]. intros s1 X1 HR4 _. cbn [aret apbind fst snd Z.leb].
      eapply raise_then; [exact HR4| exact HFcP| cbn; lia| cbn; lia|]. intros s2 X2 HR5 _.
      eapply seq_unit; [apply (sct_free_spec _ _ _ _ _ s2 R X2); rewrite Ex4; exact HR5|]. intros X4 HR6. cbn. exact HR6. }
    (* [comment removed for export] *)
    apply awp_abind. apply awp_abind. replace (sc_sig x4) with (@None (ptr * Z)) by reflexivity. cbn [option_map afree_opt].
    apply awp_aret. cbn [fst snd]. apply awp_abind.
    assert (SIG : awp ((if 0 <? siglen then q <- amalloc siglen;; aret (set_sig (Some (q, siglen)) x4) else aret (set_sig None x4)) s) X3
             (fun r X' => exists sg, fst r = set_sig sg x4 /\ snd r = s /\ obm sg siglen /\ rel s ((P3 ++ optb sg) ++ R) X')).
    { destruct (Z.ltb_spec 0 siglen) as [S0|S0].
      - apply awp_abind. apply awp_amalloc; [apply lt62c; assert (E40 : 2^40 = 1099511627776) by reflexivity; lia| |].
        { destruct HR3 as [Hs HP]. destruct MP3 as (M1 & M2 & M3 & M4 & M5 & M6).
          apply (ok_frame s (P3 ++ R) X3 siglen Hs HP); [apply bnonneg_app; assumption| lia| | | | |];
            meas_simpl; pose proof (mblk1 siglen ltac:(unfold MMAP_THRESHOLD; lia)) as (Q1 & Q2 & Q3 & Q4 & _); rewrite ?Q1, ?Q2, ?Q3; lia. }
        intros q Hq. cbn [fst snd]. apply awp_aret. exists (Some (q, siglen)). split; [reflexivity|]. split; [reflexivity|].
        split; [apply obm_some; unfold MMAP_THRESHOLD; lia|].
        destruct HR3 as [Hs HP]. split; [exact Hs|]. cbn [optb]. perm_via (perm_skip (q, siglen) HP).
      - apply awp_aret. exists None. split; [reflexivity|]. split; [reflexivity|]. split; [apply obm_none; lia|].
        cbn [optb]. rewrite app_nil_r. exact HR3. }
    eapply awp_mono; [exact SIG|]. clear SIG.
    intros [x5 s5] X5 (sg & Ex5 & Es5 & (Bsg & D1 & D2 & D3 & D4 & D5 & D6 & D7) & HR5). cbn [fst snd] in Ex5, Es5. subst x5 s5.
    subst len'. cbn -[st_blocks sctb set_sig measure P3 imeas_ok Z.add Z.sub Z.leb rel].
    replace (L - 43 - len2 - (L - 43 - len2 - 4 - siglen) <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    cbn -[st_blocks sctb set_sig measure P3 imeas_ok Z.add Z.sub rel].
    assert (Ex5 : sctb (set_sig sg x4) = [(lg, CT_V1_HASHLEN)] ++ optb oe ++ optb sg ++ [(blk, SZ_SCT)]) by (unfold x4; apply Esctb).
    rewrite Ex5.
    split.
    { destruct HR5 as [Hs HP]. split; [exact Hs|]. unfold P3 in HP. perm_via HP. }
    split; [apply bnonneg_app; [repeat constructor; cbn; unfold CT_V1_HASHLEN; lia| apply bnonneg_app; [exact Boe| apply bnonneg_app; [exact Bsg| exact B104]]]|].
    split.
    { (* [comment removed for export] *)
      destruct MP3 as (M1 & M2 & M3 & M4 & M5 & M6). unfold imeas_ok. meas_simpl. unfold SZ_SCT, CT_V1_HASHLEN. small_consts.
      (* [comment removed for export] *)
      assert (NS : m_nsec (measure (optb oe)) + m_nsec (measure (optb sg)) <= 1) by (unfold ASAN_SEC_MIN in *; nia).
      lia. }
    (* [comment removed for export] *)
    unfold i2o_sct_len, sc_siglen. unfold x4, x2. cbn [sc_version sc_extlen sc_sig set_sig set_algs set_ext set_ts set_logid set_version sct_new].
    rewrite V0. cbn [Z.eqb]. destruct sg as [[sq sn]|]; cbn [osz] in D7; lia.
  - (* [comment removed for export] *)
    apply awp_abind. apply awp_amalloc; [apply lt62c; assert (E40 : 2^40 = 1099511627776) by reflexivity; lia| |].
    { destruct HR1 as [Hs HP]. apply (ok_frame s ([(blk, SZ_SCT)] ++ R) _ L Hs HP); [apply bnonneg_app; assumption| lia| | | | |];
        meas_simpl; unfold SZ_SCT; small_consts; pose proof (mblk1 L ltac:(unfold MMAP_THRESHOLD; lia)) as (Q1 & Q2 & Q3 & Q4 & _); rewrite ?Q1, ?Q2, ?Q3; lia. }
    intros q Hq. cbn -[st_blocks sctb measure imeas_ok Z.add rel].
    replace (sctb (set_blob (Some (q, L)) (set_version (byte c p) (sct_new blk)))) with ([(q, L); (blk, SZ_SCT)]) by reflexivity.
    split.
    { destruct HR1 as [Hs HP]. split; [exact Hs|]. cbn [app]. perm_via (perm_skip (q, L) HP). }
    pose proof (mblk1 L ltac:(unfold MMAP_THRESHOLD; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    split; [repeat constructor; cbn; unfold SZ_SCT; lia|].
    split.
    { unfold imeas_ok. meas_simpl. unfold SZ_SCT. small_consts. rewrite Q1, Q2, Q3.
      destruct (Z.eq_dec (issec L) 1) as [E|E]; [pose proof (Q6 E); unfold ASAN_SEC_MIN in *; lia| lia]. }
    unfold i2o_sct_len, sc_bloblen. cbn [sc_version sc_blob set_blob set_version sct_new]. destruct (Z.eqb_spec (byte c p) 0); [congruence| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RFo R : Prop :=
  bnonneg R /\ m_cnt (measure R) <= 1240 /\ m_sm (measure R) <= 540000 /\ m_n63 (measure R) <= 2 /\ m_r63 (measure R) + 406374 <= CT_BIGB /\ m_nsec (measure R) <= 2.

(* [comment removed for export] *)
Definition kinv (k : skr ptr) : Prop :=
  match sk_data k with None => sk_items k = [] | Some (_, na) => In na GROWTH /\ sk_num k <= na end.

Lemma arrb_meas k : kinv k -> bnonneg (arrb k) /\ m_cnt (measure (arrb k)) <= 1 /\ m_sm (measure (arrb k)) <= 131051 /\ m_n63 (measure (arrb k)) <= 1
  /\ m_r63 (measure (arrb k)) <= 203187 /\ m_nsec (measure (arrb k)) <= 1.
Proof.
  intros HK. unfold arrb, kinv in *. destruct (sk_data k) as [[q na]|]; cbn [optb option_map fst snd].
  - destruct HK as [Hg _]. pose proof (GROWTH_bound na Hg). meas_simpl.
    pose proof (smsz_bound (8 * na) ltac:(lia)). pose proof (isbig_01 (8 * na)). pose proof (issec_01 (8 * na)). pose proof (bigb_le (8 * na) ltac:(lia)).
    split; [repeat constructor; cbn; lia| lia].
  - rewrite (@measure_nil ptr). cbn. split; [apply Forall_nil| lia].
Qed.

Lemma sctsb_items_app (k : skr ptr) (x : sctr ptr) : sctsb (sk_items k ++ [x]) = sctsb (sk_items k) ++ sctb x.
Proof. rewrite sctsb_app. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma sk_push_spec k x u1 u2 s R X : rel s (sctb x ++ skb k ++ R) X -> RFo R -> kinv k ->
  bnonneg (sctb x) -> imeas_ok u1 (measure (sctb x)) -> bnonneg (sctsb (sk_items k)) -> imeas_ok u2 (measure (sctsb (sk_items k))) ->
  0 <= u1 -> 0 <= u2 -> u1 + u2 <= 65533 -> 3 * (sk_num k + 1) <= u1 + u2 ->
  awp (sk_push k x s) X (fun r X' =>
    rel (snd r) (skb (fst r) ++ R) X' /\ snd r = s /\ kinv (fst r) /\ sk_items (fst r) = sk_items k ++ [x] /\ sk_blk (fst r) = sk_blk k).
Proof.
  intros HR HF HK Bx Ix Bi Ii Hu1 Hu2 Hu Hn. pose proof HF as (F0 & F1 & F2 & F3 & F4 & F5). pose proof (arrb_meas k HK) as (A0 & A1 & A2 & A3 & A4 & A5).
  assert (Hnum : 0 <= sk_num k) by (unfold sk_num, zlength; lia).
  unfold sk_push. unfold kinv in HK. unfold skb, arrb in HR. destruct (sk_data k) as [[q na]|] eqn:Ek.
  - destruct HK as [Hg Hle]. pose proof (GROWTH_bound na Hg) as Bna.
    destruct (Z.leb_spec (Z.max (sk_num k + 1) SK_MIN_NODES) na) as [W|W].
    + (* [comment removed for export] *)
      apply awp_aret. cbn [fst snd]. split; [| split; [reflexivity| split; [| split; reflexivity]]].
      * destruct HR as [Hs HP]. split; [exact Hs|]. unfold skb, arrb. cbn [sk_items sk_data sk_blk]. rewrite sctsb_items_app. cbn [optb option_map fst snd] in *. perm_via HP.
      * unfold kinv. cbn [sk_data sk_items]. split; [exact Hg|]. unfold sk_num in *. cbn [sk_items]. unfold zlength in *. rewrite length_app. cbn [length]. unfold SK_MIN_NODES in W. lia.
    + (* [comment removed for export] *)
      unfold SK_MIN_NODES in W. assert (E : sk_num k = na) by lia.
      replace (Z.max (sk_num k + 1) SK_MIN_NODES) with (na + 1) by (unfold SK_MIN_NODES; lia). rewrite (sk_grow_once na) by lia.
      pose proof (GROWTH_next na Hg ltac:(lia)) as (Hg' & Hst & _). pose proof (GROWTH_bound _ Hg') as Bna'.
      remember (na * 8 / 5) as nb eqn:Enb.
      apply awp_abind. destruct HR as [Hs HP]. cbn [optb option_map fst snd] in HP.
      eapply (awp_arealloc _ _ _ _ _ q (8 * na) (8 * nb) s X (st_blocks s ++ sctb x ++ sctsb (sk_items k) ++ [(sk_blk k, SZ_STACK)] ++ R)).
      * perm_via HP.
      * apply lt62c. assert (E40 : 2^40 = 1099511627776) by reflexivity. lia.
      * subst nb. apply Hgrow; [exact Hg| lia].
      * assert (BA : bnonneg (sctb x ++ (sctsb (sk_items k) ++ [(q, 8 * na)] ++ [(sk_blk k, SZ_STACK)]) ++ R)).
        { apply bnonneg_app; [exact Bx|]. apply bnonneg_app; [| exact F0]. apply bnonneg_app; [exact Bi|].
          apply bnonneg_app; [unfold arrb in A0; rewrite Ek in A0; exact A0|]. repeat constructor; cbn; unfold SZ_STACK; lia. }
        apply (ok_frame s _ X (8 * nb) Hs HP BA ltac:(lia)); meas_simpl; unfold SZ_STACK; small_consts; unfold imeas_ok in Ix, Ii; unfold CT_NBT, CT_SMB, CT_NB63, CT_BIGB, CT_NSEC in *.
        -- lia.
        -- pose proof (smsz_bound (8 * nb) ltac:(lia)). pose proof (smsz_bound (8 * na) ltac:(lia)). lia.
        -- pose proof (isbig_01 (8 * nb)). pose proof (isbig_01 (8 * na)). lia.
        -- pose proof (bigb_le (8 * nb) ltac:(lia)). pose proof (bigb_le (8 * na) ltac:(lia)). lia.
        -- pose proof (issec_01 (8 * nb)). pose proof (issec_01 (8 * na)). lia.
      * intros q' Hq'. cbn [fst snd]. apply awp_aret. cbn [fst snd]. split; [| split; [reflexivity| split; [| split; reflexivity]]].
        -- split; [exact Hs|]. unfold skb, arrb. cbn [sk_items sk_data sk_blk optb option_map fst snd]. rewrite sctsb_items_app. perm_solve.
        -- unfold kinv. cbn [sk_data sk_items]. split; [exact Hg'|]. unfold sk_num in *. cbn [sk_items]. unfold zlength in *. rewrite length_app. cbn [length]. lia.
  - (* [comment removed for export] *)
    rewrite HK in *. unfold sk_num. rewrite HK. replace (Z.max (zlength (@nil (sctr ptr)) + 1) SK_MIN_NODES) with 4 by reflexivity. change (8 * 4) with 32.
    apply awp_abind. destruct HR as [Hs HP]. cbn [optb option_map fst snd sctsb app] in HP.
    apply awp_amalloc; [apply lt62; lia| |].
    { assert (BA : bnonneg (sctb x ++ (sk_blk k, SZ_STACK) :: R)) by (apply bnonneg_app; [exact Bx|]; constructor; [cbn; unfold SZ_STACK; lia| exact F0]).
      apply (ok_frame s _ X 32 Hs HP BA ltac:(lia)); meas_simpl; unfold SZ_STACK; small_consts; unfold imeas_ok in Ix; unfold CT_NBT, CT_SMB, CT_NB63, CT_BIGB, CT_NSEC in *; lia. }
    intros q Hq. cbn [fst snd]. apply awp_aret. cbn [fst snd]. split; [| split; [reflexivity| split; [| split; reflexivity]]].
    + split; [exact Hs|]. unfold skb, arrb. cbn [sk_items sk_data sk_blk optb option_map fst snd sctsb app]. rewrite app_nil_r. change (8 * 4) with 32. perm_via (perm_skip (q, 32) HP).
    + unfold kinv. cbn [sk_data sk_items]. split; [apply GROWTH_4|]. unfold sk_num, zlength. cbn [sk_items app length]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition i2o_tot (l : list (sctr ptr)) : Z := fold_right (fun x acc => 2 + i2o_sct_len x + acc) 0 l.
Lemma i2o_tot_app l1 l2 : i2o_tot (l1 ++ l2) = i2o_tot l1 + i2o_tot l2.
Proof. unfold i2o_tot. induction l1 as [|x l IH]; cbn -[Z.add i2o_sct_len]; [lia|]. rewrite IH. lia. Qed.

(* [comment removed for export] *)
Definition linv (k : skr ptr) (u : Z) : Prop :=
  kinv k /\ bnonneg (sctsb (sk_items k)) /\ imeas_ok u (measure (sctsb (sk_items k))) /\ 3 * sk_num k <= u /\ 0 <= i2o_tot (sk_items k) <= u.

Lemma linv_mono k u1 u2 : linv k u1 -> u1 <= u2 -> linv k u2.
Proof. intros (K1 & K2 & K3 & K4 & K5) Hu. unfold linv. split; [exact K1|]. split; [exact K2|]. split; [exact (imeas_ok_mono _ _ _ K3 Hu)| lia]. Qed.

Lemma skb_meas k u : linv k u -> 0 <= u <= 65533 ->
  bnonneg (skb k) /\ 3 * m_cnt (measure (skb k)) <= 2 * u + 6 /\ 3 * m_sm (measure (skb k)) <= 107 * u + 393321
  /\ m_n63 (measure (skb k)) <= 1 /\ m_r63 (measure (skb k)) <= 203187 /\ 64513 * m_nsec (measure (skb k)) <= u + 64513.
Proof.
  intros (K1 & K2 & K3 & K4 & K5) Hu. pose proof (arrb_meas k K1) as (A0 & A1 & A2 & A3 & A4 & A5). unfold imeas_ok in K3.
  unfold skb. meas_simpl. unfold SZ_STACK. small_consts.
  split; [apply bnonneg_app; [exact K2| apply bnonneg_app; [exact A0| repeat constructor; cbn; lia]]| lia].
Qed.

Lemma RFc_loop k u R : linv k u -> RFo R -> 0 <= u <= 65533 -> RFc (skb k ++ R).
Proof.
  intros HL (F0 & F1 & F2 & F3 & F4 & F5) Hu. pose proof (skb_meas k u HL Hu) as (B0 & B1 & B2 & B3 & B4 & B5).
  unfold RFc. meas_simpl. unfold CT_NBT, CT_SMB, CT_NB63, CT_BIGB, CT_NSEC in *. split; [apply bnonneg_app; assumption| lia].
Qed.

Lemma RFs_loop k u L R : linv k u -> RFo R -> 0 <= u -> 1 <= L -> u + L <= 65531 -> RFs L (skb k ++ R).
Proof.
  intros HL (F0 & F1 & F2 & F3 & F4 & F5) Hu HL1 HuL. pose proof (skb_meas k u HL ltac:(lia)) as (B0 & B1 & B2 & B3 & B4 & B5).
  unfold RFs. meas_simpl. unfold CT_NBT, CT_SMB, CT_NB63, CT_BIGB, CT_NSEC in *. split; [apply bnonneg_app; assumption| lia].
Qed.

Lemma RFc_of_RFo R : RFo R -> RFc R.
Proof.
  intros (F0 & F1 & F2 & F3 & F4 & F5). unfold RFc. unfold CT_NBT, CT_SMB, CT_NB63, CT_BIGB, CT_NSEC in *. split; [exact F0| lia].
Qed.

(* [comment removed for export] *)
Lemma o2i_loop_S fuel c (k : skr ptr) p ll :
  o2i_loop (S fuel) c k p ll =
  (if ll <=? 0 then aret (Some k)
    else if ll <? 2 then err_raise RS_list_lt2 ;;; sk_free_all k ;;; aret None
    else
      let sct_len := u16be c p in
      let p := p + 2 in
      let ll := ll - 2 in
      if (sct_len =? 0) || (ll <? sct_len) then err_raise RS_list_sctlen ;;; sk_free_all k ;;; aret None
      else
        let ll := ll - sct_len in
        r <- o2i_sct c p sct_len ;;
        match r with
        | None => sk_free_all k ;;; aret None
        | Some s => k' <- sk_push k s ;; o2i_loop fuel c k' (p + sct_len) ll
        end).
Proof. reflexivity. Qed.

Lemma o2i_loop_spec c fuel : forall k p ll s R X,
  rel s (skb k ++ R) X -> RFo R -> linv k (p - 2) -> 2 <= p -> 0 <= ll -> p - 2 + ll <= 65533 -> ll < Z.of_nat fuel ->
  awp (o2i_loop fuel c k p ll s) X (fun r X' =>
    match fst r with
    | None => rel (snd r) R X'
    | Some k' => rel (snd r) (skb k' ++ R) X' /\ linv k' 65533 /\ sk_blk k' = sk_blk k
    end).
Proof.
  induction fuel as [|fuel IH]; intros k p ll s R X HR HF HL Hp Hll Hsum Hfuel; [cbn in Hfuel; lia|].
  rewrite o2i_loop_S. pose proof (RFc_loop k (p - 2) R HL HF ltac:(lia)) as HFc.
  destruct (Z.leb_spec ll 0) as [L0|L0].
  { apply awp_aret. cbn [fst snd]. split; [exact HR|]. split; [eapply linv_mono; [exact HL| lia]| reflexivity]. }
  destruct (Z.ltb_spec ll 2) as [L2|L2].
  { eapply raise_then; [exact HR| exact HFc| cbn; lia| cbn; lia|]. intros s1 X1 HR1 _.
    eapply seq_unit; [apply (sk_free_all_spec _ _ _ _ k s1 R X1 HR1)|]. intros X2 HR2. apply awp_aret. exact HR2. }
  cbn zeta. set (L := u16be c p). pose proof (u16be_range c p) as HLr. fold L in HLr.
  destruct (Z.eqb_spec L 0) as [EL|EL]; [| destruct (Z.ltb_spec (ll - 2) L) as [LL|LL]]; cbn [orb].
  1,2: eapply raise_then; [exact HR| exact HFc| cbn; lia| cbn; lia|]; intros s1 X1 HR1 _;
       eapply seq_unit; [apply (sk_free_all_spec _ _ _ _ k s1 R X1 HR1)|]; intros X2 HR2; apply awp_aret; exact HR2.
  (* [comment removed for export] *)
  apply awp_abind.
  eapply awp_mono; [apply (o2i_sct_spec c (p + 2) L s (skb k ++ R) X HR (RFs_loop k (p - 2) L R HL HF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia))|].
  intros [[x|] s1] X1; cbn [fst snd].
  - intros (HR1 & Bx & Ix & Lx). apply awp_abind. pose proof HL as (K1 & K2 & K3 & K4 & K5).
    eapply awp_mono; [apply (sk_push_spec k x (L + 2) (p - 2) s1 R X1 HR1 HF K1 Bx Ix K2 K3); lia|].
    intros [k2 s2] X2 (HR2 & Es2 & K2' & Ei2 & Eb2). cbn [fst snd] in *. subst s2.
    eapply awp_mono; [apply (IH k2 (p + 2 + L) (ll - 2 - L) s1 R X2 HR2 HF); try lia|].
    + (* [comment removed for export] *)
      unfold linv. rewrite Ei2. unfold sk_num. rewrite Ei2. rewrite sctsb_app, i2o_tot_app. cbn [sctsb i2o_tot fold_right]. rewrite !app_nil_r.
      unfold sk_num, zlength in K4. unfold zlength. rewrite length_app. cbn [length].
      split; [exact K2'|]. split; [apply bnonneg_app; assumption|].
      split; [rewrite measure_app; replace (p + 2 + L - 2) with ((p - 2) + (L + 2)) by lia; apply imeas_ok_add; assumption|].
      unfold i2o_tot in K5 |- *. lia.
    + intros [[k3|] s3] X3; cbn [fst snd]; [| intros H; exact H]. intros (HR3 & HL3 & Eb3). rewrite Eb3, Eb2. split; [exact HR3| split; [exact HL3| reflexivity]].
  - intros HR1. eapply seq_unit; [apply (sk_free_all_spec _ _ _ _ k s1 R X1 HR1)|]. intros X2 HR2. apply awp_aret. exact HR2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma o2i_sct_list_spec c len s R X : rel s R X -> RFo R -> 0 <= len ->
  awp (o2i_sct_list c len s) X (fun r X' =>
    match fst r with
    | None => rel (snd r) R X'
    | Some k' => rel (snd r) (skb k' ++ R) X' /\ linv k' 65533
    end).
Proof.
  intros HR HF Hlen. pose proof (RFc_of_RFo R HF) as HFc. pose proof HF as (F0 & F1 & F2 & F3 & F4 & F5). unfold o2i_sct_list.
  destruct (Z.ltb_spec len 2) as [L2|L2]; [| destruct (Z.ltb_spec MAX_SCT_LIST_SIZE len) as [LM|LM]]; cbn [orb].
  1,2: eapply raise_then; [exact HR| exact HFc| cbn; lia| cbn; lia|]; intros s1 X1 HR1 _; apply awp_aret; exact HR1.
  unfold MAX_SCT_LIST_SIZE in LM.
  destruct (Z.eqb_spec (u16be c 0) (len - 2)) as [EU|EU]; cbn [negb].
  2:{ eapply raise_then; [exact HR| exact HFc| cbn; lia| cbn; lia|]. intros s1 X1 HR1 _. apply awp_aret. exact HR1. }
  rewrite EU. apply awp_abind. destruct HR as [Hs HP].
  apply awp_amalloc; [apply lt62; unfold SZ_STACK; lia| |].
  { apply (ok_frame s R X SZ_STACK Hs ltac:(exact HP) F0); unfold SZ_STACK; small_consts; unfold CT_NBT, CT_SMB, CT_NB63, CT_BIGB, CT_NSEC in *; lia. }
  intros kb Hkb. cbn [fst snd].
  assert (HR0 : rel s (skb (mkSK kb None []) ++ R) ((kb, SZ_STACK) :: X)).
  { split; [exact Hs|]. unfold skb, arrb. cbn [sk_items sk_data sk_blk sctsb optb option_map app]. perm_via (perm_skip (kb, SZ_STACK) HP). }
  assert (HL0 : linv (mkSK kb None []) (2 - 2)).
  { unfold linv, kinv, sk_num, zlength. cbn -[Z.le Z.mul imeas_ok]. rewrite (@measure_nil ptr). split; [reflexivity|]. split; [apply Forall_nil|]. split; [apply imeas_ok_0| lia]. }
  eapply awp_mono; [apply (o2i_loop_spec c (Z.to_nat len) _ 2 (len - 2) s R _ HR0 HF HL0); lia|].
  intros [[k3|] s3] X3; cbn [fst snd sk_blk]; [intros (A & B & _); split; assumption| intros H; exact H].
Qed.

End S3.
