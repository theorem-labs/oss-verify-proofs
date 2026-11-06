(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseAbs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section W.
  Variable nc : list Z.
  Variable maxSV tableLog : Z.
  Hypothesis V : valid_ncount nc maxSV tableLog.
  Variable buf0 : list Z.                 (* [comment removed for export] *)
  Variable writeIsSafe : bool.

  Let aS := maxSV + 1.
  Let bufSize := Zlength buf0.
  (* [comment removed for export] *)
  Hypothesis Hroom : 4 + 15 * (maxSV + 1) + 16 <= 8 * bufSize.

  Let TF := a_T (afinal nc maxSV tableLog).
  Let NF := a_N (afinal nc maxSV tableLog).

  Ltac cbnW := cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0].
  Ltac cbnW_all := cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in *.

  (* [comment removed for export] *)
  Definition byte_of (N i : Z) : Z := (N / 2^(8*i)) mod 256.

  (* [comment removed for export] *)
  Definition wbits (s : wstate) (N T : Z) : Prop :=
    0 <= w_out s /\ 8 * w_out s + w_bitCount s = T /\ 0 <= w_bitCount s /\
    length (w_buf s) = length buf0 /\
    (forall i, 0 <= i < w_out s -> Znth i (w_buf s) = byte_of N i) /\
    (forall i, w_out s <= i -> Znth i (w_buf s) = Znth i buf0) /\
    w_bitStream s = N / 2^(8 * w_out s).

  Definition wrel (s : wstate) (a : astate) : Prop :=
    w_symbol s = a_sym a /\ w_remaining s = a_rem a /\ w_threshold s = a_thr a /\
    w_nbBits s = a_nb a /\ w_previousIs0 s = a_p0 a /\
    1 <= w_bitCount s <= 16 /\ wbits s (a_N a) (a_T a).

  Lemma bitStream_bound s N T :
    wbits s N T -> 0 <= N < 2^T -> 0 <= w_bitStream s < 2^(w_bitCount s).
  Proof.
    intros (A & B & B' & C & D & E & F) HN. rewrite F.
    split. { apply Z.div_pos; [lia|apply pow2_pos; lia]. }
    apply Z.div_lt_upper_bound. { apply pow2_pos; lia. }
    rewrite <- Z.pow_add_r by lia. replace (8 * w_out s + w_bitCount s) with T by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma wflush_ok dec s N T :
    wbits s N T -> 8 * w_out s + 16 <= 8 * bufSize ->
    (dec = true -> 16 < w_bitCount s) ->
    exists s', wflush bufSize writeIsSafe dec s = Ok s' /\
      wbits s' N (if dec then T else T + 16) /\
      w_out s' = w_out s + 2 /\
      w_bitCount s' = (if dec then w_bitCount s - 16 else w_bitCount s) /\
      w_symbol s' = w_symbol s /\ w_remaining s' = w_remaining s /\
      w_threshold s' = w_threshold s /\ w_nbBits s' = w_nbBits s /\ w_previousIs0 s' = w_previousIs0 s.
  Proof.
    intros WB Hroom' Hdec. pose proof WB as (A & B & B' & C & D & E & F).
    unfold wflush.
    replace (negb writeIsSafe && (bufSize - 2 <? w_out s)) with false.
    2:{ destruct writeIsSafe; simpl; auto. destruct (Z.ltb_spec (bufSize - 2) (w_out s)); auto. lia. }
    unfold bufSize, Zlength in *.
    rewrite zstore_ok by (unfold Zlength; rewrite C; lia). cbn [bind].
    rewrite zstore_ok by (unfold Zlength; rewrite Zupd_length, C; lia). cbn [bind].
    eexists. split; [reflexivity|]. unfold wbits.
    cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0].
    repeat split; auto; try lia.
    - destruct dec; lia.
    - destruct dec; [specialize (Hdec eq_refl)|]; lia.
    - rewrite !Zupd_length. auto.
    - intros i Hi.
      destruct (Z.eq_dec i (w_out s + 1)).
      { subst i. rewrite Znth_Zupd_same by (unfold Zlength; rewrite Zupd_length, C; lia).
        rewrite F. unfold to_byte, byte_of. rewrite div_pow2_div_pow2 by lia. f_equal. f_equal. f_equal. lia. }
      rewrite Znth_Zupd_other by lia.
      destruct (Z.eq_dec i (w_out s)).
      { subst i. rewrite Znth_Zupd_same by (unfold Zlength; rewrite C; lia).
        rewrite F. unfold to_byte, byte_of. reflexivity. }
      rewrite Znth_Zupd_other by lia. apply D. lia.
    - intros i Hi. rewrite !Znth_Zupd_other by lia. apply E. lia.
    - rewrite F. rewrite div_pow2_div_pow2 by lia. f_equal. f_equal. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma skip_zeros_ok f g j :
    0 <= j <= aS -> aS - j < Z.of_nat f -> maxSV - j < Z.of_nat g ->
    skip_zeros nc aS f j = Ok (next_nz nc maxSV g j).
  Proof.
    pose proof (V_len _ _ _ V) as LEN. pose proof (V_msv _ _ _ V).
    revert g j. induction f; intros g j Hj Hf Hg; [simpl in Hf; lia|].
    cbn [skip_zeros]. destruct g as [|g'].
    - simpl in Hg. cbn [next_nz]. destruct (Z.ltb_spec j aS); [unfold aS in *; lia|]. reflexivity.
    - cbn [next_nz]. fold aS. destruct (Z.ltb_spec j aS).
      + rewrite zload_ok by (unfold Zlength; rewrite LEN; unfold aS in *; lia). cbn [bind andb].
        destruct (Z.eqb_spec (Znth j nc) 0).
        * apply IHf; unfold aS in *; lia.
        * reflexivity.
      + cbn [andb]. reflexivity.
  Qed.


  Definition same_ctl (s s' : wstate) : Prop :=
    w_symbol s' = w_symbol s /\ w_remaining s' = w_remaining s /\ w_threshold s' = w_threshold s /\
    w_nbBits s' = w_nbBits s /\ w_previousIs0 s' = w_previousIs0 s.

  Lemma byte_of_bits N i : byte_of N i = bits N (8*i) 8.
  Proof. reflexivity. Qed.

  Lemma ones_concat a b : 0 <= a -> 0 <= b -> (2^a - 1) + (2^b - 1) * 2^a = 2^(a+b) - 1.
  Proof. intros. rewrite Z.pow_add_r by lia. nia. Qed.

  (* [comment removed for export] *)
  Lemma wbits_add s N T v :
    wbits s N T -> 0 <= N < 2^T -> 0 <= v ->
    wbits (mkW (w_buf s) (w_out s) (w_bitStream s + v * 2^(w_bitCount s)) (w_bitCount s)
               (w_symbol s) (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s))
          (N + v * 2^T) T.
  Proof.
    intros (A & B & B' & C & D & E & F) HN Hv. unfold wbits; cbnW. repeat split; auto; try lia.
    - intros i Hi. rewrite D by lia. rewrite !byte_of_bits. symmetry. apply bits_append_lo; lia.
    - rewrite F. replace (2^T) with (2^(w_bitCount s) * 2^(8 * w_out s)).
      2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      rewrite Z.mul_assoc. rewrite div_add_mul_pow2 by lia. reflexivity.
  Qed.


  Lemma same_ctl_refl s : same_ctl s s. Proof. repeat split. Qed.
  Lemma same_ctl_trans s1 s2 s3 : same_ctl s1 s2 -> same_ctl s2 s3 -> same_ctl s1 s3.
  Proof. unfold same_ctl; intros; intuition congruence. Qed.

  (* [comment removed for export] *)
  Lemma run24_ok f : forall s start N T Tlim q,
    wbits s N T -> 0 <= N < 2^T -> 1 <= w_bitCount s <= 16 ->
    0 <= start <= w_symbol s -> q = (w_symbol s - start) / 24 -> q < Z.of_nat f ->
    T + 16 * q <= Tlim -> Tlim <= 8 * bufSize ->
    exists s', run24 bufSize writeIsSafe f s start = Ok (s', start + 24 * q) /\
      wbits s' (N + (2^(16*q) - 1) * 2^T) (T + 16*q) /\
      w_bitCount s' = w_bitCount s /\ same_ctl s s'.
  Proof.
    induction f; intros s start N T Tlim q WB HN Hbc Hst Hq Hf HT HTlim.
    { exfalso. simpl in Hf. assert (0 <= q) by (subst q; apply Z.div_pos; lia). lia. }
    cbn [run24]. destruct (Z.leb_spec (start + 24) (w_symbol s)).
    - assert (1 <= q). { subst q. apply Z.div_le_lower_bound; lia. }
      rewrite shl32_ok by lia.
      assert (P16 : 2^(w_bitCount s) <= 2^16) by (apply Z.pow_le_mono_r; lia).
      assert (P0 : 0 < 2^(w_bitCount s)) by (apply pow2_pos; lia).
      pose proof (bitStream_bound s N T WB HN) as BS.
      rewrite (u32_id (65535 * _)) by (change (2^32) with (65536 * 2^16); nia). cbn [bind].
      rewrite u32_id by (change (2^32) with (65536 * 2^16); nia).
      pose proof (wbits_add s N T 65535 WB HN ltac:(lia)) as WB1.
      pose proof WB as (A & B & _).
      destruct (wflush_ok false _ _ _ WB1) as (s2 & E2 & WB2 & O2 & BC2 & SY2 & RE2 & TH2 & NB2 & PZ2).
      { cbnW. lia. } { intros; discriminate. }
      rewrite E2. cbnW_all.
      destruct (IHf s2 (start + 24) (N + 65535 * 2^T) (T + 16) Tlim (q - 1)) as (s' & E' & WB' & BC' & SC').
      + exact WB2.
      + change 65535 with (2^16 - 1). pose proof (append_bound N (2^16-1) T 16). lia.
      + lia.
      + lia.
      + rewrite SY2. subst q. replace (w_symbol s - (start + 24)) with ((w_symbol s - start) + (-1) * 24) by lia.
        rewrite Z.div_add by lia. lia.
      + lia.
      + lia.
      + lia.
      + exists s'. cbn [bind]. rewrite E'. split. { f_equal. f_equal. lia. }
        split. 2:{ split; [lia|]. unfold same_ctl in *. intuition congruence. }
        replace (T + 16 + 16 * (q - 1)) with (T + 16 * q) in WB' by lia.
        replace (N + 65535 * 2^T + (2^(16*(q-1)) - 1) * 2^(T+16))
           with (N + (2^(16*q) - 1) * 2^T) in WB'; auto.
        rewrite (Z.pow_add_r 2 T 16) by lia.
        replace (16 * q) with (16 + 16 * (q - 1)) by lia.
        rewrite <- (ones_concat 16 (16 * (q-1))) by lia. change (2^16) with 65536. lia.
    - assert (q = 0). { subst q. apply Z.div_small. lia. }
      subst q. rewrite H0. exists s. split. { f_equal. f_equal. lia. }
      split. { rewrite Z.mul_0_r, Z.pow_0_r. replace (N + (1 - 1) * 2^T) with N by lia. rewrite Z.add_0_r. exact WB. }
      split; [lia| apply same_ctl_refl].
  Qed.


  Lemma wbits_append s N T v w :
    wbits s N T -> 0 <= N < 2^T -> 0 <= v -> 0 <= w ->
    wbits (mkW (w_buf s) (w_out s) (w_bitStream s + v * 2^(w_bitCount s)) (w_bitCount s + w)
               (w_symbol s) (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s))
          (N + v * 2^T) (T + w).
  Proof.
    intros (A & B & B' & C & D & E & F) HN Hv Hw. unfold wbits; cbnW. repeat split; auto; try lia.
    - intros i Hi. rewrite D by lia. rewrite !byte_of_bits. symmetry. apply bits_append_lo; lia.
    - rewrite F. replace (2^T) with (2^(w_bitCount s) * 2^(8 * w_out s)).
      2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      rewrite Z.mul_assoc. rewrite div_add_mul_pow2 by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma run3_ok f : forall s start N T q,
    wbits s N T -> 0 <= N < 2^T -> 0 <= w_bitCount s ->
    0 <= start <= w_symbol s -> q = (w_symbol s - start) / 3 -> q < Z.of_nat f ->
    w_bitCount s + 2 * q <= 32 ->
    exists s', run3 f s start = Ok (s', start + 3 * q) /\
      wbits s' (N + (2^(2*q) - 1) * 2^T) (T + 2*q) /\
      w_bitCount s' = w_bitCount s + 2 * q /\ w_out s' = w_out s /\ same_ctl s s'.
  Proof.
    induction f; intros s start N T q WB HN Hbc Hst Hq Hf Hroom2.
    { exfalso. simpl in Hf. assert (0 <= q) by (subst q; apply Z.div_pos; lia). lia. }
    cbn [run3]. destruct (Z.leb_spec (start + 3) (w_symbol s)).
    - assert (1 <= q). { subst q. apply Z.div_le_lower_bound; lia. }
      rewrite shl32_ok by lia.
      assert (P30 : 2^(w_bitCount s) <= 2^30) by (apply Z.pow_le_mono_r; lia).
      assert (P0 : 0 < 2^(w_bitCount s)) by (apply pow2_pos; lia).
      pose proof (bitStream_bound s N T WB HN) as BS.
      rewrite (u32_id (3 * _)) by (change (2^32) with (4 * 2^30); nia). cbn [bind].
      rewrite u32_id by (change (2^32) with (4 * 2^30); nia).
      pose proof (wbits_append s N T 3 2 WB HN ltac:(lia) ltac:(lia)) as WB1.
      pose proof WB as (A & B & _).
      destruct (IHf _ (start + 3) (N + 3 * 2^T) (T + 2) (q - 1) WB1) as (s' & E' & WB' & BC' & OUT' & SC'); cbnW_all.
      + change 3 with (2^2 - 1) at 1. pose proof (append_bound N (2^2-1) T 2). lia.
      + lia.
      + lia.
      + subst q. replace (w_symbol s - (start + 3)) with ((w_symbol s - start) + (-1) * 3) by lia.
        rewrite Z.div_add by lia. lia.
      + lia.
      + lia.
      + exists s'. cbn [bind]. rewrite E'. split. { f_equal. f_equal. lia. }
        split. 2:{ split; [lia|]. split; [lia|]. unfold same_ctl in *; cbnW_all. intuition congruence. }
        replace (T + 2 + 2 * (q - 1)) with (T + 2 * q) in WB' by lia.
        replace (N + 3 * 2^T + (2^(2*(q-1)) - 1) * 2^(T+2))
           with (N + (2^(2*q) - 1) * 2^T) in WB'; auto.
        rewrite (Z.pow_add_r 2 T 2) by lia.
        replace (2 * q) with (2 + 2 * (q - 1)) by lia.
        rewrite <- (ones_concat 2 (2 * (q-1))) by lia. change (2^2) with 4. lia.
    - assert (q = 0). { subst q. apply Z.div_small. lia. }
      subst q. rewrite H0. exists s. split. { f_equal. f_equal. lia. }
      split. { rewrite Z.mul_0_r, Z.pow_0_r. replace (N + (1 - 1) * 2^T) with N by lia. rewrite Z.add_0_r. exact WB. }
      split; [lia|]. split; [lia | apply same_ctl_refl].
  Qed.


  Lemma wflush_if_ok s N T :
    wbits s N T -> 1 <= w_bitCount s <= 32 -> T <= 8 * bufSize ->
    exists s', wflush_if bufSize writeIsSafe s = Ok s' /\ wbits s' N T /\
      1 <= w_bitCount s' <= 16 /\ same_ctl s s'.
  Proof.
    intros WB Hbc HT. unfold wflush_if. pose proof WB as (A & B & _).
    destruct (Z.ltb_spec 16 (w_bitCount s)).
    - destruct (wflush_ok true s N T WB) as (s' & E & WB' & O' & BC' & SY & RE & TH & NB & PZ); [lia|auto|].
      exists s'. rewrite E. split; [reflexivity|]. split; [exact WB'|]. split; [lia|]. repeat split; congruence.
    - exists s. split; [reflexivity|]. split; [exact WB|]. split; [lia|]. apply same_ctl_refl.
  Qed.

  Lemma wbits_T_nonneg s N T : wbits s N T -> 0 <= T.
  Proof. intros (A & B & B' & _). lia. Qed.

  (* [comment removed for export] *)
  Lemma wzero_block_ok s a :
    ainv nc maxSV tableLog a -> a_sym a <= maxSV -> wrel s a -> a_p0 a = true ->
    let '(j, N1, T1) := askip nc maxSV a in
    T1 <= 8 * bufSize ->
    exists s', wzero_block nc aS bufSize writeIsSafe s = Ok (Cont s') /\
      w_symbol s' = j /\ wbits s' N1 T1 /\ 1 <= w_bitCount s' <= 16 /\
      w_remaining s' = a_rem a /\ w_threshold s' = a_thr a /\ w_nbBits s' = a_nb a /\
      w_previousIs0 s' = a_p0 a.
  Proof.
    intros I Hs R P0.
    pose proof (askip_spec nc maxSV tableLog V a I Hs) as SK.
    destruct (askip nc maxSV a) as [[j N1] T1] eqn:ESK.
    destruct SK as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & _).
    destruct (S7 P0) as (J1 & J2 & J3 & J4 & J5). clear S7.
    intros HT1.
    destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & WB).
    destruct I as (A & B & C & D & E & F & G).
    pose proof (V_msv _ _ _ V). pose proof (V_len _ _ _ V) as LEN.
    set (k := j - a_sym a) in *.
    pose proof (runw_pos k ltac:(lia)) as RW.
    unfold wzero_block.
    rewrite (skip_zeros_ok _ 256) by (unfold aS; rewrite ?R1; simpl; lia). cbn [bind].
    rewrite R1, <- J1.
    destruct (Z.eqb_spec j aS); [unfold aS in *; lia|].
    (* [comment removed for export] *)
    set (s0 := mkW (w_buf s) (w_out s) (w_bitStream s) (w_bitCount s) j (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s)).
    assert (WB0 : wbits s0 (a_N a) (a_T a)) by (unfold wbits in *; cbnW_all; exact WB).
    set (q24 := k / 24).
    assert (Hq24a : 0 <= q24) by (subst q24; apply Z.div_pos; lia).
    assert (Hq24 : 0 <= q24 /\ 8 * q24 <= k / 3).
    { split; auto. subst q24.
      apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le k 24 ltac:(lia)). lia. }
    assert (Hk3 : k / 3 <= maxSV). { apply Z.div_le_upper_bound; lia. }
    assert (Hq24def : q24 = (j - a_sym a) / 24) by reflexivity.
    assert (HT1' : a_T a + 16 * q24 <= T1) by (rewrite J3; unfold runw; lia).
    destruct (run24_ok (S (Z.to_nat aS)) s0 (a_sym a) (a_N a) (a_T a) T1 q24 WB0)
      as (s1 & E1 & WB1 & BC1 & SC1); subst s0; cbnW_all; auto; try lia.
    rewrite E1. cbn [bind].
    (* [comment removed for export] *)
    set (m := k - 24 * q24).
    assert (Hm : 0 <= m < 24). { subst m q24. pose proof (Z.mod_pos_bound k 24 ltac:(lia)). rewrite Zmod_eq in * by lia. lia. }
    set (q3 := m / 3).
    assert (Hq3 : 0 <= q3 < 8). { subst q3. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. }
    assert (Hk3' : k / 3 = 8 * q24 + q3).
    { subst q3 m. replace (k - 24 * q24) with (k + (- (8 * q24)) * 3) by lia.
      rewrite Z.div_add by lia. lia. }
    destruct SC1 as (SY1 & RE1 & TH1 & NB1 & PZ1). cbnW_all.
    pose proof (append_bound (a_N a) (2^(16*q24) - 1) (a_T a) (16 * q24) ltac:(lia) ltac:(lia) ltac:(lia)) as AB1.
    assert (HB1 : 0 <= 2^(16*q24) - 1 < 2^(16*q24)). { pose proof (pow2_pos (16*q24)). lia. }
    specialize (AB1 HB1).
    destruct (run3_ok (S (Z.to_nat aS)) s1 (a_sym a + 24 * q24) _ _ q3 WB1 AB1)
      as (s2 & E2 & WB2 & BC2 & OUT2 & SC2); try lia.
    { rewrite SY1. subst q3 m k. f_equal. lia. }
    rewrite E2. cbn [bind].
    destruct SC2 as (SY2 & RE2 & TH2 & NB2 & PZ2).
    (* [comment removed for export] *)
    rewrite shl32_ok by lia.
    set (v := j - (a_sym a + 24 * q24 + 3 * q3)).
    assert (Hv : v = k mod 3 /\ 0 <= v < 3).
    { subst v. rewrite (Zmod_eq k 3) by lia. rewrite Hk3'. subst q3 m k.
      pose proof (Z.mod_pos_bound (j - a_sym a - 24 * q24) 3 ltac:(lia)) as MB.
      rewrite Zmod_eq in MB by lia. lia. }
    rewrite SY2. fold v.
    assert (P30 : 2^(w_bitCount s2) <= 2^30) by (apply Z.pow_le_mono_r; lia).
    assert (P0' : 0 < 2^(w_bitCount s2)) by (apply pow2_pos; lia).
    set (N2 := a_N a + (2^(16*q24) - 1) * 2^(a_T a) + (2^(2*q3) - 1) * 2^(a_T a + 16 * q24)) in *.
    set (T2 := a_T a + 16 * q24 + 2 * q3) in *.
    assert (HN2 : 0 <= N2 < 2^T2).
    { subst N2 T2. pose proof (pow2_pos (2*q3)). apply append_bound; lia. }
    pose proof (bitStream_bound s2 N2 T2 WB2 HN2) as BS2.
    rewrite (u32_id v) by lia.
    rewrite (u32_id (v * _)) by (change (2^32) with (4 * 2^30); nia). cbn [bind].
    rewrite u32_id by (change (2^32) with (4 * 2^30); nia).
    pose proof (wbits_append s2 N2 T2 v 2 WB2 HN2 ltac:(lia) ltac:(lia)) as WB3.
    match goal with |- context [wflush_if _ _ ?st] => set (s3 := st) in * end.
    assert (HT : T2 + 2 = T1).
    { subst T2. rewrite J3. unfold runw. rewrite Hk3'. lia. }
    destruct (wflush_if_ok s3 _ _ WB3) as (s4 & E4 & WB4 & BC4 & SC4); [subst s3; cbnW; lia| lia |].
    rewrite E4. exists s4. split; [reflexivity|].
    destruct SC4 as (SY4 & RE4 & TH4 & NB4 & PZ4). subst s3. cbnW_all.
    split; [congruence|]. split.
    { rewrite HT in WB4. replace (N2 + v * 2^T2) with N1 in WB4; auto.
      rewrite J2. subst N2 T2. unfold runval. rewrite Hk3', (proj1 Hv).
      replace (2 * (8 * q24 + q3)) with (16 * q24 + 2 * q3) by lia.
      rewrite <- (ones_concat (16 * q24) (2 * q3)) by lia.
      rewrite !Z.pow_add_r by lia. lia. }
    repeat split; try lia; congruence.
  Qed.


  (* [comment removed for export] *)
  Lemma shrink_ok f : forall r t nb,
    1 <= r -> 1 <= nb -> t = 2^(nb-1) -> nb <= Z.of_nat f ->
    shrink f r t nb = Ok (norm r t nb).
  Proof.
    induction f; intros r t nb Hr Hnb Ht Hf; [simpl in Hf; lia|].
    cbn [shrink]. unfold norm. destruct (Z.ltb_spec r t); auto.
    assert (Hnb2 : 2 <= nb).
    { destruct (Z_lt_le_dec nb 2); auto. assert (nb = 1) by lia. subst. simpl in *. lia. }
    assert (Ht2 : t / 2 = 2^(nb-1-1)).
    { subst t. replace (nb-1) with ((nb-1-1)+1) at 1 by lia. rewrite pow2_S by lia.
      rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
    rewrite (IHf r (t/2) (nb-1)); try lia.
    unfold norm. destruct (Z.ltb_spec r (t/2)); auto.
    assert (Z.log2 r = nb - 2).
    { apply Z.log2_unique; [lia|]. rewrite Z.pow_succ_r by lia.
      replace (nb-1-1) with (nb-2) in Ht2 by lia. rewrite <- Ht2.
      rewrite Ht in *. replace (nb-1) with ((nb-2)+1) in * by lia. rewrite pow2_S in * by lia.
      rewrite Z.mul_comm, Z.div_mul in * by lia. lia. }
    rewrite H1. rewrite Ht2. f_equal. f_equal; [f_equal; lia | lia].
  Qed.


  (* [comment removed for export] *)
  Lemma wcount_block_ok s1 a :
    ainv nc maxSV tableLog a -> a_sym a <= maxSV ->
    let '(j, N1, T1) := askip nc maxSV a in
    w_symbol s1 = j -> wbits s1 N1 T1 -> 1 <= w_bitCount s1 <= 16 ->
    w_remaining s1 = a_rem a -> w_threshold s1 = a_thr a -> w_nbBits s1 = a_nb a ->
    let a' := astep nc maxSV a in
    exists s2, wcount_block nc s1 = Ok s2 /\
      w_symbol s2 = a_sym a' /\ w_remaining s2 = a_rem a' /\ w_threshold s2 = a_thr a' /\
      w_nbBits s2 = a_nb a' /\ w_previousIs0 s2 = a_p0 a' /\
      wbits s2 (a_N a') (a_T a') /\ 2 <= w_bitCount s2 <= 29 /\ w_out s2 = w_out s1.
  Proof.
    intros I Hs.
    pose proof (askip_spec nc maxSV tableLog V a I Hs) as SK.
    unfold astep.
    destruct (askip nc maxSV a) as [[j N1] T1] eqn:ESK.
    destruct SK as (S1 & S2 & S3 & S4 & S5 & S6 & _ & _).
    intros SY WB BC RE TH NB.
    pose proof (acount_pre nc maxSV tableLog V a j I ltac:(lia) S2) as CP. cbv zeta in CP.
    destruct CP as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
    pose proof (count_code_ok (Znth j nc) (a_rem a) (a_thr a) (a_nb a) C9 C10 C11 C4 C1 C3) as CC.
    cbv zeta in CC. destruct CC as (K1 & K2 & K3 & K4 & K5 & _).
    set (c := Znth j nc) in *.
    set (v := cval c (a_rem a) (a_thr a)) in *.
    set (w := cwidth c (a_rem a) (a_thr a) (a_nb a)) in *.
    destruct I as (A & B & C & D & E & F & G).
    pose proof (V_msv _ _ _ V). pose proof (V_len _ _ _ V) as LEN. pose proof (V_tl _ _ _ V).
    unfold wcount_block.
    rewrite zload_ok by (unfold Zlength; rewrite LEN; lia). cbn [bind]. rewrite SY. fold c.
    rewrite RE, TH, NB.
    replace (if c <? 0 then - c else c) with (Z.abs c) by (destruct (Z.ltb_spec c 0); lia).
    replace (if a_thr a <=? c + 1 then c + 1 + (2 * a_thr a - 1 - a_rem a) else c + 1) with v by reflexivity.
    replace (a_nb a - (if v <? 2 * a_thr a - 1 - a_rem a then 1 else 0)) with w by reflexivity.
    assert (Pw : 2^w <= 2^13) by (apply Z.pow_le_mono_r; lia).
    assert (Pbc : 2^(w_bitCount s1) <= 2^16) by (apply Z.pow_le_mono_r; lia).
    assert (Pbc0 : 0 < 2^(w_bitCount s1)) by (apply pow2_pos; lia).
    pose proof (bitStream_bound s1 N1 T1 WB S3) as BS.
    rewrite shl32_ok by lia. rewrite (u32_id v) by (change (2^32) with (2^13 * 2^19); lia).
    rewrite (u32_id (v * _)) by (change (2^32) with (2^13 * 2^3 * 2^16); nia). cbn [bind].
    rewrite u32_id by (change (2^32) with (2^16 * 2^3 * 2^13); nia).
    destruct (Z.ltb_spec (a_rem a - Z.abs c) 1); [lia|].
    rewrite (shrink_ok 64) by (simpl; lia). cbn [bind].
    destruct (norm (a_rem a - Z.abs c) (a_thr a) (a_nb a)) as [t' nb'] eqn:EN.
    eexists. split; [reflexivity|]. cbnW. cbn [a_sym a_rem a_thr a_nb a_p0 a_N a_T].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split.
    { replace (w_bitCount s1 + a_nb a - (if v <? 2 * a_thr a - 1 - a_rem a then 1 else 0))
        with (w_bitCount s1 + w) by (subst w v; unfold cwidth, cmax; lia).
      apply (wbits_append s1 N1 T1 v w WB S3); lia. }
    subst w v. unfold cwidth, cmax in *. split; [lia|reflexivity].
  Qed.


  Lemma astep_T a :
    ainv nc maxSV tableLog a -> a_sym a <= maxSV ->
    let '(j, N1, T1) := askip nc maxSV a in
    T1 + 1 <= a_T (astep nc maxSV a) <= T1 + 13 /\ a_sym (astep nc maxSV a) = j + 1.
  Proof.
    intros I Hs.
    pose proof (askip_spec nc maxSV tableLog V a I Hs) as SK.
    unfold astep.
    destruct (askip nc maxSV a) as [[j N1] T1] eqn:ESK.
    destruct SK as (S1 & S2 & S3 & S4 & S5 & S6 & _ & _).
    pose proof (acount_pre nc maxSV tableLog V a j I ltac:(lia) S2) as CP. cbv zeta in CP.
    destruct CP as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
    pose proof (count_code_ok (Znth j nc) (a_rem a) (a_thr a) (a_nb a) C9 C10 C11 C4 C1 C3) as CC.
    cbv zeta in CC. destruct CC as (K1 & K2 & K3 & K4 & K5 & _).
    destruct (norm _ _ _) as [t' nb']. cbn [a_T a_sym].
    destruct I as (A & B & C & D & E & F & G). pose proof (V_tl _ _ _ V). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma wbody_ok s a :
    ainv nc maxSV tableLog a -> a_sym a <= maxSV -> wrel s a ->
    a_T (astep nc maxSV a) <= 8 * bufSize ->
    exists s', wbody nc aS bufSize writeIsSafe s = Ok (Cont s') /\ wrel s' (astep nc maxSV a).
  Proof.
    intros I Hs R HT.
    pose proof (astep_T a I Hs) as AT.
    pose proof (wzero_block_ok s a I Hs R) as ZB.
    pose proof (wcount_block_ok) as CB.
    pose proof (askip_spec nc maxSV tableLog V a I Hs) as SK.
    destruct (askip nc maxSV a) as [[j N1] T1] eqn:ESK.
    destruct AT as [AT1 AT2].
    destruct SK as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & WB).
    unfold wbody. rewrite R5.
    (* [comment removed for export] *)
    assert (exists s1, (if a_p0 a then wzero_block nc aS bufSize writeIsSafe s else Ok (Cont s)) = Ok (Cont s1)
              /\ w_symbol s1 = j /\ wbits s1 N1 T1 /\ 1 <= w_bitCount s1 <= 16
              /\ w_remaining s1 = a_rem a /\ w_threshold s1 = a_thr a /\ w_nbBits s1 = a_nb a)
      as (s1 & E1 & SY1 & WB1 & BC1 & RE1 & TH1 & NB1).
    { destruct (a_p0 a) eqn:P0.
      - destruct (ZB eq_refl ltac:(lia)) as (s1 & E1 & Q). exists s1. rewrite E1. split; [reflexivity|]. tauto.
      - destruct (S8 eq_refl) as (-> & -> & ->). exists s. split; [reflexivity|]. split; [auto|]. split; [exact WB|].
        repeat split; auto; lia. }
    rewrite E1. cbn [bind].
    specialize (CB s1 a I Hs). rewrite ESK in CB.
    destruct (CB SY1 WB1 BC1 RE1 TH1 NB1) as (s2 & E2 & SY2 & RE2 & TH2 & NB2 & PZ2 & WB2 & BC2 & OUT2).
    rewrite E2. cbn [bind].
    destruct (wflush_if_ok s2 _ _ WB2 ltac:(lia) HT) as (s3 & E3 & WB3 & BC3 & SC3).
    rewrite E3. exists s3. split; [reflexivity|].
    destruct SC3 as (SY3 & RE3 & TH3 & NB3 & PZ3).
    unfold wrel. split; [congruence|]. split; [congruence|]. split; [congruence|].
    split; [congruence|]. split; [congruence|]. split; [lia|]. exact WB3.
  Qed.

  (* [comment removed for export] *)
  Lemma wloop_ok f : forall s a,
    ainv nc maxSV tableLog a -> wrel s a ->
    acond maxSV (arun nc maxSV f a) = false ->
    a_T (arun nc maxSV f a) <= 8 * bufSize ->
    exists s', wloop nc aS bufSize writeIsSafe (S f) s = Ok s' /\ wrel s' (arun nc maxSV f a).
  Proof.
    induction f; intros s a I R DONE HT.
    - cbn [arun] in *. cbn [wloop]. pose proof R as (R1 & R2 & _).
      unfold acond in DONE. fold aS in DONE. rewrite <- R1, <- R2 in DONE. rewrite DONE.
      exists s; split; auto.
    - cbn [arun] in *. cbn [wloop]. pose proof R as (R1 & R2 & _).
      destruct (acond maxSV a) eqn:C.
      + pose proof C as C'. unfold acond in C'. fold aS in C'. rewrite <- R1, <- R2 in C'. rewrite C'.
        pose proof (proj1 (acond_true nc maxSV tableLog V a I) C) as Hs.
        pose proof (astep_ainv nc maxSV tableLog V a I Hs) as (I' & _ & _ & _).
        pose proof (arun_prefix nc maxSV tableLog V f (astep nc maxSV a) I') as (P1 & _).
        destruct (wbody_ok s a I Hs R ltac:(lia)) as (s1 & E1 & R1').
        rewrite E1. cbn [bind]. apply IHf; auto.
      + unfold acond in C. fold aS in C. rewrite <- R1, <- R2 in C. rewrite C.
        exists s; split; auto.
  Qed.


  (* [comment removed for export] *)
  Lemma winit_ok : exists s0, winit buf0 tableLog = Ok s0 /\ wrel s0 (a0 tableLog).
  Proof.
    pose proof (V_tl _ _ _ V). unfold winit, assert.
    destruct (Z.leb_spec 0 tableLog); [|lia]. destruct (Z.ltb_spec tableLog 31); [|lia]. cbn [andb bind].
    rewrite shl32_ok by lia. cbn [bind]. unfold FSE_MIN_TABLELOG.
    rewrite Z.pow_0_r, Z.mul_1_r.
    rewrite (u32_id (tableLog - 5)) by (change (2^32) with 4294967296; lia).
    rewrite (u32_id (tableLog - 5)) by (change (2^32) with 4294967296; lia).
    rewrite Z.add_0_l.
    rewrite (u32_id (tableLog - 5)) by (change (2^32) with 4294967296; lia).
    eexists; split; [reflexivity|].
    unfold wrel, wbits, a0; cbnW; cbn [a_sym a_rem a_thr a_nb a_p0 a_N a_T]. unfold FSE_MIN_TABLELOG.
    repeat split; try lia.
    rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity.
  Qed.

  Lemma TF_ge_9 : 9 <= TF.
  Proof.
    pose proof (V_msv _ _ _ V). pose proof (V_tl _ _ _ V).
    pose proof (ainv_a0 nc maxSV tableLog V) as I0.
    assert (C0 : acond maxSV (a0 tableLog) = true).
    { apply (acond_true nc maxSV tableLog V); auto. cbn [a0 a_sym]. lia. }
    unfold TF, afinal. cbn [arun]. rewrite C0.
    pose proof (astep_ainv nc maxSV tableLog V (a0 tableLog) I0 ltac:(cbn [a0 a_sym]; lia)) as (I1 & _).
    pose proof (arun_prefix nc maxSV tableLog V (Z.to_nat (maxSV + 1)) _ I1) as (P1 & _).
    enough (9 <= a_T (astep nc maxSV (a0 tableLog))) by lia.
    pose proof (askip_spec nc maxSV tableLog V (a0 tableLog) I0 ltac:(cbn [a0 a_sym]; lia)) as SK.
    unfold astep. destruct (askip nc maxSV (a0 tableLog)) as [[j N1] T1] eqn:ESK.
    destruct SK as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
    specialize (S8 ltac:(reflexivity)). destruct S8 as (-> & -> & ->).
    pose proof (acount_pre nc maxSV tableLog V (a0 tableLog) (a_sym (a0 tableLog)) I0 ltac:(cbn [a0 a_sym]; lia) eq_refl) as CP.
    cbv zeta in CP. destruct CP as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
    pose proof (count_code_ok _ _ _ _ C9 C10 C11 C4 C1 C3) as CC.
    cbv zeta in CC. destruct CC as (K1 & K2 & K3 & K4 & K5 & _).
    destruct (norm _ _ _) as [t' nb']. cbn [a_T]. cbn [a0 a_nb a_T a_sym a_rem a_thr] in *. lia.
  Qed.

  Definition hdrSize : Z := (TF + 7) / 8.

  (* [comment removed for export] *)
  Theorem write_generic_ok :
    exists buf' E,
      write_ncount_generic buf0 nc maxSV tableLog writeIsSafe = Ok (buf', hdrSize) /\
      length buf' = length buf0 /\
      8 * (hdrSize - 1) < TF <= 8 * hdrSize /\ 2 <= hdrSize /\ 8 * hdrSize <= 4 + 15 * (maxSV + 1) + 7 /\
      hdrSize <= E <= hdrSize + 1 /\ E <= bufSize /\
      (forall i, 0 <= i < E -> Znth i buf' = byte_of NF i) /\
      (forall i, E <= i -> Znth i buf' = Znth i buf0).
  Proof.
    pose proof (V_msv _ _ _ V). pose proof (V_tl _ _ _ V).
    pose proof (afinal_spec nc maxSV tableLog V) as (IF & SYF & REMF & CF & TBF & NBF).
    pose proof TF_ge_9 as T9. fold TF in TBF. fold NF TF in NBF.
    destruct winit_ok as (s0 & E0 & R0).
    unfold write_ncount_generic. fold bufSize aS. rewrite E0. cbn [bind].
    assert (EaS : S (Z.to_nat aS) = S (Z.to_nat (maxSV + 1))) by reflexivity.
    destruct (wloop_ok (Z.to_nat (maxSV + 1)) s0 (a0 tableLog) (ainv_a0 nc maxSV tableLog V) R0)
      as (s1 & E1 & R1).
    { apply (arun_acond_done nc maxSV tableLog V). lia. }
    { rewrite (arun_afinal nc maxSV tableLog V) by lia. fold TF. lia. }
    rewrite (arun_afinal nc maxSV tableLog V) in R1 by lia.
    unfold aS in E1 |- *. rewrite E1. cbn [bind].
    destruct R1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & WB).
    pose proof WB as (A & B & B' & C & D & E & F). fold TF in B. fold NF in D, F.
    unfold wfinish. rewrite Q2, REMF. cbn [Z.eqb Pos.eqb negb].
    replace (negb writeIsSafe && (bufSize - 2 <? w_out s1)) with false.
    2:{ destruct writeIsSafe; simpl; auto. destruct (Z.ltb_spec (bufSize - 2) (w_out s1)); auto. lia. }
    unfold bufSize, Zlength in *.
    rewrite zstore_ok by (unfold Zlength; rewrite C; lia). cbn [bind].
    rewrite zstore_ok by (unfold Zlength; rewrite Zupd_length, C; lia). cbn [bind].
    rewrite Z.quot_div_nonneg by lia.
    assert (HS : hdrSize = w_out s1 + (w_bitCount s1 + 7) / 8).
    { unfold hdrSize. rewrite <- B. replace (8 * w_out s1 + w_bitCount s1 + 7) with (w_out s1 * 8 + (w_bitCount s1 + 7)) by lia.
      rewrite Z.div_add_l by lia. reflexivity. }
    rewrite <- HS.
    eexists _, (w_out s1 + 2). split; [reflexivity|].
    assert (1 <= (w_bitCount s1 + 7) / 8 < 3).
    { split. apply Z.div_le_lower_bound; lia. apply Z.div_lt_upper_bound; lia. }
    assert (8 * ((w_bitCount s1 + 7) / 8) < w_bitCount s1 + 8 /\ w_bitCount s1 <= 8 * ((w_bitCount s1 + 7) / 8)).
    { pose proof (Z.div_mod (w_bitCount s1 + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (w_bitCount s1 + 7) 8 ltac:(lia)). lia. }
    pose proof (bitStream_bound s1 NF TF WB NBF) as BS.
    repeat split; try lia.
    - rewrite !Zupd_length. exact C.
    - intros i Hi.
      destruct (Z.eq_dec i (w_out s1 + 1)).
      { subst i. rewrite Znth_Zupd_same by (unfold Zlength; rewrite Zupd_length, C; lia).
        rewrite F. unfold to_byte, byte_of. rewrite div_pow2_div_pow2 by lia. f_equal. f_equal. f_equal. lia. }
      rewrite Znth_Zupd_other by lia.
      destruct (Z.eq_dec i (w_out s1)).
      { subst i. rewrite Znth_Zupd_same by (unfold Zlength; rewrite C; lia).
        rewrite F. unfold to_byte, byte_of. reflexivity. }
      rewrite Znth_Zupd_other by lia. apply D. lia.
    - intros i Hi. rewrite !Znth_Zupd_other by lia. apply E. lia.
  Qed.

End W.
