From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLib RcIdentModel RcIdentLib reac_identity_ingest_c.
Import ListNotations.
Open Scope Z_scope.

Lemma fin_refused : forall ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m id ad p len idb pb
    (y0 y1 x1 x2 x3 x4 x5 x6 x7 : word),
  ingest_refused id p len = true ->
  reac_identity_ingest_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m id ad p len idb pb
    (MS (mkR ra sp gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 (-1)) x1 x2 x3 x4 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m id ad p len idb pb
    y0 y1 x1 x2 x3 x4 x5 x6 x7 H.
  unfold reac_identity_ingest_post. exists y0, y1, x1, x2, x3, x4, x5, x6, x7, m.
  unfold ingest_ret. rewrite H.
  split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact (fun H0 => H0)|].
  split; [intros _; reflexivity|]. intros H'. discriminate H'.
Qed.

Section Arms.
Variables (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (id ad p len : Z) (idb pb : list byte).
Hypothesis Hid : 0 < id < 2^64.
Hypothesis Had : 0 <= ad < 65536.
Hypothesis Hp : 0 <= p < 2^64.
Hypothesis Hlen : 0 <= len < 2^64.
Hypothesis Hpl : length pb = Z.to_nat len.
Hypothesis HNR : ingest_refused id p len = false.
Hypothesis HS3 : id <> 0 -> id mod 2 = 0 /\ rw_cells rsegs m0 id [CB 38 idb].
Hypothesis HS4 : 0 < len -> p <> 0 -> bytes_at rsegs m0 p pb.
Hypothesis HD : id <> 0 -> 0 < len -> p <> 0 -> p + len <= id \/ id + 38 <= p.

Local Abbreviation Post := (reac_identity_ingest_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                          F fc m0 id ad p len idb pb).

Lemma p_nz : 0 < len -> p <> 0.
Proof.
  intros H E. unfold ingest_refused in HNR. rewrite E in HNR.
  replace (id =? 0) with false in HNR by (symmetry; apply Z.eqb_neq; lia).
  replace (len =? 0) with false in HNR by (symmetry; apply Z.eqb_neq; lia).
  discriminate HNR.
Qed.

Lemma rw0 : rw_cells rsegs m0 id [CB 38 idb].
Proof. apply HS3. lia. Qed.

Lemma iv0 : 0 < len -> ivs rsegs m0 m0 id idb p pb.
Proof.
  intros H. pose proof (p_nz H) as Hp0. apply ivs_start; [exact rw0 | exact (HS4 H Hp0) |].
  rewrite Hpl, Z2Nat.id by lia. exact (HD ltac:(lia) H Hp0).
Qed.

Lemma fin0 : forall (y0 y1 x1 x2 x3 x4 x5 x6 x7 : word),
  ING idb ad pb = (0, idb) ->
  Post (MS (mkR ra sp gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 0) x1 x2 x3 x4 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (ret_pc ra) fc None m0 (seg_rom rsegs)).
Proof.
  intros y0 y1 x1 x2 x3 x4 x5 x6 x7 E.
  unfold reac_identity_ingest_post. exists y0, y1, x1, x2, x3, x4, x5, x6, x7, m0.
  unfold ingest_ret. rewrite HNR, E.
  split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact (fun H0 => H0)|].
  split; [intros H; discriminate H|]. intros _. exact rw0.
Qed.

Lemma fin : forall (y0 y1 x1 x2 x3 x4 x5 x6 x7 : word) m r idb',
  ivs rsegs m0 m id idb' p pb -> ING idb ad pb = (r, idb') ->
  Post (MS (mkR ra sp gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 r) x1 x2 x3 x4 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (ret_pc ra) fc None m (seg_rom rsegs)).
Proof.
  intros y0 y1 x1 x2 x3 x4 x5 x6 x7 m r idb' IV E.
  pose proof (ivs_post rsegs m0 m id idb' p pb IV) as (MU & WM & MI').
  unfold reac_identity_ingest_post. exists y0, y1, x1, x2, x3, x4, x5, x6, x7, m.
  unfold ingest_ret. rewrite HNR, E.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  split; [intros H; discriminate H|]. intros _. exact (ivs_rw_cells rsegs m0 m id idb' p pb IV).
Qed.

Lemma exit_ok : forall (y0 y1 x2 x3 x4 x5 x6 x7 : word) m idb' k,
  0 <= k -> k < 38 -> ivs rsegs m0 m id idb' p pb ->
  ING idb ad pb = (1, upd idb' (Z.to_nat k) [zb 1]) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 id) (Z_to_bv 64 k) x2 x3 x4 x5 x6 x7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x157b0) fc None m (seg_rom rsegs)).
Proof.
  intros y0 y1 x2 x3 x4 x5 x6 x7 m idb' k Hk0 Hk IV E.
  ivs_sok IV k 1%nat.
  step. step. step.
  ivs_after IV k.
  step. step.
  apply evt_done. eapply fin; [exact IV|].
  rewrite E, le1_lit by lia. reflexivity.
Qed.

Lemma fw_loop : ad = 0 -> 4 <= len -> forall n i (a4w x5 x6 x7 y0 y1 : word),
  a4w = Z_to_bv 64 (p + Z.of_nat i) ->
  (i + n = 4)%nat -> (0 < n)%nat -> (forall j, (j < i)%nat -> bz (nthb pb j) <= 9) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 id) (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 p)
             (Z_to_bv 64 9) a4w x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15658) fc None m0 (seg_rom rsegs)).
Proof.
  intros Ha H4 n. induction n as [|n IH]; intros i a4w x5 x6 x7 y0 y1 Ea Hin Hn Hd; [lia|]. subst a4w.
  pose proof (iv0 ltac:(lia)) as IV.
  assert (L4 : (4 <= length pb)%nat) by lia.
  pose proof (ivs_rdb rsegs m0 m0 id idb p pb i IV ltac:(lia)) as RD.
  pose proof (byte_range (nth i pb (Z_to_bv 8 0))) as BR.
  step. step.
  rewrite ii_ltu_zxb by lia.
  destruct (Z.ltb_spec 9 (bv_unsigned (nth i pb (Z_to_bv 8 0)))) as [Hb|Hb]; cbv iota.
  - step. step. step. step.
    apply evt_done. eapply fin0. rewrite Ha. apply (fw_bad idb pb i L4); [lia|]. exact Hb.
  - step. step. step.
    replace (Z.of_nat (S n) + -1) with (Z.of_nat n) by lia.
    rewrite ii_eqb_lit by lia.
    destruct n as [|n].
    + replace (Z.of_nat 0 =? 0) with true by reflexivity. cbn [negb].
      replace i with 3%nat in * by lia.
      pose proof (ivs_rdb rsegs m0 m0 id idb p pb 0 IV ltac:(lia)) as R0.
      pose proof (ivs_rdb rsegs m0 m0 id idb p pb 1 IV ltac:(lia)) as R1.
      pose proof (ivs_rdb rsegs m0 m0 id idb p pb 2 IV ltac:(lia)) as R2.
      ivs_sok IV 0 2%nat.
      do 14 step.
      ivs_after IV 0.
      step. step.
      eapply exit_ok; [lia | lia | exact IV |].
      assert (D0 : bz (nthb pb 0) <= 9) by (apply Hd; lia).
      assert (D1 : bz (nthb pb 1) <= 9) by (apply Hd; lia).
      assert (D2 : bz (nthb pb 2) <= 9) by (apply Hd; lia).
      assert (D3 : bz (nthb pb 3) <= 9) by exact Hb.
      rewrite Ha, (ING_fw idb pb L4).
      rewrite (proj2 (Z.leb_le _ _) D0), (proj2 (Z.leb_le _ _) D1), (proj2 (Z.leb_le _ _) D2),
        (proj2 (Z.leb_le _ _) D3).
      cbn [andb]. rewrite !zxb_u.
      unfold bz, nthb, zb in *.
      pose proof (byte_range (nth 0 pb (Z_to_bv 8 0))). pose proof (byte_range (nth 1 pb (Z_to_bv 8 0))).
      pose proof (byte_range (nth 2 pb (Z_to_bv 8 0))).
      rewrite le2_le16 by lia.
      match goal with
      | |- (_, upd (upd _ _ (le16 ?a)) _ _) = (_, upd (upd _ _ (le16 ?b)) _ _) =>
          replace a with b by (unfold fw_value, bz, nthb, zb; lia)
      end.
      reflexivity.
    + cbn [negb]. replace (Z.of_nat (S n) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      apply (IH (S i)); [f_equal; lia | lia | lia |].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|Hji]; [unfold bz, nthb, zb; lia | apply Hd; lia].
Qed.

Lemma fw_arm : ad = 0 -> forall (x1 x4 x5 x6 x7 y0 y1 : word),
  evt rsegs Post
    (MS (mkR ra sp gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 id) x1 (Z_to_bv 64 p) (Z_to_bv 64 len) x4 x5 x6 x7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15648) fc None m0 (seg_rom rsegs)).
Proof.
  intros Ha x1 x4 x5 x6 x7 y0 y1.
  step. step.
  rewrite ii_ltu_lit by lia.
  destruct (Z.ltb_spec len 4) as [H4|H4]; cbv iota.
  - step. step. step. step.
    apply evt_done. eapply fin0. rewrite Ha. apply ING_fw_short. lia.
  - step. step.
    change (Z_to_bv 64 4) with (Z_to_bv 64 (Z.of_nat 4)).
    apply (fw_loop Ha H4 4 0); [f_equal; lia | lia | lia | intros j Hj; lia].
Qed.

Lemma ver_arm : ad = 1536 -> forall (x1 x4 x5 x6 x7 y0 y1 : word),
  evt rsegs Post
    (MS (mkR ra sp gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 id) x1 (Z_to_bv 64 p) (Z_to_bv 64 len) x4 x5 x6 x7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x156ac) fc None m0 (seg_rom rsegs)).
Proof.
  intros Ha x1 x4 x5 x6 x7 y0 y1.
  step. step.
  rewrite ii_ltu_lit by lia.
  destruct (Z.ltb_spec len 8) as [H8|H8]; cbv iota.
  - step. step. step. step.
    apply evt_done. eapply fin0. rewrite Ha. apply ING_ver_short. lia.
  - pose proof (iv0 ltac:(lia)) as IV.
    assert (L8 : (8 <= length pb)%nat) by lia.
    pose proof (ivs_rdb rsegs m0 m0 id idb p pb 0 IV ltac:(lia)) as R0.
    pose proof (ivs_rdb rsegs m0 m0 id idb p pb 1 IV ltac:(lia)) as R1.
    pose proof (ivs_rdb rsegs m0 m0 id idb p pb 2 IV ltac:(lia)) as R2.
    pose proof (ivs_rdb rsegs m0 m0 id idb p pb 3 IV ltac:(lia)) as R3.
    pose proof (ivs_rdb rsegs m0 m0 id idb p pb 4 IV ltac:(lia)) as R4.
    pose proof (ivs_rdb rsegs m0 m0 id idb p pb 5 IV ltac:(lia)) as R5.
    pose proof (ivs_rdb rsegs m0 m0 id idb p pb 6 IV ltac:(lia)) as R6.
    pose proof (ivs_rdb rsegs m0 m0 id idb p pb 7 IV ltac:(lia)) as R7.
    do 16 step.
    ivs_sok IV 28 2%nat. step. ivs_after IV 28.
    ivs_sok IV 30 2%nat. step. ivs_after IV 30.
    ivs_sok IV 32 2%nat. step. ivs_after IV 32.
    ivs_sok IV 34 2%nat. step. ivs_after IV 34.
    clear R0 R1 R2 R3 R4 R5 R6 R7.
    pose proof (ivs_rdb rsegs _ _ id _ p pb 2 IV ltac:(lia)) as R2.
    pose proof (ivs_rdb rsegs _ _ id _ p pb 3 IV ltac:(lia)) as R3.
    do 4 step.
    ivs_sok IV 22 2%nat. step. ivs_after IV 22.
    clear R2 R3.
    pose proof (ivs_rdb rsegs _ _ id _ p pb 4 IV ltac:(lia)) as R4.
    pose proof (ivs_rdb rsegs _ _ id _ p pb 5 IV ltac:(lia)) as R5.
    do 4 step.
    ivs_sok IV 24 2%nat. step. ivs_after IV 24.
    clear R4 R5.
    pose proof (ivs_rdb rsegs _ _ id _ p pb 6 IV ltac:(lia)) as R6.
    pose proof (ivs_rdb rsegs _ _ id _ p pb 7 IV ltac:(lia)) as R7.
    do 4 step.
    ivs_sok IV 26 2%nat. step. ivs_after IV 26.
    step. step.
    eapply exit_ok; [lia | lia | exact IV |].
    rewrite Ha, (ING_ver idb pb L8), !le2_orshl.
    assert (LI : length idb = 38%nat) by (destruct rw0 as [[[Hl _] _] _]; exact Hl).
    rewrite (ver_eq idb) by exact LI. reflexivity.
Qed.

Local Abbreviation NN := (Nat.min (length pb - 1) 16).

Lemma name_loop : ad = 4096 -> 2 <= len -> forall k i m (a2w a3w a4w a5w a6w x7 y0 y1 : word),
  a2w = Z_to_bv 64 (p + 1 + Z.of_nat i) -> a3w = Z_to_bv 64 (Z.of_nat NN) -> a4w = Z_to_bv 64 (- Z.of_nat i) ->
  a5w = Z_to_bv 64 (- Z.of_nat NN) -> a6w = Z_to_bv 64 (id + 3 + Z.of_nat i) ->
  (i + k = NN)%nat -> (0 < k)%nat -> (forall j, (j < i)%nat -> bz (nthb pb (1 + j)) <> 0) ->
  ivs rsegs m0 m id (upd idb 3 (firstn i (skipn 1 pb))) p pb ->
  evt rsegs Post
    (MS (mkR ra sp gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 id) (Z_to_bv 64 (id + 3)) a2w a3w a4w a5w a6w x7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1577c) fc None m (seg_rom rsegs)).
Proof.
  intros Ha H2 k. induction k as [|k IH];
    intros i m a2w a3w a4w a5w a6w x7 y0 y1 E2 E3 E4 E5 E6 Hik Hk Hnz IV; [lia|].
  subst a2w a3w a4w a5w a6w.
  assert (LI : length idb = 38%nat) by (destruct rw0 as [[[Hl _] _] _]; exact Hl).
  pose proof (ivs_rdb rsegs m0 m id _ p pb (1 + i) IV ltac:(lia)) as RD.
  step. step.
  rewrite ii_eqb_zxb0.
  destruct (Z.eqb_spec (bv_unsigned (nth (1 + i) pb (Z_to_bv 8 0))) 0) as [Hz|Hz]; cbv iota.
  - step. rewrite ii_eqb_neg0 by lia.
    destruct (Z.eqb_spec (Z.of_nat i) 0) as [I0|I0]; cbv iota.
    + step. step.
      apply evt_done. eapply fin; [exact IV|].
      assert (i = 0%nat) by lia. subst i.
      rewrite Ha, ING_name_zero.
      * cbn [firstn]. rewrite upd_nil by lia. reflexivity.
      * right. apply name_len_hit; [lia | lia | exact Hz | intros j Hj; lia].
    + step. rewrite ii_neg. replace (- - Z.of_nat i) with (Z.of_nat i) by lia.
      ivs_sok IV (3 + Z.of_nat i) 1%nat.
      step. step.
      ivs_after IV (3 + Z.of_nat i).
      step.
      eapply exit_ok; [lia | lia | exact IV |].
      assert (NL : name_len pb = i) by (apply name_len_hit; [lia | lia | exact Hz | exact Hnz]).
      rewrite Ha, (ING_name idb pb) by lia. rewrite NL, le1_lit by lia.
      rewrite (upd_cat idb (firstn i (skipn 1 pb)) [zb 0] 3 (Z.to_nat (3 + Z.of_nat i)))
        by (rewrite ?length_firstn, ?length_skipn; lia).
      reflexivity.
  - ivs_sok IV (3 + Z.of_nat i) 1%nat.
    step.
    ivs_after IV (3 + Z.of_nat i).
    rewrite le1_zxb in IV.
    rewrite (upd_cat idb (firstn i (skipn 1 pb)) [nth (1 + i) pb (Z_to_bv 8 0)] 3 (Z.to_nat (3 + Z.of_nat i)))
      in IV by (rewrite ?length_firstn, ?length_skipn; lia).
    replace (firstn i (skipn 1 pb) ++ [nth (1 + i) pb (Z_to_bv 8 0)]) with (firstn (S i) (skipn 1 pb)) in IV
      by (rewrite firstn_snoc by (rewrite length_skipn; lia); rewrite nthb_skipn1; reflexivity).
    assert (Hnz' : forall j, (j < S i)%nat -> bz (nthb pb (1 + j)) <> 0).
    { intros j Hj. destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hz | apply Hnz; lia]. }
    step. step. step. step.
    replace (- Z.of_nat i + -1) with (- Z.of_nat (S i)) by lia.
    rewrite ii_eqb_neg by lia.
    destruct k as [|k].
    + replace (Z.of_nat NN =? Z.of_nat (S i)) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
      ivs_sok IV (3 + Z.of_nat NN) 1%nat.
      step. step. step.
      ivs_after IV (3 + Z.of_nat NN).
      step.
      eapply exit_ok; [lia | lia | exact IV |].
      assert (NL : name_len pb = NN) by (apply name_len_full; [lia | intros j Hj; apply Hnz'; lia]).
      rewrite Ha, (ING_name idb pb) by lia. rewrite NL, le1_lit by lia.
      replace (S i) with NN in * by lia.
      rewrite (upd_cat idb (firstn NN (skipn 1 pb)) [zb 0] 3 (Z.to_nat (3 + Z.of_nat NN)))
        by (rewrite ?length_firstn, ?length_skipn; lia).
      reflexivity.
    + replace (Z.of_nat NN =? Z.of_nat (S i)) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      apply (IH (S i)); [f_equal; lia | reflexivity | reflexivity | reflexivity | f_equal; lia | lia | lia
                         | exact Hnz' | exact IV].
Qed.

Lemma name_pre : ad = 4096 -> 2 <= len -> forall (a3w x1 x4 x5 x6 x7 y0 y1 : word),
  a3w = Z_to_bv 64 (Z.of_nat NN) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 id) x1 (Z_to_bv 64 p) a3w x4 x5 x6 x7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15768) fc None m0 (seg_rom rsegs)).
Proof.
  intros Ha H2 a3w x1 x4 x5 x6 x7 y0 y1 E3. subst a3w.
  assert (LI : length idb = 38%nat) by (destruct rw0 as [[[Hl _] _] _]; exact Hl).
  do 5 step.
  apply (name_loop Ha H2 NN 0); [f_equal; lia | reflexivity | reflexivity | apply ii_neg | f_equal; lia | lia | lia
                                 | intros j Hj; lia |].
  cbn [firstn]. rewrite upd_nil by lia. exact (iv0 ltac:(lia)).
Qed.

Lemma name_arm : ad = 4096 -> forall (x1 x4 x5 x6 x7 y0 y1 : word),
  evt rsegs Post
    (MS (mkR ra sp gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 id) x1 (Z_to_bv 64 p) (Z_to_bv 64 len) x4 x5 x6 x7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15748) fc None m0 (seg_rom rsegs)).
Proof.
  intros Ha x1 x4 x5 x6 x7 y0 y1.
  step. step.
  rewrite ii_ltu_lit by lia.
  destruct (Z.ltb_spec len 2) as [H2|H2]; cbn [negb].
  - step. step. step. step.
    apply evt_done. eapply fin0. rewrite Ha. apply ING_name_zero. left. lia.
  - step. step. step.
    rewrite ii_ltu_lit by lia.
    destruct (Z.ltb_spec (len + -1) 16) as [H16|H16]; cbv iota.
    + apply (name_pre Ha H2). f_equal. lia.
    + step. apply (name_pre Ha H2). f_equal. lia.
Qed.

Lemma dispatch : forall (x4 x5 x6 x7 y0 y1 : word),
  evt rsegs Post
    (MS (mkR ra sp gp tp y0 y1 t2 s0 s1 (Z_to_bv 64 id) (Z_to_bv 64 ad) (Z_to_bv 64 p) (Z_to_bv 64 len) x4 x5 x6 x7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15634) fc None m0 (seg_rom rsegs)).
Proof.
  intros x4 x5 x6 x7 y0 y1.
  step. step.
  rewrite ii_eqb_lit by lia.
  destruct (Z.eqb_spec ad 4096) as [A1|A1]; cbv iota; [exact (name_arm A1 _ _ _ _ _ _ _)|].
  step. step.
  rewrite ii_eqb_lit by lia.
  destruct (Z.eqb_spec ad 1536) as [A2|A2]; cbv iota; [exact (ver_arm A2 _ _ _ _ _ _ _)|].
  step.
  rewrite ii_eqb_lit by lia.
  destruct (Z.eqb_spec ad 0) as [A3|A3]; cbn [negb]; [exact (fw_arm A3 _ _ _ _ _ _ _)|].
  step. step. step. step.
  apply evt_done. eapply fin0. apply ING_other; assumption.
Qed.
End Arms.

Theorem reac_identity_ingest_holds : reac_identity_ingest_contract.
Proof.
  unfold reac_identity_ingest_contract, REAC_IDENTITY_INGEST.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    id ad p len idb pb -> -> -> -> Hid Had Hp Hlen HS3 Hpl HS4 HD.
  step. step.
  rewrite ii_eqb_lit by lia.
  destruct (Z.eqb_spec id 0) as [I0|I0]; cbv iota.
  - step. step. apply evt_done. apply fin_refused.
    unfold ingest_refused. rewrite I0. reflexivity.
  - assert (Hid' : 0 < id < 2^64) by lia.
    step.
    rewrite ii_eqb_lit by lia.
    destruct (Z.eqb_spec p 0) as [P0|P0]; cbn [negb].
    + step.
      rewrite ii_eqb_lit by lia.
      destruct (Z.eqb_spec len 0) as [L0|L0]; cbn [negb].
      * assert (HNR : ingest_refused id p len = false).
        { unfold ingest_refused. rewrite (proj2 (Z.eqb_neq id 0) I0), L0. reflexivity. }
        eapply dispatch; eassumption.
      * step. step. apply evt_done. apply fin_refused.
        unfold ingest_refused. rewrite P0, (proj2 (Z.eqb_neq len 0) L0). apply Bool.orb_true_r.
    + assert (HNR : ingest_refused id p len = false).
      { unfold ingest_refused. rewrite (proj2 (Z.eqb_neq id 0) I0), (proj2 (Z.eqb_neq p 0) P0).
        rewrite Bool.andb_false_r. reflexivity. }
      eapply dispatch; eassumption.
Qed.

Theorem reac_identity_ingest_id_ok_kept_holds : reac_identity_ingest_id_ok_kept.
Proof. intros idb pb ad L OK. exact (ING_id_ok idb ad pb L OK). Qed.
