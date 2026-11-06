(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec SeqExec Hoare StoreOk MemSplit MmapSim AllocSim ShapeAlg AgentLib StepTac MuslStrlen.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree MallocOps.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Abbreviation u := bv_unsigned.

Lemma u_wlit : forall z, 0 <= z < 2^64 -> u (wlit z) = z.
Proof. intros z Hz. unfold wlit. apply u64_lit. exact Hz. Qed.

Lemma is0_true : forall x : word, is0 x = true <-> u x = 0.
Proof.
  intros x. unfold is0, c_eq, w0. rewrite bv_eqb_eq. split.
  - intros ->. reflexivity.
  - intros H. apply bv_eq. rewrite H. reflexivity.
Qed.

Lemma is0_false : forall x : word, is0 x = false <-> u x <> 0.
Proof.
  intros x. destruct (is0 x) eqn:E.
  - apply is0_true in E. split; [discriminate | intros H; exfalso; exact (H E)].
  - split; [| reflexivity]. intros _ H. apply (proj2 (is0_true x)) in H. congruence.
Qed.

Lemma u_v_sub : forall x y : word, u y <= u x -> u (v_sub x y) = u x - u y.
Proof. intros x y H. unfold v_sub. pose proof (u64_range x). pose proof (u64_range y). apply u64_lit. lia. Qed.

Lemma u_v_add : forall x y : word, u x + u y < 2^64 -> u (v_add x y) = u x + u y.
Proof. intros x y H. unfold v_add. pose proof (u64_range x). pose proof (u64_range y). apply u64_lit. lia. Qed.

Lemma u_v_addi : forall (x : word) k, 0 <= u x + k < 2^64 -> u (v_addi x k) = u x + k.
Proof. intros x k H. unfold v_addi. apply u64_lit. exact H. Qed.

Lemma u_at : forall (x : word) k, 0 <= u x + k < 2^64 -> u (at_ x k) = u x + k.
Proof. intros x k H. unfold at_. apply u64_lit. exact H. Qed.

Lemma u_v_srli : forall (x : word) k, 0 <= k -> u (v_srli x k) = u x / 2^k.
Proof.
  intros x k Hk. unfold v_srli. pose proof (u64_range x). rewrite Z.shiftr_div_pow2 by exact Hk.
  assert (0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  apply u64_lit. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma lor_bound : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros a b n Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [-> | Ha0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [-> | Hb0]; [rewrite Z.lor_0_r; lia|].
  assert (Hn : 0 <= n) by (destruct (Z.le_gt_cases 0 n); [lia | rewrite Z.pow_neg_r in Ha; lia]).
  assert (Hpos : 0 < Z.lor a b).
  { pose proof (Z.lor_nonneg a b). destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia].
    apply Z.lor_eq_0_iff in E. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n Hpos)).
  rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; [apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))) | apply (proj1 (Z.log2_lt_pow2 b n ltac:(lia)))]; lia.
Qed.

Lemma u_v_or : forall x y : word, u (v_or x y) = Z.lor (u x) (u y).
Proof.
  intros x y. unfold v_or. pose proof (u64_range x). pose proof (u64_range y).
  apply u64_lit. apply lor_bound; lia.
Qed.

Lemma u_v_or_0 : forall x y : word, u (v_or x y) = 0 <-> u x = 0 /\ u y = 0.
Proof.
  intros x y. rewrite u_v_or. split.
  - intros Hl. apply Z.lor_eq_0_iff in Hl. exact Hl.
  - intros [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_pagemask : forall x, 0 <= x < 2^64 -> Z.land x (2^64 - 4096) = x - x mod 4096.
Proof.
  intros x Hx.
  replace (2^64 - 4096) with (Z.shiftl (Z.ones 52) 12) by reflexivity.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec.
  replace (x - x mod 4096) with (x / 2^12 * 2^12)
    by (change 4096 with (2^12); pose proof (Z.div_mod x (2^12) ltac:(lia)); lia).
  destruct (Z.lt_ge_cases i 12).
  - rewrite Z.shiftl_spec_low by lia. rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  - rewrite Z.shiftl_spec_high by lia. rewrite Z.mul_pow2_bits by lia. rewrite Z.div_pow2_bits by lia.
    replace (i - 12 + 12) with i by lia.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.testbit_ones_nonneg by lia. replace (i - 12 <? 52) with true by (symmetry; apply Z.ltb_lt; lia).
      apply andb_true_r.
    + rewrite Z.testbit_ones_nonneg by lia. replace (i - 12 <? 52) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite andb_false_r. symmetry. apply Z.testbit_false; [lia|].
      rewrite Z.div_small; [reflexivity|]. split; [lia|]. apply Z.lt_le_trans with (2^64); [lia|].
      apply Z.pow_le_mono_r; lia.
Qed.

Lemma u_and_pagemask : forall x : word, u (v_and x PAGEMASK) = u x - u x mod 4096.
Proof.
  intros x. unfold v_and, PAGEMASK. pose proof (u64_range x) as Hx.
  rewrite (u64_lit (2^64 - 4096)) by lia. rewrite land_pagemask by exact Hx.
  apply u64_lit. pose proof (Z.mod_pos_bound (u x) 4096 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma u_low12 : forall x : word, u (v_srli (v_slli x 52) 52) = u x mod 4096.
Proof.
  intros x. pose proof (u64_range x) as Hx.
  unfold v_srli, v_slli. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite (Z_to_bv_unsigned 64 (u x * 2^52)). unfold bv_wrap.
  change (bv_modulus 64) with (2^12 * 2^52).
  rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
  change 4096 with (2^12). apply u64_lit. pose proof (Z.mod_pos_bound (u x) (2^12) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma le_val_u8 : forall bs, length bs = 8%nat -> u (le_val bs) = bytes_le_to_Z bs.
Proof. intros bs Hl. unfold le_val. apply u64_lit. apply bytes_le_to_Z_range. exact Hl. Qed.

Lemma bytes_zero_nth : forall bs k, bytes_le_to_Z bs = 0 -> (k < length bs)%nat ->
  nth k bs (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  intros bs k Hz Hk. apply bv_eq. rewrite <- (zb_of_bytes bs k Hk). rewrite Hz.
  unfold HZ.zb. rewrite Z.div_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithLayout.
Context {ML : MallocLayout}.

(* [comment removed for export] *)
Record blk (s : mstate) (lo hi : Z) : Prop := BLK {
  blk_bounds : 0 <= lo /\ lo <= hi /\ hi < 2^64;
  blk_win : hi <= ms_lo s \/ ms_hi s <= lo;
  blk_zonE : hi <= IMG_LO \/ IMG_HI <= lo;
  blk_def : forall a : word, lo <= u a < hi -> ms_mem s a <> None
}.

Lemma blk_acc_ok : forall s lo hi (a : word) n,
  blk s lo hi -> 0 <= n -> lo <= u a -> u a + n <= hi -> acc_ok s a n = true.
Proof.
  intros s lo hi a n [Hb Hw _ _] Hn H1 H2. unfold acc_ok.
  destruct Hw as [Hw | Hw].
  - rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  - rewrite orb_true_iff. right. rewrite andb_true_iff, !Z.leb_le. lia.
Qed.

Lemma blk_st_zone : forall s lo hi (a : word) n,
  blk s lo hi -> 0 <= n -> lo <= u a -> u a + n <= hi -> st_zone a n = true.
Proof.
  intros s lo hi a n [Hb _ Hz _] Hn H1 H2. unfold st_zone. cbn zeta.
  destruct Hz as [Hz | Hz].
  - rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  - rewrite (proj2 (Z.leb_le IMG_HI (u a))) by lia. rewrite orb_true_r. reflexivity.
Qed.

Lemma blk_store_ok : forall s lo hi (a : word) (n : nat),
  blk s lo hi -> lo <= u a -> u a + Z.of_nat n <= hi -> store_ok ml_segs (ms_mem s) a n = true.
Proof.
  intros s lo hi a n B H1 H2. destruct B as [Hb _ _ Hd].
  apply store_ok_of_all; [lia|]. intros x Hx. unfold wview.
  destruct (ms_mem s x) as [b|] eqn:E; [discriminate|]. exfalso. apply (Hd x); [lia | exact E].
Qed.

Lemma blk_rdn : forall s lo hi (a : word) (n : nat),
  blk s lo hi -> lo <= u a -> u a + Z.of_nat n <= hi ->
  exists bs, rdn ml_segs (ms_mem s) a n = Some bs /\ length bs = n /\
             forall k, (k < n)%nat -> ms_mem s (at_ a (Z.of_nat k)) = Some (nth k bs (Z_to_bv 8 0)).
Proof.
  intros s lo hi a n B H1 H2. destruct B as [Hb _ _ Hd].
  revert a H1 H2. induction n as [|n IH]; intros a H1 H2.
  - exists []. split; [reflexivity | split; [reflexivity | intros k Hk; lia]].
  - rewrite Nat2Z.inj_succ in H2. cbn [rdn]. destruct (ms_mem s a) as [b|] eqn:E.
    2: { exfalso. apply (Hd a); [lia | exact E]. }
    assert (Ha0 : at_ a (Z.of_nat 0) = a) by (apply bv_eq; rewrite u_at by lia; lia).
    destruct n as [|n'].
    + exists [b]. split; [reflexivity | split; [reflexivity|]].
      intros k Hk. destruct k; [|lia]. rewrite Ha0. exact E.
    + rewrite Nat2Z.inj_succ in H2.
      assert (Hu1 : u (a + 1) = u a + 1) by (apply u_add1; lia).
      assert (HH1 : lo <= u (a + 1)%bv) by (rewrite Hu1; lia).
      assert (HH2 : u (a + 1)%bv + Z.of_nat (S n') <= hi) by (rewrite Hu1, Nat2Z.inj_succ; lia).
      destruct (IH (a + 1)%bv HH1 HH2) as (bs & Hr & Hl & Hn).
      rewrite Hr. exists (b :: bs). split; [reflexivity | split; [cbn; lia|]].
      intros k Hk. destruct k as [|k].
      * rewrite Ha0. exact E.
      * change (nth (S k) (b :: bs) (Z_to_bv 8 0)) with (nth k bs (Z_to_bv 8 0)).
        rewrite <- (Hn k) by lia. f_equal. apply bv_eq. rewrite !u_at by (try rewrite Hu1; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma blk_upd : forall s lo hi m h,
  blk s lo hi -> (forall a : word, lo <= u a < hi -> m a <> None) -> blk (upd s m h) lo hi.
Proof. intros s lo hi m h [B1 B2 B3 B4] Hm. constructor; cbn; auto. Qed.

Lemma blk_sub : forall s lo hi lo' hi', blk s lo hi -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> blk s lo' hi'.
Proof.
  intros s lo hi lo' hi' [B1 B2 B3 B4] H1 H2 H3. constructor; try lia.
  intros a Ha. apply B4. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma length_zero_bytes : forall n, length (zero_bytes n) = Z.to_nat (u n).
Proof. intros n. unfold zero_bytes. apply repeat_length. Qed.

Lemma m_memset0_nil : forall d n s, u n = 0 -> m_memset0 d n s = TRet d s.
Proof.
  intros d n s Hn. unfold m_memset0, mbind, mret. rewrite (proj2 (is0_true n) Hn). reflexivity.
Qed.

Lemma m_memset0_eq : forall d n s lo hi,
  blk s lo hi -> lo <= u d -> u d + u n <= hi ->
  m_memset0 d n s = TRet d (if is0 n then s else upd s (wbytes (ms_mem s) d (zero_bytes n)) (ms_vm s)).
Proof.
  intros d n s lo hi B H1 H2. unfold m_memset0, mbind, mret.
  destruct (is0 n) eqn:E; [reflexivity|].
  unfold m_stbytes. rewrite length_zero_bytes.
  pose proof (u64_range n).
  rewrite (blk_acc_ok s lo hi d) by (try exact B; lia).
  rewrite (blk_st_zone s lo hi d) by (try exact B; lia).
  rewrite (blk_store_ok s lo hi d) by (try exact B; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wbytes_zero_in : forall m (d n : word) (x : word),
  u d + u n <= 2^64 -> u d <= u x < u d + u n ->
  wbytes m d (zero_bytes n) x = Some (Z_to_bv 8 0).
Proof.
  intros m d n x Hnw Hx. unfold zero_bytes. pose proof (u64_range n). pose proof (u64_range d).
  rewrite wbytes_inside by (rewrite repeat_length; lia).
  f_equal. apply nth_repeat.
Qed.

Lemma wbytes_zero_out : forall m (d n : word) (x : word),
  u d + u n <= 2^64 -> ~ (u d <= u x < u d + u n) ->
  wbytes m d (zero_bytes n) x = m x.
Proof.
  intros m d n x Hnw Hx. unfold zero_bytes. pose proof (u64_range n). pose proof (u64_range d). pose proof (u64_range x).
  apply wbytes_outside; rewrite repeat_length; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zero_at (m : word -> option byte) (lo hi : Z) : Prop :=
  forall a : word, lo <= u a < hi -> m a = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Lemma m_zscan_eq : forall fuel (a1 a0 a2 : word) s lo hi,
  blk s lo hi -> lo <= u a1 -> u a1 + 4096 <= hi ->
  0 < u a2 <= 4096 -> u a2 mod 16 = 0 -> u a0 = u a1 + u a2 ->
  u a2 <= 16 * Z.of_nat fuel ->
  zero_at (ms_mem s) (u a0) (u a1 + 4096) ->
  exists d len, m_zscan fuel a1 a0 a2 s = TRet (d, len) s /\
    u d = u a1 /\ 0 <= u len <= u a2 /\ u len mod 16 = 0 /\
    zero_at (ms_mem s) (u a1 + u len) (u a1 + 4096).
Proof.
  induction fuel as [|fuel IH]; intros a1 a0 a2 s lo hi B Hlo Hhi Ha2 Hm16 Ha0 Hf Hz; [lia|].
  cbn [m_zscan]. unfold mbind, m_ld, m_rd, mbind, mret, mcrash. change (Z.of_nat 8) with 8.
  pose proof (u64_range a1). pose proof (u64_range a0).
  assert (Hu16 : u (at_ a0 (-16)) = u a0 - 16) by (rewrite u_at; lia).
  assert (Hu8 : u (at_ a0 (-8)) = u a0 - 8) by (rewrite u_at; lia).
  rewrite (blk_acc_ok s lo hi (at_ a0 (-16)) 8 B) by lia.
  destruct (blk_rdn s lo hi (at_ a0 (-16)) 8 B ltac:(lia) ltac:(cbn; lia)) as (bs1 & -> & Hl1 & Hn1).
  cbn [tbind].
  rewrite (blk_acc_ok s lo hi (at_ a0 (-8)) 8 B) by lia.
  destruct (blk_rdn s lo hi (at_ a0 (-8)) 8 B ltac:(lia) ltac:(cbn; lia)) as (bs2 & -> & Hl2 & Hn2).
  cbn [tbind].
  destruct (is0 (v_or (le_val bs1) (le_val bs2))) eqn:E; cbn [negb].
  - (* [comment removed for export] *)
    apply is0_true in E. apply u_v_or_0 in E. destruct E as [E1 E2].
    rewrite le_val_u8 in E1 by exact Hl1. rewrite le_val_u8 in E2 by exact Hl2.
    assert (Hz' : zero_at (ms_mem s) (u a0 - 16) (u a1 + 4096)).
    { intros x Hx. destruct (Z.lt_ge_cases (u x) (u a0)) as [Hlt | Hge]; [| apply Hz; lia].
      destruct (Z.lt_ge_cases (u x) (u a0 - 8)) as [Hlt8 | Hge8].
      - specialize (Hn1 (Z.to_nat (u x - (u a0 - 16))) ltac:(lia)).
        replace (at_ (at_ a0 (-16)) (Z.of_nat (Z.to_nat (u x - (u a0 - 16))))) with x in Hn1
          by (apply bv_eq; rewrite u_at by (rewrite Hu16; lia); rewrite Hu16; lia).
        rewrite Hn1. f_equal. apply bytes_zero_nth; [exact E1 | lia].
      - specialize (Hn2 (Z.to_nat (u x - (u a0 - 8))) ltac:(lia)).
        replace (at_ (at_ a0 (-8)) (Z.of_nat (Z.to_nat (u x - (u a0 - 8))))) with x in Hn2
          by (apply bv_eq; rewrite u_at by (rewrite Hu8; lia); rewrite Hu8; lia).
        rewrite Hn2. f_equal. apply bytes_zero_nth; [exact E2 | lia]. }
    assert (Hu2' : u (v_addi a2 (-16)) = u a2 - 16) by (rewrite u_v_addi; lia).
    assert (Hu0' : u (v_addi a0 (-16)) = u a0 - 16) by (rewrite u_v_addi; lia).
    destruct (is0 (v_addi a2 (-16))) eqn:E2'; cbn [negb].
    + (* [comment removed for export] *)
      apply is0_true in E2'.
      exists (v_sub a1 (v_addi a2 (-16))), (v_addi a2 (-16)). split; [reflexivity|].
      rewrite u_v_sub by (rewrite Hu2'; lia). rewrite E2'. repeat split; try lia.
      intros x Hx. apply Hz'. lia.
    + apply is0_false in E2'.
      assert (P1 : 0 < u (v_addi a2 (-16)) <= 4096) by (rewrite Hu2'; lia).
      assert (P2 : u (v_addi a2 (-16)) mod 16 = 0) by (rewrite Hu2', Zminus_mod, Hm16; reflexivity).
      assert (P3 : u (v_addi a0 (-16)) = u a1 + u (v_addi a2 (-16))) by (rewrite Hu2', Hu0'; lia).
      assert (P4 : u (v_addi a2 (-16)) <= 16 * Z.of_nat fuel) by (rewrite Hu2'; lia).
      assert (P5 : zero_at (ms_mem s) (u (v_addi a0 (-16))) (u a1 + 4096)) by (rewrite Hu0'; exact Hz').
      destruct (IH a1 (v_addi a0 (-16)) (v_addi a2 (-16)) s lo hi B Hlo Hhi P1 P2 P3 P4 P5)
        as (d & len & Heq & Hd & Hlen & Hm & Hzz).
      exists d, len. rewrite Heq. rewrite Hu2' in Hlen. repeat split; try assumption; lia.
  - (* [comment removed for export] *)
    exists (v_sub a0 a2), a2. split; [reflexivity|].
    rewrite u_v_sub by lia. repeat split; try lia. intros x Hx. apply Hz. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition same_out (m m' : word -> option byte) (lo hi : Z) : Prop :=
  forall a : word, ~ (lo <= u a < hi) -> m' a = m a.

Lemma m_mal0_loop_eq : forall fuel (p pp : word) s lo hi top,
  blk s lo hi -> lo <= u p -> u pp <= hi -> u p + 4096 <= u pp ->
  (u pp - u p) / 4096 < Z.of_nat fuel ->
  zero_at (ms_mem s) (u pp) top ->
  exists len s', m_mal0_loop fuel p pp s = TRet len s' /\
    u len = (u pp - u p) mod 4096 /\
    ms_vm s' = ms_vm s /\ ms_lo s' = ms_lo s /\ ms_hi s' = ms_hi s /\
    blk s' lo hi /\
    zero_at (ms_mem s') (u p + u len) top /\
    same_out (ms_mem s) (ms_mem s') (u p + u len) (u pp).
Proof.
  induction fuel as [|fuel IH]; intros p pp s lo hi top B Hlo Hhi Hpp Hf Hz; [cbn in Hf; lia|].
  pose proof (u64_range p). pose proof (u64_range pp). destruct (blk_bounds _ _ _ B) as (B1 & B2 & B3).
  cbn [m_mal0_loop]. unfold mbind.
  set (a1 := v_addi (v_addi pp (-2048)) (-2048)).
  assert (Ha1 : u a1 = u pp - 4096) by (subst a1; rewrite !u_v_addi; rewrite ?u_v_addi; lia).
  assert (H4096 : u (wlit 4096) = 4096) by (apply u_wlit; lia).
  assert (Q1 : lo <= u a1) by (rewrite Ha1; lia).
  assert (Q2 : u a1 + 4096 <= hi) by (rewrite Ha1; lia).
  assert (Q3 : 0 < u (wlit 4096) <= 4096) by (rewrite H4096; lia).
  assert (Q4 : u (wlit 4096) mod 16 = 0) by (rewrite H4096; reflexivity).
  assert (Q5 : u pp = u a1 + u (wlit 4096)) by (rewrite Ha1, H4096; lia).
  assert (Q6 : u (wlit 4096) <= 16 * Z.of_nat ZSCAN_FUEL) by (rewrite H4096; unfold ZSCAN_FUEL; cbn; lia).
  assert (Q7 : zero_at (ms_mem s) (u pp) (u a1 + 4096)) by (rewrite Ha1; intros x Hx; apply Hz; lia).
  destruct (m_zscan_eq ZSCAN_FUEL a1 pp (wlit 4096) s lo hi B Q1 Q2 Q3 Q4 Q5 Q6 Q7) as (d & len & Heq & Hd & Hlen & Hm16 & Hzz).
  rewrite Heq. cbn [tbind].
  rewrite H4096 in Hlen.
  rewrite (m_memset0_eq d len s lo hi B) by lia. cbn [tbind].
  set (s1 := if is0 len then s else upd s (wbytes (ms_mem s) d (zero_bytes len)) (ms_vm s)).
  assert (Hsh : ms_vm s1 = ms_vm s /\ ms_lo s1 = ms_lo s /\ ms_hi s1 = ms_hi s).
  { subst s1. destruct (is0 len); repeat split; reflexivity. }
  assert (Hmem : forall x : word, ms_mem s1 x = (if is0 len then ms_mem s x else wbytes (ms_mem s) d (zero_bytes len) x)).
  { subst s1. destruct (is0 len); reflexivity. }
  assert (B' : blk s1 lo hi).
  { subst s1. destruct (is0 len); [exact B|]. apply blk_upd; [exact B|]. intros x Hx.
    destruct (Z.lt_ge_cases (u x) (u d)); [| destruct (Z.lt_ge_cases (u x) (u d + u len))].
    - rewrite wbytes_zero_out by lia. apply (blk_def _ _ _ B). lia.
    - rewrite wbytes_zero_in by lia. discriminate.
    - rewrite wbytes_zero_out by lia. apply (blk_def _ _ _ B). lia. }
  assert (Hz1 : zero_at (ms_mem s1) (u d) top).
  { intros x Hx. rewrite Hmem. destruct (is0 len) eqn:E.
    - apply is0_true in E. destruct (Z.lt_ge_cases (u x) (u a1 + 4096)); [apply Hzz; lia | apply Hz; lia].
    - destruct (Z.lt_ge_cases (u x) (u d + u len)).
      + apply wbytes_zero_in; lia.
      + rewrite wbytes_zero_out by lia.
        destruct (Z.lt_ge_cases (u x) (u a1 + 4096)); [apply Hzz; lia | apply Hz; lia]. }
  assert (Hso1 : same_out (ms_mem s) (ms_mem s1) (u d) (u d + u len)).
  { intros x Hx. rewrite Hmem. destruct (is0 len); [reflexivity|]. apply wbytes_zero_out; lia. }
  assert (Hs1 : True) by exact I.
  clearbody s1. destruct Hsh as (Hv1 & Hl1 & Hh1). clear Hmem.
  assert (Hsub : u (v_sub d p) = u d - u p) by (apply u_v_sub; lia).
  destruct (is0 (v_srli (v_sub d p) 12)) eqn:E.
  - (* [comment removed for export] *)
    apply is0_true in E. rewrite u_v_srli in E by lia. change (2^12) with 4096 in E. rewrite Hsub in E.
    assert (u d - u p < 4096) by (apply Z.div_small_iff in E; lia).
    exists (v_sub d p), s1. split; [reflexivity|]. rewrite Hsub.
    split; [| split; [exact Hv1 | split; [exact Hl1 | split; [exact Hh1 | split; [exact B' | split]]]]].
    + replace (u pp - u p) with ((u d - u p) + 1 * 4096) by lia.
      rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
    + replace (u p + (u d - u p)) with (u d) by lia. exact Hz1.
    + intros x Hx. apply Hso1. lia.
  - apply is0_false in E. rewrite u_v_srli in E by lia. change (2^12) with 4096 in E. rewrite Hsub in E.
    assert (4096 <= u d - u p) by (destruct (Z.lt_ge_cases (u d - u p) 4096); [rewrite Z.div_small in E; lia | lia]).
    assert (R1 : u d <= hi) by lia.
    assert (R2 : u p + 4096 <= u d) by lia.
    assert (R3 : (u d - u p) / 4096 < Z.of_nat fuel).
    { replace (u pp - u p) with ((u d - u p) + 1 * 4096) in Hf by lia.
      rewrite Z_div_plus_full in Hf by lia. lia. }
    destruct (IH p d s1 lo hi top B' Hlo R1 R2 R3 Hz1) as (len' & s' & Heq' & Hlen' & Hv' & Hl' & Hh' & B'' & Hz' & Hso').
    exists len', s'. rewrite Heq'. split; [reflexivity|].
    split; [| split; [congruence | split; [congruence | split; [congruence | split; [exact B'' | split; [exact Hz'|]]]]]].
    + rewrite Hlen'. replace (u pp - u p) with ((u d - u p) + 1 * 4096) by lia.
      rewrite Z_mod_plus_full. reflexivity.
    + intros x Hx. rewrite (Hso' x) by lia. apply Hso1. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma st_zone_errno : st_zone A_ERRNO 4 = true.
Proof.
  unfold st_zone. cbn zeta. rewrite !orb_true_iff. left. right.
  rewrite andb_true_iff, !Z.leb_le. lia.
Qed.

Lemma lw_zero4 : is0 (v_lw (le_val [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0])) = true.
Proof. apply is0_true. reflexivity. Qed.

(* [comment removed for export] *)
Lemma tsafe_mbind_ret : forall {A B} (m : M A) (f : A -> M B) s a s' Q,
  m s = TRet a s' -> tsafe (f a s') Q -> tsafe (mbind m f s) Q.
Proof. intros A B m f s a s' Q Hm Hf. unfold mbind. rewrite Hm. exact Hf. Qed.

Lemma tsafe_mbind_gen : forall {A B} (m : M A) (f : A -> M B) s (R : A -> mstate -> Prop) Q,
  tsafe (m s) R -> (forall a s', R a s' -> tsafe (f a s') Q) -> tsafe (mbind m f s) Q.
Proof. intros A B m f s R Q Hm Hf. unfold mbind. eapply tsafe_bind; eauto. Qed.

Lemma m_lw_eq : forall (a : word) s bs,
  acc_ok s a 4 = true -> rdn ml_segs (ms_mem s) a 4 = Some bs -> m_lw a s = TRet (v_lw (le_val bs)) s.
Proof.
  intros a s bs Hacc Hrd. unfold m_lw, mbind, m_rd, mret. change (Z.of_nat 4) with 4.
  rewrite Hacc, Hrd. reflexivity.
Qed.

Theorem tsafe_calloc :
  forall fuel (sp m n : word) s (MP : word -> mstate -> Prop) (P : word -> mstate -> Prop),
  let sz := v_mul n m in
  let ovf := negb (is0 n) && negb (is0 (v_mulhu n m)) in
  (* [comment removed for export] *)
  (ovf = true ->
     acc_ok s A_ERRNO 4 = true /\ store_ok ml_segs (ms_mem s) A_ERRNO 4 = true /\
     P w0 (upd s (wbytes (ms_mem s) A_ERRNO (word_to_le_bytes 4 (wlit 12))) (ms_vm s))) ->
  (ovf = false ->
     tsafe (m_malloc (at_ sp (-48)) sz s) MP /\
     (forall s', MP w0 s' -> P w0 s') /\
     (forall p s', MP p s' -> u p <> 0 ->
        u sz / 4096 < Z.of_nat fuel /\
        acc_ok s' A_MALLOC_REPLACED 4 = true /\
        rdn ml_segs (ms_mem s') A_MALLOC_REPLACED 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] /\
        (exists AZ : word -> mstate -> Prop,
           tsafe (m_allzerop p s') AZ /\
           (forall z s'', AZ z s'' -> s'' = s' /\ (u z <> 0 -> zero_at (ms_mem s') (u p) (u p + u sz)))) /\
        blk s' (u p) (u p + u sz) /\
        (forall s'', ms_vm s'' = ms_vm s' -> ms_lo s'' = ms_lo s' -> ms_hi s'' = ms_hi s' ->
           blk s'' (u p) (u p + u sz) ->
           zero_at (ms_mem s'') (u p) (u p + u sz) ->
           same_out (ms_mem s') (ms_mem s'') (u p) (u p + u sz) ->
           P p s''))) ->
  tsafe (m_calloc fuel sp m n s) P.
Proof.
  intros fuel sp m n s MP P sz ovf Hovf Hok.
  unfold m_calloc. fold ovf. fold sz.
  destruct ovf eqn:Eovf.
  - (* [comment removed for export] *)
    destruct (Hovf eq_refl) as (Hacc & Hst & HP).
    unfold mbind, m_sw, m_st. change (Z.of_nat 4) with 4. rewrite Hacc, st_zone_errno. cbn [andb].
    rewrite Hst. cbn [tbind]. exact HP.
  - destruct (Hok eq_refl) as (HM & HP0 & HK). clear Hovf Hok.
    eapply tsafe_mbind_gen; [exact HM|].
    intros p s' HMP. cbn beta.
    destruct (is0 p) eqn:Ep.
    { apply is0_true in Ep. assert (p = w0) by (apply bv_eq; rewrite Ep; reflexivity). subst p. exact (HP0 s' HMP). }
    apply is0_false in Ep.
    destruct (HK p s' HMP Ep) as (Hfuel & Hacc & Hrd & (AZ & HAZ & HAZpost) & B & HP).
    pose proof (u64_range p) as Hp. pose proof (u64_range sz) as Hsz. destruct (blk_bounds _ _ _ B) as (_ & _ & Htop).
    (* [comment removed for export] *)
    eapply tsafe_mbind_ret; [apply (m_lw_eq _ _ _ Hacc Hrd)|].
    rewrite lw_zero4.
    (* [comment removed for export] *)
    eapply (tsafe_mbind_gen _ _ s' (fun keep s'' => s'' = s' /\ (keep = true -> zero_at (ms_mem s') (u p) (u p + u sz)))).
    { eapply tsafe_mbind_gen; [exact HAZ|]. intros z s'' Hz. destruct (HAZpost z s'' Hz) as [-> Hzz].
      cbn. split; [reflexivity|]. intros Hk. apply Hzz. apply is0_false. destruct (is0 z); [discriminate | reflexivity]. }
    intros keep s'' [-> Hkeep].
    destruct keep.
    { (* [comment removed for export] *)
      cbn. apply HP; try reflexivity; [exact B | apply Hkeep; reflexivity | intros x Hx; reflexivity]. }
    clear Hkeep.
    (* [comment removed for export] *)
    destruct (is0 (v_srli sz 12)) eqn:Esz.
    + (* [comment removed for export] *)
      apply is0_true in Esz. rewrite u_v_srli in Esz by lia. change (2^12) with 4096 in Esz.
      assert (u sz < 4096) by (apply Z.div_small_iff in Esz; lia).
      eapply tsafe_mbind_ret; [reflexivity|].
      rewrite (m_memset0_eq p sz s' (u p) (u p + u sz) B) by lia.
      destruct (is0 sz) eqn:Ez.
      * apply is0_true in Ez. apply HP; try reflexivity; [exact B | intros x Hx; lia | intros x Hx; reflexivity].
      * apply HP; try reflexivity.
        -- apply blk_upd; [exact B|]. intros x Hx. cbn. rewrite wbytes_zero_in by lia. discriminate.
        -- intros x Hx. cbn. apply wbytes_zero_in; lia.
        -- intros x Hx. cbn. apply wbytes_zero_out; lia.
    + apply is0_false in Esz. rewrite u_v_srli in Esz by lia. change (2^12) with 4096 in Esz.
      assert (4096 <= u sz) by (destruct (Z.lt_ge_cases (u sz) 4096); [rewrite Z.div_small in Esz; lia | lia]).
      set (pp0 := v_add p sz). set (i := v_srli (v_slli pp0 52) 52). set (d0 := v_and pp0 PAGEMASK).
      assert (Hpp0 : u pp0 = u p + u sz) by (subst pp0; apply u_v_add; lia).
      assert (Hi : u i = u pp0 mod 4096) by (subst i; apply u_low12).
      assert (Hd0 : u d0 = u pp0 - u pp0 mod 4096) by (subst d0; apply u_and_pagemask).
      pose proof (Z.mod_pos_bound (u pp0) 4096 ltac:(lia)) as Hmod.
      assert (Hd0p : u p < u d0).
      { rewrite Hd0, Hpp0. enough ((u p + u sz) mod 4096 < u sz) by lia.
        apply Z.lt_le_trans with 4096; [apply Z.mod_pos_bound; lia | lia]. }
      (* [comment removed for export] *)
      unfold mbind at 1. unfold mbind at 1.
      rewrite (m_memset0_eq d0 i s' (u p) (u p + u sz) B) by lia.
      cbn [tbind].
      set (s1 := if is0 i then s' else upd s' (wbytes (ms_mem s') d0 (zero_bytes i)) (ms_vm s')).
      assert (Hsh : ms_vm s1 = ms_vm s' /\ ms_lo s1 = ms_lo s' /\ ms_hi s1 = ms_hi s').
      { subst s1. destruct (is0 i); repeat split; reflexivity. }
      assert (Hmem : forall x : word, ms_mem s1 x = (if is0 i then ms_mem s' x else wbytes (ms_mem s') d0 (zero_bytes i) x)).
      { subst s1. destruct (is0 i); reflexivity. }
      assert (B1 : blk s1 (u p) (u p + u sz)).
      { subst s1. destruct (is0 i); [exact B|]. apply blk_upd; [exact B|]. intros x Hx.
        destruct (Z.lt_ge_cases (u x) (u d0)); [| destruct (Z.lt_ge_cases (u x) (u d0 + u i))].
        - rewrite wbytes_zero_out by lia. apply (blk_def _ _ _ B). lia.
        - rewrite wbytes_zero_in by lia. discriminate.
        - rewrite wbytes_zero_out by lia. apply (blk_def _ _ _ B). lia. }
      assert (Hz1 : zero_at (ms_mem s1) (u d0) (u p + u sz)).
      { intros x Hx. rewrite Hmem. destruct (is0 i) eqn:E.
        - apply is0_true in E. exfalso. lia.
        - apply wbytes_zero_in; lia. }
      assert (Hso1 : same_out (ms_mem s') (ms_mem s1) (u d0) (u p + u sz)).
      { intros x Hx. rewrite Hmem. destruct (is0 i); [reflexivity|]. apply wbytes_zero_out; lia. }
      clearbody s1. clear Hmem. destruct Hsh as (Hv1 & Hl1 & Hh1).
      assert (Hsub : u (v_sub d0 p) = u d0 - u p) by (apply u_v_sub; lia).
      destruct (is0 (v_srli (v_sub d0 p) 12)) eqn:Ed.
      * (* [comment removed for export] *)
        apply is0_true in Ed. rewrite u_v_srli in Ed by lia. change (2^12) with 4096 in Ed. rewrite Hsub in Ed.
        assert (u d0 - u p < 4096) by (apply Z.div_small_iff in Ed; lia).
        unfold mret at 1. cbn [tbind].
        rewrite (m_memset0_eq p (v_sub d0 p) s1 (u p) (u p + u sz) B1) by (rewrite ?Hsub; lia).
        destruct (is0 (v_sub d0 p)) eqn:Ez; [apply is0_true in Ez; rewrite Hsub in Ez; lia|].
        apply HP; cbn; try congruence.
        -- apply blk_upd; [exact B1|]. intros x Hx. cbn.
           destruct (Z.lt_ge_cases (u x) (u d0)); [rewrite wbytes_zero_in by (rewrite ?Hsub; lia); discriminate|].
           rewrite wbytes_zero_out by (rewrite ?Hsub; lia). apply (blk_def _ _ _ B1). lia.
        -- intros x Hx. destruct (Z.lt_ge_cases (u x) (u d0)).
           ++ apply wbytes_zero_in; rewrite ?Hsub; lia.
           ++ rewrite wbytes_zero_out by (rewrite ?Hsub; lia). apply Hz1. lia.
        -- intros x Hx. rewrite wbytes_zero_out by (rewrite ?Hsub; lia). apply Hso1. lia.
      * (* [comment removed for export] *)
        apply is0_false in Ed. rewrite u_v_srli in Ed by lia. change (2^12) with 4096 in Ed. rewrite Hsub in Ed.
        assert (4096 <= u d0 - u p) by (destruct (Z.lt_ge_cases (u d0 - u p) 4096); [rewrite Z.div_small in Ed; lia | lia]).
        assert (Hf' : (u d0 - u p) / 4096 < Z.of_nat fuel).
        { apply Z.le_lt_trans with (u sz / 4096); [apply Z.div_le_mono; lia | exact Hfuel]. }
        destruct (m_mal0_loop_eq fuel p d0 s1 (u p) (u p + u sz) (u p + u sz) B1 ltac:(lia) ltac:(lia) ltac:(lia) Hf' Hz1)
          as (len & s2 & Heq2 & Hlen & Hv2 & Hl2 & Hh2 & B2 & Hz2 & Hso2).
        rewrite Heq2. cbn [tbind].
        pose proof (Z.mod_pos_bound (u d0 - u p) 4096 ltac:(lia)) as Hlm.
        rewrite (m_memset0_eq p len s2 (u p) (u p + u sz) B2) by lia.
        destruct (is0 len) eqn:Ez.
        -- apply is0_true in Ez. apply HP; try congruence.
           ++ intros x Hx. apply Hz2. lia.
           ++ intros x Hx. rewrite (Hso2 x) by lia. apply Hso1. lia.
        -- apply HP; cbn; try congruence.
           ++ apply blk_upd; [exact B2|]. intros x Hx. cbn.
              destruct (Z.lt_ge_cases (u x) (u p + u len)); [rewrite wbytes_zero_in by lia; discriminate|].
              rewrite wbytes_zero_out by lia. apply (blk_def _ _ _ B2). lia.
           ++ intros x Hx. destruct (Z.lt_ge_cases (u x) (u p + u len)).
              ** apply wbytes_zero_in; lia.
              ** rewrite wbytes_zero_out by lia. apply Hz2. lia.
           ++ intros x Hx. rewrite wbytes_zero_out by lia. rewrite (Hso2 x) by lia. apply Hso1. lia.
Qed.

End WithLayout.
