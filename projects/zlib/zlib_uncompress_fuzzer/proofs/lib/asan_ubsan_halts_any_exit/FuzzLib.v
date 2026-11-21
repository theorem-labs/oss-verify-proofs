(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.


Definition lkeeps (l : list reg) (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r l -> getr regs' r = getr regs r.

Lemma lkeeps_refl : forall l regs, lkeeps l regs regs.
Proof. intros l regs r _. reflexivity. Qed.

Lemma lkeeps_trans : forall l r1 r2 r3, lkeeps l r1 r2 -> lkeeps l r2 r3 -> lkeeps l r1 r3.
Proof. intros l r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma lkeeps_upd : forall l regs regs' (rd : reg) v,
  lkeeps l regs regs' -> ~ In rd l -> lkeeps l regs (regupd regs' rd v).
Proof.
  intros l regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

Lemma lkeeps_upd_same : forall l regs regs' (rd : reg) v,
  lkeeps l regs regs' -> getr regs rd = v -> rd <> 0%bv -> lkeeps l regs (regupd regs' rd v).
Proof.
  intros l regs regs' rd v K Hv Hnz r Hr.
  destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply K, Hr.
Qed.

Lemma lkeeps_incl : forall l l' regs regs', incl l' l -> lkeeps l regs regs' -> lkeeps l' regs regs'.
Proof. intros l l' regs regs' Hi K r Hr. apply K, Hi, Hr. Qed.

Lemma lkeeps_getr : forall l regs regs' (r : reg), lkeeps l regs regs' -> In r l -> getr regs' r = getr regs r.
Proof. intros l regs regs' r K Hr. apply K, Hr. Qed.

Lemma keeps_cs_lkeeps : forall regs regs', keeps_cs regs regs' <-> lkeeps callee_saved regs regs'.
Proof. intros; split; intros K r Hr; apply K, Hr. Qed.

Ltac not_inl := first [ apply RefMemcpyLib.not_in_regs_dec; reflexivity | cbv; intuition discriminate ].
Ltac solve_lkeeps :=
  repeat (apply lkeeps_upd; [| not_inl]); first [apply lkeeps_refl | assumption].

Lemma incl_regs_dec : forall (l' l : list reg),
  forallb (fun x => existsb (fun y => bv_eqb y x) l) l' = true -> incl l' l.
Proof.
  intros l' l H r Hr. apply in_regs_dec.
  exact (proj1 (forallb_forall _ _) H r Hr).
Qed.
Ltac incl_dec := apply incl_regs_dec; reflexivity.

Definition ak1 : list reg := [1; 3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition aku : list reg := [1; 3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition bk : list reg := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv.


Lemma lxor_lt_256 : forall a b, (0 <= a < 256)%Z -> (0 <= b < 256)%Z -> (0 <= Z.lxor a b < 256)%Z.
Proof.
  intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  apply (Z_bounded_by_bits 8); [lia | apply Z.lxor_nonneg; lia |].
  intros k Hk. rewrite Z.lxor_spec.
  rewrite (Z_testbit_high 8 a k) by lia. rewrite (Z_testbit_high 8 b k) by lia. reflexivity.
Qed.

Lemma u_LB : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. pose proof (u8_range b). apply u64_lit. lia. Qed.

Lemma u_LB_lt : forall b : byte, (bv_unsigned (Z_to_bv 64 (bv_unsigned b)) < 256)%Z.
Proof. intros b. rewrite u_LB. apply u8_range. Qed.

Lemma u_andi_255 : forall w : word, (bv_unsigned (v_andi w 255) < 256)%Z.
Proof.
  intros w. unfold v_andi. pose proof (u64_range w).
  change (bv_wrap 64 255) with (Z.ones 8). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned w) (2 ^ 8) ltac:(lia)).
  rewrite u64_lit by (cbn in *; lia). cbn in *. lia.
Qed.

Lemma u_xor_byte : forall x y : word,
  (bv_unsigned x < 256)%Z -> (bv_unsigned y < 256)%Z -> (bv_unsigned (v_xor x y) < 256)%Z.
Proof.
  intros x y Hx Hy. pose proof (u64_range x). pose proof (u64_range y).
  pose proof (lxor_lt_256 (bv_unsigned x) (bv_unsigned y) ltac:(lia) ltac:(lia)).
  unfold v_xor. rewrite u64_lit by lia. lia.
Qed.

Lemma u_slli_2 : forall w : word, (bv_unsigned w < 256)%Z ->
  bv_unsigned (v_slli w 2) = (4 * bv_unsigned w)%Z.
Proof.
  intros w Hw. pose proof (u64_range w). unfold v_slli.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite u64_lit by lia. lia.
Qed.

Lemma u_slli_2_bound : forall w : word, (bv_unsigned w < 256)%Z ->
  (bv_unsigned (v_slli w 2) + 4 <= 1024)%Z.
Proof. intros w Hw. pose proof (u64_range w). rewrite u_slli_2 by lia. lia. Qed.

Lemma v_srli_lit : forall z s, (0 <= z < 2 ^ 64)%Z -> (0 <= s)%Z ->
  v_srli (Z_to_bv 64 z) s = Z_to_bv 64 (z / 2 ^ s).
Proof.
  intros z s Hz Hs. unfold v_srli. rewrite u64_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma v_srliw_lit : forall z s, (0 <= z < 2 ^ 31)%Z -> (0 <= s)%Z ->
  v_srliw (Z_to_bv 64 z) s = Z_to_bv 64 (z / 2 ^ s).
Proof.
  intros z s Hz Hs. unfold v_srliw. rewrite u64_lit by lia.
  pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) Hs) as Hp.
  assert (Hd : (0 <= z / 2 ^ s <= z)%Z).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  rewrite (bv_wrap_small 32 z) by (change (bv_modulus 32) with (2 ^ 32)%Z; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia). reflexivity.
Qed.

Lemma v_slli_lit : forall z s, (0 <= s)%Z -> (0 <= z)%Z -> (z * 2 ^ s < 2 ^ 64)%Z ->
  v_slli (Z_to_bv 64 z) s = Z_to_bv 64 (z * 2 ^ s).
Proof.
  intros z s Hs Hz Hzs. unfold v_slli. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) Hs).
  rewrite u64_lit by nia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma v_mul_lit : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a < 2 ^ 64)%Z -> (b < 2 ^ 64)%Z ->
  v_mul (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof. intros a b Ha Hb Ha' Hb'. unfold v_mul. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma ul_count : forall blk, (8 <= blk < 2 ^ 31)%Z ->
  v_addi (v_slli (v_srliw (v_addi (Z_to_bv 64 blk) (-8)) 3) 3) 8
  = Z_to_bv 64 ((blk - 8) / 2 ^ 3 * 2 ^ 3 + 8).
Proof.
  intros blk Hblk.
  replace (v_addi (Z_to_bv 64 blk) (-8)) with (Z_to_bv 64 (blk - 8))
    by (unfold v_addi; rewrite u64_lit by lia; f_equal; lia).
  rewrite v_srliw_lit by lia.
  assert (Hd : (0 <= (blk - 8) / 2 ^ 3 <= blk)%Z).
  { change (2 ^ 3)%Z with 8%Z. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  rewrite v_slli_lit by (change (2 ^ 3)%Z with 8%Z in *; lia).
  unfold v_addi. rewrite u64_lit by (change (2 ^ 3)%Z with 8%Z in *; lia). reflexivity.
Qed.

Lemma srl3sll3 : forall q, (0 <= q)%Z -> (8 * q < 2 ^ 31)%Z ->
  v_slli (v_srliw (Z_to_bv 64 (8 * q)) 3) 3 = Z_to_bv 64 (8 * q).
Proof.
  intros q Hq Hq31. rewrite v_srliw_lit by lia. change (2 ^ 3)%Z with 8%Z.
  replace (8 * q / 8)%Z with q by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  rewrite v_slli_lit by (change (2 ^ 3)%Z with 8%Z; lia). f_equal. change (2 ^ 3)%Z with 8%Z. lia.
Qed.

Lemma v_sub_wrap : forall a b, v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. unfold v_sub. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma v_add_wrap2 : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma v_addi_wrap : forall a i, v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof.
  intros a i. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.


Lemma v_add_at_l : forall (a : word) d (w : word),
  v_add (at_ a d) w = at_ a (d + bv_unsigned w).
Proof.
  intros a d w. unfold at_. rewrite <- (Z_to_bv_bv_unsigned 64 w) at 1. rewrite v_add_wrap2. f_equal. lia.
Qed.

Lemma v_add_at_r : forall (a : word) d (w : word),
  v_add w (at_ a d) = at_ a (d + bv_unsigned w).
Proof. intros a d w. rewrite v_add_comm. unfold at_ at 2. fold (at_ a d). apply v_add_at_l. Qed.

Lemma v_add_base_r : forall (a w : word), v_add w a = at_ a (bv_unsigned w).
Proof. intros a w. rewrite <- (at_0 a) at 1. rewrite v_add_at_r. f_equal. Qed.

Lemma v_add_base_l : forall (a w : word), v_add a w = at_ a (bv_unsigned w).
Proof. intros a w. rewrite <- (at_0 a) at 1. rewrite v_add_at_l. f_equal. Qed.

Lemma v_sub_at_at : forall (a : word) x y, v_sub (at_ a x) (at_ a y) = Z_to_bv 64 (x - y).
Proof.
  intros a x y. unfold at_. rewrite v_sub_wrap. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. f_equal. lia.
Qed.

Lemma u_at : forall (a : word) d, (0 <= bv_unsigned a + d < 2 ^ 64)%Z -> bv_unsigned (at_ a d) = (bv_unsigned a + d)%Z.
Proof. intros a d H. unfold at_. apply u64_lit. exact H. Qed.

Lemma c_eq_at : forall (a : word) x y,
  (0 <= bv_unsigned a + x < 2 ^ 64)%Z -> (0 <= bv_unsigned a + y < 2 ^ 64)%Z ->
  c_eq (at_ a x) (at_ a y) = (x =? y)%Z.
Proof.
  intros a x y Hx Hy. unfold at_. rewrite c_eq_lit by lia.
  destruct (Z.eqb_spec x y) as [->|Hne]; [apply Z.eqb_refl | apply Z.eqb_neq; lia].
Qed.

Lemma c_ltu_at : forall (a : word) x y,
  (0 <= bv_unsigned a + x < 2 ^ 64)%Z -> (0 <= bv_unsigned a + y < 2 ^ 64)%Z ->
  c_ltu (at_ a x) (at_ a y) = (x <? y)%Z.
Proof.
  intros a x y Hx Hy. unfold at_. rewrite c_ltu_lit by lia.
  destruct (Z.ltb_spec x y); [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

Lemma c_eq_at_lit : forall (a : word) d z,
  (0 <= bv_unsigned a + d < 2 ^ 64)%Z -> (0 <= z < 2 ^ 64)%Z ->
  c_eq (at_ a d) (Z_to_bv 64 z) = (bv_unsigned a + d =? z)%Z.
Proof. intros a d z Hd Hz. unfold at_. apply c_eq_lit; lia. Qed.

Lemma c_ltu_at_lit_l : forall (a : word) d z,
  (0 <= bv_unsigned a + d < 2 ^ 64)%Z -> (0 <= z < 2 ^ 64)%Z ->
  c_ltu (at_ a d) (Z_to_bv 64 z) = (bv_unsigned a + d <? z)%Z.
Proof. intros a d z Hd Hz. unfold at_. apply c_ltu_lit; lia. Qed.

Lemma c_ltu_at_lit_r : forall (a : word) d z,
  (0 <= bv_unsigned a + d < 2 ^ 64)%Z -> (0 <= z < 2 ^ 64)%Z ->
  c_ltu (Z_to_bv 64 z) (at_ a d) = (z <? bv_unsigned a + d)%Z.
Proof. intros a d z Hd Hz. unfold at_. apply c_ltu_lit; lia. Qed.

Definition M1W : Z := 18446744073709551615.
Definition M3W : Z := 18446744073709551613.

Definition LIM1 : Z := 18446744073708503040.
Definition LIM2 : Z := 18446744073708503039.

Lemma entry_test_in : forall n, (1 <= n <= 1048576)%Z ->
  c_ltu (v_add (Z_to_bv 64 n) (Z_to_bv 64 LIM2)) (Z_to_bv 64 LIM1) = false.
Proof.
  intros n Hn. unfold LIM1, LIM2. rewrite v_add_lit by lia. rewrite c_ltu_lit by lia. apply Z.ltb_ge. lia.
Qed.

Lemma entry_test_out : forall n, (0 <= n < 2 ^ 64)%Z -> ~ (1 <= n <= 1048576)%Z ->
  c_ltu (v_add (Z_to_bv 64 n) (Z_to_bv 64 LIM2)) (Z_to_bv 64 LIM1) = true.
Proof.
  intros n Hn Hout. unfold LIM1, LIM2. rewrite v_add_wrap2.
  destruct (Z.eq_dec n 0) as [->|Hnz].
  - rewrite c_ltu_lit by lia. apply Z.ltb_lt. lia.
  - rewrite (Z_to_bv_64_mod (n + _)).
    replace ((n + 18446744073708503039) mod 2 ^ 64)%Z with (n - 1048577)%Z.
    + rewrite c_ltu_lit by lia. apply Z.ltb_lt. lia.
    + replace (n + 18446744073708503039)%Z with ((n - 1048577) + 1 * 2 ^ 64)%Z by lia.
      rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
Qed.


Definition AM : Z := 106321291491121335.

Definition am_ok (m : Z) : bool := (Z.shiftr (m * AM) 65 =? m / 347)%Z.

Lemma am_ok_all : forall m, (0 <= m < 65537)%Z -> am_ok m = true.
Proof.
  intros m Hm. apply (zallN_spec 65537%N am_ok); [|exact Hm].
  vm_compute. reflexivity.
Qed.

Lemma adler_q : forall n, (0 <= n <= 1048576)%Z ->
  (Z.shiftr (Z.shiftr (n / 2 ^ 4 * AM) 64) 1 = n / 5552)%Z.
Proof.
  intros n Hn. rewrite Z.shiftr_shiftr by lia. change (64 + 1)%Z with 65%Z.
  pose proof (am_ok_all (n / 2 ^ 4)) as Hm.
  unfold am_ok in Hm. apply Z.eqb_eq in Hm.
  - rewrite Hm. change (2 ^ 4)%Z with 16%Z. rewrite Z.div_div by lia. reflexivity.
  - change (2 ^ 4)%Z with 16%Z. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma adler_srli4 : forall n, (0 <= n < 2 ^ 64)%Z -> v_srli (Z_to_bv 64 n) 4 = Z_to_bv 64 (n / 2 ^ 4).
Proof. intros n Hn. apply v_srli_lit; lia. Qed.

Lemma adler_mulhu : forall n, (0 <= n <= 1048576)%Z ->
  v_mulhu (Z_to_bv 64 (n / 2 ^ 4)) (Z_to_bv 64 AM) = Z_to_bv 64 (Z.shiftr (n / 2 ^ 4 * AM) 64).
Proof.
  intros n Hn. unfold v_mulhu. change (2 ^ 4)%Z with 16%Z.
  assert (0 <= n / 16 <= n)%Z by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite !u64_lit by (unfold AM; lia). reflexivity.
Qed.

Lemma adler_blk : forall n, (0 <= n <= 1048576)%Z ->
  v_srli (Z_to_bv 64 (Z.shiftr (n / 2 ^ 4 * AM) 64)) 1 = Z_to_bv 64 (n / 5552).
Proof.
  intros n Hn. unfold v_srli. rewrite <- adler_q by lia. f_equal. f_equal.
  apply u64_lit. change (2 ^ 4)%Z with 16%Z.
  assert (0 <= n / 16 <= n)%Z by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; unfold AM; nia|].
  apply Z.div_lt_upper_bound; [lia|]. unfold AM. nia.
Qed.

Lemma adler_qmul : forall n, (0 <= n <= 1048576)%Z ->
  v_mul (Z_to_bv 64 (n / 5552)) (Z_to_bv 64 5552) = Z_to_bv 64 (n / 5552 * 5552).
Proof.
  intros n Hn. assert (0 <= n / 5552 <= n)%Z by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  apply v_mul_lit; lia.
Qed.

Lemma adler_rem : forall n, (0 <= n)%Z ->
  v_sub (Z_to_bv 64 n) (Z_to_bv 64 (n / 5552 * 5552)) = Z_to_bv 64 (n mod 5552).
Proof.
  intros n Hn. rewrite v_sub_wrap. f_equal. rewrite Zmod_eq by lia. reflexivity.
Qed.


Lemma rdn1_grows : forall segs m m' (a : word) b,
  mem_grows m m' -> rdn segs m a 1 = Some [b] -> exists b', rdn segs m' a 1 = Some [b'].
Proof.
  intros segs m m' a b Hg H. cbn [rdn] in *.
  destruct (m a) as [b0|] eqn:Hm.
  - assert (Hm' : m' a <> None) by (apply Hg; congruence).
    destruct (m' a) as [b1|]; [exists b1; reflexivity | congruence].
  - destruct (m' a) as [b1|]; [exists b1; reflexivity|].
    destruct (seg_rom segs a) as [b2|]; [exists b2; reflexivity | discriminate].
Qed.

Lemma rdn1_wbytes : forall segs m (a wa : word) bs b,
  rdn segs m a 1 = Some [b] -> exists b', rdn segs (wbytes m wa bs) a 1 = Some [b'].
Proof. intros segs m a wa bs b H. eapply rdn1_grows; [apply wbytes_grows | exact H]. Qed.

Lemma lenW8 : forall v : word, length (word_to_le_bytes 8 v) = 8%nat.
Proof. intros v. apply length_N_to_le_bytes. Qed.
