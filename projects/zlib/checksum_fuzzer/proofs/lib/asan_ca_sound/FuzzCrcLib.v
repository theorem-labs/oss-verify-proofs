(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound Require Import PropExec SeqExec FuzzZ FuzzCk FuzzMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.cks Require Import CkTables CkModel CkMathCrc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma land_255_low32 : forall y, Z.land y 255 = Z.land (y mod two32) 255.
Proof.
  intros y. rewrite land_mod32_l. symmetry. apply Z.mod_small.
  pose proof (land_255_range y). lia.
Qed.

Lemma land_shiftr_255_low32 : forall y k, 0 <= k -> k + 8 <= 32 ->
  Z.land (Z.shiftr y k) 255 = Z.land (Z.shiftr (y mod two32) k) 255.
Proof.
  intros y k Hk Hk8. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  destruct (Z.ltb_spec n 8).
  - rewrite testbit_mod32 by lia. reflexivity.
  - replace (Z.testbit 255 n) with false; [rewrite !andb_false_r; reflexivity|].
    symmetry. change 255 with (Z.ones 8). apply Z.ones_spec_high. lia.
Qed.

Lemma land_1020_shiftr : forall y k, 2 <= k ->
  Z.land (Z.shiftr y (k - 2)) 1020 = Z.land (Z.shiftr y k) 255 * 4.
Proof.
  intros y k Hk. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec by lia.
  change 4 with (2 ^ 2). rewrite Z.mul_pow2_bits by lia.
  destruct (Z.ltb_spec n 2).
  - replace (Z.testbit 1020 n) with false.
    + rewrite andb_false_r. rewrite Z.testbit_neg_r by lia. reflexivity.
    + assert (E : n = 0 \/ n = 1) by lia. destruct E as [-> | ->]; reflexivity.
  - rewrite Z.land_spec, Z.shiftr_spec by lia.
    replace (n - 2 + k) with (n + (k - 2)) by lia. f_equal.
    change 1020 with (255 * 2 ^ 2). rewrite Z.mul_pow2_bits by lia. reflexivity.
Qed.

Lemma shiftr24_low32_range : forall y, 0 <= Z.shiftr (y mod two32) 24 < 256.
Proof.
  intros y. pose proof (mod32_range y).
  apply (shiftr_range (y mod two32) 24 8); [lia|lia|]. change (2 ^ (8 + 24)) with two32. lia.
Qed.

Lemma land_255_small : forall a, 0 <= a < 256 -> Z.land a 255 = a.
Proof. intros a Ha. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma shiftr8_range32 : forall c, 0 <= c < two32 -> 0 <= Z.shiftr c 8 < two32.
Proof.
  intros c Hc. pose proof (shiftr_range c 8 24 ltac:(lia) ltac:(lia) ltac:(change (2 ^ (24 + 8)) with two32; lia)).
  change (2 ^ 24) with 16777216 in H. lia.
Qed.

Lemma ctab_range32 : forall i, 0 <= ctab i < two32.
Proof. intros. pose proof (CkMathCrc.ctab_range i). change (2 ^ 32) with two32 in H. lia. Qed.

Lemma btab_range32 : forall k i, 0 <= btab k i < two32.
Proof. intros. pose proof (CkMathCrc.btab_range k i). change (2 ^ 32) with two32 in H. lia. Qed.

Definition MAGIC20 : Z := 14757395258967641293.

Lemma magic20_div : forall n, 0 <= n < two64 -> Z.shiftr (n * MAGIC20 / two64) 4 = n / 20.
Proof.
  intros n Hn. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_div by lia.
  assert (E : n * MAGIC20 = (n * 2 ^ 66 + n) / 5).
  { apply Z.div_unique_exact; [lia|]. unfold MAGIC20. lia. }
  rewrite E. rewrite Z.div_div by lia.
  set (q := n / 20). set (r := n mod 20).
  assert (Hn' : n = 20 * q + r) by (subst q r; apply Z.div_mod; lia).
  assert (Hr : 0 <= r < 20) by (subst r; apply Z.mod_pos_bound; lia).
  symmetry. apply (Z.div_unique _ _ _ (r * 2 ^ 66 + n)); [left; change two64 with (2 ^ 64) in Hn; lia | change two64 with (2 ^ 64); lia].
Qed.

Lemma mulhu_range : forall a b, 0 <= a < two64 -> 0 <= b < two64 -> 0 <= a * b / two64 < two64.
Proof.
  intros a b Ha Hb. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. apply Z.mul_lt_mono_nonneg; lia.
Qed.


Lemma crc_byte_range : forall c b, 0 <= c < two32 -> 0 <= crc_byte c b < two32.
Proof.
  intros c b Hc. unfold crc_byte. apply lxor_range32; [apply shiftr8_range32; lia | apply ctab_range32].
Qed.

Lemma crc_bytes_range : forall bs c, 0 <= c < two32 -> 0 <= crc_bytes c bs < two32.
Proof.
  induction bs as [|b bs IH]; intros c Hc; [exact Hc|].
  rewrite crc_bytes_cons. apply IH. apply crc_byte_range. exact Hc.
Qed.

Lemma crc_bytes4 : forall c b0 b1 b2 b3,
  crc_bytes c [b0; b1; b2; b3] = crc_byte (crc_byte (crc_byte (crc_byte c b0) b1) b2) b3.
Proof. intros. unfold crc_bytes. cbn [fold_left]. reflexivity. Qed.

Lemma crc_bytes8 : forall c b0 b1 b2 b3 b4 b5 b6 b7,
  crc_bytes c [b0; b1; b2; b3; b4; b5; b6; b7]
  = crc_byte (crc_byte (crc_byte (crc_byte (crc_byte (crc_byte (crc_byte (crc_byte c b0) b1) b2) b3) b4) b5) b6) b7.
Proof. intros. unfold crc_bytes. cbn [fold_left]. reflexivity. Qed.

Definition mlane (x w : Z) : Z :=
  let y := Z.lxor (sx32 w) x in
  Z.lxor (Z.lxor (sx32 (btab 3 (Z.shiftr (y mod two32) 24)))
                 (sx32 (btab 2 (Z.land (Z.shiftr y 16) 255))))
         (Z.lxor (sx32 (btab 1 (Z.land (Z.shiftr y 8) 255)))
                 (sx32 (btab 0 (Z.land y 255)))).

Definition bT0 (y : Z) : Z := sx32 (btab 0 (Z.land y 255)).
Definition bT1 (y : Z) : Z := sx32 (btab 1 (Z.land (Z.shiftr y 8) 255)).
Definition bT2 (y : Z) : Z := sx32 (btab 2 (Z.land (Z.shiftr y 16) 255)).
Definition bT3 (y : Z) : Z := sx32 (btab 3 (Z.shiftr (y mod two32) 24)).
Definition mlaneY (y : Z) : Z := Z.lxor (Z.lxor (bT3 y) (bT2 y)) (Z.lxor (bT1 y) (bT0 y)).

Lemma mlane_Y : forall x w, mlane x w = mlaneY (Z.lxor (sx32 w) x).
Proof. reflexivity. Qed.

Lemma sx32_range' : forall x, 0 <= x < two32 -> 0 <= sx32 x < two64.
Proof. exact sx32_range. Qed.

Lemma lxor4_mod32 : forall a b c d,
  (Z.lxor (Z.lxor a b) (Z.lxor c d)) mod two32
  = Z.lxor (Z.lxor (a mod two32) (b mod two32)) (Z.lxor (c mod two32) (d mod two32)).
Proof. intros. rewrite !lxor_mod32. reflexivity. Qed.

Lemma lxor4_perm : forall b0 b1 b2 b3,
  Z.lxor (Z.lxor b3 b2) (Z.lxor b1 b0) = Z.lxor (Z.lxor (Z.lxor b0 b1) b2) b3.
Proof.
  intros. rewrite (Z.lxor_comm b3 b2), (Z.lxor_comm b1 b0).
  rewrite (Z.lxor_comm (Z.lxor b2 b3) (Z.lxor b0 b1)). rewrite <- !Z.lxor_assoc. reflexivity.
Qed.

Lemma mlane_mod32 : forall x w, 0 <= w < two32 ->
  (mlane x w) mod two32 = braid1 (x mod two32) w.
Proof.
  intros x w Hw. unfold mlane, braid1. cbv zeta.
  set (y := Z.lxor (sx32 w) x).
  assert (Hy : y mod two32 = Z.lxor (x mod two32) w).
  { subst y. rewrite <- lxor_mod32, sx32_mod32, Z.lxor_comm by lia. reflexivity. }
  rewrite lxor4_mod32, !sx32_mod32 by (apply btab_range32).
  rewrite (land_255_low32 y), (land_shiftr_255_low32 y 8), (land_shiftr_255_low32 y 16) by lia.
  rewrite Hy.
  rewrite <- (land_255_small (Z.shiftr (Z.lxor (x mod two32) w) 24)) at 1
    by (rewrite <- Hy; apply shiftr24_low32_range).
  apply lxor4_perm.
Qed.

Lemma mlane_range : forall x w, 0 <= mlane x w < two64.
Proof.
  intros x w. unfold mlane. cbv zeta.
  apply lxor_range64; apply lxor_range64; apply sx32_range; apply btab_range32.
Qed.

Definition mw1 (y : Z) : Z := Z.lxor (Z.shiftr (y mod two32) 8) (sx32 (ctab (Z.land y 255))).
Definition mw3 (y : Z) : Z := mw1 (mw1 (mw1 y)).
Definition mw4 (z t : Z) : Z := Z.lxor (sx32 (ctab (Z.land z 255))) (Z.lxor t (Z.shiftr (z mod two32) 8)).
Definition mwf (z : Z) : Z := Z.lxor (Z.shiftr (z mod two32) 8) (ctab (Z.land z 255)).

Definition mlast (x0 x1 x2 x3 x4 w0 w1 w2 w3 w4 : Z) : Z :=
  let y0 := Z.lxor (sx32 w0) x0 in
  let y1 := mw4 (mw3 y0) (Z.lxor x1 (sx32 w1)) in
  let y2 := mw4 (mw3 y1) (Z.lxor x2 (sx32 w2)) in
  let y3 := mw4 (mw3 y2) (Z.lxor x3 (sx32 w3)) in
  let y4 := mw4 (mw3 y3) (Z.lxor x4 (sx32 w4)) in
  mwf (mw3 y4).

Lemma mw1_mod32 : forall y, (mw1 y) mod two32 = crc_word1 (y mod two32).
Proof.
  intros y. unfold mw1, crc_word1. rewrite <- lxor_mod32, sx32_mod32 by (apply ctab_range32).
  rewrite (Z.mod_small (Z.shiftr _ 8)) by (apply shiftr8_range32; apply mod32_range).
  rewrite <- land_255_low32. reflexivity.
Qed.

Lemma mw3_mod32 : forall y, (mw3 y) mod two32 = crc_word1 (crc_word1 (crc_word1 (y mod two32))).
Proof. intros. unfold mw3. rewrite !mw1_mod32. reflexivity. Qed.

Lemma mw4_mod32 : forall z t, (mw4 z t) mod two32 = Z.lxor (t mod two32) (crc_word1 (z mod two32)).
Proof.
  intros z t. unfold mw4, crc_word1. rewrite <- !lxor_mod32, sx32_mod32 by (apply ctab_range32).
  rewrite (Z.mod_small (Z.shiftr _ 8)) by (apply shiftr8_range32; apply mod32_range).
  rewrite <- land_255_low32.
  rewrite (Z.lxor_comm (ctab _) _), <- Z.lxor_assoc. reflexivity.
Qed.

Lemma mwf_exact : forall z, mwf z = crc_word1 (z mod two32).
Proof. intros z. unfold mwf, crc_word1. rewrite <- land_255_low32. reflexivity. Qed.

Lemma mwf_range : forall z, 0 <= mwf z < two32.
Proof.
  intros z. unfold mwf. apply lxor_range32; [apply shiftr8_range32; apply mod32_range | apply ctab_range32].
Qed.

Lemma crc_word_mw : forall y, crc_word (y mod two32) = crc_word1 ((mw3 y) mod two32).
Proof. intros. unfold crc_word. rewrite mw3_mod32. reflexivity. Qed.

Lemma lxor_sx32_mod32 : forall x w, 0 <= w < two32 -> (Z.lxor x (sx32 w)) mod two32 = Z.lxor (x mod two32) w.
Proof. intros x w Hw. rewrite <- lxor_mod32, sx32_mod32 by lia. reflexivity. Qed.

Lemma mlast_ok : forall x0 x1 x2 x3 x4 w0 w1 w2 w3 w4 blk,
  0 <= w0 < two32 -> 0 <= w1 < two32 -> 0 <= w2 < two32 -> 0 <= w3 < two32 -> 0 <= w4 < two32 ->
  words_le blk = [w0; w1; w2; w3; w4] ->
  mlast x0 x1 x2 x3 x4 w0 w1 w2 w3 w4
  = braid_last [x0 mod two32; x1 mod two32; x2 mod two32; x3 mod two32; x4 mod two32] blk.
Proof.
  intros x0 x1 x2 x3 x4 w0 w1 w2 w3 w4 blk H0 H1 H2 H3 H4 Hb.
  unfold braid_last. rewrite Hb. unfold mlast. cbv zeta.
  rewrite mwf_exact, <- crc_word_mw.
  rewrite mw4_mod32, lxor_sx32_mod32, <- crc_word_mw by exact H4.
  rewrite mw4_mod32, lxor_sx32_mod32, <- crc_word_mw by exact H3.
  rewrite mw4_mod32, lxor_sx32_mod32, <- crc_word_mw by exact H2.
  rewrite mw4_mod32, lxor_sx32_mod32, <- crc_word_mw by exact H1.
  rewrite <- (lxor_mod32 (sx32 w0) x0), sx32_mod32, (Z.lxor_comm w0) by exact H0.
  reflexivity.
Qed.

Lemma mlast_range : forall x0 x1 x2 x3 x4 w0 w1 w2 w3 w4,
  0 <= mlast x0 x1 x2 x3 x4 w0 w1 w2 w3 w4 < two32.
Proof. intros. unfold mlast. cbv zeta. apply mwf_range. Qed.


Definition lanes : Type := (Z * Z * Z * Z * Z)%type.
Definition lmod (x : lanes) : list Z :=
  let '(x0, x1, x2, x3, x4) := x in [x0 mod two32; x1 mod two32; x2 mod two32; x3 mod two32; x4 mod two32].
Definition lrng (x : lanes) : Prop :=
  let '(x0, x1, x2, x3, x4) := x in
  0 <= x0 < two64 /\ 0 <= x1 < two64 /\ 0 <= x2 < two64 /\ 0 <= x3 < two64 /\ 0 <= x4 < two64.

Lemma align4_zero : forall a, a mod 4 = 0 <-> align4 a = 0.
Proof.
  intros a. unfold align4. pose proof (Z.mod_pos_bound a 4 ltac:(lia)) as H.
  split; intros E.
  - rewrite E. reflexivity.
  - assert (C : a mod 4 = 0 \/ a mod 4 = 1 \/ a mod 4 = 2 \/ a mod 4 = 3) by lia.
    destruct C as [C|[C|[C|C]]]; rewrite C in E; cbv in E; lia.
Qed.

Lemma mod4_succ : forall a, (a + 1) mod 4 = (if a mod 4 =? 3 then 0 else a mod 4 + 1).
Proof.
  intros a. pose proof (Z.mod_pos_bound a 4 ltac:(lia)) as H.
  rewrite <- Z.add_mod_idemp_l by lia.
  destruct (Z.eqb_spec (a mod 4) 3) as [E|E]; [rewrite E; reflexivity | apply Z.mod_small; lia].
Qed.

Lemma align4_cases : forall a, a mod 4 <> 0 ->
  (align4 a = 1 /\ (a + 1) mod 4 = 0) \/ (2 <= align4 a <= 3 /\ (a + 1) mod 4 <> 0 /\ align4 (a + 1) = align4 a - 1).
Proof.
  intros a Ha. unfold align4. rewrite mod4_succ. pose proof (Z.mod_pos_bound a 4 ltac:(lia)) as H.
  assert (C : a mod 4 = 1 \/ a mod 4 = 2 \/ a mod 4 = 3) by lia.
  destruct C as [C|[C|C]]; rewrite C; vm_compute; intuition discriminate.
Qed.

Section ORACLE.
  Variable BA : Z -> Z.
  Hypothesis BA_range : forall a, 0 <= BA a < 256.

  Fixpoint bl (a : Z) (n : nat) : list Z :=
    match n with O => [] | S n' => BA a :: bl (a + 1) n' end.

  Definition Wd (a : Z) : Z := wle (BA a) (BA (a + 1)) (BA (a + 2)) (BA (a + 3)).

  Lemma bl_S : forall a n, bl a (S n) = BA a :: bl (a + 1) n.
  Proof. reflexivity. Qed.

  Lemma bl_length : forall n a, length (bl a n) = n.
  Proof. induction n; intros; cbn; [reflexivity | rewrite IHn; reflexivity]. Qed.

  Lemma bl_Zlen : forall n a, Zlen (bl a n) = Z.of_nat n.
  Proof. intros. unfold Zlen. rewrite bl_length. reflexivity. Qed.

  Lemma bl_app : forall n1 n2 a, bl a (n1 + n2) = bl a n1 ++ bl (a + Z.of_nat n1) n2.
  Proof.
    induction n1 as [|n1 IH]; intros n2 a.
    - cbn. rewrite Z.add_0_r. reflexivity.
    - cbn [bl Nat.add app]. rewrite IH. f_equal. f_equal. f_equal. lia.
  Qed.

  Lemma bl_bytes : forall n a, bytes (bl a n).
  Proof. induction n; intros a; cbn; constructor; [apply BA_range | apply IHn]. Qed.

  Lemma firstn_bl : forall k n a, (k <= n)%nat -> firstn k (bl a n) = bl a k.
  Proof.
    induction k as [|k IH]; intros n a Hk; [reflexivity|].
    destruct n as [|n]; [lia|]. cbn [bl firstn]. rewrite IH by lia. reflexivity.
  Qed.

  Lemma skipn_bl : forall k n a, (k <= n)%nat -> skipn k (bl a n) = bl (a + Z.of_nat k) (n - k).
  Proof.
    induction k as [|k IH]; intros n a Hk.
    - cbn. rewrite Z.add_0_r, Nat.sub_0_r. reflexivity.
    - destruct n as [|n]; [lia|]. cbn [bl skipn]. rewrite IH by lia.
      replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (S k)) by lia. reflexivity.
  Qed.

  Lemma Wd_range : forall a, 0 <= Wd a < two32.
  Proof.
    intros a. unfold Wd. pose proof (wle_range (BA a) (BA (a + 1)) (BA (a + 2)) (BA (a + 3))
      (BA_range _) (BA_range _) (BA_range _) (BA_range _)). change (2 ^ 32) with two32 in H. exact H.
  Qed.

  Lemma words_le_bl20 : forall a, words_le (bl a 20) = [Wd a; Wd (a + 4); Wd (a + 8); Wd (a + 12); Wd (a + 16)].
  Proof.
    intros a. cbn [bl words_le]. unfold Wd.
    repeat match goal with
           | |- (_ :: _) = (_ :: _) => apply (f_equal2 (@cons Z))
           | |- wle _ _ _ _ = wle _ _ _ _ => f_equal
           | |- BA _ = BA _ => apply (f_equal BA); lia
           | |- @nil _ = @nil _ => reflexivity
           end.
  Qed.

  Definition mstep (a : Z) (x : lanes) : lanes :=
    let '(x0, x1, x2, x3, x4) := x in
    (mlane x0 (Wd a), mlane x1 (Wd (a + 4)), mlane x2 (Wd (a + 8)), mlane x3 (Wd (a + 12)), mlane x4 (Wd (a + 16))).

  Fixpoint mrun (k : nat) (a : Z) (x : lanes) : lanes :=
    match k with O => x | S k' => mrun k' (a + 20) (mstep a x) end.

  Lemma mstep_ok : forall a x, braid_step (lmod x) (bl a 20) = lmod (mstep a x).
  Proof.
    intros a [[[[x0 x1] x2] x3] x4]. unfold braid_step. rewrite words_le_bl20. cbn [lmod mstep combine map fst snd].
    rewrite !mlane_mod32 by apply Wd_range. reflexivity.
  Qed.

  Lemma mrun_ok : forall k a x n, (20 * k <= n)%nat -> braid_state (lmod x) k (bl a n) = lmod (mrun k a x).
  Proof.
    induction k as [|k IH]; intros a x n Hn; [reflexivity|].
    rewrite braid_state_S_front. cbn [mrun].
    rewrite firstn_bl, skipn_bl by lia. rewrite mstep_ok.
    replace (Z.of_nat 20) with 20 by reflexivity. apply IH. lia.
  Qed.

  Lemma mstep_rng : forall a x, lrng (mstep a x).
  Proof. intros a [[[[x0 x1] x2] x3] x4]. cbn. repeat split; apply mlane_range. Qed.

  Lemma mrun_rng : forall k a x, lrng x -> lrng (mrun k a x).
  Proof. induction k; intros a x Hx; cbn; [exact Hx | apply IHk, mstep_rng]. Qed.

  Lemma mrun_S_end : forall k a x, mrun (S k) a x = mstep (a + 20 * Z.of_nat k) (mrun k a x).
  Proof.
    induction k as [|k IH]; intros a x.
    - cbn. rewrite Z.add_0_r. reflexivity.
    - cbn [mrun] in *. rewrite IH. f_equal. lia.
  Qed.

  Definition mlastx (x : lanes) (a : Z) : Z :=
    let '(x0, x1, x2, x3, x4) := x in
    mlast x0 x1 x2 x3 x4 (Wd a) (Wd (a + 4)) (Wd (a + 8)) (Wd (a + 12)) (Wd (a + 16)).

  Definition tail_entry (adr len c : Z) : Z * Z * Z :=
    let c0 := crc_pre c in
    if len <? 23 then (c0, adr, len) else
    let na := align4 adr in
    let c1 := crc_bytes c0 (bl adr (Z.to_nat na)) in
    let a1 := adr + na in
    let n1 := len - na in
    let blks := n1 / 20 in
    let x := mrun (Z.to_nat (blks - 1)) a1 (c1, 0, 0, 0, 0) in
    let aL := a1 + 20 * (blks - 1) in
    (mlastx x aL, aL + 20, n1 - 20 * blks).

  Lemma crc_pre_range32 : forall c, 0 <= crc_pre c < two32.
  Proof. intros c. pose proof (crc_pre_range c). change (2 ^ 32) with two32 in H. exact H. Qed.

  Lemma mlastx_ok : forall x a, mlastx x a = braid_last (lmod x) (bl a 20).
  Proof.
    intros [[[[x0 x1] x2] x3] x4] a. cbn [mlastx lmod].
    apply mlast_ok; [apply Wd_range .. | apply words_le_bl20].
  Qed.

  Lemma mlastx_range : forall x a, 0 <= mlastx x a < two32.
  Proof. intros [[[[x0 x1] x2] x3] x4] a. cbn [mlastx]. apply mlast_range. Qed.

  Theorem crc32_z_bridge : forall adr len c, 0 <= len ->
    crc32_z_model adr c (bl adr (Z.to_nat len)) =
    (let '(cT, aT, nT) := tail_entry adr len c in Z.lxor (crc_bytes cT (bl aT (Z.to_nat nT))) M32).
  Proof.
    intros adr len c Hlen. unfold crc32_z_model, tail_entry. rewrite bl_Zlen, Z2Nat.id by lia.
    destruct (Z.ltb_spec len 23) as [Hs|Hb]; [reflexivity|].
    unfold crc_braid_phase. cbv zeta.
    pose proof (align4_range adr) as Hna. set (na := align4 adr) in *.
    rewrite firstn_bl, skipn_bl by lia. rewrite Z2Nat.id by lia.
    rewrite bl_Zlen. rewrite Nat2Z.inj_sub, Z2Nat.id, Z2Nat.id by lia.
    set (n1 := len - na). set (blks := n1 / 20).
    assert (Hb1 : 1 <= blks) by (subst blks n1; apply Z.div_le_lower_bound; lia).
    assert (Hb2 : 20 * blks <= n1) by (subst blks; apply Z.mul_div_le; lia).
    set (c1 := crc_bytes (crc_pre c) (bl adr (Z.to_nat na))).
    assert (Hc1 : 0 <= c1 < two32) by (subst c1; apply crc_bytes_range, crc_pre_range32).
    replace [c1; 0; 0; 0; 0] with (lmod (c1, 0, 0, 0, 0))
      by (cbn; rewrite (Z.mod_small c1) by lia; reflexivity).
    rewrite mrun_ok by lia.
    cbn [fst snd]. f_equal. f_equal.
    - rewrite mlastx_ok. f_equal. unfold block. rewrite skipn_bl, firstn_bl by lia. f_equal. lia.
    - rewrite skipn_bl by lia. f_equal; lia.
  Qed.
End ORACLE.


Lemma bl_bytes_at : forall segs m n a, bl (byte_at segs m) a n = bytes_at segs m a n.
Proof. intros segs m n; induction n as [|n IH]; intros a; cbn; [reflexivity | now rewrite IH]. Qed.

Lemma Wd_bytes_at : forall segs m a,
  Wd (byte_at segs m) a
  = byte_at segs m a + 2 ^ 8 * byte_at segs m (a + 1) + 2 ^ 16 * byte_at segs m (a + 2) + 2 ^ 24 * byte_at segs m (a + 3).
Proof. intros. reflexivity. Qed.

Lemma land_1020_6 : forall y, Z.land (Z.shiftr y 6) 1020 = Z.land (Z.shiftr y 8) 255 * 4.
Proof. intros y. rewrite <- (land_1020_shiftr y 8) by lia. reflexivity. Qed.

Lemma land_1020_14 : forall y, Z.land (Z.shiftr y 14) 1020 = Z.land (Z.shiftr y 16) 255 * 4.
Proof. intros y. rewrite <- (land_1020_shiftr y 16) by lia. reflexivity. Qed.

Lemma crc_pre_machine : forall c, (Z.lxor c (-1)) mod two32 = crc_pre c.
Proof.
  intros c. unfold crc_pre. rewrite Z.lxor_m1_r. rewrite CkMathCrc.land_M32. reflexivity.
Qed.
