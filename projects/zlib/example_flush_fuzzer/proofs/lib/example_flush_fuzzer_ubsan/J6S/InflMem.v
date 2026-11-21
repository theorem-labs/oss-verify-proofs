(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface InflateState.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.



Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Lemma shiftr_lor_shiftl : forall (b L : Z), (0 <= b < 2^8)%Z -> (0 <= L)%Z ->
  Z.shiftr (Z.lor b (Z.shiftl L 8)) 8 = L.
Proof.
  intros b L Hb HL. apply Z.bits_inj'. intros n Hn.
  rewrite Z.shiftr_spec by lia.
  rewrite Z.lor_spec.
  rewrite (Z_testbit_high 8 b (n + 8)) by lia.
  rewrite Z.shiftl_spec by lia.
  replace (n + 8 - 8)%Z with n by lia.
  reflexivity.
Qed.

Lemma mod_lor_shiftl : forall (b L : Z), (0 <= b < 2^8)%Z -> (0 <= L)%Z ->
  (Z.lor b (Z.shiftl L 8)) mod 2^8 = b.
Proof.
  intros b L Hb HL.
  rewrite <- Z.land_ones by lia.
  rewrite Z.land_lor_distr_l.
  rewrite !Z.land_ones by lia.
  rewrite (Z.mod_small b) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mod_mul by lia.
  apply Z.lor_0_r.
Qed.

Lemma Z_to_le_bytes_bytes_le : forall (L : list byte),
  Z_to_le_bytes (length L) (bytes_le_to_Z L) = L.
Proof.
  induction L as [|b L IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  assert (Hb : (0 <= bv_unsigned b < 2^8)%Z)
    by (pose proof (u8_range b); change (bv_modulus 8) with 256%Z in *; lia).
  assert (HL : (0 <= bytes_le_to_Z L)%Z) by apply bytes_le_to_Z_nonneg.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap8_mod.
    apply mod_lor_shiftl; assumption.
  - rewrite shiftr_lor_shiftl by assumption. exact IH.
Qed.


Lemma zalu_sll_small : forall a b, 0 <= a -> 0 <= b < 64 -> a * 2 ^ b < 2 ^ 64 ->
  zalu ALU_SLL a b = a * 2 ^ b.
Proof.
  intros a b Ha Hb Hab. unfold zalu. rewrite zw_sll, u_zw, (Z.mod_small b 64) by lia.
  apply Z.mod_small. split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia] | exact Hab].
Qed.

Lemma zalu_srl_small : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 64 ->
  zalu ALU_SRL a b = a / 2 ^ b.
Proof.
  intros a b Ha Hb. unfold zalu. rewrite zw_srl, u_zw, (Z.mod_small b 64), (Z.mod_small a) by lia.
  pose proof (Z.pow_pos_nonneg 2 b ltac:(lia) ltac:(lia)).
  apply Z.mod_small. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.


Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros n Hn. apply Z.pow_pos_nonneg; lia. Qed.

Lemma shiftr_lt_pow2 : forall h b n, 0 <= h < 2 ^ b -> 0 <= n <= b -> h / 2 ^ n < 2 ^ (b - n).
Proof.
  intros h b n Hh Hn. pose proof (pow2_pos n ltac:(lia)).
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (n + (b - n)) with b by lia. lia.
Qed.

Lemma pull1_lt : forall h b v, 0 <= h < 2 ^ b -> 0 <= b -> 0 <= v < 256 -> h + v * 2 ^ b < 2 ^ (b + 8).
Proof.
  intros h b v Hh Hb Hv. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  pose proof (pow2_pos b Hb). nia.
Qed.
Lemma pull2_lt : forall h b v0 v1, 0 <= h < 2 ^ b -> 0 <= b -> 0 <= v0 < 256 -> 0 <= v1 < 256 ->
  h + v0 * 2 ^ b + v1 * 2 ^ (b + 8) < 2 ^ (b + 16).
Proof.
  intros h b v0 v1 Hh Hb Hv0 Hv1.
  pose proof (pull1_lt h b v0 Hh Hb Hv0) as H1.
  pose proof (pull1_lt (h + v0 * 2 ^ b) (b + 8) v1) as H2.
  replace (b + 8 + 8) with (b + 16) in H2 by lia.
  apply H2; [|lia|lia]. pose proof (pow2_pos b Hb). nia.
Qed.


Lemma land_ones_mod : forall h n, 0 <= n -> Z.land h (2 ^ n - 1) = h mod 2 ^ n.
Proof.
  intros h n Hn. replace (2 ^ n - 1) with (Z.ones n) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  apply Z.land_ones. exact Hn.
Qed.
Lemma land_ones_range : forall h n, 0 <= n -> 0 <= Z.land h (2 ^ n - 1) < 2 ^ n.
Proof. intros h n Hn. rewrite land_ones_mod by lia. apply Z.mod_pos_bound. apply pow2_pos. lia. Qed.

Lemma zaluw_sll_m1 : forall e, 0 <= e < 32 -> zaluw ALU_SLL (-1) e = 2 ^ 64 - 2 ^ e.
Proof.
  intros e He. unfold zaluw. rewrite zw_sllw, u_zw, (Z.mod_small e 32) by lia.
  pose proof (Z.pow_le_mono_r 2 e 31 ltac:(lia) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) ltac:(lia)).
  rewrite szwrap32_small by (change (2 ^ 31) with 2147483648 in *; lia).
  replace (-1 * 2 ^ e) with (2 ^ 64 - 2 ^ e + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. change (2 ^ 31) with 2147483648 in *. change (2 ^ 64) with 18446744073709551616. lia.
Qed.


Lemma negmask_land : forall e h, 0 <= e < 32 -> 0 <= h < 2 ^ 64 ->
  Z.land (Z.lxor (zaluw ALU_SLL (-1) e) (-1)) h = h mod 2 ^ e.
Proof.
  intros e h He Hh. rewrite zaluw_sll_m1 by lia.
  pose proof (Z.pow_le_mono_r 2 e 31 ltac:(lia) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) ltac:(lia)).
  change (-1) with (Z.lnot 0). rewrite <- Z.lnot_lxor_r, Z.lxor_0_r.
  rewrite Z.land_comm, <- Z.ldiff_land.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.ldiff_spec, <- (Z.land_ones h e), Z.land_spec, Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i e).
  -
    replace (Z.testbit (2 ^ 64 - 2 ^ e) i) with false; [destruct (Z.testbit h i); reflexivity|].
    symmetry. replace (2 ^ 64 - 2 ^ e) with ((2 ^ (64 - e) - 1) * 2 ^ e) by (rewrite Z.mul_sub_distr_r, <- Z.pow_add_r by lia; replace (64 - e + e) with 64 by lia; lia).
    rewrite <- Z.shiftl_mul_pow2 by lia. apply Z.shiftl_spec_low. lia.
  - destruct (Z.ltb_spec i 64).
    + replace (Z.testbit (2 ^ 64 - 2 ^ e) i) with true; [destruct (Z.testbit h i); reflexivity|].
      symmetry. replace (2 ^ 64 - 2 ^ e) with ((2 ^ (64 - e) - 1) * 2 ^ e) by (rewrite Z.mul_sub_distr_r, <- Z.pow_add_r by lia; replace (64 - e + e) with 64 by lia; lia).
      rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec_high by lia.
      replace (2 ^ (64 - e) - 1) with (Z.ones (64 - e)) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
      rewrite Z.testbit_ones_nonneg by lia. apply Z.ltb_lt. lia.
    +
      replace (Z.testbit h i) with false; [reflexivity|].
      symmetry. apply Z.bits_above_log2; [lia|].
      assert (Z.log2 h < 64); [|lia]. destruct (Z.eq_dec h 0) as [->|]; [cbn; lia|].
      apply Z.log2_lt_pow2; lia.
Qed.


Lemma code_op_eq : forall v, code_op v = v mod 256.
Proof. intros v. unfold code_op. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma code_bits_eq : forall v, code_bits v = (v / 256) mod 256.
Proof.
  intros v. unfold code_bits. change 255 with (Z.ones 8). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma code_val_eq : forall v, code_val v = (v / 65536) mod 65536.
Proof.
  intros v. unfold code_val. change 65535 with (Z.ones 16). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma code_op_range : forall v, 0 <= code_op v < 256.
Proof. intros v. rewrite code_op_eq. apply Z.mod_pos_bound. lia. Qed.
Lemma code_bits_range : forall v, 0 <= code_bits v < 256.
Proof. intros v. rewrite code_bits_eq. apply Z.mod_pos_bound. lia. Qed.
Lemma code_val_range : forall v, 0 <= code_val v < 65536.
Proof. intros v. rewrite code_val_eq. apply Z.mod_pos_bound. lia. Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma code_read_op : forall m (A : Z) v,
  cell segs m A 4 v ->
  exists bs, rdn segs m (zw A) 1 = Some bs /\ bytes_le_to_Z bs = code_op v.
Proof.
  intros m A v Hc. unfold cell in Hc.
  exists (firstn 1 (Z_to_le_bytes 4 v)). split.
  - exact (rdn_firstn segs m 4 (zw A) _ 1 Hc ltac:(lia)).
  - rewrite firstn_Z_to_le_bytes by lia. rewrite bytes_le_to_Z_of_Z, code_op_eq. reflexivity.
Qed.

Lemma code_read_bits : forall m (A : Z) v,
  cell segs m A 4 v ->
  exists bs, rdn segs m (zw (A + 1)) 1 = Some bs /\ bytes_le_to_Z bs = code_bits v.
Proof.
  intros m A v Hc. unfold cell in Hc.
  exists (firstn 1 (skipn 1 (Z_to_le_bytes 4 v))). split.
  - change 1 with (Z.of_nat 1) at 1. rewrite zw_add_nat. exact (rdn_sub segs 1 4 (zw A) m _ 1 Hc ltac:(lia)).
  - rewrite skipn_Z_to_le_bytes, firstn_Z_to_le_bytes by lia. rewrite bytes_le_to_Z_of_Z, code_bits_eq.
    change (2 ^ (8 * Z.of_nat 1)) with 256. reflexivity.
Qed.

Lemma code_read_val : forall m (A : Z) v,
  cell segs m A 4 v ->
  exists bs, rdn segs m (zw (A + 2)) 2 = Some bs /\ bytes_le_to_Z bs = code_val v.
Proof.
  intros m A v Hc. unfold cell in Hc.
  exists (firstn 2 (skipn 2 (Z_to_le_bytes 4 v))). split.
  - change 2 with (Z.of_nat 2) at 1. rewrite zw_add_nat. exact (rdn_sub segs 2 4 (zw A) m _ 2 Hc ltac:(lia)).
  - rewrite skipn_Z_to_le_bytes, firstn_Z_to_le_bytes by lia. rewrite bytes_le_to_Z_of_Z, code_val_eq.
    change (2 ^ (8 * Z.of_nat 2)) with 65536. reflexivity.
Qed.

Lemma ctab_read_op : forall m A n f i a,
  cells segs m A 4 4 n f -> 0 <= i < n -> a = A + 4 * i ->
  exists bs, rdn segs m (zw a) 1 = Some bs /\ bytes_le_to_Z bs = code_op (f i).
Proof. intros m A n f i a Hc Hi ->. apply code_read_op. exact (Hc i Hi). Qed.
Lemma ctab_read_bits : forall m A n f i a,
  cells segs m A 4 4 n f -> 0 <= i < n -> a = A + 4 * i + 1 ->
  exists bs, rdn segs m (zw a) 1 = Some bs /\ bytes_le_to_Z bs = code_bits (f i).
Proof. intros m A n f i a Hc Hi ->. apply code_read_bits. exact (Hc i Hi). Qed.
Lemma ctab_read_val : forall m A n f i a,
  cells segs m A 4 4 n f -> 0 <= i < n -> a = A + 4 * i + 2 ->
  exists bs, rdn segs m (zw a) 2 = Some bs /\ bytes_le_to_Z bs = code_val (f i).
Proof. intros m A n f i a Hc Hi ->. apply code_read_val. exact (Hc i Hi). Qed.

Lemma cells_shift : forall m A (w : nat) n f k,
  cells segs m A (Z.of_nat w) w n f -> 0 <= k <= n ->
  cells segs m (A + Z.of_nat w * k) (Z.of_nat w) w (n - k) (fun i => f (k + i)).
Proof.
  intros m A w n f k Hc Hk i Hi. replace (A + Z.of_nat w * k + Z.of_nat w * i) with (A + Z.of_nat w * (k + i)) by lia.
  apply Hc. lia.
Qed.


Definition ctab_byte (f : Z -> Z) (j : Z) : byte := Z_to_bv 8 (Z.shiftr (f (j / 4)) (8 * (j mod 4))).

Lemma rom_code_cells : forall A f (n : nat) mem,
  chk_rom segs A (ctab_byte f) (4 * n) = true ->
  (forall x : word, A <= bv_unsigned x < A + 4 * Z.of_nat n -> mem x = None) ->
  0 <= A -> A + 4 * Z.of_nat n < 2 ^ 64 ->
  cells segs mem A 4 4 (Z.of_nat n) f.
Proof.
  intros A f n mem Hchk Hnone HA HAn i Hi. unfold cell.
  assert (R : forall k, 0 <= k < 4 -> seg_rom segs (zw (A + 4 * i + k)) = Some (Z_to_bv 8 (Z.shiftr (f i) (8 * k)))).
  { intros k Hk. replace (A + 4 * i + k) with (A + (4 * i + k)) by lia.
    unfold zw. rewrite (chk_rom_sound segs A (ctab_byte f) (4 * n) (4 * i + k) Hchk) by lia.
    unfold ctab_byte. f_equal. f_equal.
    replace ((4 * i + k) / 4) with i by (rewrite Z.mul_comm, Z.div_add_l by lia; rewrite Z.div_small by lia; lia).
    replace ((4 * i + k) mod 4) with k by (rewrite Z.add_comm, Z.mul_comm, Z.mod_add, Z.mod_small by lia; lia).
    reflexivity. }
  assert (N : forall k, 0 <= k < 4 -> mem (zw (A + 4 * i + k)) = None).
  { intros k Hk. apply Hnone. rewrite u_zw_small; lia. }
  assert (E1 : forall k, (zw (A + 4 * i + k) + 1)%bv = zw (A + 4 * i + (k + 1))).
  { intros k. rewrite word1_nat. replace (A + 4 * i + (k + 1)) with (A + 4 * i + k + Z.of_nat 1) by lia.
    rewrite zw_add_nat. reflexivity. }
  replace (zw (A + 4 * i)) with (zw (A + 4 * i + 0)) by (f_equal; lia).
  cbn [rdn Z_to_le_bytes].
  rewrite (N 0), (R 0) by lia. rewrite (E1 0). rewrite (N (0 + 1)), (R (0 + 1)) by lia. rewrite (E1 (0 + 1)).
  rewrite (N (0 + 1 + 1)), (R (0 + 1 + 1)) by lia. rewrite (E1 (0 + 1 + 1)).
  rewrite (N (0 + 1 + 1 + 1)), (R (0 + 1 + 1 + 1)) by lia.
  rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Z.mul Pos.add Pos.mul]. rewrite Z.shiftr_0_r. reflexivity.
Qed.



Fixpoint cbytes (f : Z -> Z) (s : Z) (n : nat) : list byte :=
  match n with
  | O => []
  | S n' => Z_to_bv 8 (f s) :: cbytes f (s + 1) n'
  end.

Lemma cbytes_length : forall f s n, length (cbytes f s n) = n.
Proof. intros f s n. revert s. induction n as [|n IH]; intros s; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma cbytes_nth : forall f n k s, (k < n)%nat -> nth k (cbytes f s n) (Z_to_bv 8 0) = Z_to_bv 8 (f (s + Z.of_nat k)).
Proof.
  intros f n. induction n as [|n IH]; intros k s Hk; [lia|].
  destruct k as [|k]; cbn [cbytes nth]; [f_equal; f_equal; lia|].
  rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma cells_rdn_bytes : forall m P N f s n,
  cells segs m P 1 1 N f -> 0 <= s -> s + Z.of_nat n <= N -> 0 <= P -> P + N < 2 ^ 64 ->
  rdn segs m (zw (P + s)) n = Some (cbytes f s n).
Proof.
  intros m P N f s n Hc. revert s. induction n as [|n IH]; intros s Hs Hn HP HPN; [reflexivity|].
  pose proof (Hc s ltac:(lia)) as H1. unfold cell in H1. replace (P + 1 * s) with (P + s) in H1 by lia.
  cbn [rdn Z_to_le_bytes] in H1. cbn [rdn cbytes].
  destruct (match m (zw (P + s)) with Some b => Some b | None => seg_rom segs (zw (P + s)) end) as [b|]; [|discriminate].
  injection H1 as ->.
  replace (zw (P + s) + 1)%bv with (zw (P + (s + 1))) by (rewrite word1_nat; replace (P + (s + 1)) with (P + s + Z.of_nat 1) by lia; rewrite zw_add_nat; reflexivity).
  rewrite IH by lia. reflexivity.
Qed.





End WithSegs.



Definition tab_byte (a : arr) (j : Z) : byte :=
  Z_to_bv 8 (if Z.even j then arr_get a (j / 2) mod 256 else arr_get a (j / 2) / 256).

Definition tab_u16 (a : arr) (n : nat) : bool :=
  forallb (fun j => (0 <=? arr_get a (Z.of_nat j)) && (arr_get a (Z.of_nat j) <? 65536)) (seq 0 n).

Lemma tab_u16_sound : forall a n i, tab_u16 a n = true -> 0 <= i < Z.of_nat n -> 0 <= arr_get a i < 65536.
Proof.
  intros a n i H Hi. unfold tab_u16 in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Section Rod16.
Variable segs : list Segment.

Lemma tab_byte_even : forall a i, 0 <= i -> tab_byte a (2 * i) = Z_to_bv 8 (arr_get a i mod 256).
Proof.
  intros a i Hi. unfold tab_byte. rewrite Z.even_mul. cbn [Z.even orb].
  rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Lemma tab_byte_odd : forall a i, 0 <= i -> tab_byte a (2 * i + 1) = Z_to_bv 8 (arr_get a i / 256).
Proof.
  intros a i Hi. unfold tab_byte. rewrite Z.even_add, Z.even_mul. cbn [Z.even orb xorb Bool.eqb negb].
  replace ((2 * i + 1) / 2) with i by (rewrite Z.mul_comm, Z.div_add_l by lia; change (1 / 2) with 0; lia).
  reflexivity.
Qed.

Lemma tab16_cell : forall A a (n : nat) mem i,
  chk_rom segs A (tab_byte a) (2 * n) = true -> tab_u16 a n = true ->
  (forall x : word, A <= bv_unsigned x < A + 2 * Z.of_nat n -> mem x = None) ->
  0 <= i < Z.of_nat n -> 0 <= A -> A + 2 * Z.of_nat n < 2 ^ 64 ->
  cell segs mem (A + 2 * i) 2 (arr_get a i).
Proof.
  intros A a n mem i Hchk Hu Hnone Hi HA HAn.
  pose proof (tab_u16_sound a n i Hu Hi) as Hv.
  unfold cell. cbn [rdn Z_to_le_bytes].
  rewrite (Hnone (zw (A + 2 * i))) by (rewrite u_zw_small; lia).
  replace (zw (A + 2 * i)) with (Z_to_bv 64 (A + 2 * i)) by reflexivity.
  rewrite (chk_rom_sound _ _ _ _ (2 * i) Hchk) by lia.
  replace (Z_to_bv 64 (A + 2 * i) + 1)%bv with (zw (A + (2 * i + 1)))
    by (rewrite word1_nat; change (Z_to_bv 64 (A + 2 * i)) with (zw (A + 2 * i));
        rewrite <- (zw_add_nat (A + 2 * i) 1); f_equal; lia).
  rewrite (Hnone (zw (A + (2 * i + 1)))) by (rewrite u_zw_small; lia).
  replace (zw (A + (2 * i + 1))) with (Z_to_bv 64 (A + (2 * i + 1))) by reflexivity.
  rewrite (chk_rom_sound _ _ _ _ (2 * i + 1) Hchk) by lia.
  rewrite tab_byte_even, tab_byte_odd by lia.
  do 2 f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
  - f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. reflexivity.
Qed.

Lemma tab16_cells : forall A a (n : nat) mem,
  chk_rom segs A (tab_byte a) (2 * n) = true -> tab_u16 a n = true ->
  (forall x : word, A <= bv_unsigned x < A + 2 * Z.of_nat n -> mem x = None) ->
  0 <= A -> A + 2 * Z.of_nat n < 2 ^ 64 ->
  cells segs mem A 2 2 (Z.of_nat n) (arr_get a).
Proof. intros A a n mem Hchk Hu Hnone HA HAn i Hi. apply (tab16_cell A a n); assumption. Qed.
End Rod16.
End FXG.
