(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require MState Mem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.MState.PropExec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.MState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Mem.

Module Bytes.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require MState Mem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.MState.PropExec OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.MState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib.Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Fixpoint le_val (bs : list Z) : Z :=
  match bs with [] => 0 | b :: bs' => b + 256 * le_val bs' end.
Fixpoint ones (n : nat) : Z := match n with O => 0 | S n' => 1 + 256 * ones n' end.
Definition highs (n : nat) : Z := 128 * ones n.
Definition bytes_ok (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.

Lemma le_val_range : forall bs, bytes_ok bs -> 0 <= le_val bs < 256 ^ Z.of_nat (length bs).
Proof.
  induction bs as [|b bs IH]; intros H; cbn [le_val length]; [lia|].
  inversion H; subst. specialize (IH ltac:(assumption)).
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma split_mod : forall x y M, 0 <= x < 256 -> 0 < M -> (x + 256 * y) mod (256 * M) = x + 256 * (y mod M).
Proof.
  intros x y M Hx HM. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia.
  rewrite Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.

Lemma testbit_split : forall x y i, 0 <= x < 256 -> 0 <= i ->
  Z.testbit (x + 256 * y) i = if i <? 8 then Z.testbit x i else Z.testbit y (i - 8).
Proof.
  intros x y i Hx Hi. destruct (Z.ltb_spec0 i 8).
  - rewrite <- (Z.mod_pow2_bits_low _ 8) by lia. change (2^8) with 256.
    rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia. reflexivity.
  - replace i with ((i - 8) + 8) at 1 by lia. rewrite <- Z.div_pow2_bits by lia. change (2^8) with 256.
    rewrite (Z.mul_comm 256 y), Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.

Lemma land_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b -> 0 <= Z.land a b < 2^n.
Proof.
  intros a b n Ha Hb.
  assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  pose proof (Z.land_nonneg a b) as Hnn. split; [lia|].
  destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]. { apply Z.pow_pos_nonneg; lia. }
  destruct (Z.eq_dec a 0) as [->|Haz]. { rewrite Z.land_0_l. apply Z.pow_pos_nonneg; lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.land a b) n ltac:(lia))).
  pose proof (Z.log2_land a b ltac:(lia) Hb). assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma lor_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros a b n Ha Hb.
  assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  pose proof (Z.lor_nonneg a b) as Hnn. split; [lia|].
  destruct (Z.eq_dec a 0) as [->|]. { rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0) as [->|]. { rewrite Z.lor_0_r. lia. }
  assert (Hp : 0 < Z.lor a b). { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n Hp)). rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 ->
  Z.land (x + 256 * y) (x' + 256 * y') = Z.land x x' + 256 * Z.land y y'.
Proof.
  intros x y x' y' Hx Hx'.
  pose proof (land_lt_pow2 x x' 8 ltac:(cbn; lia) ltac:(lia)) as Hl. change (2^8) with 256 in Hl.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !testbit_split by lia.
  destruct (i <? 8); rewrite Z.land_spec; reflexivity.
Qed.

Lemma lor_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 ->
  Z.lor (x + 256 * y) (x' + 256 * y') = Z.lor x x' + 256 * Z.lor y y'.
Proof.
  intros x y x' y' Hx Hx'.
  pose proof (lor_lt_pow2 x x' 8 ltac:(cbn; lia) ltac:(cbn; lia)) as Hl. change (2^8) with 256 in Hl.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, !testbit_split by lia.
  destruct (i <? 8); rewrite Z.lor_spec; reflexivity.
Qed.

Lemma lnot_split : forall b w, Z.lnot (b + 256 * w) = (255 - b) + 256 * Z.lnot w.
Proof. intros. unfold Z.lnot. lia. Qed.

Lemma byte_fact1 : forall b, 1 <= b < 256 -> Z.land (Z.land (b - 1) (255 - b)) 128 = 0.
Proof.
  intros b Hb.
  assert (C : forallb (fun b => Z.land (Z.land (b - 1) (255 - b)) 128 =? 0) (map Z.of_nat (seq 1 255)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. apply Z.eqb_eq, C. apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.

Theorem haszero_iff : forall bs, bytes_ok bs ->
  let n := length bs in let w := le_val bs in
  Z.land (Z.land ((w - ones n) mod 256 ^ Z.of_nat n) (Z.lnot w)) (highs n) <> 0 <-> In 0 bs.
Proof.
  induction bs as [|b bs IH]; intros H; cbn [length le_val ones highs].
  - cbn. split; [|intros []]. intros C; apply C. reflexivity.
  - inversion H as [|b' bs' Hb Hbs]; subst. specialize (IH Hbs). cbn zeta in IH.
    unfold highs in *. cbn [ones].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (Z.pow_pos_nonneg 256 (Z.of_nat (length bs)) ltac:(lia) ltac:(lia)) as HM.
    rewrite lnot_split.
    replace (128 * (1 + 256 * ones (length bs))) with (128 + 256 * (128 * ones (length bs))) by lia.
    destruct (Z.eq_dec b 0) as [->|Hb0].
    + replace (0 + 256 * le_val bs - (1 + 256 * ones (length bs))) with (255 + 256 * (le_val bs - ones (length bs) - 1)) by lia.
      rewrite split_mod by lia. rewrite land_split by lia. change (Z.land 255 (255 - 0)) with 255.
      rewrite land_split by lia. change (Z.land 255 128) with 128.
      split; [intros; left; reflexivity| intros _]. lia.
    + replace (b + 256 * le_val bs - (1 + 256 * ones (length bs))) with ((b - 1) + 256 * (le_val bs - ones (length bs))) by lia.
      rewrite split_mod by lia.
      rewrite land_split by lia.
      rewrite land_split. 2:{ pose proof (land_lt_pow2 (b-1) (255-b) 8 ltac:(cbn; lia) ltac:(lia)). cbn in *. lia. }
      2:{ lia. }
      rewrite byte_fact1 by lia.
      split.
      * intros Hnz. right. apply IH. lia.
      * intros [Hz|Hin]; [lia|]. apply IH in Hin. lia.
Qed.


Definition ONES64b  : Z := 0x0101010101010101.
Definition HIGHS64b : Z := 0x8080808080808080.

Lemma ones_8 : ones 8 = ONES64b. Proof. reflexivity. Qed.
Lemma highs_8 : highs 8 = HIGHS64b. Proof. reflexivity. Qed.

Lemma testbit_high_false : forall x n i, 0 <= x < 2^n -> 0 <= n <= i -> Z.testbit x i = false.
Proof.
  intros x n i Hx Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with n; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma land_mod_pow2_r : forall a b n, 0 <= a < 2^n -> 0 <= n -> Z.land a (b mod 2^n) = Z.land a b.
Proof.
  intros a b n Ha Hn. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i n).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite (testbit_high_false a n i) by lia. reflexivity.
Qed.

Lemma lnot_mod64 : forall w, 0 <= w < 2^64 -> Z.lxor w 18446744073709551615 = (Z.lnot w) mod 2^64.
Proof.
  intros w Hw. change 18446744073709551615 with (Z.ones 64). rewrite <- Z.land_ones by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
    destruct (Z.eq_dec w 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Theorem haszero64_gcc : forall bs, bytes_ok bs -> length bs = 8%nat ->
  let w := le_val bs in
  Z.land (Z.land ((w + 18374403900871474943) mod 18446744073709551616) (Z.lxor w 18446744073709551615)) 9259542123273814144 = 0
  <-> ~ In 0 bs.
Proof.
  intros bs Hok Hlen w. change 18446744073709551616 with (2^64).
  pose proof (le_val_range bs Hok) as Hw. rewrite Hlen in Hw. change (256 ^ Z.of_nat 8) with (2^64) in Hw.
  pose proof (haszero_iff bs Hok) as HZ. rewrite Hlen in HZ. cbn zeta in HZ. fold w in HZ, Hw.
  change (256 ^ Z.of_nat 8) with (2^64) in HZ. rewrite ones_8, highs_8 in HZ. unfold ONES64b, HIGHS64b in HZ.
  replace ((w + 18374403900871474943) mod 2 ^ 64) with ((w - 72340172838076673) mod 2^64).
  2:{ replace (w + 18374403900871474943) with ((w - 72340172838076673) + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity. }
  rewrite lnot_mod64 by lia. rewrite land_mod_pow2_r by (try lia; apply Z.mod_pos_bound; lia).
  destruct HZ as [HZ1 HZ2]. split.
  - intros E I. apply HZ2 in I. apply I. exact E.
  - intros NI. match goal with |- ?x = 0 => destruct (Z.eq_dec x 0) as [E|NE] end; [assumption|].
    exfalso. apply NI. apply HZ1. exact NE.
Qed.

Lemma demorgan_highs : forall D w H, 0 <= D < 2^64 -> 0 <= w < 2^64 -> 0 <= H < 2^64 ->
  Z.land (Z.lor (Z.lxor D 18446744073709551615) w) H = H <-> Z.land (Z.land D (Z.lnot w)) H = 0.
Proof.
  intros D w H HD Hw HH. change 18446744073709551615 with (Z.ones 64).
  assert (HI : forall x, 0 <= x < 2^64 -> forall i, 64 <= i -> Z.testbit x i = false).
  { intros x Hx i Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia]. }
  split; intros E; apply Z.bits_inj'; intros i Hi.
  - rewrite Z.bits_0, !Z.land_spec, Z.lnot_spec by lia.
    apply (f_equal (fun x => Z.testbit x i)) in E. rewrite Z.land_spec, Z.lor_spec, Z.lxor_spec in E.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.ones_spec_low in E by lia.
      destruct (Z.testbit D i), (Z.testbit w i), (Z.testbit H i); cbn in *; congruence.
    + rewrite (HI D) by lia. reflexivity.
  - apply (f_equal (fun x => Z.testbit x i)) in E. rewrite Z.bits_0, !Z.land_spec, Z.lnot_spec in E by lia.
    rewrite Z.land_spec, Z.lor_spec, Z.lxor_spec.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.ones_spec_low by lia.
      destruct (Z.testbit D i), (Z.testbit w i), (Z.testbit H i); cbn in *; congruence.
    + rewrite (HI H) by lia. apply andb_false_r.
Qed.

Theorem haszero64_clang : forall bs, bytes_ok bs -> length bs = 8%nat ->
  let w := le_val bs in
  Z.land (Z.lor ((72340172838076672 - w) mod 18446744073709551616) w) 9259542123273814144 = 9259542123273814144
  <-> ~ In 0 bs.
Proof.
  intros bs Hok Hlen w. change 18446744073709551616 with (2^64).
  pose proof (le_val_range bs Hok) as Hw. rewrite Hlen in Hw. change (256 ^ Z.of_nat 8) with (2^64) in Hw.
  pose proof (haszero_iff bs Hok) as HZ. rewrite Hlen in HZ. cbn zeta in HZ. fold w in HZ, Hw.
  change (256 ^ Z.of_nat 8) with (2^64) in HZ. rewrite ones_8, highs_8 in HZ. unfold ONES64b, HIGHS64b in HZ.
  set (D := (w - 72340172838076673) mod 2 ^ 64) in HZ.
  assert (HD : 0 <= D < 2^64) by (apply Z.mod_pos_bound; lia).
  replace ((72340172838076672 - w) mod 2 ^ 64) with (Z.lxor D 18446744073709551615).
  2:{ rewrite lnot_mod64 by lia. unfold Z.lnot. subst D. Z.div_mod_to_equations. lia. }
  rewrite demorgan_highs by lia.
  destruct HZ as [HZ1 HZ2]. split.
  - intros E I. apply HZ2 in I. apply I. exact E.
  - intros NI. match goal with |- ?x = 0 => destruct (Z.eq_dec x 0) as [E|NE] end; [assumption|].
    exfalso. apply NI. apply HZ1. exact NE.
Qed.


Lemma lor_shiftl8_add : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (Z.shiftl y 8) = x + 256 * y.
Proof.
  intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
  rewrite <- Z.lxor_lor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
       replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
       destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
       rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
       destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia]. }
  symmetry. replace (256 * y) with (y * 256) by lia. apply Z.add_nocarry_lxor.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
  destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
  rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
  destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma bytes_ok_map : forall bs : list byte, bytes_ok (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
Qed.

Lemma bytes_le_to_Z_le_val : forall bs : list byte, bytes_le_to_Z bs = le_val (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z le_val map]; [reflexivity|].
  rewrite IH. apply lor_shiftl8_add.
  - pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
  - pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)). lia.
Qed.

Lemma load8_le_val : forall bs : list byte, length bs = 8%nat ->
  bv_unsigned (bv_extract 0 64 (le_bytes_to_word bs)) = le_val (map bv_unsigned bs).
Proof.
  intros bs Hlen. unfold le_bytes_to_word. rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
  rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr. rewrite length_map, Hlen in Hr.
  change (256 ^ Z.of_nat 8) with (2^64) in Hr.
  rewrite (bv_wrap_small 64 (le_val _)) by (change (bv_modulus 64) with (2^64); lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64); lia.
Qed.

Lemma In0_map_unsigned : forall bs : list byte, In 0 (map bv_unsigned bs) <-> In (Z_to_bv 8 0) bs.
Proof.
  intros bs. rewrite in_map_iff. split.
  - intros (b & Hb & Hin). replace (Z_to_bv 8 0) with b; [exact Hin|]. apply bv_eq. rewrite Hb. reflexivity.
  - intros Hin. exists (Z_to_bv 8 0). split; [reflexivity|exact Hin].
Qed.
End Bytes.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Inductive cell : Type :=
| C8 (v : word)
| C4 (v : word)
| C2 (v : word)
| C1 (b : byte)
| CB (n : nat) (bs : list byte).

Definition csize (c : cell) : nat :=
  match c with C8 _ => 8 | C4 _ => 4 | C2 _ => 2 | C1 _ => 1 | CB n _ => n end.
Definition cbytes (c : cell) : list byte :=
  match c with C8 v => le8 v | C4 v => le4 v | C2 v => le2 v | C1 b => [b] | CB _ bs => bs end.
Fixpoint cells_size (cs : list cell) : nat :=
  match cs with [] => 0 | c :: cs' => csize c + cells_size cs' end.
Fixpoint cells_bytes (cs : list cell) : list byte :=
  match cs with [] => [] | c :: cs' => cbytes c ++ cells_bytes cs' end.
Definition cell_wf (c : cell) : Prop := match c with CB n bs => length bs = n | _ => True end.
Fixpoint cells_wf (cs : list cell) : Prop :=
  match cs with [] => True | c :: cs' => cell_wf c /\ cells_wf cs' end.

Lemma cbytes_length : forall c, cell_wf c -> length (cbytes c) = csize c.
Proof.
  intros [v|v|v|b|n bs] H; cbn -[le8 le4 le2].
  - apply length_le8. - apply length_le4. - apply length_le2. - reflexivity. - exact H.
Qed.

Lemma cells_bytes_length : forall cs, cells_wf cs -> length (cells_bytes cs) = cells_size cs.
Proof.
  induction cs as [|c cs IH]; intros H; [reflexivity|].
  cbn [cells_bytes cells_size]. destruct H as [H1 H2]. rewrite app_length, cbytes_length, IH by assumption. reflexivity.
Qed.

Fixpoint cell_at (cs : list cell) (k : nat) : option cell :=
  match cs with
  | [] => None
  | c :: cs' => if Nat.eqb k 0 then Some c
                else if Nat.ltb k (csize c) then None
                else cell_at cs' (k - csize c)
  end.

Fixpoint cell_upd (cs : list cell) (k : nat) (c' : cell) : list cell :=
  match cs with
  | [] => []
  | c :: cs' => if Nat.eqb k 0 then c' :: cs'
                else c :: cell_upd cs' (k - csize c) c'
  end.

Lemma cells_wf_app : forall a b, cells_wf (a ++ b) <-> cells_wf a /\ cells_wf b.
Proof. induction a as [|c a IH]; intros b; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma cells_bytes_app : forall a b, cells_bytes (a ++ b) = cells_bytes a ++ cells_bytes b.
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.
Lemma cells_size_app : forall a b, cells_size (a ++ b) = (cells_size a + cells_size b)%nat.
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa. lia. Qed.

Lemma cell_at_split : forall cs k c c',
  cell_at cs k = Some c ->
  exists pre post, cs = pre ++ c :: post /\ cells_size pre = k /\ cell_upd cs k c' = pre ++ c' :: post.
Proof.
  induction cs as [|c0 cs IH]; intros k c c' H; [discriminate|].
  cbn [cell_at cell_upd] in *. destruct (Nat.eqb_spec k 0).
  - inversion H; subst. exists [], cs. repeat split; auto.
  - destruct (Nat.ltb_spec0 k (csize c0)); [discriminate|].
    destruct (IH _ _ c' H) as (pre & post & -> & Hsz & Hupd).
    exists (c0 :: pre), post. repeat split; auto.
    + cbn. lia.
    + cbn. rewrite Hupd. reflexivity.
Qed.

Lemma skipn_app_exact : forall {X} (a b : list X), skipn (length a) (a ++ b) = b.
Proof. intros X a b. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.
Lemma firstn_app_exact : forall {X} (a b : list X), firstn (length a) (a ++ b) = a.
Proof. intros X a b. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Section WithSegs.
Variable segs : list Segment.

Definition cells_at (m : word -> option byte) (A : Z) (cs : list cell) : Prop :=
  cells_wf cs /\ bytes_at segs m A (cells_bytes cs).

Lemma cells_at_read : forall m A cs k c,
  cells_at m A cs -> cell_at cs k = Some c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) (csize c) = Some (cbytes c).
Proof.
  intros m A cs k c [Hwf Hb] Hc.
  destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre [Hwc Hwpost]].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by assumption. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. destruct Hb as [Hb _].
  rewrite <- (cbytes_length c) by assumption.
  rewrite <- (Z.add_0_r (A + Z.of_nat k)). change 0%Z with (Z.of_nat 0).
  rewrite (bytes_at_ov_read segs _ _ _ 0 (length (cbytes c)) Hb) by lia.
  cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma cells_at_write : forall m A cs k c c',
  cells_at m A cs -> cell_at cs k = Some c -> csize c' = csize c -> cell_wf c' ->
  cells_at (write_to_mem m (wa (A + Z.of_nat k)) (cbytes c')) A (cell_upd cs k c').
Proof.
  intros m A cs k c c' [Hwf Hb] Hc Hsz Hwf'.
  destruct (cell_at_split _ _ _ c' Hc) as (pre & post & Ecs & Hszp & Hupd).
  rewrite Hupd. rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre [Hwc Hwpost]].
  split. { apply cells_wf_app. cbn. tauto. }
  rewrite cells_bytes_app in *. cbn [cells_bytes] in *.
  pose proof (cells_bytes_length pre Hwpre) as Lpre.
  pose proof (cbytes_length c Hwc) as Lc. pose proof (cbytes_length c' Hwf') as Lc'.
  replace (A + Z.of_nat k)%Z with (A + Z.of_nat (length (cells_bytes pre)))%Z by (rewrite Lpre, Hszp; reflexivity).
  pose proof (bytes_at_bound _ _ _ _ Hb) as HB. rewrite !app_length in HB.
  replace (cells_bytes pre ++ cbytes c' ++ cells_bytes post)
     with (upd_bytes (cells_bytes pre ++ cbytes c ++ cells_bytes post) (Z.to_nat (Z.of_nat (length (cells_bytes pre)))) (cbytes c')).
  - apply bytes_at_write_inside; [exact Hb| lia |]. rewrite !app_length. lia.
  - unfold upd_bytes. rewrite Nat2Z.id. rewrite firstn_app_exact. f_equal. f_equal.
    replace (length (cells_bytes pre) + length (cbytes c'))%nat with (length (cells_bytes pre ++ cbytes c)) by (rewrite app_length; lia).
    rewrite app_assoc. apply skipn_app_exact.
Qed.

Lemma cells_at_frame : forall m A cs (a : Z) bs,
  cells_at m A cs -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  cells_at (write_to_mem m (wa a) bs) A cs.
Proof.
  intros m A cs a bs [Hwf Hb] Ha Hl Hd. split; [assumption|].
  apply bytes_at_write_other; try assumption. rewrite cells_bytes_length by assumption. exact Hd.
Qed.

Lemma cells_at_bound : forall m A cs, cells_at m A cs -> (0 <= A /\ A + Z.of_nat (cells_size cs) <= 2^64)%Z.
Proof. intros m A cs [Hwf Hb]. rewrite <- cells_bytes_length by assumption. eapply bytes_at_bound; eauto. Qed.

Lemma cells_at_wf : forall m A cs, cells_at m A cs -> cells_wf cs.
Proof. intros m A cs [H _]; exact H. Qed.

End WithSegs.


Lemma CB3_bytes : forall k n (bs : list byte), (k + n <= length bs)%nat ->
  firstn k bs ++ firstn n (skipn k bs) ++ skipn (k + n) bs = bs.
Proof.
  intros k n bs H. rewrite <- (firstn_skipn k bs) at 4. f_equal.
  rewrite <- (firstn_skipn n (skipn k bs)) at 2. f_equal. rewrite skipn_skipn. f_equal. lia.
Qed.

Definition cb_pieces (k n sz : nat) (bs : list byte) : list cell :=
  (if Nat.eqb k 0 then [] else [CB k (firstn k bs)])
  ++ CB n (firstn n (skipn k bs))
  :: (if Nat.eqb (k + n) sz then [] else [CB (sz - k - n) (skipn (k + n) bs)]).

Lemma cb_pieces_props : forall k n sz bs, length bs = sz -> (k + n <= sz)%nat ->
  cells_wf (cb_pieces k n sz bs) /\ cells_bytes (cb_pieces k n sz bs) = bs /\ cells_size (cb_pieces k n sz bs) = sz.
Proof.
  intros k n sz bs Hl Hkn. unfold cb_pieces.
  destruct (Nat.eqb_spec k 0); destruct (Nat.eqb_spec (k + n) sz); subst; cbn -[firstn skipn Nat.sub];
  rewrite ?firstn_length, ?skipn_length, ?app_nil_r.
  - cbn [skipn]. repeat split; try lia. apply firstn_all2. lia.
  - cbn [skipn Nat.add]. repeat split; try lia. apply firstn_skipn.
  - repeat split; try lia. rewrite <- (firstn_skipn k bs) at 3. f_equal. apply firstn_all2. rewrite skipn_length. lia.
  - repeat split; try lia. apply CB3_bytes. lia.
Qed.

Fixpoint cb_split (cs : list cell) (k n : nat) : list cell :=
  match cs with
  | [] => []
  | c :: cs' =>
      if Nat.ltb k (csize c) then
        match c with
        | CB sz bs => if (Nat.eqb k 0 && Nat.eqb n sz)%bool then c :: cs' else cb_pieces k n sz bs ++ cs'
        | _ => c :: cs'
        end
      else c :: cb_split cs' (k - csize c) n
  end.

Fixpoint cb_split_ok (cs : list cell) (k n : nat) : bool :=
  match cs with
  | [] => true
  | c :: cs' =>
      if Nat.ltb k (csize c) then
        match c with
        | CB sz bs => Nat.leb (k + n) sz
        | _ => true
        end
      else cb_split_ok cs' (k - csize c) n
  end.

Lemma cb_split_props : forall cs k n,
  cells_wf cs -> cb_split_ok cs k n = true ->
  cells_wf (cb_split cs k n) /\ cells_bytes (cb_split cs k n) = cells_bytes cs /\ cells_size (cb_split cs k n) = cells_size cs.
Proof.
  induction cs as [|c cs IH]; intros k n Hwf Hok; [cbn; tauto|].
  cbn [cells_wf] in Hwf. destruct Hwf as [Hc Hcs].
  cbn [cb_split cb_split_ok] in *.
  destruct (Nat.ltb k (csize c)) eqn:LT.
  - destruct c as [v|v|v|b|sz bs]; try (cbn; tauto).
    cbn [cell_wf] in Hc. apply Nat.leb_le in Hok.
    destruct (Nat.eqb k 0 && Nat.eqb n sz)%bool; [cbn; tauto|].
    destruct (cb_pieces_props k n sz bs Hc Hok) as (A1 & A2 & A3).
    rewrite cells_bytes_app, cells_size_app, A2, A3. split; [|split; [reflexivity|cbn; lia]].
    apply cells_wf_app. cbn. tauto.
  - cbn. destruct (IH (k - csize c)%nat n Hcs Hok) as (A1 & A2 & A3). rewrite A2, A3. tauto.
Qed.

Lemma cells_at_cb_split : forall segs m A cs k n,
  cells_at segs m A cs -> cb_split_ok cs k n = true -> cells_at segs m A (cb_split cs k n).
Proof.
  intros segs m A cs k n [Hwf Hb] Hok. destruct (cb_split_props cs k n Hwf Hok) as (A1 & A2 & A3).
  split; [exact A1|]. rewrite A2. exact Hb.
Qed.

Lemma cells_size_cb_split : forall cs k n, cells_wf cs -> cb_split_ok cs k n = true ->
  cells_size (cb_split cs k n) = cells_size cs.
Proof. intros. eapply cb_split_props; eauto. Qed.
