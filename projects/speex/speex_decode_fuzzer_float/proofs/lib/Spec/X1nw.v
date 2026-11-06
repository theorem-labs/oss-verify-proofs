(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2.
Import ListNotations.
Open Scope Z_scope.

Definition CRC_POLY : Z := 0x04c11db7.
Definition M32 : Z := 2^32.

Fixpoint crc_bitsteps (n : nat) (r : Z) : Z :=
match n with
| O => r
| S n' => crc_bitsteps n' (if Z.testbit r 31 then Z.lxor ((r * 2) mod M32) CRC_POLY else (r * 2) mod M32)
end.
Definition crc_entry (i : Z) : Z := crc_bitsteps 8 (i * 2^24).

Definition iota256 : list Z := map Z.of_nat (seq 0 256).
Definition crc_table : list Z := map crc_entry iota256.

Definition crc_step_tbl (tbl : list Z) (crc b : Z) : Z :=
Z.lxor ((crc * 256) mod M32) (znth tbl (Z.lxor (crc / 2^24) b)).
Definition crc_step (crc b : Z) : Z := crc_step_tbl crc_table crc b.

Fixpoint crc_bytes_tbl (tbl : list Z) (crc : Z) (bs : list Z) : Z :=
match bs with
| [] => crc
| b :: bs' => crc_bytes_tbl tbl (crc_step_tbl tbl crc b) bs'
end.

Definition os_update_crc (crc : Z) (bs : list Z) : Z := crc_bytes_tbl crc_table crc bs.

Lemma os_update_crc_nil : forall c, os_update_crc c [] = c.
Proof. reflexivity. Qed.
Lemma os_update_crc_cons : forall c b bs, os_update_crc c (b :: bs) = os_update_crc (crc_step c b) bs.
Proof. reflexivity. Qed.
Lemma crc_bytes_tbl_app : forall tbl l1 c l2,
crc_bytes_tbl tbl c (l1 ++ l2) = crc_bytes_tbl tbl (crc_bytes_tbl tbl c l1) l2.
Proof. induction l1 as [|b l1 IH]; intros c l2; cbn; [reflexivity| apply IH]. Qed.
Lemma os_update_crc_app : forall c l1 l2, os_update_crc c (l1 ++ l2) = os_update_crc (os_update_crc c l1) l2.
Proof. intros. unfold os_update_crc. apply crc_bytes_tbl_app. Qed.

Definition crc_tables : list (list Z) :=
map (fun k => map (fun b => os_update_crc 0 (b :: zrepeat 0 (Z.of_nat k))) iota256) (seq 0 8).

Section Slice8.
Variable T : list (list Z).
Definition tk (k : nat) (b : Z) : Z := znth (nth k T []) b.

Definition slice8_block (crc b0 b1 b2 b3 b4 b5 b6 b7 : Z) : Z :=
let c := Z.lxor crc (b0 * 2^24 + b1 * 2^16 + b2 * 2^8 + b3) in
Z.lxor (Z.lxor (Z.lxor (Z.lxor (Z.lxor (Z.lxor (Z.lxor
(tk 7 (c / 2^24))
(tk 6 ((c / 2^16) mod 256)))
(tk 5 ((c / 2^8) mod 256)))
(tk 4 (c mod 256)))
(tk 3 b4))
(tk 2 b5))
(tk 1 b6))
(tk 0 b7).

Fixpoint os_update_crc_slice8 (crc : Z) (bs : list Z) {struct bs} : Z :=
match bs with
| b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
os_update_crc_slice8 (slice8_block crc b0 b1 b2 b3 b4 b5 b6 b7) rest
| _ => crc_bytes_tbl (nth 0 T []) crc bs
end.
End Slice8.

Definition byte_ok (b : Z) : Prop := 0 <= b < 256.
Definition reg_ok (c : Z) : Prop := 0 <= c < M32.

Lemma crc_table_length : length crc_table = 256%nat.
Proof. reflexivity. Qed.

Lemma nth_map' {A B} (f : A -> B) (l : list A) (d : A) (d' : B) (n : nat) :
(n < length l)%nat -> nth n (map f l) d' = f (nth n l d).
Proof. revert n; induction l as [|x l IH]; intros [|n] H; cbn in *; try lia; auto. apply IH. lia. Qed.

Lemma iota256_length : length iota256 = 256%nat.
Proof. reflexivity. Qed.

Lemma iota256_spec : forall i, (i < 256)%nat -> nth i iota256 0 = Z.of_nat i.
Proof.
intros i Hi. unfold iota256. rewrite (nth_map' Z.of_nat (seq 0 256) O 0 i) by (rewrite length_seq; exact Hi).
rewrite seq_nth by exact Hi. reflexivity.
Qed.

Lemma lxor_bound : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lxor a b < 2^n.
Proof.
intros a b n Ha Hb.
assert (Hn : 0 < n \/ n = 0 \/ n < 0) by lia. destruct Hn as [Hn|[Hn|Hn]];
[| subst n; change (2^0) with 1 in *; replace a with 0 by lia; replace b with 0 by lia; cbn; lia
| rewrite Z.pow_neg_r in Ha by lia; lia].
split; [apply Z.lxor_nonneg; lia|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [E|NE]; [rewrite E; lia|].
apply Z.log2_lt_pow2; [pose proof (Z.lxor_nonneg a b); lia|].
eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
- destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lxor_mod_pow2 : forall x y n, 0 <= n -> (Z.lxor x y) mod 2^n = Z.lxor (x mod 2^n) (y mod 2^n).
Proof.
intros x y n Hn. apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec.
destruct (Z.lt_ge_cases i n).
- rewrite !Z.mod_pow2_bits_low by lia. apply Z.lxor_spec.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma shl_lxor_mod : forall x y k n, 0 <= x -> 0 <= y -> 0 <= k -> 0 <= n ->
(Z.lxor x y * 2^k) mod 2^n = Z.lxor ((x * 2^k) mod 2^n) ((y * 2^k) mod 2^n).
Proof.
intros x y k n Hx Hy Hk Hn.
rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_lxor. apply lxor_mod_pow2. lia.
Qed.

Definition crc_bitstep (r : Z) : Z :=
if Z.testbit r 31 then Z.lxor ((r * 2) mod M32) CRC_POLY else (r * 2) mod M32.

Lemma crc_bitsteps_S : forall n r, crc_bitsteps (S n) r = crc_bitsteps n (crc_bitstep r).
Proof. reflexivity. Qed.

Lemma crc_bitstep_alt : forall r,
crc_bitstep r = Z.lxor ((r * 2) mod M32) (if Z.testbit r 31 then CRC_POLY else 0).
Proof. intros r. unfold crc_bitstep. destruct (Z.testbit r 31); [reflexivity| rewrite Z.lxor_0_r; reflexivity]. Qed.

Lemma crc_bitstep_ok : forall r, 0 <= r -> reg_ok (crc_bitstep r).
Proof.
intros r Hr. rewrite crc_bitstep_alt. unfold reg_ok, M32. apply lxor_bound.
- apply Z.mod_pos_bound. lia.
- destruct (Z.testbit r 31); unfold CRC_POLY; lia.
Qed.

Lemma crc_bitstep_lxor : forall x y, 0 <= x -> 0 <= y ->
crc_bitstep (Z.lxor x y) = Z.lxor (crc_bitstep x) (crc_bitstep y).
Proof.
intros x y Hx Hy. rewrite !crc_bitstep_alt.
unfold M32. replace (Z.lxor x y * 2) with (Z.lxor x y * 2^1) by ring. rewrite shl_lxor_mod by lia.
rewrite !Z.pow_1_r.
rewrite Z.lxor_spec.
set (u := (x * 2) mod 2^32). set (v := (y * 2) mod 2^32).
destruct (Z.testbit x 31), (Z.testbit y 31); cbn [xorb]; rewrite ?Z.lxor_0_r.
- rewrite (Z.lxor_comm v CRC_POLY). rewrite Z.lxor_assoc. rewrite <- (Z.lxor_assoc CRC_POLY). rewrite Z.lxor_nilpotent. rewrite Z.lxor_0_l. reflexivity.
- rewrite !Z.lxor_assoc. rewrite (Z.lxor_comm v CRC_POLY). reflexivity.
- rewrite !Z.lxor_assoc. reflexivity.
- reflexivity.
Qed.

Lemma crc_bitsteps_ok : forall n r, 0 <= r < M32 -> reg_ok (crc_bitsteps n r).
Proof.
induction n as [|n IH]; intros r Hr; [exact Hr|]. rewrite crc_bitsteps_S. apply IH. apply crc_bitstep_ok. lia.
Qed.

Lemma crc_bitsteps_lxor : forall n x y, 0 <= x -> 0 <= y ->
crc_bitsteps n (Z.lxor x y) = Z.lxor (crc_bitsteps n x) (crc_bitsteps n y).
Proof.
induction n as [|n IH]; intros x y Hx Hy; [reflexivity|].
rewrite !crc_bitsteps_S. rewrite crc_bitstep_lxor by assumption. apply IH; apply crc_bitstep_ok; assumption.
Qed.

Lemma crc_entry_lxor : forall a b, 0 <= a -> 0 <= b ->
crc_entry (Z.lxor a b) = Z.lxor (crc_entry a) (crc_entry b).
Proof.
intros a b Ha Hb. unfold crc_entry. rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_lxor.
apply crc_bitsteps_lxor; rewrite Z.shiftl_mul_pow2 by lia; lia.
Qed.

Lemma crc_entry_ok : forall i, 0 <= i < 256 -> reg_ok (crc_entry i).
Proof. intros i Hi. unfold crc_entry. apply crc_bitsteps_ok. unfold M32. lia. Qed.

Lemma znth_crc_table : forall i, 0 <= i < 256 -> znth crc_table i = crc_entry i.
Proof.
intros i Hi. unfold znth. destruct (Z.ltb_spec i 0); [lia|]. unfold crc_table.
rewrite (nth_map' crc_entry iota256 0 0 (Z.to_nat i)) by (rewrite iota256_length; lia).
rewrite iota256_spec by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma znth_crc_table_ok : forall i, 0 <= i < 256 -> reg_ok (znth crc_table i).
Proof. intros i Hi. rewrite znth_crc_table by exact Hi. apply crc_entry_ok. exact Hi. Qed.

Lemma crc_table_linear : forall a b, 0 <= a < 256 -> 0 <= b < 256 ->
znth crc_table (Z.lxor a b) = Z.lxor (znth crc_table a) (znth crc_table b).
Proof.
intros a b Ha Hb. rewrite !znth_crc_table; [| exact Hb | exact Ha | apply (lxor_bound a b 8); lia].
apply crc_entry_lxor; lia.
Qed.

Lemma crc_table_0 : znth crc_table 0 = 0.
Proof. reflexivity. Qed.

Lemma byte_hi : forall c, reg_ok c -> 0 <= c / 2^24 < 256.
Proof. intros c [H1 H2]. unfold M32 in H2. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. Qed.

Lemma crc_step_ok : forall c b, reg_ok c -> byte_ok b -> reg_ok (crc_step c b).
Proof.
intros c b Hc Hb. unfold crc_step, crc_step_tbl. unfold reg_ok, M32 in *.
apply lxor_bound; [split; [apply Z.mod_pos_bound|apply Z.mod_pos_bound]; lia|].
apply znth_crc_table_ok. apply lxor_bound with (n := 8); [apply byte_hi; unfold reg_ok, M32; lia| unfold byte_ok in Hb; lia].
Qed.

Lemma os_update_crc_ok : forall bs c, reg_ok c -> Forall byte_ok bs -> reg_ok (os_update_crc c bs).
Proof.
induction bs as [|b bs IH]; intros c Hc Hbs; [exact Hc|]. rewrite os_update_crc_cons.
inversion Hbs; subst. apply IH; [apply crc_step_ok|]; assumption.
Qed.

Lemma shl8_lxor : forall x y, 0 <= x -> 0 <= y ->
(Z.lxor x y * 256) mod M32 = Z.lxor ((x * 256) mod M32) ((y * 256) mod M32).
Proof. intros x y Hx Hy. unfold M32. change 256 with (2^8). apply shl_lxor_mod; lia. Qed.

Lemma shr24_lxor : forall x y, Z.lxor x y / 2^24 = Z.lxor (x / 2^24) (y / 2^24).
Proof. intros. rewrite <- !Z.shiftr_div_pow2 by lia. apply Z.shiftr_lxor. Qed.

Lemma crc_step_lxor : forall x y b, reg_ok x -> reg_ok y -> byte_ok b ->
crc_step (Z.lxor x y) b = Z.lxor (crc_step x b) (crc_step y 0).
Proof.
intros x y b Hx Hy Hb. unfold crc_step, crc_step_tbl.
rewrite shl8_lxor by (unfold reg_ok in *; lia). rewrite shr24_lxor.
rewrite Z.lxor_0_r.
replace (Z.lxor (Z.lxor (x / 2^24) (y / 2^24)) b) with (Z.lxor (Z.lxor (x / 2^24) b) (y / 2^24)).
2:{ rewrite !Z.lxor_assoc. f_equal. apply Z.lxor_comm. }
rewrite crc_table_linear; [| apply lxor_bound with (n:=8); [apply byte_hi; assumption| unfold byte_ok in Hb; lia] | apply byte_hi; assumption].

rewrite !Z.lxor_assoc. f_equal. rewrite <- !Z.lxor_assoc. f_equal. apply Z.lxor_comm.
Qed.

Lemma os_update_crc_lxor : forall l x y, reg_ok x -> reg_ok y -> Forall byte_ok l ->
os_update_crc (Z.lxor x y) l = Z.lxor (os_update_crc x l) (os_update_crc y (zrepeat 0 (zlength l))).
Proof.
induction l as [|b l IH]; intros x y Hx Hy Hl; [reflexivity|].
inversion Hl; subst. rewrite zlength_cons. unfold zrepeat. rewrite Z2Nat.inj_add by (pose proof (zlength_nonneg l); lia).
rewrite Nat.add_comm. cbn [Z.to_nat Pos.to_nat Nat.add repeat]. rewrite !os_update_crc_cons.
rewrite crc_step_lxor by assumption. fold (zrepeat 0 (zlength l)). apply IH; [apply crc_step_ok; auto| apply crc_step_ok; [auto| unfold byte_ok; lia] | assumption].
Qed.

Lemma crc_step_shift : forall x b, reg_ok x -> byte_ok b ->
crc_step x b = crc_step (Z.lxor x (b * 2^24)) 0.
Proof.
intros x b Hx Hb. unfold crc_step, crc_step_tbl. rewrite Z.lxor_0_r.
rewrite shr24_lxor. rewrite Z.div_mul by lia.
rewrite shl8_lxor by (unfold reg_ok, byte_ok in *; lia).
replace ((b * 2^24 * 256) mod M32) with 0.
2:{ unfold M32. replace (b * 2^24 * 256) with (b * 2^32) by ring. rewrite Z.mod_mul. reflexivity. lia. }
rewrite Z.lxor_0_r. reflexivity.
Qed.

Lemma crc_step_small : forall x, 0 <= x < 2^24 -> crc_step x 0 = x * 256.
Proof.
intros x Hx. unfold crc_step, crc_step_tbl. rewrite Z.div_small by lia. rewrite Z.lxor_0_l, crc_table_0, Z.lxor_0_r.
apply Z.mod_small. unfold M32. lia.
Qed.

Lemma os_update_crc_zero_nil : forall k, os_update_crc 0 (zrepeat 0 k) = 0.
Proof.
intros k. unfold zrepeat. induction (Z.to_nat k) as [|n IH]; [reflexivity|].
cbn [repeat]. rewrite os_update_crc_cons. rewrite crc_step_small by lia. exact IH.
Qed.

Definition Tk (k : nat) (b : Z) : Z := os_update_crc 0 (b :: zrepeat 0 (Z.of_nat k)).

Lemma crc_tables_spec : forall k b, (k < 8)%nat -> 0 <= b < 256 -> tk crc_tables k b = Tk k b.
Proof.
intros k b Hk Hb. unfold tk, crc_tables.
rewrite (nth_map' _ (seq 0 8) O [] k) by (rewrite length_seq; exact Hk).
rewrite seq_nth by exact Hk. cbn [Nat.add].
unfold znth. destruct (Z.ltb_spec b 0); [lia|].
rewrite (nth_map' _ iota256 0 0 (Z.to_nat b)) by (rewrite iota256_length; lia).
rewrite iota256_spec by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma nth0_crc_tables : nth 0 crc_tables [] = crc_table.
Proof.

unfold crc_tables. cbn [seq map nth Z.of_nat zrepeat Z.to_nat repeat].
unfold crc_table. apply map_ext_in. intros b Hb.
unfold os_update_crc, crc_bytes_tbl, crc_step_tbl. fold crc_table. rewrite Z.div_0_l by lia.
rewrite Z.mul_0_l. rewrite Z.mod_0_l by (unfold M32; lia). rewrite !Z.lxor_0_l.
assert (0 <= b < 256).
{ unfold iota256 in Hb. apply in_map_iff in Hb. destruct Hb as (n & <- & Hn). apply in_seq in Hn. lia. }
apply znth_crc_table. assumption.
Qed.

Lemma Tk_ok : forall k b, byte_ok b -> reg_ok (Tk k b).
Proof.
intros k b Hb. unfold Tk. apply os_update_crc_ok; [unfold reg_ok, M32; lia|].
constructor; [exact Hb|]. unfold zrepeat. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. unfold byte_ok. lia.
Qed.

Lemma testbit_hi24 : forall c i, 0 <= i -> Z.testbit (c / 2^24 * 2^24) i = ((24 <=? i) && Z.testbit c i)%bool.
Proof.
intros c i Hi. rewrite Z.mul_pow2_bits by lia.
destruct (Z.leb_spec 24 i).
- rewrite Z.div_pow2_bits by lia. cbn [andb]. f_equal. lia.
- rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma testbit_field : forall c k i, 0 <= k -> 0 <= i ->
Z.testbit ((c / 2^k) mod 2^8 * 2^k) i = ((k <=? i) && (i <? k + 8) && Z.testbit c i)%bool.
Proof.
intros c k i Hk Hi. rewrite Z.mul_pow2_bits by lia.
destruct (Z.leb_spec k i).
- rewrite Z.testbit_mod_pow2 by lia. rewrite Z.div_pow2_bits by lia. cbn [andb].
replace (i - k + k) with i by lia.
destruct (Z.ltb_spec (i - k) 8), (Z.ltb_spec i (k + 8)); cbn [andb]; auto; lia.
- rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma testbit_lo8 : forall c i, 0 <= i -> Z.testbit (c mod 2^8) i = ((i <? 8) && Z.testbit c i)%bool.
Proof. intros. rewrite Z.testbit_mod_pow2 by lia. reflexivity. Qed.

Lemma reg_bytes_lxor : forall c,
c = Z.lxor (Z.lxor (Z.lxor (c / 2^24 * 2^24) ((c / 2^16) mod 2^8 * 2^16)) ((c / 2^8) mod 2^8 * 2^8)) (c mod 2^8).
Proof.
intros c. apply Z.bits_inj'. intros i Hi.
rewrite !Z.lxor_spec, testbit_hi24, !testbit_field, testbit_lo8 by lia.
destruct (Z.leb_spec 24 i); destruct (Z.leb_spec 16 i); destruct (Z.ltb_spec i (16 + 8));
destruct (Z.leb_spec 8 i); destruct (Z.ltb_spec i (8 + 8)); destruct (Z.ltb_spec i 8); cbn [andb]; try lia;
destruct (Z.testbit c i); reflexivity.
Qed.

Lemma field_bounds : forall c, reg_ok c ->
byte_ok (c / 2^24) /\ byte_ok ((c / 2^16) mod 2^8) /\ byte_ok ((c / 2^8) mod 2^8) /\ byte_ok (c mod 2^8).
Proof.
intros c [H1 H2]. unfold byte_ok, M32 in *. change (2^8) with 256.
repeat split; try (apply Z.mod_pos_bound; lia).
- apply Z.div_pos; lia.
- apply Z.div_lt_upper_bound; lia.
Qed.

Lemma upd_small_zeros : forall k y, 0 <= y -> y * 2^(8 * Z.of_nat k) < M32 ->
os_update_crc y (zrepeat 0 (Z.of_nat k)) = y * 2^(8 * Z.of_nat k).
Proof.
induction k as [|k IH]; intros y Hy Hlt.
- unfold zrepeat. cbn [Z.of_nat Z.to_nat repeat Z.mul Z.pow Z.pow_pos Pos.iter]. rewrite os_update_crc_nil. lia.
- unfold zrepeat. rewrite Nat2Z.id. cbn [repeat]. rewrite os_update_crc_cons.
assert (Hp : 2^(8 * Z.of_nat (S k)) = 256 * 2^(8 * Z.of_nat k)).
{ rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia.
rewrite Z.pow_add_r by lia. reflexivity. }
rewrite Hp in Hlt.
assert (Hy24 : y < 2^24).
{ unfold M32 in Hlt. assert (0 < 2^(8 * Z.of_nat k)) by (apply Z.pow_pos_nonneg; lia). nia. }
rewrite crc_step_small by lia.
pose proof (IH (y * 256) ltac:(lia) ltac:(unfold M32 in *; nia)) as E.
unfold zrepeat in E. rewrite Nat2Z.id in E. rewrite E. rewrite Hp. ring.
Qed.

Lemma upd_small_zeros_nat : forall k y, 0 <= y -> y * 2^(8 * Z.of_nat k) < M32 ->
os_update_crc y (repeat 0 k) = y * 2^(8 * Z.of_nat k).
Proof. intros k y Hy Hlt. rewrite <- (upd_small_zeros k y Hy Hlt). unfold zrepeat. rewrite Nat2Z.id. reflexivity. Qed.

Lemma upd_zeros_absorb : forall k x y, reg_ok x -> 0 <= y -> y * 2^(8 * Z.of_nat k) < M32 ->
Z.lxor (os_update_crc x (zrepeat 0 (Z.of_nat k))) (y * 2^(8 * Z.of_nat k)) =
os_update_crc (Z.lxor x y) (zrepeat 0 (Z.of_nat k)).
Proof.
intros k x y Hx Hy Hlt.
assert (Hyok : reg_ok y).
{ unfold reg_ok. split; [lia|]. assert (0 < 2^(8 * Z.of_nat k)) by (apply Z.pow_pos_nonneg; lia). nia. }
rewrite os_update_crc_lxor; [| exact Hx | exact Hyok |].
2:{ unfold zrepeat. apply Forall_forall. intros b Hb. apply repeat_spec in Hb. subst. unfold byte_ok. lia. }
rewrite zlength_zrepeat by lia. rewrite (upd_small_zeros k y Hy Hlt). reflexivity.
Qed.

Lemma add_hi_lo_lxor : forall b v, 0 <= b -> 0 <= v < 2^24 -> b * 2^24 + v = Z.lxor (b * 2^24) v.
Proof.
intros b v Hb Hv. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.bits_0. destruct (Z.lt_ge_cases i 24).
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace v with (v mod 2^24) by (apply Z.mod_small; lia).
rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

Lemma fold1 : forall c b v, reg_ok c -> byte_ok b -> 0 <= v < 2^24 ->
crc_step (Z.lxor c (b * 2^24 + v)) 0 = Z.lxor (crc_step c b) (v * 256).
Proof.
intros c b v Hc Hb Hv. rewrite add_hi_lo_lxor by (unfold byte_ok in Hb; lia).
rewrite <- Z.lxor_assoc.
assert (HcB : reg_ok (Z.lxor c (b * 2^24))).
{ unfold reg_ok, M32. apply lxor_bound; unfold reg_ok, byte_ok, M32 in *; lia. }
rewrite crc_step_lxor; [| exact HcB | unfold reg_ok, M32; lia | unfold byte_ok; lia].
rewrite <- crc_step_shift by assumption. rewrite crc_step_small by lia. reflexivity.
Qed.

Lemma fold4 : forall c b0 b1 b2 b3 rest, reg_ok c -> byte_ok b0 -> byte_ok b1 -> byte_ok b2 -> byte_ok b3 ->
os_update_crc c (b0 :: b1 :: b2 :: b3 :: rest) =
os_update_crc (Z.lxor c (b0 * 2^24 + b1 * 2^16 + b2 * 2^8 + b3)) (0 :: 0 :: 0 :: 0 :: rest).
Proof.
intros c b0 b1 b2 b3 rest Hc H0 H1 H2 H3. unfold byte_ok in *.
rewrite !os_update_crc_cons.
replace (b0 * 2^24 + b1 * 2^16 + b2 * 2^8 + b3) with (b0 * 2^24 + (b1 * 2^16 + b2 * 2^8 + b3)) by ring.
rewrite fold1; [| exact Hc | unfold byte_ok; lia | lia].
replace ((b1 * 2^16 + b2 * 2^8 + b3) * 256) with (b1 * 2^24 + (b2 * 2^16 + b3 * 2^8)) by ring.
rewrite fold1; [| apply crc_step_ok; unfold byte_ok; auto; lia | unfold byte_ok; lia | lia].
replace ((b2 * 2^16 + b3 * 2^8) * 256) with (b2 * 2^24 + b3 * 2^16) by ring.
rewrite fold1; [| apply crc_step_ok; [apply crc_step_ok|]; unfold byte_ok; auto; lia | unfold byte_ok; lia | lia].
replace (b3 * 2^16 * 256) with (b3 * 2^24 + 0) by ring.
rewrite fold1; [| repeat (apply crc_step_ok); unfold reg_ok, byte_ok in *; auto; lia | unfold byte_ok; lia | lia].
rewrite Z.mul_0_l, Z.lxor_0_r. reflexivity.
Qed.

Lemma bytes_ok_zrepeat0 : forall n, Forall byte_ok (zrepeat 0 n).
Proof. intros. unfold zrepeat. apply Forall_forall. intros b Hb. apply repeat_spec in Hb. subst. unfold byte_ok. lia. Qed.

Lemma upd0_cons : forall b l, byte_ok b -> Forall byte_ok l ->
os_update_crc 0 (b :: l) = Z.lxor (Tk (length l) b) (os_update_crc 0 l).
Proof.
intros b l Hb Hl. rewrite os_update_crc_cons.
rewrite <- (Z.lxor_0_l (crc_step 0 b)).
assert (R0 : reg_ok 0) by (unfold reg_ok, M32; lia).
rewrite (os_update_crc_lxor l 0 (crc_step 0 b) R0 (crc_step_ok 0 b R0 Hb) Hl).
rewrite Z.lxor_comm. f_equal.
Qed.

Lemma upd0_zero_cons : forall l, os_update_crc 0 (0 :: l) = os_update_crc 0 l.
Proof. intros. rewrite os_update_crc_cons. rewrite crc_step_small by lia. reflexivity. Qed.

Lemma Tk_shifted : forall j k b, byte_ok b -> (j <= 3)%nat ->
os_update_crc (b * 2^(8 * Z.of_nat j)) (zrepeat 0 (Z.of_nat (3 - j) + (1 + Z.of_nat k))) = Tk k b.
Proof.
intros j k b Hb Hj. unfold byte_ok in Hb.
unfold zrepeat. rewrite Z2Nat.inj_add by lia. rewrite repeat_app, os_update_crc_app.
rewrite Nat2Z.id.
rewrite (upd_small_zeros_nat (3 - j) (b * 2^(8 * Z.of_nat j))); [| apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia] |].
2:{ unfold M32. rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
apply Z.lt_le_trans with (m := 256 * 2^(8 * Z.of_nat j + 8 * Z.of_nat (3 - j))); [|].
- apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; lia| lia].
- change 256 with (2^8). rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia.
replace (8 * Z.of_nat j + 8 * Z.of_nat (3 - j)) with 24 by lia.
rewrite Z2Nat.inj_add by lia. rewrite Nat2Z.id. change (Z.to_nat 1 + k)%nat with (S k). cbn [repeat].
rewrite os_update_crc_cons. rewrite <- (Z.lxor_0_l (b * 2^24)). rewrite <- crc_step_shift; [| unfold reg_ok, M32; lia | unfold byte_ok; lia].
unfold Tk. rewrite os_update_crc_cons. unfold zrepeat. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma reg_zeros8 : forall c, reg_ok c ->
os_update_crc c (zrepeat 0 8) =
Z.lxor (Z.lxor (Z.lxor (Tk 7 (c / 2^24)) (Tk 6 ((c / 2^16) mod 256))) (Tk 5 ((c / 2^8) mod 256))) (Tk 4 (c mod 256)).
Proof.
intros c Hc. change 256 with (2^8). pose proof (field_bounds c Hc) as (HA & HB & HC & HD).
rewrite (reg_bytes_lxor c) at 1.
set (A := c / 2^24) in *. set (B := (c / 2^16) mod 2^8) in *. set (C := (c / 2^8) mod 2^8) in *. set (D := c mod 2^8) in *.
unfold byte_ok in HA, HB, HC, HD.
assert (R1 : reg_ok (A * 2^24)) by (unfold reg_ok, M32; lia).
assert (R2 : reg_ok (B * 2^16)) by (unfold reg_ok, M32; lia).
assert (R3 : reg_ok (C * 2^8)) by (unfold reg_ok, M32; lia).
assert (R4 : reg_ok D) by (unfold reg_ok, M32; lia).
assert (R12 : reg_ok (Z.lxor (A * 2^24) (B * 2^16))) by (unfold reg_ok, M32 in *; apply lxor_bound; lia).
assert (R123 : reg_ok (Z.lxor (Z.lxor (A * 2^24) (B * 2^16)) (C * 2^8))) by (unfold reg_ok, M32 in *; apply lxor_bound; lia).
pose proof (bytes_ok_zrepeat0 8) as Z8.
rewrite (os_update_crc_lxor _ _ D R123 R4 Z8).
rewrite (os_update_crc_lxor _ _ (C * 2^8) R12 R3 Z8).
rewrite (os_update_crc_lxor _ _ (B * 2^16) R1 R2 Z8).
rewrite zlength_zrepeat by lia.
pose proof (Tk_shifted 3 7 A ltac:(unfold byte_ok; lia) ltac:(lia)) as E7.
pose proof (Tk_shifted 2 6 B ltac:(unfold byte_ok; lia) ltac:(lia)) as E6.
pose proof (Tk_shifted 1 5 C ltac:(unfold byte_ok; lia) ltac:(lia)) as E5.
pose proof (Tk_shifted 0 4 D ltac:(unfold byte_ok; lia) ltac:(lia)) as E4.
cbn [Z.of_nat Nat.sub Pos.of_succ_nat Pos.succ Z.add Z.mul Pos.add Pos.mul] in E7, E6, E5.
replace (Z.of_nat (3 - 0) + (1 + Z.of_nat 4)) with 8 in E4 by reflexivity.
rewrite Z.pow_0_r, Z.mul_1_r in E4.
rewrite E7, E6, E5, E4. reflexivity.
Qed.

Theorem os_update_crc_slice8_eq : forall bs crc, reg_ok crc -> Forall byte_ok bs ->
os_update_crc_slice8 crc_tables crc bs = os_update_crc crc bs.
Proof.
fix IH 1.
intros bs crc Hc Hbs.
destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 rest]]]]]]]].
1-8: cbn [os_update_crc_slice8]; rewrite nth0_crc_tables; unfold os_update_crc; reflexivity.
cbn [os_update_crc_slice8].
inversion_clear Hbs as [|x0 l0 H0 Hbs']. inversion_clear Hbs' as [|x1 l1 H1 Hbs'']. inversion_clear Hbs'' as [|x2 l2 H2 Hbs3].
inversion_clear Hbs3 as [|x3 l3 H3 Hbs4]. inversion_clear Hbs4 as [|x4 l4 H4 Hbs5]. inversion_clear Hbs5 as [|x5 l5 H5 Hbs6].
inversion_clear Hbs6 as [|x6 l6 H6 Hbs7]. inversion_clear Hbs7 as [|x7 l7 H7 Hrest].
assert (Hblk : slice8_block crc_tables crc b0 b1 b2 b3 b4 b5 b6 b7 = os_update_crc crc [b0;b1;b2;b3;b4;b5;b6;b7]).
2:{ rewrite Hblk. rewrite IH; [| apply os_update_crc_ok; [exact Hc| repeat (constructor; [assumption|]); constructor] | assumption].
rewrite <- os_update_crc_app. reflexivity. }
rewrite fold4 by assumption.
set (c' := Z.lxor crc (b0 * 2^24 + b1 * 2^16 + b2 * 2^8 + b3)).
assert (Hc' : reg_ok c').
{ unfold c', reg_ok, M32. apply lxor_bound; unfold reg_ok, byte_ok, M32 in *; lia. }

rewrite <- (Z.lxor_0_l c') at 1.
assert (Hl8 : Forall byte_ok [0;0;0;0;b4;b5;b6;b7]).
{ repeat (constructor; [first [assumption | unfold byte_ok; lia] |]). constructor. }
rewrite (os_update_crc_lxor [0;0;0;0;b4;b5;b6;b7] 0 c' ltac:(unfold reg_ok, M32; lia) Hc' Hl8).
change (zlength [0;0;0;0;b4;b5;b6;b7]) with 8.
rewrite !upd0_zero_cons.
assert (Hl3 : Forall byte_ok [b5;b6;b7]) by (repeat (constructor; [assumption|]); constructor).
assert (Hl2 : Forall byte_ok [b6;b7]) by (repeat (constructor; [assumption|]); constructor).
assert (Hl1 : Forall byte_ok [b7]) by (repeat (constructor; [assumption|]); constructor).
rewrite (upd0_cons b4 [b5;b6;b7] H4 Hl3), (upd0_cons b5 [b6;b7] H5 Hl2), (upd0_cons b6 [b7] H6 Hl1), (upd0_cons b7 [] H7 (Forall_nil _)).
cbn [length]. rewrite os_update_crc_nil, Z.lxor_0_r.
rewrite (reg_zeros8 c' Hc').
pose proof (field_bounds c' Hc') as (HA & _ & _ & _). unfold byte_ok in HA, H4, H5, H6, H7.
assert (HB : 0 <= (c' / 2^16) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (HC : 0 <= (c' / 2^8) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (HD : 0 <= c' mod 256 < 256) by (apply Z.mod_pos_bound; lia).
unfold slice8_block. cbv zeta. fold c'.
rewrite (crc_tables_spec 7 _ ltac:(lia) HA), (crc_tables_spec 6 _ ltac:(lia) HB), (crc_tables_spec 5 _ ltac:(lia) HC),
(crc_tables_spec 4 _ ltac:(lia) HD), (crc_tables_spec 3 _ ltac:(lia) H4), (crc_tables_spec 2 _ ltac:(lia) H5),
(crc_tables_spec 1 _ ltac:(lia) H6), (crc_tables_spec 0 _ ltac:(lia) H7).

rewrite (Z.lxor_comm (Z.lxor (Tk 3 b4) _)). rewrite !Z.lxor_assoc. reflexivity.
Qed.
