(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Btauto.
From Ltac2 Require Ltac2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Export X1gj X1il.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Export X0qm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Definition mem := word -> option byte.
Definition ubytes (bs : list byte) : list Z := map bv_unsigned bs.
Definition int31 (z : Z) : Prop := 0 <= z < 2^31.

Lemma ubytes_length : forall bs, length (ubytes bs) = length bs.
Proof. intros. apply length_map. Qed.
Lemma zlength_ubytes : forall bs, zlength (ubytes bs) = Z.of_nat (length bs).
Proof. intros. unfold zlength. rewrite ubytes_length. reflexivity. Qed.
Lemma ubytes_app : forall a b, ubytes (a ++ b) = ubytes a ++ ubytes b.
Proof. intros. apply map_app. Qed.
Lemma ubytes_firstn : forall n bs, ubytes (firstn n bs) = firstn n (ubytes bs).
Proof. intros. unfold ubytes. rewrite firstn_map. reflexivity. Qed.
Lemma ubytes_skipn : forall n bs, ubytes (skipn n bs) = skipn n (ubytes bs).
Proof. intros. unfold ubytes. rewrite skipn_map. reflexivity. Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia. Qed.

Lemma ubytes_ok : forall bs, Forall (fun b => 0 <= b < 256) (ubytes bs).
Proof. intros. apply bytes_ok_map. Qed.

Lemma znth_ubytes : forall bs i, 0 <= i -> (Z.to_nat i < length bs)%nat ->
znth (ubytes bs) i = bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
intros bs i Hi Hlt. unfold znth. destruct (Z.ltb_spec i 0); [lia|]. unfold ubytes.
rewrite <- (map_nth bv_unsigned). f_equal.
Qed.

Lemma znth_ubytes_range : forall bs i, 0 <= znth (ubytes bs) i < 256.
Proof.
intros. unfold znth. destruct (i <? 0); [lia|].
destruct (nth_in_or_default (Z.to_nat i) (ubytes bs) 0) as [H| ->]; [|lia].
pose proof (ubytes_ok bs) as F. rewrite Forall_forall in F. apply F. exact H.
Qed.

Lemma le_val_eq : forall l, X1r2.le_val l = X1bk.le_val l.
Proof. induction l; cbn; [reflexivity|]. rewrite IHl. reflexivity. Qed.

Lemma sx32_wz : forall v, int31 v -> sx32 (wz v) = wz v.
Proof.
intros v [H0 H1]. unfold sx32, wz. f_equal. rewrite Z_to_bv_unsigned.
unfold bv_swrap. change (bv_modulus 64) with (2^64). unfold bv_wrap.
change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
rewrite (Z.mod_small v (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sx32_lit : forall v, int31 v -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros. apply sx32_wz. assumption. Qed.

Lemma signed_lit_small : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
change (bv_modulus 64) with (2^64) in *. change (bv_half_modulus 64) with (2^63) in *.
rewrite Zplus_mod_idemp_l.
destruct (Z.lt_ge_cases z 0).
- replace ((z + 2 ^ 63) mod 2 ^ 64) with (z + 2^63); [lia|]. symmetry. apply Z.mod_small. lia.
- rewrite Z.mod_small by lia. lia.
Qed.

Lemma unsigned_wz : forall z, 0 <= z < 2^64 -> bv_unsigned (wz z) = z.
Proof. intros. unfold wz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia. Qed.

Lemma bytes_at_read1 : forall segs m A bs (i : Z) a,
bytes_at segs m A bs -> 0 <= i -> (Z.to_nat i < length bs)%nat -> a = wa (A + i) ->
ov_read_bytes segs m a 1 = Some [nth (Z.to_nat i) bs (Z_to_bv 8 0)].
Proof.
intros segs m A bs i a HB Hi Hlt ->.
eapply u8ro_read; [exact HB| | exact Hi| reflexivity].
apply nth_error_nth'. exact Hlt.
Qed.

Lemma unsigned_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros. unfold zxb. rewrite Z_to_bv_unsigned. apply bv_wrap_small. pose proof (byte_range b). unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia. Qed.

Lemma unsigned_zxb_nth : forall bs i, 0 <= i -> (Z.to_nat i < length bs)%nat ->
bv_unsigned (zxb (nth (Z.to_nat i) bs (Z_to_bv 8 0))) = znth (ubytes bs) i.
Proof. intros. rewrite unsigned_zxb. symmetry. apply znth_ubytes; assumption. Qed.

Lemma zxb_nth : forall bs i, 0 <= i -> (Z.to_nat i < length bs)%nat ->
zxb (nth (Z.to_nat i) bs (Z_to_bv 8 0)) = wz (znth (ubytes bs) i).
Proof. intros. unfold zxb, wz. rewrite znth_ubytes by assumption. reflexivity. Qed.

Definition sync_cells (D : Z) (sy : sync_st bptr) : list cell :=
[C8 (wz D); C4 (wz (sy_storage sy)); C4 (wz (sy_fill sy)); C4 (wz (sy_returned sy));
C4 (wz (sy_unsynced sy)); C4 (wz (sy_headerbytes sy)); C4 (wz (sy_bodybytes sy))].

Definition sync_fields_ok (sy : sync_st bptr) : Prop :=
int31 (sy_storage sy) /\ int31 (sy_fill sy) /\ int31 (sy_returned sy) /\ int31 (sy_unsynced sy) /\
int31 (sy_headerbytes sy) /\ int31 (sy_bodybytes sy).

Definition sync_data (m : mem) (D : Z) (sy : sync_st bptr) (bytes : list byte) : Prop :=
match sy_data sy with
| None => D = 0 /\ bytes = [] /\ sy_buf sy = [] /\ sy_storage sy = 0
| Some _ => 0 < D /\ u8arr rsegs m D bytes /\ Z.of_nat (length bytes) = sy_storage sy /\
firstn (length (sy_buf sy)) (ubytes bytes) = sy_buf sy /\ (length (sy_buf sy) <= length bytes)%nat
end.

Definition sync_rep (m : mem) (A D : Z) (sy : sync_st bptr) (bytes : list byte) : Prop :=
rw_cells rsegs m A (sync_cells D sy) /\ sync_fields_ok sy /\ sync_data m D sy bytes /\
(D + Z.of_nat (length bytes) <= A \/ A + 32 <= D).

Definition page_cells (D : Z) (og : page) : list cell :=
[C8 (wz (D + pg_hdr og)); C8 (wz (pg_header_len og)); C8 (wz (D + pg_hdr og + pg_header_len og)); C8 (wz (pg_body_len og))].

Definition packet_cells (Bd : Z) (op : packet) : list cell :=
[C8 (wz (Bd + pk_off op)); C8 (wz (pk_bytes op)); C8 (wz (pk_b_o_s op)); C8 (wz (pk_e_o_s op));
C8 (wz (pk_granulepos op)); C8 (wz (pk_packetno op))].

Definition stream_cells (Bd L G : Z) (hdr : list byte) (os : stream_st bptr) : list cell :=
[C8 (wz Bd); C8 (wz (os_body_storage os)); C8 (wz (os_body_fill os)); C8 (wz (os_body_returned os));
C8 (wz L); C8 (wz G); C8 (wz (os_lacing_storage os)); C8 (wz (os_lacing_fill os));
C8 (wz (os_lacing_packet os)); C8 (wz (os_lacing_returned os));
CB 284 hdr;
C4 (wz (os_header_fill os)); C4 (wz (os_e_o_s os)); C4 (wz (os_b_o_s os));
C8 (wz (os_serialno os)); C8 (wz (os_pageno os)); C8 (wz (os_packetno os)); C8 (wz (os_granulepos os))].

Lemma stream_cells_size : forall Bd L G hdr os, length hdr = 284%nat -> cells_size (stream_cells Bd L G hdr os) = 408%nat.
Proof. intros. reflexivity. Qed.
Lemma sync_cells_size : forall D sy, cells_size (sync_cells D sy) = 32%nat.
Proof. intros. reflexivity. Qed.

Lemma testbit_byte_high : forall b i, 0 <= b < 256 -> 8 <= i -> Z.testbit b i = false.
Proof. intros. apply (testbit_high_false b 8); lia. Qed.

Lemma bits_inj_upto : forall n x y, 0 <= n -> 0 <= x < 2^n -> 0 <= y < 2^n ->
(forall i, 0 <= i < n -> Z.testbit x i = Z.testbit y i) -> x = y.
Proof.
intros n x y Hn Hx Hy H. apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i n).
- apply H. lia.
- rewrite !(testbit_high_false _ n) by lia. reflexivity.
Qed.

Lemma forall_below_S : forall (P : Z -> Prop) n, 0 <= n ->
(forall i, 0 <= i < n -> P i) -> P n -> forall i, 0 <= i < n + 1 -> P i.
Proof. intros P n Hn H Hn' i Hi. destruct (Z.eq_dec i n) as [->|]; [exact Hn'|]. apply H. lia. Qed.
Lemma forall_below_0 : forall (P : Z -> Prop), forall i, 0 <= i < 0 -> P i.
Proof. intros P i Hi. lia. Qed.

Lemma word_eq_bits : forall x y,
(forall i, 0 <= i < 64 -> Z.testbit x i = Z.testbit y i) -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
apply (bits_inj_upto 64); [lia| apply Z.mod_pos_bound; lia| apply Z.mod_pos_bound; lia|].
intros i Hi. rewrite !Z.mod_pow2_bits_low by lia. apply H. exact Hi.
Qed.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma forall_zseq : forall (P : Z -> Prop) n, Forall P (zseq n) -> forall i, 0 <= i < Z.of_nat n -> P i.
Proof.
intros P n H i Hi. rewrite Forall_forall in H. apply H. unfold zseq. apply in_map_iff.
exists (Z.to_nat i). split; [lia|]. apply in_seq. lia.
Qed.
Lemma word_eq_bits64 : forall x y,
Forall (fun i => Z.testbit x i = Z.testbit y i) (zseq 64) -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply word_eq_bits. intros i Hi. exact (forall_zseq _ 64%nat H i Hi). Qed.

Lemma wz_s64 : forall v, wz (s64 v) = wz v.
Proof.
intros v. unfold wz, s64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma wz_s32_mod : forall v, wz (s32 v) = wz ((v + 2^31) mod 2^32 - 2^31).
Proof. intros. reflexivity. Qed.

Lemma zslice_S : forall off n l, 0 <= off -> off < zlength l ->
zslice off (Z.of_nat (S n)) l = znth l off :: zslice (off + 1) (Z.of_nat n) l.
Proof.
intros off n l Hoff Hlt. unfold zslice, ztake, zdrop, znth, zlength in *.
destruct (Z.ltb_spec off 0); [lia|].
rewrite !Nat2Z.id. replace (Z.to_nat (off + 1)) with (S (Z.to_nat off)) by lia.
assert (Hk : (Z.to_nat off < length l)%nat) by lia. clear Hlt.
revert Hk. generalize (Z.to_nat off) as k. intros k. revert l.
induction k as [|k IH]; intros l Hk.
- destruct l as [|x l]; [cbn in Hk; lia|]. reflexivity.
- destruct l as [|x l]; [cbn in Hk; lia|]. cbn [skipn nth]. apply IH. cbn in Hk. lia.
Qed.
Lemma zslice_0 : forall off l, zslice off 0 l = [].
Proof. intros. reflexivity. Qed.

Lemma testbit_mask64 : forall x i, 0 <= i < 64 -> Z.testbit (Z.land x 18446744073709551615) i = Z.testbit x i.
Proof. intros. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_pow2_bits_low. lia. Qed.
Lemma testbit_mask32 : forall x i, 0 <= i < 32 -> Z.testbit (Z.land x 4294967295) i = Z.testbit x i.
Proof. intros. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_pow2_bits_low. lia. Qed.
Lemma testbit_mask32_hi : forall x i, 32 <= i -> Z.testbit (Z.land x 4294967295) i = false.
Proof. intros. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_pow2_bits_high. lia. Qed.
Lemma testbit_mod64 : forall x i, 0 <= i < 64 -> Z.testbit (x mod 2^64) i = Z.testbit x i.
Proof. intros. apply Z.mod_pow2_bits_low. lia. Qed.
Lemma testbit_add256 : forall x y i, 0 <= x < 256 -> 0 <= i ->
Z.testbit (x + 256 * y) i = if i <? 8 then Z.testbit x i else Z.testbit y (i - 8).
Proof. intros. apply testbit_split; assumption. Qed.

Lemma testbit_eqm32 : forall x y i, 0 <= i < 32 -> x mod 2^32 = y mod 2^32 -> Z.testbit x i = Z.testbit y i.
Proof. intros x y i Hi E. rewrite <- (Z.mod_pow2_bits_low x 32 i) by lia. rewrite <- (Z.mod_pow2_bits_low y 32 i) by lia. rewrite E. reflexivity. Qed.

Lemma testbit_small_signed_hi : forall y i, -2^31 <= y < 2^31 -> 31 <= i -> Z.testbit y i = Z.testbit y 31.
Proof.
intros y i Hy Hi.
destruct (Z.lt_ge_cases y 0).
- assert (T : forall j, 31 <= j -> Z.testbit y j = true).
{ intros j Hj. apply Z.testbit_true; [lia|].
assert (H0 : y / 2^j = -1).
{ symmetry. apply Z.div_unique with (r := y + 2^j); [| lia].
left. assert (2^31 <= 2^j) by (apply Z.pow_le_mono_r; lia). lia. }
rewrite H0. reflexivity. }
rewrite !T by lia. reflexivity.
- rewrite !(Z.bits_above_log2 y) ; try lia.
+ destruct (Z.eq_dec y 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 31; [apply Z.log2_lt_pow2; lia| lia].
+ destruct (Z.eq_dec y 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 31; [apply Z.log2_lt_pow2; lia| lia].
Qed.

Lemma testbit_swrap32 : forall x i, 0 <= i ->
Z.testbit (bv_swrap 32 x) i = if i <? 32 then Z.testbit x i else Z.testbit x 31.
Proof.
intros x i Hi. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
set (y := (x + 2^31) mod 2^32 - 2^31).
assert (Hy : -2^31 <= y < 2^31) by (subst y; pose proof (Z.mod_pos_bound (x + 2^31) (2^32) ltac:(lia)); lia).
assert (E : y mod 2^32 = x mod 2^32).
{ subst y. rewrite Zminus_mod_idemp_l. replace (x + 2^31 - 2^31) with x by lia. reflexivity. }
destruct (Z.ltb_spec i 32).
- apply testbit_eqm32; [lia| exact E].
- rewrite (testbit_small_signed_hi y i) by lia. apply testbit_eqm32; [lia| exact E].
Qed.

Lemma testbit_wrap32 : forall x i, 0 <= i -> Z.testbit (bv_wrap 32 x) i = if i <? 32 then Z.testbit x i else false.
Proof.
intros. unfold bv_wrap. change (bv_modulus 32) with (2^32).
destruct (Z.ltb_spec i 32); [apply Z.mod_pow2_bits_low; lia| apply Z.mod_pow2_bits_high; lia].
Qed.
Lemma testbit_mod2p32 : forall x i, 0 <= i -> Z.testbit (x mod 4294967296) i = if i <? 32 then Z.testbit x i else false.
Proof. intros. change 4294967296 with (2^32). destruct (Z.ltb_spec i 32); [apply Z.mod_pow2_bits_low; lia| apply Z.mod_pow2_bits_high; lia]. Qed.
Lemma testbit_mod256 : forall x i, 0 <= i -> Z.testbit (x mod 256) i = if i <? 8 then Z.testbit x i else false.
Proof. intros. change 256 with (2^8). destruct (Z.ltb_spec i 8); [apply Z.mod_pow2_bits_low; lia| apply Z.mod_pow2_bits_high; lia]. Qed.
Lemma testbit_divp2 : forall x k i, 0 <= k -> 0 <= i -> Z.testbit (x / 2^k) i = Z.testbit x (i + k).
Proof. intros. apply Z.div_pow2_bits; lia. Qed.
Lemma testbit_mul4 : forall x i, 0 <= i -> Z.testbit (4 * x) i = if i <? 2 then false else Z.testbit x (i - 2).
Proof.
intros. replace (4 * x) with (x * 2^2) by lia.
destruct (Z.ltb_spec i 2); [apply Z.mul_pow2_bits_low; lia| rewrite Z.mul_pow2_bits by lia; reflexivity].
Qed.
Lemma testbit_mulp2 : forall x k i, 0 <= k -> 0 <= i -> Z.testbit (x * 2^k) i = if i <? k then false else Z.testbit x (i - k).
Proof. intros. destruct (Z.ltb_spec i k); [apply Z.mul_pow2_bits_low; lia| rewrite Z.mul_pow2_bits by lia; reflexivity]. Qed.

Lemma testbit_small_high : forall b n i, 0 <= b < n -> 0 <= i -> n <= 2^i -> Z.testbit b i = false.
Proof. intros b n i Hb Hi Hn. apply (testbit_high_false b i i); lia. Qed.

Lemma s32_swrap : forall x, s32 x = bv_swrap 32 x.
Proof. intros. reflexivity. Qed.

Ltac is_lit x := lazymatch x with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Definition tbit := Z.testbit.

Module GroundL2.
Import Ltac2.
Ltac2 is_ground (c : constr) : bool :=
let ok := Ref.ref true in
let rec go (t : constr) : unit :=
if Ref.get ok then
match Constr.Unsafe.kind t with
| Constr.Unsafe.Var _ => Ref.set ok false
| Constr.Unsafe.Rel _ => Ref.set ok false
| Constr.Unsafe.Evar _ _ => Ref.set ok false
| Constr.Unsafe.Meta _ => Ref.set ok false
| _ => Constr.Unsafe.iter go t
end
else () in
go c; Ref.get ok.
Ltac2 ground_goal () : unit :=
if is_ground (Control.goal ()) then () else Control.zero (Tactic_failure None).
Ltac2 ground_goal1 () : unit := Control.enter ground_goal.
End GroundL2.
Ltac ground_goal := ltac2:(GroundL2.ground_goal1 ()).
Ltac ground_prove :=
lazymatch goal with
| |- _ /\ _ => split; ground_prove
| |- _ \/ _ => first [ left; ground_prove | right; ground_prove ]
| |- (?a <= ?b)%Z => exact (proj1 (Z.leb_le a b) eq_refl)
| |- (?a < ?b)%Z => exact (proj1 (Z.ltb_lt a b) eq_refl)
| |- (?a >= ?b)%Z => apply Z.le_ge; exact (proj1 (Z.leb_le b a) eq_refl)
| |- (?a > ?b)%Z => apply Z.lt_gt; exact (proj1 (Z.ltb_lt b a) eq_refl)
| |- (?a <= ?b)%nat => exact (proj1 (Nat.leb_le a b) eq_refl)
| |- (?a < ?b)%nat => exact (proj1 (Nat.ltb_lt a b) eq_refl)
| |- True => exact I
end.

Ltac ground_or tac := tryif ground_goal then solve [ ground_prove ] else tac.
Ltac tb_lia := ground_or ltac:(lia).
Ltac byte_side := first [assumption | apply byte_range | apply znth_ubytes_range | tb_lia].
Ltac tb1 :=
match goal with
| |- context [Z.testbit ?a (?x - ?y)] =>
is_lit x; is_lit y; let v := eval vm_compute in (x - y) in change (Z.testbit a (x - y)) with (Z.testbit a v)
| |- context [Z.testbit ?a (?x + ?y)] =>
is_lit x; is_lit y; let v := eval vm_compute in (x + y) in change (Z.testbit a (x + y)) with (Z.testbit a v)
| |- context [?i <? ?j] =>
is_lit i; is_lit j; let v := eval vm_compute in (i <? j) in change (i <? j) with v; cbv iota
| |- context [Z.testbit ?x ?i] =>
is_lit x; let v := eval vm_compute in (Z.testbit x i) in change (Z.testbit x i) with v
| |- context [Z.testbit ?e ?i] =>
lazymatch e with
| Z.lor ?a ?b => rewrite (Z.lor_spec a b i)
| Z.land ?a 18446744073709551615 => rewrite (testbit_mask64 a i) by tb_lia
| Z.land ?a 4294967295 =>
first [rewrite (testbit_mask32 a i) by tb_lia | rewrite (testbit_mask32_hi a i) by tb_lia]
| Z.land ?a ?b => rewrite (Z.land_spec a b i)
| Z.lxor ?a ?b => rewrite (Z.lxor_spec a b i)
| Z.shiftl ?a ?k => first [rewrite (Z.shiftl_spec a k i) by tb_lia | rewrite (Z.testbit_neg_r (Z.shiftl a k) i) by tb_lia]
| Z.shiftr ?a ?k => rewrite (Z.shiftr_spec a k i) by tb_lia
| ?x mod 2^64 => rewrite (testbit_mod64 x i) by tb_lia
| ?x mod 4294967296 => rewrite (testbit_mod2p32 x i) by tb_lia; cbv iota
| ?x mod 256 => rewrite (testbit_mod256 x i) by tb_lia
| bv_wrap 32 ?x => rewrite (testbit_wrap32 x i) by tb_lia
| bv_swrap 32 ?x => rewrite (testbit_swrap32 x i) by tb_lia
| s32 ?x => rewrite (s32_swrap x), (testbit_swrap32 x i) by tb_lia
| ?x / 2 ^ ?k => rewrite (testbit_divp2 x k i) by tb_lia
| ?x / ?d => is_lit d; let k := eval vm_compute in (Z.log2 d) in
change (Z.testbit (x / d) i) with (Z.testbit (x / 2^k) i); rewrite (testbit_divp2 x k i) by tb_lia
| 4 * ?x => rewrite (testbit_mul4 x i) by tb_lia
| ?x * 2 ^ ?k => rewrite (testbit_mulp2 x k i) by tb_lia
| ?x * ?d => is_lit d; let k := eval vm_compute in (Z.log2 d) in
change (Z.testbit (x * d) i) with (Z.testbit (x * 2^k) i); rewrite (testbit_mulp2 x k i) by tb_lia
| ?x mod 2 ^ 32 => change (Z.testbit (x mod 2^32) i) with (Z.testbit (x mod 4294967296) i);
rewrite (testbit_mod2p32 x i) by tb_lia; cbv iota
| ?x + 256 * ?y => rewrite (testbit_add256 x y i) by byte_side
| _ => first [ rewrite (testbit_byte_high e i) by byte_side
| rewrite (testbit_small_high e _ i) by (first [eassumption | apply byte_range | apply znth_ubytes_range | tb_lia])
| rewrite (Z.testbit_neg_r e i) by tb_lia
| change (Z.testbit e i) with (tbit e i) ]
end
| |- _ => progress (rewrite ?andb_true_r, ?andb_true_l, ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l, ?orb_true_r, ?orb_true_l)
end.
Ltac tb := repeat tb1; unfold tbit.

Ltac tb_close :=
first [ reflexivity | btauto
| repeat match goal with |- context [Z.testbit ?b ?i] => destruct (Z.testbit b i); cbn [andb orb xorb negb]; try reflexivity end;
reflexivity ].

Ltac norm_lit_idx :=
repeat match goal with
| |- context [znth ?l (?a + ?b)] => let v := eval vm_compute in (a + b) in change (a + b) with v
| |- context [Z.to_nat (?a + ?b)] =>
lazymatch a with Z0 => idtac | Zpos _ => idtac end;
let v := eval vm_compute in (a + b) in change (a + b) with v
end.

Lemma zeq_bits_n : forall (n : nat) x y, 0 <= x < 2^(Z.of_nat n) -> 0 <= y < 2^(Z.of_nat n) ->
Forall (fun i => Z.testbit x i = Z.testbit y i) (zseq n) -> x = y.
Proof.
intros n x y Hx Hy H. apply (bits_inj_upto (Z.of_nat n)); [lia| exact Hx| exact Hy|].
intros i Hi. exact (forall_zseq _ n H i Hi).
Qed.
Ltac zeq_bits n :=
apply (zeq_bits_n n); [ | |
let l := eval vm_compute in (zseq n) in change (zseq n) with l;
repeat (apply Forall_cons; [tb; tb_close|]); try apply Forall_nil ].

Ltac name_bytes :=
repeat match goal with
| |- context [bv_unsigned (nth ?n ?l ?d)] =>
let b := fresh "b" in let Hb := fresh "Hb" in
pose proof (byte_range (nth n l d)) as Hb; set (b := bv_unsigned (nth n l d)) in *; clearbody b
end.

Ltac word_bits :=
name_bytes;
unfold wz; apply word_eq_bits64;
let l := eval vm_compute in (zseq 64) in change (zseq 64) with l;
repeat (apply Forall_cons; [tb; tb_close|]); try apply Forall_nil.

Lemma land_ones64 : forall x, Z.land x 18446744073709551615 = x mod 2^64.
Proof. intros. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones. lia. Qed.

Lemma swrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
intros x Hx. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
rewrite Z.mod_small by lia. lia.
Qed.

Lemma snez_byte_255 : forall b, 0 <= b < 256 ->
Z.b2z (0 <? Z.land (b + -255) 18446744073709551615) = (if b <? 255 then 1 else 0).
Proof.
intros b Hb. rewrite land_ones64.
destruct (Z.ltb_spec b 255).
- replace ((b + -255) mod 2^64) with (b + -255 + 2^64).
2:{ symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia. }
destruct (Z.ltb_spec 0 (b + -255 + 2^64)); cbn; lia.
- replace b with 255 by lia. reflexivity.
Qed.

Lemma firstn_S_snoc : forall {A} (l : list A) n d, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
induction l as [|x l IH]; intros [|n] d H; cbn in *; try lia; [reflexivity|].
rewrite (IH n d) by lia. reflexivity.
Qed.

Lemma zslice_snoc : forall off n l, 0 <= off -> 0 <= n -> off + n < zlength l ->
zslice off (n + 1) l = zslice off n l ++ [znth l (off + n)].
Proof.
intros off n l Ho Hn Hl. unfold zslice, ztake, zdrop, znth, zlength in *.
destruct (Z.ltb_spec (off + n) 0); [lia|].
replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
rewrite (firstn_S_snoc _ _ 0) by (rewrite length_skipn; lia).
rewrite nth_skipn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma count_lt255_app : forall l1 l2, count_lt255 (l1 ++ l2) = count_lt255 l1 + count_lt255 l2.
Proof. induction l1 as [|x l1 IH]; intros; [cbn [app count_lt255]; lia|]. cbn [app count_lt255]. rewrite IH. destruct (x <? 255); lia. Qed.

Lemma count_lt255_bound : forall l, 0 <= count_lt255 l <= zlength l.
Proof. induction l as [|x l IH]; [rewrite zlength_nil; cbn [count_lt255]; lia|]. cbn [count_lt255]. rewrite zlength_cons. destruct (x <? 255); lia. Qed.

Lemma rw_cells_recell : forall segs m A cs cs',
rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
rw_cells segs m A cs'.
Proof.
intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split|].
- exact Hwf'.
- rewrite Eb. exact Hb.
- rewrite Es. exact Hw.
Qed.

Lemma le8_zero_split : le8 (Z_to_bv 64 0) = le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0).
Proof. reflexivity. Qed.

Lemma u32ro_read : forall segs m A ws (i : Z) w a,
bytes_at segs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 4 * i) ->
ov_read_bytes segs m a 4 = Some (le4 w).
Proof.
intros segs m A ws i w a Hb Hn Hi ->.
first [ pose proof (u32s_split _ _ _ Hn) as sfP_; sf_destruct 6%nat sfP_ as pre post E Hlen Eu Hlu | sf_fb; destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu) ].
replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 4 Hb).
2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma zr_shiftl_small : forall a k, (0 <= k <= 63)%Z -> (0 <= a)%Z -> (a * 2^k < 2^64)%Z -> inr64 (Z.shiftl a k).
Proof. intros a k Hk Ha Hlt. unfold inr64. rewrite Z.shiftl_mul_pow2 by lia. nia. Qed.
Lemma zr_shiftl_byte : forall a k, (0 <= k <= 56)%Z -> (0 <= a < 256)%Z -> inr64 (Z.shiftl a k).
Proof.
intros a k Hk Ha. apply zr_shiftl_small; [lia| lia|].
apply Z.lt_le_trans with (256 * 2^k); [nia|]. change 256 with (2^8). rewrite <- Z.pow_add_r by lia.
apply Z.pow_le_mono_r; lia.
Qed.
Lemma zr_shiftl_u32 : forall a k, (0 <= k <= 32)%Z -> (0 <= a < 4294967296)%Z -> inr64 (Z.shiftl a k).
Proof.
intros a k Hk Ha. apply zr_shiftl_small; [lia| lia|].
apply Z.lt_le_trans with (4294967296 * 2^k); [nia|]. change 4294967296 with (2^32). rewrite <- Z.pow_add_r by lia.
apply Z.pow_le_mono_r; lia.
Qed.
Lemma zr_shiftl_land255 : forall a k, (0 <= k <= 56)%Z -> inr64 (Z.shiftl (Z.land a 255) k).
Proof.
intros a k Hk. apply zr_shiftl_byte; [exact Hk|].
rewrite Z.land_comm. replace (Z.land 255 a) with (Z.land 255 (a mod 2^64)).
- apply (X1bk.land_lt_pow2 255 (a mod 2^64) 8); [lia| apply Z.mod_pos_bound; lia].
- apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i 64); [rewrite Z.mod_pow2_bits_low by lia; reflexivity|].
rewrite (testbit_high_false 255 8) by lia. reflexivity.
Qed.
Lemma zr_swrap32_nonneg_byte : forall a, (0 <= a < 2^31)%Z -> inr64 (bv_swrap 32 a).
Proof. intros a Ha. unfold inr64. rewrite swrap32_small by lia. lia. Qed.

Ltac zrange ::=
lazymatch goal with
| |- inr64 ?e =>
lazymatch e with
| bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
| Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
| apply zr_land_l; [zrange | zrange_nonneg] | apply zr_land_r; [zrange_nonneg | zrange] ]
| Z.lor _ _ => apply zr_lor; [zrange | zrange]
| Z.lxor _ _ => apply zr_lxor; [zrange | zrange]
| Z.shiftr _ _ => apply zr_shiftr; [zrange | flia]
| Z.shiftl (Z.land _ 255) _ => apply zr_shiftl_land255; flia
| Z.shiftl _ _ => first [ apply zr_shiftl_byte; [flia | flia] | apply zr_shiftl_u32; [flia | flia] ]
| Z.modulo _ (2^64)%Z => apply zr_mod64
| Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
| Z.div _ _ => apply zr_div; [zrange | flia]
| Z.b2z _ => apply zr_b2z
| bv_swrap 32 _ => apply zr_swrap32_nonneg_byte; flia
| (if _ then _ else _) => apply zr_ite; [zrange | zrange]
| _ => first [ apply zr_lit; flia
| is_var e; progress (unfold e); zrange ]
end
| |- (0 <= ?e < _)%Z => change (inr64 e); zrange
end.
