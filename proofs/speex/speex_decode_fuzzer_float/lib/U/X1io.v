(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ii.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nw X1qz X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition crc_entries : list Z := concat crc_tables.
Definition crc_tbl_bytes : list byte := u32s (map wz crc_entries).

Lemma crc_entries_length : length crc_entries = 2048%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma crc_tbl_bytes_eq : crc_tbl_bytes = u32s (map wz crc_entries).
Proof. reflexivity. Qed.
Lemma crc_tbl_bytes_length : length crc_tbl_bytes = 8192%nat.
Proof. unfold crc_tbl_bytes. rewrite u32s_length, length_map, crc_entries_length. reflexivity. Qed.
Lemma crc_tbl_ro : ro_bytes_b rsegs A_crc_lookup crc_tbl_bytes = true.
Proof. vm_compute. reflexivity. Qed.

Lemma crc_tbl_bytes_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_crc_lookup crc_tbl_bytes.
Proof.
intros m MI. pose proof (ro_cells_image rsegs m A_crc_lookup crc_tbl_bytes MI crc_tbl_ro ltac:(unfold A_crc_lookup; lia) ltac:(rewrite crc_tbl_bytes_length; unfold A_crc_lookup; cbv; discriminate)) as RO.
destruct RO as [_ HB]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
Qed.

Lemma nth_concat_uniform : forall {A} (L : list (list A)) n k i d,
Forall (fun r => length r = n) L -> (k < length L)%nat -> (i < n)%nat ->
nth (n * k + i) (concat L) d = nth i (nth k L []) d.
Proof.
induction L as [|r L IH]; intros n k i d HL Hk Hi; [cbn in Hk; lia|].
inversion HL as [|r' L' Hr HL']; subst r' L'. cbn [concat nth].
destruct k as [|k].
- rewrite Nat.mul_0_r, Nat.add_0_l. rewrite app_nth1 by lia. reflexivity.
- rewrite app_nth2 by nia. rewrite Hr. replace (n * S k + i - n)%nat with (n * k + i)%nat by nia.
apply IH; [exact HL'| cbn in Hk; lia| exact Hi].
Qed.

Lemma crc_tables_rows : Forall (fun r => length r = 256%nat) crc_tables.
Proof. unfold crc_tables. apply Forall_forall. intros r Hr. apply in_map_iff in Hr. destruct Hr as (k & <- & _). rewrite length_map. reflexivity. Qed.
Lemma crc_tables_length : length crc_tables = 8%nat.
Proof. reflexivity. Qed.

Lemma crc_entries_nth : forall k i, (k < 8)%nat -> 0 <= i < 256 ->
nth (256 * k + Z.to_nat i) crc_entries 0 = tk crc_tables k i.
Proof.
intros k i Hk Hi. unfold crc_entries, tk, znth. destruct (Z.ltb_spec i 0); [lia|].
apply nth_concat_uniform; [apply crc_tables_rows| rewrite crc_tables_length; exact Hk| lia].
Qed.

Lemma crc_tbl_read : forall m (k : nat) i a, mem_inv rsegs m -> (k < 8)%nat -> 0 <= i < 256 ->
a = wa (A_crc_lookup + (1024 * Z.of_nat k + 4 * i)) ->
ov_read_bytes rsegs m a 4 = Some (le4 (wz (tk crc_tables k i))).
Proof.
intros m k i a MI Hk Hi ->.
pose proof (crc_tbl_bytes_at m MI) as HB. rewrite crc_tbl_bytes_eq in HB.
replace (1024 * Z.of_nat k + 4 * i) with (4 * (256 * Z.of_nat k + i)) by lia.
rewrite (u32ro_read rsegs m A_crc_lookup (map wz crc_entries) (256 * Z.of_nat k + i) (wz (tk crc_tables k i))); [reflexivity| exact HB| | lia| reflexivity].
rewrite nth_error_map. replace (Z.to_nat (256 * Z.of_nat k + i)) with (256 * k + Z.to_nat i)%nat by lia.
rewrite (nth_error_nth' _ 0) by (rewrite crc_entries_length; lia). cbn [option_map]. f_equal. f_equal. apply crc_entries_nth; assumption.
Qed.

Section BlockArith.
Context {RCEIL : RunCeiling}.
Variables b0 b1 b2 b3 c : Z.
Hypothesis Hb0 : 0 <= b0 < 256. Hypothesis Hb1 : 0 <= b1 < 256.
Hypothesis Hb2 : 0 <= b2 < 256. Hypothesis Hb3 : 0 <= b3 < 256.
Hypothesis Hc : 0 <= c < 2^32.

Definition Ereg : Z := Z.lxor (Z.lor (Z.lor (Z.shiftl b1 16) (Z.shiftl b0 24)) (Z.lor (Z.shiftl b2 8) b3))
(Z.land (bv_swrap 32 c) 18446744073709551615).

Definition c1 : Z := Z.lxor c (b0 * 2^24 + b1 * 2^16 + b2 * 2^8 + b3).

#[using="Type"] Lemma c1_nested : c1 = Z.lxor c (b3 + 256 * (b2 + 256 * (b1 + 256 * b0))).
Proof. unfold c1. f_equal. lia. Qed.
#[using="Hb0 Hb1 Hb2 Hb3 Hc"] Lemma c1_range : 0 <= c1 < 2^32.
Proof. unfold c1. apply (lxor_bound c _ 32); lia. Qed.

#[using="Type"] Lemma land_M_range : forall x, 0 <= Z.land x 18446744073709551615 < 2^64.
Proof. intros. rewrite land_ones64. apply Z.mod_pos_bound. lia. Qed.
#[using="Type"] Lemma land_1020_range : forall x, 0 <= Z.land x 1020 < 1024.
Proof.
intros. rewrite Z.land_comm.
replace (Z.land 1020 x) with (Z.land 1020 (x mod 2^64)).
- apply (X1bk.land_lt_pow2 1020 (x mod 2^64) 10); [lia| apply Z.mod_pos_bound; lia].
- apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i 64); [rewrite Z.mod_pow2_bits_low by lia; reflexivity|].
rewrite (testbit_high_false 1020 10) by lia. reflexivity.
Qed.

#[using="Hb0 Hb1 Hb2 Hb3 Hc"] Lemma idxA : Z.shiftl (Z.land (bv_swrap 32 (Z.shiftr (bv_wrap 32 Ereg) 24)) 18446744073709551615) 2 = 4 * (c1 / 16777216).
Proof.
pose proof c1_range as R1. rewrite Z.shiftl_mul_pow2 by lia.
pose proof (land_M_range (bv_swrap 32 (Z.shiftr (bv_wrap 32 Ereg) 24))) as R2.
assert (R3 : 0 <= c1 / 16777216 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
rewrite c1_nested in *. unfold Ereg in *.
zeq_bits 66%nat; nia.
Qed.

#[using="Hb0 Hb1 Hb2 Hb3 Hc"] Lemma idxB : Z.land (Z.shiftr Ereg 14) 1020 = 4 * ((c1 / 65536) mod 256).
Proof.
pose proof c1_range as R1. pose proof (land_1020_range (Z.shiftr Ereg 14)) as R2.
assert (R3 : 0 <= (c1 / 65536) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
rewrite c1_nested in *. unfold Ereg in *.
zeq_bits 12%nat; nia.
Qed.
#[using="Hb0 Hb1 Hb2 Hb3 Hc"] Lemma idxD : Z.shiftl (Z.land (Z.land Ereg 18446744073709551615) 255) 2 = 4 * (c1 mod 256).
Proof.
pose proof c1_range as R1.
assert (R2 : 0 <= Z.land (Z.land Ereg 18446744073709551615) 255 < 256).
{ rewrite Z.land_comm. apply (X1bk.land_lt_pow2 255 _ 8); [lia|]. apply (proj1 (land_M_range _)). }
assert (R3 : 0 <= c1 mod 256 < 256) by (apply Z.mod_pos_bound; lia).
rewrite Z.shiftl_mul_pow2 by lia.
rewrite c1_nested in *. unfold Ereg in *.
zeq_bits 12%nat; nia.
Qed.
#[using="Hb0 Hb1 Hb2 Hb3 Hc"] Lemma idxC : Z.land (Z.shiftr Ereg 6) 1020 = 4 * ((c1 / 256) mod 256).
Proof.
pose proof c1_range as R1. pose proof (land_1020_range (Z.shiftr Ereg 6)) as R2.
assert (R3 : 0 <= (c1 / 256) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
rewrite c1_nested in *. unfold Ereg in *.
zeq_bits 12%nat; nia.
Qed.
End BlockArith.

Definition crcw (c : Z) : word := Z_to_bv 64 (bv_swrap 32 c).

Lemma swrap32_mod64 : forall t, bv_swrap 32 (bv_wrap 64 t) = bv_swrap 32 t.
Proof.
intros. unfold bv_swrap. f_equal. unfold bv_wrap. change (bv_modulus 32) with (2^32). change (bv_modulus 64) with (2^32 * 2^32).
rewrite Z.rem_mul_r by lia.
rewrite <- Z.add_assoc, (Z.add_comm (2^32 * _)), Z.add_assoc. rewrite Z.mul_comm, Z.mod_add by lia.
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma unsigned_sx32_wz : forall t, bv_unsigned (sx32 (wz t)) = (bv_swrap 32 t) mod 2^64.
Proof.
intros. unfold sx32, wz. rewrite Z_to_bv_unsigned. unfold bv_wrap at 1. change (bv_modulus 64) with (2^64). f_equal.
rewrite Z_to_bv_unsigned. apply swrap32_mod64.
Qed.

Lemma xor8_value : forall u0 u1 u2 u3 u4 u5 u6 u7 : Z,
Z_to_bv 64 (Z.lxor (Z.lxor (Z.lxor ((bv_swrap 32 u6) mod 2^64) ((bv_swrap 32 u7) mod 2^64))
(Z.lxor ((bv_swrap 32 u5) mod 2^64) ((bv_swrap 32 u4) mod 2^64)))
(Z.lxor (Z.lxor (Z.lxor ((bv_swrap 32 u3) mod 2^64) ((bv_swrap 32 u2) mod 2^64))
((bv_swrap 32 u1) mod 2^64)) ((bv_swrap 32 u0) mod 2^64)))
= crcw (Z.lxor (Z.lxor (Z.lxor (Z.lxor (Z.lxor (Z.lxor (Z.lxor u7 u6) u5) u4) u3) u2) u1) u0).
Proof. intros. unfold crcw. word_bits. Qed.

Lemma tk_range : forall k i, (k < 8)%nat -> 0 <= i < 256 -> 0 <= tk crc_tables k i < 2^32.
Proof.
intros k i Hk Hi. rewrite crc_tables_spec by assumption.
pose proof (Tk_ok k i ltac:(unfold byte_ok; lia)) as H. unfold reg_ok, M32 in H. exact H.
Qed.

Lemma slice8_block_range : forall c b0 b1 b2 b3 b4 b5 b6 b7,
0 <= c < 2^32 -> 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 ->
0 <= slice8_block crc_tables c b0 b1 b2 b3 b4 b5 b6 b7 < 2^32.
Proof.
intros. unfold slice8_block. cbv zeta.
pose proof (c1_range b0 b1 b2 b3 c ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as R1. unfold c1 in R1.
set (c' := Z.lxor c (b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3)) in *.
assert (RA : 0 <= c' / 2^24 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (RB : 0 <= (c' / 2^16) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (RC : 0 <= (c' / 2^8) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (RD : 0 <= c' mod 256 < 256) by (apply Z.mod_pos_bound; lia).
repeat (apply (lxor_bound _ _ 32); [|apply tk_range; [lia| assumption]]).
apply tk_range; [lia| assumption].
Qed.

Section TailArith.
Context {RCEIL : RunCeiling}.
Variables c b : Z.
Hypothesis Hc : 0 <= c < 2^32. Hypothesis Hb : 0 <= b < 256.

#[using="Hc"] Lemma tail_hi : Z.land (bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.land (bv_swrap 32 c) 18446744073709551615)) 24)) 18446744073709551615 = c / 16777216.
Proof.
assert (R : 0 <= c / 16777216 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
zeq_bits 64%nat; [apply land_M_range | lia].
Qed.

#[using="Type"] Lemma tail_value : forall T,
Z_to_bv 64 (Z.lxor ((bv_swrap 32 T) mod 2^64)
(Z.land (bv_swrap 32 (Z.shiftl (Z.land (bv_swrap 32 c) 18446744073709551615) 8)) 18446744073709551615))
= crcw (Z.lxor ((c * 256) mod M32) T).
Proof. intros. unfold crcw, M32. word_bits. Qed.
End TailArith.

Definition os_update_crc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(c : Z) (bs : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs)
/\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m
/\ a0 = crcw (os_update_crc c (ubytes bs)).

Lemma tk0_crc_table : forall x, tk crc_tables 0 x = znth crc_table x.
Proof. intros. unfold tk. rewrite nth0_crc_tables. reflexivity. Qed.

Lemma block_eq : forall c b0 b1 b2 b3 b4 b5 b6 b7,
0 <= c < 2^32 -> 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 ->
slice8_block crc_tables c b0 b1 b2 b3 b4 b5 b6 b7 = os_update_crc c [b0;b1;b2;b3;b4;b5;b6;b7].
Proof.
intros. rewrite <- (os_update_crc_slice8_eq [b0;b1;b2;b3;b4;b5;b6;b7] c) by
(first [unfold reg_ok, M32; lia | repeat (constructor; [unfold byte_ok; lia|]); constructor]).
reflexivity.
Qed.

Lemma block_value : forall c b0 b1 b2 b3 b4 b5 b6 b7,
let c' := c1 b0 b1 b2 b3 c in
Z.lxor (Z.lxor (Z.lxor (Z.lxor (Z.lxor (Z.lxor (Z.lxor
(tk crc_tables 7 (c' / 16777216)) (tk crc_tables 6 ((c' / 65536) mod 256))) (tk crc_tables 5 ((c' / 256) mod 256)))
(tk crc_tables 4 (c' mod 256))) (tk crc_tables 3 b4)) (tk crc_tables 2 b5)) (tk crc_tables 1 b6)) (tk crc_tables 0 b7)
= slice8_block crc_tables c b0 b1 b2 b3 b4 b5 b6 b7.
Proof. intros. reflexivity. Qed.

Lemma ubytes_skip_8 : forall bs i, 0 <= i -> (Z.to_nat (i + 7) < length bs)%nat ->
skipn (Z.to_nat i) (ubytes bs) =
[bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)); bv_unsigned (nth (Z.to_nat (i + 1)) bs (Z_to_bv 8 0));
bv_unsigned (nth (Z.to_nat (i + 2)) bs (Z_to_bv 8 0)); bv_unsigned (nth (Z.to_nat (i + 3)) bs (Z_to_bv 8 0));
bv_unsigned (nth (Z.to_nat (i + 4)) bs (Z_to_bv 8 0)); bv_unsigned (nth (Z.to_nat (i + 5)) bs (Z_to_bv 8 0));
bv_unsigned (nth (Z.to_nat (i + 6)) bs (Z_to_bv 8 0)); bv_unsigned (nth (Z.to_nat (i + 7)) bs (Z_to_bv 8 0))]
++ skipn (Z.to_nat (i + 8)) (ubytes bs).
Proof.
intros bs i Hi Hl.
rewrite (ubytes_skip_cons bs i), (ubytes_skip_cons bs (i + 1)), (ubytes_skip_cons bs (i + 1 + 1)), (ubytes_skip_cons bs (i + 1 + 1 + 1)),
(ubytes_skip_cons bs (i + 1 + 1 + 1 + 1)), (ubytes_skip_cons bs (i + 1 + 1 + 1 + 1 + 1)), (ubytes_skip_cons bs (i + 1 + 1 + 1 + 1 + 1 + 1)),
(ubytes_skip_cons bs (i + 1 + 1 + 1 + 1 + 1 + 1 + 1)) by lia.
cbn [app]. rewrite <- !Z.add_assoc. reflexivity.
Qed.

Section Crc.
Context {RCEIL : RunCeiling}.
Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Variables (B : Z) (bs : list byte) (c0 : Z).
Hypothesis MI : mem_inv rsegs m.
Hypothesis BUF : bytes_at rsegs m B bs.
Hypothesis TOP : B + Z.of_nat (length bs) < 2^63.

Notation POST := (os_update_crc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c0 bs m).
Let len := Z.of_nat (length bs).

Ltac name_byte k b Hb R :=
pose proof (bytes_at_read1 rsegs m B bs k _ BUF ltac:(lia) ltac:(lia) eq_refl) as R;
pose proof (byte_range (nth (Z.to_nat k) bs (Z_to_bv 8 0))) as Hb;
set (b := bv_unsigned (nth (Z.to_nat k) bs (Z_to_bv 8 0))) in Hb.

#[using="MI BUF TOP"] Lemma tail_loop : forall (k : nat) (i c : Z) (x5 x6 x7 va0 va1 va2 x14 x15 x16 x17 x28 x29 x30 x31 : word),
Z.to_nat (len - i) = k -> 0 <= i < len -> 0 <= c < 2^32 ->
os_update_crc c (skipn (Z.to_nat i) (ubytes bs)) = os_update_crc c0 (ubytes bs) ->
va0 = crcw c -> va1 = wz (B + i) -> va2 = wz (B + len) ->
evt rsegs POST
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 va0 va1 va2 (wz A_crc_lookup) x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x302cc) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i c x5 x6 x7 va0 va1 va2 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hi Hc EQ -> -> ->; [lia|].
unfold crcw, wz, A_crc_lookup.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof BUF as (HB0 & HB1 & HB).
name_byte i b Hb Rb.
zstep. unfold zxb. fold b.
zstep. zstep. rewrite tail_hi by assumption. zstep. zstep.
assert (RI : 0 <= Z.lxor (c / 16777216) b < 256).
{ apply (lxor_bound _ _ 8); [split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia] | lia]. }
pose proof (crc_tbl_read m 0 (Z.lxor (c / 16777216) b) _ MI ltac:(lia) RI eq_refl) as T0r. unfold A_crc_lookup in T0r.
rewrite !Z.shiftl_mul_pow2 by lia.
zstep. zstep. zstep. zstep. zstep.
rewrite unsigned_sx32_wz. rewrite (tail_value c) by assumption.
set (c1 := Z.lxor ((c * 256) mod M32) (tk crc_tables 0 (Z.lxor (c / 16777216) b))).
assert (Ec1 : c1 = crc_step c b).
{ unfold c1, crc_step, crc_step_tbl. rewrite tk0_crc_table. reflexivity. }
assert (Hc1 : 0 <= c1 < 2^32).
{ rewrite Ec1. pose proof (crc_step_ok c b ltac:(unfold reg_ok, M32; lia) ltac:(unfold byte_ok; lia)) as R. unfold reg_ok, M32 in R. exact R. }
rewrite (ubytes_skip_cons bs i) in EQ by lia. fold b in EQ. rewrite os_update_crc_cons, <- Ec1 in EQ.
zstep. if_cases K; zify_cond K; rewrite ?land_ones64, ?Z.mod_small in K by lia.
-
eapply (IH (i + 1) c1); [lia| lia| exact Hc1| exact EQ| reflexivity | unfold wz; f_equal; lia| reflexivity].
-
zstep. finish. rewrite <- EQ. replace (Z.to_nat (i + 1)) with (length (ubytes bs)) by (rewrite ubytes_length; lia).
rewrite skipn_all, os_update_crc_nil. reflexivity.
Qed.

#[using="MI BUF TOP"] Lemma tail_entry : forall (i c : Z) (x5 x6 x7 va0 va1 va2 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
0 <= i <= len -> len - i < 8 -> 0 <= c < 2^32 ->
os_update_crc c (skipn (Z.to_nat i) (ubytes bs)) = os_update_crc c0 (ubytes bs) ->
va0 = crcw c -> va1 = wz (B + i) -> va2 = wz (len - i) ->
evt rsegs POST
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 va0 va1 va2 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x302ac) fc None m (seg_rom rsegs)).
Proof.
intros i c x5 x6 x7 va0 va1 va2 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hi Hrem Hc EQ -> -> ->.
unfold crcw, wz.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof BUF as (HB0 & HB1 & HB).
zstep. if_cases K; zify_cond K; rewrite ?land_ones64, ?Z.mod_small in K by lia.
-
zstep. finish. rewrite <- EQ. replace (Z.to_nat i) with (length (ubytes bs)) by (rewrite ubytes_length; lia).
rewrite skipn_all, os_update_crc_nil. reflexivity.
- zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. rewrite Z.div_mul by lia.
eapply (tail_loop (Z.to_nat (len - i)) i c); [lia| lia| exact Hc| exact EQ| reflexivity| reflexivity| unfold wz; f_equal; lia].
Qed.

#[using="MI BUF TOP"] Lemma block_loop : forall (k : nat) (i c : Z) (x5 x6 x7 va0 va1 va2 x17 x28 x29 x30 x31 : word),
len - i <= 8 * Z.of_nat k -> 0 <= i -> 8 <= len - i -> len < 2^31 -> 0 <= c < 2^32 ->
os_update_crc c (skipn (Z.to_nat i) (ubytes bs)) = os_update_crc c0 (ubytes bs) ->
va0 = crcw c -> va1 = wz (B + i) -> va2 = wz (len - i) ->
evt rsegs POST
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 va0 va1 va2 (Z_to_bv 64 8192) (Z_to_bv 64 4096) (wz A_crc_lookup) (Z_to_bv 64 15) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x301bc) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i c x5 x6 x7 va0 va1 va2 x17 x28 x29 x30 x31 Hk Hi Hrem Hlen Hc EQ -> -> ->; [lia|].
unfold crcw, wz, A_crc_lookup.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof BUF as (HB0 & HB1 & HB).
name_byte i b0 Hb0 R0. name_byte (i + 1) b1 Hb1 R1. name_byte (i + 2) b2 Hb2 R2. name_byte (i + 3) b3 Hb3 R3.
name_byte (i + 4) b4 Hb4 R4. name_byte (i + 5) b5 Hb5 R5. name_byte (i + 6) b6 Hb6 R6. name_byte (i + 7) b7 Hb7 R7.

zstep. unfold zxb. fold b0. zstep. unfold zxb. fold b1. zstep. unfold zxb. fold b2. zstep. unfold zxb. fold b3.

zstep. zstep. zstep. zstep.

zstep. zstep. zstep. zstep. zstep. zstep. zstep.

zstep. zstep. zstep. zstep. zstep. zstep.
fold (Ereg b0 b1 b2 b3 c).
rewrite (idxA b0 b1 b2 b3 c Hb0 Hb1 Hb2 Hb3 Hc), (idxB b0 b1 b2 b3 c Hb0 Hb1 Hb2 Hb3 Hc), (idxC b0 b1 b2 b3 c Hb0 Hb1 Hb2 Hb3 Hc).
pose proof (c1_range b0 b1 b2 b3 c Hb0 Hb1 Hb2 Hb3 Hc) as Hc'.
set (c' := c1 b0 b1 b2 b3 c) in *.
assert (RA : 0 <= c' / 16777216 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (RB : 0 <= (c' / 65536) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (RC : 0 <= (c' / 256) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (RD : 0 <= c' mod 256 < 256) by (apply Z.mod_pos_bound; lia).
pose proof (crc_tbl_read m 7 (c' / 16777216) _ MI ltac:(lia) RA eq_refl) as T7r.
pose proof (crc_tbl_read m 6 ((c' / 65536) mod 256) _ MI ltac:(lia) RB eq_refl) as T6r.
pose proof (crc_tbl_read m 5 ((c' / 256) mod 256) _ MI ltac:(lia) RC eq_refl) as T5r.
pose proof (crc_tbl_read m 4 (c' mod 256) _ MI ltac:(lia) RD eq_refl) as T4r.
pose proof (crc_tbl_read m 3 b4 _ MI ltac:(lia) Hb4 eq_refl) as T3r.
pose proof (crc_tbl_read m 2 b5 _ MI ltac:(lia) Hb5 eq_refl) as T2r.
pose proof (crc_tbl_read m 1 b6 _ MI ltac:(lia) Hb6 eq_refl) as T1r.
pose proof (crc_tbl_read m 0 b7 _ MI ltac:(lia) Hb7 eq_refl) as T0r.
unfold A_crc_lookup in T7r, T6r, T5r, T4r, T3r, T2r, T1r, T0r.

zstep. zstep. zstep.

zstep. unfold zxb. fold b4. zstep. unfold zxb. fold b5. zstep. unfold zxb. fold b6. zstep. unfold zxb. fold b7.

zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia.
zstep. zstep. zstep. zstep. zstep.

zstep. zstep. zstep.

zstep. zstep. rewrite (idxD b0 b1 b2 b3 c Hb0 Hb1 Hb2 Hb3 Hc). fold c'. zstep.

zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. zstep. zstep.

zstep. zstep. zstep. zstep.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite !unsigned_sx32_wz. rewrite xor8_value. rewrite (block_value c b0 b1 b2 b3 b4 b5 b6 b7).
rewrite (swrap32_small (len - i + -8)) by lia.
pose proof (slice8_block_range c b0 b1 b2 b3 b4 b5 b6 b7 Hc Hb0 Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7) as Hc2.
set (c2 := slice8_block crc_tables c b0 b1 b2 b3 b4 b5 b6 b7) in *.
rewrite (ubytes_skip_8 bs i) in EQ by lia. fold b0 b1 b2 b3 b4 b5 b6 b7 in EQ.
rewrite os_update_crc_app, <- (block_eq c b0 b1 b2 b3 b4 b5 b6 b7) in EQ by assumption. fold c2 in EQ.

zstep. if_cases K; zify_cond K; rewrite ?land_ones64, ?Z.mod_small in K by lia.
-
eapply (IH (i + 8) c2); [lia| lia| lia| exact Hlen| exact Hc2| exact EQ| reflexivity| unfold wz; f_equal; lia| unfold wz; f_equal; lia].
-
eapply (tail_entry (i + 8) c2); [lia| lia| exact Hc2| exact EQ| reflexivity| unfold wz; f_equal; lia| unfold wz; f_equal; lia].
Qed.

#[using="MI BUF TOP"] Lemma crc_body : forall (x5 x6 x7 va1 va2 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
len < 2^31 -> 0 <= c0 < 2^32 ->
va1 = wz B -> va2 = wz len ->
evt rsegs POST
(MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (crcw c0) va1 va2 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 A_os_update_crc) fc None m (seg_rom rsegs)).
Proof.
intros x5 x6 x7 va1 va2 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hlen Hc -> ->.
unfold crcw, wz, A_os_update_crc.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof BUF as (HB0 & HB1 & HB).
zstep. zstep. if_cases K; zify_cond K; rewrite signed_lit_small in K by lia.
-
eapply (tail_entry 0 c0); [lia| lia| exact Hc| reflexivity| reflexivity| unfold wz; f_equal; lia| unfold wz; f_equal; lia].
- zstep. zstep. zstep. zstep. zstep.
eapply (block_loop (Z.to_nat len) 0 c0); [lia| lia| lia| exact Hlen| exact Hc| reflexivity| reflexivity| unfold wz; f_equal; lia| unfold wz; f_equal; lia].
Qed.
End Crc.

Lemma os_update_crc_spec : forall (B : Z) (bs : list byte) (c0 : Z)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem),
bytes_at rsegs m B bs ->
mem_inv rsegs m ->
B + Z.of_nat (length bs) < 2^63 -> Z.of_nat (length bs) < 2^31 -> 0 <= c0 < 2^32 ->
a0 = crcw c0 -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
evt rsegs (os_update_crc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c0 bs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_update_crc) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros BUF MI TOP LEN Hc -> -> ->.
eapply (crc_body ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m B bs c0 MI BUF TOP); [exact LEN| exact Hc| reflexivity| reflexivity].
Qed.

Lemma ubytes_zero4 : forall h : list byte, (26 <= length h)%nat ->
ubytes (upd_bytes h 22 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) = ztake 22 (ubytes h) ++ [0; 0; 0; 0] ++ zdrop 26 (ubytes h).
Proof.
intros h Hl. unfold upd_bytes, ztake, zdrop. rewrite !ubytes_app, ubytes_firstn, ubytes_skipn. reflexivity.
Qed.

Definition crc4 (c : Z) : list byte :=
[Z_to_bv 8 (c mod 256); Z_to_bv 8 ((c / 2^8) mod 256); Z_to_bv 8 ((c / 2^16) mod 256); Z_to_bv 8 ((c / 2^24) mod 256)].
Lemma crc4_checksum : forall hdr body,
map (Z_to_bv 8) (ogg_page_checksum hdr body) = crc4 (os_update_crc (os_update_crc 0 (ztake 22 hdr ++ [0; 0; 0; 0] ++ zdrop 26 hdr)) body).
Proof. intros. reflexivity. Qed.

Lemma crc_b0 : forall c, 0 <= c < 2^32 -> le1 (Z_to_bv 64 (bv_swrap 32 c)) = [Z_to_bv 8 (c mod 256)].
Proof. intros. assert (0 <= c mod 256 < 256) by (apply Z.mod_pos_bound; lia). le1_by_bits. Qed.
Lemma crc_b1 : forall c, 0 <= c < 2^32 ->
le1 (Z_to_bv 64 (Z.shiftr (Z.land (bv_swrap 32 c) 18446744073709551615) 8)) = [Z_to_bv 8 ((c / 2^8) mod 256)].
Proof. intros. assert (0 <= (c / 2^8) mod 256 < 256) by (apply Z.mod_pos_bound; lia). le1_by_bits. Qed.
Lemma crc_b2 : forall c, 0 <= c < 2^32 ->
le1 (Z_to_bv 64 (Z.shiftr (Z.land (bv_swrap 32 c) 18446744073709551615) 16)) = [Z_to_bv 8 ((c / 2^16) mod 256)].
Proof. intros. assert (0 <= (c / 2^16) mod 256 < 256) by (apply Z.mod_pos_bound; lia). le1_by_bits. Qed.
Lemma crc_b3 : forall c, 0 <= c < 2^32 ->
le1 (Z_to_bv 64 (Z.shiftr (Z.land (bv_swrap 32 c) 18446744073709551615) 24)) = [Z_to_bv 8 ((c / 2^24) mod 256)].
Proof. intros. assert (0 <= (c / 2^24) mod 256 < 256) by (apply Z.mod_pos_bound; lia). le1_by_bits. Qed.

Definition cks_page_cells (H hlen : Z) (x1 : word) (Bo blen : Z) (x2 : word) : list cell :=
[C8 (wz H); C4 (wz hlen); C4 x1; C8 (wz Bo); C4 (wz blen); C4 x2].

Definition ogg_page_checksum_set_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D po hlen blen : Z) (bytes : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (D + po + 22, D + po + 26)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ u8arr rsegs m' D (upd_bytes bytes (Z.to_nat (po + 22))
(map (Z_to_bv 8) (ogg_page_checksum (ubytes (firstn (Z.to_nat hlen) (skipn (Z.to_nat po) bytes)))
(ubytes (firstn (Z.to_nat blen) (skipn (Z.to_nat (po + hlen)) bytes)))))).

Section Cks.
Context {RCEIL : RunCeiling}.
Variables (D po hlen blen : Z) (bytes : list byte) (G lo : Z) (x1 x2 : word).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem).
Hypothesis PG : rw_cells rsegs m G (cks_page_cells (D + po) hlen x1 (D + po + hlen) blen x2).
Hypothesis ARR : u8arr rsegs m D bytes.
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis MI : mem_inv rsegs m.
Hypothesis Hpo : 0 <= po. Hypothesis Hhlen : 27 <= hlen < 2^31. Hypothesis Hblen : 0 <= blen < 2^31.
Hypothesis Hfit : po + hlen + blen <= Z.of_nat (length bytes).
Hypothesis TOP : D + Z.of_nat (length bytes) < 2^63.
Hypothesis HG : 0 < G.
Hypothesis LO : lo + 32 <= bv_unsigned sp.
Hypothesis SEP1 : G + 32 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= G.
Hypothesis SEP2 : D + Z.of_nat (length bytes) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= D.
Hypothesis SEP3 : G + 32 <= D \/ D + Z.of_nat (length bytes) <= G.

Notation POST := (ogg_page_checksum_set_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D po hlen blen bytes lo m).

#[using="x1 x2 PG ARR ST MI Hpo Hhlen Hblen Hfit TOP HG LO SEP1 SEP2 SEP3"] Lemma cks_body :
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_page_checksum_set) fc None m (seg_rom rsegs)).
Proof.
unfold A_ogg_page_checksum_set. unfold cks_page_cells, wz in PG.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (D + po + 22, D + po + 26)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (rw_cells_bound _ _ _ _ PG) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (u8arr_bound _ _ _ _ ARR) as AB.
zstep. if_cases K; zify_cond K; [lia|].
carve_frame 32%nat ST.
zstep. zstep. zstep. zstep. zstep. zstep.

pose proof (u8arr_store_ok rsegs _ _ _ (po + 22) (wa (D + po + 22)) ARR ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep. arr_store ARR (po + 22) (Z_to_bv 8 0).
pose proof (u8arr_store_ok rsegs _ _ _ (po + 23) (wa (D + po + 23)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
zstep. zstep. arr_store ARR (po + 23) (Z_to_bv 8 0).
pose proof (u8arr_store_ok rsegs _ _ _ (po + 24) (wa (D + po + 24)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
zstep. zstep. arr_store ARR (po + 24) (Z_to_bv 8 0).
pose proof (u8arr_store_ok rsegs _ _ _ (po + 25) (wa (D + po + 25)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
zstep. zstep. arr_store ARR (po + 25) (Z_to_bv 8 0).

zstep. zstep. zstep. zstep. zstep.
match type of ARR with u8arr _ _ _ ?b4 => set (bytes4 := b4) in ARR end.
assert (L4 : length bytes4 = length bytes) by (unfold bytes4; rewrite !upd_length; reflexivity).
pose proof (bytes_at_sub _ D bytes4 (Z.to_nat po) (Z.to_nat hlen) (proj1 ARR) ltac:(lia)) as HDR.
replace (D + Z.of_nat (Z.to_nat po)) with (D + po) in HDR by lia.
call (os_update_crc_spec (D + po) (firstn (Z.to_nat hlen) (skipn (Z.to_nat po) bytes4)) 0).
all: rewrite ?firstn_length_le by (rewrite skipn_length; lia).
1:{ exact HDR. } 1:{ exact MI. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ reflexivity. } 1:{ reflexivity. }
1:{ rewrite sx32_lit by (unfold int31; lia). f_equal. lia. }
rename POST into PC1. match type of PC1 with ?v = _ => subst v end.
set (c1 := os_update_crc 0 (ubytes (firstn (Z.to_nat hlen) (skipn (Z.to_nat po) bytes4)))) in *.
assert (Hc1 : 0 <= c1 < 2^32).
{ pose proof (os_update_crc_ok (ubytes (firstn (Z.to_nat hlen) (skipn (Z.to_nat po) bytes4))) 0 ltac:(unfold reg_ok, M32; lia)
ltac:(apply Forall_impl with (P := fun b => 0 <= b < 256); [intros; unfold byte_ok; lia| apply ubytes_ok])) as R.
unfold reg_ok, M32 in R. exact R. }
pose proof (bytes_at_sub _ D bytes4 (Z.to_nat (po + hlen)) (Z.to_nat blen) (proj1 ARR) ltac:(lia)) as BODY.
replace (D + Z.of_nat (Z.to_nat (po + hlen))) with (D + po + hlen) in BODY by lia.

zstep. zstep. zstep.
call (os_update_crc_spec (D + po + hlen) (firstn (Z.to_nat blen) (skipn (Z.to_nat (po + hlen)) bytes4)) c1).
all: rewrite ?firstn_length_le by (rewrite skipn_length; lia).
1:{ exact BODY. } 1:{ exact MI. } 1:{ lia. } 1:{ lia. } 1:{ exact Hc1. } 1:{ reflexivity. } 1:{ reflexivity. }
1:{ rewrite sx32_lit by (unfold int31; lia). f_equal. lia. }
rename POST into PC2. match type of PC2 with ?v = _ => subst v end.
set (c2 := os_update_crc c1 (ubytes (firstn (Z.to_nat blen) (skipn (Z.to_nat (po + hlen)) bytes4)))) in *.
assert (Hc2 : 0 <= c2 < 2^32).
{ pose proof (os_update_crc_ok (ubytes (firstn (Z.to_nat blen) (skipn (Z.to_nat (po + hlen)) bytes4))) c1 ltac:(unfold reg_ok, M32; lia)
ltac:(apply Forall_impl with (P := fun b => 0 <= b < 256); [intros; unfold byte_ok; lia| apply ubytes_ok])) as R.
unfold reg_ok, M32 in R. exact R. }

pose proof (u8arr_store_ok rsegs _ _ _ (po + 22) (wa (D + po + 22)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
unfold crcw. zstep. rewrite crc_b0 by exact Hc2. arr_store ARR (po + 22) (Z_to_bv 8 (c2 mod 256)).

zstep. zstep.
pose proof (u8arr_store_ok rsegs _ _ _ (po + 23) (wa (D + po + 23)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
zstep. rewrite crc_b1 by exact Hc2. arr_store ARR (po + 23) (Z_to_bv 8 ((c2 / 2^8) mod 256)).
zstep. zstep.
pose proof (u8arr_store_ok rsegs _ _ _ (po + 24) (wa (D + po + 24)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
zstep. rewrite crc_b2 by exact Hc2. arr_store ARR (po + 24) (Z_to_bv 8 ((c2 / 2^16) mod 256)).
zstep. zstep.
pose proof (u8arr_store_ok rsegs _ _ _ (po + 25) (wa (D + po + 25)) ARR ltac:(rewrite ?upd_length; lia) ltac:(f_equal; lia)) as SOK.
zstep. rewrite crc_b3 by exact Hc2. arr_store ARR (po + 25) (Z_to_bv 8 ((c2 / 2^24) mod 256)).

zstep. zstep. zstep. zstep. zstep.
release_frame FR ST (bv_unsigned sp).
match type of ARR with u8arr _ _ _ ?l4 =>
replace l4 with (upd_bytes bytes (Z.to_nat (po + 22))
(map (Z_to_bv 8) (ogg_page_checksum (ubytes (firstn (Z.to_nat hlen) (skipn (Z.to_nat po) bytes)))
(ubytes (firstn (Z.to_nat blen) (skipn (Z.to_nat (po + hlen)) bytes)))))) in ARR end.
{ finish. }

subst c2 c1.
assert (E4 : bytes4 = upd_bytes bytes (Z.to_nat (po + 22)) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
{ subst bytes4. apply upd4_upd_bytes; lia. }
clearbody bytes4. subst bytes4.
rewrite upd4_upd_bytes by (rewrite ?upd_bytes_length; cbn [length]; lia).
rewrite upd_bytes_twice by (cbn [length]; lia).
rewrite crc4_checksum. unfold crc4.
replace (Z.to_nat (po + 22)) with (Z.to_nat po + 22)%nat by lia.
rewrite slice_upd_bytes_in by (cbn [length]; lia).
rewrite slice_upd_bytes_out by (cbn [length]; lia).
rewrite ubytes_zero4 by (rewrite firstn_length_le by (rewrite skipn_length; lia); lia).
reflexivity.
Qed.
End Cks.

Lemma ogg_page_checksum_set_spec : forall (D po hlen blen : Z) (bytes : list byte) (G lo : Z) (x1 x2 : word)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m G (cks_page_cells (D + po) hlen x1 (D + po + hlen) blen x2) ->
u8arr rsegs m D bytes ->
stk rsegs m lo (bv_unsigned sp) ->
mem_inv rsegs m ->
0 <= po -> 27 <= hlen < 2^31 -> 0 <= blen < 2^31 -> po + hlen + blen <= Z.of_nat (length bytes) ->
D + Z.of_nat (length bytes) < 2^63 -> 0 < G -> lo + 32 <= bv_unsigned sp ->
(G + 32 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= G) ->
(D + Z.of_nat (length bytes) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= D) ->
(G + 32 <= D \/ D + Z.of_nat (length bytes) <= G) ->
a0 = Z_to_bv 64 G ->
evt rsegs (ogg_page_checksum_set_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D po hlen blen bytes lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_page_checksum_set) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros PG ARR ST MI Hpo Hhlen Hblen Hfit TOP HG LO SEP1 SEP2 SEP3 ->.
eapply (cks_body D po hlen blen bytes G lo x1 x2); eassumption.
Qed.
