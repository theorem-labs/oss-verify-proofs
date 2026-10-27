(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN01.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma nth_error_Z_to_le_bytes : forall n z k, (k < n)%nat ->
nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma le_byte_bv : forall v w k, (k < w)%nat ->
Z_to_bv 8 (le_byte v w k) = Z_to_bv 8 (Z.shiftr (v mod 2 ^ (8 * Z.of_nat w)) (8 * Z.of_nat k)).
Proof.
intros v w k Hk. unfold le_byte. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma bytes_rdn : forall segs mem a (w : nat) v,
0 <= a -> a + Z.of_nat w <= 2^64 ->
(forall k, (k < w)%nat -> mbyte segs mem (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v w k))) ->
rdn segs mem (Z_to_bv 64 a) w = Some (Z_to_le_bytes w (v mod 2 ^ (8 * Z.of_nat w))).
Proof.
intros segs mem a w v Ha Hw Hb. apply rdn_mbytes. split; [apply length_Z_to_le_bytes|].
intros i Hi. rewrite (Hb i Hi), nth_error_Z_to_le_bytes by lia. f_equal. apply le_byte_bv. exact Hi.
Qed.
Lemma word_mem_rdn : forall segs mem a v,
word_mem segs mem a v -> 0 <= a -> a + 8 <= 2^64 ->
rdn segs mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).
Proof.
intros segs mem a v Hw Ha H8. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned.
change (bv_wrap 64 v) with (v mod 2 ^ (8 * Z.of_nat 8)).
apply bytes_rdn; [lia|lia|]. exact Hw.
Qed.
Lemma word_mem_ld : forall segs mem a v,
word_mem segs mem a v -> 0 <= a -> a + 8 <= 2^64 ->
exists bs, rdn segs mem (Z_to_bv 64 a) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 v).
Proof.
intros segs mem a v Hw Ha H8. eexists. split; [apply (word_mem_rdn segs mem a v Hw Ha H8)|]. apply bytes_le_to_Z_8.
Qed.
Lemma bytes_le_to_Z_Z_to_le_bytes : forall n z, 0 <= z < 2 ^ (8 * Z.of_nat n) ->
bytes_le_to_Z (Z_to_le_bytes n z) = z.
Proof.
induction n as [|n IH]; intros z Hz.
- cbn in *. lia.
- cbn [Z_to_le_bytes bytes_le_to_Z]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256.
rewrite IH.
+ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
replace (z / 2^8 * 2^8) with (2^8 * (z / 2^8)) by lia.
rewrite lor_add_high; [|change (2^8) with 256; pose proof (Z.mod_pos_bound z 256); lia|apply Z.div_pos; lia].
change (2^8) with 256. pose proof (Z.div_mod z 256 ltac:(lia)). lia.
+ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]. rewrite Nat2Z.inj_succ in Hz.
replace (8 * Z.succ (Z.of_nat n)) with (8 + 8 * Z.of_nat n) in Hz by lia.
rewrite Z.pow_add_r in Hz by lia. lia.
Qed.
Lemma bytes4_rdn : forall segs mem a v,
0 <= a -> a + 4 <= 2^64 ->
(forall k, (k < 4)%nat -> mbyte segs mem (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v 4 k))) ->
rdn segs mem (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 (v mod 2^32)) /\
bytes_le_to_Z (Z_to_le_bytes 4 (v mod 2^32)) = v mod 2^32.
Proof.
intros segs mem a v Ha H4 Hb. split.
- change (2^32) with (2 ^ (8 * Z.of_nat 4)). apply bytes_rdn; assumption.
- apply bytes_le_to_Z_Z_to_le_bytes. change (2 ^ (8 * Z.of_nat 4)) with (2^32). apply Z.mod_pos_bound. lia.
Qed.
Lemma bytes2_rdn : forall segs mem a v,
0 <= a -> a + 2 <= 2^64 ->
(forall k, (k < 2)%nat -> mbyte segs mem (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v 2 k))) ->
rdn segs mem (Z_to_bv 64 a) 2 = Some (Z_to_le_bytes 2 (v mod 2^16)) /\
bytes_le_to_Z (Z_to_le_bytes 2 (v mod 2^16)) = v mod 2^16.
Proof.
intros segs mem a v Ha H2 Hb. split.
- change (2^16) with (2 ^ (8 * Z.of_nat 2)). apply bytes_rdn; assumption.
- apply bytes_le_to_Z_Z_to_le_bytes. change (2 ^ (8 * Z.of_nat 2)) with (2^16). apply Z.mod_pos_bound. lia.
Qed.
Lemma byte1_rdn : forall segs mem a b,
mbyte segs mem a = Some b -> rdn segs mem (Z_to_bv 64 a) 1 = Some [b].
Proof.
intros segs mem a b Hb. apply rdn_mbytes. split; [reflexivity|].
intros i Hi. destruct i; [|lia]. cbn. rewrite Z.add_0_r. exact Hb.
Qed.
Lemma cell1_rdn : forall segs mem a v,
(forall k, (k < 1)%nat -> mbyte segs mem (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v 1 k))) ->
rdn segs mem (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 (v mod 256)].
Proof.
intros segs mem a v Hb. apply byte1_rdn. specialize (Hb 0%nat ltac:(lia)). rewrite Z.add_0_r in Hb.
rewrite Hb. f_equal. unfold le_byte. apply bv_eq. rewrite !Z_to_bv_unsigned.
change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.shiftr_0_r, Z.mod_mod by lia. reflexivity.
Qed.
Lemma writable_store_ok : forall segs mem a (n : nat),
0 <= a < 2^64 -> a + Z.of_nat n <= 2^64 ->
(forall x, a <= x < a + Z.of_nat n -> writable_at segs mem x) ->
store_ok segs mem (Z_to_bv 64 a) n = true.
Proof.
intros segs mem a n Ha Hn Hw. apply store_ok_of_all; [rewrite u_Z2bv by lia; lia|].
intros x Hx. rewrite u_Z2bv in Hx by lia.
pose proof (Hw (bv_unsigned x) Hx) as W. unfold writable_at in W. rewrite Z_to_bv_bv_unsigned in W. exact W.
Qed.
Lemma rdn_sd_hit : forall segs mem a (v : word),
0 <= a -> a + 8 <= 2^64 ->
rdn segs (wbytes mem (Z_to_bv 64 a) (word_to_le_bytes 8 v)) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v).
Proof. intros. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. Qed.
Lemma rdn_sd_out : forall segs mem a (v : word) b n,
0 <= a -> a + 8 <= 2^64 -> 0 <= b < 2^64 -> b + Z.of_nat n <= 2^64 ->
(b + Z.of_nat n <= a \/ a + 8 <= b) ->
rdn segs (wbytes mem (Z_to_bv 64 a) (word_to_le_bytes 8 v)) (Z_to_bv 64 b) n = rdn segs mem (Z_to_bv 64 b) n.
Proof.
intros. apply rdn_wbytes_out; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; lia.
Qed.
End c.
