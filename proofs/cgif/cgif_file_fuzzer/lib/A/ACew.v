(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0m YP09 YP06 YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma byte_of_chunk_ok : forall E mem base off e V,
YP09.chunk_ok tfibsegs E mem base (YP09.mkChunk off (CVal 1 e)) ->
sv_denot E e = Z_to_bv 64 V -> 0 <= V < 2 ^ 64 ->
val_mem tfibsegs mem (base + off) 1 (V mod 256).
Proof.
intros E mem base off e V H He HV k Hk. assert (k = 0%nat) as -> by lia.
destruct (H 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2.
rewrite He in Hb1. unfold YP09.byte_of_word in Hb1. rewrite Z_to_bv_unsigned in Hb1.
unfold bv_wrap, bv_modulus in Hb1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hb1. rewrite Z.mod_small in Hb1 by lia.
replace (8 * 0) with 0 in Hb1 by lia. rewrite Z.shiftr_0_r in Hb1. injection Hb1 as <-.
change (Z.of_nat 0) with 0. rewrite Hb2. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma val_mem_bytes2 : forall m a v0 v1, val_mem tfibsegs m a 1 v0 -> val_mem tfibsegs m (a + 1) 1 v1 -> 0 <= v0 < 256 -> 0 <= v1 < 256 ->
val_mem tfibsegs m a 2 (v0 + 256 * v1).
Proof.
intros m a v0 v1 H0 H1 R0 R1 k Hk.
assert (L1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v).
{ intros v Hv. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, !Z.mod_small by lia. reflexivity. }
destruct k as [|[|k]]; [| |lia].
- specialize (H0 0%nat ltac:(lia)). rewrite (L1 v0 R0) in H0. change (Z.of_nat 0) with 0 in *. rewrite H0. f_equal. f_equal.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, (Z.mod_small _ 65536) by lia.
rewrite <- Z.add_mod_idemp_r, (Z.mul_comm 256 v1), Z.mod_mul, Z.add_0_r by lia. symmetry. apply Z.mod_small. lia.
- specialize (H1 0%nat ltac:(lia)). rewrite (L1 v1 R1) in H1. change (Z.of_nat 0) with 0 in H1. rewrite Z.add_0_r in H1.
change (Z.of_nat 1) with 1. rewrite H1. f_equal. f_equal.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 1) with 8. rewrite (Z.mod_small _ 65536) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite (Z.mul_comm 256 v1), Z.div_add, (Z.div_small v0 256), Z.add_0_l by lia. symmetry. apply Z.mod_small. lia.
Qed.
Lemma le_byte_div : forall z w j, 0 <= z < 2 ^ (8 * Z.of_nat w) -> YO0f.le_byte z w j = (z / 2 ^ (8 * Z.of_nat j)) mod 256.
Proof. intros z w j Hz. unfold YO0f.le_byte. rewrite (Z.mod_small _ _ Hz). rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma val_mem_half2 : forall m a u0 u1, val_mem tfibsegs m a 2 u0 -> val_mem tfibsegs m (a + 2) 2 u1 -> 0 <= u0 < 65536 -> 0 <= u1 < 65536 ->
val_mem tfibsegs m a 4 (u0 + 65536 * u1).
Proof.
intros m a u0 u1 H0 H1 R0 R1 k Hk.
rewrite (le_byte_div _ 4%nat k) by (change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia).
destruct (Nat.lt_ge_cases k 2) as [Hl | Hl].
- specialize (H0 k Hl). rewrite (le_byte_div _ 2%nat k) in H0 by (change (2 ^ (8 * Z.of_nat 2)) with 65536; lia). rewrite H0. f_equal. f_equal.
destruct k as [|[|k]]; [| |lia].
+ change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite !Z.div_1_r. rewrite <- Z.add_mod_idemp_r by lia.
replace (65536 * u1) with ((u1 * 256) * 256) by lia. rewrite Z.mod_mul, Z.add_0_r by lia. reflexivity.
+ change (2 ^ (8 * Z.of_nat 1)) with 256. replace (u0 + 65536 * u1) with (u0 + (u1 * 256) * 256) by lia. rewrite Z.div_add by lia.
rewrite <- Z.add_mod_idemp_r, Z.mod_mul, Z.add_0_r by lia. reflexivity.
- specialize (H1 (k - 2)%nat ltac:(lia)). rewrite (le_byte_div _ 2%nat (k - 2)%nat) in H1 by (change (2 ^ (8 * Z.of_nat 2)) with 65536; lia).
replace (a + 2 + Z.of_nat (k - 2)) with (a + Z.of_nat k) in H1 by lia. rewrite H1. f_equal. f_equal.
destruct k as [|[|[|[|k]]]]; [lia|lia| | |lia]; cbn [Nat.sub].
+ change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
rewrite (Z.mul_comm 65536 u1), Z.div_add, (Z.div_small u0 65536), Z.add_0_l by lia. reflexivity.
+ change (2 ^ (8 * Z.of_nat 3)) with (256 * 65536). change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite <- (Z.div_div _ 65536 256) by lia. rewrite (Z.mul_comm 65536 u1), Z.div_add, (Z.div_small u0 65536), Z.add_0_l by lia. reflexivity.
Qed.
Lemma byte_of_region : forall E m n b cs lo hi wlo whi od e,
region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs ->
val_mem tfibsegs m (b + od) 1 (bv_unsigned (sv_denot E e) mod 256).
Proof.
intros E m n b cs lo hi wlo whi od e (_ & _ & _ & Hcs) Hn Hc.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
apply (byte_of_chunk_ok E m b od e (bv_unsigned (sv_denot E e)) Hck).
- rewrite Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as HR. change (bv_modulus 64) with (2 ^ 64) in HR. exact HR.
Qed.
Definition abyte (H : word -> bool) (m : word -> option byte) (a : Z) : Z :=
match aview tfibsegs H m a with Some v => v | None => 0 end.
Lemma abyte_range : forall H m a, 0 <= abyte H m a < 256.
Proof.
intros H m a. unfold abyte. destruct (aview tfibsegs H m a) as [v|] eqn:Ev; [|lia].
destruct (aview_byte tfibsegs H m a v Ev) as (b & _ & _ & Hv). exact Hv.
Qed.
Lemma val_mem1_of_aview : forall H m a v, aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
destruct (aview_byte tfibsegs H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, !Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma abyte_val : forall H m a, apresent H m a -> val_mem tfibsegs (mrestrict H m) a 1 (abyte H m a).
Proof.
intros H m a Hp. unfold abyte. destruct (aview tfibsegs H m a) as [v|] eqn:Ev.
- apply val_mem1_of_aview. exact Ev.
- exfalso. exact (aview_some_of_apresent tfibsegs H m a Hp Ev).
Qed.
Lemma land1_low : forall x y, 0 <= x -> 0 <= y -> Z.land (x + 256 * y) 1 = Z.land x 1.
Proof.
intros x y Hx Hy. change (Z.land (x + 256 * y) (Z.ones 1) = Z.land x (Z.ones 1)). rewrite !Z.land_ones by lia. change (2 ^ 1) with 2.
rewrite <- Z.add_mod_idemp_r by lia. replace (256 * y) with ((128 * y) * 2) by lia. rewrite Z.mod_mul by lia. rewrite Z.add_0_r. reflexivity.
Qed.
End c.
