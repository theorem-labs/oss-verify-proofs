(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI09 YI08.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma U_or_smallAF : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
U E (SAlu ALU_OR a b) = Z.lor x y.
Proof.
intros E a b x y Hx Hy Rx Ry Rs. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy.
assert (0 <= Z.lor x y) by (apply Z.lor_nonneg; lia). assert (0 <= Z.land x y) by (apply Z.land_nonneg; lia).
pose proof (Z.add_lor_land x y). apply zcanon_id. unfold M64. lia.
Qed.
Lemma land5_eq0_iff : forall x, Z.land x 5 = 0 <-> Z.land x 1 = 0 /\ Z.land x 4 = 0.
Proof. intros x. change 5 with (Z.lor 1 4). rewrite Z.land_lor_distr_r. apply Z.lor_eq_0_iff. Qed.
Lemma U_orAF : forall E a b, U E (SAlu ALU_OR a b) = Z.lor (U E a) (U E b).
Proof.
intros E a b. rewrite U_SAlu. cbn [zalu_raw]. pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold M64 in *.
assert (Hnn : 0 <= Z.lor (U E a) (U E b)) by (apply Z.lor_nonneg; lia).
apply zcanon_id. unfold M64. split; [exact Hnn|].
destruct (Z.eq_dec (Z.lor (U E a) (U E b)) 0) as [E0|Hnz]; [rewrite E0; lia|].
apply (proj2 (Z.log2_lt_pow2 (Z.lor (U E a) (U E b)) 64 ltac:(lia))). rewrite Z.log2_lor by lia.
apply Z.max_lub_lt.
- destruct (Z.eq_dec (U E a) 0) as [E0|E0]; [rewrite E0; cbn; lia | apply (proj1 (Z.log2_lt_pow2 (U E a) 64 ltac:(lia))); lia].
- destruct (Z.eq_dec (U E b) 0) as [E0|E0]; [rewrite E0; cbn; lia | apply (proj1 (Z.log2_lt_pow2 (U E b) 64 ltac:(lia))); lia].
Qed.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI3w UI1d.
Lemma rc_int_small : forall v, 0 <= v < 2 ^ 31 -> rc_int v = v.
Proof. intros v Hv. unfold rc_int. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.
Lemma rc_int_eq_small : forall v c, 0 <= v < 2 ^ 32 -> 0 <= c < 2 ^ 31 -> (rc_int v = c <-> v = c).
Proof. intros v c Hv Hc. unfold rc_int. destruct (Z.ltb_spec v (2 ^ 31)); lia. Qed.
Lemma U_sext32_small : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt. rewrite (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small v (2 ^ 32)) by lia. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
