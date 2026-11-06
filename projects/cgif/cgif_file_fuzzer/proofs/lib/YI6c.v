(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04 YI09 YI08.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable segs : list Segment.
Lemma vst_ok_region_nth : forall E ss ms i r,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok segs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma vval_mem_of_chunk : forall E mem r p a off (n : BinNums.N) e v,
region_ok segs E mem r -> r_base r = Some p -> In (mkChunk off (CVal n e)) (r_chunks r) ->
bv_unsigned (ew E p) = a -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem segs mem (a + off) (N.to_nat n) v.
Proof.
intros E mem r p a off n e v HR Hb Hin Hp He Hv Hn.
destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
eapply val_of_chunk_ok; [exact Hc | exact He | exact Hv | exact Hn].
Qed.
Lemma vval_of_chunk_ok_mod : forall E mem base off (n : N) (e : sv) v,
chunk_ok segs E mem base (mkChunk off (CVal n e)) ->
bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n) = v -> (Z.of_N n <= 8) ->
val_mem segs mem (base + off) (N.to_nat n) v.
Proof.
intros E mem base off n e v H He Hn k Hk. unfold chunk_ok in H. cbn [c_off c_val c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1.
unfold byte_of_word in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold le_byte. rewrite Z.mod_mod by lia. subst v. rewrite Hnn.
set (w := bv_unsigned (sv_denot E e)). set (K := Z.of_nat k). set (N8 := Z.of_N n).
assert (HK : 0 <= K < N8) by (subst K N8; lia).
rewrite (Z.mod_small (w mod 2 ^ (8 * N8)) (2 ^ (8 * N8))) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
rewrite !Z.shiftr_div_pow2 by lia.
replace (2 ^ (8 * N8)) with (2 ^ (8 * K) * 2 ^ (8 * (N8 - K))) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; try (apply Z.pow_pos_nonneg); lia).
rewrite (Z.mul_comm (2 ^ (8 * K))), Z.div_add by (apply Z.pow_nonzero; lia).
rewrite (Z.div_small (w mod 2 ^ (8 * K))) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
rewrite Z.add_0_l.
replace (2 ^ (8 * (N8 - K))) with (256 * 2 ^ (8 * (N8 - K) - 8)) by (change 256 with (2 ^ 8); rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; try (apply Z.pow_pos_nonneg); lia).
rewrite (Z.mul_comm 256), Z.mod_add by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma vval_mem_of_chunk_mod : forall E mem r p a off (n : BinNums.N) e v,
region_ok segs E mem r -> r_base r = Some p -> In (mkChunk off (CVal n e)) (r_chunks r) ->
bv_unsigned (ew E p) = a -> bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n) = v -> Z.of_N n <= 8 ->
val_mem segs mem (a + off) (N.to_nat n) v.
Proof.
intros E mem r p a off n e v HR Hb Hin Hp He Hn.
destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
eapply vval_of_chunk_ok_mod; [exact Hc | exact He | exact Hn].
Qed.
End d.
End c.
