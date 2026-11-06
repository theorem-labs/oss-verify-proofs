(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X09f X09e X091.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X0ys X0yt X0x2 X0zp X0zs X0zc.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Lemma lor_byte_shift : forall a R, 0 <= a < 256 -> 0 <= R -> Z.lor a (Z.shiftl R 8) = a + 256 * R.
Proof.
intros a R Ha HR.
assert (L0 : Z.land a (Z.shiftl R 8) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases n 8) as [L|G]; [rewrite Z.shiftl_spec_low by lia; apply andb_false_r|].
destruct (Z.eq_dec a 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
rewrite (Z.bits_above_log2 a n); [reflexivity| lia|]. apply Z.lt_le_trans with 8; [|exact G]. apply Z.log2_lt_pow2; [lia|]. change (2^8) with 256. lia. }
rewrite <- Z.lxor_lor by exact L0. rewrite <- Z.add_nocarry_lxor by exact L0. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. lia.
Qed.
Lemma bytes_le_to_Z_bound : forall bs, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
induction bs as [|b bs IH]; [cbn; lia|].
cbn [bytes_le_to_Z length]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
replace (8 * Z.of_nat (S (length bs))) with (8 * Z.of_nat (length bs) + 8) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256. rewrite lor_byte_shift by lia. nia.
Qed.
Lemma Z_to_le_bytes_of_bytes : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [bytes_le_to_Z length Z_to_le_bytes]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
pose proof (bytes_le_to_Z_bound bs) as B. rewrite lor_byte_shift by lia. f_equal.
- apply zb8_eq. replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs); [exact IH|].
apply Z.div_unique with (r := bv_unsigned b); [left; lia| lia].
Qed.
Lemma rw_cells_CB8_C8 : forall segs (m : mem) a j, rw_cells segs m a [CB 8 j] -> exists w, rw_cells segs m a [C8 w].
Proof.
intros segs m a j H. assert (L : length j = 8%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
exists (le_bytes_to_word j). eapply rw_cells_recast; [exact H | cbn; exact (conj I I) |].
cbn [cells_bytes cbytes app]. rewrite !app_nil_r. unfold le8, word_to_le_bytes, le_bytes_to_word.
pose proof (bytes_le_to_Z_bound j) as B. rewrite L in B. change (8 * Z.of_nat 8) with 64 in B.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small by lia.
rewrite <- L at 1. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma le8_of_bytes : forall j : list byte, length j = 8%nat -> le8 (le_bytes_to_word j) = j.
Proof.
intros j L. unfold le8, word_to_le_bytes, le_bytes_to_word.
pose proof (bytes_le_to_Z_bound j) as B. rewrite L in B. change (8 * Z.of_nat 8) with 64 in B.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small by lia.
rewrite <- L at 1. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma CB_C8s : forall n (j : list byte), length j = (8 * n)%nat -> exists ws : list word, length ws = n /\ cells_bytes (map C8 ws) = j.
Proof.
induction n as [|n IH]; intros j L.
- exists []. split; [reflexivity|]. destruct j; [reflexivity| cbn in L; lia].
- destruct (IH (skipn 8 j)) as (ws & Lws & E); [rewrite length_skipn; lia|].
exists (le_bytes_to_word (firstn 8 j) :: ws). split; [cbn; lia|].
cbn [map cells_bytes cbytes]. rewrite E, le8_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn.
Qed.
Lemma cells_wf_C8s : forall ws : list word, cells_wf (map C8 ws).
Proof. induction ws; cbn; auto. Qed.
Definition sset (k : Z) (v : word) (s : nbslots) : nbslots :=
if k =? 0 then NBS v (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 8 then NBS (v0 s) v (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 16 then NBS (v0 s) (v8 s) v (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 24 then NBS (v0 s) (v8 s) (v16 s) v (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 32 then NBS (v0 s) (v8 s) (v16 s) (v24 s) v (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 40 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) v (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 48 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) v (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 56 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) v (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 64 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) v (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 72 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) v (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 80 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) v (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 88 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) v (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 96 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) v (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 104 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) v (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 112 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) v (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 120 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) v (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 128 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) v (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 136 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) v (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 144 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) v (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 152 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) v (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 160 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) v (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 168 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) v (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 176 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) v (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 184 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) v (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 192 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) v (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 200 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) v (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 208 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) v (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 216 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) v (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 224 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) v (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 232 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) v (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 240 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) v (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 248 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) v (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 256 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) v (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 264 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) v (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 272 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) v (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 280 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) v (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 288 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) v (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 296 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) v (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 304 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) v (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 312 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) v (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 320 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) v (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 328 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) v (v336 s) (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 336 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) v (v344 s) (v352 s) (v360 s) (v368 s)
else if k =? 344 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) v (v352 s) (v360 s) (v368 s)
else if k =? 352 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) v (v360 s) (v368 s)
else if k =? 360 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) v (v368 s)
else if k =? 368 then NBS (v0 s) (v8 s) (v16 s) (v24 s) (v32 s) (v40 s) (v48 s) (v56 s) (v64 s) (v72 s) (v80 s) (v88 s) (v96 s) (v104 s) (v112 s) (v120 s) (v128 s) (v136 s) (v144 s) (v152 s) (v160 s) (v168 s) (v176 s) (v184 s) (v192 s) (v200 s) (v208 s) (v216 s) (v224 s) (v232 s) (v240 s) (v248 s) (v256 s) (v264 s) (v272 s) (v280 s) (v288 s) (v296 s) (v304 s) (v312 s) (v320 s) (v328 s) (v336 s) (v344 s) (v352 s) (v360 s) v
else s.

Lemma frameA_slots : forall (m : mem) a ST A OUT f sf (ja jb jc jd je jf jg jh1 jh2 : list byte) (sv : list cell),
rw_cells bsegs m a (nbd_frame_A ST A OUT f sf ja jb jc jd je jf jg jh1 jh2 sv) ->
exists s : nbslots, rw_cells bsegs m a (slot_cells s) /\ rw_cells bsegs m (a + 376) sv
/\ v0 s = Z_to_bv 64 0 /\ v48 s = Z_to_bv 64 f /\ v56 s = Z_to_bv 64 f /\ v64 s = Z_to_bv 64 (ST + 2047) /\ v88 s = Z_to_bv 64 ST /\ v168 s = Z_to_bv 64 (ST + 2032) /\ v176 s = Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB) /\ v192 s = Z_to_bv 64 (ST + 2184) /\ v200 s = Z_to_bv 64 sf /\ v240 s = Z_to_bv 64 OUT /\ v288 s = Z_to_bv 64 A /\ v304 s = Z_to_bv 64 0 /\ v336 s = Z_to_bv 64 (ST + 2256) /\ v344 s = Z_to_bv 64 (ST + 2904) /\ v368 s = Z_to_bv 64 f.
Proof.
intros m a ST A OUT f sf ja jb jc jd je jf jg jh1 jh2 sv H. unfold nbd_frame_A in H.
apply rw_cells_app in H. destruct H as (H & SV). cbn [cells_size csize Nat.add] in SV. change (Z.of_nat 376) with 376 in SV.
pose proof H as [[WF _] _]. cbn in WF.
destruct WF as (_ & La & _ & _ & _ & Lb & _ & Lc & _ & _ & Ld & _ & _ & Le & _ & Lf & _ & Lg & _ & Lh1 & _ & _ & Lh2 & _).
destruct (CB_C8s 5 ja La) as (wa & Lwa & Ea). destruct (CB_C8s 2 jb Lb) as (wb & Lwb & Eb). destruct (CB_C8s 9 jc Lc) as (wc & Lwc & Ec).
destruct (CB_C8s 1 jd Ld) as (wd & Lwd & Ed). destruct (CB_C8s 4 je Le) as (we & Lwe & Ee). destruct (CB_C8s 5 jf Lf) as (wf & Lwf & Ef).
destruct (CB_C8s 1 jg Lg) as (wg & Lwg & Eg). destruct (CB_C8s 3 jh1 Lh1) as (wh & Lwh & Eh). destruct (CB_C8s 2 jh2 Lh2) as (wi & Lwi & Ei).
destruct wa as [|a0 [|a1 [|a2 [|a3 [|a4 [|? ?]]]]]]; try discriminate Lwa. destruct wb as [|b0 [|b1 [|? ?]]]; try discriminate Lwb.
destruct wc as [|c0 [|c1 [|c2 [|c3 [|c4 [|c5 [|c6 [|c7 [|c8 [|? ?]]]]]]]]]]; try discriminate Lwc.
destruct wd as [|d0 [|? ?]]; try discriminate Lwd. destruct we as [|e0 [|e1 [|e2 [|e3 [|? ?]]]]]; try discriminate Lwe.
destruct wf as [|f0 [|f1 [|f2 [|f3 [|f4 [|? ?]]]]]]; try discriminate Lwf. destruct wg as [|g0 [|? ?]]; try discriminate Lwg.
destruct wh as [|h0 [|h1 [|h2 [|? ?]]]]; try discriminate Lwh. destruct wi as [|i0 [|i1 [|? ?]]]; try discriminate Lwi.
exists (NBS (Z_to_bv 64 0) a0 a1 a2 a3 a4 (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 (ST + 2047)) b0 b1 (Z_to_bv 64 ST) c0 c1 c2 c3 c4 c5 c6 c7 c8 (Z_to_bv 64 (ST + 2032)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) d0 (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 sf) e0 e1 e2 e3 (Z_to_bv 64 OUT) f0 f1 f2 f3 f4 (Z_to_bv 64 A) g0 (Z_to_bv 64 0) h0 h1 h2 (Z_to_bv 64 (ST + 2256)) (Z_to_bv 64 (ST + 2904)) i0 i1 (Z_to_bv 64 f)).
split; [| split; [exact SV| cbn; repeat split; reflexivity]].
eapply rw_cells_recast; [exact H | cbn; tauto |].
cbn [slot_cells v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 v240 v248 v256 v264 v272 v280 v288 v296 v304 v312 v320 v328 v336 v344 v352 v360 v368].
rewrite <- Ea, <- Eb, <- Ec, <- Ed, <- Ee, <- Ef, <- Eg, <- Eh, <- Ei. cbn [cells_bytes cbytes map app]. rewrite <- !app_assoc. reflexivity.
Qed.

Definition nbd_shg (top lpc qlsp ak innov exc32 innov2 iq : bool) : list byte :=
repeat bF1 4 ++ [if top then b04 else bF8] ++ [bF2] ++ (if top then [z8; b04] else [bF8; bF8]) ++ repeat bF2 2
++ sh_run lpc 5 ++ repeat bF2 5 ++ sh_run qlsp 5 ++ repeat bF2 5 ++ sh_run ak 5 ++ repeat bF2 5
++ sh_run innov 20 ++ repeat bF2 8 ++ sh_run exc32 20 ++ repeat bF2 8 ++ sh_run innov2 20 ++ repeat bF2 8
++ sh_run iq 5 ++ repeat bF3 7.
Definition nbd_shadow_g (top lpc qlsp ak innov exc32 innov2 iq : bool) (rest : list byte) : list cell :=
map C1 (nbd_shg top lpc qlsp ak innov exc32 innov2 iq) ++ [CB 120 rest].
Lemma nbd_shadow_g_eq : forall s rest,
nbd_shadow s rest = nbd_shadow_g (sc_top s) (sc_lpc s) (sc_main s) (sc_main s) (sc_main s) (sc_main s) (sc_innov2 s) (sc_iq s) rest.
Proof. reflexivity. Qed.

Definition smr_ptr_at (mo : Z) : Z := match smrec_at mo with Some r => smr_ptr r | None => 0 end.
Lemma sub_ptr_read : forall (m : mem) mo, lib_consts m -> 0 <= mo <= 8 ->
ov_read_bytes bsegs m (wa (NB_SUBMODES_PTR + 8 * mo)) 8 = Some (le8 (Z_to_bv 64 (smr_ptr_at mo))).
Proof.
intros m mo LC Hmo. pose proof (lib_const m A_nb_mode LC_nb_mode LC ltac:(lc_in)) as RO.
assert (C : mo = 0 \/ mo = 1 \/ mo = 2 \/ mo = 3 \/ mo = 4 \/ mo = 5 \/ mo = 6 \/ mo = 7 \/ mo = 8) by lia.
unfold NB_SUBMODES_PTR.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]];
match goal with |- ov_read_bytes _ _ (wa (?base + 32 + 8 * ?i)) 8 = _ =>
exact (ro_cells_read_at bsegs m base LC_nb_mode (Z.to_nat (32 + 8 * i)) _ 8 _ RO ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) end.
Qed.
Definition nb_tabs_acc (m : mem) : Prop := aobj bsegs m A_nb_mode 208 /\ Forall (fun r => aobj bsegs m (smr_ptr r) 88) nb_smrecs.
Lemma smrec_facts : forall mo r, smrec_at mo = Some r ->
In r nb_smrecs /\ 1 <= mo <= 8 /\ smr_ptr_at mo = smr_ptr r /\ 0x10000 <= smr_ptr r /\ smr_ptr r + 88 <= IMG_TOP_B /\ smr_ptr r mod 8 = 0
/\ lsp_order (sm_lsp_unquant (smr_sm r)) = 10
/\ forall m : mem, lib_consts m -> ro_cells bsegs m (smr_ptr r) (smrec_cells r).
Proof.
intros mo r H. unfold smrec_at in H. destruct (mo <? 1) eqn:K; [discriminate|]. apply Z.ltb_ge in K.
assert (C : mo = 1 \/ mo = 2 \/ mo = 3 \/ mo = 4 \/ mo = 5 \/ mo = 6 \/ mo = 7 \/ mo = 8 \/ 9 <= mo) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | C]]]]]]]].
1-8: cbn in H; injection H as <-; (split; [cbn; tauto|]); (split; [lia|]); (split; [reflexivity|]); unfold IMG_TOP_B;
cbv [smr_ptr nb_smrec1 nb_smrec2 nb_smrec3 nb_smrec4 nb_smrec5 nb_smrec6 nb_smrec7 nb_smrec8 A_nb_submode1 A_nb_submode2 A_nb_submode3 A_nb_submode4 A_nb_submode5 A_nb_submode6 A_nb_submode7 A_nb_submode8];
(split; [lia|]); (split; [lia|]); (split; [reflexivity|]); (split; [reflexivity|]); intros m LC.
- exact (lib_const m A_nb_submode1 LC_nb_submode1 LC ltac:(lc_in)).
- exact (lib_const m A_nb_submode2 LC_nb_submode2 LC ltac:(lc_in)).
- exact (lib_const m A_nb_submode3 LC_nb_submode3 LC ltac:(lc_in)).
- exact (lib_const m A_nb_submode4 LC_nb_submode4 LC ltac:(lc_in)).
- exact (lib_const m A_nb_submode5 LC_nb_submode5 LC ltac:(lc_in)).
- exact (lib_const m A_nb_submode6 LC_nb_submode6 LC ltac:(lc_in)).
- exact (lib_const m A_nb_submode7 LC_nb_submode7 LC ltac:(lc_in)).
- exact (lib_const m A_nb_submode8 LC_nb_submode8 LC ltac:(lc_in)).
- exfalso. assert (E : (8 <= Z.to_nat (mo - 1))%nat) by lia. apply nth_error_Some_lt in H || (assert (Hx : nth_error nb_smrecs (Z.to_nat (mo - 1)) <> None) by congruence; apply nth_error_Some in Hx; cbn in Hx; lia).
Qed.

Lemma lib_tables_range : forallb (fun t => (0xf8380 <=? fst t) && (fst t + Z.of_nat (cells_size (snd t)) <=? 0xfce00)) LIB_TABLES = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lib_consts_munch : forall W (m m' : mem), lib_consts m -> munch W m m' -> Forall (fun iv => snd iv <= 0xf8380 \/ 0xfce00 <= fst iv) W -> lib_consts m'.
Proof.
intros W m m' LC MU FW. unfold lib_consts in *.
pose proof lib_tables_range as R. rewrite forallb_forall in R. rewrite Forall_forall in *.
intros t Ht. specialize (LC t Ht). specialize (R t Ht). apply andb_prop in R. destruct R as [R1 R2]. apply Z.leb_le in R1, R2.
apply (ro_cells_transport bsegs W m m' _ _ LC MU).
clear - FW R1 R2. induction W as [|[l h] W IH]; [exact I|]. cbn [disjoint_from]. split.
- specialize (FW (l, h) (or_introl eq_refl)). cbn [fst snd] in FW. lia.
- apply IH. intros x Hx. apply FW. right. exact Hx.
Qed.
Lemma lsp_entryA_even : forall k, lsp_entryA k mod 2 = 0 /\ 0 <= lsp_entryA k < 2^64.
Proof. intros []; cbn -[Z.pow Z.modulo Z.lt Z.le]; unfold A_lsp_unquant_lbr, A_lsp_unquant_nb, A_lsp_unquant_high; lia. Qed.

Lemma shadow_acc : forall (m : mem) (f sf : Z) (cs : list cell) (pre rest : list byte) (k : nat),
rw_cells bsegs m sf cs -> cells_bytes cs = pre ++ repeat z8 k ++ rest -> sf = Z.shiftr f 3 + SHB -> f mod 64 = 0 -> 0 <= f ->
acc bsegs m (f + 8 * Z.of_nat (length pre)) (8 * Z.of_nat k).
Proof.
intros m f sf cs pre rest k [[_ B] _] E Esf F64 F0. rewrite E in B.
apply bytes_at_app in B. destruct B as [_ B]. apply bytes_at_app in B. destruct B as [B _].
apply acc_zero_run; [clear - F64; Z.div_mod_to_equations; lia | lia |].
replace (shad (f + 8 * Z.of_nat (length pre))) with (sf + Z.of_nat (length pre)); [exact B|].
rewrite Esf, shad_shiftr. unfold shad. clear - F64. Z.div_mod_to_equations. lia.
Qed.

Lemma lsp_tabs_munch : forall W (m m' : mem), lsp_tabs m -> munch W m m' -> (forall o n, 0x10000 <= o -> o + n <= 0x630200 -> shfree W o n) -> lsp_tabs m'.
Proof.
intros W m m' (T1 & T2 & T3 & T4 & T5 & T6 & T7) MU SF. unfold lsp_tabs, A_cdbk_nb, A_cdbk_nb_low1, A_cdbk_nb_low2, A_cdbk_nb_high1, A_cdbk_nb_high2, A_high_lsp_cdbk, A_high_lsp_cdbk2 in *.
repeat split; (eapply aobj_munch; [eassumption | exact MU | apply SF; lia]).
Qed.
