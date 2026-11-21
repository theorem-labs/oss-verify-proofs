(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Tac.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require SysStep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Walk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require ITree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Common Require SFModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM11.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM14.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Common Require RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Bytes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM07.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM12.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM10.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ASlot_W12.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import F_malloc_entry. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2.
Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import ASlot_W1. Import MM08.ASlot_W10.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.

Lemma stc_q_eq : j = stc_q (szc * cnt).
Proof.
  unfold j, n'. rewrite size_to_class_q by nia. f_equal. Z.div_mod_to_equations. nia.
Qed.
End STC.

Definition nest_frame (j gm cnt size sc : Z) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (wz j); C8 (Z_to_bv 64 gm); C8 (wz cnt); C8 (wz cnt); C8 (wz size); C8 (Z_to_bv 64 (sc + 58)); C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

End CANSEC1.
End ASlot_W12.

Module ASlot_W14.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Arr. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Bytes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import F_malloc_entry. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2. Import MM08. Import MM08.F_malloc_bigw. Import MM07. Import MM07.F_malloc_big.
Import MM08. Import MM08.MallocKit_A3.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1. Context {rc : runConstT}.
Lemma land_high_low x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.land (x * 2^k) y = 0.
Proof.
  intros Hx Hk Hy. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n k) as [LT|GE].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit y n) with false; [apply Bool.andb_false_r|].
    symmetry. destruct (Z.eq_dec y 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ k); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_shl_small x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.lor (x * 2^k) y = x * 2^k + y.
Proof. intros. apply lor_disjoint_add. apply land_high_low; assumption. Qed.

Lemma lor_small_shl x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.lor y (x * 2^k) = x * 2^k + y.
Proof. intros. rewrite Z.lor_comm. apply lor_shl_small; assumption. Qed.

Lemma lor_32 c : 0 <= c < 32 -> Z.lor c 32 = c + 32.
Proof. intros. change 32 with (1 * 2^5) at 1. rewrite lor_small_shl by lia. lia. Qed.

Lemma land_pg_mask q : 0 <= q < 2^52 -> Z.land (4096 * q) 18446744073709547520 = 4096 * q.
Proof.
  intros Hq. replace (4096 * q) with (Z.shiftl q 12) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  change 18446744073709547520 with (Z.shiftl (Z.ones 52) 12).
  rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma hdr_byte_facts x ai : 0 <= x < 256 -> 0 <= ai < 32 ->
  0 <= Z.lor (Z.land x 18446744073709551584) ai < 256 /\ Z.land (Z.lor (Z.land x 18446744073709551584) ai) 31 = ai.
Proof.
  intros Hx Hai.
  assert (E : Z.land x 18446744073709551584 = Z.land x 224).
  { replace x with (Z.land x 255) at 1 by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    rewrite <- !Z.land_assoc. reflexivity. }
  rewrite E. pose proof (land_upper x 224 ltac:(lia) ltac:(lia)).
  split.
  - change 256 with (2^8). apply lor_lt_pow2; lia.
  - rewrite Z.land_lor_distr_l. rewrite <- Z.land_assoc. change (Z.land 224 31) with 0. rewrite Z.land_0_r. rewrite Z.lor_0_l.
    change 31 with (Z.ones 5). rewrite Z.land_ones, Z.mod_small by lia. reflexivity.
Qed.

Lemma tail_low16 sc cnt q : 0 <= sc < 48 -> 1 <= cnt <= 32 -> 0 <= q < 16 ->
  Z.lor (Z.lor (Z.land sc 63 * 2^6) (Z.lor (Z.land (cnt - 1) 31) 32)) (Z.land (4096 * q) 18446744073709547520)
  = (cnt - 1) + 32 + 64 * sc + 4096 * q.
Proof.
  intros Hsc Hc Hq.
  replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  rewrite land_pg_mask by lia.
  replace 32 with (1 * 2^5) at 1 by reflexivity. rewrite (lor_small_shl 1 5 (cnt - 1)) by lia.
  rewrite (lor_shl_small sc 6) by (cbn; lia).
  replace (4096 * q) with (q * 2^12) by (cbn; lia). rewrite (lor_small_shl q 12) by (cbn; lia). cbn. lia.
Qed.

Lemma firstn_le_bytes n k z : firstn n (Z_to_le_bytes (n + k) z) = Z_to_le_bytes n z.
Proof. revert z. induction n as [|n IH]; intros z; [reflexivity|]. cbn [Z_to_le_bytes Nat.add firstn]. f_equal. apply IH. Qed.

Lemma skipn_le_bytes n k z : skipn n (Z_to_le_bytes (n + k) z) = Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  revert z. induction n as [|n IH]; intros z.
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Z_to_le_bytes Nat.add skipn]. rewrite IH. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma tail_word_bytes (s0r : word) (L W W' : Z) :
  0 <= W < 2^64 -> 0 <= W' < 2^64 -> 0 <= L < 65536 ->
  bv_unsigned s0r mod 65536 = L -> W' mod 65536 = L -> Z.shiftr W' 16 = Z.shiftr W 16 ->
  le2 s0r ++ skipn 2 (le8 (wz W)) = le8 (wz W').
Proof.
  intros HW HW' HL HS HM HH.
  unfold le2, le8, word_to_le_bytes, wz. rewrite !unsigned_lit by lia.
  change 8%nat with (2 + 6)%nat. rewrite skipn_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul].
  rewrite <- (firstn_skipn 2 (Z_to_le_bytes (2 + 6) W')). rewrite firstn_le_bytes, skipn_le_bytes.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]. rewrite HH. f_equal.
  rewrite <- (Z_to_le_bytes_mod 2 (bv_unsigned s0r) 16) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 2 W' 16) by (cbn; lia).
  change (2^16) with 65536. rewrite HS, HM. reflexivity.
Qed.

Lemma word_low16_bytes W : 0 <= W < 2^64 -> firstn 2 (le8 (wz W)) = le2 (wz (W mod 65536)).
Proof.
  intros HW. unfold le2, le8, word_to_le_bytes, wz. rewrite !unsigned_lit by (try lia; Z.div_mod_to_equations; lia).
  change 8%nat with (2 + 6)%nat. rewrite firstn_le_bytes.
  change 65536 with (2^16). rewrite Z_to_le_bytes_mod by (cbn; lia). reflexivity.
Qed.

Lemma sllw2_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (i mod 32))) = wz (sxv (2 ^ (i + 1))).
Proof.
  intros Hi. rewrite Z.mod_small by lia. change 2 with (2^1) at 1. rewrite Z.shiftl_mul_pow2, <- Z.pow_add_r by lia.
  replace (1 + i) with (i + 1) by lia. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma subw_sxv_word a b : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv a)) - bv_unsigned (wz (sxv b)))) = wz (sxv (a - b)).
Proof.
  rewrite !wz_unsigned by (apply sxv_range). unfold wz, sxv.
  rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (bv_swrap 32 a mod 2 ^ 64 - bv_swrap 32 b mod 2 ^ 64))). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.

Lemma cell_read_hdr_havoc_old : forall st b o,
  snd b mod 16 = 0 -> 0 <= o < 12 ->
  (forall v t, (r_cells (get_shadow st (fst b))) !! (snd b + o) = Some (v, t) -> (t < s_tick st)%N) ->
  exists h, cell_read (get_shadow (hdr_havoc b st) (fst b)) (snd b + o) = Unknown h.
Proof.
  intros st b o B16 Ho OLD. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id].
  unfold cell_read. cbn [r_cells r_hav r_havp].
  replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
  rewrite lookup_insert_eq. cbn [default from_option id].
  replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
  unfold hav_add. unfold stale. cbn [existsb fst snd].
  replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  destruct (r_cells (get_shadow st (fst b)) !! (snd b + o)) as [[v t]|] eqn:E.
  - specialize (OLD v t eq_refl). replace (t <? s_tick st)%N with true by (symmetry; apply N.ltb_lt; exact OLD).
    cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
  - cbn [orb]. rewrite Bool.orb_true_r. eexists; reflexivity.
Qed.

Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
  (r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

Definition stA : mstate := hdr_havoc p stT.
Definition stB : mstate := set_usage sc (usage stT sc + cnt) stA.
Definition recA : meta := mkMeta None None (Some p) AV FR 0 0 0 ml.
Definition stC : mstate := put_meta mt recA stB.
Definition stD : mstate := put_group p (Some mt) ai stC.
Definition recF : meta := mkMeta (Some mt) (Some mt) (Some p) (AV - 1) FR (cnt - 1) 1 sc ml.
Definition stE : mstate := put_meta mt recF stD.
Definition stFin : mstate := set_active sc (Some mt) stE.

Definition st_model : mstate :=
  let st := hdr_havoc p stT in
  let st1 := set_usage sc (usage st sc + cnt) st in
  let avail := mask_upto ai in
  let freed := mask_upto (cnt - 1) - avail in
  let st2 := upd_meta mt (fun r =>
               m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
               (m_set_mem (Some p) (m_set_freed freed (m_set_avail avail r)))))) st1 in
  let st3 := put_group p (Some mt) ai st2 in
  let st4 := add_slots mt p (get_stride (get_meta_rec st3 mt)) cnt st3 in
  let st5 := upd_meta mt (fun r => m_set_avail (m_avail r - 1) r) st4 in
  let st6 := upd_meta mt (fun r => m_set_prev (Some mt) (m_set_next (Some mt) r)) st5 in
  set_active sc (Some mt) st6.

Lemma mask_upto_range k : 0 <= k <= 31 -> 1 <= mask_upto k < 2^32 /\ 2^k <= mask_upto k.
Proof.
  intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
  assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
  assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
  change (2^32) with (2 * 2^31). lia.
Qed.

Lemma AV_FR_range : 1 <= AV < 2^32 /\ 0 <= FR < 2^32 /\ 0 <= AV - 1 < 2^32.
Proof.
  pose proof (mask_upto_range ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range (cnt - 1) ltac:(lia)) as [C1 C2].
  assert (mask_upto ai <= mask_upto (cnt - 1)).
  { unfold mask_upto. apply Z.sub_le_mono_r. apply Z.pow_le_mono_r; lia. }
  unfold AV, FR. lia.
Qed.

Lemma rec_set_slots st v q : get_meta_rec (set_slots v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma rec_put_group st b g a q : get_meta_rec (put_group b g a st) q = get_meta_rec st q. Proof. reflexivity. Qed.
Lemma rec_hdr_havoc st b q : get_meta_rec (hdr_havoc b st) q = get_meta_rec st q. Proof. reflexivity. Qed.

Lemma st_model_eq_rec q : get_meta_rec st_model q = get_meta_rec stFin q.
Proof.
  unfold st_model, stFin, stE, stD, stC, stB, stA. cbv zeta. unfold upd_meta, add_slots.
  rewrite !rec_set_active.
  destruct (decide (q = mt)) as [->|NE].
  - rewrite !get_meta_rec_put_same, rec_set_slots, rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC.
    unfold recF. cbv [m_set_prev m_set_next m_set_avail m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen].
    replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
    change (Z.land 1 1) with 1. reflexivity.
  - rewrite !get_meta_rec_put_other, rec_set_slots, !rec_put_group, !get_meta_rec_put_other by congruence. reflexivity.
Qed.

Definition tailW : list (Z * Z) :=
  [(CTX + 464 + 8 * sc, CTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (CTX + 80 + 8 * sc, CTX + 80 + 8 * sc + 8)]%Z.
End TAIL.


End CANSEC1.
End ASlot_W14.

Module F_free_C.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM12. Import MM12.F_mm_syscalls.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocTree.
Import MM13. Import MM13.MallocKit_B. Import MM12. Import MM12.MallocModel_B. Import MM14. Import MM14.MallocKit_B3. Import MM10. Import MM10.F_ntf_D.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma le4_sx32 (v : word) : le4 (sx32 v) = le4 v.
Proof.
  apply le4_congr. unfold sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite mod64_mod32, swrap32_eq'.
  set (u := bv_unsigned v) in *. clearbody u. Z.div_mod_to_equations. lia.
Qed.

End CANSEC1.
End F_free_C.
