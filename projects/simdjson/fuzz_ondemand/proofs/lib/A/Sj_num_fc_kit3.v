(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Sj_num_fc_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma fc_sx32_small : forall x, (0 <= x < 2147483648)%Z -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_id by lia. reflexivity. Qed.

Lemma fc_c8_split_lo : forall segs (m : mem) A d, rw_cells segs m A [C8 (Z_to_bv 64 d)] -> (0 <= d < 4294967296)%Z ->
  rw_cells segs m A [C4 (Z_to_bv 64 d); C4 (Z_to_bv 64 0)].
Proof.
  intros segs m A d [[Hwf Hb] Hw] Hd. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in Hb.
    replace (le4 (Z_to_bv 64 d) ++ le4 (Z_to_bv 64 0) ++ []) with (le8 (Z_to_bv 64 d)); [exact Hb|].
    unfold le8, word_to_le_bytes, le4. rewrite !unsigned_lit by lia.
    cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia.
    assert (HS : forall k, (32 <= k)%Z -> Z.shiftr d k = 0%Z).
    { intros k Hk. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. split; [lia|].
      assert (2 ^ 32 <= 2 ^ k)%Z by (apply Z.pow_le_mono_r; lia). change (2 ^ 32)%Z with 4294967296%Z in *. lia. }
    rewrite (HS (8 + 8 + 8 + 8)%Z), (HS (8 + 8 + 8 + 8 + 8)%Z), (HS (8 + 8 + 8 + 8 + 8 + 8)%Z), (HS (8 + 8 + 8 + 8 + 8 + 8 + 8)%Z) by lia. rewrite !Z.shiftr_0_l.
    reflexivity.
  - exact Hw.
Qed.

Definition fc_sub (A FIRST LAST : Z) (txt : list byte) : list byte := firstn (Z.to_nat (LAST - FIRST)) (skipn (Z.to_nat (FIRST - A)) txt).

Lemma fc_sub_length : forall A FIRST LAST txt, A <= FIRST -> FIRST <= LAST -> LAST <= A + Z.of_nat (length txt) ->
  Z.of_nat (length (fc_sub A FIRST LAST txt)) = LAST - FIRST.
Proof. intros A FIRST LAST txt H1 H2 H3. unfold fc_sub. rewrite length_firstn, length_skipn. lia. Qed.

Lemma fc_sub_bytes : forall segs (m : mem) A FIRST LAST txt, A <= FIRST -> FIRST <= LAST -> LAST <= A + Z.of_nat (length txt) ->
  bytes_at segs m A txt -> bytes_at segs m FIRST (fc_sub A FIRST LAST txt).
Proof.
  intros segs m A FIRST LAST txt H1 H2 H3 HB. unfold fc_sub.
  replace FIRST with (A + Z.of_nat (Z.to_nat (FIRST - A))) at 1 by lia.
  apply bytes_at_sub; [exact HB | lia].
Qed.

Lemma fpfacts_spans_sub : forall A txt FIRST LAST IP IL FPT FL, A <= FIRST -> FIRST <= LAST -> LAST <= A + Z.of_nat (length txt) ->
  fpfacts A txt FIRST LAST IP IL FPT FL -> pm_spans_ok FIRST (fc_sub A FIRST LAST txt) IP IL FPT FL.
Proof.
  intros A txt FIRST LAST IP IL FPT FL H1 H2 H3 ((P1 & P2 & P3) & _ & PD). unfold pm_spans_ok.
  rewrite (fc_sub_length A FIRST LAST txt H1 H2 H3).
  destruct PD as [[-> ->] | [(-> & F1 & F2 & _) _]].
  - split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
  - split; [lia|]. split; [lia|]. split; [lia|]. right. lia.
Qed.

Lemma fc_exp32 : forall qe dg, -342 <= qe <= 330 -> 0 <= dg <= 770 ->
  bv_swrap 32 (bv_swrap 32 (qe mod 18446744073709551616 - bv_unsigned (sx32 (Z_to_bv 64 dg))) mod 18446744073709551616 + 1) = qe - dg + 1.
Proof.
  intros qe dg Hq Hd. rewrite (fc_sx32_small dg) by lia. rewrite unsigned_lit by lia.
  rewrite bv_swrap32. unfold swrap32. rewrite bv_swrap32. unfold swrap32.
  assert (E1 : (qe mod 18446744073709551616 - dg + 2147483648) mod 4294967296 = qe - dg + 2147483648).
  { destruct (Z_lt_le_dec qe 0).
    - replace (qe mod 18446744073709551616) with (qe + 18446744073709551616) by (apply (Z.mod_unique _ _ (-1)); lia).
      symmetry. apply (Z.mod_unique _ _ 4294967296); lia.
    - rewrite (Z.mod_small qe) by lia. apply Z.mod_small. lia. }
  rewrite E1. replace (qe - dg + 2147483648 - 2147483648) with (qe - dg) by lia.
  destruct (Z_lt_le_dec (qe - dg) 0).
  - replace ((qe - dg) mod 18446744073709551616) with (qe - dg + 18446744073709551616) by (apply (Z.mod_unique _ _ (-1)); lia).
    replace ((qe - dg + 18446744073709551616 + 1 + 2147483648) mod 4294967296) with (qe - dg + 1 + 2147483648) by (apply (Z.mod_unique _ _ 4294967296); lia).
    lia.
  - rewrite (Z.mod_small (qe - dg)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
