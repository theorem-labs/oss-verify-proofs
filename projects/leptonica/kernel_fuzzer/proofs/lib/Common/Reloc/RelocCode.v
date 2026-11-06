(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import Reloc.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record cchunk := mkChunk { cc_blk : positive; cc_start : Z; cc_n : Z; cc_words : list (option Z) }.

(* [comment removed for export] *)
Definition fetch_is (segs : list Segment) (a z : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 a) with
  | Some w => Z.eqb (bv_unsigned w) z
  | None => false
  end.

Fixpoint words_check (segs : list Segment) (a : Z) (ws : list (option Z)) : bool :=
  match ws with
  | [] => true
  | None :: ws' => words_check segs (a + 4) ws'
  | Some z :: ws' => fetch_is segs a z && words_check segs (a + 4) ws'
  end.

Definition chunk_check (segs : list Segment) (delta : positive -> Z) (ch : cchunk) : bool :=
  words_check segs (cc_start ch + delta (cc_blk ch)) (cc_words ch).

Definition code_check (segs : list Segment) (delta : positive -> Z) (chs : list cchunk) : bool :=
  forallb (chunk_check segs delta) chs.

(* [comment removed for export] *)
Definition chunk_lookup (ch : cchunk) (b : positive) (c : Z) : option Z :=
  if Pos.eqb b (cc_blk ch) && (cc_start ch <=? c) && (c <? cc_start ch + 4 * cc_n ch) && ((c - cc_start ch) mod 4 =? 0) then
    match nth_error (cc_words ch) (Z.to_nat ((c - cc_start ch) / 4)) with
    | Some (Some z) => Some z
    | _ => None
    end
  else None.

Fixpoint code_lookup (chs : list cchunk) (b : positive) (c : Z) : option Z :=
  match chs with
  | [] => None
  | ch :: chs' => match chunk_lookup ch b c with Some z => Some z | None => code_lookup chs' b c end
  end.

Definition code_has (chs : list cchunk) (b : positive) (c z : Z) : bool :=
  match code_lookup chs b c with Some z' => Z.eqb z z' | None => false end.

(* [comment removed for export] *)
Definition chunk_has (ch : cchunk) (c z : Z) : bool :=
  match chunk_lookup ch (cc_blk ch) c with Some z' => Z.eqb z z' | None => false end.

(* [comment removed for export] *)
Fixpoint code_find (chs : list cchunk) (i : nat) (b : positive) (c : Z) : option (nat * Z) :=
  match chs with
  | [] => None
  | ch :: chs' => match chunk_lookup ch b c with Some z => Some (i, z) | None => code_find chs' (S i) b c end
  end.

Lemma words_check_nth : forall segs ws a n z,
  words_check segs a ws = true -> nth_error ws n = Some (Some z) ->
  fetch_is segs (a + 4 * Z.of_nat n) z = true.
Proof.
  intros segs ws. induction ws as [|o ws IH]; intros a n z Hc Hn.
  - destruct n; discriminate Hn.
  - destruct n as [|n].
    + cbn [nth_error] in Hn. injection Hn as ->. cbn [words_check] in Hc.
      apply andb_prop in Hc as [Hc _]. replace (a + 4 * Z.of_nat 0) with a by lia. exact Hc.
    + cbn [nth_error] in Hn.
      assert (Hc' : words_check segs (a + 4) ws = true).
      { destruct o; cbn [words_check] in Hc; [apply andb_prop in Hc as [_ Hc]|]; exact Hc. }
      replace (a + 4 * Z.of_nat (S n)) with (a + 4 + 4 * Z.of_nat n) by lia.
      exact (IH _ _ _ Hc' Hn).
Qed.

Lemma fetch_is_sound : forall segs a z (w : bv 32),
  fetch_is segs a z = true -> bv_unsigned w = z -> fetch_word segs (Z_to_bv 64 a) = Some w.
Proof.
  intros segs a z w H Hw. unfold fetch_is in H.
  destruct (fetch_word segs (Z_to_bv 64 a)) as [w'|]; [|discriminate H].
  apply Z.eqb_eq in H. f_equal. apply bv_eq. lia.
Qed.

Lemma chunk_lookup_sound : forall segs delta ch b c z (w : bv 32),
  chunk_check segs delta ch = true -> chunk_lookup ch b c = Some z -> bv_unsigned w = z ->
  fetch_word segs (rl (delta b) c) = Some w.
Proof.
  intros segs delta ch b c z w Hch Hcl Hw. unfold chunk_lookup in Hcl.
  destruct (Pos.eqb b (cc_blk ch) && (cc_start ch <=? c) && (c <? cc_start ch + 4 * cc_n ch) && ((c - cc_start ch) mod 4 =? 0)) eqn:G; [|discriminate Hcl].
  apply andb_prop in G as [G G3]. apply andb_prop in G as [G _]. apply andb_prop in G as [G1 G2].
  apply Pos.eqb_eq in G1. apply Z.leb_le in G2. apply Z.eqb_eq in G3. subst b.
  destruct (nth_error (cc_words ch) (Z.to_nat ((c - cc_start ch) / 4))) as [[z0|]|] eqn:Hn; try discriminate Hcl.
  injection Hcl as ->.
  pose proof (words_check_nth _ _ _ _ _ Hch Hn) as Hf.
  rewrite Z2Nat.id in Hf by (apply Z.div_pos; lia).
  pose proof (Z.div_mod (c - cc_start ch) 4 ltac:(lia)) as Hdm.
  replace (cc_start ch + delta (cc_blk ch) + 4 * ((c - cc_start ch) / 4)) with (c + delta (cc_blk ch)) in Hf by lia.
  unfold rl. exact (fetch_is_sound _ _ _ w Hf Hw).
Qed.

Theorem chunk_sound : forall segs delta chs (i : nat) ch c (w : bv 32),
  code_check segs delta chs = true -> nth_error chs i = Some ch ->
  chunk_has ch c (bv_unsigned w) = true ->
  fetch_word segs (rl (delta (cc_blk ch)) c) = Some w.
Proof.
  intros segs delta chs i ch c w Hck Hi Hhas. unfold chunk_has in Hhas.
  destruct (chunk_lookup ch (cc_blk ch) c) as [z|] eqn:Hl; [|discriminate Hhas].
  apply Z.eqb_eq in Hhas.
  unfold code_check in Hck. rewrite forallb_forall in Hck.
  exact (chunk_lookup_sound segs delta ch _ c z w (Hck ch (nth_error_In _ _ Hi)) Hl Hhas).
Qed.

Theorem code_sound : forall segs delta chs b c (w : bv 32),
  code_check segs delta chs = true ->
  code_has chs b c (bv_unsigned w) = true ->
  fetch_word segs (rl (delta b) c) = Some w.
Proof.
  intros segs delta chs b c w Hck Hhas. unfold code_has in Hhas.
  destruct (code_lookup chs b c) as [z|] eqn:Hl; [|discriminate Hhas].
  apply Z.eqb_eq in Hhas.
  induction chs as [|ch chs IH]; [discriminate Hl|].
  cbn [code_check forallb] in Hck. apply andb_prop in Hck as [Hch Hck].
  cbn [code_lookup] in Hl.
  destruct (chunk_lookup ch b c) as [z0|] eqn:Hcl.
  - injection Hl as ->. exact (chunk_lookup_sound segs delta ch b c z w Hch Hcl Hhas).
  - exact (IH Hck Hl).
Qed.

Lemma code_find_sound : forall chs i0 b c i z,
  code_find chs i0 b c = Some (i, z) -> code_lookup chs b c = Some z.
Proof.
  induction chs as [|ch chs IH]; intros i0 b c i z H; [discriminate H|].
  cbn [code_find] in H. cbn [code_lookup].
  destruct (chunk_lookup ch b c) as [z0|]; [injection H as _ ->; reflexivity | exact (IH _ _ _ _ _ H)].
Qed.
