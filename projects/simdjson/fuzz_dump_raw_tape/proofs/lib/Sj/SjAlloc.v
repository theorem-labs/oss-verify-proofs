(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition roundup64 (x : Z) : Z := (x + 63) / 64 * 64.
Definition cap (len : Z) : Z := Z.max len 32.
Definition sz_sbuf (len : Z) : Z := roundup64 (5 * (cap len / 3) + 64).
Definition tape_words (len : Z) : Z := roundup64 (cap len + 3).
Definition sz_tape (len : Z) : Z := 8 * tape_words len.
Definition sz_impl : Z := 96.
Definition idx_words (len : Z) : Z := roundup64 (cap len) + 9.
Definition sz_idx (len : Z) : Z := 4 * idx_words len.
Definition sz_oc : Z := 8192.
Definition sz_ia : Z := 1024.
Definition sz_copy (len : Z) : Z := len + 64.
Definition PADMAX : Z := 1048512.

Lemma roundup64_ge : forall x, x <= roundup64 x.
Proof. intros x. unfold roundup64. pose proof (Z.div_mod (x + 63) 64). pose proof (Z.mod_pos_bound (x + 63) 64). lia. Qed.

Lemma roundup64_lt : forall x, roundup64 x < x + 64.
Proof. intros x. unfold roundup64. pose proof (Z.div_mod (x + 63) 64). pose proof (Z.mod_pos_bound (x + 63) 64). lia. Qed.

Lemma roundup64_mod : forall x, roundup64 x mod 64 = 0.
Proof. intros x. unfold roundup64. apply Z.mod_mul. lia. Qed.

Lemma cap_ge : forall len, len <= cap len /\ 32 <= cap len.
Proof. intros; unfold cap; lia. Qed.

Inductive aev : Type :=
| ANew    (size : Z)
| ANewArr (size : Z)
| ADel    (size : Z)
| ADelArr (size : Z).

Definition strip_bom (payload : list Z) : list Z :=
  match payload with 239 :: 187 :: 191 :: r => r | _ => payload end.

Definition is_numstart_b (b : Z) : bool := (b =? 45) || ((48 <=? b) && (b <=? 57)).
Definition root_copy (bs : list Z) (s1code idx0 : Z) : option Z :=
  if (s1code =? 0) && is_numstart_b (B bs idx0) then Some (blen bs - idx0 + 64) else None.

Definition alloc_seq (payload : list Z) (s1code idx0 : Z) : list aev :=
  let len := blen payload in
  [ANewArr (sz_sbuf len); ANewArr (sz_tape len); ANew sz_impl; ANewArr (sz_idx len); ANewArr sz_oc; ANewArr sz_ia]
  ++ (if len <=? PADMAX
      then [ANewArr (sz_copy len)]
           ++ match root_copy (strip_bom payload) s1code idx0 with Some c => [ANewArr c; ADelArr c] | None => [] end
           ++ [ADelArr (sz_copy len)]
      else [])
  ++ [ADelArr (sz_sbuf len); ADelArr (sz_tape len); ADelArr sz_ia; ADelArr sz_oc; ADelArr (sz_idx len); ADel sz_impl].

Lemma blen_strip_bom : forall payload, blen (strip_bom payload) <= blen payload.
Proof.
  intros payload. unfold strip_bom, blen.
  repeat (match goal with |- context [match ?x with _ => _ end] => destruct x; simpl length; try lia end).
Qed.

Section Caps.
  Variables (len l' : Z).
  Hypothesis Hl : 0 <= l' <= len.

  Lemma tape_cap_ok : l' + 3 <= tape_words len.
  Proof. unfold tape_words. pose proof (roundup64_ge (cap len + 3)). pose proof (cap_ge len). lia. Qed.

  Lemma sbuf_cap_ok : 5 * l' + 5 <= 3 * sz_sbuf len.
  Proof.
    unfold sz_sbuf. pose proof (roundup64_ge (5 * (cap len / 3) + 64)). pose proof (cap_ge len).
    pose proof (Z.div_mod (cap len) 3). pose proof (Z.mod_pos_bound (cap len) 3). lia.
  Qed.

  Lemma idx_cap_ok : forall n, n <= l' -> n + 3 <= idx_words len.
  Proof. intros n Hn. unfold idx_words. pose proof (roundup64_ge (cap len)). pose proof (cap_ge len). lia. Qed.
End Caps.

Definition LENMAX : Z := 67108858.

Section Bounds.
  Variable len : Z.
  Hypothesis Hlen : 0 <= len < LENMAX.

  Lemma sz_tape_le : sz_tape len <= 536870912.
  Proof.
    unfold sz_tape, tape_words, LENMAX in *. pose proof (roundup64_lt (cap len + 3)). pose proof (roundup64_mod (cap len + 3)).
    unfold cap in *. assert (roundup64 (Z.max len 32 + 3) <= 67108864); [|lia].
    assert (H64 : roundup64 (Z.max len 32 + 3) < 67108864 + 64) by lia.
    pose proof (Z.div_mod (roundup64 (Z.max len 32 + 3)) 64). lia.
  Qed.

  Lemma sz_sbuf_le : sz_sbuf len <= 111848192.
  Proof.
    unfold sz_sbuf, LENMAX in *. pose proof (roundup64_lt (5 * (cap len / 3) + 64)). pose proof (roundup64_mod (5 * (cap len / 3) + 64)).
    unfold cap in *. pose proof (Z.div_mod (Z.max len 32) 3). pose proof (Z.mod_pos_bound (Z.max len 32) 3).
    pose proof (Z.div_mod (roundup64 (5 * (Z.max len 32 / 3) + 64)) 64). lia.
  Qed.

  Lemma sz_idx_le : sz_idx len <= 268435492.
  Proof.
    unfold sz_idx, idx_words, LENMAX in *. pose proof (roundup64_lt (cap len)). pose proof (roundup64_mod (cap len)). unfold cap in *.
    pose proof (Z.div_mod (roundup64 (Z.max len 32)) 64). lia.
  Qed.

  Lemma sizes_pos : 0 < sz_sbuf len /\ 0 < sz_tape len /\ 0 < sz_idx len /\ 0 < sz_copy len.
  Proof.
    unfold sz_sbuf, sz_tape, tape_words, sz_idx, idx_words, sz_copy.
    pose proof (roundup64_ge (5 * (cap len / 3) + 64)). pose proof (roundup64_ge (cap len + 3)). pose proof (roundup64_ge (cap len)).
    pose proof (cap_ge len). pose proof (Z.div_pos (cap len) 3). lia.
  Qed.

  Definition live_peak : Z :=
    sz_sbuf len + sz_tape len + sz_impl + sz_idx len + sz_oc + sz_ia + (if len <=? PADMAX then 2 * sz_copy len else 0).

  Lemma live_peak_le : live_peak <= 917163908.
  Proof.
    unfold live_peak. pose proof sz_tape_le. pose proof sz_sbuf_le. pose proof sz_idx_le.
    unfold sz_impl, sz_oc, sz_ia, sz_copy, PADMAX. destruct (len <=? 1048512) eqn:E; [apply Z.leb_le in E|lia].

    clear H H0 H1. unfold sz_sbuf, sz_tape, tape_words, sz_idx, idx_words.
    pose proof (roundup64_lt (5 * (cap len / 3) + 64)). pose proof (roundup64_lt (cap len + 3)). pose proof (roundup64_lt (cap len)).
    unfold cap in *. pose proof (Z.div_mod (Z.max len 32) 3). pose proof (Z.mod_pos_bound (Z.max len 32) 3). lia.
  Qed.

  Lemma live_peak_small : len <= PADMAX -> live_peak <= 17300000.
  Proof.
    intros Hs. unfold live_peak, sz_impl, sz_oc, sz_ia, sz_copy, PADMAX in *.
    destruct (len <=? 1048512) eqn:E; [|apply Z.leb_gt in E; lia].
    unfold sz_sbuf, sz_tape, tape_words, sz_idx, idx_words.
    pose proof (roundup64_lt (5 * (cap len / 3) + 64)). pose proof (roundup64_lt (cap len + 3)). pose proof (roundup64_lt (cap len)).
    unfold cap in *. pose proof (Z.div_mod (Z.max len 32) 3). pose proof (Z.mod_pos_bound (Z.max len 32) 3). lia.
  Qed.
End Bounds.

Lemma root_copy_le : forall bs s1code idx0 c, 0 <= idx0 -> root_copy bs s1code idx0 = Some c -> c <= blen bs + 64.
Proof.
  intros bs s1code idx0 c H0 H. unfold root_copy in H.
  destruct ((s1code =? 0) && is_numstart_b (B bs idx0)); inversion H; subst; lia.
Qed.
