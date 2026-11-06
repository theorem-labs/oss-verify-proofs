(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* RELOCATED B -> B' (h-pre-b3's #102 row, 2026-10-29): the walk of origin/cold/h-pre-b3-exstring-b 5f62ea0b5c45 (OLD
   pin f8f98a95, unstripped twin 3b5e1a09) moved to the #102 pin B' (asan-ubsan d663f82d7f48, unstripped twin
   c90d4fa54d43, facts 8f3e7e1a07f1) by alreloc c4338d099cfb8025 (cold/c-asan-tools d99acc3edd9), on int102 with the kit
   decff67d721f. ex_string, ex_hex4 and ex_utf8 have equal instruction words on B and B' up to pc-relative fields,
   and every pc-relative target names the same symbol + offset. Every address in this file, in a comment or in a term, is the B' image's; a mention of the record image
   f8f98a95 below names the donor's image. *)
(* Theorem Labs, 2026-10: fuzz_preset, ex_string's walk on image B: the PURE part. The model of ex_string is
   PjGrammar.jr_string at the empty outcome list (tex_string_specX, PRH_FnEx.v:263), which is PjGrammar.decode; and one
   step of decode per arm of the C loop (fuzz_preset.c :165-206), in the form the walk's branches meet them. No
   program, no memory. *)
From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
Import ListNotations.
Local Open Scope Z_scope.

(* at the empty outcome list jalloc succeeds, so jr_string's value is decode's *)
Lemma exs_jr_decode : forall xs, fst (fst (jr_string xs [])) = decode xs.
Proof.
intros xs. unfold jr_string. destruct (scan xs) as [q|] eqn:Hs.
- unfold jbind, jalloc, take, jret, jfree, jrefuse. cbn. destruct (decode xs) as [[s r]|]; reflexivity.
- unfold jrefuse. cbn. destruct (decode xs) as [[s r]|] eqn:Hd; [|reflexivity].
  destruct (decode_stop xs s r Hd) as (q & Hq & _). rewrite Hq in Hs. discriminate.
Qed.

Lemma exs_emit_app : forall a b d, emit a (emit b d) = emit (a ++ b) d.
Proof. intros a b [[s r]|]; cbn; [rewrite app_assoc|]; reflexivity. Qed.
Lemma exs_emit_nil : forall d, emit [] d = d.
Proof. intros [[s r]|]; reflexivity. Qed.
Lemma exs_emit_none : forall a, emit a None = None.
Proof. reflexivity. Qed.

(* ---- one step of decode, per arm ---- *)
Lemma exs_dec_quote : forall r, decode (34 :: r) = Some ([], r).
Proof. reflexivity. Qed.
Lemma exs_dec_ctl : forall c r, c < 32 -> decode (c :: r) = None.
Proof.
intros c r Hc. cbn [decode].
destruct (Z.eqb_spec c 34); [lia|]. destruct (Z.ltb_spec c 32); [reflexivity | lia].
Qed.
Lemma exs_dec_plain : forall c r, 32 <= c -> c <> 34 -> c <> 92 -> decode (c :: r) = emit [c] (decode r).
Proof.
intros c r H1 H2 H3. cbn [decode].
destruct (Z.eqb_spec c 34); [lia|]. destruct (Z.ltb_spec c 32); [lia|].
destruct (Z.eqb_spec c 92); [lia|]. reflexivity.
Qed.
Lemma exs_dec_bs_end : decode [92] = None.
Proof. reflexivity. Qed.
Lemma exs_dec_esc : forall e r, e <> 117 ->
  decode (92 :: e :: r) = match escape e with Some c => emit [c] (decode r) | None => None end.
Proof. intros e r He. cbn [decode]. destruct (Z.eqb_spec e 117); [lia|]. reflexivity. Qed.

(* the escape table against the code's dispatch (B 0x84480-0x84498, 0x845dc-0x84610, 0x84638-0x84644) *)
Lemma exs_escape_none : forall e,
  e <> 34 -> e <> 92 -> e <> 47 -> e <> 98 -> e <> 102 -> e <> 110 -> e <> 114 -> e <> 116 -> escape e = None.
Proof.
intros e H1 H2 H3 H4 H5 H6 H7 H8. unfold escape.
repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b); [lia|] end. reflexivity.
Qed.

(* `\u`: the four digits *)
Lemma exs_dec_u_short : forall r2, (length r2 < 4)%nat -> decode (92 :: 117 :: r2) = None.
Proof. intros [|a [|b [|c [|d r]]]] H; cbn in H; try lia; reflexivity. Qed.
Lemma exs_dec_u_nohex : forall r2, hex4 r2 = None -> decode (92 :: 117 :: r2) = None.
Proof.
intros [|a [|b [|c [|d r]]]] H; try reflexivity. cbn [decode]. change (117 =? 117) with true. cbv iota.
rewrite H. reflexivity.
Qed.
Lemma exs_dec_u_zero : forall r2, hex4 r2 = Some 0 -> decode (92 :: 117 :: r2) = None.
Proof.
intros [|a [|b [|c [|d r]]]] H; try discriminate. cbn [decode]. change (117 =? 117) with true. cbv iota.
rewrite H. reflexivity.
Qed.
Lemma exs_dec_u_low : forall r2 cp, hex4 r2 = Some cp -> 56320 <= cp < 57344 -> decode (92 :: 117 :: r2) = None.
Proof.
intros [|a [|b [|c [|d r]]]] cp H Hc; try discriminate. cbn [decode]. change (117 =? 117) with true. cbv iota.
rewrite H. destruct (Z.eqb_spec cp 0); [reflexivity|].
destruct (Z.leb_spec 55296 cp), (Z.ltb_spec cp 56320); cbn [andb]; try lia.
destruct (Z.leb_spec 56320 cp), (Z.ltb_spec cp 57344); cbn [andb]; try lia. reflexivity.
Qed.
Lemma exs_dec_u_bmp : forall r2 cp, hex4 r2 = Some cp -> cp <> 0 -> ~ (55296 <= cp < 57344) ->
  decode (92 :: 117 :: r2) = emit (utf8 cp) (decode (skipn 4 r2)).
Proof.
intros [|a [|b [|c [|d r]]]] cp H H0 Hc; try discriminate. cbn [decode skipn]. change (117 =? 117) with true.
cbv iota. rewrite H. destruct (Z.eqb_spec cp 0); [lia|].
destruct (Z.leb_spec 55296 cp), (Z.ltb_spec cp 56320); cbn [andb]; try lia;
destruct (Z.leb_spec 56320 cp), (Z.ltb_spec cp 57344); cbn [andb]; try lia; reflexivity.
Qed.
(* the high surrogate: six more bytes `\uXXXX` *)
Lemma exs_dec_u_hi : forall r2 cp, hex4 r2 = Some cp -> 55296 <= cp < 56320 ->
  decode (92 :: 117 :: r2) =
  match skipn 4 r2 with
  | _ :: _ :: _ :: _ :: _ :: _ :: r4 =>
      match low (skipn 4 r2) with Some lo => emit (utf8 (pair_cp cp lo)) (decode r4) | None => None end
  | _ => None
  end.
Proof.
intros [|a [|b [|c [|d r]]]] cp H Hc; try discriminate. cbn [decode skipn]. change (117 =? 117) with true.
cbv iota. rewrite H. destruct (Z.eqb_spec cp 0); [lia|].
destruct (Z.leb_spec 55296 cp), (Z.ltb_spec cp 56320); cbn [andb]; try lia. reflexivity.
Qed.
Lemma exs_dec_hi_short : forall r2 cp, hex4 r2 = Some cp -> 55296 <= cp < 56320 -> (length (skipn 4 r2) < 6)%nat ->
  decode (92 :: 117 :: r2) = None.
Proof.
intros r2 cp H Hc Hl. rewrite (exs_dec_u_hi r2 cp H Hc).
destruct (skipn 4 r2) as [|a [|b [|c [|d [|e [|f r]]]]]]; cbn in Hl; try lia; reflexivity.
Qed.
Lemma exs_dec_hi_pair : forall r2 cp b1 b2 h0 h1 h2 h3 r4, hex4 r2 = Some cp -> 55296 <= cp < 56320 ->
  skipn 4 r2 = b1 :: b2 :: h0 :: h1 :: h2 :: h3 :: r4 ->
  decode (92 :: 117 :: r2) =
  if (b1 =? 92) && (b2 =? 117) then
    match hex4 [h0; h1; h2; h3] with
    | Some lo => if (56320 <=? lo) && (lo <=? 57343) then emit (utf8 (pair_cp cp lo)) (decode r4) else None
    | None => None
    end
  else None.
Proof.
intros r2 cp b1 b2 h0 h1 h2 h3 r4 H Hc Hs. rewrite (exs_dec_u_hi r2 cp H Hc), Hs. cbn [low].
destruct ((b1 =? 92) && (b2 =? 117)); [|reflexivity].
change (hex4 (h0 :: h1 :: h2 :: h3 :: r4)) with (hex4 [h0; h1; h2; h3]).
destruct (hex4 [h0; h1; h2; h3]) as [lo|]; [|reflexivity].
destruct ((56320 <=? lo) && (lo <=? 57343)); reflexivity.
Qed.

(* hex4 reads only the first four bytes *)
Lemma exs_hex4_firstn : forall l, hex4 (firstn 4 l) = hex4 l.
Proof. intros [|a [|b [|c [|d r]]]]; reflexivity. Qed.
Lemma exs_hex4_range : forall l v, hex4 l = Some v -> 0 <= v < 65536.
Proof.
intros l v H. destruct (hex4_some l v H) as (a & b & c & d & r & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1). exact H1.
Qed.

(* the pair's code point as the code computes it (B 0x8456c-0x84584: hi * 1024 + lo - 0x35fdc00) *)
Lemma exs_pair_cp : forall hi lo, pair_cp hi lo = hi * 1024 + lo - 56613888.
Proof. intros hi lo. unfold pair_cp. lia. Qed.
Lemma exs_pair_range : forall hi lo, 55296 <= hi < 56320 -> 56320 <= lo <= 57343 -> 65536 <= pair_cp hi lo <= 1114111.
Proof. intros hi lo H1 H2. unfold pair_cp. lia. Qed.

(* the UTF-8 byte count against the escape's length *)
Lemma exs_utf8_len_bmp : forall cp, 0 < cp < 65536 -> (1 <= length (utf8 cp) <= 3)%nat.
Proof.
intros cp Hc. unfold utf8.
destruct (Z.ltb_spec cp 128); [cbn; lia|]. destruct (Z.ltb_spec cp 2048); [cbn; lia|].
destruct (Z.ltb_spec cp 65536); [cbn; lia | lia].
Qed.
Lemma exs_utf8_len_pair : forall cp, 65536 <= cp -> length (utf8 cp) = 4%nat.
Proof.
intros cp Hc. unfold utf8.
destruct (Z.ltb_spec cp 128); [lia|]. destruct (Z.ltb_spec cp 2048); [lia|].
destruct (Z.ltb_spec cp 65536); [lia | reflexivity].
Qed.

(* ---- the closing quote: decode's value at the whole string, as tex_string_specX's Some arm states it ---- *)
Lemma exs_skipn_skipn : forall (l : list Z) a b, skipn a (skipn b l) = skipn (a + b) l.
Proof.
intros l a b. revert l. induction b as [|b IH]; intros l; [rewrite Nat.add_0_r; reflexivity|].
destruct l as [|x l]; [destruct a; reflexivity|]. rewrite Nat.add_succ_r. cbn [skipn]. apply IH.
Qed.
Lemma exs_quote_scan : forall (x : list Z) i0 j s,
  decode (skipn (S i0) x) = Some (s, skipn (S j) x) -> (j < length x)%nat ->
  exists c, scan (skipn (S i0) x) = Some c /\ skipn (S j) x = skipn (S c) (skipn (S i0) x) /\ j = (i0 + 1 + c)%nat.
Proof.
intros x i0 j s Hd Hj. destruct (decode_stop _ _ _ Hd) as (c & Hc & Hr & _).
pose proof (scan_quote _ _ Hc) as [Hcl _]. rewrite length_skipn in Hcl.
exists c. split; [exact Hc|]. split; [exact Hr|].
rewrite exs_skipn_skipn in Hr. apply (f_equal (@length Z)) in Hr. rewrite !length_skipn in Hr. lia.
Qed.
