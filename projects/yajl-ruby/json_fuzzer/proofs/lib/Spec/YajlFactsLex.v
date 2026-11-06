(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlFactsBuf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma znth_nil : forall i, znth [] i = 0.
Proof. intros. unfold znth. destruct (i <? 0); auto. destruct (Z.to_nat i); reflexivity. Qed.

Lemma nth_skipn : forall (l : list Z) i k, nth k (skipn i l) 0 = nth (i + k) l 0.
Proof.
  induction l as [|x l IH]; intros i k.
  - rewrite skipn_nil. rewrite !nth_overflow by (cbn; lia). reflexivity.
  - destruct i; cbn; auto.
Qed.

Lemma nth_firstn_lt : forall (l : list Z) n k, (k < n)%nat -> nth k (firstn n l) 0 = nth k l 0.
Proof.
  induction l as [|x l IH]; intros n k Hk.
  - rewrite firstn_nil. reflexivity.
  - destruct n; [lia|]. cbn. destruct k; auto. apply IH. lia.
Qed.

Lemma zslice_znth : forall l i n k, 0 <= i -> 0 <= k < n -> znth (zslice l i n) k = znth l (i + k).
Proof.
  intros l i n k Hi Hk. unfold znth, zslice.
  destruct (Z.ltb_spec k 0); [lia|]. destruct (Z.ltb_spec (i + k) 0); [lia|].
  rewrite nth_firstn_lt by lia. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma zslice_nil_len : forall l i n, n <= 0 -> zslice l i n = [].
Proof. intros. unfold zslice. replace (Z.to_nat n) with 0%nat by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ylex_utf8_char_bounds : forall txt len off cur,
  0 <= off <= len ->
  match ylex_utf8_char txt len off cur with
  | U8_ok o => off <= o <= len
  | U8_eof o => off <= o <= len
  | U8_error o => off <= o <= len
  end.
Proof.
  intros txt len off cur Hoff. unfold ylex_utf8_char.
  repeat match goal with
         | |- context [if (?a <=? ?b) then _ else _] => destruct (Z.leb_spec a b)
         | |- context [if ?c then _ else _] => destruct c
         end; lia.
Qed.

Ltac desif :=
  repeat match goal with
         | |- context [if (?a <=? ?b) then _ else _] => destruct (Z.leb_spec a b)
         | |- context [if (?a <? ?b) then _ else _] => destruct (Z.ltb_spec a b)
         | |- context [if (?a =? ?b) then _ else _] => destruct (Z.eqb_spec a b)
         | |- context [if ?c then _ else _] => destruct c eqn:?
         end.

Lemma ylex_hex4_spec : forall n txt len off,
  0 <= off <= len ->
  match ylex_hex4 n txt len off with
  | HX_ok o => o = off + Z.of_nat n /\ o <= len /\
               (forall k, 0 <= k < Z.of_nat n -> is_vhc (znth txt (off + k)) = true)
  | HX_eof o => off <= o <= len /\ len <= o
  | HX_bad o => off <= o < len
  end.
Proof.
  induction n as [|n IH]; intros txt len off Hoff; cbn [ylex_hex4].
  - split; [lia|]. split; [lia|]. intros; lia.
  - destruct (Z.leb_spec len off); [lia|].
    destruct (is_vhc (znth txt off)) eqn:Hv.
    + specialize (IH txt len (off + 1) ltac:(lia)).
      destruct (ylex_hex4 n txt len (off + 1)); try lia.
      destruct IH as (-> & Hle & Hall). split; [lia|]. split; [lia|].
      intros k Hk. destruct (Z.eq_dec k 0) as [->|].
      * rewrite Z.add_0_r; auto.
      * replace (off + k) with (off + 1 + (k - 1)) by lia. apply Hall. lia.
    + lia.
Qed.

Lemma ylex_want_spec : forall want txt len off,
  0 <= off <= len ->
  match ylex_want want txt len off with
  | W_ok o => o = off + zlength want /\ o <= len
  | W_eof o => off <= o <= len /\ len <= o
  | W_bad o => off <= o < len
  end.
Proof.
  induction want as [|w want IH]; intros txt len off Hoff; cbn [ylex_want].
  - unfold zlength; cbn; lia.
  - destruct (Z.leb_spec len off); [lia|].
    destruct (Z.eqb_spec (znth txt off) w).
    + specialize (IH txt len (off + 1) ltac:(lia)). unfold zlength in *. cbn [length].
      destruct (ylex_want want txt len (off + 1)); lia.
    + lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sbody_ix (txt : list Z) : Z -> Z -> Prop :=
| sbi_nil : forall i, sbody_ix txt i i
| sbi_plain : forall i j, i < j -> znth txt i <> c_bslash -> sbody_ix txt (i + 1) j -> sbody_ix txt i j
| sbi_esc : forall i j, i + 1 < j -> znth txt i = c_bslash ->
    is_vec (znth txt (i + 1)) = true -> sbody_ix txt (i + 2) j -> sbody_ix txt i j
| sbi_uesc : forall i j, i + 5 < j -> znth txt i = c_bslash -> znth txt (i + 1) = c_u ->
    (forall k, 0 <= k < 4 -> is_vhc (znth txt (i + 2 + k)) = true) ->
    sbody_ix txt (i + 6) j -> sbody_ix txt i j.

Lemma sbody_ix_le : forall txt i j, sbody_ix txt i j -> i <= j.
Proof. induction 1; lia. Qed.

(* [comment removed for export] *)
Lemma sbody_ix_snoc_plain : forall txt i j, sbody_ix txt i j -> znth txt j <> c_bslash -> sbody_ix txt i (j + 1).
Proof.
  induction 1; intros.
  - apply sbi_plain; [lia|auto|]. apply sbi_nil.
  - apply sbi_plain; auto; lia.
  - eapply sbi_esc; eauto; lia.
  - eapply sbi_uesc; eauto; lia.
Qed.

Lemma sbody_ix_snoc_esc : forall txt i j, sbody_ix txt i j -> znth txt j = c_bslash ->
  is_vec (znth txt (j + 1)) = true -> sbody_ix txt i (j + 2).
Proof.
  induction 1; intros.
  - eapply sbi_esc; eauto; [lia|]. replace (i + 2) with (i + 2) by lia. apply sbi_nil.
  - apply sbi_plain; auto; lia.
  - eapply sbi_esc; eauto; lia.
  - eapply sbi_uesc; eauto; lia.
Qed.

Lemma sbody_ix_snoc_uesc : forall txt i j, sbody_ix txt i j -> znth txt j = c_bslash ->
  znth txt (j + 1) = c_u -> (forall k, 0 <= k < 4 -> is_vhc (znth txt (j + 2 + k)) = true) ->
  sbody_ix txt i (j + 6).
Proof.
  induction 1; intros.
  - eapply sbi_uesc; eauto; [lia|]. apply sbi_nil.
  - apply sbi_plain; auto; lia.
  - eapply sbi_esc; eauto; lia.
  - eapply sbi_uesc; eauto; lia.
Qed.

(* [comment removed for export] *)
Lemma sbody_ix_shift : forall txt i j, sbody_ix txt i j ->
  forall base n, 0 <= base -> base <= i -> j <= base + n ->
  sbody_ix (zslice txt base n) (i - base) (j - base).
Proof.
  induction 1; intros base n Hb Hbi Hjn.
  - apply sbi_nil.
  - apply sbi_plain; [lia| |].
    + rewrite zslice_znth by lia. replace (base + (i - base)) with i by lia. auto.
    + replace (i - base + 1) with (i + 1 - base) by lia. apply IHsbody_ix; lia.
  - eapply sbi_esc; [lia| | |].
    + rewrite zslice_znth by lia. replace (base + (i - base)) with i by lia. auto.
    + rewrite zslice_znth by lia. replace (base + (i - base + 1)) with (i + 1) by lia. auto.
    + replace (i - base + 2) with (i + 2 - base) by lia. apply IHsbody_ix; lia.
  - eapply sbi_uesc; [lia| | | |].
    + rewrite zslice_znth by lia. replace (base + (i - base)) with i by lia. auto.
    + rewrite zslice_znth by lia. replace (base + (i - base + 1)) with (i + 1) by lia. auto.
    + intros k Hk. rewrite zslice_znth by lia. replace (base + (i - base + 2 + k)) with (i + 2 + k) by lia. auto.
    + replace (i - base + 6) with (i + 6 - base) by lia. apply IHsbody_ix; lia.
Qed.

Lemma sbody_ix_extend_plain : forall txt i j n,
  sbody_ix txt i j -> (forall p, j <= p < j + Z.of_nat n -> znth txt p <> c_bslash) ->
  sbody_ix txt i (j + Z.of_nat n).
Proof.
  intros txt i j n. revert j. induction n as [|n IH]; intros j Hb Hall.
  - rewrite Z.add_0_r. auto.
  - rewrite Nat2Z.inj_succ. replace (j + Z.succ (Z.of_nat n)) with (j + 1 + Z.of_nat n) by lia.
    apply IH.
    + apply sbody_ix_snoc_plain; auto. apply Hall. lia.
    + intros p Hp. apply Hall. lia.
Qed.

Lemma is_utf8_cont_not_bslash : forall c, is_utf8_cont c = true -> c <> c_bslash.
Proof.
  intros c Hc ->. cbv in Hc. discriminate.
Qed.

Lemma ylex_utf8_char_ok_conts : forall txt len off cur o,
  ylex_utf8_char txt len off cur = U8_ok o ->
  off <= o /\ forall p, off <= p < o -> is_utf8_cont (znth txt p) = true.
Proof.
  intros txt len off cur o. unfold ylex_utf8_char.
  desif; intros E; try discriminate; injection E as <-;
    (split; [lia|]); intros p Hp; try lia;
    repeat match goal with
      | H : is_utf8_cont (znth txt ?q) = true |- _ =>
          destruct (Z.eq_dec p q) as [->|]; [exact H | clear H]
      end; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ylex_string_loop_spec : forall fuel v txt len body_start off esc,
  0 <= body_start <= off -> off <= len -> sbody_ix txt body_start off ->
  let '(tok, off', err, esc') := ylex_string_loop fuel v txt len off esc in
  off <= off' <= len /\ (esc = true -> esc' = true) /\
  match tok with
  | TK_string => err = None /\ off + 1 <= off' /\ znth txt (off' - 1) = c_quote /\
                 sbody_ix txt body_start (off' - 1)
  | TK_eof => err = None
  | TK_error => err <> None
  | _ => False
  end.
Proof.
  induction fuel as [|fuel IH]; intros v txt len body_start off esc Hbs Hoff Hbody; cbn [ylex_string_loop].
  - repeat split; auto; lia.
  - destruct (Z.leb_spec len off). { repeat split; auto; lia. }
    destruct (Z.eqb_spec (znth txt off) c_quote) as [Eq|Nq].
    { repeat split; auto; try lia. replace (off + 1 - 1) with off by lia. auto.
      replace (off + 1 - 1) with off by lia. auto. }
    destruct (Z.eqb_spec (znth txt off) c_bslash) as [Eb|Nb].
    + destruct (Z.leb_spec len (off + 1)). { repeat split; auto; lia. }
      destruct (Z.eqb_spec (znth txt (off + 1)) c_u) as [Eu|Nu].
      * pose proof (ylex_hex4_spec 4 txt len (off + 1 + 1) ltac:(lia)) as Hx.
        destruct (ylex_hex4 4 txt len (off + 1 + 1)) as [o|o|o].
        -- destruct Hx as (-> & Hle & Hall). cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
           assert (Hb' : sbody_ix txt body_start (off + 6)).
           { apply sbody_ix_snoc_uesc; auto. intros k Hk.
             replace (off + 2 + k) with (off + 1 + 1 + k) by lia. apply Hall. lia. }
           specialize (IH v txt len body_start (off + 1 + 1 + 4) true ltac:(lia) ltac:(lia)
                         ltac:(replace (off + 1 + 1 + 4) with (off + 6) by lia; exact Hb')).
           destruct (ylex_string_loop fuel v txt len (off + 1 + 1 + 4) true) as [[[tok off'] err] esc'].
           destruct IH as (H1 & H2 & H3). split; [lia|]. split; [auto|]. destruct tok; auto.
           destruct H3 as (?&?&?&?). repeat split; auto. lia.
        -- repeat split; auto; lia.
        -- destruct Hx. repeat split; auto; try lia. congruence.
      * destruct (is_vec (znth txt (off + 1))) eqn:Hvec.
        -- assert (Hb' : sbody_ix txt body_start (off + 2)) by (apply sbody_ix_snoc_esc; auto).
           specialize (IH v txt len body_start (off + 1 + 1) true ltac:(lia) ltac:(lia)
                         ltac:(replace (off + 1 + 1) with (off + 2) by lia; exact Hb')).
           destruct (ylex_string_loop fuel v txt len (off + 1 + 1) true) as [[[tok off'] err] esc'].
           destruct IH as (H1 & H2 & H3). split; [lia|]. split; [auto|]. destruct tok; auto.
           destruct H3 as (?&?&?&?). repeat split; auto. lia.
        -- repeat split; auto; try lia. congruence.
    + destruct (is_ijc (znth txt off)) eqn:Hijc. { repeat split; auto; try lia. congruence. }
      assert (Hb' : sbody_ix txt body_start (off + 1)) by (apply sbody_ix_snoc_plain; auto).
      destruct (negb (v =? 0)).
      * pose proof (ylex_utf8_char_bounds txt len (off + 1) (znth txt off) ltac:(lia)) as Hu.
        destruct (ylex_utf8_char txt len (off + 1) (znth txt off)) as [o|o|o] eqn:Hu8.
        -- (* [comment removed for export] *)
           assert (Hcont : sbody_ix txt body_start o).
           { clear IH. destruct (ylex_utf8_char_ok_conts _ _ _ _ _ Hu8) as [Ho Hc].
             replace o with (off + 1 + Z.of_nat (Z.to_nat (o - (off + 1)))) by lia.
             apply sbody_ix_extend_plain; auto. intros p Hp.
             apply is_utf8_cont_not_bslash. apply Hc. lia. }
           specialize (IH v txt len body_start o esc ltac:(lia) ltac:(lia) Hcont).
           destruct (ylex_string_loop fuel v txt len o esc) as [[[tok off'] err] esc'].
           destruct IH as (H1 & H2 & H3). split; [lia|]. split; [auto|]. destruct tok; auto.
           destruct H3 as (?&?&?&?). repeat split; auto. lia.
        -- repeat split; auto; lia.
        -- repeat split; auto; try lia. congruence.
      * specialize (IH v txt len body_start (off + 1) esc ltac:(lia) ltac:(lia) Hb').
        destruct (ylex_string_loop fuel v txt len (off + 1) esc) as [[[tok off'] err] esc'].
        destruct IH as (H1 & H2 & H3). split; [lia|]. split; [auto|]. destruct tok; auto.
        destruct H3 as (?&?&?&?). repeat split; auto. lia.
Qed.

Lemma ylex_string_spec : forall v txt len off,
  0 <= off <= len ->
  let '(tok, off', err) := ylex_string v txt len off in
  off <= off' <= len /\
  match tok with
  | TK_string | TK_string_esc =>
      err = None /\ off + 1 <= off' /\ znth txt (off' - 1) = c_quote /\ sbody_ix txt off (off' - 1)
  | TK_eof => err = None
  | TK_error => err <> None
  | _ => False
  end.
Proof.
  intros v txt len off Hoff. unfold ylex_string.
  pose proof (ylex_string_loop_spec (lex_fuel len off) v txt len off off false
                ltac:(lia) ltac:(lia) (sbi_nil txt off)) as Hs.
  destruct (ylex_string_loop (lex_fuel len off) v txt len off false) as [[[tok off'] err] esc'].
  destruct Hs as (H1 & H2 & H3). destruct tok; try contradiction; destruct esc'; cbn; intuition auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read1_spec : forall txt len off, 0 <= off <= len ->
  match read1 txt len off with
  | RD_eof => off = len
  | RD_char c o => o = off + 1 /\ off < len /\ c = znth txt off
  end.
Proof.
  intros. unfold read1. destruct (Z.leb_spec len off); repeat split; lia.
Qed.

Lemma read_past_digits_spec : forall fuel txt len off, 0 <= off <= len ->
  match read_past_digits fuel txt len off with
  | RD_eof => True
  | RD_char c o => off + 1 <= o <= len /\ is_digit c = false /\ c = znth txt (o - 1)
  end.
Proof.
  induction fuel as [|fuel IH]; intros txt len off Hoff; cbn [read_past_digits]; auto.
  pose proof (read1_spec txt len off Hoff) as H1.
  destruct (read1 txt len off) as [|c o]; auto. destruct H1 as (-> & Hlt & ->).
  destruct (is_digit (znth txt off)) eqn:Hd.
  - specialize (IH txt len (off + 1) ltac:(lia)).
    destruct (read_past_digits fuel txt len (off + 1)); auto. intuition lia.
  - repeat split; auto; try lia. f_equal; lia.
Qed.

Ltac spec_reads txt len :=
  repeat match goal with
  | |- context [match read1 txt len ?o with _ => _ end] =>
      pose proof (read1_spec txt len o ltac:(lia)); destruct (read1 txt len o)
  | |- context [match read_past_digits ?f txt len ?o with _ => _ end] =>
      pose proof (read_past_digits_spec f txt len o ltac:(lia)); destruct (read_past_digits f txt len o)
  | |- context [if ?c then _ else _] => destruct c eqn:?
  end.

Lemma ylex_number_spec : forall txt len off, 0 <= off <= len ->
  let '(tok, off', err) := ylex_number txt len off in
  off <= off' <= len /\
  match tok with
  | TK_integer | TK_double => err = None /\ off + 1 <= off' /\ off' < len
  | TK_eof => err = None
  | TK_error => err <> None
  | _ => False
  end.
Proof.
  intros txt len off Hoff. unfold ylex_number.
  spec_reads txt len; cbn -[Z.add Z.sub]; intuition (auto; try lia; try congruence).
Qed.

Lemma skip_line_comment_spec : forall fuel txt len off, 0 <= off <= len ->
  match skip_line_comment fuel txt len off with
  | RD_eof => True
  | RD_char c o => off + 1 <= o <= len
  end.
Proof.
  induction fuel as [|fuel IH]; intros txt len off Hoff; cbn [skip_line_comment]; auto.
  pose proof (read1_spec txt len off Hoff) as H1.
  destruct (read1 txt len off) as [|c o]; auto. destruct H1 as (-> & Hlt & ->).
  destruct (znth txt off =? c_lf); [lia|].
  specialize (IH txt len (off + 1) ltac:(lia)).
  destruct (skip_line_comment fuel txt len (off + 1)); auto. lia.
Qed.

Lemma skip_block_comment_spec : forall fuel txt len off, 0 <= off <= len ->
  match skip_block_comment fuel txt len off with
  | RD_eof => True
  | RD_char c o => off + 1 <= o <= len
  end.
Proof.
  induction fuel as [|fuel IH]; intros txt len off Hoff; cbn [skip_block_comment]; auto.
  pose proof (read1_spec txt len off Hoff) as H1.
  destruct (read1 txt len off) as [|c o]; auto. destruct H1 as (-> & Hlt & ->).
  destruct (znth txt off =? c_star).
  - pose proof (read1_spec txt len (off + 1) ltac:(lia)) as H2.
    destruct (read1 txt len (off + 1)) as [|c2 o2]; auto. destruct H2 as (-> & Hlt2 & ->).
    destruct (znth txt (off + 1) =? c_slash); [lia|].
    specialize (IH txt len (off + 1) ltac:(lia)).
    destruct (skip_block_comment fuel txt len (off + 1)); auto. lia.
  - specialize (IH txt len (off + 1) ltac:(lia)).
    destruct (skip_block_comment fuel txt len (off + 1)); auto. lia.
Qed.

Lemma ylex_comment_spec : forall txt len off, 0 <= off <= len ->
  let '(tok, off', err) := ylex_comment txt len off in
  off <= off' <= len /\
  match tok with
  | TK_comment => err = None /\ off + 1 <= off'
  | TK_eof => err = None
  | TK_error => err <> None
  | _ => False
  end.
Proof.
  intros txt len off Hoff. unfold ylex_comment.
  pose proof (read1_spec txt len off Hoff) as H1.
  destruct (read1 txt len off) as [|c o]. { repeat split; auto; lia. }
  destruct H1 as (-> & Hlt & ->).
  destruct (znth txt off =? c_slash).
  - pose proof (skip_line_comment_spec (lex_fuel len (off + 1)) txt len (off + 1) ltac:(lia)) as Hs.
    destruct (skip_line_comment _ txt len (off + 1)); repeat split; auto; lia.
  - destruct (znth txt off =? c_star).
    + pose proof (skip_block_comment_spec (lex_fuel len (off + 1)) txt len (off + 1) ltac:(lia)) as Hs.
      destruct (skip_block_comment _ txt len (off + 1)); repeat split; auto; lia.
    + repeat split; auto; try lia. congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lex_inv (lx : ylexer) : Prop :=
  lx_bufInUse lx = 0 /\ lx_bufOff lx = 0 /\ lx_lineOff lx = 0 /\ lx_charOff lx = 0 /\
  lx_allowComments lx = 1 /\ lx_validateUTF8 lx = 1 /\ lx_buf lx = ybuf_zero.

Lemma lex_inv_set_error : forall lx e, lex_inv lx -> lex_inv (lx_set_error lx e).
Proof. intros lx e H. exact H. Qed.

Lemma lex_inv_set_error_opt : forall lx e, lex_inv lx -> lex_inv (lx_set_error_opt lx e).
Proof. intros lx [e|] H; cbn; auto. Qed.

Lemma ylex_alloc_post : forall Q,
  Q None ->
  (forall blk lx, lex_inv lx -> lx_error lx = LE_ok -> Q (Some (blk, lx))) ->
  ypost (ylex_alloc 1 1) Q.
Proof.
  intros Q HN HS. unfold ylex_alloc, ybuf_alloc. cbn.
  intros [blk|]; cbn; auto. intros [bb|]; cbn; auto. apply HS; auto.
  unfold lex_inv; cbn; repeat split; auto.
Qed.

Lemma ylex_realloc_post : forall lx, lex_inv lx ->
  ypost (ylex_realloc lx) (fun lx' => lex_inv lx' /\ lx_error lx' = LE_ok /\ lx_bufblk lx' = lx_bufblk lx).
Proof.
  intros lx (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold ylex_realloc. rewrite H7. cbn.
  unfold lex_inv; cbn. repeat split; auto.
Qed.

Lemma ylex_free_safe : forall blk lx, ysafe (ylex_free blk lx).
Proof.
  intros. unfold ylex_free. apply (ypost_safe _ (fun _ => True)).
  eapply ypost_bind; [apply ypost_true, ybuf_free_safe|]. intros; cbn; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition loop_post (txt : list Z) (len off : Z) (r : ylexer * ytok * Z * Z) : Prop :=
  let '(lx', tok, off', start') := r in
  lex_inv lx' /\ off <= start' /\ start' <= off' <= len /\
  match tok with
  | TK_eof | TK_error => True
  | TK_string | TK_string_esc =>
      start' + 2 <= off' /\ znth txt start' = c_quote /\ znth txt (off' - 1) = c_quote /\
      sbody_ix txt (start' + 1) (off' - 1)
  | TK_comment => False
  | TK_bool => (znth txt start' = c_t /\ off' = start' + 4) \/ (znth txt start' = c_f /\ off' = start' + 5)
  | TK_null => off' = start' + 4
  | TK_integer | TK_double => start' + 1 <= off' /\ off' < len
  | _ => off' = start' + 1
  end.

Lemma ylex_loop_post : forall fuel lx txt len off,
  lex_inv lx -> 0 <= off <= len -> (Z.to_nat (len - off) < fuel)%nat ->
  ypost (ylex_loop fuel lx txt len off off) (loop_post txt len off).
Proof.
  induction fuel as [|fuel IH]; intros lx txt len off Hlx Hoff Hfuel; [lia|].
  cbn [ylex_loop]. unfold yassert.
  destruct (Z.leb_spec off len); [|lia]. cbn [ybind].
  destruct (Z.leb_spec len off).
  { cbn. split; [auto|lia]. }
  Ltac fin := cbn [ypost]; unfold loop_post;
    split; [ first [ assumption | apply lex_inv_set_error; assumption
                   | apply lex_inv_set_error_opt; assumption ] | ];
    repeat match goal with |- _ /\ _ => split end; auto; try lia.
  destruct (Z.eqb_spec (znth txt off) c_lbrace); [fin|].
  destruct (Z.eqb_spec (znth txt off) c_rbrace); [fin|].
  destruct (Z.eqb_spec (znth txt off) c_lbracket); [fin|].
  destruct (Z.eqb_spec (znth txt off) c_rbracket); [fin|].
  destruct (Z.eqb_spec (znth txt off) c_comma); [fin|].
  destruct (Z.eqb_spec (znth txt off) c_colon); [fin|].
  destruct (is_lex_ws (znth txt off)).
  { eapply ypost_mono. apply IH; auto; try lia.
    intros [[[lx' tok] off'] start']. unfold loop_post. intuition lia. }
  destruct (Z.eqb_spec (znth txt off) c_t).
  { pose proof (ylex_want_spec want_rue txt len (off + 1) ltac:(lia)) as Hw.
    destruct (ylex_want want_rue txt len (off + 1)); unfold zlength, want_rue in Hw; cbn in Hw;
      fin. }
  destruct (Z.eqb_spec (znth txt off) c_f).
  { pose proof (ylex_want_spec want_alse txt len (off + 1) ltac:(lia)) as Hw.
    destruct (ylex_want want_alse txt len (off + 1)); unfold zlength, want_alse in Hw; cbn in Hw;
      fin. }
  destruct (Z.eqb_spec (znth txt off) c_n).
  { pose proof (ylex_want_spec want_ull txt len (off + 1) ltac:(lia)) as Hw.
    destruct (ylex_want want_ull txt len (off + 1)); unfold zlength, want_ull in Hw; cbn in Hw;
      fin. }
  destruct (Z.eqb_spec (znth txt off) c_quote).
  { pose proof (ylex_string_spec (lx_validateUTF8 lx) txt len (off + 1) ltac:(lia)) as Hs.
    destruct (ylex_string _ txt len (off + 1)) as [[tok o] err].
    destruct Hs as [Ho Hs]. destruct tok; try contradiction; fin; try apply lex_inv_set_error_opt; auto;
      try (replace (off + 1 - 1) with off in * by lia); intuition (auto; try lia).
    all: replace (off + 1) with (off + 1) by lia; auto. }
  destruct (orb (znth txt off =? c_minus) (is_digit (znth txt off))) eqn:Hnum.
  { pose proof (ylex_number_spec txt len off ltac:(lia)) as Hn.
    destruct (ylex_number txt len off) as [[tok o] err].
    destruct Hn as [Ho Hn]. destruct tok; try contradiction; fin; try apply lex_inv_set_error_opt; auto; intuition lia. }
  destruct (Z.eqb_spec (znth txt off) c_slash).
  { destruct Hlx as (H1 & H2 & H3 & H4 & H5 & H6 & H7). rewrite H5. cbn [Z.eqb].
    pose proof (ylex_comment_spec txt len (off + 1) ltac:(lia)) as Hc.
    destruct (ylex_comment txt len (off + 1)) as [[tok o] err].
    destruct Hc as [Ho Hc].
    assert (Hlx : lex_inv lx) by (unfold lex_inv; repeat split; auto).
    destruct tok; try contradiction.
    - fin.
    - fin.
    - rewrite H7. cbn [ybuf_clear yb_state ybuf_zero ybind yb_len yb_data].
      eapply ypost_mono. apply IH.
      + unfold lex_inv; cbn; repeat split; auto.
      + lia.
      + lia.
      + intros [[[lx' tok] off'] start']. unfold loop_post. intuition lia. }
  fin.
Qed.

(* [comment removed for export] *)
Definition lex_post (txt : list Z) (len off : Z) (r : ylexer * ytok * Z * outref * Z) : Prop :=
  let '(lx', tok, off', ob, n) := r in
  off <= off' <= len /\ lx_allowComments lx' = 1 /\ lx_validateUTF8 lx' = 1 /\
  match tok with
  | TK_eof =>
      (* [comment removed for export] *)
      ob = OB_null /\ n = 0 /\ lx_bufInUse lx' = 1 /\ lx_bufOff lx' = 0 /\
      buf_inv (lx_buf lx') /\ yb_state (lx_buf lx') = BS_ok /\ yb_data (lx_buf lx') <> None /\
      exists start, off <= start <= off' /\ yb_bytes (lx_buf lx') = zslice txt start (off' - start)
  | TK_error =>
      ob = OB_null /\ n = 0 /\
      (lex_inv lx' \/
       (* [comment removed for export] *)
       (lx_error lx' = LE_alloc_failed /\ lx_bufInUse lx' = 1 /\ buf_inv (lx_buf lx') /\
        yb_state (lx_buf lx') <> BS_ok /\ yb_data (lx_buf lx') = None))
  | TK_comment => False
  | _ =>
      lex_inv lx' /\ off < off' /\
      exists i, ob = OB_text i /\ off <= i /\ 0 <= n /\ i + n <= off' /\
        match tok with
        | TK_string | TK_string_esc =>
            1 <= i /\ znth txt (i - 1) = c_quote /\ znth txt (i + n) = c_quote /\ i + n + 1 = off' /\
            sbody_ix txt i (i + n)
        | TK_integer | TK_double => 0 < n /\ off' < len
        | TK_bool => (n = 4 /\ znth txt i = c_t) \/ (n = 5 /\ znth txt i = c_f)
        | TK_null => n = 4
        | _ => n = 1
        end
  end.

Lemma ylex_finish_post : forall txt len off r,
  len = zlength txt -> len < 2^32 -> 0 <= off ->
  loop_post txt len off r ->
  let '(lx1, tok, off1, start) := r in
  ypost (ylex_finish lx1 txt tok off1 start) (lex_post txt len off).
Proof.
  intros txt len off [[[lx1 tok] off1] start] Hlen Hlen32 Hoff (Hlx & Hst & Hoff1 & Htok).
  pose proof Hlx as Hlx0.
  destruct Hlx as (HinUse & HbufOff & Hline & Hchar & Hac & Hv & Hbuf).
  unfold ylex_finish. rewrite HinUse. cbn [Z.eqb negb orb].
  Ltac fin_tok w :=
    cbn; split; [lia|]; split; [auto|]; split; [auto|]; split; [auto|]; split; [lia|];
    exists w; repeat match goal with |- _ /\ _ => split end; auto; try lia.
  destruct tok; cbn [tok_eqb tok_code Z.eqb Pos.eqb is_string_tok orb negb]; try contradiction.
  - fin_tok start.
  - fin_tok start.
  - fin_tok start.
  - (* [comment removed for export] *)
    rewrite Hbuf. cbn [ybuf_clear yb_state ybuf_zero ybind yb_len yb_data].
    eapply ypost_bind.
    { apply (ybuf_append_post (mkBuf BS_ok 0 0 None []) (zslice txt start (off1 - start))).
      - apply buf_inv_zero.
      - reflexivity.
      - cbn -[Z.pow Z.add]. rewrite zslice_length by lia. lia. }
    intros b2 (Hinv2 & Herr2 & Hok2). unfold ybuf_err.
    destruct (yb_state b2) eqn:Hs2; cbn.
    + specialize (Hok2 eq_refl). destruct Hok2 as (Hd2 & Hby2 & _).
      repeat match goal with |- _ /\ _ => split end; auto; try lia.
      exists start. split; [lia|]. rewrite Hby2. reflexivity.
    + repeat match goal with |- _ /\ _ => split end; auto; try lia.
      right. repeat match goal with |- _ /\ _ => split end; auto; try congruence.
      destruct Hinv2 as (?&?&?&?&?&Hx). apply Hx. congruence.
    + repeat match goal with |- _ /\ _ => split end; auto; try lia.
      right. repeat match goal with |- _ /\ _ => split end; auto; try congruence.
      destruct Hinv2 as (?&?&?&?&?&Hx). apply Hx. congruence.
  - (* [comment removed for export] *)
    cbn. repeat match goal with |- _ /\ _ => split end; auto; try lia.
  - fin_tok start.
  - fin_tok start.
  - fin_tok start.
  - fin_tok start.
  - fin_tok start.
  - fin_tok start.
  - fin_tok start.
  - (* [comment removed for export] *)
    unfold yassert. destruct (Z.leb_spec 2 (off1 - start)); [|lia]. fin_tok (start + 1).
    + replace (start + 1 - 1) with start by lia. intuition auto.
    + replace (start + 1 + (off1 - start - 2)) with (off1 - 1) by lia. intuition auto.
    + replace (start + 1 + (off1 - start - 2)) with (off1 - 1) by lia. intuition auto.
  - (* [comment removed for export] *)
    unfold yassert. destruct (Z.leb_spec 2 (off1 - start)); [|lia]. fin_tok (start + 1).
    + replace (start + 1 - 1) with start by lia. intuition auto.
    + replace (start + 1 + (off1 - start - 2)) with (off1 - 1) by lia. intuition auto.
    + replace (start + 1 + (off1 - start - 2)) with (off1 - 1) by lia. intuition auto.
Qed.

Theorem ylex_lex_post : forall lx txt len off,
  len = zlength txt -> len < 2^32 -> lex_inv lx -> 0 <= off <= len ->
  ypost (ylex_lex lx txt len off) (lex_post txt len off).
Proof.
  intros lx txt len off Hlen H32 Hlx Hoff. unfold ylex_lex. eapply ypost_bind.
  - apply ylex_loop_post; eauto; unfold lex_fuel; lia.
  - intros [[[lx1 tok] off1] start] Hr.
    exact (ylex_finish_post txt len off (lx1, tok, off1, start) Hlen H32 ltac:(lia) Hr).
Qed.

(* [comment removed for export] *)
Corollary ylex_lex_safe : forall lx txt len off,
  len = zlength txt -> len < 2^32 -> lex_inv lx -> 0 <= off <= len ->
  ysafe (ylex_lex lx txt len off).
Proof. intros. eapply ypost_safe. apply ylex_lex_post; eauto. Qed.
