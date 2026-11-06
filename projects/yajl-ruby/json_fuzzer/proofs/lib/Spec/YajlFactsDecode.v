(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlDecode
     YajlFactsBuf YajlFactsLex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zseq (lo : Z) (n : nat) : list Z :=
  match n with O => [] | S n' => lo :: zseq (lo + 1) n' end.

Lemma zseq_forallb : forall f n lo, forallb f (zseq lo n) = true ->
  forall c, lo <= c < lo + Z.of_nat n -> f c = true.
Proof.
  induction n as [|n IH]; intros lo Hf c Hc; cbn [zseq forallb] in Hf.
  - lia.
  - apply andb_prop in Hf. destruct Hf as [H1 H2].
    destruct (Z.eq_dec c lo) as [->|]; auto.
    apply (IH (lo + 1)); auto. lia.
Qed.

Lemma byte_forall : forall f, forallb f (zseq 0 256) = true -> forall c, 0 <= c < 256 -> f c = true.
Proof. intros f Hf c Hc. apply (zseq_forallb f 256 0); auto. Qed.

Lemma clt_range : forall c, clt c <> 0 -> 0 <= c < 256.
Proof.
  intros c Hc. unfold clt, znth in Hc.
  destruct (Z.ltb_spec c 0); [congruence|].
  destruct (Z.lt_ge_cases c 256) as [|Hge]; [lia|].
  exfalso. apply Hc. apply nth_overflow.
  change (length char_lookup_table) with 256%nat. lia.
Qed.

Lemma is_vhc_range : forall c, is_vhc c = true -> 0 <= c < 256.
Proof.
  intros c H. apply clt_range. unfold is_vhc in H. intros E. rewrite E in H. discriminate.
Qed.
Lemma is_vec_range : forall c, is_vec c = true -> 0 <= c < 256.
Proof.
  intros c H. apply clt_range. unfold is_vec in H. intros E. rewrite E in H. discriminate.
Qed.

(* [comment removed for export] *)
Lemma vhc_hex_digit : forall c, is_vhc c = true ->
  Z.land (hex_digit_adj c) 240 = 0 /\ 0 <= hex_digit_adj c < 16.
Proof.
  intros c Hv.
  pose proof (byte_forall (fun c => implb (is_vhc c)
                 ((Z.land (hex_digit_adj c) 240 =? 0) && (0 <=? hex_digit_adj c) && (hex_digit_adj c <? 16)))
                 ltac:(vm_compute; reflexivity) c (is_vhc_range c Hv)) as H.
  cbn beta in H. rewrite Hv in H. cbn [implb] in H.
  apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2]. lia.
Qed.

(* [comment removed for export] *)
Lemma vec_simple_escape : forall c, is_vec c = true -> simple_escape c <> None.
Proof.
  intros c Hv.
  pose proof (byte_forall (fun c => implb (is_vec c)
                 (match simple_escape c with Some _ => true | None => false end))
                 ltac:(vm_compute; reflexivity) c (is_vec_range c Hv)) as H.
  cbn beta in H. rewrite Hv in H. cbn [implb] in H. destruct (simple_escape c); congruence.
Qed.

Lemma vec_not_u : forall c, is_vec c = true -> c <> c_u.
Proof. intros c Hv ->. cbv in Hv. discriminate. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hex_loop_some : forall hs val,
  (forall h, In h hs -> is_vhc h = true) ->
  exists v, hex_loop val hs = Some v.
Proof.
  induction hs as [|h hs IH]; intros val Hall; cbn [hex_loop].
  - eauto.
  - pose proof (vhc_hex_digit h (Hall h (or_introl eq_refl))) as [Hmask Hrange].
    rewrite Hmask. cbn [Z.eqb]. apply IH. intros; apply Hall; right; auto.
Qed.

Lemma yhexToDigit_some : forall str i,
  (forall k, 0 <= k < 4 -> is_vhc (znth str (i + k)) = true) ->
  exists v, yhexToDigit 0 str i = Some v.
Proof.
  intros str i Hall. unfold yhexToDigit. apply hex_loop_some.
  intros h Hin. cbn in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]].
  - replace i with (i + 0) by lia. apply Hall. lia.
  - apply Hall. lia.
  - apply Hall. lia.
  - apply Hall. lia.
Qed.

Lemma yUtf32toUtf8_nonempty : forall cp, yUtf32toUtf8 cp <> [].
Proof. intros cp. unfold yUtf32toUtf8. repeat (destruct (_ <? _)); congruence. Qed.

Lemma yUtf32toUtf8_length : forall cp, (length (yUtf32toUtf8 cp) <= 4)%nat.
Proof. intros cp. unfold yUtf32toUtf8. repeat (destruct (_ <? _)); cbn; lia. Qed.

Lemma cstr_length : forall l, (length (cstr l) <= length l)%nat.
Proof. induction l; cbn; auto. destruct (a =? 0); cbn; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zslice_length_le : forall l i n, 0 <= n -> 0 <= zlength (zslice l i n) <= n.
Proof.
  intros l i n Hn. unfold zslice, zlength. rewrite length_firstn. lia.
Qed.

Definition dec_post (len K : Z) (r : ybuf * Z * Z) : Prop :=
  let '(b', beg', e') := r in
  e' = len /\ 0 <= beg' <= len /\ buf_inv b' /\ yb_used b' <= K + beg'.

Lemma simple_escape_u : simple_escape c_u = None.
Proof. reflexivity. Qed.

Lemma ydecode_loop_post : forall fuel b str len beg e K,
  sbody_ix str e len -> 0 <= beg <= e -> 0 <= K -> K + 2 * len < 2^62 ->
  buf_inv b -> yb_used b <= K + beg ->
  (Z.to_nat (len - e) < fuel)%nat ->
  ypost (ydecode_loop fuel b str len beg e) (dec_post len K).
Proof.
  induction fuel as [|fuel IH]; intros b str len beg e K Hbody Hbeg HK Hbig Hinv Hused Hfuel; [lia|].
  pose proof (sbody_ix_le _ _ _ Hbody) as Hle.
  cbn [ydecode_loop].
  inversion Hbody as [i | i j Hlt Hnb Hrest | i j Hlt Hb Hvec Hrest | i j Hlt Hb Hu Hhex Hrest]; subst.
  - (* [comment removed for export] *)
    destruct (Z.ltb_spec len len); [lia|]. cbn. unfold dec_post. split; [lia|]. split; [lia|]. split; [auto|lia].
  - (* [comment removed for export] *)
    destruct (Z.ltb_spec e len); [|lia].
    destruct (Z.eqb_spec (znth str e) c_bslash); [congruence|].
    apply IH; auto; try lia.
  - (* [comment removed for export] *)
    destruct (Z.ltb_spec e len); [|lia].
    destruct (Z.eqb_spec (znth str e) c_bslash); [|congruence].
    pose proof (zslice_length_le str beg (e - beg) ltac:(lia)) as Hsl.
    eapply ypost_bind.
    { apply ybuf_append_post2; auto. lia. }
    intros b1 (Hinv1 & Hok1 & Herr1).
    assert (Hu1 : yb_used b1 <= K + e).
    { destruct (yb_state b1).
      - destruct (Hok1 eq_refl) as (_ & -> & _). lia.
      - destruct (Herr1 ltac:(congruence)) as [-> _]. lia.
      - destruct (Herr1 ltac:(congruence)) as [-> _]. lia. }
    pose proof (vec_simple_escape _ Hvec) as Hse.
    destruct (simple_escape (znth str (e + 1))) as [u|]; [|congruence].
    eapply ypost_bind.
    { apply ybuf_append_post2; auto. cbn -[Z.pow Z.add]. lia. }
    intros b2 (Hinv2 & Hok2 & Herr2).
    assert (Hu2 : yb_used b2 <= K + e + 1).
    { destruct (yb_state b2).
      - destruct (Hok2 eq_refl) as (_ & -> & _). cbn -[Z.add]. lia.
      - destruct (Herr2 ltac:(congruence)) as [-> _]. lia.
      - destruct (Herr2 ltac:(congruence)) as [-> _]. lia. }
    replace (e + 1 + 1) with (e + 2) by lia.
    apply IH; auto; lia.
  - (* [comment removed for export] *)
    destruct (Z.ltb_spec e len); [|lia].
    destruct (Z.eqb_spec (znth str e) c_bslash); [|congruence].
    pose proof (zslice_length_le str beg (e - beg) ltac:(lia)) as Hsl.
    eapply ypost_bind.
    { apply ybuf_append_post2; auto. lia. }
    intros b1 (Hinv1 & Hok1 & Herr1).
    assert (Hu1 : yb_used b1 <= K + e).
    { destruct (yb_state b1).
      - destruct (Hok1 eq_refl) as (_ & -> & _). lia.
      - destruct (Herr1 ltac:(congruence)) as [-> _]. lia.
      - destruct (Herr1 ltac:(congruence)) as [-> _]. lia. }
    rewrite Hu, simple_escape_u. cbn [Z.eqb c_u Pos.eqb].
    destruct (yhexToDigit_some str (e + 1 + 1)
                ltac:(intros k Hk; replace (e + 1 + 1 + k) with (e + 2 + k) by lia; auto)) as [cp ->].
    (* [comment removed for export] *)
    assert (Hcont : forall cp' p, e + 5 <= p -> sbody_ix str (p + 1) len ->
              ypost (b2 <- ybuf_append b1 (if cp' =? 0 then [0] else cstr (yUtf32toUtf8 cp')) ;;
                     ydecode_loop fuel b2 str len (p + 1) (p + 1)) (dec_post len K)).
    { intros cp' p Hp Hbody'.
      pose proof (sbody_ix_le _ _ _ Hbody') as Hle'.
      assert (Hol : zlength (if cp' =? 0 then [0] else cstr (yUtf32toUtf8 cp')) <= 4).
      { destruct (cp' =? 0). { cbv. congruence. }
        unfold zlength. pose proof (cstr_length (yUtf32toUtf8 cp')). pose proof (yUtf32toUtf8_length cp'). lia. }
      pose proof (zlength_nonneg (if cp' =? 0 then [0] else cstr (yUtf32toUtf8 cp'))) as Hol0.
      eapply ypost_bind.
      { apply ybuf_append_post2; auto. lia. }
      intros b2 (Hinv2 & Hok2 & Herr2).
      assert (Hu2 : yb_used b2 <= K + e + 5).
      { destruct (yb_state b2).
        - destruct (Hok2 eq_refl) as (_ & -> & _). lia.
        - destruct (Herr2 ltac:(congruence)) as [-> _]. lia.
        - destruct (Herr2 ltac:(congruence)) as [-> _]. lia. }
      apply IH; auto; lia. }
    destruct (Z.eqb_spec (Z.land cp 64512) 55296) as [Hsur|Hnsur].
    + (* [comment removed for export] *)
      destruct (andb (andb (e + 1 + 1 + 3 + 2 <? len) (znth str (e + 1 + 1 + 3 + 1) =? c_bslash))
                     (znth str (e + 1 + 1 + 3 + 2) =? c_u)) eqn:Hlook.
      * apply andb_prop in Hlook as [Hlook Hu2]. apply andb_prop in Hlook as [Hlt2 Hb2].
        apply Z.ltb_lt in Hlt2. apply Z.eqb_eq in Hb2. apply Z.eqb_eq in Hu2.
        replace (e + 1 + 1 + 3 + 1) with (e + 6) in Hb2 by lia.
        replace (e + 1 + 1 + 3 + 2) with (e + 7) in Hu2, Hlt2 by lia.
        (* [comment removed for export] *)
        inversion Hrest as [i' | i' j' Hlt' Hnb' Hrest' | i' j' Hlt' Hb' Hvec' Hrest' | i' j' Hlt' Hb' Hu' Hhex' Hrest']; subst.
        -- lia.
        -- congruence.
        -- exfalso. replace (e + 6 + 1) with (e + 7) in Hvec' by lia. rewrite Hu2 in Hvec'. cbv in Hvec'. discriminate.
        -- destruct (yhexToDigit_some str (e + 1 + 1 + 3 + 1 + 2)
                      ltac:(intros k Hk; replace (e + 1 + 1 + 3 + 1 + 2 + k) with (e + 6 + 2 + k) by lia; auto)) as [sur ->].
           replace (e + 1 + 1 + 3 + 1 + 5) with (e + 11) by lia.
           apply Hcont; [lia|]. replace (e + 11 + 1) with (e + 6 + 6) by lia. auto.
      * (* [comment removed for export] *)
        eapply ypost_bind.
        { apply ybuf_append_post2; auto. cbn -[Z.pow Z.add]. lia. }
        intros b2 (Hinv2 & Hok2 & Herr2).
        assert (Hu2 : yb_used b2 <= K + e + 1).
        { destruct (yb_state b2).
          - destruct (Hok2 eq_refl) as (_ & -> & _). cbn -[Z.add]. lia.
          - destruct (Herr2 ltac:(congruence)) as [-> _]. lia.
          - destruct (Herr2 ltac:(congruence)) as [-> _]. lia. }
        replace (e + 1 + 1 + 3 + 1) with (e + 6) by lia.
        apply IH; auto; lia.
    + replace (e + 1 + 1 + 3) with (e + 5) by lia. apply Hcont; [lia|].
      replace (e + 5 + 1) with (e + 6) by lia. auto.
Qed.

(* [comment removed for export] *)
Theorem ystring_decode_post : forall b str len,
  sbody_ix str 0 len -> 0 <= len -> buf_inv b -> yb_used b + 2 * len < 2^62 ->
  ypost (ystring_decode b str len)
        (fun b' => buf_inv b' /\ yb_used b' <= yb_used b + len).
Proof.
  intros b str len Hbody Hlen Hinv Hbig. unfold ystring_decode.
  pose proof Hinv as (Hu0 & _).
  eapply ypost_bind.
  { apply (ydecode_loop_post (decode_fuel len) b str len 0 0 (yb_used b)); auto; try lia.
    unfold decode_fuel. lia. }
  intros [[b1 beg] e'] (-> & Hbeg & Hinv1 & Hu1).
  pose proof (zslice_length_le str beg (len - beg) ltac:(lia)) as Hsl.
  eapply ypost_mono. { apply ybuf_append_post2; auto. lia. }
  intros b2 (Hinv2 & Hok2 & Herr2). split; auto.
  destruct (yb_state b2).
  - destruct (Hok2 eq_refl) as (_ & -> & _). lia.
  - destruct (Herr2 ltac:(congruence)) as [-> _]. lia.
  - destruct (Herr2 ltac:(congruence)) as [-> _]. lia.
Qed.

Corollary ystring_decode_safe : forall b str len,
  sbody_ix str 0 len -> 0 <= len -> buf_inv b -> yb_used b + 2 * len < 2^62 ->
  ysafe (ystring_decode b str len).
Proof. intros. eapply ypost_safe. apply ystring_decode_post; eauto. Qed.
