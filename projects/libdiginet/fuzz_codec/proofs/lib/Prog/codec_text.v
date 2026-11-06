From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
Import ListNotations.
Open Scope Z_scope.

(** The library's text helpers agree with the harness's owed_* functions: the facts behind
    check_text_scribble, check_text_seg7, check_text_counter and check_text_masks (fuzz_codec.c:431-519),
    and the widths of the call record that the text operations 12 and 13 hand to SCRIBBLE and COUNTER. *)

(** ---- a check over a finite range of integers ---- *)

Fixpoint all_from (f : Z -> bool) (lo : Z) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => f lo && all_from f (lo + 1) k'
  end.

Lemma all_from_spec : forall f k lo, all_from f lo k = true -> forall x, lo <= x < lo + Z.of_nat k -> f x = true.
Proof.
  intros f k. induction k as [|k IH]; intros lo H x Hx; [lia|].
  cbn [all_from] in H. apply andb_true_iff in H as [H1 H2].
  destruct (Z.eq_dec x lo) as [->|Hne]; [exact H1|]. apply (IH (lo + 1)); [exact H2 | lia].
Qed.

Lemma nth_Forall : forall (P : Z -> Prop) l k d, Forall P l -> P d -> P (nth k l d).
Proof.
  intros P l. induction l as [|x l IH]; intros k d Hl Hd; destruct k; cbn; auto; inversion Hl; auto.
Qed.

(** ---- the scribble text ---- *)

Lemma scr_agree : forall k t, scr_lib t k = scr_owe t k.
Proof.
  induction k as [|k IH]; intros t; [destruct t; reflexivity|].
  destruct t as [|x t']; [reflexivity|]. cbn [scr_lib scr_owe].
  destruct (x =? 0); [reflexivity|].
  destruct t' as [|y t'']; cbn [tl].
  - replace (0x31 <=? 0) with false by reflexivity. rewrite andb_false_r. cbn [andb]. rewrite IH. reflexivity.
  - destruct ((x =? 0x2e) && (0x31 <=? y) && (y <=? 0x39)); rewrite IH; reflexivity.
Qed.

(** check_text_scribble: the characters and the bytes used. *)
Theorem scribble_agree : forall t n, scribble_text_spec t n = owed_scribble_text_spec t n.
Proof. intros t n. apply scr_agree. Qed.

Lemma scr_owe_out : forall k t, Forall (fun x => 0 <= x < 256) t ->
  length (fst (scr_owe t k)) = k /\ Forall (fun x => 0 <= x < 0x80) (fst (scr_owe t k)) /\
  0 <= snd (scr_owe t k) <= Z.of_nat (length t).
Proof.
  assert (Hrep : forall k, length (repeat 0x20 k) = k /\ Forall (fun x => 0 <= x < 0x80) (repeat 0x20 k)).
  { intros k. rewrite repeat_length. split; [reflexivity|]. apply Forall_forall. intros x Hx.
    apply repeat_spec in Hx. cbv beta. lia. }
  induction k as [|k IH]; intros t Ht.
  { destruct t; cbn [scr_owe fst snd length]; (split; [reflexivity | split; [constructor | lia]]). }
  destruct t as [|x t'].
  { cbn [scr_owe fst snd length]. destruct (Hrep (S k)) as [L F]. split; [exact L | split; [exact F | lia]]. }
  inversion Ht as [|? ? Hx Ht']; subst. cbn [scr_owe].
  destruct (x =? 0) eqn:E0.
  { cbn [fst snd length]. destruct (Hrep (S k)) as [L F]. split; [exact L | split; [exact F | lia]]. }
  set (y := match t' with y :: _ => y | [] => 0 end).
  destruct ((x =? 0x2e) && (0x31 <=? y) && (y <=? 0x39)) eqn:E1.
  - apply andb_true_iff in E1 as [E1 E3]. apply andb_true_iff in E1 as [E1 E2].
    destruct t' as [|y' t'']; [cbn in y; subst y; discriminate E2|]. cbn [tl].
    inversion Ht' as [|? ? Hy Ht'']; subst. cbn in y; subst y.
    destruct (IH t'' Ht'') as (L & F & U). destruct (scr_owe t'' k) as [o u]. cbn [fst snd length] in *.
    apply Z.leb_le in E2. apply Z.leb_le in E3.
    split; [lia|]. split; [constructor; [lia | exact F]|]. lia.
  - destruct (IH t' Ht') as (L & F & U). destruct (scr_owe t' k) as [o u]. cbn [fst snd length] in *.
    split; [lia|]. split; [constructor; [destruct (x <? 0x80) eqn:E; [apply Z.ltb_lt in E|]; lia | exact F]|]. lia.
Qed.

(** ---- seg7 ---- *)

Lemma seg7_agree_check : all_from (fun c => seg7_spec c =? owed_seg7_spec c) 0 256 = true.
Proof. vm_compute. reflexivity. Qed.

(** check_text_seg7: the library's table and the harness's glyphs draw each unsigned char alike. *)
Theorem seg7_agree : forall c, 0 <= c < 256 -> seg7_spec c = owed_seg7_spec c.
Proof. intros c Hc. apply Z.eqb_eq. apply (all_from_spec _ 256 0 seg7_agree_check). lia. Qed.

Lemma glyph_segs_check :
  forallb (fun gs => (0 <=? segs_val (snd gs)) && (segs_val (snd gs) <? 128)) glyph = true.
Proof. vm_compute. reflexivity. Qed.

Lemma owed_seg7_range : forall c, owed_seg7_spec c = -1 \/ 0 <= owed_seg7_spec c < 128.
Proof.
  intros c. unfold owed_seg7_spec. pose proof glyph_segs_check as H. revert H.
  generalize glyph as gs. induction gs as [|[g s] gs IH]; intros H; cbn [owed_seg7_go]; [left; reflexivity|].
  cbn [forallb snd] in H. apply andb_true_iff in H as [Hs H]. apply andb_true_iff in Hs as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (glyph_match g c); [right; lia | apply IH; exact H].
Qed.

(** ---- the counter text ---- *)

Lemma skipn_cons_nth : forall (l : list Z) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros k d Hk; [cbn in Hk; lia|].
  destruct k; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hk. lia.
Qed.

Lemma upd_same : forall l i, (Z.to_nat i < length l)%nat -> upd_at l i (nth (Z.to_nat i) l 0) = l.
Proof.
  intros l i Hi. unfold upd_at. rewrite <- skipn_cons_nth by exact Hi. apply firstn_skipn.
Qed.

Lemma upd_length : forall l i v, (Z.to_nat i < length l)%nat -> length (upd_at l i v) = length l.
Proof.
  intros l i v Hi. unfold upd_at. rewrite length_app. cbn [length]. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma nth_upd_other : forall l i v j, (Z.to_nat i < length l)%nat -> j <> Z.to_nat i ->
  nth j (upd_at l i v) 0 = nth j l 0.
Proof.
  intros l i v j Hi Hj. unfold upd_at.
  pose proof (firstn_skipn (Z.to_nat i) l) as Hl. rewrite (skipn_cons_nth _ _ 0 Hi) in Hl.
  transitivity (nth j (firstn (Z.to_nat i) l ++ nth (Z.to_nat i) l 0 :: skipn (S (Z.to_nat i)) l) 0);
    [| rewrite Hl; reflexivity].
  assert (length (firstn (Z.to_nat i) l) = Z.to_nat i) as Lf by (apply firstn_length_le; lia).
  destruct (Nat.lt_ge_cases j (Z.to_nat i)) as [Hlt|Hge].
  - rewrite !app_nth1 by lia. reflexivity.
  - rewrite !app_nth2 by lia. rewrite Lf. destruct (j - Z.to_nat i)%nat eqn:E; [lia|]. reflexivity.
Qed.

(** The first loop's state: n digits placed, 8 dot flags, those from digit n on still clear. *)
Definition ct_inv (n : Z) (dot : list Z) : Prop :=
  0 <= n <= 8 /\ length dot = 8%nat /\ (forall j, n <= Z.of_nat j < 8 -> nth j dot 0 = 0).

Lemma ct_inv_dot : forall n dot, ct_inv n dot -> 0 < n -> ct_inv n (upd_at dot (n - 1) 1).
Proof.
  intros n dot (Hn & Hl & Hz) Hp. split; [lia|]. split; [rewrite upd_length; lia|].
  intros j Hj. rewrite nth_upd_other by lia. apply Hz. lia.
Qed.

Lemma ct_inv_next : forall n dot v, ct_inv n dot -> n < 8 -> ct_inv (n + 1) (upd_at dot n v).
Proof.
  intros n dot v (Hn & Hl & Hz) Hp. split; [lia|]. split; [rewrite upd_length; lia|].
  intros j Hj. rewrite nth_upd_other by lia. apply Hz. lia.
Qed.

Lemma ct1_agree : forall t n s dot, Forall (fun x => 0 <= x < 256) t -> ct_inv n dot ->
  ct1_lib t n s dot = ct1_owe t n s dot.
Proof.
  induction t as [|ch t IH]; intros n s dot Ht Hinv; [reflexivity|].
  inversion Ht as [|? ? Hch Ht']; subst. cbn [ct1_lib ct1_owe].
  destruct (ch =? 0); [reflexivity|].
  destruct ((ch =? 0x2e) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0)) eqn:E1.
  - apply andb_true_iff in E1 as [E1 _]. apply andb_true_iff in E1 as [_ E1]. apply Z.ltb_lt in E1.
    apply IH; [exact Ht' | apply ct_inv_dot; assumption].
  - rewrite seg7_agree by (destruct (ch =? 0x2e); lia).
    destruct ((owed_seg7_spec (if ch =? 0x2e then 0x20 else ch) <? 0) || (n =? 8)) eqn:E2; [reflexivity|].
    apply orb_false_iff in E2 as [_ E2]. apply Z.eqb_neq in E2.
    destruct Hinv as (Hn & Hl & Hz) eqn:Hinv'.
    replace (if ch =? 0x2e then upd_at dot n 1 else dot) with (upd_at dot n (if ch =? 0x2e then 1 else 0)).
    + apply IH; [exact Ht' | apply ct_inv_next; [exact Hinv | lia]].
    + destruct (ch =? 0x2e); [reflexivity|].
      rewrite <- (Hz (Z.to_nat n)) at 1 by lia. apply upd_same. lia.
Qed.

Lemma ct_inv_0 : ct_inv 0 (repeat 0 8).
Proof. split; [lia|]. split; [reflexivity|]. intros j _. apply nth_repeat. Qed.

(** check_text_counter: the code, the digits and the dots. *)
Theorem counter_text_agree : forall t, Forall (fun x => 0 <= x < 256) t ->
  counter_text_spec t = owed_counter_text_spec t.
Proof.
  intros t Ht. unfold counter_text_spec, owed_counter_text_spec. rewrite ct1_agree; [reflexivity | exact Ht |].
  apply ct_inv_0.
Qed.

Lemma ct1_owe_out : forall t n s dot n' s' dot', Forall (fun v => 0 <= v < 128) s -> 0 <= n ->
  ct1_owe t n s dot = Some (n', s', dot') -> Forall (fun v => 0 <= v < 128) s'.
Proof.
  induction t as [|ch t IH]; intros n s dot n' s' dot' Hs Hn H; cbn [ct1_owe] in H.
  - injection H as <- <- <-. exact Hs.
  - destruct (ch =? 0); [injection H as <- <- <-; exact Hs|].
    destruct ((ch =? 0x2e) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0)); [eapply IH; eauto|].
    destruct ((owed_seg7_spec (if ch =? 0x2e then 0x20 else ch) <? 0) || (n =? 8)) eqn:E; [discriminate H|].
    apply orb_false_iff in E as [E _]. apply Z.ltb_ge in E.
    eapply IH; [| | exact H]; [| lia]. apply Forall_app. split; [exact Hs|]. constructor; [|constructor].
    destruct (owed_seg7_range (if ch =? 0x2e then 0x20 else ch)) as [E'|E']; lia.
Qed.

Lemma ct2_go_out : forall k n s dot i seg d,
  Forall (fun v => 0 <= v < 128) s -> Forall (fun v => 0 <= v < 128) seg -> 0 <= d < 128 -> 0 <= i ->
  i + Z.of_nat k <= 8 ->
  fst (fst (ct2_go n s dot i k seg d)) = 0 ->
  length (snd (fst (ct2_go n s dot i k seg d))) = (length seg + k)%nat /\
  Forall (fun v => 0 <= v < 128) (snd (fst (ct2_go n s dot i k seg d))) /\
  0 <= snd (ct2_go n s dot i k seg d) < 128.
Proof.
  induction k as [|k IH]; intros n s dot i seg d Hs Hseg Hd Hi Hk H; cbn [ct2_go] in *.
  - cbn [fst snd]. rewrite Nat.add_0_r. auto.
  - set (v := if i - (8 - n) <? 0 then 0 else nth (Z.to_nat (i - (8 - n))) s 0) in *.
    assert (Hv : 0 <= v < 128).
    { subst v. destruct (i - (8 - n) <? 0); [lia|]. apply (nth_Forall (fun v => 0 <= v < 128)); [exact Hs | lia]. }
    assert (Hseg' : Forall (fun v => 0 <= v < 128) (seg ++ [v])).
    { apply Forall_app. split; [exact Hseg | constructor; [exact Hv | constructor]]. }
    destruct ((0 <=? i - (8 - n)) && negb (nth (Z.to_nat (i - (8 - n))) dot 0 =? 0)).
    + destruct (i =? 7) eqn:E7; [cbn in H; discriminate H|]. apply Z.eqb_neq in E7.
      assert (Hd' : 0 <= Z.lor d (2 ^ i) < 128).
      { pose proof (lor_lt_pow2 d (2 ^ i) 7) as Hl. change (2 ^ 7) with 128 in Hl. apply Hl; [lia|].
        split; [apply Z.pow_nonneg; lia|]. change 128 with (2 ^ 7). apply Z.pow_lt_mono_r; lia. }
      destruct (IH n s dot (i + 1) (seg ++ [v]) (Z.lor d (2 ^ i)) Hs Hseg' Hd' ltac:(lia) ltac:(lia) H)
        as (L & F & D).
      rewrite length_app in L. cbn [length] in L. split; [lia|]. auto.
    + destruct (IH n s dot (i + 1) (seg ++ [v]) d Hs Hseg' Hd ltac:(lia) ltac:(lia) H) as (L & F & D).
      rewrite length_app in L. cbn [length] in L. split; [lia|]. auto.
Qed.

(** An owed counter text that succeeds gives 8 digits of 7 bits and dots of 7 bits. *)
Lemma owed_counter_ok : forall t rc seg dots, owed_counter_text_spec t = (rc, seg, dots) -> rc = 0 ->
  length seg = 8%nat /\ Forall (fun v => 0 <= v < 128) seg /\ 0 <= dots < 128.
Proof.
  intros t rc seg dots H Hrc. unfold owed_counter_text_spec in H.
  destruct (ct1_owe t 0 [] (repeat 0 8)) as [[[n s] dot]|] eqn:E1; [|injection H as <- _ _; discriminate Hrc].
  pose proof (ct1_owe_out t 0 [] (repeat 0 8) n s dot (Forall_nil _) ltac:(lia) E1) as Hs.
  unfold ct2 in H. pose proof (ct2_go_out 8 n s dot 0 [] 0 Hs (Forall_nil _) ltac:(lia) ltac:(lia) ltac:(cbn; lia))
    as Hc.
  rewrite H in Hc. cbn [fst snd length] in Hc. apply Hc. exact Hrc.
Qed.

(** ---- the call records of the text operations ---- *)

(** The desk of a text operation is Control|24 or ProControl, with at most 8 characters. *)
Lemma text_desk_ok : forall od, od_ok od -> od_ok (Some (text_desk od)) /\ 0 <= d_chars (text_desk od) <= 8.
Proof.
  intros od [-> | [-> | ->]]; cbn; (split; [unfold od_ok; auto | lia]).
Qed.

(** Operation 12: the SCRIBBLE call record after a scribble text (a = u8 & 0x7f). *)
Lemma reader_ok_12 : forall t a chars, 0 <= a < 2 ^ 32 -> 0 <= chars <= 24 -> Forall (fun x => 0 <= x < 256) t ->
  reader_ok 9 a 0 0 0 (scribble_bytes t chars) 0.
Proof.
  intros t a chars Ha Hc Ht. unfold scribble_bytes, owed_scribble_text_spec.
  destruct (scr_owe_out (Z.to_nat chars) t Ht) as (L & F & _).
  repeat split; try lia; try (change (2 ^ 32) with 4294967296; lia).
  - rewrite length_app, repeat_length, L. lia.
  - apply Forall_app. split.
    + eapply Forall_impl; [| exact F]. cbn. intros x Hx. lia.
    + apply Forall_forall. intros x Hx. apply repeat_spec in Hx. cbv beta. lia.
Qed.

(** Operation 13: the COUNTER call record after an owed counter text that succeeds (b = dots). *)
Lemma reader_ok_13 : forall t seg dots, owed_counter_text_spec t = (0, seg, dots) ->
  reader_ok 10 0 dots 0 0 (counter_bytes seg) 0.
Proof.
  intros t seg dots H. destruct (owed_counter_ok t 0 seg dots H eq_refl) as (L & F & D).
  unfold counter_bytes. repeat split; try lia; try (change (2 ^ 32) with 4294967296; lia).
  - rewrite length_app, repeat_length, L. reflexivity.
  - apply Forall_app. split.
    + eapply Forall_impl; [| exact F]. cbn. intros x Hx. lia.
    + apply Forall_forall. intros x Hx. apply repeat_spec in Hx. cbv beta. lia.
Qed.

(** ---- check_text_masks ---- *)

Lemma meter_mask_agree : forall n, 0 <= n -> meter_mask_spec n = owed_meter_mask n.
Proof.
  intros n Hn. unfold meter_mask_spec, owed_meter_mask. apply Z.mod_small.
  pose proof (pow_m1 (Z.min n 14) ltac:(lia)) as H. change (2 ^ 14) with 16384 in H.
  change (2 ^ 16) with 65536. lia.
Qed.

Lemma meter_segments_check :
  all_from (fun m => meter_segments_spec m =? spec_segments_spec m) 0 (Z.to_nat 65536) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma meter_segments_agree : forall mask, 0 <= mask < 2 ^ 16 -> meter_segments_spec mask = spec_segments_spec mask.
Proof.
  intros mask Hm. apply Z.eqb_eq. apply (all_from_spec _ _ 0 meter_segments_check).
  rewrite Z2Nat.id by lia. change (2 ^ 16) with 65536 in Hm. lia.
Qed.

Lemma ring_dot_agree : forall n, 0 <= n -> ring_dot_spec n = owed_ring_dot n.
Proof.
  intros n Hn. unfold ring_dot_spec, owed_ring_dot. destruct (n <? 15) eqn:E; [|reflexivity].
  apply Z.ltb_lt in E. apply Z.mod_small. split; [apply Z.pow_nonneg; lia|].
  apply Z.pow_lt_mono_r; lia.
Qed.

Lemma ring_fill_agree : forall n, 0 <= n -> ring_fill_spec n = owed_ring_fill n.
Proof.
  intros n Hn. unfold ring_fill_spec, owed_ring_fill. destruct (n <=? 15) eqn:E; [|reflexivity].
  apply Z.leb_le in E. apply Z.mod_small.
  assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ n <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). change (2 ^ 15) with 32768 in *.
  change (2 ^ 16) with 65536. lia.
Qed.

(** check_text_masks's four comparisons, for its unsigned n and uint16_t mask. *)
Theorem masks_agree : forall n mask, 0 <= n < 2 ^ 32 -> 0 <= mask < 2 ^ 16 ->
  meter_mask_spec n = owed_meter_mask n /\ meter_segments_spec mask = spec_segments_spec mask /\
  ring_dot_spec n = owed_ring_dot n /\ ring_fill_spec n = owed_ring_fill n.
Proof.
  intros n mask Hn Hm. split; [apply meter_mask_agree; lia|]. split; [apply meter_segments_agree; exact Hm|].
  split; [apply ring_dot_agree | apply ring_fill_agree]; lia.
Qed.
