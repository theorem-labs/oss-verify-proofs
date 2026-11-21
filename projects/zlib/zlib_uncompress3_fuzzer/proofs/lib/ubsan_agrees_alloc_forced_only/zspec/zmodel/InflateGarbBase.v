(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition weq (w w' : iw) : Prop :=
  w_s w' = w_s w /\ w_r w' = w_r w
  /\ w_c w' = icset_outbuf (w_c w) (ic_outbuf (w_c w'))
  /\ arr_len (ic_outbuf (w_c w')) = arr_len (ic_outbuf (w_c w))
  /\ (forall i, 0 <= i < ir_put (w_r w) -> arr_get (ic_outbuf (w_c w')) i = arr_get (ic_outbuf (w_c w)) i)
  /\ ic_next_out (w_c w) <= ir_put (w_r w).









Definition agree_below (p : Z) (a a' : arr) : Prop :=
  arr_len a' = arr_len a /\ forall i, 0 <= i < p -> arr_get a' i = arr_get a i.






Lemma ic_outbuf_set : forall c ob, ic_outbuf (icset_outbuf c ob) = ob.
Proof. intros [] ob; reflexivity. Qed.
Lemma icset_outbuf_twice : forall c a b, icset_outbuf (icset_outbuf c a) b = icset_outbuf c b.
Proof. intros [] a b; reflexivity. Qed.
Lemma icset_outbuf_self : forall c, icset_outbuf c (ic_outbuf c) = c.
Proof. intros []; reflexivity. Qed.
Lemma ic_input_set : forall c ob, ic_input (icset_outbuf c ob) = ic_input c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_next_in_set : forall c ob, ic_next_in (icset_outbuf c ob) = ic_next_in c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_avail_in_set : forall c ob, ic_avail_in (icset_outbuf c ob) = ic_avail_in c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_next_out_set : forall c ob, ic_next_out (icset_outbuf c ob) = ic_next_out c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_avail_out_set : forall c ob, ic_avail_out (icset_outbuf c ob) = ic_avail_out c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_total_in_set : forall c ob, ic_total_in (icset_outbuf c ob) = ic_total_in c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_total_out_set : forall c ob, ic_total_out (icset_outbuf c ob) = ic_total_out c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_adler_set : forall c ob, ic_adler (icset_outbuf c ob) = ic_adler c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_data_type_set : forall c ob, ic_data_type (icset_outbuf c ob) = ic_data_type c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_msg_set : forall c ob, ic_msg (icset_outbuf c ob) = ic_msg c.
Proof. intros [] ob; reflexivity. Qed.
Create HintDb icr discriminated.
#[export] Hint Rewrite ic_outbuf_set icset_outbuf_twice icset_outbuf_self ic_input_set ic_next_in_set ic_avail_in_set
  ic_next_out_set ic_avail_out_set ic_total_in_set ic_total_out_set ic_adler_set ic_data_type_set ic_msg_set : icr.






Definition zupto (n : Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat n)).
Lemma zupto_spec : forall n i, In i (zupto n) <-> 0 <= i < n.
Proof.
  intros n i. unfold zupto. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hi. exists (Z.to_nat i). split; [lia|]. apply in_seq. lia.
Qed.
Lemma forallb_zupto : forall f n, forallb f (zupto n) = true -> forall i, 0 <= i < n -> f i = true.
Proof. intros f n H i Hi. rewrite forallb_forall in H. apply H. apply zupto_spec. exact Hi. Qed.


Definition ares_rel {A} (a a' : ares A) : Prop :=
  match a, a' with
  | ARun x w1, ARun x' w1' => x' = x /\ weq w1 w1'
  | ALeave w1, ALeave w1' => weq w1 w1'
  | ARet rc w1, ARet rc' w1' => rc' = rc /\ weq w1 w1'
  | _, _ => False
  end.

Definition WP {A} (chk : iw -> bool) (m : AM A) : Prop :=
  forall w w', chk w' = true -> weq w w' -> ares_rel (m w) (m w').
Definition ctrue : iw -> bool := fun _ => true.
Definition WP0 {A} (m : AM A) : Prop := WP ctrue m.

Definition after {A} (m : AM A) (chk : A -> iw -> bool) (w : iw) : bool :=
  match m w with ARun a w1 => chk a w1 | _ => true end.

Lemma WP_mono : forall {A} (chk chk' : iw -> bool) (m : AM A),
  (forall w, chk' w = true -> chk w = true) -> WP chk m -> WP chk' m.
Proof. intros A chk chk' m H HW w w' C E. apply HW; [apply H; exact C | exact E]. Qed.


Lemma WP_bind : forall {A B} chk1 (m : AM A) chk2 (f : A -> AM B),
  WP chk1 m -> (forall a, WP (chk2 a) (f a)) ->
  WP (fun w => chk1 w && after m chk2 w) (abind m f).
Proof.
  intros A B chk1 m chk2 f H1 H2 w w' C E. apply andb_prop in C as [C1 C2]. unfold after in C2.
  unfold abind. specialize (H1 w w' C1 E). destruct (m w) as [a w1|w1|rc w1]; destruct (m w') as [a' w1'|w1'|rc' w1']; cbn in H1; try contradiction.
  - destruct H1 as [-> E1]. apply H2; [exact C2 | exact E1].
  - exact H1.
  - exact H1.
Qed.


Lemma WP_bind0 : forall {A B} (m : AM A) (f : A -> AM B),
  WP0 m -> (forall a, WP0 (f a)) -> WP0 (abind m f).
Proof.
  intros A B m f H1 H2. unfold WP0. apply (WP_mono (fun w => ctrue w && after m (fun _ => ctrue) w)); [|apply WP_bind; assumption].
  intros w _. unfold after, ctrue. destruct (m w); reflexivity.
Qed.


Lemma WP_aret : forall {A} (a : A), WP0 (aret a).
Proof. intros A a w w' _ E. cbn. auto. Qed.
Lemma WP_aleave : forall {A}, WP0 (@aleave A).
Proof. intros A w w' _ E. exact E. Qed.
Lemma WP_areturn : forall {A} rc, WP0 (@areturn A rc).
Proof. intros A rc w w' _ E. cbn. auto. Qed.

Lemma WP_gs : forall {A} (f : inflate_state -> A), WP0 (gs f).
Proof. intros A f w w' _ E. cbn. rewrite (proj1 E). split; [reflexivity | exact E]. Qed.
Lemma WP_gr : forall {A} (f : iregs -> A), WP0 (gr f).
Proof. intros A f w w' _ E. cbn. rewrite (proj1 (proj2 E)). split; [reflexivity | exact E]. Qed.
Lemma WP_gc : forall {A} (f : icall -> A),
  (forall c ob, f (icset_outbuf c ob) = f c) -> WP0 (gc f).
Proof. intros A f Hf w w' _ E. cbn. rewrite (proj1 (proj2 (proj2 E))), Hf. split; [reflexivity | exact E]. Qed.

Lemma WP_us : forall (f : inflate_state -> inflate_state), WP0 (us f).
Proof.
  intros f w w' _ (Hs & Hr & Hc & L & AG & NO). cbn. split; [reflexivity|].
  unfold weq; cbn. rewrite Hs, Hr. repeat split; assumption.
Qed.
Lemma WP_ur : forall (f : iregs -> iregs),
  (forall r, ir_put (f r) = ir_put r) -> WP0 (ur f).
Proof.
  intros f Hf w w' _ (Hs & Hr & Hc & L & AG & NO). cbn. split; [reflexivity|].
  unfold weq; cbn. rewrite Hs, Hr, Hf. repeat split; assumption.
Qed.
Lemma WP_uc : forall (f : icall -> icall),
  (forall c ob, f (icset_outbuf c ob) = icset_outbuf (f c) ob) ->
  (forall c, ic_outbuf (f c) = ic_outbuf c) ->
  (forall c, ic_next_out (f c) = ic_next_out c) ->
  WP0 (uc f).
Proof.
  intros f H1 H2 H3 w w' _ (Hs & Hr & Hc & L & AG & NO). cbn. split; [reflexivity|].
  unfold weq; cbn. rewrite Hs, Hr, Hc, H1, !H2, H3. autorewrite with icr. repeat split; assumption.
Qed.

Lemma WP_if0 : forall {A} (b : bool) (m1 m2 : AM A),
  WP0 m1 -> WP0 m2 -> WP0 (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.


Definition keeps {A} (chk : iw -> bool) (m : AM A) : Prop :=
  forall w a w1, chk w = true -> m w = ARun a w1 -> chk w1 = true.

Lemma WP_aget : forall {A} (K : iw -> AM A),
  (forall s c r ob, K (mkW s (icset_outbuf c ob) r) = K (mkW s c r)) ->
  (forall w, WP0 (K w)) -> WP0 (abind aget K).
Proof.
  intros A K HK HW w w' C E. cbn [abind aget]. pose proof E as (Hs & Hr & Hc & _).
  destruct w as [s c r], w' as [s' c' r']; cbn in Hs, Hr, Hc. subst s' r'. rewrite Hc at 1. rewrite HK.
  apply HW; [exact C | exact E].
Qed.

Lemma WP_amodify : forall (f : iw -> iw),
  (forall w w', weq w w' -> weq (f w) (f w')) -> WP0 (amodify f).
Proof. intros f Hf w w' _ E. cbn. split; [reflexivity | apply Hf; exact E]. Qed.

Lemma weq_RESTORE : forall w w', weq w w' -> weq (RESTORE w) (RESTORE w').
Proof.
  intros [s c r] [s' c' r'] (Hs & Hr & Hc & L & AG & NO); cbn in *. subst s' r'. rewrite Hc.
  unfold weq, RESTORE; cbn. destruct c; cbn in *. repeat split; try assumption. lia.
Qed.


Lemma WP_PULLBYTE : WP0 PULLBYTE.
Proof.
  intros w w' _ (Hs & Hr & Hc & L & AG & NO). unfold PULLBYTE. rewrite Hr, Hc.
  cbn [ic_input icset_outbuf]. replace (ic_input (icset_outbuf (w_c w) (ic_outbuf (w_c w')))) with (ic_input (w_c w)) by (destruct (w_c w); reflexivity).
  destruct (ir_have (w_r w) =? 0).
  - unfold weq. repeat split; assumption.
  - cbn. split; [reflexivity|]. unfold weq; cbn. rewrite Hs, Hc. repeat split; try assumption.
Qed.

Lemma WP_NEEDBITS_k : forall k n, WP0 (NEEDBITS_k k n).
Proof.
  induction k as [|k IH]; intros n; cbn [NEEDBITS_k].
  - apply WP_aret.
  - apply WP_bind0; [apply WP_gr|]. intros bits. apply WP_if0; [|apply WP_aret].
    apply WP_bind0; [apply WP_PULLBYTE | intros _; apply IH].
Qed.
Lemma WP_NEEDBITS : forall n, WP0 (NEEDBITS n).
Proof. intros n. apply WP_NEEDBITS_k. Qed.



Lemma WP_BITS : forall n, WP0 (BITS n).
Proof. intros n. apply WP_gr. Qed.
Lemma WP_HOLD : WP0 HOLD.
Proof. apply WP_gr. Qed.
Lemma WP_DROPBITS : forall n, WP0 (DROPBITS n).
Proof. intros n. apply WP_ur. reflexivity. Qed.
Lemma WP_INITBITS : WP0 INITBITS.
Proof. apply WP_ur. reflexivity. Qed.
Lemma WP_BYTEBITS : WP0 BYTEBITS.
Proof. apply WP_ur. reflexivity. Qed.
Lemma WP_set_mode : forall m, WP0 (set_mode m).
Proof. intros m. apply WP_us. Qed.
Lemma WP_set_msg : forall m, WP0 (set_msg m).
Proof. intros m. apply WP_uc; intros; try destruct c; reflexivity. Qed.
Lemma WP_go_bad : forall m, WP0 (go_bad m).
Proof. intros m. apply WP_bind0; [apply WP_set_msg | intros _; apply WP_set_mode]. Qed.
Lemma WP_set_adler_check : forall v, WP0 (set_adler_check v).
Proof. intros v. apply WP_bind0; [apply WP_us | intros _; apply WP_uc; intros; try destruct c; reflexivity]. Qed.

Lemma WP_DECODE_k : forall k p index need, WP0 (DECODE_k k p index need).
Proof.
  induction k as [|k IH]; intros p index need; cbn [DECODE_k].
  - apply WP_bind0; [apply WP_HOLD | intros hold; apply WP_gs].
  - apply WP_bind0; [apply WP_HOLD | intros hold].
    apply WP_bind0; [apply WP_gr | intros bits].
    apply WP_bind0; [apply WP_gs | intros here].
    apply WP_if0; [apply WP_aret|]. apply WP_bind0; [apply WP_PULLBYTE | intros _; apply IH].
Qed.
Lemma WP_DECODE1 : forall p nbits, WP0 (DECODE1 p nbits).
Proof. intros. apply WP_DECODE_k. Qed.
Lemma WP_DECODE2 : forall p last, WP0 (DECODE2 p last).
Proof. intros. apply WP_DECODE_k. Qed.



Lemma WP_crc_input : forall copy, WP0 (crc_input copy).
Proof.
  intros copy w w' _ (Hs & Hr & Hc & L & AG & NO). unfold crc_input. rewrite Hs, Hr, Hc.
  replace (ic_input (icset_outbuf (w_c w) (ic_outbuf (w_c w')))) with (ic_input (w_c w)) by (destruct (w_c w); reflexivity).
  cbn. split; [reflexivity|]. unfold weq; cbn. rewrite Hr, Hc. repeat split; assumption.
Qed.
Lemma WP_CRC2 : forall word, WP0 (CRC2 word).
Proof. intros. apply WP_us. Qed.
Lemma WP_CRC4 : forall word, WP0 (CRC4 word).
Proof. intros. apply WP_us. Qed.

Lemma WP_set_lens : forall i v, WP0 (set_lens i v).
Proof. intros. apply WP_us. Qed.
Lemma WP_lens_repeat : forall copy len, WP0 (lens_repeat copy len).
Proof. intros. apply WP_us. Qed.

Lemma WP_name_like : forall flag, WP0 (name_like flag).
Proof.
  intros flag. unfold name_like.
  apply WP_bind0; [apply WP_gs | intros s]. apply WP_if0; [|apply WP_aret].
  apply WP_bind0; [apply WP_gr | intros r]. apply WP_if0; [apply WP_aret|].
  apply WP_aget.
  - intros s0 c r0 ob. cbn [w_c]. rewrite ic_input_set. reflexivity.
  - intros w0. destruct (scan_zero _ _ _) as [copy len].
    apply WP_bind0; [apply WP_if0; [apply WP_crc_input | apply WP_aret] | intros _].
    apply WP_bind0; [apply WP_ur; reflexivity | intros _]. apply WP_if0; apply WP_aret.
Qed.

Ltac wp0_step :=
  lazymatch goal with
  | |- WP0 (abind aget _) => apply WP_aget; [intros; cbn [w_c w_s w_r]; autorewrite with icr; reflexivity | intros]
  | |- WP0 (abind _ _) => apply WP_bind0; [|intros]
  | |- WP0 (if _ then _ else _) => apply WP_if0
  | |- WP0 (aret _) => apply WP_aret
  | |- WP0 aleave => apply WP_aleave
  | |- WP0 (areturn _) => apply WP_areturn
  | |- WP0 (gs _) => apply WP_gs
  | |- WP0 (gr _) => apply WP_gr
  | |- WP0 (gc _) => apply WP_gc; intros [] ?; reflexivity
  | |- WP0 (us _) => apply WP_us
  | |- WP0 (ur _) => apply WP_ur; intros []; reflexivity
  | |- WP0 (uc _) => apply WP_uc; [intros [] ? | intros [] | intros []]; reflexivity
  | |- WP0 (amodify RESTORE) => apply WP_amodify; apply weq_RESTORE
  | |- WP0 PULLBYTE => apply WP_PULLBYTE
  | |- WP0 (NEEDBITS_k _ _) => apply WP_NEEDBITS_k
  | |- WP0 (NEEDBITS _) => apply WP_NEEDBITS
  | |- WP0 (BITS _) => apply WP_BITS
  | |- WP0 HOLD => apply WP_HOLD
  | |- WP0 (DROPBITS _) => apply WP_DROPBITS
  | |- WP0 INITBITS => apply WP_INITBITS
  | |- WP0 BYTEBITS => apply WP_BYTEBITS
  | |- WP0 (set_mode _) => apply WP_set_mode
  | |- WP0 (set_msg _) => apply WP_set_msg
  | |- WP0 (go_bad _) => apply WP_go_bad
  | |- WP0 (set_adler_check _) => apply WP_set_adler_check
  | |- WP0 (DECODE_k _ _ _ _) => apply WP_DECODE_k
  | |- WP0 (DECODE1 _ _) => apply WP_DECODE1
  | |- WP0 (DECODE2 _ _) => apply WP_DECODE2
  | |- WP0 (crc_input _) => apply WP_crc_input
  | |- WP0 (CRC2 _) => apply WP_CRC2
  | |- WP0 (CRC4 _) => apply WP_CRC4
  | |- WP0 (set_lens _ _) => apply WP_set_lens
  | |- WP0 (lens_repeat _ _) => apply WP_lens_repeat
  | |- WP0 (name_like _) => apply WP_name_like
  | |- WP0 (aux _ _) => unfold aux; apply WP_if0; [apply WP_us | apply WP_aret]
  | |- WP0 (set_back _ _) => unfold set_back, aux; apply WP_if0; [apply WP_us | apply WP_aret]
  | |- WP0 (add_back _ _) => unfold add_back, aux; apply WP_if0; [apply WP_us | apply WP_aret]
  | |- WP0 (match ?x with _ => _ end) => destruct x
  | |- WP0 (let x := _ in _) => cbv zeta
  end.
Ltac wp0 := repeat wp0_step.

Lemma weq_canon : forall w w', weq w w' ->
  exists ob', w' = mkW (w_s w) (icset_outbuf (w_c w) ob') (w_r w)
    /\ agree_below (ir_put (w_r w)) (ic_outbuf (w_c w)) ob' /\ ic_next_out (w_c w) <= ir_put (w_r w).
Proof.
  intros [s c r] [s' c' r'] (Hs & Hr & Hc & L & AG & NO); cbn in *. subst s' r'.
  exists (ic_outbuf c'). rewrite <- Hc. split; [reflexivity|]. split; [split; assumption | exact NO].
Qed.

Ltac am_cbn :=
  cbn beta iota zeta delta [abind aret gs gc gr us ur uc aleave areturn amodify agets aget aput w_s w_c w_r wset_s wset_r wset_c
       BITS HOLD DROPBITS INITBITS BYTEBITS set_mode set_msg go_bad set_adler_check
       is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk
       iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits iset_wsize
       iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset iset_extra iset_lencode
       iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have iset_next iset_lens iset_work
       iset_codes iset_sane iset_back iset_was iset_self_blk
       ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg
       icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out icset_adler
       icset_data_type icset_msg
       ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret
       irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret
       fst snd].

Ltac wp_canon :=
  let w := fresh "w" in let w' := fresh "w'" in let C := fresh "C" in let E := fresh "E" in
  let ob' := fresh "ob'" in
  intros w w' C E;
  let H := fresh in
  destruct (weq_canon w w' E) as (ob' & H & AG & NO); rewrite H in C |- *; clear H E;
  destruct w as [s c r]; cbn [w_s w_c w_r] in C, AG, NO |- *.

Ltac am_red :=
  lazy beta iota zeta delta [abind aret gs gc gr us ur uc aleave areturn amodify agets aget aput wset_s wset_r wset_c
                             set_mode set_msg go_bad set_adler_check BITS HOLD DROPBITS INITBITS BYTEBITS].
Ltac am_red_in H :=
  lazy beta iota zeta delta [abind aret gs gc gr us ur uc aleave areturn amodify agets aget aput wset_s wset_r wset_c
                             set_mode set_msg go_bad set_adler_check BITS HOLD DROPBITS INITBITS BYTEBITS] in H.

