(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateInv InflateInvTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition live_check (s : inflate_state) : bool :=
  let m := is_mode s in
  negb (m =? HEAD) && negb (m =? BAD) && negb (m =? MEM) && negb (m =? SYNC)
  && (((FLAGS <=? m) && (m <=? HCRC)) || negb (is_wrap s =? 0)).
Definition live_length (s : inflate_state) : bool :=
  let m := is_mode s in
  (m =? COPY_) || (m =? COPY) || (m =? LIT) || (m =? LENEXT) || (m =? DIST) || (m =? DISTEXT) || (m =? MATCH)
  || ((m =? EXTRA) && negb (Z.land (is_flags s) 1024 =? 0)).
Definition live_offset (m : Z) : bool := (m =? DISTEXT) || (m =? MATCH).
Definition live_extra (m : Z) : bool := (m =? LENEXT) || (m =? DISTEXT).
Definition live_lenbits (m : Z) : bool := codes_live m || (m =? CODELENS).
Definition live_distbits (m : Z) : bool := codes_live m.
Definition live_dyn (m : Z) : bool := (m =? LENLENS) || (m =? CODELENS).
Definition live_codes (m : Z) : bool := negb ((m =? BAD) || (m =? MEM) || (m =? SYNC)).

Definition icoreq (s : inflate_state) :=
  (is_mode s, is_last s, is_wrap s, is_havedict s, is_flags s, is_dmax s, is_total s, is_head s, is_wbits s,
   is_wsize s, is_whave s, is_wnext s, is_window_blk s, is_hold s, is_bits s, is_lencode s, is_distcode s,
   is_next s, is_sane s, is_back s, is_self_blk s).


Definition WDW (s : inflate_state) : Prop :=
  8 <= is_wbits s <= 15 /\ is_sane s = 1
  /\ 0 <= is_whave s <= is_wsize s /\ 0 <= is_wnext s <= is_wsize s
  /\ (is_wsize s <> 0 -> is_whave s < is_wsize s -> is_wnext s = is_whave s)
  /\ match is_window_blk s with
     | Some _ => arr_len (is_window s) = 2 ^ is_wbits s /\ (is_wsize s = 0 \/ is_wsize s = 2 ^ is_wbits s)
     | None => is_wsize s = 0 /\ arr_len (is_window s) = 0
     end.

Definition SEQX (chk : bool) (s1 s2 : inflate_state) : Prop :=
  icoreq s2 = icoreq s1
  /\ (chk = true -> is_check s2 = is_check s1)
  /\ (live_length s1 = true -> is_length s2 = is_length s1)
  /\ (live_offset (is_mode s1) = true -> is_offset s2 = is_offset s1)
  /\ (live_extra (is_mode s1) = true -> is_extra s2 = is_extra s1)
  /\ (live_lenbits (is_mode s1) = true -> is_lenbits s2 = is_lenbits s1)
  /\ (live_distbits (is_mode s1) = true -> is_distbits s2 = is_distbits s1)
  /\ (live_dyn (is_mode s1) = true ->
      is_ncode s2 = is_ncode s1 /\ is_nlen s2 = is_nlen s1 /\ is_ndist s2 = is_ndist s1 /\ is_have s2 = is_have s1)
  /\ arr_len (is_lens s2) = arr_len (is_lens s1) /\ arr_len (is_work s2) = arr_len (is_work s1)
  /\ arr_len (is_codes s2) = arr_len (is_codes s1) /\ arr_len (is_window s2) = arr_len (is_window s1)
  /\ (is_mode s1 = LENLENS -> forall j, 0 <= j < is_have s1 ->
        arr_get (is_lens s2) (arr_get order_a j) = arr_get (is_lens s1) (arr_get order_a j))
  /\ (is_mode s1 = CODELENS -> forall i, 0 <= i -> (i < 19 \/ i < is_have s1) ->
        arr_get (is_lens s2) i = arr_get (is_lens s1) i)
  /\ (live_codes (is_mode s1) = true -> forall i, 0 <= i < is_next s1 -> arr_get (is_codes s2) i = arr_get (is_codes s1) i)
  /\ (forall i, 0 <= i < is_whave s1 -> arr_get (is_window s2) i = arr_get (is_window s1) i)
  /\ WDW s1.

Definition SEQ (s1 s2 : inflate_state) : Prop := SEQX (live_check s1) s1 s2.

Definition chk_guard (s : inflate_state) (r : iregs) : bool :=
  live_check s || (negb (is_wrap s =? 0) && negb (ir_out r =? ir_left r)).

Definition cdt (c : icall) (d : Z) : icall := icset_data_type c d.

Definition WEQ (w1 w2 : iw) : Prop :=
  w_c w2 = cdt (w_c w1) (ic_data_type (w_c w2)) /\ w_r w2 = w_r w1 /\ SEQX (chk_guard (w_s w1) (w_r w1)) (w_s w1) (w_s w2).

Definition RREL {A} (a1 a2 : ares A) : Prop :=
  match a1, a2 with
  | ARun x1 w1, ARun x2 w2 => x2 = x1 /\ WEQ w1 w2
  | ALeave w1, ALeave w2 => WEQ w1 w2
  | ARet rc1 w1, ARet rc2 w2 => rc2 = rc1 /\ WEQ w1 w2
  | _, _ => False
  end.




Definition reput {A} (s : inflate_state) (c : icall) (a : ares A) : ares A :=
  match a with
  | ARun x w => ARun x (mkW s c (w_r w))
  | ALeave w => ALeave (mkW s c (w_r w))
  | ARet rc w => ARet rc (mkW s c (w_r w))
  end.

Definition keep5 (r r' : iregs) : Prop :=
  ir_put r' = ir_put r /\ ir_left r' = ir_left r /\ ir_in r' = ir_in r /\ ir_out r' = ir_out r /\ ir_ret r' = ir_ret r.

Definition state_free {A} (m : AM A) : Prop :=
  forall s s' c c' r, ic_input c' = ic_input c ->
    m (mkW s' c' r) = reput s' c' (m (mkW s c r)) /\
    match m (mkW s c r) with ARun _ w | ALeave w | ARet _ w => exists r', w = mkW s c r' /\ keep5 r r' end.

Lemma keep5_refl : forall r, keep5 r r.
Proof. intros r. repeat split; reflexivity. Qed.
Lemma keep5_trans : forall r1 r2 r3, keep5 r1 r2 -> keep5 r2 r3 -> keep5 r1 r3.
Proof. intros r1 r2 r3 (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5). unfold keep5. rewrite B1, B2, B3, B4, B5. repeat split; assumption. Qed.

Lemma PULLBYTE_free : state_free PULLBYTE.
Proof.
  intros s s' c c' r Ei. unfold PULLBYTE. cbn [w_r w_c w_s wset_r]. rewrite Ei.
  destruct (ir_have r =? 0); (split; [reflexivity | eexists; split; [reflexivity | repeat split; reflexivity]]).
Qed.

Lemma NEEDBITS_k_free : forall k n, state_free (NEEDBITS_k k n).
Proof.
  induction k as [|k IH]; intros n s s' c c' r Ei.
  - cbn. split; [reflexivity | eexists; split; [reflexivity | apply keep5_refl]].
  - cbn [NEEDBITS_k]. unfold abind, gr, aret. cbn [w_r].
    destruct (ir_bits r <? n); [| split; [reflexivity | eexists; split; [reflexivity | apply keep5_refl]]].
    destruct (PULLBYTE_free s s' c c' r Ei) as [P1 P2].
    rewrite P1. destruct (PULLBYTE (mkW s c r)) as [u w|w|rc w]; cbn [reput].
    + destruct P2 as (r0 & -> & K0). cbn [w_r]. destruct (IH n s s' c c' r0 Ei) as [Q1 Q2]. split; [exact Q1|].
      destruct (NEEDBITS_k k n (mkW s c r0)) as [u' w'|w'|rc' w'];
        destruct Q2 as (r' & -> & K'); eexists; (split; [reflexivity | exact (keep5_trans _ _ _ K0 K')]).
    + split; [reflexivity | exact P2].
    + split; [reflexivity | exact P2].
Qed.

Lemma NEEDBITS_free : forall n, state_free (NEEDBITS n).
Proof. intros n. unfold NEEDBITS. apply NEEDBITS_k_free. Qed.

Lemma DECODE_k_par : forall k p index need s s' c c' r, ic_input c' = ic_input c ->
  (forall h, code_at s' p (index h) = code_at s p (index h)) ->
  DECODE_k k p index need (mkW s' c' r) = reput s' c' (DECODE_k k p index need (mkW s c r)) /\
  match DECODE_k k p index need (mkW s c r) with
  | ARun here w => exists h r', here = code_at s p (index h) /\ w = mkW s c r' /\ keep5 r r'
  | ALeave w | ARet _ w => exists r', w = mkW s c r' /\ keep5 r r'
  end.
Proof.
  induction k as [|k IH]; intros p index need s s' c c' r Ei E.
  - cbn [DECODE_k]. unfold abind, HOLD, gr, gs, aret. cbn [w_r w_s reput w_c]. rewrite E.
    split; [reflexivity | eexists; eexists; split; [reflexivity | split; [reflexivity | apply keep5_refl]]].
  - cbn [DECODE_k]. unfold abind, HOLD, gr, gs, aret. cbn [w_r w_s]. rewrite E.
    destruct (need (code_at s p (index (ir_hold r))) <=? ir_bits r);
      [cbn [reput w_c w_r]; split; [reflexivity | eexists; eexists; split; [reflexivity | split; [reflexivity | apply keep5_refl]]]|].
    destruct (PULLBYTE_free s s' c c' r Ei) as [P1 P2].
    rewrite P1. destruct (PULLBYTE (mkW s c r)) as [u w|w|rc w]; cbn [reput].
    + destruct P2 as (r0 & -> & K0). cbn [w_r]. destruct (IH p index need s s' c c' r0 Ei E) as [Q1 Q2]. split; [exact Q1|].
      destruct (DECODE_k k p index need (mkW s c r0)) as [h' w'|w'|rc' w'].
      * destruct Q2 as (hq & r' & Hh & -> & K'). eexists; eexists. split; [exact Hh|]. split; [reflexivity | exact (keep5_trans _ _ _ K0 K')].
      * destruct Q2 as (r' & -> & K'). eexists. split; [reflexivity | exact (keep5_trans _ _ _ K0 K')].
      * destruct Q2 as (r' & -> & K'). eexists. split; [reflexivity | exact (keep5_trans _ _ _ K0 K')].
    + split; [reflexivity | exact P2].
    + split; [reflexivity | exact P2].
Qed.


Definition TV (ty : codetype) (codes : arr) (nx : Z) (p : codeptr) (rb : Z) : Prop :=
  match p with
  | CDyn off => exists ext, 0 <= off /\ off + ext <= nx /\ tab_ok ty (cat codes p) rb ext = true
  | _ => 1 <= rb
  end.

Lemma TV_read1 : forall ty codes1 codes2 nx p rb, TV ty codes1 nx p rb ->
  (forall i, 0 <= i < nx -> arr_get codes2 i = arr_get codes1 i) ->
  forall h, cat codes2 p (BITSv h rb) = cat codes1 p (BITSv h rb).
Proof.
  intros ty codes1 codes2 nx [off| |] rb T CO h; cbn [cat]; [| reflexivity | reflexivity].
  destruct T as (ext & Ho & He & T). destruct (tab_ok_root _ _ _ _ T) as (R1 & R2 & _).
  pose proof (BITSv_root h rb ltac:(lia)). apply CO. lia.
Qed.

Lemma root_follow_link : forall ty rd root ext x, tab_ok ty rd root ext = true -> 0 <= x < 2 ^ root ->
  Z.land (code_op (rd x)) 240 = 0 -> (ty = DISTS \/ code_op (rd x) <> 0) ->
  1 <= code_op (rd x) <= 15 - root /\ 0 <= code_val (rd x) /\ code_val (rd x) + 2 ^ code_op (rd x) <= ext.
Proof.
  intros ty rd root ext x T Hx L NZ.
  destruct (tab_root_entry ty rd root ext x T Hx) as (B & R & RE & [[NL TM] | (O1 & O2 & O3 & O4 & _)]).
  - exfalso. pose proof (link_op_lt16 _ L) as L16. apply is_linkop_false in NL.
    pose proof (InflateGarbBase.code_op_bound (rd x)) as OB.
    destruct ty.
    + apply term_ok_CODES in TM. destruct NZ as [X | X]; [discriminate X | lia].
    + apply term_ok_LENS in TM. destruct TM as (_ & [[O _] | [(O & _) | [O _]]]).
      * destruct NZ as [X | X]; [discriminate X | lia].
      * destruct (op_base_tests (code_op (rd x)) ltac:(lia)) as (_ & _ & _ & O240 & _). lia.
      * exact (land64_240 _ O L).
    + apply term_ok_DISTS in TM. destruct TM as (_ & [(O & _) | [O _]]).
      * destruct (op_base_tests (code_op (rd x)) ltac:(lia)) as (_ & _ & _ & O240 & _). lia.
      * exact (land64_240 _ O L).
  - pose proof (Z.pow_pos_nonneg 2 root). lia.
Qed.

Lemma TV_read2 : forall ty codes1 codes2 nx p rb, TV ty codes1 nx p rb ->
  (forall i, 0 <= i < nx -> arr_get codes2 i = arr_get codes1 i) ->
  forall hq, let last := cat codes1 p (BITSv hq rb) in
  Z.land (code_op last) 240 = 0 -> (ty = DISTS \/ code_op last <> 0) ->
  forall h, cat codes2 p (code_val last + Z.shiftr (BITSv h (code_bits last + code_op last)) (code_bits last))
          = cat codes1 p (code_val last + Z.shiftr (BITSv h (code_bits last + code_op last)) (code_bits last)).
Proof.
  intros ty codes1 codes2 nx p rb T CO hq last L NZ h.
  assert (Hrb : 0 <= rb).
  { destruct p as [off| |]; cbn [TV] in T; [| lia | lia]. destruct T as (ext & _ & _ & T). destruct (tab_ok_root _ _ _ _ T) as (R1 & _). lia. }
  pose proof (BITSv_root hq rb Hrb) as Hx.
  destruct p as [off| |]; cbn [cat]; [| reflexivity | reflexivity].
  destruct T as (ext & Ho & He & T).
  destruct (root_follow_link ty _ rb ext (BITSv hq rb) T Hx L NZ) as (Q1 & Q2 & Q3).
  subst last. cbn [cat] in *.
  pose proof (InflateGarbBase.code_bits_bound (arr_get codes1 (off + BITSv hq rb))).
  pose proof (shiftr_BITSv_sub h (code_bits (arr_get codes1 (off + BITSv hq rb))) (code_op (arr_get codes1 (off + BITSv hq rb))) ltac:(lia) ltac:(lia)).
  apply CO. lia.
Qed.

Definition WD (s : inflate_state) : Prop :=
  0 <= is_whave s <= is_wsize s /\ 0 <= is_wnext s <= is_wsize s
  /\ (is_wsize s <> 0 -> is_whave s < is_wsize s -> is_wnext s = is_whave s)
  /\ is_sane s = 1.


