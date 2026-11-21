(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition LIVE_length (m : Z) : bool :=
  (m =? COPY_) || (m =? COPY) || (m =? LENEXT) || (m =? DIST) || (m =? DISTEXT) || (m =? MATCH) || (m =? LIT).
Definition LIVE_offset (m : Z) : bool := (m =? DISTEXT) || (m =? MATCH).
Definition LIVE_extra (m : Z) : bool := (m =? LENEXT) || (m =? DISTEXT).
Definition LIVE_codes (m : Z) : bool :=
  (m =? LEN_) || (m =? LEN) || (m =? LENEXT) || (m =? DIST) || (m =? DISTEXT) || (m =? MATCH) || (m =? LIT).
Definition LIVE_lenbits (m : Z) : bool := (m =? CODELENS) || LIVE_codes m.
Definition LIVE_nlen (m : Z) : bool := (m =? LENLENS) || (m =? CODELENS).

Definition tbl_eq (codes1 codes2 : arr) (ty : codetype) (p : codeptr) (root : Z) : Prop :=
  match p with
  | CDyn o => exists used, TBLg ty (fun x => arr_get codes1 (o + x)) root used
                           /\ forall i, o <= i < o + used -> arr_get codes2 i = arr_get codes1 i
  | _ => True
  end.


Definition IEQ (s1 s2 : inflate_state) : Prop :=
  let m := is_mode s1 in
  (is_mode s2 = is_mode s1 /\ is_last s2 = is_last s1 /\ is_wrap s2 = is_wrap s1 /\ is_havedict s2 = is_havedict s1
   /\ is_flags s2 = is_flags s1 /\ is_dmax s2 = is_dmax s1 /\ is_total s2 = is_total s1 /\ is_head s2 = is_head s1
   /\ is_wbits s2 = is_wbits s1 /\ is_wsize s2 = is_wsize s1 /\ is_whave s2 = is_whave s1 /\ is_wnext s2 = is_wnext s1
   /\ is_window_blk s2 = is_window_blk s1 /\ is_hold s2 = is_hold s1 /\ is_bits s2 = is_bits s1
   /\ is_lencode s2 = is_lencode s1 /\ is_distcode s2 = is_distcode s1 /\ is_next s2 = is_next s1
   /\ is_sane s2 = is_sane s1 /\ is_back s2 = is_back s1 /\ is_self_blk s2 = is_self_blk s1
   /\ arr_len (is_window s2) = arr_len (is_window s1) /\ arr_len (is_lens s2) = arr_len (is_lens s1)
   /\ arr_len (is_work s2) = arr_len (is_work s1) /\ arr_len (is_codes s2) = arr_len (is_codes s1))
  /\ (is_flags s1 = 0 -> is_check s2 = is_check s1)
  /\ (LIVE_length m = true -> is_length s2 = is_length s1)
  /\ (LIVE_offset m = true -> is_offset s2 = is_offset s1)
  /\ (LIVE_extra m = true -> is_extra s2 = is_extra s1)
  /\ (LIVE_lenbits m = true -> is_lenbits s2 = is_lenbits s1)
  /\ (LIVE_codes m = true -> is_distbits s2 = is_distbits s1)
  /\ (m = LENLENS -> is_ncode s2 = is_ncode s1)
  /\ (LIVE_nlen m = true -> is_nlen s2 = is_nlen s1 /\ is_ndist s2 = is_ndist s1 /\ is_have s2 = is_have s1)
  /\ (forall i, 0 <= i < is_whave s1 -> arr_get (is_window s2) i = arr_get (is_window s1) i)
  /\ (m = LENLENS -> forall k, 0 <= k < is_have s1 -> arr_get (is_lens s2) (arr_get order_a k) = arr_get (is_lens s1) (arr_get order_a k))
  /\ (m = CODELENS -> forall i, (0 <= i < 19 \/ 0 <= i < is_have s1) -> arr_get (is_lens s2) i = arr_get (is_lens s1) i)
  /\ (m = CODELENS -> tbl_eq (is_codes s1) (is_codes s2) CODES (is_lencode s1) (is_lenbits s1))
  /\ (LIVE_codes m = true -> tbl_eq (is_codes s1) (is_codes s2) LENS (is_lencode s1) (is_lenbits s1)
                            /\ tbl_eq (is_codes s1) (is_codes s2) DISTS (is_distcode s1) (is_distbits s1)).

Definition gzb (m : Z) : bool :=
  (m =? FLAGS) || (m =? TIME) || (m =? OS) || (m =? EXLEN) || (m =? EXTRA) || (m =? NAME) || (m =? COMMENT) || (m =? HCRC).
Definition UW (s : inflate_state) (c : icall) (r : iregs) : Prop :=
  is_wrap s = 5 /\ gzb (is_mode s) = false /\
  (is_flags s = 0 \/ (is_flags s = -1 /\ (is_mode s = HEAD \/ is_mode s = BAD) /\ ir_put r = 0 /\ ir_out r = arr_len (ic_outbuf c))).

Definition WMID (w1 w2 : iw) : Prop :=
  w_c w2 = w_c w1 /\ w_r w2 = w_r w1 /\ IEQ (w_s w1) (w_s w2) /\ UW (w_s w1) (w_c w1) (w_r w1).

Lemma WMID_mk : forall s1 s2 c r, IEQ s1 s2 -> UW s1 c r -> WMID (mkW s1 c r) (mkW s2 c r).
Proof. intros. split; [reflexivity|]. split; [reflexivity|]. split; assumption. Qed.

Definition RES2 {A} (r1 r2 : ares A) : Prop :=
  match r1, r2 with
  | ARun a w1, ARun b w2 => b = a /\ WMID w1 w2
  | ALeave w1, ALeave w2 => WMID w1 w2
  | ARet x w1, ARet y w2 => y = x /\ WMID w1 w2
  | _, _ => False
  end.


Section Rules.
  Context {A B : Type}.

  Lemma RES2_bind : forall (m1 m2 : AM A) (f1 f2 : A -> AM B) w1 w2,
    RES2 (m1 w1) (m2 w2) ->
    (forall a s1 s2 c r, IEQ s1 s2 -> UW s1 c r -> m1 w1 = ARun a (mkW s1 c r) -> RES2 (f1 a (mkW s1 c r)) (f2 a (mkW s2 c r))) ->
    RES2 (abind m1 f1 w1) (abind m2 f2 w2).
  Proof.
    intros m1 m2 f1 f2 w1 w2 H K. unfold abind.
    destruct (m1 w1) as [a w1'|w1'|x w1'] eqn:E1; destruct (m2 w2) as [b w2'|w2'|y w2']; cbn [RES2] in H; try contradiction.
    - destruct H as [-> H]. destruct w1' as [s1 c1 r1], w2' as [s2 c2 r2].
      destruct H as (Ec & Er & HQ & HU). cbn [w_c w_r w_s] in Ec, Er, HQ, HU. subst c2 r2.
      exact (K a s1 s2 c1 r1 HQ HU eq_refl).
    - exact H.
    - exact H.
  Qed.


  Lemma RES2_ret : forall (a : A) w1 w2, WMID w1 w2 -> RES2 (aret a w1) (aret a w2).
  Proof. intros. split; [reflexivity|assumption]. Qed.
  Lemma RES2_leave : forall w1 w2, WMID w1 w2 -> RES2 (@aleave A w1) (@aleave A w2).
  Proof. intros. exact H. Qed.
  Lemma RES2_return : forall rc w1 w2, WMID w1 w2 -> RES2 (@areturn A rc w1) (@areturn A rc w2).
  Proof. intros. split; [reflexivity|assumption]. Qed.

  Definition SFREE (m : AM A) : Prop :=
    forall s c r,
      match m (mkW s c r) with
      | ARun a w' => exists r', (forall s', m (mkW s' c r) = ARun a (mkW s' c r')) /\ ir_put r' = ir_put r /\ ir_out r' = ir_out r
      | ALeave w' => exists r', (forall s', m (mkW s' c r) = ALeave (mkW s' c r')) /\ ir_put r' = ir_put r /\ ir_out r' = ir_out r
      | ARet x w' => exists r', (forall s', m (mkW s' c r) = ARet x (mkW s' c r')) /\ ir_put r' = ir_put r /\ ir_out r' = ir_out r
      end.

  Lemma UW_regs : forall s c r r', UW s c r -> ir_put r' = ir_put r -> ir_out r' = ir_out r -> UW s c r'.
  Proof. intros s c r r' (W & G & U) Ep Eo. split; [exact W|]. split; [exact G|]. rewrite Ep, Eo. exact U. Qed.

  Lemma RES2_sfree : forall (m : AM A) s1 s2 c r, SFREE m -> IEQ s1 s2 -> UW s1 c r ->
    RES2 (m (mkW s1 c r)) (m (mkW s2 c r)).
  Proof.
    intros m s1 s2 c r SF HQ HU. specialize (SF s1 c r).
    destruct (m (mkW s1 c r)) as [a w'|w'|x w'] eqn:E1;
      destruct SF as (r' & E & Ep & Eo); rewrite (E s1) in E1; rewrite (E s2);
      [injection E1; intros <-; split; [reflexivity|] | injection E1; intros <- | injection E1; intros <-; split; [reflexivity|]];
      (apply WMID_mk; [exact HQ | exact (UW_regs _ _ _ _ HU Ep Eo)]).
  Qed.
End Rules.


Lemma SFREE_gr : forall {A} (f : iregs -> A), SFREE (gr f).
Proof. intros A f s c r. cbn [gr w_r]. exists r. repeat split; reflexivity. Qed.

Lemma SFREE_ur : forall (f : iregs -> iregs), (forall r, ir_put (f r) = ir_put r /\ ir_out (f r) = ir_out r) -> SFREE (ur f).
Proof. intros f Hf s c r. cbn [ur w_r wset_r]. exists (f r). split; [intros; reflexivity|apply Hf]. Qed.
Lemma SFREE_ret : forall {A} (a : A), SFREE (aret a).
Proof. intros A a s c r. cbn [aret]. exists r. repeat split; reflexivity. Qed.
Lemma SFREE_leave : forall {A}, SFREE (@aleave A).
Proof. intros A s c r. cbn [aleave]. exists r. repeat split; reflexivity. Qed.

Lemma SFREE_bind : forall {A B} (m : AM A) (f : A -> AM B), SFREE m -> (forall a, SFREE (f a)) -> SFREE (abind m f).
Proof.
  intros A B m f Hm Hf s c r. unfold abind. specialize (Hm s c r).
  destruct (m (mkW s c r)) as [a w'|w'|x w'] eqn:E1; destruct Hm as (r' & E & Ep & Eo).
  - rewrite (E s) in E1. injection E1; intros <-. specialize (Hf a s c r').
    destruct (f a (mkW s c r')) as [b w''|w''|y w'']; destruct Hf as (r'' & E' & Ep' & Eo');
      exists r''; (split; [intros s'; rewrite (E s'); apply E' | split; congruence]).
  - exists r'. split; [intros s'; rewrite (E s'); reflexivity | split; assumption].
  - exists r'. split; [intros s'; rewrite (E s'); reflexivity | split; assumption].
Qed.

Lemma SFREE_PULLBYTE : SFREE PULLBYTE.
Proof.
  intros s c r. rewrite PULLBYTE_eq. destruct (ir_have r =? 0) eqn:E.
  - exists r. split; [intros s'; rewrite PULLBYTE_eq, E; reflexivity | split; reflexivity].
  - exists (pullr c r). split; [intros s'; rewrite PULLBYTE_eq, E; reflexivity | split; reflexivity].
Qed.

Lemma SFREE_NEEDBITS_k : forall k n, SFREE (NEEDBITS_k k n).
Proof.
  induction k as [|k IH]; intros n; cbn [NEEDBITS_k].
  - apply SFREE_ret.
  - apply SFREE_bind; [apply SFREE_gr|]. intros b. destruct (b <? n); [|apply SFREE_ret].
    apply SFREE_bind; [apply SFREE_PULLBYTE | intros; apply IH].
Qed.
Lemma SFREE_NEEDBITS : forall n, SFREE (NEEDBITS n).
Proof. intros n. unfold NEEDBITS. apply SFREE_NEEDBITS_k. Qed.

Lemma SFREE_BYTEBITS : SFREE BYTEBITS.
Proof. unfold BYTEBITS. apply SFREE_ur. intros; split; reflexivity. Qed.


Ltac live_red_in H :=
  cbv beta iota delta [LIVE_length LIVE_offset LIVE_extra LIVE_codes LIVE_lenbits LIVE_nlen
                       Z.eqb Pos.eqb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in H.
Ltac live_red :=
  cbv beta iota delta [LIVE_length LIVE_offset LIVE_extra LIVE_codes LIVE_lenbits LIVE_nlen
                       Z.eqb Pos.eqb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC].

Ltac cond_use H :=
  lazymatch type of H with
  | true = true -> _ => specialize (H eq_refl)
  | false = true -> _ => clear H
  | ?x = ?x -> _ => specialize (H eq_refl)
  | ?n = ?m -> _ => first [ let TMP := fresh in assert (TMP : n <> m) by discriminate; clear TMP; clear H | idtac ]
  | _ => idtac
  end.

Ltac ieq_open HQ E :=
  unfold IEQ in HQ; cbv zeta in HQ; rewrite ?E in HQ;
  destruct HQ as ((Qmode & Qlast & Qwrap & Qhavedict & Qflags & Qdmax & Qtotal & Qhead & Qwbits & Qwsize & Qwhave & Qwnext
                   & Qwblk & Qhold & Qbits & Qlencode & Qdistcode & Qnext & Qsane & Qback & Qself & QLwin & QLlens & QLwork & QLcodes)
                  & Qcheck & Qlength & Qoffset & Qextra & Qlenbits & Qdistbits & Qncode & Qnlen & Qwin & Qlens1 & Qlens2 & Qctbl & Qtbls);
  live_red_in Qlength; live_red_in Qoffset; live_red_in Qextra; live_red_in Qlenbits; live_red_in Qdistbits;
  live_red_in Qncode; live_red_in Qnlen; live_red_in Qlens1; live_red_in Qlens2; live_red_in Qctbl; live_red_in Qtbls;
  cond_use Qlength; cond_use Qoffset; cond_use Qextra; cond_use Qlenbits; cond_use Qdistbits;
  cond_use Qncode; cond_use Qnlen; cond_use Qlens1; cond_use Qlens2; cond_use Qctbl; cond_use Qtbls;
  try lazymatch type of Qnlen with _ /\ _ => destruct Qnlen as (Qnlen & Qndist & Qhave) end;
  try lazymatch type of Qtbls with _ /\ _ => destruct Qtbls as [QtblL QtblD] end.

Ltac ieq_rw s1 s2 :=
  repeat match goal with
         | Q : ?f s2 = ?f s1 |- context [?f s2] => rewrite !Q
         | Q : arr_len (?f s2) = arr_len (?f s1) |- context [arr_len (?f s2)] => rewrite !Q
         end.

Ltac ieq_leaf :=
  first [ assumption | reflexivity | exact I
        | (intros X; discriminate X)
        | (intros _; repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | exact I | solve [congruence] | idtac])
        | solve [congruence]
        | idtac ].
Ltac ieq_close E :=
  unfold IEQ; cbv zeta; unfold fixedtables; sacc; rewrite ?E; live_red; cbn [tbl_eq];
  repeat match goal with |- _ /\ _ => split end; ieq_leaf.


Lemma UW_notHB : forall s c r, UW s c r -> is_mode s <> HEAD -> is_mode s <> BAD -> is_wrap s = 5 /\ is_flags s = 0.
Proof.
  intros s c r (W & G & [F|(F & [M|M] & _)]) NH NB; [split; assumption| exfalso; exact (NH M) | exfalso; exact (NB M)].
Qed.
Lemma UW_gz : forall s c r, UW s c r -> gzb (is_mode s) = false.
Proof. intros s c r (W & G & _). exact G. Qed.
Lemma UW_intro0 : forall s c r, is_wrap s = 5 -> is_flags s = 0 -> gzb (is_mode s) = false -> UW s c r.
Proof. intros s c r W F G. split; [exact W|]. split; [exact G|left; exact F]. Qed.

Lemma RES2_step2 : forall {A B} (m : AM A) (f : A -> AM B) w1 w2 a1 a2 w1' w2',
  m w1 = ARun a1 w1' -> m w2 = ARun a2 w2' ->
  RES2 (f a1 w1') (f a2 w2') ->
  RES2 (abind m f w1) (abind m f w2).
Proof. intros A B m f w1 w2 a1 a2 w1' w2' E1 E2 H. unfold abind. rewrite E1, E2. exact H. Qed.

Definition arm_cong (M : Z) (F : inflate_state -> icall -> iregs -> Prop) (arm : AM unit) : Prop :=
  forall s1 s2 c r, F s1 c r -> is_mode s1 = M -> IEQ s1 s2 -> UW s1 c r ->
  RES2 (arm (mkW s1 c r)) (arm (mkW s2 c r)).
Definition FTrue (s : inflate_state) (c : icall) (r : iregs) : Prop := True.
Definition FCore (s : inflate_state) (c : icall) (r : iregs) : Prop := CORE s.


Definition LOCK {A} (m : AM A) (s1 s2 : inflate_state) : Prop := forall c r,
  match m (mkW s1 c r) with
  | ARun a w' => exists r', w' = mkW s1 c r' /\ m (mkW s2 c r) = ARun a (mkW s2 c r') /\ ir_put r' = ir_put r /\ ir_out r' = ir_out r
  | ALeave w' => exists r', w' = mkW s1 c r' /\ m (mkW s2 c r) = ALeave (mkW s2 c r') /\ ir_put r' = ir_put r /\ ir_out r' = ir_out r
  | ARet x w' => exists r', w' = mkW s1 c r' /\ m (mkW s2 c r) = ARet x (mkW s2 c r') /\ ir_put r' = ir_put r /\ ir_out r' = ir_out r
  end.

Lemma SFREE_LOCK : forall {A} (m : AM A) s1 s2, SFREE m -> LOCK m s1 s2.
Proof.
  intros A m s1 s2 SF c r. specialize (SF s1 c r).
  destruct (m (mkW s1 c r)) as [a w'|w'|x w'] eqn:E1; destruct SF as (r' & E & Ep & Eo);
    exists r'; rewrite (E s1) in E1; (split; [congruence|]); (split; [apply E|]); split; assumption.
Qed.

Section LockRules.
  Context {A B : Type}.

  Lemma RES2_bind_lock : forall (m : AM A) (f : A -> AM B) s1 s2 c r,
    LOCK m s1 s2 -> IEQ s1 s2 -> UW s1 c r ->
    (forall a r', UW s1 c r' -> m (mkW s1 c r) = ARun a (mkW s1 c r') -> RES2 (f a (mkW s1 c r')) (f a (mkW s2 c r'))) ->
    RES2 (abind m f (mkW s1 c r)) (abind m f (mkW s2 c r)).
  Proof.
    intros m f s1 s2 c r L HQ HU K. unfold abind. specialize (L c r).
    destruct (m (mkW s1 c r)) as [a w'|w'|x w'] eqn:E1; destruct L as (r' & -> & E2 & Ep & Eo); rewrite E2; cbn [RES2].
    - apply K; [exact (UW_regs _ _ _ _ HU Ep Eo) | reflexivity].
    - apply WMID_mk; [exact HQ | exact (UW_regs _ _ _ _ HU Ep Eo)].
    - split; [reflexivity|]. apply WMID_mk; [exact HQ | exact (UW_regs _ _ _ _ HU Ep Eo)].
  Qed.
End LockRules.

Lemma DECODE_k_LOCK : forall k p index need s1 s2,
  (forall h, code_at s2 p (index h) = code_at s1 p (index h)) ->
  LOCK (DECODE_k k p index need) s1 s2.
Proof.
  induction k as [|k IH]; intros p index need s1 s2 HC c r.
  - rewrite !DECODE_k_O. exists r. rewrite (HC _). repeat split; reflexivity.
  - rewrite !DECODE_k_S. rewrite (HC _).
    destruct (need (code_at s1 p (index (ir_hold r))) <=? ir_bits r).
    + exists r. repeat split; reflexivity.
    + destruct (ir_have r =? 0).
      * exists r. repeat split; reflexivity.
      * specialize (IH p index need s1 s2 HC c (pullr c r)).
        destruct (DECODE_k k p index need (mkW s1 c (pullr c r))) as [a w'|w'|x w'];
          destruct IH as (r' & E1 & E2 & Ep & Eo); exists r'; rewrite E2; (split; [exact E1|]); (split; [reflexivity|]);
          rewrite Ep, Eo; unfold pullr; cbn [ir_put ir_out]; split; reflexivity.
Qed.

Lemma DECODE_k_ret : forall k p index need s c r a w',
  DECODE_k k p index need (mkW s c r) = ARun a w' -> exists r', w' = mkW s c r' /\ a = code_at s p (index (ir_hold r')).
Proof.
  induction k as [|k IH]; intros p index need s c r a w' H.
  - rewrite DECODE_k_O in H. injection H; intros <- <-. exists r. split; reflexivity.
  - rewrite DECODE_k_S in H. destruct (need (code_at s p (index (ir_hold r))) <=? ir_bits r).
    + injection H; intros <- <-. exists r. split; reflexivity.
    + destruct (ir_have r =? 0); [discriminate H|]. exact (IH _ _ _ _ _ _ _ _ H).
Qed.

Lemma BITSv_bound : forall h n, 0 <= n < 32 -> 0 <= BITSv h n < 2 ^ n.
Proof.
  intros h n Hn. unfold BITSv. pose proof (wrap32_range h).
  rewrite land_zmask by lia. apply Z.mod_pos_bound. apply pow2_pos. lia.
Qed.

Lemma tbl_eq_DECODE1 : forall s1 s2 ty p root, tbl_eq (is_codes s1) (is_codes s2) ty p root ->
  forall h, code_at s2 p (BITSv h root) = code_at s1 p (BITSv h root).
Proof.
  intros s1 s2 ty p root HT h. destruct p as [o| |]; cbn [code_at]; [|reflexivity|reflexivity].
  cbn [tbl_eq] in HT. destruct HT as (used & HT & HE).
  pose proof (T_root _ _ _ _ HT). pose proof (T_used _ _ _ _ HT). pose proof (BITSv_bound h root ltac:(lia)).
  apply HE. lia.
Qed.

Lemma tbl_eq_DECODE2 : forall s1 s2 ty p root h0, tbl_eq (is_codes s1) (is_codes s2) ty p root ->
  let last := code_at s1 p (BITSv h0 root) in
  match p with CDyn _ => is_linkb last = true | _ => True end ->
  forall h, code_at s2 p (code_val last + Z.shiftr (BITSv h (code_bits last + code_op last)) (code_bits last))
            = code_at s1 p (code_val last + Z.shiftr (BITSv h (code_bits last + code_op last)) (code_bits last)).
Proof.
  intros s1 s2 ty p root h0 HT last HL h. subst last. destruct p as [o| |]; cbn [code_at] in *; [|reflexivity|reflexivity].
  cbn [tbl_eq] in HT. destruct HT as (used & HT & HE).
  pose proof (T_root _ _ _ _ HT). pose proof (BITSv_bound h0 root ltac:(lia)) as X0.
  destruct (root_cell _ _ _ _ HT (BITSv h0 root) X0) as (Hb & RL & _). destruct (RL HL) as (Hbr & Hop & Hv1 & Hv2).
  set (L := arr_get (is_codes s1) (o + BITSv h0 root)) in *.
  pose proof (BITSv_bound h (code_bits L + code_op L) ltac:(lia)) as X1.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= BITSv h (code_bits L + code_op L) / 2 ^ code_bits L < 2 ^ code_op L).
  { split; [apply Z.div_pos; [lia|apply pow2_pos; lia]|].
    apply Z.div_lt_upper_bound; [apply pow2_pos; lia|]. rewrite <- Z.pow_add_r by lia. first [lia | rewrite Z.add_comm; lia]. }
  apply HE. lia.
Qed.

Definition shaped (ty : codetype) (e : Z) : Prop :=
  (exists sy, 0 <= sy < nsyms ty /\ code_op e = fst (sym_entry ty sy) /\ code_val e = snd (sym_entry ty sy)) \/ code_op e = 64.

Lemma dists_two_contra : forall e, shaped DISTS e -> (Z.land (code_op e) 240 =? 0) = true -> False.
Proof.
  intros e SH TW. apply Z.eqb_eq in TW.
  assert (NZ : code_op e <> 0).
  { destruct SH as [[sy (Hsy & Hop & Hv)]|Hop]; [|rewrite Hop; discriminate].
    cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L.
    destruct (sym_entry DISTS sy) as [op v]. cbn [fst snd] in Hop, Hv. rewrite Hop. destruct L as [(L & _)|[L _]]; lia. }
  exact (notlink_land240 DISTS e SH ltac:(discriminate) NZ TW).
Qed.
Lemma lens_two_contra : forall e, shaped LENS e -> (negb (code_op e =? 0) && (Z.land (code_op e) 240 =? 0)) = true -> False.
Proof.
  intros e SH TW. apply andb_prop in TW as [T1 T2].
  apply Bool.negb_true_iff in T1. apply Z.eqb_neq in T1. apply Z.eqb_eq in T2.
  exact (notlink_land240 LENS e SH ltac:(discriminate) T1 T2).
Qed.

Lemma tbl_eq_link : forall s1 s2 ty p root h0 (P : Z -> bool),
  tbl_eq (is_codes s1) (is_codes s2) ty p root ->
  (forall e, shaped ty e -> P (code_op e) = true -> False) ->
  let last := code_at s1 p (BITSv h0 root) in
  P (code_op last) = true ->
  match p with CDyn _ => is_linkb last = true | _ => True end.
Proof.
  intros s1 s2 ty p root h0 P HT Hc last HP. subst last. destruct p as [o| |]; [|exact I|exact I].
  cbn [tbl_eq] in HT. destruct HT as (used & HT & HE). cbn [code_at] in *.
  pose proof (T_root _ _ _ _ HT). pose proof (BITSv_bound h0 root ltac:(lia)) as X0.
  destruct (root_cell _ _ _ _ HT (BITSv h0 root) X0) as (Hb & RL & RN).
  destruct (is_linkb (arr_get (is_codes s1) (o + BITSv h0 root))) eqn:HL; [reflexivity|].
  exfalso. destruct (RN eq_refl) as [_ SH]. exact (Hc _ SH HP).
Qed.

Lemma IEQ_set_back : forall s1 s2 v, IEQ s1 s2 -> IEQ (iset_back s1 v) (iset_back s2 v).
Proof.
  intros s1 s2 v H. unfold IEQ in *; cbv zeta in *. sacc.
  destruct H as [A B]. split; [|exact B].
  decompose [and] A. repeat split; first [assumption | reflexivity].
Qed.
