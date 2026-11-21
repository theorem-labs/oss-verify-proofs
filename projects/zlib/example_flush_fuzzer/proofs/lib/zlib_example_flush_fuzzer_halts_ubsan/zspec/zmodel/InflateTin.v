(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb InflateRc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope am_scope.

Definition tinw (w : iw) : Z := ic_total_in (w_c w).

(* zlib 1.4 (smodel14-r1's DICT row): a direct return may move total_in (DICT adds in - avail_in before Z_NEED_DICT),
   so kS no longer constrains an ARet; a run or a leave still keeps total_in *)
Definition kS {A} (m : AM A) : Prop :=
  forall w, match m w with ARun _ w' => tinw w' = tinw w | ALeave w' => tinw w' = tinw w | ARet _ w' => True end.

Lemma kS_bind : forall {A B} (m : AM A) (f : A -> AM B), kS m -> (forall a, kS (f a)) -> kS (abind m f).
Proof.
  intros A B m f Hm Hf w. unfold abind. specialize (Hm w). destruct (m w) as [a w'|w'|rc w']; [| exact Hm | exact Hm].
  specialize (Hf a w'). destruct (f a w'); try exact I; congruence.
Qed.
Lemma kS_if : forall {A} (b : bool) (m1 m2 : AM A), kS m1 -> kS m2 -> kS (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
Lemma kS_aret : forall {A} (a : A), kS (aret a). Proof. intros A a w; reflexivity. Qed.
Lemma kS_gs : forall {A} (f : inflate_state -> A), kS (gs f). Proof. intros A f w; reflexivity. Qed.
Lemma kS_gc : forall {A} (f : icall -> A), kS (gc f). Proof. intros A f w; reflexivity. Qed.
Lemma kS_gr : forall {A} (f : iregs -> A), kS (gr f). Proof. intros A f w; reflexivity. Qed.
Lemma kS_agets : forall {A} (f : iw -> A), kS (agets f). Proof. intros A f w; reflexivity. Qed.
Lemma kS_us : forall f, kS (us f). Proof. intros f w; reflexivity. Qed.
Lemma kS_ur : forall f, kS (ur f). Proof. intros f w; reflexivity. Qed.
Lemma kS_uc : forall f, (forall c, ic_total_in (f c) = ic_total_in c) -> kS (uc f).
Proof. intros f H w. unfold uc, tinw. cbn. apply H. Qed.
Lemma kS_amodify : forall F, (forall w, tinw (F w) = tinw w) -> kS (amodify F).
Proof. intros F H w. unfold amodify. cbn. apply H. Qed.
Lemma kS_aleave : forall {A}, kS (@aleave A). Proof. intros A w; reflexivity. Qed.
Lemma kS_areturn : forall {A} rc, kS (@areturn A rc). Proof. intros A rc w; exact I. Qed.
Lemma kS_PULLBYTE : kS PULLBYTE.
Proof. intros w. unfold PULLBYTE. destruct (ir_have (w_r w) =? 0); reflexivity. Qed.
Lemma kS_NEEDBITS_k : forall k n, kS (NEEDBITS_k k n).
Proof.
  induction k as [|k IH]; intros n; cbn [NEEDBITS_k]; [apply kS_aret|].
  apply kS_bind; [apply kS_gr|]. intros b. apply kS_if; [| apply kS_aret].
  apply kS_bind; [apply kS_PULLBYTE | intros ?; apply IH].
Qed.
Lemma kS_NEEDBITS : forall n, kS (NEEDBITS n). Proof. intros n. apply kS_NEEDBITS_k. Qed.
Lemma kS_BITS : forall n, kS (BITS n). Proof. intros n. apply kS_gr. Qed.
Lemma kS_HOLD : kS HOLD. Proof. apply kS_gr. Qed.
Lemma kS_DROPBITS : forall n, kS (DROPBITS n). Proof. intros n. apply kS_ur. Qed.
Lemma kS_INITBITS : kS INITBITS. Proof. apply kS_ur. Qed.
Lemma kS_BYTEBITS : kS BYTEBITS. Proof. apply kS_ur. Qed.
Lemma kS_set_mode : forall m, kS (set_mode m). Proof. intros m. apply kS_us. Qed.
Lemma kS_set_msg : forall m, kS (set_msg m). Proof. intros m. apply kS_uc. intros []; reflexivity. Qed.
Lemma kS_go_bad : forall m, kS (go_bad m).
Proof. intros m. unfold go_bad. apply kS_bind; [apply kS_set_msg | intros ?; apply kS_set_mode]. Qed.
Lemma kS_set_adler_check : forall v, kS (set_adler_check v).
Proof. intros v. unfold set_adler_check. apply kS_bind; [apply kS_us | intros ?; apply kS_uc; intros []; reflexivity]. Qed.
Lemma kS_DECODE_k : forall k p index need, kS (DECODE_k k p index need).
Proof.
  induction k as [|k IH]; intros p index need; cbn [DECODE_k].
  - apply kS_bind; [apply kS_HOLD | intros h; apply kS_gs].
  - apply kS_bind; [apply kS_HOLD | intros h]. apply kS_bind; [apply kS_gr | intros b]. apply kS_bind; [apply kS_gs | intros here].
    apply kS_if; [apply kS_aret|]. apply kS_bind; [apply kS_PULLBYTE | intros ?; apply IH].
Qed.
Lemma kS_DECODE1 : forall p n, kS (DECODE1 p n). Proof. intros. apply kS_DECODE_k. Qed.
Lemma kS_DECODE2 : forall p l, kS (DECODE2 p l). Proof. intros. apply kS_DECODE_k. Qed.
Lemma kS_crc_input : forall copy, kS (crc_input copy). Proof. intros copy w; reflexivity. Qed.
Lemma kS_CRC2 : forall v, kS (CRC2 v). Proof. intros v. apply kS_us. Qed.
Lemma kS_CRC4 : forall v, kS (CRC4 v). Proof. intros v. apply kS_us. Qed.
Lemma kS_match_copy_step : forall from copy,
  kS (fun w => let '(ob, put, _, _) := match_copy (is_window (w_s w)) (ic_outbuf (w_c w), ir_put (w_r w), from, copy) in
               ARun tt (wset_r (wset_c w (icset_outbuf (w_c w) ob)) (irset_put (w_r w) put))).
Proof.
  intros from copy w. cbv beta. destruct (match_copy _ _) as [[[ob put] x3] x4]. unfold tinw. cbn. destruct (w_c w); reflexivity.
Qed.

Lemma inflate_fast_tin : forall w, ic_total_in (w_c (inflate_fast w)) = ic_total_in (w_c w).
Proof.
  intros w. unfold inflate_fast.
  match goal with |- context [iterZ ?n ?st ?df ?f0] => destruct (iterZ n st df f0) as [f mm] end.
  destruct mm as [[mode [msg|]]|]; destruct (w_c w); reflexivity.
Qed.
Lemma RESTORE_tin : forall w, tinw (RESTORE w) = tinw w.
Proof. intros [s c r]. unfold tinw, RESTORE. cbn. destruct c; reflexivity. Qed.
Lemma LOAD_c : forall w, w_c (LOAD w) = w_c w.
Proof. intros [s c r]; reflexivity. Qed.

Create HintDb kdb discriminated.
#[export] Hint Resolve kS_aret kS_gs kS_gc kS_gr kS_agets kS_us kS_ur kS_aleave kS_areturn kS_PULLBYTE kS_NEEDBITS_k kS_NEEDBITS
  kS_BITS kS_HOLD kS_DROPBITS kS_INITBITS kS_BYTEBITS kS_set_mode kS_set_msg kS_go_bad kS_set_adler_check
  kS_DECODE_k kS_DECODE1 kS_DECODE2 kS_crc_input kS_CRC2 kS_CRC4 kS_match_copy_step : kdb.

Ltac k1 :=
  lazymatch goal with
  | |- kS (abind _ _) => apply kS_bind; [ | intros ? ]
  | |- kS (if _ then _ else _) => apply kS_if
  | |- kS (match ?x with _ => _ end) => destruct x
  | |- kS (uc _) => apply kS_uc; intros []; reflexivity
  | |- kS (amodify _) => apply kS_amodify; let w := fresh "w" in intros w; unfold tinw; rewrite ?LOAD_c, ?inflate_fast_tin;
                           first [reflexivity | apply (RESTORE_tin w)]
  | |- kS _ => solve [auto 2 with kdb nocore]
  end.
Ltac kcrush := repeat k1.

Section Arms.
  Variable iv : ivariant.
  Variable flush : Z.

  Lemma kS_aux : forall f, kS (aux iv f).
  Proof. intros f. unfold aux. destruct (iv_aux iv); [apply kS_us | apply kS_aret]. Qed.
  Lemma kS_set_back : forall v, kS (set_back iv v). Proof. intros v. apply kS_aux. Qed.
  Lemma kS_add_back : forall v, kS (add_back iv v). Proof. intros v. apply kS_aux. Qed.
  Hint Resolve kS_aux kS_set_back kS_add_back : kdb.

  Lemma k_DONE : kS (arm_DONE).
  Proof. unfold arm_DONE. kcrush. Qed.
  Hint Resolve k_DONE : kdb.
  Lemma k_LENGTH : kS (arm_LENGTH).
  Proof. unfold arm_LENGTH. kcrush. Qed.
  Hint Resolve k_LENGTH : kdb.
  Lemma k_CHECK : kS (arm_CHECK).
  Proof. unfold arm_CHECK. kcrush. Qed.
  Hint Resolve k_CHECK : kdb.
  Lemma k_LIT : kS (arm_LIT).
  Proof. unfold arm_LIT. kcrush. Qed.
  Hint Resolve k_LIT : kdb.
  Lemma k_MATCH : kS (arm_MATCH iv).
  Proof. unfold arm_MATCH. kcrush. Qed.
  Hint Resolve k_MATCH : kdb.
  Lemma k_DISTEXT : kS (arm_DISTEXT iv).
  Proof. unfold arm_DISTEXT. kcrush. Qed.
  Hint Resolve k_DISTEXT : kdb.
  Lemma k_DIST : kS (arm_DIST iv).
  Proof. unfold arm_DIST. kcrush. Qed.
  Hint Resolve k_DIST : kdb.
  Lemma k_LENEXT : kS (arm_LENEXT iv).
  Proof. unfold arm_LENEXT. kcrush. Qed.
  Hint Resolve k_LENEXT : kdb.
  Lemma k_LEN : kS (arm_LEN iv).
  Proof. unfold arm_LEN. kcrush. Qed.
  Hint Resolve k_LEN : kdb.
  Lemma k_LEN_ : kS (arm_LEN_ iv).
  Proof. unfold arm_LEN_. kcrush. Qed.
  Hint Resolve k_LEN_ : kdb.
  Lemma k_set_lens : forall i v, kS (set_lens i v).
  Proof. intros. unfold set_lens. apply kS_us. Qed.
  Hint Resolve k_set_lens : kdb.
  Lemma k_lens_repeat : forall c l, kS (lens_repeat c l).
  Proof. intros. unfold lens_repeat. apply kS_us. Qed.
  Hint Resolve k_lens_repeat : kdb.
  Lemma k_codelens_body : kS codelens_body.
  Proof. unfold codelens_body. kcrush. Qed.
  Hint Resolve k_codelens_body : kdb.
  Lemma k_codelens_while : forall k, kS (codelens_while k).
  Proof. induction k as [|k IH]; cbn [codelens_while]; kcrush. Qed.
  Hint Resolve k_codelens_while : kdb.
  Lemma k_CODELENS : kS (arm_CODELENS iv flush).
  Proof. unfold arm_CODELENS. kcrush. Qed.
  Hint Resolve k_CODELENS : kdb.
  Lemma k_lenlens_while1 : forall k, kS (lenlens_while1 k).
  Proof. induction k as [|k IH]; cbn [lenlens_while1]; kcrush. Qed.
  Hint Resolve k_lenlens_while1 : kdb.
  Lemma k_lenlens_while2 : forall k, kS (lenlens_while2 k).
  Proof. induction k as [|k IH]; cbn [lenlens_while2]; kcrush. Qed.
  Hint Resolve k_lenlens_while2 : kdb.
  Lemma k_LENLENS : kS (arm_LENLENS iv flush).
  Proof. unfold arm_LENLENS. kcrush. Qed.
  Hint Resolve k_LENLENS : kdb.
  Lemma k_TABLE : kS (arm_TABLE iv flush).
  Proof. unfold arm_TABLE. kcrush. Qed.
  Hint Resolve k_TABLE : kdb.
  Lemma k_COPY : kS (arm_COPY).
  Proof. unfold arm_COPY. kcrush. Qed.
  Hint Resolve k_COPY : kdb.
  Lemma k_COPY_ : kS (arm_COPY_).
  Proof. unfold arm_COPY_. kcrush. Qed.
  Hint Resolve k_COPY_ : kdb.
  Lemma k_STORED : kS (arm_STORED iv flush).
  Proof. unfold arm_STORED. kcrush. Qed.
  Hint Resolve k_STORED : kdb.
  Lemma k_TYPEDO : kS (arm_TYPEDO iv flush).
  Proof. unfold arm_TYPEDO. kcrush. Qed.
  Hint Resolve k_TYPEDO : kdb.
  Lemma k_TYPE : kS (arm_TYPE iv flush).
  Proof. unfold arm_TYPE. kcrush. Qed.
  Hint Resolve k_TYPE : kdb.
  (* 1.4: the need-dict return moves total_in, which kS allows on an ARet *)
  Lemma k_DICT : kS (arm_DICT iv flush).
  Proof.
    unfold arm_DICT. apply kS_bind; [apply kS_gs | intros s]. destruct (is_havedict s =? 0).
    - intros w. cbv [abind amodify gr uc areturn]. exact I.
    - kcrush.
  Qed.
  Hint Resolve k_DICT : kdb.
  Lemma k_DICTID : kS (arm_DICTID iv flush).
  Proof. unfold arm_DICTID. kcrush. Qed.
  Hint Resolve k_DICTID : kdb.
  Lemma k_HCRC : kS (arm_HCRC).
  Proof. unfold arm_HCRC. kcrush. Qed.
  Hint Resolve k_HCRC : kdb.
  Lemma k_name_like : forall f, kS (name_like f).
  Proof. intros f. unfold name_like. kcrush. Qed.
  Hint Resolve k_name_like : kdb.
  Lemma k_COMMENT : kS (arm_COMMENT).
  Proof. unfold arm_COMMENT. kcrush. Qed.
  Hint Resolve k_COMMENT : kdb.
  Lemma k_NAME : kS (arm_NAME).
  Proof. unfold arm_NAME. kcrush. Qed.
  Hint Resolve k_NAME : kdb.
  Lemma k_EXTRA : kS (arm_EXTRA).
  Proof. unfold arm_EXTRA. kcrush. Qed.
  Hint Resolve k_EXTRA : kdb.
  Lemma k_EXLEN : kS (arm_EXLEN).
  Proof. unfold arm_EXLEN. kcrush. Qed.
  Hint Resolve k_EXLEN : kdb.
  Lemma k_OS : kS (arm_OS).
  Proof. unfold arm_OS. kcrush. Qed.
  Hint Resolve k_OS : kdb.
  Lemma k_TIME : kS (arm_TIME).
  Proof. unfold arm_TIME. kcrush. Qed.
  Hint Resolve k_TIME : kdb.
  Lemma k_FLAGS : kS (arm_FLAGS).
  Proof. unfold arm_FLAGS. kcrush. Qed.
  Hint Resolve k_FLAGS : kdb.
  Lemma k_HEAD : kS (arm_HEAD iv).
  Proof. unfold arm_HEAD. kcrush. Qed.
  Hint Resolve k_HEAD : kdb.
  Lemma k_BAD : kS (arm_BAD).
  Proof. unfold arm_BAD. kcrush. Qed.
  Hint Resolve k_BAD : kdb.
  Lemma k_MEM : kS (arm_MEM).
  Proof. unfold arm_MEM. kcrush. Qed.
  Hint Resolve k_MEM : kdb.
  Lemma k_SYNC : kS (arm_SYNC).
  Proof. unfold arm_SYNC. kcrush. Qed.
  Hint Resolve k_SYNC : kdb.

  Lemma k_dispatch : kS (dispatch iv flush).
  Proof. unfold dispatch. kcrush. Qed.

  (* 1.4: a stop by a direct return (SRet) may move total_in; a leave keeps it *)
  Lemma iterK_tin : forall n w,
    match iterK_nat n (gstep iv flush) w with
    | inl w' => tinw w' = tinw w
    | inr (st, w') => match st with SRet _ => True | _ => tinw w' = tinw w end
    end.
  Proof.
    induction n as [|n IH]; intros w; [reflexivity|].
    rewrite (iterK_gstep_S iv flush). pose proof (k_dispatch w) as K.
    destruct (dispatch iv flush w) as [u w'|w'|rc w']; [| exact K | exact K].
    specialize (IH w'). destruct (iterK_nat n (gstep iv flush) w') as [w2|[st w2]]; [congruence|].
    destruct st; cbv iota in IH |- *; [congruence | exact I].
  Qed.

  Theorem inf_loop_tin : forall w,
    match fst (inf_loop iv flush w) with SRet _ => True | _ => tinw (snd (inf_loop iv flush w)) = tinw w end.
  Proof.
    intros w. rewrite (inf_loop_iter iv flush). pose proof (iterK_tin (Z.to_nat (gfuel w)) w) as X.
    destruct (iterK_nat _ _ w) as [w'|[st w']]; exact X.
  Qed.
End Arms.
