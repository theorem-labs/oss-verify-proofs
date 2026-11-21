(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb ModelRel
  InflateInv InflateInvRun InflateInvTab InflateInvKit InflateInvApi InflateInvLoop.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope am_scope.

Unset Lia Cache.

Definition RL (rc : Z) : Prop := rc = Z_OK \/ rc = Z_STREAM_END \/ rc = Z_DATA_ERROR.
Definition RR (rc : Z) : Prop := rc = Z_NEED_DICT \/ rc = Z_MEM_ERROR \/ rc = Z_STREAM_ERROR.
Definition retw (w : iw) : Z := ir_ret (w_r w).

Definition okS {A} (m : AM A) : Prop :=
  forall w, retw w = Z_OK ->
  match m w with ARun _ w' => retw w' = Z_OK | ALeave w' => RL (retw w') | ARet rc _ => RR rc end.
Definition okA {A} (m : AM A) : Prop :=
  forall w, retw w = Z_OK ->
  match m w with ARun _ w' => retw w' = Z_OK \/ is_mode (w_s w') = BAD | ALeave w' => RL (retw w') | ARet rc _ => RR rc end.

Lemma okA_of_okS : forall {A} (m : AM A), okS m -> okA m.
Proof. intros A m H w R. specialize (H w R). destruct (m w); [left; exact H | exact H | exact H]. Qed.


Lemma okS_bind : forall {A B} (m : AM A) (f : A -> AM B), okS m -> (forall a, okS (f a)) -> okS (abind m f).
Proof.
  intros A B m f Hm Hf w R. unfold abind. specialize (Hm w R). destruct (m w) as [a w'|w'|rc w']; [exact (Hf a w' Hm) | exact Hm | exact Hm].
Qed.
Lemma okA_bind : forall {A B} (m : AM A) (f : A -> AM B), okS m -> (forall a, okA (f a)) -> okA (abind m f).
Proof.
  intros A B m f Hm Hf w R. unfold abind. specialize (Hm w R). destruct (m w) as [a w'|w'|rc w']; [exact (Hf a w' Hm) | exact Hm | exact Hm].
Qed.
Lemma okS_if : forall {A} (b : bool) (m1 m2 : AM A), okS m1 -> okS m2 -> okS (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
Lemma okA_if : forall {A} (b : bool) (m1 m2 : AM A), okA m1 -> okA m2 -> okA (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.


Lemma okS_aret : forall {A} (a : A), okS (aret a).
Proof. intros A a w R. exact R. Qed.
Lemma okS_gs : forall {A} (f : inflate_state -> A), okS (gs f).
Proof. intros A f w R. exact R. Qed.
Lemma okS_gc : forall {A} (f : icall -> A), okS (gc f).
Proof. intros A f w R. exact R. Qed.
Lemma okS_gr : forall {A} (f : iregs -> A), okS (gr f).
Proof. intros A f w R. exact R. Qed.
Lemma okS_agets : forall {A} (f : iw -> A), okS (agets f).
Proof. intros A f w R. exact R. Qed.
Lemma okS_us : forall f, okS (us f).
Proof. intros f w R. exact R. Qed.
Lemma okS_uc : forall f, okS (uc f).
Proof. intros f w R. exact R. Qed.
Lemma okS_ur : forall f, (forall r, ir_ret (f r) = ir_ret r) -> okS (ur f).
Proof. intros f H w R. unfold ur, retw in *. cbn. rewrite H. exact R. Qed.
Lemma okS_amodify : forall F, (forall w, retw (F w) = retw w) -> okS (amodify F).
Proof. intros F H w R. unfold amodify. cbn. rewrite H. exact R. Qed.
Lemma okS_aleave : forall {A}, okS (@aleave A).
Proof. intros A w R. unfold aleave. left. exact R. Qed.
Lemma okS_areturn : forall {A} rc, RR rc -> okS (@areturn A rc).
Proof. intros A rc H w R. exact H. Qed.

Lemma okS_PULLBYTE : okS PULLBYTE.
Proof. intros w R. unfold PULLBYTE. destruct (ir_have (w_r w) =? 0); [left; exact R | exact R]. Qed.
Lemma okS_NEEDBITS_k : forall k n, okS (NEEDBITS_k k n).
Proof.
  induction k as [|k IH]; intros n; cbn [NEEDBITS_k]; [apply okS_aret|].
  apply okS_bind; [apply okS_gr|]. intros b. apply okS_if; [| apply okS_aret].
  apply okS_bind; [apply okS_PULLBYTE | intros _; apply IH].
Qed.
Lemma okS_NEEDBITS : forall n, okS (NEEDBITS n).
Proof. intros n. apply okS_NEEDBITS_k. Qed.
Lemma okS_BITS : forall n, okS (BITS n).
Proof. intros n. apply okS_gr. Qed.
Lemma okS_HOLD : okS HOLD.
Proof. apply okS_gr. Qed.
Lemma okS_DROPBITS : forall n, okS (DROPBITS n).
Proof. intros n. apply okS_ur. intros r; reflexivity. Qed.
Lemma okS_INITBITS : okS INITBITS.
Proof. apply okS_ur. intros r; reflexivity. Qed.
Lemma okS_BYTEBITS : okS BYTEBITS.
Proof. apply okS_ur. intros r; reflexivity. Qed.
Lemma okS_set_mode : forall m, okS (set_mode m).
Proof. intros m. apply okS_us. Qed.
Lemma okS_set_msg : forall m, okS (set_msg m).
Proof. intros m. apply okS_uc. Qed.
Lemma okS_go_bad : forall m, okS (go_bad m).
Proof. intros m. unfold go_bad. apply okS_bind; [apply okS_set_msg | intros _; apply okS_set_mode]. Qed.
Lemma okS_set_adler_check : forall v, okS (set_adler_check v).
Proof. intros v. unfold set_adler_check. apply okS_bind; [apply okS_us | intros _; apply okS_uc]. Qed.
Lemma okS_DECODE_k : forall k p index need, okS (DECODE_k k p index need).
Proof.
  induction k as [|k IH]; intros p index need; cbn [DECODE_k].
  - apply okS_bind; [apply okS_HOLD | intros h; apply okS_gs].
  - apply okS_bind; [apply okS_HOLD | intros h]. apply okS_bind; [apply okS_gr | intros b]. apply okS_bind; [apply okS_gs | intros here].
    apply okS_if; [apply okS_aret|]. apply okS_bind; [apply okS_PULLBYTE | intros _; apply IH].
Qed.
Lemma okS_DECODE1 : forall p n, okS (DECODE1 p n).
Proof. intros. apply okS_DECODE_k. Qed.
Lemma okS_DECODE2 : forall p l, okS (DECODE2 p l).
Proof. intros. apply okS_DECODE_k. Qed.
Lemma okS_crc_input : forall copy, okS (crc_input copy).
Proof. intros copy w R. exact R. Qed.
Lemma okS_CRC2 : forall v, okS (CRC2 v).
Proof. intros v. apply okS_us. Qed.
Lemma okS_CRC4 : forall v, okS (CRC4 v).
Proof. intros v. apply okS_us. Qed.

Lemma okS_set_ret_leave : forall {A} rc, RL rc -> okS (ur (fun r => irset_ret r rc) ;; @aleave A).
Proof. intros A rc H w R. unfold abind, ur, aleave, retw. cbn. destruct (w_r w); cbn. exact H. Qed.

Lemma okA_table : forall ret msg (k : AM unit),
  (ret = 0 -> okA k) -> okA (ur (fun r => irset_ret r ret) ;; if negb (ret =? 0) then go_bad msg else k).
Proof.
  intros ret msg k Hk w R. unfold abind at 1. unfold ur. cbn.
  destruct (Z.eqb_spec ret 0) as [E|E]; cbn [negb].
  - apply (Hk E). unfold retw. cbn. destruct (w_r w); cbn. rewrite E. reflexivity.
  - unfold go_bad, abind, set_msg, set_mode, uc, us. cbn. right. destruct (w_s w); reflexivity.
Qed.

Lemma inflate_fast_r : forall w, w_r (inflate_fast w) = w_r w.
Proof.
  intros w. unfold inflate_fast.
  match goal with |- context [iterZ ?n ?st ?df ?f0] => destruct (iterZ n st df f0) as [f mm] end.
  destruct mm as [[mode [msg|]]|]; reflexivity.
Qed.

Lemma okS_match_copy_step : forall from copy,
  okS (fun w => let '(ob, put, _, _) := match_copy (is_window (w_s w)) (ic_outbuf (w_c w), ir_put (w_r w), from, copy) in
                ARun tt (wset_r (wset_c w (icset_outbuf (w_c w) ob)) (irset_put (w_r w) put))).
Proof.
  intros from copy w R. cbv beta. destruct (match_copy _ _) as [[[ob put] x3] x4]. unfold retw in *. cbn. destruct (w_r w); cbn in *. exact R.
Qed.


Create HintDb okdb discriminated.
#[export] Hint Resolve okS_aret okS_gs okS_gc okS_gr okS_agets okS_us okS_uc okS_aleave okS_PULLBYTE okS_NEEDBITS_k okS_NEEDBITS
  okS_BITS okS_HOLD okS_DROPBITS okS_INITBITS okS_BYTEBITS okS_set_mode okS_set_msg okS_go_bad okS_set_adler_check
  okS_DECODE_k okS_DECODE1 okS_DECODE2 okS_crc_input okS_CRC2 okS_CRC4 okS_match_copy_step : okdb.

Ltac ok1 :=
  lazymatch goal with
  | |- okA (abind (ur (fun r => irset_ret r ?ret)) (fun _ => if negb (?ret =? 0) then go_bad _ else _)) =>
      apply okA_table; intros ?
  | |- okS (abind (ur (fun r => irset_ret r ?rc)) (fun _ => aleave)) => apply okS_set_ret_leave; unfold RL; auto
  | |- okA (abind (ur (fun r => irset_ret r ?rc)) (fun _ => aleave)) => apply okA_of_okS; apply okS_set_ret_leave; unfold RL; auto
  | |- okS (abind _ _) => apply okS_bind; [ | intros ? ]
  | |- okA (abind _ _) => apply okA_bind; [ | intros ? ]
  | |- okS (if _ then _ else _) => apply okS_if
  | |- okA (if _ then _ else _) => apply okA_if
  | |- okS (match ?x with _ => _ end) => destruct x
  | |- okA (match ?x with _ => _ end) => destruct x
  | |- okS (ur _) => apply okS_ur; intros ?; reflexivity
  | |- okS (amodify _) => apply okS_amodify; intros ?; unfold retw; cbn -[inflate_fast]; rewrite ?inflate_fast_r; cbn; reflexivity
  | |- okS (areturn _) => apply okS_areturn; unfold RR; auto
  | |- okA (areturn _) => apply okA_of_okS; apply okS_areturn; unfold RR; auto
  | |- okS _ => solve [auto 2 with okdb nocore]
  | |- okA _ => first [solve [auto 2 with okdb nocore] | solve [apply okA_of_okS; auto 2 with okdb nocore] | apply okA_of_okS]
  end.
Ltac okcrush := repeat ok1.


Section Arms.
  Variable iv : ivariant.
  Variable flush : Z.

  Lemma okS_aux : forall f, okS (aux iv f).
  Proof. intros f. unfold aux. destruct (iv_aux iv); [apply okS_us | apply okS_aret]. Qed.
  Lemma okS_set_back : forall v, okS (set_back iv v).
  Proof. intros v. apply okS_aux. Qed.
  Lemma okS_add_back : forall v, okS (add_back iv v).
  Proof. intros v. apply okS_aux. Qed.
  Hint Resolve okS_aux okS_set_back okS_add_back : okdb.

  Lemma ok_DONE : okA (arm_DONE).
  Proof. unfold arm_DONE. okcrush. Qed.
  Hint Resolve ok_DONE : okdb.
  Lemma ok_LENGTH : okA (arm_LENGTH).
  Proof. unfold arm_LENGTH. okcrush. Qed.
  Hint Resolve ok_LENGTH : okdb.
  Lemma ok_CHECK : okA (arm_CHECK).
  Proof. unfold arm_CHECK. okcrush. Qed.
  Hint Resolve ok_CHECK : okdb.
  Lemma ok_LIT : okA (arm_LIT).
  Proof. unfold arm_LIT. okcrush. Qed.
  Hint Resolve ok_LIT : okdb.
  Lemma ok_MATCH : okA (arm_MATCH iv).
  Proof. unfold arm_MATCH. okcrush. Qed.
  Hint Resolve ok_MATCH : okdb.
  Lemma ok_DISTEXT : okA (arm_DISTEXT iv).
  Proof. unfold arm_DISTEXT. okcrush. Qed.
  Hint Resolve ok_DISTEXT : okdb.
  Lemma ok_DIST : okA (arm_DIST iv).
  Proof. unfold arm_DIST. okcrush. Qed.
  Hint Resolve ok_DIST : okdb.
  Lemma ok_LENEXT : okA (arm_LENEXT iv).
  Proof. unfold arm_LENEXT. okcrush. Qed.
  Hint Resolve ok_LENEXT : okdb.
  Lemma ok_LEN : okA (arm_LEN iv).
  Proof. unfold arm_LEN. okcrush. Qed.
  Hint Resolve ok_LEN : okdb.
  Lemma ok_LEN_ : okA (arm_LEN_ iv).
  Proof. unfold arm_LEN_. okcrush. Qed.
  Hint Resolve ok_LEN_ : okdb.
  Lemma ok_set_lens : forall i v, okS (set_lens i v).
  Proof. intros. unfold set_lens. apply okS_us. Qed.
  Hint Resolve ok_set_lens : okdb.
  Lemma ok_lens_repeat : forall c l, okS (lens_repeat c l).
  Proof. intros. unfold lens_repeat. apply okS_us. Qed.
  Hint Resolve ok_lens_repeat : okdb.
  Lemma ok_codelens_body : okS codelens_body.
  Proof. unfold codelens_body. okcrush. Qed.
  Hint Resolve ok_codelens_body : okdb.
  Lemma ok_codelens_while : forall k, okS (codelens_while k).
  Proof. induction k as [|k IH]; cbn [codelens_while]; okcrush. Qed.
  Hint Resolve ok_codelens_while : okdb.
  Lemma ok_CODELENS : okA (arm_CODELENS iv flush).
  Proof. unfold arm_CODELENS. okcrush. Qed.
  Hint Resolve ok_CODELENS : okdb.
  Lemma ok_lenlens_while1 : forall k, okS (lenlens_while1 k).
  Proof. induction k as [|k IH]; cbn [lenlens_while1]; okcrush. Qed.
  Hint Resolve ok_lenlens_while1 : okdb.
  Lemma ok_lenlens_while2 : forall k, okS (lenlens_while2 k).
  Proof. induction k as [|k IH]; cbn [lenlens_while2]; okcrush. Qed.
  Hint Resolve ok_lenlens_while2 : okdb.
  Lemma ok_LENLENS : okA (arm_LENLENS iv flush).
  Proof. unfold arm_LENLENS. okcrush. Qed.
  Hint Resolve ok_LENLENS : okdb.
  Lemma ok_TABLE : okA (arm_TABLE iv flush).
  Proof. unfold arm_TABLE. okcrush. Qed.
  Hint Resolve ok_TABLE : okdb.
  Lemma ok_COPY : okA (arm_COPY).
  Proof. unfold arm_COPY. okcrush. Qed.
  Hint Resolve ok_COPY : okdb.
  Lemma ok_COPY_ : okA (arm_COPY_).
  Proof. unfold arm_COPY_. okcrush. Qed.
  Hint Resolve ok_COPY_ : okdb.
  Lemma ok_STORED : okA (arm_STORED iv flush).
  Proof. unfold arm_STORED. okcrush. Qed.
  Hint Resolve ok_STORED : okdb.
  Lemma ok_TYPEDO : okA (arm_TYPEDO iv flush).
  Proof. unfold arm_TYPEDO. okcrush. Qed.
  Hint Resolve ok_TYPEDO : okdb.
  Lemma ok_TYPE : okA (arm_TYPE iv flush).
  Proof. unfold arm_TYPE. okcrush. Qed.
  Hint Resolve ok_TYPE : okdb.
  Lemma ok_DICT : okA (arm_DICT iv flush).
  Proof. unfold arm_DICT. okcrush. Qed.
  Hint Resolve ok_DICT : okdb.
  Lemma ok_DICTID : okA (arm_DICTID iv flush).
  Proof. unfold arm_DICTID. okcrush. Qed.
  Hint Resolve ok_DICTID : okdb.
  Lemma ok_HCRC : okA (arm_HCRC).
  Proof. unfold arm_HCRC. okcrush. Qed.
  Hint Resolve ok_HCRC : okdb.
  Lemma ok_name_like : forall f, okS (name_like f).
  Proof. intros f. unfold name_like. okcrush. Qed.
  Hint Resolve ok_name_like : okdb.
  Lemma ok_COMMENT : okA (arm_COMMENT).
  Proof. unfold arm_COMMENT. okcrush. Qed.
  Hint Resolve ok_COMMENT : okdb.
  Lemma ok_NAME : okA (arm_NAME).
  Proof. unfold arm_NAME. okcrush. Qed.
  Hint Resolve ok_NAME : okdb.
  Lemma ok_EXTRA : okA (arm_EXTRA).
  Proof. unfold arm_EXTRA. okcrush. Qed.
  Hint Resolve ok_EXTRA : okdb.
  Lemma ok_EXLEN : okA (arm_EXLEN).
  Proof. unfold arm_EXLEN. okcrush. Qed.
  Hint Resolve ok_EXLEN : okdb.
  Lemma ok_OS : okA (arm_OS).
  Proof. unfold arm_OS. okcrush. Qed.
  Hint Resolve ok_OS : okdb.
  Lemma ok_TIME : okA (arm_TIME).
  Proof. unfold arm_TIME. okcrush. Qed.
  Hint Resolve ok_TIME : okdb.
  Lemma ok_FLAGS : okA (arm_FLAGS).
  Proof. unfold arm_FLAGS. okcrush. Qed.
  Hint Resolve ok_FLAGS : okdb.
  Lemma ok_HEAD : okA (arm_HEAD iv).
  Proof. unfold arm_HEAD. okcrush. Qed.
  Hint Resolve ok_HEAD : okdb.
  Lemma ok_BAD : okA (arm_BAD).
  Proof. unfold arm_BAD. okcrush. Qed.
  Hint Resolve ok_BAD : okdb.
  Lemma ok_MEM : okA (arm_MEM).
  Proof. unfold arm_MEM. okcrush. Qed.
  Hint Resolve ok_MEM : okdb.
  Lemma ok_SYNC : okA (arm_SYNC).
  Proof. unfold arm_SYNC. okcrush. Qed.
  Hint Resolve ok_SYNC : okdb.

  Definition RB (w : iw) : Prop := retw w = Z_OK \/ is_mode (w_s w) = BAD.

  Lemma ok_dispatch_ok : okA (dispatch iv flush).
  Proof. unfold dispatch. okcrush. Qed.

  Lemma dispatch_BAD : forall w, is_mode (w_s w) = BAD -> dispatch iv flush w = arm_BAD w.
  Proof. intros w E. unfold dispatch, abind, gs. rewrite E. reflexivity. Qed.

  Theorem dispatch_rc : forall w, RB w ->
    match dispatch iv flush w with ARun _ w' => RB w' | ALeave w' => RL (retw w') | ARet rc _ => RR rc end.
  Proof.
    intros w [R|B].
    - exact (ok_dispatch_ok w R).
    - rewrite (dispatch_BAD w B). unfold arm_BAD, abind, ur, aleave, retw. cbn. destruct (w_r w); cbn. unfold RL. auto.
  Qed.

  Section Loop.
    Variables (NI NO WN TOT0 : Z).
    Hypothesis NI32 : 0 <= NI < 2 ^ 32.
    Hypothesis NO32 : 0 <= NO < 2 ^ 32.

    Lemma iterK_rc : forall n w, pinv NI NO WN TOT0 w -> RB w -> PHI w < Z.of_nat n ->
      match iterK_nat n (gstep iv flush) w with
      | inl _ => False
      | inr (SLeave, w') => RL (retw w')
      | inr (SRet rc, _) => RR rc
      end.
    Proof.
      induction n as [|n IH]; intros w PI HB Hn.
      - exfalso. pose proof (PHI_nonneg NI NO WN TOT0 w PI). lia.
      - rewrite (iterK_gstep_S iv flush). pose proof (dispatch_ok iv flush NI NO WN TOT0 NI32 NO32 w PI) as [_ A]. pose proof (dispatch_rc w HB) as R.
        destruct (dispatch iv flush w) as [u w'|w'|rc w']; cbn [apost] in A.
        + destruct A as [P M]. apply IH; [exact P | exact R | lia].
        + exact R.
        + exact R.
    Qed.

    Theorem inf_loop_rc : forall w, pinv NI NO WN TOT0 w -> RB w ->
      let r := inf_loop iv flush w in
      match fst r with SLeave => RL (retw (snd r)) | SRet rc => RR rc end.
    Proof.
      intros w PI HB. cbv zeta. rewrite (inf_loop_iter iv flush).
      pose proof (iterK_rc (Z.to_nat (gfuel w)) w PI HB) as X.
      assert (F : PHI w < Z.of_nat (Z.to_nat (gfuel w))).
      { unfold gfuel. pose proof (PHI_fuel NI NO WN TOT0 w PI). pose proof (PHI_nonneg NI NO WN TOT0 w PI). rewrite Z2Nat.id; lia. }
      specialize (X F). destruct (iterK_nat _ _ w) as [w'|[[|rc] w']]; [exfalso; exact X | exact X | exact X].
    Qed.
  End Loop.
End Arms.
